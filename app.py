# -*- coding: utf-8 -*-
import pytz
from flask import Flask, render_template,redirect,request, session, url_for, abort, send_file # type: ignore
from flask_mysqldb import MySQL # type: ignore
from werkzeug.security import generate_password_hash, check_password_hash # type: ignore
from random import randint
from flask_socketio import SocketIO, emit, join_room, leave_room # type: ignore
import io
import base64
from io import BytesIO
from PIL import Image, ImageDraw, ImageFont
import random
import string
import json
import time
import numpy as np
from scipy.ndimage import label # type: ignore
import copy
import math
from itertools import product
from functools import wraps
from multiprocessing import Pool, cpu_count
from re import search
from collections import defaultdict
import threading
import traceback
from datetime import datetime
game_locks = {}    # Dictionary to hold locks by game ID
lock_for_create = threading.Lock()
fiirstN = 20
import random, math
from typing import List


def get_game_lock(game_id):
	#Only create one Lock per game ID
    with lock_for_create:
        if game_id not in game_locks:
            game_locks[game_id] = threading.Lock()
    return game_locks[game_id]


# Constants for the board
ROWS = 5
COLS = 7
TOTAL_SQUARES = ROWS * COLS

# Directions for movement (up, down, left, right, and diagonals)
DIRECTIONS = [(-1, -1), (-1, 0), (-1, 1),
              (0, -1),  (0,0),       (0, 1),
              (1, -1),  (1, 0),  (1, 1)]

# Piece types
CIRCLE = 'circle'
TRIANGLE = 'triangle'

# Square states
EMPTY = None
INACTIVE = 'inactive'

def pos_to_coords(pos):
    """Converts a position to (x, y) coordinates."""
    x = pos // COLS
    y = pos % COLS
    return x, y

def coords_to_pos(x, y):
    """Converts (x, y) coordinates to a position."""
    return x * COLS + y

class GameState:
    """Represents the state of the game."""
    def __init__(self, my_color, opponent_color, my_pieces, opponent_pieces, inactive_squares, my_score, opponent_score, is_overtime=False):
        self.my_color = my_color  # 'white' or 'black'
        self.opponent_color = opponent_color
        self.my_pieces = my_pieces  # {'circle': [pos1, pos2], 'triangle': [pos1, pos2]}
        self.opponent_pieces = opponent_pieces
        self.inactive_squares = set(inactive_squares)  # Set of positions
        self.my_score = my_score
        self.opponent_score = opponent_score
        self.is_overtime = is_overtime  # Boolean flag for overtime

    def is_terminal(self):
        # Check for win conditions
        if self.my_score >= 18 or self.opponent_score >= 18:
            return True
        if not self.has_moves():
            return True
        return False

    def has_moves(self):
        # Check if there are valid moves left
        for piece_type in [CIRCLE, TRIANGLE]:
            for pos in self.my_pieces[piece_type]:
                if pos == -1:
                    continue
                if self.get_valid_moves(pos):
                    return True
        return False

    def get_valid_moves(self, pos):
        moves = []
        x, y = pos_to_coords(pos)
        for dx, dy in DIRECTIONS:
            nx, ny = x + dx, y + dy
            if 0 <= nx < ROWS and 0 <= ny < COLS:
                n_pos = coords_to_pos(nx, ny)
                if n_pos in self.inactive_squares:
                    continue
                if n_pos in self.get_all_my_piece_positions(): #or n_pos in self.get_all_opponent_piece_positions():
                    continue
                moves.append(n_pos)
        return moves

    def get_all_my_piece_positions(self):
        positions = []
        for piece_list in self.my_pieces.values():
            positions.extend([pos for pos in piece_list if pos != -1])
        return positions

    def get_all_opponent_piece_positions(self):
        positions = []
        for piece_list in self.opponent_pieces.values():
            positions.extend([pos for pos in piece_list if pos != -1])
        return positions

    def apply_move(self, my_move, opponent_move):
        """
        Applies both my_move and opponent_move to the current state to produce a new state.
        If my_move or opponent_move is None, it means that player does not change their positions.
        """
        new_state = copy.deepcopy(self)

        # Update my_pieces if my_move is provided
        if my_move is not None:
            new_state.my_pieces = my_move

        # Update opponent_pieces if opponent_move is provided
        if opponent_move is not None:
            new_state.opponent_pieces = opponent_move

        # Resolve collisions
        collisions = {}
        my_positions = {}
        for piece_type in [CIRCLE, TRIANGLE]:
            for idx, pos in enumerate(new_state.my_pieces[piece_type]):
                if pos == -1:
                    continue
                my_positions[pos] = (piece_type, idx)

        opponent_positions = {}
        for piece_type in [CIRCLE, TRIANGLE]:
            for idx, pos in enumerate(new_state.opponent_pieces[piece_type]):
                if pos == -1:
                    continue
                opponent_positions[pos] = (piece_type, idx)

        # Check for collisions
        collided_positions = set(my_positions.keys()) & set(opponent_positions.keys())
        for pos in collided_positions:
            my_piece_type, my_idx = my_positions[pos]
            opp_piece_type, opp_idx = opponent_positions[pos]

            # Determine collision outcome
            if my_piece_type == opp_piece_type:
                # Square colored as White
                winner_color = 'white'
            else:
                # Square colored as Black
                winner_color = 'black'

            new_state.inactive_squares.add(pos)

            # Update scores
            if winner_color == self.my_color:
                new_state.my_score += 1
            else:
                new_state.opponent_score += 1

            # Remove pieces (they cannot move anymore)
            #new_state.my_pieces[my_piece_type][my_idx] = -1
            #new_state.opponent_pieces[opp_piece_type][opp_idx] = -1

        return new_state

    # Ensuring the GameState is picklable for multiprocessing
    def __getstate__(self):
        return self.__dict__

    def __setstate__(self, state):
        self.__dict__.update(state)


def expectimax(state, depth, maximizing_player):
    if depth == 0 or state.is_terminal():
        return evaluate_state(state)

    if maximizing_player:
        max_eval = -math.inf
        my_moves = generate_all_moves(state, state.my_pieces)
        for my_move in my_moves:
            exp_value = 0
            opponent_moves = generate_all_moves(state, state.opponent_pieces)
            if not opponent_moves:
                # If opponent has no moves, treat as terminal
                next_state = state.apply_move(my_move, None)
                eval = expectimax(next_state, depth - 1, False)
                exp_value += eval
            else:
                prob = 1 / len(opponent_moves)
                for opp_move in opponent_moves:
                    next_state = state.apply_move(my_move, opp_move)
                    eval = expectimax(next_state, depth - 1, False)
                    exp_value += prob * eval
            if exp_value > max_eval:
                max_eval = exp_value
        return max_eval
    else:
        # Expected value over opponent's possible moves
        exp_value = 0
        opponent_moves = generate_all_moves(state, state.opponent_pieces)
        if not opponent_moves:
            # If opponent has no moves, treat as terminal
            next_state = state.apply_move(None, None)
            eval = expectimax(next_state, depth - 1, True)
            exp_value += eval
        else:
            prob = 1 / len(opponent_moves)
            for opp_move in opponent_moves:
                next_state = state.apply_move(None, opp_move)
                eval = expectimax(next_state, depth - 1, True)
                exp_value += prob * eval
        return exp_value


def generate_all_moves(state, pieces):
    moves_list = []
    piece_types = [CIRCLE, TRIANGLE]
    moves_per_piece = {}
    for piece_type in piece_types:
        moves_per_piece[piece_type] = []
        for idx, pos in enumerate(pieces[piece_type]):
            if pos == -1:
                moves_per_piece[piece_type].append([-1])
                continue
            valid_moves = state.get_valid_moves(pos)
            if valid_moves:
                # To limit the branching factor, consider only the best moves based on a heuristic
                # For simplicity, we can shuffle and take the first few moves
                # Select three random moves from the valid moves
                random.shuffle(valid_moves)

                moves_per_piece[piece_type].append(valid_moves[:3])  # Consider up to 3 moves per piece
            else:
                # If no valid moves, the piece must stay in place
                moves_per_piece[piece_type].append([pos])

    # Generate all combinations of moves
    all_moves = []
    circle_moves = list(product(*moves_per_piece[CIRCLE]))
    triangle_moves = list(product(*moves_per_piece[TRIANGLE]))
    for c_move in circle_moves:
        for t_move in triangle_moves:
            # Combine all move positions
            move_positions = list(c_move) + list(t_move)
            # Exclude inactive positions (-1) from overlap checks
            active_positions = [p for p in move_positions if p != -1]
            # Check for overlapping positions within the player's own pieces
            if len(active_positions) != len(set(active_positions)):
                continue  # Overlapping detected, skip this move

            move = {
                CIRCLE: list(c_move),
                TRIANGLE: list(t_move)
            }
            all_moves.append(move)
    return all_moves

def evaluate_state(state):
    # Simple evaluation function: score difference
    return state.my_score - state.opponent_score

def evaluate_move(args):
    """Helper function for multiprocessing to evaluate a move."""
    my_move, state, depth = args
    exp_value = 0
    opponent_moves = generate_all_moves(state, state.opponent_pieces)

    if not opponent_moves:
        # If opponent has no moves, evaluate the state after my_move
        next_state = state.apply_move(my_move, None)
        eval = expectimax(next_state, depth - 1, False)
        exp_value += eval
    else:
        prob = 1 / len(opponent_moves)
        for opp_move in opponent_moves:
            next_state = state.apply_move(my_move, opp_move)
            eval = expectimax(next_state, depth - 1, False)
            exp_value += prob * eval
    return (exp_value, my_move)


def select_best_move(state, depth):
    max_eval = -math.inf
    best_move = None
    my_moves = generate_all_moves(state, state.my_pieces)
    num_processes = min(cpu_count(), len(my_moves))  # Use optimal number of processes

    # Using multiproc33essing to evaluate moves in parallel
    with Pool(processes=num_processes) as pool:
        args = [(my_move, state, depth) for my_move in my_moves]
        results = pool.map(evaluate_move, args)

    for exp_value, my_move in results:
        if exp_value > max_eval:
            max_eval = exp_value
            best_move = my_move
    return best_move


def beestMove(state):
    
    best_move = select_best_move(state, 2)
    return [pos for pos in best_move['circle'] + best_move['triangle']]

# state = GameState(my_color, opponent_color, my_pieces, opponent_pieces, inactive_squares, my_score, opponent_score)


def computeRegions(grid):

    pieceOverlay = np.array(grid).reshape(ROWS, COLS)
    zero_array = np.array([[0 if '0' in cell else 1 for cell in row] for row in pieceOverlay])
    #print(pieceOverlay)

    grid = pieceOverlay

    labeledGrid, numRegions = label(zero_array != 0)
    #or i in labeledGrid:
        #print("".join(str(i)))

    #print()

    pieceRegions = []

    for i in range(len(grid)):
        
        for j in range(len(grid[i])):
            
            if j == "":
                continue
            pieces = [char for char in pieceOverlay[i,j] if char.isalpha()]
            for piece in pieces:
                pieceRegions.append([piece,labeledGrid[i,j],i*7+j])

    #or p in pieceRegions:
        #print(p)

    #print()
    regionsIndices = defaultdict(list)
    for i in range(len(labeledGrid)):
        for j in range(len(labeledGrid[i])):
            region = labeledGrid[i][j]
            if region != 0:
                regionsIndices[region].append(i * 7 + j)

    regions = {}
    #print(regionsIndices)
    for i in range(numRegions+1):
        
        piecesInRegion = [g[0] for g in pieceRegions if g[1] == i]
        #print(piecesInRegion)
        regions[str(i)] = [len(regionsIndices[i]),regionsIndices[i],[g[:1]+g[1+1:] for g in pieceRegions if g[1] == i and g[0].islower()]+[g[:1]+g[1+1:] for g in pieceRegions if g[1] == i and g[0].isupper()]]
        if len(regionsIndices[i]) == 1:
            del regions[str(i)]
        #print(f"Regija {i} ima {len(regionsIndices[i])} polja")
        
        #print(f"Broj koraka bez sudara prije izvanrednog koraka: {np.count_nonzero(labeledGrid == i)}")
        #print(f"U slučaju izvanrednog sudara bijeli dobiva odabir/e {[g[:1]+g[1+1:] for g in pieceRegions if g[1] == i and g[0].islower()]}")
        #print(f"U slučaju izvanrednog sudara  crni  dobiva odabir/e {[g[:1]+g[1+1:] for g in pieceRegions if g[1] == i and g[0].isupper()]}")
        #print() 
    
    print(regions)
    print("TO SU REGIJE")
    return regions


import os
from dotenv import load_dotenv # type: ignore

app = Flask(__name__, template_folder=os.getenv('TEMPLATE_FOLDER'), static_folder=os.getenv('STATIC_FOLDER'),)
app.secret_key = os.getenv("SECRET_KEY")

app.config["MYSQL_HOST"] = os.getenv("MYSQL_HOST")
app.config["MYSQL_USER"] = os.getenv("MYSQL_USER")
app.config["MYSQL_PASSWORD"] = os.getenv("MYSQL_PASSWORD")
app.config["MYSQL_DB"] = os.getenv("MYSQL_DB")
app.config['SESSION_TYPE'] = 'filesystem'

app.config['TRAP_HTTP_EXCEPTIONS']=True

mysql = MySQL(app)

socketio = SocketIO(app, manage_session=True)

botGames = {}

waitingGames = {}

awaitingRevenge = {}

#listeners = {}

#+---------------+--------------+------+-----+---------+-------+
#| Field         | Type         | Null | Key | Default | Extra |
#+---------------+--------------+------+-----+---------+-------+
#| ID            | varchar(255) | NO   | PRI | NULL    |       |
#| tempIgraci    | json         | YES  |     | NULL    |       |
#| igraci        | json         | YES  |     | NULL    |       |
#| vrijeme       | timestamp    | YES  |     | NULL    |       |
#| potezi        | json         | YES  |     | NULL    |       |
#| vremenaPoteza | json         | YES  |     | NULL    |       |
#| krenulo       | tinyint(1)   | YES  |     | NULL    |       |
#| privatna      | tinyint(1)   | YES  |     | NULL    |       |
#| crnaPolja     | json         | YES  |     | NULL    |       |
#| bijelaPolja   | json         | YES  |     | NULL    |       |
#| pobjednik     | int          | YES  |     | NULL    |       |
#| DIDSS         | tinyint(1)   | YES  |     | NULL    |       |
#| regije        | json         | YES  |     | NULL    |       |
#+---------------+--------------+------+-----+---------+-------+

@socketio.on("listenIn")
def listenIn(data):
    join_room(data.get("id"))
    #print(f"Korisnik {session['user']} se pridružio sobi {data.get('id')}")
    

@app.route("/bot")
def bot():
    if session.get("user") == None:
        return redirect(url_for("login"))
    id = genRandomString()
    botGames[id] = "g"
    waitingGames[id] = "v"
    cur = mysql.connection.cursor()
    cur.execute("START TRANSACTION")
    cur.execute("select id from users where username=%s FOR UPDATE",(session.get("user"),))
    userId = cur.fetchone()[0]
    print(userId)
    temp = [userId]
    temp=str(temp)
    cur.execute("insert into igre (ID,tempIgraci,krenulo,privatna,vrijeme) values (%s,%s,%s,%s,%s)",(id,str([userId,-1]),False,False,time.time()))
    mysql.connection.commit()
    cur.close()

    return redirect(url_for("gamePage",id=id))

def areSamePiece(x,y):
    # 0,1 su krug a 2,3 su trokut
    if x in [0,1] and y in [0,1]:
        return True
    elif x in [2,3] and y in [2,3]:
        return True
    else:
        return False


@socketio.on("revenge")
def revenge(data):
    id = data.get("id")
    isBlack = data.get("isBlack")
    if id in awaitingRevenge and awaitingRevenge[id][0] != isBlack:
        game = startGame(session.get("user"),isPrivate=True)
        username = session.get("user")
        gameId = game
        isPrivate = True
        del awaitingRevenge[id]
        waitingGames[game] = "g"
        cur = mysql.connection.cursor()
        cur.execute("START TRANSACTION")
        cur.execute("select id from users where username=%s FOR UPDATE",(username,))
        userId = cur.fetchone()[0]
        print(userId)
        temp = [userId]
        temp=str(temp)
        cur.execute("insert into igre (ID,tempIgraci,krenulo,privatna,vrijeme) values (%s,%s,%s,%s,%s)",(gameId,temp,False,isPrivate,time.time()))
        mysql.connection.commit()
        cur.close()

        emit("revengeGotten",{"id":game},to=id)
        
    else:
        awaitingRevenge[id] = [isBlack,session.get("user")]
        emit("awaitingRevenge",{"isBlack":isBlack},to=id)

@socketio.on("giveUp")
def gaveUp(data):
    id = data.get("id")
    isBlack = data.get("isBlack")
    userLeft = data.get("userLeft")
    cur = mysql.connection.cursor()
    cur.execute("select igraci from igre where id=%s",(id,))
    players = json.loads(cur.fetchone()[0])
    cur.execute("update igre set pobjednik=%s where id=%s",(players[int(isBlack)],id))
    mysql.connection.commit()
    if userLeft:
        reason = "userLeft"
    else:
        reason = "gaveUp"
    emit("gameOver",{"loserIsBlack":isBlack,"reason":reason},to=id)


@socketio.on("selectedForExclusive")
def selectedForExclusive(data):
    emit("exclusiveMoveDecided",{"isBlack":data.get("isBlack"),"cell":data.get("cell")},to=data.get("id"))

exclusiveMoves = {}


class Board:
    """Initalizes the board for the selected parameters. \n
        The structure of the parameters is:
        spaces: a list of taken spaces, color is irrelevant
        pieces: a list of two lists for each player's pieces.
          The first two elements represent the position of the respected player's circles, and the last two are for the triangles.
            If an element is -1, that piece is no longer on the board.
        
    """
    def __init__(self, spaces, pieces):
        self.spaces = spaces
        self.pieces = pieces
        self.grid = ["" for _ in range(35)]
        for space in spaces:
            self.grid[space] += "0"
        
        for i in range(4):
            whitePiece = pieces[0][i]
            if whitePiece != -1:
                if i<2:
                    self.grid[whitePiece] += "k"
                else:
                    self.grid[whitePiece] += "t"
            blackPiece =pieces[1][i]
            if blackPiece != -1:
                if i<2:
                    self.grid[blackPiece] += "K" 
                else:
                    self.grid[blackPiece] += "T"

def generateAllMoves(board):
    whiteMoves = [[],[],[],[]]
    blackMoves = [[],[],[],[]]
    for i in range(4):
        whitePiece = board.pieces[0][i]
        if whitePiece == -1:
            whiteMoves[i].append(-1)
        if whitePiece != -1:
            transforms = [-7,7]
            if "0" not in board.grid[whitePiece]:
                transforms.append(0)
            if whitePiece%7 != 0:
                transforms.extend([-8,-1,6])
            if whitePiece%7 != 6:
                transforms.extend([8,1,-6])
            for transform in transforms:
                transformed = whitePiece + transform
                if transformed > -1 and transformed < 35:
                    if transformed == whitePiece or transformed not in board.spaces and transformed not in board.pieces[0]:
                        
                        whiteMoves[i].append(transformed)
        blackPiece = board.pieces[1][i]
        if blackPiece == -1:
            blackMoves[i].append(-1)
        if blackPiece != -1:
            transforms = [-7,0,7]
            if blackPiece%7 != 0:
                transforms.extend([-8,-1,6])
            if blackPiece%7 != 6:
                transforms.extend([8,1,-6])
            for transform in transforms:
                transformed = blackPiece + transform
                if transformed > -1 and transformed < 35:
                    if transformed == blackPiece or transformed not in board.spaces and transformed not in board.pieces[1]:
                        
                        blackMoves[i].append(transformed)
    print(f"white can make {len(whiteMoves[0])*len(whiteMoves[1])*len(whiteMoves[2])*len(whiteMoves[3])} different moves")
    print(f"black can make {len(blackMoves[0])*len(blackMoves[1])*len(blackMoves[2])*len(blackMoves[3])} different moves")
    return whiteMoves, blackMoves



def allNextSubmittedStates(board, maximizingPlayerIsBlack):

    whiteMoves, blackMoves = generateAllMoves(board)
    whiteBestMoves = []
    blackBestMoves = []
    whiteBestScore = 0
    blackBestScore = 0
    bestBoard = None
    counter = 0
    for k1 in whiteMoves[0]:
        for k2 in whiteMoves[1]:
            for t1 in whiteMoves[2]:
                for t2 in whiteMoves[3]:
                    for K1 in blackMoves[0]:
                        for K2 in blackMoves[1]:
                            for T1 in blackMoves[2]:
                                for T2 in blackMoves[3]:
                                    counter += 1
                                    tempWhiteScore = 0
                                    tempBlackScore = 0
                                    newBoard = Board(board.spaces, [[k1,k2,t1,t2],[K1,K2,T1,T2]])
                                    for i in newBoard.grid:
                                        if i == "kT" or i == "Tk" or i == "tK" or i == "Kt":
                                            tempBlackScore += 1
                                        if i == "kK" or i == "tT":
                                            tempWhiteScore += 1
                                    if tempWhiteScore > whiteBestScore:
                                        whiteBestScore = tempWhiteScore
                                        whiteBestMoves = [k1,k2,t1,t2]
                                        if not maximizingPlayerIsBlack:
                                            bestBoard = newBoard
                                    if tempBlackScore > blackBestScore:
                                        blackBestScore = tempBlackScore
                                        blackBestMoves = [K1,K2,T1,T2]
                                        if maximizingPlayerIsBlack:
                                            bestBoard = newBoard
    print("white best moves", whiteBestMoves)
    print("black best moves", blackBestMoves)
    print("white best score", whiteBestScore)
    print("black best score", blackBestScore)
    print("counter", counter)

    print("done")    
    return blackBestMoves if maximizingPlayerIsBlack else whiteBestMoves   

    
class Board:
    def __init__(self, fields:List[int], positions:List[List[int]]):
        self.fields=set(fields)
        self.positions=positions

def bot_move(board:Board, isBlack:bool)->List[int]:
# Constants
    R,C=5,7

    # Extract references for convenience
    me  = 1 if isBlack else 0
    opp = 1-me
    myP = board.positions[me]   # [c1,c2,t1,t2]
    opP = board.positions[opp]  # [c1,c2,t1,t2]

    # Board helpers
    def toRC(pos): return divmod(pos, C)
    def dist(a,b): return math.hypot(toRC(a)[0]-toRC(b)[0], toRC(a)[1]-toRC(b)[1])
    def neighs(pos):
        if pos<0: return []
        r,c=toRC(pos); out=[]
        for dr in[-1,0,1]:
            for dc in[-1,0,1]:
                rr,cc=r+dr,c+dc
                if 0<=rr<R and 0<=cc<C:
                    p=rr*C+cc
                    if p not in board.fields: out.append(p)
        return out+[pos] if pos not in board.fields else out

    # Compute collisions & score from final positions
    def collision_score(newB):
        # newB.positions = [blackPieces,whitePieces]
        bp,wp=newB.positions
        bpts=wpts=0
        # If any black piece == any white piece => collision
        for i,bpos in enumerate(bp):
            for j,wpos in enumerate(wp):
                if bpos>=0 and wpos>=0 and bpos==wpos:
                    sameType=(i<2 and j<2)or(i>=2 and j>=2)
                    if sameType: wpts+=1
                    else: bpts+=1
        return bpts,wpts

    # Apply a move [c1,c2,t1,t2] for black & white, returns new board
    def apply_moves(b:Board, blackM, whiteM):
        nb=Board([],[])  # minimal copy
        nb.fields=b.fields.copy()
        nb.positions=[blackM[:], whiteM[:]]
        return nb

    # Generate candidate moves (subset for brevity)
    # For each piece, gather neighbors, pick up to ~4 that bring it closer
    # to desired collision-type if isBlack else same-type. Shuffle for unpredictability.
    def gen_moves(player):
        ps=b.positions[player]; oc=b.positions[1-player]
        cTgt= oc[2:4] if player==0 else oc[:2] # black circle→white triangle or white circle→black circle
        tTgt= oc[:2] if player==0 else oc[2:4]
        moves=[]
        def best_nbs(p,t):
            if p<0:return [p]
            ns=neighs(p); random.shuffle(ns)
            if not t: return ns[:2]
            d0=min(dist(p,x)for x in t)
            # pick neighbors that are as good or better
            chosen=sorted(ns,key=lambda x: min(dist(x,xx) for xx in t))[:3]
            return chosen
        # For circles
        for c in best_nbs(ps[0], cTgt): 
            for c2 in best_nbs(ps[1], cTgt):
                # ensure no stacking
                if c2==c and c!=-1: continue
                # Triangles
                for t1 in best_nbs(ps[2], tTgt):
                    if t1 in[c,c2] and t1!=-1: continue
                    for t2 in best_nbs(ps[3], tTgt):
                        if t2 in[c,c2,t1] and t2!=-1: continue
                        moves.append([c,c2,t1,t2])
        random.shuffle(moves)
        return moves#[:100] # limit to keep branching small

    # Evaluate board for me
    def evaluate(bd):
        bpts,wpts=collision_score(bd)
        return (bpts-wpts) if isBlack else (wpts-bpts)

    # MiniMax depth=2 with alpha-beta
    def minimax(bd, depth, alpha, beta, maximizing):
        if depth==0: return None,evaluate(bd)
        candidateMoves = gen_moves(me if maximizing else opp)
        if not candidateMoves: return None,evaluate(bd)
        bestM = candidateMoves[0]
        if maximizing:
            val=-999
            for m in candidateMoves:
                newB1=apply_moves(bd,m,bd.positions[opp]) if maximizing and me==0 else apply_moves(bd,bd.positions[0],m)
                # Opponent's response
                if depth>1:
                    _,v=minimax(newB1,depth-1,alpha,beta,not maximizing)
                else:
                    v=evaluate(newB1)
                if v>val: val,bestM=v,m
                alpha=max(alpha,val)
                if beta<=alpha: break
            return bestM,val
        else:
            val=999
            for m in candidateMoves:
                newB1=apply_moves(bd,m,bd.positions[me]) if not maximizing and opp==0 else apply_moves(bd,bd.positions[0],m)
                if depth>1:
                    _,v=minimax(newB1,depth-1,alpha,beta,not maximizing)
                else:
                    v=evaluate(newB1)
                if v<val: val,bestM=v,m
                beta=min(beta,val)
                if beta<=alpha: break
            return bestM,val

    # Decide best move by simulating up to 2-ply
    b=Board(board.fields,list(map(list,board.positions)))
    move,_=minimax(b,2,-999,999,True)
    return move if move else myP[:]  # fallback to no-move if none



@socketio.on("submitMoves")
def submitMoves(data):
    global exclusiveMoves
    id = data.get("id")
    gameId = id
    isBlack = data.get("isBlack")
    moves = data.get("moves")
    time = data.get("time")
    myExclusiveMove = data.get("exclusiveMove")
    cur = mysql.connection.cursor()
    cur.execute("START TRANSACTION")
    cur.execute("SELECT potezi, crnaPolja, bijelaPolja, vremenaPoteza, igraci FROM igre WHERE id=%s FOR UPDATE", (id,))
    result = cur.fetchone()
    potezi = json.loads(result[0])
    vremenaPoteza = json.loads(result[3])
    igraci = json.loads(result[4])

    #fallback for fields white/black
    #  if they're empty
    if result[1] == None:
        bijelaPolja = []
        crnaPolja = []
    else:
        bijelaPolja = json.loads(result[2])
        crnaPolja = json.loads(result[1])


    #print(potezi)
    
    #print("TO SU ONI")
    #print(moves)
    
    potezi[-1][int(isBlack)] = moves
    #print(isBlack)
    #print(vremenaPoteza)
    vremenaPoteza[-1][int(isBlack)] = time
    #print(vremenaPoteza)
    #print("OVO JE VRIJEME")
    #print(potezi)
    fields = []
    
    for i in bijelaPolja:
        if i[1] != []:
            fields.extend([ int(a) for a in i[1]])
    for i in crnaPolja:
        if i[1] != []:
            fields.extend([ int(a) for a in i[1]])

    if myExclusiveMove != None:
        print(exclusiveMoves)
        print("ATO JE EKXLSUAV")
        print(moves)

        exclusiveMoves[id][int(isBlack)] = [int(myExclusiveMove),potezi[-1][int(isBlack)][int(myExclusiveMove)]]


            

            
    if potezi[-1][int(not isBlack)] != [] or id in botGames:
            id = request.sid if id in botGames else id
            
            #write a comment of how to get the union of two lists
            #the syntax is list(set(list1) | set(list2))
            print("POTEZI SU ",potezi)
            #if len(potezi) == 2 and gameId in botGames:
            #    emit("ok",{"moves":potezi[-1],"whiteTaken":white_spaces,"blackTaken":black_spaces,"exclusiveMove":[exclusiveMove[0],exclusiveMove[1]]},to=id)
            #ovaj je već gotov
                # potezi.append([[],[]])
                # vremenaPoteza.append([0,0])
                # vremenaPoteza = json.dumps(vremenaPoteza)
                # potezi = json.dumps(potezi)  
                # bijelaPolja = json.dumps(bijelaPolja)
                # crnaPolja = json.dumps(crnaPolja)
                # cur.execute("update igre set potezi=%s, crnaPolja=%s, bijelaPolja=%s, vremenaPoteza=%s where id=%s",(potezi,crnaPolja,bijelaPolja,vremenaPoteza,gameId))
                # mysql.connection.commit()
                # return
            if gameId in botGames and len(potezi) > 2:
                adversariesLastMove = [int(i) for i in potezi[-2][int(not isBlack)]]
                playersLastMove = [int(i) for i in potezi[-2][int(isBlack)]]
                lastMoves = [adversariesLastMove,playersLastMove] if not isBlack else [playersLastMove,adversariesLastMove]
                print(lastMoves)
                print(len(lastMoves))
                botColor = "white" if isBlack else "black"
                myColor = "black" if isBlack else "white"
             
        #             def __init__(self, my_color, opponent_color, my_pieces, opponent_pieces, inactive_squares, my_score, opponent_score, is_overtime=False):
        # self.my_color = my_color  # 'white' or 'black'
        # self.opponent_color = opponent_color
        # self.my_pieces = my_pieces  # {'circle': [pos1, pos2], 'triangle': [pos1, pos2]}
        # self.opponent_pieces = opponent_pieces
        # self.inactive_squares = set(inactive_squares)  # Set of positions
        # self.my_score = my_score
        # self.opponent_score = opponent_score
        # self.is_overtime = is_overtime  # Boolean flag for overtime
                state = GameState(myColor,botColor,{CIRCLE:adversariesLastMove[:2],TRIANGLE:adversariesLastMove[2:]},{CIRCLE:adversariesLastMove[:2],TRIANGLE:adversariesLastMove[2:]},fields,0,0)
                board = Board(fields,lastMoves)

                botMoves = bot_move(board,isBlack)
                potezi[-1][int(not isBlack)] = [str(i) for i in botMoves]
                vremenaPoteza[-1][int(not isBlack)] = time
                print("BOT MOVES",botMoves)
                print("BOT MOVES",potezi[-1][int(not isBlack)])
            if len(potezi) == 2 and gameId in botGames:
                print(potezi)

            cur.execute("update igre set potezi=%s, vremenaPoteza=%s where id=%s",(json.dumps(potezi),json.dumps(vremenaPoteza),gameId))

            mysql.connection.commit()
            player1_moves = potezi[-1][0]
            player2_moves = potezi[-1][1]
            white_spaces = []
            black_spaces = []

            if myExclusiveMove != None:
                print(exclusiveMoves)
                print("TO JE EXCLUSIVE MOVE")
                whitePiece = "circle" if exclusiveMoves[id][0][0] in [0,1] else "triangle"
                blackPiece = "circle" if exclusiveMoves[id][1][0] in [0,1] else "triangle"
                whitePos = exclusiveMoves[id][0][1]
                blackPos = exclusiveMoves[id][1][1]
                print(whitePiece,blackPiece)
                print(whitePos,blackPos)
                print("TO SU POZICIJE")
                if whitePiece == blackPiece: #bod za bijele
                    if whitePos != blackPos: #ako su se promakli a bijeli bi pobjedio
                        print("CRNA")
                        black_spaces.append(blackPos)
                if whitePiece != blackPiece: #bod za crne
                    if whitePos != blackPos:
                        print("BIJELA")
                        white_spaces.append(whitePos)
                exclusiveMoves[id] = [None,None]

            for i, move1 in enumerate(player1_moves):
                if move1 == -1:  # Skip removed pieces
                    continue

                for j, move2 in enumerate(player2_moves):
                    if move2 == -1:  # Skip removed pieces
                        continue

                    if move1 == move2:  # Overlap found
                        # Determine ownership based on piece type
                        if (i < 2 and j < 2) or (i >= 2 and j >= 2):  # Same type (circle & circle OR triangle & triangle)
                            if move1 not in white_spaces:  # Avoid duplicates
                                white_spaces.append(move1)
                        else:  # Different types (circle & triangle OR triangle & circle)
                            if move1 not in black_spaces:  # Avoid duplicates
                                black_spaces.append(move1)

            bijelaPolja.append([len(potezi),white_spaces])    
            crnaPolja.append([len(potezi),black_spaces])
            brojBijelih = 0
            brojCrnih = 0

            for i in bijelaPolja:
                if i[1] != []:
                    brojBijelih += len(i[1])
            for i in crnaPolja:
                if i[1] != []:
                    brojCrnih += len(i[1])

            grid = ["" for i in range(35)]
        
            #print(bijelaPolja , crnaPolja)

            for w in bijelaPolja:
                for pos in w[1]:
                    pos = int(pos)
                    grid[pos] += "0"
                
            for b in crnaPolja:
                for pos in b[1]:
                    pos = int(pos)
                    grid[pos] += "0"

            for pos in potezi[-1][0]:
                pos = int(pos)
                if pos != -1:
                    grid[pos] += 'w'

            for pos in potezi[-1][1]:
                pos = int(pos)
                if pos != -1:
                    grid[pos] += 'B'
            exclusiveMove = [[] , []]




            


            #OČITOVANA STRUKTURA REGIJA GLASI OVAKO
            #{ KEY!! KAO U PRIMARY KEY ?!?! genijalno
            #   1:[brojPolja,[polja],[[tip,pozicija],...]]
            #   2:[brojPolja,[polja],[[tip,pozicija],...]]
            #   3:[brojPolja,[polja],[[tip,pozicija],...]]
            #...
            #}
            #zamislimo jednu utopiju gdje je regija u bazi već stavljena
            #jer zamisao nepostavljenih regija me drži budnim noću
            #i onda je očitamo i usporedimo sa stvarnim stanjem
            #i onda se dogodi magija
            #i onda se dogodi izvanredni potez
            #i onda se dogodi pobjeda
            #i onda se dogodi sreća
            #i onda se dogodi ljubav
            #i onda se dogodi mir
            #i onda se dogodi svijet
            #i onda se dogodi svemir
            #i onda se dogodi sve
            #i onda se dogodi ništa
            #i onda se dogodi ništa
            #i onda se dogodi ništa
            #i onda se dogodi ništa
            #i onda se dogodi ništa
            #...
            #i onda se dogodi ništa

            #ovo je najbolji dio

            #ali kako da usporedimo regije? kako ćemo znati ako je regija 1 u bazi ista kao regija 1 u igri?
            #pa to je jednostavno
            #ako je broj polja isti
            #ako su polja ista     
            #ako su tipovi isti
            #onda je regija ista
            #postoji li bolji način?
            #ne
            #ali oduzimamo od broja polja svaki potez
            #i onda ako je broj polja 0
            #izvanredni potez!
            #također, ako se polje između ovog poteza i prošlog poteza nije promijenilo
            #onda je izvanredni potez
            
            
            regionsToSubmit = {}
            cur.execute("SELECT regije FROM igre WHERE id=%s", (gameId,))
            row = cur.fetchone()
            dbRegions = json.loads(row[0]) if row and row[0] else {}
            localRegions = computeRegions(grid)
            areNotSegregated = 0

            #jako bitno
            dbRegions = {key:value for (key,value) in dbRegions.items() if key in localRegions}
            



            if not dbRegions:
                print("nema regija")
                regionsToSubmit = localRegions
            else:
                for i, (key,value) in enumerate(dbRegions.items()):
                    print(f"---++POČETAK++--- REGIJE {key}")
                    whitePiecesInRegion = 0
                    blackPiecesInRegion = 0
                    for piece in value[2]:
                        if piece[0].islower():
                            whitePiecesInRegion += 1
                        else:
                            blackPiecesInRegion += 1
                    if whitePiecesInRegion == 0 or blackPiecesInRegion == 0:
                        continue


                    print(len(localRegions[key][1]))
                    print(len(value[1]))
                    print("lens")
                    if len(localRegions[key][1]) != len(value[1]):
                        print("različit broj polja")
                        print(i)
                        print(len(dbRegions)-1)


                        continue
                    print("still iterating")
                    if len(localRegions[key][2]) == 1:
                        print("jednofiguran prostor")

                        continue
                    print("došao sam do tu")

                            
                    print(value[0])
                    
                    print(value[0])
                    print("ovo je value")
                    print(value[2])
                    print(localRegions[key][2]) #hmm
                    value[0] -= 1
                    localRegions[key][0] = value[0]
                    print("to su stvari")

                    print(key,value[0])
                    print("on je na tom")
                    if value[0] == 0:
                        for piece in value[2]:
                            if piece[0].islower():
                                exclusiveMove[0].append(piece[1])
                            else:
                                exclusiveMove[1].append(piece[1])
                        
                        print("palo je na 0")
                    if value[2] == localRegions[key][2]:
                        for piece in value[2]:
                            if piece[0].islower():
                                exclusiveMove[0].append(piece[1])
                            else:
                                exclusiveMove[1].append(piece[1])
                        
                        print("nema pomicanja u regiji")
                    else:
                        print("nisu isti")
                for key in list(dbRegions.keys()):
                    if dbRegions[key][0] == 0:
                        del dbRegions[key]
                    if dbRegions[key][2] == localRegions[key][2]:
                        del dbRegions[key]



                dbRegions.update(localRegions)
                
                     #ovo je bitno


                
                for key in dbRegions:
                    if key not in localRegions:
                        del dbRegions[key]
                regionsToSubmit = dbRegions

            for key,value in regionsToSubmit.items():
                whiteSeg = 0
                blackSeg = 0
                for piece in value[2]:
                    if piece[0].islower():
                        whiteSeg += 1
                    else:
                        blackSeg += 1
                print(whiteSeg,blackSeg)
                print(key)

                if whiteSeg == 0 or blackSeg == 0:
                    areNotSegregated+=1
                
                    


            
            if areNotSegregated == len(regionsToSubmit):
                if brojBijelih == brojCrnih:
                    cur.execute("update igre set didss=%s where id=%s",(True,gameId))
                    emit("ok",{"didss":True},to=id)
                else:
                    winner = True if brojBijelih > brojCrnih else False
                    cur.execute("update igre set pobjednik=%s where id=%s",(igraci[int(winner)],gameId))
                    emit("gameOver",{"loserIsBlack":winner,"reason":"segregation"},to=id)
            del regionsToSubmit['0']

            print(regionsToSubmit)
            print(exclusiveMove)
            print("TO SU REGIJEEEE")



            
            
            

            # Save dbRegions
            cur.execute("UPDATE igre SET regije=%s WHERE id=%s", (json.dumps(regionsToSubmit), gameId))
            mysql.connection.commit()


            #print(white_spaces)
            #print(black_spaces)
            #print(len(potezi)-1)
            #print(bijelaPolja)
            #print(crnaPolja)
            #print(brojBijelih,brojCrnih)
            #print("TO SU BIJELI I DESNI")
            if brojBijelih > 17 and brojCrnih < 17:
                cur.execute("update igre set pobjednik=%s where id=%s",(igraci[0],gameId))
                mysql.connection.commit()
                emit("gameOver",{"loserIsBlack":True,"reason":"spaces"},to=id)
            elif brojCrnih > 17 and brojBijelih < 17:
                cur.execute("update igre set pobjednik=%s where id=%s",(igraci[1],gameId))
                mysql.connection.commit()
                emit("gameOver",{"loserIsBlack":False,"reason":"spaces"},to=id)
            if exclusiveMove != [[] , []]:
                print("O MOJ BOŽE IZVANREDNI POTEZ")

            canMove = False
            directions = [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]
            for iid in range(35):
                x,y = iid//7,iid%7
                pos = grid[iid]
                print(pos)
                if any(p in pos for p in ["w","B"]):
                    for dx,dy in directions:
                        nx,ny = x+dx,y+dy
                        print(nx,ny)
                        if 0 <= nx < 5 and 0 <= ny < 7:
                            print(grid[nx*7+ny])
                            if grid[nx*7+ny] == "":
                                canMove = True
                                print("CAN MOVE")
                                break
                    if canMove:
                        break
            if not canMove:
                if brojBijelih == brojCrnih:
                    cur.execute("update igre set didss=%s where id=%s",(True,gameId))
                    emit("ok",{"didss":True},to=id)
                else:
                    winner = False if brojBijelih > brojCrnih else True
                    cur.execute("update igre set pobjednik=%s where id=%s",(igraci[int(winner)],gameId))
                    print("NEMA POMAKA A POBJEDNIK JE",winner)
                    emit("gameOver",{"loserIsBlack":winner,"reason":"spaces"},to=id)
            else:


            # state = GameState(my_coflor, opponent_color, my_pieces, opponent_pieces, inactive_squares, my_score, opponent_score)
                        #emit("ok",{"moves":potezi[-1]},to=id)
                emit("ok",{"moves":potezi[-1],"whiteTaken":white_spaces,"blackTaken":black_spaces,"exclusiveMove":[exclusiveMove[0],exclusiveMove[1]]},to=id)
            #ovaj je već gotov
                potezi.append([[],[]])
                vremenaPoteza.append([0,0])
                vremenaPoteza = json.dumps(vremenaPoteza)
                potezi = json.dumps(potezi)  
                bijelaPolja = json.dumps(bijelaPolja)
                crnaPolja = json.dumps(crnaPolja)
                cur.execute("update igre set potezi=%s, crnaPolja=%s, bijelaPolja=%s, vremenaPoteza=%s where id=%s",(potezi,crnaPolja,bijelaPolja,vremenaPoteza,gameId))
                mysql.connection.commit()
    if potezi[-1][int(not isBlack)] == []:
        
        

        #print(f"{isBlack} je prvi napravio potez")
        #ako smo mi prvi napravili potez
        
        emit("waiting",{"whoIsDone":isBlack},to=id)
        cur.execute("update igre set potezi=%s, vremenaPoteza=%s where id=%s",(json.dumps(potezi),json.dumps(vremenaPoteza),id))

        mysql.connection.commit()

firstMoves = {}

@socketio.on("firstMove")
def firstMove(data):
    global firstMoves
    global exclusiveMoves
    gameId = data.get("id")
    move = data.get("move")
    isAdversary = data.get("isAdversary")
    moveTime = data.get("moveTime")
    username = session.get("user")
    cur = mysql.connection.cursor()
    isBotGame = False if gameId not in botGames else True
    # Ensure firstMoves entry exists for this game
    if isBotGame:
        playerIsBlack = random.choice([True,False])
        adversaryIsBlack = not playerIsBlack
        if playerIsBlack:
            adversaryMovee = int(not playerIsBlack)
        else:
            adversaryMovee = int(playerIsBlack)
        illegalFirstMoves = ["7", "8", "9", "14", "15", "16", "21", "22", "23"] if adversaryIsBlack else ["11", "12", "13", "18", "19", "20", "25", "26", "27"]
        valid_moves = list(set(str(i) for i in range(35)) - set(illegalFirstMoves))
        adversaryMove = random.sample(valid_moves, 4)
        cur.execute("SELECT id FROM users WHERE username=%s",(username,))
        userId = cur.fetchone()[0]
        players = [userId,-1] if playerIsBlack else [-1,userId]
        moves = [[],adversaryMove] if not playerIsBlack else [adversaryMove,[]]
        times = [[moveTime,0]] if playerIsBlack else [[0,moveTime]]
        cur.execute("""
        UPDATE igre 
        SET igraci = %s, potezi = %s, vremenaPoteza = %s, krenulo = %s 
        WHERE ID = %s
    """, (
        json.dumps(players),
        json.dumps([[move, adversaryMovee], moves]),
        json.dumps([times, [0, 0]]),
        True,
        gameId
    ))
        mysql.connection.commit()
        cur.close()
        emit("recieved",{"isBlack":playerIsBlack,"otherPlayer":"4NT3"},to=request.sid)
        return

    if gameId not in firstMoves:
        firstMoves[gameId] = {
            'player': {  # Store game creator as "player"
                'sid': request.sid,
                'move': move,
                'isAdversary': isAdversary,
                'username': username,
                'time': moveTime
            }
        }
        emit("ok", {"message": "Waiting for opponent's move", "isAdversary": isAdversary})
        return

    # Process the second move
    player_data = firstMoves[gameId]['player']  # Game creator
    adversary_data = {
        'sid': request.sid,
        'move': move,
        'isAdversary': isAdversary,
        'username': username,
        'time': moveTime
    }

    # Assign colors based on moves
    moves_match = player_data['move'] == adversary_data['move']
    player_is_white = not isAdversary if moves_match else isAdversary

    # Get player IDs
    cur.execute("SELECT id FROM users WHERE username = %s", (player_data['username'],))
    player_id = cur.fetchone()[0]
    cur.execute("SELECT id FROM users WHERE username = %s", (adversary_data['username'],))
    adversary_id = cur.fetchone()[0]

    # Assign white and black
    white_player = player_id if player_is_white else adversary_id
    black_player = adversary_id if player_is_white else player_id

    cur.execute("SELECT * FROM igre WHERE JSON_CONTAINS(igraci,JSON_ARRAY(%s))",(white_player,))
    gamesWhite = cur.fetchall()
    cur.execute("SELECT * FROM igre WHERE JSON_CONTAINS(igraci,JSON_ARRAY(%s))",(black_player,))
    gamesBlack = cur.fetchall()
    whitePoints = 0 
    blackPoints = 0
    # for game in gamesWhite:
    #     try:
    #         users = json.loads(game[2])
    #         white = users[1]
    #         black = users[0]
    #         thisGamesPointsWhite = 0
    #         thisGamesPointsBlack = 0
    #         for i in json.loads(game[8]):
    #             thisGamesPointsBlack += len(i[1])
    #         for i in json.loads(game[9]):
    #             thisGamesPointsWhite += len(i[1])
    #         if black == white_player:
    #             for i in json.loads(game[8]):
    #                 whitePoints += len(i[1])

    #             for i in json.loads(game[9]):
    #                 whitePoints -= len(i[1])
    #         elif white == white_player:
    #             for i in json.loads(game[9]):
    #                 whitePoints += len(i[1])

    #             for i in json.loads(game[8]):
    #                 whitePoints -= len(i[1])
    #     except:
    #         pass

    # for game in gamesBlack:
    #     users = json.loads(game[2])
    #     white = users[1]
    #     black = users[0]
    #     thisGamesPointsWhite = 0
    #     thisGamesPointsBlack = 0
    #     for i in json.loads(game[8]):
    #         thisGamesPointsBlack += len(i[1])
    #     for i in json.loads(game[9]):
    #         thisGamesPointsWhite += len(i[1])
    #     if black == black_player:
    #         for i in json.loads(game[8]):
    #             blackPoints += len(i[1])

    #         for i in json.loads(game[9]):
    #             blackPoints -= len(i[1])
    #     elif white == black_player:
    #         for i in json.loads(game[9]):
    #             blackPoints += len(i[1])

    #         for i in json.loads(game[8]):
    #             blackPoints -= len(i[1])




    # Notify both players
    emit("recieved", {
        "isBlack": False,  # White player
        "otherPlayer": adversary_data['username'],
        "whitePoints":whitePoints,
        "blackPoints":blackPoints
    }, room=player_data['sid'])

    emit("recieved", {
        "isBlack": True,  # Black player
        "otherPlayer": player_data['username'],
        "whitePoints":whitePoints,
        "blackPoints":blackPoints
    }, room=adversary_data['sid'])

    # Update game in the database
    cur.execute("""
        UPDATE igre 
        SET igraci = %s, potezi = %s, vremenaPoteza = %s, krenulo = %s 
        WHERE ID = %s
    """, (
        json.dumps([white_player, black_player]),
        json.dumps([[player_data['move'], adversary_data['move']], [[], []]]),
        json.dumps([[player_data['time'], adversary_data['time']], [0, 0]]),
        True,
        gameId
    ))
    mysql.connection.commit()
    cur.close()
    print("COMMITAO SAM")
    #make a print for the states that are being commited
    print([white_player, black_player])
    print([[player_data['move'], adversary_data['move']], [[], []]])
    print([[player_data['time'], adversary_data['time'], [0, 0]]])
    print(True)
    print(gameId)

    # Clean up state
    del firstMoves[gameId]
    exclusiveMoves[gameId] = [None,None]
    print("EXLCUSAIUHERWMAFV")
    print(exclusiveMoves)


@socketio.on("awaitAdversary")
def awaitAdversary(data):
    gameId = data.get("id")
    username = session.get("user")
    isPrivate = data.get("isPrivate").lower() == "true"
    cur = mysql.connection.cursor()
    cur.execute("START TRANSACTION")
    cur.execute("select id from users where username=%s FOR UPDATE",(username,))
    userId = cur.fetchone()[0]
    print(userId)
    temp = [userId]
    temp=str(temp)
    cur.execute("insert into igre (ID,tempIgraci,krenulo,privatna,vrijeme) values (%s,%s,%s,%s,%s)",(gameId,temp,False,isPrivate,time.time()))
    mysql.connection.commit()
    cur.close()


    global waitingGames
    gameId = data.get("id")
    name = session.get("user")
    waitingGames[gameId] = [request.sid, name]
    print(f"Korisnik {name} čeka na igrača za igru {gameId}")
    emit("ok",{"message":f"Čeka se adversary za {id}"})

@socketio.on("joinGame")
def joinGame(data):
    global waitingGames
    global exclusiveMoves
    gameId = data.get("id")
    
    if gameId in waitingGames:
        if session.get("user") == waitingGames[gameId][1]:
            return
        else:
            waitingSid = waitingGames[gameId][0]
            try:
                print(waitingSid)
            except:
                print("nema")
            emit("matched",{"message":"Adversary nazočan","isAdversary":False}, room=waitingSid)
            emit("matched",{"message":"Postao adversary","isAdversary":True})

        
@socketio.on("disconnect")
def disconnect():
    for gameId, sid in list(waitingGames.items()):
        if sid == request.sid:
            del waitingGames[gameId]
            break

@app.context_processor
def contextProccesingInjection():
    return {"marquee":["Ne sufinancira EU","©2025 Nijedna prava pridržana","α 0.4.6 AB",]}

def genRandomString():
    return ''.join(random.choices(string.ascii_lowercase + string.digits, k=6))

@app.errorhandler(Exception)
def errorHandler(e):
    if isinstance(e,Exception):
        print(e)
        #if is not pyhton error
        

        print(traceback.format_exc())
        print("""#####
#####
#####
ERROR
#####
#####
#####""")

    descs = {
        500:"Ups! Napravili smo grešku.",
        404:"Stranica koju tražite ne postoji."
    }
    if hasattr(e,"code"):
        return render_template("error.html",error=e.code,errorDescription=descs[e.code])
    else:
        return render_template("error.html",error=500,errorDescription=descs[500])
    

def register(username,password):
    if len(username) > 16 or len(username) < 4:
        return "name"
    cur = mysql.connection.cursor()
    cur.execute("SELECT * FROM users WHERE username = %s",(username,))
    
    user = cur.fetchone()
    print(user)
    if user is not None:
        user = user[0]
        
        print("AVLA")
        print()
        cur.close()
        return "over"
    else:
        try:

            cur.execute("INSERT INTO users (username,password) VALUES (%s, %s)",(username, generate_password_hash(password)))
            mysql.connection.commit()
            cur.close()
            return True
        
        except:
            return False

def login(username,password):
    try:
        cur = mysql.connection.cursor()
        cur.execute("SELECT password,theme FROM users WHERE username = %s ",(username,))
        print(username,password)
        user = cur.fetchone()
        print("sada ide user")
        print(user,"OVO JE USER")
        if user and check_password_hash(user[0], password):
            return [True,user[1]]
        else:
            return [False]
    except Exception as e:
        print(e)
        return ["error"]

@app.route("/review/<id>")
def reviewPage(id):
    #+---------------+--------------+------+-----+---------+-------+
#| Field         | Type         | Null | Key | Default | Extra |
#+---------------+--------------+------+-----+---------+-------+
#| ID            | varchar(255) | NO   | PRI | NULL    |       |
#| tempIgraci    | json         | YES  |     | NULL    |       |
#| igraci        | json         | YES  |     | NULL    |       |
#| vrijeme       | timestamp    | YES  |     | NULL    |       |
#| potezi        | json         | YES  |     | NULL    |       |
#| vremenaPoteza | json         | YES  |     | NULL    |       |
#| krenulo       | tinyint(1)   | YES  |     | NULL    |       |
#| privatna      | tinyint(1)   | YES  |     | NULL    |       |
#| crnaPolja     | json         | YES  |     | NULL    |       |
#| bijelaPolja   | json         | YES  |     | NULL    |       |
#| pobjednik     | int          | YES  |     | NULL    |       |
#| DIDSS         | tinyint(1)   | YES  |     | NULL    |       |
#| regije        | json         | YES  |     | NULL    |       |
#+---------------+--------------+------+-----+---------+-------+
    cur = mysql.connection.cursor()
    cur.execute("SELECT * FROM igre WHERE ID = %s",(id,))
    game = cur.fetchone()
    print(game)
    print("OVOJE GAME")
    if game:
        if game[10] != None:
            print(game)
            users = json.loads(game[2])
            white = users[1]
            black = users[0]
            print(white,black)
            print("CRVCRN")
            white = cur.execute("SELECT username FROM users WHERE id = %s",(white,))
            white = cur.fetchone()[0]
            black = cur.execute("SELECT username FROM users WHERE id = %s",(black,))
            black = cur.fetchone()[0]
            moves = json.loads(game[4])
            times = json.loads(game[5])
            whiteSpaces = json.loads(game[9])
            blackSpaces = json.loads(game[8])
            return render_template("review.html",id=id,white=white,black=black,moves=moves,times=times,whiteSpaces=whiteSpaces,blackSpaces=blackSpaces)
        else:
            print("neamg a")
            return abort(404)
    else:
        return abort(404)
   


@app.route("/image/<username>")
def showImage(username):
    cur = mysql.connection.cursor()
    cur.execute("SELECT profile FROM users WHERE username = %s",(username,))
    imageData = cur.fetchone()[0]
    
    if imageData is None:
        print("ii ništa")
        return send_file(os.getenv("STATIC_FOLDER")+"/default"+str(randint(0,1))+".png",mimetype="image/png")
    else:
        print("paa nije ništa")
        return send_file(io.BytesIO(imageData), mimetype='image/png')

@app.route("/user/profile/<username>")
def userProfile(username):
    global fiirstN
    cur = mysql.connection.cursor()
    cur.execute("SELECT ID FROM users WHERE username = %s",(username,))
    userId = cur.fetchone()[0]
    points = 0
    cummulative = 0
    print(userId)
    timezone = pytz.timezone(session.get("timezone","UTC"))

    if userId:
        cur.execute("SELECT * FROM igre WHERE JSON_CONTAINS(igraci,JSON_ARRAY(%s)) ORDER BY vrijeme DESC",(userId,))
        games = cur.fetchall()
        gamesToSend = []
        applicableGames = 0
        firstN = fiirstN
        for game in games:
            try:
                
                doNotAppend = False
                time = datetime.utcfromtimestamp(int(game[3]))
                local_time = time.astimezone(timezone)
                time = local_time.strftime("%H:%M %d.%m.%Y")
                #time = float(game[3])  # Convert to float to ensure compatibility
                # Convert server time to local time using javascript on client side
                formattedTime = time# datetime.datetime.fromtimestamp(time).strftime("%d.%m.%Y %H:%M")
                users = json.loads(game[2])
                white = users[1]
                black = users[0]
                thisGamesPointsWhite = 0
                thisGamesPointsBlack = 0

                for i in json.loads(game[8]):
                    thisGamesPointsBlack += len(i[1])
                for i in json.loads(game[9]):
                    thisGamesPointsWhite += len(i[1])
                if thisGamesPointsBlack == 0 and thisGamesPointsWhite == 0:
                    #print("nema bodova")
                    doNotAppend = True
                else:
                    #print("ima bodova")
                    applicableGames +=1
                if not doNotAppend and fiirstN > 0:
                    if black == userId:
                        for i in json.loads(game[8]):

                            points += len(i[1]) if firstN > 0 else 0
                            cummulative += len(i[1])
                        for i in json.loads(game[9]):
                            points -= len(i[1]) if firstN > 0 else 0
                    elif white == userId:
                        for i in json.loads(game[9]):
                            points += len(i[1]) if firstN > 0 else 0
                            cummulative += len(i[1])
                        for i in json.loads(game[8]):
                            points -= len(i[1]) if firstN > 0 else 0
                    firstN -= 1
                    #print(firstN)
                whitee = cur.execute("SELECT username FROM users WHERE id = %s",(white,))
                whitee = cur.fetchone()[0]
                blackk = cur.execute("SELECT username FROM users WHERE id = %s",(black,))
                blackk = cur.fetchone()[0]
                winner = whitee if game[10] == white else blackk

                
                gamesToSend.append({"id":game[0],"white":whitee,"black":blackk,"winner":winner, "time":time, "score": str(thisGamesPointsWhite)+"-"+str(thisGamesPointsBlack)})
            except Exception as e:
                #print(e)
                pass
    #sort gamesToSend by time
    #gamesToSend = sorted(gamesToSend,key=lambda x: x["time"],reverse=True)
   # for game in gamesToSend:
        #game["time"] = datetime.datetime.fromtimestamp(game["time"]).strftime("%d.%m.%Y %H:%M")
    try: 
        
        print(points,"SU BODOVI")
        print("APLIKABLO GEMASTOJSEND",applicableGames)
        #print(applicableGames)
        print("TO JE LEN GEMASTOJSEND")
        print(min(fiirstN,applicableGames))
        
        points = points/min(fiirstN,applicableGames)
        print("Igrač",username,"ima",points,"bodova.")
        points += 18
        print(points)
        
    except:
        points = 0
    
    points = round(points,2)
    points = min(36,points)
    points = max(0,points)
    print(points)
    #print(gamesToSend)
        
    return render_template("profile.html",username=username,games=gamesToSend,points=points,cummulative=cummulative,firstN=fiirstN)

@app.route("/eula")
def eulaPage():
    return render_template("eula.html")

@app.route("/logout")
def logOut():
    session.clear()
    return redirect(url_for("indexPage"))

@app.route("/auth",methods=["POST"])
def auth():
    username = request.form.get("username")
    password = request.form.get("password")
    action = request.form.get("action")
    eula = request.form.get("eula")
    timezone = request.form.get("timezone")
    if action == "register":
        reg = register(username,password)

        if eula != "on":
            return render_template("login.html",error="Prihvatite uvjete da biste nastavili.")
        elif reg == "over":
            return render_template("login.html",error="Ime već zauzeto.")
        elif reg == "name":
            return render_template("login.html",error="Ime mora imati između 4 i 24 znakova.")
        elif not reg:
            return abort(500)
        elif reg and eula == "on":
            session["user"] = username
            session["timezone"] = timezone
            session["theme"] = "dark"

            return redirect(url_for("indexPage"))
    elif action == "login":
        log = login(username,password)
        if log[0]:
            session["user"] = username
            session["timezone"] = timezone
            print(log)
            print("OVO JE LOG")
            session["theme"] = log[1]
            return redirect(url_for("indexPage"))
        elif not log[0]:
            return render_template("login.html",error="Pogrešno ime ili lozinka.")
        else:
            return render_template("login.html",error="Unutarnja greška.")

@app.route("/editprofile",methods=["POST"])
def editProfilePOST():
    username = request.form.get("originalUsername")
    newUsername = request.form.get("username")
    password = request.form.get("password")
    theme = request.form.get("theme")

    cur = mysql.connection.cursor()
    print(session["user"])
    print(request.form.get("removeProfilePicture"))
    
        
    if username != newUsername:
        print("OVO JE NOVI USERNAME")
        print("ČOVJEK IMA NOVI USERNAME")
        print(newUsername)
        cur.execute("select username from users where username = %s",(newUsername,))
        asd = cur.fetchone()
        
        
        print(asd)
        #print(newUsername == asd[0])
        print("EVAL")
        
        if asd is not None:
            print("OVO JE ASDD")
            print(asd)
            return render_template("edit.html",error="Korisnik s tim imenom već postoji.")



    try:
        session.clear()
        session["user"] = newUsername
        session["theme"] = theme
        print(theme)
        print("OVO JE THEME")
        image = request.form.get("profilePictureData")

        if image.startswith("data:image"):
            image = image.split(',')[1]
        imageData = base64.b64decode(image)
        print("izbjegao sam raise")
        imagee = Image.open(BytesIO(imageData))
        width, height = imagee.size
        if width+height > 0:
            
            cur.execute("SELECT * FROM users WHERE username = %s",(username,))
            user = cur.fetchone()

            if user and check_password_hash(user[1],password):
                if request.form.get("removeProfilePicture") == "on": cur.execute("update users set profile = %s where username = %s",(None,newUsername,))
                print(f"{username} (sada {newUsername}) je stavio profilnu")
                
                cur.execute("update users set username=%s, password=%s, profile=%s, theme=%s where username=%s",(newUsername,generate_password_hash(password),imageData,theme,username))
                mysql.connection.commit()
                cur.close()
                return redirect(url_for("userProfile",username=username))
            else:
                print(width,height,"SKROZ KRIVO")
                return render_template("edit.html",error="Molimo probajte ponovno.")
        else:
            print(width,height,"SLIKA GLUPA")
            return render_template("edit.html",error="Slika krivih veličina.")
    except Exception as e:

        print(e)
        cur = mysql.connection.cursor()
        cur.execute("SELECT * FROM users WHERE username = %s",(username,))
        user = cur.fetchone()

        if user and check_password_hash(user[1],password):
            print("DA TO EJT O")
            if request.form.get("removeProfilePicture") == "on": cur.execute("update users set profile = %s where username = %s",(None,newUsername,))
            cur.execute("update users set username=%s where username=%s",(newUsername,username))
            mysql.connection.commit()
            cur.close()
            return redirect(url_for("userProfile",username=newUsername))
        else:
            return render_template("edit.html",error="Korisnik s tim imenom već postoji.")

@app.route("/game/<id>")
def gamePage(id):
    global waitingGames
    if session.get("user"): 
        print(waitingGames)
        print(id)
        print("OVO JE ID")
        if id in waitingGames:
            print(waitingGames)
            print("da tu je")
            print(waitingGames[id])
            print("TO JE ID")
            if waitingGames[id] == "g":
                waitingGames[id] = "v"
                return render_template("kontranto.html",id=id)
            if waitingGames[id] == "v":
                print("OVO JE V")
                del waitingGames[id]
                return render_template("kontranto.html",id=id)
            else:
                waitingGames[id] = "v"
                return render_template("kontranto.html",id=id)
            
        else:
            print(f"nema {id} u waitingGames")
            return redirect(url_for("indexPage"))
    else: return render_template("login.html",error="Ulogirajte se da biste igrali.")

def startGame(username,isPrivate,bot=False):
    id = genRandomString()

    return id

@app.route("/createPrivate")
def privateGame():
    global waitingGames
    if session.get("user"): 
        id = startGame(session["user"],isPrivate=True,bot=False)
        waitingGames[id] = "g"
        print(waitingGames)
        print("NAPRAVIO SAM CPRAIVET GAME")
        return render_template("wait.html",id=id,isPrivate=True)
    else: return render_template("login.html",error="Ulogirajte se da biste igrali.")


@app.route("/public")
def publicSelection():
    lock = threading.Lock()
    with lock:
        try:
            cur = mysql.connection.cursor()
            cur.execute("START TRANSACTION")
            cur.execute("select id,tempIgraci from igre where privatna=0 and krenulo=0 FOR UPDATE")
            fetch = cur.fetchone()
            try:
                
                print(fetch)
                games = fetch[0]
                players = fetch[1]
                print(games)
                print(players)
            except:
                print("neradi")
            

        
            cur.execute("select id from users where username=%s",(session["user"],))
            playerId = cur.fetchone()[0]
            print(playerId,"OVO JE ID")

            
            
            if fetch == None:
                    if session.get("user"): 
                        id = startGame(session["user"],isPrivate=False,bot=False)
                        
                        return render_template("wait.html",id=id,isPrivate=False)
                    else: return render_template("login.html",error="Ulogirajte se da biste igrali.")
            
            print(playerId)
            print(players)
            print("TO SU ONi")
            cur.execute("update igre set krenulo=1 where id=%s",(games,))
            mysql.connection.commit()
            cur.close()
            if playerId in json.loads(players):
                return render_template("login.html",error="Već ste u igri.")

            socketio.emit("matched",{"message":"Adversary nazočan","isAdversary":False},room=waitingGames[games][0])
            return redirect(url_for("gamePage", id=games))
        except Exception as e:
            print(e)
            print("PUBLIC SELECTION RACE CONDITION")
            mysql.connection.rollback()
            return abort(500)

@app.route("/createPublic")
def publicGame():
    if session.get("user"): 
        id = startGame(session["user"],isPrivate=False,bot=False)
        return render_template("wait.html",id=id,isPrivate=False)
    else: return render_template("login.html",error="Ulogirajte se da biste igrali.")


@app.route("/private")
def privateSelection():
    return render_template("private.html")

@app.route("/cancel/<id>")
def cancelGame(id):
    if session.get("user"):
        cur = mysql.connection.cursor()
        cur.execute("select krenulo from igre where id=%s",(id,))
        ax = cur.fetchone()
        if ax == None:
            return redirect(url_for("matchMaking"))
        if not ax[0]:
            cur.execute("delete from igre where id=%s",(id,))
            mysql.connection.commit()
            cur.close()
        else:
            return redirect(url_for("indexPage"))
        return redirect(url_for("matchMaking"))
    else: return render_template("login.html",error="Ulogirajte se.")


def getPointsofPlayer(username):
    global fiirstN
    firstN = fiirstN
    cur = mysql.connection.cursor()
    cur.execute("SELECT ID FROM users WHERE username = %s",(username,))
    userId = cur.fetchone()[0]
    points = 0
    cur.execute("SELECT * FROM igre WHERE JSON_CONTAINS(igraci,JSON_ARRAY(%s))",(userId,))
    games = cur.fetchall()
    acculumate = 0
    for game in games:
        try:
            if firstN == 0:
                break
            users = json.loads(game[2])
            white = users[1]
            black = users[0]

            if black == userId:

                for i in json.loads(game[8]):
                    points += len(i[1])
                    acculumate += len(i[1])
                for i in json.loads(game[9]):
                    points -= len(i[1])
            elif white == userId:
                for i in json.loads(game[9]):
                    acculumate += len(i[1])
                    points += len(i[1])
                for i in json.loads(game[8]):
                    points -= len(i[1])
            firstN -= 1
        except: pass
    try: 
        points = points/min(firstN,len(games))
        points += 18
    except:
        points = 0
    
    points = round(points,2)
    points = min(36,points)
    points = max(0,points)
    return [points,acculumate,len(games)]

@app.route("/leaderboard")
def leaderboard():
    cur = mysql.connection.cursor()
    cur.execute("SELECT username FROM users")
    users = cur.fetchall()
    print(users)
    print("USERS")
    leaderboard = []
    for user in users:
        points = getPointsofPlayer(user[0])
        print(points)
        print("POINTS")
        leaderboard.append({"username":user[0],"points":points[0],"cummulative":points[1],"games":points[2]})
    leaderboard = sorted(leaderboard,key=lambda x: x["points"],reverse=True)
    return render_template("leaderboard.html",leaderboard=leaderboard)


@app.route("/reviewimage/<id>")
def reviewImage(id):
    cur = mysql.connection.cursor()
    cur.execute("SELECT * FROM igre WHERE ID = %s",(id,))
    game = cur.fetchone()
    if not game:
        return abort(404)
    
    players = json.loads(game[2])
    white = players[1]
    black = players[0]
    cur.execute("SELECT profile FROM users WHERE id = %s",(white,))
    
    imageData = cur.fetchone()[0]
    
    if imageData is None:
        print("ii ništa")
        imageData = os.getenv("STATIC_FOLDER")+"/default"+str(randint(0,1))+".png"
    else:
        print("paa nije ništa")
        imageData = io.BytesIO(imageData)
    left_image = Image.open(imageData)
    cur.execute("SELECT profile FROM users WHERE id = %s",(black,))

    imageData = cur.fetchone()[0]
    if imageData is None:
        print("ii ništa")
        imageData = os.getenv("STATIC_FOLDER")+"/default"+str(randint(0,1))+".png"
    else:
        print("paa nije ništa")
        imageData = io.BytesIO(imageData)
    right_image = Image.open(imageData)
    cur.execute("SELECT username FROM users WHERE id = %s",(white,))
    white = cur.fetchone()[0]
    cur.execute("SELECT username FROM users WHERE id = %s",(black,))
    black = cur.fetchone()[0]
    whitePoints = 0
    blackPoints = 0
    for whiteSpace in json.loads(game[9]):
        if whiteSpace[1] != []:
            whitePoints += len(whiteSpace[1])
    for blackSpace in json.loads(game[8]):
        if blackSpace[1] != []:
            blackPoints += len(blackSpace[1])
    formatted_time = datetime.utcfromtimestamp(int(game[3])+3600).strftime("%H:%M %d.%m.%Y")

    
    
    cur.close()

    
    
    box_size = (100, 100)  # Desired size for images


    # Create a blank canvas
    width, height = 512, 320 # Canvas dimensions
    canvas = Image.new("RGB", (width, height), "#111111")

    # Load the font (adjust the path as necessary)
    font_large = ImageFont.truetype("/usr/share/fonts/truetype/msttcorefonts/times.ttf", size=40)  # Large text
    font_medium = ImageFont.truetype("/usr/share/fonts/truetype/msttcorefonts/times.ttf", size=30)  # Medium text
    font_small = ImageFont.truetype("/usr/share/fonts/truetype/msttcorefonts/times.ttf", size=20)  # Small text

    # Create a drawing object
    draw = ImageDraw.Draw(canvas)

    # Add main title
    draw.text((width // 2, 50), id, font=font_large, fill="#aaaaaa", anchor="mm")

    # Add subtitle
    draw.text((width // 2, 100), formatted_time, font=font_medium, fill="#aaaaaa", anchor="mm")

    # Draw the left image and its dynamic text
    left_x = width // 4 - 100 // 2
    left_y = 200
    draw.text((left_x + 100 // 2, left_y - 30), white, font=font_small, fill="#aaaaaa", anchor="mm")
    canvas.paste(left_image, (left_x, left_y), mask=left_image)

    # Draw the right image and its dynamic text
    right_x = 3 * width // 4 - 100 // 2
    right_y = 200
    draw.text((right_x + 100 // 2, right_y - 30), black, font=font_small, fill="#aaaaaa", anchor="mm")
    canvas.paste(right_image, (right_x, right_y), mask=right_image)

    # Draw the centered text
    #draw.text((width // 2, left_y + left_image.height // 2), "<- they should be aligned ->", font=font_small, fill="#aaaaaa", anchor="mm")
    # Draw the score
    draw.text((width // 2, 250), f"{whitePoints} - {blackPoints}", font=font_large, fill="#aaaaaa", anchor="mm")

    # Convert canvas to bytes
    image_bytes = BytesIO()
    canvas.save(image_bytes, format='PNG')
    image_bytes.seek(0)

    return send_file(image_bytes, mimetype='image/png')
    # Save the image to a BytesIO object
    #image_io = BytesIO()
    #canvas.save(image_io, format="PNG")  # Save as PNG
    #image_io.seek(0)
  
#@app.route("/joinPrivate",methods=["POST"])
def joinPrivateGame():
    #TODO: napravi ovo
    id = request.form.get("gameId")
    cur = mysql.connection.cursor()
    cur.execute("select from ")


@app.route("/play")
def matchMaking():
    if session.get("user"): return render_template("matchmaking.html")
    else: return render_template("login.html",error="Ulogirajte se da biste igrali.")

@app.route("/edit")
def editProfile():
    if session.get("user"): return render_template("edit.html")
    else: return render_template("login.html",error="Ulogirajte se.")



@app.route("/about")
def aboutPage():
    return render_template("about.html")        

@app.route("/login")
def loginPage():
    return render_template("login.html")

@app.route("/")
def indexPage():
    return render_template("index.html")



if __name__ == "__main__":
    socketio.run(app,host="127.0.0.1",port="25565", debug=True,)




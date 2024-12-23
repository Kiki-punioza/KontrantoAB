from flask import Flask, render_template,redirect,request, session, url_for, abort, send_file # type: ignore
from flask_mysqldb import MySQL # type: ignore
from werkzeug.security import generate_password_hash, check_password_hash # type: ignore
from random import randint
from flask_socketio import SocketIO, emit, join_room, leave_room # type: ignore
import io
import base64
from io import BytesIO
from PIL import Image
import random
import string
import json
import time
import numpy as np
from scipy.ndimage import label
import copy
import math
from itertools import product
from functools import wraps
from multiprocessing import Pool, cpu_count
from re import search
from collections import defaultdict


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
        #print(f"Broj koraka bez sudara prije izvanrednog koraka: {np.count_nonzero(labeledGrid == i)}")
        #print(f"U slučaju izvanrednog sudara bijeli dobiva odabir/e {[g[:1]+g[1+1:] for g in pieceRegions if g[1] == i and g[0].islower()]}")
        #print(f"U slučaju izvanrednog sudara  crni  dobiva odabir/e {[g[:1]+g[1+1:] for g in pieceRegions if g[1] == i and g[0].isupper()]}")
        #print() 
    del regions["0"]
    print(regions)
    print("TO SU REGIJE")
    return regions


import os
from dotenv import load_dotenv

app = Flask(__name__, template_folder=os.getenv('TEMPLATE_FOLDER'), static_folder=os.getenv('STATIC_FOLDER'),)
app.secret_key = os.getenv("SECRET_KEY")

app.config["MYSQL_HOST"] = os.getenv("MYSQL_HOST")
app.config["MYSQL_USER"] = os.getenv("MYSQL_USER")
app.config["MYSQL_PASSWORD"] = os.getenv("MYSQL_PASSWORD")
app.config["MYSQL_DB"] = os.getenv("MYSQL_DB")

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
        game = startGame(session.get("user"),isPrivate=False)
        del awaitingRevenge[id]
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


@socketio.on("submitMoves")
def submitMoves(data):
   
    id = data.get("id")
    isBlack = data.get("isBlack")
    moves = data.get("moves")
    time = data.get("time")
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
    
    
    cur.execute("update igre set potezi=%s, vremenaPoteza=%s where id=%s",(json.dumps(potezi),json.dumps(vremenaPoteza),id))

    mysql.connection.commit()
    if potezi[-1][int(not isBlack)] == []:
            
            #print(f"{isBlack} je prvi napravio potez")
            #ako smo mi prvi napravili potez
            emit("waiting",{"whoIsDone":isBlack},to=id)

            
    else:   
            
            player1_moves = potezi[-1][0]
            player2_moves = potezi[-1][1]
            white_spaces = []
            black_spaces = []

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
            cur.execute("SELECT regije FROM igre WHERE id=%s", (id,))
            row = cur.fetchone()
            dbRegions = json.loads(row[0]) if row and row[0] else {}
            localRegions = computeRegions(grid)


            if not dbRegions:
                print("nema regija")
                regionsToSubmit = localRegions
            else:
                for key,value in dbRegions.items():
                    if value[0] == 0:
                        for piece in value[2]:
                            if piece[0].islower():
                                exclusiveMove[0].append(piece[1])
                            else:
                                exclusiveMove[1].append(piece[1])
                        del dbRegions[key]
                        print("palo je na 0")
                print(value[0])
                value[0] -= 1
                print(value[0])
                print("ovo je value")
                print(value[2])
                print(localRegions[key][2])
                print("to su stvari")
                if value[2] == localRegions[key][2]:
                        for piece in value[2]:
                            if piece[0].islower():
                                exclusiveMove[0].append(piece[1])
                            else:
                                exclusiveMove[1].append(piece[1])
                        del dbRegions[key]
                        print("nema pomicanja u regiji")
                else:
                    print("nisu isti")

                localRegions.update(dbRegions)
                regionsToSubmit = localRegions


            print(regionsToSubmit)
            print(exclusiveMove)
            print("TO SU REGIJEEEE")



            
            
            

            # Save dbRegions
            cur.execute("UPDATE igre SET regije=%s WHERE id=%s", (json.dumps(regionsToSubmit), id))
            mysql.connection.commit()

            for i in bijelaPolja:
                if i[1] != []:
                    brojBijelih += len(i[1])
            for i in crnaPolja:
                if i[1] != []:
                    brojCrnih += len(i[1])
            #print(white_spaces)
            #print(black_spaces)
            #print(len(potezi)-1)
            #print(bijelaPolja)
            #print(crnaPolja)
            #print(brojBijelih,brojCrnih)
            #print("TO SU BIJELI I DESNI")
            if brojBijelih > 17 and brojCrnih < 17:
                cur.execute("update igre set pobjednik=%s where id=%s",(igraci[0],id))
                mysql.connection.commit()
                emit("gameOver",{"loserIsBlack":True,"reason":"spaces"},to=id)
            elif brojCrnih > 17 and brojBijelih < 17:
                cur.execute("update igre set pobjednik=%s where id=%s",(igraci[1],id))
                mysql.connection.commit()
                emit("gameOver",{"loserIsBlack":False,"reason":"spaces"},to=id)
            if exclusiveMove != [[] , []]:
                print("O MOJ BOŽE IZVANREDNI POTEZ")
            #emit("ok",{"moves":potezi[-1]},to=id)
            emit("ok",{"moves":potezi[-1],"whiteTaken":white_spaces,"blackTaken":black_spaces,"exclusiveMove":[exclusiveMove[0],exclusiveMove[1]]},to=id)
            #ovaj je već gotov
            potezi.append([[],[]])
            vremenaPoteza.append([0,0])
            vremenaPoteza = json.dumps(vremenaPoteza)
            potezi = json.dumps(potezi)  
            bijelaPolja = json.dumps(bijelaPolja)
            crnaPolja = json.dumps(crnaPolja)
            cur.execute("update igre set potezi=%s, crnaPolja=%s, bijelaPolja=%s, vremenaPoteza=%s where id=%s",(potezi,crnaPolja,bijelaPolja,vremenaPoteza,id))
            mysql.connection.commit()


firstMoves = {}

@socketio.on("firstMove")
def firstMove(data):
    global firstMoves
    gameId = data.get("id")
    move = data.get("move")
    isAdversary = data.get("isAdversary")
    moveTime = data.get("moveTime")
    username = session.get("user")
    cur = mysql.connection.cursor()

    # Ensure firstMoves entry exists for this game
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

    # Notify both players
    emit("recieved", {
        "isBlack": False,  # White player
        "otherPlayer": adversary_data['username']
    }, room=player_data['sid'])

    emit("recieved", {
        "isBlack": True,  # Black player
        "otherPlayer": player_data['username']
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

    # Clean up state
    del firstMoves[gameId]


@socketio.on("awaitAdversary")
def awaitAdversary(data):
    
    global waitingGames
    gameId = data.get("id")
    name = session.get("user")
    waitingGames[gameId] = [request.sid, name]
    emit("ok",{"message":f"Čeka se adversary za {id}"})

@socketio.on("joinGame")
def joinGame(data):
    global waitingGames
    gameId = data.get("id")
    if gameId in waitingGames:
        if session.get("user") == waitingGames[gameId][1]:
            return
        else:
            waitingSid = waitingGames.pop(gameId)[0]
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
        e = 500
    descs = {
        500:"Ups! Napravili smo grešku.",
        404:"Stranica koju tražite ne postoji."
    }
    return render_template("error.html",error=e,errorDescription=descs[e])
    

def register(username,password):
    if len(username) > 24 or len(username) < 4:
        return "name"
    cur = mysql.connection.cursor()
    cur.execute("SELECT * FROM users WHERE username = %s",(username,))
    user = cur.fetchone()
    if user:
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
        cur.execute("SELECT password FROM users WHERE username = %s ",(username,))
        print(username,password)
        user = cur.fetchone()
        print("sada ide user")
        print(user,"OVO JE USER")
        if user and check_password_hash(user[0], password):
            return True
        else:
            return False
    except Exception as e:
        print(e)
        return "error"

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
    return render_template("profile.html",username=username)

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
    if action == "register":
        reg = register(username,password)
        if reg and eula == "on":
            session["user"] = username
            return redirect(url_for("indexPage"))
        elif eula != "on":
            return render_template("login.html",error="Prihvatite uvjete da biste nastavili.")
        elif reg == "over":
            return render_template("login.html",error="Ime već zauzeto.")
        elif reg == "name":
            return render_template("login.html",error="Ime mora imati između 4 i 24 znakova.")
        elif not reg:
            return abort(500)
    elif action == "login":
        log = login(username,password)
        if log:
            session["user"] = username
            return redirect(url_for("indexPage"))
        elif not log:
            return render_template("login.html",error="Pogrešno ime ili lozinka.")
        else:
            return render_template("login.html",error="Unutarnja greška.")

@app.route("/editprofile",methods=["POST"])
def editProfilePOST():
    username = request.form.get("originalUsername")
    newUsername = request.form.get("username")
    password = request.form.get("password")
    session.clear()
    session["user"] = newUsername
    cur = mysql.connection.cursor()
    print(session["user"])
    print(request.form.get("removeProfilePicture"))
    
        
    if username != newUsername:
        
        cur.execute("SELECT * from users where username = %s",(newUsername,))
        if cur.fetchone():
            return render_template("edit.html",error="Korisnik s tim imenom već postoji.")
    try:
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
                
                cur.execute("update users set username=%s, password=%s, profile=%s where username=%s",(newUsername,generate_password_hash(password),imageData,username))
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
    if session.get("user"): return render_template("kontranto.html",id=id)
    else: return render_template("login.html",error="Ulogirajte se da biste igrali.")

def startGame(username,isPrivate,bot=False):
    id = genRandomString()
    cur = mysql.connection.cursor()
    cur.execute("select id from users where username=%s",(username,))
    userId = cur.fetchone()[0]
    print(userId)
    temp = [userId]
    if bot != False:
        temp = [userId,bot]
    temp=str(temp)
    cur.execute("insert into igre (ID,tempIgraci,krenulo,privatna,vrijeme) values (%s,%s,%s,%s,%s)",(id,temp,False,isPrivate,time.time()))
    mysql.connection.commit()
    cur.close()
    return id

@app.route("/createPrivate")
def privateGame():
    if session.get("user"): 
        id = startGame(session["user"],isPrivate=True,bot=False)
        return render_template("wait.html",id=id,isPrivate=True)
    else: return render_template("login.html",error="Ulogirajte se da biste igrali.")


@app.route("/public")
def publicSelection():
    cur = mysql.connection.cursor()
    cur.execute("START TRANSACTION")
    cur.execute("select id,tempIgraci from igre where privatna=0 and krenulo=0")
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
        return redirect(url_for("publicGame"))
    
    print(playerId)
    print(players)
    print("TO SU ONi")
    if playerId in json.loads(players):
        return render_template("login.html",error="Već ste u igri.")
    cur.execute("update igre set krenulo=1 where id=%s",(games,))
    mysql.connection.commit()
    cur.close()
    socketio.emit("matched",{"message":"Adversary nazočan","isAdversary":False},room=waitingGames[games])
    return redirect(url_for("gamePage", id=games))

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
        if not cur.fetchone()[0]:
            cur.execute("delete from igre where id=%s",(id,))
            mysql.connection.commit()
            cur.close()
        else:
            return redirect(url_for("indexPage"))
        return redirect(url_for("matchMaking"))
    else: return render_template("login.html",error="Ulogirajte se.")


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
    socketio.run(app,host="0.0.0.0",port="25565", debug=True,)




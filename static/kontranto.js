


 // _    _ _____   ____ __________  _____   ____  _____  ______ _   _      _ ______ _ _ 
 //| |  | |  __ \ / __ \___  / __ \|  __ \ / __ \|  __ \|  ____| \ | |    | |  ____| | |
 //| |  | | |__) | |  | | / / |  | | |__) | |  | | |__) | |__  |  \| |    | | |__  | | |
 //| |  | |  ___/| |  | |/ /| |  | |  _  /| |  | |  _  /|  __| | . ` |_   | |  __| | | |
 //| |__| | |    | |__| / /_| |__| | | \ \| |__| | | \ \| |____| |\  | |__| | |____|_|_|
 // \____/|_|     \____/_____\____/|_|  \_\\____/|_|  \_\______|_| \_|\____/|______(_|_)
 //
 //
 // sve ove funkcije su samo za PRVI KORAK!!!
 // treba smisliti GENERALIZIRANE FUNKCIJE PRIDONOŠENJA KORAKA KONTRANTU, k?
 // 
 //_______ ____  _____   ____  
 //|__   __/ __ \|  __ \ / __ \ 
 //   | | | |  | | |  | | |  | |
 //   | | | |  | | |  | | |  | |
 //   | | | |__| | |__| | |__| |
 //   |_|  \____/|_____/ \____/ 
 //                      
 // osmisliti način da igra zapravo radi ?!?!?=I!#?=!#?!#"?)!" 
 //        
 // GFPKK ^
 // popraviti svg figura (nisu centrirane)
 // timer za oba igrača koji se može zaustavit i započet na neki emit od glavnog hivemind servera 
 // (kad ADVERSARY pošalje pokret da na MOM ekranu stanje NJEGOV timer)
 //
 // IZVANREDNI KORAK I DIDSS!!!
 // zapravo napravit igru
 // to je to :>                             

 vrijeme1 = new Date();

 const socket = io()

 const gameId = "{{ id }}";
 console.log(gameId);
 const isAdversary = localStorage.getItem('isAdversary');
 console.log(isAdversary);
 let  circle  =  document.     getElementById("circle")   ;
 let triangle =  document.    getElementById("triangle")  ;
 let  button  =  document.  getElementById("confirmFirst");

 let selectedPiece;
 let moves = [[-2,-2,-2,-2],[-2,-2,-2,-2]];
 let whitePlayer;
 let blackPlayer;
 let selected;
 
 circle.addEventListener('click', () => {
    circle.   innerHTML   =    '<circle cx="50" cy="50" r="47" stroke="black" stroke-width="3" fill="#ccc" />'   ;
   triangle.  innerHTML   =    '<polygon points="50,3 97,97 3,97" stroke="black" stroke-width="3" fill="grey" />';

   selected = 0;
   button.disabled = false;
   button.innerHTML = '✅';

 });


 triangle.addEventListener('click', () =>{
    circle.   innerHTML   =    '<circle cx="50" cy="50" r="47" stroke="black" stroke-width="3" fill="grey" />'   ;
   triangle.  innerHTML   =    '<polygon points="50,3 97,97 3,97" stroke="black" stroke-width="3" fill="#ccc" />';

   selected = 1;
   button.disabled = false;
   button.innerHTML = '✅';



 });


 button.addEventListener('click', () => {
   // TODO: napravti igur
   vrijeme2 = new Date();
   var selectedElement;
   socket.emit("firstMove",{"id":gameId,"move":selected,"isAdversary":isAdversary,"moveTime":Math.round(vrijeme2 - vrijeme1)})
   
   console.log("kliknuo njesra");
   socket.on("recieved", (data) => {

     

     vrijeme2 = new Date();
     console.log("MEČAO")
     console.log(data.isBlack);
     const isBlack = data.isBlack;
     socket.emit("listenIn",{"id":gameId,"isBlack":isBlack});
     var timerLeft = { value: 0, isRunning: true };
     var timerRight = { value: 0, isRunning: true };

     function formatTime(seconds) {
     const minutes = Math.floor(seconds / 60);
     const remainingSeconds = seconds % 60;
     return `${String(minutes).padStart(2, "0")}:${String(remainingSeconds).padStart(2, "0")}`;
}

     function startTimer(timer) {
 if (!isRunning) {
   isRunning = true;
   timer = setInterval(() => {
     timer.value++;
     
     //UPDATEANJE TIMERA?!

   }, 1000);
 }
}

     function stopTimer(timer) {
 if (timer.isRunning) {
   clearInterval(timer);
   timer.isRunning = false;
 }
}


    // ovo tu služi za kad je drugi gotov, izašao ili predao se

     var illegalMoves = isBlack ? ["7", "8", "9", "14", "15", "16", "21", "22", "23"] :
                                  ["11", "12", "13", "18", "19", "20", "25", "26", "27"];
     var isFirstMove = true;
     var allowedMoves;
     var a = 0;

     

     blackPlayer = isBlack ? "{{ session['user'] }}" : data.otherPlayer;
     whitePlayer = isBlack ? data.otherPlayer : "{{ session['user'] }}";
     const  K  =   `
 <svg height="76" class="piece black" width="76" xmlns="http://www.w3.org/2000/svg" id="circle">
   <circle cx="38" cy="38" r="35" stroke="white" stroke-width="3" fill="black" />
 </svg>

   `
     const T =   `
 <svg height="76" class="piece black" width="76" xmlns="http://www.w3.org/2000/svg" id="triangle">
   <polygon points="38,3 73,73 3,73" stroke="white" stroke-width="3" fill="black" />
 </svg>
   `

     const  k  =   `
 <svg height="76" class="piece white" width="76" xmlns="http://www.w3.org/2000/svg" id="circle">
   <circle cx="38" cy="38" r="35" stroke="black" stroke-width="3" fill="white" />
 </svg>

   `
     const t =   `


 <svg height="76" class="piece white" width="76" xmlns="http://www.w3.org/2000/svg" id="triangle">
   <polygon points="38,3 73,73 3,73" stroke="black" stroke-width="3" fill="white" />
 </svg>
   `

     const kK = `
     <div style="display: flex; justify-content: center; align-content: center;">
<svg height="38" class="piece white" width="38" xmlns="http://www.w3.org/2000/svg" id="circle">
  <circle cx="19" cy="19" r="17" stroke="black" stroke-width="3" fill="white" />
</svg>
<svg height="38" class="piece black" width="38" xmlns="http://www.w3.org/2000/svg" id="circle">
 <circle cx="19" cy="19" r="17" stroke="white" stroke-width="3" fill="black" />
</svg>
</div>
     `
     const kT = `
     <div style="display: flex; justify-content: center; align-content: center;">
<svg height="38" class="piece white" width="38" xmlns="http://www.w3.org/2000/svg" id="circle">
  <circle cx="19" cy="19" r="17" stroke="black" stroke-width="3" fill="white" />
</svg>
 <svg height="38" class="piece black" width="38" xmlns="http://www.w3.org/2000/svg" id="triangle">
   <polygon points="19,3 35,35 3,35" stroke="white" stroke-width="3" fill="black" />
 </svg>
</div>
     `
   const tK = `
   <div style="display: flex; justify-content: center; align-content: center;">
 <svg height="38" class="piece white" width="38" xmlns="http://www.w3.org/2000/svg" id="triangle">
   <polygon points="19,3 35,35 3,35" stroke="black" stroke-width="3" fill="white" />
 </svg>
<svg height="38" class="piece black" width="38" xmlns="http://www.w3.org/2000/svg" id="circle">
  <circle cx="19" cy="19" r="17" stroke="white" stroke-width="3" fill="black" />
</svg>

</div>
   `
   const tT = `
   <div style="display: flex; justify-content: center; align-content: center;">
 <svg height="38" class="piece black" width="38" xmlns="http://www.w3.org/2000/svg" id="triangle">
   <polygon points="19,3 35,35 3,35" stroke="black" stroke-width="3" fill="white" />
 </svg>
 <svg height="38" class="piece black" width="38" xmlns="http://www.w3.org/2000/svg" id="triangle">
   <polygon points="19,3 35,35 3,35" stroke="white" stroke-width="3" fill="black" />
 </svg>

</div>
   `

     newhtml = `
     <div class="centered">
       <div>
       <div style="display:flex;width:100%;justify-content: space-between;"> 
         <div>
           <img class="gameProfile" src="/image/${whitePlayer}">
           ${whitePlayer}
           </div>
         
         <div>
           ${blackPlayer}
           <img class="gameProfile" src="/image/${blackPlayer}">
           </div>
         </div>
      <div id="gameGrid"></div>
      <div id="initialPieces" style="display:flex;width:100%;justify-content: center; gap:10px;"></div>
      </div>
 <div style="display: flex;flex-direction: row;gap: 66px;">

 <button class="actionButton" id="giveUp" style="float:left;">🏳️</button>

 <button class="actionButton" id="confirmMove" style="float:right; disabled">🚫</button>
</div></div>
`;
 document.body.innerHTML = newhtml;
 var confirmButton = document.getElementById("confirmMove");
 var giveUpButton = document.getElementById("giveUp");

const gridDisplay = document.getElementById("gameGrid");  
let initialPieces = document.getElementById("initialPieces");

 
   initialPieces.innerHTML= (isBlack ? K : k).repeat(2)+ (isBlack ? T : t).repeat(2);
   




for (let i = 0; i < 35; i++) {
     
       const cell = document.createElement("div");
       cell.classList.add("cell");
       cell.id = ''+i;
       if (["7", "8", "9", "14", "15", "16", "21", "22", "23"].includes(""+i)) {
         cell.classList.add("restricted-left");
       }
       if (["11", "12", "13", "18", "19", "20", "25", "26", "27"].includes(""+i)) {
         cell.classList.add("restricted-right");
       }


       gridDisplay.appendChild(cell);
     

   }
     colorTakenSpaces = function(takenSpaces){
       //TODO: napravit 
     }
     disableConfirmButton = function(){
       confirmButton.disabled = true;
       confirmButton.innerHTML = "🚫";
     }
     enableConfirmButton = function(){
       confirmButton.disabled = false;
       confirmButton.innerHTML = "✅"
     }
   submitMove = function(){

    

     disableConfirmButton();
       
       //TODO: napravit
       movesforSubmitting = moves[+isBlack];
       console.log(movesforSubmitting);
       
       socket.emit("submitMoves",{"id":gameId,"isBlack":isBlack,"moves":movesforSubmitting});
       //socket.off("waiting");
       socket.on("waiting",  (data) => {
       //tu ćemo djelovati kad se čeka na nama
       //ovo ne radi i ne znam zašto
       console.log("ALO OVAJ JE VEĆG OTOV");
     });
     
       socket.on("ok", (data) => {

          //TODO: ovdje započeti tajmere

           if (isFirstMove){
             //document.querySelectorAll()
             isFirstMove = false;

             //TODO: GFPKK

           }
           
           //ako smo mi drugi poslali naše pokrete
           moves = data.moves;
           for (i = 0; i < 34; i++){
             document.getElementById(i.toString()).className	= "cell"
           }
           // for (i of data.whiteTaken){
           //   document.getElementById(i).className = "cell white taken"
           // }
           // for (i of data.blackTaken){
           //   document.getElementById(i).className = "cell black taken"
           // }
           updateBoard();
           colorTakenSpaces(data.takenSpaces);
          

       });
      }

   colorAllowedMoves = function(moves){
     console.log(moves);
     console.log("OVO SU POKRETI");
       for (var id of moves){
         //id = id.padStart(2,"0");
         console.log(id);
         console.log("OVO JE ID");
         console.log(document.getElementById(id));
         document.getElementById(id).style="border: 3px solid #090;";

       }
     }

     computeAllowedMoves = function(position=0){
       let allowedMoves = [];
       if (isFirstMove){
         console.log(illegalMoves);
         console.log("OVO SU NEDOZVOLJENI");
         
         for (let i = 0; i < 35; i++){
           if (illegalMoves.includes(i.toString()) == false){
             console.log(i);
             console.log("OVAJ MERE");
             allowedMoves.push(i.toString());
             
           }
         }
         
       }
       else {
         let allowedMoves = [];
         let transforms = 
       [
         -6,-5,-4,
         -1, 0, 1,
          4, 5, 6,
       ]
         
         for (let i = 0; i<9; i++){
           newPosistion = position+transforms[i];
           if(newPosistion > -1 && newPosistion < 35 && !document.getElementById(newPosistion.toString()).classList.contains("taken")){ // && još toga ali kasnije
             allowedMoves.push(i.toString());
             
           }
         }

       }
       return allowedMoves;
     }

     // što ako su dva na jednom mjestu?!?!?!? 
     // kK  b
     // kT  c
     // tK  c
     // tT  b
     updateBoard = function(){
       lookupTable = {
         "k": k,
         "t": t,
         "K": K,
         "T": T,
         "kK": kK,
         "kT": kT,
         "tK": tK,
         "tT": tT,
       }

       for (i = 0; i < 35; i++){
         document.getElementById(i.toString()).innerHTML = "";
       }
       let result = {};

       for (let i = 0; i < moves[0].length; i++) {
 let lowerMove = moves[0][i];
 if (i < 2){
 if (lowerMove !== -1 && lowerMove !== -2) { // Skip if the number is -1
   if (!result[lowerMove]) {
     result[lowerMove] = "k"; // Assign "k" for lowercase piece
   } else {
     result[lowerMove] += "k"; // Add another "k" if already exists
   }
 }
}
else{
 if (lowerMove !== -1 && lowerMove !== -2) { // Skip if the number is -1
   if (!result[lowerMove]) {
     result[lowerMove] = "t"; // Assign "k" for lowercase piece
   } else {
     result[lowerMove] += "t"; // Add another "k" if already exists
   }
 }
}
}

// Process uppercase pieces
for (let i = 0; i < moves[1].length; i++) {
 let upperMove = moves[1][i];
 if (i < 2){
 if (upperMove !== -1 && upperMove !== -2) { // Skip if the number is -1
   if (!result[upperMove]) {
     result[upperMove] = "K"; // Assign "k" for lowercase piece
   } else {
     result[upperMove] += "K"; // Add another "k" if already exists
   }
 }
}
else{
 if (upperMove !== -1 && upperMove !== -2) { // Skip if the number is -1
   if (!result[upperMove]) {
     result[upperMove] = "T"; // Assign "k" for lowercase piece
   } else {
     result[upperMove] += "T"; // Add another "k" if already exists
   }
 }
}
}

     for (id in result){
       console.log(`${id}: ${result[id]}`);
       document.getElementById(id.toString()).innerHTML = lookupTable[result[id]];
     }
   }
   

     clearSelections = function(){
       for (i = 0; i < 35; i++){
         document.getElementById(i.toString()).style = "";
       }
     }

     //ovo radi
     document.querySelectorAll(".piece").forEach(element => {
       element.addEventListener("click", () =>{
         console.log(`KLIKNUO SAM NA ${element.id}`);
         if (selectedElement !== undefined){
           console.log("SELECTED VEĆ POSTOJI");
           console.log(selectedElement.innerHTML);
           selectedElement.innerHTML = selectedElement.innerHTML.replace('<rect width="76" height="76" fill="#ef9"></rect>',"");
           
         }
         selectedElement = element;
         selectedPiece = element.id;
         element.innerHTML = '<rect width="76" height="76" fill="#ef9"></rect>'+element.innerHTML;
         colorAllowedMoves(computeAllowedMoves());
       });
     });

     document.querySelectorAll(".cell").forEach(element => {
       element.addEventListener("click", () => {
         console.log("klikitis");
         console.log(element.id);
         if (selectedElement !== undefined && computeAllowedMoves().includes(element.id)){

           playerMoves = moves[+isBlack];

           if (selectedPiece == "circle") {
   // Try to place the circle in the first two available spots (index 0 or 1)
   if (playerMoves[0] === -2) {
     playerMoves[0] = element.id; // Place circle in the first empty spot
   } else if (playerMoves[1] === -2) {
     playerMoves[1] = element.id; // Place circle in the second empty spot
   }
 } else if (selectedPiece == "triangle") {
   // Try to place the triangle in the last two available spots (index 2 or 3)
   if (playerMoves[2] === -2) {
     playerMoves[2] = element.id; // Place triangle in the first empty spot
   } else if (playerMoves[3] === -2) {
     playerMoves[3] = element.id; // Place triangle in the second empty spot
   }
 }
         illegalMoves.push(element.id);
         clearSelections();
         updateBoard();
         a++;
         if (a == 4){
           a = -Infinity
           enableConfirmButton();
           confirmButton.onclick = function() {submitMove()};
         }
         selectedElement.remove();
         selectedElement = undefined;
         selectedPiece = undefined;
         }
       });
     });

   });

 });



    // =========================================
    //                ideja je
    //           jedan je malo slovo 
    //             drugi je veliko
    //  zapiši koji su legalni oko pojedinog
    // dopusti pomicanje u bilo koje od 9 polja
    //        svaka figura jednistvena
    // =========================================


    //        +----+-----------------+
    //        |Znak|  Značenje var.  |
    //        +----+-----------------+
    //        | bt | Bijeli trokut 1 |
    //        | bT | Bijeli trokut 2 |
    //        | bk | Bijeli krug 1   |
    //        | bK | bijeli krug 2   |
    //        +----+-----------------+
    //        | ct | Crni trokut 1   |
    //        | cT | Crni trokut 2   |
    //        | ck | Crni krug 1     |
    //        | cK | Crni krug 2     |
    //        +----+-----------------+



    const bt = "https://upload.wikimedia.org/wikipedia/commons/3/3b/Chess_klt60.png";
    const bk = "https://upload.wikimedia.org/wikipedia/commons/4/49/Chess_qlt60.png";

    const giveUpButton = document.getElementById("giveUp");
    const confirmButton = document.getElementById("confirmMove");


    let isMovingPiece = false;
    let pieceToMove;
    let canMakeMove = true;
    let surrender = 0;

    const gridDisplay = document.getElementById("gameGrid");

    var grid =
      [
        ["e", "e", "e", "e", "e", "e", "e"],
        ["e", "e", "e", "e", "e", "e", "e"],
        ["e", "e", "e", "e", "e", "e", "e"],
        ["e", "e", "e", "e", "e", "e", "e"],
        ["e", "e", "e", "e", "e", "e", "e"],
      ]


    var border = [
          [-1, -1], [0, -1], [1, -1],
          [-1,  0], [0,  0], [1,  0],
          [-1,  1], [0,  1], [1,  1],
        ]



    function playerSurrendered(){
      //TODO napravit server koji zapravo spoji dva klijenta ?!?! 
      console.log("odusta si");
    }

    document.addEventListener("click", event => {
      if (event.target == giveUpButton){
      switch(surrender){
        case 0:
          surrender++;
          giveUpButton.innerHTML="Ozbiljno?";
          giveUpButton.style = "font-size: 12px; background-color: #a00; border: 2px solid #500;";
          break;
        case 1:
        giveUpButton.innerHTML=":(";
        giveUpButton.style = "background-color: #700; border: 2px solid #200";
          playerSurrendered();
          break;
      }
      }
      else{
        surrender = 0;
        giveUpButton.innerHTML="🏳️";
        giveUpButton.style.cssText="";
      }
    });


    // zasad radi sve
    function gridUpdate() {

      console.log("UPDATE");

      for (const child of gridDisplay.children) {

        if (child.childElementCount == 0) {

          if (child.id.includes("bt")) {
            image = document.createElement("img");
            image.src = bt;
            child.appendChild(image);
            grid[Number(child.id[0])][Number(child.id[1])] = "bt";

          }

          else if (child.id.includes("bk")) {
            image = document.createElement("img");
            image.src = bk;
            child.appendChild(image);
            grid[Number(child.id[0])][Number(child.id[1])] = "bk";
          }
          

        }

        else if (child.childElementCount > 0 && child.id.length < 4) {
            console.log("BASTARD");
            child.innerHTML = "";
          }

      }
      
    }

    


    var k = 0;
    var t = 0;

    var playerColor = "b";

    console.log(grid)

    //postavljanje
    for (let i = 0; i < 5; i++) {
      for (let j = 0; j < 7; j++) {
        const cell = document.createElement("div");
        cell.classList.add("cell");
        cell.id = '' + i + '' + j;
        if (["10", "11", "12", "20", "21", "22", "30", "31", "32"].includes(""+i+""+j)) {
          cell.classList.add("restricted-left");
        }
        if (["14", "15", "16", "24", "25", "26", "34", "35", "36"].includes(""+i+""+j)) {
          cell.classList.add("restricted-right");
        }


        gridDisplay.appendChild(cell);
      }

    }

    const cells = document.querySelectorAll('.cell');





    cells.forEach(el => el.addEventListener('click', event => {
      
      if (canMakeMove){

      if (isMovingPiece != false) {
        console.log("POMAK")
        if (event.target.style.border == "1px solid green" && event.target.childElementCount == 0) {
          event.target.id += isMovingPiece+"P";
          isMovingPiece = false;
          piece = document.getElementById(pieceToMove);
          piece.id = pieceToMove.slice(0,2);

        }
        else {
          isMovingPiece = false;
        }

        for (const child of gridDisplay.children){
          child.style.border = "none";
        }
      }

      console.log(event.target.id.length);


      if (event.target.id.length >=  4) {
        console.log("tu smo");
        isMovingPiece = "bt";
        



        



        for (i = 0; i < 9; i++) {
          try {
            cell = document.getElementById('' +
              (border[i][0] + Number(event.target.id[0]) +
                '' + (border[i][1] + Number(event.target.id[1])
                )
              ))
            cell.style.border = "1px solid green";

          }
          catch { continue; }

        }
        
        
        pieceToMove = event.target.id;

      }




      // POČETNO POSTAVLJANJE
      if (event.target.id.length == 2 && t < 2 && isMovingPiece == false) {
        if (["14", "15", "16", "24", "25", "26", "34", "35", "36"].includes(event.target.id) == false) {
          console.log(["14", "15", "16", "24", "25", "26", "34", "35", "36"].includes(event.target.id));
          event.target.id = event.target.id + playerColor + "t"
          console.log(event.target.id);
          t++;
          if (t == 2){
            canMakeMove = false;

          }
        }
      }
      // 11  21  32
      // 12  22  32
      // 13  23  33


      gridUpdate()
    }
    else {}
    }));

    cells.forEach(el => el.addEventListener('contextmenu', event => {
      event.target.style = "background-color: red";
      console.log(event.target.style.color)
    }));

    // Initialize grid and example usage





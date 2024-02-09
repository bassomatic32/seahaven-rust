#![allow(non_snake_case)]

use rand::seq::SliceRandom;
use rand::thread_rng;
use array_init;
use std::{collections::HashMap,thread,time,process};
use terminal::{Clear, Action, Color};
use base64::prelude::*;
use sha2::{Sha256, Digest};

const ABANDON_THRESHOLD:u32 = 500000;


#[derive(Copy, Clone, Debug)]
struct Card {
	suit: u8,
	value: u8,
}

type Stack = Vec<Card>;

#[derive(Debug)]
struct Board {
	goals: [Stack;4],
	cells: [Stack;4],
	stacks: [Stack;10]
}

#[derive(Copy,Clone)]
struct Tally {
	totalGames: u32,
	winnable: u32,
	losers: u32,
	abandoned: u32
}

#[derive( Clone, Debug)]
struct GameMove {
	source: Position,
	target: Position,
	msg: String,
	extent: u16
}
#[derive(Copy, Clone, Debug)]
enum StackType {
	GOAL,
	CELL,
	TABLEAU
}


#[derive(Copy, Clone, Debug)]
struct Position {
	stackIndex: usize,
	stackType: StackType
}

#[derive( Clone, Debug)]
struct LegalMove {
	source: Position,
	target: Position,
	extent: u16
}




fn suitName(suit:u8) -> &'static str {
	match suit {
		0 => "H",
		1 => "D",
		2 => "C",
		3 => "S",
		_ => "u"
	}
}

fn initializeBoard() -> Board {
	let mut deck:Stack = Stack::with_capacity(52);

	// initialize deck sequentially

	for suit in 0..4 {
		for value in 1..14 {
			deck.push( Card { suit, value });
		}
	}

	// shuffle it
	let mut rng: rand::prelude::ThreadRng = thread_rng();
	deck.shuffle(&mut rng);

	// print!("{:?}",deck);
	
	let goals:[Stack;4] = array_init::array_init(|_| Stack::with_capacity(13));
	let cells:[Stack;4] = array_init::array_init(|_| Stack::with_capacity(1));
	let stacks:[Stack;10] = array_init::array_init(|_| Stack::with_capacity(52));

	let mut board: Board = Board { goals,cells,stacks};

	// init each of the 10 stacks with 5 cards each
	for stack in board.stacks.iter_mut() {
		for _ in 0..5 {
			stack.push(deck.pop().unwrap());
		}
	}

	// That leaves 2 cards remaining to put in 2 of the 4 cells
	board.cells[0].push(deck.pop().unwrap());
	board.cells[1].push(deck.pop().unwrap());
	
	
	return board;
}


fn colorCard(card: Option<&Card>) -> Color {

	match card {
		Some(c) => {
			match c.suit {
				0 => Color::DarkRed,
				1 => Color::Red,
				2 => Color::DarkBlue,
				3 => Color::Blue,
				_ => Color::White
		
			}
		}
		None => Color::White
	}
}

fn cardName(card: Option<&Card>,default:String) -> String {
	
	match card {
		Some(c) => {
			let suitStr = suitName(c.suit);
			
			let valueStr: String = match c.value {
				1 => "A".to_string(),
				11 => "J".to_string(),
				12 => "Q".to_string(),
				13 => "K".to_string(),
				_ => format!("{}",c.value)
			};
			let cn = format!("{valueStr}{suitStr} ");
			return cn;
		}
		None => default
	}

}

fn cardNumerical(card: Option<&Card>) -> u16 {
	match card {
		Some(c) => c.suit as u16 * 100 + c.value as u16,
		None => 0
	}
}


// you cannot create a sequence of more than 5 consecutive cards if a lower card of the same suit is higher in the stack.
// Doing so will block that suit from ever making it to the goal, because you can only move 5 cards in sequence at once
// e.g. with stack 2H 10H 9H 8H 7H 6H, moving the 5H on the end would cause a situation where the 2H could never be freed.
// we can ensure this doesn't happen and reduce our possiblity tree
fn isBlockingMove(card:&Card,targetStack:&Stack,extentLength:u16) -> bool {

	if targetStack.len() < 5 {
		return false;
	} 

	let mut foundLower = false;
	let mut sequenceBroken = false;
	let mut count = 1;

	// println!("Stack {:?}",target.stack);
	
	for (i,stackCard) in targetStack[1..].iter().rev().enumerate() {
		let pos = (targetStack.len() - i) - 1;
		let nextCard = targetStack[pos-1];

		// keep counting the sequence until its broken
		if !sequenceBroken && stackCard.suit == nextCard.suit && stackCard.value == nextCard.value-1 {
			count += 1;
		} else {
			sequenceBroken = true
		}

		if stackCard.suit == card.suit && stackCard.value < card.value {
			foundLower = true;
			break; // no reason to continue at this point
		}
		
		// println!("item {0} {1:?} {2:?}",i,stackCard,nextCard);
	}

	// if we found a lower card higher in the stack AND the counted sequence + extentLength ( how many cards we are moving onto the stack ) >= 5 , then its a blocking move, as it will
	// result in 6 or more cards in sequence with a lower card higher in the stack
	if foundLower && (count + extentLength) >= 5 {
		
		return true;
	}

	return false
}	



// returns how many cards on the top of the stack are ordered ( inclusive ).  That is, there will always be at least one, unless the stack is empty
fn stackOrderedCount(stack:&Stack) -> u16 {
	if stack.len() == 0 {
		return 0;
	}
	let mut count = 1;
	for (i,stackCard) in stack[1..].iter().rev().enumerate() {
		let pos = (stack.len() - i) - 1;
		let nextCard = stack[pos-1];
		if stackCard.suit == nextCard.suit && stackCard.value == nextCard.value-1 {
			count += 1;
		} else {
			break;
		}
	}

	return count
}

// an extent is a ordered set of cards ( starting with top most ) that is less or euqal to the number of freeCells+1
// For example, the most basic extent is 1 card, and we don't need any free cells
// we can move an extent of values 5,4,3 if there are 2 or more free cells
// logic is simple:  move every card except the final one into the available free cells, move the final card to target, then move cards from cells back onto final card in new position
// we will return the total number of cards in the extent, or 0 meaning there is no movable card
fn findExtent(board: &Board,stack: &Stack) -> u16 {
	let freeCellCount = countFreeCells(board);
	
	let count = stackOrderedCount(stack);
		
	if count <= (freeCellCount+1) { return count }

	return 0

}
		



// determines if the stack's top card suit has other cards in the same suit that disconnected in the stack. 
fn isDisconnectedStack(stack:&Stack) -> bool {
	if stack.len() <=1 {
		return false;
	}
	// println!("isDisconnected {:?}",stack);

	let mut breakPoint = false;
	let mut disconnected = false;
	let firstCard = stack.last().unwrap();

	for (i,stackCard) in stack.iter().rev().enumerate() {
		if stackCard.suit == firstCard.suit  {
			if !breakPoint {
				continue ;
			}
			disconnected = true;
			break;		
		}
		breakPoint = true;
	}

	return disconnected;

}

// return a collection of all cell positions that have nothing in them
fn findFreeCells(board: &Board) -> Vec<Position>  {
	let mut freeCells: Vec<Position> = Vec::new();
	for (stackIndex,stack) in board.cells.iter().enumerate() {
		if stack.len() == 0 {
			freeCells.push(Position { 
				stackIndex, 
				stackType: StackType::CELL});
		}		
	}

	return freeCells;

	
}

// count how many free cells there are
fn countFreeCells(board: &Board) -> u16  {
	let count = findFreeCells(board).len() as u16;
	return count;
}

fn countGoal(board:&Board) -> u16 {
	let tot = board.goals.iter().map(|s| s.len()).reduce(|acc,e| acc + e).unwrap();	return tot as u16;
}

fn isSuccess(board:&Board) -> bool {
	return countGoal(board) == 52 // goal will have 52 cards if game is over
}

// create a unique checksum for the boards current state. This is used to ensure we never repeat a configuration, as its
// easy in this game to achieve the same configuration from multiple move possibilities
// Goal configuration is not considered
// Cells are sorted to ensure that any order of the same cards in the cells are considered to be the same configuration
// Stacks are sorted by the bottom most card, again to remove consideration of order from the checksum
fn checksumBoard(board:&Board) -> String {
	
	// get a sorted group of cells
	let mut cells: Vec<u16> = board.cells.iter()
		.map(|s| cardNumerical(s.last()))
		.collect::<Vec<u16>>();
	cells.sort();

	let mut stacks : Vec<Vec<u16>> = board.stacks.iter()
		.map(|s| s.iter().map(|c| cardNumerical(Some(c))).collect::<Vec<u16>>()
		).collect();
	stacks.sort_by_key(|k| if k.len() == 0 { 0 } else { k[0] });
	
	
	let key = format!("{0:?}{1:?}",cells,stacks);
	return key;
}





// Check to see if the stack is fully ordered
// a stack is considered to be fully ordered if any ordered sequence from the top of the stack down is made up of more than the available free cells + 1
// ( once you've hit 6 cards, the only place you can move the top card is to the goal.  You'll fill up the available cells trying to move the whole sequence)
fn isFullyOrdered(board:&Board,stack:&Stack) -> bool {
	if stack.len() == 0 {
		return true
	}
	let freeCells = countFreeCells(board);

	if !(stack.len() as u16 > (freeCells + 1) ) { // impossible to be fully ordered unless stack size is greater than the available free cells + 1
		return false;
		}

	let count = stackOrderedCount(stack);

	if count > (freeCells+1) {
		return true;
	}

	return false
}


struct Game {
	board: Board,
	boardSet: HashMap<String,bool>,
	stackSize: u32,
	totalMoves: u32,
	repeatsAvoided: u32,
	tally: Tally,
	gameMoves: Vec<GameMove>,
	abandoned: bool
}

impl Game {
	fn new(tally: Tally) -> Self {
		let board = initializeBoard();
	
		Game {
			board,
			boardSet: HashMap::new(),
			stackSize: 0,
			totalMoves: 0,
			repeatsAvoided: 0,
			tally,
			gameMoves: Vec::new(),
			abandoned: false
		}
	}

	fn print(&self,title: &str) {
		let term = terminal::stdout();
	
		term.act(Action::MoveCursorTo(1,1));
		term.act(Action::SetForegroundColor(Color::Reset));
		print!("{}",title);
	
		let offsetY = 2;
	
		// print goals
		for (i,goalStack) in self.board.goals.iter().enumerate() {
			term.act(Action::MoveCursorTo(1+(i as u16 * 4),offsetY+1));
			term.act(Action::SetForegroundColor(colorCard(goalStack.last())));
			let name = cardName(goalStack.last()," - ".to_string());
			print!("{name}");
		}
		
		// print cells
		for (i,cellStack) in self.board.cells.iter().enumerate() {
			term.act(Action::MoveCursorTo(30+(i as u16 * 4),offsetY+1));
			term.act(Action::SetForegroundColor(colorCard(cellStack.last())));
			let name = cardName(cellStack.last()," x ".to_string());
			print!("{name}");
		}
		// find the max length of the stacks
		let maxLength = self.board.stacks.iter().map(|s| s.len()).max().unwrap()+10;
	
		for row in 0..maxLength {		
			for (col,tableStack) in self.board.stacks.iter().enumerate() {
				term.act(Action::MoveCursorTo(1+((col as u16)*4),offsetY+3+(row as u16)));			
				let card = tableStack.get(row);
				term.act(Action::SetForegroundColor(colorCard(card)));
				let name = cardName(card,"   ".to_string());
				print!("{name}");
			}
		}
	
		term.act(Action::SetForegroundColor(Color::Reset));
	
		term.act(Action::MoveCursorTo(50,offsetY+2));
		print!("Games Played {0}",self.tally.totalGames);
		term.act(Action::MoveCursorTo(50,offsetY+4));
		print!("Winnable {0}  Losers: {1}  Abandoned {2}",self.tally.winnable,self.tally.losers,self.tally.abandoned);
		term.act(Action::MoveCursorTo(50,offsetY+6));
		print!("Stack Size {0}",self.stackSize);
		term.act(Action::MoveCursorTo(50,offsetY+8));
		print!("Total Moves {0}",self.totalMoves);
		term.act(Action::MoveCursorTo(50,offsetY+10));
		print!("Unique Boards {0}  Collisions: {1}",self.boardSet.len(),self.repeatsAvoided);
		
	
	}	

	// Resolve a position into a reference to a particlar card stack
	fn resolvePosition(&self,position:Position) -> &Stack {
		
		let stack = match position.stackType {
			StackType::GOAL => &self.board.goals[position.stackIndex],
			StackType::CELL => &self.board.cells[position.stackIndex],
			StackType::TABLEAU => &self.board.stacks[position.stackIndex]
		};

		return stack;
	}

	fn resolvePositionMut(&mut self,position:Position) -> &mut Stack {
		
		let stack = match position.stackType {
			StackType::GOAL => &mut self.board.goals[position.stackIndex],
			StackType::CELL => &mut self.board.cells[position.stackIndex],
			StackType::TABLEAU => &mut self.board.stacks[position.stackIndex]
		};

		return stack;
	}

	fn popCard(&mut self,position:Position) -> Card {
		let stack = self.resolvePositionMut(position);	
		return stack.pop().unwrap()
	}

	fn pushCard(&mut self,card:Card,position:Position) {
		let stack = self.resolvePositionMut(position);		
		stack.push(card);
	}


	fn registerBoard(&mut self) -> bool {
		let checksum = checksumBoard(&self.board);
	
		if self.boardSet.contains_key(&checksum) {
			self.repeatsAvoided = self.repeatsAvoided + 1;
			return true;
		}
		self.boardSet.insert(checksum,true);
		if self.boardSet.len() > ABANDON_THRESHOLD as usize { // give up after a certain point
			self.abandoned = true;
			return true;
		}

	
		return false
	}

	fn recordMove(&mut self,source:Position,target:Position,extent:u16) {
		let sourceStack = self.resolvePosition(source);
		let targetStack = self.resolvePosition(target);
	
		let cardName = cardName(sourceStack.last(), " ".to_string());
		// let msg = format!("Move: {0} From: {1:?}/{2:?} To: {3:?}/{4:?} ",cardName,sourceStack,source.stackType,targetStack,target.stackType);
		let msg = String::from("n");
		// record the move
		self.gameMoves.push(GameMove {
			source,
			target,
			msg,
			extent
		});
	
	}

	// We move an extent by moving extent-1 cards to free cells, moving the inner most card in the extent, then moving the remaining from the cells in reverse order
	// e.g. if we have an extent of values 5,4,3 moving to a target stack where top card is 6, move 3, 4 to free cells, move 5 -> target stack, then 4,3 to target stack in that order
	// this totals to (extent-1) * 2 + 1 total moves.  This amount should be used when undoing this action
	// assume there are enough free cells to do this
	fn moveExtent(&mut self,source:Position,target:Position,extent:u16) {
		// let sourceStack = self.resolvePosition(source);
		
		// println!("Move extent {0:?} to {1:?} extent {2:?}",source,target,extent);
		let freeCells = findFreeCells(&self.board);
		// the number of free cells must be at least the extent-1.  That is, we can move 1 card when theres no free cells, 2 if 1 free cell, etc.
		if freeCells.len() >= (extent as usize - 1) {
			for i in 0..extent as usize -1 {
				let cellPosition = freeCells[i];
				self.moveCard(source,cellPosition,extent);
			}
			self.moveCard(source,target,extent);
			for i in (0..extent as usize -1).rev() {
				let cellPosition = freeCells[i];
				self.moveCard(cellPosition,target,extent);
			}

		}
	}

	fn moveCard(&mut self,source:Position,target:Position,extent:u16) {
		self.recordMove(source, target, extent);
		
		let sourceStack = self.resolvePosition(source);
		// println!("Move card: {0:?} as part of extent {1:?}",sourceStack,extent);		// // make the move
		if sourceStack.len() == 0 {
			// self.print("About to panic!!!");
			println!("{:?}",source);
			thread::sleep(time::Duration::from_secs(10));
			
		}	

		let card = self.popCard(source);
		self.pushCard(card, target);
	
		self.totalMoves += 1;

		if self.totalMoves % 1000 == 0 {
			self.print("Playing") ;
		}
	
	}
	
	fn undoLastMove(&mut self) {
		if self.gameMoves.len() > 0 {
			let gameMove = self.gameMoves.pop().unwrap(); // pull off the last move

			

			let card = self.popCard(gameMove.target);
			self.pushCard(card,gameMove.source);
			
			// self.totalMoves -= 1;
			

		} else {
			println!("Ran out of moves to undo!");
			process::exit(1);
		}
	}


	// determine if moving the card to the target stack constitues a legal move
	fn isLegalMove(&self,card:&Card,target:Position,extentLength:u16) -> bool {

		let targetStack = self.resolvePosition(target);
		if matches!(target.stackType, StackType::GOAL)  {
			//  two conditions.  The card is an Ace, and the goal is empty
			//  -or- the target's card is the same suit, and exactly one less in card value
			if targetStack.len() == 0 {
				return (card.value == 1)				
			}
			// check if card value is same suit and exactly +1 in value
			let targetCard = targetStack.last().unwrap();
			return targetCard.suit == card.suit && targetCard.value == (card.value-1)
		}

		if matches!(target.stackType, StackType::CELL ) {
			return targetStack.len() == 0 // our only requiremnt if the target is a Cell is that the stack is empty
		}

		// target is a stack, no need to check
		if targetStack.len() == 0 {
			return card.value == 13 // only a King can target an empty stack
		}

		// for all other TABLEAU moves, the top of the target stack must be same suit and one GREATER in value
		let targetCard = targetStack.last().unwrap();
		return targetCard.suit == card.suit && targetCard.value == (card.value+1) && !isBlockingMove(card, targetStack, extentLength);
	
	}

	// even though a card may have up to 3 legal moves, only one of them make sense to make in any given circumstance
	fn findLegalMove(&self,source:Position) -> Option<LegalMove> {

		
		let sourceStack = self.resolvePosition(source);
		if (sourceStack.len() > 0) { // cannot move anything from an empty stack
			let mut card = sourceStack.last().unwrap();

			// first check, for each goal stack, if move to goal is a legal move
			for (stackIndex,goalStack) in self.board.goals.iter().enumerate() {
				let target = Position { stackIndex,stackType:StackType::GOAL};
				if self.isLegalMove(card, target, 1) { return Some(LegalMove{source,target,extent:1}) } 
			}

			// short-circuit here if source stack is fully ordered.  
			if matches!(source.stackType,StackType::TABLEAU) && isFullyOrdered(&self.board, sourceStack) { return None } // no reason to move fully ordered card except to goal ( see isFullyOrdered for full definition )

			let mut extent = 0; 
			
			if matches!(source.stackType,StackType::TABLEAU) {
				// stack to stack moves will use an extent
				extent = findExtent(&self.board,&sourceStack);
				if extent > 0 {
					card = sourceStack.get(sourceStack.len() - extent as usize).unwrap()
				} else {
					return None; // if we found no extent from a source that is a Tableau, it means there's nothing that can be moved from that stack
				}
			}

			// consider all moves that target the Tableau
			for (i,targetStack) in self.board.stacks.iter().enumerate() {
				let target = Position { stackIndex: i,stackType: StackType::TABLEAU};
				if self.isLegalMove(&card, target, extent) { return Some(LegalMove{source,target,extent}) }
			}

			// only thing left is targeting free cells
			if matches!(source.stackType,StackType::CELL) { return None } // a card in a cell should only move to a goal or stack, which have already been considered.  Short-circuit here if our card is in a cell
			
			let freeCells = findFreeCells(&self.board);
			if freeCells.len() > 0 && extent <= 1 {
				return Some( LegalMove { source, 
					target: freeCells.get(0).copied().unwrap(),
					extent:1}); // move to the first free cell available
			}

		}

		return None;
	}

	// Make the given move and recursively continue playing from the new configuration.
	// That is, we will make that move, then follow that line of the possibility tree recursively.  Otherwise, we fail out of the function
	fn moveAndPlayOn(&mut self,legalMove:LegalMove ) -> bool {


		// for TABLEAU -> TABLEAU, use move extent
		if legalMove.extent > 1 && matches!(legalMove.source.stackType,StackType::TABLEAU) && matches!(legalMove.target.stackType,StackType::TABLEAU ) {
			self.moveExtent(legalMove.source, legalMove.target, legalMove.extent);
		} else {
			self.moveCard(legalMove.source, legalMove.target, legalMove.extent);
		}

		if isSuccess(&self.board) { return true } // check for success
		
		let repeatBoard = self.registerBoard();
		

		if !repeatBoard {  // don't continue unless move wasn't a repeat ( classic example of too many negatives:  continue if not repeated)
			let success = self.cycleThroughCards(); // recursively attempt to solve the new board configuration
			if success { return true } // the path from this configuration succeeded, so return true
		}

		// at this point, we know that this configuration wasn't a success, it might be a repeat, or its attempt to solve from the new configuration resulted in failure
		// in either case, we undo the move we just made
		
		if legalMove.extent > 1 {
			let totalExtentMoves = (legalMove.extent-1)*2 + 1;  // each extent move is recorded as individual moves, so we need to back them all out individually
			// println!("Undo extent move: {:?} ",legalMove);
			for i in 0..totalExtentMoves  {
				// println!("Undo extent {0} totalEtentMoves {1} index {2}",legalMove.extent,totalExtentMoves,i);
				self.undoLastMove() 
			}
		} else { 
			// println!("Undo standard move: {:?} ",legalMove);
			self.undoLastMove() 
		}


		return false // return the fact that this did not succeed

	}

	// our fundamental game loop.  Iterate over every Tableau and Cell stack, finding each legal move in the current configuration
	// then make that move.  This function will be called recursively from the moveAndPlanOn() to attempt to win from the new configuration
	fn cycleThroughCards(&mut self) -> bool {
		self.stackSize += 1;

		let mut success = false;

		let mut allMoves : Vec<LegalMove> = Vec::new();

		for stackIndex in 0..14 { // we will resolve this index as 10 Tableau stacks and 4 cells
			let mut source: Position;

			// determine the source position
			if stackIndex > 3 {
				source = Position { stackIndex: stackIndex - 4,stackType:StackType::TABLEAU}
			} else {
				source = Position { stackIndex,stackType: StackType::CELL }
			}

			match self.findLegalMove(source) {
				Some(lm) => {
					allMoves.push(lm);
				},
				None => {}
			}			
		}

		// allMoves now has a list of legal moves
		allMoves.sort_by_key(|lm| match lm.target.stackType {
			StackType::GOAL => 0,
			StackType::TABLEAU => 1,
			_ => 2
		});

		for lm in allMoves {
			
			// thread::sleep(time::Duration::from_secs(1));
			success = self.moveAndPlayOn(lm);
			if success { break }
		}

		self.stackSize -= 1;
		return success;
	}

	fn replayGame(&mut self) {
		// rewind the entire game based on the move stack
		let moveCopy = self.gameMoves.to_vec();
		
		// # undo all moves
		for i in 0..moveCopy.len() {
			self.undoLastMove();
			self.print("Rewinding        ");
			thread::sleep(time::Duration::from_millis(10));
		}
		
		for m in moveCopy {
			self.moveCard(m.source,m.target,m.extent);
			if m.extent <= 1 {
				self.print("Replay") ;
				thread::sleep(time::Duration::from_millis(100));
			}
		}

	}

	

}


fn main() {
	let term = terminal::stdout();
	term.act(Action::ClearTerminal(Clear::All));

	let mut tally = Tally {
		totalGames: 0,
		winnable: 0,
		losers: 0,
		abandoned: 0
	};
	
	for _ in 0..1000 {
		
		let mut game = Game::new(tally);

		let success = game.cycleThroughCards();

		tally.totalGames += 1;
		if (success) { tally.winnable += 1 }
		else { tally.losers += 1 }

		if (game.abandoned) { tally.abandoned += 1 }
		game.print(("Finished"));

		// if success {
			// game.replayGame();
		// }

	}
    
}

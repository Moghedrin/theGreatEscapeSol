import Control.Applicative
import Control.Monad
import Data.List (foldl', break, minimumBy, maximumBy)
import Data.Maybe
import Data.Monoid
import Data.Ord (comparing)
import System.IO
import Text.Printf
import qualified Data.Graph as Graph
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

if' a b clause = if clause then a else b

data Dir = RIGHT | LEFT | UP | DOWN
	deriving(Show, Eq, Ord, Read)

moveDir RIGHT (x, y) = (x+1, y)
moveDir LEFT (x, y) = (x-1, y)
moveDir UP (x, y) = (x, y-1)
moveDir DOWN (x, y) = (x, y+1)

type Coord = (Int, Int)
type Branch = [Coord]
type States = Set.Set Coord
type EdgeTree = Map.Map Coord (Set.Set Coord)

data BFS = BFS {children :: (Coord -> States), searchGoals :: States, visited :: States, branches :: [Branch]}

data Orientation = H | V
	deriving (Show, Read, Eq, Ord)
data Wall = Wall Coord Orientation
	deriving (Show, Eq, Ord)

appendLeafs :: States -> Branch -> [Branch]
appendLeafs s b = Set.foldl' (\x y -> (y:b):x) [] s

stepBranch :: (Coord -> States) -> (States, [Branch]) -> Branch -> (States, [Branch])
stepBranch children (visited, bs) branch =
	foldl' visitBranch (visited, bs) (appendLeafs (children (head branch)) branch) where
	visitBranch (visited', branches) branch'@(x:xs) =
		if Set.notMember x visited'
		then (Set.insert x visited', branch':branches)
		else (visited', branches)

bfsStep :: BFS -> BFS
bfsStep (BFS children g v b) = uncurry (BFS children g) (foldl' (stepBranch children) (v, []) b)

runBFS :: BFS -> Branch
runBFS (BFS _ _ _ []) = []
runBFS bfs@(BFS children g v bs)
	| Set.null g = []
	| otherwise =
		let (_, k) = break (\x -> Set.member (head x) g) bs in
			if null k
			then runBFS (bfsStep bfs)
			else head k

data Player = Player {wallCount :: Int, coords :: Coord, goals :: States}
	deriving(Show)

data Board = Board {boardEdges :: EdgeTree, players :: [Player], allowedWalls :: Set.Set Wall}
	deriving (Show)

newBoard pCoords = Board (convertToMap startingEdges) players allowableWalls where
	convertToMap = foldl' addToSet Map.empty where
		addToSet set (src, dest) = Map.alter addIn src set where
			addIn Nothing = Just . Set.singleton $ dest
			addIn a = Set.insert dest <$> a
	startingEdges = leftEdges ++ rightEdges ++ upEdges ++ downEdges where
		leftEdges = [((x, y), (x-1, y)) | x<-[1..9], y<-[1..9], x > 1]
		rightEdges = [((x, y), (x+1, y)) | x<-[1..9], y<-[1..9], x < 9]
		upEdges = [((x, y), (x, y-1)) | x<-[1..9], y<-[1..9], y > 1]
		downEdges = [((x, y), (x, y+1)) | x<-[1..9], y<-[1..9], y < 9]
	allowableWalls = Set.fromList $ concat [[Wall (x, y) V, Wall (x, y) H]| x<-[1..8], y<-[1..8]]
	players = map makePlayer (zip [0..] pCoords) where
		makePlayer (id, coord) = Player 10 coord (Set.fromList $ playerGoals id) where
			playerGoals 0 = [(9, y) | y<-[1..9]]
			playerGoals 1 = [(1, y) | y<-[1..9]]
			playerGoals 2 = [(x, 9) | x<-[1..9]]

addWall :: Board -> Wall -> Board
addWall (Board e p walls) w@(Wall c o) =
	Board (if' (addVertical c e) (addHorizontal c e) (o == V)) p (trimPoss walls w) where
		addVertical c = (addVert c) . (addVert (moveDir DOWN c)) where
			addVert c = removeEdgeBetween c (moveDir LEFT c)
		addHorizontal c = (addHorz c) . (addHorz (moveDir RIGHT c)) where
			addHorz c = removeEdgeBetween c (moveDir UP c)
		removeEdgeBetween a b e =
			let e' = Map.update (return . Set.delete b) a e in Map.update (return . Set.delete a) b e'
		trimPoss ws w@(Wall c V) =
			let ws' = Set.delete w walls;
				ws'' = Set.delete (Wall (moveDir DOWN c) V) ws';
				ws''' = Set.delete (Wall (moveDir UP c) V) ws'' in
					Set.delete (findCross w) ws'''
		trimPoss ws w@(Wall c H) =
			let ws' = Set.delete w walls;
				ws'' = Set.delete (Wall (moveDir RIGHT c) H) ws';
				ws''' = Set.delete (Wall (moveDir LEFT c) H) ws'' in
					Set.delete (findCross w) ws'''
		findCross (Wall c V) = Wall (moveDir DOWN . moveDir LEFT $ c) H
		findCross (Wall c H) = Wall (moveDir UP . moveDir RIGHT $ c) H

initialize :: IO (Int, Int, Int, Int)
initialize = do
	k <- map read <$> (words <$> getLine)
	let width = k !! 0
	let height = k !! 1
	let playerCount = k !! 2
	let myId = k !! 3
	return (width, height, playerCount, myId)

turnInput :: Board -> IO Board
turnInput b@(Board e p _) = do
	players' <- flip mapM p $ \player -> playerLine player <$> getLine
	wallCount <- read <$> getLine
	(Board e' _ w') <- foldM addW b [1..wallCount]
	return (Board e' players' w') where
		addW board _ = do
			k <- words <$> getLine
			let w = Wall ((1+) $ read $ k !! 0, (1+) $ read $ k !! 1) (read $ k !! 2)
			return $ addWall board w

playerLine :: Player -> String -> Player
playerLine player str =
	let k = map read . words $ str in Player (k !! 2) ((1+) $ k !! 0, (1+) $ k !! 1) (goals player) where

runBoardBFS :: Int -> Board -> Branch
runBoardBFS myId (Board e p _) =
	reverse $ runBFS $ BFS (getChildren e) (goals (p !! myId)) Set.empty [[coords $ p !! myId]] where
		getChildren e c = let k = Map.lookup c e in checkIn k where
			checkIn Nothing = Set.empty
			checkIn (Just a) = a

findAllShortest :: Board -> [(Int, Branch)]
findAllShortest b@(Board _ p _) = filterOut $ map (\x -> (x, flip runBoardBFS b x)) [0..(length p)-1] where
	filterOut = filter (not . null . snd)

getDirTo (x1, y1) (x2, y2)
	| x1 - x2 == 1 = LEFT
	| x1 - x2 == (-1) = RIGHT
	| y1 - y2 == 1 = UP
	| y1 - y2 == (-1) = DOWN
	| otherwise = undefined

losing :: Int -> [(Int, Branch)] -> Bool
losing myId branches = let k = minimumBy (comparing $ rank myId) branches in fst k /= myId where

rank :: Int -> (Int, Branch) -> Int
rank myId (id, b) = length b + id

-- #TODO Disallow walls which would block the path of a player
-- Use Data.Graph.bcc to check this. Edges existing in Forest are fine to delete.

findWallableAlongPath :: Board -> Branch -> Maybe Wall
findWallableAlongPath board@(Board _ _ walls) branch =
	alongThePath branch where
		alongThePath [] = Nothing
		alongThePath (_:[]) = Nothing
		alongThePath (x:(xs:xss)) =
			let w = createWall x xs;
				placeW = canPlaceWall w walls;
				w' = primeWall w;
				placeW' = canPlaceWall w' walls in
					if placeW
						then (Just w)
						else if' (Just w') (alongThePath (xs:xss)) placeW' where
					primeWall (Wall c V) = Wall (moveDir UP c) V
					primeWall (Wall c H) = Wall (moveDir LEFT c) H
					createWall a b
						| a `getDirTo` b == UP = Wall a H
						| a `getDirTo` b == DOWN = Wall b H
						| a `getDirTo` b == LEFT = Wall a V
						| a `getDirTo` b == RIGHT = Wall b V
					canPlaceWall wall walls = Set.member wall walls

takeTurn :: Int -> Board -> IO ()
takeTurn myId board = do
	board'@(Board _ p' _) <- turnInput board
	let shortestPaths = findAllShortest board'
	let move = head . tail . fromJust $ lookup myId shortestPaths
	let me = p' !! myId
	if losing myId shortestPaths && length shortestPaths == 2 && wallCount me > 0
	--if losing myId shortestPaths && wallCount me > 0
		then placeWall myId board' shortestPaths me move
		else putStrLn . show $ coords me `getDirTo` move
	where
		placeWall myId b@(Board _ p w) sp me move = do
			let (id, winnerM) = minimumBy (comparing $ rank myId) sp
			hPrint stderr . Set.size $ w
			let k = findWallableAlongPath b winnerM
			if isNothing k || myId == id
				then putStrLn . show $ coords me `getDirTo` move
				else do
					let (Wall c o) = fromJust k
					let (x, y) = moveDir UP . moveDir LEFT $ c
					printf "%d %d %s %s\n" x y (show o) "Die!"

main = do
	hSetBuffering stdout NoBuffering
	hSetBuffering stderr NoBuffering
	(width, height, pC, myId) <- initialize
	let board = newBoard (replicate pC $ (0, 0))
	forever (takeTurn myId board)

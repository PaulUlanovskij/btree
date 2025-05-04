{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
data BTree a = Empty Int | Leaf Int [a] | Node Int [a] [BTree a] deriving (Show, Read)

btree_construct :: Ord a => Int -> [a] -> BTree a
btree_construct k = foldl btree_insert (Empty k)

btree_contains :: Ord a => BTree a -> a -> Bool
btree_contains (Empty _) _ = False
btree_contains (Leaf _ []) _ = False
btree_contains (Leaf m (k:ks)) x
  | x == k = True
  | x < k  = False
  | x > k  = btree_contains (Leaf m ks) x
btree_contains (Node _ [] (t:ts)) x = btree_contains t x
btree_contains (Node m (k:ks) (t:ts)) x
  | x == k = True
  | x < k  = btree_contains t x
  | x > k  = btree_contains (Node m ks ts) x

btree_insert :: Ord a => BTree a -> a -> BTree a
btree_insert t x = if has_max_elements t then insert (split t) x
                          else insert t x

btree_delete :: Ord a => BTree a -> a -> BTree a
btree_delete (Empty _) _ = error "Underflow"
btree_delete (Leaf _ []) _ = error "Underflow"
btree_delete n@(Node m [k] [t1, t2]) x | not (btree_contains n x) = n
                                       | otherwise = if has_min_elements t1 && has_min_elements t2
                                         then delete (merge k t1 t2) x
                                         else delete n x
btree_delete n x | not (btree_contains n x) = n
                 | otherwise = delete n x


insert :: Ord a => BTree a -> a -> BTree a
insert (Empty m) x = Leaf m [x]
insert (Leaf m []) x = Leaf m [x]
insert l@(Leaf m keys@(k:ks)) x
  | x <= k  = Leaf m (x:keys)
  | x > k  = Leaf m (k:new_ks)
    where Leaf _ new_ks = insert (Leaf m ks) x
insert (Node m [] (t:ts)) x = if has_max_elements t then insert (split t) x
                                                    else Node m [] [insert t x]
insert n@(Node m keys@(k:ks) trees@(t:ts)) x
  | x <= k  = if has_max_elements t then insert (Node m (newK:k:ks) (newT1:newT2:ts)) x
                          else Node m keys (insert t x:ts)
  | x > k  = Node m (k:new_ks) (t:new_ts)
    where Node _ new_ks new_ts = insert (Node m ks ts) x
          Node _ [newK] [newT1, newT2] = split t

split :: Ord a => BTree a -> BTree a
split (Leaf m keys) = Node m [k] [Leaf m k1, Leaf m k2]
  where (k1, k:k2) = halve keys
split (Node m keys trees) = Node m [k] [Node m k1 t1, Node m k2 t2]
  where (k1, k:k2) = halve keys
        (t1, t2) = halve trees

has_max_elements :: Ord a => BTree a -> Bool
has_max_elements (Empty m) = False
has_max_elements (Leaf m ks) = length ks == 2 * m - 1
has_max_elements (Node m ks _) = length ks == 2 * m - 1


has_min_elements :: Ord a => BTree a -> Bool
has_min_elements (Empty _) = False
has_min_elements (Leaf m keys)   = length keys == m - 1
has_min_elements (Node m keys _) = length keys == m - 1

delete :: Ord a => BTree a -> a -> BTree a
delete l@(Leaf _ _) x = delete_from_leaf l x
delete n@(Node m [k] [t1, t2]) x
  | x == k = delete_here n x
  | x < k  = delete_middle n x
  | x > k  = delete_last n x
delete n@(Node m (k:ks) (t1:t2:ts)) x
  | x == k = delete_here n x
  | x < k  = delete_middle n x
  | x > k  = Node m (k:new_ks) (t1:new_ts)
    where Node _ new_ks new_ts = delete (Node m ks (t2:ts)) x

delete_from_leaf :: Ord a => BTree a -> a -> BTree a
delete_from_leaf l@(Leaf m (k:ks)) x
  | x == k = Leaf m ks
  | x < k  = l
  | x > k  = Leaf m (k:new_ks) where Leaf _ new_ks = delete_from_leaf (Leaf m ks) x

delete_here :: Ord a => BTree a -> a -> BTree a
delete_here (Node m (k:ks) (t1:t2:ts)) x
  | has_min_elements t1 && has_min_elements t2 = Node m ks (delete (merge k t1 t2) x:ts)
  | has_min_elements t1 = Node m (get_min t2:ks) (t1:delete_min t2:ts)
  | otherwise = Node m (get_max t1:ks) (delete_max t1:t2:ts)

delete_middle :: Ord a => BTree a -> a -> BTree a
delete_middle (Node m (k:ks) (t1:t2:ts)) x
  | has_min_elements t1 && has_min_elements t2 = Node m ks (delete (merge k t1 t2) x:ts)
  | has_min_elements t1 = Node m (shifted_k:ks) (delete shifted_t1 x:shifted_t2:ts)
  | otherwise = Node m (k:ks) (delete t1 x:t2:ts)
  where
      Node _ [shifted_k] [shifted_t1, shifted_t2] = shift_left k t1 t2

delete_last :: Ord a => BTree a -> a -> BTree a
delete_last (Node m [k] [t1, t2]) x
  | has_min_elements t2 && has_min_elements t1 = Node m [] [delete (merge k t1 t2) x]
  | has_min_elements t2 = Node m [shifted_k] [shifted_t1, delete shifted_t2 x]
  | otherwise = Node m [k] [t1, delete t2 x]
  where
      Node _ [shifted_k] [shifted_t1, shifted_t2] = shift_right k t1 t2

merge :: Ord a => a -> BTree a -> BTree a -> BTree a
merge k (Leaf m1 keys1) (Leaf _ keys2) = Leaf m1 (keys1 ++ [k] ++ keys2)
merge k (Node m1 keys1 trees1) (Node _ keys2 trees2) = Node m1 (keys1 ++ [k] ++ keys2) (trees1 ++ trees2)


shift_left :: Ord a => a -> BTree a -> BTree a -> BTree a
shift_left k (Leaf m keys1) (Leaf _ (k2:keys2)) = Node m [k2] [Leaf m (keys1 ++ [k]), Leaf m keys2]
shift_left k (Node m keys1 trees1) (Node _ (k2:keys2) (t2:trees2)) = Node m [k2] [Node m (keys1 ++ [k]) (trees1 ++ [t2]), Node m keys2 trees2]

shift_right :: Ord a => a -> BTree a -> BTree a -> BTree a
shift_right k (Leaf m keys1) (Leaf _ keys2) = Node m [last keys1] [Leaf m (init keys1), Leaf m (k:keys2)]
shift_right k (Node m keys1 trees1) (Node _ keys2 trees2) = Node m [last keys1] [Node m (init keys1) (init trees1), Node m (k:keys2) (last trees1:trees2)]

get_min :: Ord a => BTree a -> a
get_min (Leaf _ keys) = head keys
get_min (Node _ _ trees) = get_min (head trees)

delete_min :: Ord a => BTree a -> BTree a
delete_min (Leaf m keys) = Leaf m (tail keys)
delete_min (Node m keys (t:ts)) = Node m keys (delete_min t:ts)

get_max :: Ord a => BTree a -> a
get_max (Leaf _ keys) = last keys
get_max (Node _ _ trees) = get_max (last trees)

delete_max :: Ord a => BTree a -> BTree a
delete_max (Leaf m keys) = Leaf m (init keys)
delete_max (Node m keys trees) = Node m keys (init trees ++ [delete_max (last trees)])

halve :: [a] -> ([a], [a])
halve ls = splitAt (div (length ls) 2) ls

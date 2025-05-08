{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

data BTree a = Empty Int | Leaf Int [a] | Node Int [a] [BTree a] deriving (Show, Read)
{- 
  Задекларували три конструктори:
    Пустий вузол – містить лише інформацію про порядок Б-дерева
    Листя – містить порядок дерева та список ключів
    Вузол – місить порядок дерева, список ключів та список дочірніх вузлів Б-дерева
-}

btree_construct :: Ord a => Int -> [a] -> BTree a
{- 
  По черзі вставляємо ключі з списку в пусте дерево порядку k
-}
btree_construct k = foldl btree_insert (Empty k)


btree_contains :: Ord a => BTree a -> a -> Bool
{-
  Перевірка на те, чи існує ключ в дереві
-}
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
{-  
  Вставка ключа в дерево
-}
btree_insert t x = if has_max_elements t then insert (split t) x -- якщо корінь повний, то перед вставкою розділяємо його
                          else insert t x

btree_delete :: Ord a => BTree a -> a -> BTree a
{- 
  Видалення ключа з дерева 
-}
btree_delete n@(Empty _) _ = n
btree_delete n@(Leaf _ []) _ = n
btree_delete n@(Node m [k] [t1, t2]) x | not (btree_contains n x) = n
                                       | otherwise = if has_min_elements t1 && has_min_elements t2
                                         then delete (merge k t1 t2) x
                                         else delete n x
btree_delete n x | not (btree_contains n x) = n
                 | otherwise = delete n x



insert :: Ord a => BTree a -> a -> BTree a
{-
 Основна реалізація логіки вставки ключа
-}
insert (Empty m) x = Leaf m [x]
insert (Leaf m []) x = Leaf m [x]
insert l@(Leaf m keys@(k:ks)) x -- лінійно проходимося по ключам листка поки не знайдемо місце куди має стати новий ключ
  | x <= k  = Leaf m (x:keys)
  | x > k  = Leaf m (k:new_ks)
    where Leaf _ new_ks = insert (Leaf m ks) x
insert (Node m [] (t:_)) x = if has_max_elements t then insert (split t) x -- вставляємо ключ в останній дочірній вузол вузла
                                                    else Node m [] [insert t x]
insert n@(Node m keys@(k:ks) trees@(t:ts)) x -- лінійно проходимося по всім ключам вузла поки не знайдемо більший за той, що намагаємося вставити
  | x <= k  = if has_max_elements t then insert (Node m (newK:k:ks) (newT1:newT2:ts)) x
                          else Node m keys (insert t x:ts)
  | x > k  = Node m (k:new_ks) (t:new_ts)
    where Node _ new_ks new_ts = insert (Node m ks ts) x
          Node _ [newK] [newT1, newT2] = split t


split :: Ord a => BTree a -> BTree a -- Перетворює вузол на вузол з двома дочірніми вузлами та ключем для їх розділення
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

delete :: Ord a => BTree a -> a -> BTree a -- Лінійно проходить по ключам вузла поки не знайде ключ який потрібно видалити, або поки не перейде в піддерево, щоб видаляти ключ у ньому
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

delete_from_leaf :: Ord a => BTree a -> a -> BTree a -- Лінійно проходиться по ключвм в листку поки не знайде той, що треба видалити
delete_from_leaf l@(Leaf m (k:ks)) x
  | x == k = Leaf m ks
  | x < k  = l
  | x > k  = Leaf m (k:new_ks) where Leaf _ new_ks = delete_from_leaf (Leaf m ks) x

delete_here :: Ord a => BTree a -> a -> BTree a -- Видаляє перший ключ у вузлі
delete_here (Node m (k:ks) (t1:t2:ts)) x
  | has_min_elements t1 && has_min_elements t2 = Node m ks ((delete (merge k t1 t2) x):ts)
  | has_min_elements t1 = Node m (get_min t2:ks) (t1:(delete_min t2):ts)
  | otherwise = Node m (get_max t1:ks) ((delete_max t1):t2:ts)

delete_middle :: Ord a => BTree a -> a -> BTree a -- Видаляє ключ з першого дочірнього дерева вузла
delete_middle (Node m (k:ks) (t1:t2:ts)) x
  | has_min_elements t1 && has_min_elements t2 = Node m ks ((delete (merge k t1 t2) x):ts)
  | has_min_elements t1 = Node m (shifted_k:ks) ((delete shifted_t1 x):shifted_t2:ts)
  | otherwise = Node m (k:ks) ((delete t1 x):t2:ts)
  where
      Node _ [shifted_k] [shifted_t1, shifted_t2] = shift_left k t1 t2

delete_last :: Ord a => BTree a -> a -> BTree a -- Видаляє ключ з останнього дочірнього дерева вузла
delete_last (Node m [k] [t1, t2]) x
  | has_min_elements t2 && has_min_elements t1 = Node m [] [delete (merge k t1 t2) x]
  | has_min_elements t2 = Node m [shifted_k] [shifted_t1, delete shifted_t2 x]
  | otherwise = Node m [k] [t1, delete t2 x]
  where
      Node _ [shifted_k] [shifted_t1, shifted_t2] = shift_right k t1 t2

merge :: Ord a => a -> BTree a -> BTree a -> BTree a -- Об'єднує ключ та два вузли в один вузол
merge k (Leaf m1 keys1) (Leaf _ keys2) = Leaf m1 (keys1 ++ [k] ++ keys2)
merge k (Node m1 keys1 trees1) (Node _ keys2 trees2) = Node m1 (keys1 ++ [k] ++ keys2) (trees1 ++ trees2)


shift_left :: Ord a => a -> BTree a -> BTree a -> BTree a -- З ключа К та двох вузлів(А і Б) формує вузол з найменшим ключем вузла Б та дочірніми вузлами А з ключем К та вузлом Б без найменшого ключа
shift_left k (Leaf m keys1) (Leaf _ (k2:keys2)) = Node m [k2] [Leaf m (keys1 ++ [k]), Leaf m keys2]
shift_left k (Node m keys1 trees1) (Node _ (k2:keys2) (t2:trees2)) = Node m [k2] [Node m (keys1 ++ [k]) (trees1 ++ [t2]), Node m keys2 trees2]

shift_right :: Ord a => a -> BTree a -> BTree a -> BTree a -- З ключа К та двох вузлів(А і Б) формує вузол з найбільшим ключем вузла А та дочірніми вузлами А найбільшого ключа та вузла Б з ключем К
shift_right k (Leaf m keys1) (Leaf _ keys2) = Node m [last keys1] [Leaf m (init keys1), Leaf m (k:keys2)]
shift_right k (Node m keys1 trees1) (Node _ keys2 trees2) = Node m [last keys1] [Node m (init keys1) (init trees1), Node m (k:keys2) (last trees1:trees2)]

get_min :: Ord a => BTree a -> a -- Повертає найменший ключ у листі дерева
get_min (Leaf _ keys) = head keys
get_min (Node _ _ trees) = get_min (head trees)

delete_min :: Ord a => BTree a -> BTree a -- видаляє мінімальний ключ у листі дерева
delete_min (Leaf m keys) = Leaf m (tail keys)
delete_min (Node m keys (t:ts)) = Node m keys (delete_min t:ts)

get_max :: Ord a => BTree a -> a -- Повертає найбільший ключ у листі дерева
get_max (Leaf _ keys) = last keys
get_max (Node _ _ trees) = get_max (last trees)

delete_max :: Ord a => BTree a -> BTree a -- видаляє максимальний ключ у листі дерева
delete_max (Leaf m keys) = Leaf m (init keys)
delete_max (Node m keys trees) = Node m keys (init trees ++ [delete_max (last trees)])

halve :: [a] -> ([a], [a]) -- ділить список порівну з різницею в максимум 1 елемент
halve ls = splitAt (div (length ls) 2) ls

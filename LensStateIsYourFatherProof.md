# Lens, State Is Your Father (Informal Proof)

If we provide a `MonadState` instance with focus on `a` and `State s` as monadic
effect, we are actually instantiating a `Lens s a`.

## Given

#### Laws

`MonadState a (State s) { get :: State s a; set :: a -> State s () }` such that:
* GetGet: `get >>= (a1 -> get >>= (a2 -> k (a1, a2))) = get >>= (a -> k (a, a))`
* GetPut: `get >>= put = return ()`
* PutGet: `put a >> get = put a >> return a`
* PutPut: `put a1 >> put a2 = put a2`

#### And defs

```haskell
def view s = eval get s
def update s a = exec (put a) s
```

## Then

#### GetPut

```haskell
> [update (view s) s => s]
  update (view s) s
= [def view]
  update (eval get s) s
= [def update]
  exec (put (eval get s)) s
= [non-effectful return]
  exec (put (eval get s)) (exec (return ()) s)
= [MonadState - GetPut]
  exec (put (eval get s)) (exec (get >>= put) s)
= [MonadState - GetGet]
  exec (put (eval get s)) (exec (get >>= (_ -> get >>= put)) s)
= [MonadState - GetPut]
  exec (put (eval get s)) (exec (get >>= (_ -> return ())) s)
= [def >>]
  exec (put (eval get s)) (exec (get >> return ()) s)
= [non-effectful return]
  exec (put (eval get s)) (exec get s)
= [def >>=]
  exec (get >>= put) s
= [MonadState - GetPut]
  exec (return ()) s
= [def return, def exec]
  s
◻
```

#### PutGet

```haskell
> [view (update a s) => a]
  view (update a s)
= [def update]
  view (exec (put a) s)
= [def view]
  eval get (exec (put a) s)
= [def >>]
  eval (put a >> get) s
= [MonadState - PutGet]
  eval (put a >> return a) s
= [def >>]
  eval (return a) (exec (put a) s)
= [def eval, def return]
  a
◻
```

#### PutPut

```haskell
> [update a2 (update a1 s) => update a2 s]
  update a2 (update a1 s)
= [def update]
  exec (put a2) (exec (put a1) s)
= [def >>]
  exec (put a1 >> put a2) s
= [MonadState - PutPut]
  exec (put a2) s
= [def update]
  update a2 s
◻
```

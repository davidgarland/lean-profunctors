import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic

/--
  In functional programming, a "profunctor" is a function on types `p : Type u₀ → Type u₁ → Type u₂`
  equipped with an operator called `dimap` which maps contravariantly over the first parameter and covariantly over the second:

  ```
  dimap : (α₂ → α₁) → (β₁ → β₂) → p α₁ β₁ → p α₂ β₂
  lmap  : (α₂ → α₁)             → p α₁ β  → p α₂ β  := (dimap . id) -- default
  rmap  :             (β₁ → β₂) → p α  β₁ → p α  β₂ := dimap id     -- default
  ```

  The quintessential profunctor is `Fun`, where `Fun α β` is a type definition for `α → β`: we use the first argument to `dimap` to
  modify the input, and the second argument to `dimap` to modify the output.
-/
class Profunctor (p : Type u₁ → Type u₂ → Type u₃) where
  /--
  Map contravariantly over a profunctor's first parameter and covariantly over the second.
  
  `(α₂ → α₁) → (β₁ → β₂) → p α₁ β₁ → p α₂ β₂`
  -/
  dimap : (α₂ → α₁) → (β₁ → β₂) → p α₁ β₁ → p α₂ β₂
  
  /--
  Map contravariantly over the first parameter of a profunctor.
  
  `(α₂ → α₁) → p α₁ β → p α₂ β`
  -/
  lmap : (α₂ → α₁) → p α₁ β  → p α₂ β  := (dimap . id)

  /--
  Map covariantly over the second parameter of a profunctor.
  
  `(β₁ → β₂) → p α β₁ → p α β₂`
  -/
  rmap : (β₁ → β₂) → p α  β₁ → p α  β₂ := dimap id

/--
  `Strong` extends `Profunctor` with three new operations:

  ```
  lensE  : (σ → α) → (σ → β → τ) → p α β → p σ τ
  first  : p α β → p (α × δ) (β × δ) := lens Prod.fst (func (_, c) b => (b, c)) -- default
  second : p α β → p (δ × α) (δ × β) := lens Prod.snd (func (c, _) b => (c, b)) -- default
  ```
-/
class Strong (p : Type u₁ → Type u₁ → Type u₂) extends Profunctor p where
  /--
  Create a lens in the profunctor encoding of optics given a getter and setter function.

  `(σ → α) → (σ → β → τ) → p α β → p σ τ`
  -/
  lensE : (σ → α) → (σ → β → τ) → p α β → p σ τ -- := fun get set p => dimap (fun s => (get s, s)) (fun (b, s) => set s b) (first p)
  
  /--
  Carry extra information of type `δ` through a profunctor, putting the original `α` and `β` first.

  `p α β → p (α × δ) (β × δ)`
  -/
  first {δ : Type u₁} : p α β → p (α × δ) (β × δ) := lensE Prod.fst (fun (_, c) b => (b, c))

  /--
  Carry extra information of type `δ` through a profunctor, putting the original `α` and `β` second.

  `p α β → p (δ × α) (δ × β)`
  -/
  second {δ : Type u₁} : p α β → p (δ × α) (δ × β) := lensE Prod.snd (fun (c, _) b => (c, b)) --dimap Prod.swap Prod.swap ∘ first

/--
  `Choice` extends `Profunctor` with three new operations:

  ```
  prismE : (β → τ) → (σ → τ ⊕ α) → p α β → p σ τ 
  left   : p α β → p (α ⊕ δ) (β ⊕ δ) := prismE (Sum.inl) (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)) -- default
  right  : p α β → p (δ ⊕ α) (δ ⊕ β) := prismE (Sum.inr) (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) -- default
  ```
-/
class Choice (p : Type u₁ → Type u₁ → Type u₂) extends Profunctor p where
  /--
  Create a prism in the profunctor encoding of optics given a constructing and matching function.

  `(β → τ) → (σ → τ ⊕ α) → p α β → p σ τ`
  -/
  prismE : (β → τ) → (σ → τ ⊕ α) → p α β → p σ τ 
 
  /--
  `p α β → p (α ⊕ δ) (β ⊕ δ)`
  -/
  left {δ : Type u₁} : p α β → p (α ⊕ δ) (β ⊕ δ) := prismE (Sum.inl) (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr))

  /--
  `p α β → p (δ ⊕ α) (δ ⊕ β)`
  -/
  right {δ : Type u₁} : p α β → p (δ ⊕ α) (δ ⊕ β) := prismE (Sum.inr) (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)

/--
  `Costrong` extends `Profunctor` with two new operations:

  ```
  unfirst  : p (α × δ) (β × δ) → p α β
  unsecond : p (δ × α) (δ × β) → p α β := unfirst ∘ dimap Prod.swap Prod.swap -- default
  ```
-/
class Costrong (p : Type u₁ → Type u₁ → Type u₂) extends Profunctor p where
  /--
  `p (α × δ) (β × δ) → p α β`
  -/
  unfirst {δ : Type u₁} : p (α × δ) (β × δ) → p α β
  
  /--
  `p (δ × α) (δ × β) → p α β`
  -/
  unsecond {δ : Type u₁} : p (δ × α) (δ × β) → p α β := unfirst ∘ dimap Prod.swap Prod.swap

/--
  `Cochoice` extends `Profunctor` with two new operations:
 
  ```
  unleft  : p (α ⊕ δ) (β ⊕ δ) → p α β
  unright : p (δ ⊕ α) (δ ⊕ β) → p α β := unleft ∘ dimap Sum.swap Sum.swap -- default
  ```
-/
class Cochoice (p : Type u₁ → Type u₁ → Type u₂) extends Profunctor p where
  /--
  `p (α ⊕ δ) (β ⊕ δ) → p α β`
  -/
  unleft {δ : Type u₁} : p (α ⊕ δ) (β ⊕ δ) → p α β

  /--
  `p (δ ⊕ α) (δ ⊕ β) → p α β`
  -/
  unright {δ : Type u₁} : p (δ ⊕ α) (δ ⊕ β) → p α β := unleft ∘ dimap Sum.swap Sum.swap

/--
  `Closed` extends `Profunctor` with a new operation:

  ```
  closed : p α β → p (δ → α) (δ → β)
  ```
-/
class Closed (p : Type u₁ → Type u₁ → Type u₂) extends Profunctor p where
  /-- `p α β → p (δ → α) (δ → β)`-/
  closed {δ : Type u₁} : p α β → p (δ → α) (δ → β)

/--
  `Wander` extends `Profunctor` with two new operations:

  ```
  wander : (∀{f}[Applicative f], (α → f β) → σ → f τ) → p α β → p σ τ
  traverse' [Traversable f] : p α β → p (f α) (f β) := wander traverse -- default
  ```
-/
class Wander (p : Type u₁ → Type u₁ → Type u₂) extends Profunctor p where
  /--
  `(∀{f}[Applicative f], (α → f β) → σ → f τ) → p α β → p σ τ`
  -/
  wander : (∀{f : Type u₁ → Type u₁}[Applicative f], (α → f β) → σ → f τ) → p α β → p σ τ
  
  /--
  `∀{f}[Traversable f], p α β → p (f α) (f β)`
  -/
  traverse' [Traversable f] : p α β → p (f α) (f β) := wander traverse

/--
  `Traversing` bundles `Wander`, `Strong`, and `Choice` together.
-/
class Traversing (p : Type u₁ → Type u₁ → Type u₂) extends Wander p, Strong p, Choice p
instance [Wander p] [Strong p] [Choice p] : Traversing p where
  lensE  := Strong.lensE
  prismE := Choice.prismE

/--
  `Roam` extends `Profunctor` with two new operations:

  ```
  roam : ((α → β) → σ → τ) → p α β → p σ τ
  map' [Functor f] : p α β → p (f α) (f β) := roam Functor.map
  ```
-/
class Roam (p : Type u₁ → Type u₁ → Type u₂) extends Profunctor p where
  roam : ((α → β) → σ → τ) → p α β → p σ τ
  map' [Functor f] : p α β → p (f α) (f β) := roam Functor.map

/--
  `Mapping` bundles `Traversing`, `Roam` and `Closed` together.
-/
class Mapping (p : Type u₁ → Type u₁ → Type u₂) extends Traversing p, Roam p, Closed p where
instance [Traversing p] [Roam p] [Closed p] : Mapping p where
  roam := Roam.roam
  closed := Closed.closed

/--
  A "bicontravariant" is a function on types `p : Type u₁ → Type u₂ → Type u₃` which is like `Bifunctor` except
  where both sides are mapped over contravariantly instead of covariantly.

  ```
  cimap    : (α₂ → α₁) → (β₂ → β₁) → p α₁ β₁ → p α₂ β₂
  cofirst  : (α₂ → α₁) →             p α₁ β  → p α₂ β  := (cimap . id)
  cosecond :             (β₂ → β₁) → p α  β₁ → p α  β₂ := cimap id
  ```

  This class is exceptionally rare in practice and really only sees use in
  [the implementation of profunctor optics](https://oleg.fi/gists/posts/2017-04-18-glassery.html#getter).
-/
class Bicontravariant (p : Type u₁ → Type u₂ → Type u₃) where
  /--
  Map contravariantly over both sides of a bicontravariant.

  `(α₂ → α₁) → (β₂ → β₁) → p α₁ β₁ → p α₂ β₂`
  -/
  cimap    : (α₂ → α₁) → (β₂ → β₁) → p α₁ β₁ → p α₂ β₂

  /--
  Map contravariantly over the first parameter of a bicontravariant.

  `(α₂ → α₁) → p α₁ β → p α₂ β`
  -/
  cofirst  : (α₂ → α₁) → p α₁ β → p α₂ β := (cimap . id)

  /--
  Map contravariantly over the second parameter of a bicontravariant.

  `(β₂ → β₁) → p α β₁ → p α β₂`
  -/
  cosecond : (β₂ → β₁) → p α β₁ → p α β₂ := cimap id

/--
  `α → β`
-/
def Fun (α : Type u₁) (β : Type u₂) := α → β
def Fun.mk  (f : α → β  ) : Fun α β := f
def Fun.run (f : Fun α β) : α → β   := f

instance : Functor (Fun α) where
  map := (. ∘ .)

instance : Applicative (Fun α) where
  pure x _ := x
  seq f g x := f x (g () x)

instance : Monad (Fun α) where
  bind f p x := p (f x) x

instance : Profunctor Fun where
  dimap f g fn := g ∘ fn ∘ f
  lmap  f   fn :=     fn ∘ f
  rmap    g fn := g ∘ fn

instance : Strong Fun where
  lensE get set f := (fun s => set s (f (get s)))

instance : Choice Fun where
  prismE con case p := Sum.elim id (con ∘ p) ∘ case

instance : Closed Fun where
  closed := Function.comp

instance : Wander Fun where
  wander f p := Id.run ∘ f p

instance : Roam Fun where
  roam f p := f p

/--
  Kleisli arrows of a monad.
  
  `α → f β`
-/
def Kleisli (f : Type u₁ → Type u₂) (α β : Type u₁) := α → f β
def Kleisli.mk (fn : α → f β) : Kleisli f α β := fn
def Kleisli.run (fn : Kleisli f α β) : α → f β := fn

instance [Functor f] : Functor (Kleisli f α) where
  map f p x := Functor.map f (p x)

instance [Applicative f] : Applicative (Kleisli f α) where
  pure x := fun _ => Pure.pure x
  seq f g x := Seq.seq (f x) (g . x)

instance [Monad f] : Monad (Kleisli f α) where
  bind f k x := Bind.bind (f x) (fun a => k a x)

instance [Functor f] : Profunctor (Kleisli f) where
  dimap f g p := fun x => (g <$> .) $ p (f x)

instance [Functor f] : Strong (Kleisli f) where
  lensE get set p := fun s => set s <$> p (get s)

instance [Applicative f] : Choice (Kleisli f) where
  prismE con case p := Sum.elim Pure.pure (con <$> p .) ∘ case

instance [Applicative f] : Wander (Kleisli f) where
  wander f p := f p

/--
  `α → r`
-/
def Forget (r : Type u₁) (α _β : Type u₂) := α → r 
def Forget.mk (fn : α → r) : Forget r α _β := fn
def Forget.run (fn : Forget r α _β) : α → r := fn

instance : Functor (Forget r α) where
  map _ p := p

instance : Bicontravariant (Forget r) where
  cimap f _ p := fun a => p (f a)

instance : Profunctor (Forget r) where
  dimap f _ p := fun a => p (f a)

instance : Strong (Forget r) where
  lensE get _ p := p ∘ get

instance [Monoid r] : Choice (Forget r) where
  prismE _ case p := Sum.elim (fun _ => One.one) p ∘ case

instance : Cochoice (Forget r) where
  unleft p := p ∘ Sum.inl

instance [Monoid r] : Wander (Forget r) where
  wander f p := f (Functor.Const.mk ∘ p)

/--
  `α → Option r`
-/
def Forget? (r : Type u₁) (α _β : Type u₂) := α → Option r
def Forget?.mk (fn : α → Option r) : Forget? r α _β := fn
def Forget?.run (fn : Forget? r α _β) : α → Option r := fn

instance : Functor (Forget? r α) where
  map _ p := p

instance : Bicontravariant (Forget? r) where
  cimap f _ p := p ∘ f

instance : Profunctor (Forget? r) where
  dimap f _ p := p ∘ f

instance : Strong (Forget? r) where
  lensE get _ p := p ∘ get

instance : Choice (Forget? r) where
  prismE _ case p := Sum.elim (fun _ => none) p ∘ case

instance : Cochoice (Forget? r) where
  unleft p := p ∘ Sum.inl

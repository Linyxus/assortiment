import Mathlib.Data.Fin.Basic

/-!
# Contextual Modal Capture Calculus
!-/
namespace CMCC

/-!
## Finite number maps
!-/
def FinMap (n : Nat) (n' : Nat) := Fin n -> Fin n'

def FinMap.ext (f : FinMap n n') : FinMap n.succ n'.succ := by
  intro x
  cases x using Fin.cases
  case zero => exact 0
  case succ x0 => exact (f x0).succ

def FinMap.weaken {n : Nat} : FinMap n n.succ := Fin.succ

def FinMap.open (x : Fin n) : FinMap n.succ n := by
  intro i
  cases i using Fin.cases
  case zero => exact x
  case succ i0 => exact i0

/-!
## Capture sets

### Definition
!-/
inductive CaptureSet : Nat -> Nat -> Type where
| singleton : (x : Fin n) -> CaptureSet n k
| csingleton : (c : Fin k) -> CaptureSet n k
| empty : CaptureSet n k
| union : CaptureSet n k -> CaptureSet n k -> CaptureSet n k

instance : EmptyCollection (CaptureSet n k) where
  emptyCollection := CaptureSet.empty

instance : Union (CaptureSet n k) where
  union := CaptureSet.union

notation:max "{x=" x "}" => CaptureSet.singleton x
notation:max "{c=" c "}" => CaptureSet.csingleton c

/-!
### Renaming
!-/
structure RenameMap (n m k n' m' k' : Nat) where
  map : FinMap n n'
  tmap : FinMap m m'
  cmap : FinMap k k'

def RenameMap.ext (ρ : RenameMap n m k n' m' k') : RenameMap n.succ m k n'.succ m' k' :=
  ⟨ρ.map.ext, ρ.tmap, ρ.cmap⟩

def RenameMap.text (ρ : RenameMap n m k n' m' k') : RenameMap n m.succ k n' m'.succ k' :=
  ⟨ρ.map, ρ.tmap.ext, ρ.cmap⟩

def RenameMap.cext (ρ : RenameMap n m k n' m' k') : RenameMap n m k.succ n' m' k'.succ :=
  ⟨ρ.map, ρ.tmap, ρ.cmap.ext⟩

def RenameMap.weaken : RenameMap n m k n.succ m k := ⟨FinMap.weaken, id, id⟩

def RenameMap.tweaken : RenameMap n m k n m.succ k := ⟨id, FinMap.weaken, id⟩

def RenameMap.cweaken : RenameMap n m k n m k.succ := ⟨id, id, FinMap.weaken⟩

def RenameMap.open (x : Fin n) : RenameMap n.succ m k n m k := ⟨FinMap.open x, id, id⟩

def RenameMap.topen (x : Fin m) : RenameMap n m.succ k n m k := ⟨id, FinMap.open x, id⟩

def RenameMap.copen (x : Fin k) : RenameMap n m k.succ n m k := ⟨id, id, FinMap.open x⟩

def CaptureSet.rename (C : CaptureSet n k) (ρ : RenameMap n m k n' m' k') : CaptureSet n' k' :=
  match C with
  | CaptureSet.singleton x => CaptureSet.singleton (ρ.map x)
  | CaptureSet.csingleton c => CaptureSet.csingleton (ρ.cmap c)
  | CaptureSet.empty => CaptureSet.empty
  | CaptureSet.union C1 C2 => CaptureSet.union (CaptureSet.rename C1 ρ) (CaptureSet.rename C2 ρ)

def CaptureSet.weaken (C : CaptureSet n k) : CaptureSet n.succ k :=
  C.rename (RenameMap.weaken (m := 0))

def CaptureSet.cweaken (C : CaptureSet n k) : CaptureSet n k.succ :=
  C.rename (RenameMap.cweaken (m := 0))

/-!
## Types
!-/

mutual

inductive CType : Nat -> Nat -> Nat -> Type where
| capt (C : CaptureSet n k) (S : SType n m k) : CType n m k

inductive SType : Nat -> Nat -> Nat -> Type where
| top : SType n m k
| tvar : (x : Fin m) -> SType n m k
| forall : CType n m k -> CType (n+1) m k -> SType n m k
| tforall : SType n m k -> CType n (m+1) k -> SType n m k
| cforall : CType n m (k+1) -> SType n m k
| box : CaptureSet n k -> CType n m k -> SType n m k

end

notation:80 S " ^ " C => CType.capt C S
notation:max "⊤" => SType.top
notation:50 "∀(x:" T ")" U => SType.forall T U
notation:50 "∀[X<:" T "]" U => SType.tforall T U
notation:50 "∀[c]" T => SType.cforall T
notation:60 "□[" C "]" T => SType.box C T

/-!
### Renaming
!-/

mutual

def CType.rename (T : CType n m k) (ρ : RenameMap n m k n' m' k') : CType n' m' k' :=
  match T with
  | CType.capt C S => CType.capt (CaptureSet.rename C ρ) (SType.rename S ρ)

def SType.rename (S : SType n m k) (ρ : RenameMap n m k n' m' k') : SType n' m' k' :=
  match S with
  | SType.top => SType.top
  | SType.tvar x => SType.tvar (ρ.tmap x)
  | SType.forall T U => SType.forall (CType.rename T ρ) (CType.rename U ρ.ext)
  | SType.tforall T U => SType.tforall (SType.rename T ρ) (CType.rename U ρ.text)
  | SType.cforall T => SType.cforall (CType.rename T ρ.cext)
  | SType.box C T => SType.box (C.rename ρ) (CType.rename T ρ)

end

def CType.weaken (T : CType n m k) : CType n.succ m k := T.rename RenameMap.weaken

def SType.weaken (S : SType n m k) : SType n.succ m k := S.rename RenameMap.weaken

def CType.tweaken (T : CType n m k) : CType n m.succ k := T.rename RenameMap.tweaken

def SType.tweaken (S : SType n m k) : SType n m.succ k := S.rename RenameMap.tweaken

def CType.cweaken (T : CType n m k) : CType n m k.succ := T.rename RenameMap.cweaken

def SType.cweaken (S : SType n m k) : SType n m k.succ := S.rename RenameMap.cweaken

def CType.open {n : Nat} (T : CType n.succ m k) (x : Fin n) : CType n m k :=
  T.rename (RenameMap.open x)

/-!
## Terms
!-/

inductive Term : Nat -> Nat -> Nat -> Type where
| var : Fin n -> Term n m k
| abs : CType n m k -> Term n.succ m k -> Term n m k
| tabs : SType n m k -> Term n m.succ k -> Term n m k
| cabs : Term n m k.succ -> Term n m k
| app : Fin n -> Fin n -> Term n m k
| tapp : Fin n -> SType n m k -> Term n m k
| capp : Fin n -> CaptureSet n k -> Term n m k
| box : Term n m k -> Term n m k
| unbox : CaptureSet n k -> Fin n -> Term n m k
| letin : Term n m k -> Term n.succ m k -> Term n m k

notation:60 "λ(x:" T ")" t => Term.abs T t
notation:60 "λ[X<:" S "]" t => Term.tabs S t
notation:60 "λ[c]" t => Term.cabs t

/-!
### Renaming
!-/

def Term.rename (t : Term n m k) (ρ : RenameMap n m k n' m' k') : Term n' m' k' :=
  match t with
  | Term.var x => Term.var (ρ.map x)
  | Term.abs T t => Term.abs (CType.rename T ρ) (t.rename ρ.ext)
  | Term.tabs S t => Term.tabs (SType.rename S ρ) (t.rename ρ.text)
  | Term.cabs t => Term.cabs (t.rename ρ.cext)
  | Term.app f x => Term.app (ρ.map f) (ρ.map x)
  | Term.tapp f S => Term.tapp (ρ.map f) (SType.rename S ρ)
  | Term.capp f C => Term.capp (ρ.map f) (CaptureSet.rename C ρ)
  | Term.box t => Term.box (t.rename ρ)
  | Term.unbox C x => Term.unbox (CaptureSet.rename C ρ) (ρ.map x)
  | Term.letin t1 t2 => Term.letin (t1.rename ρ) (t2.rename ρ.ext)

def Term.open {n : Nat} (t : Term n.succ m k) (x : Fin n) : Term n m k :=
  t.rename (RenameMap.open x)

def Term.weaken (t : Term n m k) : Term (n+1) m k := t.rename RenameMap.weaken

def Term.tweaken (t : Term n m k) : Term n m.succ k := t.rename RenameMap.tweaken

def Term.cweaken (t : Term n m k) : Term n m k.succ := t.rename RenameMap.cweaken

/-!
## Substitution
!-/

def TypeMap (m n' m' k' : Nat) := Fin m -> SType n' m' k'

def CaptureMap (k n' k' : Nat) := Fin k -> CaptureSet n' k'

def TypeMap.ext (f : TypeMap m n' m' k') : TypeMap m n'.succ m' k' :=
  fun X => (f X).weaken

def CaptureMap.ext (f : CaptureMap k n' k') : CaptureMap k n'.succ k' :=
  fun c => (f c).weaken

def TypeMap.open (S : SType n m k) : TypeMap m.succ n m k := by
  intro i
  cases i using Fin.cases
  case zero => exact S
  case succ i0 => exact (SType.tvar i0)

def CaptureMap.open (C : CaptureSet n k) : CaptureMap k.succ n k := by
  intro c
  cases c using Fin.cases
  case zero => exact C
  case succ c0 => exact {c=c0}

def TypeMap.text (f : TypeMap m n' m' k') : TypeMap m.succ n' m'.succ k' := by
  intro X
  cases X using Fin.cases
  case zero => exact (SType.tvar 0)
  case succ X0 => exact (f X0).tweaken

def TypeMap.cext (f : TypeMap m n' m' k') : TypeMap m n' m' k'.succ :=
  fun X => (f X).cweaken

def CaptureMap.cext (f : CaptureMap k n' k') : CaptureMap k.succ n' k'.succ := by
  intro c
  cases c using Fin.cases
  case zero => exact {c=0}
  case succ c0 => exact (f c0).cweaken

def TypeMap.id : TypeMap m n m k := fun X => SType.tvar X

def CaptureMap.id : CaptureMap k n k := fun c => {c=c}

structure SubstMap (n m k n' m' k' : Nat) where
  map : FinMap n n'
  tmap : TypeMap m n' m' k'
  cmap : CaptureMap k n' k'

def SubstMap.ext (σ : SubstMap n m k n' m' k') : SubstMap n.succ m k n'.succ m' k' :=
  ⟨σ.map.ext, σ.tmap.ext, σ.cmap.ext⟩

def SubstMap.text (σ : SubstMap n m k n' m' k') : SubstMap n m.succ k n' m'.succ k' :=
  ⟨σ.map, σ.tmap.text, σ.cmap⟩

def SubstMap.cext (σ : SubstMap n m k n' m' k') : SubstMap n m k.succ n' m' k'.succ :=
  ⟨σ.map, σ.tmap.cext, σ.cmap.cext⟩

def SubstMap.topen (S : SType n m k) : SubstMap n m.succ k n m k := ⟨id, TypeMap.open S, CaptureMap.id⟩

def SubstMap.copen (C : CaptureSet n k) : SubstMap n m k.succ n m k := ⟨id, TypeMap.id, CaptureMap.open C⟩

def CaptureSet.subst (C : CaptureSet n k) (σ : SubstMap n m k n' m' k') : CaptureSet n' k' :=
  match C with
  | singleton x => singleton (σ.map x)
  | csingleton c => σ.cmap c
  | empty => empty
  | union C1 C2 => union (C1.subst σ) (C2.subst σ)

mutual

def SType.subst (S : SType n m k) (σ : SubstMap n m k n' m' k') : SType n' m' k' :=
  match S with
  | SType.top => SType.top
  | SType.tvar x => σ.tmap x
  | SType.forall T U => SType.forall (T.subst σ) (U.subst σ.ext)
  | SType.tforall T U => SType.tforall (T.subst σ) (U.subst σ.text)
  | SType.cforall T => SType.cforall (T.subst σ.cext)
  | SType.box C T => SType.box (C.subst σ) (T.subst σ)

def CType.subst (T : CType n m k) (σ : SubstMap n m k n' m' k') : CType n' m' k' :=
  match T with
  | CType.capt C S => CType.capt (C.subst σ) (S.subst σ)

end

def Term.subst (t : Term n m k) (σ : SubstMap n m k n' m' k') : Term n' m' k' :=
  match t with
  | Term.var x => Term.var (σ.map x)
  | Term.abs T t => Term.abs (T.subst σ) (t.subst σ.ext)
  | Term.tabs S t => Term.tabs (S.subst σ) (t.subst σ.text)
  | Term.cabs t => Term.cabs (t.subst σ.cext)
  | Term.app f x => Term.app (σ.map f) (σ.map x)
  | Term.tapp f S => Term.tapp (σ.map f) (S.subst σ)
  | Term.capp f C => Term.capp (σ.map f) (C.subst σ)
  | Term.box t => Term.box (t.subst σ)
  | Term.unbox C x => Term.unbox (C.subst σ) (σ.map x)
  | Term.letin t1 t2 => Term.letin (t1.subst σ) (t2.subst σ.ext)

def CType.topen {m : Nat} (T : CType n m.succ k) (S : SType n m k) : CType n m k :=
  T.subst (SubstMap.topen S)

def CType.copen {k : Nat} (T : CType n m k.succ) (C : CaptureSet n k) : CType n m k :=
  T.subst (SubstMap.copen C)

def Term.topen {m : Nat} (t : Term n m.succ k) (S : SType n m k) : Term n m k :=
  t.subst (SubstMap.topen S)

def Term.copen {k : Nat} (t : Term n m k.succ) (C : CaptureSet n k) : Term n m k :=
  t.subst (SubstMap.copen C)

/-!
## Context
!-/

inductive Context : Nat -> Nat -> Nat -> Type where
| empty : Context 0 0 0
| var : Context n m k -> CType n m k -> Context n.succ m k
| tvar : Context n m k -> SType n m k -> Context n m.succ k
| cvar : Context n m k -> Context n m k.succ

inductive Context.Bound : Context n m k -> Fin n -> CType n m k -> Prop where
| here :
  Context.Bound (Context.var Γ T) 0 T.weaken
| there_var :
  Context.Bound Γ x T ->
  Context.Bound (Context.var Γ T') x.succ T.weaken
| there_tvar :
  Context.Bound Γ x T ->
  Context.Bound (Context.tvar Γ S) x T.tweaken
| there_cvar :
  Context.Bound Γ x T ->
  Context.Bound (Context.cvar Γ) x T.cweaken

inductive Context.TBound : Context n m k -> Fin m -> SType n m k -> Prop where
| here :
  Context.TBound (Context.tvar Γ S) 0 S.tweaken
| there_var :
  Context.TBound Γ x S ->
  Context.TBound (Context.var Γ T) x S.weaken
| there_tvar :
  Context.TBound Γ x S ->
  Context.TBound (Context.tvar Γ S') x.succ S.tweaken
| there_cvar :
  Context.TBound Γ x S ->
  Context.TBound (Context.cvar Γ) x S.cweaken

/-!
## Subcapturing
!-/

inductive CaptureSet.Subset : CaptureSet n k -> CaptureSet n k -> Prop where
| refl :
  CaptureSet.Subset C C
| empty :
  CaptureSet.Subset CaptureSet.empty C
| unionl :
  C1.Subset C ->
  C2.Subset C ->
  CaptureSet.Subset (C1 ∪ C2) C
| unionrr :
  C.Subset C1 ->
  CaptureSet.Subset C (C1 ∪ C2)
| unionrl :
  C.Subset C2 ->
  CaptureSet.Subset C (C1 ∪ C2)

instance : HasSubset (CaptureSet n k) where
  Subset := CaptureSet.Subset

inductive Subcapture : Context n m k -> CaptureSet n k -> CaptureSet n k -> Prop where
| sc_var :
  Context.Bound Γ x (S^C) ->
  Subcapture Γ {x= x} C
| sc_elem :
  C1 ⊆ C2 ->
  Subcapture Γ C1 C2
| sc_set :
  Subcapture Γ C1 C ->
  Subcapture Γ C2 C ->
  Subcapture Γ (C1 ∪ C2) C
| sc_trans :
  Subcapture Γ C1 C2 ->
  Subcapture Γ C2 C3 ->
  Subcapture Γ C1 C3

notation:50 Γ "⊢" C1 "<:c" C2 => Subcapture Γ C1 C2

/-!
## Subtyping
!-/

mutual

inductive CSubtyp : Context n m k -> CType n m k -> CType n m k -> Prop where
| capt :
  (Γ ⊢ C1 <:c C2) ->
  SSubtyp Γ S1 S2 ->
  CSubtyp Γ (S1^C1) (S2^C2)

inductive SSubtyp : Context n m k -> SType n m k -> SType n m k -> Prop where
| refl :
  SSubtyp Γ S S
| top :
  SSubtyp Γ S ⊤
| trans :
  SSubtyp Γ S1 S2 ->
  SSubtyp Γ S2 S3 ->
  SSubtyp Γ S1 S3
| tvar :
  Context.TBound Γ X S ->
  SSubtyp Γ (SType.tvar X) S
| forall :
  CSubtyp Γ T2 T1 ->
  CSubtyp (Γ.var T2) U1 U2 ->
  SSubtyp Γ (∀(x: T1) U1) (∀(x: T2) U2)
| tforall :
  SSubtyp Γ S2 S1 ->
  CSubtyp (Γ.tvar S2) T1 T2 ->
  SSubtyp Γ (∀[X<: S1] T1) (∀[X<: S2] T2)
| cforall :
  CSubtyp (Context.cvar Γ) T1 T2 ->
  SSubtyp Γ (∀[c] T1) (∀[c] T2)
| boxed :
  (Γ ⊢ C1 <:c C2) ->
  CSubtyp Γ T1 T2 ->
  SSubtyp Γ (□[ C1 ] T1) (□[ C2 ] T2)

end

notation:50 Γ "⊢" T1 "<:" T2 => CSubtyp Γ T1 T2
notation:50 Γ "⊢" S1 "<:s" S2 => SSubtyp Γ S1 S2

/-!
## Typing
!-/
inductive Typed : Context n m k -> Term n m k -> CType n m k -> CaptureSet n k -> Prop where
| var :
  Context.Bound Γ x (S^C) ->
  Typed Γ (Term.var x) (S^{x= x}) {x= x}
| sub :
  Typed Γ t T C ->
  (Γ ⊢ T <: T') ->
  (Γ ⊢ C <:c C') ->
  Typed Γ t T' C'
| abs :
  Typed (Context.var Γ T) t U (CaptureSet.weaken C0 ∪ {x=0}) ->
  Typed Γ (λ(x:T)t) ((∀(x:T)U)^C0) {}
| tabs :
  Typed (Context.tvar Γ S) t T C ->
  Typed Γ (λ[X<:S]t) ((∀[X<:S]T)^C) {}
| cabs :
  Typed (Context.cvar Γ) t T (CaptureSet.cweaken C0) ->
  Typed Γ (λ[c]t) ((∀[c]T)^C0) {}
| box :
  Typed Γ t T C ->
  Typed Γ (Term.box t) ((□[C]T)^{}) {}
| app :
  Typed Γ (Term.var x) ((∀(x:T)U)^C) C1 ->
  Typed Γ (Term.var y) T C2 ->
  Typed Γ (Term.app x y) (U.open x) (C1 ∪ C2)
| tapp :
  Typed Γ (Term.var x) ((∀[X<:S]T)^C) C0 ->
  Typed Γ (Term.tapp x S) (T.topen S) C0
| capp :
  Typed Γ (Term.var x) ((∀[c]T)^C) C0 ->
  Typed Γ (Term.capp x C) (T.copen C) C0
| unbox :
  Typed Γ (Term.var x) ((□[C]T)^{}) {} ->
  Typed Γ (Term.unbox C x) T C
| letin :
  Typed Γ t1 T1 C1 ->
  Typed (Context.var Γ T1) t2 (T2.weaken) (C2.weaken) ->
  Typed Γ (Term.letin t1 t2) T2 (C1 ∪ C2)

notation:30 Γ "⊢" t ":" T "@" C => Typed Γ t T C

/-!
### Value
!-/

inductive Term.IsVal : Term n m k -> Prop where
| abs : Term.IsVal (λ(x:T)t)
| tabs : Term.IsVal (λ[X<:S]t)
| cabs : Term.IsVal (λ[c]t)
| box : Term.IsVal (Term.box t)

lemma Term.rename_isval {t : Term n m k}
  (hv : t.IsVal) :
  (t.rename ρ).IsVal := by
  cases hv <;> simp [Term.rename] <;> constructor

def Term.weaken_ext {n : Nat} (t : Term (n+1) m k) : Term (n+2) m k :=
  t.rename RenameMap.weaken.ext

/-!
## Reduction
### Store
!-/
inductive Store : Nat -> Type where
| empty : Store 0
| cons :
  (γ : Store n) ->
  (t : Term n 0 0) ->
  (hv : t.IsVal) ->
  Store (n+1)

inductive Store.Lookup : Store n -> Fin n -> Term n m k -> Prop where
| here :
  Store.Lookup (Store.cons γ t hv) 0 t.weaken
| there :
  Store.Lookup γ x t ->
  Store.Lookup (Store.cons γ t hv) x.succ t.weaken

/-!
### Continuation
!-/
inductive Cont : Nat -> Type where
| empty : Cont n
| cons : Term (n+1) 0 0 -> Cont n -> Cont n

def Cont.weaken (cont : Cont n) : Cont (n+1) :=
  match cont with
  | Cont.empty => Cont.empty
  | Cont.cons t cont => Cont.cons t.weaken_ext cont.weaken

/-!
### State
!-/
structure State (n : Nat) : Type where
  store : Store n
  cont : Cont n
  redex : Term n 0 0

inductive Reduce : State n -> State n' -> Prop where
| apply :
  Store.Lookup γ x (λ(x:T)t) ->
  Reduce
    ⟨γ, cont, Term.app x y⟩
    ⟨γ, cont, t.open y⟩
| tapply :
  Store.Lookup γ x (λ[X<:S]t) ->
  Reduce
    ⟨γ, cont, Term.tapp x S⟩
    ⟨γ, cont, t.topen S⟩
| capply :
  Store.Lookup γ x (λ[c]t) ->
  Reduce
    ⟨γ, cont, Term.capp x C⟩
    ⟨γ, cont, t.copen C⟩
| openbox :
  Store.Lookup γ x (Term.box t) ->
  Reduce
    ⟨γ, cont, Term.unbox C x⟩
    ⟨γ, cont, t⟩
| push :
  Reduce
    ⟨γ, cont, Term.letin t u⟩
    ⟨γ, cont.cons u, t⟩
| lift :
  (hv : Term.IsVal v) ->
  Reduce
    ⟨γ, Cont.cons t cont, v⟩
    ⟨γ.cons v hv, cont.weaken, t⟩
| rename :
  Reduce
    ⟨γ, Cont.cons t cont, Term.var x⟩
    ⟨γ, cont, t.open x⟩

/-!
## Renaming
!-/
structure Rename (Γ : Context n m k) (f : RenameMap n m k n' m' k') (Δ : Context n' m' k') where
  map : ∀ x T, Γ.Bound x T -> Δ.Bound (f.map x) (T.rename f)
  tmap : ∀ X S, Γ.TBound X S -> Δ.TBound (f.tmap X) (S.rename f)

def Rename.ext {Γ : Context n m k} (ρ : Rename Γ f Δ) (T : CType n m k) :
  Rename (Γ.var T) (f.ext) (Δ.var (T.rename f)) := by
  constructor
  case map =>
    intro x T hb
    sorry
  case tmap =>
    intro X S hb
    sorry

end CMCC

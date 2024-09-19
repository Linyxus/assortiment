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

def CaptureSet.rename (C : CaptureSet n k) (ρ : RenameMap n m k n' m' k') : CaptureSet n' k' :=
  match C with
  | CaptureSet.singleton x => CaptureSet.singleton (ρ.map x)
  | CaptureSet.csingleton c => CaptureSet.csingleton (ρ.cmap c)
  | CaptureSet.empty => CaptureSet.empty
  | CaptureSet.union C1 C2 => CaptureSet.union (CaptureSet.rename C1 ρ) (CaptureSet.rename C2 ρ)

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
| box : CType n m k -> SType n m k

end

notation:60 S " ^ " C => CType.capt C S
notation:max "⊤" => SType.top
notation:50 "∀(x:" T ")" U => SType.forall T U
notation:50 "∀[X<:" T "]" U => SType.tforall T U
notation:50 "∀[c]" T => SType.cforall T

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
  | SType.box T => SType.box (CType.rename T ρ)

end

def CType.weaken (T : CType n m k) : CType n.succ m k := T.rename RenameMap.weaken

def SType.weaken (S : SType n m k) : SType n.succ m k := S.rename RenameMap.weaken

def CType.tweaken (T : CType n m k) : CType n m.succ k := T.rename RenameMap.tweaken

def SType.tweaken (S : SType n m k) : SType n m.succ k := S.rename RenameMap.tweaken

def CType.cweaken (T : CType n m k) : CType n m k.succ := T.rename RenameMap.cweaken

def SType.cweaken (S : SType n m k) : SType n m k.succ := S.rename RenameMap.cweaken

/-!
## Terms
!-/

inductive Term : Nat -> Nat -> Nat -> Type where
| var : Fin n -> Term n m k
| abs : CType n m k -> Term n.succ m k -> Term n m k
| tabs : SType n m k -> Term n m.succ k -> Term n m k
| cabs : Term n m k.succ -> Term n m k
| app : Term n m k -> Fin n -> Term n m k
| tapp : Term n m k -> SType n m k -> Term n m k
| capp : Term n m k -> CaptureSet n k -> Term n m k
| box : Term n m k -> Term n m k
| unbox : CaptureSet n k -> Term n m k -> Term n m k
| letin : Term n m k -> Term n.succ m k -> Term n m k

/-!
### Renaming
!-/

def Term.rename (t : Term n m k) (ρ : RenameMap n m k n' m' k') : Term n' m' k' :=
  match t with
  | Term.var x => Term.var (ρ.map x)
  | Term.abs T t => Term.abs (CType.rename T ρ) (t.rename ρ.ext)
  | Term.tabs S t => Term.tabs (SType.rename S ρ) (t.rename ρ.text)
  | Term.cabs t => Term.cabs (t.rename ρ.cext)
  | Term.app t x => Term.app (t.rename ρ) (ρ.map x)
  | Term.tapp t S => Term.tapp (t.rename ρ) (SType.rename S ρ)
  | Term.capp t C => Term.capp (t.rename ρ) (CaptureSet.rename C ρ)
  | Term.box t => Term.box (t.rename ρ)
  | Term.unbox C t => Term.unbox (CaptureSet.rename C ρ) (t.rename ρ)
  | Term.letin t1 t2 => Term.letin (t1.rename ρ) (t2.rename ρ.ext)

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

end

end CMCC

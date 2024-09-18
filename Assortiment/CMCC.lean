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

notation:20 "{x=" x "}" => CaptureSet.singleton x
notation:20 "{c=" c "}" => CaptureSet.csingleton c

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

end CMCC

module

public import StacksFrontier.Algebra.Module.ProZeroTower
public import StacksFrontier.Algebra.Module.SuccTowerSections

/-!
# The compatible sequences of a tower of modules are its categorical inverse limit

A tower of `A`-modules `T : ℕ → ModuleCat A` with transition maps `t n : T (n + 1) ⟶ T n` is the
functor `Stacks.ProZero.towerFunctor` out of `ℕᵒᵖ`, and its inverse limit is realised concretely
as the module `Stacks.ProZero.towerSections` of compatible sequences.  This file proves that the
concrete realisation *is* the categorical limit: the obvious cone on the compatible sequences is
a limit cone, and the resulting comparison is a linear equivalence whose component at `n` is the
term of a compatible sequence there.

This is what lets a statement about `limit F` for `F : ℕᵒᵖ ⥤ ModuleCat A` be read as a statement
about compatible sequences — the form in which an inverse limit of modules of sections is
written down, and the form the operations of
`StacksFrontier.Algebra.Module.SuccTowerSections` act on.

## Main definitions

* `Stacks.ProZero.towerSectionsCone` — the cone over the tower with vertex its compatible
  sequences.
* `Stacks.ProZero.towerSectionsConeIsLimit` — it is a limit cone.
* `Stacks.ProZero.towerSectionsLimitEquiv` — the comparison
  `towerSections T t ≃ₗ[A] limit (towerFunctor T t)`.

## Main results

* `Stacks.ProZero.limit_π_towerSectionsLimitEquiv` — the components of the comparison.

## Implementation notes

No induction on the index is needed anywhere.  The cone is assembled by
`CategoryTheory.NatTrans.ofOpSequence`, which asks for the naturality square only at the
successor transitions, and over the constant functor that square is exactly the compatibility of
a sequence; the universal map is read off the legs of the competing cone, whose compatibility is
again only needed at the successor transitions, where `Cone.w` supplies it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.ProZero

variable {A : Type u} [CommRing A] (T : ℕ → ModuleCat.{v} A) (t : ∀ n, T (n + 1) ⟶ T n)

/-- The projection of the compatible sequences of a tower onto its term at level `n`. -/
def towerSectionsProj (n : ℕ) : ModuleCat.of A (towerSections T t) ⟶ T n :=
  ModuleCat.ofHom
    { toFun x := x.1 n
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- **The cone over a tower of modules with vertex its compatible sequences.**  The leg at
`op n` is the term at level `n`, and the naturality square at a successor transition is the
compatibility of a sequence. -/
def towerSectionsCone : Cone (towerFunctor T t) where
  pt := ModuleCat.of A (towerSections T t)
  π := NatTrans.ofOpSequence
    (F := (Functor.const ℕᵒᵖ).obj (ModuleCat.of A (towerSections T t)))
    (G := towerFunctor T t) (fun n => towerSectionsProj T t n) fun n => by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, towerFunctor,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact ModuleCat.hom_ext (LinearMap.ext fun x => (x.2 n).symm)

/-- The legs of `Stacks.ProZero.towerSectionsCone`. -/
theorem towerSectionsCone_π (n : ℕ) (x : towerSections T t) :
    (towerSectionsCone T t).π.app (op n) x = x.1 n := rfl

/-- **The cone of compatible sequences is a limit cone.**  A cone over the tower is a family of
maps into its terms compatible with the transition maps, which is exactly a map into the
compatible sequences. -/
def towerSectionsConeIsLimit : IsLimit (towerSectionsCone T t) where
  lift c := ModuleCat.ofHom
    { toFun z := ⟨fun n => c.π.app (op n) z, fun n => by
        have hw := c.w (homOfLE (Nat.le_add_right n 1)).op
        rw [show (towerFunctor T t).map (homOfLE (Nat.le_add_right n 1)).op = t n from
          towerMapLE_succ T t n (Nat.le_add_right n 1)] at hw
        exact congrArg (fun φ : c.pt ⟶ T n => φ z) hw⟩
      map_add' z w := Subtype.ext (funext fun n => map_add (c.π.app (op n)).hom z w)
      map_smul' a z := Subtype.ext (funext fun n => map_smul (c.π.app (op n)).hom a z) }
  fac c n := ModuleCat.hom_ext (LinearMap.ext fun z => rfl)
  uniq c f hf := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun z => Subtype.ext (funext fun n => ?_)
    exact congrArg (fun φ : c.pt ⟶ T n => φ z) (hf (op n))

/-- **The compatible sequences of a tower of modules are its categorical inverse limit.** -/
def towerSectionsLimitEquiv :
    towerSections T t ≃ₗ[A] (limit (towerFunctor T t) : ModuleCat.{v} A) :=
  (IsLimit.conePointUniqueUpToIso (towerSectionsConeIsLimit T t)
    (limit.isLimit (towerFunctor T t))).toLinearEquiv

/-- The components of `Stacks.ProZero.towerSectionsLimitEquiv`: the limit projection at `op n`
recovers the term of a compatible sequence at level `n`. -/
theorem limit_π_towerSectionsLimitEquiv (x : towerSections T t) (n : ℕ) :
    limit.π (towerFunctor T t) (op n) (towerSectionsLimitEquiv T t x) = x.1 n :=
  congrArg (fun φ : ModuleCat.of A (towerSections T t) ⟶ T n => φ x)
    (IsLimit.conePointUniqueUpToIso_hom_comp (towerSectionsConeIsLimit T t)
      (limit.isLimit (towerFunctor T t)) (op n))

end Stacks.ProZero

end

module

public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk

/-!
# Freeness and finiteness of stalks under pullback and finite coproducts

Two elementary consequences of the two stalk formulas.

The first is the stalk formula for a pullback, Stacks Tag 0098, in the named form
`AlgebraicGeometry.Scheme.Modules.pullbackStalkEquiv`: the stalk of `p^* F` at `y` is the base
change of the stalk of `F` at `p y` along the map of local rings. Base change along a ring map
carries a free module to a free module and a finite module to a finite module, so freeness and
finiteness of a stalk survive pullback, and the rank of a free stalk is unchanged.

The second is `Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree`: the stalk of
a finite locally free module is finite free. A coproduct of `r` copies of the structure sheaf is
the free module on a type equivalent to `Fin r`, hence finite locally free, so its stalks are
finite free.

## Main results

* `Stacks.StalkFreeBridge.free_stalk_pullback` and
  `Stacks.StalkFreeBridge.finite_stalk_pullback`: freeness, resp. finiteness, of the stalk at
  `p y` is inherited by the stalk of the pullback at `y`.
* `Stacks.StalkFreeBridge.finrank_stalk_pullback`: the rank of a free stalk at `p y` is the rank
  of the stalk of the pullback at `y`.
* `Stacks.StalkFreeBridge.freeAndFinite_stalk_coproductUnit` and
  `Stacks.StalkFreeBridge.free_stalk_coproductUnit`: the stalks of `∐ i : Fin r, 𝒪_X` are finite
  free over the local rings.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace Stacks.StalkFreeBridge

/-- **A free stalk stays free under pullback.** The stalk of `p^* F` at `y` is the base change
of the stalk of `F` at `p y` along the induced map of local rings, by Stacks Tag 0098, and base
change carries a free module to a free module. -/
theorem free_stalk_pullback {X Y : Scheme.{u}} (p : Y ⟶ X) (F : X.Modules) (y : Y)
    (hF : Module.Free (X.presheaf.stalk (p y)) (F.presheaf.stalk (p y))) :
    Module.Free (Y.presheaf.stalk y)
      (((Scheme.Modules.pullback p).obj F).presheaf.stalk y) := by
  let : Algebra (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) :=
    (p.stalkMap y).hom.toAlgebra
  have := hF
  let e : (((Scheme.Modules.pullback p).obj F).presheaf.stalk y) ≃ₗ[Y.presheaf.stalk y]
      TensorProduct (X.presheaf.stalk (p y)) (Y.presheaf.stalk y)
        (F.presheaf.stalk (p y)) :=
    Scheme.Modules.pullbackStalkEquiv p F y
  exact Module.Free.of_equiv e.symm

/-- **A finite stalk stays finite under pullback.** Same proof as `free_stalk_pullback`: the
stalk of the pullback is a base change, and base change carries a finite module to a finite
module. -/
theorem finite_stalk_pullback {X Y : Scheme.{u}} (p : Y ⟶ X) (F : X.Modules) (y : Y)
    (hF : Module.Finite (X.presheaf.stalk (p y)) (F.presheaf.stalk (p y))) :
    Module.Finite (Y.presheaf.stalk y)
      (((Scheme.Modules.pullback p).obj F).presheaf.stalk y) := by
  let : Algebra (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) :=
    (p.stalkMap y).hom.toAlgebra
  have := hF
  let e : (((Scheme.Modules.pullback p).obj F).presheaf.stalk y) ≃ₗ[Y.presheaf.stalk y]
      TensorProduct (X.presheaf.stalk (p y)) (Y.presheaf.stalk y)
        (F.presheaf.stalk (p y)) :=
    Scheme.Modules.pullbackStalkEquiv p F y
  exact Module.Finite.equiv e.symm

/-- **The rank of a free stalk is unchanged by pullback.** Same proof as `free_stalk_pullback`:
by Stacks Tag 0098 the stalk of a pullback is the base change of the stalk at the image point,
and base change preserves the rank of a free module. -/
theorem finrank_stalk_pullback {X Y : Scheme.{u}} (p : Y ⟶ X) (F : X.Modules)
    (y : Y) (x : X) (hxy : p y = x)
    (hF : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    Module.finrank (Y.presheaf.stalk y)
        (((Scheme.Modules.pullback p).obj F).presheaf.stalk y) =
      Module.finrank (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  subst hxy
  let : Algebra (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) :=
    (p.stalkMap y).hom.toAlgebra
  have : Module.Free (X.presheaf.stalk (p y))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (p y)) := hF
  exact (LinearEquiv.finrank_eq (Scheme.Modules.pullbackStalkEquiv p F y)).trans
    Module.finrank_baseChange

/-- The coproduct of `r` copies of the structure sheaf is the free module on a type equivalent
to `Fin r`. -/
def coproductUnitIsoFree {X : Scheme.{u}} (r : ℕ) :
    (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) : X.Modules) :=
  Sigma.whiskerEquiv (f := fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf)
    (g := fun _ : ULift.{u} (Fin r) => SheafOfModules.unit X.ringCatSheaf)
    Equiv.ulift.symm fun _ ↦ Iso.refl _

/-- **The stalks of a finite coproduct of copies of the structure sheaf are finite free.** The
coproduct is the free module on a type equivalent to `Fin r`, hence finite locally free, and the
stalk of a finite locally free module is finite free. -/
theorem freeAndFinite_stalk_coproductUnit {X : Scheme.{u}} (r : ℕ) (x : X) :
    Module.Free (X.presheaf.stalk x)
        ((∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf :
          X.Modules).presheaf.stalk x) ∧
      Module.Finite (X.presheaf.stalk x)
        ((∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf :
          X.Modules).presheaf.stalk x) := by
  have hfree : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin r))) :=
    Stacks.FiniteLocallyFree.instIsFiniteLocallyFreeFree.{u, u, u} _
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso.{u, u, u}
      (R := X.ringCatSheaf)
      (M := SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
      (N := (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules))
      (coproductUnitIsoFree r).symm
  have := isFiniteLocallyFree_of_finiteLocallyFree
    (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules)
  exact freeAndFinite_stalk_of_isFiniteLocallyFree _ x

/-- The freeness half of `freeAndFinite_stalk_coproductUnit`. -/
theorem free_stalk_coproductUnit {X : Scheme.{u}} (r : ℕ) (x : X) :
    Module.Free (X.presheaf.stalk x)
      ((∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf :
        X.Modules).presheaf.stalk x) :=
  (freeAndFinite_stalk_coproductUnit r x).1

end Stacks.StalkFreeBridge

end

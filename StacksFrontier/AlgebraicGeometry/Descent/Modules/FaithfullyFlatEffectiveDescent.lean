module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.EffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FaithfullyFlatEffective
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Faithfully flat descent for modules is effective

Let `R → A` be a faithfully flat ring map. Then every descent datum for modules along `R → A`
is effective, and extension of scalars is an equivalence from `R`-modules onto the category of
descent data. This is Stacks 023N.

The mathematics is already present: descent of modules is effective exactly for the
universally injective ring maps, which is
`ModuleCat.isEffectiveDescentMorphismForModules_iff_universallyInjective` (Stacks 08XA), and a
faithfully flat ring map is universally injective, which is
`Algebra.UniversallyInjective.of_faithfullyFlat` of
`StacksFrontier/AlgebraicGeometry/Descent/Modules/FaithfullyFlatEffective.lean`; that file also
assembles the two into part (2) of Stacks 023N,
`ModuleCat.isEffectiveDescentMorphismForModules_of_faithfullyFlat`. What this file adds are the
further forms of Stacks 023N that consumers ask for.

## Main results

* `ModuleCat.isDescentMorphismForModules_of_faithfullyFlat`: a faithfully flat ring map is a
  descent morphism for modules, i.e. extension of scalars to descent data is fully faithful.
* `ModuleCat.DescentData.isEffective_of_faithfullyFlat` is part (1) of Stacks 023N, in the
  pointwise form: every descent datum for modules along a faithfully flat ring map is
  effective.
* `ModuleCat.DescentData.invariantsBaseChangeEquiv` is the counit of part (3) of Stacks 023N at
  a single descent datum: its base extension of the invariants is the datum itself.

## Implementation notes

Part (1) of Stacks 023N is extracted from part (2) rather than proved separately. The
underlying module of `ModuleCat.canonicalDatum R A M` is `A ⊗[R] M` and its transition
isomorphism sends `(a ⊗ m) ⊗ b` to `a ⊗ (b ⊗ m)` definitionally, so an isomorphism of descent
data from the canonical datum of `M` to `D` has exactly the shape that
`ModuleCat.DescentData.IsEffective` asks for: the underlying `A`-linear isomorphism is the
required `(A ⊗[R] M) ≃ₗ[A] D.module`, and the compatibility is the `comm` field of that
isomorphism evaluated at `(a ⊗ m) ⊗ b`.

`ModuleCat.DescentData.invariantsBaseChangeEquiv` is the counit of part (3) at a single descent
datum, which is all most consumers need.  The identification of the inverse *functor* with
`(N, φ) ↦ H⁰(s(N_•))`, which is what part (3) asserts, is
`Stacks.Descent.faithfullyFlatInvariantsEquivalence_inverse` of
`StacksFrontier/AlgebraicGeometry/Descent/Modules/InvariantsInverseFunctor.lean`.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 08XA](https://stacks.math.columbia.edu/tag/08XA)
* [Stacks Project, Tag 05CK](https://stacks.math.columbia.edu/tag/05CK)
-/

@[expose] public section

universe u w

open CategoryTheory TensorProduct

namespace ModuleCat

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]

/-- A faithfully flat ring map is a descent morphism for modules: extension of scalars from
`R`-modules to descent data along `R → A` is fully faithful. -/
@[sga "4 XVII 6.3.29" "special case"]
public theorem isDescentMorphismForModules_of_faithfullyFlat :
    IsDescentMorphismForModules.{u, u, w} R A :=
  (isDescentMorphismForModules_iff_universallyInjective.{u, w} R A).2
    (Algebra.UniversallyInjective.of_faithfullyFlat R A)

/-- **Stacks 023N, part (1).** Every descent datum for modules along a faithfully flat ring map
`R → A` is effective: it is isomorphic, as a descent datum, to the canonical datum on the
extension of scalars of an `R`-module. -/
@[stacks 023N "effectivity of descent data",
  stacks 03OD "descent data for modules along a faithfully flat ring map are effective",
  sga "1 VIII 1.1" "affine case",
  sga "1 VIII 1.6" "effectivity",
  sga "4½ Arcata 1.4.5" "ess. surj. (affine)", sga "4½ Arcata 1.4" "module case"]
public theorem DescentData.isEffective_of_faithfullyFlat
    (D : DescentData.{u, u, max u w} R A) : D.IsEffective R A := by
  have h : IsEffectiveDescentMorphismForModules.{u, u, w} R A :=
    isEffectiveDescentMorphismForModules_of_faithfullyFlat R A
  set F := (baseExtension.{u, u, w} R A).functor with hF
  set M := F.objPreimage D with hM
  set e : F.obj M ≅ D := F.objObjPreimageIso D with he
  have h1 := congrArg ModuleCat.Hom.hom (congrArg DescentData.Hom.hom e.hom_inv_id)
  have h2 := congrArg ModuleCat.Hom.hom (congrArg DescentData.Hom.hom e.inv_hom_id)
  have hfwd : ∀ x, e.inv.hom.hom (e.hom.hom.hom x) = x := fun x => LinearMap.congr_fun h1 x
  have hbwd : ∀ y, e.hom.hom.hom (e.inv.hom.hom y) = y := fun y => LinearMap.congr_fun h2 y
  refine ⟨M, ?_, ?_⟩
  · exact
    { toFun := fun x => e.hom.hom.hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => map_smul _ a x
      invFun := fun y => e.inv.hom.hom y
      left_inv := hfwd
      right_inv := hbwd }
  · intro a b m
    have hc := LinearMap.congr_fun e.hom.comm
      ((show restrictModule R A (F.obj M).module from (a ⊗ₜ[R] m)) ⊗ₜ[R] b)
    simp only [LinearMap.coe_comp, Function.comp_apply, restrictHom] at hc
    exact hc

/-- The counit of part (3) of Stacks 023N at a single descent datum: for a faithfully flat ring
map `R → A` and every descent datum `D` the base extension of
`ModuleCat.invariantSubmodule R A D` is `D` itself, by the `A`-linear isomorphism sending
`a ⊗ m` to `a • m`. -/
@[sga "1 VIII 1.6"]
public noncomputable def DescentData.invariantsBaseChangeEquiv
    (D : DescentData.{u, u, max u w} R A) :
    (A ⊗[R] invariantSubmodule R A D) ≃ₗ[A] D.module :=
  descentCounitLinearEquiv R A (Algebra.UniversallyInjective.of_faithfullyFlat R A) D

/-- The isomorphism of Stacks 023N, part (3), sends `a ⊗ m` to `a • m`. -/
@[simp]
public theorem DescentData.invariantsBaseChangeEquiv_tmul
    (D : DescentData.{u, u, max u w} R A) (a : A) (m : invariantSubmodule R A D) :
    DescentData.invariantsBaseChangeEquiv R A D (a ⊗ₜ[R] m) = a • (m.1 : D.module) :=
  descentCounitLinearEquiv_tmul R A _ D a m

end ModuleCat

end

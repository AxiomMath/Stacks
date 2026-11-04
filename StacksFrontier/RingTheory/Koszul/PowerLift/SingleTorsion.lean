module

public import StacksFrontier.Homology.DerivedCategory.StrongGenerator
import all StacksFrontier.Homology.DerivedCategory.StrongGenerator
public import StacksFrontier.Homology.DerivedComplete.PrincipalTorsionTower
import all StacksFrontier.Homology.DerivedComplete.PrincipalTorsionTower
public import StacksFrontier.RingTheory.Koszul.PowerLift.HomTorsion

@[expose] public noncomputable section

/-!
# Morphisms from the ring in one degree into a complex with power-torsion cohomology

Let `A` be a commutative ring, let `g : A`, and let `E` be an object of `D(A)`. If every element
of the cohomology module `H^p(E)` is annihilated by some power of `g`, then so is every morphism
`A[-p] ⟶ E` in `D(A)`, where `A[-p]` denotes the ring placed in degree `p`.

This is the base case of the Koszul lifting lemma [Stacks, Tag 08E3]. The Koszul complex of a
sequence of length `m` is an iterated mapping cone built from `A` in degree `0`
([Stacks, Tag 062C]), so `Stacks.Koszul.PowerLift.HomPowerTorsion.of_distTriang₃` propagates the
conclusion below from `A` in the degrees `-m, …, 0` to the whole Koszul complex, which is what
the hypothesis of [Stacks, Tag 08E3] on the cohomology of `E` in degrees `-r + 1, …, 0` is for.

The nontrivial input is that a morphism out of the ring in degree `p` is detected by its effect on
degree-`p` cohomology; that is
`StrongGeneration.derived_single_map_eq_zero`
(`StacksFrontier/Homology/DerivedCategory/StrongGenerator.lean`), proved there from K-projectivity
of the single complex on the free module `A`. It is `private` in that file and is reused here
through `import all` rather than reproved.

## Main results

* `Stacks.Koszul.PowerLift.derivedHomologyMap_smul_id` — scalars act on the cohomology of an
  object of `D(A)` through the scalar action on the object.
* `Stacks.Koszul.PowerLift.homPowerTorsion_singleRing` — power-torsion cohomology in degree `p`
  makes `Hom(A[-p], E)` power torsion.

## Implementation notes

Everything here carries a free `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` binder and mentions
`CategoryTheory.HasDerivedCategory.standard` nowhere, so the results are available at the locally
small model `ModuleCat.hasDerivedCategory`
(`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean`), where the morphisms of `D(A)` are in
`Type u`, as well as at the standard one. The two results this file rests on —
`StrongGeneration.derived_single_map_eq_zero` and
`PrincipalTorsionTower.homologyFunctor_map_Q_smul_id` — sit in files that pin the standard model
at file level, but each is itself stated at a free model binder, because each proof uses only
`DerivedCategory.Q`, `DerivedCategory.quotientCompQhIso`,
`CochainComplex.IsKProjective.Qh_map_bijective` and `DerivedCategory.homologyFunctorFactors`,
all of which Mathlib states for an arbitrary chosen derived category.
`StacksFrontier/RingTheory/Koszul/PowerLift/HomTorsion.lean` is model-free and stays so.

## References

* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
-/

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Koszul.PowerLift

variable {A : Type u} [CommRing A]

/-- A morphism out of the ring in `ModuleCat` is killed by a scalar as soon as its value at `1`
is: the morphism sends `a` to `a` times its value at `1`. -/
private theorem smul_eq_zero_of_smul_one_eq_zero {M : ModuleCat.{u} A}
    (f : ModuleCat.of A A ⟶ M) (r : A) (h : r • f.hom (1 : A) = 0) : r • f = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  have ha : f.hom a = a • f.hom (1 : A) := by
    conv_lhs => rw [show a = a • (1 : A) by simp]
    exact map_smul _ _ _
  simp only [ModuleCat.hom_smul, ModuleCat.hom_zero, LinearMap.smul_apply,
    LinearMap.zero_apply, ha, smul_comm r a, h, smul_zero]

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- **Scalars act on derived cohomology through the object.** For `E` an object of `D(A)` and
`r : A`, the map induced on `H^p` by the scalar multiple `r • 𝟙 E` of the identity is
multiplication by `r`. -/
public theorem derivedHomologyMap_smul_id (E : DerivedCategory (ModuleCat.{u} A)) (p : ℤ)
    (r : A) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).map (r • 𝟙 E) =
      r • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj E) := by
  let C := (DerivedCategory.Q (C := ModuleCat.{u} A)).objPreimage E
  let e := (DerivedCategory.Q (C := ModuleCat.{u} A)).objObjPreimageIso E
  have h1 : r • 𝟙 E = e.inv ≫ DerivedCategory.Q.map (r • 𝟙 C) ≫ e.hom := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp,
      Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]
  rw [h1, Functor.map_comp, Functor.map_comp,
    PrincipalTorsionTower.homologyFunctor_map_Q_smul_id]
  simp only [Linear.smul_comp, Category.id_comp, Linear.comp_smul, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- **Power-torsion cohomology makes morphisms out of the ring power torsion.** If every element
of `H^p(E)` is killed by a power of `g`, then every morphism in `D(A)` from the ring placed in
degree `p` to `E` is killed by a power of `g`.

A morphism `φ` out of the ring in degree `p` is zero as soon as `H^p(φ)` is, and `H^p(φ)` is a map
out of the free module `A`, hence determined by the single element `H^p(φ)(1)` of `H^p(E)`; a power
of `g` killing that element therefore kills `φ`. -/
public theorem homPowerTorsion_singleRing (g : A) (p : ℤ)
    (E : DerivedCategory (ModuleCat.{u} A))
    (hE : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj E,
      ∃ k : ℕ, g ^ k • x = 0) :
    HomPowerTorsion g
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) p).obj (ModuleCat.of A A)) E := by
  intro φ
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) p).app
    (ModuleCat.of A A)
  obtain ⟨k, hk⟩ := hE ((e.inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).map φ).hom (1 : A))
  refine ⟨k, ?_⟩
  apply StrongGeneration.derived_single_map_eq_zero p
  rw [show g ^ k • φ = φ ≫ (g ^ k • 𝟙 E) by rw [Linear.comp_smul, Category.comp_id],
    Functor.map_comp, derivedHomologyMap_smul_id, Linear.comp_smul, Category.comp_id,
    ← cancel_epi e.inv, comp_zero, Linear.comp_smul]
  exact smul_eq_zero_of_smul_one_eq_zero _ _ hk

end Stacks.Koszul.PowerLift

end

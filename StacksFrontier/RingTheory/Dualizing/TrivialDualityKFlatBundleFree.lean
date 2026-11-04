module

public import StacksFrontier.RingTheory.Dualizing.TrivialDualityKFlat

/-!
# Stacks 0BZE on K-flat complexes, read off the change-of-rings comparison

`StacksFrontier/RingTheory/Dualizing/TrivialDualityKFlat.lean` reduces Stacks 0BZE to invertibility
of `Stacks0BZE.comparison`, a morphism assembled from the field `directTensorUnderlying` of the
derived change-of-rings bundle of Stacks 06Y6. That field is constrained by **no axiom** of
`CochainComplex.DerivedTensor.DerivedTensorChangeOfRings`: `Stacks0BZE.twistUnderlying` below
replaces it by its composite with an arbitrary automorphism of its target and leaves a bundle
satisfying every field and every axiom, and
`Stacks0BZE.comparisonOfBundle_twistUnderlying` computes the effect on the comparison, which is
the insertion of that automorphism. Since the bundle of Stacks 06Y6 is obtained by choice from a
nonemptiness statement, the comparison is determined only up to such a twist.

This file supplies the comparison that avoids the field: on a K-flat complex `K` the two
isomorphisms `alphaF` and `directTensorComparison` identify `K ⊗ᴸ_R RHom_R(A, R)` with the
ordinary complex `(A ⊗_R K) ⊗_A RHom_R(A, R)`, naturally in chain maps between K-flat complexes.
Stacks 0BZE therefore follows from a natural family of isomorphisms
`RHom_R(A, K) ≅ Q((A ⊗_R K) ⊗_A RHom_R(A, R))` on the K-flat complexes, a statement in which no
derived change-of-rings bundle occurs at all.

## Main definitions

* `Stacks0BZE.twistUnderlying`: a derived change-of-rings bundle with `directTensorUnderlying`
  twisted by an arbitrary automorphism of its target.
* `Stacks0BZE.kFlatTensorIso`: the identification, at a K-flat complex, of the derived tensor
  product with the ordinary tensor product of the extension of scalars.

## Main results

* `Stacks0BZE.kFlatTensorIso_naturality`: that identification is natural in chain maps between
  K-flat complexes.
* `Stacks0BZE.comparisonOfBundle_twistUnderlying`: twisting `directTensorUnderlying` inserts the
  twist into the comparison of Stacks 0BZE.
* `Stacks0BZE.card_of_tensorIsos`: **Stacks 0BZE from a natural family of isomorphisms between
  derived coextension of scalars and the ordinary tensor product of the extension of scalars, on
  the K-flat complexes.**

## Implementation notes

`Stacks0BZE.comparisonOfBundle` restates `Stacks0BZE.comparison` for an arbitrary bundle on the
same complex, which is what makes the twist visible; at the bundle of Stacks 06Y6 the two agree
by `Stacks0BZE.comparisonOfBundle_bundle`.

## References

* [The Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [The Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks0BZE

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

section Twist

variable {N : CochainComplex (ModuleCat.{max v u} A) ℤ}

/-- A derived change-of-rings bundle whose `directTensorUnderlying` is composed with an arbitrary
automorphism of its target, every other field being unchanged. The field occurs in no other
field's type and in no axiom, so this is again a bundle: the interface of Stacks 06Y6 determines
the underlying comparison only up to an automorphism of the tensor-total functor over `R`. -/
def twistUnderlying (T : DerivedTensorChangeOfRings f N)
    (θ : tensorRightLarge.{u, max v u} ((restrictScalarsLarge.{v, u, u} f).obj N) ≅
      tensorRightLarge.{u, max v u} ((restrictScalarsLarge.{v, u, u} f).obj N)) :
    DerivedTensorChangeOfRings f N where
  directTensor := T.directTensor
  directTensorUnderlying := T.directTensorUnderlying ≪≫ θ
  directTensorComparison := T.directTensorComparison
  F := T.F
  B := T.B
  G := T.G
  commShift := T.commShift
  isTriangulated := T.isTriangulated
  alphaF := T.alphaF
  alphaB := T.alphaB
  alphaG := T.alphaG
  isLeftDerivedF := T.isLeftDerivedF
  isLeftDerivedB := T.isLeftDerivedB
  isLeftDerivedG := T.isLeftDerivedG
  isIso_alphaF := T.isIso_alphaF
  changeOfRings := T.changeOfRings
  changeOfRings_coherence := T.changeOfRings_coherence

end Twist

section BundleFree

variable {N : CochainComplex (ModuleCat.{max v u} A) ℤ}

/-- **The identification that uses no `directTensorUnderlying`.** At a K-flat complex `K` the
derived tensor product `K ⊗ᴸ_R N` is the class of the ordinary complex `(A ⊗_R K) ⊗_A N`: the
counit `alphaF` is invertible at K-flat complexes and `directTensorComparison` is invertible
everywhere. -/
def kFlatTensorIso (T : DerivedTensorChangeOfRings f N)
    (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    T.F.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        ((extendScalarsLarge.{v, u, u} f ⋙ tensorRightLarge.{u, max v u} N).obj K) :=
  letI := T.isIso_alphaF K hK
  asIso (T.alphaF.app K) ≪≫ DerivedCategory.Q.mapIso (T.directTensorComparison.app K)

/-- The forward map of `kFlatTensorIso` is `alphaF` at `K` followed by the image in the derived
category of `directTensorComparison` at `K`. -/
lemma kFlatTensorIso_hom (T : DerivedTensorChangeOfRings f N)
    (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    (kFlatTensorIso f T K hK).hom =
      T.alphaF.app K ≫ DerivedCategory.Q.map (T.directTensorComparison.hom.app K) :=
  rfl

/-- `Stacks0BZE.kFlatTensorIso` is natural in chain maps between K-flat complexes. -/
theorem kFlatTensorIso_naturality (T : DerivedTensorChangeOfRings f N)
    {K L : CochainComplex (ModuleCat.{max v u} R) ℤ}
    (hK : CochainComplex.KFlat.{u, max v u} K) (hL : CochainComplex.KFlat.{u, max v u} L)
    (g : K ⟶ L) :
    T.F.map (DerivedCategory.Q.map g) ≫ (kFlatTensorIso f T L hL).hom =
      (kFlatTensorIso f T K hK).hom ≫
        DerivedCategory.Q.map
          ((extendScalarsLarge.{v, u, u} f ⋙ tensorRightLarge.{u, max v u} N).map g) := by
  have h1 : T.F.map (DerivedCategory.Q.map g) ≫ T.alphaF.app L =
      T.alphaF.app K ≫ DerivedCategory.Q.map (T.directTensor.map g) := T.alphaF.naturality g
  have h2 : T.directTensor.map g ≫ T.directTensorComparison.hom.app L =
      T.directTensorComparison.hom.app K ≫
        (extendScalarsLarge.{v, u, u} f ⋙ tensorRightLarge.{u, max v u} N).map g :=
    T.directTensorComparison.hom.naturality g
  rw [kFlatTensorIso_hom, kFlatTensorIso_hom, ← Category.assoc, h1, Category.assoc,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp, h2]

end BundleFree

section TwistedComparison

/-- `Stacks0BZE.underlyingNatTrans` for an arbitrary bundle on the dual complex. -/
def underlyingNatTransOfBundle
    (T : DerivedTensorChangeOfRings f (dualComplex.{u, v} f)) :
    DerivedCategory.Q ⋙ (T.F ⋙ resDerived f) ⟶
      tensorRightLarge.{u, max v u} (dualRestricted.{u, v} f) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight T.alphaF (resDerived f) ≫
    Functor.whiskerLeft T.directTensor
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.hom ≫
    Functor.whiskerRight T.directTensorUnderlying.hom DerivedCategory.Q

/-- `Stacks0BZE.comparison` for an arbitrary bundle on the dual complex. -/
def comparisonOfBundle (T : DerivedTensorChangeOfRings f (dualComplex.{u, v} f))
    (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    T.F.obj (DerivedCategory.Q.obj K) ⟶
      (Dualizing.derivedHom.{u, v} f).obj (DerivedCategory.Q.obj K) :=
  (Dualizing.derivedHomAdjunction.{u, u, v} f).homEquiv _ _
    ((underlyingNatTransOfBundle.{u, v} f T).app K ≫ tensorCounit.{u, v} f K hK)

/-- At the bundle of Stacks 06Y6, `Stacks0BZE.comparisonOfBundle` is `Stacks0BZE.comparison`. -/
lemma comparisonOfBundle_bundle (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    comparisonOfBundle.{u, v} f (bundle.{u, v} f) K hK = comparison.{u, v} f K hK :=
  rfl

/-- **Twisting `directTensorUnderlying` inserts the twist into the comparison of Stacks 0BZE.**
Together with `Stacks0BZE.twistUnderlying` this says that the comparison is determined by the
interface of Stacks 06Y6 only up to an automorphism of the tensor-total functor over `R`. -/
theorem comparisonOfBundle_twistUnderlying
    (T : DerivedTensorChangeOfRings f (dualComplex.{u, v} f))
    (θ : tensorRightLarge.{u, max v u} (dualRestricted.{u, v} f) ≅
      tensorRightLarge.{u, max v u} (dualRestricted.{u, v} f))
    (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    comparisonOfBundle.{u, v} f (twistUnderlying.{u, v} f T θ) K hK =
      (Dualizing.derivedHomAdjunction.{u, u, v} f).homEquiv _ _
        (((underlyingNatTransOfBundle.{u, v} f T).app K ≫
          DerivedCategory.Q.map (θ.hom.app K)) ≫ tensorCounit.{u, v} f K hK) := by
  have happ : (underlyingNatTransOfBundle.{u, v} f (twistUnderlying.{u, v} f T θ)).app K =
      (underlyingNatTransOfBundle.{u, v} f T).app K ≫
        DerivedCategory.Q.map (θ.hom.app K) := by
    change (resDerived f).map (T.alphaF.app K) ≫
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.hom.app
        (T.directTensor.obj K) ≫
      DerivedCategory.Q.map (T.directTensorUnderlying.hom.app K ≫ θ.hom.app K) =
      ((resDerived f).map (T.alphaF.app K) ≫
        (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.hom.app
          (T.directTensor.obj K) ≫
        DerivedCategory.Q.map (T.directTensorUnderlying.hom.app K)) ≫
      DerivedCategory.Q.map (θ.hom.app K)
    simp only [Category.assoc]
    congr 2
    exact DerivedCategory.Q.map_comp _ _
  rw [comparisonOfBundle, happ]
  rfl

end TwistedComparison

section Card

/-- **Stacks 0BZE from a bundle-free family of isomorphisms.** If derived coextension of scalars
`RHom_R(A, -)` is isomorphic, at every K-flat complex `K` and naturally in chain maps between
such, to the class of the ordinary complex `(A ⊗_R K) ⊗_A RHom_R(A, R)`, then it is isomorphic as
a functor to the derived tensor product with `RHom_R(A, R)`.

No derived change-of-rings bundle occurs in the hypothesis: the bundle enters only through
`Stacks0BZE.kFlatTensorIso`, which uses the two invertible comparisons of Stacks 06Y6 and not the
unconstrained `directTensorUnderlying`. -/
theorem card_of_tensorIsos
    (hperfect : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule (R := R) A)
    (e : ∀ K : CochainComplex (ModuleCat.{max v u} R) ℤ,
      CochainComplex.KFlat.{u, max v u} K →
        ((Dualizing.derivedHom.{u, v} f).obj (DerivedCategory.Q.obj K) ≅
          DerivedCategory.Q.obj
            ((extendScalarsLarge.{v, u, u} f ⋙
              tensorRightLarge.{u, max v u} (dualComplex.{u, v} f)).obj K)))
    (he : ∀ K L (hK : CochainComplex.KFlat.{u, max v u} K)
      (hL : CochainComplex.KFlat.{u, max v u} L) (g : K ⟶ L),
      (Dualizing.derivedHom.{u, v} f).map (DerivedCategory.Q.map g) ≫ (e L hL).hom =
        (e K hK).hom ≫
          DerivedCategory.Q.map
            ((extendScalarsLarge.{v, u, u} f ⋙
              tensorRightLarge.{u, max v u} (dualComplex.{u, v} f)).map g)) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
    letI : MonoidalCategory (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, max v u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))
    Nonempty (Dualizing.derivedHom.{u, v} f ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f
        ((DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage
          ((Dualizing.derivedHom.{u, v} f).obj R₀)).as).F) := by
  refine card_of_kFlatComparison.{u, v} f hperfect
    ⟨fun K hK => e K hK ≪≫ (kFlatTensorIso.{u, v} f (bundle.{u, v} f) K hK).symm, ?_⟩
  intro K L hK hL g
  have hnat := kFlatTensorIso_naturality.{u, v} f (bundle.{u, v} f) hK hL g
  have hinv : DerivedCategory.Q.map
        ((extendScalarsLarge.{v, u, u} f ⋙
          tensorRightLarge.{u, max v u} (dualComplex.{u, v} f)).map g) ≫
          (kFlatTensorIso.{u, v} f (bundle.{u, v} f) L hL).inv =
      (kFlatTensorIso.{u, v} f (bundle.{u, v} f) K hK).inv ≫
        (bundle.{u, v} f).F.map (DerivedCategory.Q.map g) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hnat.symm
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, he K L hK hL g, Category.assoc, hinv, Category.assoc]

end Card

end Stacks0BZE

end

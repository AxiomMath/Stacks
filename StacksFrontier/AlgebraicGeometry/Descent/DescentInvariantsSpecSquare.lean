module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumCocycleDiagram
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumStepFourFive

/-!
# The spectrum of a pushout of algebras as a fibre product of schemes

Let `f : X ⟶ S` be a morphism of affine schemes, write `R = Γ(S, ⊤)` and `A = Γ(X, ⊤)`, and let
`C` be an `A`-algebra which is the base change to `A` of an `R`-algebra `C₀`. Then `Spec C` is the
fibre product `Spec C₀ ×_S X`: this is `CategoryTheory.IsPushout` of rings read through `Spec`,
transported along the canonical isomorphisms `X ≅ Spec A` and `S ≅ Spec R`.

This file records that square and applies it to the invariants of a descent datum. For a descent
datum `D` relative to a surjective flat morphism of affine schemes and a subset `E` of its scheme
`V` which is an intersection of a nonempty family of quasi-compact opens, step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) presents `C = Γ(E, 𝒪_V|_E)` as the
base change of the subalgebra `C₀` of invariants of the transition isomorphism; the square above
then exhibits `Spec Γ(E, 𝒪_V|_E)` as `Spec C₀ ×_S X`.

## Main results

* `AlgebraicGeometry.isPullback_specMap_algebraMap_of_isPushout`: **`Spec` of a pushout of
  algebras is a fibre product of schemes.** Over affine `S` and `X`, if `C` is the base change to
  `Γ(X, ⊤)` of a `Γ(S, ⊤)`-algebra `C₀`, then `Spec C` is `Spec C₀ ×_S X`.
* `AlgebraicGeometry.faithfullyFlat_of_appTop_eq`: the global functions of a flat surjection of
  affine schemes form a faithfully flat algebra.
* `AlgebraicGeometry.DescentDatum.isPushout_descentInvariants`: **step 4 of the proof of Stacks
  0APK with its coassociativity obligation discharged.** `Γ(E, 𝒪_V|_E)` is the base change to
  `Γ(X, ⊤)` of the subalgebra of invariants of
  `AlgebraicGeometry.DescentDatum.descentAlgebraTransition`, with no hypothesis beyond the
  geometry.
* `AlgebraicGeometry.DescentDatum.isPullback_specMap_descentInvariants`: the two combined —
  `Spec Γ(E, 𝒪_V|_E)` is the fibre product of `Spec` of the invariants with `X` over `S`.

## Implementation notes

*Why the coassociativity obligation is free here.*
`AlgebraicGeometry.DescentDatum.isPushout_descentInvariants_of_cocycle` asks for the hypothesis
`hkey`, an identity in a triple tensor product. The cocycle diagram which implies it is produced
from the descent datum by
`AlgebraicGeometry.DescentDatum.exists_cocycleDiagram_descentAlgebraTransition`, and
`AlgebraicGeometry.DescentDatum.unitCoassoc_descentAlgebraTransition` turns that diagram into
`hkey`. So the composite asks only for the geometry, in particular not for the invariance of `E`
under the gluing isomorphism — only for the two inclusions of preimages `h₁` and `h₂`.

*Where faithful flatness comes from.* `Γ(S, ⊤) ⟶ Γ(X, ⊤)` is faithfully flat because `f` is a
flat surjection of affine schemes, which is
`AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` read through the
identification `hRA` of `algebraMap` with `f.appTop`. It is therefore not a hypothesis.

*No tag is placed.* The first result is a general statement about pushouts of algebras, carried by
no tag of the Stacks project; the other two are steps in the proof of Tag 0APK, which is stated
for arbitrary fpqc covering families.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **`Spec` of a pushout of algebras is a fibre product of schemes.** Let `f : X ⟶ S` be a
morphism of affine schemes whose map on global functions is `algebraMap Γ(S, ⊤) Γ(X, ⊤)`, and let
`C` be a ring which is the base change to `Γ(X, ⊤)` of a `Γ(S, ⊤)`-algebra `C₀`. Then `Spec C`,
with the morphisms induced by `C₀ ⟶ C` and `Γ(X, ⊤) ⟶ C`, is the fibre product
`Spec C₀ ×_S X`. -/
theorem isPullback_specMap_algebraMap_of_isPushout {S X : Scheme.{u}} [IsAffine S] [IsAffine X]
    (f : X ⟶ S) (C₀ C : Type u) [CommRing C₀] [CommRing C]
    [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) C₀] [Algebra ↥Γ(S, ⊤) C]
    [Algebra ↥Γ(X, ⊤) C] [Algebra C₀ C]
    [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) C] [IsScalarTower ↥Γ(S, ⊤) C₀ C]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hpo : Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤) C₀ C) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) C)) ≫ X.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))
      f (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) C₀)) ≫ S.isoSpec.inv) := by
  have h0 : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) C)))
      (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))
      (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) C₀))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_iff_isPushout.mpr hpo)
  refine h0.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) S.isoSpec.symm
    ((Category.id_comp _).symm) (by simp) ?_ ((Category.id_comp _).symm)
  rw [Iso.symm_hom, Iso.symm_hom, hRA]
  exact Scheme.isoSpec_inv_naturality f

/-- **The global functions of a flat surjection of affine schemes form a faithfully flat
algebra**, read at an algebra structure whose `algebraMap` is the map on global functions. -/
theorem faithfullyFlat_of_appTop_eq {S X : Scheme.{u}} [IsAffine S] [IsAffine X] (f : X ⟶ S)
    [Flat f] [Surjective f] [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop) :
    Module.FaithfullyFlat ↥Γ(S, ⊤) ↥Γ(X, ⊤) := by
  have hhom : (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop.hom :=
    (CommRingCat.hom_ofHom _).symm.trans (congrArg CommRingCat.Hom.hom hRA)
  rw [← RingHom.faithfullyFlat_algebraMap_iff, hhom]
  exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
    ⟨inferInstance, inferInstance⟩

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (E : Set D.over.left)
    [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)
    (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E)
    [IsAffine S] [IsAffine X] [Flat f] [Surjective f] [QuasiSeparatedSpace D.over.left]
    {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
    (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))

include hRA hRC hAC hU hE in
/-- **Step 4 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) over an
affine base, with its coassociativity obligation discharged.** For `f : X ⟶ S` a surjective flat
morphism of affine schemes, `D` a descent datum relative to `f` whose scheme `V` is
quasi-separated, and `E ⊆ V` an intersection of a nonempty family of quasi-compact opens whose two
preimages are carried into one another by the gluing isomorphism, the ring `Γ(E, 𝒪_V|_E)` is the
base change to `Γ(X, ⊤)` of the `Γ(S, ⊤)`-subalgebra of invariants of the transition isomorphism
the datum induces on functions. -/
theorem isPushout_descentInvariants :
    Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤)
      (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)
        (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
      ↥(D.over.left.sectionsRingOnSubset E) := by
  have _ : Module.FaithfullyFlat ↥Γ(S, ⊤) ↥Γ(X, ⊤) := faithfullyFlat_of_appTop_eq f hRA
  obtain ⟨Q₃, i₃, j₃, Λ, Λ', hQ₃, hΛ₁, hΛ₂, hΛ₁', hΛ₂', hcoc⟩ :=
    D.exists_cocycleDiagram_descentAlgebraTransition E hRA U hU hE h₁ h₂
  exact D.isPushout_descentInvariants_of_cocycle E hRA hRC hAC U hU hE h₁ h₂
    (D.unitCoassoc_descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂ hQ₃ hΛ₁ hΛ₂ hΛ₁' hΛ₂'
      hcoc)

include hRA hRC hAC hU hE in
/-- **`Spec Γ(E, 𝒪_V|_E)` is the fibre product of `Spec` of the invariants with `X` over `S`.**
In the situation of `AlgebraicGeometry.DescentDatum.isPushout_descentInvariants`, the morphism
induced by the inclusion of the subalgebra of invariants and the morphism to `X` induced by
restriction of functions exhibit `Spec Γ(E, 𝒪_V|_E)` as `Spec C₀ ×_S X`. -/
theorem isPullback_specMap_descentInvariants :
    IsPullback
      (Spec.map (CommRingCat.ofHom
          (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E))) ≫ X.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (algebraMap
        (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)
          (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
        ↥(D.over.left.sectionsRingOnSubset E))))
      f
      (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤)
        (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)
          (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))) ≫ S.isoSpec.inv) :=
  isPullback_specMap_algebraMap_of_isPushout f _ _ hRA
    (D.isPushout_descentInvariants E hRA hRC hAC U hU hE h₁ h₂)

end DescentDatum

end AlgebraicGeometry

end

end

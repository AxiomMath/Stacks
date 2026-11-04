module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateSectionExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.QcohPullbackOpenCover
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde

/-!
# Universal acyclicity is tested over the spectra

`Stacks.Adequate.universallyAcyclic_of_affine` tests universal acyclicity over the schemes `T`
with `IsAffine T`, which are the members of an affine open cover and not literally spectra. The
comparison of [Stacks, Tag 06ZR] with a condition on the algebras of the base runs over the
spectra, so the two readings have to be matched: an affine scheme is isomorphic to the spectrum
of its ring, `AlgebraicGeometry.Scheme.isoSpec`, and acyclicity of a pullback has to be carried
along that isomorphism.

Pullback of `𝒪`-modules along an isomorphism of schemes is an **equivalence** of categories,
`AlgebraicGeometry.Scheme.Modules.isEquivalence_pullback_of_isIso`, so it is exact and reflects
isomorphisms and therefore detects acyclicity in both directions.

## Main results

* `Stacks.Adequate.plus_subcategoryAcyclic_qcohPullback_iff_of_iso` — **acyclicity of the
  pullback of a complex of quasi-coherent modules is unchanged by precomposing the morphism with
  an isomorphism of schemes.**
* `Stacks.Adequate.universallyAcyclic_of_spec` — **a complex whose pullback along every morphism
  from a spectrum is acyclic is universally acyclic**: the strengthening of
  `Stacks.Adequate.universallyAcyclic_of_affine` that the comparison of [Stacks, Tag 06ZR]
  consumes.

## Implementation notes

Both replacements — of the affine scheme `T` by `Spec Γ(T, ⊤)`, and of the morphism `T ⟶ Spec A`
by the `Spec` of a ring map — are made at the level of the *morphism*, by rewriting with
`f = T.isoSpec.hom ≫ (T.isoSpec.inv ≫ f)`, so no object property is ever transported along an
equivalence.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Adequate

variable {S : Scheme.{u}}

/-- **Acyclicity of the pullback of a complex of quasi-coherent `𝒪_S`-modules is unchanged by
precomposing with an isomorphism of schemes.** The pullback along `e.hom ≫ g` is the pullback
along `g` followed by the pullback along `e.hom`, `Stacks.Adequate.qcohPullbackComp`, and
pullback along an isomorphism detects acyclicity, being an equivalence. -/
public theorem plus_subcategoryAcyclic_qcohPullback_iff_of_iso {T T' : Scheme.{u}} (e : T ≅ T')
    (g : T' ⟶ S)
    (K : HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    HomotopyCategory.Plus.subcategoryAcyclic T.Modules
        ((qcohPullback (e.hom ≫ g)).mapHomotopyCategoryPlus.obj K) ↔
      HomotopyCategory.Plus.subcategoryAcyclic T'.Modules
        ((qcohPullback g).mapHomotopyCategoryPlus.obj K) := by
  have key := (Functor.mapHomotopyCategoryPlusCompIso (qcohPullbackComp e.hom g).symm).app K
  rw [(HomotopyCategory.Plus.subcategoryAcyclic T.Modules).prop_iff_of_iso key.symm,
    Functor.comp_obj, plus_acyclic_map_iff (Scheme.Modules.pullback e.hom)]

/-- **A bounded below complex of quasi-coherent `𝒪_S`-modules whose pullback along every
morphism from the spectrum of a ring is acyclic is universally acyclic.** This strengthens
`Stacks.Adequate.universallyAcyclic_of_affine`: an affine scheme `T` is isomorphic to
`Spec Γ(T, ⊤)` by `AlgebraicGeometry.Scheme.isoSpec`, and acyclicity of the pullback is carried
along that isomorphism by
`Stacks.Adequate.plus_subcategoryAcyclic_qcohPullback_iff_of_iso`. -/
public theorem universallyAcyclic_of_spec
    (K : HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (h : ∀ (R : CommRingCat.{u}) (g : Spec R ⟶ S),
      HomotopyCategory.Plus.subcategoryAcyclic (Spec R).Modules
        ((qcohPullback g).mapHomotopyCategoryPlus.obj K)) :
    universallyAcyclic S K := by
  refine universallyAcyclic_of_affine K fun T f hT => ?_
  let := hT
  have hf : T.isoSpec.hom ≫ (T.isoSpec.inv ≫ f) = f := by
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← hf]
  exact (plus_subcategoryAcyclic_qcohPullback_iff_of_iso T.isoSpec (T.isoSpec.inv ≫ f) K).2
    (h _ _)

end Stacks.Adequate

end

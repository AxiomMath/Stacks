module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackChartOver
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition

/-!
# Charts over a product with the base, for the descent of infinitesimal lifts

For Stacks 0DNU the stack `𝒳` lives over `S`, not over the thickened affine `T'`, so the chart
algebra is the ring of an affine `W''` étale over `W ×_Z T'`, where `W` is étale over a chart
`U₀` of `𝒳` and `Z` is the object of the site the stack maps to.

* `AlgebraicGeometry.Stack.locallyOfFinitePresentation_siteMap_of_isLocallyOfFinitePresentation`:
  a 1-morphism of represented algebraic stacks which is locally of finite presentation comes
  from a morphism of schemes locally of finite presentation.
* `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_sectionsHom_of_etale_pullback`: the point
  `Spec Γ(W'') ≅ W'' ⟶ W ⟶ U₀` lifts compatible points of `U₀` across square-zero thickenings
  (two applications of Stacks 04AL and the universal property of the fibre product).
* `AlgebraicGeometry.Stack.GroupoidLift.faithfullyFlat_of_specOverToBase`,
  `AlgebraicGeometry.Stack.GroupoidLift.finitePresentation_of_specOverToBase`: an algebra over
  `Γ(T')` is faithfully flat, resp. finitely presented, when its spectrum is flat and surjective,
  resp. locally of finite presentation, over `T'`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_sectionsHom_of_etale_pullback`.
-/

@[expose] public section

open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack

universe w u

/-- **A 1-morphism of represented algebraic stacks which is locally of finite presentation comes
from a morphism of schemes locally of finite presentation.** -/
theorem locallyOfFinitePresentation_siteMap_of_isLocallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V)
    (hc : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (siteMap B S hS c)) := by
  have hsome := (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (schemeStack.{u, w} B S hS U).property (schemeStack.{u, w} B S hS V).property _).1 hc
  have h := (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (schemeStack.{u, w} B S hS U).property (schemeStack.{u, w} B S hS V).property
      (yoneda.obj U) (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (PresheafOfCategories.sliceElementsEquivalenceOver V) c.hom).1 hsome
  rw [representingMap_eq_yoneda_map_siteMap] at h
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget _).1 h

namespace GroupoidLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- A property stable under isomorphisms passes from the spectrum of an algebra over `T'`, viewed
as a scheme over `T'`, to the spectrum of the structure map. -/
private theorem property_spec_algebraMap_of_specOverToBase (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (C : SmallAlg (ringOf B S hS T') B.cutoff)
    (h : P ((BigFppfOver.toScheme B S hS).map (specOverToBase C))) :
    P (Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C.obj))) := by
  have e : (BigFppfOver.toScheme B S hS).map (specOverToBase C) ≫
      ((BigFppfOver.toScheme B S hS).obj T').isoSpec.hom =
        Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C.obj)) := by
    show specToBase C ≫ _ = _
    rw [specToBase, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← e]
  exact (MorphismProperty.cancel_right_of_respectsIso (P := P) _ _).mpr h

/-- An algebra whose spectrum is flat and surjective over `T'` is faithfully flat. -/
theorem faithfullyFlat_of_specOverToBase (C : SmallAlg (ringOf B S hS T') B.cutoff)
    (hfl : Flat ((BigFppfOver.toScheme B S hS).map (specOverToBase C)))
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map (specOverToBase C))) :
    Module.FaithfullyFlat (ringOf B S hS T') C.obj := by
  have _ : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact RingHom.faithfullyFlat_algebraMap_iff.mp
    ((flat_and_surjective_SpecMap_iff _).mp
      ⟨property_spec_algebraMap_of_specOverToBase (@Flat.{u}) C hfl,
        property_spec_algebraMap_of_specOverToBase (@Surjective.{u}) C hs⟩)

/-- An algebra whose spectrum is locally of finite presentation over `T'` is finitely
presented. -/
theorem finitePresentation_of_specOverToBase (C : SmallAlg (ringOf B S hS T') B.cutoff)
    (h : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (specOverToBase C))) :
    Algebra.FinitePresentation (ringOf B S hS T') C.obj := by
  have _ : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact RingHom.finitePresentation_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
      (property_spec_algebraMap_of_specOverToBase (@LocallyOfFinitePresentation.{u}) C h))

variable {U₀ W W'' Z : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W'')]

/-- **An affine étale chart over `W ×_Z T'` lifts compatible points across square-zero
thickenings.** Let `s : W ⟶ U₀` be étale, `hZ : U₀ ⟶ Z`, `τ : T' ⟶ Z`, and `s'' : W'' ⟶ W ×_Z T'`
étale with `W''` affine; give `Γ(W'')` the `Γ(T')`-algebra structure of the second projection. A
point `m'` of `U₀` over `Spec C'` compatible with `τ` and restricting over `Spec C` to the point
of `u : Γ(W'') → C` is the point of a lift `u' : Γ(W'') → C'` of `u`. -/
theorem exists_lift_sectionsHom_of_etale_pullback (s : W ⟶ U₀)
    (hs : Etale ((BigFppfOver.toScheme B S hS).map s)) (hZ : U₀ ⟶ Z) (τ : T' ⟶ Z)
    (s'' : W'' ⟶ pullback (s ≫ hZ) τ) (hs'' : Etale ((BigFppfOver.toScheme B S hS).map s''))
    {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
    (m' : specOver C' ⟶ U₀)
    (u : (sectionsAlg W'' (s'' ≫ pullback.snd _ _)).obj →ₐ[ringOf B S hS T'] C.obj)
    (hm'Z : m' ≫ hZ = specOverToBase C' ≫ τ)
    (hm' : specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫
      sectionsHom W'' (s'' ≫ pullback.snd _ _) ≫ s'' ≫ pullback.fst _ _ ≫ s) :
    ∃ u' : (sectionsAlg W'' (s'' ≫ pullback.snd _ _)).obj →ₐ[ringOf B S hS T'] C'.obj,
      e.q.hom.hom.comp u' = u ∧ specOverMap (SmallAlg.homMk u') ≫
        sectionsHom W'' (s'' ≫ pullback.snd _ _) ≫ s'' ≫ pullback.fst _ _ ≫ s = m' := by
  have hsq := isSquareZeroClosedImmersion_specOverMap e.q e.surj e.sq
  -- lift through `s`
  have hfe : Space.FormallyEtale (yoneda.map s) := Space.formallyEtale_of_etale B S hS _
    ((Space.presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mpr hs)
  obtain ⟨g₁, ⟨hg₁, hg₁'⟩, -⟩ := hfe (specOver C) (specOver C') inferInstance inferInstance
    (specOverMap e.q) hsq
    ((specOverMap (SmallAlg.homMk u) ≫ sectionsHom W'' (s'' ≫ pullback.snd _ _)) ≫ s'' ≫
      pullback.fst _ _) m'
    (by
      show ((specOverMap (SmallAlg.homMk u) ≫ sectionsHom W'' (s'' ≫ pullback.snd _ _)) ≫ s'' ≫
        pullback.fst _ _) ≫ s = specOverMap e.q ≫ m'
      rw [hm']; simp only [Category.assoc])
  change specOverMap e.q ≫ g₁ = (specOverMap (SmallAlg.homMk u) ≫
    sectionsHom W'' (s'' ≫ pullback.snd _ _)) ≫ s'' ≫ pullback.fst _ _ at hg₁
  change g₁ ≫ s = m' at hg₁'
  -- lift through `s''`
  have hfe'' : Space.FormallyEtale (yoneda.map s'') := Space.formallyEtale_of_etale B S hS _
    ((Space.presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mpr hs'')
  have hy : g₁ ≫ s ≫ hZ = specOverToBase C' ≫ τ := by
    rw [← Category.assoc, hg₁', hm'Z]
  obtain ⟨g₂, ⟨hg₂, hg₂'⟩, -⟩ := hfe'' (specOver C) (specOver C') inferInstance inferInstance
    (specOverMap e.q) hsq
    (specOverMap (SmallAlg.homMk u) ≫ sectionsHom W'' (s'' ≫ pullback.snd _ _))
    (pullback.lift g₁ (specOverToBase C') hy)
    (by
      show (specOverMap (SmallAlg.homMk u) ≫ sectionsHom W'' (s'' ≫ pullback.snd _ _)) ≫ s'' =
        specOverMap e.q ≫ pullback.lift _ _ _
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        rw [hg₁]; simp only [Category.assoc]
      · simp only [Category.assoc, pullback.lift_snd]
        rw [sectionsHom_comp, specOverMap_comp_toBase, specOverMap_comp_toBase])
  change specOverMap e.q ≫ g₂ = specOverMap (SmallAlg.homMk u) ≫
    sectionsHom W'' (s'' ≫ pullback.snd _ _) at hg₂
  change g₂ ≫ s'' = pullback.lift _ _ _ at hg₂'
  -- read the lift as an algebra map
  have hbase : (g₂ ≫ inv (sectionsHom W'' (s'' ≫ pullback.snd _ _))) ≫
      specOverToBase (sectionsAlg W'' (s'' ≫ pullback.snd _ _)) = specOverToBase C' := by
    rw [Category.assoc, ← sectionsHom_comp W'' (s'' ≫ pullback.snd _ _), IsIso.inv_hom_id_assoc,
      ← Category.assoc, hg₂', pullback.lift_snd]
  obtain ⟨k, hk⟩ := exists_specOverMap _ hbase
  have hk' : specOverMap k ≫ sectionsHom W'' (s'' ≫ pullback.snd _ _) = g₂ := by
    rw [hk, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨k.hom.hom, ?_, ?_⟩
  · have hkq : k ≫ e.q = SmallAlg.homMk u := by
      apply specOverMap_injective
      rw [specOverMap_comp, ← cancel_mono (sectionsHom W'' (s'' ≫ pullback.snd _ _)),
        Category.assoc, hk', hg₂]
    exact congrArg (fun t ↦ t.hom.hom) hkq
  · show specOverMap k ≫ sectionsHom W'' (s'' ≫ pullback.snd _ _) ≫ s'' ≫ pullback.fst _ _ ≫ s
      = m'
    rw [← Category.assoc, hk', ← Category.assoc, hg₂', ← Category.assoc, pullback.lift_fst, hg₁']

end GroupoidLift

end AlgebraicGeometry.Stack

end

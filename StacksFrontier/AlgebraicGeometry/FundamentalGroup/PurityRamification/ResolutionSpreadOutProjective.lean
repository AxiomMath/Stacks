module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOut
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety

/-!
# Spreading out a scheme over the local ring at a point: projectivity

Continuing `PurityRamification/ResolutionSpreadOut.lean`. In the proof of [Stacks, Tag 0EA3]:
"Since `W ⟶ Spec(𝒪_{X, x})` is projective (as a sequence of normalized blowing ups), we may
assume after shrinking `X` that `b` is projective (details omitted)." The details: a closed
immersion `W ⟶ ℙⁿ_{𝒪_{X, x}} = ℙⁿ_U ×_U Spec(𝒪_{X, x})` over `Spec(𝒪_{X, x})` is, after
shrinking the affine open neighbourhood `U` of `x`, the base change of a morphism `X' ⟶ ℙⁿ_U`
over `U` ([Stacks, Tag 01ZM], part (2)), which is a closed immersion after shrinking further
([Stacks, Tag 01ZP]).

## Main results

* `AlgebraicGeometry.exists_hom_isProjectiveMorphism_model`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An H-projective morphism stays H-projective after precomposing with an isomorphism. -/
theorem IsProjectiveMorphism.iso_comp {X X' S : Scheme.{u}} (e : X' ≅ X) {f : X ⟶ S}
    (hf : IsProjectiveMorphism f) : IsProjectiveMorphism (e.hom ≫ f) := by
  obtain ⟨n, i, hi, hif⟩ := hf
  exact ⟨n, e.hom ≫ i, inferInstance, by rw [Category.assoc, hif]⟩

/-- H-projectivity of a base change depends only on the morphism base changed along. -/
theorem isProjectiveMorphism_pullback_snd_congr {X Y S : Scheme.{u}} (f : X ⟶ S)
    {g g' : Y ⟶ S} (h : g = g') :
    IsProjectiveMorphism (pullback.snd f g) ↔ IsProjectiveMorphism (pullback.snd f g') := by
  subst h
  rfl

/-- An iterated base change which is H-projective is H-projective as a single base change. -/
theorem isProjectiveMorphism_pullback_snd_comp {X Y Z T : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (k : T ⟶ Y) (h : IsProjectiveMorphism (pullback.snd (pullback.snd f g) k)) :
    IsProjectiveMorphism (pullback.snd f (k ≫ g)) := by
  have : pullback.snd f (k ≫ g) =
      (pullbackLeftPullbackSndIso f g k).inv ≫ pullback.snd (pullback.snd f g) k := by
    rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
  rw [this]
  exact h.iso_comp (pullbackLeftPullbackSndIso f g k).symm

/-- **The model is H-projective over a smaller neighbourhood (the projectivity step of the proof
of [Stacks, Tag 0EA3]).** Let `X` be locally Noetherian, `x ∈ X`, and let
`g : W ⟶ Spec(𝒪_{X, x})` be H-projective and the base change of a morphism of finite
presentation `Z ⟶ U` over an affine open neighbourhood `U` of `x`. Then `Z ×_U U' ⟶ U'` is
H-projective for some smaller affine open neighbourhood `U'` of `x`. -/
theorem exists_hom_isProjectiveMorphism_model (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {W : Scheme.{u}} (g : W ⟶ Spec (X.presheaf.stalk x)) (hg : IsProjectiveMorphism g)
    {j : AffineOpenNhds X x} (Z : Over ((affineOpenNhdsDiagram X x).obj j))
    (hfp : FinitePresentation Z.hom)
    (e : Over.mk g ≅ (Over.pullback ((specStalkCone X x).π.app j)).obj Z) :
    ∃ (k : AffineOpenNhds X x) (h : k ⟶ j),
      IsProjectiveMorphism (pullback.snd Z.hom ((affineOpenNhdsDiagram X x).map h)) := by
  let D := affineOpenNhdsDiagram X x
  let c := specStalkCone X x
  obtain ⟨n, i, hi, hig⟩ := hg
  let P : Over (D.obj j) := Over.mk (projectiveSpaceOver n (D.obj j) ↘ D.obj j)
  have := isProper_projectiveSpaceOver n (D.obj j)
  have hPfp : FinitePresentation P.hom :=
    ⟨inferInstanceAs (LocallyOfFinitePresentation (projectiveSpaceOver n (D.obj j) ↘ D.obj j)),
      inferInstanceAs (QuasiCompact (projectiveSpaceOver n (D.obj j) ↘ D.obj j)),
      inferInstanceAs (QuasiSeparated (projectiveSpaceOver n (D.obj j) ↘ D.obj j))⟩
  let π : Spec (X.presheaf.stalk x) ⟶ D.obj j := c.π.app j
  let ε : pullback (projectiveSpaceOver n (D.obj j) ↘ D.obj j) π ≅
      projectiveSpaceOver n (Spec (X.presheaf.stalk x)) :=
    projectiveSpaceOverBaseChangeIso n π
  have hε : ε.inv ≫ pullback.snd (projectiveSpaceOver n (D.obj j) ↘ D.obj j) π =
      projectiveSpaceOver n (Spec (X.presheaf.stalk x)) ↘ Spec (X.presheaf.stalk x) := by
    rw [Iso.inv_comp_eq]
    exact (projectiveSpaceOverBaseChangeIso_hom_over n π).symm
  have hiε : (i ≫ ε.inv) ≫ pullback.snd (projectiveSpaceOver n (D.obj j) ↘ D.obj j) π = g := by
    rw [Category.assoc, hε, hig]
  let φ₀ : Over.mk g ⟶ (Over.pullback π).obj P := Over.homMk (i ≫ ε.inv) hiε
  let φ := e.inv ≫ φ₀
  have hiso : ∀ {S : Scheme.{u}} {A B : Over S} (u : A ≅ B), IsIso u.hom.left :=
    fun u => (Over.forget _).map_isIso u.hom
  have hφ : IsClosedImmersion φ.left := by
    have := hiso e.symm
    exact inferInstanceAs (IsClosedImmersion (e.symm.hom.left ≫ i ≫ ε.inv))
  obtain ⟨k, h, ψ, α, β, -, -, hcomm⟩ :=
    exists_morphism_after_baseChange D c (isLimitSpecStalkCone X x) j Z P hfp hPfp φ
  have hlim : IsClosedImmersion ((Over.pullback (c.π.app k)).map ψ).left := by
    have := hiso α
    have := hiso β
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ β.hom.left,
      ← Over.comp_left, ← hcomm]
    exact inferInstanceAs (IsClosedImmersion (α.hom.left ≫ φ.left))
  let Zk := (Over.pullback (D.map h)).obj Z
  let Pk := (Over.pullback (D.map h)).obj P
  obtain ⟨_, _, _⟩ : FinitePresentation Zk.hom := finitePresentation_overPullback_obj _ Z hfp
  obtain ⟨_, _, _⟩ : FinitePresentation Pk.hom := finitePresentation_overPullback_obj _ P hPfp
  have : CompactSpace Zk.left := QuasiCompact.compactSpace_of_compactSpace Zk.hom
  have : QuasiSeparatedSpace Zk.left := quasiSeparatedSpace_of_quasiSeparated Zk.hom
  have : CompactSpace Pk.left := QuasiCompact.compactSpace_of_compactSpace Pk.hom
  have : QuasiSeparatedSpace Pk.left := quasiSeparatedSpace_of_quasiSeparated Pk.hom
  have : LocallyOfFiniteType ψ.left := by
    have : LocallyOfFiniteType (ψ.left ≫ Pk.hom) := by rw [Over.w ψ]; infer_instance
    exact locallyOfFiniteType_of_comp ψ.left Pk.hom
  obtain ⟨l, h', hcl⟩ :=
    exists_isClosedImmersion_baseChange_of_isLimit D c (isLimitSpecStalkCone X x) k Zk Pk ψ
  refine ⟨l, h' ≫ h, ?_⟩
  have hPl : IsProjectiveMorphism ((Over.pullback (D.map h')).obj Pk).hom :=
    ((isProjectiveMorphism_projectiveSpaceOver n (D.obj j)).baseChange (D.map h)).baseChange
      (D.map h')
  obtain ⟨N, ι, hι, hιf⟩ := hPl
  have hZl : IsProjectiveMorphism ((Over.pullback (D.map h')).obj Zk).hom := by
    refine ⟨N, ((Over.pullback (D.map h')).map ψ).left ≫ ι, inferInstance, ?_⟩
    rw [Category.assoc, hιf]
    exact Over.w ((Over.pullback (D.map h')).map ψ)
  exact (isProjectiveMorphism_pullback_snd_congr Z.hom (D.map_comp h' h)).mpr
    (isProjectiveMorphism_pullback_snd_comp Z.hom (D.map h) (D.map h') hZl)

end AlgebraicGeometry

end

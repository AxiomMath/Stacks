module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartFibre

/-!
# Proper pushforward on a represented space and on the representing scheme

Let `σ : U → V` be a morphism of schemes of the big fppf site of `S`, and `h_σ : h_U → h_V` the
morphism of the algebraic spaces they represent. At a point `x` of `h_U`, corresponding to a
point `u` of `U`, the residue field extension of `h_σ` of Stacks 0EMW is the residue field
extension `κ(u) / κ(σ(u))` of the morphism of schemes: both are presented by the canonical
morphisms `Spec κ(u) → U` and `Spec κ(σ(u)) → V`, which are monomorphisms, and the residue field
of a decent space may be computed on any monomorphic representative. So the degrees agree.

In Situation 0EDT, for good spaces `h_U → B` and `h_V → B` with δ-compatible scheme situations
over a common base `(C.S, δ)`, Stacks 0EP1 and Stacks 02R4 then give the same pushforward of
cycles along a proper `σ`: under the isomorphisms `Z_k(h_U) ≅ Z_k(U)` and `Z_k(h_V) ≅ Z_k(V)`
of `AlgebraicGeometry.Space.cycleGroupEquivScheme`, the proper pushforward of the space theory is
the proper pushforward of the scheme theory. The closure of the image of an integral closed
subspace corresponds to the closure of the image of its generic point, and the degree
`[R(Z) : R(Z')]` of Stacks 0EP1 is the residue degree of Stacks 02R4 at the generic point.

## Main results

* `AlgebraicGeometry.Space.finrank_residueFieldHom_yoneda_map`: the residue degree of `h_σ` at a
  point is the residue degree of `σ` at the corresponding point.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.schemeGenericPoint_closureImage`: the generic
  point of the closure of the image of an integral closed subspace is the image of its generic
  point.
* `AlgebraicGeometry.Space.functionFieldDegree_yoneda_map`: the degree of Stacks 0EP1 along
  `h_σ` is the residue degree of `σ` at the generic point.
* `AlgebraicGeometry.Space.cycleGroupEquivScheme_properCyclePushforward`: proper pushforward of
  cycles commutes with the comparison `Z_k(h_U) ≅ Z_k(U)`.

## References

* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section ResidueDegree

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical field-valued point of a represented presheaf at a point of the representing
scheme presents it by a monomorphism: the canonical morphism from the spectrum of the residue
field is a monomorphism of schemes. -/
theorem mono_fieldMorphism_canonicalSiteFieldPoint (U : BigFppfOver B S hS)
    (a : (BigFppfOver.toScheme B S hS).obj U) :
    Mono (fieldMorphism B S hS (yoneda.obj U) (canonicalSiteFieldPoint B S hS U a)) := by
  rw [fieldMorphism_yoneda]
  have : Mono ((BigFppfOver.toScheme B S hS).map
      (canonicalSiteFieldPoint B S hS U a).siteHom) := by
    change Mono (B.inclusion.map ((canonicalSiteFieldPoint B S hS U a).siteHom B S hS).left)
    have h₁ : B.inclusion.map ((canonicalSiteFieldPoint B S hS U a).siteHom B S hS).left =
        ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField a :=
      map_siteFieldPointOfSchemeMap_value_left B S hS _ _ _
    have h₀ : Mono (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField a) :=
      inferInstance
    rw [h₁]
    exact h₀
  have := (BigFppfOver.toScheme B S hS).mono_of_mono_map this
  infer_instance

/-- **The residue degree of a morphism of represented spaces.** For a morphism of schemes
`σ : U → V` of the site, the degree of the residue field extension of `h_σ : h_U → h_V` at a
point, Stacks 0EMW, is the residue degree of `σ` at the corresponding point of `U`. -/
theorem finrank_residueFieldHom_yoneda_map {U V : BigFppfOver B S hS} (σ : U ⟶ V)
    (hUdec : IsDecentSpace B S hS (yoneda.obj U)) (hVdec : IsDecentSpace B S hS (yoneda.obj V))
    (x : points B S hS (yoneda.obj U)) :
    (letI := (residueFieldHom B S hS (yoneda.obj U) (yoneda.obj V)
        (isAlgebraicSpace_yoneda B S hS V) hUdec hVdec (yoneda.map σ) x).toAlgebra;
      Module.finrank
        (residueField B S hS (yoneda.obj V) hVdec (pointsMap B S hS _ (yoneda.map σ) x))
        (residueField B S hS (yoneda.obj U) hUdec x)) =
      ((BigFppfOver.toScheme B S hS).map σ).residueDegree (pointsToScheme B S hS U x) := by
  set a := pointsToScheme B S hS U x
  set σ₀ := (BigFppfOver.toScheme B S hS).map σ
  have hq : (canonicalSiteFieldPoint B S hS U a).class B S hS (yoneda.obj U) = x :=
    injective_pointsToScheme B S hS U (pointsToScheme_class_canonicalSiteFieldPoint B S hS U a)
  have hq' : (canonicalSiteFieldPoint B S hS V (σ₀ a)).class B S hS (yoneda.obj V) =
      pointsMap B S hS _ (yoneda.map σ) x := by
    apply injective_pointsToScheme B S hS V
    rw [pointsToScheme_class_canonicalSiteFieldPoint, pointsToScheme_pointsMap]
  obtain ⟨h, h₁, h₂⟩ := exists_siteHom_canonicalSiteFieldPoint B S hS σ a
  have hsq : yoneda.map h ≫ fieldMorphism B S hS (yoneda.obj V)
      (canonicalSiteFieldPoint B S hS V (σ₀ a)) =
      fieldMorphism B S hS (yoneda.obj U) (canonicalSiteFieldPoint B S hS U a) ≫ yoneda.map σ := by
    rw [fieldMorphism_yoneda, fieldMorphism_yoneda, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg yoneda.map h₂
  rw [finrank_residueFieldHom_eq_of_mono B S hS (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_yoneda B S hS V) hUdec hVdec (yoneda.map σ) x _ hq
    (mono_fieldMorphism_canonicalSiteFieldPoint B S hS U a) _ hq'
    (mono_fieldMorphism_canonicalSiteFieldPoint B S hS V (σ₀ a)) (σ₀.residueFieldMap a).hom h
    (by rw [h₁]; rfl) hsq]
  rfl

end ResidueDegree

section ClosureImage

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The generic point of an integral closed subspace of `h_U`, read in `U`, is the point of `U`
below its ambient generic point. -/
theorem IntegralClosedSubspace.schemeGenericPoint_eq_pointsToScheme {U : BigFppfOver B S hS}
    (Z : IntegralClosedSubspace B S hS (yoneda.obj U)) :
    Z.schemeGenericPoint B S hS U = pointsToScheme B S hS U (Z.ambientGenericPoint B S hS) :=
  rfl

/-- The generic point of the closure of the image of an integral closed subspace `Z ⊆ h_U` along
`h_σ` is the image under `σ` of the generic point of `Z`. -/
theorem IntegralClosedSubspace.schemeGenericPoint_closureImage {U V : BigFppfOver B S hS}
    (σ : U ⟶ V) (hVdec : IsDecentSpace B S hS (yoneda.obj V))
    (Z : IntegralClosedSubspace B S hS (yoneda.obj U)) :
    (IntegralClosedSubspace.closureImage B S hS (isAlgebraicSpace_yoneda B S hS V) hVdec
        (yoneda.map σ) Z).schemeGenericPoint B S hS V =
      (BigFppfOver.toScheme B S hS).map σ (Z.schemeGenericPoint B S hS U) := by
  rw [IntegralClosedSubspace.schemeGenericPoint_eq_pointsToScheme,
    IntegralClosedSubspace.ambientGenericPoint_closureImage_eq B S hS
      (isAlgebraicSpace_yoneda B S hS U), pointsToScheme_pointsMap]
  rfl

end ClosureImage

section Pushforward

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **The degree of Stacks 0EP1 on represented spaces.** The degree `[R(Z) : R(Z')]` of the
function field extension induced by `h_σ` at an integral closed subspace `Z ⊆ h_U` is the residue
degree of `σ` at the generic point of `Z`. -/
theorem functionFieldDegree_yoneda_map {U V : BigFppfOver D.site D.base D.base_mem}
    {sX : yoneda.obj U ⟶ D.space} (hX : D.IsGood sX) {sY : yoneda.obj V ⟶ D.space}
    (hY : D.IsGood sY) (σ : U ⟶ V)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U)) :
    functionFieldDegree D sX hX sY hY (yoneda.map σ) Z =
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map σ).residueDegree
        (Z.schemeGenericPoint D.site D.base D.base_mem U) :=
  finrank_residueFieldHom_yoneda_map D.site D.base D.base_mem σ _ _ _

/-- **Proper pushforward on a represented space is proper pushforward on the representing
scheme.** Let `σ : U → V` be a morphism of schemes of the site, proper, with `h_U → B` and
`h_V → B` good and compatible through `h_σ`, and let `s₀ : U → C.S` and `t₀ : V → C.S` be
δ-compatible scheme situations over a common base with `t₀ ∘ σ = s₀`. Then the pushforward of
cycles along `h_σ`, Stacks 0EP1, corresponds under `Z_k(h_U) ≅ Z_k(U)` and `Z_k(h_V) ≅ Z_k(V)`
to the proper pushforward along `σ`, Stacks 02R4. -/
theorem cycleGroupEquivScheme_properCyclePushforward
    {U V : BigFppfOver D.site D.base D.base_mem}
    {sX : yoneda.obj U ⟶ D.space} (hX : D.IsGood sX) {sY : yoneda.obj V ⟶ D.space}
    (hY : D.IsGood sY) {C : Stacks.Chow.ChowSituation.{u}}
    {s₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U ⟶ C.S} [LocallyOfFiniteType s₀]
    {t₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj V ⟶ C.S} [LocallyOfFiniteType t₀]
    (hδX : IsDeltaCompatible D U sX C s₀) (hδY : IsDeltaCompatible D V sY C t₀)
    (σ : U ⟶ V)
    [_root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme D.site D.base D.base_mem).map σ)]
    (hfB : yoneda.map σ ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem (yoneda.map σ))
    (hσ : (BigFppfOver.toScheme D.site D.base D.base_mem).map σ ≫ t₀ = s₀) (k : ℤ)
    (α : CycleGroup D sX k) :
    cycleGroupEquivScheme sY t₀ hδY k (properCyclePushforward D sX hX sY hY hfB hf k α) =
      Stacks.Chow.properPushforward C s₀ t₀ ((BigFppfOver.toScheme D.site D.base D.base_mem).map σ)
        hσ k (cycleGroupEquivScheme sX s₀ hδX k α) := by
  classical
  set σ₀ := (BigFppfOver.toScheme D.site D.base D.base_mem).map σ
  set eU := IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U
  set eV := IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem V
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [Stacks.Chow.properPushforward_apply, cycleGroupEquivScheme_apply, properPushforward_apply,
    ← finsum_comp_equiv eU.symm, finsum_mem_def]
  refine finsum_congr fun x => ?_
  rw [Set.indicator_apply]
  simp only [cycleGroupEquivScheme_apply]
  have himage : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U),
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) (yoneda.map σ) Z = eV.symm y ↔
        σ₀ (Z.schemeGenericPoint D.site D.base D.base_mem U) = y := fun Z => by
    rw [← IntegralClosedSubspace.schemeGenericPoint_closureImage D.site D.base D.base_mem σ
      (D.isDecentSpace_of_isGood sY hY) Z, ← IntegralClosedSubspace.equivSchemePoints_apply]
    exact ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [← h, Equiv.symm_apply_apply]⟩
  have hgen : (eU.symm x).schemeGenericPoint D.site D.base D.base_mem U = x :=
    IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm _ _ _ U x
  unfold properCycleMult properCycleDegree
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  by_cases hxy : σ₀ x = y
  · rw [ite_eq_left ((himage _).2 (by rw [hgen]; exact hxy)), ite_eq_left hxy,
      hδY.deltaDimension_eq, hδX.deltaDimension_eq,
      IntegralClosedSubspace.schemeGenericPoint_closureImage D.site D.base D.base_mem σ, hgen,
      functionFieldDegree_yoneda_map hX hY σ, hgen]
    by_cases hd : Stacks.Chow.relativeDimension C.dimensionFunction t₀ (σ₀ x) =
        Stacks.Chow.relativeDimension C.dimensionFunction s₀ x
    · rw [ite_eq_left hd, ite_eq_left hd.symm]
    · rw [ite_eq_right hd, ite_eq_right (Ne.symm hd)]
  · rw [ite_eq_right (fun h => hxy (by rw [← hgen]; exact (himage _).1 h)), ite_eq_right hxy,
      mul_zero]

end Pushforward

end AlgebraicGeometry.Space

end

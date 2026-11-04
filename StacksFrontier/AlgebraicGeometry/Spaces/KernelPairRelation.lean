module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.KernelPairCoequalizer

/-!
# The kernel pair of a surjective étale atlas (Stacks 0262)

Let `F` be a presheaf on the big fppf site of `S` and `f : yoneda.obj U ⟶ F` a morphism from a
represented presheaf whose kernel pair is represented by `s, t : R ⟶ U`.

Then the two projections make `R` an equivalence relation on `U` over `S`, and — when `f` is
moreover a surjective étale atlas of an algebraic space — `F` is the coequalizer of `s` and `t`
in the category of fppf sheaves of sets.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback`: **Stacks 0262**, part (1).
* `AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`: **Stacks 0262**, part (3).

## Implementation notes

Part (1) is proved internally to the site: reflexivity, symmetry and transitivity of the
kernel pair are the three lifts into `R` given by the pullback property, and monicity of
`R ⟶ U ×_S U` is the uniqueness half of that property. The source states the relation on all
schemes over `S` rather than on objects of the site, so the internal relation is transported
along `Over.post B.inclusion`, which preserves finite limits and therefore monomorphisms; the
cutoff category has pullbacks and a terminal object, which is where the size bounds of the site
enter.

Part (3) is the generic coequalizer criterion
`CategoryTheory.Sheaf.nonempty_isColimitCoforkOfKernelPair`: a locally surjective morphism of
sheaves of sets whose kernel pair is realised pointwise exhibits its target as a coequalizer.
Its two hypotheses are supplied by the Yoneda lemma — a pair of sections of `yoneda.obj U` with
the same image under `f` is the pair of projections of the lift into `R` — and by
`AlgebraicGeometry.isLocallySurjective_of_surjective_etale`, which is Tag 05VM for a surjective
étale atlas. Representables are sheaves because the big fppf site is subcanonical.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

private noncomputable def kernelPairLift
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    {T : BigFppfOver B S hS} (x y : T ⟶ U)
    (hxy : yoneda.map x ≫ f = yoneda.map y ≫ f) : T ⟶ R :=
  yoneda.preimage (hR.lift (yoneda.map x) (yoneda.map y) hxy)

private theorem kernelPairLift_props
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    {T : BigFppfOver B S hS} (x y : T ⟶ U)
  (hxy : yoneda.map x ≫ f = yoneda.map y ≫ f) :
    kernelPairLift f s t hR x y hxy ≫ s = x ∧
      kernelPairLift f s t hR x y hxy ≫ t = y := by
  constructor <;> apply yoneda.map_injective <;>
    simp only [Functor.map_comp, kernelPairLift, Functor.map_preimage]
  · exact hR.lift_fst _ _ _
  · exact hR.lift_snd _ _ _

section Part1

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable {R U : BigFppfOver B S hS}
variable (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)

/-- The kernel pair of a map from a representable presheaf defines an equivalence
relation over the base scheme. This includes monicity of `R ⟶ U ×_S U`. -/
@[stacks 0262 "part (1)"]
theorem isEquivalenceRelation_of_isPullback
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f) :
    IsEquivalenceRelation ((Over.post B.inclusion).map s)
      ((Over.post B.inclusion).map t) := by
  let c : PullbackCone t s := pullback.cone t s
  have hcomm {T : BigFppfOver B S hS} (g : T ⟶ R) :
      yoneda.map (g ≫ s) ≫ f = yoneda.map (g ≫ t) ≫ f := by
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun q => yoneda.map g ≫ q) hR.w
  have hmid : yoneda.map (c.fst ≫ t) ≫ f = yoneda.map (c.snd ≫ s) ≫ f := by
    simpa only [Functor.map_comp] using congrArg (fun q => yoneda.map q ≫ f) c.condition
  have hcomp : yoneda.map (c.fst ≫ s) ≫ f = yoneda.map (c.snd ≫ t) ≫ f :=
    (hcomm c.fst).trans (hmid.trans (hcomm c.snd))
  let e : EquivalenceRelation s t := {
    right_cancellation := by
      intro T a b has hbt
      apply yoneda.map_injective
      apply hR.hom_ext
      · simpa only [← Functor.map_comp] using congrArg yoneda.map has
      · simpa only [← Functor.map_comp] using congrArg yoneda.map hbt
    r := kernelPairLift f s t hR (𝟙 U) (𝟙 U) (by simp)
    reflexivity₁ := by
      exact (kernelPairLift_props f s t hR (𝟙 U) (𝟙 U) (by simp)).1
    reflexivity₂ := by
      exact (kernelPairLift_props f s t hR (𝟙 U) (𝟙 U) (by simp)).2
    s := kernelPairLift f s t hR t s hR.w.symm
    symmetry₁ := by
      exact (kernelPairLift_props f s t hR t s hR.w.symm).1
    symmetry₂ := by
      exact (kernelPairLift_props f s t hR t s hR.w.symm).2
    c := c
    isLimit := pullback.isLimit t s
    t := kernelPairLift f s t hR (c.fst ≫ s) (c.snd ≫ t) hcomp
    transitivity₁ := by
      exact (kernelPairLift_props f s t hR (c.fst ≫ s) (c.snd ≫ t) hcomp).1
    transitivity₂ := by
      exact (kernelPairLift_props f s t hR (c.fst ≫ s) (c.snd ≫ t) hcomp).2 }
  -- The source asserts the relation on all schemes over S. Transport the
  -- internal relation along the inclusion, which preserves finite limits.
  let : HasFiniteLimits B.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := by infer_instance
  let : PreservesLimitsOfShape (Discrete PEmpty) B.inclusion := by infer_instance
  let : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  let G : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let : PreservesFiniteLimits G :=
    PreservesFiniteLimits.overPost (F := B.inclusion) (X := B.obj hS)
  let : PreservesLimitsOfShape WalkingCospan G := by infer_instance
  let : PreservesLimitsOfShape (Discrete WalkingPair) G := by infer_instance
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let p : R ⟶ U ⨯ U := prod.lift s t
  have hp : Mono p := by
    constructor
    intro Y a b hab
    apply e.right_cancellation a b
    · simpa [p] using congrArg (fun k => k ≫ prod.fst) hab
    · simpa [p] using congrArg (fun k => k ≫ prod.snd) hab
  let : Mono (G.map p) := preserves_mono_of_preservesLimit G p
  let eprod : G.obj (U ⨯ U) ≅ G.obj U ⨯ G.obj U :=
    PreservesLimitPair.iso G U U
  let : JointlyMono₂ (G.map s) (G.map t) := by
    constructor
    intro Y a b h₁ h₂
    apply (cancel_mono (G.map p)).mp
    apply (cancel_mono eprod.hom).mp
    apply prod.hom_ext
    · simpa [eprod, p, PreservesLimitPair.iso_hom, ← G.map_comp] using h₁
    · simpa [eprod, p, PreservesLimitPair.iso_hom, ← G.map_comp] using h₂
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := e.toReflexiveRelation.map G
      __ := e.toSymmetricRelation.map G
      __ := e.toTransitiveRelation.map G }


end Part1

add_to_stacks 0262 "part (2), étale projections" CategoryTheory.MorphismProperty.relative.property

/-- **Stacks 0262**, part (3). A surjective étale atlas of an algebraic space is the
coequalizer, in fppf sheaves of sets, of its kernel pair: every map to a sheaf which
identifies the two projections descends uniquely. -/
@[stacks 0262 "part (3)"]
theorem isCoequalizer_of_surjectiveEtale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hF : IsAlgebraicSpace B S hS F)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    let J := BigFppfOver.topology B S hS
    ∃ (hRsh : Presheaf.IsSheaf J (yoneda.obj R))
      (hUsh : Presheaf.IsSheaf J (yoneda.obj U)),
      let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
      let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
      let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
      let sf : RF ⟶ UF := ⟨yoneda.map s⟩
      let tf : RF ⟶ UF := ⟨yoneda.map t⟩
      let ff : UF ⟶ FF := ⟨f⟩
    let w : sf ≫ ff = tf ≫ ff := by
        apply Sheaf.hom_ext
        exact hR.w
      Nonempty (IsColimit (Cofork.ofπ ff w)) := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : J.Subcanonical := inferInstance
  have hsh (X : BigFppfOver B S hS) : Presheaf.IsSheaf J (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type J (yoneda.obj X)).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj X))
  have hRsh := hsh R
  have hUsh := hsh U
  refine ⟨hRsh, hUsh, ?_⟩
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let ff : UF ⟶ FF := ⟨f⟩
  let w : sf ≫ ff = tf ≫ ff := by
    apply Sheaf.hom_ext
    exact hR.w
  have hker : ∀ ⦃T : BigFppfOver B S hS⦄ (x y : UF.obj.obj (Opposite.op T)),
      ff.hom.app (Opposite.op T) x = ff.hom.app (Opposite.op T) y →
      ∃ r : RF.obj.obj (Opposite.op T),
        sf.hom.app (Opposite.op T) r = x ∧ tf.hom.app (Opposite.op T) r = y := by
    intro T x y hxy
    have hxy' : yoneda.map x ≫ f = yoneda.map y ≫ f := by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hxy
    exact ⟨kernelPairLift f s t hR x y hxy', (kernelPairLift_props f s t hR x y hxy').1,
      (kernelPairLift_props f s t hR x y hxy').2⟩
  exact Sheaf.nonempty_isColimitCoforkOfKernelPair sf tf ff w hker
    (isLocallySurjective_of_surjective_etale B S hS f hsurj hetale)

end AlgebraicGeometry.Space

end

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubfunctorSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionReduction
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineSupplement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas

/-!
# The completion of a formal algebraic space along a closed subset is a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` and let `T ⊆ |X_red|` be a closed subset. **Stacks 0GVR** says that the functor

```
X_{/T} : (Sch/S)_fppf ⟶ Sets,    U ↦ {f : U ⟶ X | f(|U|) ⊆ T}
```

is a formal algebraic space. This file proves it with no hypothesis beyond the tag's own.

The functor is `AlgebraicGeometry.Space.completionSubfunctorULift` of `X`, along the image of
`T` in `|X|` under the inclusion of the reduction; the completion `X_{/T}` of the library is
`AlgebraicGeometry.FormalSpace.completionAlong` (Stacks 0GVS), its fppf sheafification. The
first step of the source's proof — the functor is already an fppf sheaf, because a covering is
surjective on points — is `AlgebraicGeometry.Space.isSheaf_completionSubfunctorULift`, so the
functor and `completionAlong` are the same sheaf, and the theorem is stated for both.

The atlas of Definition 0AIM is the one of the source,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheafULift`: the base changes
`X_k ×_X X_{/T} = (X_k)_{/T_k}` of an atlas `{X_k ⟶ X}` of `X`, affine formal algebraic spaces
by Stacks 0GVQ. What remains is the set-theoretic condition of Stacks 0AIS, which Definition
0AIM includes and which is proved here from the condition for `X` itself:

* the condition for `X` gives a surjection `p : h_U ⟶ X` from the sheaf of an object of the site;
  the completion of `h_U` along the inverse image of `T` surjects onto `X_{/T}`, and it receives
  a surjection from the sheaf of an object `V` of the site by Stacks 0AIS for the completion of
  an algebraic space, so `X_{/T}` does;
* the kernel pair of `h_V ⟶ X_{/T}` is that of `h_V ⟶ X`, the inclusion `X_{/T} ⟶ X` being a
  monomorphism, and `h_V ⟶ X` factors through `p`; so that kernel pair maps to `h_U ×_X h_U`
  by a morphism which is representable (two base changes of a morphism `h_V ⟶ h_U` of
  representable sheaves), and its base change along the surjection onto `h_U ×_X h_U` given by
  the condition for `X` is the required representable surjection.

## Main results

* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_epi_of_mono_factor`: the
  set-theoretic condition for a subsheaf receiving a representable surjection which factors
  through the one of the ambient sheaf.
* `satisfiesSetTheoreticCondition_completionSheafULift_of_satisfiesSetTheoreticCondition`:
  Stacks 0AIS for the completion of a sheaf satisfying it, along a closed set of points.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheafULift_of_isClosed`: the
  completion of a formal algebraic space along a closed set of its points is a formal
  algebraic space.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionAlong_of_isClosed`: the same
  for the completion `X_{/T}` along a closed subset `T ⊆ |X_red|` of a reduction.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionFunctor`: **Stacks 0GVR**.

## What is assumed

Nothing beyond the tag's own hypotheses. In particular the set-theoretic condition of Stacks
0AIS on `X_{/T}` is proved, and so is the affine case (Stacks 0GVQ). The reduction
`i : X_red ⟶ X` is any reduction of `X`; one exists by Stacks 0AIN
(`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`), and the
statement holds for every one of them.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0GVQ](https://stacks.math.columbia.edu/tag/0GVQ)
* [Stacks Project, Tag 0GVR](https://stacks.math.columbia.edu/tag/0GVR)
* [Stacks Project, Tag 0GVS](https://stacks.math.columbia.edu/tag/0GVS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The set-theoretic condition of Stacks 0AIS for a completion -/

/-- **The set-theoretic condition passes to a subsheaf receiving a representable surjection
compatibly with a given one.** Let `X` be an fppf sheaf over `S` with a surjection `p : h_U ⟶ X`
from a representable sheaf and a surjection `q : h_R ⟶ h_U ×_X h_U` from a representable sheaf
onto its kernel pair. Let `m : Y ⟶ X` be a monomorphism and `e : h_V ⟶ Y` a surjection from a
representable sheaf whose composite into `X` factors through `p` as `a ≫ p`. Then `Y` satisfies
the set-theoretic condition of Stacks 0AIS.

The surjection onto `Y` is `e`. Its kernel pair `h_V ×_Y h_V` is `h_V ×_X h_V`, `m` being a
monomorphism, and it maps to `h_U ×_X h_U` by a morphism which is two base changes of
`a : h_V ⟶ h_U`, hence representable: `a` is a morphism between representable sheaves of a
subcanonical site with fibre products. Its base change along `q` is therefore representable by
an object of the site, and surjects onto `h_V ×_Y h_V` because `q` is a surjection. -/
theorem satisfiesSetTheoreticCondition_of_epi_of_mono_factor
    {X Y hU hR : FppfSheaf B S hS} {U R V : BigFppfOver B S hS}
    (hUrep : Nonempty (hU.obj ≅ (uliftYoneda.{u + 1}).obj U))
    (hRrep : Nonempty (hR.obj ≅ (uliftYoneda.{u + 1}).obj R))
    (p : hU ⟶ X) (q : hR ⟶ pullback p p) (hq : Epi q)
    (m : Y ⟶ X) (hm : Mono m)
    (e : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ Y) (he : Epi e)
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ hU)
    (ha : a ≫ p = e ≫ m) :
    SatisfiesSetTheoreticCondition B S hS Y := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let G := Sheaf.sheafifiedYoneda J
  let Fp := sheafToPresheaf J (Type (u + 1))
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  let _ : PreservesLimitsOfShape WalkingCospan G :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  let eU : hU ≅ G.obj U :=
    (Functor.FullyFaithful.ofFullyFaithful Fp).preimageIso
      (Classical.choice hUrep ≪≫ (Fp.mapIso (eG.app U)).symm)
  let eR : hR ≅ G.obj R :=
    (Functor.FullyFaithful.ofFullyFaithful Fp).preimageIso
      (Classical.choice hRrep ≪≫ (Fp.mapIso (eG.app R)).symm)
  -- `a` is a morphism between representable sheaves, hence relatively representable
  have hrep_a : G.relativelyRepresentable a := by
    have h := MorphismProperty.comp_mem _ _ _
      (Functor.relativelyRepresentable.map G (Sheaf.representingHom (a ≫ eU.hom)))
      (Functor.relativelyRepresentable.of_isIso G eU.inv)
    rwa [Sheaf.map_representingHom, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  let w := a ≫ p
  -- the comparison `h_V ×_X h_V ⟶ h_V ×_X h_U ⟶ h_U ×_X h_U`, two base changes of `a`
  let φ₁ : pullback w w ⟶ pullback w p :=
    pullback.lift (pullback.fst w w) (pullback.snd w w ≫ a) (by
      rw [Category.assoc]
      exact pullback.condition)
  let φ₂ : pullback w p ⟶ pullback p p :=
    pullback.lift (pullback.fst w p ≫ a) (pullback.snd w p) (by
      rw [Category.assoc]
      exact pullback.condition)
  have h₁ : IsPullback φ₁ (pullback.snd w w) (pullback.snd w p) a := by
    have hs : IsPullback (φ₁ ≫ pullback.fst w p) (pullback.snd w w) w (a ≫ p) := by
      rw [show φ₁ ≫ pullback.fst w p = pullback.fst w w from pullback.lift_fst _ _ _]
      exact IsPullback.of_hasPullback w w
    exact IsPullback.of_right hs (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback w p)
  have h₂ : IsPullback φ₂ (pullback.fst w p) (pullback.fst p p) a := by
    have hs : IsPullback (φ₂ ≫ pullback.snd p p) (pullback.fst w p) p (a ≫ p) := by
      rw [show φ₂ ≫ pullback.snd p p = pullback.snd w p from pullback.lift_snd _ _ _]
      exact (IsPullback.of_hasPullback w p).flip
    exact IsPullback.of_right hs (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback p p).flip
  have hφ : G.relativelyRepresentable (φ₁ ≫ φ₂) :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.of_isPullback h₁.flip hrep_a)
      (MorphismProperty.of_isPullback h₂.flip hrep_a)
  -- the base change of the surjection onto `h_U ×_X h_U` is represented
  let q' : G.obj R ⟶ pullback p p := eR.inv ≫ q
  have hq' : Epi q' := by dsimp only [q']; infer_instance
  obtain ⟨Q, s, f₁, hpb⟩ := hφ q'
  have hf₁ : Epi f₁ := by
    have := Sheaf.epi_pullback_snd q' (φ₁ ≫ φ₂) hq'
    rw [← hpb.flip.isoPullback_hom_snd]
    infer_instance
  -- `h_V ×_X h_V` is `h_V ×_Y h_V`, since `m` is a monomorphism
  let c : pullback w w ⟶ pullback e e :=
    pullback.lift (pullback.fst w w) (pullback.snd w w) (by
      refine hm.right_cancellation _ _ ?_
      rw [Category.assoc, Category.assoc, ← ha]
      exact pullback.condition)
  let d : pullback e e ⟶ pullback w w :=
    pullback.lift (pullback.fst e e) (pullback.snd e e) (by
      change _ ≫ a ≫ p = _ ≫ a ≫ p
      rw [ha, ← Category.assoc, ← Category.assoc, pullback.condition])
  have hdc : d ≫ c = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc]
      exact (congrArg (d ≫ ·) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _)
    · rw [Category.id_comp, Category.assoc]
      exact (congrArg (d ≫ ·) (pullback.lift_snd _ _ _)).trans (pullback.lift_snd _ _ _)
  have hc : IsSplitEpi c := ⟨⟨d, hdc⟩⟩
  exact ⟨V, Q, G.obj V, G.obj Q, ⟨Fp.mapIso (eG.app V)⟩, ⟨Fp.mapIso (eG.app Q)⟩, e, he,
    f₁ ≫ c, epi_comp' hf₁ (IsSplitEpi.epi c)⟩

/-- **Stacks 0AIS for the completion of a sheaf satisfying it.** Let `X` be an fppf sheaf over
`S` satisfying the set-theoretic condition of Stacks 0AIS — a formal algebraic space, say — and
let `W` be a closed set of points of `X`. Then the completion `X_{/W}` satisfies the condition.

The condition for `X` gives a surjection `p : h_U ⟶ X` from the sheaf of an object `U` of the
site and a surjection from a representable sheaf onto `h_U ×_X h_U`. The completion of `h_U`
along the inverse image of `W` surjects onto `X_{/W}`
(`AlgebraicGeometry.FormalSpace.epi_completionSheafMapULift`), and it satisfies the condition
by Stacks 0AIS for the completion of an algebraic space
(`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheaf`), so `X_{/W}`
receives a surjection `e : h_V ⟶ X_{/W}` from the sheaf of an object `V` of the site, which
factors through `p` after the inclusion `X_{/W} ⟶ X` by the completion square. Since that
inclusion is a monomorphism, the kernel pair of `e` is represented after base change along the
given surjection onto `h_U ×_X h_U`:
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_epi_of_mono_factor`. -/
theorem satisfiesSetTheoreticCondition_completionSheafULift_of_satisfiesSetTheoreticCondition
    (X : FppfSheaf B S hS) (hX : SatisfiesSetTheoreticCondition B S hS X)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W) :
    SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS X W) := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let G := Sheaf.sheafifiedYoneda J
  let Fp := sheafToPresheaf J (Type (u + 1))
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  -- the representable surjection onto `X` and onto its kernel pair
  obtain ⟨U₀, R₀, hU₀, hR₀, hU₀rep, hR₀rep, p, hp, q₀, hq₀⟩ := hX
  let Y : FppfSheaf B S hS := ⟨yoneda.obj U₀ ⋙ uliftFunctor.{u + 1},
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U₀).isSheaf⟩
  let eU : hU₀ ≅ Y :=
    (Functor.FullyFaithful.ofFullyFaithful Fp).preimageIso (Classical.choice hU₀rep)
  let g : Y ⟶ X := eU.inv ≫ p
  have hg : Epi g := by dsimp only [g]; infer_instance
  let _ := Space.pointTopologyULift.{u + 1} B S hS X.obj
  let _ := Space.pointTopologyULift.{u + 1} B S hS Y.obj
  let _ := Space.pointTopology B S hS (yoneda.obj U₀)
  -- the inverse image of `W` on the chart, as a closed set of points of the chart
  have hW'closed : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Y.obj)
      (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) :=
    hW.preimage (Space.continuous_pointsMapULift.{u + 1} B S hS g.hom)
  set T₀ : Set (Space.points B S hS (yoneda.obj U₀)) :=
    Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U₀) ⁻¹'
      (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) with hT₀def
  have hT₀ : @IsClosed _ (Space.pointTopology B S hS (yoneda.obj U₀)) T₀ :=
    hW'closed.preimage
      (Space.pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U₀)).continuous
  have hWeq : (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U₀)).symm ⁻¹' T₀ =
      Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W := by
    rw [hT₀def, ← Set.preimage_comp, Equiv.self_comp_symm, Set.preimage_id]
  have hbridge : Space.completionSheaf B S hS (yoneda.obj U₀) T₀ =
      Space.completionSheafULift B S hS Y
        (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) := by
    rw [← hWeq]
    exact completionSheaf_eq_completionSheafULift_uliftYoneda B S hS U₀ T₀
  -- Stacks 0AIS for the completion of the chart, a represented sheaf
  have hcond :
      SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS Y
        (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W)) := by
    rw [← hbridge]
    exact satisfiesSetTheoreticCondition_completionSheaf
      (isAlgebraicSpace_yoneda B S hS U₀) T₀ hT₀
  obtain ⟨V, -, hV, -, hVrep, -, qV, hqV, -, -⟩ := hcond
  have hm : Epi (Space.completionSheafMapULift B S hS g
      (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) W (Set.Subset.refl _)) :=
    epi_completionSheafMapULift B S hS g hg W
  let eV : hV ≅ G.obj V :=
    (Functor.FullyFaithful.ofFullyFaithful Fp).preimageIso
      (Classical.choice hVrep ≪≫ (Fp.mapIso (eG.app V)).symm)
  let fV : G.obj V ⟶ Space.completionSheafULift B S hS X W :=
    eV.inv ≫ qV ≫ Space.completionSheafMapULift B S hS g
      (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) W (Set.Subset.refl _)
  have hfV : Epi fV := by dsimp only [fV]; infer_instance
  -- the completion square of the chart: `fV` lies over `p` after the inclusion into `X`
  have hsq := Space.isPullback_completionSheafMapULift B S hS g
    (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) W (Set.Subset.refl _) (Set.Subset.refl _)
  refine satisfiesSetTheoreticCondition_of_epi_of_mono_factor B S hS hU₀rep hR₀rep p q₀ hq₀
    (Space.completionSheafULiftInclusion B S hS X W)
    (Space.mono_completionSheafULiftInclusion B S hS X W) fV hfV
    (eV.inv ≫ qV ≫ Space.completionSheafULiftInclusion B S hS Y
      (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) ≫ eU.inv) ?_
  simp only [fV, Category.assoc]
  rw [← hsq.w]

/-- **The completion of a formal algebraic space along a closed set of its points is a formal
algebraic space**, with no hypothesis: the atlas is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheafULift`, its affine charts
are clause (1) of Stacks 0GVV (`AlgebraicGeometry.FormalSpace.completionOfAffineIsAffine`), and
the set-theoretic condition of Stacks 0AIS is
`satisfiesSetTheoreticCondition_completionSheafULift_of_satisfiesSetTheoreticCondition`, from the
condition for `X` itself. -/
theorem isFormalAlgebraicSpace_completionSheafULift_of_isClosed {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) T) :
    IsFormalAlgebraicSpace B S hS (Space.completionSheafULift B S hS X T) :=
  isFormalAlgebraicSpace_completionSheafULift' B S hS hX T hT
    (satisfiesSetTheoreticCondition_completionSheafULift_of_satisfiesSetTheoreticCondition B S hS
      X hX.1 T hT)

/-- **The completion `X_{/T}` of a formal algebraic space along a closed subset of its
reduction is a formal algebraic space**, for the completion
`AlgebraicGeometry.FormalSpace.completionAlong` of Stacks 0GVS and any reduction
`i : X_red ⟶ X`. The closed subset `T ⊆ |X_red|` is closed in `|X|` through `i`, the inclusion
of a reduction being a homeomorphism on points. -/
theorem isFormalAlgebraicSpace_completionAlong_of_isClosed {X Xred : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T) :
    IsFormalAlgebraicSpace B S hS (completionAlong i T) :=
  isFormalAlgebraicSpace_completionSheafULift_of_isClosed B S hS hX _
    (hi.isClosed_image_pointsMapULift (T := T) hT)

/-- **Stacks 0GVR.** Let `S` be a scheme, let `X` be a formal algebraic space over `S` and let
`T ⊆ |X_red|` be a closed subset, for a reduction `i : X_red ⟶ X` of `X`. Then the functor
`X_{/T}` on the big fppf site of `S` sending `U` to the morphisms `f : U ⟶ X` with
`f(|U|) ⊆ T` is a formal algebraic space: it is an fppf sheaf, and as such a formal algebraic
space over `S`. It is the completion `completionAlong i T` of Stacks 0GVS, which is a formal
algebraic space as well.

The functor is `AlgebraicGeometry.Space.completionSubfunctorULift` of `X` along the image of
`T` in `|X|`. Nothing is assumed: the sheaf property is
`AlgebraicGeometry.Space.isSheaf_completionSubfunctorULift`, the atlas of Definition 0AIM is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheafULift` with its affine
charts from Stacks 0GVQ, and the set-theoretic condition of Stacks 0AIS is
`satisfiesSetTheoreticCondition_completionSheafULift_of_satisfiesSetTheoreticCondition`.
A reduction exists by Stacks 0AIN, and the statement holds for every one. -/
@[stacks 0GVR "the functor `X_{/T}` is an fppf sheaf and a formal algebraic space, for any \
reduction `X_red` of `X` and `T` closed in `|X_red|`; the atlas, the affine case 0GVQ and the \
set-theoretic condition of 0AIS for `X_{/T}` are all proved here"]
theorem isFormalAlgebraicSpace_completionFunctor {X Xred : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T) :
    ∃ h : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
        (Space.completionSubfunctorULift B S hS X.obj
          (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T)).toFunctor,
      IsFormalAlgebraicSpace B S hS ⟨_, h⟩ ∧
        IsFormalAlgebraicSpace B S hS (completionAlong i T) := by
  have h := Space.isSheaf_completionSubfunctorULift B S hS X
    (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T)
  have hc := isFormalAlgebraicSpace_completionAlong_of_isClosed B S hS hX hi T hT
  exact ⟨h, isFormalAlgebraicSpace_of_iso B S hS (Space.isoSheafifySheaf B S hS ⟨_, h⟩) hc, hc⟩

end AlgebraicGeometry.FormalSpace

end

module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraizationGluing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringOfOpenCover

/-!
# The functor of Stacks 0AR5, unconditionally

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be closed and let `U ⊂ X` be the open subspace with
`|U| = |X| ∖ T`. **Stacks 0AR5** is the completion functor
`(f : X' ⟶ X) ↦ (f_{/T} : X'_{/T'} ⟶ X_{/T})` from the morphisms locally of finite type which
are an isomorphism over `U` to the rig-étale morphisms `g : W ⟶ X_{/T}` of formal algebraic
spaces with `W` locally Noetherian.

The library's `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor` carries
three hypotheses (`h0AIZ`, `hnoeth`, `hred`) placing the completion in the target category. The
functor here carries none: the three conditions are proved, by Stacks 0AIZ
(`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheaf_of_isClosed`), Stacks
0AQ1 (2)
(`AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian`) and
Stacks 0AR2 (`AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap_of_isEtale`).
The two functors are equal whenever the hypotheses of the first are supplied.

## Main definitions

* `AlgebraicGeometry.FormalSpace.completionModificationFunctor`: **Stacks 0AR5**, with no
  hypotheses beyond the source's.
* `AlgebraicGeometry.FormalSpace.completionModificationFunctorFullyFaithful`: it is fully
  faithful (Stacks 0GDR).
* `AlgebraicGeometry.FormalSpace.rigEtaleOverCompletionBaseChange`: for an étale morphism
  `e : X₁ ⟶ X` of algebraic spaces, the base change `W ×_{X/T} X_{1,/T}` of an object of the
  right-hand category of Stacks 0AR5 for `X` is an object of that category for `X₁`.

## Main results

* `completionFiniteTypeModificationFunctor_eq_completionModificationFunctor`: the library's
  conditional functor is this one.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_completionSheafMap`,
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_pullback_completionSheafMap` and
  `AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_completionSheafMap`: the three
  conditions on the base change along an étale chart; the last one is Stacks 0GD1.
* `AlgebraicGeometry.FormalSpace.mem_essImage_completionModificationFunctor_of_cover`: the
  global gluing step of Stacks 0ARB for this functor.
* `AlgebraicGeometry.FormalSpace.mem_essImage_completionModificationFunctor_of_affine_charts`:
  the same over the affine étale charts `Spec R ⟶ X` (with `R` Noetherian) of an atlas of `X`.

## References

* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
* [Stacks Project, Tag 0AIZ](https://stacks.math.columbia.edu/tag/0AIZ)
* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-! ### The functor -/

/-- **Stacks 0AR5.** Let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be
closed and let `U ⊂ X` be the open subspace with `|U| = |X| ∖ T`. Completion along `T` is a
functor from the morphisms `f : X' ⟶ X` of algebraic spaces which are locally of finite type and
an isomorphism over `U` to the morphisms `g : W ⟶ X_{/T}` of formal algebraic spaces with `W`
locally Noetherian and `g` rig-étale.

The arrow map is `AlgebraicGeometry.Space.completionOverFunctor`. The three conditions on the
value are proved: `X'_{/T'}` is a formal algebraic space by Stacks 0AIZ, it is locally Noetherian
by Stacks 0AQ1 (2) since `X'` is locally of finite type over the locally Noetherian `X`, and
`f_{/T}` is rig-étale by Stacks 0AR2 since `U' ⟶ U` is an isomorphism.

This is a new object and not a copy of
`AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor`: that functor is only
defined when three hypotheses (`h0AIZ`, `hnoeth`, `hred`) are given, and this one needs none of
them. When they are given, the two functors are equal
(`completionFiniteTypeModificationFunctor_eq_completionModificationFunctor`). -/
@[stacks 0AR5 "the completion functor with the source's hypotheses only: X a locally Noetherian \
algebraic space and T closed; the three conditions placing f_{/T} in the right-hand category \
are proved by 0AIZ, 0AQ1 (2) and 0AR2"]
def completionModificationFunctor {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (hXsp : IsAlgebraicSpace B S hS X)
    (hX : Space.IsLocallyNoetherian B S hS X) :
    Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ) ⥤
      RigEtaleOverCompletion B S hS X T :=
  ObjectProperty.lift _ (finiteTypeModificationCompletion T) fun M =>
    ⟨isFormalAlgebraicSpace_completionSheaf_of_isClosed M.property.1.1 _
        (hT.preimage (Space.continuous_pointsMap B S hS M.obj.hom)),
      isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian M.property.1.1
        (isLocallyNoetherian_of_isLocallyOfFiniteType M.property.1.1 hXsp M.obj.hom
          M.property.2 hX) _ (hT.preimage (Space.continuous_pointsMap B S hS M.obj.hom)),
      isRigEtale_completionSheafMap_of_isEtale M.property.1.1 hXsp M.obj.hom T hT hX
        M.property.2
        (Space.isEtale_openComplementRestriction B S hS M.obj.hom T M.property.1.2)⟩

/-- Followed by the inclusion of the right-hand category, the functor of Stacks 0AR5 is the
completion functor `AlgebraicGeometry.FormalSpace.finiteTypeModificationCompletion`. -/
theorem completionModificationFunctor_comp_ι {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (hXsp : IsAlgebraicSpace B S hS X)
    (hX : Space.IsLocallyNoetherian B S hS X) :
    completionModificationFunctor T hT hXsp hX ⋙
        ObjectProperty.ι (fun W : Over (Space.completionSheaf B S hS X T) =>
          IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
            IsRigEtale B S hS W.hom) =
      finiteTypeModificationCompletion T :=
  rfl

/-- **The conditional functor of Stacks 0AR5 is the unconditional one.** Whenever the three
hypotheses of `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor` are
supplied, it is equal to `AlgebraicGeometry.FormalSpace.completionModificationFunctor`. -/
theorem completionFiniteTypeModificationFunctor_eq_completionModificationFunctor
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (hXsp : IsAlgebraicSpace B S hS X)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T) :
    completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred =
      completionModificationFunctor T hT hXsp hX :=
  rfl

/-- The étale-local form of local Noetherianity of an algebraic space. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXsp : IsAlgebraicSpace B S hS X)
    (hX : Space.IsLocallyNoetherian B S hS X) :
    Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) :=
  (Space.exists_atlas_iff_forall_etale B S hS X _ hXsp).mpr fun W q hq ↦
    hX W q ((Space.isEtale_iff_presheaf_of_yoneda B S hS q).2 hq)

/-- **The functor of Stacks 0AR5 is fully faithful** (Stacks 0GDR). This is
`AlgebraicGeometry.FormalSpace.finiteTypeModificationCompletionFullyFaithful` read through the
full subcategory of the right-hand side. -/
def completionModificationFunctorFullyFaithful {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (hXsp : IsAlgebraicSpace B S hS X)
    (hX : Space.IsLocallyNoetherian B S hS X) :
    (completionModificationFunctor T hT hXsp hX).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    (finiteTypeModificationCompletionFullyFaithful hXsp
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hXsp hX) T hT)

/-! ### Base change along an étale chart -/

/-- Pullbacks of fppf sheaves (in `Type (u + 1)`, where completions live), found once: instance
search for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_sheaf_CompletionModificationFunctor :
    HasPullbacks (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) := by
  set_option synthInstance.maxHeartbeats 400000 in infer_instance

/-- The pullback of two morphisms of fppf sheaves in `Type (u + 1)`. -/
local instance (priority := high) hasLimit_cospan_sheaf_CompletionModificationFunctor
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section BaseChange

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_CompletionModificationFunctor :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_CompletionModificationFunctor
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {X X₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXsp : IsAlgebraicSpace B S hS X)
  (hX : Space.IsLocallyNoetherian B S hS X) {T : Set (Space.points B S hS X)} (hT : IsClosed T)
  (W : RigEtaleOverCompletion B S hS X T) (hX₁ : IsAlgebraicSpace B S hS X₁) (e : X₁ ⟶ X)
  (he : Space.IsEtale B S hS e)

include hXsp hX₁ he in
/-- The completion of an étale morphism of algebraic spaces is representable étale
(Stacks 0GI0). -/
theorem isRepresentableEtale_completionSheafMap :
    IsRepresentableEtale B S hS (Space.completionSheafMap B S hS e T) :=
  isEtale_completionSheafMap B S hS hX₁ hXsp e T he

include hXsp hT hX₁ in
/-- **The base change of an object of the right-hand category of Stacks 0AR5 along a chart is a
formal algebraic space.** For a morphism `e : X₁ ⟶ X` of algebraic spaces, `W ×_{X/T} X_{1,/T}`
is a formal algebraic space: `X_{/T}` and `X_{1,/T}` are formal algebraic spaces by Stacks 0AIZ,
and a fibre product of formal algebraic spaces over a formal algebraic space is one. -/
theorem isFormalAlgebraicSpace_pullback_completionSheafMap :
    IsFormalAlgebraicSpace B S hS (pullback W.obj.hom (Space.completionSheafMap B S hS e T)) :=
  isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS _ _
    (isFormalAlgebraicSpace_completionSheaf_of_isClosed hXsp T hT) W.property.1
    (isFormalAlgebraicSpace_completionSheaf_of_isClosed hX₁ _
      (hT.preimage (Space.continuous_pointsMap B S hS e)))

include hXsp hT hX₁ he in
/-- **The base change of an object of the right-hand category of Stacks 0AR5 along an étale chart
is locally Noetherian.** For an étale morphism `e : X₁ ⟶ X` of algebraic spaces, the projection
`W ×_{X/T} X_{1,/T} ⟶ W` is representable étale, so every affine chart of the fibre product is an
affine chart of the locally Noetherian `W`, hence Noetherian. -/
theorem isLocallyNoetherian_pullback_completionSheafMap :
    IsLocallyNoetherian B S hS (pullback W.obj.hom (Space.completionSheafMap B S hS e T)) := by
  have hP := isFormalAlgebraicSpace_pullback_completionSheafMap hXsp hT W hX₁ e
  have hfst : IsRepresentableEtale B S hS
      (pullback.fst W.obj.hom (Space.completionSheafMap B S hS e T)) :=
    isRepresentableEtale_pullback_fst B S hS _ _
      (isRepresentableEtale_completionSheafMap (T := T) hXsp hX₁ e he)
  obtain ⟨-, I, Xi, f, haff, het, hsurj⟩ := id hP
  exact ⟨hP, I, Xi, f, haff, het, hsurj, fun i =>
    isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS W.property.2.1 _
      (haff i) (IsRepresentableEtale.comp B S hS (het i) hfst)⟩

include hXsp hX hT hX₁ he in
/-- **The base change of an object of the right-hand category of Stacks 0AR5 along an étale chart
is rig-étale over the completion of the chart** (Stacks 0GD1). `X_{/T}` and `X_{1,/T}` are
locally Noetherian by Stacks 0AQ1 (2), `X₁` being étale over the locally Noetherian `X`, and the
completion of `e` is adic, being representable by algebraic spaces. -/
theorem isRigEtale_pullback_snd_completionSheafMap :
    IsRigEtale B S hS (pullback.snd W.obj.hom (Space.completionSheafMap B S hS e T)) :=
  isRigEtale_pullback_snd_of_isLocallyNoetherian B S hS _ _ W.property.2.1
    (isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hXsp hX T hT)
    (isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hX₁
      (isLocallyNoetherian_of_isLocallyOfFiniteType hX₁ hXsp e
        (Space.isLocallyOfFiniteType_of_isEtale' B S hS e he) hX) _
      (hT.preimage (Space.continuous_pointsMap B S hS e)))
    W.property.2.2 (isRepresentableEtale_completionSheafMap (T := T) hXsp hX₁ e he).1

/-- **The chart input of Stacks 0ARB.** For an étale morphism `e : X₁ ⟶ X` of algebraic spaces,
with `X` locally Noetherian, the base change `W ×_{X/T} X_{1,/T} ⟶ X_{1,/T}` of an object `W` of
the right-hand category of Stacks 0AR5 for `X` and `T` is an object of that category for `X₁`
and `|e|⁻¹T`. The source applies this with `X₁ = Spec R` an affine étale chart, `R` Noetherian,
before Stacks 0ARA. -/
def rigEtaleOverCompletionBaseChange :
    RigEtaleOverCompletion B S hS X₁ (Space.pointsMap B S hS X₁ e ⁻¹' T) :=
  ⟨Over.mk (pullback.snd W.obj.hom (Space.completionSheafMap B S hS e T)),
    isFormalAlgebraicSpace_pullback_completionSheafMap hXsp hT W hX₁ e,
    isLocallyNoetherian_pullback_completionSheafMap hXsp hT W hX₁ e he,
    isRigEtale_pullback_snd_completionSheafMap hXsp hX hT W hX₁ e he⟩

end BaseChange

/-! ### Essential surjectivity from charts -/

/-- **Essential surjectivity of the functor of Stacks 0AR5, from algebraizations over a
covering.** If, over each member `X i` of an fppf covering of `Y₀` by locally Noetherian algebraic
spaces locally of finite type over `Y₀`, the base change `W ×_{Y₀/T} (X i)_{/T}` is the
completion of a finite-type modification of `X i`, then `W` is in the essential image of
`AlgebraicGeometry.FormalSpace.completionModificationFunctor`. This is the global step of the
proof of Stacks 0ARB,
`AlgebraicGeometry.Space.CompletionAlgebraization.exists_completion_iso_of_cover`, for the
unconditional functor. -/
theorem mem_essImage_completionModificationFunctor_of_cover
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS Y₀)) (hT : IsClosed T) (hY₀sp : IsAlgebraicSpace B S hS Y₀)
    (hY₀ : Space.IsLocallyNoetherian B S hS Y₀) (W : RigEtaleOverCompletion B S hS Y₀ T)
    {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {e : ∀ i, X i ⟶ Y₀}
    (hcov : Space.IsFppfCovering B S hS X e)
    (hXnoeth : ∀ i, Space.HasEtaleLocalProperty B S hS (X i)
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (he : ∀ i, Space.IsLocallyOfFiniteType B S hS (e i))
    (hloc : ∀ i, ∃ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS (X i) (Space.pointsMap B S hS (X i) (e i) ⁻¹' T)ᶜ),
      Nonempty ((Space.completionOverFunctor B S hS
          (Space.pointsMap B S hS (X i) (e i) ⁻¹' T)).obj M.obj ≅
        Over.mk (pullback.snd W.obj.hom (Space.completionSheafMap B S hS (e i) T)))) :
    (completionModificationFunctor T hT hY₀sp hY₀).essImage W := by
  choose M hM using hloc
  let γ' := fun i => (hM i).some
  obtain ⟨N, hN, ⟨φ⟩⟩ := Space.CompletionAlgebraization.exists_completion_iso_of_cover
    W.obj.hom hT hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace hXnoeth he
    (M := fun i => (M i).obj) (fun i => (M i).property) (fun i => (Over.forget _).mapIso (γ' i))
    (fun i => Over.w (γ' i).hom) hcov W.property.1.1
  exact ⟨⟨N, hN⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    (φ ≪≫ Over.isoMk (Iso.refl _) (by simp))⟩⟩

/-- **Essential surjectivity of the functor of Stacks 0AR5, from algebraizations over affine
étale charts.** Let `X` be a locally Noetherian algebraic space, `T ⊆ |X|` closed and `W` an
object of the right-hand category of Stacks 0AR5. If for every étale morphism
`e : Spec R ⟶ X` with `R` Noetherian the base change `W ×_{X/T} (Spec R)_{/T}` is the completion
of a finite-type modification of `Spec R`, then `W` is in the essential image of
`AlgebraicGeometry.FormalSpace.completionModificationFunctor`.

The charts are the affine opens of the scheme of an étale atlas of `X`; they form an fppf
covering of `X` (an étale atlas followed by a Zariski covering), each is étale over `X`, and its
ring is Noetherian because `X` is locally Noetherian. This is the reduction of Stacks 0ARB to
the affine case Stacks 0ARA, whose input is `rigEtaleOverCompletionBaseChange`. -/
theorem mem_essImage_completionModificationFunctor_of_affine_charts
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (hXsp : IsAlgebraicSpace B S hS X)
    (hX : Space.IsLocallyNoetherian B S hS X) (W : RigEtaleOverCompletion B S hS X T)
    (hloc : ∀ (R : Type u) [CommRing R], IsNoetherianRing R →
      ∀ (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
        (e : yoneda.obj (affineOver B S hS hR s) ⟶ X), Space.IsEtale B S hS e →
      ∃ M : Space.FiniteTypeModification B S hS
          (Space.openSubspaceOfPoints B S hS (yoneda.obj (affineOver B S hS hR s))
            (Space.pointsMap B S hS _ e ⁻¹' T)ᶜ),
        Nonempty ((Space.completionOverFunctor B S hS
            (Space.pointsMap B S hS _ e ⁻¹' T)).obj M.obj ≅
          Over.mk (pullback.snd W.obj.hom (Space.completionSheafMap B S hS e T)))) :
    (completionModificationFunctor T hT hXsp hX).essImage W := by
  classical
  obtain ⟨U₀, p, hps, hpe⟩ := hXsp.exists_atlas
  let Y := (BigFppfOver.toScheme B S hS).obj U₀
  let K := Y.affineOpens
  let A : K → Type u := fun V ↦ Γ(Y, V.1)
  have hopen : ∀ V : K, IsOpenImmersion (V.2.fromSpec : Spec (.of (A V)) ⟶ Y) := fun V ↦
    IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hA : ∀ V : K, B.Contains (Spec (.of (A V))) := fun V ↦
    Scheme.size_lt_of_isOpenImmersion (V.2.fromSpec : Spec (.of (A V)) ⟶ Y) U₀.left.property
  let str : ∀ V : K, Spec (.of (A V)) ⟶ S := fun V ↦ V.2.fromSpec ≫ B.inclusion.map U₀.hom
  let ι : ∀ V : K, affineOver B S hS (hA V) (str V) ⟶ U₀ := fun V ↦
    Over.homMk (ObjectProperty.homMk V.2.fromSpec) rfl
  have hιet : ∀ V, Space.IsEtale B S hS (yoneda.map (ι V)) := fun V ↦
    (Space.isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((Space.presheaf_yoneda_map_etale_iff B S hS (ι V)).2 (by
        have := hopen V
        exact (inferInstance : Etale (V.2.fromSpec : Spec (.of (A V)) ⟶ Y))))
  have hcovx : ∀ x : (BigFppfOver.toScheme B S hS).obj U₀,
      ∃ V : K, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι V)) := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤)
      trivial
    exact ⟨⟨V, hV⟩, hV.range_fromSpec.ge hxV⟩
  have hcov₁ : Space.IsFppfCovering B S hS (fun _ : PUnit.{u + 1} => yoneda.obj U₀)
      (fun _ => p) :=
    Space.isFppfCovering_of_isEtaleCovering B S hS
      (Space.isEtaleCovering_atlas B S hS hXsp hps hpe)
  have hcov₂ : Space.IsFppfCovering B S hS
      (fun V : K => yoneda.obj (affineOver B S hS (hA V) (str V))) (fun V => yoneda.map (ι V)) :=
    Space.isFppfCovering_yoneda_of_openCover B S hS _ ι (fun V => hopen V) hcovx
  have hcov := Space.isFppfCovering_comp B S hS PUnit.{u + 1} (fun _ => K) _ _ _ _ hcov₁
    (fun _ => hcov₂)
  have het : ∀ q : Σ _ : PUnit.{u + 1}, K, Space.IsEtale B S hS (yoneda.map (ι q.2) ≫ p) :=
    fun q => Space.isEtale_comp B S hS (hιet q.2)
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS p).2 hpe)
  have hlft := fun q => Space.isLocallyOfFiniteType_of_isEtale' B S hS _ (het q)
  refine mem_essImage_completionModificationFunctor_of_cover T hT hXsp hX W hcov
    (fun q => ?_) hlft (fun q => ?_)
  · exact hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType
      (isAlgebraicSpace_yoneda B S hS _) hXsp _ (hlft q)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hXsp hX)
  · have : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of (A q.2))) :=
      hX (affineOver B S hS (hA q.2) (str q.2)) _ (het q)
    exact hloc (A q.2) (isNoetherian_Spec.mp ⟨⟩) (hA q.2) (str q.2) _ (het q)

end AlgebraicGeometry.FormalSpace

end

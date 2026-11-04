module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraicSpaceCoproductFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupSecondCentreChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFinitePresentationOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteEtaleCoverStratificationDefs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor
public import StacksFrontier.Topology.Irreducible.ClosedSetInduction

/-!
# Building stratifications by closed subspaces with finite étale covers

This file develops the closed-subspace calculus behind Stacks 0GUP. A *cover* of a closed
subspace `Z ⊆ X` over a set `D` of points of `X` is a finite morphism of finite presentation
`f : Y ⟶ Z` from a scheme which is étale at every point of `Y` lying over `D`. A subfunctor `W`
of `X` is *cover-stratified* when it is thickened by the first member of a chain of closed
subspaces of finite presentation as in Stacks 0GUP, with a surjective cover of each member over
its difference with the next.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleCoverOver`: a finite, finitely presented morphism from a scheme
  to a closed subspace, étale over a set of points.
* `AlgebraicGeometry.Space.IsCoverStratified`: the chain of Stacks 0GUP for a subfunctor, with
  the covers in pointwise form.

## Main results

* `AlgebraicGeometry.Space.isFiniteEtaleCoverStep_of_isEtaleCoverOver`: a surjective cover over
  the difference of two consecutive members is a step of the chain of Stacks 0GUP.
* `AlgebraicGeometry.Space.IsEtaleCoverOver.comp_homOfLe`: a cover of `Z₁` is a cover of a larger
  closed subspace `Z₂` over the points of an open subspace on which `Z₁` and `Z₂` agree.

## References

* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A cover of a subfunctor `Z` of `X` over a set `D` of points of `X`**: a finite morphism of
finite presentation `f : Y ⟶ Z` from a scheme which is étale at every point lying over `D`. -/
def IsEtaleCoverOver (Z : Subfunctor X) {Y : BigFppfOver B S hS}
    (f : yoneda.obj Y ⟶ Z.toFunctor) (D : Set (points B S hS X)) : Prop :=
  IsFinite B S hS f ∧ IsFinitePresentation B S hS f ∧
    ∀ y, pointsMap B S hS _ (f ≫ Z.ι) y ∈ D → IsEtaleAt B S hS f y

/-- **A cover-stratified subfunctor**: a chain of closed subspaces of finite presentation
`Z₀ ⊇ Z₁ ⊇ ⋯` with `Z₀ ⊆ W` having the points of `W`, `Z_t` without points, and for `i < t` a
cover of `Z_i` over `|Z_i| ∖ |Z_{i+1}|` which is surjective onto `|Z_i|`. -/
def IsCoverStratified (W : Subfunctor X) : Prop :=
  ∃ (t : ℕ) (Z : ℕ → Subfunctor X),
    (∀ i, IsClosedSubspace B S hS (Z i)) ∧ (∀ i, IsFinitePresentation B S hS (Z i).ι) ∧
    (∀ i, Z (i + 1) ≤ Z i) ∧ Z 0 ≤ W ∧
    subspacePointSet B S hS X (Z 0) = subspacePointSet B S hS X W ∧
    subspacePointSet B S hS X (Z t) = ∅ ∧
    ∀ i < t, ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ (Z i).toFunctor),
      IsEtaleCoverOver B S hS (Z i) f
        (subspacePointSet B S hS X (Z i) \ subspacePointSet B S hS X (Z (i + 1))) ∧
      subspacePointSet B S hS X (Z i) ⊆ Set.range (pointsMap B S hS _ (f ≫ (Z i).ι))

variable {B S hS}

/-- A cover over `D` is a cover over any smaller set of points. -/
theorem IsEtaleCoverOver.mono {Z : Subfunctor X} {Y : BigFppfOver B S hS}
    {f : yoneda.obj Y ⟶ Z.toFunctor} {D D' : Set (points B S hS X)}
    (hf : IsEtaleCoverOver B S hS Z f D) (h : D' ⊆ D) : IsEtaleCoverOver B S hS Z f D' :=
  ⟨hf.1, hf.2.1, fun y hy => hf.2.2 y (h hy)⟩

/-- If `f` hits every point of a closed subspace `Z`, then `f` is surjective on points. -/
private theorem surjective_pointsMap_of_subset_range {Z : Subfunctor X} {Y : BigFppfOver B S hS}
    {f : yoneda.obj Y ⟶ Z.toFunctor}
    (hsurj : subspacePointSet B S hS X Z ⊆ Set.range (pointsMap B S hS _ (f ≫ Z.ι))) :
    Function.Surjective (pointsMap B S hS _ f) := fun w => by
  obtain ⟨y, hy⟩ := hsurj ⟨w, rfl⟩
  exact ⟨y, pointsMap_injective_of_mono B S hS _ (by rw [← pointsMap_comp_apply, hy])⟩

/-- **A surjective cover over the difference of two consecutive members is a step of the chain of
Stacks 0GUP.** The open subspace of `Z` is the preimage of the open complement of `Z'`. -/
theorem isFiniteEtaleCoverStep_of_isEtaleCoverOver (hX : IsAlgebraicSpace B S hS X)
    {Z Z' : Subfunctor X} (hZ : IsClosedSubspace B S hS Z) (hZ' : IsClosedSubspace B S hS Z')
    {Y : BigFppfOver B S hS} {f : yoneda.obj Y ⟶ Z.toFunctor}
    (hf : IsEtaleCoverOver B S hS Z f
      (subspacePointSet B S hS X Z \ subspacePointSet B S hS X Z'))
    (hsurj : subspacePointSet B S hS X Z ⊆ Set.range (pointsMap B S hS _ (f ≫ Z.ι))) :
    IsFiniteEtaleCoverStep B S hS Z Z' := by
  let U : Subfunctor Z.toFunctor := (openComplement B S hS Z').preimage Z.ι
  have hU : IsOpenSubspace B S hS U :=
    isOpenSubspace_preimage B S hS Z.ι _ hX hZ.1 (isOpenSubspace_openComplement B S hS hX Z' hZ')
  have hUpts : Set.range (pointsMap B S hS U.toFunctor (U.ι ≫ Z.ι)) =
      subspacePointSet B S hS X Z \ subspacePointSet B S hS X Z' := by
    rw [pointsMap_comp, Set.range_comp, range_pointsMap_preimage_ι,
      range_pointsMap_ι_openComplement, Set.image_preimage_eq_range_inter]
    rfl
  refine ⟨Y, f, U, ?_, hf.1, hf.2.1, hU, hUpts, ?_, ?_⟩
  · exact surjective_pointsMap_of_subset_range hsurj
  · exact isFinite_of_isPullback B S hS (IsPullback.of_hasPullback U.ι f).flip hf.1
  · refine isEtale_pullback_fst_of_forall_isEtaleAt B S hS hZ.1
      (isAlgebraicSpace_yoneda B S hS Y) U hU f fun y hy => hf.2.2 y ?_
    rw [← hUpts, pointsMap_comp_apply]
    obtain ⟨u, hu⟩ := hy
    exact ⟨u, by rw [pointsMap_comp_apply, hu]⟩

/-- **A closed immersion which agrees with its target over an open subspace is étale over it.**
If `Z₁ ⊆ Z₂` are subfunctors of `X` with `Z₁ ∩ O = Z₂ ∩ O` for an open subspace `O`, then the
inclusion `Z₁ ⟶ Z₂` is étale at every point of `Z₁` lying in `O`. -/
theorem isEtaleAt_homOfLe_of_inf_eq (hX : IsAlgebraicSpace B S hS X) {Z₁ Z₂ O : Subfunctor X}
    (hZ₁ : IsAlgebraicSpace B S hS Z₁.toFunctor) (hZ₂ : IsAlgebraicSpace B S hS Z₂.toFunctor)
    (hle : Z₁ ≤ Z₂) (hO : IsOpenSubspace B S hS O) (heq : Z₁ ⊓ O = Z₂ ⊓ O)
    (z : points B S hS Z₁.toFunctor)
    (hz : pointsMap B S hS _ Z₁.ι z ∈ subspacePointSet B S hS X O) :
    IsEtaleAt B S hS (Subfunctor.homOfLe hle) z := by
  let O₂ : Subfunctor Z₂.toFunctor := O.preimage Z₂.ι
  have hO₂ : IsOpenSubspace B S hS O₂ := isOpenSubspace_preimage B S hS Z₂.ι O hX hZ₂ hO
  let O₁ : Subfunctor Z₁.toFunctor := O₂.preimage (Subfunctor.homOfLe hle)
  have hO₁ : IsOpenSubspace B S hS O₁ :=
    isOpenSubspace_preimage B S hS (Subfunctor.homOfLe hle) O₂ hZ₂ hZ₁ hO₂
  have hk : IsIso (O₂.fromPreimage (Subfunctor.homOfLe hle)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    refine fun T => (isIso_iff_bijective _).2 ⟨fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun c => c.1.1) hab)), fun b => ?_⟩
    have hx : b.1.1 ∈ (Z₁ ⊓ O).obj T := by
      rw [heq]
      exact ⟨b.1.2, b.2⟩
    exact ⟨⟨⟨b.1.1, hx.1⟩, b.2⟩, rfl⟩
  obtain ⟨z', hz''⟩ : z ∈ Set.range (pointsMap B S hS O₁.toFunctor O₁.ι) := by
    rwa [range_pointsMap_preimage_ι, Set.mem_preimage, range_pointsMap_preimage_ι,
      Set.mem_preimage, ← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
  refine ⟨O₁, hO₁, z', hz'', ?_⟩
  rw [← Subfunctor.fromPreimage_ι]
  exact isEtale_comp B S hS (isEtale_of_iso B S hS
    (asIso (O₂.fromPreimage (Subfunctor.homOfLe hle)))) (isEtale_ι_of_isOpenSubspace hO₂)

/-- A morphism whose points all miss `D` is a cover over `D` as soon as it is finite and of finite
presentation. -/
theorem IsEtaleCoverOver.of_disjoint {Z : Subfunctor X} {Y : BigFppfOver B S hS}
    {f : yoneda.obj Y ⟶ Z.toFunctor} {D : Set (points B S hS X)} (hfin : IsFinite B S hS f)
    (hfp : IsFinitePresentation B S hS f)
    (hD : Disjoint (Set.range (pointsMap B S hS _ (f ≫ Z.ι))) D) :
    IsEtaleCoverOver B S hS Z f D :=
  ⟨hfin, hfp, fun y hy => absurd hy (Set.disjoint_left.1 hD ⟨y, rfl⟩)⟩

/-- The inclusion of closed subspaces of finite presentation is finite and of finite
presentation. -/
theorem isFinite_and_isFinitePresentation_homOfLe (hX : IsAlgebraicSpace B S hS X)
    {Z₁ Z₂ : Subfunctor X} (hZ₁ : IsClosedSubspace B S hS Z₁)
    (hZ₁fp : IsFinitePresentation B S hS Z₁.ι) (hZ₂ : IsClosedSubspace B S hS Z₂)
    (hZ₂fp : IsFinitePresentation B S hS Z₂.ι) (hle : Z₁ ≤ Z₂) :
    IsFinite B S hS (Subfunctor.homOfLe hle) ∧
      IsFinitePresentation B S hS (Subfunctor.homOfLe hle) := by
  have hci : IsClosedImmersion B S hS (Subfunctor.homOfLe hle) :=
    isClosedImmersion_homOfLe' B S hS hZ₁.2 hle
  refine ⟨isFinite_of_isClosedImmersion B S hS _ hci, ?_⟩
  refine (isFinitePresentation_comp_iff_of_isClosedImmersion B S hS hZ₁.1 hZ₂.1 hX _ Z₂.ι hci
    hZ₂fp).1 ?_
  rw [Subfunctor.homOfLe_ι]
  exact hZ₁fp

/-- Composing a finite morphism of finite presentation into `Z₁` with the inclusion of closed
subspaces of finite presentation `Z₁ ≤ Z₂` gives a finite morphism of finite presentation. -/
private theorem isFinite_and_isFinitePresentation_comp_homOfLe
    (hX : IsAlgebraicSpace B S hS X) {Z₁ Z₂ : Subfunctor X} (hZ₁ : IsClosedSubspace B S hS Z₁)
    (hZ₁fp : IsFinitePresentation B S hS Z₁.ι) (hZ₂ : IsClosedSubspace B S hS Z₂)
    (hZ₂fp : IsFinitePresentation B S hS Z₂.ι) (hle : Z₁ ≤ Z₂) {Y : BigFppfOver B S hS}
    {f : yoneda.obj Y ⟶ Z₁.toFunctor} (hfin : IsFinite B S hS f)
    (hfp : IsFinitePresentation B S hS f) :
    IsFinite B S hS (f ≫ Subfunctor.homOfLe hle) ∧
      IsFinitePresentation B S hS (f ≫ Subfunctor.homOfLe hle) := by
  obtain ⟨hgfin, hgfp⟩ := isFinite_and_isFinitePresentation_homOfLe hX hZ₁ hZ₁fp hZ₂ hZ₂fp hle
  exact ⟨isFinite_comp B S hS hfin hgfin,
    isFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS Y) hZ₁.1 hZ₂.1 _ _ hfp hgfp⟩

/-- **A cover of `Z₁` is a cover of a larger closed subspace `Z₂`** over the points of an open
subspace `O` on which the two agree. -/
theorem IsEtaleCoverOver.comp_homOfLe (hX : IsAlgebraicSpace B S hS X) {Z₁ Z₂ O : Subfunctor X}
    (hZ₁ : IsClosedSubspace B S hS Z₁) (hZ₁fp : IsFinitePresentation B S hS Z₁.ι)
    (hZ₂ : IsClosedSubspace B S hS Z₂) (hZ₂fp : IsFinitePresentation B S hS Z₂.ι)
    (hle : Z₁ ≤ Z₂) (hO : IsOpenSubspace B S hS O) (heq : Z₁ ⊓ O = Z₂ ⊓ O)
    {D : Set (points B S hS X)} (hD : D ⊆ subspacePointSet B S hS X O)
    {Y : BigFppfOver B S hS} {f : yoneda.obj Y ⟶ Z₁.toFunctor}
    (hf : IsEtaleCoverOver B S hS Z₁ f D) :
    IsEtaleCoverOver B S hS Z₂ (f ≫ Subfunctor.homOfLe hle) D := by
  obtain ⟨hfin, hfp⟩ :=
    isFinite_and_isFinitePresentation_comp_homOfLe hX hZ₁ hZ₁fp hZ₂ hZ₂fp hle hf.1 hf.2.1
  refine ⟨hfin, hfp, fun y hy => ?_⟩
  rw [Category.assoc, Subfunctor.homOfLe_ι] at hy
  refine IsEtaleAt.comp B S hS (isAlgebraicSpace_yoneda B S hS Y) hZ₁.1 (hf.2.2 y hy) ?_
  refine isEtaleAt_homOfLe_of_inf_eq hX hZ₁.1 hZ₂.1 hle hO heq _ ?_
  rw [← pointsMap_comp_apply]
  exact hD hy

/-- The points of a composite with an inclusion of subfunctors, read in the ambient space. -/
theorem range_pointsMap_comp_homOfLe_ι {Z₁ Z₂ : Subfunctor X} (hle : Z₁ ≤ Z₂)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ Z₁.toFunctor) :
    Set.range (pointsMap B S hS _ ((f ≫ Subfunctor.homOfLe hle) ≫ Z₂.ι)) =
      Set.range (pointsMap B S hS _ (f ≫ Z₁.ι)) := by
  rw [Category.assoc, Subfunctor.homOfLe_ι]

/-- **Étaleness at a point is stable under base change.** In a cartesian square of algebraic
spaces, the base change `b` of `f` is étale at every point whose image under `a` is a point at
which `f` is étale. -/
theorem IsEtaleAt.of_isPullback {P V Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : P ⟶ V} {b : P ⟶ Y} {f : V ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback a b f g)
    (hP : IsAlgebraicSpace B S hS P) (hV : IsAlgebraicSpace B S hS V)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    {p : points B S hS P} (hf : IsEtaleAt B S hS f (pointsMap B S hS _ a p)) :
    IsEtaleAt B S hS b p := by
  obtain ⟨U, hU, x', hx', he⟩ := hf
  have hU' : IsOpenSubspace B S hS (U.preimage a) := isOpenSubspace_preimage B S hS a U hV hP hU
  have hp : p ∈ Set.range (pointsMap B S hS _ (U.preimage a).ι) := by
    rw [range_pointsMap_preimage_ι]
    exact ⟨x', hx'⟩
  obtain ⟨p', hp'⟩ := hp
  refine ⟨U.preimage a, hU', p', hp', ?_⟩
  have hsq : IsPullback (U.fromPreimage a) ((U.preimage a).ι ≫ b) (U.ι ≫ f) g :=
    (Subfunctor.isPullback_preimage a U).paste_vert sq
  exact isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsq.flip hU'.1 hY hU.1 hZ he

/-- **The base change of a cover to the intersection with a closed subspace.** If `f` is a cover
of `Z` over `D`, its base change along `Z ∩ W ⟶ Z` is a cover of `Z ∩ W` over `D`, and it is
surjective onto the points of `Z ∩ W` when `f` is surjective onto the points of `Z`. -/
theorem IsEtaleCoverOver.exists_inf (hX : IsAlgebraicSpace B S hS X) {Z W : Subfunctor X}
    (hZ : IsClosedSubspace B S hS Z) (hW : IsClosedSubspace B S hS W)
    {Y : BigFppfOver B S hS} {f : yoneda.obj Y ⟶ Z.toFunctor} {D : Set (points B S hS X)}
    (hf : IsEtaleCoverOver B S hS Z f D)
    (hsurj : subspacePointSet B S hS X Z ⊆ Set.range (pointsMap B S hS _ (f ≫ Z.ι))) :
    ∃ (Y' : BigFppfOver B S hS) (f' : yoneda.obj Y' ⟶ (Z ⊓ W).toFunctor),
      IsEtaleCoverOver B S hS (Z ⊓ W) f' D ∧
      subspacePointSet B S hS X (Z ⊓ W) ⊆ Set.range (pointsMap B S hS _ (f' ≫ (Z ⊓ W).ι)) := by
  have hZW : IsClosedSubspace B S hS (Z ⊓ W) := inf_isClosedSubspace B S hS X hX ⟨Z, hZ⟩ ⟨W, hW⟩
  let g : (Z ⊓ W).toFunctor ⟶ Z.toFunctor := Subfunctor.homOfLe inf_le_left
  have hg : IsClosedImmersion B S hS g := isClosedImmersion_homOfLe' B S hS hZW.2 inf_le_left
  let Y' := hg.rep.pullback f
  let f' : yoneda.obj Y' ⟶ (Z ⊓ W).toFunctor := hg.rep.fst f
  let s : yoneda.obj Y' ⟶ yoneda.obj Y := yoneda.map (hg.rep.snd f)
  have sq : IsPullback f' s g f := hg.rep.isPullback f
  have hY := isAlgebraicSpace_yoneda B S hS Y
  have hY' := isAlgebraicSpace_yoneda B S hS Y'
  have hcomp : f' ≫ (Z ⊓ W).ι = s ≫ f ≫ Z.ι := by
    rw [← Subfunctor.homOfLe_ι (inf_le_left : Z ⊓ W ≤ Z), ← Category.assoc, sq.w,
      Category.assoc]
  refine ⟨Y', f', ⟨isFinite_of_isPullback B S hS sq.flip hf.1,
    IsFinitePresentation.of_isPullback B S hS hY' hY hZW.1 hZ.1 sq.flip hf.2.1,
    fun y hy => ?_⟩, ?_⟩
  · rw [hcomp, pointsMap_comp_apply] at hy
    exact IsEtaleAt.of_isPullback sq.flip hY' hY hZW.1 hZ.1 (hf.2.2 _ hy)
  · rintro _ ⟨z, rfl⟩
    obtain ⟨y', hy'⟩ := surjective_pointsMap_of_isPullback B S hS sq.flip
      (surjective_pointsMap_of_subset_range hsurj) z
    exact ⟨y', by rw [pointsMap_comp_apply, hy']⟩

/-- **Two covers over the same set of points glue to one** on the coproduct of their sources, with
point range the union of theirs. -/
theorem IsEtaleCoverOver.exists_coprod {Z : Subfunctor X}
    (hZ : IsAlgebraicSpace B S hS Z.toFunctor) {Y₁ Y₂ : BigFppfOver B S hS}
    {f₁ : yoneda.obj Y₁ ⟶ Z.toFunctor} {f₂ : yoneda.obj Y₂ ⟶ Z.toFunctor}
    {D : Set (points B S hS X)} (h₁ : IsEtaleCoverOver B S hS Z f₁ D)
    (h₂ : IsEtaleCoverOver B S hS Z f₂ D) :
    ∃ (Y : BigFppfOver B S hS) (c : yoneda.obj Y ⟶ Z.toFunctor),
      IsEtaleCoverOver B S hS Z c D ∧
      Set.range (pointsMap B S hS _ (c ≫ Z.ι)) =
        Set.range (pointsMap B S hS _ (f₁ ≫ Z.ι)) ∪ Set.range (pointsMap B S hS _ (f₂ ≫ Z.ι)) := by
  obtain ⟨c, hc₁, hc₂, hint, hrange, het, -⟩ :=
    exists_coprod_glue B S hS (X := X) (U := X) hZ Y₁ Y₂ f₁ f₂
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have hYc : IsColimit (Cofan.mk (J.yoneda.obj (Y₁ ⨿ Y₂))
      fun b => J.yoneda.map (coprodPairIncl B S hS Y₁ Y₂ b)) :=
    BigFppfOver.isColimit_yoneda_cofan B S hS (coprodPairObj B S hS Y₁ Y₂)
      (coprodPairIncl B S hS Y₁ Y₂) (isColimit_cofan_coprodPair B S hS Y₁ Y₂)
  have hY₁ := isAlgebraicSpace_yoneda B S hS Y₁
  have hY₂ := isAlgebraicSpace_yoneda B S hS Y₂
  have hfp : IsFinitePresentation B S hS c := by
    refine isFinitePresentation_of_isColimit_cofan_of_cofinitely_isEmpty B S hS
      (fun b => J.yoneda.map (coprodPairIncl B S hS Y₁ Y₂ b)) hYc
      (fun b => isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hZ c
      ?_ ?_ fun T _ g => ⟨Set.univ, Set.finite_univ, fun i hi => absurd (Set.mem_univ i) hi⟩
    · rintro ⟨_ | _⟩
      · exact hc₁ ▸ h₁.2.1
      · exact hc₂ ▸ h₂.2.1
    · rintro ⟨_ | _⟩
      · exact hc₁ ▸ isSeparated_of_isFinite B S hS f₁ hY₁ hZ h₁.1
      · exact hc₂ ▸ isSeparated_of_isFinite B S hS f₂ hY₂ hZ h₂.1
  refine ⟨Y₁ ⨿ Y₂, c, ⟨?_, hfp, fun y hy => ?_⟩, ?_⟩
  · exact isFinite_of_isIntegralHom_of_isLocallyOfFiniteType B S hS c
      (isAlgebraicSpace_yoneda B S hS _) hZ (hint h₁.1.isIntegralHom h₂.1.isIntegralHom)
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp.1)
  · refine het (pointsMap B S hS _ Z.ι ⁻¹' D) (fun z hz => h₁.2.2 z ?_)
      (fun z hz => h₂.2.2 z ?_) y ?_
    · rwa [pointsMap_comp_apply]
    · rwa [pointsMap_comp_apply]
    · rwa [pointsMap_comp_apply] at hy
  · rw [pointsMap_comp, Set.range_comp, hrange, Set.image_union, ← Set.range_comp,
      ← Set.range_comp, ← pointsMap_comp, ← pointsMap_comp]

/-! ### Operations on cover-stratified subfunctors -/

/-- **Cover-stratified subfunctors are stable under intersection with a closed subspace of finite
presentation**: the chain and the covers are base changed. -/
theorem IsCoverStratified.inf (hX : IsAlgebraicSpace B S hS X) {W W₁ : Subfunctor X}
    (hW : IsCoverStratified B S hS W) (hW₁ : IsClosedSubspace B S hS W₁)
    (hW₁fp : IsFinitePresentation B S hS W₁.ι) :
    IsCoverStratified B S hS (W ⊓ W₁) := by
  obtain ⟨t, Z, hcl, hfp, hdec, h0, hpts, hemp, hstep⟩ := hW
  have hcl' : ∀ i, IsClosedSubspace B S hS (Z i ⊓ W₁) := fun i =>
    inf_isClosedSubspace B S hS X hX ⟨Z i, hcl i⟩ ⟨W₁, hW₁⟩
  refine ⟨t, fun i => Z i ⊓ W₁, hcl',
    fun i => isFinitePresentation_inf B S hS hX _ _ (hcl i) hW₁ (hcl' i) (hfp i) hW₁fp,
    fun i => inf_le_inf_right _ (hdec i), inf_le_inf_right _ h0, ?_, ?_, fun i hi => ?_⟩
  · rw [subspacePointSet_inf B S hS, subspacePointSet_inf B S hS, hpts]
  · rw [subspacePointSet_inf B S hS, hemp, Set.empty_inter]
  · obtain ⟨Y, f, hf, hs⟩ := hstep i hi
    obtain ⟨Y', f', hf', hs'⟩ := hf.exists_inf hX (hcl i) hW₁ hs
    refine ⟨Y', f', hf'.mono ?_, hs'⟩
    rintro x ⟨hx₁, hx₂⟩
    rw [subspacePointSet_inf B S hS] at hx₁ hx₂
    exact ⟨hx₁.1, fun h => hx₂ ⟨h, hx₁.2⟩⟩

/-- A cover-stratified subfunctor stays cover-stratified when enlarged without changing its
points. -/
theorem IsCoverStratified.of_le {W W' : Subfunctor X} (hW : IsCoverStratified B S hS W)
    (hle : W ≤ W') (hpts : subspacePointSet B S hS X W = subspacePointSet B S hS X W') :
    IsCoverStratified B S hS W' := by
  obtain ⟨t, Z, hcl, hfp, hdec, h0, hpts₀, hemp, hstep⟩ := hW
  exact ⟨t, Z, hcl, hfp, hdec, h0.trans hle, hpts₀.trans hpts, hemp, hstep⟩

/-- The members of a decreasing chain of subfunctors are contained in the first. -/
theorem le_zero_of_antitone_step {Z : ℕ → Subfunctor X} (hdec : ∀ i, Z (i + 1) ≤ Z i) :
    ∀ i, Z i ≤ Z 0
  | 0 => le_rfl
  | i + 1 => (hdec i).trans (le_zero_of_antitone_step hdec i)

/-- **A cover-stratified closed subspace of finite presentation with a point is the image of a
single finite morphism of finite presentation from a scheme**: glue the covers of the members of
the chain. -/
theorem IsCoverStratified.exists_cover (hX : IsAlgebraicSpace B S hS X) {W : Subfunctor X}
    (hW : IsCoverStratified B S hS W) (hWcl : IsClosedSubspace B S hS W)
    (hWfp : IsFinitePresentation B S hS W.ι)
    (hne : (subspacePointSet B S hS X W).Nonempty) :
    ∃ (Y : BigFppfOver B S hS) (g : yoneda.obj Y ⟶ W.toFunctor),
      IsFinite B S hS g ∧ IsFinitePresentation B S hS g ∧
        Set.range (pointsMap B S hS _ (g ≫ W.ι)) = subspacePointSet B S hS X W := by
  obtain ⟨t, Z, hcl, hfp, hdec, h0, hpts, hemp, hstep⟩ := hW
  have hle : ∀ i, Z i ≤ W := fun i => (le_zero_of_antitone_step hdec i).trans h0
  -- the cover of `Z i`, moved to `W`
  have hpiece : ∀ i < t, ∃ (Y : BigFppfOver B S hS) (g : yoneda.obj Y ⟶ W.toFunctor),
      IsEtaleCoverOver B S hS W g ∅ ∧
        subspacePointSet B S hS X (Z i) ⊆ Set.range (pointsMap B S hS _ (g ≫ W.ι)) := by
    intro i hi
    obtain ⟨Y, f, hf, hs⟩ := hstep i hi
    obtain ⟨hgfin, hgfp⟩ := isFinite_and_isFinitePresentation_comp_homOfLe hX (hcl i) (hfp i)
      hWcl hWfp (hle i) hf.1 hf.2.1
    refine ⟨Y, f ≫ Subfunctor.homOfLe (hle i),
      IsEtaleCoverOver.of_disjoint hgfin hgfp (Set.disjoint_empty _), ?_⟩
    rw [range_pointsMap_comp_homOfLe_ι]
    exact hs
  have ht : 0 < t := Nat.pos_of_ne_zero <| by
    rintro rfl
    rw [← hpts, hemp] at hne
    exact Set.not_nonempty_empty hne
  have hind : ∀ n, 1 ≤ n → n ≤ t → ∃ (Y : BigFppfOver B S hS) (g : yoneda.obj Y ⟶ W.toFunctor),
      IsEtaleCoverOver B S hS W g ∅ ∧
        subspacePointSet B S hS X (Z 0) \ subspacePointSet B S hS X (Z n) ⊆
          Set.range (pointsMap B S hS _ (g ≫ W.ι)) := by
    intro n hn hnt
    induction n, hn using Nat.le_induction with
    | base =>
      obtain ⟨Y, g, hg, hs⟩ := hpiece 0 ht
      exact ⟨Y, g, hg, Set.diff_subset.trans hs⟩
    | succ n hn ih =>
      obtain ⟨Y, g, hg, hs⟩ := ih (by omega)
      obtain ⟨Y', g', hg', hs'⟩ := hpiece n (by omega)
      obtain ⟨Y'', c, hc, hcr⟩ := hg.exists_coprod hWcl.1 hg'
      refine ⟨Y'', c, hc, ?_⟩
      rw [hcr]
      intro x hx
      by_cases hxn : x ∈ subspacePointSet B S hS X (Z n)
      · exact Or.inr (hs' hxn)
      · exact Or.inl (hs ⟨hx.1, hxn⟩)
  obtain ⟨Y, g, hg, hs⟩ := hind t ht le_rfl
  refine ⟨Y, g, hg.1, hg.2.1, le_antisymm ?_ ?_⟩
  · rw [pointsMap_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  · rw [← hpts]
    exact fun x hx => hs ⟨hx, by rw [hemp]; exact Set.notMem_empty x⟩

/-- **Extending a cover-stratification by one member.** If `W₁` is a closed subspace of finite
presentation, `W'` is cover-stratified, and `f` is a cover of `W₁` over the points of `W₁` not
in `W'` which is surjective onto them, then `W₁` is cover-stratified: the chain is `W₁` followed
by the chain of `W' ∩ W₁`. -/
theorem isCoverStratified_of_isEtaleCoverOver (hX : IsAlgebraicSpace B S hS X)
    {W₁ W' : Subfunctor X} (hW₁ : IsClosedSubspace B S hS W₁)
    (hW₁fp : IsFinitePresentation B S hS W₁.ι) (hW' : IsClosedSubspace B S hS W')
    (hW'fp : IsFinitePresentation B S hS W'.ι) (hstr : IsCoverStratified B S hS W')
    {Y : BigFppfOver B S hS} {f : yoneda.obj Y ⟶ W₁.toFunctor}
    (hf : IsEtaleCoverOver B S hS W₁ f
      (subspacePointSet B S hS X W₁ \ subspacePointSet B S hS X W'))
    (hsurj : subspacePointSet B S hS X W₁ \ subspacePointSet B S hS X W' ⊆
      Set.range (pointsMap B S hS _ (f ≫ W₁.ι))) :
    IsCoverStratified B S hS W₁ := by
  have hstr' := hstr.inf hX hW₁ hW₁fp
  have hIcl : IsClosedSubspace B S hS (W' ⊓ W₁) :=
    inf_isClosedSubspace B S hS X hX ⟨W', hW'⟩ ⟨W₁, hW₁⟩
  have hIfp : IsFinitePresentation B S hS (W' ⊓ W₁).ι :=
    isFinitePresentation_inf B S hS hX _ _ hW' hW₁ hIcl hW'fp hW₁fp
  -- a cover of `W₁` over the points not in `W'`, surjective onto all of `W₁`
  have hcover : ∃ (Y' : BigFppfOver B S hS) (c : yoneda.obj Y' ⟶ W₁.toFunctor),
      IsEtaleCoverOver B S hS W₁ c
        (subspacePointSet B S hS X W₁ \ subspacePointSet B S hS X W') ∧
      subspacePointSet B S hS X W₁ ⊆ Set.range (pointsMap B S hS _ (c ≫ W₁.ι)) := by
    by_cases hne : (subspacePointSet B S hS X (W' ⊓ W₁)).Nonempty
    · obtain ⟨Y'', g, hgfin, hgfp, hgr⟩ := hstr'.exists_cover hX hIcl hIfp hne
      obtain ⟨hcfin, hcfp⟩ := isFinite_and_isFinitePresentation_comp_homOfLe hX hIcl hIfp hW₁
        hW₁fp (inf_le_right : W' ⊓ W₁ ≤ W₁) hgfin hgfp
      have hg' : IsEtaleCoverOver B S hS W₁ (g ≫ Subfunctor.homOfLe inf_le_right)
          (subspacePointSet B S hS X W₁ \ subspacePointSet B S hS X W') := by
        refine IsEtaleCoverOver.of_disjoint hcfin hcfp ?_
        rw [range_pointsMap_comp_homOfLe_ι, hgr, subspacePointSet_inf B S hS]
        exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.1
      obtain ⟨Y', c, hc, hcr⟩ := hf.exists_coprod hW₁.1 hg'
      refine ⟨Y', c, hc, fun x hx => ?_⟩
      rw [hcr, range_pointsMap_comp_homOfLe_ι, hgr, subspacePointSet_inf B S hS]
      by_cases hx' : x ∈ subspacePointSet B S hS X W'
      · exact Or.inr ⟨hx', hx⟩
      · exact Or.inl (hsurj ⟨hx, hx'⟩)
    · refine ⟨Y, f, hf, fun x hx => hsurj ⟨hx, fun hx' => hne ⟨x, ?_⟩⟩⟩
      rw [subspacePointSet_inf B S hS]
      exact ⟨hx', hx⟩
  obtain ⟨Y', c, hc, hcs⟩ := hcover
  obtain ⟨t, Z, hcl, hfp, hdec, h0, hpts, hemp, hstep⟩ := hstr'
  let Z' : ℕ → Subfunctor X := fun i => match i with
    | 0 => W₁
    | i + 1 => Z i
  refine ⟨t + 1, Z', fun i => ?_, fun i => ?_, fun i => ?_, le_rfl, rfl, hemp, fun i hi => ?_⟩
  · rcases i with _ | i
    · exact hW₁
    · exact hcl i
  · rcases i with _ | i
    · exact hW₁fp
    · exact hfp i
  · rcases i with _ | i
    · exact h0.trans inf_le_right
    · exact hdec i
  · rcases i with _ | i
    · refine ⟨Y', c, hc.mono ?_, hcs⟩
      rintro x ⟨hx₁, hx₂⟩
      refine ⟨hx₁, fun hx' => hx₂ ?_⟩
      show x ∈ subspacePointSet B S hS X (Z 0)
      rw [hpts, subspacePointSet_inf B S hS]
      exact ⟨hx', hx₁⟩
    · exact hstep i (by omega)

/-! ### Sums of closed subspaces -/

section Sum

variable (Xs : AlgebraicSpaces B S hS)

/-- A summand of a sum of closed subspaces is contained in the sum: its ideal contains the
product of the ideals. -/
theorem le_sumClosedSubspaces_left (D₁ D₂ : ClosedSubspaces B S hS Xs.1) :
    D₁.1 ≤ (sumClosedSubspaces B S hS Xs D₁ D₂).1 := by
  refine le_of_chartKer_le Xs _ _ (atlasHom_surjective B S hS Xs)
    (atlasHom_etale B S hS Xs) ?_
  rw [chartKer_sumClosedSubspaces]
  exact Scheme.IdealSheafData.le_def.2 fun U => by
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]; exact Ideal.mul_le_inf.trans inf_le_left

/-- The second summand of a sum of closed subspaces is contained in the sum. -/
theorem le_sumClosedSubspaces_right (D₁ D₂ : ClosedSubspaces B S hS Xs.1) :
    D₂.1 ≤ (sumClosedSubspaces B S hS Xs D₁ D₂).1 := by
  refine le_of_chartKer_le Xs _ _ (atlasHom_surjective B S hS Xs)
    (atlasHom_etale B S hS Xs) ?_
  rw [chartKer_sumClosedSubspaces]
  exact Scheme.IdealSheafData.le_def.2 fun U => by
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]; exact Ideal.mul_le_inf.trans inf_le_right

/-- Adding a closed subspace without points changes nothing: its ideal is the unit ideal. -/
theorem sumClosedSubspaces_eq_left_of_subspacePointSet_eq_empty
    (D E : ClosedSubspaces B S hS Xs.1) (hE : subspacePointSet B S hS Xs.1 E.1 = ∅) :
    sumClosedSubspaces B S hS Xs D E = D := by
  have h : chartKer B S hS Xs (sumClosedSubspaces B S hS Xs D E) (atlasHom B S hS Xs) =
      chartKer B S hS Xs D (atlasHom B S hS Xs) := by
    rw [chartKer_sumClosedSubspaces, chartKer_eq_top_of_subspacePointSet_eq_empty Xs E hE,
      Scheme.IdealSheafData.mul_top]
  refine Subtype.ext (le_antisymm ?_ (le_sumClosedSubspaces_left Xs D E))
  exact le_of_chartKer_le Xs _ _ (atlasHom_surjective B S hS Xs)
    (atlasHom_etale B S hS Xs) h.ge

/-- **Off the second summand, a sum of closed subspaces is the first summand**: over an open
subspace `O` missing the points of `D₂`, the sum `D₁ + D₂` and `D₁` agree. -/
theorem sumClosedSubspaces_inf_eq (D₁ D₂ : ClosedSubspaces B S hS Xs.1) {O : Subfunctor Xs.1}
    (hO : IsOpenSubspace B S hS O)
    (hdisj : Disjoint (subspacePointSet B S hS Xs.1 D₂.1) (subspacePointSet B S hS Xs.1 O)) :
    (sumClosedSubspaces B S hS Xs D₁ D₂).1 ⊓ O = D₁.1 ⊓ O := by
  let Os : AlgebraicSpaces B S hS := ⟨O.toFunctor, hO.1⟩
  let j : Os ⟶ Xs := ObjectProperty.homMk O.ι
  have hE : subspacePointSet B S hS Os.1 (D₂.1.preimage O.ι) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    change x ∈ Set.range (pointsMap B S hS _ (D₂.1.preimage O.ι).ι) at hx
    rw [range_pointsMap_preimage_ι] at hx
    exact Set.disjoint_left.1 hdisj hx ⟨x, rfl⟩
  have h₁ := preimage_sumClosedSubspaces B S hS j D₁ D₂
  have h₂ := sumClosedSubspaces_eq_left_of_subspacePointSet_eq_empty Os
    ⟨D₁.1.preimage O.ι, isClosedSubspace_preimage B S hS O.ι D₁.1 Xs.2 Os.2 D₁.2⟩
    ⟨D₂.1.preimage O.ι, isClosedSubspace_preimage B S hS O.ι D₂.1 Xs.2 Os.2 D₂.2⟩ hE
  have h₃ : (sumClosedSubspaces B S hS Xs D₁ D₂).1.preimage O.ι = D₁.1.preimage O.ι :=
    congrArg Subtype.val (h₁.trans h₂)
  ext T x
  constructor <;> rintro ⟨hx, hxO⟩ <;> refine ⟨?_, hxO⟩
  · exact (congrArg (fun P => (⟨x, hxO⟩ : O.toFunctor.obj T) ∈ P.obj T) h₃).mp hx
  · exact (congrArg (fun P => (⟨x, hxO⟩ : O.toFunctor.obj T) ∈ P.obj T) h₃).mpr hx

end Sum

/-- **The union of two cover-stratified closed subspaces of finite presentation is contained in a
third.** By descending induction along the chain `Z_i` of the first, the sums `Z_i + W₂` are
cover-stratified: off `W₂` the sum `Z_i + W₂` is `Z_i`, so the cover of `Z_i` serves. -/
theorem IsCoverStratified.exists_union (hX : IsAlgebraicSpace B S hS X) {W₁ W₂ : Subfunctor X}
    (hW₂ : IsClosedSubspace B S hS W₂) (hW₂fp : IsFinitePresentation B S hS W₂.ι)
    (h₁ : IsCoverStratified B S hS W₁) (h₂ : IsCoverStratified B S hS W₂) :
    ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
      IsCoverStratified B S hS W ∧
      subspacePointSet B S hS X W₁ ∪ subspacePointSet B S hS X W₂ ⊆
        subspacePointSet B S hS X W := by
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  obtain ⟨t, Z, hcl, hfp, hdec, h0, hpts, hemp, hstep⟩ := h₁
  let Sm : ℕ → ClosedSubspaces B S hS X := fun k =>
    sumClosedSubspaces B S hS Xs ⟨Z k, hcl k⟩ ⟨W₂, hW₂⟩
  have hSmpts : ∀ k, subspacePointSet B S hS X (Sm k).1 =
      subspacePointSet B S hS X (Z k) ∪ subspacePointSet B S hS X W₂ := fun k =>
    subspacePointSet_sumClosedSubspaces Xs _ _
  have hSmfp : ∀ k, IsFinitePresentation B S hS (Sm k).1.ι := fun k =>
    isFinitePresentation_ι_sumClosedSubspaces Xs _ _ (hfp k) hW₂fp
  let O : Subfunctor X := openComplement B S hS W₂
  have hO : IsOpenSubspace B S hS O := isOpenSubspace_openComplement B S hS hX W₂ hW₂
  have hOpts : subspacePointSet B S hS X O = (subspacePointSet B S hS X W₂)ᶜ :=
    range_pointsMap_ι_openComplement B S hS W₂
  have hdisj : Disjoint (subspacePointSet B S hS X W₂) (subspacePointSet B S hS X O) := by
    rw [hOpts]
    exact disjoint_compl_right
  have hclaim : ∀ n, n ≤ t → IsCoverStratified B S hS (Sm (t - n)).1 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine h₂.of_le (le_sumClosedSubspaces_right Xs ⟨Z (t - 0), hcl _⟩ ⟨W₂, hW₂⟩) ?_
      rw [Nat.sub_zero, hSmpts, hemp, Set.empty_union]
    | succ n ih =>
      intro hn
      have hk : t - (n + 1) + 1 = t - n := by omega
      have ih' := ih (by omega)
      rw [← hk] at ih'
      set k := t - (n + 1)
      obtain ⟨Y, f, hf, hs⟩ := hstep k (by omega)
      have hD : subspacePointSet B S hS X (Sm k).1 \ subspacePointSet B S hS X (Sm (k + 1)).1 ⊆
          subspacePointSet B S hS X (Z k) \ subspacePointSet B S hS X (Z (k + 1)) := by
        rintro x ⟨hx₁, hx₂⟩
        rw [hSmpts] at hx₁ hx₂
        rcases hx₁ with hx₁ | hx₁
        · exact ⟨hx₁, fun h => hx₂ (Or.inl h)⟩
        · exact absurd (Or.inr hx₁) hx₂
      have hDO : subspacePointSet B S hS X (Sm k).1 \ subspacePointSet B S hS X (Sm (k + 1)).1 ⊆
          subspacePointSet B S hS X O := by
        rintro x ⟨-, hx₂⟩
        rw [hOpts]
        intro hx
        rw [hSmpts] at hx₂
        exact hx₂ (Or.inr hx)
      have heq : Z k ⊓ O = (Sm k).1 ⊓ O :=
        (sumClosedSubspaces_inf_eq Xs ⟨Z k, hcl k⟩ ⟨W₂, hW₂⟩ hO hdisj).symm
      have hf' := (hf.mono hD).comp_homOfLe hX (hcl k) (hfp k) (Sm k).2 (hSmfp k)
        (le_sumClosedSubspaces_left Xs ⟨Z k, hcl k⟩ ⟨W₂, hW₂⟩) hO heq hDO
      refine isCoverStratified_of_isEtaleCoverOver hX (Sm k).2 (hSmfp k) (Sm (k + 1)).2
        (hSmfp (k + 1)) ih' hf' ?_
      rw [range_pointsMap_comp_homOfLe_ι]
      intro x hx
      exact hs (hD hx).1
  refine ⟨(Sm 0).1, (Sm 0).2, hSmfp 0, by simpa using hclaim t le_rfl, ?_⟩
  rw [hSmpts, hpts]

/-! ### The induction on irreducible closed sets of points -/

section Induction

attribute [local instance] pointTopology

/-- The empty closed subspace is cover-stratified, by the chain of length zero. -/
theorem isCoverStratified_emptyClosedSubspace (hX : IsAlgebraicSpace B S hS X) :
    IsCoverStratified B S hS (emptyClosedSubspace (⟨X, hX⟩ : AlgebraicSpaces B S hS)).1 :=
  ⟨0, fun _ => (emptyClosedSubspace (⟨X, hX⟩ : AlgebraicSpaces B S hS)).1,
    fun _ => (emptyClosedSubspace _).2, fun _ => isFinitePresentation_ι_emptyClosedSubspace _,
    fun _ => le_rfl, le_rfl, rfl, subspacePointSet_emptyClosedSubspace _,
    fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- The points off a closed subspace of finite presentation of a quasi-compact algebraic space
form a quasi-compact set. -/
theorem isCompact_compl_subspacePointSet (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) {W : Subfunctor X} (hW : IsClosedSubspace B S hS W)
    (hWfp : IsFinitePresentation B S hS W.ι) :
    IsCompact (subspacePointSet B S hS X W)ᶜ := by
  have hO := isOpenSubspace_openComplement B S hS hX W hW
  have hqc := isQuasiCompactSpace_openComplement_of_isFinitePresentation hX hXqc W hW hWfp
  have := (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hO.1).1 hqc
  rw [← range_pointsMap_ι_openComplement B S hS W]
  exact isCompact_range (continuous_pointsMap B S hS _)

/-- **The induction principle behind Stacks 0GUP.** On a quasi-compact algebraic space, if every
irreducible closed set of points all of whose proper closed subsets lie in cover-stratified closed
subspaces of finite presentation itself lies in one, then some cover-stratified closed subspace of
finite presentation has all the points of `X`. -/
theorem exists_isCoverStratified_univ_of_step (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hstep : ∀ C : Set (points B S hS X), IsClosed C → IsIrreducible C →
      (∀ C' : Set (points B S hS X), IsClosed C' → C' ⊂ C →
        ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
          IsCoverStratified B S hS W ∧ C' ⊆ subspacePointSet B S hS X W) →
      ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
        IsCoverStratified B S hS W ∧ C ⊆ subspacePointSet B S hS X W) :
    ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
      IsCoverStratified B S hS W ∧ subspacePointSet B S hS X W = Set.univ := by
  let G : Set (Set (points B S hS X)) := {s | ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧
    IsFinitePresentation B S hS W.ι ∧ IsCoverStratified B S hS W ∧
      s = subspacePointSet B S hS X W}
  have hG : ∀ C : Set (points B S hS X), (∃ s ∈ G, C ⊆ s) ↔
      ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
        IsCoverStratified B S hS W ∧ C ⊆ subspacePointSet B S hS X W := fun C =>
    ⟨fun ⟨_, ⟨W, h₁, h₂, h₃, rfl⟩, hC⟩ => ⟨W, h₁, h₂, h₃, hC⟩,
      fun ⟨W, h₁, h₂, h₃, hC⟩ => ⟨_, ⟨W, h₁, h₂, h₃, rfl⟩, hC⟩⟩
  obtain ⟨s, ⟨W, hW, hWfp, hWs, rfl⟩, huniv⟩ :=
    TopologicalSpace.exists_mem_univ_subset_of_isIrreducible_step G
      ⟨_, ⟨_, (emptyClosedSubspace (⟨X, hX⟩ : AlgebraicSpaces B S hS)).2,
        isFinitePresentation_ι_emptyClosedSubspace _, isCoverStratified_emptyClosedSubspace hX,
        rfl⟩⟩
      (fun _ ⟨W, hW, hWfp, _, hs⟩ => hs ▸ isCompact_compl_subspacePointSet hX hXqc hW hWfp)
      (fun _ ⟨W₁, _, _, h₁, hs₁⟩ _ ⟨W₂, hW₂, hW₂fp, h₂, hs₂⟩ => by
        obtain ⟨W, hW, hWfp, hWs, hsub⟩ := h₁.exists_union hX hW₂ hW₂fp h₂
        exact ⟨_, ⟨W, hW, hWfp, hWs, rfl⟩, hs₁ ▸ hs₂ ▸ hsub⟩)
      (fun C hC hirr hsmall => (hG C).2 (hstep C hC hirr fun C' hC' hlt =>
        (hG C').1 (hsmall C' hC' hlt)))
  exact ⟨W, hW, hWfp, hWs, Set.eq_univ_of_univ_subset huniv⟩

end Induction

end AlgebraicGeometry.Space

end

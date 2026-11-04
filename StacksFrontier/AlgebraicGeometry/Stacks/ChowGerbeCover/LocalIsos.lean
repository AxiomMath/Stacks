module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.SectionFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackMapProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationStabilizerFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# Zariski local isomorphisms between the local sections in the proof of Stacks 0CQ7

In the fourth paragraph of the proof of [Stacks, Tag 0CQ7] (situation (d) to (e)) the base carries
quasi-compact opens `W₁, …, Wₙ` with local sections `xᵢ : Wᵢ ⟶ 𝒳` of `f`, and a quasi-compact
open `V ⊆ W₁ ∩ … ∩ Wₙ` over which `f` is a gerbe. The morphisms
`T_ij = Isom_𝒳(xᵢ|_V, xⱼ|_V) ⟶ V` are surjective, flat and locally of finite presentation, so
[Stacks, Tag 0CQ6] gives finite surjective `Y'_ij ⟶ Y` over which `T_ij` has sections Zariski
locally; after replacing `Y` by a space finite over all of them, `xᵢ` and `xⱼ` are Zariski locally
isomorphic over `V`. Here the pairs are treated one at a time, each base change over the previous
one, and isomorphisms found at earlier steps are pulled back along the later ones.

## Main results

* `AlgebraicGeometry.Stack.exists_eq_algebraicSpaceStackMap`: a 1-morphism between the algebraic
  stacks of two algebraic spaces is the 1-morphism of a morphism of algebraic spaces.
* `AlgebraicGeometry.Stack.isSurjective_algebraicSpaceStackMap_of_isSurjective`: the 1-morphism of
  a surjective morphism of algebraic spaces is surjective.
* `AlgebraicGeometry.Stack.IsomFamily.tautological`: the universal family of isomorphisms over
  `Isom_𝒳(x₁, x₂)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_finite_cover_isomFamily_pair`: the step for one
  pair of points.
* `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily.exists_finite_cover_localIsos`: the step
  (d) to (e) for all pairs.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CQ6](https://stacks.math.columbia.edu/tag/0CQ6)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A point in the image of an open immersion `g` lies in the image of the inclusion of the
range subfunctor of `g`. -/
theorem mem_range_pointsMap_range_ι {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G)
    {y : points B S hS G} (hy : y ∈ Set.range (pointsMap B S hS F g)) :
    y ∈ Set.range (pointsMap B S hS (Subfunctor.range g).toFunctor (Subfunctor.range g).ι) := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨pointsMap B S hS F (Subfunctor.toRange g) z, by
    rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]⟩

/-- **A finite morphism to a quasi-compact and quasi-separated algebraic space has
quasi-compact and quasi-separated source.** -/
theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isFinite
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsFinite B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    IsQuasiCompactSpace B S hS X ∧ IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X :=
  ⟨isQuasiCompactSpace_of_isQuasiCompact B S hS hY hYqc f
      (isQuasiCompact_of_isIntegralHom f hX hY (IsFinite.isIntegralHom B S hS hf)),
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hX hYqs
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isIntegralHom B S hS f hX hY (IsFinite.isIntegralHom B S hS hf)))⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A 1-morphism between the algebraic stacks of two algebraic spaces is the 1-morphism of a
morphism of algebraic spaces** (Stacks 04SW): it is 2-isomorphic to the 1-morphism of the morphism
of representing presheaves it induces, and 2-isomorphic 1-morphisms into the stack of an
algebraic space are equal. -/
theorem exists_eq_algebraicSpaceStackMap {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G)
    (a : algebraicSpaceStack.{u, w} B S hS T hT ⟶ algebraicSpaceStack.{u, w} B S hS G hG) :
    ∃ g : T ⟶ G, a = algebraicSpaceStackMap.{u, w} B S hS hT hG g := by
  obtain ⟨e⟩ := nonempty_twoIso_associatedMap_representingMap B S hS T G a.hom
  exact ⟨_, Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS e.inv)⟩

/-- **The 1-morphism of algebraic stacks attached to a morphism of algebraic spaces determines
the morphism**: the morphism of representing presheaves it induces is the morphism. -/
theorem algebraicSpaceStackMap_injective {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hT : IsAlgebraicSpace B S hS T} {hG : IsAlgebraicSpace B S hS G} {g g' : T ⟶ G}
    (h : algebraicSpaceStackMap.{u, w} B S hS hT hG g =
      algebraicSpaceStackMap.{u, w} B S hS hT hG g') : g = g' := by
  have h' := congrArg (fun a : algebraicSpaceStack.{u, w} B S hS T hT ⟶
      algebraicSpaceStack.{u, w} B S hS G hG =>
    representingMap B S hS (fibredCategory B S hS T) (fibredCategory B S hS G) T G
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom) h
  exact (representingMap_associatedMap B S hS T G g).symm.trans
    (h'.trans (representingMap_associatedMap B S hS T G g'))

/-- Restricting a 1-morphism along `b` and then along `a` is restricting it along `a ≫ b`. -/
theorem algebraicSpaceStackMap_comp_comp_eq {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y}
    {hZ : IsAlgebraicSpace B S hS Z} {𝒳 : AlgebraicStacks.{u, w} B S hS} (a : X ⟶ Y) (b : Y ⟶ Z)
    {c : X ⟶ Z} (h : a ≫ b = c) (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    algebraicSpaceStackMap.{u, w} B S hS hX hY a ≫ algebraicSpaceStackMap.{u, w} B S hS hY hZ b ≫
      x = algebraicSpaceStackMap.{u, w} B S hS hX hZ c ≫ x := by
  rw [← Category.assoc, ← AlgebraicStacks.algebraicSpaceStackMap_comp, h]

/-- **The 1-morphism of a surjective morphism of algebraic spaces is surjective**, by
Stacks 04XI: it is representable by algebraic spaces, and its relative surjectivity is the
surjectivity of the morphism. -/
theorem isSurjective_algebraicSpaceStackMap_of_isSurjective
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G)
    (hg : Space.IsSurjective B S hS g) :
    IsSurjective B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g) :=
  (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS _
    (isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap.{u, w} B S hS hT hG g)).2
    ((hasRelativeProperty_algebraicSpaceStackMap_iff.{u, w} B S hS hT hG g
      (Space.surjectiveMorphismProperty B S hS)).2 hg)

namespace IsomFamily

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hZ : IsAlgebraicSpace B S hS Z}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The tautological family of isomorphisms over `Isom_𝒳(x₁, x₂)`**: at a section of
`Isom_𝒳(x₁, x₂)`, the isomorphism it is. -/
noncomputable def tautological (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (hI : IsAlgebraicSpace B S hS (isomSpaceOverSpace B S hS Z hZ x₁ x₂)) :
    IsomFamily B S hS (isomSpaceOverSpace B S hS Z hZ x₁ x₂) hI
      (algebraicSpaceStackMap.{u, w} B S hS hI hZ (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) ≫ x₁)
      (algebraicSpaceStackMap.{u, w} B S hS hI hZ (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) ≫
        x₂) :=
  ⟨fun _ t => t.2.1, fun _ _ => rfl⟩

/-- Families of isomorphisms between equal 1-morphisms. -/
theorem nonempty_congr {x₁ x₂ x₁' x₂' : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (h : Nonempty (IsomFamily B S hS Z hZ x₁ x₂)) (h₁ : x₁ = x₁') (h₂ : x₂ = x₂') :
    Nonempty (IsomFamily B S hS Z hZ x₁' x₂') := by
  subst h₁ h₂
  exact h

/-- Families of isomorphisms between restrictions along `a` and then `b` are families between
restrictions along `a ≫ b`. -/
private theorem nonempty_of_comp_comp_eq {Y₁ Y₂ Y₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY₁ : IsAlgebraicSpace B S hS Y₁} {hY₂ : IsAlgebraicSpace B S hS Y₂}
    {hY₃ : IsAlgebraicSpace B S hS Y₃} (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃) {c : Y₁ ⟶ Y₃}
    (h : a ≫ b = c) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Y₃ hY₃ ⟶ 𝒳)
    (hφ : Nonempty (IsomFamily B S hS Y₁ hY₁
      (algebraicSpaceStackMap.{u, w} B S hS hY₁ hY₂ a ≫
        algebraicSpaceStackMap.{u, w} B S hS hY₂ hY₃ b ≫ x₁)
      (algebraicSpaceStackMap.{u, w} B S hS hY₁ hY₂ a ≫
        algebraicSpaceStackMap.{u, w} B S hS hY₂ hY₃ b ≫ x₂))) :
    Nonempty (IsomFamily B S hS Y₁ hY₁ (algebraicSpaceStackMap.{u, w} B S hS hY₁ hY₃ c ≫ x₁)
      (algebraicSpaceStackMap.{u, w} B S hS hY₁ hY₃ c ≫ x₂)) :=
  nonempty_congr hφ (algebraicSpaceStackMap_comp_comp_eq a b h x₁)
    (algebraicSpaceStackMap_comp_comp_eq a b h x₂)

/-- **A morphism to `Isom_𝒳(x₁, x₂)` over `r : Z' ⟶ Z` is a family of isomorphisms between the
restrictions of `x₁` and `x₂` along `r`.** -/
theorem nonempty_of_comp_proj_eq {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ' : IsAlgebraicSpace B S hS Z') {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (hI : IsAlgebraicSpace B S hS (isomSpaceOverSpace B S hS Z hZ x₁ x₂)) (r : Z' ⟶ Z)
    (s : Z' ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂)
    (hs : s ≫ isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ = r) :
    Nonempty (IsomFamily B S hS Z' hZ' (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ r ≫ x₁)
      (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ r ≫ x₂)) := by
  subst hs
  exact ⟨(tautological x₁ x₂ hI).restrict hZ' s⟩

end IsomFamily

namespace AlgebraicStacks

/-- **The step (d) to (e) of the proof of Stacks 0CQ7 for one pair of points.** Let `V₁` be a
quasi-compact open of a quasi-compact and quasi-separated algebraic space `Y₁`, and let
`x₁, x₂ : V₁ ⟶ 𝒳` be two points over the same morphism `V₁ ⟶ V`, for `f` a gerbe over `V` in the
sense of `hgerbe`. Then `Isom_𝒳(x₁, x₂) ⟶ V₁` is surjective, flat and locally of finite
presentation, so Stacks 0CQ6 gives a finite surjective `r : Y₂ ⟶ Y₁` such that every point of
`r⁻¹(V₁)` has an open neighbourhood over which the restrictions of `x₁` and `x₂` are isomorphic. -/
theorem exists_finite_cover_isomFamily_pair
    (h0CQ6 : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Y)
      (_ : Space.IsQuasiCompactSpace B S hS Y)
      (_ : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
      (_ : Space.IsQuasiCompactSpace B S hS V.toFunctor)
      {𝒳 : AlgebraicStacks.{u, w} B S hS}
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1)
      (_ : IsSurjective B S hS f) (_ : AlgebraicStacks.IsFlat B S hS f)
      (_ : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f),
      ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y),
        Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
        ∃ (J : Type u) (W : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (hW : ∀ j, IsAlgebraicSpace B S hS (W j)) (ι : ∀ j, W j ⟶ Y')
          (q : ∀ j, W j ⟶ V.toFunctor)
          (x : ∀ j, algebraicSpaceStack.{u, w} B S hS (W j) (hW j) ⟶ 𝒳),
          (∀ j, Space.IsOpenImmersion B S hS (ι j)) ∧ (∀ j, ι j ≫ g = q j ≫ V.ι) ∧
          (∀ y : Space.points B S hS Y',
            Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) →
              ∃ j, y ∈ Set.range (Space.pointsMap B S hS (W j) (ι j))) ∧
          ∀ j, Nonempty (x j ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j)))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
    (V : Subfunctor Y)
    (hgerbe : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
      (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (g : Z ⟶ V.toFunctor),
      x₁ ≫ f = algebraicSpaceStackMap.{u, w} B S hS hZ hY (g ≫ V.ι) →
      x₂ ≫ f = algebraicSpaceStackMap.{u, w} B S hS hZ hY (g ≫ V.ι) →
      Space.IsSurjective B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) ∧
        Space.IsFlat B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) ∧
        Space.IsLocallyOfFinitePresentation B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂))
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₁qc : Space.IsQuasiCompactSpace B S hS Y₁)
    (hY₁qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₁)
    (V₁ : Subfunctor Y₁) (hV₁ : Space.IsOpenSubspace B S hS V₁)
    (hV₁qc : Space.IsQuasiCompactSpace B S hS V₁.toFunctor)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS V₁.toFunctor hV₁.1 ⟶ 𝒳)
    (g : V₁.toFunctor ⟶ V.toFunctor)
    (h₁ : x₁ ≫ f = algebraicSpaceStackMap.{u, w} B S hS hV₁.1 hY (g ≫ V.ι))
    (h₂ : x₂ ≫ f = algebraicSpaceStackMap.{u, w} B S hS hV₁.1 hY (g ≫ V.ι)) :
    ∃ (Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y₂) (r : Y₂ ⟶ Y₁),
      Space.IsFinite B S hS r ∧ Space.IsSurjective B S hS r ∧
      ∀ y : Space.points B S hS Y₂,
        Space.pointsMap B S hS Y₂ r y ∈ Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι) →
        ∃ (O : Subfunctor Y₂) (hO : Space.IsOpenSubspace B S hS O) (hOV : O ≤ V₁.preimage r),
          y ∈ Set.range (Space.pointsMap B S hS O.toFunctor O.ι) ∧
          Nonempty (IsomFamily B S hS O.toFunctor hO.1
            (algebraicSpaceStackMap.{u, w} B S hS hO.1 hV₁.1
              (Subfunctor.homOfLe hOV ≫ V₁.fromPreimage r) ≫ x₁)
            (algebraicSpaceStackMap.{u, w} B S hS hO.1 hV₁.1
              (Subfunctor.homOfLe hOV ≫ V₁.fromPreimage r) ≫ x₂)) := by
  -- the isomorphism space `T = Isom_𝒳(x₁, x₂)` and its projection to `V₁` (Stacks 0CPR)
  have hT := isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS V₁.toFunctor hV₁.1 x₁ x₂
  set p := isomSpaceOverSpaceProj B S hS V₁.toFunctor hV₁.1 x₁ x₂
  obtain ⟨hps, hpf, hpl⟩ := hgerbe V₁.toFunctor hV₁.1 x₁ x₂ g h₁ h₂
  -- Stacks 0CQ6 applied to the 1-morphism of `p`
  obtain ⟨Y₂, hY₂, r, hrf, hrs, J, W, hW, ι, q, x, hι, hιq, hcov, hx⟩ :=
    h0CQ6 hY₁ hY₁qc hY₁qs V₁ hV₁ hV₁qc (algebraicSpaceStackMap.{u, w} B S hS hT hV₁.1 p)
      (isSurjective_algebraicSpaceStackMap_of_isSurjective.{u, w} hT hV₁.1 p hps)
      ((isFlat_algebraicSpaceStackMap_iff.{u, w} B S hS hT hV₁.1 p).2 hpf)
      ((isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS hT hV₁.1 p).2 hpl)
  refine ⟨Y₂, hY₂, r, hrf, hrs, fun y hy => ?_⟩
  obtain ⟨j, hj⟩ := hcov y hy
  -- the 1-morphism `x j` is the 1-morphism of a section `s` of `T` over `q j`
  obtain ⟨s, hs⟩ := exists_eq_algebraicSpaceStackMap (hW j) hT (x j)
  have hsq : s ≫ p = q j := by
    obtain ⟨e⟩ := hx j
    have h := eq_of_iso_algebraicSpaceStack e
    rw [hs, ← algebraicSpaceStackMap_comp] at h
    exact algebraicSpaceStackMap_injective h
  -- the open `O = ι j (W j)`
  have : Mono (ι j) := Space.mono_of_isOpenImmersion B S hS (ι j) (hι j)
  let O := Subfunctor.range (ι j)
  have hO : Space.IsOpenSubspace B S hS O :=
    Space.isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace B S hS (ι j) (hW j) (hι j)
  let e : W j ≅ O.toFunctor := asIso (Subfunctor.toRange (ι j))
  have he : e.inv ≫ ι j = O.ι := by
    rw [Iso.inv_comp_eq]
    exact (Subfunctor.toRange_ι (ι j)).symm
  have hOV : O ≤ V₁.preimage r := by
    rintro T _ ⟨a, rfl⟩
    show ((ι j ≫ r).app T a) ∈ V₁.obj T
    rw [hιq j]
    exact ((q j).app T a).2
  refine ⟨O, hO, hOV, Space.mem_range_pointsMap_range_ι (ι j) hj, ?_⟩
  have hfac : e.inv ≫ q j = Subfunctor.homOfLe hOV ≫ V₁.fromPreimage r := by
    rw [← cancel_mono V₁.ι, Category.assoc, Category.assoc, ← hιq j, ← Category.assoc, he,
      Subfunctor.fromPreimage_ι, Subfunctor.homOfLe_ι_assoc]
  exact IsomFamily.nonempty_of_comp_proj_eq hO.1 hT
    (Subfunctor.homOfLe hOV ≫ V₁.fromPreimage r) (e.inv ≫ s) (by rw [Category.assoc, hsq, hfac])

namespace SectionFamily

/-- The sections of the restriction of a family of local sections. -/
theorem restrict_x {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
    {W : Subfunctor Y} {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀}
    {q₀ : Y₀ ⟶ Y} {ι : Type} (F : SectionFamily hY f W hY₀ q₀ ι)
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁) (r : Y₁ ⟶ Y₀)
    (hr : Space.IsQuasiCompact B S hS r) (i : ι) :
    (F.restrict hY₁ r hr).x i = algebraicSpaceStackMap.{u, w} B S hS
      (Space.isOpenSubspace_preimage B S hS r (F.U i) hY₀ hY₁ (F.isOpen i)).1 (F.isOpen i).1
      ((F.U i).fromPreimage r) ≫ F.x i :=
  rfl

/-- **The step (d) to (e) of the proof of Stacks 0CQ7.** Let `F` be a family of local sections
`x i : U i ⟶ 𝒳` over a quasi-compact and quasi-separated `Y₀` proper over `Y`, and let
`V₀ ⊆ ⋂ U i` be a quasi-compact open mapping into the open `V ⊆ Y` over which `f` is a gerbe in
the sense of `hgerbe`. Then there is a proper surjective `r : Y₁ ⟶ Y₀` from a quasi-compact and
quasi-separated algebraic space such that, for all `i` and `j`, every point of `r⁻¹(V₀)` has an
open neighbourhood `O ⊆ r⁻¹(V₀)` over which the restrictions of `x i ∘ r` and `x j ∘ r` are
isomorphic. The pairs are treated one at a time by
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_finite_cover_isomFamily_pair` (Stacks 0CQ6
applied to `Isom_𝒳(x i, x j) ⟶ V₀`), each over the previous base change, and the families found
at earlier steps are restricted along the later ones. -/
theorem exists_finite_cover_localIsos
    (h0CQ6 : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Y)
      (_ : Space.IsQuasiCompactSpace B S hS Y)
      (_ : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
      (_ : Space.IsQuasiCompactSpace B S hS V.toFunctor)
      {𝒳 : AlgebraicStacks.{u, w} B S hS}
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1)
      (_ : IsSurjective B S hS f) (_ : AlgebraicStacks.IsFlat B S hS f)
      (_ : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f),
      ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y),
        Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
        ∃ (J : Type u) (W : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (hW : ∀ j, IsAlgebraicSpace B S hS (W j)) (ι : ∀ j, W j ⟶ Y')
          (q : ∀ j, W j ⟶ V.toFunctor)
          (x : ∀ j, algebraicSpaceStack.{u, w} B S hS (W j) (hW j) ⟶ 𝒳),
          (∀ j, Space.IsOpenImmersion B S hS (ι j)) ∧ (∀ j, ι j ≫ g = q j ≫ V.ι) ∧
          (∀ y : Space.points B S hS Y',
            Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) →
              ∃ j, y ∈ Set.range (Space.pointsMap B S hS (W j) (ι j))) ∧
          ∀ j, Nonempty (x j ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j)))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
    (V : Subfunctor Y) (_hV : Space.IsOpenSubspace B S hS V)
    (hgerbe : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
      (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (g : Z ⟶ V.toFunctor),
      x₁ ≫ f = algebraicSpaceStackMap.{u, w} B S hS hZ hY (g ≫ V.ι) →
      x₂ ≫ f = algebraicSpaceStackMap.{u, w} B S hS hZ hY (g ≫ V.ι) →
      Space.IsSurjective B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) ∧
        Space.IsFlat B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) ∧
        Space.IsLocallyOfFinitePresentation B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂))
    {W : Subfunctor Y} {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀}
    {q₀ : Y₀ ⟶ Y} {ι : Type} [Finite ι]
    (F : SectionFamily hY f W hY₀ q₀ ι) (hY₀qc : Space.IsQuasiCompactSpace B S hS Y₀)
    (hY₀qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀)
    (V₀ : Subfunctor Y₀) (hV₀ : Space.IsOpenSubspace B S hS V₀)
    (hV₀qc : Space.IsQuasiCompactSpace B S hS V₀.toFunctor) (hVU : ∀ i, V₀ ≤ F.U i)
    (hV₀V : V₀ ≤ V.preimage q₀) :
    ∃ (Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY₁ : IsAlgebraicSpace B S hS Y₁) (r : Y₁ ⟶ Y₀)
      (hr : Space.IsProper B S hS r),
      Space.IsSurjective B S hS r ∧ Space.IsQuasiCompactSpace B S hS Y₁ ∧
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₁ ∧
      ∀ (y : Space.points B S hS Y₁), Space.pointsMap B S hS Y₁ r y ∈
          Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) → ∀ i j,
        ∃ (O : Subfunctor Y₁) (hO : Space.IsOpenSubspace B S hS O) (hOV : O ≤ V₀.preimage r),
          y ∈ Set.range (Space.pointsMap B S hS O.toFunctor O.ι) ∧
          Nonempty (IsomFamily B S hS O.toFunctor hO.1
            (algebraicSpaceStackMap.{u, w} B S hS hO.1 ((F.restrict hY₁ r hr.2.1.2).isOpen i).1
                (Subfunctor.homOfLe (fun T _ ha => hVU i T (hOV T ha))) ≫
              (F.restrict hY₁ r hr.2.1.2).x i)
            (algebraicSpaceStackMap.{u, w} B S hS hO.1 ((F.restrict hY₁ r hr.2.1.2).isOpen j).1
                (Subfunctor.homOfLe (fun T _ ha => hVU j T (hOV T ha))) ≫
              (F.restrict hY₁ r hr.2.1.2).x j)) := by
  classical
  have := Fintype.ofFinite ι
  -- the restrictions `X i` of the `x i` to `V₀`, all over `g₀ : V₀ ⟶ V`
  let X : ι → (algebraicSpaceStack.{u, w} B S hS V₀.toFunctor hV₀.1 ⟶ 𝒳) := fun i =>
    algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen i).1 (Subfunctor.homOfLe (hVU i)) ≫
      F.x i
  let g₀ : V₀.toFunctor ⟶ V.toFunctor := Subfunctor.homOfLe hV₀V ≫ V.fromPreimage q₀
  have hX : ∀ i, X i ≫ f = algebraicSpaceStackMap.{u, w} B S hS hV₀.1 hY (g₀ ≫ V.ι) := by
    intro i
    have h : Subfunctor.homOfLe (hVU i) ≫ (F.U i).ι ≫ q₀ = g₀ ≫ V.ι := rfl
    rw [Category.assoc, F.hx, ← algebraicSpaceStackMap_comp, h]
  -- the pairs are handled one at a time
  have main : ∀ s : Finset (ι × ι), ∃ (Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (hY₁ : IsAlgebraicSpace B S hS Y₁) (r : Y₁ ⟶ Y₀),
      Space.IsProper B S hS r ∧ Space.IsSurjective B S hS r ∧
      Space.IsQuasiCompactSpace B S hS Y₁ ∧
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₁ ∧
      ∀ y : Space.points B S hS Y₁, Space.pointsMap B S hS Y₁ r y ∈
          Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) → ∀ p ∈ s,
        ∃ (O : Subfunctor Y₁) (hO : Space.IsOpenSubspace B S hS O) (hOV : O ≤ V₀.preimage r),
          y ∈ Set.range (Space.pointsMap B S hS O.toFunctor O.ι) ∧
          Nonempty (IsomFamily B S hS O.toFunctor hO.1
            (algebraicSpaceStackMap.{u, w} B S hS hO.1 hV₀.1
              (Subfunctor.homOfLe hOV ≫ V₀.fromPreimage r) ≫ X p.1)
            (algebraicSpaceStackMap.{u, w} B S hS hO.1 hV₀.1
              (Subfunctor.homOfLe hOV ≫ V₀.fromPreimage r) ≫ X p.2)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨Y₀, hY₀, 𝟙 Y₀, Space.isProper_of_isIso B S hS (𝟙 Y₀), Space.isSurjective_id B S hS Y₀,
        hY₀qc, hY₀qs, fun _ _ p hp => absurd hp (Finset.notMem_empty p)⟩
    | insert p s _ ih =>
      obtain ⟨Y₁, hY₁, r, hr, hrs, hY₁qc, hY₁qs, hfam⟩ := ih
      have hV₁ := Space.isOpenSubspace_preimage B S hS r V₀ hY₀ hY₁ hV₀
      have hV₁qc := Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY₀ hY₁ r
        hr.2.1.2 hV₀ hV₀qc
      have hXr : ∀ i, (algebraicSpaceStackMap.{u, w} B S hS hV₁.1 hV₀.1 (V₀.fromPreimage r) ≫
          X i) ≫ f = algebraicSpaceStackMap.{u, w} B S hS hV₁.1 hY
            ((V₀.fromPreimage r ≫ g₀) ≫ V.ι) := by
        intro i
        rw [Category.assoc, hX, ← algebraicSpaceStackMap_comp]
        congr 1
      obtain ⟨Y₂, hY₂, r₂, hr₂f, hr₂s, hfam₂⟩ := exists_finite_cover_isomFamily_pair h0CQ6 V
        hgerbe hY₁ hY₁qc hY₁qs (V₀.preimage r) hV₁ hV₁qc
        (algebraicSpaceStackMap.{u, w} B S hS hV₁.1 hV₀.1 (V₀.fromPreimage r) ≫ X p.1)
        (algebraicSpaceStackMap.{u, w} B S hS hV₁.1 hV₀.1 (V₀.fromPreimage r) ≫ X p.2)
        (V₀.fromPreimage r ≫ g₀) (hXr p.1) (hXr p.2)
      have hr₂ : Space.IsProper B S hS r₂ :=
        ((Space.isFinite_iff_isAffineHom_and_isProper B S hS hY₂ hY₁ r₂).1 hr₂f).2
      obtain ⟨hY₂qc, hY₂qs⟩ :=
        Space.isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isFinite hY₂ hY₁ r₂ hr₂f
          hY₁qc hY₁qs
      refine ⟨Y₂, hY₂, r₂ ≫ r, Space.isProper_comp B S hS hY₂ hY₁ hY₀ r₂ r hr₂ hr,
        Space.isSurjective_comp B S hS hr₂s hrs, hY₂qc, hY₂qs, fun y hy p' hp' => ?_⟩
      rw [Space.pointsMap_comp_apply] at hy
      rcases Finset.mem_insert.1 hp' with rfl | hp'
      · -- the new pair, from the step for one pair
        obtain ⟨O, hO, hOV, hyO, hφ⟩ := hfam₂ y (by rwa [Space.range_pointsMap_preimage_ι])
        have hOV' : O ≤ V₀.preimage (r₂ ≫ r) := fun T _ ha => hOV T ha
        have hc : (Subfunctor.homOfLe hOV ≫ (V₀.preimage r).fromPreimage r₂) ≫
            V₀.fromPreimage r = Subfunctor.homOfLe hOV' ≫ V₀.fromPreimage (r₂ ≫ r) := rfl
        exact ⟨O, hO, hOV', hyO, IsomFamily.nonempty_of_comp_comp_eq _ _ hc _ _ hφ⟩
      · -- an earlier pair, by restriction along `r₂`
        obtain ⟨O, hO, hOV, hyO, ⟨φ⟩⟩ := hfam (Space.pointsMap B S hS Y₂ r₂ y) hy p' hp'
        have hO' := Space.isOpenSubspace_preimage B S hS r₂ O hY₁ hY₂ hO
        have hOV' : O.preimage r₂ ≤ V₀.preimage (r₂ ≫ r) := fun T _ ha => hOV _ ha
        have hc : O.fromPreimage r₂ ≫ Subfunctor.homOfLe hOV ≫ V₀.fromPreimage r =
            Subfunctor.homOfLe hOV' ≫ V₀.fromPreimage (r₂ ≫ r) := rfl
        exact ⟨O.preimage r₂, hO', hOV', by rwa [Space.range_pointsMap_preimage_ι],
          IsomFamily.nonempty_of_comp_comp_eq _ _ hc _ _
            ⟨φ.restrict hO'.1 (O.fromPreimage r₂)⟩⟩
  obtain ⟨Y₁, hY₁, r, hr, hrs, hqc, hqs, hfam⟩ := main Finset.univ
  refine ⟨Y₁, hY₁, r, hr, hrs, hqc, hqs, fun y hy i j => ?_⟩
  obtain ⟨O, hO, hOV, hyO, hφ⟩ := hfam y hy (i, j) (Finset.mem_univ _)
  have hc : ∀ k, (Subfunctor.homOfLe hOV ≫ V₀.fromPreimage r) ≫ Subfunctor.homOfLe (hVU k) =
      Subfunctor.homOfLe (fun T a ha => hVU k T (hOV T ha) :
        O ≤ (F.restrict hY₁ r hr.2.1.2).U k) ≫ (F.U k).fromPreimage r := by
    intro k
    ext T a
    rfl
  have hX' : ∀ k, algebraicSpaceStackMap.{u, w} B S hS hO.1 hV₀.1
      (Subfunctor.homOfLe hOV ≫ V₀.fromPreimage r) ≫ X k =
      algebraicSpaceStackMap.{u, w} B S hS hO.1 ((F.restrict hY₁ r hr.2.1.2).isOpen k).1
        (Subfunctor.homOfLe (fun T a ha => hVU k T (hOV T ha))) ≫
          (F.restrict hY₁ r hr.2.1.2).x k := by
    intro k
    rw [restrict_x, algebraicSpaceStackMap_comp_comp_eq _ _ (hc k)]
    exact (algebraicSpaceStackMap_comp_comp_eq _ _ rfl _).symm
  exact ⟨O, hO, hOV, hyO, IsomFamily.nonempty_congr hφ (hX' i) (hX' j)⟩

end SectionFamily

end AlgebraicStacks

end AlgebraicGeometry.Stack

end

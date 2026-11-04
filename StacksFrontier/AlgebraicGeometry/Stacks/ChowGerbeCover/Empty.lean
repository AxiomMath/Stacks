module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.SectionCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary

/-!
# Section covers over pointless pieces in the proof of Stacks 0CQ7

An object of the big fppf site with empty underlying scheme is covered by the empty sieve, so a
stack has, over it, a unique object up to unique isomorphism. Consequently a 1-morphism into an
algebraic stack out of an algebraic space without points always exists, with any prescribed
composite to the stack of an algebraic space. This is the degenerate case of the gluing of
sections that the proof of [Stacks, Tag 0CQ7] performs when it takes unions of section covers.

## Main results

* `CategoryTheory.Functor.IsStackInGroupoids.nonempty_iso_and_subsingleton_hom_of_bot_mem`: the
  fibre of a stack in groupoids over an object covered by the empty sieve is equivalent to the
  point.
* `CategoryTheory.Functor.IsStackInGroupoids.eq_of_isHomLift_of_bot_mem`: two morphisms over the
  same morphism of the base with source over such an object are equal.
* `AlgebraicGeometry.Stack.AlgebraicStacks.algebraicSpaceStack_hom_ext_of_cover`: two
  1-morphisms between the stacks of two algebraic spaces agree once they agree on a family of
  subspaces covering the source locally.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_algebraicSpaceStack_hom_comp_eq_of_isEmpty`:
  a 1-morphism out of an algebraic space without points with a prescribed composite.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver.of_isEmpty_points_preimage`: a
  section cover over `q₀` by `p = 𝟙`, when `q₀⁻¹(W)` has no points.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w t v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsStackInGroupoids

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion Fiber.mk

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {p : D ⥤ C} {J : GrothendieckTopology C}

/-- **The fibre of a stack in groupoids over an object covered by the empty sieve is equivalent to
the point**: any two objects are isomorphic, and there is at most one morphism between them.
Both are the sheaf condition of the `Isom` presheaf for the empty covering family. -/
theorem nonempty_iso_and_subsingleton_hom_of_bot_mem (hp : p.IsStackInGroupoids.{t} J) {U : C}
    (hU : ⊥ ∈ J U) (x y : p.Fiber U) : Nonempty (x ≅ y) ∧ Subsingleton (x ⟶ y) := by
  have hg := hp.isFiberedInGroupoids.fiber_isGroupoid U
  have h := hp.isom_isSheaf x.1 y.1 x.2 y.2
    (fun e : PEmpty.{t + 1} => e.elim) (fun e => e.elim)
    (by simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty, Sieve.generate_bot] using hU)
    (fun e _ => e.elim) (fun e _ => e.elim) (fun e _ => e.elim)
    (fun e _ => e.elim) (fun e => e.elim) (fun e => e.elim)
    (fun e _ => e.elim) (fun e _ => e.elim)
  obtain ⟨f, hf, huniq⟩ := h (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim) (fun e _ => e.elim)
  refine ⟨⟨fibreIsoMk hf.1 hf.2.1⟩, ⟨fun a b => Fiber.hom_ext ?_⟩⟩
  have key (c : x ⟶ y) := huniq c.1 ⟨fibreHom_of_fiberHom c,
    inferInstanceAs (IsIso (Fiber.fiberInclusion.map c)), fun e => e.elim⟩
  exact (key a).trans (key b).symm

/-- **Two morphisms of a stack in groupoids over the same morphism of the base, out of an object
lying over an object covered by the empty sieve, are equal.** The second is cartesian, so the
first factors through it by a vertical endomorphism of its source, which is the identity because
the fibre there has a single morphism between any two objects. -/
theorem eq_of_isHomLift_of_bot_mem (hp : p.IsStackInGroupoids.{t} J) {T T' : C} (hT : ⊥ ∈ J T)
    (m : T ⟶ T') {a b : D} (f g : a ⟶ b) [p.IsHomLift m f] [p.IsHomLift m g] : f = g := by
  have := hp.isFiberedInGroupoids.isStronglyCartesian_homLift m g
  have ha : p.obj a = T := IsHomLift.domain_eq p m f
  have hsub := (nonempty_iso_and_subsingleton_hom_of_bot_mem hp hT (Fiber.mk ha)
    (Fiber.mk ha)).2
  have h1 : Fiber.homMk p T (IsCartesian.map p m g f) = 𝟙 (Fiber.mk ha) := Subsingleton.elim _ _
  have h2 : IsCartesian.map p m g f = 𝟙 a := congrArg Fiber.fiberInclusion.map h1
  rw [← IsCartesian.fac p m g f, h2, Category.id_comp]

end CategoryTheory.Functor.IsStackInGroupoids

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An object of the site carrying a section of a presheaf without points is covered by the
empty sieve**: the section maps the points of the object into those of the presheaf, so the
underlying scheme of the object is empty. -/
theorem bot_mem_topology_of_isEmpty_points {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsEmpty (Space.points B S hS Z)) {T : BigFppfOver B S hS} (z : Z.obj (op T)) :
    (⊥ : Sieve T) ∈ BigFppfOver.topology B S hS T :=
  BigFppfOver.bot_mem_topology T ⟨fun t => hZ.false (Space.pointsMap B S hS (yoneda.obj T)
    (yonedaEquiv.symm z) ((Space.pointsEquivScheme B S hS T).symm t))⟩

/-- **1-morphisms between stacks of algebraic spaces agree when they agree locally.** Two
1-morphisms out of the stack of `Z` into the stack of `Y` are equal once their restrictions to a
family of algebraic subspaces `U i ⊆ Z` covering `Z` locally agree: the elements of `Y` they name
agree along a covering sieve, and `Y` is a sheaf. -/
theorem algebraicSpaceStack_hom_ext_of_cover {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y) {ι : Type*}
    (U : ι → Subfunctor Z) (hU : ∀ i, IsAlgebraicSpace B S hS (U i).toFunctor)
    (hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)), ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f → ∃ i, Z.map f.op z ∈ (U i).obj (op V))
    {g g' : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
    (h : ∀ i, algebraicSpaceStackMap.{u, w} B S hS (hU i) hZ (U i).ι ≫ g =
      algebraicSpaceStackMap.{u, w} B S hS (hU i) hZ (U i).ι ≫ g') : g = g' := by
  refine Bicategory.InducedBicategory.hom_ext (hom_ext_of_section B S hS _ _ fun ξ => ?_)
  obtain ⟨R, hR, hRU⟩ := hcov ξ.base ξ.fiber.as
  have hY' : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hY.isSheaf
  refine (hY' R hR).isSeparatedFor.ext fun V f hf => ?_
  obtain ⟨i, hi⟩ := hRU hf
  let c : (fibredCategory B S hS (U i).toFunctor).val.obj :=
    ⟨V, Discrete.mk ⟨Z.map f.op ξ.fiber.as, hi⟩⟩
  let u : (associatedMap B S hS (U i).ι).1.hom.obj c ⟶ ξ := fibredCategoryHomOfEq f rfl
  have e1 := sectionOfBasedFunctor_map g.hom.hom.toFunctor g.hom.hom.w u
  have e2 := sectionOfBasedFunctor_map g'.hom.hom.toFunctor g'.hom.hom.w u
  have h' := congrArg (fun t => sectionOfBasedFunctor t.hom.hom.toFunctor t.hom.hom.w c) (h i)
  exact e1.trans (h'.trans e2.symm)

/-- **A 1-morphism out of an algebraic space without points, with a prescribed composite.** For
an algebraic space `Z` without points, a morphism `g : Z ⟶ Y` of algebraic spaces and a
1-morphism `f : 𝒳 ⟶ Y` from an algebraic stack, there is a 1-morphism `x : Z ⟶ 𝒳` with
`x ≫ f = g`. Every object of the site over which `Z` has a section is covered by the empty sieve,
so `x` is glued along the empty family, and the equality holds because it is checked locally
along the same empty covering. -/
theorem exists_algebraicSpaceStack_hom_comp_eq_of_isEmpty {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y)
    (hZe : IsEmpty (Space.points B S hS Z)) (g : Z ⟶ Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) :
    ∃ x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳,
      x ≫ f = algebraicSpaceStackMap.{u, w} B S hS hZ hY g := by
  let U : PEmpty.{1} → Subfunctor Z := fun i => i.elim
  have hU : ∀ i, IsAlgebraicSpace B S hS (U i).toFunctor := fun i => i.elim
  have hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)),
      ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄,
        R.arrows f → ∃ i, Z.map f.op z ∈ (U i).obj (op V) :=
    fun T z => ⟨⊥, bot_mem_topology_of_isEmpty_points hZe z, fun _ _ hf => False.elim hf⟩
  obtain ⟨x, -⟩ := exists_algebraicSpaceStack_hom_of_cocycle hZ U hU (𝒳 := 𝒳)
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
    hcov
  exact ⟨x, algebraicSpaceStack_hom_ext_of_cover hZ hY U hU hcov fun i => i.elim⟩

/-- **A section along a morphism whose preimage of `W` has no points.** -/
theorem hasSectionAlong_of_isEmpty_points {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (W : Subfunctor Y)
    (hW : Space.IsOpenSubspace B S hS W) {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y)
    (h : IsEmpty (Space.points B S hS (W.preimage g).toFunctor)) :
    HasSectionAlong hY f W hW hY' g :=
  exists_algebraicSpaceStack_hom_comp_eq_of_isEmpty _ hY h _ f

/-- **A section cover by the identity when `q₀⁻¹(W)` has no points.** If the preimage of `W`
under `q₀ : Y₀ ⟶ Y` has no points, then `p = 𝟙 Y₀` together with the 1-morphism of
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_algebraicSpaceStack_hom_comp_eq_of_isEmpty` is a
section cover over `q₀` of every `V₀ ⊆ Y₀` whose points map into those of `W`. (Such a `V₀` has
no points itself.) -/
theorem HasSectionCoverOver.of_isEmpty_points_preimage {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (W : Subfunctor Y)
    (hW : Space.IsOpenSubspace B S hS W) {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY₀ : IsAlgebraicSpace B S hS Y₀) (q₀ : Y₀ ⟶ Y) (V₀ : Subfunctor Y₀)
    (h : IsEmpty (Space.points B S hS (W.preimage q₀).toFunctor))
    (hV : Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) ⊆
      Space.pointsMap B S hS Y₀ q₀ ⁻¹' Set.range (Space.pointsMap B S hS W.toFunctor W.ι)) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V₀ := by
  refine ⟨Y₀, hY₀, 𝟙 Y₀, Space.isProper_of_isIso B S hS (𝟙 Y₀),
    (hasSectionAlong_of_isEmpty_points f W hW hY₀ q₀ h).congr (Category.id_comp q₀).symm,
    fun v hv => ⟨v, ?_, by rw [Space.pointsMap_id]; rfl⟩⟩
  rw [Category.id_comp]
  exact hV hv

end AlgebraicGeometry.Stack.AlgebraicStacks

end

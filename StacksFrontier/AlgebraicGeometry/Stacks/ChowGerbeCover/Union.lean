module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.Empty
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafCoproduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.CategoryTheory.Sites.CoproductUniversality

/-!
# Unions of section covers in the proof of Stacks 0CQ7

The proof of [Stacks, Tag 0CQ7] covers `Y` by finitely many pieces over each of which it has a
section cover (`AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver`) and then takes the
union. This file proves that section covers are stable under finite unions: given section covers
`p_i : Y'_i ⟶ Y₀` with sections `x_i : (p_i ≫ q₀)⁻¹(W) ⟶ 𝒳`, the coproduct `Y' = ∐ Y'_i` (a
coproduct of sheaves, which is an algebraic space) with `p = [p_i]` (proper) carries a section
over `(p ≫ q₀)⁻¹(W)` glued from the `x_i`. The pieces of the coproduct overlap only over objects
of the site with empty underlying scheme, where any two objects of the stack `𝒳` are uniquely
isomorphic, which gives the transition isomorphisms and their cocycle condition.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOverPoints`: the datum of a section
  cover, for an arbitrary set of points of `Y₀` in place of the points of a subfunctor.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOverPoints.iUnion_of_finite`: the
  coproduct construction over a finite index type.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver.of_isEmpty`: a section cover
  of a subfunctor without points.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver.union` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver.iUnion`: a subfunctor whose points
  are covered by those of two, or of finitely many, subfunctors with section covers has one.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A section cover over `q₀` of a set of points `P` of `Y₀`**: a proper morphism
`p : Y' ⟶ Y₀` of algebraic spaces and a 1-morphism `(p ≫ q₀)⁻¹(W) ⟶ 𝒳` over `Y`, such that every
point of `P` is the image of a point of `(p ≫ q₀)⁻¹(W)`. For `P` the points of a subfunctor `V₀`
this is `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver`. -/
def HasSectionCoverOverPoints {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (W : Subfunctor Y)
    (hW : Space.IsOpenSubspace B S hS W) {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hY₀ : IsAlgebraicSpace B S hS Y₀) (q₀ : Y₀ ⟶ Y) (P : Set (Space.points B S hS Y₀)) :
    Prop :=
  ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY' : IsAlgebraicSpace B S hS Y') (p : Y' ⟶ Y₀),
    Space.IsProper B S hS p ∧ HasSectionAlong hY f W hW hY' (p ≫ q₀) ∧
      P ⊆ Space.pointsMap B S hS Y' p '' (Space.pointsMap B S hS Y' (p ≫ q₀) ⁻¹'
          Set.range (Space.pointsMap B S hS W.toFunctor W.ι))

/-! ### Gluing along a cover whose members meet only over pointless objects -/

section Disjoint

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ι : Type*} (U : ι → Subfunctor Z)
  (hU : ∀ i, IsAlgebraicSpace B S hS (U i).toFunctor) {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (x : ∀ i, algebraicSpaceStack.{u, w} B S hS (U i).toFunctor (hU i) ⟶ 𝒳)

/-- The image under a 1-morphism out of the stack of `U i` of an object of the stack of `Z`
lying in `U i` lies over the same object of the site. -/
theorem p_obj_obj_fibredCategorySubfunctorObj (i : ι) (a : (fibredCategory B S hS Z).val.obj)
    (hi : a.fiber.as ∈ (U i).obj (op a.base)) :
    𝒳.val.val.p.obj ((x i).hom.hom.obj (fibredCategorySubfunctorObj (U i) a hi)) = a.base :=
  Functor.congr_obj (x i).hom.hom.w _

variable (hdisj : ∀ i j, i ≠ j → ∀ {T : BigFppfOver B S hS} (z : Z.obj (op T)),
  z ∈ (U i).obj (op T) → z ∈ (U j).obj (op T) → (⊥ : Sieve T) ∈ BigFppfOver.topology B S hS T)

/-- A `dite` whose condition fails lies over what its second branch lies over. -/
private theorem isHomLift_dite_of_not {C D : Type*} [Category C] [Category D] {p : D ⥤ C} {R : C}
    {a b : D} {c : Prop} [Decidable c] (t : c → (a ⟶ b)) (e : ¬c → (a ⟶ b)) (h : ¬c)
    (he : p.IsHomLift (𝟙 R) (e h)) : p.IsHomLift (𝟙 R) (dite c t e) := by
  rwa [dite_eq_right h]

open Classical in
/-- **The transition morphisms for a cover whose members meet only over pointless objects.** On
`U i ∩ U i` it is the identity; on `U i ∩ U j` for `i ≠ j` the object of the site is covered by
the empty sieve, and it is the unique isomorphism of the fibre of `𝒳` there. -/
noncomputable def disjointTransition (i j : ι) (a : (fibredCategory B S hS Z).val.obj)
    (hi : a.fiber.as ∈ (U i).obj (op a.base)) (hj : a.fiber.as ∈ (U j).obj (op a.base)) :
    (x i).hom.hom.obj (fibredCategorySubfunctorObj (U i) a hi) ⟶
      (x j).hom.hom.obj (fibredCategorySubfunctorObj (U j) a hj) :=
  if hij : i = j then eqToHom (by subst hij; rfl) else
    Functor.Fiber.fiberInclusion.map
      ((Functor.IsStackInGroupoids.nonempty_iso_and_subsingleton_hom_of_bot_mem
        𝒳.property.choose_spec.1.2 (hdisj i j hij a.fiber.as hi hj)
        (Functor.Fiber.mk (p_obj_obj_fibredCategorySubfunctorObj U hU x i a hi))
        (Functor.Fiber.mk (p_obj_obj_fibredCategorySubfunctorObj U hU x j a hj))).1.some.hom)

/-- The transition morphism `disjointTransition` from `U i` to itself is the identity. -/
theorem disjointTransition_self (i : ι) (a : (fibredCategory B S hS Z).val.obj)
    (hi hi' : a.fiber.as ∈ (U i).obj (op a.base)) :
    disjointTransition U hU x hdisj i i a hi hi' = 𝟙 _ := by
  unfold disjointTransition
  exact (dite_eq_left rfl).trans (eqToHom_refl _ _)

/-- Each transition morphism `disjointTransition U hU x hdisj i j a hi hj` lies over the identity
of `a.base`. -/
theorem isHomLift_disjointTransition (i j : ι) (a : (fibredCategory B S hS Z).val.obj)
    (hi : a.fiber.as ∈ (U i).obj (op a.base)) (hj : a.fiber.as ∈ (U j).obj (op a.base)) :
    𝒳.val.val.p.IsHomLift (𝟙 a.base) (disjointTransition U hU x hdisj i j a hi hj) := by
  by_cases hij : i = j
  · subst hij
    rw [disjointTransition_self]
    exact IsHomLift.id (p_obj_obj_fibredCategorySubfunctorObj U hU x i a hi)
  · classical
    unfold disjointTransition
    exact isHomLift_dite_of_not _ _ hij (Subtype.property _)

include hdisj in
/-- **Gluing 1-morphisms out of an algebraic space along a cover whose members meet only over
objects of the site covered by the empty sieve.** No transition data is needed: over such an
object the fibre of the algebraic stack `𝒳` is equivalent to the point, so the transitions of
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_algebraicSpaceStack_hom_of_cocycle` are forced,
and they are natural and satisfy the cocycle condition by uniqueness. -/
theorem exists_algebraicSpaceStack_hom_of_disjoint (hZ : IsAlgebraicSpace B S hS Z)
    (hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)), ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f → ∃ i, Z.map f.op z ∈ (U i).obj (op V)) :
    ∃ y : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳,
      ∀ i, Nonempty (algebraicSpaceStackMap.{u, w} B S hS (hU i) hZ (U i).ι ≫ y ≅ x i) := by
  have h𝒳 := 𝒳.property.choose_spec.1.2
  let φ := disjointTransition U hU x hdisj
  have hlift : ∀ i j a hi hj, 𝒳.val.val.p.IsHomLift (𝟙 a.base) (φ i j a hi hj) :=
    isHomLift_disjointTransition U hU x hdisj
  have hnat : ∀ i j {a b : (fibredCategory B S hS Z).val.obj} (n : a ⟶ b) hai haj hbi hbj,
      (x i).hom.hom.map (fibredCategorySubfunctorHom (U i) n hai hbi) ≫ φ i j b hbi hbj =
        φ i j a hai haj ≫ (x j).hom.hom.map (fibredCategorySubfunctorHom (U j) n haj hbj) := by
    intro i j a b n hai haj hbi hbj
    by_cases hij : i = j
    · subst hij
      simp only [φ, disjointTransition_self, Category.comp_id, Category.id_comp]
    · have hl : ∀ k (hak : a.fiber.as ∈ (U k).obj (op a.base))
          (hbk : b.fiber.as ∈ (U k).obj (op b.base)),
          𝒳.val.val.p.IsHomLift n.base
            ((x k).hom.hom.map (fibredCategorySubfunctorHom (U k) n hak hbk)) := by
        intro k hak hbk
        have h2 : (fibredCategory B S hS (U k).toFunctor).val.p.IsHomLift n.base
            (fibredCategorySubfunctorHom (U k) n hak hbk) := by
          change (fibredCategory B S hS (U k).toFunctor).val.p.IsHomLift
            ((fibredCategory B S hS (U k).toFunctor).val.p.map
              (fibredCategorySubfunctorHom (U k) n hak hbk))
            (fibredCategorySubfunctorHom (U k) n hak hbk)
          exact IsHomLift.map _ _
        exact BasedFunctor.preserves_isHomLift (x k).hom.hom n.base _
      have := hl i hai hbi
      have := hl j haj hbj
      have := hlift i j a hai haj
      have := hlift i j b hbi hbj
      exact Functor.IsStackInGroupoids.eq_of_isHomLift_of_bot_mem h𝒳
        (hdisj i j hij a.fiber.as hai haj) n.base _ _
  have hcoc : ∀ i j k a hi hj hk, φ i j a hi hj ≫ φ j k a hj hk = φ i k a hi hk := by
    intro i j k a hi hj hk
    by_cases hij : i = j
    · subst hij
      simp only [φ, disjointTransition_self, Category.id_comp]
    by_cases hjk : j = k
    · subst hjk
      simp only [φ, disjointTransition_self, Category.comp_id]
    have := hlift i j a hi hj
    have := hlift j k a hj hk
    have := hlift i k a hi hk
    exact Functor.IsStackInGroupoids.eq_of_isHomLift_of_bot_mem h𝒳
      (hdisj i j hij a.fiber.as hi hj) (𝟙 a.base) _ _
  exact exists_algebraicSpaceStack_hom_of_cocycle hZ U hU x φ hlift hnat hcoc hcov

end Disjoint

section

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
  {W : Subfunctor Y} {hW : Space.IsOpenSubspace B S hS W}
  {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀} {q₀ : Y₀ ⟶ Y}

/-- A section cover of a subfunctor is a section cover of its set of points. -/
theorem hasSectionCoverOver_iff_points (V₀ : Subfunctor Y₀) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V₀ ↔
      HasSectionCoverOverPoints hY f W hW hY₀ q₀
        (Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι)) :=
  Iff.rfl

/-- Section covers of sets of points are monotone. -/
theorem HasSectionCoverOverPoints.mono {P P' : Set (Space.points B S hS Y₀)}
    (h : HasSectionCoverOverPoints hY f W hW hY₀ q₀ P) (hP : P' ⊆ P) :
    HasSectionCoverOverPoints hY f W hW hY₀ q₀ P' := by
  obtain ⟨Y', hY', p, hp, hx, hcov⟩ := h
  exact ⟨Y', hY', p, hp, hx, hP.trans hcov⟩

/-- **The coproduct of finitely many section covers.** For finitely many proper morphisms
`p i : Y' i ⟶ Y₀` of algebraic spaces, each with a section over `(p i ≫ q₀)⁻¹(W)`, the coproduct
sheaf `Y' = ∐ Y' i` with the morphism `p = [p i] : Y' ⟶ Y₀` is a section cover over `q₀` of the
union of the sets of points covered by the `p i`.

`Y'` is an algebraic space (Stacks 040T) and `p` is proper. The section over
`(p ≫ q₀)⁻¹(W)` is glued from the given ones along the ranges of the legs, which cover `Y'`
locally; two different legs meet only over objects of the site with empty underlying scheme,
where the stack `𝒳` has a unique isomorphism between any two objects, and these isomorphisms are
the transition data. -/
theorem HasSectionCoverOverPoints.iUnion_of_finite {I : Type u} [Finite I]
    (Y' : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY' : ∀ i, IsAlgebraicSpace B S hS (Y' i))
    (p : ∀ i, Y' i ⟶ Y₀) (hp : ∀ i, Space.IsProper B S hS (p i))
    (hx : ∀ i, HasSectionAlong hY f W hW (hY' i) (p i ≫ q₀)) :
    HasSectionCoverOverPoints hY f W hW hY₀ q₀
      (⋃ i, Space.pointsMap B S hS (Y' i) (p i) '' (Space.pointsMap B S hS (Y' i) (p i ≫ q₀) ⁻¹'
        Set.range (Space.pointsMap B S hS W.toFunctor W.ι))) := by
  classical
  let J := BigFppfOver.topology B S hS
  have _ : EssentiallySmall.{u} (BigFppfOver B S hS) := essentiallySmall_bigFppfOver B S hS
  let _ : HasSheafify J (Type u) := hasSheafifyEssentiallySmallSite.{_, _, _, _, u} J (Type u)
  have _ : HasFiniteCoproducts (Sheaf J (Type u)) := inferInstance
  have _ : HasColimitsOfShape (Discrete I) (Sheaf J (Type u)) :=
    CategoryTheory.Limits.hasColimitsOfShape_discrete _ I
  let Fs : I → Sheaf J (Type u) := fun i => ⟨Y' i, (hY' i).isSheaf⟩
  let ιs : ∀ i, Fs i ⟶ ∐ Fs := Sigma.ι Fs
  have hP : IsColimit (Cofan.mk (∐ Fs) ιs) := coproductIsCoproduct Fs
  have hPalg : IsAlgebraicSpace B S hS (∐ Fs).obj :=
    Space.isAlgebraicSpace_finiteCoproduct B S hS Y' hY' (∐ Fs) ιs hP
  let tgt : ∀ i, Fs i ⟶ (⟨Y₀, hY₀.isSheaf⟩ : Sheaf J (Type u)) := fun i => ⟨p i⟩
  let π : (∐ Fs).obj ⟶ Y₀ := (Cofan.IsColimit.desc hP tgt).hom
  have hfac : ∀ i, (ιs i).hom ≫ π = p i := fun i =>
    congrArg (fun k : Fs i ⟶ (⟨Y₀, hY₀.isSheaf⟩ : Sheaf J (Type u)) => k.hom)
      (Cofan.IsColimit.fac hP tgt i)
  have hfac' : ∀ i, (ιs i).hom ≫ π ≫ q₀ = p i ≫ q₀ := fun i => by
    rw [← Category.assoc, hfac i]
  have hπ : Space.IsProper B S hS π :=
    Space.isProper_of_isColimit_cofan B S hS ιs hP hY' hPalg hY₀ π fun i => by
      rw [hfac i]
      exact hp i
  refine ⟨(∐ Fs).obj, hPalg, π, hπ, ?_, ?_⟩
  swap
  · intro v hv
    obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hv
    refine ⟨Space.pointsMap B S hS (Y' i) (ιs i).hom z, ?_, ?_⟩
    · rwa [Set.mem_preimage, ← Space.pointsMap_comp_apply, ← Category.assoc, hfac i]
    · rw [← Space.pointsMap_comp_apply, hfac i]
  let Z := W.preimage (π ≫ q₀)
  have hZ : IsAlgebraicSpace B S hS Z.toFunctor :=
    (Space.isOpenSubspace_preimage B S hS (π ≫ q₀) W hY hPalg hW).1
  let Zi : ∀ i, Subfunctor (Y' i) := fun i => W.preimage (p i ≫ q₀)
  have hZi : ∀ i, IsAlgebraicSpace B S hS (Zi i).toFunctor := fun i =>
    (Space.isOpenSubspace_preimage B S hS (p i ≫ q₀) W hY (hY' i) hW).1
  have hmemZ : ∀ i, Subfunctor.range ((Zi i).ι ≫ (ιs i).hom) ≤ Z := by
    rintro i T _ ⟨w, rfl⟩
    change ((ιs i).hom ≫ π ≫ q₀).app T ((Zi i).ι.app T w) ∈ W.obj T
    rw [hfac' i]
    exact w.2
  let m : ∀ i, (Zi i).toFunctor ⟶ Z.toFunctor := fun i => Z.lift _ (hmemZ i)
  have hm : ∀ i, m i ≫ Z.ι = (Zi i).ι ≫ (ιs i).hom := fun i => Z.lift_ι _ (hmemZ i)
  have : ∀ i, Mono (m i) := fun i => by
    have := AlgebraicGeometry.Sheaf.mono_hom_cofan_inj ιs hP i
    have : Mono ((Zi i).ι ≫ (ιs i).hom) := mono_comp _ _
    rw [← hm i] at this
    exact mono_of_mono _ Z.ι
  let U : I → Subfunctor Z.toFunctor := fun i => Subfunctor.range (m i)
  have hU : ∀ i, IsAlgebraicSpace B S hS (U i).toFunctor := fun i =>
    (hZi i).of_iso (asIso (Subfunctor.toRange (m i)))
  let e : ∀ i, (U i).toFunctor ⟶ (Zi i).toFunctor := fun i => inv (Subfunctor.toRange (m i))
  have he : ∀ i, e i ≫ (Zi i).ι ≫ p i ≫ q₀ = (U i).ι ≫ Z.ι ≫ π ≫ q₀ := by
    intro i
    rw [IsIso.inv_comp_eq, ← Category.assoc (Subfunctor.toRange (m i)), Subfunctor.toRange_ι,
      ← Category.assoc (m i), hm i, Category.assoc, hfac' i]
  choose x hxf using hx
  let x' : ∀ i, algebraicSpaceStack.{u, w} B S hS (U i).toFunctor (hU i) ⟶ 𝒳 := fun i =>
    algebraicSpaceStackMap.{u, w} B S hS (hU i) (hZi i) (e i) ≫ x i
  have hx'f : ∀ i, x' i ≫ f = algebraicSpaceStackMap.{u, w} B S hS (hU i) hY
      ((U i).ι ≫ Z.ι ≫ π ≫ q₀) := by
    intro i
    rw [Category.assoc, hxf i, ← he i,
      algebraicSpaceStackMap_comp B S hS (hU i) (hZi i) hY (e i) ((Zi i).ι ≫ p i ≫ q₀)]
  have hcov : ∀ (T : BigFppfOver B S hS) (z : Z.toFunctor.obj (op T)),
      ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃g : V ⟶ T⦄,
        R.arrows g → ∃ i, Z.toFunctor.map g.op z ∈ (U i).obj (op V) := by
    intro T z
    have hz : Z.ι.app (op T) z ∈ ((⨆ i, Subfunctor.range (ιs i).hom).sheafify J).obj (op T) := by
      rw [Sheaf.sheafify_iSup_range_eq_top J ιs hP]
      trivial
    refine ⟨_, hz, fun V g hg => ?_⟩
    have hg' : (∐ Fs).obj.map g.op (Z.ι.app (op T) z) ∈
        (⨆ i, Subfunctor.range (ιs i).hom).obj (op V) := hg
    rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hg'
    obtain ⟨i, w, hw⟩ := hg'
    have hwZ : w ∈ (Zi i).obj (op V) := by
      change (p i ≫ q₀).app (op V) w ∈ W.obj (op V)
      rw [← hfac' i]
      change (π ≫ q₀).app (op V) ((ιs i).hom.app (op V) w) ∈ W.obj (op V)
      rw [hw]
      exact (Z.toFunctor.map g.op z).2
    exact ⟨i, ⟨w, hwZ⟩, Subtype.ext hw⟩
  have hdisj : ∀ i j, i ≠ j → ∀ {T : BigFppfOver B S hS} (z : Z.toFunctor.obj (op T)),
      z ∈ (U i).obj (op T) → z ∈ (U j).obj (op T) →
        (⊥ : Sieve T) ∈ BigFppfOver.topology B S hS T := by
    rintro i j hij T z ⟨a, rfl⟩ ⟨b, hb⟩
    refine BigFppfOver.bot_mem_topology T
      (Sheaf.isEmpty_toScheme_of_eq_of_ne ιs hP hij ((Zi i).ι.app _ a) ((Zi j).ι.app _ b) ?_)
    have h1 := congrArg (fun k : (Zi i).toFunctor ⟶ (∐ Fs).obj => k.app (op T) a) (hm i)
    have h2 := congrArg (fun k : (Zi j).toFunctor ⟶ (∐ Fs).obj => k.app (op T) b) (hm j)
    exact h1.symm.trans ((congrArg (Z.ι.app (op T)) hb.symm).trans h2)
  obtain ⟨y, hy⟩ := exists_algebraicSpaceStack_hom_of_disjoint U hU x' hdisj hZ hcov
  refine ⟨y, algebraicSpaceStack_hom_ext_of_cover hZ hY U hU hcov fun i => ?_⟩
  obtain ⟨ei⟩ := hy i
  have h1 : (algebraicSpaceStackMap.{u, w} B S hS (hU i) hZ (U i).ι ≫ y) ≫ f = x' i ≫ f :=
    Bicategory.InducedBicategory.hom_ext
      (hom_eq_of_hom₂ B S hS (Bicategory.whiskerRight ei.hom f).hom)
  rw [← Category.assoc, h1, hx'f i, ← algebraicSpaceStackMap_comp]

/-- **A section cover of the empty set of points**: the coproduct over the empty index type. -/
theorem HasSectionCoverOverPoints.empty :
    HasSectionCoverOverPoints hY f W hW hY₀ q₀ ∅ :=
  (HasSectionCoverOverPoints.iUnion_of_finite (I := PEmpty.{u + 1}) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)).mono
    (Set.empty_subset _)

/-- **The union of two section covers of sets of points**: the coproduct over a two-element
index type. -/
theorem HasSectionCoverOverPoints.union {P₁ P₂ : Set (Space.points B S hS Y₀)}
    (h₁ : HasSectionCoverOverPoints hY f W hW hY₀ q₀ P₁)
    (h₂ : HasSectionCoverOverPoints hY f W hW hY₀ q₀ P₂) :
    HasSectionCoverOverPoints hY f W hW hY₀ q₀ (P₁ ∪ P₂) := by
  obtain ⟨Y₁, hY₁, p₁, hp₁, hx₁, hcov₁⟩ := h₁
  obtain ⟨Y₂, hY₂, p₂, hp₂, hx₂, hcov₂⟩ := h₂
  let Y' : ULift.{u} Bool → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
    | ⟨false⟩ => Y₁
    | ⟨true⟩ => Y₂
  let hY' : ∀ b, IsAlgebraicSpace B S hS (Y' b)
    | ⟨false⟩ => hY₁
    | ⟨true⟩ => hY₂
  let p : ∀ b, Y' b ⟶ Y₀
    | ⟨false⟩ => p₁
    | ⟨true⟩ => p₂
  have hp : ∀ b, Space.IsProper B S hS (p b)
    | ⟨false⟩ => hp₁
    | ⟨true⟩ => hp₂
  have hx : ∀ b, HasSectionAlong hY f W hW (hY' b) (p b ≫ q₀)
    | ⟨false⟩ => hx₁
    | ⟨true⟩ => hx₂
  refine (HasSectionCoverOverPoints.iUnion_of_finite Y' hY' p hp hx).mono ?_
  rintro v (hv | hv)
  · exact Set.mem_iUnion.2 ⟨⟨false⟩, hcov₁ hv⟩
  · exact Set.mem_iUnion.2 ⟨⟨true⟩, hcov₂ hv⟩

/-- **A finite union of section covers of sets of points.** -/
theorem HasSectionCoverOverPoints.biUnion {ι : Type*} (s : Finset ι)
    (P : ι → Set (Space.points B S hS Y₀))
    (h : ∀ i ∈ s, HasSectionCoverOverPoints hY f W hW hY₀ q₀ (P i)) :
    HasSectionCoverOverPoints hY f W hW hY₀ q₀ (⋃ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasSectionCoverOverPoints.empty
  | insert i s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (Finset.mem_insert_self i s)).union
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **A section cover of a subfunctor without points.** -/
theorem HasSectionCoverOver.of_isEmpty {V₀ : Subfunctor Y₀}
    (hV₀ : IsEmpty (Space.points B S hS V₀.toFunctor)) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V₀ :=
  (HasSectionCoverOverPoints.empty (hY₀ := hY₀)).mono fun _ ⟨v, _⟩ => hV₀.elim v

/-- **The union of two section covers.** A subfunctor `V ⊆ Y₀` whose points are covered by those
of two subfunctors `V₁`, `V₂` with section covers over `q₀` has a section cover over `q₀`. -/
theorem HasSectionCoverOver.union {V₁ V₂ : Subfunctor Y₀}
    (h₁ : HasSectionCoverOver hY f W hW hY₀ q₀ V₁)
    (h₂ : HasSectionCoverOver hY f W hW hY₀ q₀ V₂) {V : Subfunctor Y₀}
    (hV : Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ⊆
      Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι) ∪
        Set.range (Space.pointsMap B S hS V₂.toFunctor V₂.ι)) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V :=
  (HasSectionCoverOverPoints.union (hY₀ := hY₀) h₁ h₂).mono hV

/-- **A finite union of section covers.** A subfunctor `V₀ ⊆ Y₀` whose points are covered by
those of finitely many subfunctors `V i` with section covers over `q₀` has a section cover over
`q₀`. -/
theorem HasSectionCoverOver.iUnion {ι : Type*} [Finite ι] (V : ι → Subfunctor Y₀)
    (h : ∀ i, HasSectionCoverOver hY f W hW hY₀ q₀ (V i)) (V₀ : Subfunctor Y₀)
    (hV : Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) ⊆
      ⋃ i, Set.range (Space.pointsMap B S hS (V i).toFunctor (V i).ι)) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V₀ := by
  have := Fintype.ofFinite ι
  refine (HasSectionCoverOverPoints.biUnion (hY₀ := hY₀) Finset.univ _ fun i _ => h i).mono ?_
  simpa using hV

end

end AlgebraicGeometry.Stack.AlgebraicStacks

end

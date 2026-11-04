module

public import Mathlib.CategoryTheory.Limits.Final
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksCore.Tactic.StacksAttribute

/-!
# Compactifications with dense interior

Let `S` be a quasi-compact and quasi-separated scheme and let `X` be a scheme over `S` which is
compactifiable over `S`. Among the compactifications of `X` over `S` are those whose interior is
dense and scheme-theoretically dense in the ambient proper scheme. There are enough of them: the
scheme-theoretic closure of the interior inside any compactification is again a compactification,
with the same interior, now dense; and a compactification whose interior is scheme-theoretically
dense admits *at most one* morphism to any other compactification, because two such morphisms
agree on the interior and the target is separated over the base. Those two facts give both the
cofilteredness of the category of compactifications and the initiality of the dense ones.

## Main definitions

* `AlgebraicGeometry.HasDenseInterior` is the property of a compactification that its interior is
  dense and scheme-theoretically dense in the ambient scheme.
* `AlgebraicGeometry.CategoryOfCompactifications.interiorClosure` is the scheme-theoretic closure
  of the interior inside a compactification, with
  `...interiorClosureHom` the morphism to the given compactification.
* `AlgebraicGeometry.CategoryOfCompactifications.commonRefinement` is the scheme-theoretic
  closure of the interior inside the fibre product of two compactifications over the base, with
  `...commonRefinementFst` and `...commonRefinementSnd` its two projections.

## Main results

* `AlgebraicGeometry.CategoryOfCompactifications.hom_ext_of_hasDenseInterior`: a compactification
  with scheme-theoretically dense interior admits at most one morphism to a given
  compactification.
* `AlgebraicGeometry.CategoryOfCompactifications.isCofiltered_category` is part (a) of the source
  lemma: the category of compactifications is cofiltered.
* `AlgebraicGeometry.CategoryOfCompactifications.initial_ι_hasDenseInterior` is part (b): the
  full subcategory of compactifications with dense interior is initial.

Part (c) is `AlgebraicGeometry.preimage_range_immersion_eq` of
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/Compactifications.lean`.

## Implementation notes

The notion of an initial functor in the sense of Categories, Definition 4.17.3
([Stacks, Tag 09WP]) is `CategoryTheory.Functor.Initial`, which carries that tag in
`StacksCore/CategoryTheory/FinalFunctors.lean`; "the full subcategory is initial" is initiality of
its inclusion functor `CategoryTheory.ObjectProperty.ι`. Cofilteredness in the sense of
Categories, Definition 4.21.1 ([Stacks, Tag 04AZ]) is `CategoryTheory.IsCofiltered`, compared
with the source's formulation in `StacksFrontier/CategoryTheory/Filtered/Cofiltered.lean`.

That a morphism into the fibre product is an immersion is `AlgebraicGeometry.IsImmersion.of_comp`
applied to the first projection; no separatedness is needed, so the graph construction of the
source's proof is not required. Quasi-compactness of the morphisms whose scheme-theoretic image
is taken comes from `AlgebraicGeometry.quasiCompact_of_compactSpace`: the interior is a compact
space because some compactification of it is quasi-compact over a proper scheme over a compact
base, and the fibre product is quasi-separated because it is proper over the quasi-separated
base.

`initial_of_exists_hom_of_exists_refinement` is the dual of
`CategoryTheory.Functor.final_of_exists_hom_of_exists_refinement` of
`StacksFrontier/CategoryTheory/Limits/FinalFromRefinement.lean`. It is kept `private` here rather
than added next to its sibling, which is outside the scope of this change; it should be moved
there when that file is next touched.

## References

* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 01RH](https://stacks.math.columbia.edu/tag/01RH)
* [Stacks Project, Tag 04AZ](https://stacks.math.columbia.edu/tag/04AZ)
* [Stacks Project, Tag 09WP](https://stacks.math.columbia.edu/tag/09WP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u

/-- **Initiality from nonemptiness and common refinements.** The dual of
`CategoryTheory.Functor.final_of_exists_hom_of_exists_refinement`: if every object of `E`
receives a morphism from the image of `u`, and any two such morphisms `a₁ : u(Y₁) ⟶ X` and
`a₂ : u(Y₂) ⟶ X` are dominated by a third, then `u` is initial. -/
private theorem initial_of_exists_hom_of_exists_refinement
    {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E] (u : C ⥤ E)
    (h₁ : ∀ X : E, ∃ Y : C, Nonempty (u.obj Y ⟶ X))
    (h₂ : ∀ (X : E) (Y₁ Y₂ : C) (a₁ : u.obj Y₁ ⟶ X) (a₂ : u.obj Y₂ ⟶ X),
      ∃ (Y : C) (q₁ : Y ⟶ Y₁) (q₂ : Y ⟶ Y₂) (a : u.obj Y ⟶ X),
        u.map q₁ ≫ a₁ = a ∧ u.map q₂ ≫ a₂ = a) :
    u.Initial := by
  refine ⟨fun X => ?_⟩
  obtain ⟨Y₀, ⟨f₀⟩⟩ := h₁ X
  have : Nonempty (CostructuredArrow u X) := ⟨CostructuredArrow.mk f₀⟩
  refine zigzag_isConnected fun j₁ j₂ => ?_
  obtain ⟨Y, q₁, q₂, a, hq₁, hq₂⟩ := h₂ X j₁.left j₂.left j₁.hom j₂.hom
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (Or.inr ⟨(CostructuredArrow.homMk q₁ hq₁ : CostructuredArrow.mk a ⟶ j₁)⟩))
    (Relation.ReflTransGen.single
      (Or.inl ⟨(CostructuredArrow.homMk q₂ hq₂ : CostructuredArrow.mk a ⟶ j₂)⟩))

namespace AlgebraicGeometry

/-- A compactification *has dense interior* when its interior is both topologically dense and
scheme-theoretically dense in the ambient scheme. -/
def HasDenseInterior {S : Scheme.{u}} (X : Over S) : ObjectProperty (CompactificationOf X) :=
  fun j =>
    IsDominant j.immersion ∧ Scheme.Opens.IsSchemeTheoreticallyDense j.immersion.opensRange

namespace CategoryOfCompactifications

variable (D : CategoryOfCompactifications.{u})

/-- The interior of a compactifiable scheme over a quasi-compact base is a compact space. -/
instance compactSpace_interior : CompactSpace D.X.left := by
  obtain ⟨j, hj⟩ := D.exists_quasiCompact_compactification
  let := hj
  let : CompactSpace j.space := QuasiCompact.compactSpace_of_compactSpace j.toBase
  exact QuasiCompact.compactSpace_of_compactSpace j.immersion

/-- The ambient scheme of a compactification is quasi-separated. -/
instance quasiSeparatedSpace_ambient (j : D.category) : QuasiSeparatedSpace j.space :=
  quasiSeparatedSpace_of_quasiSeparated j.toBase

/-- The scheme-theoretic closure of the interior inside a compactification: the interior is an
open subscheme of it, now dense, and it is again proper over the base. -/
def interiorClosure (j : D.category) : D.category :=
  ⟨StructuredArrow.mk (Y := Over.mk (j.immersion.imageι ≫ j.toBase))
      (Over.homMk j.immersion.toImage (by
        change j.immersion.toImage ≫ j.immersion.imageι ≫ j.toBase = D.X.hom
        rw [← Category.assoc, Scheme.Hom.toImage_imageι]
        simp [CompactificationOf.immersion, CompactificationOf.toBase])),
    ⟨isOpenImmersion_toImage j.immersion (Or.inl inferInstance),
      show IsProper (j.immersion.imageι ≫ j.toBase) from inferInstance⟩⟩

/-- The canonical morphism from the scheme-theoretic closure of the interior to the given
compactification. -/
def interiorClosureHom (j : D.category) : interiorClosure D j ⟶ j :=
  ObjectProperty.homMk (StructuredArrow.homMk (Over.homMk j.immersion.imageι rfl) (by
    apply Over.OverMorphism.ext
    simp only [Functor.id_obj, Functor.id_map, Over.comp_left, Over.homMk_left, interiorClosure,
      StructuredArrow.mk_hom_eq_self]
    exact j.immersion.toImage_imageι))

/-! ### The common refinement of two compactifications -/

section CommonRefinement

variable (j k : D.category)

/-- The fibre product of the ambient schemes of two compactifications is quasi-separated. -/
instance quasiSeparatedSpace_pullback_ambient :
    QuasiSeparatedSpace (pullback j.toBase k.toBase : Scheme.{u}) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst j.toBase k.toBase ≫ j.toBase)

/-- The morphism from the interior into the fibre product of two compactifications of it. -/
def commonRefinementMap : D.X.left ⟶ (pullback j.toBase k.toBase : Scheme.{u}) :=
  pullback.lift j.immersion k.immersion
    (by simp [CompactificationOf.immersion, CompactificationOf.toBase])

/-- The first projection recovers the first open immersion. -/
lemma commonRefinementMap_fst :
    commonRefinementMap D j k ≫ pullback.fst j.toBase k.toBase = j.immersion :=
  pullback.lift_fst _ _ _

/-- The second projection recovers the second open immersion. -/
lemma commonRefinementMap_snd :
    commonRefinementMap D j k ≫ pullback.snd j.toBase k.toBase = k.immersion :=
  pullback.lift_snd _ _ _

/-- The morphism into the fibre product is an immersion, because its composite with the first
projection is the open immersion of the first compactification. -/
instance isImmersion_commonRefinementMap : IsImmersion (commonRefinementMap D j k) := by
  have h : IsImmersion (commonRefinementMap D j k ≫ pullback.fst j.toBase k.toBase) := by
    rw [commonRefinementMap_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst j.toBase k.toBase)

/-- The interior maps to the base through the common refinement as it does directly. -/
lemma commonRefinementMap_toImage_imageι_fst_toBase :
    (commonRefinementMap D j k).toImage ≫ (commonRefinementMap D j k).imageι ≫
      pullback.fst j.toBase k.toBase ≫ j.toBase = D.X.hom := by
  rw [← Category.assoc, ← Category.assoc, Scheme.Hom.toImage_imageι, commonRefinementMap_fst]
  simp [CompactificationOf.immersion, CompactificationOf.toBase]

/-- The common refinement of two compactifications: the scheme-theoretic interiorClosure of the
interior inside their fibre product over the base. -/
def commonRefinement : D.category :=
  ⟨StructuredArrow.mk (Y := Over.mk ((commonRefinementMap D j k).imageι ≫
      pullback.fst j.toBase k.toBase ≫ j.toBase))
      (Over.homMk (commonRefinementMap D j k).toImage
        (commonRefinementMap_toImage_imageι_fst_toBase D j k)),
    ⟨isOpenImmersion_toImage (commonRefinementMap D j k) (Or.inl inferInstance),
      show IsProper ((commonRefinementMap D j k).imageι ≫
        pullback.fst j.toBase k.toBase ≫ j.toBase) from inferInstance⟩⟩

/-- The projection of the common refinement to the first compactification. -/
def commonRefinementFst : commonRefinement D j k ⟶ j :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk ((commonRefinementMap D j k).imageι ≫ pullback.fst j.toBase k.toBase)
      (Category.assoc _ _ _)) (by
    apply Over.OverMorphism.ext
    simp only [Functor.id_obj, Functor.id_map, Over.comp_left, Over.homMk_left, commonRefinement,
      StructuredArrow.mk_hom_eq_self, ← Category.assoc, Scheme.Hom.toImage_imageι]
    exact commonRefinementMap_fst D j k))

/-- The projection of the common refinement to the second compactification. -/
def commonRefinementSnd : commonRefinement D j k ⟶ k :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk ((commonRefinementMap D j k).imageι ≫ pullback.snd j.toBase k.toBase)
      (by
        change ((commonRefinementMap D j k).imageι ≫ pullback.snd j.toBase k.toBase) ≫ k.toBase =
          (commonRefinementMap D j k).imageι ≫ pullback.fst j.toBase k.toBase ≫ j.toBase
        rw [Category.assoc, ← pullback.condition])) (by
    apply Over.OverMorphism.ext
    simp only [Functor.id_obj, Functor.id_map, Over.comp_left, Over.homMk_left, commonRefinement,
      StructuredArrow.mk_hom_eq_self, ← Category.assoc, Scheme.Hom.toImage_imageι]
    exact commonRefinementMap_snd D j k))

end CommonRefinement

/-! ### Density, rigidity, cofilteredness and initiality -/

/-- The scheme-theoretic closure of the interior has dense interior. -/
lemma hasDenseInterior_interiorClosure (j : D.category) :
    HasDenseInterior D.X (interiorClosure D j) :=
  ⟨isDominant_toImage j.immersion (Or.inl inferInstance),
    isSchemeTheoreticallyDense_toImage j.immersion (Or.inl inferInstance)⟩

/-- The common refinement of two compactifications has dense interior. -/
lemma hasDenseInterior_commonRefinement (j k : D.category) :
    HasDenseInterior D.X (commonRefinement D j k) :=
  ⟨isDominant_toImage (commonRefinementMap D j k) (Or.inl inferInstance),
    isSchemeTheoreticallyDense_toImage (commonRefinementMap D j k) (Or.inl inferInstance)⟩

/-- There is at most one morphism out of a compactification whose interior is
scheme-theoretically dense: two such morphisms agree on the interior, and the target is
separated over the base. -/
@[ega "IV 11.10.1" "(a) ⇒ (d), special case"]
theorem hom_ext_of_hasDenseInterior {j k : D.category} (hj : HasDenseInterior D.X j)
    (a b : j ⟶ k) : a = b := by
  have key (c : j ⟶ k) : j.immersion ≫ CompactificationOf.Hom.map c = k.immersion := by
    simpa [CompactificationOf.Hom.map] using congrArg (Over.forget D.S).map c.hom.w
  apply ObjectProperty.hom_ext
  apply StructuredArrow.ext
  refine eq_of_isSchemeTheoreticallyDense a.hom.right b.hom.right
    j.immersion.opensRange hj.2 ?_
  rw [← cancel_epi j.immersion.isoOpensRange.hom, ← Category.assoc, ← Category.assoc,
    j.immersion.isoOpensRange_hom_ι]
  exact (key a).trans (key b).symm

/-- The category of compactifications satisfies the two cone axioms: the common refinement for
objects, and the closure of the interior for parallel morphisms. -/
@[sga "4 XVII 3.2.6" "(ii)"]
instance isCofilteredOrEmpty_category : IsCofilteredOrEmpty D.category where
  cone_objs j k :=
    ⟨commonRefinement D j k, commonRefinementFst D j k, commonRefinementSnd D j k, trivial⟩
  cone_maps {j _} _ _ :=
    ⟨interiorClosure D j, interiorClosureHom D j,
      hom_ext_of_hasDenseInterior D (hasDenseInterior_interiorClosure D j) _ _⟩

/-- The category of compactifications of a scheme over a quasi-compact, quasi-separated base is
cofiltered. -/
@[stacks 0ATU "part (a)"]
theorem isCofiltered_category : IsCofiltered D.category :=
  @IsCofiltered.mk _ _ (isCofilteredOrEmpty_category D) inferInstance

/-- The scheme-theoretic closure of the interior of a compactification, as an object of the
full subcategory of compactifications with dense interior. -/
def interiorClosureDense (j : D.category) : (HasDenseInterior D.X).FullSubcategory :=
  ⟨interiorClosure D j, hasDenseInterior_interiorClosure D j⟩

/-- The common refinement of two compactifications, as an object of the full subcategory of
compactifications with dense interior. -/
def commonRefinementDense (j k : D.category) : (HasDenseInterior D.X).FullSubcategory :=
  ⟨commonRefinement D j k, hasDenseInterior_commonRefinement D j k⟩

/-- The full subcategory of compactifications whose interior is dense and scheme-theoretically
dense is initial. -/
@[stacks 0ATU "part (b)"]
theorem initial_ι_hasDenseInterior : (HasDenseInterior D.X).ι.Initial := by
  refine initial_of_exists_hom_of_exists_refinement _
    (fun j => ⟨interiorClosureDense D j, ⟨interiorClosureHom D j⟩⟩) ?_
  intro j Y₁ Y₂ a₁ a₂
  refine ⟨commonRefinementDense D Y₁.obj Y₂.obj,
    ObjectProperty.homMk (commonRefinementFst D Y₁.obj Y₂.obj),
    ObjectProperty.homMk (commonRefinementSnd D Y₁.obj Y₂.obj),
    commonRefinementFst D Y₁.obj Y₂.obj ≫ a₁, rfl,
    hom_ext_of_hasDenseInterior D (hasDenseInterior_commonRefinement D Y₁.obj Y₂.obj) _ _⟩

end CategoryOfCompactifications

end AlgebraicGeometry

end

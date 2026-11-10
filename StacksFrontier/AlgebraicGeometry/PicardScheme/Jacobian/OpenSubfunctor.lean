module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open subfunctors of a presheaf on schemes over a base

Let `P` be a presheaf of sets on the category of schemes over `S`. A subfunctor `F ⊆ P` is
*open* ([Stacks, Tag 01JI]) when for every `S`-scheme `T` and every `x ∈ P(T)` there is an open
`U ⊆ T` such that for every morphism of `S`-schemes `g : T' ⟶ T` the restriction of `x` to `T'`
lies in `F(T')` exactly when `g` maps `T'` into `U`. This file proves that the inclusion of an
open subfunctor is then representable by open immersions in Mathlib's sense,
`(IsOpenImmersion.over).presheaf F.ι`, which is the hypothesis `hopen` of the group-scheme
criterion `AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor` (Tag 0B9Q).

## Main definitions

* `AlgebraicGeometry.IsOpenSubfunctor` — the condition above.

## Main results

* `AlgebraicGeometry.IsOpenSubfunctor.isOpenImmersion_presheaf_ι` — the inclusion of an open
  subfunctor is representable by open immersions.

## References

* [Stacks Project, Tag 01JI](https://stacks.math.columbia.edu/tag/01JI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {P : (Over S)ᵒᵖ ⥤ Type u}

/-- **An open subfunctor** ([Stacks, Tag 01JI]): every section of the ambient presheaf has an
open of its base where exactly the restrictions lying in the subfunctor live. -/
def IsOpenSubfunctor (F : Subfunctor P) : Prop :=
  ∀ (T : Over S) (x : P.obj (op T)), ∃ U : T.left.Opens, ∀ (T' : Over S) (g : T' ⟶ T),
    P.map g.op x ∈ F.obj (op T') ↔ Set.range g.left ⊆ (U : Set T.left)

/-- Being an open immersion on underlying schemes is invariant under isomorphism of arrows of
`S`-schemes. -/
instance respectsIso_isOpenImmersion_over : (IsOpenImmersion.over (X := S)).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun _ _ e hf =>
    (MorphismProperty.arrow_mk_iso_iff @IsOpenImmersion ((Over.forget S).mapArrow.mapIso e)).1 hf

namespace IsOpenSubfunctor

variable {F : Subfunctor P}

/-- The open `U` of `T`, regarded as a scheme over `S`. -/
private abbrev overOpen (T : Over S) (U : T.left.Opens) : Over S := Over.mk (U.ι ≫ T.hom)

/-- The inclusion of `U` into `T` over `S`. -/
private abbrev overOpenι (T : Over S) (U : T.left.Opens) : overOpen T U ⟶ T := Over.homMk U.ι rfl

private theorem isPullback (T : Over S) (x : P.obj (op T)) (U : T.left.Opens)
    (hU : ∀ (T' : Over S) (g : T' ⟶ T), P.map g.op x ∈ F.obj (op T') ↔
      Set.range g.left ⊆ (U : Set T.left))
    (z : F.toFunctor.obj (op (overOpen T U))) (hz : (z : P.obj _) = P.map (overOpenι T U).op x) :
    IsPullback (yonedaEquiv.symm z) (yoneda.map (overOpenι T U)) F.ι (yonedaEquiv.symm x) := by
  have hw : yonedaEquiv.symm z ≫ F.ι = yoneda.map (overOpenι T U) ≫ yonedaEquiv.symm x := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply]
    exact hz
  refine IsPullback.of_forall_isPullback_app fun W ↦ (Types.isPullback_iff _ _ _ _).mpr
    ⟨by simpa using NatTrans.congr_app hw W, ?_, ?_⟩
  · rintro c₁ c₂ ⟨-, h⟩
    exact (cancel_mono (overOpenι T U)).mp h
  · intro (β : F.toFunctor.obj W) (α : W.unop ⟶ T) h
    change (β : P.obj W) = P.map α.op x at h
    have hmem : P.map α.op x ∈ F.obj W := h ▸ β.2
    have hrange : Set.range α.left ⊆ Set.range U.ι.base := by
      simpa using (hU W.unop α).mp hmem
    let c : W.unop.left ⟶ U := IsOpenImmersion.lift U.ι α.left hrange
    have hc : c ≫ U.ι = α.left := IsOpenImmersion.lift_fac _ _ _
    let cO : W.unop ⟶ overOpen T U :=
      Over.homMk c (show c ≫ U.ι ≫ T.hom = W.unop.hom by rw [← Category.assoc, hc, Over.w α])
    have hcO : cO ≫ overOpenι T U = α := Over.OverMorphism.ext hc
    refine ⟨cO, ?_, hcO⟩
    apply Subtype.ext
    change P.map cO.op (z : P.obj _) = (β : P.obj W)
    rw [hz, h, ← Functor.map_comp_apply, ← op_comp, hcO]

/-- **The inclusion of an open subfunctor is representable by open immersions.** -/
theorem isOpenImmersion_presheaf_ι (hF : IsOpenSubfunctor F) :
    (IsOpenImmersion.over (X := S)).presheaf F.ι := by
  refine MorphismProperty.relative.of_exists fun T g ↦ ?_
  obtain ⟨x, rfl⟩ := yonedaEquiv.symm.surjective g
  obtain ⟨U, hU⟩ := hF T x
  exact ⟨overOpen T U, _, overOpenι T U,
    isPullback T x U hU ⟨P.map (overOpenι T U).op x, (hU _ _).2 (by simp)⟩ rfl,
    show IsOpenImmersion U.ι from inferInstance⟩

end IsOpenSubfunctor

end AlgebraicGeometry

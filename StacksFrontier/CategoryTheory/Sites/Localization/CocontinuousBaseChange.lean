module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.Localization.LocalizationComposite

/-!
# The base change map of a cocontinuous functor and a localization

Let `v : C ⥤ D` be a cocontinuous functor of small sites and `V` an object of `C`, with the
localized functor `v' = Over.post v : C/V ⥤ D/v(V)` and the localization functors
`j_V = Over.forget V`, `j_{v(V)} = Over.forget (v(V))`. The square `v' ⋙ j_{v(V)} = j_V ⋙ v`
commutes on the nose, so the restrictions along its two composites agree, and the mate of that
identity under the right Kan extension adjunctions of `v` and `v'` is a base change map
`j_{v(V)}^{-1}(v_* P) ⟶ v'_*(j_V^{-1} P)` of direct images (Stacks 03EG: unlike in the continuous
case it is not an isomorphism in general). Its further mate under the localization adjunctions
`j^{-1} ⊣ j_*` is the conjugate of the identity, hence invertible.

## Main definitions

* `CategoryTheory.Functor.overPostRanBaseChangeCocontinuousBaseChange`: the base change map of
  presheaves.
* `CategoryTheory.Functor.overPostSheafBaseChangeCocontinuousBaseChange`: the base change map of
  sheaves of sets.

## Main results

* `CategoryTheory.Functor.overPostRanBaseChange_counit_cocontinuousBaseChange`: its transpose
  along `v'` is the counit of `v` restricted to `C/V`.
* `CategoryTheory.Functor.overPostRanBaseChange_homEquiv_symm_cocontinuousBaseChange`: it carries
  the restriction of a map into `v_* B` to the restriction of its transpose.
* `CategoryTheory.Functor.isIso_mateEquiv_overPostSheafBaseChange_cocontinuousBaseChange`: the
  mate under the localization adjunctions is invertible.

## References

* [Stacks Project, Tag 03EG](https://stacks.math.columbia.edu/tag/03EG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.Functor

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (v : C ⥤ D) (V : C)

/-- The identity of the restrictions along the two composites of the square
`v' ⋙ j_{v(V)} = j_V ⋙ v`. -/
def overPostRestrictionSquareCocontinuousBaseChange :
    TwoSquare ((whiskeringLeft (Over (v.obj V))ᵒᵖ Dᵒᵖ (Type u)).obj (Over.forget (v.obj V)).op)
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj v.op)
      ((whiskeringLeft (Over V)ᵒᵖ (Over (v.obj V))ᵒᵖ (Type u)).obj (Over.post (X := V) v).op)
      ((whiskeringLeft (Over V)ᵒᵖ Cᵒᵖ (Type u)).obj (Over.forget V).op) where
  app P := 𝟙 ((Over.forget V).op ⋙ v.op ⋙ P)
  naturality _ _ _ := rfl

/-- The identity of the restrictions along the two composites of the square
`v' ⋙ j_{v(V)} = j_V ⋙ v` is an isomorphism. -/
instance : IsIso (overPostRestrictionSquareCocontinuousBaseChange v V).natTrans :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun P ↦
    inferInstanceAs (IsIso (𝟙 ((Over.forget V).op ⋙ v.op ⋙ P)))

/-- **The presheaf base change map** `j_{v(V)}^{-1} ⋙ v'_* ⟵ v_* ⋙ j_V^{-1}`: the mate, under the
right Kan extension adjunctions of `v` and of `v' = Over.post v`, of the equality of the
restrictions along `v' ⋙ j_{v(V)} = j_V ⋙ v`. -/
noncomputable def overPostRanBaseChangeCocontinuousBaseChange :
    TwoSquare (v.op.ran (H := Type u))
      ((whiskeringLeft (Over V)ᵒᵖ Cᵒᵖ (Type u)).obj (Over.forget V).op)
      ((whiskeringLeft (Over (v.obj V))ᵒᵖ Dᵒᵖ (Type u)).obj (Over.forget (v.obj V)).op)
      ((Over.post (X := V) v).op.ran (H := Type u)) :=
  mateEquiv (v.op.ranAdjunction (Type u)) ((Over.post (X := V) v).op.ranAdjunction (Type u))
    (overPostRestrictionSquareCocontinuousBaseChange v V)

/-- The transpose of the base change map along `v'` is the counit of the right Kan extension
along `v`, restricted to `C/V`. -/
theorem overPostRanBaseChange_counit_cocontinuousBaseChange (P : Cᵒᵖ ⥤ Type u) :
    ((whiskeringLeft (Over V)ᵒᵖ (Over (v.obj V))ᵒᵖ (Type u)).obj (Over.post (X := V) v).op).map
        ((overPostRanBaseChangeCocontinuousBaseChange v V).app P) ≫
        ((Over.post (X := V) v).op.ranAdjunction (Type u)).counit.app
          ((Over.forget V).op ⋙ P) =
      ((whiskeringLeft (Over V)ᵒᵖ Cᵒᵖ (Type u)).obj (Over.forget V).op).map
        ((v.op.ranAdjunction (Type u)).counit.app P) :=
  (mateEquiv_counit (v.op.ranAdjunction (Type u))
    ((Over.post (X := V) v).op.ranAdjunction (Type u))
    (overPostRestrictionSquareCocontinuousBaseChange v V) P).trans
    (Category.id_comp _)

/-- The base change map, as a transpose: it is the transpose along `v'` of the counit of the
right Kan extension along `v`, restricted to `C/V`. -/
theorem overPostRanBaseChange_app_cocontinuousBaseChange (P : Cᵒᵖ ⥤ Type u) :
    (overPostRanBaseChangeCocontinuousBaseChange v V).app P =
      ((Over.post (X := V) v).op.ranAdjunction (Type u)).homEquiv _ _
        (((whiskeringLeft (Over V)ᵒᵖ Cᵒᵖ (Type u)).obj (Over.forget V).op).map
          ((v.op.ranAdjunction (Type u)).counit.app P)) := by
  refine (Equiv.symm_apply_eq _).mp ?_
  rw [Adjunction.homEquiv_counit]
  exact overPostRanBaseChange_counit_cocontinuousBaseChange v V P

/-- **The base change map is compatible with transposes.** For `β : A ⟶ v_* B`, the
transpose along `v'` of the restriction of `β` followed by the base change map is the
restriction of the transpose of `β` along `v`. -/
theorem overPostRanBaseChange_homEquiv_symm_cocontinuousBaseChange {A : Dᵒᵖ ⥤ Type u}
    {B : Cᵒᵖ ⥤ Type u}
    (β : A ⟶ (v.op.ran (H := Type u)).obj B) :
    (((Over.post (X := V) v).op.ranAdjunction (Type u)).homEquiv _ _).symm
        (((whiskeringLeft (Over (v.obj V))ᵒᵖ Dᵒᵖ (Type u)).obj (Over.forget (v.obj V)).op).map β ≫
          (overPostRanBaseChangeCocontinuousBaseChange v V).app B) =
      ((whiskeringLeft (Over V)ᵒᵖ Cᵒᵖ (Type u)).obj (Over.forget V).op).map
        (((v.op.ranAdjunction (Type u)).homEquiv _ _).symm β) := by
  rw [overPostRanBaseChange_app_cocontinuousBaseChange, Adjunction.homEquiv_naturality_left_symm]
  refine (congrArg (_ ≫ ·) (Equiv.symm_apply_apply _ _)).trans ?_
  rw [Adjunction.homEquiv_counit, Functor.map_comp]
  rfl

/-- **The localization mate of the presheaf base change map is invertible**: by
`iterated_mateEquiv_conjugateEquiv` it is the conjugate of an identity. -/
theorem isIso_mateEquiv_overPostRanBaseChange_cocontinuousBaseChange :
    IsIso (mateEquiv ((Over.forget V).op.ranAdjunction (Type u))
      ((Over.forget (v.obj V)).op.ranAdjunction (Type u))
        (overPostRanBaseChangeCocontinuousBaseChange v V)).natTrans := by
  rw [overPostRanBaseChangeCocontinuousBaseChange, iterated_mateEquiv_conjugateEquiv]
  exact conjugateEquiv_iso _ _ _

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} [v.IsCocontinuous J K]

/-- **The base change map of sheaves of sets** `j_{v(V)}^{-1}(v_* P) ⟶ v'_*(j_V^{-1} P)` for a
cocontinuous `v` (Stacks 03EG), on underlying presheaves the presheaf base change map. -/
noncomputable def overPostSheafBaseChangeCocontinuousBaseChange :
    TwoSquare (v.sheafPushforwardCocontinuous (Type u) J K)
      ((Over.forget V).sheafPushforwardContinuous (Type u) (J.over V) J)
      ((Over.forget (v.obj V)).sheafPushforwardContinuous (Type u) (K.over (v.obj V)) K)
      ((Over.post (X := V) v).sheafPushforwardCocontinuous (Type u) (J.over V)
        (K.over (v.obj V))) :=
  TwoSquare.mk _ _ _ _
    { app := fun P ↦ ⟨(overPostRanBaseChangeCocontinuousBaseChange v V).app P.obj⟩
      naturality := fun _ _ g ↦
        Sheaf.hom_ext ((overPostRanBaseChangeCocontinuousBaseChange v V).naturality g.hom) }

/-- On the underlying presheaf of a sheaf `P`, the base change map of sheaves of sets is the
presheaf base change map at `P`. -/
@[simp]
theorem overPostSheafBaseChange_app_hom_cocontinuousBaseChange (P : Sheaf J (Type u)) :
    ((overPostSheafBaseChangeCocontinuousBaseChange v V (J := J) (K := K)).app P).hom =
      (overPostRanBaseChangeCocontinuousBaseChange v V).app P.obj := rfl

/-- The localization mate of the base change map of sheaves of sets is, on underlying presheaves,
the localization mate of the presheaf base change map. -/
theorem mateEquiv_overPostSheafBaseChange_app_hom_cocontinuousBaseChange
    (N : Sheaf (J.over V) (Type u)) :
    ((mateEquiv ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J)
        ((Over.forget (v.obj V)).sheafAdjunctionCocontinuous (Type u) (K.over (v.obj V)) K)
        (overPostSheafBaseChangeCocontinuousBaseChange v V)).app N).hom =
      (mateEquiv ((Over.forget V).op.ranAdjunction (Type u))
        ((Over.forget (v.obj V)).op.ranAdjunction (Type u))
        (overPostRanBaseChangeCocontinuousBaseChange v V)).app N.obj := by
  have h₁ : ∀ {P Q : Sheaf (K.over (v.obj V)) (Type u)} (g : P ⟶ Q),
      (((Over.forget (v.obj V)).sheafPushforwardCocontinuous (Type u) (K.over (v.obj V)) K).map
        g).hom = (Over.forget (v.obj V)).op.ran.map g.hom := fun _ ↦ rfl
  have h₂ : ∀ {P Q : Sheaf (J.over V) (Type u)} (g : P ⟶ Q),
      (((Over.post (X := V) v).sheafPushforwardCocontinuous (Type u) (J.over V)
        (K.over (v.obj V))).map g).hom = (Over.post (X := V) v).op.ran.map g.hom := fun _ ↦ rfl
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, h₁, h₂,
    Functor.sheafAdjunctionCocontinuous_unit_app_hom,
    Functor.sheafAdjunctionCocontinuous_counit_app_hom]
  rfl

/-- **The localization mate of the base change map of sheaves of sets is invertible.** -/
theorem isIso_mateEquiv_overPostSheafBaseChange_cocontinuousBaseChange :
    IsIso (mateEquiv ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J)
      ((Over.forget (v.obj V)).sheafAdjunctionCocontinuous (Type u) (K.over (v.obj V)) K)
      (overPostSheafBaseChangeCocontinuousBaseChange v V)).natTrans := by
  have h := isIso_mateEquiv_overPostRanBaseChange_cocontinuousBaseChange v V
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N ↦ ?_
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf K (Type u))]
  have h' := @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ h N.obj
  rw [← mateEquiv_overPostSheafBaseChange_app_hom_cocontinuousBaseChange v V (K := K)] at h'
  exact h'

end CategoryTheory.Functor

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.EtaleDerivedBaseChange

/-!
# Base change along an open immersion

Let
```
XU --j'--> X
|fU        |f
v          v
U  --j---> Y
```
be a cartesian square of schemes with `j` an open immersion and `f` arbitrary. The underived
base change comparison `j^{-1} f_* ⟶ fU_* (j')^{-1}` of abelian sheaves on the small étale sites
is an isomorphism.

## Main results

* `CategoryTheory.isIso_mateEquiv_symm_of_isIso_counit` — the mate of an invertible 2-cell
  between right adjoints is invertible when both counits are, provided the two composites of left
  adjoints it compares are isomorphic in *some* way.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isOpenImmersion` — the base change
  comparison of a cartesian square along an open immersion is invertible.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion` — the derived
  base change map of such a square is invertible.

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- **The mate of an invertible 2-cell of right adjoints is invertible when both counits are.**
Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` have invertible counits and let
`α : R₁ ⋙ G ⟶ H ⋙ R₂` be invertible. If `G ⋙ L₂` and `L₁ ⋙ H` are isomorphic by any natural
isomorphism, then the mate `G ⋙ L₂ ⟶ L₁ ⋙ H` of `α` is invertible. -/
public theorem isIso_mateEquiv_symm_of_isIso_counit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    [IsIso adj₁.counit] [IsIso adj₂.counit] (α : TwoSquare R₁ H G R₂) [IsIso α.natTrans]
    (ρ : G ⋙ L₂ ≅ L₁ ⋙ H) :
    IsIso ((mateEquiv adj₁ adj₂).symm α).natTrans := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun a => ?_
  have hL : IsIso (L₁.map (adj₁.unit.app a)) := by
    have h := adj₁.left_triangle_components a
    have : IsIso (L₁.map (adj₁.unit.app a) ≫ adj₁.counit.app (L₁.obj a)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj₁.counit.app (L₁.obj a))
  have hGL : IsIso (L₂.map (G.map (adj₁.unit.app a))) := by
    have hnat := ρ.hom.naturality (adj₁.unit.app a)
    have hrw : L₂.map (G.map (adj₁.unit.app a)) =
        ρ.hom.app a ≫ H.map (L₁.map (adj₁.unit.app a)) ≫ ρ.inv.app _ := by
      rw [← Category.assoc]
      exact (Iso.eq_comp_inv (ρ.app _)).2 hnat
    rw [hrw]
    infer_instance
  have hcomp : ((mateEquiv adj₁ adj₂).symm α).natTrans.app a =
      L₂.map (G.map (adj₁.unit.app a)) ≫ L₂.map (α.natTrans.app (L₁.obj a)) ≫
        adj₂.counit.app (H.obj (L₁.obj a)) := by
    simp [mateEquiv]
  rw [hcomp]
  infer_instance

end CategoryTheory

namespace Stacks.EtaleCohomology

/-- Direct image of abelian sheaves along an open immersion is fully faithful. -/
public def etaleAbelianDirectImageFullyFaithfulOfIsOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (etaleAbelianDirectImage.{u, v} j).FullyFaithful :=
  ((etaleDirectImageAdj.{u, v} j).fullyFaithfulROfIsIsoCounit).ofIso
    (Adjunction.rightAdjointUniq (etaleDirectImageAdj.{u, v} j)
      (etaleRestrictionAbelianDirectImageAdj.{u, v} j))

/-- The counit `j^{-1} j_* ⟶ 𝟭` of inverse and direct image of abelian sheaves along an open
immersion is invertible. -/
public instance isIso_etaleAbelianInverseImageDirectImageAdj_counit {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (etaleAbelianInverseImageDirectImageAdj.{u, v} j).counit := by
  have := (etaleAbelianDirectImageFullyFaithfulOfIsOpenImmersion.{u, v} j).full
  have := (etaleAbelianDirectImageFullyFaithfulOfIsOpenImmersion.{u, v} j).faithful
  infer_instance

/-- **Inverse image along an étale morphism commutes with direct image**, as an isomorphism of
functors `f_* ⋙ g^{-1} ≅ (g')^{-1} ⋙ f'_*` of abelian sheaves on the small étale sites, for a
cartesian square with `g` and `g'` étale. -/
public def etaleAbelianDirectImageInverseImageIsoOfIsPullback {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    [Etale g] [Etale g'] :
    etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ≅
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f' :=
  Functor.isoWhiskerLeft _ (etaleAbelianInverseImageRestrictionIso.{u, v} g) ≪≫
    (etaleAbelianRestrictionPushforwardIsoOfIsPullback.{u, v} sq.flip).symm ≪≫
    Functor.isoWhiskerRight (etaleAbelianInverseImageRestrictionIso.{u, v} g').symm _

/-- **The base change comparison along an open immersion is invertible.** For a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes with `g` an open immersion and `f` arbitrary, the comparison
`g^{-1} f_* ⟶ f'_* (g')^{-1}` of abelian sheaves on the small étale sites is an isomorphism. -/
public theorem isIso_etaleAbelianBaseChange_of_isOpenImmersion {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)
    [IsOpenImmersion g] : IsIso (etaleAbelianBaseChange.{u, v} f g g' f' sq.w) := by
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback sq.flip ‹IsOpenImmersion g›
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, v} f g g' f' sq.w
    (g' ≫ f) rfl sq.w]
  have : IsIso ((etaleAbelianDirectImageCompIso'.{u, v} g' f (g' ≫ f) rfl).hom ≫
      (etaleAbelianDirectImageCompIso'.{u, v} f' g (g' ≫ f) sq.w).inv) := inferInstance
  exact isIso_mateEquiv_symm_of_isIso_counit _ _ _
    (etaleAbelianDirectImageInverseImageIsoOfIsPullback.{u, v} sq)

/-- **The derived base change map along an open immersion is invertible.** For a cartesian
square with `g` an open immersion and `f` arbitrary, the base change map
`g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on unbounded derived categories of abelian sheaves is an
isomorphism. -/
public theorem isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)
    [IsOpenImmersion g] : IsIso (etaleAbelianDerivedBaseChange.{u, v} f g g' f' sq.w) := by
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback sq.flip ‹IsOpenImmersion g›
  exact isIso_etaleAbelianDerivedBaseChange_of_etale.{u, v} f g g' f' sq.w
    (isIso_etaleAbelianBaseChange_of_isOpenImmersion.{u, v} f g g' f' sq)

end Stacks.EtaleCohomology

end

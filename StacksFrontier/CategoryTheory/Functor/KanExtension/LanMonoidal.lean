module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Connected

/-!
# Left Kan extension along a functor with filtered comma categories is monoidal

Let `L : C ⥤ D` be a functor and `H` a monoidal category such that all pointwise left Kan
extensions along `L` exist, and equip the functor categories `C ⥤ H` and `D ⥤ H` with the
pointwise tensor product. Precomposition with `L` is (strictly) monoidal, so its left adjoint
`L.lan` is oplax monoidal (`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`). At an object
`X : D` the comparison `L.lan (P ⊗ Q) ⟶ L.lan P ⊗ L.lan Q` is the canonical map from the colimit
over `CostructuredArrow L X` of `P ⊗ Q` to the tensor product of the colimits of `P` and of `Q`.
If these comma categories are filtered and the tensor product of `H` commutes with colimits of
that shape in each variable, the comparison is an isomorphism, and so is the comparison of
units: `L.lan` is a monoidal functor.

## Main definitions

* `CategoryTheory.Functor.lanOplaxMonoidal`: the oplax monoidal structure on `L.lan`.
* `CategoryTheory.Functor.lanMonoidal`: the monoidal structure, under filteredness.

## Main results

* `CategoryTheory.Functor.lanUnit_app_comp_whiskerLeft_δ`: the defining property of the
  comparison.
* `CategoryTheory.Functor.isIso_δ_lan`, `CategoryTheory.Functor.isIso_η_lan`: under filteredness,
  the tensor and unit comparisons of `L.lan` are isomorphisms.
* `CategoryTheory.Functor.lanMonoidal_ε_app`: the unit comparison at `L c` is the colimit
  inclusion at `(c, 𝟙 (L c))`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open Limits MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (H : Type*) [Category* H]
  [MonoidalCategory H] [∀ P : C ⥤ H, HasPointwiseLeftKanExtension L P]

/-- **The oplax monoidal structure on the left Kan extension functor**, from the strictly
monoidal precomposition functor through the adjunction `L.lan ⊣ (L ⋙ -)`. -/
@[instance_reducible]
def lanOplaxMonoidal : (L.lan : (C ⥤ H) ⥤ (D ⥤ H)).OplaxMonoidal :=
  (L.lanAdjunction H).leftAdjointOplaxMonoidal

attribute [local instance] lanOplaxMonoidal

variable {H}

/-- The comparison `δ : L.lan (P ⊗ Q) ⟶ L.lan P ⊗ L.lan Q` is characterized by its restriction
along the units: it carries the unit of `P ⊗ Q` to the tensor product of the units. -/
theorem lanUnit_app_comp_whiskerLeft_δ (P Q : C ⥤ H) :
    L.lanUnit.app (P ⊗ Q) ≫ L.whiskerLeft (OplaxMonoidal.δ L.lan P Q) =
      L.lanUnit.app P ⊗ₘ L.lanUnit.app Q := by
  have h := ((L.lanAdjunction H).homEquiv _ _).apply_symm_apply
    (((L.lanAdjunction H).unit.app P ⊗ₘ (L.lanAdjunction H).unit.app Q) ≫
      LaxMonoidal.μ ((whiskeringLeft _ _ H).obj L) _ _)
  rw [Adjunction.homEquiv_unit, lanAdjunction_unit] at h
  have hδ : OplaxMonoidal.δ L.lan P Q = ((L.lanAdjunction H).homEquiv _ _).symm
      (((L.lanAdjunction H).unit.app P ⊗ₘ (L.lanAdjunction H).unit.app Q) ≫
        LaxMonoidal.μ ((whiskeringLeft _ _ H).obj L) _ _) := rfl
  rw [hδ]
  simp only [lanAdjunction_unit]
  change L.lanUnit.app (P ⊗ Q) ≫ ((whiskeringLeft C D H).obj L).map _ = _
  refine h.trans ?_
  ext X
  simp

/-- The comparison at `X : D`, restricted to the leg of the colimit over `CostructuredArrow L X`
at `f : L.obj Y ⟶ X`, is the tensor product of the legs. -/
theorem lanUnit_app_app_map_δ_app (P Q : C ⥤ H) (X : D) (f : CostructuredArrow L X) :
    (L.lanUnit.app (P ⊗ Q)).app f.left ≫ (L.lan.obj (P ⊗ Q)).map f.hom ≫
        (OplaxMonoidal.δ L.lan P Q).app X =
      ((L.lanUnit.app P).app f.left ≫ (L.lan.obj P).map f.hom) ⊗ₘ
        ((L.lanUnit.app Q).app f.left ≫ (L.lan.obj Q).map f.hom) := by
  rw [(OplaxMonoidal.δ L.lan P Q).naturality, ← Category.assoc]
  have h := congrArg (fun φ => φ.app f.left) (lanUnit_app_comp_whiskerLeft_δ L P Q)
  dsimp at h
  exact (congrArg (· ≫ (L.lan.obj P ⊗ L.lan.obj Q).map f.hom) h).trans
    (tensorHom_comp_tensorHom _ _ _ _)

section Monoidal

variable [∀ X : D, IsFiltered (CostructuredArrow L X)]
  [∀ (X : D) (M : H), PreservesColimitsOfShape (CostructuredArrow L X) ((curriedTensor H).obj M)]
  [∀ (X : D) (M : H),
    PreservesColimitsOfShape (CostructuredArrow L X) ((curriedTensor H).flip.obj M)]

/-- The pointwise colimit cocone of a left Kan extension. -/
abbrev lanCoconeAt (P : C ⥤ H) (X : D) : Cocone (CostructuredArrow.proj L X ⋙ P) :=
  (LeftExtension.mk _ (L.lanUnit.app P)).coconeAt X

/-- The pointwise cocone of `L.lan P` at `X` is a colimit cocone. -/
def isColimitLanCoconeAt (P : C ⥤ H) (X : D) : IsColimit (lanCoconeAt L P X) :=
  isPointwiseLeftKanExtensionOfIsLeftKanExtension (L.lan.obj P) (L.lanUnit.app P) X

attribute [local instance] IsFiltered.isSifted in
/-- **The tensor comparison of `L.lan` is an isomorphism** when the comma categories are filtered
and the tensor product commutes with their colimits in each variable. -/
instance isIso_δ_lan (P Q : C ⥤ H) : IsIso (OplaxMonoidal.δ L.lan P Q) := by
  suffices ∀ X, IsIso ((OplaxMonoidal.δ L.lan P Q).app X) from NatIso.isIso_of_isIso_app _
  intro X
  let hPQ := isColimitLanCoconeAt L (P ⊗ Q) X
  let hT : IsColimit ((lanCoconeAt L P X).tensor (lanCoconeAt L Q X)) :=
    (isColimitLanCoconeAt L P X).tensor (isColimitLanCoconeAt L Q X)
  let φ : lanCoconeAt L (P ⊗ Q) X ⟶ (lanCoconeAt L P X).tensor (lanCoconeAt L Q X) :=
    { hom := (OplaxMonoidal.δ L.lan P Q).app X
      w := fun f => by
        dsimp [LeftExtension.coconeAt]
        exact (Category.assoc _ _ _).trans (lanUnit_app_app_map_δ_app L P Q X f) }
  have := IsColimit.hom_isIso hPQ hT φ
  exact (Cocone.forget _).map_isIso φ

attribute [local instance] IsFiltered.isConnected in
/-- **The unit comparison of `L.lan` is an isomorphism** when the comma categories are
filtered. -/
instance isIso_η_lan : IsIso (OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H))) := by
  suffices ∀ X, IsIso ((OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H))).app X) from
    NatIso.isIso_of_isIso_app _
  intro X
  let hU := isColimitLanCoconeAt L (𝟙_ (C ⥤ H)) X
  let hC : IsColimit (constCocone (CostructuredArrow L X) (𝟙_ H)) :=
    isColimitConstCocone _ (𝟙_ H)
  let φ : lanCoconeAt L (𝟙_ (C ⥤ H)) X ⟶ constCocone (CostructuredArrow L X) (𝟙_ H) :=
    { hom := (OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H))).app X
      w := fun f => by
        have hη : OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H)) =
            ((L.lanAdjunction H).homEquiv _ _).symm
              (LaxMonoidal.ε ((whiskeringLeft _ _ H).obj L)) := rfl
        have h := ((L.lanAdjunction H).homEquiv _ _).apply_symm_apply
          (LaxMonoidal.ε ((whiskeringLeft _ _ H).obj L))
        rw [Adjunction.homEquiv_unit, lanAdjunction_unit, ← hη] at h
        have h' : (L.lanUnit.app (𝟙_ (C ⥤ H))).app f.left ≫
            (OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H))).app (L.obj f.left) = 𝟙 _ := by
          have := congrArg (fun φ => φ.app f.left) h
          simpa using this
        have hn := (OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H))).naturality f.hom
        dsimp [LeftExtension.coconeAt]
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (_ ≫ ·) hn).trans ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ _) h').trans ?_
        simp }
  have := IsColimit.hom_isIso hU hC φ
  exact (Cocone.forget _).map_isIso φ

/-- **The left Kan extension functor is monoidal** for the pointwise tensor products, when the
comma categories `CostructuredArrow L X` are filtered and the tensor product of `H` commutes with
colimits of that shape in each variable. -/
@[instance_reducible]
def lanMonoidal : (L.lan : (C ⥤ H) ⥤ (D ⥤ H)).Monoidal :=
  .ofOplaxMonoidal _

attribute [local instance] lanMonoidal in
/-- **The unit comparison of the monoidal left Kan extension at `L c`** is the component at `c`
of the unit of `L.lan ⊣ (L ⋙ -)` at the tensor unit: the colimit inclusion of the constant
diagram at the object `(c, 𝟙 (L c))`. -/
theorem lanMonoidal_ε_app (c : C) :
    (LaxMonoidal.ε (L.lan : (C ⥤ H) ⥤ (D ⥤ H))).app (L.obj c) =
      (L.lanUnit.app (𝟙_ (C ⥤ H))).app c := by
  have hη : OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H)) =
      ((L.lanAdjunction H).homEquiv _ _).symm
        (LaxMonoidal.ε ((whiskeringLeft _ _ H).obj L)) := rfl
  have h := ((L.lanAdjunction H).homEquiv _ _).apply_symm_apply
    (LaxMonoidal.ε ((whiskeringLeft _ _ H).obj L))
  rw [Adjunction.homEquiv_unit, lanAdjunction_unit, ← hη] at h
  have h' : (L.lanUnit.app (𝟙_ (C ⥤ H))).app c ≫
      (OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H))).app (L.obj c) = 𝟙 _ := by
    have := congrArg (fun φ => φ.app c) h
    simpa using this
  have hε : LaxMonoidal.ε (L.lan : (C ⥤ H) ⥤ (D ⥤ H)) =
      CategoryTheory.inv (OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H))) := rfl
  rw [← cancel_mono ((OplaxMonoidal.η (L.lan : (C ⥤ H) ⥤ (D ⥤ H))).app (L.obj c)), h', hε,
    ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
  rfl

end Monoidal

end CategoryTheory.Functor

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AbstractKunnethMap
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapTransport

/-!
# The projection map along equivalences of the base and the top

Let `a : L ⊣ R` with `L : C ⥤ D`, and `a' : L' ⊣ R'` with `L' : C' ⥤ D'`, be adjunctions whose
source and target carry bifunctors `T_C`, `T_D`, `T_C'`, `T_D'` and comparisons
`μ : L(M ⊗ N) ⟶ LM ⊗ LN`, `μ' : L'(M ⊗ N) ⟶ L'M ⊗ L'N`. Let `i_C : C ⥤ C'` and `i_D : D ⥤ D'` be
equivalences commuting with the left adjoints, `c : i_C ⋙ L' ≅ L ⋙ i_D`, and with the bifunctors,
`ν_C : i_C(M ⊗ N) ≅ i_C M ⊗ i_C N`, `ν_D`. If `c` carries the composite comparison of `i_C ⋙ L'`
to that of `L ⋙ i_D`, then `i_C` carries the projection map
`A ⊗ R B ⟶ R(L A ⊗ B)` of `a` (`Stacks.Cohomology.AbstractKunnethMap.projectionMap`) to the one of
`a'` at `(i_C A, i_D B)`, up to isomorphisms on either side; in particular one is invertible
exactly when the other is.

This is the abstract form of reading a projection formula on one model of a derived category on
another one: the equivalences are derived pullbacks along equivalences of ringed topoi, `c` comes
from Stacks 0D6D, and the compatibility of `c` with the comparisons is the composition law of
Stacks 07A4.

## Main definitions

* `Stacks.Cohomology.AbstractKunnethMap.TensorCompat`: a transformation `F ⟶ G` carries a
  comparison `μ_F` to `μ_G`.
* `Stacks.Cohomology.AbstractKunnethMap.compTensor`: the comparison of a composite functor.
* `Stacks.Cohomology.AbstractKunnethMap.rightAdjointMate`: the transformation `R ⋙ i_C ⟶ i_D ⋙ R'`
  attached to `c`; an isomorphism when `i_C` and `i_D` are equivalences.

## Main results

* `Stacks.Cohomology.AbstractKunnethMap.map_projectionMap_of_counit_comm`
* `Stacks.Cohomology.AbstractKunnethMap.isIso_projectionMap_iff_of_tensorCompat`
* `Stacks.Cohomology.AbstractKunnethMap.isIso_projectionMap_iff_of_iso`: the case of the identity
  functors, two adjunctions with isomorphic left adjoints.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.AbstractKunnethMap

/-! ### Comparisons carried by transformations -/

section TensorCompat

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {TC : C × C ⥤ C} {TD : D × D ⥤ D} {TE : E × E ⥤ E}

/-- **A transformation `c : F ⟶ G` carries the comparison `μ_F` to `μ_G`**:
`c_{M ⊗ N} ≫ μ_G = μ_F ≫ (c_M ⊗ c_N)`. -/
def TensorCompat {F G : C ⥤ D} (μF : TC ⋙ F ⟶ F.prod F ⋙ TD) (μG : TC ⋙ G ⟶ G.prod G ⋙ TD)
    (c : F ⟶ G) : Prop :=
  ∀ P Q : C, c.app (TC.obj (P, Q)) ≫ μG.app (P, Q) = μF.app (P, Q) ≫ TD.map (c.app P ×ₘ c.app Q)

variable {F G H : C ⥤ D} {μF : TC ⋙ F ⟶ F.prod F ⋙ TD} {μG : TC ⋙ G ⟶ G.prod G ⋙ TD}
  {μH : TC ⋙ H ⟶ H.prod H ⋙ TD}

/-- A compatibility stated as an equation of transformations of bifunctors. -/
theorem TensorCompat.of_eq {c : F ⟶ G}
    (h : Functor.whiskerLeft TC c ≫ μG = μF ≫ Functor.whiskerRight (NatTrans.prod c c) TD) :
    TensorCompat μF μG c :=
  fun P Q => NatTrans.congr_app h (P, Q)

/-- Compatibilities compose. -/
theorem TensorCompat.comp {c₁ : F ⟶ G} {c₂ : G ⟶ H} (h₁ : TensorCompat μF μG c₁)
    (h₂ : TensorCompat μG μH c₂) : TensorCompat μF μH (c₁ ≫ c₂) := by
  intro P Q
  rw [NatTrans.comp_app, Category.assoc, h₂ P Q, reassoc_of% (h₁ P Q), ← TD.map_comp]
  rfl

/-- The inverse of a compatible isomorphism is compatible. -/
theorem TensorCompat.symm {e : F ≅ G} (h : TensorCompat μF μG e.hom) :
    TensorCompat μG μF e.inv := by
  intro P Q
  rw [← cancel_epi (e.hom.app (TC.obj (P, Q))), Iso.hom_inv_id_app_assoc, reassoc_of% (h P Q),
    ← TD.map_comp]
  simp

/-- The identity is compatible. -/
theorem TensorCompat.refl (μF : TC ⋙ F ⟶ F.prod F ⋙ TD) : TensorCompat μF μF (𝟙 F) := by
  intro P Q
  simp

/-- **The comparison of a composite functor**, `F₂F₁(M ⊗ N) ⟶ F₂(F₁M ⊗ F₁N) ⟶ F₂F₁M ⊗ F₂F₁N`. -/
@[simps]
def compTensor {F₁ : C ⥤ D} {F₂ : D ⥤ E} (μ₁ : TC ⋙ F₁ ⟶ F₁.prod F₁ ⋙ TD)
    (μ₂ : TD ⋙ F₂ ⟶ F₂.prod F₂ ⋙ TE) : TC ⋙ (F₁ ⋙ F₂) ⟶ (F₁ ⋙ F₂).prod (F₁ ⋙ F₂) ⋙ TE where
  app P := F₂.map (μ₁.app P) ≫ μ₂.app (F₁.obj P.1, F₁.obj P.2)
  naturality {P Q} g := by
    have h₁ := μ₁.naturality g
    have h₂ := μ₂.naturality (F₁.map g.1 ×ₘ F₁.map g.2)
    dsimp at h₁ h₂ ⊢
    rw [← F₂.map_comp_assoc, h₁, F₂.map_comp_assoc, h₂, Category.assoc]

end TensorCompat

/-! ### The mate of a commutation of left adjoints -/

section Mate

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {L' : C' ⥤ D'} {R' : D' ⥤ C'} (a' : L' ⊣ R')
  {iC : C ⥤ C'} {iD : D ⥤ D'} (c : iC ⋙ L' ≅ L ⋙ iD)

/-- **The transformation `R ⋙ i_C ⟶ i_D ⋙ R'` attached to `c : i_C ⋙ L' ≅ L ⋙ i_D`**: at `Y` the
adjoint, for `a'`, of `L' i_C R Y ≅ i_D L R Y ⟶ i_D Y`. -/
@[simps]
def rightAdjointMate : R ⋙ iC ⟶ iD ⋙ R' where
  app Y := a'.homEquiv _ _ (c.hom.app (R.obj Y) ≫ iD.map (a.counit.app Y))
  naturality {Y Y'} g := by
    dsimp
    rw [← a'.homEquiv_naturality_left, ← a'.homEquiv_naturality_right]
    congr 1
    have hc := c.hom.naturality (R.map g)
    dsimp at hc
    rw [reassoc_of% hc, Category.assoc, ← iD.map_comp, ← iD.map_comp, a.counit_naturality]

/-- The defining property of `rightAdjointMate`: it is compatible with the two counits. -/
theorem map_rightAdjointMate_app_comp_counit (Y : D) :
    L'.map ((rightAdjointMate a a' c).app Y) ≫ a'.counit.app (iD.obj Y) =
      c.hom.app (R.obj Y) ≫ iD.map (a.counit.app Y) := by
  have h := (a'.homEquiv _ _).symm_apply_apply (c.hom.app (R.obj Y) ≫ iD.map (a.counit.app Y))
  rwa [Adjunction.homEquiv_counit] at h

/-- **The mate of `c` is invertible when `i_C` and `i_D` are equivalences.** Composition with it
is, up to the bijections `i_C`, the two adjunctions, `i_D` and `c`, the identity of
`Hom(Z, R Y)`. -/
instance isIso_rightAdjointMate_app [iC.IsEquivalence] [iD.IsEquivalence] (Y : D) :
    IsIso ((rightAdjointMate a a' c).app Y) := by
  let t : iC.obj (R.obj Y) ⟶ R'.obj (iD.obj Y) := (rightAdjointMate a a' c).app Y
  let hC := Functor.FullyFaithful.ofFullyFaithful iC
  let hD := Functor.FullyFaithful.ofFullyFaithful iD
  have key : ∀ Z : C, Function.Bijective (fun x : iC.obj Z ⟶ iC.obj (R.obj Y) => x ≫ t) := by
    intro Z
    let e : (iC.obj Z ⟶ iC.obj (R.obj Y)) ≃ (iC.obj Z ⟶ R'.obj (iD.obj Y)) :=
      hC.homEquiv.symm.trans ((a.homEquiv Z Y).symm.trans (hD.homEquiv.trans
        ((c.app Z).symm.homFromEquiv.trans (a'.homEquiv _ _))))
    have he : ∀ x, e x = x ≫ t := by
      intro x
      obtain ⟨x₀, rfl⟩ := hC.map_surjective x
      simp only [e, t, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_symm_apply,
        Functor.FullyFaithful.preimage_map, Functor.FullyFaithful.homEquiv_apply,
        Iso.homFromEquiv_apply, Iso.symm_inv, Iso.app_hom, rightAdjointMate_app,
        Functor.comp_obj]
      rw [← a'.homEquiv_naturality_left]
      congr 1
      have hc := c.hom.naturality x₀
      dsimp at hc
      rw [reassoc_of% hc, Adjunction.homEquiv_counit, iD.map_comp]
    rw [show (fun x : iC.obj Z ⟶ iC.obj (R.obj Y) => x ≫ t) = ⇑e from
      funext fun x => (he x).symm]
    exact e.bijective
  refine isIso_of_yoneda_map_bijective t fun T => ?_
  let eT : iC.obj (iC.objPreimage T) ≅ T := iC.objObjPreimageIso T
  have h : (fun x : T ⟶ iC.obj (R.obj Y) => x ≫ t) =
      eT.homFromEquiv ∘ (fun x => x ≫ t) ∘ eT.symm.homFromEquiv := by
    funext x
    simp
  rw [h]
  exact eT.homFromEquiv.bijective.comp ((key _).comp eT.symm.homFromEquiv.bijective)

/-- `rightAdjointMate` as an isomorphism `i_D ⋙ R' ≅ R ⋙ i_C`, when `i_C` and `i_D` are
equivalences. -/
def rightAdjointMateIso [iC.IsEquivalence] [iD.IsEquivalence] : iD ⋙ R' ≅ R ⋙ iC :=
  haveI : IsIso (rightAdjointMate a a' c) := NatIso.isIso_of_isIso_app _
  (asIso (rightAdjointMate a a' c)).symm

/-- The inverse of `rightAdjointMateIso` is `rightAdjointMate`. -/
@[simp]
theorem rightAdjointMateIso_inv [iC.IsEquivalence] [iD.IsEquivalence] :
    (rightAdjointMateIso a a' c).inv = rightAdjointMate a a' c :=
  rfl

end Mate

/-! ### The projection map along the commutations -/

section Projection

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  (TC : C × C ⥤ C) (TD : D × D ⥤ D) (TC' : C' × C' ⥤ C') (TD' : D' × D' ⥤ D')
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {L' : C' ⥤ D'} {R' : D' ⥤ C'} (a' : L' ⊣ R')

/-- A product of two isomorphisms is an isomorphism. -/
private instance isIso_prodMk {P Q : C} {S T : D} (f : P ⟶ Q) (g : S ⟶ T) [IsIso f] [IsIso g] :
    IsIso (f ×ₘ g) :=
  (isIso_prod_iff _ _).2 ⟨‹_›, ‹_›⟩

/-- **The defining equation of the projection map, transposed**: `L` of the projection map
followed by the counit is the comparison followed by the counit in the second factor. -/
theorem map_projectionMap_comp_counit (μ : TC ⋙ L ⟶ L.prod L ⋙ TD) (A : C) (B : D) :
    L.map (projectionMap TC TD a μ A B) ≫ a.counit.app _ =
      μ.app (A, R.obj B) ≫ TD.map (𝟙 (L.obj A) ×ₘ a.counit.app B) := by
  have h := (a.homEquiv _ _).symm_apply_apply
    (μ.app (A, R.obj B) ≫ TD.map (𝟙 (L.obj A) ×ₘ a.counit.app B))
  rwa [Adjunction.homEquiv_counit] at h

variable {TC TD TC' TD'} {iC : C ⥤ C'} {iD : D ⥤ D'} (c : iC ⋙ L' ≅ L ⋙ iD)
  (d : iD ⋙ R' ≅ R ⋙ iC)
  (νC : TC ⋙ iC ≅ iC.prod iC ⋙ TC') (νD : TD ⋙ iD ≅ iD.prod iD ⋙ TD')
  (μ : TC ⋙ L ⟶ L.prod L ⋙ TD) (μ' : TC' ⋙ L' ⟶ L'.prod L' ⋙ TD')

/-- A transformation carrying the comparison of `i_C ⋙ L'` to that of `L ⋙ i_D` is compatible
with `μ` and `μ'` in the form used for the projection maps. -/
private theorem comp_map_eq_of_tensorCompat
    (h : TensorCompat (compTensor νC.hom μ') (compTensor μ νD.hom) c.hom) (P Q : C) :
    c.hom.app (TC.obj (P, Q)) ≫ iD.map (μ.app (P, Q)) =
      L'.map (νC.hom.app (P, Q)) ≫ μ'.app (iC.obj P, iC.obj Q) ≫
        TD'.map (c.hom.app P ×ₘ c.hom.app Q) ≫ νD.inv.app (L.obj P, L.obj Q) := by
  rw [← cancel_mono (νD.hom.app (L.obj P, L.obj Q))]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Functor.prod_obj,
    Category.comp_id]
  simpa only [compTensor_app, Category.assoc] using h P Q

/-- **The projection map along a correspondence of adjunctions.** Let `i_C`, `i_D` carry the
adjunction `L ⊣ R` to `L' ⊣ R'` through commutation isomorphisms `c`, `d` under which the counits
correspond (`hc`), and the bifunctors through `ν_C`, `ν_D`, with `c` carrying the comparison of
`i_C ⋙ L'` to that of `L ⋙ i_D` (`h`). Then `i_C` carries the projection map of `μ` at `(A, B)`
to that of `μ'` at `(i_C A, i_D B)`, up to the evident isomorphisms on either side. -/
theorem map_projectionMap_of_counit_comm
    (hc : ∀ Y : D, L'.map (d.inv.app Y) ≫ a'.counit.app (iD.obj Y) =
      c.hom.app (R.obj Y) ≫ iD.map (a.counit.app Y))
    (h : TensorCompat (compTensor νC.hom μ') (compTensor μ νD.hom) c.hom) (A : C) (B : D) :
    iC.map (projectionMap TC TD a μ A B) =
      νC.hom.app (A, R.obj B) ≫ TC'.map (𝟙 (iC.obj A) ×ₘ d.inv.app B) ≫
        projectionMap TC' TD' a' μ' (iC.obj A) (iD.obj B) ≫
          R'.map (TD'.map (c.hom.app A ×ₘ 𝟙 (iD.obj B)) ≫ νD.inv.app (L.obj A, B)) ≫
            d.hom.app (TD.obj (L.obj A, B)) := by
  have h' := comp_map_eq_of_tensorCompat c νC νD μ μ' h A (R.obj B)
  have hnatc := c.hom.naturality (projectionMap TC TD a μ A B)
  have hnatνD := νD.inv.naturality (𝟙 (L.obj A) ×ₘ a.counit.app B)
  have hnatμ' := μ'.naturality (𝟙 (iC.obj A) ×ₘ d.inv.app B)
  dsimp at hnatc hnatνD hnatμ'
  rw [← cancel_mono (d.inv.app (TD.obj (L.obj A, B)))]
  apply (a'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app,
    Functor.comp_obj, Category.comp_id, Adjunction.counit_naturality,
    Adjunction.counit_naturality_assoc]
  rw [hc, reassoc_of% hnatc, ← iD.map_comp, map_projectionMap_comp_counit TC TD a μ A B,
    iD.map_comp, reassoc_of% h', ← hnatνD,
    reassoc_of% (map_projectionMap_comp_counit TC' TD' a' μ' (iC.obj A) (iD.obj B)),
    reassoc_of% hnatμ']
  simp only [← TD'.map_comp_assoc, prod_comp, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]
  rw [hc]

/-- **Invertibility of the projection map along a correspondence of adjunctions.** -/
theorem isIso_projectionMap_iff_of_counit_comm [iC.ReflectsIsomorphisms]
    (hc : ∀ Y : D, L'.map (d.inv.app Y) ≫ a'.counit.app (iD.obj Y) =
      c.hom.app (R.obj Y) ≫ iD.map (a.counit.app Y))
    (h : TensorCompat (compTensor νC.hom μ') (compTensor μ νD.hom) c.hom) (A : C) (B : D) :
    IsIso (projectionMap TC TD a μ A B) ↔
      IsIso (projectionMap TC' TD' a' μ' (iC.obj A) (iD.obj B)) := by
  rw [← isIso_iff_of_reflects_iso (projectionMap TC TD a μ A B) iC,
    map_projectionMap_of_counit_comm a a' c d νC νD μ μ' hc h,
    isIso_comp_left_iff, isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff,
    isIso_comp_right_iff]

/-- **Invertibility of the projection map along equivalences.** If `i_C` and `i_D` are
equivalences, `c : i_C ⋙ L' ≅ L ⋙ i_D` carries the composite comparison of `i_C ⋙ L'` to that of
`L ⋙ i_D`, then the projection map of `μ` at `(A, B)` is invertible exactly when the one of `μ'`
at `(i_C A, i_D B)` is. The commutation of the right adjoints is the mate of `c`. -/
theorem isIso_projectionMap_iff_of_tensorCompat [iC.IsEquivalence] [iD.IsEquivalence]
    (h : TensorCompat (compTensor νC.hom μ') (compTensor μ νD.hom) c.hom) (A : C) (B : D) :
    IsIso (projectionMap TC TD a μ A B) ↔
      IsIso (projectionMap TC' TD' a' μ' (iC.obj A) (iD.obj B)) :=
  isIso_projectionMap_iff_of_counit_comm a a' c (rightAdjointMateIso a a' c) νC νD μ μ'
    (fun Y => by
      rw [rightAdjointMateIso_inv]
      exact map_rightAdjointMate_app_comp_counit a a' c Y)
    h A B

end Projection

/-! ### Two adjunctions with isomorphic left adjoints -/

section SameCategories

variable {C D : Type*} [Category* C] [Category* D] {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {L' : C ⥤ D} {R' : D ⥤ C} (a' : L' ⊣ R')
  (κ : L ≅ L') (μ : TC ⋙ L ⟶ L.prod L ⋙ TD) (μ' : TC ⋙ L' ⟶ L'.prod L' ⋙ TD)

/-- **The projection map does not depend on the choice of the adjunction**, up to an
isomorphism `κ : L ≅ L'` of left adjoints carrying the comparison `μ` to `μ'`: one projection
map is invertible exactly when the other is. -/
theorem isIso_projectionMap_iff_of_iso (h : TensorCompat μ μ' κ.hom) (A : C) (B : D) :
    IsIso (projectionMap TC TD a μ A B) ↔ IsIso (projectionMap TC TD a' μ' A B) := by
  refine isIso_projectionMap_iff_of_tensorCompat a a' (iC := 𝟭 C) (iD := 𝟭 D)
    (Functor.leftUnitor L' ≪≫ κ.symm ≪≫ (Functor.rightUnitor L).symm)
    (Functor.rightUnitor TC ≪≫ (Functor.leftUnitor TC).symm)
    (Functor.rightUnitor TD ≪≫ (Functor.leftUnitor TD).symm) μ μ' ?_ A B
  intro P Q
  simpa using (TensorCompat.symm (e := κ) h) P Q

end SameCategories

/-! ### Invariance under isomorphisms of the arguments -/

section Objects

variable {C D : Type*} [Category* C] [Category* D] (TC : C × C ⥤ C) (TD : D × D ⥤ D)
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (μ : TC ⋙ L ⟶ L.prod L ⋙ TD)

/-- **Invertibility of the projection map depends only on the isomorphism classes of its
arguments**, by its naturality. -/
theorem isIso_projectionMap_iff_of_iso_objects {A A' : C} {B B' : D} (eA : A ≅ A')
    (eB : B ≅ B') :
    IsIso (projectionMap TC TD a μ A B) ↔ IsIso (projectionMap TC TD a μ A' B') := by
  rw [← isIso_comp_left_iff (TC.map (eA.hom ×ₘ R.map eB.hom)),
    projectionMap_naturality TC TD a μ eA.hom eB.hom, isIso_comp_right_iff]

end Objects

/-! ### The other variant of the projection map along equivalences -/

section AdjunctionTensorMap

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {TC : C × C ⥤ C} {TD : D × D ⥤ D} {TC' : C' × C' ⥤ C'} {TD' : D' × D' ⥤ D'}
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {L' : C' ⥤ D'} {R' : D' ⥤ C'} (a' : L' ⊣ R')
  {iC : C ⥤ C'} {iD : D ⥤ D'} (c : iC ⋙ L' ≅ L ⋙ iD)
  (νC : TC ⋙ iC ≅ iC.prod iC ⋙ TC') (νD : TD ⋙ iD ≅ iD.prod iD ⋙ TD')
  (μ : TC ⋙ L ⟶ L.prod L ⋙ TD) (μ' : TC' ⋙ L' ⟶ L'.prod L' ⋙ TD')

/-- **Invertibility of the canonical map `R G ⊗ H ⟶ R(G ⊗ L H)`
(`CategoryTheory.adjunctionTensorMap`) along equivalences**, under the same compatibility as
`isIso_projectionMap_iff_of_tensorCompat`. -/
theorem isIso_adjunctionTensorMap_iff_of_tensorCompat [iC.IsEquivalence] [iD.IsEquivalence]
    (h : TensorCompat (compTensor νC.hom μ') (compTensor μ νD.hom) c.hom) (G : D) (H : C) :
    IsIso (adjunctionTensorMap a TC TD μ G H) ↔
      IsIso (adjunctionTensorMap a' TC' TD' μ' (iD.obj G) (iC.obj H)) := by
  rw [← isIso_iff_of_reflects_iso (adjunctionTensorMap a TC TD μ G H) iC]
  refine isIso_map_adjunctionTensorMap_iff_of_counit_comm a a' c (rightAdjointMateIso a a' c)
    νC.symm νD.symm μ μ' (fun Y => ?_) (fun P Q => ?_) G H
  · rw [rightAdjointMateIso_inv]
    exact (map_rightAdjointMate_app_comp_counit a a' c Y).symm
  · simpa only [Iso.symm_inv, Iso.symm_hom] using comp_map_eq_of_tensorCompat c νC νD μ μ' h P Q

end AdjunctionTensorMap

section AdjunctionTensorMapSameCategories

variable {C D : Type*} [Category* C] [Category* D] {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {L' : C ⥤ D} {R' : D ⥤ C} (a' : L' ⊣ R')
  (κ : L ≅ L') (μ : TC ⋙ L ⟶ L.prod L ⋙ TD) (μ' : TC ⋙ L' ⟶ L'.prod L' ⋙ TD)

/-- **The canonical map `R G ⊗ H ⟶ R(G ⊗ L H)` does not depend on the choice of the
adjunction**, up to an isomorphism `κ : L ≅ L'` of left adjoints carrying `μ` to `μ'`. -/
theorem isIso_adjunctionTensorMap_iff_of_iso (h : TensorCompat μ μ' κ.hom) (G : D) (H : C) :
    IsIso (adjunctionTensorMap a TC TD μ G H) ↔ IsIso (adjunctionTensorMap a' TC TD μ' G H) := by
  refine isIso_adjunctionTensorMap_iff_of_tensorCompat a a' (iC := 𝟭 C) (iD := 𝟭 D)
    (Functor.leftUnitor L' ≪≫ κ.symm ≪≫ (Functor.rightUnitor L).symm)
    (Functor.rightUnitor TC ≪≫ (Functor.leftUnitor TC).symm)
    (Functor.rightUnitor TD ≪≫ (Functor.leftUnitor TD).symm) μ μ' ?_ G H
  intro P Q
  simpa using (TensorCompat.symm (e := κ) h) P Q

/-- **Invertibility of the canonical map depends only on the isomorphism classes of its
arguments.** -/
theorem isIso_adjunctionTensorMap_iff_of_iso_objects {G G' : D} {H H' : C} (eG : G ≅ G')
    (eH : H ≅ H') :
    IsIso (adjunctionTensorMap a TC TD μ G H) ↔ IsIso (adjunctionTensorMap a TC TD μ G' H') := by
  rw [← isIso_comp_left_iff (TC.map (R.map eG.hom ×ₘ eH.hom)),
    adjunctionTensorMap_natural a TC TD μ eG.hom eH.hom, isIso_comp_right_iff]

end AdjunctionTensorMapSameCategories

/-! ### The projection map against the canonical map of the other variable -/

section Braiding

variable {C D : Type*} [Category* C] [Category* D] {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (μ : TC ⋙ L ⟶ L.prod L ⋙ TD)
  (σC : TC ≅ CategoryTheory.Prod.swap C C ⋙ TC) (σD : TD ≅ CategoryTheory.Prod.swap D D ⋙ TD)

/-- **The projection map `A ⊗ R B ⟶ R(L A ⊗ B)` is the canonical map
`R B ⊗ A ⟶ R(B ⊗ L A)` (`CategoryTheory.adjunctionTensorMap`) read through the commutativity
constraints**, provided the comparison `μ` commutes with them. -/
theorem projectionMap_eq_adjunctionTensorMap
    (hμ : ∀ P Q : C, L.map (σC.hom.app (P, Q)) ≫ μ.app (Q, P) =
      μ.app (P, Q) ≫ σD.hom.app (L.obj P, L.obj Q)) (A : C) (B : D) :
    projectionMap TC TD a μ A B =
      σC.hom.app (A, R.obj B) ≫ adjunctionTensorMap a TC TD μ B A ≫
        R.map (σD.inv.app (L.obj A, B)) := by
  apply (a.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, map_projectionMap_comp_counit,
    L.map_comp, L.map_comp, Category.assoc, Category.assoc, a.counit_naturality,
    map_adjunctionTensorMap_comp_counit_assoc, reassoc_of% (hμ A (R.obj B))]
  have n := σD.hom.naturality (𝟙 (L.obj A) ×ₘ a.counit.app B)
  dsimp at n
  rw [← reassoc_of% n, Iso.hom_inv_id_app, Category.comp_id]

/-- The projection map is invertible exactly when the canonical map of the other variable is. -/
theorem isIso_projectionMap_iff_isIso_adjunctionTensorMap
    (hμ : ∀ P Q : C, L.map (σC.hom.app (P, Q)) ≫ μ.app (Q, P) =
      μ.app (P, Q) ≫ σD.hom.app (L.obj P, L.obj Q)) (A : C) (B : D) :
    IsIso (projectionMap TC TD a μ A B) ↔ IsIso (adjunctionTensorMap a TC TD μ B A) := by
  rw [projectionMap_eq_adjunctionTensorMap a μ σC σD hμ, isIso_comp_left_iff,
    isIso_comp_right_iff]

end Braiding

end Stacks.Cohomology.AbstractKunnethMap

end

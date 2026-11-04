module

public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomTransferProjection

/-!
# The pullback map of internal Homs along a functor with a left adjoint

Let `F : C ⥤ D` carry tensor products to tensor products, `μ : F(A ⊗ B) ≅ F A ⊗ F B`, and let
`F` have a left adjoint `E` (extension by zero, when `F` is pullback along an étale morphism).
The **projection map** `E(Z ⊗ F M) ⟶ E Z ⊗ M` is the transpose of
`Z ⊗ F M ⟶ F E Z ⊗ F M ≅ F(E Z ⊗ M)`. If it is invertible for every `Z`, then the pullback map
`F H_C(M, K) ⟶ H_D(F M, F K)` of [Stacks, Tag 08JF] is invertible for every `K`: this is
`CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective_of_isIso_projection`.

## Main definitions

* `CategoryTheory.PullbackInternalHom.leftAdjointProjectionMap`: the projection map.

## Main results

* `CategoryTheory.PullbackInternalHom.isIso_pullbackHomMap_of_isIso_leftAdjointProjectionMap`.
* `CategoryTheory.PullbackInternalHom.isIso_leftAdjointProjectionMap_of_iso`: invertibility of
  the projection map depends only on the isomorphism classes of `Z` and `M`.
* `CategoryTheory.PullbackInternalHom.isIso_leftAdjointProjectionMap_of_unit_comp`: an
  isomorphism with the defining transpose shows the projection map invertible.
* `CategoryTheory.PullbackInternalHom.isIso_leftAdjointProjectionMap_ofNatIsoRight_iff`:
  replacing the right adjoint by an isomorphic functor.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public noncomputable section

namespace CategoryTheory.PullbackInternalHom

open Opposite

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {E : D ⥤ C} (adjE : E ⊣ F)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
  (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
  (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
  (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P))

/-- **The projection map** `E(Z ⊗ F M) ⟶ E Z ⊗ M` of a left adjoint `E` of `F`: the transpose
of the unit tensored with `F M`, followed by `μ⁻¹ : F E Z ⊗ F M ⟶ F(E Z ⊗ M)`. -/
def leftAdjointProjectionMap (Z : D) (M : C) :
    E.obj ((TD.obj Z).obj (F.obj M)) ⟶ (TC.obj (E.obj Z)).obj M :=
  (adjE.homEquiv _ _).symm
    ((TD.map (adjE.unit.app Z)).app (F.obj M) ≫ μ.inv.app (E.obj Z, M))

/-- The projection map is the morphism whose transpose is the unit tensored with `F M` followed
by `μ⁻¹`. -/
theorem leftAdjointProjectionMap_eq_of_homEquiv {Z : D} {M : C}
    (φ : E.obj ((TD.obj Z).obj (F.obj M)) ⟶ (TC.obj (E.obj Z)).obj M)
    (h : adjE.homEquiv _ _ φ =
      (TD.map (adjE.unit.app Z)).app (F.obj M) ≫ μ.inv.app (E.obj Z, M)) :
    leftAdjointProjectionMap adjE TC TD μ Z M = φ := by
  rw [leftAdjointProjectionMap, ← h, Equiv.symm_apply_apply]

/-- The projection map is natural in the object `Z` of `D`. -/
theorem leftAdjointProjectionMap_naturality_left {Z Z' : D} (g : Z ⟶ Z') (M : C) :
    E.map ((TD.map g).app (F.obj M)) ≫ leftAdjointProjectionMap adjE TC TD μ Z' M =
      leftAdjointProjectionMap adjE TC TD μ Z M ≫ (TC.map (E.map g)).app M := by
  have hμ := μ.inv.naturality (X := (E.obj Z, M)) (Y := (E.obj Z', M)) (E.map g, 𝟙 M)
  simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_map,
    Functor.prod_map, Functor.uncurry_obj_map, Functor.map_id, Category.comp_id] at hμ
  rw [leftAdjointProjectionMap, leftAdjointProjectionMap,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hu : g ≫ adjE.unit.app Z' = adjE.unit.app Z ≫ F.map (E.map g) :=
    adjE.unit.naturality g
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, hu, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, hμ, Category.assoc]

/-- The projection map is natural in the object `M` of `C`. -/
theorem leftAdjointProjectionMap_naturality_right (Z : D) {M M' : C} (l : M ⟶ M') :
    E.map ((TD.obj Z).map (F.map l)) ≫ leftAdjointProjectionMap adjE TC TD μ Z M' =
      leftAdjointProjectionMap adjE TC TD μ Z M ≫ (TC.obj (E.obj Z)).map l := by
  have hμ := μ.inv.naturality (X := (E.obj Z, M)) (Y := (E.obj Z, M')) (𝟙 (E.obj Z), l)
  simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_map,
    Functor.prod_map, Functor.uncurry_obj_map, Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hμ
  rw [leftAdjointProjectionMap, leftAdjointProjectionMap,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hn : (TD.obj Z).map (F.map l) ≫ (TD.map (adjE.unit.app Z)).app (F.obj M') =
      (TD.map (adjE.unit.app Z)).app (F.obj M) ≫ (TD.obj (F.obj (E.obj Z))).map (F.map l) :=
    (TD.map (adjE.unit.app Z)).naturality (F.map l)
  rw [reassoc_of% hn, hμ, Category.assoc]

/-- **Invertibility of the projection map only depends on the isomorphism classes** of `Z` and
`M`. -/
theorem isIso_leftAdjointProjectionMap_of_iso {Z Z' : D} {M M' : C} (g : Z ≅ Z') (l : M ≅ M')
    [IsIso (leftAdjointProjectionMap adjE TC TD μ Z' M')] :
    IsIso (leftAdjointProjectionMap adjE TC TD μ Z M) := by
  have h1 : IsIso (E.map ((TD.map g.hom).app (F.obj M')) ≫
      leftAdjointProjectionMap adjE TC TD μ Z' M') := inferInstance
  rw [leftAdjointProjectionMap_naturality_left] at h1
  have h2 : IsIso (E.map ((TD.obj Z).map (F.map l.hom)) ≫
      leftAdjointProjectionMap adjE TC TD μ Z M') := by
    have := (isIso_comp_right_iff _ _).mp h1
    infer_instance
  rw [leftAdjointProjectionMap_naturality_right] at h2
  exact (isIso_comp_right_iff _ _).mp h2

/-- **The pullback map of internal Homs is invertible when the projection maps are.** If
`E(Z ⊗ F M) ⟶ E Z ⊗ M` is invertible for every `Z`, then `F H_C(M, K) ⟶ H_D(F M, F K)` is
invertible for every `K`. -/
theorem isIso_pullbackHomMap_of_isIso_leftAdjointProjectionMap (M K : C)
    (hp : ∀ Z, IsIso (leftAdjointProjectionMap adjE TC TD μ Z M)) :
    IsIso (pullbackHomMap TC TD μ HC HD adjC adjD M K) := by
  refine InternalHomTransfer.isIso_of_tensorHomBijective_of_isIso_projection TC TD adjE
    (fun A B => μ.app (A, B)) ?_ hp ((adjC M).counit.app K)
    (fun Z => ((adjC M).homEquiv Z K).symm.bijective) ((adjD (F.obj M)).counit.app (F.obj K))
    (fun Z => ((adjD (F.obj M)).homEquiv Z _).symm.bijective) _ ?_
  · intro A A' f B
    have h := μ.hom.naturality (X := (A, B)) (Y := (A', B)) (f, 𝟙 B)
    simpa using h
  · exact ((adjD (F.obj M)).homEquiv_counit
      (g := pullbackHomMap TC TD μ HC HD adjC adjD M K)).symm.trans
      (((adjD (F.obj M)).homEquiv _ _).symm_apply_apply _)

/-- **A criterion for the projection map to be invertible**: it is so as soon as some
isomorphism `E(Z ⊗ F M) ≅ E Z ⊗ M` has the transpose that defines the projection map. -/
theorem isIso_leftAdjointProjectionMap_of_unit_comp {Z : D} {M : C}
    (φ : E.obj ((TD.obj Z).obj (F.obj M)) ≅ (TC.obj (E.obj Z)).obj M)
    (h : adjE.unit.app _ ≫ F.map φ.hom =
      (TD.map (adjE.unit.app Z)).app (F.obj M) ≫ μ.inv.app (E.obj Z, M)) :
    IsIso (leftAdjointProjectionMap adjE TC TD μ Z M) := by
  rw [leftAdjointProjectionMap_eq_of_homEquiv adjE TC TD μ φ.hom
    (by rw [Adjunction.homEquiv_unit]; exact h)]
  infer_instance

section Transport

variable {F' : C ⥤ D} (e : F ≅ F')
  (μ' : Functor.uncurry.obj TC ⋙ F' ≅ F'.prod F' ⋙ Functor.uncurry.obj TD)

/-- An isomorphism `F(A ⊗ B) ≅ F' A ⊗ F' B`, read through an isomorphism `F ≅ F'` as an
isomorphism `F(A ⊗ B) ≅ F A ⊗ F B`. -/
def tensorIsoOfNatIsoRight :
    Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD :=
  Functor.isoWhiskerLeft (Functor.uncurry.obj TC) e ≪≫ μ' ≪≫
    Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) (Functor.uncurry.obj TD)

/-- The projection map of `E ⊣ F'`, for `F'` isomorphic to `F`, is that of `E ⊣ F` for the
transported tensor comparison, up to the isomorphism `E(Z ⊗ F' M) ≅ E(Z ⊗ F M)`. -/
theorem leftAdjointProjectionMap_ofNatIsoRight (Z : D) (M : C) :
    leftAdjointProjectionMap (adjE.ofNatIsoRight e) TC TD μ' Z M =
      E.map ((TD.obj Z).map (e.inv.app M)) ≫
        leftAdjointProjectionMap adjE TC TD (tensorIsoOfNatIsoRight TC TD e μ') Z M := by
  simp only [leftAdjointProjectionMap, Adjunction.homEquiv_counit, Adjunction.ofNatIsoRight,
    tensorIsoOfNatIsoRight]
  simp only [Category.assoc, Functor.map_comp, Iso.symm_inv, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod_inv, Functor.uncurry_obj_map,
    Functor.prod_obj, Functor.comp_obj, Functor.uncurry_obj_obj, NatTrans.prod_app_fst,
    NatTrans.prod_app_snd]
  have key : (TD.obj Z).map (e.inv.app M) ≫ (TD.map (adjE.unit.app Z)).app (F.obj M) ≫
      (TD.map (e.hom.app (E.obj Z))).app (F.obj M) ≫
        (TD.obj (F'.obj (E.obj Z))).map (e.hom.app M) =
      (TD.map (adjE.unit.app Z)).app (F'.obj M) ≫
        (TD.map (e.hom.app (E.obj Z))).app (F'.obj M) := by
    rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, (TD.map _).naturality_assoc,
      ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id,
      Functor.map_comp, NatTrans.comp_app]
  have key' := congrArg E.map key
  simp only [Functor.map_comp] at key'
  simp only [reassoc_of% key']

/-- Invertibility of the projection map is unchanged by replacing the right adjoint by an
isomorphic functor. -/
theorem isIso_leftAdjointProjectionMap_ofNatIsoRight_iff (Z : D) (M : C) :
    IsIso (leftAdjointProjectionMap (adjE.ofNatIsoRight e) TC TD μ' Z M) ↔
      IsIso (leftAdjointProjectionMap adjE TC TD (tensorIsoOfNatIsoRight TC TD e μ') Z M) := by
  rw [leftAdjointProjectionMap_ofNatIsoRight]
  exact isIso_comp_left_iff _ _

end Transport

section Lemmas

/-- The transpose of the projection map is the unit tensored with `F M` followed by `μ⁻¹`. -/
theorem unit_comp_map_leftAdjointProjectionMap (Z : D) (M : C) :
    adjE.unit.app _ ≫ F.map (leftAdjointProjectionMap adjE TC TD μ Z M) =
      (TD.map (adjE.unit.app Z)).app (F.obj M) ≫ μ.inv.app (E.obj Z, M) := by
  have h := adjE.homEquiv_unit (X := (TD.obj Z).obj (F.obj M)) (Y := (TC.obj (E.obj Z)).obj M)
    (f := leftAdjointProjectionMap adjE TC TD μ Z M)
  rw [← h, leftAdjointProjectionMap, Equiv.apply_symm_apply]



/-- Composing two morphisms of pairs under a bifunctor. -/
theorem bifunctor_map_comp_map {A B C' : Type*} [Category A] [Category B] [Category C']
    (T : A ⥤ B ⥤ C') {X X' X'' : A} {Y Y' Y'' : B} (a : X ⟶ X') (a' : X' ⟶ X'')
    (b : Y ⟶ Y') (b' : Y' ⟶ Y'') :
    (T.map a).app Y ≫ (T.obj X').map b ≫ (T.map a').app Y' ≫ (T.obj X'').map b' =
      (T.map (a ≫ a')).app Y ≫ (T.obj X'').map (b ≫ b') := by
  rw [(T.map a').naturality_assoc b, T.map_comp, NatTrans.comp_app, (T.obj X'').map_comp,
    Category.assoc]


/-- Naturality of a transformation `L(A ⊗ B) ⟶ L₁A ⊗' L₂B` in the first variable. -/
theorem uncurry_natTrans_app_fst {A B C' D' A' B' : Type*} [Category A] [Category B]
    [Category C'] [Category D'] [Category A'] [Category B']
    (T : A ⥤ B ⥤ C') (L : C' ⥤ D') (L₁ : A ⥤ A') (L₂ : B ⥤ B') (T' : A' ⥤ B' ⥤ D')
    (α : Functor.uncurry.obj T ⋙ L ⟶ L₁.prod L₂ ⋙ Functor.uncurry.obj T')
    {x x' : A} (a : x ⟶ x') (b : B) :
    L.map ((T.map a).app b) ≫ α.app (x', b) =
      α.app (x, b) ≫ (T'.map (L₁.map a)).app (L₂.obj b) := by
  have h := α.naturality ((a, 𝟙 b) : (x, b) ⟶ (x', b))
  simpa using h


/-- For an isomorphism `i : a ≅ b`, precomposing with `T(F i⁻¹)` and then `T(F i)` at `X` is the
identity. -/
theorem bifunctor_map_inv_hom_app {A A' B C' : Type*} [Category A] [Category A'] [Category B]
    [Category C'] (T : A ⥤ B ⥤ C') (F : A' ⥤ A) {a b : A'} (i : a ≅ b) (X : B) {Z : C'}
    (r : (T.obj (F.obj b)).obj X ⟶ Z) :
    (T.map (F.map i.inv)).app X ≫ (T.map (F.map i.hom)).app X ≫ r = r := by
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, Functor.map_id, NatTrans.id_app, Category.id_comp]

section TransportApp

variable {F' : C ⥤ D} (e : F ≅ F')
  (μ' : Functor.uncurry.obj TC ⋙ F' ≅ F'.prod F' ⋙ Functor.uncurry.obj TD)

/-- The components of `tensorIsoOfNatIsoRight`. -/
theorem tensorIsoOfNatIsoRight_hom_app (A B : C) :
    (tensorIsoOfNatIsoRight TC TD e μ').hom.app (A, B) =
      e.hom.app _ ≫ μ'.hom.app (A, B) ≫
        (TD.map (e.inv.app A)).app _ ≫ (TD.obj _).map (e.inv.app B) := rfl

/-- The inverse components of `tensorIsoOfNatIsoRight`. -/
theorem tensorIsoOfNatIsoRight_inv_app (A B : C) :
    (tensorIsoOfNatIsoRight TC TD e μ').inv.app (A, B) =
      ((TD.map (e.hom.app A)).app _ ≫ (TD.obj _).map (e.hom.app B)) ≫ μ'.inv.app (A, B) ≫
        e.inv.app _ := by
  simp [tensorIsoOfNatIsoRight]

end TransportApp

end Lemmas

end CategoryTheory.PullbackInternalHom

end

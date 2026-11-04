module

public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomLeftAdjoint

/-!
# The projection formula from the compatibility of a right adjoint with internal Homs

Let `E ⊣ R` with `R : C ⥤ D`, tensor bifunctors on `C` and `D`, and `c : R(A ⊗ B) ≅ R A ⊗ R B`.
For a fixed object `L` of `C`, suppose that for every `M` the functor `Z ↦ Hom(Z ⊗ L, M)` is
represented by an internal Hom `H(L, M)`, that `Z ↦ Hom(Z ⊗ R L, R M)` is represented by
`H(R L, R M)`, and that the canonical comparison `R H(L, M) ⟶ H(R L, R M)` is invertible for every
`M`. Then the canonical projection map `E(Z ⊗ R L) ⟶ E Z ⊗ L` is invertible for every `Z`. This is
the converse of
`CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective_of_isIso_projection`
(Fausk–Hu–May): a right adjoint commutes with internal Homs exactly when its left adjoint satisfies
the projection formula.

## Main results

* `CategoryTheory.InternalHomTransfer.isIso_projection_of_tensorHomBijective_of_isIso`.
* `CategoryTheory.PullbackInternalHom.isIso_leftAdjointProjectionMap_of_isIso_pullbackHomMap`:
  the same for `CategoryTheory.PullbackInternalHom.leftAdjointProjectionMap` and the pullback map
  of internal Homs `CategoryTheory.PullbackInternalHom.pullbackHomMap` of [Stacks, Tag 08JF].
* `CategoryTheory.PullbackInternalHom.tensorIsoOfNatIsoRight_trans`: transporting a tensor
  comparison along a composite isomorphism is transporting it twice.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.InternalHomTransfer

variable {C D : Type*} [Category C] [Category D]
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) {R : C ⥤ D} {E : D ⥤ C} (adj : E ⊣ R)
  (c : ∀ A B, R.obj ((TC.obj A).obj B) ≅ (TD.obj (R.obj A)).obj (R.obj B))

/-- **The projection formula from the compatibility with internal homs.** If for every `M` the
comparison `t_M : R H(L, M) ⟶ H(R L, R M)`, whose transpose under the bijection of
`H(R L, R M)` is `c⁻¹ ≫ R e_M`, is an isomorphism, then for every `Z` the transpose
`E(Z ⊗ R L) ⟶ E Z ⊗ L` of `(η_Z ⊗ 1) ≫ c⁻¹ : Z ⊗ R L ⟶ R(E Z ⊗ L)` is an isomorphism. -/
theorem isIso_projection_of_tensorHomBijective_of_isIso
    (hc : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    {L : C} (H : C → C) (e : ∀ M, (TC.obj (H M)).obj L ⟶ M)
    (he : ∀ M Z, Function.Bijective (fun g : Z ⟶ H M => (TC.map g).app L ≫ e M))
    (H' : C → D) (e' : ∀ M, (TD.obj (H' M)).obj (R.obj L) ⟶ R.obj M)
    (he' : ∀ M Z, Function.Bijective (fun g : Z ⟶ H' M => (TD.map g).app (R.obj L) ≫ e' M))
    (t : ∀ M, R.obj (H M) ⟶ H' M)
    (ht : ∀ M, (TD.map (t M)).app (R.obj L) ≫ e' M = (c (H M) L).inv ≫ R.map (e M))
    (htiso : ∀ M, IsIso (t M)) (Z : D) :
    IsIso ((adj.homEquiv ((TD.obj Z).obj (R.obj L)) ((TC.obj (E.obj Z)).obj L)).symm
      ((TD.map (adj.unit.app Z)).app (R.obj L) ≫ (c (E.obj Z) L).inv)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  let p : (TD.obj Z).obj (R.obj L) ⟶ R.obj ((TC.obj (E.obj Z)).obj L) :=
    (TD.map (adj.unit.app Z)).app (R.obj L) ≫ (c (E.obj Z) L).inv
  have h3 : (fun f : E.obj Z ⟶ H M => p ≫ R.map ((TC.map f).app L ≫ e M)) =
      (adj.homEquiv _ M) ∘ (fun h => (adj.homEquiv _ _).symm p ≫ h) ∘
        (fun f : E.obj Z ⟶ H M => (TC.map f).app L ≫ e M) := by
    funext f
    rw [Function.comp_apply, Function.comp_apply, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
  have h2 : (fun f : E.obj Z ⟶ H M => p ≫ R.map ((TC.map f).app L ≫ e M)) =
      (fun g : Z ⟶ H' M => (TD.map g).app (R.obj L) ≫ e' M) ∘ (fun x => x ≫ t M) ∘
        (adj.homEquiv Z (H M)) := by
    funext f
    have hcf : (TD.map (R.map f)).app (R.obj L) ≫ (c (H M) L).inv =
        (c (E.obj Z) L).inv ≫ R.map ((TC.map f).app L) := by
      rw [Iso.comp_inv_eq, Category.assoc, hc f L, Iso.inv_hom_id_assoc]
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp,
      NatTrans.comp_app, Category.assoc, p, ht]
    rw [reassoc_of% hcf]
  have hb : Function.Bijective
      ((fun g : Z ⟶ H' M => (TD.map g).app (R.obj L) ≫ e' M) ∘ (fun x => x ≫ t M) ∘
        (adj.homEquiv Z (H M))) := by
    have := htiso M
    have hpost : Function.Bijective (fun x : Z ⟶ R.obj (H M) => x ≫ t M) :=
      Function.bijective_iff_has_inverse.2
        ⟨fun y => y ≫ inv (t M), fun y => by simp, fun y => by simp⟩
    exact (he' M Z).comp (hpost.comp (adj.homEquiv Z (H M)).bijective)
  rw [← h2, h3] at hb
  rw [← Function.Bijective.of_comp_iff _ (he M (E.obj Z))]
  exact (Function.Bijective.of_comp_iff' (adj.homEquiv _ M).bijective _).1 hb

end CategoryTheory.InternalHomTransfer

namespace CategoryTheory.PullbackInternalHom

open Opposite

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {E : D ⥤ C} (adjE : E ⊣ F)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
  (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
  (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
  (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P))

/-- **The projection maps are invertible when the pullback maps of internal Homs are**
(Fausk–Hu–May). If `F H_C(M, K) ⟶ H_D(F M, F K)` is invertible for every `K`, then
`E(Z ⊗ F M) ⟶ E Z ⊗ M` is invertible for every `Z`. This is the converse of
`CategoryTheory.PullbackInternalHom.isIso_pullbackHomMap_of_isIso_leftAdjointProjectionMap`. -/
theorem isIso_leftAdjointProjectionMap_of_isIso_pullbackHomMap (Z : D) (M : C)
    (hp : ∀ K, IsIso (pullbackHomMap TC TD μ HC HD adjC adjD M K)) :
    IsIso (leftAdjointProjectionMap adjE TC TD μ Z M) := by
  refine InternalHomTransfer.isIso_projection_of_tensorHomBijective_of_isIso TC TD adjE
    (fun A B => μ.app (A, B)) ?_ (fun K => (HC.obj (op M)).obj K)
    (fun K => (adjC M).counit.app K)
    (fun K Z => ((adjC M).homEquiv Z K).symm.bijective)
    (fun K => (HD.obj (op (F.obj M))).obj (F.obj K))
    (fun K => (adjD (F.obj M)).counit.app (F.obj K))
    (fun K Z => ((adjD (F.obj M)).homEquiv Z _).symm.bijective)
    (fun K => pullbackHomMap TC TD μ HC HD adjC adjD M K) ?_ hp Z
  · intro A A' f B
    have h := μ.hom.naturality (X := (A, B)) (Y := (A', B)) (f, 𝟙 B)
    simpa using h
  · intro K
    exact ((adjD (F.obj M)).homEquiv_counit
      (g := pullbackHomMap TC TD μ HC HD adjC adjD M K)).symm.trans
      (((adjD (F.obj M)).homEquiv _ _).symm_apply_apply _)

section Transport

variable {F' F'' : C ⥤ D} (e : F ≅ F') (e' : F' ≅ F'')
  (μ'' : Functor.uncurry.obj TC ⋙ F'' ≅ F''.prod F'' ⋙ Functor.uncurry.obj TD)

/-- **Transporting a tensor comparison along a composite isomorphism** is transporting it along
each factor in turn. -/
theorem tensorIsoOfNatIsoRight_trans :
    tensorIsoOfNatIsoRight TC TD (e ≪≫ e') μ'' =
      tensorIsoOfNatIsoRight TC TD e (tensorIsoOfNatIsoRight TC TD e' μ'') := by
  ext ⟨A, B⟩
  simp [tensorIsoOfNatIsoRight]

/-- Transporting a tensor comparison along an identity isomorphism does nothing. -/
theorem tensorIsoOfNatIsoRight_refl :
    tensorIsoOfNatIsoRight TC TD (Iso.refl F) μ = μ := by
  ext ⟨A, B⟩
  simp [tensorIsoOfNatIsoRight]

end Transport

end CategoryTheory.PullbackInternalHom

end

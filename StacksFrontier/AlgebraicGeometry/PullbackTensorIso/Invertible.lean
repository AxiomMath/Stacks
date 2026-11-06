module

public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.PullbackStalkTensor

/-!
# Stacks 01CD: pullback commutes with the tensor product

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `A`, `B` be sheaves of
`𝒪_Y`-modules. `Stacks.RingedSpace.comparison` is the canonical morphism

`f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B`,

and Stacks 01CD is the assertion that it is invertible. This file proves that, so
`Stacks.PullbackTensorIso.pullbackTensorIso` is the isomorphism of bifunctors, with no
hypothesis beyond a morphism of ringed spaces.

## Main results

* `Stacks.PullbackTensorIso.isIso_comparison`: Stacks 01CD, componentwise. The comparison
  is an isomorphism.
* `Stacks.PullbackTensorIso.isIso_comparisonNatTrans_app`: the same read as the instance
  hypothesis of `Stacks.RingedSpace.comparisonIso`, so that hypothesis is now always met.
* `Stacks.PullbackTensorIso.pullbackTensorIso`: Stacks 01CD. The isomorphism of
  bifunctors expressing `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` for the canonical sheaf tensor, natural
  in both module arguments, with `pullbackTensorIso_hom` identifying its forward direction with the
  comparison. By `Stacks.RingedSpace.comparison_unique` the comparison is the only candidate.
* `Stacks.PullbackTensorIso.bijective_comparisonStalkMap`: the comparison is bijective on the
  stalk at every point, which is what the above rests on.
* `Stacks.PullbackTensorIso.tensorStalkIso_comp_comparisonStalkMap`: the identity that does
  the work — the comparison's map on the stalk at `x`, conjugated by the identification of
  the stalk of a pullback and the stalk of a tensor product, is the algebraic base-change
  isomorphism.

## The route

Invertibility is checked on stalks, and all three inputs are element formulas rather than
abstract comparisons.

* The stalk of a pullback is `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} A_{f x}` (`pullbackStalkEquiv`), carrying
  `1 ⊗ germ a` to `germ (η a)`, the germ of the pullback-unit image
  (`pullbackStalkEquiv_one_tmul`). This rests on
  `Stacks.ModuleSkyscraper.ringedSpacePullbackStalkIso` with its left adjoint instantiated as
  `Stacks.PullbackTensorIso.stalkExtendScalars`, so that the tensor product is taken over the
  stalks of Stacks 01CB.
* The stalk of a tensor product is `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`,
  with `tensorStalkIso_germ` on germs of pure tensors.
* The comparison on germs is `Stacks.PullbackTensorIso.germ_comparison_pullbackUnit` and its
  reading through the previous item, `tensorStalkIso_germ_comparison`.

Given those, the two sides of `tensorStalkIso_comp_comparisonStalkMap` are linear maps out of
`𝒪_{X,x} ⊗_{𝒪_{Y,f x}} (A ⊗ B)_{f x}`, so `tmul_one_ext` reduces equality to the elements
`1 ⊗ germ t`; `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` reduces `germ t` to a
sum of germs of pure tensors over a common open neighbourhood (`exists_common_germ`); and on one
of those both sides give `germ (η a) ⊗ germ (η b)` — the left by the germ formula, the right by
`TensorProduct.AlgebraTensorModule.distribBaseChange_tmul`. The base-change isomorphism being
invertible, so is the comparison's map on stalks, and
`Stacks.PullbackTensorIso.isIso_of_bijective_stalk_map` finishes.

## Universes

A single universe `u`, over `AlgebraicGeometry.RingedSpace.{u, u}` and `SheafOfModules.{u}`,
which is the generality of `Stacks.RingedSpace.comparison`,
`RingedSpaceModuleAdjunction.modulePullback` and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` alike. The restriction comes from
Mathlib's `PresheafOfModules.instIsRightAdjointPushforward`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped TensorProduct

universe u

namespace Stacks.PullbackTensorIso

section Algebraic

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {P : Type u} [AddCommGroup P] [Module R P] {Q : Type u} [AddCommGroup Q] [Module S Q]

/-- Two `S`-linear maps out of `S ⊗[R] P` that agree on the elements `1 ⊗ₜ p` are equal: an
element of `S ⊗[R] P` is a sum of `s ⊗ₜ p = s • (1 ⊗ₜ p)`. -/
lemma tmul_one_ext {g h : (S ⊗[R] P) →ₗ[S] Q} (H : ∀ p : P, g (1 ⊗ₜ p) = h (1 ⊗ₜ p)) :
    g = h := by
  refine LinearMap.ext fun t => ?_
  induction t with
  | tmul s p =>
    have e : (s ⊗ₜ[R] p : S ⊗[R] P) = s • ((1 : S) ⊗ₜ[R] p) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul, H]
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

end Algebraic

open RingedSpaceModuleAdjunction Stacks.ModuleSkyscraper

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)

/-- The algebra structure on the stalk at `x` over the stalk at `f x` given by the stalk map
of `f` between the stalks taken in `CommRingCat`. -/
abbrev commStalkAlgebra :
    Algebra (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y (f.hom.base x))
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x) :=
  (commStalkRingMap f x).toAlgebra

attribute [local instance] commStalkAlgebra

/-- The stalk of a pullback, as a linear equivalence over the stalk at `x` taken in
`CommRingCat`. The second factor still carries the module `stalkExtendScalars` consumes. -/
def pullbackStalkLinear (A : SheafOfModules.{u} (structureSheafRing Y)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x
      ⊗[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y (f.hom.base x)]
        ((ModuleCat.restrictScalars (stalkRingEquiv Y (f.hom.base x)).toRingHom).obj
          (stalkMod (structureSheafRing Y) (f.hom.base x) A))
            ≃ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x]
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X (pullbackSheaf f A).val x :=
  (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv (stalkRingEquiv X x)).counitIso.app
          ((ModuleCat.extendScalars (commStalkRingMap f x)).obj
            ((ModuleCat.restrictScalars (stalkRingEquiv Y (f.hom.base x)).toRingHom).obj
              (stalkMod (structureSheafRing Y) (f.hom.base x) A)))).symm ≪≫
        (ModuleCat.restrictScalars (stalkRingEquiv X x).toRingHom).mapIso
          ((pullbackStalkTensorIso f x).symm.app A)).toLinearEquiv.trans
    (stalkRestrictEquiv (pullbackSheaf f A))

/-- The stalk of a pullback as a tensor product over the stalks of Stacks 01CB, with both
factors carrying the module structures of Stacks 01CB:
`(f^*A)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} A_{f x}`. -/
def pullbackStalkEquiv (A : SheafOfModules.{u} (structureSheafRing Y)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x
      ⊗[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y (f.hom.base x)]
        Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y A.val (f.hom.base x)
          ≃ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x]
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X (pullbackSheaf f A).val x :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
    (stalkRestrictEquiv A)).symm.trans (pullbackStalkLinear f x A)

/-- The identification of the stalk of a pullback, on elements: `1 ⊗ germ a` goes to the
germ of the pullback-unit image of `a`. -/
lemma pullbackStalkEquiv_one_tmul
    (A : SheafOfModules.{u} (structureSheafRing Y)) (V : Opens Y.carrier)
    (hV : f.hom.base x ∈ V) (a : A.val.obj (op V)) :
    pullbackStalkEquiv f x A
        ((1 : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x) ⊗ₜ
          Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm Y A.val (f.hom.base x) V hV a) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X (pullbackSheaf f A).val x
        ((opensMap f).obj V) hV
        (Stacks.RingedSpace.pullbackUnit f A (op V) a) :=
  pullbackStalkTensorIso_inv_app_unit f x A V hV a

variable (A B : SheafOfModules.{u} (structureSheafRing
  Y))

/-- The base-change isomorphism. Extension of scalars is strong monoidal, so the stalk of
`A ⊗ B` extended to `x` is the tensor product over `𝒪_{X,x}` of the two stalks extended to
`x`; composed with the two identifications of `pullbackStalkEquiv` this is
`𝒪_{X,x} ⊗_{𝒪_{Y,f x}} (A_{f x} ⊗_{𝒪_{Y,f x}} B_{f x}) ≅ (f^*A)_x ⊗_{𝒪_{X,x}} (f^*B)_x`. -/
def tensorStalkBaseChange :
    Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x
      ⊗[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y (f.hom.base x)]
        (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y A.val (f.hom.base x) ⊗[
            Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y (f.hom.base x)]
          Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y B.val (f.hom.base x))
            ≃ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x]
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X (pullbackSheaf f A).val x
        ⊗[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x]
        Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X (pullbackSheaf f B).val x :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange _ _ _ _).trans
    (TensorProduct.congr (pullbackStalkEquiv f x A) (pullbackStalkEquiv f x B))

/-- The model of the comparison's map on stalks: the stalk of a tensor product of
Stacks 01CB, extended to `x`, followed by the base-change isomorphism. -/
def stalkComparisonModel :
    letI := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule Y
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B).val
        (f.hom.base x)
    Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x
      ⊗[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y (f.hom.base x)]
        Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B).val
            (f.hom.base x)
      ≃ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x]
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X (pullbackSheaf f A).val x
        ⊗[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x]
        Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X (pullbackSheaf f B).val x :=
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule Y
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B).val
      (f.hom.base x)
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y (f.hom.base x) A B)).trans
      (tensorStalkBaseChange f x A B)

/-- The comparison morphism of Stacks 01CD, read on the stalk at `x` as a linear map over the
stalk of the structure sheaf taken in `CommRingCat`. -/
def comparisonStalkMap :
    letI := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
        (pullbackSheaf f A)).obj (pullbackSheaf f B)).val x
    Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X (pullbackSheaf f
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B)).val x
      →ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x]
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
          (pullbackSheaf f A)).obj (pullbackSheaf f B)).val x :=
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
      (pullbackSheaf f A)).obj (pullbackSheaf f B)).val x
  Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X _ _ (Stacks.RingedSpace.comparison f A
    B).val x

/-- Two germs at a point have representatives over a common open neighbourhood. -/
lemma exists_common_germ (y : Y.carrier)
    (m : Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y A.val y)
    (n : Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y B.val y) :
    ∃ (U : Opens Y.carrier) (hU : y ∈ U) (a : A.val.obj (op U)) (b : B.val.obj (op U)),
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm Y A.val y U hU a = m ∧
        Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm Y B.val y U hU b = n := by
  obtain ⟨U, hU, a₀, ha⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) A.val.presheaf m
  obtain ⟨V, hV, b₀, hb⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) B.val.presheaf n
  refine ⟨U ⊓ V, ⟨hU, hV⟩, A.val.presheaf.map (homOfLE inf_le_left).op a₀,
    B.val.presheaf.map (homOfLE inf_le_right).op b₀, ?_, ?_⟩
  · exact (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) A.val.presheaf
      (homOfLE inf_le_left) y ⟨hU, hV⟩ a₀).trans ha
  · exact (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) B.val.presheaf
      (homOfLE inf_le_right) y ⟨hU, hV⟩ b₀).trans hb

/-- The common value both sides take on the germ of a pure tensor: the left-hand side, by the
germ formula for the comparison. -/
lemma tensorStalkIso_comparisonStalkMap_germ (U : Opens Y.carrier) (hU : f.hom.base x ∈ U)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x (pullbackSheaf f A)
      (pullbackSheaf f B)
        (comparisonStalkMap f x A B
          (pullbackStalkEquiv f x
            (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B)
            ((1 : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x) ⊗ₜ
              Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm Y
                (((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B).val
                (f.hom.base x) U hU
                (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Y A B (op U)
                  (a ⊗ₜ b))))) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X (pullbackSheaf f A).val x
        ((opensMap f).obj U) hU
          (Stacks.RingedSpace.pullbackUnit f A (op U) a) ⊗ₜ
        Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X (pullbackSheaf f B).val x
          ((opensMap f).obj U) hU
          (Stacks.RingedSpace.pullbackUnit f B (op U) b) := by
  refine (congrArg (fun t => Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x
    (pullbackSheaf f A) (pullbackSheaf f B) (comparisonStalkMap f x A B t))
      (pullbackStalkEquiv_one_tmul f x _ U hU _)).trans ?_
  exact tensorStalkIso_germ_comparison f A B x U hU a b

/-- The same value, taken by the base-change model: `distribBaseChange` on `1 ⊗ (m ⊗ n)`. -/
lemma stalkComparisonModel_germ (U : Opens Y.carrier) (hU : f.hom.base x ∈ U)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    letI := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule Y
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B).val
        (f.hom.base x)
    stalkComparisonModel f x A B
        ((1 : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x) ⊗ₜ
          Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm Y
            (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B).val
              (f.hom.base x) U hU
            (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Y A B (op U)
              (a ⊗ₜ b))) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X (pullbackSheaf f A).val x
        ((opensMap f).obj U) hU
          (Stacks.RingedSpace.pullbackUnit f A (op U) a) ⊗ₜ
        Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X (pullbackSheaf f B).val x
          ((opensMap f).obj U) hU
          (Stacks.RingedSpace.pullbackUnit f B (op U) b) := by
  simp only [stalkComparisonModel, tensorStalkBaseChange, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul,
    pullbackStalkEquiv_one_tmul]

/-- The comparison morphism of Stacks 01CD induces the base-change isomorphism on the stalk at
`x`. Both sides are linear over the stalk at `x`, so they agree as soon as they agree on the
elements `1 ⊗ germ t`; there `t` is a germ of a section of `A ⊗ B`, which the stalk of a tensor
product of Stacks 01CB reduces to a sum of germs of pure tensors over a common open
neighbourhood, and on those the germ formula and `distribBaseChange` give the same answer
`germ (η a) ⊗ germ (η b)`. -/
lemma tensorStalkIso_comp_comparisonStalkMap :
    letI := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
        (pullbackSheaf f A)).obj (pullbackSheaf f B)).val x
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x (pullbackSheaf f A)
          (pullbackSheaf f B)).toLinearMap ∘ₗ
        (comparisonStalkMap f x A B ∘ₗ
          (pullbackStalkEquiv f x
            (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B)).toLinearMap) =
      (stalkComparisonModel f x A B).toLinearMap := by
  refine tmul_one_ext fun p => ?_
  obtain ⟨t, rfl⟩ :=
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y (f.hom.base x) A
      B).symm.surjective p
  induction t with
  | add left right left_eq right_eq =>
      simpa only [map_add, TensorProduct.tmul_add] using
        congrArg₂ (· + ·) left_eq right_eq
  | tmul m n =>
    obtain ⟨U, hU, a, b, rfl, rfl⟩ := exists_common_germ A B (f.hom.base x) m n
    rw [(LinearEquiv.symm_apply_eq _).2
      (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ Y (f.hom.base x) A B U hU a
        b).symm,
      LinearMap.comp_apply, LinearMap.comp_apply]
    exact (tensorStalkIso_comparisonStalkMap_germ f x A B U hU a b).trans
      (stalkComparisonModel_germ f x A B U hU a b).symm

/-- Stacks 01CD on stalks. The comparison morphism induces a bijection on the stalk at
every point of `X`: it is the base-change isomorphism, conjugated by two isomorphisms. -/
lemma bijective_comparisonStalkMap : Function.Bijective (comparisonStalkMap f x A B) := by
  have h : Function.Bijective (stalkComparisonModel f x A B).toLinearMap :=
    (stalkComparisonModel f x A B).bijective
  rw [← tensorStalkIso_comp_comparisonStalkMap f x A B] at h
  exact (Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)).1
    ((Function.Bijective.of_comp_iff' (LinearEquiv.bijective _) _).1 h)

/-- Stacks 01CD, componentwise. The comparison morphism
`f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B` is an isomorphism. -/
theorem isIso_comparison : IsIso (Stacks.RingedSpace.comparison f A B) :=
  isIso_of_bijective_stalk_map (Stacks.RingedSpace.structureRingSheaf X)
    (Stacks.RingedSpace.comparison f A B) fun x' =>
      bijective_comparisonStalkMap f x' A B

/-- Every component of `Stacks.RingedSpace.comparisonNatTrans` is an isomorphism. This is the
instance hypothesis of `Stacks.RingedSpace.comparisonIso`, discharged. -/
instance isIso_comparisonNatTrans_app
    (P : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y) ×
      SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)) :
    IsIso ((Stacks.RingedSpace.comparisonNatTrans f).app P) :=
  isIso_comparison f P.1 P.2

/-- Stacks 01CD. For a morphism of ringed spaces `f : X ⟶ Y`, pullback of sheaves of
modules commutes with the tensor product: `f^*(A ⊗_{𝒪_Y} B) ≅ f^*A ⊗_{𝒪_X} f^*B`, as an
isomorphism of bifunctors, so naturally in both module arguments. This is
`Stacks.RingedSpace.comparisonIso` with its instance hypothesis discharged, and by
`Stacks.RingedSpace.comparison_unique` the comparison is the only candidate.

`Stacks.RingedSpace.comparisonBifunctorIso` reaches the identical statement by the other
unconditional route — discharging the Tag 0098 stalk formula — and is the same isomorphism, both
forward maps being `Stacks.RingedSpace.comparisonNatTrans f`. -/
@[stacks 01CD]
def pullbackTensorIso :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩) ⋙
        Stacks.RingedSpace.pullbackFunctor f ≅
      Functor.prod (Stacks.RingedSpace.pullbackFunctor f)
          (Stacks.RingedSpace.pullbackFunctor f) ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩) :=
  Stacks.RingedSpace.comparisonIso f

/-- The forward direction of the isomorphism of bifunctors is the comparison morphism. -/
lemma pullbackTensorIso_hom :
    (pullbackTensorIso f).hom = Stacks.RingedSpace.comparisonNatTrans f := rfl

end Stacks.PullbackTensorIso

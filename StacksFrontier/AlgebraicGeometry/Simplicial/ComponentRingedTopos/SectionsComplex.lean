module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology on ringed simplicial sites

Let `S` be a simplicial-site situation, `O` a sheaf of rings on its total site and `F` a sheaf of
`O`-modules. Applying `Hom_O(-, F)` to the resolution `… → g_{1!} O_1 → g_{0!} O_0 → O` of the
structure sheaf, and using the identifications `Hom(O, F) = Γ(C_total, F)` and
`Hom(g_{n!} O_n, F) = Γ(C_n, F_n)`, gives the complex

`0 → Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1) → …`

It is exact in degrees `-1` and `0` for every `F`, because `Hom(-, F)` is left exact and the
augmentation is epi, and exact everywhere when `F` is an injective `O`-module.

## Main definitions

Names below are in the namespace `CategoryTheory.SimplicialSiteSituation`.

* `SimplicialModuleResolution.sectionsComplex`: the complex displayed above, whose term in index
  `n + 1` is the type `componentSections S O ⦋n⦌ F` of sections of `F` over the `n`-th component.

## Main results

* `SimplicialModuleResolution.sectionsComplex_exactAt_le_one`: the complex is exact in degrees
  `-1` and `0`, with no hypothesis on `F`.
* `SimplicialModuleResolution.sectionsComplex_acyclic`: the complex is exact everywhere when `F`
  is an injective `O`-module.
* `exists_sectionsComplex`: the three assertions above for the resolution of Stacks 0D9B, which
  exists for every `S` and `O`.

## Implementation notes

The complex is indexed by `ℕ`, with `Γ(C_total, F)` in index `0` and `Γ(C_n, F_n)` in index
`n + 1`; the source's degrees `-1` and `0` are indices `0` and `1`. Exactness in index `0` says
that `Γ(C_total, F) → Γ(C_0, F_0)` is injective, which is the leading `0 →` of the displayed
complex. This indexing is Mathlib's `ChainComplex.augment` convention, used here on the resolution
side as well.

The group structure on `Γ(C_n, F_n)` is carried over from `Hom(g_{n!} O_n, F)` along the universal
property `homSectionsEquiv`, which is the identification the source's proof invokes. It is the
pointwise structure: `sectionsEval` exhibits evaluation at an object of the `n`-th component as a
homomorphism of abelian groups.

Coefficients sit at the site universe, as for the resolution of Stacks 0D9B.

## References

* [Stacks Project, Tag 0D9C](https://stacks.math.columbia.edu/tag/0D9C)
* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}

/-- Precomposition with `u : X ⟶ Y`, as a homomorphism of abelian groups
`Hom(Y, F) ⟶ Hom(X, F)`. -/
public def precompHom {X Y : SheafOfModules.{u} O} (u : X ⟶ Y) (F : SheafOfModules.{u} O) :
    AddCommGrpCat.of (Y ⟶ F) ⟶ AddCommGrpCat.of (X ⟶ F) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun ψ => u ≫ ψ) (fun a b => by simp))

/-- `precompHom u F` sends `ψ : Y ⟶ F` to `u ≫ ψ`. -/
@[simp]
public lemma precompHom_apply {X Y : SheafOfModules.{u} O} (u : X ⟶ Y)
    (F : SheafOfModules.{u} O) (ψ : Y ⟶ F) : precompHom u F ψ = u ≫ ψ :=
  rfl

/-- Precomposition is contravariantly functorial: precomposing with `v` and then with `u` is
precomposing with `u ≫ v`. -/
public lemma precompHom_comp {X Y Z : SheafOfModules.{u} O} (u : X ⟶ Y) (v : Y ⟶ Z)
    (F : SheafOfModules.{u} O) :
    precompHom v F ≫ precompHom u F = precompHom (u ≫ v) F :=
  ConcreteCategory.ext_apply (fun ψ => (Category.assoc u v ψ).symm)

/-- Precomposition with the zero morphism is the zero homomorphism. -/
@[simp]
public lemma precompHom_zero {X Y : SheafOfModules.{u} O} (F : SheafOfModules.{u} O) :
    precompHom (0 : X ⟶ Y) F = 0 := by
  refine ConcreteCategory.ext_apply (fun ψ => ?_)
  show (0 : X ⟶ Y) ≫ ψ = _
  rw [Limits.zero_comp]
  simp

/-- The cochain complex `Hom(C_•, F)` obtained from a chain complex `C_•` of `O`-modules by
applying `Hom(-, F)` termwise. -/
public def homComplex (C : ChainComplex (SheafOfModules.{u} O) ℕ) (F : SheafOfModules.{u} O) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (fun n => AddCommGrpCat.of (C.X n ⟶ F))
    (fun n => precompHom (C.d (n + 1) n) F)
    (fun n => by rw [precompHom_comp, C.d_comp_d, precompHom_zero])

/-- The differential `Hom(C_n, F) ⟶ Hom(C_{n+1}, F)` of `homComplex C F` is precomposition with
`C.d (n + 1) n`. -/
@[simp]
public lemma homComplex_d (C : ChainComplex (SheafOfModules.{u} O) ℕ)
    (F : SheafOfModules.{u} O) (n : ℕ) :
    (homComplex C F).d n (n + 1) = precompHom (C.d (n + 1) n) F := by
  dsimp only [homComplex]
  exact CochainComplex.of_d _ _ n

/-- The differential of `homComplex C F` sends `ψ : C_n ⟶ F` to `C.d (n + 1) n ≫ ψ`. -/
public lemma homComplex_d_apply (C : ChainComplex (SheafOfModules.{u} O) ℕ)
    (F : SheafOfModules.{u} O) (n : ℕ) (ψ : C.X n ⟶ F) :
    (homComplex C F).d n (n + 1) ψ = C.d (n + 1) n ≫ ψ := by
  rw [homComplex_d]
  rfl

/-- `Hom(C_•, F)` is exact in index `0` as soon as `C_1 → C_0` is epi: precomposition with an
epimorphism is injective. -/
public lemma homComplex_exactAt_zero (C : ChainComplex (SheafOfModules.{u} O) ℕ)
    (F : SheafOfModules.{u} O) (h : Epi (C.d 1 0)) : (homComplex C F).ExactAt 0 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero
    ((ComplexShape.up ℕ).next_eq' (by simp))]
  refine (ShortComplex.exact_iff_mono _ ((homComplex C F).shape 0 0 (by simp))).2 ?_
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b hab
  exact (cancel_epi (C.d 1 0)).mp
    (((homComplex_d_apply C F 0 a).symm.trans hab).trans (homComplex_d_apply C F 0 b))

/-- `Hom(C_•, F)` is exact in index `n + 1` as soon as every `ψ : C_{n+1} ⟶ F` killing
`C_{n+2} → C_{n+1}` factors through `C_{n+1} → C_n`. -/
public lemma homComplex_exactAt_succ (C : ChainComplex (SheafOfModules.{u} O) ℕ)
    (F : SheafOfModules.{u} O) (n : ℕ)
    (h : ∀ ψ : C.X (n + 1) ⟶ F, C.d (n + 2) (n + 1) ≫ ψ = 0 →
      ∃ χ : C.X n ⟶ F, C.d (n + 1) n ≫ χ = ψ) :
    (homComplex C F).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n)
    ((ComplexShape.up ℕ).next_eq' (by simp)), ShortComplex.ab_exact_iff]
  intro ψ hψ
  obtain ⟨χ, hχ⟩ := h ψ ((homComplex_d_apply C F (n + 1) ψ).symm.trans hψ)
  exact ⟨χ, (homComplex_d_apply C F n χ).trans hχ⟩

namespace SimplicialModuleResolution

variable (D : SimplicialModuleResolution S O) (F : SheafOfModules.{u} O)

/-- The resolution of Stacks 0D9B with the structure sheaf adjoined in degree `-1`, indexed by
`ℕ` with `O` in index `0` and `g_{n!} O_n` in index `n + 1`. -/
public def augmentedComplex : ChainComplex (SheafOfModules.{u} O) ℕ :=
  ChainComplex.augment D.complex D.augmentation D.augmentation_comp

/-- The group `Γ(C_n, F_n)` of sections of `F` over the `n`-th component, with the structure of
`Hom(g_{n!} O_n, F)` carried over along the universal property `homSectionsEquiv`. -/
public def sectionsGrp (n : ℕ) : AddCommGrpCat.{u} :=
  @AddCommGrpCat.of (componentSections S O ⦋n⦌ F)
    (Equiv.addCommGroup (D.homSectionsEquiv n F).symm)

/-- The terms of the complex of Stacks 0D9C: `Γ(C_total, F) = Hom(O, F)` in index `0`, and
`Γ(C_n, F_n)` in index `n + 1`. -/
public def sectionsObj : ℕ → AddCommGrpCat.{u}
  | 0 => AddCommGrpCat.of (SheafOfModules.unit O ⟶ F)
  | (n + 1) => D.sectionsGrp F n

/-- Termwise identification of the terms of the complex with `Hom(-, F)` of the augmented
resolution. -/
public def sectionsIso : ∀ i, D.sectionsObj F i ≅ (homComplex D.augmentedComplex F).X i
  | 0 => Iso.refl _
  | (n + 1) => AddEquiv.toAddCommGrpIso (Equiv.addEquiv (D.homSectionsEquiv n F).symm)

/-- Evaluation of `ψ : Hom(g_{n!} O_n, F)` at the identity-labelled generator over `U`, as a
homomorphism of abelian groups. -/
public def homEvalGen (n : ℕ) (U : (S.component ⦋n⦌)ᵒᵖ) :
    AddCommGrpCat.of (D.complex.X n ⟶ F) ⟶
      F.val.presheaf.obj ((componentFunctor S ⦋n⦌).op.obj U) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun ψ : D.complex.X n ⟶ F =>
    (((D.degreeIso n).inv ≫ ψ.val).app ((componentFunctor S ⦋n⦌).op.obj U))
      (componentGenerator S O ⦋n⦌ U)) (fun a b => by simp))

/-- Evaluation of a section of `F` over the `n`-th component at an object `U`, as a homomorphism
of abelian groups: the group structure on `Γ(C_n, F_n)` is the pointwise one. -/
public def sectionsEval (n : ℕ) (U : (S.component ⦋n⦌)ᵒᵖ) :
    D.sectionsGrp F n ⟶ F.val.presheaf.obj ((componentFunctor S ⦋n⦌).op.obj U) :=
  (D.sectionsIso F (n + 1)).hom ≫ D.homEvalGen F n U

/-- `sectionsEval F n U` sends a section `a` of `F` over the `n`-th component to its value
`a.val U` at `U`. -/
@[simp]
public lemma sectionsEval_apply (n : ℕ) (U : (S.component ⦋n⦌)ᵒᵖ)
    (a : componentSections S O ⦋n⦌ F) : D.sectionsEval F n U a = a.val U := by
  have h := D.homSectionsEquiv_apply n F ((D.homSectionsEquiv n F).symm a) U
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  rfl

/-- **Stacks 0D9C.** The canonical complex

`0 → Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1) → …`

obtained by applying `Hom(-, F)` to the resolution `… → g_{1!} O_1 → g_{0!} O_0 → O`. Its term in
index `0` is `Hom(O, F) = Γ(C_total, F)` and its term in index `n + 1` is `Γ(C_n, F_n)`. -/
@[stacks 0D9C "the complex"]
public def sectionsComplex : CochainComplex AddCommGrpCat.{u} ℕ where
  X := D.sectionsObj F
  d i j := (D.sectionsIso F i).hom ≫ (homComplex D.augmentedComplex F).d i j ≫
    (D.sectionsIso F j).inv
  shape i j h := by rw [(homComplex D.augmentedComplex F).shape i j h]; simp
  d_comp_d' i j k _ _ := by simp

/-- The complex of component sections is isomorphic to `Hom(-, F)` of the augmented
resolution. -/
public def sectionsComplexIso : D.sectionsComplex F ≅ homComplex D.augmentedComplex F :=
  HomologicalComplex.Hom.isoOfComponents (D.sectionsIso F)
    (fun i j _ => by simp [sectionsComplex])

/-- The term of the complex in index `0` is `Hom(O, F)`. -/
@[simp]
public lemma sectionsComplex_X_zero :
    (D.sectionsComplex F).X 0 = AddCommGrpCat.of (SheafOfModules.unit O ⟶ F) :=
  rfl

/-- The term of the complex in index `n + 1` is `D.sectionsGrp F n`. -/
@[simp]
public lemma sectionsComplex_X_succ (n : ℕ) :
    (D.sectionsComplex F).X (n + 1) = D.sectionsGrp F n :=
  rfl

/-- The term of the complex in index `n + 1` is the type of sections of `F` over the `n`-th
component. -/
public lemma sectionsGrp_type (n : ℕ) :
    (D.sectionsGrp F n : Type u) = componentSections S O ⦋n⦌ F :=
  rfl

/-- The first differential sends `χ : Hom(O, F)` to the section of `F` over `C_0` corresponding to
`ε ≫ χ`, where `ε : g_{0!} O_0 → O` is the augmentation. -/
public lemma sectionsComplex_d_zero_apply (χ : SheafOfModules.unit O ⟶ F) :
    (D.sectionsComplex F).d 0 1 χ = D.homSectionsEquiv 0 F (D.augmentation ≫ χ) := by
  simp only [sectionsComplex, sectionsIso, homComplex_d]
  rfl

/-- Under `homSectionsEquiv`, the differential `Γ(C_n, F_n) → Γ(C_{n+1}, F_{n+1})` is
precomposition with the differential `g_{n+1!} O_{n+1} → g_{n!} O_n` of the resolution. -/
public lemma sectionsComplex_d_succ_apply (n : ℕ) (s : componentSections S O ⦋n⦌ F) :
    (D.sectionsComplex F).d (n + 1) (n + 2) s =
      D.homSectionsEquiv (n + 1) F (D.complex.d (n + 1) n ≫ (D.homSectionsEquiv n F).symm s) := by
  simp only [sectionsComplex, sectionsIso, homComplex_d]
  rfl

/-- The differential of the complex is the alternating sum of the canonical face maps. -/
public lemma sectionsComplex_d_succ_apply_eq_sum (n : ℕ) (s : componentSections S O ⦋n⦌ F) :
    (D.sectionsComplex F).d (n + 1) (n + 2) s =
      D.homSectionsEquiv (n + 1) F (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (D.faceMap (SimplexCategory.δ i) ≫ (D.homSectionsEquiv n F).symm s)) := by
  rw [D.sectionsComplex_d_succ_apply F n s, D.differential_eq_sum_faceMap n]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  rfl

/-- Exactness in index `0`, i.e. in degree `-1`: the map `Γ(C_total, F) → Γ(C_0, F_0)` is
injective, because the augmentation `g_{0!} O_0 → O` is epi. -/
public lemma sectionsComplex_exactAt_zero : (D.sectionsComplex F).ExactAt 0 :=
  (homComplex_exactAt_zero D.augmentedComplex F D.augmentation_epi).of_iso
    (D.sectionsComplexIso F).symm

/-- The differentials of the augmented resolution in positive degrees are those of the
resolution. -/
private theorem augmentedComplex_d_succ_succ (n : ℕ) :
    D.augmentedComplex.d (n + 2) (n + 1) = D.complex.d (n + 1) n := by
  simp [augmentedComplex]

/-- Exactness in index `1`, i.e. in degree `0`: a section over `C_0` killed by the differential
descends to `Γ(C_total, F)`, because `g_{1!} O_1 → g_{0!} O_0 → O → 0` is exact. -/
public lemma sectionsComplex_exactAt_one : (D.sectionsComplex F).ExactAt 1 := by
  refine HomologicalComplex.ExactAt.of_iso ?_ (D.sectionsComplexIso F).symm
  refine homComplex_exactAt_succ _ _ 0 ?_
  intro ψ hψ
  rw [D.augmentedComplex_d_succ_succ 0] at hψ
  have : Epi (ShortComplex.mk (D.complex.d 1 0) D.augmentation D.augmentation_comp).g :=
    D.augmentation_epi
  obtain ⟨χ, hχ⟩ := D.exact_zero.desc' ψ hψ
  exact ⟨χ, hχ⟩

/-- Exactness in index `n + 2`, i.e. in positive degrees, for an injective `O`-module: a section
killed by the differential descends, by exactness of the resolution and injectivity of `F`. -/
public lemma sectionsComplex_exactAt_succ_succ [Injective F] (n : ℕ) :
    (D.sectionsComplex F).ExactAt (n + 2) := by
  refine HomologicalComplex.ExactAt.of_iso ?_ (D.sectionsComplexIso F).symm
  refine homComplex_exactAt_succ _ _ (n + 1) ?_
  intro ψ hψ
  rw [D.augmentedComplex_d_succ_succ (n + 1)] at hψ
  have hex : (D.complex.sc' (n + 2) (n + 1) n).Exact := by
    rw [← HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
    exact D.exact_positive (n + 1) (by omega)
  refine ⟨hex.descToInjective ψ hψ, ?_⟩
  rw [D.augmentedComplex_d_succ_succ n]
  exact hex.comp_descToInjective ψ hψ

/-- **Stacks 0D9C.** The complex `0 → Γ(C_total, F) → Γ(C_0, F_0) → …` is exact in degrees `-1`
and `0`, i.e. in indices `0` and `1`, for every sheaf of `O`-modules `F`. -/
@[stacks 0D9C "exactness in degrees -1 and 0"]
public theorem sectionsComplex_exactAt_le_one (i : ℕ) (hi : i ≤ 1) :
    (D.sectionsComplex F).ExactAt i := by
  interval_cases i
  · exact D.sectionsComplex_exactAt_zero F
  · exact D.sectionsComplex_exactAt_one F

/-- **Stacks 0D9C.** The complex `0 → Γ(C_total, F) → Γ(C_0, F_0) → …` is exact in every degree
when `F` is an injective `O`-module. -/
@[stacks 0D9C "exactness in all degrees for an injective module"]
public theorem sectionsComplex_acyclic [Injective F] : (D.sectionsComplex F).Acyclic := by
  intro i
  match i with
  | 0 => exact D.sectionsComplex_exactAt_zero F
  | 1 => exact D.sectionsComplex_exactAt_one F
  | (n + 2) => exact D.sectionsComplex_exactAt_succ_succ F n

end SimplicialModuleResolution

/-- **Stacks 0D9C.** For every sheaf of rings `O` on the total site of a simplicial-site situation
and every sheaf of `O`-modules `F` there is a complex whose term in index `0` is
`Γ(C_total, F) = Hom(O, F)` and whose term in index `n + 1` is `Γ(C_n, F_n)`, which is exact in
degrees `-1` and `0`, and exact everywhere if `F` is injective. -/
public theorem exists_sectionsComplex (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u}) (F : SheafOfModules.{u} O) :
    ∃ K : CochainComplex AddCommGrpCat.{u} ℕ,
      (K.X 0 = AddCommGrpCat.of (SheafOfModules.unit O ⟶ F)) ∧
      (∀ n : ℕ, (K.X (n + 1) : Type u) = componentSections S O ⦋n⦌ F) ∧
      (∀ i ≤ 1, K.ExactAt i) ∧ (Injective F → K.Acyclic) := by
  obtain ⟨D⟩ := nonempty_simplicialModuleResolution S O
  refine ⟨D.toSimplicialModuleResolution.sectionsComplex F, rfl, fun n => rfl,
    D.toSimplicialModuleResolution.sectionsComplex_exactAt_le_one F, fun hF => ?_⟩
  have := hF
  exact D.toSimplicialModuleResolution.sectionsComplex_acyclic F

end CategoryTheory.SimplicialSiteSituation

end

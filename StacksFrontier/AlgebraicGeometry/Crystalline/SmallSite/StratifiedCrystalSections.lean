module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPointedSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StratifiedCrystal
public import StacksFrontier.RingTheory.AdicCompletion.AdditiveFunctoriality

/-!
# The limit module of the crystal of a stratified module

Let `D` be the completed divided power envelope of the situation's own presentation and let
`E` be a stratification of a `D`-module `M` relative to the levels `T(0)_e` of the system of
[Stacks, Tag 07JN] (`...SmallSite.wholeSpaceDescentSystem`).  The quasi-inverse in the proof of
[Stacks, Proposition 60.17.4, Tag 07JH] sends `(M, E)` to the crystal
`...SmallSite.stratCrystal E`, and to see that it is a quasi-inverse one has to recover `M` from
that crystal by the recipe of [Stacks, Lemma 60.17.3, Tag 07JG], `M(ℱ) = lim_e Γ(T(0)_e, ℱ)`.
This module does so.

## Main definitions

* `...SmallSite.stratLevelEquiv E e`: **the sections of the crystal over `T(0)_e` are
  `M ⧸ p^{N+e} M`**, as `D`-modules (`D` acting on the sections through
  `...SmallSite.levelSectionsScalars`).  Over `T(0)_e` with its identity pointing the descended
  module is `Γ(T(0)_e, 𝒪) ⊗_D M`, and the structure map `D → Γ(T(0)_e, 𝒪)` is surjective with
  kernel `p^{N+e} D`; the algebra is `Crystalline.twistQuotEquiv`.
* `...SmallSite.stratLimitEquiv E hM`: for `M` `p`-adically complete, **the module of
  [Stacks, Tag 07JG] of the crystal is `M`**.  Its inverse sends `m` to the family of the sections
  `1 ⊗ m` over the levels (`...SmallSite.evalEquivOf_stratLimitEquiv_symm`).

## Main results

* `...SmallSite.stratLevelEquiv_eq_mk`: the section corresponding to `1 ⊗ m` goes to the class
  of `m`; `...SmallSite.stratLevelEquiv_restrict`: the identifications commute with the
  restrictions along the level maps and the projections of the `p`-adic tower.
* `...SmallSite.stratLimitEquiv_naturality`: the identification is natural in the stratified
  module, for the maps `...SmallSite.wholeSpaceSectionsLinearMap` of the limit modules.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u v w

namespace Crystalline

/-! ### A twisted tensor product along a surjection is a quotient -/

section TwistQuotient

variable {D : Type u} [CommRing D] {B : Type v} [CommRing B] (f : D →+* B)
  {M : Type w} [AddCommGroup M] [Module D M]

/-- On a twisted tensor product, a scalar `d` of `D` and its image `f d` act in the same way. -/
theorem ringHom_smul_twistedTensor (d : D) (z : TwistedScalars f ⊗[D] M) :
    f d • z = d • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, smul_zero]
  | tmul b m => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']; rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

variable (hf : Function.Surjective f) (J : Ideal D) (hJ : ∀ d, f d = 0 ↔ d ∈ J)

/-- **`D ⧸ J` is the twist of `B` along a surjection `f` with kernel `J`**, as `D`-modules. -/
noncomputable def quotTwistedScalarsEquiv : (D ⧸ J) ≃ₗ[D] TwistedScalars f :=
  AddEquiv.toLinearEquiv
    ((Ideal.quotEquivOfEq (Ideal.ext fun d ↦ (hJ d).symm.trans RingHom.mem_ker.symm)).trans
      (RingHom.quotientKerEquivOfSurjective hf)).toAddEquiv
    (fun d x ↦ by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
      change f (d * x) = f d * f x
      exact map_mul f d x)

/-- `quotTwistedScalarsEquiv` sends the class of `d` to `f d`. -/
theorem quotTwistedScalarsEquiv_mk (d : D) :
    quotTwistedScalarsEquiv f hf J hJ (Ideal.Quotient.mk J d) = TwistedScalars.mk f (f d) := rfl

/-- `quotTwistedScalarsEquiv` matches the units. -/
theorem quotTwistedScalarsEquiv_symm_one :
    (quotTwistedScalarsEquiv f hf J hJ).symm 1 = 1 := by
  rw [LinearEquiv.symm_apply_eq, ← map_one (Ideal.Quotient.mk J),
    quotTwistedScalarsEquiv_mk, map_one]
  rfl

/-- **The twisted tensor product along a surjection `f : D → B` with kernel `J` is `M ⧸ J M`.** -/
noncomputable def twistQuotEquiv : TwistedScalars f ⊗[D] M ≃ₗ[D] M ⧸ (J • ⊤ : Submodule D M) :=
  (TensorProduct.congr (quotTwistedScalarsEquiv f hf J hJ).symm (LinearEquiv.refl D M)).trans
    (TensorProduct.quotTensorEquivQuotSMul M J)

/-- The identification `twistQuotEquiv` sends `1 ⊗ m` to the class of `m`. -/
@[simp] theorem twistQuotEquiv_one_tmul (m : M) :
    twistQuotEquiv f hf J hJ ((1 : TwistedScalars f) ⊗ₜ[D] m) = Submodule.Quotient.mk m := by
  rw [twistQuotEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    quotTwistedScalarsEquiv_symm_one, LinearEquiv.refl_apply,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]

end TwistQuotient

namespace GlobalCrystallineSituation.SmallSite

open StratifiedDescent

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}
  [WholeSpacePresentation S hp] {M : Type u} [AddCommGroup M] [Module (envD S hp) M]
  (E : Stratification (wholeSpaceDescentSystem S hp) M)

variable (hp M) in
/-- The level `p^{N+e} M` of the `p`-adic filtration of a `D`-module, `N` the uniform shift
`Crystalline.uniformLevel` at which the levels `T(0)_e` are cut out. -/
noncomputable abbrev stratLevelSubmodule (e : ℕ) : Submodule (envD S hp) M :=
  DividedPowers.pAdicIdeal (A := envD S hp) S.p ^
    (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) • ⊤

/-! ### The sections over a level -/

/-- The sections of the crystal of `E` over the level `T(0)_e` are the descended module there,
`...SmallSite.stratSectionsEquiv` read as an additive equivalence. -/
noncomputable def stratLevelSec (e : ℕ) :
    (stratSheaf E).val.obj (op (levelObj hp 0 e)) ≃+
      E.sections ((wholeSpaceDescentSystem S hp).T0 e) :=
  (stratSectionsEquiv E (affineLevel S hp 0 e)).toAddEquiv

/-- `stratLevelSec` is `...SmallSite.stratSectionsEquiv`. -/
theorem stratLevelSec_apply (e : ℕ)
    (x : (stratSheaf E).val.obj (op (levelObj hp 0 e))) :
    stratLevelSec E e x = stratSectionsEquiv E (affineLevel S hp 0 e) x := rfl

/-- `stratLevelSec` is semilinear over the structure map `D → Γ(T(0)_e, 𝒪)`. -/
theorem stratLevelSec_smul (d : envD S hp) (e : ℕ)
    (x : (stratSheaf E).val.obj (op (levelObj hp 0 e))) :
    stratLevelSec E e (d • x) = (wholeSpaceDescentSystem S hp).a e d • stratLevelSec E e x :=
  (stratSectionsEquiv E (affineLevel S hp 0 e)).map_smul (levelSectionsScalars hp ⦋0⦌ e d) x

/-- `stratLevelSec` commutes with restriction along a map of levels. -/
theorem stratLevelSec_restrict {e e' : ℕ}
    (k : (wholeSpaceDescentSystem S hp).T0 e ⟶ (wholeSpaceDescentSystem S hp).T0 e')
    (x : (stratSheaf E).val.obj (op (levelObj hp 0 e'))) :
    stratLevelSec E e ((stratSheaf E).val.map k.hom.op x) = E.restrict k (stratLevelSec E e' x) :=
  stratSectionsEquiv_restrict E k x

/-- The structure map `D → Γ(T(0)_e, 𝒪)` of the system is surjective. -/
theorem surjective_wholeSpaceDescentSystem_a (e : ℕ) :
    Function.Surjective ((wholeSpaceDescentSystem S hp).a e) :=
  surjective_levelSectionsScalars hp ⦋0⦌ e

/-- The kernel of the structure map `D → Γ(T(0)_e, 𝒪)` of the system is `p^{N+e} D`. -/
theorem wholeSpaceDescentSystem_a_eq_zero_iff (e : ℕ) (d : envD S hp) :
    (wholeSpaceDescentSystem S hp).a e d = 0 ↔ d ∈ DividedPowers.pAdicIdeal (A := envD S hp) S.p ^
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) :=
  levelSectionsScalars_eq_zero_iff hp ⦋0⦌ e d

/-- **The sections of the crystal of a stratified module over the level `T(0)_e` are
`M ⧸ p^{N+e} M`**, as `D`-modules, `D` acting on the sections through
`...SmallSite.levelSectionsScalars`.  It is the evaluation at the identity pointing of `T(0)_e`,
landing in `Γ(T(0)_e, 𝒪) ⊗_D M`, followed by `Crystalline.twistQuotEquiv` for the structure map
`D → Γ(T(0)_e, 𝒪)`, which is surjective with kernel `p^{N+e} D`. -/
noncomputable def stratLevelEquiv (e : ℕ) :
    (stratSheaf E).val.obj (op (levelObj hp 0 e)) ≃ₗ[envD S hp]
      M ⧸ stratLevelSubmodule hp M e :=
  AddEquiv.toLinearEquiv
    (((stratLevelSec E e).trans (E.evalEquivOf (𝟙 _) ((wholeSpaceDescentSystem S hp).a e)
      ((wholeSpaceDescentSystem S hp).ptRing_id e)).toAddEquiv).trans
      (twistQuotEquiv ((wholeSpaceDescentSystem S hp).a e)
        (surjective_wholeSpaceDescentSystem_a e) _
        (wholeSpaceDescentSystem_a_eq_zero_iff e)).toAddEquiv)
    (fun d x ↦ (congrArg (twistQuotEquiv _ (surjective_wholeSpaceDescentSystem_a e) _
        (wholeSpaceDescentSystem_a_eq_zero_iff e))
      (((congrArg (E.evalEquivOf _ _ ((wholeSpaceDescentSystem S hp).ptRing_id e))
        (stratLevelSec_smul E d e x)).trans (map_smul _ _ _)).trans
          (ringHom_smul_twistedTensor _ d _))).trans (map_smul _ d _))

/-- `stratLevelEquiv` unfolded: the evaluation at the identity pointing followed by
`Crystalline.twistQuotEquiv`. -/
theorem stratLevelEquiv_apply (e : ℕ)
    (x : (stratSheaf E).val.obj (op (levelObj hp 0 e))) :
    stratLevelEquiv E e x = twistQuotEquiv ((wholeSpaceDescentSystem S hp).a e)
      (surjective_wholeSpaceDescentSystem_a e) _ (wholeSpaceDescentSystem_a_eq_zero_iff e)
      (E.evalEquivOf (𝟙 _) ((wholeSpaceDescentSystem S hp).a e)
        ((wholeSpaceDescentSystem S hp).ptRing_id e)
        (stratSectionsEquiv E (affineLevel S hp 0 e) x)) := rfl

/-- **The characterisation of `stratLevelEquiv`**: the section whose evaluation at the identity
pointing of `T(0)_e` is `1 ⊗ m` goes to the class of `m`. -/
theorem stratLevelEquiv_eq_mk (e : ℕ)
    (x : (stratSheaf E).val.obj (op (levelObj hp 0 e))) (m : M)
    (hx : E.evalEquivOf (𝟙 _) ((wholeSpaceDescentSystem S hp).a e)
      ((wholeSpaceDescentSystem S hp).ptRing_id e)
        (stratSectionsEquiv E (affineLevel S hp 0 e) x) =
      (1 : TwistedScalars _) ⊗ₜ[envD S hp] m) :
    stratLevelEquiv E e x = Submodule.Quotient.mk m := by
  rw [stratLevelEquiv_apply, hx, twistQuotEquiv_one_tmul]

/-- `stratLevelEquiv` on the section corresponding to `1 ⊗ m` through `stratLevelSec`. -/
theorem stratLevelEquiv_stratLevelSec_symm (e : ℕ) (m : M) :
    stratLevelEquiv E e ((stratLevelSec E e).symm
      ((E.evalEquiv (𝟙 _)).symm ((1 : TwistedScalars _) ⊗ₜ[envD S hp] m))) =
      Submodule.Quotient.mk m := by
  rw [stratLevelEquiv_apply, ← stratLevelSec_apply, AddEquiv.apply_symm_apply,
    Stratification.evalEquivOf_apply,
    LinearEquiv.apply_symm_apply, twistCongr_one_tmul, twistQuotEquiv_one_tmul]

/-- **The section over the level `T(0)_e` of an element `m` of `M`**: the one corresponding to
`1 ⊗ m` (`evalEquiv_stratLevelSec_stratLevelMap`), as a `D`-linear map. -/
noncomputable def stratLevelMap (e : ℕ) :
    M →ₗ[envD S hp] (stratSheaf E).val.obj (op (levelObj hp 0 e)) :=
  (stratLevelEquiv E e).symm.toLinearMap ∘ₗ Submodule.mkQ _

/-- `stratLevelEquiv` sends the section of `m` to the class of `m`. -/
theorem stratLevelEquiv_stratLevelMap (e : ℕ) (m : M) :
    stratLevelEquiv E e (stratLevelMap E e m) = Submodule.Quotient.mk m :=
  (stratLevelEquiv E e).apply_symm_apply _

/-- The section of `m` over `T(0)_e`, evaluated at the identity pointing, is `1 ⊗ m`. -/
theorem evalEquiv_stratLevelSec_stratLevelMap (e : ℕ) (m : M) :
    E.evalEquiv (𝟙 _) (stratLevelSec E e (stratLevelMap E e m)) =
      (1 : TwistedScalars _) ⊗ₜ[envD S hp] m := by
  have h : stratLevelMap E e m = (stratLevelSec E e).symm
      ((E.evalEquiv (𝟙 _)).symm ((1 : TwistedScalars _) ⊗ₜ[envD S hp] m)) :=
    (stratLevelEquiv E e).injective
      ((stratLevelEquiv_stratLevelMap E e m).trans
        (stratLevelEquiv_stratLevelSec_symm E e m).symm)
  rw [h, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- A section over `T(0)_e` whose evaluation at the identity pointing is `1 ⊗ m` is the section
of `m`. -/
private theorem eq_stratLevelMap_of_evalEquiv_eq (e : ℕ)
    (x : (stratSheaf E).val.obj (op (levelObj hp 0 e))) (m : M)
    (hx : E.evalEquiv (𝟙 _) (stratLevelSec E e x) = (1 : TwistedScalars _) ⊗ₜ[envD S hp] m) :
    x = stratLevelMap E e m :=
  (stratLevelSec E e).injective ((E.evalEquiv (𝟙 _)).injective
    (hx.trans (evalEquiv_stratLevelSec_stratLevelMap E e m).symm))

/-- The composite level map `T(0)_e ⟶ T(0)_n` of the system is the map of the levels of
`...SmallSite.wholeSpaceSystem`. -/
theorem wholeSpaceDescentSystem_levTo_hom (e n : ℕ) (hn : e ≤ n) :
    ((wholeSpaceDescentSystem S hp).levTo e n hn).hom =
      ((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map (homOfLE hn) := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [System.levTo_self, show homOfLE (le_refl e) = 𝟙 e from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id]
      rfl
  | succ n hen ih =>
      rw [System.levTo_succ _ e n hen, InducedCategory.comp_hom, ih]
      change ((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map (homOfLE hen) ≫
          ((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map (homOfLE (Nat.le_succ n)) = _
      rw [← Functor.map_comp]
      rfl

/-- **The sections of `m` over the levels are compatible with the level maps.** -/
theorem stratLevelMap_restrict {e e' : ℕ} (h : e ⟶ e') (m : M) :
    (stratSheaf E).val.map (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h).op
      (stratLevelMap E e' m) = stratLevelMap E e m := by
  set k : (wholeSpaceDescentSystem S hp).T0 e ⟶ (wholeSpaceDescentSystem S hp).T0 e' :=
    (wholeSpaceDescentSystem S hp).levTo e e' (leOfHom h) with hkdef
  have hk : k.hom = ((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h := by
    rw [hkdef, wholeSpaceDescentSystem_levTo_hom]
    rfl
  refine eq_stratLevelMap_of_evalEquiv_eq E e _ m ?_
  rw [← hk]
  refine (congrArg (E.evalEquiv (𝟙 _)) (stratLevelSec_restrict E k _)).trans ?_
  have hz := evalEquiv_stratLevelSec_stratLevelMap E e' m
  have h1 : E.evalEquiv (𝟙 _ ≫ k) (E.restrict k (stratLevelSec E e' (stratLevelMap E e' m))) =
      (1 : TwistedScalars _) ⊗ₜ[envD S hp] m := by
    rw [E.evalEquiv_restrict' k (𝟙 _) (𝟙 _ ≫ k) (by rw [Category.comp_id, Category.id_comp]),
      hz, twistMap_one_tmul]
  rw [hkdef, E.evalEquiv_levTo] at h1
  have h2 := congrArg (twistCongr ((wholeSpaceDescentSystem S hp).ptRing_levTo (𝟙 _) e'
    (leOfHom h))) h1
  rw [twistCongr_twistCongr, twistCongr_rfl, twistCongr_one_tmul] at h2
  exact h2

/-- **The identifications `stratLevelEquiv` commute with the restrictions along the level maps**
and the projections of the `p`-adic tower of `M`. -/
theorem stratLevelEquiv_restrict {e e' : ℕ} (h : e ≤ e')
    (x : (stratSheaf E).val.obj (op (levelObj hp 0 e'))) :
    stratLevelEquiv E e ((stratSheaf E).val.map
        (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map (homOfLE h)).op x) =
      AdicCompletion.transitionMap (DividedPowers.pAdicIdeal (A := envD S hp) S.p) M
        (Nat.add_le_add_left h _) (stratLevelEquiv E e' x) := by
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (stratLevelEquiv E e' x)
  obtain rfl : stratLevelMap E e' m = x :=
    (stratLevelEquiv E e').injective (by rw [stratLevelEquiv_stratLevelMap, hm])
  rw [stratLevelMap_restrict, stratLevelEquiv_stratLevelMap, stratLevelEquiv_stratLevelMap,
    PAdicCompletion.transitionMap_mk]

/-- The section of `m` over `T(0)_e` vanishes exactly when `m ∈ p^{N+e} M`. -/
theorem stratLevelMap_eq_zero_iff (e : ℕ) (m : M) :
    stratLevelMap E e m = 0 ↔ m ∈ stratLevelSubmodule hp M e := by
  rw [← (stratLevelEquiv E e).map_eq_zero_iff, stratLevelEquiv_stratLevelMap,
    Submodule.Quotient.mk_eq_zero]

/-! ### The limit module -/

/-- **The map `M → lim_e Γ(T(0)_e, ℱ)`** to the module of [Stacks, Tag 07JG] of the crystal of
`E`, sending `m` to the family of its sections `stratLevelMap`. -/
noncomputable def stratToLimit :
    M →ₗ[envD S hp] wholeSpaceSections hp (stratCrystal E) ⦋0⦌ where
  toFun m := wholeSpaceSectionsMk hp (stratCrystal E) (fun e ↦ stratLevelMap E e m)
    (fun h ↦ stratLevelMap_restrict E h m)
  map_add' x y := wholeSpaceSectionsVal_injective hp (stratCrystal E) fun e ↦ by
    rw [wholeSpaceSectionsVal_add]
    exact map_add (stratLevelMap E e) x y
  map_smul' d x := wholeSpaceSectionsVal_injective hp (stratCrystal E) fun e ↦ by
    rw [RingHom.id_apply, wholeSpaceSectionsVal_smul]
    exact map_smul (stratLevelMap E e) d x

/-- The components of `stratToLimit m` are the sections of `m`. -/
theorem wholeSpaceSectionsVal_stratToLimit (m : M) (e : ℕ) :
    wholeSpaceSectionsVal hp (stratCrystal E) (stratToLimit E m) e = stratLevelMap E e m := rfl

/-- `stratToLimit` is injective for `M` separated, a fortiori for `M` `p`-adically complete. -/
theorem injective_stratToLimit (hM : IsPAdicallyComplete S.p (envD S hp) M) :
    Function.Injective (stratToLimit E) := by
  have : IsAdicComplete (DividedPowers.pAdicIdeal (A := envD S hp) S.p) M := hM
  refine (injective_iff_map_eq_zero _).mpr fun m hm ↦ ?_
  refine IsHausdorff.haus' (I := DividedPowers.pAdicIdeal (A := envD S hp) S.p) m fun n ↦ ?_
  have hn : stratLevelMap E n m = 0 :=
    congrArg (fun x ↦ wholeSpaceSectionsVal hp (stratCrystal E) x n) hm
  rw [SModEq.zero]
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    ((stratLevelMap_eq_zero_iff E n m).mp hn)

/-- `stratToLimit` is surjective for `M` `p`-adically complete: lifts of the components of a
compatible family form a `p`-adic Cauchy sequence, whose limit maps to the family. -/
theorem surjective_stratToLimit (hM : IsPAdicallyComplete S.p (envD S hp) M) :
    Function.Surjective (stratToLimit E) := by
  have : IsAdicComplete (DividedPowers.pAdicIdeal (A := envD S hp) S.p) M := hM
  intro x
  choose mm hmm using fun e ↦ Submodule.Quotient.mk_surjective _
    (stratLevelEquiv E e (wholeSpaceSectionsVal hp (stratCrystal E) x e))
  have hcompat : ∀ {a b : ℕ}, a ≤ b → mm b ≡ mm a [SMOD stratLevelSubmodule hp M a] := by
    intro a b hab
    calc Submodule.Quotient.mk (mm b)
        = AdicCompletion.transitionMap (DividedPowers.pAdicIdeal (A := envD S hp) S.p) M
            (Nat.add_le_add_left hab _) (Submodule.Quotient.mk (mm b)) :=
          (PAdicCompletion.transitionMap_mk _ _ _ _).symm
      _ = AdicCompletion.transitionMap (DividedPowers.pAdicIdeal (A := envD S hp) S.p) M
            (Nat.add_le_add_left hab _)
            (stratLevelEquiv E b (wholeSpaceSectionsVal hp (stratCrystal E) x b)) := by
          rw [hmm b]
      _ = stratLevelEquiv E a ((stratSheaf E).val.map
            (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map (homOfLE hab)).op
              (wholeSpaceSectionsVal hp (stratCrystal E) x b)) :=
          (stratLevelEquiv_restrict E hab _).symm
      _ = stratLevelEquiv E a (wholeSpaceSectionsVal hp (stratCrystal E) x a) :=
          congrArg (stratLevelEquiv E a)
            (wholeSpaceSectionsVal_restrict hp (stratCrystal E) x (homOfLE hab))
      _ = Submodule.Quotient.mk (mm a) := (hmm a).symm
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := DividedPowers.pAdicIdeal (A := envD S hp) S.p) mm
    (fun {a b} hab ↦ ((hcompat hab).mono
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))).symm)
  refine ⟨L, wholeSpaceSectionsVal_injective hp (stratCrystal E) fun e ↦ ?_⟩
  refine (stratLevelEquiv E e).injective ?_
  refine (stratLevelEquiv_stratLevelMap E e L).trans ?_
  rw [← hmm e]
  exact ((hL _).symm.trans (hcompat (by omega : e ≤
    _root_.Crystalline.uniformLevel (affineSituation S hp) + e)))

/-- **The limit module of the crystal of a `p`-adically complete stratified module is the
module**: `lim_e Γ(T(0)_e, ℱ) ≅ M` for `ℱ = ...SmallSite.stratCrystal E`, the inverse of
`stratToLimit`. -/
noncomputable def stratLimitEquiv (hM : IsPAdicallyComplete S.p (envD S hp) M) :
    wholeSpaceSections hp (stratCrystal E) ⦋0⦌ ≃ₗ[envD S hp] M :=
  (LinearEquiv.ofBijective (stratToLimit E)
    ⟨injective_stratToLimit E hM, surjective_stratToLimit E hM⟩).symm

/-- The inverse of `stratLimitEquiv` is `stratToLimit`. -/
theorem stratLimitEquiv_symm_apply (hM : IsPAdicallyComplete S.p (envD S hp) M) (m : M) :
    (stratLimitEquiv E hM).symm m = stratToLimit E m := rfl

/-- The components of the inverse of `stratLimitEquiv` are the sections of `m`. -/
theorem wholeSpaceSectionsVal_stratLimitEquiv_symm
    (hM : IsPAdicallyComplete S.p (envD S hp) M) (m : M) (e : ℕ) :
    wholeSpaceSectionsVal hp (stratCrystal E) ((stratLimitEquiv E hM).symm m) e =
      stratLevelMap E e m := rfl

/-- The component at the level `e` of the element of the limit module corresponding to `m` is the
section whose evaluation at the identity pointing of `T(0)_e` is `1 ⊗ m`. -/
theorem evalEquiv_stratLimitEquiv_symm (hM : IsPAdicallyComplete S.p (envD S hp) M)
    (m : M) (e : ℕ) :
    E.evalEquiv (𝟙 _) (stratSectionsEquiv E (affineLevel S hp 0 e)
        (wholeSpaceSectionsVal hp (stratCrystal E) ((stratLimitEquiv E hM).symm m) e)) =
      (1 : TwistedScalars _) ⊗ₜ[envD S hp] m :=
  evalEquiv_stratLevelSec_stratLevelMap E e m

/-- **The characterisation of `stratLimitEquiv`**: the component at the level `e` of the element
corresponding to `m` is the section `1 ⊗ m` of `Γ(T(0)_e, 𝒪) ⊗_D M`, the twist being along the
structure map `D → Γ(T(0)_e, 𝒪)`. -/
theorem evalEquivOf_stratLimitEquiv_symm (hM : IsPAdicallyComplete S.p (envD S hp) M)
    (m : M) (e : ℕ) :
    E.evalEquivOf (𝟙 _) ((wholeSpaceDescentSystem S hp).a e)
        ((wholeSpaceDescentSystem S hp).ptRing_id e)
        (stratSectionsEquiv E (affineLevel S hp 0 e)
          (wholeSpaceSectionsVal hp (stratCrystal E) ((stratLimitEquiv E hM).symm m) e)) =
      (1 : TwistedScalars _) ⊗ₜ[envD S hp] m :=
  (congrArg (twistCongr ((wholeSpaceDescentSystem S hp).ptRing_id e))
    (evalEquiv_stratLimitEquiv_symm E hM m e)).trans
      (twistCongr_one_tmul ((wholeSpaceDescentSystem S hp).ptRing_id e) m)

/-- The component at the level `e` of an element `x` of the limit module is the class of
`stratLimitEquiv x` modulo `p^{N+e}`. -/
theorem stratLevelEquiv_wholeSpaceSectionsVal (hM : IsPAdicallyComplete S.p (envD S hp) M)
    (x : wholeSpaceSections hp (stratCrystal E) ⦋0⦌) (e : ℕ) :
    stratLevelEquiv E e (wholeSpaceSectionsVal hp (stratCrystal E) x e) =
      Submodule.Quotient.mk (stratLimitEquiv E hM x) := by
  conv_lhs => rw [← (stratLimitEquiv E hM).symm_apply_apply x]
  exact stratLevelEquiv_stratLevelMap E e _

/-! ### Naturality -/

/-- The identification `stratLevelSec` is natural in the stratified module. -/
theorem stratLevelSec_naturality {X Y : StratModule S hp} (f : X ⟶ Y) (e : ℕ)
    (x : (stratSheaf X.strat).val.obj (op (levelObj hp 0 e))) :
    stratLevelSec Y.strat e
      ((((quasiCoherentCrystalι S).map (stratCrystalFunctor.map f)).val.app
        (op (levelObj hp 0 e))).hom x) =
      X.strat.mapSections Y.strat (StratModule.Hom.toLinearMap f) (StratModule.Hom.comm f) _
        (stratLevelSec X.strat e x) :=
  congrArg (fun φ ↦ (φ.val.app (op (affineLevel S hp 0 e))).hom x)
    ((affineModuleEquivalence S).counit.naturality (stratAffineSheafMap f))

/-- The sections of elements over the levels are natural in the stratified module. -/
theorem stratLevelMap_naturality {X Y : StratModule S hp} (f : X ⟶ Y) (e : ℕ)
    (m : X.carrier) :
    (((quasiCoherentCrystalι S).map (stratCrystalFunctor.map f)).val.app
        (op (levelObj hp 0 e))).hom (stratLevelMap X.strat e m) =
      stratLevelMap Y.strat e (StratModule.Hom.toLinearMap f m) := by
  refine eq_stratLevelMap_of_evalEquiv_eq Y.strat e _ _ ?_
  rw [stratLevelSec_naturality, Stratification.evalEquiv_mapSections,
    evalEquiv_stratLevelSec_stratLevelMap, LinearMap.lTensor_tmul]

/-- **Naturality of `stratLimitEquiv`**: for a morphism `f` of stratified modules, the map of
limit modules induced by the morphism of crystals `stratCrystalFunctor.map f` is `f`. -/
theorem stratLimitEquiv_naturality {X Y : StratModule S hp} (f : X ⟶ Y)
    (hX : IsPAdicallyComplete S.p (envD S hp) X.carrier)
    (hY : IsPAdicallyComplete S.p (envD S hp) Y.carrier)
    (x : wholeSpaceSections hp (stratCrystal X.strat) ⦋0⦌) :
    stratLimitEquiv Y.strat hY (wholeSpaceSectionsLinearMap hp (stratCrystalFunctor.map f) x) =
      StratModule.Hom.toLinearMap f (stratLimitEquiv X.strat hX x) := by
  obtain ⟨m, rfl⟩ := (stratLimitEquiv X.strat hX).symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearEquiv.eq_symm_apply _).mp
    (wholeSpaceSectionsVal_injective hp _ fun e ↦ stratLevelMap_naturality f e m)

/-- `stratLimitEquiv_naturality` as an equality of linear maps. -/
theorem stratLimitEquiv_comp_wholeSpaceSectionsLinearMap {X Y : StratModule S hp} (f : X ⟶ Y)
    (hX : IsPAdicallyComplete S.p (envD S hp) X.carrier)
    (hY : IsPAdicallyComplete S.p (envD S hp) Y.carrier) :
    (stratLimitEquiv Y.strat hY).toLinearMap ∘ₗ
        wholeSpaceSectionsLinearMap hp (stratCrystalFunctor.map f) =
      StratModule.Hom.toLinearMap f ∘ₗ (stratLimitEquiv X.strat hX).toLinearMap :=
  LinearMap.ext (stratLimitEquiv_naturality f hX hY)

end GlobalCrystallineSituation.SmallSite

end Crystalline

end

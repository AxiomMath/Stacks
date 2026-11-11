module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ClassifyingStackDirectImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardOfStacksProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheafLqcFbcUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineObjectStructureSheafVanishingUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ProductStructureSheafNotLocallyQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.CohomologySheafOfProducts
public import StacksFrontier.AlgebraicTopology.TrivialBarComplexZModTwo
public import StacksFrontier.Examples.Stacks.ClassifyingStackConstantZ2

/-!
# The unbounded derived direct image does not preserve quasi-coherent cohomology

Let `k = 𝔽₂`, `S = Spec k[x]`, `G = (ℤ/2)_S` the constant group acting trivially on `S`,
`𝒳 = BG = [S/G]` and `f : 𝒳 ⟶ S` the structure morphism, which is quasi-compact and
quasi-separated. Put `E = ∏_{m ≥ 0} 𝒪_𝒳[m]`, the product taken in `D(𝒪_𝒳)`. Then:

* every cohomology sheaf of `E` is `𝒪_𝒳` or zero, because the structure sheaf has no higher
  cohomology over objects lying over affine schemes, so `E` lies in `D_{LQCoh^fbc}(𝒪_𝒳)`;
* `Rf_*` commutes with products and shifts, and `Rf_*𝒪_𝒳` is computed by the inhomogeneous
  cochain complex of `ℤ/2` with trivial coefficients `𝒪_S`, which in characteristic `2` is
  homotopy equivalent to the complex with `𝒪_S` in every degree `n ≥ 0` and zero differential;
  hence `Rf_*𝒪_𝒳 ≅ ∏_{n ≥ 0} 𝒪_S[-n]` and `Rf_*E ≅ ∏_{m, n ≥ 0} 𝒪_S[m - n]`;
* so `H⁰(Rf_*E) ≅ ∏_{m = n} 𝒪_S ≅ ∏_ℕ 𝒪_S`, which is not locally quasi-coherent.

Therefore `Rf_*E` is not in `D_{LQCoh^fbc}(𝒪_S)`: a quasi-compact, quasi-separated morphism of
algebraic stacks need not map `D_{LQCoh^fbc}` into `D_{LQCoh^fbc}`. This is the discussion of
**Stacks 07DC** with `p = 2`, the content of **Stacks 07DD**.

## Main definitions

* `Stacks.Examples.UnboundedDerivedPushforward.zeroDiffComplexIntIso`: the two incarnations of
  the complex with zero differential and a fixed object in every degree `n ≥ 0` agree.
* `Stacks.Examples.UnboundedDerivedPushforward.barCochainComplexIntIsoPi`: in characteristic
  `2`, the cochain complex of `ℤ/2` with coefficients in an acyclic sheaf `F` represents
  `∏_n F[-n]` in the derived category.
* `Stacks.Examples.UnboundedDerivedPushforward.piShiftPiShiftIso`: a product of shifts of
  products of shifts is a product over `ℕ × ℕ` of shifts.
* `Stacks.Examples.UnboundedDerivedPushforward.shiftedStructureSheafProduct`: the object
  `E = ∏_{m ≥ 0} 𝒪_𝒳[m]` of `D(𝒪_𝒳)`.

## Main results

* `Stacks.Examples.UnboundedDerivedPushforward.shiftedStructureSheafProduct_mem`: `E` lies in
  `D_{LQCoh^fbc}(𝒪_𝒳)`, for every algebraic stack `𝒳`.
* `Stacks.Examples.UnboundedDerivedPushforward.not_mem_derivedPushforward_of_iso`: for any
  morphism `f : 𝒳 ⟶ S` of algebraic stacks over `S = Spec k[x]`, `k` nontrivial with `2 = 0`,
  such that `Rf_*𝒪_𝒳` is computed by the cochain complex of `ℤ/2` with coefficients `𝒪_S`, the
  object `Rf_*E` is not in `D_{LQCoh^fbc}(𝒪_S)`.
* `not_forall_derivedPushforward_mem_derivedLocallyQuasicoherentFlatBaseChange` (in the same
  namespace):
  **Stacks 07DD**, it is not true that every quasi-compact, quasi-separated morphism of algebraic
  stacks sends `D_{LQCoh^fbc}` into `D_{LQCoh^fbc}` under `Rf_*`; the witness is
  `f : B(ℤ/2)_S ⟶ S` over `S = Spec 𝔽₂[x]`, for which the hypothesis of
  `not_mem_derivedPushforward_of_iso` is
  `AlgebraicGeometry.Stack.ClassifyingZModTwo.derivedPushforwardStructureModuleIso` combined with
  `AlgebraicGeometry.Stack.ClassifyingZModTwo.cechCosimplicialIso`.

## Implementation notes

The derived categories are those at module universe `u + 1`, where the unbounded derived direct
image `AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacks` is defined, and `𝒪` is the
structure sheaf with its sections lifted to that universe. The field `𝔽₂` is
`ULift (ZMod 2)`, so that it lives in the universe of the schemes.

## References

* [Stacks Project, Tag 07DD](https://stacks.math.columbia.edu/tag/07DD)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Stack
open Stacks.Cohomology.CohomologySheafOfProducts Stacks.GroupCohomology.TrivialBar

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck and
enough-injectives counterparts leave a stuck universe constraint against the modules at the
pinned universe `u + 1`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

universe u w u₁ v₁ r v t d

namespace Stacks.Examples.UnboundedDerivedPushforward

/-! ### The complex with zero differential -/

section ZeroDifferential

variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A] [HasFiniteProducts A]

omit [HasFiniteProducts A] in
/-- The differentials of `zeroDiffComplexInt F` vanish. -/
theorem zeroDiffComplexInt_d (F : A) (i j : ℤ) : (zeroDiffComplexInt F).d i j = 0 := by
  rcases i with m | m
  · rcases j with m' | m'
    · rw [HomologicalComplex.extend_d_eq (zeroDiffComplex F) ComplexShape.embeddingUpNat
        (i' := Int.ofNat m) (j' := Int.ofNat m') (i := m) (j := m') rfl rfl,
        zeroDiffComplex_d, Limits.zero_comp, Limits.comp_zero]
    · refine (HomologicalComplex.isZero_extend_X _ _ _ fun i hi => ?_).eq_of_tgt _ _
      have := Int.negSucc_lt_zero m'
      simp only [ComplexShape.embeddingUpNat_f] at hi
      omega
  · refine (HomologicalComplex.isZero_extend_X _ _ _ fun i hi => ?_).eq_of_src _ _
    have := Int.negSucc_lt_zero m
    simp only [ComplexShape.embeddingUpNat_f] at hi
    omega

/-- The complex `zeroDiffComplexInt F` (the extension to `ℤ` of the complex with `F` in every
degree `n ≥ 0` and zero differential) is the complex `zeroDifferentialComplex F`. -/
def zeroDiffComplexIntIso (F : A) : zeroDiffComplexInt F ≅ zeroDifferentialComplex F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => match n with
      | Int.ofNat m => (zeroDiffComplex F).extendXIso ComplexShape.embeddingUpNat (i := m) rfl
      | Int.negSucc m => (HomologicalComplex.isZero_extend_X _ _ _ fun i hi => by
          have := Int.negSucc_lt_zero m
          simp only [ComplexShape.embeddingUpNat_f] at hi
          omega).iso (isZero_zeroDifferentialComplex_X F (Int.negSucc_lt_zero m)))
    (fun i j _ => by simp [zeroDiffComplexInt_d])

end ZeroDifferential

/-! ### The cochain complex of `ℤ/2` in characteristic `2` -/

section Sheaves

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- On a sheaf of modules over a sheaf of rings in which `2 = 0`, twice the identity is zero. -/
theorem two_zsmul_id_eq_zero [HasSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}] (M : SheafOfModules.{v} R)
    (h : ∀ X, (2 : R.obj.obj X) = 0) : (2 : ℤ) • 𝟙 M = 0 := by
  rw [two_zsmul]
  ext X m
  change m + m = 0
  rw [← two_smul (R.obj.obj X) m, h X, zero_smul]

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [IsGrothendieckAbelian.{t} (SheafOfModules.{v} R)] [HasDerivedCategory.{d} (SheafOfModules.{v} R)]

/-- **The cochain complex of `ℤ/2` with trivial coefficients, in characteristic `2`.** If `F` is
acyclic on the objects of a covering class and `2 = 0` on `F`, the inhomogeneous cochain
complex of `ℤ/2` with coefficients `F` represents the product `∏_n F[0]⟦-n⟧` in the derived
category: it is homotopy equivalent to the complex with zero differential and `F` in every
degree `n ≥ 0`. -/
def barCochainComplexIntIsoPi {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    (F : SheafOfModules.{v} R)
    (hF : ∀ ⦃U : C⦄, B U → ∀ q : ℕ, 0 < q →
      IsZero (((_root_.SheafOfModules.evaluation R (op U)).rightDerived q).obj F))
    (h2 : (2 : ℤ) • 𝟙 F = 0) :
    DerivedCategory.Q.obj (barCochainComplexInt F) ≅
      ∏ᶜ fun n : ℕ => ((DerivedCategory.singleFunctor _ 0).obj F)⟦-(n : ℤ)⟧ :=
  haveI := isIso_zeroDifferentialComplexToPi hB F hF
  haveI : IsIso (DerivedCategory.Q.map (homotopyEquivZeroDiffComplexInt h2).hom) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  (asIso (DerivedCategory.Q.map (homotopyEquivZeroDiffComplexInt h2).hom)).symm ≪≫
    DerivedCategory.Q.mapIso (zeroDiffComplexIntIso F) ≪≫ asIso (zeroDifferentialComplexToPi F)

end Sheaves

/-! ### Products of shifts of products of shifts -/

section Products

variable {D : Type*} [Category* D] [HasShift D ℤ] [HasProductsOfShape ℕ D]
  [HasProductsOfShape (ℕ × ℕ) D]

/-- `∏_m (∏_n X⟦b n⟧)⟦a m⟧ ≅ ∏_{(m, n)} X⟦b n + a m⟧`: the shift functors are equivalences, hence
commute with products, and an iterated product is a product over the product index type. -/
def piShiftPiShiftIso (X : D) (a b : ℕ → ℤ) :
    (∏ᶜ fun m : ℕ => (∏ᶜ fun n : ℕ => X⟦b n⟧)⟦a m⟧) ≅
      ∏ᶜ fun p : ℕ × ℕ => X⟦b p.2 + a p.1⟧ :=
  haveI : HasProductsOfShape (Σ _ : ℕ, ℕ) D :=
    hasLimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.sigmaEquivProd ℕ ℕ).symm)
  Pi.mapIso (fun m => PreservesProduct.iso (shiftFunctor D (a m)) (fun n => X⟦b n⟧) ≪≫
      Pi.mapIso fun n => (shiftFunctorAdd' D (b n) (a m) _ rfl).symm.app X) ≪≫
    piPiIso (fun _ : ℕ => ℕ) (fun m n => X⟦b n + a m⟧) ≪≫
    Pi.whiskerEquiv (f := fun p : Σ _ : ℕ, ℕ => X⟦b p.2 + a p.1⟧)
      (g := fun p : ℕ × ℕ => X⟦b p.2 + a p.1⟧) (Equiv.sigmaEquivProd ℕ ℕ) fun _ => Iso.refl _

end Products

/-- The diagonal `{(m, n) | -n + m = 0}` of `ℕ × ℕ` is a copy of `ℕ`. -/
def diagonalEquiv : {p : ℕ × ℕ // -(p.2 : ℤ) + p.1 = -0} ≃ ℕ where
  toFun s := s.1.1
  invFun n := ⟨(n, n), by simp⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    obtain rfl : a = b := by omega
    rfl
  right_inv _ := rfl

/-! ### Characteristic `2` on the affine line -/

section CharTwo

/-- If `2 = 0` in `Γ(S, 𝒪_S)`, then `2 = 0` in the ring of sections of the structure sheaf of a
category fibred in groupoids over `S`, over every object. -/
theorem two_eq_zero_ringStructureSheafCore {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {𝒳 : Type*} [Category* 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (τ : SiteKind) (h2 : (2 : Γ(S, ⊤)) = 0) (X : 𝒳ᵒᵖ) :
    (2 : (FibredSite.ringStructureSheafCore B S hS p hp τ).obj.obj X) = 0 := by
  let Y := (Over.post B.inclusion).obj (p.obj X.unop)
  change (2 : Γ(Y.left, ⊤)) = 0
  calc (2 : Γ(Y.left, ⊤)) = Y.hom.appTop.hom 2 := (map_ofNat _ 2).symm
    _ = Y.hom.appTop.hom 0 := congrArg _ h2
    _ = 0 := map_zero _

/-- If `2 = 0` in `k`, then `2 = 0` in the global functions on `Spec k[x]`. -/
theorem two_eq_zero_Γ_spec_polynomial {k : Type u} [CommRing k] (h2 : (2 : k) = 0) :
    (2 : Γ(Spec (CommRingCat.of (Polynomial k)), ⊤)) = 0 := by
  have hk : (2 : Polynomial k) = 0 := by
    rw [← map_ofNat Polynomial.C 2, h2, map_zero]
  calc (2 : Γ(Spec (CommRingCat.of (Polynomial k)), ⊤)) =
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom 2 := (map_ofNat _ 2).symm
    _ = (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom 0 := congrArg _ hk
    _ = 0 := map_zero _

end CharTwo

/-! ### The source: `E = ∏_m 𝒪_𝒳[m]` lies in `D_{LQCoh^fbc}(𝒪_𝒳)` -/

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ enoughInjectives_fppfModulesUnivLESucc

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

variable (𝒵 : AlgebraicStacks.{u, w} B S hS)
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)]

/-- The object `E = ∏_{m ≥ 0} 𝒪_𝒵[m]` of `D(𝒪_𝒵)`, the product of the shifts of the structure
sheaf at module universe `u + 1`. -/
abbrev shiftedStructureSheafProduct : DerivedCategory (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵) :=
  ∏ᶜ fun m : ℕ => ((DerivedCategory.singleFunctor _ 0).obj
    (Stacks.SheafOfModules.uliftUnit.{u + 1} _ : fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵))⟦(m : ℤ)⟧

/-- **`E = ∏_{m ≥ 0} 𝒪_𝒵[m]` lies in `D_{LQCoh^fbc}(𝒪_𝒵)`.** Its `j`-th cohomology sheaf is the
product of the copies of `𝒪_𝒵` indexed by the `m ≥ 0` with `m = -j`, the structure sheaf being
acyclic on the objects over affine schemes: one copy of `𝒪_𝒵` for `j ≤ 0`, zero for `j > 0`. -/
theorem shiftedStructureSheafProduct_mem :
    derivedLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, u + 1} B E h S hS 𝒵
      (shiftedStructureSheafProduct B S hS 𝒵) := by
  have := isGrothendieckAbelian_fppfModulesUnivLESucc B S hS 𝒵
  intro j
  let O : fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵 := Stacks.SheafOfModules.uliftUnit.{u + 1} _
  have hB : (BigFppfOver.associatedTopology B S hS 𝒵.val.val.p .fppf).HasEnoughObjects
      (fun x => IsAffineOver B S hS (𝒵.val.val.p.obj x)) :=
    FlatFppf.hasEnoughObjects_isAffine B S hS 𝒵
  have e := homologyPiShiftSingleIso.{u, u + 1, u + 1, u, u + 1, u + 2} hB
    (fun _ : ℕ => O)
    (fun _ => @isZero_rightDerived_evaluation_uliftUnit_of_isAffineOver B S hS 𝒵)
    (fun m : ℕ => (m : ℤ)) j
  refine locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_of_iso.{u, w, u + 1} B E h S hS 𝒵
    e.symm ?_
  rcases le_or_gt j 0 with hj | hj
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -j := ⟨(-j).toNat, by omega⟩
    have : Subsingleton {m : ℕ // (m : ℤ) = -j} :=
      ⟨fun a b => Subtype.ext (by have := a.2; have := b.2; omega)⟩
    have := isIso_pi_lift_of_subsingleton (fun _ : {m : ℕ // (m : ℤ) = -j} => O)
      (fun _ => 𝟙 O) ⟨m, hm⟩
    exact locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_of_iso.{u, w, u + 1} B E h S hS 𝒵
      (asIso (Pi.lift fun _ : {m : ℕ // (m : ℤ) = -j} => 𝟙 O))
      (locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_uliftUnit_succ B E h S hS 𝒵)
  · have : IsEmpty {m : ℕ // (m : ℤ) = -j} := ⟨fun s => by have := s.2; omega⟩
    exact locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_of_isZero.{u, w, u + 1} B E h S hS
      𝒵
      (isZero_pi_of_isEmpty _)

/-! ### The target: `Rf_*E` does not lie in `D_{LQCoh^fbc}(𝒪_S)` -/

attribute [local instance] additive_fppfModuleSheafPushforwardOfStacks

/-- **`Rf_*E` is not in `D_{LQCoh^fbc}(𝒪_S)`**, over `S = Spec k[x]` with `k` nontrivial and
`2 = 0` in `k`, for a morphism `f : 𝒳 ⟶ S` of algebraic stacks such that `Rf_*𝒪_𝒳` is computed by
the cochain complex of `ℤ/2` with trivial coefficients `𝒪_S`. Then
`Rf_*𝒪_𝒳 ≅ ∏_n 𝒪_S[-n]`, so `Rf_*E ≅ ∏_{m, n} 𝒪_S[m - n]` and
`H⁰(Rf_*E) ≅ ∏_{m = n} 𝒪_S ≅ ∏_ℕ 𝒪_S`, which is not locally quasi-coherent. -/
theorem not_mem_derivedPushforward_of_iso {k : Type u} [CommRing k] [Nontrivial k]
    (hk : (2 : k) = 0) (hS : B.Contains (Spec (CommRingCat.of (Polynomial k))))
    {𝒳 : AlgebraicStacks.{u, w} B _ hS}
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B _ hS 𝒳)]
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B _ hS
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))))]
    (f : 𝒳 ⟶ schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS))))
    (e : (fppfDerivedPushforwardOfStacks B _ hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.SheafOfModules.uliftUnit.{u + 1} _ : fppfModulesUnivLE.{u, w, u + 1} B _ hS 𝒳)) ≅
      DerivedCategory.Q.obj (barCochainComplexInt
        (Stacks.SheafOfModules.uliftUnit.{u + 1} _ : fppfModulesUnivLE.{u, w, u + 1} B _ hS
          (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS))))))) :
    ¬ derivedLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, u + 1} B E h _ hS
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS))))
      ((fppfDerivedPushforwardOfStacks B _ hS f).obj (shiftedStructureSheafProduct B _ hS 𝒳)) := by
  intro hmem
  have := isGrothendieckAbelian_fppfModulesUnivLESucc B _ hS
    (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS))))
  let O : fppfModulesUnivLE.{u, w, u + 1} B _ hS
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))) :=
    Stacks.SheafOfModules.uliftUnit.{u + 1} _
  have hB : (BigFppfOver.associatedTopology B _ hS
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))).val.val.p .fppf).HasEnoughObjects
      (fun x => IsAffineOver B _ hS
        ((schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))).val.val.p.obj x)) :=
    FlatFppf.hasEnoughObjects_isAffine B _ hS (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS))))
  have h2 : (2 : ℤ) • 𝟙 O = 0 := two_zsmul_id_eq_zero O
    (two_eq_zero_ringStructureSheafCore _ _ _ (two_eq_zero_Γ_spec_polynomial hk))
  let e₂ := e ≪≫ barCochainComplexIntIsoPi hB O
    (@isZero_rightDerived_evaluation_uliftUnit_of_isAffineOver B _ hS
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS))))) h2
  let e₃ := fppfDerivedPushforwardOfStacksPiShiftNatIso B _ hS f _ ≪≫
    Pi.mapIso (fun m : ℕ => (shiftFunctor _ (m : ℤ)).mapIso e₂) ≪≫
    piShiftPiShiftIso ((DerivedCategory.singleFunctor _ 0).obj O) (fun m => (m : ℤ))
      (fun n => -(n : ℤ))
  let e₄ := homologyPiShiftSingleIso.{u, u + 1, u + 1, u, u + 1, u + 2} hB (fun _ : ℕ × ℕ => O)
    (fun _ => @isZero_rightDerived_evaluation_uliftUnit_of_isAffineOver B _ hS
      (schemeStack.{u, w} B _ hS (Over.mk (𝟙 (B.obj hS)))))
    (fun p : ℕ × ℕ => -(p.2 : ℤ) + p.1) 0
  exact not_mem_locallyQuasicoherentFlatBaseChange_of_iso_pi.{u, w} B E h k hS _
    ((DerivedCategory.homologyFunctor _ 0).mapIso e₃ ≪≫ e₄ ≪≫
      Pi.whiskerEquiv (f := fun _ => O) (g := fun _ => O) diagonalEquiv fun _ => Iso.refl _)
    (hmem 0)

/-! ### Stacks 07DD -/

/-- **Stacks 07DD.** A quasi-compact, quasi-separated morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
need not send `D_{LQCoh^fbc}(𝒪_𝒳)` into `D_{LQCoh^fbc}(𝒪_𝒴)` under the unbounded derived direct
image `Rf_*`, read at module universe `u + 1`. The counterexample is the discussion of
**Stacks 07DC** with `p = 2`: `k = 𝔽₂`, `S = Spec k[x]`, `f : B(ℤ/2)_S ⟶ S` the structure
morphism and `E = ∏_{m ≥ 0} 𝒪_𝒳[m]`. The object `E` lies in `D_{LQCoh^fbc}(𝒪_𝒳)`
(`shiftedStructureSheafProduct_mem`), `Rf_*𝒪_𝒳` is computed by the cochain complex of `ℤ/2` with
coefficients `𝒪_S`
(`AlgebraicGeometry.Stack.ClassifyingZModTwo.derivedPushforwardStructureModuleIso` and
`AlgebraicGeometry.Stack.ClassifyingZModTwo.cechCosimplicialIso`), and then `H⁰(Rf_*E)` is a
countable product of copies of `𝒪_S`, which is not locally quasi-coherent
(`not_mem_derivedPushforward_of_iso`). -/
@[stacks 07DD "D_QCoh is read through the subcategory D_LQCoh^fbc of D(O) whose Verdier \
quotient it is (Tag 07B6), and Rf_* is the unbounded total derived direct image; the witness is \
the counterexample of Tag 07DC with p = 2"]
theorem not_forall_derivedPushforward_mem_derivedLocallyQuasicoherentFlatBaseChange :
    ¬ ∀ (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (S : Scheme.{u})
        (hS : B.Contains S) (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS)
        [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
        [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)] (f : 𝒳 ⟶ 𝒴),
        IsQuasiCompactMorphism B S hS f → AlgebraicStacks.IsQuasiSeparated B S hS f →
        ∀ K, derivedLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, u + 1} B E h S hS 𝒳 K →
          derivedLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, u + 1} B E h S hS 𝒴
            ((fppfDerivedPushforwardOfStacks B S hS f).obj K) := by
  intro hall
  obtain ⟨B, E, h, hS⟩ := exists_bigFppfSite_bigEtaleSite_contains.{u} (ULift.{u} (ZMod 2))
  let := HasDerivedCategory.standard
    (fppfModulesUnivLE.{u, w, u + 1} B _ hS (ClassifyingZModTwo.stack.{u, w} hS))
  let := HasDerivedCategory.standard
    (fppfModulesUnivLE.{u, w, u + 1} B _ hS (ClassifyingZModTwo.base.{u, w} hS))
  have hk : (2 : ULift.{u} (ZMod 2)) = 0 := rfl
  exact not_mem_derivedPushforward_of_iso B E h hk hS (ClassifyingZModTwo.structureMap.{u, w} hS)
    (ClassifyingZModTwo.derivedPushforwardStructureModuleIso.{u, w} hS ≪≫
      DerivedCategory.Q.mapIso ((ComplexShape.embeddingUpNat.extendFunctor _).mapIso
        ((AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
          (ClassifyingZModTwo.cechCosimplicialIso.{u, w} hS))))
    (hall B E h _ hS _ _ (ClassifyingZModTwo.structureMap.{u, w} hS)
      (isQuasiCompactMorphism_structureMorphism_classifyingStack_trivialDoubleCover hS
        (ClassifyingZModTwo.isSmooth_constantZModTwoGroup hS))
      (isQuasiSeparated_structureMorphism_classifyingStack_trivialDoubleCover hS
        (ClassifyingZModTwo.isSmooth_constantZModTwoGroup hS))
      _ (shiftedStructureSheafProduct_mem B E h _ hS (ClassifyingZModTwo.stack.{u, w} hS)))

end Stacks.Examples.UnboundedDerivedPushforward

end

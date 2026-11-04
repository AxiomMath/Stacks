module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusShift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportShortExactHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.Algebra.Homology.CochainComplexPlusTruncation

/-!
# `RΓ_c(X_k̄, -)` along the canonical truncations of a complex

Let `k` be a finite field, `X` a scheme over `k` with a compactification and `k̄` an extension of
`k`. For a bounded below complex `K` of sheaves on `X_étale` and `n : ℤ`, the canonical
truncations give the exact sequences

`Hⁱ_c(X_k̄, τ_{≤ n} τ_{≥ n} K) → Hⁱ_c(X_k̄, τ_{≥ n} K) → Hⁱ_c(X_k̄, τ_{≥ n+1} K)`,

natural in `K` and compatible with the geometric Frobenius `π_X^*`, whose first term is
`H^{i-n}_c(X_k̄, Hⁿ(K))` (`Stacks.EtaleCohomology.compactSupportGradedHomologyIso`), and
`Hⁱ_c(X_k̄, τ_{≥ n} K) = 0` for `n > i`.

## Main definitions

* `Stacks.EtaleCohomology.compactSupportTruncHomology`, `compactSupportGradedHomology` and the maps
  `compactSupportGradedToTrunc`, `compactSupportTruncToTrunc` between them.

## Main results

* `Stacks.EtaleCohomology.exact_compactSupportGradedToTrunc_truncToTrunc`.
* `Stacks.EtaleCohomology.compactSupportGradedHomologyIso` and its Frobenius compatibility.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
/-- **`RΓ_c(X_k̄, -)` inverts quasi-isomorphisms.** -/
theorem isIso_compactSupportFrobeniusFunctor_map_of_quasiIso
    {K L : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (φ : K ⟶ L) [QuasiIso φ.hom] :
    IsIso ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map φ) := by
  let Y := Over.mk j.toBase
  have : PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)) :=
    etaleModuleInverseImage_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)) :=
    etaleModuleInverseImage_preservesFiniteColimits _ _
  have h₁ : QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map φ)).hom) := by
    show QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapHomologicalComplex _).map
      (((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapHomologicalComplex _).map φ.hom))
    infer_instance
  have h₂ : IsIso (DerivedCategory.Plus.Q.map ((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map φ))) := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map φ)))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h₁
    exact isIso_of_fully_faithful DerivedCategory.Plus.ι _
  dsimp only [compactSupportFrobeniusFunctor, fieldBaseChangeRestrictionFunctor, Functor.comp_map]
  infer_instance

/-! ### The truncation sequences -/

/-- `H (Φ (a ≫ b)) ≫ c = H (Φ a) ≫ H (Φ b) ≫ c` for functors `Φ` and `H`. -/
private theorem map_map_comp_comp {A B C' : Type*} [Category* A] [Category* B] [Category* C']
    (Φ : A ⥤ B) (H : B ⥤ C') {x y z : A} {w : C'} (a : x ⟶ y) (b : y ⟶ z)
    (c : H.obj (Φ.obj z) ⟶ w) :
    H.map (Φ.map (a ≫ b)) ≫ c = H.map (Φ.map a) ≫ (H.map (Φ.map b) ≫ c) := by
  simp

/-- `K ↦ Hⁱ_c(X_k̄, τ_{≥ n} K)`. -/
abbrev compactSupportTruncHomology (n i : ℤ) :
    CochainComplex.Plus (EtaleModules.{u, 0} Λ X) ⥤ ModuleCat.{u + 1} Λ :=
  CochainComplex.Plus.truncGEFunctor n ⋙ compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i

/-- `K ↦ Hⁱ_c(X_k̄, τ_{≤ n} τ_{≥ n} K)`. -/
abbrev compactSupportGradedHomology (n i : ℤ) :
    CochainComplex.Plus (EtaleModules.{u, 0} Λ X) ⥤ ModuleCat.{u + 1} Λ :=
  CochainComplex.Plus.gradedFunctor n ⋙ compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i

/-- `Hⁱ_c(X_k̄, τ_{≤ n} τ_{≥ n} K) ⟶ Hⁱ_c(X_k̄, τ_{≥ n} K)`. -/
def compactSupportGradedToTrunc (n i : ℤ) :
    compactSupportGradedHomology Λ f j kbar n i ⟶ compactSupportTruncHomology Λ f j kbar n i :=
  Functor.whiskerRight (CochainComplex.Plus.ιGraded n)
    (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)

/-- `Hⁱ_c(X_k̄, -)` inverts quasi-isomorphisms of bounded below complexes. -/
private theorem isIso_homology_map_compactSupportFrobeniusFunctor_map_of_quasiIso
    {l : Type u} [Field l] (g : X ⟶ Spec (.of l)) (c : CompactificationOf (Over.mk g))
    (lbar : Type u) [Field lbar] [Algebra l lbar] (i : ℤ)
    {K L : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (φ : K ⟶ L) [QuasiIso φ.hom] :
    IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
      ((compactSupportFrobeniusFunctor.{u, 0} Λ g c lbar).map φ)) := by
  have := isIso_compactSupportFrobeniusFunctor_map_of_quasiIso Λ g c lbar φ
  infer_instance

omit [Fintype k] in
/-- For `n ≤ n'`, the map `Hⁱ_c(X_k̄, τ_{≥ n} K) ⟶ Hⁱ_c(X_k̄, τ_{≥ n'} τ_{≥ n} K)` is an
isomorphism, naturally in `K`. -/
theorem isIso_whiskerRight_truncGEπTruncGE (n n' i : ℤ) (h : n ≤ n') :
    IsIso (Functor.whiskerRight (CochainComplex.Plus.truncGEπTruncGE n n')
      (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)) := by
  have : ∀ K, IsIso ((Functor.whiskerRight (CochainComplex.Plus.truncGEπTruncGE n n')
      (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)).app K) := fun K => by
    have := CochainComplex.Plus.quasiIso_truncGEπTruncGE (C := EtaleModules.{u, 0} Λ X) n n' h K
    show IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
        ((CochainComplex.Plus.truncGEπTruncGE n n').app K)))
    exact isIso_homology_map_compactSupportFrobeniusFunctor_map_of_quasiIso Λ f j kbar i _
  exact NatIso.isIso_of_isIso_app _

omit [Fintype k] in
/-- The map `Hⁱ_c(X_k̄, τ_{≥ n} K) ⟶ Hⁱ_c(X_k̄, τ_{≥ n+1} τ_{≥ n} K)` is an isomorphism, naturally
in `K`. -/
instance isIso_whiskerRight_truncGEπTruncGE_succ (n i : ℤ) :
    IsIso (Functor.whiskerRight (CochainComplex.Plus.truncGEπTruncGE n (n + 1))
      (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)) :=
  isIso_whiskerRight_truncGEπTruncGE Λ f j kbar n (n + 1) i (by lia)

/-- `Hⁱ_c(X_k̄, τ_{≥ n} K) ⟶ Hⁱ_c(X_k̄, τ_{≥ n+1} τ_{≥ n} K) ≅ Hⁱ_c(X_k̄, τ_{≥ n+1} K)`. -/
def compactSupportTruncToTrunc (n i : ℤ) :
    compactSupportTruncHomology Λ f j kbar n i ⟶ compactSupportTruncHomology Λ f j kbar (n + 1) i :=
  Functor.whiskerRight (CochainComplex.Plus.πTruncGEComp n (n + 1))
      (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i) ≫
    inv (Functor.whiskerRight (CochainComplex.Plus.truncGEπTruncGE n (n + 1))
      (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i))

omit [Fintype k] in
/-- **The truncation sequence
`Hⁱ_c(X_k̄, τ_{≤ n} τ_{≥ n} K) → Hⁱ_c(X_k̄, τ_{≥ n} K) → Hⁱ_c(X_k̄, τ_{≥ n+1} K)` is exact.** -/
theorem exact_compactSupportGradedToTrunc_truncToTrunc [Finite k] (n i : ℤ)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    Function.Exact ((compactSupportGradedToTrunc Λ f j kbar n i).app K).hom
      ((compactSupportTruncToTrunc Λ f j kbar n i).app K).hom := by
  cases nonempty_fintype k
  let M := K.obj.truncGE n
  let S := M.shortComplexTruncLE n
  have hS : S.ShortExact := M.shortComplexTruncLE_shortExact n
  have h₁ : CochainComplex.plus _ S.X₁ := ((CochainComplex.Plus.gradedFunctor n).obj K).property
  have h₂ : CochainComplex.plus _ S.X₂ := ((CochainComplex.Plus.truncGEFunctor n).obj K).property
  have h₃ : CochainComplex.plus _ S.X₃ := by
    refine ⟨n, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro i' hi'
    have hS' := hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i')
    have := hS'.epi_g
    exact IsZero.of_epi (S.g.f i') (M.isZero_of_isStrictlyGE n i' hi')
  have hex := exact_homology_compactSupportFrobeniusFunctor_map Λ f j kbar hS h₁ h₂ h₃ i
  let ψ : (⟨S.X₃, h₃⟩ : CochainComplex.Plus _) ⟶ (CochainComplex.Plus.truncGEFunctor (n + 1)).obj
      ((CochainComplex.Plus.truncGEFunctor n).obj K) :=
    ObjectProperty.homMk (M.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl)
  let e := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
    ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map ψ) ≫
    inv ((Functor.whiskerRight (CochainComplex.Plus.truncGEπTruncGE n (n + 1))
      (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)).app K)
  have : IsIso e := by
    have : QuasiIso ψ.hom :=
      inferInstanceAs (QuasiIso (M.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl))
    have := isIso_homology_map_compactSupportFrobeniusFunctor_map_of_quasiIso Λ f j kbar i ψ
    infer_instance
  have hk : (CochainComplex.Plus.πTruncGEComp n (n + 1)).app K =
      (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩) ≫ ψ :=
    ObjectProperty.hom_ext _ (M.g_shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl).symm
  have heq : (compactSupportTruncToTrunc Λ f j kbar n i).app K =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩)) ≫ e := by
    show (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          ((CochainComplex.Plus.πTruncGEComp n (n + 1)).app K)) ≫ _ = _
    rw [NatIso.isIso_inv_app, hk]
    exact map_map_comp_comp _ _ _ _ _
  rw [heq]
  exact hex.comp_injective _ (ConcreteCategory.bijective_of_isIso e).1 (map_zero _)

omit [Fintype k] in
/-- **`Hⁱ_c(X_k̄, τ_{≥ n} K) = 0` for `i < n`.** -/
theorem isZero_compactSupportTruncHomology [Finite k] (n i : ℤ) (h : i < n)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    IsZero ((compactSupportTruncHomology Λ f j kbar n i).obj K) := by
  cases nonempty_fintype k
  have : ((CochainComplex.Plus.truncGEFunctor n).obj K).obj.IsStrictlyGE n := by
    show (K.obj.truncGE n).IsStrictlyGE n
    infer_instance
  have := isGE_compactSupportFrobeniusFunctor_obj.{u, 0} Λ f j kbar
    ((CochainComplex.Plus.truncGEFunctor n).obj K) n
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ n i h

omit [Fintype k] in
/-- For `K` with `Hᵐ(K) = 0` when `m < 0`, `Hⁱ_c(X_k̄, K) ⟶ Hⁱ_c(X_k̄, τ_{≥ 0} K)` is an
isomorphism. -/
theorem isIso_compactSupport_πTruncGE_zero (i : ℤ)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) [K.obj.IsGE 0] :
    IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
        ((CochainComplex.Plus.πTruncGE 0).app K))) := by
  have : QuasiIso ((CochainComplex.Plus.πTruncGE (C := EtaleModules.{u, 0} Λ X) 0).app K).hom :=
    inferInstanceAs (QuasiIso (K.obj.πTruncGE 0))
  exact isIso_homology_map_compactSupportFrobeniusFunctor_map_of_quasiIso Λ f j kbar i _

section Frobenius

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The geometric Frobenius on `Hⁱ_c(X_k̄, S(-))` for a functor `S` into bounded below
complexes. -/
abbrev compactSupportFrobeniusAlong {D : Type*} [Category* D]
    (S : D ⥤ CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (i : ℤ) :
    S ⋙ compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i ⟶
      S ⋙ compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i :=
  Functor.whiskerLeft S (Functor.whiskerRight
    (canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar p q hcard)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i))

/-- **The maps induced on `Hⁱ_c(X_k̄, -)` by a transformation of endofunctors of complexes commute
with the geometric Frobenius.** -/
theorem compactSupportFrobeniusAlong_whiskerRight {S S' : CochainComplex.Plus
      (EtaleModules.{u, 0} Λ X) ⥤ CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (θ : S ⟶ S')
    (i : ℤ) :
    compactSupportFrobeniusAlong Λ f j kbar p q hcard S i ≫
        Functor.whiskerRight θ (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i) =
      Functor.whiskerRight θ (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i) ≫
        compactSupportFrobeniusAlong Λ f j kbar p q hcard S' i := by
  refine NatTrans.ext (funext fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
    ← Functor.map_comp]
  congr 1
  exact ((canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar p q hcard).naturality
    (θ.app K)).symm

/-- **`Hⁱ_c(X_k̄, τ_{≤ n} τ_{≥ n} K) ⟶ Hⁱ_c(X_k̄, τ_{≥ n} K)` commutes with the geometric
Frobenius.** -/
theorem compactSupportGradedToTrunc_frobenius (n i : ℤ) :
    compactSupportFrobeniusAlong Λ f j kbar p q hcard (CochainComplex.Plus.gradedFunctor n) i ≫
        compactSupportGradedToTrunc Λ f j kbar n i =
      compactSupportGradedToTrunc Λ f j kbar n i ≫
        compactSupportFrobeniusAlong Λ f j kbar p q hcard
          (CochainComplex.Plus.truncGEFunctor n) i :=
  compactSupportFrobeniusAlong_whiskerRight Λ f j kbar p q hcard _ i

/-- **`Hⁱ_c(X_k̄, τ_{≥ n} K) ⟶ Hⁱ_c(X_k̄, τ_{≥ n+1} K)` commutes with the geometric Frobenius.** -/
theorem compactSupportTruncToTrunc_frobenius (n i : ℤ) :
    compactSupportFrobeniusAlong Λ f j kbar p q hcard (CochainComplex.Plus.truncGEFunctor n) i ≫
        compactSupportTruncToTrunc Λ f j kbar n i =
      compactSupportTruncToTrunc Λ f j kbar n i ≫
        compactSupportFrobeniusAlong Λ f j kbar p q hcard
          (CochainComplex.Plus.truncGEFunctor (n + 1)) i := by
  have h₁ := compactSupportFrobeniusAlong_whiskerRight Λ f j kbar p q hcard
    (CochainComplex.Plus.πTruncGEComp n (n + 1)) i
  have h₂ := compactSupportFrobeniusAlong_whiskerRight Λ f j kbar p q hcard
    (CochainComplex.Plus.truncGEπTruncGE n (n + 1)) i
  have h₃ : compactSupportFrobeniusAlong Λ f j kbar p q hcard
        (CochainComplex.Plus.truncGEFunctor n ⋙ CochainComplex.Plus.truncGEFunctor (n + 1)) i ≫
      inv (Functor.whiskerRight (CochainComplex.Plus.truncGEπTruncGE n (n + 1))
        (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)) =
      inv (Functor.whiskerRight (CochainComplex.Plus.truncGEπTruncGE n (n + 1))
        (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)) ≫
        compactSupportFrobeniusAlong Λ f j kbar p q hcard
          (CochainComplex.Plus.truncGEFunctor (n + 1)) i := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← h₂, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [compactSupportTruncToTrunc, ← Category.assoc, h₁, Category.assoc, h₃, Category.assoc]

end Frobenius

/-! ### The graded pieces -/

/-- **`Hⁱ_c(X_k̄, τ_{≤ n} τ_{≥ n} K) ≅ H^{i'}_c(X_k̄, Hⁿ(K))` for `-n + i = i'`**, naturally in
`K`: the graded piece is `Hⁿ(K)` placed in degree `n`. -/
def compactSupportGradedHomologyIso (n i i' : ℤ) (h : -n + i = i') :
    compactSupportGradedHomology Λ f j kbar n i ≅
      (CochainComplex.Plus.ι (EtaleModules.{u, 0} Λ X) ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n) ⋙
        (Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, 0} Λ X)).functor 0 ⋙
        compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i' :=
  Functor.isoWhiskerRight (CochainComplex.Plus.gradedIsoSingle n)
      (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (compactSupportSingleHomologyIso.{u, 0} Λ f j kbar n i i' h) ≪≫
    Functor.isoWhiskerRight (CochainComplex.Plus.gradedXIsoHomology n)
      ((Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, 0} Λ X)).functor 0 ⋙
        compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i')

section Frobenius

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification of the graded piece commutes with the geometric Frobenius.** -/
theorem compactSupportGradedHomologyIso_hom_frobenius (n i i' : ℤ) (h : -n + i = i') :
    compactSupportFrobeniusAlong Λ f j kbar p q hcard (CochainComplex.Plus.gradedFunctor n) i ≫
        (compactSupportGradedHomologyIso Λ f j kbar n i i' h).hom =
      (compactSupportGradedHomologyIso Λ f j kbar n i i' h).hom ≫
        Functor.whiskerLeft (CochainComplex.Plus.ι (EtaleModules.{u, 0} Λ X) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n)
          (compactSupportFrobeniusAlong Λ f j kbar p q hcard
            ((Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, 0} Λ X)).functor 0)
              i') := by
  let gX := CochainComplex.Plus.gradedFunctor (C := EtaleModules.{u, 0} Λ X) n ⋙
    CochainComplex.Plus.ι (EtaleModules.{u, 0} Λ X) ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) n
  let S := Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, 0} Λ X)
  have e₂ : compactSupportFrobeniusAlong Λ f j kbar p q hcard (gX ⋙ S.functor n) i ≫
      (Functor.associator gX (S.functor n) (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)).hom =
      (Functor.associator gX (S.functor n) (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)).hom ≫
        Functor.whiskerLeft gX
          (compactSupportFrobeniusAlong Λ f j kbar p q hcard (S.functor n) i) :=
    NatTrans.ext (funext fun K => (Category.comp_id _).trans (Category.id_comp _).symm)
  have e₃ : Functor.whiskerLeft gX
        (compactSupportFrobeniusAlong Λ f j kbar p q hcard (S.functor n) i) ≫
      Functor.whiskerLeft gX (compactSupportSingleHomologyIso.{u, 0} Λ f j kbar n i i' h).hom =
      Functor.whiskerLeft gX (compactSupportSingleHomologyIso.{u, 0} Λ f j kbar n i i' h).hom ≫
        Functor.whiskerLeft gX
          (compactSupportFrobeniusAlong Λ f j kbar p q hcard (S.functor 0) i') := by
    rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp]
    exact congrArg _
      (compactSupportSingleHomologyIso_hom_frobenius.{u, 0} Λ f j kbar p q hcard n i i' h)
  show _ ≫ (Functor.whiskerRight (CochainComplex.Plus.gradedIsoSingle n).hom _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft gX (compactSupportSingleHomologyIso.{u, 0} Λ f j kbar n i i' h).hom ≫
      Functor.whiskerRight (CochainComplex.Plus.gradedXIsoHomology n).hom _) =
    (Functor.whiskerRight (CochainComplex.Plus.gradedIsoSingle n).hom _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft gX (compactSupportSingleHomologyIso.{u, 0} Λ f j kbar n i i' h).hom ≫
      Functor.whiskerRight (CochainComplex.Plus.gradedXIsoHomology n).hom _) ≫ _
  rw [reassoc_of% (compactSupportFrobeniusAlong_whiskerRight Λ f j kbar p q hcard
      (CochainComplex.Plus.gradedIsoSingle (C := EtaleModules.{u, 0} Λ X) n).hom i),
    reassoc_of% e₂, reassoc_of% e₃, Functor.whiskerLeft_comp_whiskerRight
      (CochainComplex.Plus.gradedXIsoHomology n).hom
      (compactSupportFrobeniusAlong Λ f j kbar p q hcard (S.functor 0) i')]
  rfl

end Frobenius

end Stacks.EtaleCohomology

module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Dualizing.DepthFromExt
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.ExtCompletionComparison
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.ExtSupportBound
public import StacksFrontier.RingTheory.Dualizing.Normalized

/-!
# Cohen--Macaulay modules detected by a dualizing complex

Let `A` be a Noetherian local ring with a normalized dualizing complex `ω_A`, and let `M` be a
nonzero finite `A`-module. Then `M` is Cohen--Macaulay exactly when `Ext^i_A(M, ω_A)` is nonzero
for at most one `i`, and in that case the unique such `i` is the negative of the dimension of the
support of `M`.

The forward implication is the degree bound of [stacks 0A7U]: depth is the least `i` with
`Ext^{-i}_A(M, ω_A) ≠ 0`, every nonvanishing degree lies in `[-dim Supp M, 0]`, and
Cohen--Macaulayness makes the two ends coincide. The converse runs through duality: if `Ext` is
concentrated in a single degree `-d`, then `RHom_A(M, ω_A)` is a module `E` placed in degree `-d`,
biduality recovers `M` as an `Ext` group of `E`, so `dim Supp M ≤ d = depth M` by the support bound
of [stacks 0A7U], and `depth M ≤ dim Supp M` always.

## Main results

* `Dualizing.isCohenMacaulay_iff_ext_concentrated` — the three equivalent conditions.

## Implementation notes

Normalization is expressed by `Dualizing.IsNormalizedDualizingComplex`, which records the source's
isomorphism `RHom_A(κ, ω_A) ≅ κ[0]`. In condition (3), equality between the integer `i` and the
extended-natural-valued dimension of the support is written as the conjunction that `i` is
nonnegative and that its natural value equals `Module.supportDim A M`; thus negative integers are,
as in the source, different from the dimension. Vanishing of an `Ext` group is expressed by
`Subsingleton` and nonvanishing by `Nontrivial`.

The identification of `Ext^i_A(K, ω)` with `H^i(RHom_A(K, ω))` is
`Dualizing.extDerivedHomLinearEquiv`, which holds for an arbitrary object `K` of the derived
category and needs no hypothesis on `ω`.

## References

* [Stacks Project, Tag 0B5A](https://stacks.math.columbia.edu/tag/0B5A)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- Abbreviation for `Ext^i_A(M, K)` with `M` a module placed in degree zero. -/
private abbrev extAt {A : Type u} [CommRing A] {M : Type (max v u)}
    [AddCommGroup M] [Module A M] (K : DerivedCategory (ModuleCat.{max v u} A))
    (i : ℤ) :=
  DerivedCategory.Ext
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i

/-- Morphisms from a module placed in degree `-d` are `Ext^{-d}` out of the same module placed in
degree zero, by the adjunction between the shifts. -/
private noncomputable def singleShiftExtLinearEquiv
    {A : Type u} [CommRing A]
    (E : Type (max v u)) [AddCommGroup E] [Module A E]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (d : ℕ) :
    DerivedCategory.Ext
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) (-(d : ℤ))).obj
            (ModuleCat.of A E))) K 0 ≃ₗ[A]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A E))
        K (-(d : ℤ)) := by
  let eSrc := (DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso
      (d : ℤ) (-(d : ℤ)) 0 (by simp)
  let X0 := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A E)
  let Xd := DerivedCategory.Q.obj
    ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) (-(d : ℤ))).obj
      (ModuleCat.of A E))
  have hsource : Xd = (DerivedCategory.singleFunctor
      (ModuleCat.{max v u} A) (-(d : ℤ))).obj (ModuleCat.of A E) := rfl
  let e0 : DerivedCategory.Ext Xd K 0 ≃ (Xd ⟶ K) :=
    (ShiftedHom.homEquiv (C := DerivedCategory (ModuleCat.{max v u} A))
      (X := Xd) (Y := K) (0 : ℤ) rfl).symm
  let e0Lin : DerivedCategory.Ext Xd K 0 ≃ₗ[A] (Xd ⟶ K) :=
    e0.toLinearEquiv ⟨by
      intro x y
      simp [e0, ShiftedHom.homEquiv, ShiftedHom.mk₀], by
      intro a x
      simp [e0, ShiftedHom.homEquiv, ShiftedHom.mk₀]⟩
  let e1Lin : (Xd ⟶ K) ≃ₗ[A] (X0⟦(d : ℤ)⟧ ⟶ K) :=
    CategoryTheory.Linear.homCongr A
      ((eqToIso hsource) ≪≫ (eSrc.app (ModuleCat.of A E)).symm) (Iso.refl K)
  let adjEquiv := shiftEquiv (DerivedCategory (ModuleCat.{max v u} A)) (d : ℤ)
  letI : adjEquiv.functor.Additive := by
    change (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (d : ℤ)).Additive
    infer_instance
  let adj := adjEquiv.toAdjunction
  letI : adjEquiv.inverse.Linear A := by
    change (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A))
      (-(d : ℤ))).Linear A
    infer_instance
  let e2 : (((shiftFunctor (DerivedCategory (ModuleCat.{max v u} A))
      (d : ℤ)).obj X0) ⟶ K) ≃+ (X0 ⟶ K⟦-(d : ℤ)⟧) :=
    CategoryTheory.Adjunction.homAddEquiv (adj := adj) X0 K
  let e2Lin : (((shiftFunctor (DerivedCategory (ModuleCat.{max v u} A))
      (d : ℤ)).obj X0) ⟶ K) ≃ₗ[A] (X0 ⟶ K⟦-(d : ℤ)⟧) :=
    e2.toLinearEquiv (by
      intro a f
      let f' : adjEquiv.functor.obj X0 ⟶ K := f
      change adj.homAddEquiv X0 K (a • f') = a • adj.homAddEquiv X0 K f'
      change adj.homEquiv X0 K (a • f') = a • adj.homEquiv X0 K f'
      rw [CategoryTheory.Adjunction.homEquiv_apply,
        CategoryTheory.Adjunction.homEquiv_apply]
      simp only [Functor.map_smul, Linear.comp_smul])
  exact e0Lin.trans (e1Lin.trans e2Lin)

/-- A Cohen--Macaulay module has its `Ext` into a normalized dualizing complex concentrated in
degree minus the dimension of its support. -/
private theorem cm_imp_ext_concentrated
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (hcm : Module.IsCohenMacaulayAtMaximalIdeal A M) :
    ∀ i : ℤ,
      ¬ (0 ≤ i ∧ Module.supportDim A M = ((i.toNat : ℕ∞) : WithBot ℕ∞)) →
        Subsingleton (extAt (M := M) K (-i)) := by
  obtain ⟨d, hd, hdepth⟩ :=
    depth_eq_least_nonzero_negative_ext (M := M) K hK inferInstance
  have hdim : Module.supportDim A M = ((d : ℕ∞) : WithBot ℕ∞) := by
    change ((Module.depth A (IsLocalRing.maximalIdeal A) M : ℕ∞) : WithBot ℕ∞) = _ at hcm
    rw [hdepth] at hcm
    exact hcm.symm
  intro i hi
  classical
  refine not_nontrivial_iff_subsingleton.mp fun _ => ?_
  have hb' : -(d : ℤ) ≤ -i ∧ -i ≤ 0 := by
    simpa using ext_degree_mem_Icc_of_nontrivial (M := M) K hK d hdim (-i) inferInstance
  have hipos : 0 ≤ i := by omega
  have hinat : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hipos
  have hleast : d ≤ i.toNat := by
    apply hd.2
    simpa [extAt, hinat]
  exact hi ⟨hipos, by rw [show i.toNat = d by omega, hdim]⟩

/-- `Ext` concentrated in degree minus the dimension of the support is in particular nonzero in at
most one degree. -/
private theorem ext_concentrated_imp_unique
    {A : Type u} [CommRing A] {M : Type (max v u)} [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hcon : ∀ n : ℤ,
      ¬ (0 ≤ n ∧ Module.supportDim A M = ((n.toNat : ℕ∞) : WithBot ℕ∞)) →
        Subsingleton (extAt (M := M) K (-n))) :
    ∀ i j : ℤ, Nontrivial (extAt (M := M) K i) →
      Nontrivial (extAt (M := M) K j) → i = j := by
  intro i j hi hj
  have cond (n : ℤ) (hn : Nontrivial (extAt (M := M) K n)) :
      0 ≤ -n ∧ Module.supportDim A M =
        (((-n).toNat : ℕ∞) : WithBot ℕ∞) := by
    by_contra h
    have hs := hcon (-n) h
    simp only [neg_neg] at hs
    exact not_nontrivial_iff_subsingleton.mpr hs hn
  obtain ⟨hi₀, hi₁⟩ := cond i hi
  obtain ⟨hj₀, hj₁⟩ := cond j hj
  have : (-i).toNat = (-j).toNat := by exact_mod_cast hi₁.symm.trans hj₁
  omega

/-- A module whose `Ext` into a normalized dualizing complex is nonzero in at most one degree is
Cohen--Macaulay. -/
private theorem ext_unique_imp_cm
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (hunique : ∀ i j : ℤ,
      Nontrivial (extAt (M := M) K i) →
      Nontrivial (extAt (M := M) K j) → i = j) :
    Module.IsCohenMacaulayAtMaximalIdeal A M := by
  classical
  obtain ⟨d, hd, hdepth⟩ :=
    depth_eq_least_nonzero_negative_ext (M := M) K hK inferInstance
  have hExtd : Nontrivial (extAt (M := M) K (-(d : ℤ))) := hd.1
  let L := (CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A M)
  let X := DerivedCategory.Q.obj L
  let D := (dualizingDerivedHomFunctor A K).obj (.op X)
  have hExtSub : ∀ j : ℤ, j ≠ -(d : ℤ) →
      Subsingleton (extAt (M := M) K j) := by
    intro j hj
    refine not_nontrivial_iff_subsingleton.mp fun _ => ?_
    exact hj (hunique j (-(d : ℤ)) inferInstance hExtd)
  have hDSub : ∀ j : ℤ, j ≠ -(d : ℤ) →
      Subsingleton (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj D)) := by
    intro j hj
    let : Subsingleton (DerivedCategory.Ext (DerivedCategory.Q.obj L) K j) := hExtSub j hj
    exact Equiv.subsingleton.symm (extDerivedHomLinearEquiv A K j X).toEquiv
  let : D.IsGE (-(d : ℤ)) := (DerivedCategory.isGE_iff D _).2 fun j hj => by
    exact ModuleCat.isZero_iff_subsingleton.mpr (hDSub j (ne_of_lt hj))
  let : D.IsLE (-(d : ℤ)) := (DerivedCategory.isLE_iff D _).2 fun j hj => by
    exact ModuleCat.isZero_iff_subsingleton.mpr (hDSub j (ne_of_gt hj))
  let E := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) (-(d : ℤ))).obj D
  obtain ⟨E', ⟨eD'⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D (-(d : ℤ))
  let eE' : E' ≅ E :=
    (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) (-(d : ℤ))).mapIso eD') ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} A) (-(d : ℤ))).app E').symm
  let eD : D ≅ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A)
      (-(d : ℤ))).obj E :=
    eD' ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) (-(d : ℤ))).mapIso eE'
  have hXfinite : ∀ j : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj X) := by
    intro j
    let e := (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} A) j).app L
    have hLj : Module.Finite A (L.homology j) := by
      by_cases hj : j = 0
      · subst j
        let e := (HomologicalComplex.homologyFunctorSingleIso
          (ModuleCat.{max v u} A) (ComplexShape.up ℤ) 0).app (ModuleCat.of A M)
        let : Module.Finite A
            ((𝟭 (ModuleCat.{max v u} A)).obj (ModuleCat.of A M)) := ‹Module.Finite A M›
        exact Module.Finite.equiv e.toLinearEquiv.symm
      · have : Subsingleton (L.homology j) :=
          ModuleCat.isZero_iff_subsingleton.mp
            (HomologicalComplex.isZero_single_obj_homology
              (ComplexShape.up ℤ) 0 (ModuleCat.of A M) j hj)
        infer_instance
    let : Module.Finite A
        ↑((HomologicalComplex.homologyFunctor (ModuleCat.{max v u} A)
          (ComplexShape.up ℤ) j).obj L) := hLj
    exact Module.Finite.equiv e.toLinearEquiv.symm
  have hDfinite := dualizingDerivedHom_finiteCohomology A K hK.1 X hXfinite
  have hEfinite : Module.Finite A E := hDfinite (-(d : ℤ))
  have hEne : Nontrivial E := by
    let : Nontrivial (DerivedCategory.Ext (DerivedCategory.Q.obj L) K (-(d : ℤ))) := hExtd
    exact (extDerivedHomLinearEquiv A K (-(d : ℤ)) X).toEquiv.symm.nontrivial
  let Lᵢ := (CochainComplex.singleFunctor (ModuleCat.{max v u} A) (-(d : ℤ))).obj E
  let eM₂ : X ≅ (dualizingDerivedHomFunctor A K).obj
      (.op ((dualizingDerivedHomFunctor A K).obj (.op X))) := by
    let m : CoherentDerivedCategory A := ⟨X, hXfinite⟩
    let e := (ObjectProperty.ι _).mapIso ((coherentDerivedBidualityIso A K hK.1).app m)
    change X ≅ (dualizingDerivedHomFunctor A K).obj
      (.op ((dualizingDerivedHomFunctor A K).obj (.op X))) at e
    exact e
  let eDual := (dualizingDerivedHomFunctor A K).mapIso eD.op
  have eDMod : ModuleCat.of A M ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj
        ((dualizingDerivedHomFunctor A K).obj
          (.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A)
            (-(d : ℤ))).obj (ModuleCat.of A E)))) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).mapIso
      (eDual ≪≫ eM₂.symm) ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} A) 0).app (ModuleCat.of A M)).symm
  have eMExt : M ≃ₗ[A] extAt (M := E) K (-(d : ℤ)) :=
    (eDMod.toLinearEquiv.trans
      (extDerivedHomLinearEquiv A K 0 (DerivedCategory.Q.obj Lᵢ)).symm).trans
      (singleShiftExtLinearEquiv (A := A) E K d)
  have hdimle : Module.supportDim A M ≤ ((d : ℕ∞) : WithBot ℕ∞) := by
    rw [Module.supportDim_eq_of_equiv eMExt]
    simpa using supportDim_ext_le_neg_degree K E hK (-(d : ℤ))
  have hMproper : IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ :=
    .symm <| Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator <| by
      rw [IsLocalRing.jacobson_eq_maximalIdeal _
        (mt Module.annihilator_eq_top_iff.mp (not_subsingleton M))]
  change ((Module.depth A (IsLocalRing.maximalIdeal A) M : ℕ∞) : WithBot ℕ∞) =
    Module.supportDim A M
  refine le_antisymm
    (mod_cast Module.depth_le_supportDim A (IsLocalRing.maximalIdeal A) M hMproper) ?_
  rwa [hdepth]

/-- **Stacks Project, Tag 0B5A.** For a nonzero finite module over a Noetherian local ring with
normalized dualizing complex, Cohen--Macaulayness is equivalent to `Ext` into the dualizing
complex being nonzero in at most one degree, and also to its being concentrated in degree minus
the dimension of the support. -/
@[stacks 0B5A "cm_criterion"]
public theorem isCohenMacaulay_iff_ext_concentrated
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    List.TFAE [
      Module.IsCohenMacaulayAtMaximalIdeal A M,
      ∀ i j : ℤ,
        Nontrivial (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
            (ModuleCat.of A M)) K i) →
        Nontrivial (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
            (ModuleCat.of A M)) K j) → i = j,
      ∀ i : ℤ,
        ¬ (0 ≤ i ∧ Module.supportDim A M = ((i.toNat : ℕ∞) : WithBot ℕ∞)) →
          Subsingleton (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
              (ModuleCat.of A M)) K (-i))] := by
  tfae_have 1 → 3 := cm_imp_ext_concentrated K hK
  tfae_have 3 → 2 := ext_concentrated_imp_unique K
  tfae_have 2 → 1 := ext_unique_imp_cm K hK
  tfae_finish

end Dualizing

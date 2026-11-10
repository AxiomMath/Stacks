module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjections
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CechCompletionUnit
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantSystem

/-!
# The canonical maps `Hʲ_𝔪(M) → Hʲ_𝔪(M/IⁿM)` reach the stable images

In Situation [Stacks, Tag 0EFU] with `A` local, `I`-adically complete and `T = {𝔪}`, the
canonical map `Hʲ_𝔪(M) → lim_n Hʲ_𝔪(M/IⁿM)` — the limit comparison of the cone whose legs are
local cohomology applied to the quotient maps `M → M/IⁿM` — is an isomorphism for `j ≤ s`. This
is the isomorphism assertion of [Stacks, Tag 0EFR] read at the canonical comparison. As a
consequence, for every `n` the image of some later transition map `Hʲ_𝔪(M/IᵐM) → Hʲ_𝔪(M/IⁿM)`
lies in the image of the canonical map `Hʲ_𝔪(M) → Hʲ_𝔪(M/IⁿM)`.

## Main results

* `Stacks.Algebraization.isIso_localCohomologyAdicQuotientLift` — the canonical comparison is an
  isomorphism in degrees `j ≤ s`.
* `Stacks.Algebraization.exists_range_le_range_localCohomology_adicQuotient` — the stable images
  are reached by the canonical maps.

## Implementation notes

The comparison of `isIso_localCohomologyToAdicQuotientLimit_of_isAdicComplete` has a second leg
chosen by `Classical.choose` from an existential, so it is not known to be the canonical map;
`Stacks.Algebraization.localCohomologyAdicQuotientLift` is the canonical map itself, built from
the quotient maps `M → M/IⁿM`.

## References

* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

section Canonical

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- The cone of quotient maps `M → M/IⁿM` on the tower of adic quotients. -/
public def adicQuotientProjectionCone (I : Ideal A) (M : ModuleCat.{u} A) :
    Cone (adicQuotientModuleSystem A I M) where
  pt := M
  π :=
  { app := fun k => Dualizing.adicQuotientProjection A I M k.unop
    naturality := fun k l g => by
      obtain ⟨k⟩ := k
      obtain ⟨l⟩ := l
      have h : l ≤ k := leOfHom g.unop
      rw [show g = (homOfLE h).op from Subsingleton.elim _ _]
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      exact (Dualizing.adicQuotientProjection_comp_map A I M h).symm }

/-- **The canonical comparison `Hʲ_𝔪(M) → lim_n Hʲ_𝔪(M/IⁿM)`**: local cohomology applied to the
map `M → lim_n M/IⁿM`, followed by the comparison of the limits. -/
public def localCohomologyAdicQuotientLift (I : Ideal A) (M : ModuleCat.{u} A) (j : ℤ) :
    (Stacks.LocalCohomology.localCohomologyModuleFunctor A j).obj M ⟶
      limit (adicQuotientModuleSystem A I M ⋙
        Stacks.LocalCohomology.localCohomologyModuleFunctor A j) :=
  (Stacks.LocalCohomology.localCohomologyModuleFunctor A j).map
      (limit.lift _ (adicQuotientProjectionCone A I M)) ≫
    limit.post _ (Stacks.LocalCohomology.localCohomologyModuleFunctor A j)

/-- The composites of the canonical comparison with the limit projections are the canonical
maps. -/
public theorem localCohomologyAdicQuotientLift_π (I : Ideal A) (M : ModuleCat.{u} A) (j : ℤ)
    (n : ℕ) :
    localCohomologyAdicQuotientLift A I M j ≫
        limit.π (adicQuotientModuleSystem A I M ⋙
          Stacks.LocalCohomology.localCohomologyModuleFunctor A j) (op n) =
      (Stacks.LocalCohomology.localCohomologyModuleFunctor A j).map
        (Dualizing.adicQuotientProjection A I M n) := by
  rw [localCohomologyAdicQuotientLift, Category.assoc, limit.post_π]
  exact ((Stacks.LocalCohomology.localCohomologyModuleFunctor A j).map_comp _ _).symm.trans
    (congrArg (Stacks.LocalCohomology.localCohomologyModuleFunctor A j).map
      (limit.lift_π (adicQuotientProjectionCone A I M) (op n)))

/-- The tower `n ↦ Hʲ_𝔪(M/IⁿM)` is Mittag-Leffler. -/
private theorem isMittagLefflerCategorical_adicQuotientLocalCohomology (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (j : ℤ) :
    IsMittagLefflerCategorical
      (Dualizing.adicQuotientLocalCohomologySystem A I (maximalIdeal A)
          (Ideal.fg_of_isNoetherianRing _) M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) j) :=
  Stacks.LocalCohomology.isMittagLeffler_localCohomology A (adicQuotientModuleSystem A I M)
    (fun _ => Module.Finite.quotient A _) j

/-- The canonical comparison is an isomorphism in degree `j` as soon as the completion unit is
one on `j`-th cohomology. -/
private theorem isIso_localCohomologyAdicQuotientLift_of_isIso_unit (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (j : ℤ)
    (hunit : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      (Dualizing.completedLocalCohomologyUnit A I (maximalIdeal A) I.fg_of_isNoetherianRing
        (Ideal.fg_of_isNoetherianRing _) M))) :
    IsIso (localCohomologyAdicQuotientLift A I M j) := by
  obtain ⟨q, hq, hqπ⟩ :=
    NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_isIso_comp_limit_π A
      (Dualizing.adicQuotientLocalCohomologySystem A I (maximalIdeal A)
        (Ideal.fg_of_isNoetherianRing _) M)
      (Dualizing.completedLocalCohomology A I (maximalIdeal A) I.fg_of_isNoetherianRing
        (Ideal.fg_of_isNoetherianRing _) M)
      (Dualizing.completedLocalCohomologyProjection A I (maximalIdeal A)
        I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) M)
      (Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite A I
        (maximalIdeal A) I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) M)
      j (isMittagLefflerCategorical_adicQuotientLocalCohomology A I M (j - 1))
  let q' : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      (Dualizing.completedLocalCohomology A I (maximalIdeal A) I.fg_of_isNoetherianRing
        (Ideal.fg_of_isNoetherianRing _) M) ⟶ limit (adicQuotientModuleSystem A I M ⋙
          Stacks.LocalCohomology.localCohomologyModuleFunctor A j) := q
  have hq' : IsIso q' := hq
  have hqπ' : ∀ n : ℕ, q' ≫ limit.π (adicQuotientModuleSystem A I M ⋙
      Stacks.LocalCohomology.localCohomologyModuleFunctor A j) (op n) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
          (Dualizing.completedLocalCohomologyProjection A I (maximalIdeal A)
            I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) M n) := hqπ
  have heq : localCohomologyAdicQuotientLift A I M j =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
        (Dualizing.completedLocalCohomologyUnit A I (maximalIdeal A) I.fg_of_isNoetherianRing
          (Ideal.fg_of_isNoetherianRing _) M) ≫ q' := by
    refine limit.hom_ext fun k => ?_
    obtain ⟨n⟩ := k
    refine (localCohomologyAdicQuotientLift_π A I M j n).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun φ => _ ≫ φ) (hqπ' n)).symm
    refine Eq.trans ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map_comp _ _)
    exact (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      (Dualizing.completedLocalCohomologyUnit_comp_projection A I (maximalIdeal A)
        I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) M n)).symm
  rw [heq]
  exact IsIso.comp_isIso' hunit hq'

end Canonical

section Bootstrap

variable (S : BootstrapSituation.{u, u, u})

/-- **The canonical comparison of [Stacks, Tag 0EFR] is an isomorphism.** In Situation 0EFU with
`A` local, `I`-adically complete and `T = {𝔪}`, the canonical map
`Hʲ_𝔪(M) → lim_n Hʲ_𝔪(M/IⁿM)` is an isomorphism for every `j ≤ s`. -/
public theorem isIso_localCohomologyAdicQuotientLift [IsLocalRing S.A] [IsAdicComplete S.I S.A]
    (hT : S.T = {closedPoint S.A}) (j : ℤ) (hj : j ≤ S.s) :
    IsIso (localCohomologyAdicQuotientLift S.A S.I (ModuleCat.of S.A S.M) j) := by
  refine isIso_localCohomologyAdicQuotientLift_of_isIso_unit S.A S.I _ j ?_
  have h := isIso_homology_localCohomologyToCompletedLocalCohomology_maximalIdeal S hT j hj
  rw [← isIso_comp_right_iff _
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) j).map
      (completedLocalCohomologyShrinkIso S.A S.I (maximalIdeal S.A) (maximalIdeal S.A)
        S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) rfl).hom),
    ← Functor.map_comp]
  exact h

/-- **The stable images of `Hʲ_𝔪(M/IⁿM)` are reached by the canonical maps.** In Situation 0EFU
with `A` local, `I`-adically complete and `T = {𝔪}`, for `j ≤ s` and every `n` there is `m ≥ n`
such that the image of the transition map `Hʲ_𝔪(M/IᵐM) → Hʲ_𝔪(M/IⁿM)` lies in the image of the
canonical map `Hʲ_𝔪(M) → Hʲ_𝔪(M/IⁿM)` induced by `M ↠ M/IⁿM`. -/
public theorem exists_range_le_range_localCohomology_adicQuotient [IsLocalRing S.A]
    [IsAdicComplete S.I S.A] (hT : S.T = {closedPoint S.A}) (j : ℤ) (hj : j ≤ S.s) (n : ℕ) :
    ∃ m : ℕ, ∃ h : n ≤ m,
      LinearMap.range ((Stacks.LocalCohomology.localCohomologyModuleFunctor S.A j).map
          ((adicQuotientModuleSystem S.A S.I (ModuleCat.of S.A S.M)).map (homOfLE h).op)).hom ≤
        LinearMap.range ((Stacks.LocalCohomology.localCohomologyModuleFunctor S.A j).map
          (Dualizing.adicQuotientProjection S.A S.I (ModuleCat.of S.A S.M) n)).hom := by
  let F := adicQuotientModuleSystem S.A S.I (ModuleCat.of S.A S.M)
  let H := Stacks.LocalCohomology.localCohomologyModuleFunctor S.A j
  let f : ModuleCat.of S.A S.M ⟶ limit F := limit.lift F (adicQuotientProjectionCone S.A S.I _)
  have hiso : IsIso (H.map f ≫ limit.post F H) :=
    isIso_localCohomologyAdicQuotientLift S hT j hj
  have hconst := Stacks.LocalCohomology.isEssentiallyConstantInverseSystem_localCohomology S.A F
    (fun _ => Module.Finite.quotient S.A _) (ModuleCat.of S.A S.M) j f hiso
  obtain ⟨c, i, s, hs⟩ :=
    (CategoryTheory.EssentiallyConstantPro.isEssentiallyConstantPro_iff_op (F ⋙ H)).mpr hconst
  obtain ⟨k, σ, τ, hτ⟩ := hs.cofinal (op n)
  have hnk : n ≤ k.unop := leOfHom τ.unop
  have hτ' : τ = (homOfLE hnk).op := Subsingleton.elim _ _
  refine ⟨k.unop, hnk, ?_⟩
  rintro y ⟨x, rfl⟩
  have hlim : inv (H.map f ≫ limit.post F H) ≫
      H.map (Dualizing.adicQuotientProjection S.A S.I (ModuleCat.of S.A S.M) n) =
        limit.π (F ⋙ H) (op n) := by
    rw [IsIso.inv_comp_eq]
    exact (localCohomologyAdicQuotientLift_π S.A S.I (ModuleCat.of S.A S.M) j n).symm
  have h1 : H.map (F.map (homOfLE hnk).op) = ((F ⋙ H).map σ ≫ s ≫ limit.lift (F ⋙ H) c ≫
      inv (H.map f ≫ limit.post F H)) ≫
        H.map (Dualizing.adicQuotientProjection S.A S.I (ModuleCat.of S.A S.M) n) := by
    change (F ⋙ H).map (homOfLE hnk).op = _
    rw [← hτ', hτ]
    simp only [Category.assoc]
    rw [hlim, limit.lift_π]
  exact ⟨_, (congrArg (fun φ => φ.hom x) h1).symm⟩

end Bootstrap

end Stacks.Algebraization

end

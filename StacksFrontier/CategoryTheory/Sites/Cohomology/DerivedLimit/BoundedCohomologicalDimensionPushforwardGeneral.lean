module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.BoundedCohomologicalDimensionPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CohomologySheavesOfTheDerivedDirectImageUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Bounded cohomological dimension of a derived direct image, for an arbitrary morphism

Let `f : (C, O) ⟶ (C', O')` be a morphism of ringed sites, let `A ⊂ Mod(O)` be a weak Serre
subcategory and let `N` be an integer such that `C, O, A` satisfy the hypothesis of Stacks 0D6R,
`f` and `A` satisfy the hypothesis of Stacks 0D6V, and `Rᵖf_*F = 0` for `p > N` and `F` in `A`.
Then for every `K` of `D_A(O)` the map `Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))` is an isomorphism for
`j ≥ N - n`. This is Stacks 0D6W, and this file states and proves it with no hypothesis beyond
the source's.

## The argument

It is the argument of `BoundedCohomologicalDimensionPushforward.lean`, which is the source's:
the assertion is local on the target, the pushed-forward truncation tower stabilises by Stacks
0D6U's lemma, and over a member `V'_i` of a distinguished covering of an object of `B'` the value
`Hʲ(V'_i, Rf_*K)` is `Hʲ(u(V'_i), K)`, where the bound of Stacks 0D6V and the Milnor sequence of
Stacks 0D6K apply. The identification `Hʲ(V', Rf_*K) = Hʲ(u(V'), K)` is Stacks 0D6I, which the
library has for an arbitrary morphism of ringed sites as
`derivedPushforwardCohomologyPresheafSourceValueIsoGeneral`, in the namespace
`Stacks.Cohomology.UnboundedHigherDirectImageOnSites`; the declarations of the sibling file
instead take Stacks 093Y as a hypothesis, which needs `f` flat.

For `n < 0` the map factors as `Rf_*K ⟶ Rf_*(τ_{≥ 0}K) ⟶ Rf_*(τ_{≥ -n}K)`: the first map is the
case `n = 0`, and the second has fibre `Rf_*(τ_{< -n}τ_{≥ 0}K)`, which the vanishing of `Rᵖf_*`
above `N` on `A` places in degrees `≤ -n - 1 + N`.

## Main results

All in the namespace `Stacks.Cohomology.OlssonLaszlo`.

* `isIso_homology_derivedPushforward_truncGEπ_of_relativeSituation_general` (Stacks 0D6W).
* `isIso_homology_derivedPushforward_natTransTruncGEOfLE_zero`:
  `Hʲ(Rf_*(τ_{≥ 0}K)) ⟶ Hʲ(Rf_*(τ_{≥ m}K))` is an isomorphism for `j ≥ N + m`.

## Implementation notes

The hypotheses are carried as in the sibling file, as the loose data of Stacks 0D6R and 0D6V
with the cohomology of the latter computed on the source site over `f.u.obj (𝒰.X i)`, and
`Rᵖf_*F` is read as `Hᵖ(Rf_*(F[0]))`. The three universes of both ringed sites are collapsed, as
they are in `AlgebraicGeometry.RingedSite.Hom`.

## References

* [Stacks Project, Tag 0D6W](https://stacks.math.columbia.edu/tag/0D6W)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry

namespace Stacks.Cohomology.OlssonLaszlo

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (derivedPushforward)
open Stacks.Cohomology.UnboundedHigherDirectImageOnSites

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

variable (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  [hA : A.IsWeakSerreClass]
  (B : Set X.C)
  (basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
    𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : X.C, B V → ℤ)
  (coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V)
  (vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{u} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝒰.X i) p F))
  (B' : Set Y.C)
  (basisCover' : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : Y.C, B' V → ℤ)
  (coverings' : ∀ V : Y.C, B' V → Stacks.Cohomology.CofinalCoveringSystem Y.J V)
  (vanishing' : ∀ (V : Y.C) (hV : B' V) (𝒰 : PreZeroHypercover.{u} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero
          (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj (𝒰.X i)) p F))
  (N : ℤ)
  (hvanishImage : ∀ p : ℕ, N < (p : ℤ) →
    ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
      ((derivedPushforward.{u} f.toRingedToposSiteHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))



omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
include hA hvanishImage in
/-- **Truncating above degree zero does not change the cohomology of the derived direct image in
high degrees.** For `K` of `D_A(O)` and `m > 0` the map `Rf_*(τ_{≥ 0}K) ⟶ Rf_*(τ_{≥ m}K)` is an
isomorphism on `Hʲ` for `j ≥ N + m`: its fibre is `Rf_*` of `τ_{< m}τ_{≥ 0}K`, an object living in
degrees `[0, m - 1]` with cohomology in `A`, which the vanishing of `Rᵖf_*` above `N` places in
degrees `≤ m - 1 + N`. -/
theorem isIso_homology_derivedPushforward_natTransTruncGEOfLE_zero
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K)
    (m : ℤ) (hm : 0 < m) (j : ℤ) (hj : N + m ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
      ((derivedPushforward.{u} f.toRingedToposSiteHom).map
        ((DerivedCategory.TStructure.t.natTransTruncGEOfLE 0 m hm.le).app K))) := by
  have hmos := f.isMorphismOfSites_toRingedToposSiteHom
  have _ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy_hasLeftDerivedFunctor
    f.toRingedToposSiteHom _
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
    (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pullbackInvertsQuasiIso_isKFlat
      f.toRingedToposSiteHom hmos)
  let _ := Functor.IsRightDerivedFunctor.commShift
    (derivedPushforward.{u} f.toRingedToposSiteHom)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
      f.toRingedToposSiteHom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward.{u} f.toRingedToposSiteHom).IsTriangulated := by
    have _ := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    exact Stacks.Injectives.rightDerivedFunctor_isTriangulated
      f.toRingedToposSiteHom.pushforwardTopos (derivedPushforward.{u} f.toRingedToposSiteHom)
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
        f.toRingedToposSiteHom)
  obtain ⟨δ, hδ⟩ := Stacks.TruncationLevel.exists_distTriang_truncGE
    DerivedCategory.TStructure.t 0 m hm.le K
  let E := (DerivedCategory.TStructure.t.truncLT m).obj
    ((DerivedCategory.TStructure.t.truncGE 0).obj K)
  have hE0 : DerivedCategoryB.derivedCategoryB A ((DerivedCategory.TStructure.t.truncGE 0).obj K) :=
    derivedCategoryB_truncGE_mem A K hK 0
  have hEA : ∀ i : ℤ, A ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj E) := by
    intro i
    by_cases hi : i < m
    · have hι := DerivedCategory.isIso_homologyMap_truncLTι_app m i hi
        ((DerivedCategory.TStructure.t.truncGE 0).obj K)
      exact A.prop_of_iso (@asIso _ _ _ _ _ hι).symm (hE0 i)
    · have : E.IsLE (m - 1) := by
        dsimp only [E]
        infer_instance
      exact A.prop_of_isZero (DerivedCategory.isZero_of_isLE _ (m - 1) i (by omega))
  have hEGE : E.IsGE 0 := by
    dsimp only [E]
    infer_instance
  have hELE : E.IsLE (m - 1) := by
    dsimp only [E]
    infer_instance
  have hRE : ((derivedPushforward.{u} f.toRingedToposSiteHom).obj E).IsLE (m - 1 + N) :=
    isLE_map_obj_of_bounded (derivedPushforward.{u} f.toRingedToposSiteHom) A N
      (fun M n hM ↦ isLE_derivedPushforward_singleFunctor_obj f.toRingedToposSiteHom hmos A N
        hvanishImage M hM n)
      (m - 1).toNat E hEA 0 (m - 1) hEGE hELE (by omega)
  exact Stacks.TruncationLevel.isIso_homologyMap_mor₂ _
    ((derivedPushforward.{u} f.toRingedToposSiteHom).map_distinguished _ hδ) j
    (DerivedCategory.isZero_of_isLE _ (m - 1 + N) j (by omega) (hX := hRE))
    (DerivedCategory.isZero_of_isLE _ (m - 1 + N) (j + 1) (by omega) (hX := hRE))

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
include hA basisCover vanishing basisCover' vanishing' hvanishImage in
/-- **Stacks Project, Tag 0D6W.** Let `f : (C, O) ⟶ (C', O')` be a morphism of ringed sites, let
`A ⊂ Mod(O)` be a weak Serre subcategory and let `N` be an integer such that

* `C, O, A` satisfy the standing hypothesis of Stacks 0D6R: a class `B` of objects covering every
  object of `C`, each `V ∈ B` carrying an integer bound `d_V` and a cofinal system of coverings of
  `V` on whose members the cohomology of every module of `A` vanishes above `d_V`;
* `f` and `A` satisfy the standing hypothesis of Stacks 0D6V: a class `B'` of objects covering
  every object of `C'`, each `V' ∈ B'` carrying an integer bound `d_{V'}` and a cofinal system of
  coverings of `V'` on the images under `f` of whose members the cohomology, computed on `C`, of
  every module of `A` vanishes above `d_{V'}`;
* `Rᵖf_*F = 0` for every `p > N` and every `F` of `A`.

Then for every `K` of `D_A(O)` the canonical map `Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))` induced by the
truncation `K ⟶ τ_{≥ -n}K` is an isomorphism for every integer `n` and every `j ≥ N - n`. -/
@[stacks 0D6W "for a morphism of ringed sites, with Rᵖf_*F read as Hᵖ(Rf_*(F[0])) and the
identification Hʲ(V', Rf_*K) = Hʲ(u(V'), K) taken from Stacks 0D6I"]
theorem isIso_homology_derivedPushforward_truncGEπ_of_relativeSituation_general
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K)
    (n : ℤ) (j : ℤ) (hj : N - n ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
      ((derivedPushforward.{u} f.toRingedToposSiteHom).map
        ((DerivedCategory.TStructure.t.truncGEπ (-n)).app K))) := by
  -- The case of a natural number `n`, a stage of the truncation tower.
  have key : ∀ (n : ℕ) (j : ℤ), N - (n : ℤ) ≤ j →
      IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
        ((derivedPushforward.{u} f.toRingedToposSiteHom).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
    intro n j hj
    let S : Stacks.Cohomology.OlssonLaszloSituation.{u, u, u, u} :=
      { C := X.C, J := X.J, O := Stacks.SheafOfModules.Tensor.ringSheaf X.O, A := A, B := B,
        basis_cover := basisCover, degreeBound := degreeBound, coverings := coverings,
        vanishing := vanishing }
    have hmos := f.isMorphismOfSites_toRingedToposSiteHom
    have hprod : HasProduct fun k : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨k⟩ :=
      Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) K
    have hprodS : HasProduct fun k : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (S).O)
        K).obj ⟨k⟩ := hprod
    -- The pushed-forward truncation tower has invertible transition maps on `Hʲ` past `n`.
    have hW (m : ℕ) (hnm : n ≤ m) :
        Y.J.W ((derivedPushforwardCohomologyAbPresheafFunctor f j).map
          ((Stacks.DerivedLimit.truncGETower
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).map
            (homOfLE hnm).op)) :=
      (isIso_homology_derivedPushforward_map_iff_w f _ j).1 <| (isEventuallyConstantTo_of_isIso_succ
        (Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K ⋙
          derivedPushforward.{u} f.toRingedToposSiteHom ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j) n
        (fun k hk ↦ isIso_homology_derivedPushforward_truncGETower_succ
          f.toRingedToposSiteHom hmos A N hvanishImage K hK k j (by omega))).isIso_map
        (homOfLE hnm).op (𝟙 _)
    rw [isIso_homology_derivedPushforward_map_iff_w f _ j]
    apply Stacks.Cohomology.w_of_cofinal_local_isomorphisms Y.J B' basisCover' coverings'
    intro V hV
    obtain ⟨m, hnm, hm1, hm2⟩ : ∃ m : ℕ, n ≤ m ∧ 1 - j ≤ (m : ℤ) ∧
        degreeBound' V hV - j + 1 ≤ (m : ℤ) :=
      ⟨max n (max (1 - j).toNat (degreeBound' V hV - j + 1).toNat), by omega, by omega, by omega⟩
    refine ⟨(derivedPushforwardCohomologyAbPresheafFunctor f j).obj
        ((Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨m⟩),
      (derivedPushforwardCohomologyAbPresheafFunctor f j).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K),
      (derivedPushforwardCohomologyAbPresheafFunctor f j).map
        ((Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).map
          (homOfLE hnm).op), ?_, hW m hnm, ?_⟩
    · exact ((derivedPushforwardCohomologyAbPresheafFunctor f j).map_comp _ _).symm.trans
        (congrArg (derivedPushforwardCohomologyAbPresheafFunctor f j).map
          (Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map K
            (homOfLE hnm).op))
    · intro 𝒰 h𝒰 i
      exact (NatIso.isIso_map_iff
        (derivedPushforwardCohomologyPresheafSourceValueIsoGeneral f (𝒰.X i) j)
        ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K)).2
        (isIso_homologyMap_derivedSectionsOverObject_truncGEπ X (f.u.obj (𝒰.X i)) A K hK
          (degreeBound' V hV) (vanishing' V hV 𝒰 h𝒰 i)
          (fun L c pr δ hL hc ↦
            Stacks.Cohomology.isIso_to_isDerivedLimit_truncGETower_of_derivedCategoryB
              (S)
              K hK L pr ⟨δ, hL⟩ c hc)
          j m hm1 hm2)
  rcases le_or_gt 0 n with hn | hn
  · have h := key n.toNat j (by omega)
    rwa [Int.toNat_of_nonneg hn] at h
  · have h0 := key 0 j (by omega)
    have h1 := isIso_homology_derivedPushforward_natTransTruncGEOfLE_zero f A N hvanishImage K hK
      (-n) (by omega) j (by omega)
    have e : (DerivedCategory.TStructure.t.truncGEπ (-n)).app K =
        (DerivedCategory.TStructure.t.truncGEπ (-((0 : ℕ) : ℤ))).app K ≫
          (DerivedCategory.TStructure.t.natTransTruncGEOfLE 0 (-n) (by omega)).app K :=
      (DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app 0 (-n) (by omega) K).symm
    rw [e, Functor.map_comp, Functor.map_comp]
    exact IsIso.comp_isIso' h0 h1

end Stacks.Cohomology.OlssonLaszlo

end

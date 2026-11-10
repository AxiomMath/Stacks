module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafBaseChangeIso
public import
  StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGenerationGeneralField
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeDevissage.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerLocalGenerators
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Symmetry
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SectionMultiplicationExtension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SituationVeryAmpleGeneration
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.FiniteType
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing sheaf of a proper curve is coherent, and Tag 0B5H

In Situation [Stacks, Tag 0B5D] let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of
[Stacks, Tag 0BS2], and let `ℒ` be a very ample invertible `𝒪_X`-module with `deg(ℒ) ≥ 2`. This
file proves that `ω_X` is coherent (`isCoherent_dualizingSheafOverField`) and then
[Stacks, Tag 0B5H] at the source's hypotheses
(`nonempty_generatingSections_dualizingSheafOverField_tensorSheaf`).

## Coherence without the local theory of dualizing complexes

The source gets coherence of `ω_X` from `ω_X^•` being a dualizing complex ([Stacks, Tags 0AWI,
0AA3]), which this development does not have. Instead only clause (5) of [Stacks, Tag 0BS2] —
`Hom(ℱ, ω_X) = H¹(X, ℱ)^∨` on quasi-coherent `ℱ` — is used, through a growth argument:

* `ω_X` is quasi-coherent, hence the directed union of its coherent submodules `𝒢`
  ([Stacks, Tag 01PG]);
* for a globally generated `ℒ` of degree at least two and every `n`,
  `χ(𝒢) + (n + 1) χ_ℒ(𝒢) ≤ (n + 1) deg(ℒ) - χ(𝒪_X)` with `χ_ℒ(𝒢) = χ(𝒢 ⊗ ℒ) - χ(𝒢)`
  (`eulerCharacteristic_add_mul_twistDegree_le`): `H⁰(𝒢 ⊗ ℒ^{⊗ (n+1)}) = Hom(ℒ^{⊗ -(n+1)}, 𝒢)`
  embeds in `Hom(ℒ^{⊗ -(n+1)}, ω_X) = H¹(ℒ^{⊗ -(n+1)})^∨`, whose dimension is
  `(n + 1) deg(ℒ) - χ(𝒪_X)` by Riemann–Roch; so `χ_ℒ(𝒢) ≤ deg(ℒ)`;
* `χ_ℒ(𝒢) = Σ_ξ length_ξ(𝒢) deg(ℒ|_{C_ξ})` over the one-dimensional components, and
  `deg(ℒ|_{C_ξ}) > 0` for a very ample `ℒ` ([Stacks, Tags 01VT, 0BEY, 0BEV]), so `χ_ℒ` is monotone
  and is constant only along steps with zero-dimensional support, on which `χ` grows by `h⁰`;
* `χ(𝒢) ≤ h⁰(ω_X)`; so a `𝒢` maximizing first `χ_ℒ` and then `χ` contains every coherent
  submodule (`exists_forall_le_of_bddAbove_of_monotone`), and is `ω_X`.

This runs over `k̄`, where a very ample module is globally generated; the inverse image of `ω_X`
to `X_{k̄}` is `ω_{X_{k̄}}` by `pullbackDualizingSheafOverFieldIso` (part (2) of
[Stacks, Tag 0E32] at the dualizing sheaf), and finite type descends along `X_{k̄} ⟶ X`.

Only the coherence part of clause (2) of [Stacks, Tag 0BS2] is proved, and with the hypothesis
that a very ample module of degree at least two exists, so no attribute of that tag is attached.

## References

* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Invertible (tensorPowerModule)
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

open Stacks.AlgebraicGeometry.ComponentDegrees in
/-- Cohomology of a module on the curve vanishes in degrees `≥ 2`. -/
private theorem isZero_cohomologyOverField_of_two_le (N : S.X.Modules) (m : ℕ) (hm : 2 ≤ m) :
    IsZero (cohomologyOverField S.k S.f N m) :=
  isZero_cohomologyOverField_of_topologicalKrullDim_le S.k S.f N (d := 1)
    (le_of_eq S.dimension_one) (by omega)

/-- **A very ample invertible module has positive degree on every one-dimensional component.**
It is ample ([Stacks, Tag 01VT]), the degree on a reduced one-dimensional component `Z` is the
intersection number `(ℒ · Z)` ([Stacks, Tag 0BEY]), and that is positive for an ample `ℒ`
([Stacks, Tag 0BEV]). -/
theorem componentDegree_pos_of_isRelativelyVeryAmple (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L) (ξ : genericPointsOne S.X) :
    0 < componentDegree S.k S.f (le_of_eq S.dimension_one) L 1 ξ := by
  have := S.proper
  have hL1 : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f
      (Stacks.Ample.tensorPowModule S.X L ((1 : ℕ) : ℤ)) := by
    obtain ⟨E, hE, i, hi, hcomp, ⟨e⟩⟩ := hL
    exact ⟨E, hE, i, hi, hcomp, ⟨Stacks.Ample.tensorPowModuleOneIso S.X L ≪≫ e⟩⟩
  have hamp : Stacks.Ample.IsAmple S.X L :=
    (Stacks.AmpleRelativeFiniteType.isAmple_iff_exists_isRelativelyVeryAmple S.f L).2
      ⟨1, le_rfl, hL1⟩
  have hmod : Scheme.Modules.IsAmple S.X L :=
    Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple S.X L hamp
  have hpos := degreeWithRespectTo_pos S.k S.f (reducedComponentι S.X ξ) 1
    (topologicalKrullDim_reducedComponent S.X ξ) L hmod
  rw [degreeWithRespectTo_eq_invertibleCurveDegree] at hpos
  refine hpos.trans_eq ?_
  unfold componentDegree
  rw [invertibleCurveDegree_eq_curveDegree]

/-- **`H⁰(X, ω_X)` is finite-dimensional**: it is `Hom(𝒪_X, ω_X)`, which clause (5) of
[Stacks, Tag 0BS2] identifies with the dual of the finite-dimensional `H¹(X, 𝒪_X)`. -/
theorem finiteDimensional_cohomologyOverField_zero_dualizingSheafOverField :
    FiniteDimensional S.k
      (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 0) := by
  let := Scheme.Modules.linearOverBase S.f
  let : Functor.Linear S.k (globalSectionsOver S.f) := globalSectionsOver_linear_linearOverBase S.f
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have : (Stacks.Ample.unitModule S.X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent S.X
  have : FiniteDimensional S.k (cohomologyOverField S.k S.f (Stacks.Ample.unitModule S.X) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper S.k S.f _ 1
  exact Module.Finite.equiv
    (((cohomologyOverFieldZeroLinearEquivGlobalSectionsOver S.f _).trans
      (unitHomLinearEquivGlobalSections S.f _).symm).trans
      (Stacks.Duality.clauseFiveLinearEquiv S.f (le_of_eq S.dimension_one) _
        (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S.X))).symm

/-- `H⁰(X, 𝒢 ⊗ ℒ) ≃ Hom(ℒ^{⊗ -1}, 𝒢)` as `k`-vector spaces, for an invertible `ℒ`. -/
private theorem nonempty_linearEquiv_cohomologyOverField_zero_tensorSheaf (G : S.X.Modules)
    (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    letI := Scheme.Modules.linearOverBase S.f
    Nonempty (cohomologyOverField S.k S.f
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
        (S.X.ringCatSheaf.property)⟩).obj G).obj (L))) 0 ≃ₗ[S.k]
      (tensorPowerModule L (-1) ⟶ G)) := by
  let := Scheme.Modules.linearOverBase S.f
  let : Functor.Linear S.k (globalSectionsOver S.f) := globalSectionsOver_linear_linearOverBase S.f
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have := S.proper
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (tensorPowerModule L (-1)) 1 :=
    inferInstance
  let N := tensorPowerModule L (-1)
  let e1 := ((cohomologyOverFieldFunctor S.k S.f 0).mapIso
    (tensorSheafDualSheafTensorPowerModuleNegOneIso S.X L G)).toLinearEquiv.symm
  let e2 := ((cohomologyOverFieldFunctor S.k S.f 0).mapIso
    (Stacks.SheafOfModules.Scheme.dualTensorIsoSheafHomOfRank N G 1)).toLinearEquiv
  let e3 := cohomologyOverFieldZeroLinearEquivGlobalSectionsOver S.f
    ((Stacks.Algebraization.sheafHomFunctor S.X N).obj G)
  let e4 := (internalHomSectionsTopLinearEquivGlobalSections S.f N G).symm
  exact ⟨((e1.trans e2).trans e3).trans e4⟩

/-- `Hom(ℒ^{⊗ -1}, ω_X)` is finite-dimensional, of the dimension of `H¹(X, ℒ^{⊗ -1})`: clause (5)
of [Stacks, Tag 0BS2]. -/
private theorem finrank_hom_tensorPowerModule_neg_one_dualizingSheafOverField
    (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    letI := Scheme.Modules.linearOverBase S.f
    FiniteDimensional S.k (tensorPowerModule L (-1) ⟶ Stacks.Duality.dualizingSheafOverField S.f) ∧
      Module.finrank S.k (tensorPowerModule L (-1) ⟶ Stacks.Duality.dualizingSheafOverField S.f) =
        Module.finrank S.k (cohomologyOverField S.k S.f (tensorPowerModule L (-1)) 1) := by
  let := Scheme.Modules.linearOverBase S.f
  let : Functor.Linear S.k (globalSectionsOver S.f) := globalSectionsOver_linear_linearOverBase S.f
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have := S.proper
  let N := tensorPowerModule L (-1)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1 := inferInstance
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} N :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N 1
  have : N.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank S.k S.f N 1
  have : FiniteDimensional S.k (cohomologyOverField S.k S.f N 1) :=
    finiteDimensional_cohomologyOverField_of_isProper S.k S.f _ 1
  let e5 := Stacks.Duality.clauseFiveLinearEquiv S.f (le_of_eq S.dimension_one) N
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree N)
  exact ⟨Module.Finite.equiv e5.symm, e5.finrank_eq.trans Subspace.dual_finrank_eq⟩

/-- **`H⁰(X, ω_X ⊗ ℒ)` is finite-dimensional** for an invertible `ℒ`: it is
`Hom(ℒ^{⊗ -1}, ω_X)`, the dual of the finite-dimensional `H¹(X, ℒ^{⊗ -1})` by clause (5) of
[Stacks, Tag 0BS2]. -/
theorem finiteDimensional_cohomologyOverField_zero_tensorSheaf_dualizingSheafOverField
    (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    FiniteDimensional S.k (cohomologyOverField S.k S.f
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
        (S.X.ringCatSheaf.property)⟩).obj
        ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))) 0) := by
  let := Scheme.Modules.linearOverBase S.f
  obtain ⟨e⟩ := S.nonempty_linearEquiv_cohomologyOverField_zero_tensorSheaf
    (Stacks.Duality.dualizingSheafOverField S.f) L
  have := (S.finrank_hom_tensorPowerModule_neg_one_dualizingSheafOverField L).1
  exact Module.Finite.equiv e.symm

/-- **`dim_k H⁰(X, 𝒢 ⊗ ℒ) ≤ dim_k H¹(X, ℒ^{⊗ -1})` for a submodule `𝒢` of `ω_X`.** `H⁰(X, 𝒢 ⊗ ℒ)`
is `Hom(ℒ^{⊗ -1}, 𝒢)`, which embeds in `Hom(ℒ^{⊗ -1}, ω_X)`, and that is the dual of
`H¹(X, ℒ^{⊗ -1})` by clause (5) of [Stacks, Tag 0BS2]. No finiteness of `ω_X` is used. -/
theorem finrank_cohomologyOverField_zero_tensorSheaf_le_of_mono (G : S.X.Modules)
    (ι : G ⟶ Stacks.Duality.dualizingSheafOverField S.f) [Mono ι]
    (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    Module.finrank S.k (cohomologyOverField S.k S.f
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
        (S.X.ringCatSheaf.property)⟩).obj G).obj (L))) 0) ≤
      Module.finrank S.k (cohomologyOverField S.k S.f (tensorPowerModule L (-1)) 1) := by
  let := Scheme.Modules.linearOverBase S.f
  obtain ⟨e⟩ := S.nonempty_linearEquiv_cohomologyOverField_zero_tensorSheaf G L
  obtain ⟨hfin, hrank⟩ := S.finrank_hom_tensorPowerModule_neg_one_dualizingSheafOverField L
  have hinj : Function.Injective (Linear.rightComp S.k (tensorPowerModule L (-1)) ι) :=
    fun a b hab => (cancel_mono ι).mp hab
  exact (e.finrank_eq.trans_le (LinearMap.finrank_le_finrank_of_injective hinj)).trans_eq hrank

/-! ### The degree of a coherent module along `ℒ` -/

section Degree

variable (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]

/-- `ℒ` is coherent, being finite locally free of rank one. -/
theorem isCoherent_of_isInvertible' : L.IsCoherent :=
  have := S.proper
  Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank S.k S.f L 1

/-- **The degree of a coherent `ℱ` along `ℒ`**, `χ(ℱ ⊗ ℒ) - χ(ℱ)`: the quantity of
[Stacks, Tag 0AYU] at `ℱ` with `ℰ = ℒ`. -/
abbrev twistDegree (F : S.X.Modules) (hF : F.IsCoherent) : ℤ :=
  eulerCharacteristicTensorSheafSub S.k S.f L (S.isCoherent_of_isInvertible' L) 1 F hF

open Stacks.AlgebraicGeometry.ComponentDegreeDevissage in
/-- `χ(ℱ ⊗ ℒ) - χ(ℱ) = Σ_ξ length_ξ(ℱ) · deg(ℒ|_{C_ξ})` over the one-dimensional components. -/
theorem twistDegree_eq_sum [Fintype (genericPointsOne S.X)] (F : S.X.Modules) (hF : F.IsCoherent) :
    S.twistDegree L F hF = ∑ ξ : genericPointsOne S.X,
      (stalkLengthNat F ξ.1 : ℤ) *
        Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree S.k S.f
          (le_of_eq S.dimension_one) L 1 ξ := by
  have := S.proper
  exact eulerCharacteristicTensorSheafSub_eq_sum_stalkLengthNat S.k S.f
    (le_of_eq S.dimension_one) L (S.isCoherent_of_isInvertible' L) 1 F hF

variable {L} (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L)

include hL in
/-- For a very ample `ℒ` the degree of every coherent module along `ℒ` is nonnegative. -/
theorem twistDegree_nonneg (F : S.X.Modules) (hF : F.IsCoherent) : 0 ≤ S.twistDegree L F hF := by
  classical
  have := S.proper
  have : IsNoetherian S.X := S.isNoetherian
  have : Fintype (genericPointsOne S.X) :=
    @Fintype.ofFinite _
      (Stacks.AlgebraicGeometry.ComponentDegrees.finite_genericPointsOne S.X).to_subtype
  rw [twistDegree_eq_sum]
  exact Finset.sum_nonneg fun ξ _ =>
    mul_nonneg (Int.natCast_nonneg _) (S.componentDegree_pos_of_isRelativelyVeryAmple L hL ξ).le

include hL in
/-- **A coherent module of degree zero along a very ample `ℒ` has zero-dimensional support**:
its length vanishes at every generic point of a one-dimensional component. -/
theorem supp_dim_le_zero_of_twistDegree_eq_zero (F : S.X.Modules) (hF : F.IsCoherent)
    (h0 : S.twistDegree L F hF = 0) :
    topologicalKrullDim (SheafOfModules.supp F) ≤ 0 := by
  classical
  have := S.proper
  have : IsNoetherian S.X := S.isNoetherian
  have : Fintype (genericPointsOne S.X) :=
    @Fintype.ofFinite _
      (Stacks.AlgebraicGeometry.ComponentDegrees.finite_genericPointsOne S.X).to_subtype
  rw [twistDegree_eq_sum] at h0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun ξ _ =>
    mul_nonneg (Int.natCast_nonneg _)
      (S.componentDegree_pos_of_isRelativelyVeryAmple L hL ξ).le).mp h0
  refine topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne
    (le_of_eq S.dimension_one) F hF fun x hx => ?_
  have hx0 := hterm ⟨x, hx⟩ (Finset.mem_univ _)
  have hlen : Stacks.AlgebraicGeometry.ComponentDegreeDevissage.stalkLengthNat F x = 0 := by
    rcases mul_eq_zero.mp hx0 with h | h
    · exact_mod_cast h
    · exact absurd h (S.componentDegree_pos_of_isRelativelyVeryAmple L hL ⟨x, hx⟩).ne'
  have hfin := Stacks.AlgebraicGeometry.ComponentDegreeDevissage.length_stalk_ne_top_of_isCoherent
    S.k S.f ⟨x, hx⟩ F hF
  have hlen0 : Module.length (S.X.presheaf.stalk x) (F.presheaf.stalk x) = 0 := by
    unfold Stacks.AlgebraicGeometry.ComponentDegreeDevissage.stalkLengthNat at hlen
    exact (ENat.toNat_eq_zero.mp hlen).resolve_right hfin
  have hsub : Subsingleton (F.presheaf.stalk x) := Module.length_eq_zero_iff.mp hlen0
  exact notMem_supp_of_subsingleton_modulesStalk F x hsub

end Degree

/-! ### The positive tensor powers of `ℒ` -/

section Powers

variable (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]

/-- `ℒ^{⊗ (n + 1)}`, the tensor power of [Stacks, Tag 01CK] in degree `n + 1`. -/
abbrev succPow (n : ℕ) : S.X.Modules :=
  _root_.SheafOfModules.tensorPower (Opens.grothendieckTopology S.X) L (n + 1)

omit [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] in
/-- `ℒ^{⊗ 1} = ℒ`. -/
theorem succPow_zero : S.succPow L 0 = L := rfl

omit [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] in
/-- `ℒ^{⊗ (n + 2)} = ℒ ⊗ ℒ^{⊗ (n + 1)}`. -/
theorem succPow_succ (n : ℕ) : S.succPow L (n + 1) =
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
      (S.X.ringCatSheaf.property)⟩).obj L).obj (S.succPow L n)) := rfl

/-- The positive tensor powers of an invertible module are invertible ([Stacks, Tag 01CT]). -/
theorem isInvertible_succPow : ∀ n : ℕ,
    SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 (S.succPow L n)
  | 0 => inferInstanceAs (SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L)
  | n + 1 =>
    have := isInvertible_succPow n
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible S.X.presheaf
      S.X.ringCatSheaf.property L (S.succPow L n)

/-- `deg(ℒ^{⊗ (n + 1)}) = (n + 1) deg(ℒ)` ([Stacks, Tag 0AYX]). -/
theorem invertibleCurveDegree_succPow : ∀ n : ℕ,
    @invertibleCurveDegree S.k _ S.X S.f _ (le_of_eq S.dimension_one) (S.succPow L n)
        (S.isInvertible_succPow L n) =
      ((n : ℤ) + 1) * invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L
  | 0 => by
    simp only [Nat.cast_zero, zero_add, one_mul]
    rfl
  | n + 1 => by
    have := S.proper
    have := S.isInvertible_succPow L n
    have := S.isInvertible_succPow L (n + 1)
    have h := invertibleCurveDegree_tensorSheaf_eq_add S.k S.f (le_of_eq S.dimension_one) L
      (S.succPow L n)
    have ih := invertibleCurveDegree_succPow n
    refine h.trans ?_
    rw [ih]
    push_cast
    ring

omit [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] in
/-- Generating sections of `ℒ` give generating sections of `ℒ^{⊗ (n + 1)}` ([Stacks, Tag 01CK]). -/
theorem nonempty_generatingSections_succPow (σ : L.GeneratingSections) (n : ℕ) :
    Nonempty (S.succPow L n).GeneratingSections :=
  ⟨(Stacks.SheafOfModules.exists_generatingSections_tensorPower _ σ (n + 1)).choose⟩

/-- The tensor product of two coherent modules on the curve, as an instance-free statement. -/
theorem isCoherent_tensorSheaf' (F G : S.X.Modules) (hF : F.IsCoherent) (hG : G.IsCoherent) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
      (S.X.ringCatSheaf.property)⟩).obj F).obj G)).IsCoherent :=
  @SheafOfModules.tensorSheaf_isCoherent S.X.toRingedSpace F G hF hG

/-- The positive tensor powers `ℒ^{⊗ (n + 1)}` of an invertible module are coherent. -/
theorem isCoherent_succPow (n : ℕ) : (S.succPow L n).IsCoherent :=
  @isCoherent_of_isInvertible' S (S.succPow L n) (S.isInvertible_succPow L n)

/-- **`χ(𝒢 ⊗ ℒ^{⊗ (n + 1)}) = χ(𝒢) + (n + 1)(χ(𝒢 ⊗ ℒ) - χ(𝒢))`** for coherent `𝒢`: the Euler
characteristic is additive in the invertible factor ([Stacks, Tag 0AYX] in the form
`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_isCoherent`). -/
theorem eulerCharacteristic_tensorSheaf_succPow (G : S.X.Modules) (hG : G.IsCoherent) :
    ∀ n : ℕ,
    @eulerCharacteristic S.k _ S.X S.f _ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
      (S.X.ringCatSheaf.property)⟩).obj G).obj (S.succPow L n))
        (S.isCoherent_tensorSheaf' G (S.succPow L n) hG (S.isCoherent_succPow L n)) =
      @eulerCharacteristic S.k _ S.X S.f _ G hG + ((n : ℤ) + 1) *
        (@eulerCharacteristic S.k _ S.X S.f _
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj G).obj L) (S.isCoherent_tensorSheaf' G L hG
          (S.isCoherent_of_isInvertible' L)) - @eulerCharacteristic S.k _ S.X S.f _ G hG)
  | 0 => by
    rw [Nat.cast_zero, zero_add, one_mul, add_sub_cancel]
    rfl
  | n + 1 => by
    have := S.isInvertible_succPow L n
    have ih := eulerCharacteristic_tensorSheaf_succPow G hG n
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 := inferInstance
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.succPow L n) 1 := inferInstance
    have hLc := S.isCoherent_of_isInvertible' L
    have hMc := S.isCoherent_succPow L n
    have hM'c := S.isCoherent_succPow L (n + 1)
    have key : @eulerCharacteristic S.k _ S.X S.f _
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
        (S.X.ringCatSheaf.property)⟩).obj (S.succPow L (n + 1))).obj G)
          (S.isCoherent_tensorSheaf' _ G hM'c hG) + @eulerCharacteristic S.k _ S.X S.f _ G hG =
        @eulerCharacteristic S.k _ S.X S.f _
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj L).obj G)
          (S.isCoherent_tensorSheaf' L G hLc hG) +
        @eulerCharacteristic S.k _ S.X S.f _
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj (S.succPow L n)).obj G)
          (S.isCoherent_tensorSheaf' _ G hMc hG) := by
      have := eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_isCoherent S.k S.f
        (le_of_eq S.dimension_one) L (S.succPow L n) 1 1 G hG
        (S.isCoherent_tensorSheaf' L G hLc hG) (S.isCoherent_tensorSheaf' (S.succPow L n) G hMc hG)
        (S.isCoherent_tensorSheaf' (S.succPow L (n + 1)) G hM'c hG)
      simp only [Nat.cast_one, mul_one, one_mul] at this
      exact this
    have c1 : @eulerCharacteristic S.k _ S.X S.f _
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
        (S.X.ringCatSheaf.property)⟩).obj G).obj (S.succPow L (n + 1)))
          (S.isCoherent_tensorSheaf' G _ hG hM'c) =
        @eulerCharacteristic S.k _ S.X S.f _
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj (S.succPow L (n + 1))).obj G)
          (S.isCoherent_tensorSheaf' _ G hM'c hG) :=
      @eulerCharacteristic_tensorSheaf_comm S.k _ S.X S.f _ G (S.succPow L (n + 1)) hG hM'c
    have c2 : @eulerCharacteristic S.k _ S.X S.f _
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
        (S.X.ringCatSheaf.property)⟩).obj G).obj (S.succPow L n))
          (S.isCoherent_tensorSheaf' G _ hG hMc) =
        @eulerCharacteristic S.k _ S.X S.f _
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj (S.succPow L n)).obj G)
          (S.isCoherent_tensorSheaf' _ G hMc hG) :=
      @eulerCharacteristic_tensorSheaf_comm S.k _ S.X S.f _ G (S.succPow L n) hG hMc
    have c3 : @eulerCharacteristic S.k _ S.X S.f _
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
        (S.X.ringCatSheaf.property)⟩).obj G).obj L)
          (S.isCoherent_tensorSheaf' G _ hG hLc) =
        @eulerCharacteristic S.k _ S.X S.f _
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj L).obj G)
          (S.isCoherent_tensorSheaf' _ G hLc hG) :=
      @eulerCharacteristic_tensorSheaf_comm S.k _ S.X S.f _ G L hG hLc
    push_cast
    linear_combination c1 + key - c2 - c3 + ih

/-- **The growth bound.** For a coherent submodule `𝒢 ⊆ ω_X` and a globally generated `ℒ` of
degree at least two, `χ(𝒢) + (n + 1) χ_ℒ(𝒢) ≤ (n + 1) deg(ℒ) - χ(𝒪_X)` for every `n`, where
`χ_ℒ(𝒢) = χ(𝒢 ⊗ ℒ) - χ(𝒢)`. Indeed `χ(𝒢 ⊗ ℒ^{⊗ (n+1)}) ≤ dim H⁰(𝒢 ⊗ ℒ^{⊗ (n+1)}) ≤
dim H¹(ℒ^{⊗ -(n+1)})`, and `H⁰(ℒ^{⊗ -(n+1)}) = 0` because `ℒ^{⊗ (n+1)}` is globally generated
and not trivial, so the last dimension is `deg(ℒ^{⊗ (n+1)}) - χ(𝒪_X)` by Riemann–Roch. -/
theorem eulerCharacteristic_add_mul_twistDegree_le (σ : L.GeneratingSections)
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L)
    (G : S.X.Modules) (hG : G.IsCoherent) (ι : G ⟶ Stacks.Duality.dualizingSheafOverField S.f)
    [Mono ι] (n : ℕ) :
    @eulerCharacteristic S.k _ S.X S.f _ G hG + ((n : ℤ) + 1) * S.twistDegree L G hG ≤
      ((n : ℤ) + 1) * invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L -
        @eulerCharacteristic S.k _ S.X S.f _ (SheafOfModules.unit S.X.ringCatSheaf)
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k S.f) := by
  have := S.isInvertible_succPow L n
  set M := S.succPow L n with hM
  have hdegM := S.invertibleCurveDegree_succPow L n
  have hdM : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) M := by
    rw [hdegM]; nlinarith
  obtain ⟨σM⟩ := S.nonempty_generatingSections_succPow L σ n
  have hinv : Subsingleton Γ(tensorPowerModule M (-1), (⊤ : S.X.Opens)) :=
    subsingleton_globalSections_inverse_of_generatingSections M σM
      (S.not_isTrivial_of_two_le_invertibleCurveDegree M hdM)
  have hNcoh : (tensorPowerModule M (-1)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank S.k S.f
      (tensorPowerModule M (-1)) 1
  have hunit : (SheafOfModules.unit S.X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k S.f
  have hinverse := eulerCharacteristic_eq_sub_of_isZero S.k S.f (tensorPowerModule M (-1))
    (fun m hm => S.isZero_cohomologyOverField_of_two_le _ m hm)
  have hinvzero : Module.finrank S.k
      (cohomologyOverField S.k S.f (tensorPowerModule M (-1)) 0) = 0 :=
    finrank_cohomologyOverField_zero_eq_zero_of_subsingleton_sections S.k S.f _ hinv
  have hneg := invertibleCurveDegree_tensorPowerModule_neg_one_of_topologicalKrullDim_le_one
    S.k S.f (le_of_eq S.dimension_one) M
  have hdeg : invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one)
        (tensorPowerModule M (-1)) =
      eulerCharacteristic S.k S.f (tensorPowerModule M (-1)) -
        eulerCharacteristic S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) :=
    invertibleCurveDegree_eq_eulerCharacteristic_sub S.k S.f (le_of_eq S.dimension_one) _
  have hGM := S.isCoherent_tensorSheaf' G M hG (S.isCoherent_succPow L n)
  have hle0 := @eulerCharacteristic_le_finrank_cohomologyOverField_zero S.k _ S.X S.f _ _ hGM
    (fun m hm => S.isZero_cohomologyOverField_of_two_le _ m hm)
  have hle1 := S.finrank_cohomologyOverField_zero_tensorSheaf_le_of_mono G ι M
  have hpow := S.eulerCharacteristic_tensorSheaf_succPow L G hG n
  have htw : S.twistDegree L G hG =
      @eulerCharacteristic S.k _ S.X S.f _
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
          (S.X.ringCatSheaf.property)⟩).obj G).obj L)
        (S.isCoherent_tensorSheaf' G L hG (S.isCoherent_of_isInvertible' L)) -
        @eulerCharacteristic S.k _ S.X S.f _ G hG := by
    simp only [twistDegree, eulerCharacteristicTensorSheafSub, Nat.cast_one, one_mul]
  rw [htw]
  have hcast : ((Module.finrank S.k (cohomologyOverField S.k S.f
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
        (S.X.ringCatSheaf.property)⟩).obj G).obj M) 0) : ℕ) : ℤ) ≤
      ((Module.finrank S.k (cohomologyOverField S.k S.f (tensorPowerModule M (-1)) 1) : ℕ) : ℤ) :=
    by exact_mod_cast hle1
  have h1 : @eulerCharacteristic S.k _ S.X S.f _ _ hGM ≤
      ((Module.finrank S.k (cohomologyOverField S.k S.f (tensorPowerModule M (-1)) 1) : ℕ) : ℤ) :=
    hle0.trans hcast
  rw [hinverse, hinvzero] at hdeg
  rw [hneg, hdegM] at hdeg
  have e1 : @eulerCharacteristic S.k _ S.X S.f _ _ hGM =
      @eulerCharacteristic S.k _ S.X S.f _
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
          (S.X.ringCatSheaf.property)⟩).obj G).obj (S.succPow L n))
        (S.isCoherent_tensorSheaf' G (S.succPow L n) hG (S.isCoherent_succPow L n)) := rfl
  rw [e1, hpow] at h1
  push_cast at hdeg h1
  linarith

end Powers

/-- **A directed family stabilizes under two bounded monotone invariants.** Let `Q` be a
nonempty preordered type in which any two elements have an upper bound, and let `τ, χ : Q → ℤ` be
bounded above, with `τ` monotone, `χ` monotone wherever `τ` is constant, and `B ≤ A` as soon as
`A ≤ B` with `τ A = τ B` and `χ A = χ B`. Then `Q` has a greatest element: first maximize `τ`,
then maximize `χ` above that. -/
theorem exists_forall_le_of_bddAbove_of_monotone {Q : Type*} [Preorder Q] [Nonempty Q]
    (hdir : ∀ A B : Q, ∃ C, A ≤ C ∧ B ≤ C) (τ χ : Q → ℤ) (D E : ℤ) (hτD : ∀ A, τ A ≤ D)
    (hχE : ∀ A, χ A ≤ E) (hτ : ∀ A B, A ≤ B → τ A ≤ τ B)
    (hχ : ∀ A B, A ≤ B → τ A = τ B → χ A ≤ χ B)
    (hle : ∀ A B, A ≤ B → τ A = τ B → χ A = χ B → B ≤ A) : ∃ A : Q, ∀ B, B ≤ A := by
  obtain ⟨t, ⟨A₁, rfl⟩, ht⟩ := Int.exists_greatest_of_bdd (P := fun z => ∃ A, τ A = z)
    ⟨D, fun z ⟨A, hA⟩ => hA ▸ hτD A⟩ ⟨_, Classical.arbitrary Q, rfl⟩
  have hmax : ∀ B, τ B ≤ τ A₁ := fun B => ht _ ⟨B, rfl⟩
  obtain ⟨c, ⟨A₂, hA₁₂, rfl⟩, hc⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ A, A₁ ≤ A ∧ χ A = z)
    ⟨E, fun z ⟨A, _, hA⟩ => hA ▸ hχE A⟩ ⟨_, A₁, le_rfl, rfl⟩
  have habove : ∀ B, A₂ ≤ B → B ≤ A₂ := by
    intro B hB
    have hτeq : τ A₂ = τ B :=
      le_antisymm (hτ _ _ hB) ((hmax B).trans (hτ _ _ hA₁₂))
    have hχeq : χ A₂ = χ B :=
      le_antisymm (hχ _ _ hB hτeq) (hc _ ⟨B, hA₁₂.trans hB, rfl⟩)
    exact hle _ _ hB hτeq hχeq
  refine ⟨A₂, fun B => ?_⟩
  obtain ⟨C, hAC, hBC⟩ := hdir A₂ B
  exact hBC.trans (habove C hAC)

/-! ### Coherence over an algebraically closed field -/

section Coherence

variable (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]

/-- **The degree along `ℒ` of a coherent submodule of `ω_X` is at most `deg(ℒ)`**, for a globally
generated `ℒ` of degree at least two: let `n → ∞` in
`eulerCharacteristic_add_mul_twistDegree_le`. -/
theorem twistDegree_le_of_mono (σ : L.GeneratingSections)
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L)
    (G : S.X.Modules) (hG : G.IsCoherent) (ι : G ⟶ Stacks.Duality.dualizingSheafOverField S.f)
    [Mono ι] :
    S.twistDegree L G hG ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L := by
  by_contra hlt
  push Not at hlt
  set c := @eulerCharacteristic S.k _ S.X S.f _ G hG
  set e := @eulerCharacteristic S.k _ S.X S.f _ (SheafOfModules.unit S.X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k S.f)
  set n := (c + e).natAbs
  have h := S.eulerCharacteristic_add_mul_twistDegree_le L σ hd G hG ι n
  have habs : (n : ℤ) ≥ -(c + e) := by
    have := Int.natAbs_neg (c + e)
    have := Int.le_natAbs (a := -(c + e))
    omega
  have h2 : ((n : ℤ) + 1) * (S.twistDegree L G hG -
      invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) ≥ ((n : ℤ) + 1) * 1 :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  nlinarith

/-- **`χ(𝒢) ≤ dim_k H⁰(X, ω_X)`** for a coherent submodule `𝒢 ⊆ ω_X`. -/
theorem eulerCharacteristic_le_of_mono (G : S.X.Modules) (hG : G.IsCoherent)
    (ι : G ⟶ Stacks.Duality.dualizingSheafOverField S.f) [Mono ι] :
    @eulerCharacteristic S.k _ S.X S.f _ G hG ≤
      (Module.finrank S.k (cohomologyOverField S.k S.f
        (Stacks.Duality.dualizingSheafOverField S.f) 0) : ℤ) := by
  let := Scheme.Modules.linearOverBase S.f
  let : Functor.Linear S.k (globalSectionsOver S.f) := globalSectionsOver_linear_linearOverBase S.f
  have := S.finiteDimensional_cohomologyOverField_zero_dualizingSheafOverField
  have : FiniteDimensional S.k (Stacks.Ample.unitModule S.X ⟶
      Stacks.Duality.dualizingSheafOverField S.f) :=
    Module.Finite.equiv ((cohomologyOverFieldZeroLinearEquivGlobalSectionsOver S.f _).trans
      (unitHomLinearEquivGlobalSections S.f _).symm)
  have hinj : Function.Injective (Linear.rightComp S.k (Stacks.Ample.unitModule S.X) ι) :=
    fun a b hab => (cancel_mono ι).mp hab
  have h0 : Module.finrank S.k (cohomologyOverField S.k S.f G 0) ≤
      Module.finrank S.k (cohomologyOverField S.k S.f
        (Stacks.Duality.dualizingSheafOverField S.f) 0) := by
    rw [finrank_cohomologyOverField_zero_eq_finrank_hom_unit S.f,
      finrank_cohomologyOverField_zero_eq_finrank_hom_unit S.f]
    exact LinearMap.finrank_le_finrank_of_injective hinj
  exact
    (@eulerCharacteristic_le_finrank_cohomologyOverField_zero S.k _ S.X S.f _ G hG
      (fun m hm => S.isZero_cohomologyOverField_of_two_le G m hm)).trans
    (by exact_mod_cast h0)

variable {L} in
/-- **A step of the stabilization**: for coherent `A ⊆ B ⊆ ω_X` the quotient `B/A` is coherent,
`χ` and the degree along `ℒ` are additive, and `B ≤ A` as soon as `B/A = 0`. -/
theorem exists_quotient_of_le {A B : Subobject (Stacks.Duality.dualizingSheafOverField S.f)}
    (h : A ≤ B) (hA : (A : S.X.Modules).IsCoherent) (hB : (B : S.X.Modules).IsCoherent) :
    ∃ (C : S.X.Modules) (hC : C.IsCoherent), (IsZero C → B ≤ A) ∧
      @eulerCharacteristic S.k _ S.X S.f _ _ hB =
        @eulerCharacteristic S.k _ S.X S.f _ _ hA + @eulerCharacteristic S.k _ S.X S.f _ C hC ∧
      S.twistDegree L _ hB = S.twistDegree L _ hA + S.twistDegree L C hC := by
  let ι := Subobject.ofLE A B h
  have hC := isCoherent_cokernel_of_isCoherent hA hB ι
  have hepi : Epi (cokernel.π ι) :=
    ⟨fun _ _ h => Cofork.IsColimit.hom_ext (cokernelIsCokernel ι) h⟩
  let T := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _)
    inferInstance hepi
  refine ⟨cokernel ι, hC, fun hz => ?_, ?_, ?_⟩
  · have : Epi ι := (Preadditive.epi_iff_isZero_cokernel ι).mpr hz
    have : IsIso ι := isIso_of_mono_of_epi ι
    exact Subobject.le_of_comm (inv ι) (by rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow])
  · have : T.X₁.IsCoherent := hA
    have : T.X₂.IsCoherent := hB
    have : T.X₃.IsCoherent := hC
    exact eulerCharacteristic_add_of_shortExact S.k S.f hT
  · exact eulerCharacteristicTensorSheafSub_add_of_shortExact S.k S.f L
      (S.isCoherent_of_isInvertible' L) 1 hT hA hB hC
      (forall_finiteDimensional_cohomologyOverField_of_isProper S.k S.f)

/-- `χ(𝒞) = dim_k H⁰(X, 𝒞)` for a coherent `𝒞` with zero-dimensional support. -/
private theorem eulerCharacteristic_eq_finrank_zero_of_supp_dim_le_zero (C : S.X.Modules)
    (hC : C.IsCoherent) (hsupp : topologicalKrullDim (SheafOfModules.supp C) ≤ 0) :
    @eulerCharacteristic S.k _ S.X S.f _ C hC =
      Module.finrank S.k (cohomologyOverField S.k S.f C 0) := by
  rw [@eulerCharacteristic_eq_sub_of_isZero S.k _ S.X S.f _ C hC
    (fun m hm => S.isZero_cohomologyOverField_of_two_le C m hm)]
  have := @isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero S.k _ S.X S.f _
    C hC hsupp 1 Nat.one_pos
  have : Module.finrank S.k (cohomologyOverField S.k S.f C 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero this
    Module.finrank_zero_of_subsingleton
  omega

/-- **The dualizing sheaf `ω_X` is coherent** (clause (2) of [Stacks, Tag 0BS2], the coherence
assertion), given a very ample invertible `ℒ` of degree at least two that is generated by its
global sections.

`ω_X` is the union of its coherent submodules `𝒢` ([Stacks, Tag 01PG]). Their degrees along `ℒ`,
`χ(𝒢 ⊗ ℒ) - χ(𝒢) = Σ_ξ length_ξ(𝒢) deg(ℒ|_{C_ξ})`, are bounded by `deg(ℒ)`
(`twistDegree_le_of_mono`: `Hom(ℒ^{⊗ -n}, 𝒢) ⊆ Hom(ℒ^{⊗ -n}, ω_X) = H¹(ℒ^{⊗ -n})^∨` grows like
`n deg ℒ`), and are monotone with positive steps unless the step has zero-dimensional support,
because `ℒ` has positive degree on every component
(`componentDegree_pos_of_isRelativelyVeryAmple`). On a step with zero-dimensional support `χ` grows
by `dim H⁰` of the step, and `χ(𝒢) ≤ dim H⁰(ω_X)`. So a submodule maximizing first the degree and
then `χ` contains all others (`exists_forall_le_of_bddAbove_of_monotone`), and it is `ω_X`. -/
theorem isCoherent_dualizingSheafOverField_of_generatingSections
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L) (σ : L.GeneratingSections)
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) :
    (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent := by
  set ω := Stacks.Duality.dualizingSheafOverField S.f with hωdef
  have hωq : ω.IsQuasicoherent := Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have : IsNoetherian S.X := S.isNoetherian
  let Q := {A : Subobject ω // (A : S.X.Modules).IsQuasicoherent ∧ (A : S.X.Modules).IsFiniteType}
  have coh : ∀ A : Q, (A.1 : S.X.Modules).IsCoherent := fun A =>
    have := A.2.1
    have := A.2.2
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _
  have : Nonempty Q := by
    obtain ⟨G, hG1, hG2, -⟩ := exists_finiteTypeQuasicoherentSubobject_section ω ⊤
      (CompactSpace.isCompact_univ) 0
    exact ⟨⟨G, hG1, hG2⟩⟩
  obtain ⟨A, hA⟩ := exists_forall_le_of_bddAbove_of_monotone (Q := Q)
    (fun A B => by
      obtain ⟨C, hC1, hC2, hAC, hBC⟩ :=
        exists_finiteTypeQuasicoherentSubobject_sup A.2.1 A.2.2 B.2.1 B.2.2
      exact ⟨⟨C, hC1, hC2⟩, hAC, hBC⟩)
    (fun A => S.twistDegree L _ (coh A)) (fun A => @eulerCharacteristic S.k _ S.X S.f _ _ (coh A))
    (invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L)
    (Module.finrank S.k (cohomologyOverField S.k S.f ω 0))
    (fun A => S.twistDegree_le_of_mono L σ hd _ (coh A) A.1.arrow)
    (fun A => S.eulerCharacteristic_le_of_mono _ (coh A) A.1.arrow)
    (fun A B hAB => by
      obtain ⟨C, hC, -, -, hτ⟩ := S.exists_quotient_of_le (L := L) hAB (coh A) (coh B)
      have := S.twistDegree_nonneg hL C hC
      change S.twistDegree L _ (coh A) ≤ S.twistDegree L _ (coh B)
      omega)
    (fun A B hAB hτAB => by
      obtain ⟨C, hC, -, hχ, hτ⟩ := S.exists_quotient_of_le (L := L) hAB (coh A) (coh B)
      have h0 : S.twistDegree L C hC = 0 := by
        change S.twistDegree L _ (coh A) = S.twistDegree L _ (coh B) at hτAB
        omega
      have hsupp := S.supp_dim_le_zero_of_twistDegree_eq_zero hL C hC h0
      have hχC := S.eulerCharacteristic_eq_finrank_zero_of_supp_dim_le_zero C hC hsupp
      change @eulerCharacteristic S.k _ S.X S.f _ _ (coh A) ≤
        @eulerCharacteristic S.k _ S.X S.f _ _ (coh B)
      have := Nat.cast_nonneg (α := ℤ) (Module.finrank S.k (cohomologyOverField S.k S.f C 0))
      omega)
    (fun A B hAB hτAB hχAB => by
      obtain ⟨C, hC, hz, hχ, hτ⟩ := S.exists_quotient_of_le (L := L) hAB (coh A) (coh B)
      have h0 : S.twistDegree L C hC = 0 := by
        change S.twistDegree L _ (coh A) = S.twistDegree L _ (coh B) at hτAB
        omega
      have hsupp := S.supp_dim_le_zero_of_twistDegree_eq_zero hL C hC h0
      have hχ0 : @eulerCharacteristic S.k _ S.X S.f _ C hC = 0 := by
        change @eulerCharacteristic S.k _ S.X S.f _ _ (coh A) =
          @eulerCharacteristic S.k _ S.X S.f _ _ (coh B) at hχAB
        omega
      have hχC := S.eulerCharacteristic_eq_finrank_zero_of_supp_dim_le_zero C hC hsupp
      have hfin0 : Module.finrank S.k (cohomologyOverField S.k S.f C 0) = 0 := by omega
      have : FiniteDimensional S.k (cohomologyOverField S.k S.f C 0) :=
        finiteDimensional_cohomologyOverField_of_isProper S.k S.f C 0
      have h00 : IsZero (cohomologyOverField S.k S.f C 0) :=
        have := Module.finrank_zero_iff.mp hfin0
        ModuleCat.isZero_of_subsingleton _
      exact hz (isZero_of_isZero_cohomologyOverField_zero_of_supp_dim_le_zero S.f hC hsupp h00))
  have htop : A.1 = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← iSup_finiteTypeQuasicoherentSubobject_eq_top ω]
    exact iSup_le fun G => hA ⟨G.obj, G.property⟩
  have hiso : IsIso A.1.arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr htop
  have := A.2.1
  have := A.2.2
  have hft : ω.IsFiniteType := Stacks.Coherent.isFiniteType_of_iso_local (asIso A.1.arrow) A.2.2
  exact
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _

end Coherence

/-! ### Coherence over an arbitrary field, and Tag 0B5H -/

/-- **The dualizing sheaf of a proper curve is coherent** (the coherence assertion of clause (2)
of [Stacks, Tag 0BS2]) in Situation [Stacks, Tag 0B5D], given a very ample invertible module of
degree at least two — the hypotheses of [Stacks, Tag 0B5H].

Over `k̄` the very ample module is generated by its global sections, so
`isCoherent_dualizingSheafOverField_of_generatingSections` applies to `X_{k̄}` and the inverse
image of `ℒ`. The inverse image of `ω_X` along `g : X_{k̄} ⟶ X` is `ω_{X_{k̄}}`
(`pullbackDualizingSheafOverFieldIso`, part (2) of [Stacks, Tag 0E32] at the dualizing sheaf), and
finite type descends along the flat, surjective, quasi-compact `g`
(`isFiniteType_of_pullback_of_flat_surjective`). -/
theorem isCoherent_dualizingSheafOverField (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L)
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) :
    (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent := by
  let K := AlgebraicClosure S.k
  let L' := (Scheme.Modules.pullback (S.baseChangeProj K)).obj L
  let : SheafOfModules.IsInvertible (S.baseChange K).X.presheaf
      (S.baseChange K).X.ringCatSheaf.2 L' :=
    S.isInvertible_pullback_baseChangeProj K L
  have : IsAlgClosed (S.baseChange K).k := inferInstanceAs (IsAlgClosed (AlgebraicClosure S.k))
  have hL' := S.isRelativelyVeryAmple_baseChange K L hL
  have hd' : 2 ≤ invertibleCurveDegree (S.baseChange K).k (S.baseChange K).f
      (le_of_eq (S.baseChange K).dimension_one) L' :=
    hd.trans_eq (S.invertibleCurveDegree_baseChange K L).symm
  obtain ⟨σ⟩ := (S.baseChange K).nonempty_generatingSections_of_isRelativelyVeryAmple L' hL'
  have hcohK :=
    (S.baseChange K).isCoherent_dualizingSheafOverField_of_generatingSections L' hL' σ hd'
  have hftK : (Stacks.Duality.dualizingSheafOverField (S.baseChange K).f).IsFiniteType :=
    have := hcohK
    SheafOfModules.IsCoherent.isFiniteType
  have hft' : ((Scheme.Modules.pullback (S.baseChangeProj K)).obj
      (Stacks.Duality.dualizingSheafOverField S.f)).IsFiniteType :=
    Stacks.Coherent.isFiniteType_of_iso_local (S.pullbackDualizingSheafOverFieldIso K).symm hftK
  have := Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f
  have hφ : (CommRingCat.ofHom (algebraMap S.k K)).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap S.k K))) :=
    ((flat_and_surjective_SpecMap_iff _).2 hφ).1
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S.k K))) :=
    ((flat_and_surjective_SpecMap_iff _).2 hφ).2
  have : Flat (S.baseChangeProj K) :=
    Flat.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : Surjective (S.baseChangeProj K) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback _ _).flip inferInstance
  have : QuasiCompact (S.baseChangeProj K) :=
    have := S.isAffineHom_baseChangeProj K
    inferInstance
  have hft : (Stacks.Duality.dualizingSheafOverField S.f).IsFiniteType :=
    isFiniteType_of_pullback_of_flat_surjective (S.baseChangeProj K) _ hft'
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  exact
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **[Stacks, Tag 0B5H].** In Situation [Stacks, Tag 0B5D] — a field `k`, a proper scheme `X` of
dimension one over `k` with `H⁰(X, 𝒪_X) = k` — let `ℒ` be a very ample invertible `𝒪_X`-module
with `deg(ℒ) ≥ 2`. Then `ω_X ⊗ ℒ` is globally generated, where
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` is the dualizing sheaf of [Stacks, Tag 0BS2].

This is the source's proof: over `k̄` it is
`nonempty_generatingSections_dualizing_tensorSheaf_of_isAlgClosed_of_isCoherent`, and the general
case is the reduction `nonempty_generatingSections_dualizing_tensorSheaf_of_isoAlgebraicClosure`,
whose two inputs are supplied here — the coherence of `ω_X` by
`isCoherent_dualizingSheafOverField`, and the identification of the inverse image of `ω_X` with
`ω_{X_{k̄}}` (part (2) of [Stacks, Tag 0E32] at the dualizing sheaf) by
`pullbackDualizingSheafOverFieldIso`. Nothing is assumed beyond the source's hypotheses. -/
@[stacks 0B5H]
theorem nonempty_generatingSections_dualizingSheafOverField_tensorSheaf (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L)
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) :
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
      (S.X.ringCatSheaf.property)⟩).obj
      ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))).GeneratingSections :=
  S.nonempty_generatingSections_dualizing_tensorSheaf_of_isoAlgebraicClosure L hL hd
    (S.isCoherent_dualizingSheafOverField L hL hd)
    (S.pullbackDualizingSheafOverFieldIso (AlgebraicClosure S.k))

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end

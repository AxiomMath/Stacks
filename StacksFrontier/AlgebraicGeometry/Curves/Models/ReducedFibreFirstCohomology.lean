module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDownUnconditional
public import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFiltration
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreRadicalComponents
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contribution
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.Immersions

/-!
# The first cohomology of the special fibre and of its reduction

In the situation of [Stacks, Tag 0C61] assume `gcd(m₁, …, mₙ) = 1` and
`H⁰((X_k)_red, 𝒪) = k`. [Stacks, Tag 0CE9] asserts that, when `X` is a minimal model, the map
`H¹(X_k, 𝒪_{X_k}) ⟶ H¹((X_k)_red, 𝒪_{(X_k)_red})` is surjective, with a nontrivial kernel as soon
as `(X_k)_red ≠ X_k`. This file proves it for a model whose associated numerical type is minimal;
by [Stacks, Tag 0CA6] that is the same as being a minimal model.

## Main definitions

* `AlgebraicGeometry.cohomologyOverFieldStructureSheafMap`: for an affine morphism `j : Y ⟶ X` of
  schemes over `k`, the map `Hⁿ(X, 𝒪_X) ⟶ Hⁿ(Y, 𝒪_Y)`, namely `Hⁿ` of `𝒪_X ⟶ j_*𝒪_Y` followed by
  `Hⁿ(X, j_*𝒪_Y) = Hⁿ(Y, 𝒪_Y)` ([Stacks, Tag 089W]).

## Main results

* `AlgebraicGeometry.surjective_cohomologyOverFieldStructureSheafMap_of_isClosedImmersion`: for a
  closed immersion into a proper scheme of dimension at most one over `k`, the map on `H¹` is
  onto. The kernel of `𝒪_X ⟶ j_*𝒪_Y` has no `H²`, the dimension being at most one
  ([Stacks, Tag 02UZ]), and the map is onto.

In the namespace `Stacks.Models.RegularProperModelSituation`:

* `genus_radical_lt_of_isMinimal_associatedNumericalType`: the dimension count,
  `dim H¹((X_k)_red, 𝒪) < dim H¹(X_k, 𝒪)` when `X_k` is not reduced.
* `exists_iso_reduction_specialFiber`: the reduction `X_k.reduction` of the special fibre is the
  reduced closed subscheme of `X` on `X_k`.
* `surjective_and_not_injective_of_isMinimal_associatedNumericalType`: the statement of
  [Stacks, Tag 0CE9] for a model with minimal associated numerical type.

## The argument for the kernel

Take the chain `(X_k)_red = Z₀ ⊆ … ⊆ Z_M = X_k` of [Stacks, Tag 0C68] (it ends at `X_k` because
the gcd is one), with `X_k = Z_{M-1} + Cᵢ`. Every `H⁰(Z_j, 𝒪)` is a field mapping injectively to
`H⁰((X_k)_red, 𝒪) = k`, so it is `k`. By [Stacks, Tag 0CA2] and `(X_k · Cᵢ) = 0`,
`χ(X_k, 𝒪) - χ(Z_{M-1}, 𝒪) = (Cᵢ · Cᵢ) + χ(Cᵢ, 𝒪) = (Cᵢ · Cᵢ) + wᵢ(1 - gᵢ)`. There are at least
two components (one component of multiplicity `gcd = 1` would make `X_k` reduced), so
`(Cᵢ · Cᵢ) < 0` ([Stacks, Tag 0C74]); it is divisible by `wᵢ`, and it is not `-wᵢ` when `gᵢ = 0`
because the numerical type is minimal. Hence `(Cᵢ · Cᵢ) + wᵢ(1 - gᵢ) < 0`, that is
`dim H¹(X_k, 𝒪) > dim H¹(Z_{M-1}, 𝒪) ≥ dim H¹((X_k)_red, 𝒪)`, and a surjection between finite
dimensional spaces of different dimensions is not injective.

## References

* [Stacks Project, Tag 0CE9](https://stacks.math.columbia.edu/tag/0CE9)
* [Stacks Project, Tag 0C68](https://stacks.math.columbia.edu/tag/0C68)
* [Stacks Project, Tag 0CA2](https://stacks.math.columbia.edu/tag/0CA2)
* [Stacks Project, Tag 0C74](https://stacks.math.columbia.edu/tag/0C74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ComponentDegrees
open Stacks.AlgebraicGeometry.CurveEulerBridge
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent
open Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (g : X ⟶ Spec (.of k))

/-- **The map `Hⁿ(X, 𝒪_X) ⟶ Hⁿ(Y, 𝒪_Y)` of an affine morphism `j : Y ⟶ X` over `k`**: `Hⁿ` of the
comparison map `𝒪_X ⟶ j_*𝒪_Y`, followed by the identification `Hⁿ(X, j_*𝒪_Y) = Hⁿ(Y, 𝒪_Y)` of
[Stacks, Tag 089W]. -/
def cohomologyOverFieldStructureSheafMap (j : Y ⟶ X) [IsAffineHom j] (n : ℕ) :
    cohomologyOverField k g (structureSheafModule X) n ⟶
      cohomologyOverField k (j ≫ g) (structureSheafModule Y) n :=
  cohomologyOverFieldMap k g (structureSheafToPushforward j) n ≫
    (cohomologyOverFieldPushforwardIsoOfIsAffineHom k j g (structureSheafModule Y) n).inv

/-- The genus is the dimension of the first cohomology of the structure sheaf over the field. -/
private theorem genus_eq_finrank_cohomologyOverField_structureSheafModule (f : X ⟶ Spec (.of k)) :
    genus f = Module.finrank k (cohomologyOverField k f (structureSheafModule X) 1) := by
  rw [genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq]

/-- **For a closed immersion into a proper scheme of dimension at most one over a field, the map
`H¹(X, 𝒪_X) ⟶ H¹(Y, 𝒪_Y)` is surjective.** The comparison map `𝒪_X ⟶ j_*𝒪_Y` is onto, so its
cokernel has no cohomology, and its kernel has no `H²` because `X` has dimension at most one. -/
theorem surjective_cohomologyOverFieldStructureSheafMap_of_isClosedImmersion [IsProper g]
    (hdim : topologicalKrullDim X ≤ 1) (j : Y ⟶ X) [IsClosedImmersion j] :
    Function.Surjective (cohomologyOverFieldStructureSheafMap k g j 1) := by
  have : IsLocallyNoetherian X :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k g
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k g
  have : NoetherianSpace (X : Type u) := IsNoetherian.noetherianSpace
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isClosedImmersion j
  have : IsClosedImmersion (j ∣_ (⊤ : X.Opens)) :=
    isClosedImmersion_morphismRestrict_of_isClosedImmersion_pullback_snd j ⊤ inferInstance
  have hQ : SheafOfModules.IsCoherent (cokernel (Scheme.Modules.pushforwardUnitHom j)) :=
    isCoherent_cokernel (Scheme.Modules.pushforwardUnitHom j)
  have hgen : ∀ y ∈ genericPointsOne X,
      y ∉ _root_.SheafOfModules.supp (cokernel (Scheme.Modules.pushforwardUnitHom j)) :=
    fun y _ => notMem_supp_cokernel_pushforwardUnitHom_of_mem j ⊤ (Set.mem_univ y)
  have hsupp : topologicalKrullDim
      (_root_.SheafOfModules.supp (cokernel (structureSheafToPushforward j)) : Set X) ≤ 0 :=
    topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hdim
      (cokernel (Scheme.Modules.pushforwardUnitHom j)) hQ hgen
  have hQ' : SheafOfModules.IsCoherent (cokernel (structureSheafToPushforward j)) := hQ
  have hcoker : IsZero
      (cohomologyOverField k g (cokernel (structureSheafToPushforward j)) 1) :=
    @isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k _ X g _
      (cokernel (structureSheafToPushforward j)) hQ' hsupp 1 (by norm_num)
  have hker : IsZero (cohomologyOverField k g (kernel (structureSheafToPushforward j)) 2) :=
    isZero_cohomologyOverField_of_topologicalKrullDim_le k g
      (kernel (structureSheafToPushforward j)) (d := 1) (i := 2) hdim (by norm_num)
  intro y
  obtain ⟨x, hx⟩ := surjective_cohomologyOverFieldMap_structureSheafToPushforward k g j hcoker hker
    ((cohomologyOverFieldPushforwardIsoOfIsAffineHom k j g (structureSheafModule Y) 1).hom y)
  refine ⟨x, ?_⟩
  simp only [cohomologyOverFieldStructureSheafMap, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, hx]
  exact (cohomologyOverFieldPushforwardIsoOfIsAffineHom k j g (structureSheafModule Y)
    1).hom_inv_id_apply y

/-- **The genus does not increase along a closed immersion into a proper scheme of dimension at
most one over a field**, `dim H¹(Y, 𝒪_Y) ≤ dim H¹(X, 𝒪_X)`. -/
theorem genus_comp_le_of_isClosedImmersion [IsProper g] (hdim : topologicalKrullDim X ≤ 1)
    (j : Y ⟶ X) [IsClosedImmersion j] : genus (j ≫ g) ≤ genus g := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g
  have := finiteDimensional_cohomologyOverField_of_isProper k g (structureSheafModule X) 1
  rw [genus_eq_finrank_cohomologyOverField_structureSheafModule,
    genus_eq_finrank_cohomologyOverField_structureSheafModule k g]
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := (cohomologyOverFieldStructureSheafMap k g j 1).hom)
    (surjective_cohomologyOverFieldStructureSheafMap_of_isClosedImmersion k g hdim j)

end AlgebraicGeometry

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- The inclusions into `X_k` of nested closed subschemes of `X` containing the special fibre are
compatible with their inclusion. -/
private theorem inclusion_comp_fibreSubschemeι {T T' : S.X.IdealSheafData}
    (hT : S.specialFiberIdeal ≤ T) (hT' : S.specialFiberIdeal ≤ T') (h : T ≤ T') :
    Scheme.IdealSheafData.inclusion h ≫ S.fibreSubschemeι T hT = S.fibreSubschemeι T' hT' := by
  refine (cancel_mono S.specialFiberι).1 ?_
  rw [Category.assoc, S.fibreSubschemeι_comp, S.fibreSubschemeι_comp,
    Scheme.IdealSheafData.inclusion_subschemeι]

/-- The two structure morphisms of nested closed subschemes of `X` containing the special fibre
are compatible with their inclusion. -/
theorem inclusion_comp_fibreSubschemeToSpec {T T' : S.X.IdealSheafData}
    (hT : S.specialFiberIdeal ≤ T) (hT' : S.specialFiberIdeal ≤ T') (h : T ≤ T') :
    Scheme.IdealSheafData.inclusion h ≫ S.fibreSubschemeToSpec T hT =
      S.fibreSubschemeToSpec T' hT' := by
  show Scheme.IdealSheafData.inclusion h ≫ S.fibreSubschemeι T hT ≫ S.specialFiberToSpec =
    S.fibreSubschemeι T' hT' ≫ S.specialFiberToSpec
  rw [← Category.assoc, S.inclusion_comp_fibreSubschemeι hT hT' h]

/-- The reduced closed subscheme of `X` on the special fibre is reduced. -/
private theorem isReduced_radical_specialFiberIdeal_subscheme :
    IsReduced S.specialFiberIdeal.radical.subscheme :=
  Scheme.IdealSheafData.vanishingIdeal_support (I := S.specialFiberIdeal) ▸
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal S.specialFiberIdeal.support

/-- **A closed subscheme between `X_k` and `(X_k)_red` whose global functions form a field has
`H⁰ = k` when `(X_k)_red` does.** Its global functions map `k`-linearly and, being a field,
injectively into `H⁰((X_k)_red, 𝒪) = k`. -/
theorem finrank_globalSections_eq_one_of_le_radical (T : S.X.IdealSheafData)
    (hT : S.specialFiberIdeal ≤ T) (hTR : T ≤ S.specialFiberIdeal.radical)
    (hred : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.fibreSubschemeToSpec S.specialFiberIdeal.radical
        (Scheme.IdealSheafData.le_radical _)).appTop))
    (hfield : IsField Γ(T.subscheme, ⊤)) :
    letI : Algebra S.k Γ(T.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.fibreSubschemeToSpec T hT).appTop).hom.toAlgebra
    Module.finrank S.k Γ(T.subscheme, ⊤) = 1 := by
  set hR := Scheme.IdealSheafData.le_radical S.specialFiberIdeal
  set R := S.specialFiberIdeal.radical
  let : Algebra S.k Γ(T.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.fibreSubschemeToSpec T hT).appTop).hom.toAlgebra
  let : Algebra S.k Γ(R.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.fibreSubschemeToSpec R hR).appTop).hom.toAlgebra
  have hR1 : Module.finrank S.k Γ(R.subscheme, ⊤) = 1 :=
    have := hred
    finrank_globalSections_eq_one_of_isIso S.k (S.fibreSubschemeToSpec R hR)
  have hcomp := S.inclusion_comp_fibreSubschemeToSpec hT hR hTR
  let f : Γ(T.subscheme, ⊤) →ₐ[S.k] Γ(R.subscheme, ⊤) :=
    { (Scheme.IdealSheafData.inclusion hTR).appTop.hom with
      commutes' := fun c => by
        show _ = ((Scheme.ΓSpecIso (.of S.k)).inv ≫
          (S.fibreSubschemeToSpec R hR).appTop).hom c
        rw [← hcomp, Scheme.Hom.comp_appTop]
        rfl }
  let : Field Γ(T.subscheme, ⊤) := hfield.toField
  have : Nontrivial Γ(R.subscheme, ⊤) :=
    Module.nontrivial_of_finrank_pos (R := S.k) (by omega)
  have hinj : Function.Injective f.toLinearMap := f.toRingHom.injective
  have : FiniteDimensional S.k Γ(R.subscheme, ⊤) := Module.finite_of_finrank_eq_succ hR1
  have : Module.Finite S.k Γ(T.subscheme, ⊤) := Module.Finite.of_injective f.toLinearMap hinj
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hpos : 0 < Module.finrank S.k Γ(T.subscheme, ⊤) := Module.finrank_pos
  omega

/-- **`χ(X_k, ι_*𝒪_T) = 1 - g_T`** for a closed subscheme `T` between `X_k` and `(X_k)_red` whose
global functions form a field, when `H⁰((X_k)_red, 𝒪) = k`. -/
theorem eulerCharacteristic_pushforward_eq_one_sub_genus (T : S.X.IdealSheafData)
    (hT : S.specialFiberIdeal ≤ T) (hTR : T ≤ S.specialFiberIdeal.radical)
    (hred : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.fibreSubschemeToSpec S.specialFiberIdeal.radical
        (Scheme.IdealSheafData.le_radical _)).appTop))
    (hfield : IsField Γ(T.subscheme, ⊤)) :
    eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι T hT)).obj
          (SheafOfModules.unit T.subscheme.ringCatSheaf)) =
      1 - (genus (S.fibreSubschemeToSpec T hT) : ℤ) := by
  have : IsLocallyNoetherian T.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (S.fibreSubschemeι T hT)
  have := Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent T.subscheme
  refine (eulerCharacteristic_pushforward_of_isClosedImmersion S.k (S.fibreSubschemeι T hT)
    S.specialFiberToSpec (SheafOfModules.unit T.subscheme.ringCatSheaf) inferInstance
    inferInstance).trans ?_
  have h := eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus S.k
    (S.fibreSubschemeToSpec T hT) (topologicalKrullDim_fibreSubscheme_le S T hT)
  rw [S.finrank_globalSections_eq_one_of_le_radical T hT hTR hred hfield] at h
  exact_mod_cast h

/-- The genus of the special fibre, read as the closed subscheme of `X` it cuts out, is the genus
of `X_k`. -/
theorem genus_fibreSubschemeToSpec_of_eq (T : S.X.IdealSheafData)
    (hT : S.specialFiberIdeal ≤ T) (hTe : T = S.specialFiberIdeal) :
    genus (S.fibreSubschemeToSpec T hT) = genus S.specialFiberToSpec := by
  subst hTe
  exact genus_comp_iso_eq S.k S.specialFiberToSpec (asIso (S.fibreSubschemeι _ le_rfl))

/-- **The genus is antitone in the ideal** for closed subschemes of `X` containing the special
fibre: `I ≤ J` gives `g_J ≤ g_I`. -/
private theorem genus_fibreSubschemeToSpec_le_of_le {I J : S.X.IdealSheafData}
    (hI : S.specialFiberIdeal ≤ I) (hJ : S.specialFiberIdeal ≤ J) (h : I ≤ J) :
    genus (S.fibreSubschemeToSpec J hJ) ≤ genus (S.fibreSubschemeToSpec I hI) := by
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion h) := by
    have : IsClosedImmersion (Scheme.IdealSheafData.inclusion h ≫ I.subschemeι) := by
      rw [Scheme.IdealSheafData.inclusion_subschemeι]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion _ I.subschemeι
  have h' := genus_comp_le_of_isClosedImmersion S.k (S.fibreSubschemeToSpec I hI)
    (topologicalKrullDim_fibreSubscheme_le S _ hI) (Scheme.IdealSheafData.inclusion h)
  rwa [S.inclusion_comp_fibreSubschemeToSpec hI hJ h] at h'

/-- **The special fibre has at least two components when it is not reduced** and
`gcd(m₁, …, mₙ) = 1`: a single component would have multiplicity one. -/
private theorem one_lt_of_radical_specialFiberIdeal_ne (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (hgcd : Finset.univ.gcd S.specialFiberMultiplicity = 1)
    (hne : S.specialFiberIdeal.radical ≠ S.specialFiberIdeal)
    (i : irreducibleComponents S.specialFiber) : 1 < n := by
  by_contra hn
  have : Subsingleton (irreducibleComponents S.specialFiber) :=
    ⟨fun a b => e.symm.injective (Fin.ext (by omega))⟩
  have hmi : S.specialFiberMultiplicity i = 1 := by
    have : S.specialFiberMultiplicity i ∣ Finset.univ.gcd S.specialFiberMultiplicity :=
      Finset.dvd_gcd fun b _ => by rw [Subsingleton.elim b i]
    rw [hgcd] at this
    exact Nat.dvd_one.mp this
  apply hne
  rw [S.radical_specialFiberIdeal_eq_prod, S.specialFiberIdeal_eq_prod,
    Fintype.prod_subsingleton _ i, Fintype.prod_subsingleton _ i, hmi, pow_one]

/-- **The last step of the chain of [Stacks, Tag 0C68]** when `gcd(m₁, …, mₙ) = 1` and `X_k` is
not reduced: an effective Cartier divisor `D` between `X_k` and `(X_k)_red` and a component `Cᵢ`
with `D + Cᵢ = X_k`, where `H⁰(D, 𝒪)` and `H⁰(X_k, 𝒪)` are fields. -/
private theorem exists_mul_specialFiberComponentIdeal_eq_specialFiberIdeal
    (hgcd : Finset.univ.gcd S.specialFiberMultiplicity = 1)
    (hne : S.specialFiberIdeal.radical ≠ S.specialFiberIdeal) :
    ∃ (D : S.X.IdealSheafData) (i : irreducibleComponents S.specialFiber),
      D * S.specialFiberComponentIdeal i = S.specialFiberIdeal ∧ S.specialFiberIdeal ≤ D ∧
      D ≤ S.specialFiberIdeal.radical ∧ Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      IsField Γ(D.subscheme, ⊤) ∧ IsField Γ(S.specialFiberIdeal.subscheme, ⊤) := by
  -- the chain of Tag 0C68, ending at the special fibre since the gcd is one
  obtain ⟨M, Z, hZ0, hZM, hsteps, hprops⟩ := exists_chain_reducedSpecialFibre S Finset.univ
    S.specialFiberComponentIdeal S.specialFiberMultiplicity
    (fun i _ => S.isEffectiveCartierDivisor_specialFiberComponent i)
    (fun i _ => S.specialFiberMultiplicity_pos i) S.specialFiberIdeal_eq_prod
    S.radical_specialFiberIdeal_eq_prod (fun i => S.specialFiberComponentToSpec i)
    (fun i => inferInstance)
    (fun i => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent i)
    (fun i => inferInstance)
  have hZM' : Z M = S.specialFiberIdeal := by
    rw [hZM, reducedSpecialFibre, hgcd]
    simpa only [Nat.div_one] using S.specialFiberIdeal_eq_prod.symm
  have hmono : ∀ j, j ≤ M → Z j ≤ Z 0 := by
    intro j
    induction j with
    | zero => exact fun _ => le_rfl
    | succ j ih =>
      intro hj
      obtain ⟨-, -, -, hle⟩ := hsteps j (by omega)
      exact hle.trans (ih (by omega))
  obtain ⟨p, rfl⟩ : ∃ p, M = p + 1 := by
    rcases M with _ | p
    · exact absurd (hZ0.symm.trans hZM') hne
    · exact ⟨p, rfl⟩
  obtain ⟨i, -, hstep, hle⟩ := hsteps p (by omega)
  have hDR : Z p ≤ S.specialFiberIdeal.radical := (hmono p (by omega)).trans_eq hZ0
  obtain ⟨hDcart, hDfield, -⟩ := hprops p (by omega)
  obtain ⟨-, hMfield, -⟩ := hprops (p + 1) le_rfl
  exact ⟨Z p, i, hstep.symm.trans hZM', hZM' ▸ hle, hDR, hDcart, hDfield, hZM' ▸ hMfield⟩

/-- **The special fibre is reduced when its ideal is radical.** -/
private theorem isReduced_specialFiber_of_radical_eq
    (heq : S.specialFiberIdeal.radical = S.specialFiberIdeal) : IsReduced S.specialFiber := by
  set hR := Scheme.IdealSheafData.le_radical S.specialFiberIdeal
  have := S.isReduced_radical_specialFiberIdeal_subscheme
  have hiso : IsIso (S.fibreSubschemeι S.specialFiberIdeal.radical hR) := by
    have h := (S.inclusion_comp_fibreSubschemeι le_rfl hR heq.symm.le).symm
    have : IsIso (Scheme.IdealSheafData.inclusion heq.symm.le) :=
      ⟨Scheme.IdealSheafData.inclusion heq.le, by
        rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id],
        by rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id]⟩
    rw [h]
    infer_instance
  exact isReduced_of_isOpenImmersion (inv (S.fibreSubschemeι S.specialFiberIdeal.radical hR))

variable [DecidableEq (irreducibleComponents S.specialFiber)]

/-- **The coefficients of a divisor `D` with `D + Cᵢ = X_k`** are the multiplicities of `X_k`,
less one at `Cᵢ`. -/
private theorem specialFiberDivisorCoeff_add_single_eq_multiplicity (D : S.X.IdealSheafData)
    (i : irreducibleComponents S.specialFiber)
    (hD : D = ∏ W, S.specialFiberComponentIdeal W ^ S.specialFiberDivisorCoeff D W)
    (hDi : D * S.specialFiberComponentIdeal i = S.specialFiberIdeal) :
    S.specialFiberDivisorCoeff D + Pi.single i 1 = S.specialFiberMultiplicity := by
  have hsum : ∏ W, S.specialFiberComponentIdeal W ^
        (S.specialFiberDivisorCoeff D + Pi.single i 1 :
          irreducibleComponents S.specialFiber → ℕ) W =
      (∏ W, S.specialFiberComponentIdeal W ^ S.specialFiberDivisorCoeff D W) *
        S.specialFiberComponentIdeal i := by
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
      (fun W _ hW => by rw [Pi.single_eq_of_ne hW, pow_zero]), Pi.single_eq_same, pow_one]
  have hprodeq : ∏ W, S.specialFiberComponentIdeal W ^
        (S.specialFiberDivisorCoeff D + Pi.single i 1 :
          irreducibleComponents S.specialFiber → ℕ) W =
      ∏ W, S.specialFiberComponentIdeal W ^ S.specialFiberMultiplicity W := by
    rw [hsum, ← hD, hDi, S.specialFiberIdeal_eq_prod]
  funext W
  have h1 := S.specialFiberDivisorCoeff_prod (S.specialFiberDivisorCoeff D + Pi.single i 1) W
  have h2 := S.specialFiberDivisorCoeff_prod S.specialFiberMultiplicity W
  rw [hprodeq] at h1
  exact h1.symm.trans h2

/-- **`Σ_Y c_Y (Cᵢ · C_Y) = -(Cᵢ · Cᵢ)`** for coefficients `c` with `c + Cᵢ = X_k`, since
`(X_k · Cᵢ) = 0`. -/
private theorem sum_coeff_mul_intersectionMatrix_eq_neg
    (c : irreducibleComponents S.specialFiber → ℕ)
    (i : irreducibleComponents S.specialFiber)
    (hcm : c + Pi.single i 1 = S.specialFiberMultiplicity) :
    ∑ Y, (c Y : ℤ) * S.specialFiberIntersectionMatrix i Y =
      -S.specialFiberIntersectionMatrix i i := by
  have hker : ∑ Y, (S.specialFiberMultiplicity Y : ℤ) *
      S.specialFiberIntersectionMatrix i Y = 0 :=
    sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion S
      (fun W => S.specialFiberComponentIdeal W) (fun W => S.specialFiberComponentToSpec W)
      (fun W => S.isProper_specialFiberComponentToSpec W)
      (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W)
      S.specialFiberIntersectionMatrix S.specialFiberMultiplicity
      (fun W => S.isEffectiveCartierDivisor_specialFiberComponent W)
      (fun c W => S.specialFiberDivisorDegree_eq_sum W c) S.specialFiberIdeal_eq_prod i
  have hcY : ∀ Y, (c Y : ℤ) = (S.specialFiberMultiplicity Y : ℤ) - if Y = i then 1 else 0 := by
    intro Y
    have h := congrFun hcm Y
    simp only [Pi.add_apply, Pi.single_apply] at h
    split_ifs at h ⊢ <;> omega
  simp only [hcY, sub_mul, Finset.sum_sub_distrib, hker, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **`(Cᵢ · Cᵢ) + wᵢ(1 - gᵢ) < 0`** when the associated numerical type is minimal and has at
least two components: `(Cᵢ · Cᵢ)` is negative, divisible by `wᵢ`, and not `-wᵢ` when `gᵢ = 0`. -/
private theorem intersectionMatrix_self_add_weight_mul_lt_zero (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (hmin : (S.associatedNumericalType n e).IsMinimal) (htwo : 1 < n)
    (i : irreducibleComponents S.specialFiber) :
    S.specialFiberIntersectionMatrix i i +
      (S.specialFiberComponentWeight i : ℤ) * (1 - (S.specialFiberComponentGenus i : ℤ)) < 0 := by
  set T := S.associatedNumericalType n e
  obtain ⟨a, rfl⟩ := e.surjective i
  have hneg : S.specialFiberIntersectionMatrix (e a) (e a) < 0 :=
    T.intersection_self_neg_of_one_lt_componentCount htwo a
  have hdvd : (S.specialFiberComponentWeight (e a) : ℤ) ∣
      S.specialFiberIntersectionMatrix (e a) (e a) := T.weight_dvd_intersection a a
  have hnotm1 : ¬ ((S.specialFiberComponentGenus (e a) : ℤ) = 0 ∧
      S.specialFiberIntersectionMatrix (e a) (e a) = -(S.specialFiberComponentWeight (e a) : ℤ)) :=
    fun h => hmin ⟨a, h⟩
  generalize e a = i at hneg hdvd hnotm1
  have hw := S.specialFiberComponentWeight_pos i
  obtain ⟨q, hq⟩ := hdvd
  rcases Nat.eq_zero_or_pos (S.specialFiberComponentGenus i) with hg0 | hg0
  · have hne1 : S.specialFiberIntersectionMatrix i i ≠ -(S.specialFiberComponentWeight i : ℤ) :=
      fun h => hnotm1 ⟨by exact_mod_cast hg0, h⟩
    rw [hg0]
    rw [hq] at hneg hne1 ⊢
    have hq1 : q < 0 := by
      by_contra hq0
      push Not at hq0
      have : 0 ≤ (S.specialFiberComponentWeight i : ℤ) * q := by positivity
      omega
    have hq2 : q ≠ -1 := fun h => hne1 (by rw [h, mul_neg_one])
    have hq3 : q ≤ -2 := by omega
    push_cast
    nlinarith
  · have : (S.specialFiberComponentWeight i : ℤ) * (1 - (S.specialFiberComponentGenus i : ℤ))
        ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      have : (1 : ℤ) ≤ S.specialFiberComponentGenus i := by exact_mod_cast hg0
      linarith
    linarith

/-- **The genus of `X_k` exceeds that of `(X_k)_red` when `X_k` is not reduced**, for a model with
minimal associated numerical type, `gcd(m₁, …, mₙ) = 1` and `H⁰((X_k)_red, 𝒪) = k`; here
`(X_k)_red` is the reduced closed subscheme of `X` on the special fibre. This is the dimension
count of [Stacks, Tag 0CE9]; see the module docstring. -/
theorem genus_radical_lt_of_isMinimal_associatedNumericalType
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (hmin : (S.associatedNumericalType n e).IsMinimal)
    (hgcd : Finset.univ.gcd S.specialFiberMultiplicity = 1)
    (hred : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.fibreSubschemeToSpec S.specialFiberIdeal.radical
        (Scheme.IdealSheafData.le_radical _)).appTop))
    (hne : S.specialFiberIdeal.radical ≠ S.specialFiberIdeal) :
    genus (S.fibreSubschemeToSpec S.specialFiberIdeal.radical
        (Scheme.IdealSheafData.le_radical _)) < genus S.specialFiberToSpec := by
  classical
  obtain ⟨D, i, hstep, hkD, hDR, hDcart, hDfield, hMfield⟩ :=
    S.exists_mul_specialFiberComponentIdeal_eq_specialFiberIdeal hgcd hne
  set hR := Scheme.IdealSheafData.le_radical S.specialFiberIdeal
  -- the divisor `D` as a sum of components, and `D + Cᵢ = X_k`
  set c := S.specialFiberDivisorCoeff D
  have hDprod : D = ∏ W, S.specialFiberComponentIdeal W ^ c W :=
    S.eq_prod_specialFiberDivisorCoeff D hDcart hkD
  have hcm : c + Pi.single i 1 = S.specialFiberMultiplicity :=
    S.specialFiberDivisorCoeff_add_single_eq_multiplicity D i hDprod hstep
  -- the recursion of Tag 0CA2 at the last step
  have hrec := S.specialFiberDivisorEulerChar_add_single c i hcm.le
  have hkc : S.specialFiberIdeal ≤ ∏ W, S.specialFiberComponentIdeal W ^ c W := hDprod ▸ hkD
  have hkm : S.specialFiberIdeal ≤
      ∏ W, S.specialFiberComponentIdeal W ^ S.specialFiberMultiplicity W :=
    S.specialFiberIdeal_eq_prod.le
  rw [hcm, specialFiberDivisorEulerChar, specialFiberDivisorEulerChar, dite_eq_left hkm,
    dite_eq_left hkc,
    S.eulerCharacteristic_pushforward_eq_one_sub_genus _ hkm
      (S.specialFiberIdeal_eq_prod ▸ hR)
      hred (S.specialFiberIdeal_eq_prod ▸ hMfield),
    S.eulerCharacteristic_pushforward_eq_one_sub_genus _ hkc (hDprod ▸ hDR) hred
      (hDprod ▸ hDfield),
    S.genus_fibreSubschemeToSpec_of_eq _ hkm S.specialFiberIdeal_eq_prod.symm,
    S.eulerCharacteristic_specialFiberComponent_eq i,
    S.sum_coeff_mul_intersectionMatrix_eq_neg c i hcm] at hrec
  have hkey := S.intersectionMatrix_self_add_weight_mul_lt_zero n e hmin
    (S.one_lt_of_radical_specialFiberIdeal_ne n e hgcd hne i) i
  -- dimensions: `g(X_k) > g(D) ≥ g((X_k)_red)`
  have hgt : genus (S.fibreSubschemeToSpec (∏ W, S.specialFiberComponentIdeal W ^ c W) hkc) <
      genus S.specialFiberToSpec := by
    zify
    linarith
  exact (S.genus_fibreSubschemeToSpec_le_of_le hkc hR (hDprod ▸ hDR)).trans_lt hgt

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **The reduction of the special fibre is the reduced closed subscheme of `X` on it.** The
closed immersion `(X_k)_red ⟶ X_k` of the reduced closed subscheme of `X` supported on `X_k` is
surjective with reduced source, so its kernel is the nilradical of `X_k`, which is the kernel of
`X_k.reductionι`. -/
theorem exists_iso_reduction_specialFiber :
    ∃ φ : S.specialFiberIdeal.radical.subscheme ≅ S.specialFiber.reduction,
      φ.hom ≫ S.specialFiber.reductionι =
        S.fibreSubschemeι S.specialFiberIdeal.radical (Scheme.IdealSheafData.le_radical _) := by
  set hR := Scheme.IdealSheafData.le_radical S.specialFiberIdeal
  set j := S.fibreSubschemeι S.specialFiberIdeal.radical hR
  have := S.isReduced_radical_specialFiberIdeal_subscheme
  have hrange : Set.range j.base = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨z, hz⟩ : S.specialFiberι.base y ∈
        Set.range S.specialFiberIdeal.radical.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_radical,
        S.coe_support_specialFiberIdeal]
      exact ⟨y, rfl⟩
    refine ⟨z, S.specialFiberι.isClosedEmbedding.injective ?_⟩
    rw [← hz, ← S.fibreSubschemeι_comp S.specialFiberIdeal.radical hR]
    rfl
  have hker : j.ker = S.specialFiber.reductionι.ker := by
    have hsupp : j.ker.support = ⊤ :=
      eq_top_iff.2 fun y _ => j.range_subset_ker_support (hrange ▸ Set.mem_univ y)
    rw [ker_eq_vanishingIdeal_of_reduced_closed_immersion j, hsupp,
      Scheme.IdealSheafData.vanishingIdeal_top]
    exact (Scheme.IdealSheafData.ker_subschemeι _).symm
  let i := IsClosedImmersion.lift S.specialFiber.reductionι j hker.ge
  have hi : i ≫ S.specialFiber.reductionι = j := IsClosedImmersion.lift_fac _ _ _
  have : IsIso i := IsClosedImmersion.isIso_of_ker_eq j S.specialFiber.reductionι i hi hker
  exact ⟨asIso i, hi⟩

/-- **Stacks Project, Tag 0CE9, for a model with minimal associated numerical type.** In the
situation of [Stacks, Tag 0C61], suppose the numerical type associated to `X` is minimal,
`gcd(m₁, …, mₙ) = 1` and `H⁰((X_k)_red, 𝒪) = k`. Then the map
`H¹(X_k, 𝒪_{X_k}) ⟶ H¹((X_k)_red, 𝒪_{(X_k)_red})` induced by the reduction `(X_k)_red ⟶ X_k` is
surjective, and it is not injective as soon as `(X_k)_red ≠ X_k`, that is as soon as `X_k` is not
reduced. -/
theorem surjective_and_not_injective_of_isMinimal_associatedNumericalType
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (hmin : (S.associatedNumericalType n e).IsMinimal)
    (hgcd : Finset.univ.gcd S.specialFiberMultiplicity = 1)
    (hred : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.specialFiber.reductionι ≫ S.specialFiberToSpec).appTop)) :
    Function.Surjective (cohomologyOverFieldStructureSheafMap S.k S.specialFiberToSpec
        S.specialFiber.reductionι 1) ∧
      (¬ IsReduced S.specialFiber →
        ¬ Function.Injective (cohomologyOverFieldStructureSheafMap S.k S.specialFiberToSpec
          S.specialFiber.reductionι 1)) := by
  set hR := Scheme.IdealSheafData.le_radical S.specialFiberIdeal
  have hdimk : topologicalKrullDim S.specialFiber ≤ 1 :=
    (S.toRegularModelSituation.topologicalKrullDim_specialFiber S.nonempty_specialFiber).le
  have hsurj := surjective_cohomologyOverFieldStructureSheafMap_of_isClosedImmersion S.k
    S.specialFiberToSpec hdimk S.specialFiber.reductionι
  refine ⟨hsurj, fun hnr hinj => ?_⟩
  obtain ⟨φ, hφ⟩ := S.exists_iso_reduction_specialFiber
  have hcomp : φ.hom ≫ S.specialFiber.reductionι ≫ S.specialFiberToSpec =
      S.fibreSubschemeToSpec S.specialFiberIdeal.radical hR := by
    rw [← Category.assoc, hφ]
    rfl
  -- the hypothesis `H⁰ = k` on the radical subscheme
  have hred' : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.fibreSubschemeToSpec S.specialFiberIdeal.radical hR).appTop) := by
    rw [← hcomp, Scheme.Hom.comp_appTop, ← Category.assoc]
    have : IsIso φ.hom.appTop :=
      ⟨φ.inv.appTop, by rw [← Scheme.Hom.comp_appTop, φ.inv_hom_id]; simp,
        by rw [← Scheme.Hom.comp_appTop, φ.hom_inv_id]; simp⟩
    infer_instance
  -- the radical subscheme is not the special fibre
  have hne : S.specialFiberIdeal.radical ≠ S.specialFiberIdeal := fun heq =>
    hnr (S.isReduced_specialFiber_of_radical_eq heq)
  have hlt := S.genus_radical_lt_of_isMinimal_associatedNumericalType n e hmin hgcd hred' hne
  have hgeq : genus (S.specialFiber.reductionι ≫ S.specialFiberToSpec) =
      genus (S.fibreSubschemeToSpec S.specialFiberIdeal.radical hR) := by
    rw [← hcomp]
    exact (genus_comp_iso_eq S.k _ φ).symm
  -- a bijection would equate the two dimensions
  have : (SheafOfModules.unit S.specialFiber.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k S.specialFiberToSpec
  have heq := (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq
  rw [← genus_eq_finrank_cohomologyOverField_structureSheafModule,
    ← genus_eq_finrank_cohomologyOverField_structureSheafModule] at heq
  omega

end RegularProperModelSituation

end Stacks.Models

end

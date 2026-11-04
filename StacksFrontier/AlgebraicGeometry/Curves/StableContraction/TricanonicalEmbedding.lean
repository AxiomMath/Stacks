module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DegreeBound
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafRank
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import
  StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.BaseFieldExtension
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# The tricanonical embedding of a curve with ample dualizing sheaf

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, of genus
`g ≥ 2`, with at-worst-nodal singularities and ample dualizing sheaf `ω_X`. [Stacks, Tag 0E8X]
asserts that `ω_X^{⊗ 3}` is very ample and `H¹(X, ω_X^{⊗ 3}) = 0`. The proof checks the criterion
of [Stacks, Tag 0E3E] on every reduced connected subcurve `Y ⊆ X`: for a zero-dimensional
`Z ⊆ X` of degree at most two,

  `3 deg(ω_X|_Y) > -2 χ(Y, 𝒪_Y) + deg(Z ∩ Y)`.

This file collects the inputs of that check which hold on any proper curve, and the transport of
the hypothesis of [Stacks, Tag 0E8T] to a base change over an algebraic closure, where the
degree-two subschemes are checked.

## Main results

* `AlgebraicGeometry.surjectsOnDegreeTwo_of_iso`,
  `AlgebraicGeometry.surjectsOnDegreeTwo_pullback_of_isIso` and
  `AlgebraicGeometry.surjectsOnDegreeTwo_pullback_of_isPullback`: the hypothesis of
  [Stacks, Tag 0E8T] is invariant under isomorphisms, so on a base change it may be checked on the
  chosen fibre product.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.isIso_idealTwistι_top`: the twist of `ℒ` by the
  ideal of the empty subscheme `⊤` is `ℒ`.
* `AlgebraicGeometry.finrank_globalSections_sup_le`: `deg(Z ∩ Y) ≤ deg(Z)` for a
  zero-dimensional `Z`.
* `AlgebraicGeometry.one_sub_finrank_le_finsum_finrank_unit`: `χ(Y, 𝒪_Y) ≥ 1 - h¹(Y, 𝒪_Y)` for a
  nonempty proper curve `Y`.
* `AlgebraicGeometry.finsum_finrank_unit_subscheme_bot`: `χ(X, 𝒪_X) = 1 - g`, read on the closed
  subscheme `⊥`, which is `X` itself.
* `AlgebraicGeometry.neg_two_mul_finsum_add_finrank_lt_invertibleCurveDegree_bot`: the inequality
  for `Y = X`, from `deg(ω_X) = 2g - 2` and `g ≥ 2`.
* `AlgebraicGeometry.neg_two_mul_finsum_add_finrank_lt_invertibleCurveDegree`: the inequality on
  a subcurve `Y` on which `ω_X` has positive degree at least `h¹(Y, 𝒪_Y)`.
* `AlgebraicGeometry.invertibleCurveDegree_subscheme_pos_of_forall_isIntegral`: an invertible
  module of positive degree on every integral one-dimensional closed subscheme has positive
  degree on every reduced one-dimensional closed subscheme ([Stacks, Tag 0AYW]).

## References

* [Stacks Project, Tag 0E8X](https://stacks.math.columbia.edu/tag/0E8X)
* [Stacks Project, Tag 0E3E](https://stacks.math.columbia.edu/tag/0E3E)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-! ### The hypothesis of Tag 0E8T under isomorphisms -/

section SurjectsOnDegreeTwo

variable {X X' : Scheme.{u}}

/-- **The hypothesis of [Stacks, Tag 0E8T] only depends on the isomorphism class of the
module.** Pulling back global sections is natural in the module. -/
theorem surjectsOnDegreeTwo_of_iso {p : X ⟶ Spec (.of k)} {L L' : X.Modules} (θ : L ≅ L')
    (h : SurjectsOnDegreeTwo p L) : SurjectsOnDegreeTwo p L' := by
  intro Z r hr hdeg σ
  let θr := (Scheme.Modules.pullback r).mapIso θ
  obtain ⟨s, hs⟩ := h Z r hr hdeg (θr.inv.val.app (op ⊤) σ)
  refine ⟨θ.hom.val.app (op ⊤) s, ?_⟩
  rw [← pullbackSectionTop_naturality r θ.hom s, hs]
  show (θr.inv ≫ θr.hom).val.app (op ⊤) σ = σ
  rw [θr.inv_hom_id]
  rfl

/-- **The hypothesis of [Stacks, Tag 0E8T] transports along an isomorphism of schemes.** A closed
subscheme `r : Z ⟶ X'` of degree two gives the closed subscheme `r ≫ e` of `X`, and pulling back
along `r ≫ e` is pulling back along `e` and then along `r`. -/
theorem surjectsOnDegreeTwo_pullback_of_isIso (e : X' ⟶ X) [IsIso e] {p : X ⟶ Spec (.of k)}
    {L : X.Modules} (h : SurjectsOnDegreeTwo p L) :
    SurjectsOnDegreeTwo (e ≫ p) ((Scheme.Modules.pullback e).obj L) := by
  intro Z r hr hdeg σ
  have := hr
  have hdeg' : IsZeroDimensionalOfDegree ((r ≫ e) ≫ p) 2 := by rwa [Category.assoc]
  obtain ⟨s, hs⟩ := h Z (r ≫ e) inferInstance hdeg'
    (((Scheme.Modules.pullbackComp r e).hom.app L).val.app (op ⊤) σ)
  refine ⟨pullbackSectionTop e L s, ?_⟩
  rw [← pullbackSectionTop_comp r e L s, hs]
  show ((Scheme.Modules.pullbackComp r e).hom.app L ≫
    (Scheme.Modules.pullbackComp r e).inv.app L).val.app (op ⊤) σ = σ
  rw [Iso.hom_inv_id_app]
  rfl

/-- **The hypothesis of [Stacks, Tag 0E8T] on a base change may be checked on the chosen fibre
product.** For a pullback square `X' ⟶ X`, `X' ⟶ Spec K` of `p : X ⟶ Spec k` along
`φ : Spec K ⟶ Spec k`, the comparison `X' ≅ X ×_{Spec k} T` carries the hypothesis for `ℒ` pulled
back to the chosen fibre product over to the pullback of `ℒ` to `X'`. -/
theorem surjectsOnDegreeTwo_pullback_of_isPullback {K : Type u} [Field K]
    {p : X ⟶ Spec (.of k)} {φ : Spec (.of K) ⟶ Spec (.of k)} {g' : X' ⟶ X}
    {f' : X' ⟶ Spec (.of K)} (h : IsPullback g' f' p φ) (L : X.Modules)
    (hc : SurjectsOnDegreeTwo (pullback.snd p φ)
      ((Scheme.Modules.pullback (pullback.fst p φ)).obj L)) :
    SurjectsOnDegreeTwo f' ((Scheme.Modules.pullback g').obj L) := by
  have h1 := surjectsOnDegreeTwo_pullback_of_isIso h.isoPullback.hom hc
  rw [h.isoPullback_hom_snd] at h1
  exact surjectsOnDegreeTwo_of_iso ((Scheme.Modules.pullbackComp h.isoPullback.hom
    (pullback.fst p φ)).app L ≪≫ (Scheme.Modules.pullbackCongr h.isoPullback_hom_fst).app L) h1

end SurjectsOnDegreeTwo

namespace CohenMacaulayCurveSituation

/-- **The ideal of the empty subscheme is the structure sheaf**, so the twist of `ℒ` by it is `ℒ`:
`ℐ_⊤ ℒ ⟶ ℒ` is an isomorphism. The pushforward of the structure sheaf of the empty subscheme is
zero, so `𝒪_X ⟶ i_* 𝒪_∅` is zero and its kernel is all of `𝒪_X`. -/
theorem isIso_idealTwistι_top (S : CohenMacaulayCurveSituation.{u}) (L : S.X.Modules) :
    IsIso (S.idealTwistι ⊤ L) := by
  have : IsEmpty (⊤ : S.X.IdealSheafData).subscheme := by
    refine ⟨fun y => ?_⟩
    have hy : (⊤ : S.X.IdealSheafData).subschemeι y ∈
        Set.range (⊤ : S.X.IdealSheafData).subschemeι := ⟨y, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_top] at hy
  have hT : IsZero ((RingedSpaceModuleAdjunction.modulePushforward
      (⊤ : S.X.IdealSheafData).subschemeι.toLRSHom.toShHom).obj
        (SheafOfModules.unit (structureSheafRing
          (⊤ : S.X.IdealSheafData).subscheme.toRingedSpace))) :=
    Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections _ fun V =>
      inferInstanceAs (Subsingleton Γ((⊤ : S.X.IdealSheafData).subscheme, _))
  have h0 : Stacks.IdealSheafSequence.divisorQuotientMap (⊤ : S.X.IdealSheafData) = 0 :=
    hT.eq_of_tgt _ _
  have hI : IsIso (Stacks.IdealSheafSequence.divisorIdealMap (⊤ : S.X.IdealSheafData)) :=
    kernel.ι_of_zero h0
  exact Iso.isIso_hom ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
      (forget₂ CommRingCat RingCat) S.X.ringCatSheaf.2⟩).obj L)).mapIso
    (@asIso _ _ _ _ _ hI) ≪≫
    SheafOfModules.tensorSheafUnitRightIso S.X.toRingedSpace L)

end CohenMacaulayCurveSituation

/-- **The intersection with a zero-dimensional subscheme has at most its degree.** For closed
subschemes `Z, Y` of a proper `k`-scheme `X` with `Z` zero-dimensional, the scheme-theoretic
intersection `Z ∩ Y` (the closed subscheme of `Z ⊔ Y`) satisfies
`dim_k Γ(Z ∩ Y, 𝒪) ≤ dim_k Γ(Z, 𝒪)`: `Z` is affine and `Z ∩ Y ⊆ Z` is closed, so the restriction
of functions is surjective. -/
theorem finrank_globalSections_sup_le {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (Z Y : X.IdealSheafData) (hZ : topologicalKrullDim Z.subscheme ≤ 0) :
    letI : Algebra k Γ((Z ⊔ Y).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ Y).subschemeι ≫ f).appTop).hom.toAlgebra
    letI : Algebra k Γ(Z.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank k Γ((Z ⊔ Y).subscheme, ⊤) ≤ Module.finrank k Γ(Z.subscheme, ⊤) := by
  let : Algebra k Γ((Z ⊔ Y).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ Y).subschemeι ≫ f).appTop).hom.toAlgebra
  let : Algebra k Γ(Z.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ f).appTop).hom.toAlgebra
  rcases isEmpty_or_nonempty Z.subscheme with hE | hN
  · have : Subsingleton Γ((Z ⊔ Y).subscheme, ⊤) := by
      have : IsEmpty (Z ⊔ Y).subscheme :=
        ⟨fun y => hE.false (Scheme.IdealSheafData.inclusion le_sup_left y)⟩
      infer_instance
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  have hZ0 : topologicalKrullDim Z.subscheme = 0 := by
    refine le_antisymm hZ ?_
    obtain ⟨z⟩ := hN
    have : Nonempty (TopologicalSpace.IrreducibleCloseds Z.subscheme) :=
      ⟨⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  have : IsAffine Z.subscheme :=
    isAffine_of_finiteType_of_dimension_zero k (Z.subschemeι ≫ f) hZ0
  let j := Scheme.IdealSheafData.inclusion (le_sup_left : Z ≤ Z ⊔ Y)
  have hfin : Module.Finite k Γ(Z.subscheme, ⊤) := by
    have := forall_finiteDimensional_cohomologyOverField_unit k (Z.subschemeι ≫ f) 0
    exact Module.Finite.equiv (cohomologyOverFieldZeroIsoSections k (Z.subschemeι ≫ f)
      (SheafOfModules.unit Z.subscheme.ringCatSheaf)).toLinearEquiv
  have hcomp : ((Z ⊔ Y).subschemeι ≫ f).appTop = (Z.subschemeι ≫ f).appTop ≫ j.appTop := by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι (le_sup_left : Z ≤ Z ⊔ Y), Category.assoc]
    rfl
  let φ : Γ(Z.subscheme, ⊤) →ₗ[k] Γ((Z ⊔ Y).subscheme, ⊤) :=
    { toFun := j.appTop.hom
      map_add' := map_add _
      map_smul' := fun c a => by
        simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
        congr 1
        show (j.appTop).hom (((Scheme.ΓSpecIso (.of k)).inv ≫
          (Z.subschemeι ≫ f).appTop).hom c) =
          ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ Y).subschemeι ≫ f).appTop).hom c
        rw [hcomp]
        rfl }
  have hle := LinearMap.finrank_range_le φ
  rwa [LinearMap.range_eq_top.mpr (IsClosedImmersion.isAffine_surjective_of_isAffine j).2,
    finrank_top] at hle

/-- **The Euler characteristic of the structure sheaf of a nonempty proper curve is at least
`1 - h¹`.** On a nonempty proper scheme of dimension at most one over `k`,
`χ(Y, 𝒪_Y) = h⁰(Y, 𝒪_Y) - h¹(Y, 𝒪_Y)` (cohomology vanishes above the dimension) and
`h⁰(Y, 𝒪_Y) ≥ 1`. -/
theorem one_sub_finrank_le_finsum_finrank_unit {Y : Scheme.{u}} [Nonempty Y]
    (g : Y ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim Y ≤ 1) :
    1 - (Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Y.ringCatSheaf) 1) : ℤ) ≤
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k g (SheafOfModules.unit Y.ringCatSheaf) n) : ℤ) := by
  have hs := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k g
    (SheafOfModules.unit Y.ringCatSheaf)
    (fun m hm => isZero_cohomologyOverField_of_topologicalKrullDim_le k g _ (d := 1)
      (by exact_mod_cast hdim) (by omega))
  rw [hs]
  have h0 : 1 ≤ Module.finrank k
      (cohomologyOverField k g (SheafOfModules.unit Y.ringCatSheaf) 0) := by
    let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k g]
    have : FiniteDimensional k Γ(Y, ⊤) := by
      have := forall_finiteDimensional_cohomologyOverField_unit k g 0
      exact Module.Finite.equiv (cohomologyOverFieldZeroIsoSections k g
        (SheafOfModules.unit Y.ringCatSheaf)).toLinearEquiv
    have : Nonempty ((⊤ : Y.Opens) : Type u) := ⟨⟨Classical.choice ‹Nonempty Y›, trivial⟩⟩
    have : Nontrivial Γ(Y, ⊤) := Scheme.component_nontrivial Y ⊤
    exact Module.finrank_pos
  omega

/-- **`χ(X, 𝒪_X) = 1 - g`, read on the closed subscheme `⊥`.** The closed immersion of `⊥` is an
isomorphism, so its cohomology is that of `X`, and on a proper curve with `H⁰(X, 𝒪_X) = k` the
Euler characteristic of the structure sheaf is `1 - g`. -/
theorem finsum_finrank_unit_subscheme_bot {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1) :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        ((⊥ : X.IdealSheafData).subschemeι ≫ f)
        (SheafOfModules.unit (⊥ : X.IdealSheafData).subscheme.ringCatSheaf) n) : ℤ) =
      1 - (genus f : ℤ) := by
  let e := (⊥ : X.IdealSheafData).subschemeι
  have hs : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by simp
  have hsq : IsPullback e (e ≫ f) f (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [hs]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hterm (n : ℕ) : Module.finrank k (cohomologyOverField k (e ≫ f)
      (SheafOfModules.unit (⊥ : X.IdealSheafData).subscheme.ringCatSheaf) n) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) :=
    (finrank_cohomologyOverField_eq_of_iso k (e ≫ f)
        (Scheme.Modules.pullbackUnitIso e) n).symm.trans
      (finrank_cohomologyOverField_baseChange_field k k e (e ≫ f) f hsq _ n)
  have hsum := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f
    (SheafOfModules.unit X.ringCatSheaf) (isZero_cohomologyOverField_two_le k f hdim _)
  refine (finsum_congr fun n => by rw [hterm n]).trans (hsum.trans ?_)
  rw [finrank_cohomologyOverField_unit_zero_eq_one f,
    finrank_cohomologyOverField_one_unit_eq_genus k f]
  simp

/-- **The inequality of [Stacks, Tag 0E3E] for `ω_X^{⊗ 3}` on `Y = X`.** Let `X` be a proper
curve over `k` with `H⁰(X, 𝒪_X) = k` and genus `g ≥ 2` whose dualizing sheaf `ω_X` is invertible,
and let `Z ⊆ X` be zero-dimensional of degree at most two. Then on the closed subscheme `⊥`,
which is `X`,

  `-2 χ(X, 𝒪_X) + deg(Z ∩ X) < deg(ω_X^{⊗ 3})`:

the left side is `2g - 2 + deg(Z) ≤ 2g` and the right side is `3(2g - 2)` (Riemann-Roch,
[Stacks, Tag 0BS6]). -/
theorem neg_two_mul_finsum_add_finrank_lt_invertibleCurveDegree_bot {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) (hg : 2 ≤ genus f)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f)]
    (Z : X.IdealSheafData) (_hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (hZdeg : letI : Algebra k Γ(Z.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(Z.subscheme, ⊤) ≤ 2)
    (hbot : topologicalKrullDim (⊥ : X.IdealSheafData).subscheme ≤ 1) :
    letI := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
      X.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField f) 3
    letI : SheafOfModules.IsInvertible (⊥ : X.IdealSheafData).subscheme.presheaf
        (⊥ : X.IdealSheafData).subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback (⊥ : X.IdealSheafData).subschemeι).obj
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
            (Stacks.Duality.dualizingSheafOverField f) 3)) :=
      Stacks.Modules.isInvertible_pullback _ _
    letI : Algebra k Γ((Z ⊔ ⊥).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ ⊥).subschemeι ≫ f).appTop).hom.toAlgebra
    (-2 : ℤ) * (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        ((⊥ : X.IdealSheafData).subschemeι ≫ f)
        (SheafOfModules.unit (⊥ : X.IdealSheafData).subscheme.ringCatSheaf) n) : ℤ)) +
        (Module.finrank k Γ((Z ⊔ ⊥).subscheme, ⊤) : ℤ) <
      invertibleCurveDegree k ((⊥ : X.IdealSheafData).subschemeι ≫ f) hbot
        ((Scheme.Modules.pullback (⊥ : X.IdealSheafData).subschemeι).obj
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
            (Stacks.Duality.dualizingSheafOverField f) 3)) := by
  let : SheafOfModules.IsInvertible (⊥ : X.IdealSheafData).subscheme.presheaf
      (⊥ : X.IdealSheafData).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (⊥ : X.IdealSheafData).subschemeι).obj
        (Stacks.Duality.dualizingSheafOverField f)) :=
    Stacks.Modules.isInvertible_pullback _ _
  have hdeg := invertibleCurveDegree_pullback_tensorPower ((⊥ : X.IdealSheafData).subschemeι)
    ((⊥ : X.IdealSheafData).subschemeι ≫ f) hbot (Stacks.Duality.dualizingSheafOverField f) 3
    (hP := Stacks.Modules.isInvertible_pullback _ _)
  have hω := invertibleCurveDegree_pullback_of_isIso (k := k) (⊥ : X.IdealSheafData).subschemeι f
    hbot hdim (Stacks.Duality.dualizingSheafOverField f)
  have h2g := invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k f hdim
  have hχ := finsum_finrank_unit_subscheme_bot f hdim
  have he : (let : Algebra k Γ((Z ⊔ ⊥).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ ⊥).subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ((Z ⊔ ⊥).subscheme, ⊤)) ≤ 2 := by
    rwa [sup_bot_eq Z]
  have hg' : (2 : ℤ) ≤ genus f := by exact_mod_cast hg
  let : Algebra k Γ((Z ⊔ ⊥).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ ⊥).subschemeι ≫ f).appTop).hom.toAlgebra
  have he' : (Module.finrank k Γ((Z ⊔ ⊥).subscheme, ⊤) : ℤ) ≤ 2 := by exact_mod_cast he
  let := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
    X.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField f) 3
  let : SheafOfModules.IsInvertible (⊥ : X.IdealSheafData).subscheme.presheaf
      (⊥ : X.IdealSheafData).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (⊥ : X.IdealSheafData).subschemeι).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
          (Stacks.Duality.dualizingSheafOverField f) 3)) :=
    Stacks.Modules.isInvertible_pullback _ _
  have hdeg3 : invertibleCurveDegree k ((⊥ : X.IdealSheafData).subschemeι ≫ f) hbot
      ((Scheme.Modules.pullback (⊥ : X.IdealSheafData).subschemeι).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
          (Stacks.Duality.dualizingSheafOverField f) 3)) = 3 * (2 * (genus f : ℤ) - 2) := by
    rwa [← h2g, ← hω]
  rw [hdeg3, hχ]
  linarith

/-- **The inequality of [Stacks, Tag 0E3E] for `ℒ^{⊗ 3}` on a subcurve.** Let `X` be proper over
`k`, `ℒ` invertible on `X`, `Y ⊆ X` a nonempty closed subscheme of dimension at most one and
`Z ⊆ X` zero-dimensional of degree at most two. If `0 < deg(ℒ|_Y)` and
`h¹(Y, 𝒪_Y) ≤ deg(ℒ|_Y)`, then

  `-2 χ(Y, 𝒪_Y) + deg(Z ∩ Y) < deg(ℒ^{⊗ 3}|_Y)`:

the left side is at most `2 h¹(Y, 𝒪_Y) - 2 + 2` since `h⁰(Y, 𝒪_Y) ≥ 1`, and the right side is
`3 deg(ℒ|_Y) = 2 deg(ℒ|_Y) + deg(ℒ|_Y) > 2 h¹(Y, 𝒪_Y)`. -/
theorem neg_two_mul_finsum_add_finrank_lt_invertibleCurveDegree {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (Z : X.IdealSheafData) (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (hZdeg : letI : Algebra k Γ(Z.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(Z.subscheme, ⊤) ≤ 2)
    (Y : X.IdealSheafData) [Nonempty Y.subscheme] (hY : topologicalKrullDim Y.subscheme ≤ 1)
    (hpos : 0 < invertibleCurveDegree k (Y.subschemeι ≫ f) hY
      ((Scheme.Modules.pullback Y.subschemeι).obj L))
    (hge : (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
        (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) ≤
      invertibleCurveDegree k (Y.subschemeι ≫ f) hY
        ((Scheme.Modules.pullback Y.subschemeι).obj L)) :
    letI := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
      X.ringCatSheaf.2 L 3
    letI : SheafOfModules.IsInvertible Y.subscheme.presheaf Y.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback Y.subschemeι).obj
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L 3)) :=
      Stacks.Modules.isInvertible_pullback _ _
    letI : Algebra k Γ((Z ⊔ Y).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ Y).subschemeι ≫ f).appTop).hom.toAlgebra
    (-2 : ℤ) * (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (Y.subschemeι ≫ f) (SheafOfModules.unit Y.subscheme.ringCatSheaf) n) : ℤ)) +
        (Module.finrank k Γ((Z ⊔ Y).subscheme, ⊤) : ℤ) <
      invertibleCurveDegree k (Y.subschemeι ≫ f) hY
        ((Scheme.Modules.pullback Y.subschemeι).obj
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L 3)) := by
  have hdeg := invertibleCurveDegree_pullback_tensorPower Y.subschemeι (Y.subschemeι ≫ f) hY L 3
    (hP := Stacks.Modules.isInvertible_pullback _ _)
    (hQ := Stacks.Modules.isInvertible_pullback _ _)
  have hχ := one_sub_finrank_le_finsum_finrank_unit (Y.subschemeι ≫ f) hY
  have he := finrank_globalSections_sup_le f Z Y hZ
  let : Algebra k Γ((Z ⊔ Y).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ Y).subschemeι ≫ f).appTop).hom.toAlgebra
  have he' : (Module.finrank k Γ((Z ⊔ Y).subscheme, ⊤) : ℤ) ≤ 2 := by
    exact_mod_cast he.trans hZdeg
  let := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
    X.ringCatSheaf.2 L 3
  let : SheafOfModules.IsInvertible Y.subscheme.presheaf Y.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback Y.subschemeι).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L 3)) :=
    Stacks.Modules.isInvertible_pullback _ _
  have hdeg3 : invertibleCurveDegree k (Y.subschemeι ≫ f) hY
      ((Scheme.Modules.pullback Y.subschemeι).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L 3)) =
      3 * invertibleCurveDegree k (Y.subschemeι ≫ f) hY
        ((Scheme.Modules.pullback Y.subschemeι).obj L) := hdeg
  rw [hdeg3]
  linarith

/-- **Positivity of the degree on reduced subcurves from positivity on integral ones.** Let `X` be
proper over `k` and `ℳ` an invertible `𝒪_X`-module whose restriction to every integral closed
subscheme of dimension one has positive degree. Then its restriction to every reduced closed
subscheme `Y` of dimension one has positive degree: by [Stacks, Tag 0AYW] that degree is the sum
of the degrees on the one-dimensional components of `Y`, each of weight one since `Y` is
reduced, and there is at least one such component. -/
theorem invertibleCurveDegree_subscheme_pos_of_forall_isIntegral {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hpos : ∀ (C : X.IdealSheafData) (_ : IsIntegral C.subscheme)
      (hC : topologicalKrullDim C.subscheme = 1),
      0 < invertibleCurveDegree k (C.subschemeι ≫ f) hC.le
        ((Scheme.Modules.pullback C.subschemeι).obj M))
    (Y : X.IdealSheafData) [IsReduced Y.subscheme] (hY : topologicalKrullDim Y.subscheme = 1) :
    0 < invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
      ((Scheme.Modules.pullback Y.subschemeι).obj M) := by
  classical
  let : X.Over (Spec (CommRingCat.of k)) := ⟨f⟩
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsProper f)
  rw [invertibleCurveDegree_eq_curveDegree,
    Stacks.AlgebraicGeometry.ComponentDegrees.curveDegree_eq_finsum_componentDegree_of_isProper,
    Stacks.AlgebraicGeometry.ComponentDegrees.finsum_componentMultiplicity_mul_of_isReduced]
  have : IsLocallyNoetherian Y.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Y.subschemeι ≫ f)
  have : CompactSpace Y.subscheme := QuasiCompact.compactSpace_of_compactSpace (Y.subschemeι ≫ f)
  have : IsNoetherian Y.subscheme := ⟨⟩
  have : Finite (Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne Y.subscheme) :=
    (Stacks.AlgebraicGeometry.ComponentDegrees.finite_genericPointsOne Y.subscheme).to_subtype
  have hterm : ∀ ξ : Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne Y.subscheme,
      0 < Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree k (Y.subschemeι ≫ f) hY.le
        ((Scheme.Modules.pullback Y.subschemeι).obj M) 1 ξ := by
    intro ξ
    obtain ⟨C, hCint, hCdim, -, hdeg⟩ := exists_idealSheafData_componentDegree (k := k) Y hY.le M ξ
    exact lt_of_lt_of_eq (hpos C hCint hCdim) hdeg
  obtain ⟨ξ₀⟩ :
      Nonempty (Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne Y.subscheme) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 := topologicalKrullDim_le_zero_of_isClosed_of_forall_notMem_genericPointsOne
      hY.le isClosed_univ (fun x _ hx => hne.false ⟨x, hx⟩)
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph, hY] at h0
    exact absurd h0 (by decide)
  let : Fintype (Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne Y.subscheme) :=
    Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_pos (fun ξ _ => hterm ξ) ⟨ξ₀, Finset.mem_univ _⟩

end AlgebraicGeometry

end

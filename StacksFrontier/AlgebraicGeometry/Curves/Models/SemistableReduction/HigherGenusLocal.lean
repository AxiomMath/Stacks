module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.SeparableComponents
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.GeometricallyReducedSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsionSequence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsionInjective
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GorensteinGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossGorenstein
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.FieldExtension
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Injectivity
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.PicardTorsion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelNumericalTypeGenus
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusAlgClosure
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective

/-!
# Semistable reduction in genus at least two: the local case

This is the core of [Stacks, Section 0CEI]. Let `X` be a minimal model of a smooth projective
curve `C` of genus `g ≥ 2` over the fraction field `K` of a discrete valuation ring `R` with
residue field `k`, such that `C` has a `K`-rational point and
`Pic(C)[ℓ] ≅ (ℤ/ℓℤ)^{2g}` for a prime `ℓ > 768 g` invertible in `k`. Then `X ⟶ Spec(R)` is
at-worst-nodal of relative dimension one, i.e. `C` has semistable reduction.

## The argument (the source's)

With `T` the numerical type of `X` and `g_top` its topological genus:
`dim Pic(T)[ℓ] ≤ g_top` ([Stacks, Tag 0C9X], `T` minimal by [Stacks, Tag 0CA6]);
`0 ⟶ Pic(X)[ℓ] ⟶ Pic(C)[ℓ] ⟶ Pic(T)[ℓ]` is exact ([Stacks, Tag 0CAD]) and
`Pic(X)[ℓ] ⟶ Pic(X_k)[ℓ]` is injective ([Stacks, Tag 0CAE]), so
`dim Pic(X_k)[ℓ] ≥ 2g - g_top`; [Stacks, Tag 0CE6] bounds `dim Pic(X_k)[ℓ] ≤ g + g_geom(X_k/k)`;
[Stacks, Tags 0CE9 and 0CEA] give `g ≥ h¹((X_k)_red) ≥ g_top + g_geom(X_k/k)`. The arithmetic
forces all these to be equalities. So `X_k` is reduced (0CE9), all multiplicities are `1`,
equality holds in 0CEA, and every component of `X_k` is smooth over `k`
(`Stacks.Models.RegularProperModelSituation.smooth_specialFiberComponentToSpec_of_eq`, which
replaces the false separability clause of [Stacks, Tag 0CEE] used by the source). Hence
`X_{k̄}` is reduced, `dim Pic(X_{k̄})[ℓ] ≥ g + g_geom` ([Stacks, Tag 0CC5]), and the closing step
(multicross singularities by [Stacks, Tag 0C20], nodes by [Stacks, Tags 0C60, 0C03, 0CDZ], the
fibrewise criterion [Stacks, Tag 0C59]) concludes.

Here `ℓ`-torsion is compared through its number of elements, which is the same for the various
spellings of `n`-torsion in the library (`Submodule.torsionBy`, `AddSubgroup.torsionBy`,
`Stacks.Picard.zsmulTorsion`).

## Main results

All in the namespace `Stacks.Models.RegularProperModelSituation`:

* `isAtWorstNodalOfRelativeDimensionOne_of_picardTorsion_local`
  — untagged; its premises `h0CE6`, `h0C20`, `h0C20eq` are the statements of [Stacks, Tags 0CE6
  and 0C20], and `hmin`, `hred₁`, `hred₂` are what [Stacks, Tags 0CA6 and
  0CE9] give for this `X`.

## References

* [Stacks Project, Section 0CEI](https://stacks.math.columbia.edu/tag/0CEI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Picard

universe u

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-! ### Counting `ℓ`-torsion -/

section TorsionCount

variable {A B P : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup P]

/-- A finite-dimensional `ℓ`-torsion subgroup has `ℓ ^ dim` elements. -/
private theorem natCard_torsionBy_eq_pow (ℓ : ℕ) [Fact ℓ.Prime]
    [FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy A (ℓ : ℤ))] :
    Nat.card (AddSubgroup.torsionBy A (ℓ : ℤ)) =
      ℓ ^ Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy A (ℓ : ℤ)) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod ℓ), Nat.card_zmod]

/-- The `ℤ`-submodule and the additive subgroup of `n`-torsion have the same elements. -/
private def torsionBySubmoduleEquiv (n : ℤ) :
    Submodule.torsionBy ℤ A n ≃ AddSubgroup.torsionBy A n :=
  Equiv.subtypeEquivRight fun x => by rw [Submodule.mem_torsionBy_iff]; exact Iff.rfl

/-- An additive map injective on `ℓ`-torsion bounds the number of `ℓ`-torsion elements of the
source by `ℓ ^ dim` of the finite-dimensional `ℓ`-torsion of the target. -/
private theorem natCard_torsionBy_le_pow_finrank_of_injOn (ℓ : ℕ) [Fact ℓ.Prime] (f : A →+ B)
    (hf : Set.InjOn f (zsmulTorsion A (ℓ : ℤ)))
    [FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy B (ℓ : ℤ))] :
    Nat.card (AddSubgroup.torsionBy A (ℓ : ℤ)) ≤
      ℓ ^ Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy B (ℓ : ℤ)) := by
  have : Finite (AddSubgroup.torsionBy B (ℓ : ℤ)) := Module.finite_of_finite (ZMod ℓ)
  rw [← natCard_torsionBy_eq_pow]
  refine Nat.card_le_card_of_injective
    (fun x => (⟨f x, ?_⟩ : AddSubgroup.torsionBy B (ℓ : ℤ))) fun x y hxy => ?_
  · change (ℓ : ℤ) • f x = 0
    rw [← map_zsmul]
    exact (congrArg f x.2).trans (map_zero f)
  · exact Subtype.ext (hf x.2 y.2 (congrArg Subtype.val hxy))

/-- In an exact sequence `0 ⟶ M ⟶ N ⟶ Q` of abelian groups with `N` and `Q` finite,
`|N| ≤ |M| |Q|`. -/
private theorem natCard_le_mul_of_exact {M N Q : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup Q] [Module ℤ M] [Module ℤ N] [Module ℤ Q] [Finite N] [Finite Q]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] Q) (hf : Function.Injective f) (hex : Function.Exact f g) :
    Nat.card N ≤ Nat.card M * Nat.card Q := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.toAddMonoidHom.ker
  have h2 : Nat.card g.toAddMonoidHom.ker = Nat.card M := by
    refine (Nat.card_congr ?_).symm
    refine (Equiv.ofInjective f hf).trans (Equiv.subtypeEquivRight fun y => ?_)
    rw [Set.mem_range, AddMonoidHom.mem_ker]
    exact (hex y).symm
  have h3 : Nat.card (N ⧸ g.toAddMonoidHom.ker) ≤ Nat.card Q :=
    Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective g.toAddMonoidHom)
  rw [h1, h2, mul_comm]
  exact Nat.mul_le_mul_left _ h3

/-- The `n`-torsion of a finitely generated abelian group is finite, for `n ≠ 0`. -/
private theorem finite_torsionBy_of_moduleFinite (H : Type*) [AddCommGroup H] [Module.Finite ℤ H]
    {n : ℤ} (hn : n ≠ 0) : Finite (AddSubgroup.torsionBy H n) := by
  let P := AddSubgroup.torsionBy H n
  have hS : (AddSubgroup.toIntSubmodule P).FG := Submodule.FG.of_le_of_isNoetherian le_top
  have : Module.Finite ℤ P := Module.Finite.iff_addGroup_fg.mpr
    ((AddGroup.fg_iff_addSubgroup_fg P).2 (by simpa [P] using Submodule.fg_toAddSubgroup hS))
  exact Module.finite_of_fg_torsion P fun x =>
    ⟨⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩, Subtype.ext (by
      change n • (x : H) = 0
      exact x.2)⟩

end TorsionCount

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **On a reduced special fibre the local ring at the generic point of a component is a field**:
it is reduced, local, and of dimension zero, the generic point of an irreducible component being
maximal for specialization. -/
theorem isField_stalk_specialFiberComponentGenericPoint_of_isReduced [IsReduced S.specialFiber]
    (Z : irreducibleComponents S.specialFiber) :
    IsField (S.specialFiber.presheaf.stalk (S.specialFiberComponentGenericPoint Z)) := by
  set ξ := S.specialFiberComponentGenericPoint Z
  have hclosure : closure ({ξ} : Set S.specialFiber) = Z.1 := by
    change closure {(S.specialFiberComponentι Z) (genericPoint _)} = _
    rw [← Set.image_singleton,
      (S.specialFiberComponentι Z).isClosedEmbedding.closure_image_eq, genericPoint_closure,
      Set.image_univ, range_specialFiberComponentι]
  have hgen : IsGenericPoint ξ Z.1 := hclosure
  have hmax : IsMax ξ := fun w hw =>
    le_of_eq (Topology.eq_of_specializes_isGenericPoint (hclosure ▸ Z.2) hgen hw)
  have hdim : ringKrullDim (S.specialFiber.presheaf.stalk ξ) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight]
    simpa only [WithBot.coe_zero] using
      congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) (Order.coheight_eq_zero.mpr hmax)
  have : Ring.KrullDimLE 0 (S.specialFiber.presheaf.stalk ξ) :=
    Ring.krullDimLE_iff.mpr hdim.le
  exact Ring.KrullDimLE.isField_of_isReduced

/-- **`H⁰((X_k)_red, 𝒪) = k` when `X_k` has a `k`-rational point**: `(X_k)_red` is proper, reduced
and connected over `k`, so its ring of global functions is a field, which a `k`-rational point
identifies with `k`. This is the hypothesis `H⁰((X_k)_red, 𝒪) = k` of [Stacks, Tag 0CE9]. -/
theorem isIso_globalSections_reduction_specialFiber (x : S.specialFiber)
    (hx : IsRationalPoint S.specialFiberToSpec x) :
    IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.specialFiber.reductionι ≫ S.specialFiberToSpec).appTop) := by
  have : ConnectedSpace S.specialFiber := S.connectedSpace_specialFiber
  have : ConnectedSpace S.specialFiber.reduction :=
    (Scheme.isHomeomorph_reductionι S.specialFiber).homeomorph.symm.surjective.connectedSpace
      (Scheme.isHomeomorph_reductionι S.specialFiber).homeomorph.symm.continuous
  obtain ⟨y, rfl⟩ := S.specialFiber.surjective_reductionι x
  have : IsIso (S.specialFiber.reductionι.residueFieldMap y) :=
    AlgebraicGeometry.isIso_residueFieldMap_of_isClosedImmersion _ _
  exact isIso_globalSections_of_isField_of_isRationalPoint _
    (isField_globalSections_of_connectedSpace S.k
      (S.specialFiber.reductionι ≫ S.specialFiberToSpec)) y
    (isRationalPoint_comp _ S.specialFiberToSpec y hx)

/-- **The local case of [Stacks, Section 0CEI].** In the situation of [Stacks, Tag 0C61], let
`X` be a model whose numerical type is minimal, with `h¹((X_k)_red) ≤ h¹(X_k)` and `X_k` reduced
when equality holds (what [Stacks, Tags 0CA6 and 0CE9] give for a minimal model). If `C` has a
`K`-rational point, genus `g ≥ 2`, and `Pic(C)[ℓ] ≅ (ℤ/ℓℤ)^{2g}` for a prime `ℓ > 768 g`
invertible in `k`, then `X ⟶ Spec(R)` is at-worst-nodal of relative dimension one. The premises
`h0CE6`, `h0C20`, `h0C20eq` are the statements of [Stacks, Tags 0CE6 and 0C20]. -/
theorem isAtWorstNodalOfRelativeDimensionOne_of_picardTorsion_local
    (h0CE6 : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
      (_ : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (_ : IsUnit (ℓ : k)),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ≤
          genus g + geometricGenus k g)
    (h0C20 : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [IsReduced X] (_hdim : topologicalKrullDim (X : Type u) = 1)
      (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ≤
          genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)))
    (h0C20eq : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IsReduced X]
      (_hdim : topologicalKrullDim (X : Type u) = 1) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        (Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) =
            genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)) ↔
          ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
            Stacks.Curves.IsMulticrossSingularity k X x))
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (hmin : NumericalType.IsMinimal (S.associatedNumericalType n e))
    (hred₁ : genus (S.specialFiber.reductionι ≫ S.specialFiberToSpec) ≤ genus S.specialFiberToSpec)
    (hred₂ : genus (S.specialFiber.reductionι ≫ S.specialFiberToSpec) = genus S.specialFiberToSpec →
      IsReduced S.specialFiber)
    (p : Spec (.of S.K) ⟶ S.C) (hp : p ≫ S.C_to_K = 𝟙 _)
    (hg : 2 ≤ genus S.C_to_K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 768 * genus S.C_to_K < ℓ)
    (hℓk : (ℓ : S.k) ≠ 0)
    (htors : Nonempty (AddSubgroup.torsionBy (ofScheme S.C) (ℓ : ℤ) ≃+
      (Fin (2 * genus S.C_to_K) → ZMod ℓ))) :
    IsAtWorstNodalOfRelativeDimensionOne S.X_to_R := by
  classical
  set g := genus S.C_to_K
  have hℓprime : ℓ.Prime := Fact.out
  have hℓ1 : 1 ≤ ℓ := hℓprime.one_lt.le
  have : NeZero ℓ := ⟨hℓprime.ne_zero⟩
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓprime.ne_zero
  have hℓunit : IsUnit ((ℓ : ℕ) : S.k) := isUnit_iff_ne_zero.mpr hℓk
  have hℓunitℤ : IsUnit (((ℓ : ℤ) : ℤ) : S.k) := by exact_mod_cast hℓunit
  obtain ⟨⟨x, hx, hsm, hxZ⟩, hΓ, hgk⟩ :=
    S.exists_isRationalPoint_smoothAt_specialFiber_and_genus_eq p hp
  obtain ⟨Z₀, hZ₀⟩ := S.exists_mem_specialFiberComponent x
  set T := S.associatedNumericalType n e
  have hTg : T.genus = (g : ℤ) := (S.associatedNumericalType_spec_and_genus n e).2
  -- the `ℓ`-torsion of `Pic(T)`
  have hTfin : Finite (AddSubgroup.torsionBy (NumericalType.picardGroup T) (ℓ : ℤ)) :=
    finite_torsionBy_of_moduleFinite _ hℓ0
  have : FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (NumericalType.picardGroup T) (ℓ : ℤ)) :=
    Module.Finite.of_finite
  have h9X : (Module.finrank (ZMod ℓ)
      (AddSubgroup.torsionBy (NumericalType.picardGroup T) (ℓ : ℤ)) : ℤ) ≤ T.topologicalGenus :=
    NumericalType.finrank_picardGroup_torsionBy_le_topGenus_of_isMinimal T g
      (by exact_mod_cast hg) hTg hmin ℓ (by exact_mod_cast hℓ)
  set t := Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (NumericalType.picardGroup T) (ℓ : ℤ))
  -- the `ℓ`-torsion of `Pic(C)`
  have hCcard : Nat.card (AddSubgroup.torsionBy (ofScheme S.C) (ℓ : ℤ)) = ℓ ^ (2 * g) := by
    rw [Nat.card_congr htors.some.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hCfin : Finite (AddSubgroup.torsionBy (ofScheme S.C) (ℓ : ℤ)) :=
    Finite.of_equiv _ htors.some.toEquiv.symm
  -- exactness of `0 ⟶ Pic(X)[ℓ] ⟶ Pic(C)[ℓ] ⟶ Pic(T)[ℓ]` ([Stacks, Tag 0CAD])
  have hgcd : Nat.Coprime ℓ (Finset.univ.gcd S.specialFiberMultiplicity) := by
    have hdvd : Finset.univ.gcd S.specialFiberMultiplicity ∣ S.specialFiberMultiplicity Z₀ :=
      Finset.gcd_dvd (Finset.mem_univ Z₀)
    rw [(hxZ Z₀ hZ₀).2, Nat.dvd_one] at hdvd
    rw [hdvd]
    exact Nat.coprime_one_right ℓ
  obtain ⟨hinj, hex⟩ := S.picardTorsionSequence_exact n e hℓ1 hgcd
  have : Finite (Submodule.torsionBy ℤ (ofScheme S.C) (ℓ : ℤ)) :=
    Finite.of_equiv _ (torsionBySubmoduleEquiv _).symm
  have : Finite (Submodule.torsionBy ℤ (NumericalType.picardGroup T) (ℓ : ℤ)) :=
    Finite.of_equiv _ (torsionBySubmoduleEquiv _).symm
  have hseq := natCard_le_mul_of_exact _ _ hinj hex
  rw [Nat.card_congr (torsionBySubmoduleEquiv _), Nat.card_congr (torsionBySubmoduleEquiv _),
    Nat.card_congr (torsionBySubmoduleEquiv _), hCcard,
    natCard_torsionBy_eq_pow ℓ (A := NumericalType.picardGroup T)] at hseq
  -- `Pic(X)[ℓ] ⟶ Pic(X_k)[ℓ]` is injective ([Stacks, Tag 0CAE])
  have h0CAE := injOn_schemePullbackClass_specialFiberRedι_zsmulTorsion S hℓunitℤ
  have hinjk : Set.InjOn (schemePullbackClassHom S.specialFiberι)
      (zsmulTorsion (ofScheme S.X) (ℓ : ℤ)) := by
    intro a ha b hb hab
    refine h0CAE ha hb ?_
    rw [specialFiberRedι, ← schemePullbackClass_comp, ← schemePullbackClass_comp]
    exact congrArg _ hab
  -- [Stacks, Tag 0CE6] for `X_k`
  have hdimk : topologicalKrullDim S.specialFiber = (1 : WithBot ℕ∞) :=
    S.topologicalKrullDim_specialFiber ⟨x⟩
  obtain ⟨hkfd, hk6⟩ := h0CE6 S.k S.specialFiberToSpec hdimk.le ℓ hℓunit
  have := hkfd
  set dk := Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme S.specialFiber) (ℓ : ℤ))
  have hXk := natCard_torsionBy_le_pow_finrank_of_injOn (A := ofScheme S.X)
    (B := ofScheme S.specialFiber) ℓ (schemePullbackClassHom S.specialFiberι) hinjk
  -- [Stacks, Tag 0CEA]
  have h0CEA := S.topologicalGenus_add_geometricGenus_le_finrank_reduction x hx hsm n e
  rw [← genus_eq_finrank_cohomologyOverField_unit_one'] at h0CEA
  -- the numerology
  have hpow : ℓ ^ (2 * g) ≤ ℓ ^ (dk + t) := by
    rw [pow_add]
    exact hseq.trans (Nat.mul_le_mul_right _ hXk)
  have hexp : 2 * g ≤ dk + t := (Nat.pow_le_pow_iff_right hℓprime.one_lt).mp hpow
  rw [hgk] at hk6 hred₁ hred₂
  have hτ : (S.associatedNumericalType n e).topologicalGenus = T.topologicalGenus := rfl
  rw [hτ] at h0CEA
  clear hseq hXk hpow hCcard
  have hh1 : genus (S.specialFiber.reductionι ≫ S.specialFiberToSpec) = g := by omega
  have htop : T.topologicalGenus + (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      (genus (S.specialFiber.reductionι ≫ S.specialFiberToSpec) : ℤ) := by omega
  have hdk : dk = g + geometricGenus S.k S.specialFiberToSpec := by omega
  -- `X_k` is reduced ([Stacks, Tag 0CE9]) and every multiplicity is one
  have hred : IsReduced S.specialFiber := hred₂ hh1
  have hmult : ∀ Z, S.specialFiberMultiplicity Z = 1 := fun Z =>
    S.specialFiberMultiplicity_eq_one_of_isField Z
      (S.isField_stalk_specialFiberComponentGenericPoint_of_isReduced Z)
  -- equality in [Stacks, Tag 0CEA], hence every component is smooth over `k`
  have heq : (S.associatedNumericalType n e).topologicalGenus +
      (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) := by
    rw [← genus_eq_finrank_cohomologyOverField_unit_one', hτ]
    exact htop
  have hsmZ := S.smooth_specialFiberComponentToSpec_of_eq x hx hsm n e heq hmult hmin
  -- the geometric special fibre
  set kbar := AlgebraicClosure S.k
  set a := Spec.map (CommRingCat.ofHom (algebraMap S.k kbar))
  set Y := pullback S.specialFiberToSpec a
  let : Y.Over (Spec (.of kbar)) := ⟨pullback.snd _ _⟩
  have hYred : IsReduced Y := S.isReduced_pullback_specialFiberToSpec_of_smooth hsmZ kbar
  have : IsProper (Y ↘ Spec (.of kbar)) := inferInstanceAs (IsProper (pullback.snd _ _))
  have hdimY : topologicalKrullDim (Y : Type u) = 1 := by
    rw [topologicalKrullDim_baseChange S.k kbar _ _ S.specialFiberToSpec
      (IsPullback.of_hasPullback _ _)]
    exact hdimk
  have hℓkbar : (ℓ : kbar) ≠ 0 := by simpa using (algebraMap S.k kbar).injective.ne hℓk
  obtain ⟨hYfd, -⟩ := h0C20 kbar Y hdimY ℓ hℓkbar
  have hgY : genus (Y ↘ Spec (.of kbar)) = g :=
    (genus_pullback_snd_eq S.k kbar (algebraMap S.k kbar) S.specialFiberToSpec).trans hgk
  have hggY : geometricGenus kbar (Y ↘ Spec (.of kbar)) =
      geometricGenus S.k S.specialFiberToSpec :=
    (geometricGenus_eq_geometricGenus_pullback_snd S.k S.specialFiberToSpec hdimk.le).symm
  -- `Pic(X_k)[ℓ] ⟶ Pic(X_{k̄})[ℓ]` is injective ([Stacks, Tag 0CC5])
  let := Stacks.AlgebraicGeometry.PicardBaseChange.globalSectionsAlgebra S.specialFiberToSpec
  have hfd : FiniteDimensional S.k Γ(S.specialFiber, ⊤) :=
    Module.Finite.of_surjective (Algebra.linearMap S.k Γ(S.specialFiber, ⊤))
      (ConcreteCategory.bijective_of_isIso
        ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop)).2
  have h0CC5 :=
    Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_finiteDimensional
      S.specialFiber (algebraMap S.k kbar) S.specialFiberToSpec hfd
  have := hYfd
  have hYk := natCard_torsionBy_le_pow_finrank_of_injOn (A := ofScheme S.specialFiber)
    (B := ofScheme Y) ℓ _ (h0CC5.injOn (s := zsmulTorsion _ _))
  rw [natCard_torsionBy_eq_pow ℓ (A := ofScheme S.specialFiber)] at hYk
  have hdY : dk ≤ Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ)) :=
    (Nat.pow_le_pow_iff_right hℓprime.one_lt).mp hYk
  have hge : genus (Y ↘ Spec (.of kbar)) + geometricGenus kbar (Y ↘ Spec (.of kbar)) ≤
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ)) := by
    rw [hgY, hggY]
    omega
  -- the closing step: multicross singularities, Gorenstein, nodes ([Stacks, Tags 0C20, 0C60,
  -- 0C03, 0CDZ]), and the fibrewise criterion [Stacks, Tag 0C59]
  exact S.isAtWorstNodalOfRelativeDimensionOne_of_specialFiber
    (S.hasAtWorstNodalSingularities_specialFiber_of_le_finrank h0C20 h0C20eq hYred ℓ hℓk hge)

end Stacks.Models.RegularProperModelSituation

end

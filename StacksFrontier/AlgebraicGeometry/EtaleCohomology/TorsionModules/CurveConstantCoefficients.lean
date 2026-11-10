module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.Localization.SimultaneousTrivialization

/-!
# Finiteness of the cohomology of constant torsion sheaves of modules on curves

Let `Λ` be a Noetherian ring, `k` an algebraically closed field, `X` a separated scheme of finite
type over `k` of dimension at most one, and `M` a finite `Λ`-module annihilated by an integer
`n > 0`. [Stacks, Tag 0GJC] asserts that `H^q(X, M̲)` is a finite `Λ`-module when `n` is prime to
the characteristic of `k`, and also when `X` is proper. This file proves it from the statement of
[Stacks, Tag 03SC], which is not proved here but taken as the one named input.

## Main definitions

* `Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf`: constructible abelian sheaves
  (Tag 03RW part (2)) on Mathlib's small étale site, by transport to the small étale site of
  Tag 021B.
* `Stacks.EtaleCohomology.CurveTorsionStatements`: the eight statements of Situation 0A52 for one
  abelian sheaf.
* `Stacks.EtaleCohomology.CurveTorsionCohomologyStatement`: the statement of Tag 03SC.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_constantSheaf`: a finite constant
  abelian sheaf is constructible.
* `Stacks.EtaleCohomology.TorsionModules.module_finite_etaleCohomology_constantSheaf`: Tag 0GJC,
  both parts, from the statement of Tag 03SC.

## Implementation notes

`Stacks.EtaleCohomology.CurveTorsionCohomologyStatement` is a proposition and not a structure:
it is the conjunction of the eight clauses of Tag 03SC, quantified over every situation of the
source, and is used only as the hypothesis of the theorem that consumes Tag 03SC. It is a
separate declaration because the elaboration of its eight clauses, inline in the signature of
the theorem, exceeds the default heartbeat budget.

Cohomology of abelian sheaves is Mathlib's `CategoryTheory.Sheaf.H`, with `Ext`-groups in the
universe `max (u + 1) r` of the coefficients, which is what the restriction maps
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` of clauses (6) to (8) are stated for; it is
compared with the right derived functors of global sections by
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`.

## References

* [Stacks Project, Tag 0GJC](https://stacks.math.columbia.edu/tag/0GJC)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp

/-- The direct image along a morphism of the canonical big étale site containing `X`, for
sheaves of abelian groups, is a right adjoint. Stated pointwise so that instance search finds it
for the quantified instance argument of `AlgebraicGeometry.IsConstructibleAbelianSheaf`, which
it does not find from Mathlib's general instance directly. -/
instance isRightAdjoint_sheafPushforwardContinuous_addCommGrpCat_containing (X : Scheme.{u})
    (S T : (BigEtaleSite.containing X).Scheme) (f : T ⟶ S) :
    (Functor.sheafPushforwardContinuous
      (AlgebraicGeometry.smallEtaleBaseChange (BigEtaleSite.containing X) f)
      AddCommGrpCat.{max (u + 1) r}
      (AlgebraicGeometry.SmallEtale.topology (BigEtaleSite.containing X) S.obj S.property)
      (AlgebraicGeometry.SmallEtale.topology (BigEtaleSite.containing X) T.obj
        T.property)).IsRightAdjoint :=
  inferInstance

/-- **Constructible abelian sheaves** (Tag 03RW part (2)) on Mathlib's small étale site: the
transport of the sheaf to the small étale site of Tag 021B of the canonical big étale site
`AlgebraicGeometry.BigEtaleSite.containing X` is constructible in the sense of
`AlgebraicGeometry.IsConstructibleAbelianSheaf`. -/
abbrev IsConstructibleSmallEtaleAbelianSheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) : Prop :=
  IsConstructibleAbelianSheaf.{u, max (u + 1) r} (BigEtaleSite.containing X)
    ((BigEtaleSite.containing X).obj X (BigEtaleSite.contains_containing X))
    ((SmallEtale.sheafEquiv (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X)
      AddCommGrpCat.{max (u + 1) r}).inverse.obj F)

/-- **A finite constant abelian sheaf is constructible.** Transported to the small étale site of
Tag 021B it is again the constant sheaf (`CategoryTheory.equivCommuteConstant'`), whose restriction
to every object is the constant sheaf there with the same finite value, so it is finite locally
constant, hence constructible. -/
theorem isConstructibleEtaleAbelianSheaf_constantSheaf (X : Scheme.{u})
    (A : AddCommGrpCat.{max (u + 1) r}) [Finite A] :
    IsConstructibleSmallEtaleAbelianSheaf.{u, r}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj A) := by
  let B := BigEtaleSite.containing X
  let hX := BigEtaleSite.contains_containing X
  let J := SmallEtale.topology B X hX
  have hlim : ∀ T : (X.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (SmallEtale.toEtaleSite B X hX).op) AddCommGrpCat.{max (u + 1) r} :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have hT : IsTerminal ((SmallEtale.toEtaleSite B X hX).obj (SmallEtale.final B X hX)) :=
    have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
      ⟨fun _ => inferInstance⟩
    MorphismProperty.Over.mkIdTerminal _ _
  let e : (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) r}).inverse.obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj A) ≅
      (constantSheaf J AddCommGrpCat.{max (u + 1) r}).obj A :=
    ((equivCommuteConstant' J AddCommGrpCat.{max (u + 1) r} X.smallEtaleTopology
      (SmallEtale.toEtaleSite B X hX) (SmallEtale.finalIsTerminal B X hX) hT).app A).symm
  have hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant J
      ((constantSheaf J AddCommGrpCat.{max (u + 1) r}).obj A) :=
    ⟨fun U => ⟨PUnit, fun _ => U, fun _ => 𝟙 U, Stacks.ConstantSheaf.sieve_ofArrows_id_mem J U,
      fun _ => ⟨A, inferInstance, ⟨(Stacks.ConstantSheaf.overPullbackConstantSheafIso J
        AddCommGrpCat.{max (u + 1) r} U).app A⟩⟩⟩⟩
  have hF' : Stacks.ConstantSheaf.IsFiniteLocallyConstant J
      ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) r}).inverse.obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj A)) :=
    Stacks.ConstantSheaf.IsFiniteLocallyConstant.of_iso J e.symm hF
  exact isConstructibleAbelianSheaf_of_isFiniteLocallyConstant B _ _

/-- **The eight statements of Situation 0A52 for one abelian sheaf** ([Stacks, Tag 0A52],
statements 0A53 to 0A5A), on Mathlib's small étale site with coefficients in
`AddCommGrpCat.{max (u + 1) r}` and cohomology Mathlib's `Sheaf.H`. For a scheme `X` with
structure morphism `π : X ⟶ Spec k` to the spectrum of a field and an abelian sheaf `F` on
`X_étale`, "statements (0A53) -- (0A5A) hold for `F`" is the conjunction of

1. `H^q(X, F) = 0` for `q > 2`;
2. `H^q(X, F) = 0` for `q > 1` if `X` is affine;
3. `H^q(X, F) = 0` for `q > 1` if `p = char(k) > 0` and `F` is `p`-power torsion;
4. `H^q(X, F)` is finite if `F` is constructible and torsion prime to `char(k)`;
5. `H^q(X, F)` is finite if `X` is proper and `F` is constructible;
6. `H^q(X, F) ⟶ H^q(X_{k'}, F|_{X_{k'}})` is bijective for every extension `k'/k` of
   algebraically closed fields if `F` is torsion prime to `char(k)`;
7. the same map is bijective for every such `k'` if `X` is proper;
8. `H^2(X, F) ⟶ H^2(U, F)` is surjective for every open `U ⊆ X`.

The source states these in Situation 0A52, for `k` algebraically closed, `X` separated of finite
type over `k` of dimension at most one and `F` torsion; those standing hypotheses are those of the
results that conclude this predicate, not part of it. "Torsion prime to `char(k)`" is read with
the exponential characteristic, so that it is no condition in characteristic zero, and
constructibility is `Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf` (Tag 03RW part
(2)). -/
def CurveTorsionStatements {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) : Prop :=
  (∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{max (u + 1) r} F q)) ∧
    (IsAffine X → ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{max (u + 1) r} F q)) ∧
    (0 < ringChar k →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology (ringChar k) F →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{max (u + 1) r} F q)) ∧
    (IsConstructibleSmallEtaleAbelianSheaf.{u, r} F →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
      ∀ q : ℕ, Finite (Sheaf.H.{max (u + 1) r} F q)) ∧
    (IsConstructibleSmallEtaleAbelianSheaf.{u, r} F → IsProper π →
      ∀ q : ℕ, Finite (Sheaf.H.{max (u + 1) r} F q)) ∧
    (∀ (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'],
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
      ∀ q : ℕ, Function.Bijective (etaleCohomologyRestrictionMap.{u, r, max (u + 1) r}
        (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k k')))) F q)) ∧
    (IsProper π → ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'],
      ∀ q : ℕ, Function.Bijective (etaleCohomologyRestrictionMap.{u, r, max (u + 1) r}
        (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k k')))) F q)) ∧
    (∀ U : X.Opens, Function.Surjective
      (etaleCohomologyRestrictionMap.{u, r, max (u + 1) r} U.ι F 2))

/-- **The statement of [Stacks, Tag 03SC]**, for abelian sheaves on Mathlib's small étale site with
coefficients in `AddCommGrpCat.{max (u + 1) r}` and cohomology Mathlib's `Sheaf.H`: if `k` is an
algebraically closed field, `X` a separated scheme of finite type over `k` of dimension at most
one, and `F` a torsion abelian sheaf on `X_étale`, then the eight statements of Situation 0A52,
`Stacks.EtaleCohomology.CurveTorsionStatements`, hold for `F`:

1. `H^q(X, F) = 0` for `q > 2`;
2. `H^q(X, F) = 0` for `q > 1` if `X` is affine;
3. `H^q(X, F) = 0` for `q > 1` if `p = char(k) > 0` and `F` is `p`-power torsion;
4. `H^q(X, F)` is finite if `F` is constructible and torsion prime to `char(k)`;
5. `H^q(X, F)` is finite if `X` is proper and `F` is constructible;
6. `H^q(X, F) ⟶ H^q(X_{k'}, F|_{X_{k'}})` is bijective for every extension `k'/k` of
   algebraically closed fields if `F` is torsion prime to `char(k)`;
7. the same map is bijective for every such `k'` if `X` is proper;
8. `H^2(X, F) ⟶ H^2(U, F)` is surjective for every open `U ⊆ X`.

"Torsion prime to `char(k)`" is read with the exponential characteristic, so that it is no
condition in characteristic zero, and constructibility is
`Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf` (Tag 03RW part (2)). -/
def CurveTorsionCohomologyStatement : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π], topologicalKrullDim X ≤ 1 →
    ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F →
      CurveTorsionStatements.{u, r} π F

namespace TorsionModules

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks Project, Tag 0GJC, given Tag 03SC.** Let `Λ` be a Noetherian ring, `M` a finite
`Λ`-module annihilated by an integer `n > 0`, `k` an algebraically closed field and `X` a
separated scheme of finite type over `k` of dimension at most one. Then `H^q(X, M̲)` is a finite
`Λ`-module for every `q`, if `n` is prime to the characteristic of `k` (part (1)) or if `X` is
proper over `k` (part (2)).

The one input is `h03SC`, the full statement of [Stacks, Tag 03SC] — the cohomology of torsion
abelian sheaves on such curves — for abelian sheaves on Mathlib's small étale site with
coefficients in `AddCommGrpCat.{max (u + 1) r}`; it is a hypothesis and not proved here. Its
clauses (4) and (5), finiteness of `H^q(X, ℤ/ℓ̲)` for the primes `ℓ ∣ n`, are what the proof
uses.

The proof is the source's. The dévissage `0 ⟶ M[ℓ] ⟶ M ⟶ M/M[ℓ] ⟶ 0` reduces to a module killed
by a prime `ℓ`
(`Stacks.EtaleCohomology.module_finite_constantCohomology_of_nsmul_eq_zero`), and there the
`𝔽_ℓ`-basis trick (`Stacks.EtaleCohomology.module_finite_constantCohomology_of_prime`) applies:
the cohomology of `M̲` as a sheaf of `Λ`-modules is that of its underlying abelian sheaf
(Stacks 03FD, `Stacks.EtaleCohomology.etaleModuleCohomologyForgetIso`), étale cohomology of the
quasi-compact quasi-separated scheme `X` commutes with filtered colimits (Stacks 03Q5), and the
classes coming from a finite dimensional `𝔽_ℓ`-subspace of `M` lie in the `Λ`-submodule
generated by the images of the finite group `H^q(X, ℤ/ℓ̲)`. The reduction of the source from
`Λ` to `Λ/ℓΛ` is not needed: the basis trick is run over `Λ` directly.

Parts (1) and (2) are combined into one statement through the disjunction
`n.Coprime (ringExpChar k) ∨ IsProper π`; the exponential characteristic makes the coprimality
condition vacuous in characteristic zero, as in the source. -/
theorem module_finite_etaleCohomology_constantSheaf
    (h03SC : CurveTorsionCohomologyStatement.{u, r})
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1)
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] (n : ℕ) (hn : 0 < n)
    (hM : ∀ m : M, n • m = 0) (hnp : n.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated π
  refine module_finite_constantCohomology_of_nsmul_eq_zero n hn (fun ℓ hℓ hℓn q' => ?_) M hM q
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let A := AddCommGrpCat.of (ULift.{max (u + 1) r} (ZMod ℓ))
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj A
  have : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).Additive :=
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}
      (etaleSiteTerminalIsTerminal X)).left_adjoint_additive
  have hA : ((ℓ : ℤ) • 𝟙 A) = 0 := by
    refine AddCommGrpCat.ext fun x => ?_
    apply ULift.ext
    change (ℓ : ℤ) • x.down = 0
    rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  have hF : ((ℓ : ℤ) • 𝟙 F) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, hA, Functor.map_zero]
  have hsec : ∀ (U : X.Etaleᵒᵖ) (x : F.obj.obj U), ℓ • x = 0 := fun U x => by
    rw [← natCast_zsmul]
    exact (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff F ℓ).1 hF U x
  have htors : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F := fun U x =>
    ⟨⊤, X.smallEtaleTopology.top_mem U, fun V g _ => ⟨ℓ, hℓ.pos, hsec _ _⟩⟩
  have : Finite A := inferInstanceAs (Finite (ULift (ZMod ℓ)))
  have hc : IsConstructibleSmallEtaleAbelianSheaf.{u, r} F :=
    isConstructibleEtaleAbelianSheaf_constantSheaf X A
  obtain ⟨-, -, -, h4, h5, -⟩ := h03SC π hX F htors
  have hH : Finite (Sheaf.H.{max (u + 1) r} F q') := by
    rcases hnp with hcop | hprop
    · refine h4 hc (fun U x => ⟨⊤, X.smallEtaleTopology.top_mem U,
        fun V g _ => ⟨ℓ, hℓ.pos, ?_, hsec _ _⟩⟩) q'
      exact Nat.Coprime.coprime_dvd_left hℓn hcop
    · exact h5 hc hprop q'
  exact @Finite.of_equiv _ _ hH
    ((Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{r} X.smallEtaleTopology
      q').app F).addCommGroupIsoToAddEquiv.toEquiv.symm

end TorsionModules

end Stacks.EtaleCohomology

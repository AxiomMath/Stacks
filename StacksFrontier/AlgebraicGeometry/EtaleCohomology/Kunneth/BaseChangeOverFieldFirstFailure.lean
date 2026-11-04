module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NormalSepClosedConstantDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstFailureFunctionFieldDiagram
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal

/-!
# Base change over a field: the first failure, and the assembly of the proof of Stacks 0F1I

This file proves the third paragraph of the proof of [Stacks, Tag 0F1I] and puts the reductions of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverField` together with it.

The paragraph reads: *"At this point we may apply Lemma 0F1D to see that it suffices to prove:
given a commutative diagram*

```
X  ←--  X'  ←-h-  Y
|f      |f'       |
Spec K ←-- S' ←-- Spec L
```

*with both squares cartesian, where `S'` is affine, integral, and normal with algebraically
closed function field `L`, then `R^q h_*(ℤ/dℤ)` is zero for `q > 0` and `d ∣ n`. Observe that
this vanishing is equivalent to the statement that `(f')⁻¹R^q(Spec L ⟶ S')_*ℤ/dℤ ⟶
R^q h_*ℤ/dℤ` is an isomorphism, because the left hand side is zero for example by Lemma
0EZP."*

## Main definitions

* `Stacks.EtaleCohomology.BaseChangeOverField.FunctionFieldBaseChange` — the assertion the last
  paragraph of the source's proof establishes: for the diagrams of [Stacks, Tag 0F1D] over `f`
  and every `d ∣ n`, the base change map `(f')⁻¹R^q(Spec L ⟶ S')_*ℤ/dℤ ⟶ R^q h_*ℤ/dℤ` is an
  isomorphism in every degree `q > 0`.

## Main results

* `Stacks.EtaleCohomology.BaseChangeOverField.isZero_rightDerived_constantZMod_of_isAlgClosed` —
  [Stacks, Tag 0EZP] for the spectrum of an algebraically closed field: `R^q(Spec L ⟶ S')_*ℤ/dℤ`
  vanishes for `q > 0`.
* `Stacks.EtaleCohomology.BaseChangeOverField.isZero_rightDerived_constantZMod_of_isIso` — the
  observation of the source: if the base change map is an isomorphism, then
  `R^q h_*ℤ/dℤ = 0`.
* `Stacks.EtaleCohomology.BaseChangeOverField.baseChangeHolds_of_functionFieldBaseChange` — the
  application of [Stacks, Tag 0F1D]: `BC(f, n, 0)` and `FunctionFieldBaseChange f n` give
  `BC(f, n, q)` for every `q`, granted [Stacks, Tag 0F08] and [Stacks, Tag 0F09].
* `Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_of_reduction` — the
  assembly: for `X` over `K`, `n` invertible in `K` and `Z` the reduction of `X_{K̄}`, the
  degree-zero condition `BC(Z ⟶ Spec K̄, n, 0)` and `FunctionFieldBaseChange (Z ⟶ Spec K̄) n` give
  derived base change for sheaves annihilated by `n` over `X ⟶ Spec K`, granted
  [Stacks, Tag 0F09] and [Stacks, Tag 0F08].

## Implementation notes

*The inputs carried as arguments.* Two results that the source's proof cites and that are not
proved in this repository are explicit arguments, named by content: `hSmoothLimitBaseChange`, the
statement of [Stacks, Tag 0F09] (through which [Stacks, Tag 0F1C] and [Stacks, Tag 0F0B] (2) are
available), and `hFirstFailure`, of the type of [Stacks, Tag 0F08]. They are the arguments
`hSmoothLimit` and `hFirstFailure` of
`Stacks.EtaleCohomology.FirstFailureFunctionField.functionFieldFailure_of_firstFailure`, which is
[Stacks, Tag 0F1D] from them. None of the declarations here is registered.

*What the assembly still asks.* Its hypotheses `hDegreeZero` and `hFunctionField` are steps of the
source's proof that are not proved here: `hDegreeZero` is where the source applies
[Stacks, Tag 0EYS]; for `X` locally of finite type over `K` it is discharged in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverFieldDegreeZero`
(`Stacks.EtaleCohomology.BaseChangeOverField.baseChangeHolds_zero_reduction`, and the assembly
without it, `derivedBaseChangeHolds_of_reduction_of_locallyOfFiniteType`). `hFunctionField` is
the last paragraph (Tag 0EZT along the finite type subalgebras of `Γ(S', 𝒪)`
and [Stacks, Tag 0F1H]). The assembly also starts after the source's first paragraph: the
reduction to `X` affine of finite type over `K` and from a torsion sheaf to a sheaf annihilated
by one `n`.

## References

* [Stacks Project, Tag 0F1I](https://stacks.math.columbia.edu/tag/0F1I)
* [Stacks Project, Tag 0F1D](https://stacks.math.columbia.edu/tag/0F1D)
* [Stacks Project, Tag 0EZP](https://stacks.math.columbia.edu/tag/0EZP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.BaseChangeOverField

-- `smallEtaleDerivedBaseChangeAb` (BaseChangeHigher/BaseChangeCondition.lean) is built under the
-- standard model, which fixes the model of the derived categories here.
attribute [local instance] HasDerivedCategory.standard

open FirstFailureDiagram FirstFailureFunctionField

/-! ### Stacks 0EZP for the spectrum of an algebraically closed field -/

/-- The function field of the spectrum of a field is that field. -/
def functionFieldSpecEquiv (L : Type u) [Field L] :
    CommRingCat.of L ≃+* (Spec (CommRingCat.of L)).functionField :=
  letI : Algebra (CommRingCat.of L) (Spec (CommRingCat.of L)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of L)
  letI : IsFractionRing (CommRingCat.of L) (Spec (CommRingCat.of L)).functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of L)
  letI : IsFractionRing (CommRingCat.of L) (CommRingCat.of L) :=
    IsFractionRing.idem (CommRingCat.of L) (CommRingCat.of L)
  (IsFractionRing.algEquiv (CommRingCat.of L) (CommRingCat.of L)
    (Spec (CommRingCat.of L)).functionField).toRingEquiv

/-- **[Stacks, Tag 0EZP] for the spectrum of an algebraically closed field.** For a morphism
`g : Spec L ⟶ S'` with `L` algebraically closed, the higher direct images `R^q g_*(ℤ/dℤ)`,
`q > 0`, vanish: `Spec L` is integral and normal with separably closed function field `L`. -/
theorem isZero_rightDerived_constantZMod_of_isAlgClosed (L : Type u) [Field L] [IsAlgClosed L]
    {S' : Scheme.{u}} (g : Spec (CommRingCat.of L) ⟶ S') (d q : ℕ) (hq : 0 < q) :
    IsZero (((smallEtalePushforwardAb g).rightDerived q).obj
      (constantZMod (Spec (CommRingCat.of L)) d)) := by
  have : IsNormal (Spec (CommRingCat.of L)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed L)
  have : IsAlgClosed (Spec (CommRingCat.of L)).functionField :=
    IsAlgClosed.of_ringEquiv (CommRingCat.of L) _ (functionFieldSpecEquiv L)
  exact isZero_rightDerived_smallEtalePushforward_constantSheaf g
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))) q hq

/-- **The observation of the source.** In a cartesian square over the canonical morphism
`Spec K(S') ⟶ S'` of an integral scheme `S'` with algebraically closed function field, if the
base change map `(f')⁻¹R^q(Spec K(S') ⟶ S')_*ℤ/dℤ ⟶ R^q h_*ℤ/dℤ` is an isomorphism in a degree
`q > 0`, then `R^q h_*ℤ/dℤ = 0`: its source vanishes by [Stacks, Tag 0EZP]. -/
theorem isZero_rightDerived_constantZMod_of_isIso {S' X' Y : Scheme.{u}} [IsIntegral S']
    [IsAlgClosed S'.functionField] (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ Spec S'.functionField)
    (sq : IsPullback h e f' (S'.fromSpecStalk (genericPoint S'))) (d q : ℕ) (hq : 0 < q)
    (hiso : IsIso ((higherBaseChangeMapAb f' (S'.fromSpecStalk (genericPoint S')) h e sq.w q).app
      (constantZMod (Spec S'.functionField) d))) :
    IsZero (((smallEtalePushforwardAb h).rightDerived q).obj (constantZMod Y d)) := by
  have h₀ : IsZero (((smallEtalePushforwardAb (S'.fromSpecStalk (genericPoint S'))).rightDerived
      q).obj (constantZMod (Spec S'.functionField) d)) :=
    isZero_rightDerived_constantZMod_of_isAlgClosed S'.functionField _ d q hq
  have h₁ := (smallEtalePullbackAb f').map_isZero h₀
  have h₂ : IsZero (((smallEtalePushforwardAb h).rightDerived q).obj
      ((smallEtalePullbackAb e).obj (constantZMod (Spec S'.functionField) d))) :=
    h₁.of_iso (asIso ((higherBaseChangeMapAb f' _ h e sq.w q).app _)).symm
  exact h₂.of_iso (((smallEtalePushforwardAb h).rightDerived q).mapIso
    ((smallEtalePullbackAbConstantIso e).app _)).symm

/-! ### The application of Stacks 0F1D -/

/-- **The assertion the last paragraph of the proof of [Stacks, Tag 0F1I] establishes**, for
`f : X ⟶ S` and `n`. For every diagram

```
X  ←-p-  X'  ←-h-  Y
|f       |f'       |e
S  ←-s-  S'  ←---  Spec K(S')
```

with both squares cartesian, `S'` affine, integral and normal with algebraically closed function
field `K(S')`, the bottom right arrow the canonical morphism, and every `d ∣ n`, the base change
map `(f')⁻¹R^q(Spec K(S') ⟶ S')_*ℤ/dℤ ⟶ R^q h_*e⁻¹ℤ/dℤ` is an isomorphism for every `q > 0`.
These are the diagrams of [Stacks, Tag 0F1D],
`Stacks.EtaleCohomology.FirstFailureFunctionField.FunctionFieldFailure`. -/
def FunctionFieldBaseChange {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) : Prop :=
  ∀ ⦃S' X' Y : Scheme.{u}⦄ (_ : IsAffine S') (_ : IsIntegral S') (_ : IsNormalDomain Γ(S', ⊤))
    (_ : IsAlgClosed S'.functionField) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_ : IsPullback p f' f s) (h : Y ⟶ X') (e : Y ⟶ Spec S'.functionField)
    (sq : IsPullback h e f' (S'.fromSpecStalk (genericPoint S'))) (d : ℕ), (d : ℤ) ∣ n →
    ∀ q : ℕ, 0 < q →
      IsIso ((higherBaseChangeMapAb f' (S'.fromSpecStalk (genericPoint S')) h e sq.w q).app
        (constantZMod (Spec S'.functionField) d))

/-- **[Stacks, Tag 0F1I], the application of [Stacks, Tag 0F1D].** Let `n` be invertible on `S`.
If `BC(f, n, 0)` holds and base change holds in the diagrams of [Stacks, Tag 0F1D] for the
constant sheaves `ℤ/dℤ`, `d ∣ n`, then `BC(f, n, q)` holds for every `q`.

Otherwise let `q + 1` be the first degree in which `BC(f, n, ·)` fails. [Stacks, Tag 0F1D] gives a
diagram of the kind `FunctionFieldBaseChange` is about, with `R^{q+1}h_*ℤ/dℤ` nonzero for some
`d ∣ n`; but the base change map in degree `q + 1` is an isomorphism, so `R^{q+1}h_*ℤ/dℤ`
vanishes by [Stacks, Tag 0EZP]. Tag 0F1D is
`Stacks.EtaleCohomology.FirstFailureFunctionField.functionFieldFailure_of_firstFailure`, which
takes [Stacks, Tag 0F08] (`hFirstFailure`) and [Stacks, Tag 0F09] (`hSmoothLimitBaseChange`), the
latter for [Stacks, Tag 0F0B] (2). -/
theorem baseChangeHolds_of_functionFieldBaseChange {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ)
    (hn : IsUnit (n : Γ(S, ⊤)))
    (hFirstFailure : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ),
      BaseChangeHolds f n (q : ℤ) → ¬ BaseChangeHolds f n ((q : ℤ) + 1) →
        NormalFailureDiagram f n (q + 1))
    (hSmoothLimitBaseChange : SmoothLimitBaseChange.{u})
    (hDegreeZero : BaseChangeHolds f n 0) (hFunctionField : FunctionFieldBaseChange f n)
    (q : ℕ) : BaseChangeHolds f n q := by
  induction q with
  | zero => exact hDegreeZero
  | succ q ih =>
    by_contra hfail
    rw [Nat.cast_succ] at hfail
    obtain ⟨S', X', Y, haff, hint, hnorm, hcl, s, p, f', hp, h, e, sq, d, hd, hNZ⟩ :=
      functionFieldFailure_of_firstFailure f n q hn ih hfail hFirstFailure hSmoothLimitBaseChange
    exact hNZ (isZero_rightDerived_constantZMod_of_isIso f' h e sq d (q + 1) q.succ_pos
      (hFunctionField haff hint hnorm hcl s p f' hp h e sq d hd (q + 1) q.succ_pos))

/-! ### The assembly -/

/-- **[Stacks, Tag 0F1I] for a sheaf annihilated by `n`, from the steps not proved here.** Let `K`
be a field, `X` a scheme over `K`, `n` an integer invertible in `K`, `X_{K̄} = Spec K̄ ×_K X` the
base change to an algebraic closure and `Z` the reduction of `X_{K̄}`. Granted
[Stacks, Tag 0F09] (`hSmoothLimitBaseChange`) and [Stacks, Tag 0F08] (`hFirstFailure`), if
`BC(Z ⟶ Spec K̄, n, 0)` holds (`hDegreeZero`, where the source applies [Stacks, Tag 0EYS]) and
base change holds in the diagrams of
[Stacks, Tag 0F1D] over `Z ⟶ Spec K̄` (`hFunctionField`, the last paragraph of the source's
proof), then for every diagram over `X ⟶ Spec K` as in Tag 0F1I and every abelian sheaf on
`T_étale` annihilated by `n` the base change map `(f')⁻¹Rg_*𝓕 ⟶ Rh_*e⁻¹𝓕` is an isomorphism.

The proof is the source's second and third paragraphs: replace `K` by `K̄`
(`derivedBaseChangeHolds_of_baseChange`), replace `X_{K̄}` by its reduction
(`derivedBaseChangeHolds_of_universalHomeomorphism`), and apply [Stacks, Tag 0F1D]
(`baseChangeHolds_of_functionFieldBaseChange`). -/
theorem derivedBaseChangeHolds_of_reduction (hSmoothLimitBaseChange : SmoothLimitBaseChange.{u})
    (hFirstFailure : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ),
      BaseChangeHolds f n (q : ℤ) → ¬ BaseChangeHolds f n ((q : ℤ) + 1) →
        NormalFailureDiagram f n (q + 1))
    (K : Type u) [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (n : ℤ)
    (hn : IsUnit (n : K))
    (hDegreeZero : BaseChangeHolds
      ((pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
        sX).nilradical.subschemeι ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) sX)
      n 0)
    (hFunctionField : FunctionFieldBaseChange
      ((pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
        sX).nilradical.subschemeι ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) sX)
      n) :
    DerivedBaseChangeHolds sX n := by
  have hn' : IsUnit (n : Γ(Spec (CommRingCat.of (AlgebraicClosure K)), ⊤)) := by
    have : IsUnit (n : AlgebraicClosure K) := by
      simpa using hn.map (algebraMap K (AlgebraicClosure K))
    simpa using IsUnit.map (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).inv.hom this
  have H₁ := (derivedBaseChangeHolds_iff _ n).2 fun q ↦
    baseChangeHolds_of_functionFieldBaseChange _ n hn' hFirstFailure hSmoothLimitBaseChange
      hDegreeZero
      hFunctionField q
  have H₂ := derivedBaseChangeHolds_of_universalHomeomorphism _ _ n H₁
  exact derivedBaseChangeHolds_of_baseChange hSmoothLimitBaseChange K (AlgebraicClosure K) sX n
    hn H₂

end Stacks.EtaleCohomology.BaseChangeOverField

end

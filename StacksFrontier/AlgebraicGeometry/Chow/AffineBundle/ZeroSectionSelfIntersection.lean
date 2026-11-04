module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMultiplication
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionGysin
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic

/-!
# The self-intersection of the zero section of a line bundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module and let

  `p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X`

be the associated line bundle, with zero section `o : X ⟶ L`. Clause (6) of [Stacks, Tag 0F96]
asserts that

  `o^* o_* : \CH_k(X) ⟶ \CH_{k - 1}(X)`  is equal to the map  `α ↦ - c₁(ℒ) ∩ α`.

The source's proof is one line: it "follows from Lemma 42.30.3 and the fact that
`o^* p^* ℒ = ℒ`". Lemma 42.30.3 is [Stacks, Tag 0F95], the self-intersection formula
`i^* i_* β = c₁(𝒩|_{o(X)}) ∩ β` for the divisor `i : o(X) ⟶ L` and the invertible module `𝒩` on
`L` cutting it out.

## Where the minus sign comes from

The module cutting out `o(X)` is the one clause (1) names: `𝒩 = p^*(ℒ^{⊗ -1})`, the pullback of
the **inverse** of `ℒ`, carried here by `Stacks.LineBundle.Situation.basePullbackInverse`. So the
self-intersection formula produces the first Chern class of

  `𝒩|_{o(X)} = o^* p^* (ℒ^{⊗ -1}) = ℒ^{⊗ -1}`,

and `c₁(ℒ^{⊗ -1}) ∩ α = - (c₁(ℒ) ∩ α)` by [Stacks, Tag 02SP], which is
`Stacks.Chow.firstChernClassCapOfInvertible_eq_neg_of_tensorObj_iso_unit`. That is the only
source of the sign, and it is the first Chern class of `Stacks.LineBundle.Situation.baseInverse`,
the module `ℒ^{⊗ -1}` on `X` itself — not of `(p^*ℒ)^{⊗ -1}`, which is the isomorphic but
distinct module `Stacks.LineBundle.Situation.pullbackInverse`.

## The restriction of the module, with no pullback of the zero section

The identification `𝒩|_{o(X)} = ℒ^{⊗ -1}` is read here on the divisor rather than on `X`. The
divisor is `o(X)`, whose structure morphism `o(X) ⟶ X` is the isomorphism
`Stacks.LineBundle.Situation.zeroSectionDivisorIso` of clause (3); call it `e`, so that
`e = i ≫ p` by construction. Then

  `i^* 𝒩 = i^* p^* (ℒ^{⊗ -1}) = (i ≫ p)^* (ℒ^{⊗ -1}) = e^* (ℒ^{⊗ -1})`,

which is `AlgebraicGeometry.Scheme.Modules.pullbackComp` and nothing else: no identification of
`o` with `e⁻¹ ≫ i` is needed on the module side, and `e = i ≫ p` holds by `rfl`. The transport
of the cap product from the divisor to `X` is then [Stacks, Tag 02SU] for a closed immersion,
`Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible`, which is unconditional here.

The factorization of `o` through the divisor *is* needed on the cycle side, to split `o_*` as
`i_* ∘ (e⁻¹)_*`; it is
`Stacks.LineBundle.Situation.zeroSectionDivisorIso_inv_comp_subschemeι` below, proved from
`IsClosedImmersion.lift` for the zero section and the equality of `o(X)` with the zero scheme of
the tautological section.

## Degrees

No transport of degrees appears anywhere. The source writes the composite as
`\CH_k(X) ⟶ \CH_{k-1}(X)`; here `o_*` is taken in degree `k + 1` and `o^*` consumes `k + 1` and
produces `k`, which is the grading in which both maps are already stated — `o_*` is
`Stacks.Chow.zeroSectionChowPushforward` in any degree and `o^*` is
`Stacks.Chow.zeroSectionGysinChow`, graded `\CH_{k+1}(L) ⟶ \CH_k(X)`. So the degree the
conclusion drops is absorbed by the grading of `o^*`, exactly as in
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι`, and no `eqToHom` or
`Eq.rec` at an equality of degrees is written down.

## The right-hand side on a cycle representative

`c₁(ℒ) ∩ -` descends to Chow groups only through [Stacks, Tag 02TI], which this repository
carries as the hypothesis `Stacks.Chow.FirstChernClassCapFactorsThroughRationalEquivalence`. The
clause is therefore stated with the cap product of [Stacks, Tag 02SO] evaluated on a cycle
representative, `Stacks.Chow.firstChernClassCapOfInvertible`, exactly as [Stacks, Tag 0F95] is
stated in `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersectionFormula`. Both maps of the
composite `o^* o_*` are the genuine maps on Chow groups of clauses (2) and (3); only the right
hand side reads its argument through a representative, and since every class is the class of a
cycle that determines `o^* o_*` completely —
`Stacks.Chow.zeroSectionGysinChow_comp_zeroSectionChowPushforward` says so as an equality of
homomorphisms. The literal Chow-group phrasing of the source, with the descended operation of
Stacks 02TI on the right, is
`Stacks.Chow.zeroSectionGysinChow_comp_zeroSectionChowPushforward_eq_neg_firstChernClassCapOnChow`,
which takes that vanishing as its only hypothesis.

## Main definitions

* `Stacks.LineBundle.Situation.baseInverse` — the inverse `ℒ^{⊗ -1}` of the line bundle, on `X`.
* `Stacks.LineBundle.Situation.tensorBaseInverseUnitIso` — the identification
  `ℒ ⊗_{𝒪_X} ℒ^{⊗ -1} ≅ 𝒪_X` exhibiting it as the tensor inverse.
* `Stacks.LineBundle.Situation.pullbackSubschemeιBasePullbackInverseIso` — the identification
  `i^* 𝒩 ≅ e^* (ℒ^{⊗ -1})` of the restriction of the module of clause (1) to the divisor.

## Main results

* `Stacks.LineBundle.Situation.zeroSectionDivisorIso_inv_comp_subschemeι` — the zero section is
  the inclusion of the divisor read through `e : o(X) ≅ X`. Its companion
  `Stacks.LineBundle.Situation.zeroSectionDivisorIso_hom_comp_zeroSection`, and
  `Stacks.Chow.zeroSectionDivisorIso_inv_comp` used below, are in
  `StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula`, which states
  them through the abbreviation `Stacks.LineBundle.Situation.zeroSectionDivisor` for the same
  zero scheme.
* `Stacks.Chow.zeroSectionGysinChow_zeroSectionChowPushforward_mk` — **clause (6) of
  [Stacks, Tag 0F96]**: `o^* o_* α = - c₁(ℒ) ∩ α`.
* `Stacks.Chow.zeroSectionGysinChow_comp_zeroSectionChowPushforward` — the same clause as the
  equality of homomorphisms the source states.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0F95](https://stacks.math.columbia.edu/tag/0F95)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

/-! ### The inverse of the line bundle, on the base -/

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The inverse `ℒ^{⊗ -1}` of the line bundle of a situation**, as a module on `X` itself. The
module of clause (1) of [Stacks, Tag 0F96] is its pullback to the total space:
`Stacks.LineBundle.Situation.basePullbackInverse_eq`. -/
def Situation.baseInverse : D.X.Modules :=
  _root_.Stacks.SheafOfModules.TensorPower.tensorPower D.X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.X) D.L (-1)

/-- The inverse `ℒ^{⊗ -1}` of the line bundle is an invertible `𝒪_X`-module. -/
instance Situation.isInvertible_baseInverse :
    AlgebraicGeometry.SheafOfModules.IsInvertible D.X.sheaf.obj D.X.ringCatSheaf.property
      D.baseInverse :=
  (inverseSituation D.X D.L).invertible

/-- **The module of clause (1) of [Stacks, Tag 0F96] is the pullback of the inverse of the line
bundle**: `p^*(ℒ^{⊗ -1})`, with the inverse taken on `X`. True by `rfl`; it is how
`Stacks.LineBundle.Situation.basePullbackInverse` is defined. -/
theorem Situation.basePullbackInverse_eq :
    D.basePullbackInverse =
      (Scheme.Modules.pullback D.totalSpaceToBase).obj D.baseInverse :=
  rfl

/-- **The inverse of the line bundle is its tensor inverse**: `ℒ ⊗_{𝒪_X} ℒ^{⊗ -1} ≅ 𝒪_X`. This is
the multiplication law of the tensor powers in degrees `(1, -1)`, the degree-zero power being
the unit on the nose. -/
def Situation.tensorBaseInverseUnitIso :
    Scheme.Modules.tensorObj D.L D.baseInverse ≅ SheafOfModules.unit D.X.ringCatSheaf :=
  _root_.Stacks.SheafOfModules.TensorPower.tensorSheafMapIso D.X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.X)
        (_root_.Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.X) D.L).symm (Iso.refl _) ≪≫
    _root_.Stacks.SheafOfModules.TensorPower.tensorPowerMulIso D.X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.X) D.L 1 (-1)

/-! ### The zero section read through the divisor it cuts out -/

/-- **The inclusion of `o(X)` into the total space factors through the zero section.** The
subscheme `o(X)` is presented as clause (1) of [Stacks, Tag 0F96] presents it, as the zero scheme
of the tautological section of `p^*(ℒ^{⊗ -1})`; that zero scheme is the closed subscheme cut out
by the kernel ideal of the closed immersion `o`
(`Stacks.LineBundle.Situation.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection`), and a
closed immersion with a smaller kernel ideal is factored by
`AlgebraicGeometry.IsClosedImmersion.lift`. -/
theorem Situation.exists_comp_zeroSection_eq_zeroScheme_subschemeι :
    ∃ g : (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subscheme ⟶ D.X,
      g ≫ D.zeroSection =
        (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι := by
  rw [D.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection]
  exact ⟨IsClosedImmersion.lift D.zeroSection D.zeroSection.ker.subschemeι
      (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).ge,
    IsClosedImmersion.lift_fac _ _ _⟩

/-- **The zero section is the inclusion of the divisor `o(X)` read through the isomorphism
`o(X) ≅ X`**: `e⁻¹ ≫ i = o`. This is what splits `o_*` as `i_* ∘ (e⁻¹)_*`. -/
theorem Situation.zeroSectionDivisorIso_inv_comp_subschemeι :
    D.zeroSectionDivisorIso.inv ≫
        (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι = D.zeroSection := by
  rw [← D.zeroSectionDivisorIso_hom_comp_zeroSection, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- **The restriction to `o(X)` of the module of clause (1) is the pullback of `ℒ^{⊗ -1}` along
`o(X) ≅ X`**: `i^* p^* (ℒ^{⊗ -1}) ≅ e^* (ℒ^{⊗ -1})`. This is the pseudofunctoriality of the
module pullback, `AlgebraicGeometry.Scheme.Modules.pullbackComp`, at the factorization
`e = i ≫ p`, which holds by `rfl`. -/
def Situation.pullbackSubschemeιBasePullbackInverseIso :
    (Scheme.Modules.pullback (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subschemeι).obj D.basePullbackInverse ≅
      (Scheme.Modules.pullback D.zeroSectionDivisorIso.hom).obj D.baseInverse :=
  (Scheme.Modules.pullbackComp
    (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
      D.tautologicalSectionBase).subschemeι D.totalSpaceToBase).app D.baseInverse

end Stacks.LineBundle

/-! ### Clause (6) of Stacks 0F96 -/

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- **Stacks 0F96, clause (6).** The Gysin map of the zero section of a line bundle `p : L ⟶ X`
composed with the pushforward along it is intersection with the first Chern class of `ℒ`, with a
minus sign:

  `o^* o_* α = - c₁(ℒ) ∩ α`,

a map `\CH_{k+1}(X) ⟶ \CH_k(X)`.

Both maps of the composite are the maps of clauses (2) and (3),
`Stacks.Chow.zeroSectionChowPushforward` and `Stacks.Chow.zeroSectionGysinChow`, and the only
hypothesis is theirs, that `X` be locally of finite type over `S`. The right hand side is the cap
product of [Stacks, Tag 02SO] on a cycle representative, which is what makes it unconditional;
see the module documentation.

The proof is the source's: the self-intersection formula [Stacks, Tag 0F95] for the divisor
`o(X)` on `L`, whose module is `p^*(ℒ^{⊗ -1})` by clause (1), followed by the identification of
the restriction of that module with `ℒ^{⊗ -1}` and by [Stacks, Tag 02SP] in the form
`c₁(ℒ^{⊗ -1}) ∩ α = -(c₁(ℒ) ∩ α)`, which is where the sign comes from. -/
@[stacks 0F96 "part (6)", sga "5 VII 9.2" "special case"]
theorem zeroSectionGysinChow_zeroSectionChowPushforward_mk (k : ℤ)
    (α : CycleGroup C sX (k + 1)) :
    zeroSectionGysinChow C D sX k
        (zeroSectionChowPushforward C D sX (k + 1)
          (QuotientAddGroup.mk' (rationalEquivalences C sX (k + 1)) α)) =
      -firstChernClassCapOfInvertible C sX k D.L α := by
  -- the pushforward of `α` to the divisor along `X ≅ o(X)`
  set β := properPushforward C sX
      ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX)
      D.zeroSectionDivisorIso.inv (zeroSectionDivisorIso_inv_comp C D sX) (k + 1) α with hβ
  -- `o_*` splits as `i_*` after `(e⁻¹)_*`
  have hsplit : properPushforward C sX (D.totalSpaceToBase ≫ sX) D.zeroSection
        (zeroSection_comp_totalSpaceToBase_comp C D sX) (k + 1) α =
      properPushforward C
        ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX)
        (D.totalSpaceToBase ≫ sX)
        (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι rfl (k + 1) β := by
    have h := congrFun (properPushforward_comp C sX
      ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX)
      (D.totalSpaceToBase ≫ sX) D.zeroSectionDivisorIso.inv
      (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subschemeι (zeroSectionDivisorIso_inv_comp C D sX) rfl
      (k + 1)) α
    rw [Function.comp_apply] at h
    rw [hβ, h, properPushforward_congr C sX (D.totalSpaceToBase ≫ sX)
      (D.zeroSectionDivisorIso.inv ≫
        (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι) D.zeroSection
      D.zeroSectionDivisorIso_inv_comp_subschemeι _
      (zeroSection_comp_totalSpaceToBase_comp C D sX) (k + 1)]
  -- pushing `β` back along `e` returns `α`
  have hid : properPushforward C
        ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX) sX
        D.zeroSectionDivisorIso.hom (zeroSectionDivisorIso_hom_comp C D sX) (k + 1) β = α := by
    have h := congrFun (properPushforward_comp C sX
      ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX) sX
      D.zeroSectionDivisorIso.inv D.zeroSectionDivisorIso.hom
      (zeroSectionDivisorIso_inv_comp C D sX) (zeroSectionDivisorIso_hom_comp C D sX) (k + 1)) α
    rw [Function.comp_apply] at h
    rw [hβ, h, properPushforward_congr C sX sX
      (D.zeroSectionDivisorIso.inv ≫ D.zeroSectionDivisorIso.hom) (𝟙 D.X)
      D.zeroSectionDivisorIso.inv_hom_id _ (Category.id_comp sX) (k + 1), properPushforward_id]
  -- the self-intersection formula, and the two identifications of the module
  rw [zeroSectionChowPushforward_mk, hsplit, zeroSectionGysinChow_mk,
    gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι C (D.totalSpaceToBase ≫ sX) k
      D.basePullbackInverse D.tautologicalSectionBase β,
    firstChernClassCapOfInvertible_congr C
      ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX) k
      ((Scheme.Modules.pullback
        (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι).obj D.basePullbackInverse)
      ((Scheme.Modules.pullback D.zeroSectionDivisorIso.hom).obj D.baseInverse)
      D.pullbackSubschemeιBasePullbackInverseIso β,
    show chowPushforwardOfIso C
        ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX) sX
        D.zeroSectionDivisorIso.hom (zeroSectionDivisorIso_hom_comp C D sX) k =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX) sX
        D.zeroSectionDivisorIso.hom (zeroSectionDivisorIso_hom_comp C D sX) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          D.zeroSectionDivisorIso.hom C
          ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
            D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX) sX
          (zeroSectionDivisorIso_hom_comp C D sX) k) from rfl,
    properChowPushforward_firstChernClassCapOfInvertible C
      ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX) sX
      D.zeroSectionDivisorIso.hom (zeroSectionDivisorIso_hom_comp C D sX) k D.baseInverse β,
    hid]
  exact firstChernClassCapOfInvertible_eq_neg_of_tensorObj_iso_unit C sX k D.L D.baseInverse
    D.tensorBaseInverseUnitIso α

/-- **Stacks 0F96, clause (6).** The source's phrasing: the composite

  `o^* o_* : \CH_{k+1}(X) ⟶ \CH_k(X)`

*is* the map `α ↦ - c₁(ℒ) ∩ α`, as an equality of homomorphisms read on cycle representatives.
Every Chow class is the class of a cycle, so this and
`Stacks.Chow.zeroSectionGysinChow_zeroSectionChowPushforward_mk` are interchangeable. -/
@[stacks 0F96 "part (6)"]
theorem zeroSectionGysinChow_comp_zeroSectionChowPushforward (k : ℤ) :
    ((zeroSectionGysinChow C D sX k).comp
          (zeroSectionChowPushforward C D sX (k + 1))).comp
        (QuotientAddGroup.mk' (rationalEquivalences C sX (k + 1))) =
      -firstChernClassCapOfInvertible C sX k D.L :=
  AddMonoidHom.ext fun α ↦
    zeroSectionGysinChow_zeroSectionChowPushforward_mk C D sX k α

/-- **Stacks 0F96, clause (6), on Chow groups.** Granting the vanishing of [Stacks, Tag 02TI]
that lets `c₁(ℒ) ∩ -` descend to Chow groups, the composite

  `o^* o_* : \CH_{k+1}(X) ⟶ \CH_k(X)`

is the negative of the descended operation `Stacks.Chow.firstChernClassCapOnChow`. This is the
source's statement verbatim; the vanishing is the hypothesis Stacks 02TI is carried as in this
repository, and `Stacks.Chow.zeroSectionGysinChow_comp_zeroSectionChowPushforward` is the same
identity without it. -/
theorem zeroSectionGysinChow_comp_zeroSectionChowPushforward_eq_neg_firstChernClassCapOnChow
    (k : ℤ) (h : FirstChernClassCapFactorsThroughRationalEquivalence C sX k
      (firstChernComponentCycleRule C sX k D.L)) :
    (zeroSectionGysinChow C D sX k).comp (zeroSectionChowPushforward C D sX (k + 1)) =
      -firstChernClassCapOnChow C sX k (firstChernComponentCycleRule C sX k D.L) h := by
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun α ↦ ?_)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.neg_apply,
    firstChernClassCapOnChow_mk]
  exact zeroSectionGysinChow_zeroSectionChowPushforward_mk C D sX k α

end Stacks.Chow

end

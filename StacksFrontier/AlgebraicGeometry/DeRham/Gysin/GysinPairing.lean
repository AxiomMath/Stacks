module

public import StacksFrontier.AlgebraicGeometry.DeRham.Cohomology.DegreeZeroCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.Cohomology.SupportClassPairing
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinProjection
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassSpellings
import StacksCore.Tactic.StacksAttribute

/-!
# The wedge pairing with the local cohomology sheaf, and the Gysin projection formula

Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c = d + 1` cut out
the closed subset `Z`, and let `p` be an integer. This file assembles the two inputs of
[Stacks, Tag 0G88] — the **wedge pairing**

`Ω^p_{X/S} × ℋ^c_Z(Ω^c_{X/S}) ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})`

and the **cup product with a degree-zero class** — and proves the tag in **every cohomological
degree `q`**, for a closed subscheme cut out by that **global** family of equations: for
`α ∈ H^q(X, Ω^p_{X/S})`,

`γ^p(α|_Z) = α ∪ γ^0(1)` in `H^q(X, i_*ℋ^c_Z(Ω^{p+c}_{X/S}))`.

**The global family is a restriction of generality, and this file is only that case.**
[Stacks, Tag 0G88] is stated in the setting of [Stacks, Tag 0G86], where `Z` is only *locally*
cut out by `c` equations and `γ^p` is the glued map
`Stacks.DeRham.CohomologicalGysin.conormalGysinHom`. The tag is proved at that generality by
`Stacks.Gysin.conormalGysin_formRestriction_cupDegreeZero` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ConormalWedgeProjectionRank.lean`, which is where
`@[stacks 0G88]` sits; nothing in this file is registered against the tag. The implementation
notes below say which pairing the general case uses instead of this file's.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formSupportWedgePair`: the wedge pairing, the pairing of
  `StacksFrontier/AlgebraicGeometry/DeRham/Cohomology/SupportClassPairing.lean` at the
  multiplication of the sheaf of graded algebras `Ω^•_{X/S}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.rightMulHom_formSupportWedgePair`: **wedging with `γ^0(1)` is
  the Gysin formula map.** This is the identity of morphisms of sheaves
  `Ω^p_{X/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})` of which the tag is the degree-`q` cohomology.
* `AlgebraicGeometry.Scheme.Hom.cupDegreeZero_supportedGysinUnitClass`: the cup product with
  `γ^0(1)` is `H^q` of the Gysin formula map, in every degree `q`.
* `AlgebraicGeometry.Scheme.Hom.gysin_formRestriction_cupDegreeZero`: **[Stacks, Tag 0G88] for a
  global family of equations**, for any `γ` characterised by the Gysin formula of
  [Stacks, Tag 0G83] of that family.
* `AlgebraicGeometry.Scheme.Hom`
  `.formRestriction_comp_gysinMap_comp_supportCohomologyToPushforward_inv`: the Gysin map of
  [Stacks, Tag 0G83] satisfies that characterisation, in the presentation of the local cohomology
  sheaf the pairing is stated in.
* `AlgebraicGeometry.Scheme.Hom.gysinMap_formRestriction_cupDegreeZero`: **[Stacks, Tag 0G88] for
  a global family of equations, with nothing assumed** — the previous two combined, so that the
  only hypothesis is the one of [Stacks, Tag 0G83], that the equations cut out `Z`.

## Implementation notes

**Why the general case of [Stacks, Tag 0G86] uses a different pairing.** The left-hand side
`γ^p(α|_Z)` is available there: `Stacks.DeRham.CohomologicalGysin.conormalGysinHom` is the glued
`γ^p`, and its composite with `formRestriction` is a morphism of sheaves whose `H^q` is the
left-hand side. The right-hand side cannot be the one built here: the pairing used here is
`Stacks.Perfect.CechPairing.supportPair`, descended from the pairing on the terms of the extended
alternating Čech complex of `f₁, …, f_c`, so it exists only for a global family. What the general
case uses in its place is the equation-free pairing

`Ω^p_{X/S} × i_*ℋ^c_Z(Ω^c_{X/S}) ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`,

that is the multiplication of Cohomology, Remark [Stacks, Tag 0G75] at the generality of
[Stacks, Tag 0G86]. That is `Stacks.Gysin.conormalWedgePair` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ConormalWedgePair.lean`, glued over the equation
charts from `Stacks.Gysin.conormalWedgeVal`, in which no family of equations occurs. For a
*global* first argument the pairing used here is already equation-free — that is
`rightMulHom_flip_formSupportWedgePair`, which identifies it with `i_*ℋ^c_Z` applied to left
multiplication — but a `Stacks.BilinearMap` is a family of maps on the sections over every open,
which is why the general pairing had to be glued rather than read off this one. The two pairings
are nowhere identified, and the general theorem does not quote the statements below: it re-runs
the chart-level argument over an open of an equation chart.

**Why the closed subset is the zero locus itself.** The pairing is built by descending the
Čech-term pairing past the identification of the cokernel of the last differential with
`i_*ℋ^c_T`, and that identification is invertible exactly when `T` is the common zero locus of
the equations (`Stacks.Perfect.SupportedFraction.isIso_cokernelLastDifToSupport`). That is the
`Z` of the tag, so nothing is lost; the statements below carry both inclusions rather than
only `equationsClosedSet f ⊆ T`.

**Why the right-hand side is canonical.** A pairing built from a chosen family of equations
could in principle depend on the family. It does not, on the arguments the tag uses:
`AlgebraicGeometry.Scheme.Hom.rightMulHom_flip_formSupportWedgePair` identifies the pairing
with a *global* first argument `ω` with `i_*ℋ^c_Z` applied to left multiplication by `ω`, the
canonical functorial action of the wedge morphism `Ω^c_{X/S} ⟶ Ω^{p+c}_{X/S}`, which mentions
no equations at all. That statement also subsumes the degree-zero case
`AlgebraicGeometry.Scheme.Hom.supportedGysinFormulaHom_sectionsMap`.

## References

* [Stacks Project, Tag 0G88](https://stacks.math.columbia.edu/tag/0G88)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G75](https://stacks.math.columbia.edu/tag/0G75)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.CechDerivedSupport Stacks.Perfect.SupportedFraction
open Stacks.Perfect.CechPairing
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S Z : Scheme.{u}} {d : ℕ}

attribute [local instance] isQuasicoherent_relativeDifferentialForms

/-! ### The wedge pairing with the local cohomology sheaf -/

/-- **The wedge pairing `Ω^p_{X/S} × ℋ^c_Z(Ω^c_{X/S}) ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})`**, the second
input of [Stacks, Tag 0G88]: the multiplication of the sheaf of graded algebras of relative
differential forms, paired into the degree-`c` local cohomology sheaf along the equations. -/
def formSupportWedgePair (π : X ⟶ S) (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) (hTsub : T ⊆ equationsClosedSet f) :
    Stacks.BilinearMap (relativeDifferentialForms π (p : ℤ)).val
      (supportCohomologySheaf hT (relativeDifferentialForms π ((d + 1 : ℕ) : ℤ))
        ((d + 1 : ℕ) : ℤ)).val
      (supportCohomologySheaf hT
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ((d + 1 : ℕ) : ℤ)).val :=
  supportPair f ((relativeDifferentialFormsAlgebra π).mul (p : ℤ) ((d + 1 : ℕ) : ℤ))
    hT hTf hTsub

/-- The wedge pairing on a local section of `Ω^p_{X/S}` and the class of a fraction. -/
theorem formSupportWedgePair_supportedFractionSource (π : X ⟶ S)
    (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) (hTsub : T ⊆ equationsClosedSet f) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V))
    (s : Γ(relativeDifferentialForms π ((d + 1 : ℕ) : ℤ), V)) :
    (formSupportWedgePair π f p hT hTf hTsub).app (op V) ω
        ((supportedFractionSource f (relativeDifferentialForms π ((d + 1 : ℕ) : ℤ))
          hT hTf).app V s) =
      (supportedFractionSource f
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) hT hTf).app V
        (((relativeDifferentialFormsAlgebra π).mul (p : ℤ) ((d + 1 : ℕ) : ℤ)).app (op V) ω s) :=
  supportPair_supportedFractionSource f _ hT hTf hTsub V ω s

/-! ### Wedging with the Gysin class of one -/

/-- **Wedging with `γ^0(1)` is the Gysin formula map.** For a local relative `p`-form `ω`,
the wedge of `ω` with the class `d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)` is the class of
`ω ∧ d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)`.

This is the identity of morphisms of sheaves `Ω^p_{X/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})` of which
[Stacks, Tag 0G88] is the degree-`q` cohomology: its left-hand side is the right-hand side of
the tag, read through `Stacks.Cohomology.rightMulHom`, and its right-hand side is the formula
clause of [Stacks, Tag 0G83]. -/
theorem rightMulHom_formSupportWedgePair (π : X ⟶ S) (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ)
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    (hTsub : T ⊆ equationsClosedSet f) :
    Stacks.Cohomology.rightMulHom (formSupportWedgePair π f p hT hTf hTsub)
        (supportedGysinUnitClass π f hT hTf) =
      supportedGysinFormulaHom π f p hT hTf := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun ω => ?_)
  exact formSupportWedgePair_supportedFractionSource π f p hT hTf hTsub V ω
    ((equationsWedge π f).eval (op V))

/-! ### Canonicity: a global first argument -/

/-- Left multiplication by a global relative `p`-form is the morphism `t ↦ ω ∧ t` of the wedge
pairing with its first argument fixed. -/
theorem rightMulHom_flip_mul (π : X ⟶ S) (p q : ℤ)
    (ω : (relativeDifferentialForms π p).sections) :
    Stacks.Cohomology.rightMulHom
        ((relativeDifferentialFormsAlgebra π).mul p q).flip ω =
      formLeftWedgeHom π ω q := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => rfl)

/-- **The wedge pairing with a global first argument is the canonical functorial action.** For
a global relative `p`-form `ω` the pairing with `ω` is `i_*ℋ^c_Z` applied to left
multiplication by `ω`, the morphism `Ω^c_{X/S} ⟶ Ω^{p+c}_{X/S}` — a map in whose construction
no family of equations occurs.

This is what makes the right-hand side of [Stacks, Tag 0G88] canonical: the pairing is built
from the chosen equations `f₁, …, f_c`, and nothing in the construction says that another
family would give the same map, but on the arguments the tag uses it *is* the functorial
action of the wedge morphism. -/
theorem rightMulHom_flip_formSupportWedgePair (π : X ⟶ S) (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ)
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    (hTsub : T ⊆ equationsClosedSet f)
    (ω : (relativeDifferentialForms π (p : ℤ)).sections) :
    Stacks.Cohomology.rightMulHom (formSupportWedgePair π f p hT hTf hTsub).flip ω =
      supportCohomologySheafMap hT (formLeftWedgeHom π ω ((d + 1 : ℕ) : ℤ))
        ((d + 1 : ℕ) : ℤ) :=
  (rightMulHom_flip_supportPair f _ hT hTf hTsub ω).trans
    (congrArg (fun ψ => supportCohomologySheafMap hT ψ ((d + 1 : ℕ) : ℤ))
      (rightMulHom_flip_mul π (p : ℤ) ((d + 1 : ℕ) : ℤ) ω))

/-- **The degree-zero case, recovered from the pairing.** On a global relative `p`-form the
Gysin formula map is the wedge with `γ^0(1)`, and that wedge is `i_*ℋ^c_Z` applied to left
multiplication by `ω`. This is
`AlgebraicGeometry.Scheme.Hom.supportedGysinFormulaHom_sectionsMap`, the case `q = 0` of
[Stacks, Tag 0G88], derived from the pairing rather than from functoriality of the class map:
the general-`q` statement therefore extends it rather than standing beside it. -/
theorem supportedGysinFormulaHom_sectionsMap_of_pair (π : X ⟶ S) (f : Fin (d + 1) → Γ(X, ⊤))
    (p : ℕ) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    (hTsub : T ⊆ equationsClosedSet f)
    (ω : (relativeDifferentialForms π (p : ℤ)).sections) :
    SheafOfModules.sectionsMap (supportedGysinFormulaHom π f p hT hTf) ω =
      SheafOfModules.sectionsMap
        (supportCohomologySheafMap hT
          (formLeftWedgeHom π ω ((d + 1 : ℕ) : ℤ)) ((d + 1 : ℕ) : ℤ))
        (supportedGysinUnitClass π f hT hTf) := by
  refine Subtype.ext (funext fun V => ?_)
  refine Eq.trans (congrArg
    (fun ψ : relativeDifferentialForms π (p : ℤ) ⟶
        supportCohomologySheaf hT
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ((d + 1 : ℕ) : ℤ) =>
      ψ.val.app V (ω.eval V))
    (rightMulHom_formSupportWedgePair π f p hT hTf hTsub).symm) ?_
  exact congrArg
    (fun ψ : supportCohomologySheaf hT (relativeDifferentialForms π ((d + 1 : ℕ) : ℤ))
          ((d + 1 : ℕ) : ℤ) ⟶
        supportCohomologySheaf hT
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ((d + 1 : ℕ) : ℤ) =>
      ψ.val.app V ((supportedGysinUnitClass π f hT hTf).eval V))
    (rightMulHom_flip_formSupportWedgePair π f p hT hTf hTsub ω)

/-! ### The projection formula in every cohomological degree -/

variable [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf)]

/-- **Cupping with the Gysin class of one is `H^q` of the Gysin formula map**, in every
cohomological degree `q`. -/
theorem cupDegreeZero_supportedGysinUnitClass (π : X ⟶ S) (f : Fin (d + 1) → Γ(X, ⊤))
    (p : ℕ) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    (hTsub : T ⊆ equationsClosedSet f) (q : ℕ) :
    Stacks.Cohomology.cupDegreeZero X.ringCatSheaf (formSupportWedgePair π f p hT hTf hTsub)
        (supportedGysinUnitClass π f hT hTf) q =
      (_root_.Hfunctor X.ringCatSheaf ⊤ q).map
        (supportedGysinFormulaHom π f p hT hTf) :=
  congrArg (_root_.Hfunctor X.ringCatSheaf ⊤ q).map
    (rightMulHom_formSupportWedgePair π f p hT hTf hTsub)

/-- **Stacks Project, Tag 0G88.** Let `γ` be any morphism
`i_*Ω^p_{Z/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})` satisfying the Gysin formula of [Stacks, Tag 0G83] —
that is, whose composite with restriction of forms to `Z` is
`c_{f₁, …, f_c}(- ∧ d f₁ ∧ ⋯ ∧ d f_c)`, the equation that determines the Gysin map. Then in
every cohomological degree `q`, for every class `α ∈ H^q(X, Ω^p_{X/S})`,

`γ^p(α|_Z) = α ∪ γ^0(1)`,

the cup product being with the degree-zero class `γ^0(1)` for the wedge pairing
`formSupportWedgePair`.

The two sides are read as morphisms `H^q(X, Ω^p_{X/S}) ⟶ H^q(X, i_*ℋ^c_Z(Ω^{p+c}_{X/S}))`, so
the statement is the identity for all `α` at once.

**What this does not cover.** The family `f₁, …, f_c` is a *global* family of functions on `X`,
and the support is its common zero locus; [Stacks, Tag 0G88] is stated in the setting of
[Stacks, Tag 0G86], where `Z` is only locally cut out by `c` equations and `γ^p` is glued from the
local families. The tag at that generality is
`Stacks.Gysin.conormalGysin_formRestriction_cupDegreeZero`, which carries `@[stacks 0G88]`; the
implementation notes of this file say why it uses a different pairing from this one.
The instance of this statement at the Gysin map of [Stacks, Tag 0G83] itself, with `hγ` proved
rather than carried, is `gysinMap_formRestriction_cupDegreeZero`. -/
theorem gysin_formRestriction_cupDegreeZero (i : Z ⟶ X) (π : X ⟶ S)
    (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) (hTsub : T ⊆ equationsClosedSet f)
    (γ : (Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) (p : ℤ)) ⟶
      supportCohomologySheaf hT
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ((d + 1 : ℕ) : ℤ))
    (hγ : formRestriction i π (p : ℤ) ≫ γ = supportedGysinFormulaHom π f p hT hTf) (q : ℕ) :
    (_root_.Hfunctor X.ringCatSheaf ⊤ q).map (formRestriction i π (p : ℤ)) ≫
        (_root_.Hfunctor X.ringCatSheaf ⊤ q).map γ =
      Stacks.Cohomology.cupDegreeZero X.ringCatSheaf (formSupportWedgePair π f p hT hTf hTsub)
        (supportedGysinUnitClass π f hT hTf) q := by
  refine Eq.trans ((_root_.Hfunctor X.ringCatSheaf ⊤ q).map_comp
    (formRestriction i π (p : ℤ)) γ).symm ?_
  exact Eq.trans (congrArg (_root_.Hfunctor X.ringCatSheaf ⊤ q).map hγ)
    (cupDegreeZero_supportedGysinUnitClass π f p hT hTf hTsub q).symm

/-! ### The Gysin map of Tag 0G83 satisfies the characterising equation -/

omit [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf)] in
/-- **The Gysin map of [Stacks, Tag 0G83], read in the presentation the pairing uses, satisfies
the Gysin formula.** `AlgebraicGeometry.Scheme.Hom.gysinMap` lands in the presentation
`AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology` of `i_*ℋ^c_Z(Ω^{p+c}_{X/S})`, in which
the cohomology sheaf is taken on the closed subset and pushed forward afterwards; the pairing of
this file uses `Stacks.Perfect.SupportedFraction.supportCohomologySheaf`, where the direct image
comes first. The two are identified by
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward`, and the identification
carries the class map of [Stacks, Tag 0G7Q] of one presentation to the class map of the other, by
`Stacks.Perfect.supportedFractionSource_comp_supportCohomologyToPushforward`.

So the hypothesis `hγ` of `gysin_formRestriction_cupDegreeZero` holds for the Gysin map itself;
it is the equation `AlgebraicGeometry.Scheme.Hom.formRestriction_comp_gysinMap` of
[Stacks, Tag 0G83], transported. -/
theorem formRestriction_comp_gysinMap_comp_supportCohomologyToPushforward_inv (i : Z ⟶ X)
    [IsClosedImmersion i] (π : X ⟶ S) (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ)
    (hcut : Stacks.Gysin.IsCutOutByEquations i f) :
    formRestriction i π (p : ℤ) ≫ gysinMap i π f p hcut ≫
        (Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward f
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv =
      supportedGysinFormulaHom π f p (isClosed_equationsClosedSet f) subset_rfl := by
  have hFFC : formFractionClass π f ((p : ℤ) + ((d + 1 : ℕ) : ℤ)) =
      supportedFractionSource f (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))
          (isClosed_equationsClosedSet f) subset_rfl ≫
        (Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward f
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).hom :=
    (Stacks.Perfect.supportedFractionSource_comp_supportCohomologyToPushforward f
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).symm
  rw [← Category.assoc, formRestriction_comp_gysinMap, gysinFormulaHom, Category.assoc, hFFC,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- **Stacks Project, Tag 0G88 for the Gysin map of [Stacks, Tag 0G83], with nothing assumed.**
Let `π : X ⟶ S` be a morphism of schemes and let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c = d + 1` cut
out the closed subscheme `i : Z ⟶ X`. Then in every cohomological degree `q`

`γ^p(α|_Z) = α ∪ γ^0(1)`,

for `γ^p` the Gysin map `AlgebraicGeometry.Scheme.Hom.gysinMap` of [Stacks, Tag 0G83] of that
family — read in the presentation of the local cohomology sheaf the pairing uses — and `γ^0(1)`
the Gysin class of one.

This is `gysin_formRestriction_cupDegreeZero` with its hypothesis `hγ` discharged by
`formRestriction_comp_gysinMap_comp_supportCohomologyToPushforward_inv`: the only hypothesis left
is `hcut`, which is the hypothesis of [Stacks, Tag 0G83] itself, that the equations cut out `Z`.
The support is the common zero locus of the equations, which is the image of `Z` exactly because
they cut it out, by `Stacks.Gysin.equationsClosedSet_eq_range`.

**This is the global-equations case of the tag, not the general one.** [Stacks, Tag 0G88] is
stated in the setting of [Stacks, Tag 0G86], where `Z` is only *locally* cut out by `c` equations,
and it is proved there by `Stacks.Gysin.conormalGysin_formRestriction_cupDegreeZero`, which
carries `@[stacks 0G88]`. -/
theorem gysinMap_formRestriction_cupDegreeZero (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ) (hcut : Stacks.Gysin.IsCutOutByEquations i f) (q : ℕ) :
    (_root_.Hfunctor X.ringCatSheaf ⊤ q).map (formRestriction i π (p : ℤ)) ≫
        (_root_.Hfunctor X.ringCatSheaf ⊤ q).map
          (gysinMap i π f p hcut ≫
            (Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward f
              (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv) =
      Stacks.Cohomology.cupDegreeZero X.ringCatSheaf
        (formSupportWedgePair π f p (isClosed_equationsClosedSet f) subset_rfl subset_rfl)
        (supportedGysinUnitClass π f (isClosed_equationsClosedSet f) subset_rfl) q :=
  gysin_formRestriction_cupDegreeZero i π f p (isClosed_equationsClosedSet f) subset_rfl
    subset_rfl _
    (formRestriction_comp_gysinMap_comp_supportCohomologyToPushforward_inv i π f p hcut) q

end AlgebraicGeometry.Scheme.Hom

end

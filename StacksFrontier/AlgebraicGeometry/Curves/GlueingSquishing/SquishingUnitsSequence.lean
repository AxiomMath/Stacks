module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingPicard
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule

/-!
# The sheaf sequence attached to the squishing of a tangent vector

Let `k` be an algebraically closed field and let `f : X' ⟶ X` be the squishing of a tangent
vector `ϑ` of an algebraic `k`-scheme `X'`, in the sense of [Stacks, Tag 0C1K]. One of the
clauses of that predicate is a short exact sequence of sheaves of additive groups on `X`

`0 → 𝒪_X → f_*𝒪_{X'} → (k, +)_x → 0`,

whose first arrow is the canonical map from the structure sheaf to the pushforward and whose
second arrow is pinned, on every neighbourhood `U` of the contracted point `x`, to the
coefficient of `ε` of the restriction of a section along `ϑ`. The exactness clauses of
[Stacks, Tag 0C1M] and [Stacks, Tag 0C1N] both consume that sequence, so it is turned here into
a named declaration rather than a conjunct to be destructured at every use.

[Stacks, Tag 0C1N] uses the same sequence with its outer structure sheaves replaced by their
sheaves of units, the quotient map becoming the logarithmic `ε`-derivative: a unit restricting
along `ϑ` to `a + bε`, necessarily with `a ∈ k^*`, is sent to `b / a`. This file transports the
quotient map to that setting, as an honest morphism of sheaves

`f_*𝒪_{X'}^* ⟶ (k, +)_x`

described on every neighbourhood of the contracted point. On a proper reduced `X'` it kills the
global units, which is the injectivity criterion the connecting homomorphism of Tag 0C1N
consumes.

## Main results

* `Stacks.SquishSheafSequence.shortExact_of_isSquishingTangentVector` — the squishing of a
  tangent vector carries a short exact sequence of additive sheaves
  `0 → 𝒪_X → f_*𝒪_{X'} → (k, +)_x → 0` whose quotient map is the coefficient of `ε` along the
  squished vector.
* `Stacks.SquishSheafSequence.epsilonLogDeriv_mul` — the logarithmic `ε`-derivative of a product
  of units is the sum of the logarithmic `ε`-derivatives, so the quotient of the units sequence
  takes values in the *additive* group `(k, +)`.
* `Stacks.SquishSheafSequence.epsilonLogDerivSheafHom` and
  `Stacks.SquishSheafSequence.epsilonLogDerivSheafHom_app` — the quotient map
  `f_*𝒪_{X'}^* ⟶ (k, +)_x` of the units sequence, and its value on the units of the sections over
  any neighbourhood of the contracted point.
* `Stacks.SquishSheafSequence.epsilonLogDeriv_eq_zero_of_isProper_of_isReduced` — on a proper
  reduced `X'` the logarithmic `ε`-derivative of a global unit vanishes.

## Implementation notes

The three sheaves of the additive sequence and its first arrow are named as reducible
abbreviations (`Stacks.SquishSheafSequence.structureAddSheaf`,
`Stacks.SquishSheafSequence.pushforwardAddSheaf` and
`Stacks.SquishSheafSequence.structureToPushforwardAddSheaf`), so that the statement reads as the
sequence of the source instead of as a composite of `sheafCompose` and
`sheafPushforwardContinuous`; being reducible, they unify with the spelling used inside
`AlgebraicGeometry.IsSquishingTangentVector`. The third sheaf is
`AlgebraicGeometry.skyscraperAddSheaf` and the quotient map is pinned by
`AlgebraicGeometry.epsilonCoefficientAt`.

The category of additive sheaves on a scheme is preadditive, hence has zero morphisms, by
instances the elaborator finds unaided, so the vanishing of the composite is stated as `φ ≫ ψ = 0`
and the sequence as a `CategoryTheory.ShortComplex`; `ShortExact` is then the honest conjunction
of monomorphy of the first arrow, epimorphy of the second, and exactness in the middle.

Sections of the additive skyscraper over a neighbourhood of its point are the ground field only
after rewriting the defining `if`. That equality of objects is `skyscraperAddSheaf_obj_eq` and
the resulting reading of a scalar as a section is `skyscraperAddSheafMk`; both quotient maps are
described through the latter. Over an open *missing* the point there is nothing to describe:
`skyscraperAddSheaf_eq_zero` says the only section there is zero.

The restriction of a section along the tangent vector is packaged as the ring homomorphism
`Stacks.SquishSheafSequence.sectionsToDualNumber`, whose `ε`-part is
`AlgebraicGeometry.epsilonCoefficientAt` by definition. Its constant term on a unit is a unit of
`k`, because a ring homomorphism carries units to units and a unit of `k[ε]` has unit constant
term, which is what makes the quotient defining the logarithmic `ε`-derivative legitimate; the
additivity of that derivative is then the formula for the `ε`-part of a product in `k[ε]`.

The sheaves of units are the additively written `Stacks.Cohomology.Generators.unitsSheaf`, so the
units sequence lives in the same category of sheaves of additive groups as the sequence of
Tag 0C1K and has the same skyscraper as its quotient. Its quotient map is obtained from the
stalk-skyscraper adjunction: the logarithmic `ε`-derivative is compatible with restriction, hence
assembles into a map out of the stalk of `f_*𝒪_{X'}^*` at the contracted point, which the
adjunction transposes into a map of sheaves. Its description on sections is read off from
`CategoryTheory.StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk`.

## References

* [Stacks Project, Tag 0C1K](https://stacks.math.columbia.edu/tag/0C1K)
* [Stacks Project, Tag 0C1N](https://stacks.math.columbia.edu/tag/0C1N)
* [Stacks Project, Tag 0C1M](https://stacks.math.columbia.edu/tag/0C1M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.SquishSheafSequence

/-! ### The short exact sequence of additive sheaves -/

/-- The sheaf of additive groups underlying the structure sheaf `𝒪_X`. -/
abbrev structureAddSheaf (X : Scheme.{u}) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj
    X.ringCatSheaf

/-- The sheaf of additive groups underlying the pushforward `f_*𝒪_{X'}`. -/
abbrev pushforwardAddSheaf {X' X : Scheme.{u}} (f : X' ⟶ X) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj
    (((Opens.map f.base).sheafPushforwardContinuous RingCat (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology X')).obj X'.ringCatSheaf)

/-- The canonical map of additive sheaves `𝒪_X ⟶ f_*𝒪_{X'}` attached to a morphism of
schemes. -/
abbrev structureToPushforwardAddSheaf {X' X : Scheme.{u}} (f : X' ⟶ X) :
    structureAddSheaf X ⟶ pushforwardAddSheaf f :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).map
    (Scheme.Hom.toRingCatSheafHom f)

/-- The sections of the additive skyscraper at `x` over an open set containing `x` are the ground
field. -/
theorem skyscraperAddSheaf_obj_eq {k : Type u} [Field k] (X : Scheme.{u}) (x : X) {U : X.Opens}
    (hx : x ∈ U) : (skyscraperAddSheaf (k := k) X x).obj.obj (op U) = AddCommGrpCat.of k :=
  ite_eq_left hx

/-- A scalar, read as a section of the additive skyscraper at `x` over an open set containing
`x`. -/
def skyscraperAddSheafMk {k : Type u} [Field k] (X : Scheme.{u}) (x : X) {U : X.Opens}
    (hx : x ∈ U) (c : k) : (skyscraperAddSheaf (k := k) X x).obj.obj (op U) := by
  simpa only [skyscraperAddSheaf, skyscraperSheaf, skyscraperPresheaf, ite_eq_left hx] using c

/-- Transport of an element of an additive group along an equality of objects is a cast. -/
private theorem addCommGrp_eqToHom_apply {A B : AddCommGrpCat.{u}} (e : A = B) (x : A) :
    (eqToHom e : A ⟶ B) x =
      cast (congrArg (fun C : AddCommGrpCat.{u} => (C : Type u)) e) x := by
  cases e
  rfl

/-- Identifying the sections of the additive skyscraper with the ground field undoes the reading
of a scalar as a section. -/
theorem eqToHom_skyscraperAddSheafMk {k : Type u} [Field k] (X : Scheme.{u}) (x : X)
    {U : X.Opens} (hx : x ∈ U) (c : k) :
    (eqToHom (skyscraperAddSheaf_obj_eq X x hx)) (skyscraperAddSheafMk X x hx c) = c := by
  rw [addCommGrp_eqToHom_apply]
  exact cast_cast _ _ _

/-- Reading a scalar as a section of the additive skyscraper is injective. -/
theorem skyscraperAddSheafMk_injective {k : Type u} [Field k] (X : Scheme.{u}) (x : X)
    {U : X.Opens} (hx : x ∈ U) :
    Function.Injective (skyscraperAddSheafMk (k := k) X x hx) := fun c c' h => by
  rw [← eqToHom_skyscraperAddSheafMk X x hx c, ← eqToHom_skyscraperAddSheafMk X x hx c', h]

/-- The zero scalar is the zero section of the additive skyscraper. -/
theorem skyscraperAddSheafMk_zero {k : Type u} [Field k] (X : Scheme.{u}) (x : X)
    {U : X.Opens} (hx : x ∈ U) : skyscraperAddSheafMk (k := k) X x hx 0 = 0 := by
  apply (ConcreteCategory.bijective_of_isIso
    (eqToHom (skyscraperAddSheaf_obj_eq (k := k) X x hx))).1
  rw [eqToHom_skyscraperAddSheafMk, map_zero]

/-- The additive skyscraper has no sections beyond zero over an open missing its point. -/
theorem skyscraperAddSheaf_eq_zero {k : Type u} [Field k] (X : Scheme.{u}) (x : X)
    (U : X.Opens) (hx : x ∉ U) (s : (skyscraperAddSheaf (k := k) X x).obj.obj (op U)) :
    s = 0 := by
  classical
  have hsub : Subsingleton ((skyscraperAddSheaf (k := k) X x).obj.obj (op U)) := by
    dsimp only [skyscraperAddSheaf, skyscraperSheaf, skyscraperPresheaf]
    rw [ite_eq_right hx]
    exact AddCommGrpCat.subsingleton_of_isZero terminalIsTerminal.isZero
  exact hsub.elim _ _

/-- **The short exact sequence of sheaves attached to the squishing of a tangent vector.**

If `f : X' ⟶ X` squishes the tangent vector `ϑ` of `X'` to the rational point `x` of `X`, then
there is a map of additive sheaves `ψ : f_*𝒪_{X'} ⟶ (k, +)_x` to the additive skyscraper at `x`
for which

`0 → 𝒪_X → f_*𝒪_{X'} → (k, +)_x → 0`

is short exact, and `ψ` is given on every neighbourhood `U` of `x` by the coefficient of `ε` of
the restriction along `ϑ` of a section of `𝒪_{X'}` over `f⁻¹U`. This is the clause of
[Stacks, Tag 0C1K] that the exactness statements of Tags 0C1M and 0C1N consume. -/
@[stacks 0C1K "the short exact sequence of sheaves"]
theorem shortExact_of_isSquishingTangentVector {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ) :
    ∃ (ψ : pushforwardAddSheaf f ⟶ skyscraperAddSheaf (k := k) X
        ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))))
      (hzero : structureToPushforwardAddSheaf f ≫ ψ = 0),
      (ShortComplex.mk (structureToPushforwardAddSheaf f) ψ hzero).ShortExact ∧
        ∀ (U : X.Opens)
          (hx : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ U)
          (s : Γ(X', f ⁻¹ᵁ U)),
          ψ.hom.app (op U) s =
            skyscraperAddSheafMk X ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx
              (epsilonCoefficientAt θ (f ⁻¹ᵁ U) (by exact hx) s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ψ, hzero, hexact, hψ⟩ := h
  exact ⟨ψ, hzero, hexact, hψ⟩

/-! ### The logarithmic `ε`-derivative on units -/

/-- Restriction of a section along a dual-number-valued point whose closed point lies in `U`, as
a ring homomorphism to the dual numbers. Its `ε`-part is
`AlgebraicGeometry.epsilonCoefficientAt`. -/
def sectionsToDualNumber {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) :
    Γ(X, U) →+* DualNumber k :=
  (X.presheaf.germ U _ hθ ≫ Scheme.stalkClosedPointTo θ).hom

/-- The `ε`-coefficient of a section is the `ε`-part of its restriction along the point. -/
theorem snd_sectionsToDualNumber {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) (s : Γ(X, U)) :
    (sectionsToDualNumber θ U hθ s).snd = epsilonCoefficientAt θ U hθ s :=
  rfl

/-- Restriction along a dual-number-valued point is compatible with restriction of sections to a
smaller open set still containing the closed point. -/
theorem sectionsToDualNumber_res {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (hV : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ V) (s : Γ(X, U)) :
    sectionsToDualNumber θ V hV ((X.presheaf.map (homOfLE hVU).op).hom s) =
      sectionsToDualNumber θ U (hVU hV) s := by
  show (X.presheaf.map (homOfLE hVU).op ≫ X.presheaf.germ V _ hV ≫
    Scheme.stalkClosedPointTo θ).hom s = _
  rw [← Category.assoc, X.presheaf.germ_res]
  rfl

/-- The constant term of the restriction of a unit along a dual-number-valued point is nonzero:
a ring homomorphism carries units to units, and a unit of `k[ε]` has unit constant term. -/
theorem fst_sectionsToDualNumber_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) (u : Γ(X, U)ˣ) :
    (sectionsToDualNumber θ U hθ (u : Γ(X, U))).fst ≠ 0 :=
  (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp
    (u.isUnit.map (sectionsToDualNumber θ U hθ))).ne_zero

/-- The **logarithmic `ε`-derivative** of a unit `u` of `Γ(X, U)` along a dual-number-valued
point whose closed point lies in `U`: if `u` restricts to `a + bε`, necessarily with `a ∈ k^*`,
this is `b / a`. It is the arrow to `(k, +)` of the sequence of sheaves of units of
[Stacks, Tag 0C1N], read on sections. -/
def epsilonLogDeriv {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) (u : Γ(X, U)ˣ) : k :=
  (sectionsToDualNumber θ U hθ (u : Γ(X, U))).snd /
    (sectionsToDualNumber θ U hθ (u : Γ(X, U))).fst

/-- The logarithmic `ε`-derivative is the `ε`-coefficient divided by the constant term. -/
theorem epsilonLogDeriv_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) (u : Γ(X, U)ˣ) :
    epsilonLogDeriv θ U hθ u =
      epsilonCoefficientAt θ U hθ (u : Γ(X, U)) /
        (sectionsToDualNumber θ U hθ (u : Γ(X, U))).fst :=
  rfl

/-- The logarithmic `ε`-derivative of `1` vanishes. -/
@[simp]
theorem epsilonLogDeriv_one {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) :
    epsilonLogDeriv θ U hθ 1 = 0 := by
  simp only [epsilonLogDeriv, Units.val_one, map_one, TrivSqZeroExt.snd_one, zero_div]

/-- **The logarithmic `ε`-derivative is additive in the unit.** This is what lets the short exact
sequence of additive sheaves of [Stacks, Tag 0C1K] be transported to a sequence whose outer terms
are sheaves of units while its quotient is still the additive group `(k, +)`. -/
theorem epsilonLogDeriv_mul {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) (u v : Γ(X, U)ˣ) :
    epsilonLogDeriv θ U hθ (u * v) =
      epsilonLogDeriv θ U hθ u + epsilonLogDeriv θ U hθ v := by
  have hu := fst_sectionsToDualNumber_ne_zero θ U hθ u
  have hv := fst_sectionsToDualNumber_ne_zero θ U hθ v
  simp only [epsilonLogDeriv, Units.val_mul, map_mul, TrivSqZeroExt.fst_mul,
    TrivSqZeroExt.snd_mul, op_smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- The logarithmic `ε`-derivative vanishes exactly when the `ε`-coefficient does, the constant
term of a unit being invertible. -/
theorem epsilonLogDeriv_eq_zero_iff {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) (u : Γ(X, U)ˣ) :
    epsilonLogDeriv θ U hθ u = 0 ↔ epsilonCoefficientAt θ U hθ (u : Γ(X, U)) = 0 := by
  rw [epsilonLogDeriv_eq, div_eq_zero_iff, or_iff_left (fst_sectionsToDualNumber_ne_zero θ U hθ u)]

/-- The logarithmic `ε`-derivative is unchanged by restricting a unit to a smaller open set still
containing the closed point of the tangent vector. -/
theorem epsilonLogDeriv_res {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (hV : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ V) (u : Γ(X, U)ˣ) :
    epsilonLogDeriv θ V hV
        (Units.map (X.presheaf.map (homOfLE hVU).op).hom.toMonoidHom u) =
      epsilonLogDeriv θ U (hVU hV) u := by
  exact congrArg (fun z : DualNumber k => z.snd / z.fst)
    (sectionsToDualNumber_res θ hVU hV (u : Γ(X, U)))

/-- The logarithmic `ε`-derivative, as a homomorphism from the additively written group of units
of `Γ(X, U)` to the additive group of the ground field. -/
def epsilonLogDerivAddHom {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) :
    Additive (Γ(X, U)ˣ) →+ k where
  toFun u := epsilonLogDeriv θ U hθ u.toMul
  map_zero' := epsilonLogDeriv_one θ U hθ
  map_add' u v := epsilonLogDeriv_mul θ U hθ u.toMul v.toMul

/-! ### The quotient map of the sequence of sheaves of units -/

/-- The logarithmic `ε`-derivative on the neighbourhoods of the contracted point, as a cocone on
the diagram computing the stalk of `f_*𝒪_{X'}^*` there. -/
def epsilonLogDerivCocone {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') :
    Cocone ((OpenNhds.inclusion
        (f.base (θ.base (IsLocalRing.closedPoint (DualNumber k))))).op ⋙
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
        (Stacks.Cohomology.Generators.unitsSheaf
          X'.toLocallyRingedSpace.toRingedSpace)).presheaf) := by
  refine ⟨AddCommGrpCat.of k, ?_, ?_⟩
  · intro U
    exact AddCommGrpCat.ofHom (epsilonLogDerivAddHom θ (f ⁻¹ᵁ U.unop.1) (by
      change f.base (θ.base (IsLocalRing.closedPoint (DualNumber k))) ∈ U.unop.1
      exact U.unop.2))
  · intro U V inc
    have hpre : f ⁻¹ᵁ V.unop.1 ≤ f ⁻¹ᵁ U.unop.1 := fun z hz => inc.unop.le hz
    have hpt : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ f ⁻¹ᵁ V.unop.1 := V.unop.2
    ext s
    change epsilonLogDeriv θ (f ⁻¹ᵁ V.unop.1) hpt
        (Units.map (X'.presheaf.map (homOfLE hpre).op).hom.toMonoidHom s) =
      epsilonLogDeriv θ (f ⁻¹ᵁ U.unop.1) (hpre hpt) s
    exact epsilonLogDeriv_res θ hpre hpt s

/-- The logarithmic `ε`-derivative on the stalk of `f_*𝒪_{X'}^*` at the contracted point. -/
def epsilonLogDerivStalkMap {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') :
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
        (Stacks.Cohomology.Generators.unitsSheaf
          X'.toLocallyRingedSpace.toRingedSpace)).presheaf.stalk
        ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)))) ⟶ AddCommGrpCat.of k :=
  colimit.desc _ (epsilonLogDerivCocone f θ)

/-- The stalk logarithmic `ε`-derivative computes the logarithmic `ε`-derivative on germs. -/
theorem epsilonLogDerivStalkMap_germ {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') (U : X.Opens)
    (hx : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ U)
    (s : Γ(X', f ⁻¹ᵁ U)ˣ) :
    epsilonLogDerivStalkMap f θ
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
        (Stacks.Cohomology.Generators.unitsSheaf
          X'.toLocallyRingedSpace.toRingedSpace)).presheaf.germ
          U ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx
          (Additive.ofMul s)) = epsilonLogDeriv θ (f ⁻¹ᵁ U) hx s := by
  let F := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
    (Stacks.Cohomology.Generators.unitsSheaf X'.toLocallyRingedSpace.toRingedSpace)
  let J := (OpenNhds.inclusion
    (f.base (θ.base (IsLocalRing.closedPoint (DualNumber k))))).op ⋙ F.presheaf
  show ((colimit.ι J (op ⟨U, hx⟩) ≫ colimit.desc J (epsilonLogDerivCocone f θ))
    (Additive.ofMul s)) = _
  rw [colimit.ι_desc]
  rfl

/-- **The quotient map `f_*𝒪_{X'}^* ⟶ (k, +)_x` of the sequence of sheaves of units** of
[Stacks, Tag 0C1N]: the logarithmic `ε`-derivative along the squished tangent vector, transposed
across the stalk-skyscraper adjunction. -/
def epsilonLogDerivSheafHom {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
        (Stacks.Cohomology.Generators.unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) ⟶
      skyscraperAddSheaf (k := k) X
        ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) := by
  classical
  change (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
      (Stacks.Cohomology.Generators.unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) ⟶
    skyscraperSheaf ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)))
      (AddCommGrpCat.of k)
  exact ⟨StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf _
    (epsilonLogDerivStalkMap f θ)⟩

/-- Composing the quotient map of the units sequence with the identification of the skyscraper's
sections with the ground field gives the germ followed by the stalk logarithmic
`ε`-derivative. -/
private theorem epsilonLogDerivSheafHom_app_comp {k : Type u} [Field k] {X' X : Scheme.{u}}
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X') (U : X.Opens)
    (hx : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) :
    (epsilonLogDerivSheafHom f θ).hom.app (op U) ≫
        eqToHom (skyscraperAddSheaf_obj_eq (k := k) X
          ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx) =
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
          (Stacks.Cohomology.Generators.unitsSheaf
            X'.toLocallyRingedSpace.toRingedSpace)).presheaf.germ U _ hx ≫
        epsilonLogDerivStalkMap f θ := by
  classical
  show (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
      ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)))
      (epsilonLogDerivStalkMap f θ)).app (op U) ≫ _ = _
  have h := StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk
    ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)))
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
      ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)))
      (epsilonLogDerivStalkMap f θ)) U hx
  rw [StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper] at h
  exact h.symm

/-- The quotient map of the units sequence, read through the identification of the skyscraper's
sections with the ground field, is the logarithmic `ε`-derivative. -/
private theorem epsilonLogDerivSheafHom_app_eval {k : Type u} [Field k] {X' X : Scheme.{u}}
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X') (U : X.Opens)
    (hx : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ U)
    (s : Γ(X', f ⁻¹ᵁ U)ˣ) :
    (eqToHom (skyscraperAddSheaf_obj_eq (k := k) X
          ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx))
        ((epsilonLogDerivSheafHom f θ).hom.app (op U) (Additive.ofMul s)) =
      epsilonLogDeriv θ (f ⁻¹ᵁ U) hx s :=
  ((CategoryTheory.comp_apply ((epsilonLogDerivSheafHom f θ).hom.app (op U))
        (eqToHom (skyscraperAddSheaf_obj_eq (k := k) X
          ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx))
        (Additive.ofMul s)).symm.trans
    (congrArg (fun m => (ConcreteCategory.hom m) (Additive.ofMul s))
      (epsilonLogDerivSheafHom_app_comp f θ U hx))).trans
    ((CategoryTheory.comp_apply
        (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
            (Stacks.Cohomology.Generators.unitsSheaf
              X'.toLocallyRingedSpace.toRingedSpace)).presheaf.germ
          U ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx)
        (epsilonLogDerivStalkMap f θ) (Additive.ofMul s)).trans
      (epsilonLogDerivStalkMap_germ f θ U hx s))

/-- **The quotient map of the units sequence is the logarithmic `ε`-derivative** on the units of
the sections over every neighbourhood of the contracted point. -/
@[stacks 0C1N "the quotient map of the sequence of sheaves of units"]
theorem epsilonLogDerivSheafHom_app {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') (U : X.Opens)
    (hx : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ U)
    (s : Γ(X', f ⁻¹ᵁ U)ˣ) :
    (epsilonLogDerivSheafHom f θ).hom.app (op U) (Additive.ofMul s) =
      skyscraperAddSheafMk X ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx
        (epsilonLogDeriv θ (f ⁻¹ᵁ U) hx s) :=
  (ConcreteCategory.bijective_of_isIso (eqToHom (skyscraperAddSheaf_obj_eq (k := k) X _ hx))).1 <|
    (epsilonLogDerivSheafHom_app_eval f θ U hx s).trans (eqToHom_skyscraperAddSheafMk X _ hx _).symm

/-- **On a proper reduced `X'` the logarithmic `ε`-derivative of a global unit vanishes**, so the
arrow to `(k, +)` of the units sequence of [Stacks, Tag 0C1N] kills the global units and the
connecting homomorphism `(k, +) → Pic(X)` is injective. The `ε`-coefficient of every global
section already vanishes, by
`Stacks.SquishPicard.epsilonCoefficientAt_eq_zero_of_isProper_of_isReduced`. -/
@[stacks 0C1N "vanishing of the logarithmic derivative on a proper reduced scheme"]
theorem epsilonLogDeriv_eq_zero_of_isProper_of_isReduced
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    [IsProper (X' ↘ Spec (.of k))] [IsReduced X'] (u : Γ(X', ⊤)ˣ) :
    epsilonLogDeriv θ ⊤ (Opens.mem_top _) u = 0 := by
  rw [epsilonLogDeriv_eq_zero_iff]
  exact Stacks.SquishPicard.epsilonCoefficientAt_unit_eq_zero_of_isProper_of_isReduced f θ h u

end Stacks.SquishSheafSequence

end

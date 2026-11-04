module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointSkyscraperSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreFunctionField

/-!
# The fundamental exact sequence of Stacks 03RI, read on sections

Let `X` be a smooth curve over an algebraically closed field, let `η` be its generic point with
inclusion `j : η ↪ X`, and let `X_0` be its set of closed points with inclusions `i_x`. The
fundamental exact sequence of Stacks 03RI,
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0`,
is obtained in the source by writing down, for an étale `X`-scheme `U`, the sequence of abelian
groups
`0 → Γ(U, 𝒪_U^*) → Γ(η ×_X U, 𝒪^*) → ⨁_{x ∈ X_0} Γ(x ×_X U, 𝐙)`
and reading it as the sequence of sheaves evaluated at `U`. This file constructs that sequence of
abelian groups for an irreducible `U` and proves it is a complex, exact at its left end.

The second map is the order of vanishing. Its `x`-component is a `𝐙`-valued function on the fibre
`x ×_X U = U ×_X Spec κ(x)`, and the function must be locally constant to be a section of
`(i_x)_* 𝐙`: it is, because the fibre is a discrete space, being étale over the one-point space
`Spec κ(x)`. The function is in general *not* constant — the fibre has one point for each point of
`U` over `x`, and the orders of vanishing there differ.

## Main definitions

* `Stacks.EtaleCohomology.etaleGenericFibreOrd`: the order of vanishing at a point of an
  irreducible étale `X`-scheme `U` of an invertible global function on the generic fibre of `U`.
* `Stacks.EtaleCohomology.residueFibreOrd`: the `x`-component of the second map, as a
  homomorphism into the locally constant `𝐙`-valued maps on the fibre `x ×_X U`.
* `Stacks.EtaleCohomology.integerSkyscraperDivisor`: the same component read as a homomorphism
  into the sections of `(i_x)_* 𝐙` over `U`, through the sections description of the constant
  sheaf of Stacks 03P5.
* `Stacks.EtaleCohomology.genericFibreDivisorSections`: **the second map of the fundamental exact
  sequence on sections over an irreducible étale `X`-scheme**, with values in
  `⨁_{x ∈ X_0} ((i_x)_* 𝐙)(U)`.
* `Stacks.EtaleCohomology.directSumOfFiniteSupport`: a dependent family with finite support, as an
  element of the direct sum.

## Main results

* `Stacks.EtaleCohomology.discreteTopology_residueFibre`: the fibre of an étale `X`-scheme over a
  point of `X` is discrete.
* `Stacks.EtaleCohomology.injective_restrict_genericFibre`: **exactness at `Γ(U, 𝒪_U^*)`** — on an
  integral scheme restriction of an invertible global function to the generic fibre is injective.
* `Stacks.EtaleCohomology.finite_support_residueFibreOrd`: the components of the second map are
  nonzero at only finitely many points of `X`, which is what makes their family an element of the
  direct sum.
* `Stacks.EtaleCohomology.genericFibreDivisorSections_restrict_eq_zero`: **the sequence is a
  complex** — an invertible global function on `U` has order of vanishing zero on every fibre.

## Implementation notes

The hypotheses are irreducibility of `X` and integrality, local Noetherianity and Noetherianity
of the space of `U`, rather than the smooth curve of the source: that is what the order of
vanishing uses, and a smooth curve over a field supplies it for a quasi-compact irreducible `U`.

Irreducibility of `U` is the one hypothesis the source does not carry, and it **is** removable:
`Stacks.EtaleCohomology.closedPointDivisorSections`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSections`, is the same
second map over an arbitrary étale `X`-scheme. What is removed is irreducibility of `U`, not the
need for a function field: instead of one function field for the whole of `U`, the order of
vanishing at a point of `U` is taken in an integral open neighbourhood of that point
(`Stacks.EtaleCohomology.genericFibreOrdOfPoint`), and
`Stacks.EtaleCohomology.genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen` is the independence of
the choice. The price is normality of `X`, which is what makes every point of a scheme étale
over `X` have an integral open neighbourhood — an étale scheme over an integral scheme need not
be locally irreducible — and which the smooth curve of Stacks 03RI supplies, a smooth curve over
a field being regular and hence normal. So this file is the irreducible case and
`ClosedPointDivisorSections` the general one; the decomposition into connected components that
the source performs by appealing to its Proposition 59.26.2 is not needed for either.

`Stacks.EtaleCohomology.etaleGenericFibreOrd` repackages
`Stacks.EtaleCohomology.genericFibreOrd` at the structure morphism of an object of the small étale
site. The repackaging is needed because the source of that morphism is `(𝟭 Scheme).obj U.left`,
for which the integrality and Noetherianity hypotheses carried at `U.left` are not found by
instance search; supplying them as instances on the identity functor's value risks a loop in
instance search, since the identity functor's value unifies with its own argument.

The target of the second map is the direct sum of the groups of sections of the summands, not the
group of sections of `⨁_{x ∈ X_0} (i_x)_* 𝐙`: the coproduct of sheaves is the sheafification of
the coproduct of presheaves, and the identification of the two on sections is a separate matter
handled by `Stacks.EtaleCohomology.closedPointDivisorSheaf.homOfPresheafHom`.

Discreteness of the fibre is derived rather than assumed: an étale morphism is locally
quasi-finite by `AlgebraicGeometry.locallyQuasiFinite_of_etale`, so its preimage of a point is a
discrete subset, and over a one-point base that preimage is the whole space.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5): the sections of a
  constant sheaf are the locally constant maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-! ### The fibre of an étale morphism over a point is discrete -/

/-- **A scheme étale over a one-point scheme is discrete.** An étale morphism is locally
quasi-finite, so the preimage of a point is a discrete subset of the source; over a one-point base
that preimage is everything. -/
theorem discreteTopology_of_etale_of_subsingleton {Y S : Scheme.{u}} (g : Y ⟶ S) [Etale g]
    [Subsingleton ↥S] [Nonempty ↥S] : DiscreteTopology ↥Y := by
  have : LocallyQuasiFinite g := (AlgebraicGeometry.locallyQuasiFinite_of_etale g).2
  have h := g.isDiscrete_preimage_singleton (Classical.arbitrary ↥S)
  have he : g.base ⁻¹' {Classical.arbitrary ↥S} = Set.univ := by
    ext y
    simp [Subsingleton.elim (g.base y) (Classical.arbitrary ↥S)]
  rw [he] at h
  exact isDiscrete_univ_iff.mp h

/-- **The fibre `U ×_X Spec κ(x)` of an étale `X`-scheme over a point of `X` is discrete.** It is
étale over `Spec κ(x)`, which is a one-point space.

This is why a `𝐙`-valued function on the fibre is automatically locally constant, hence a section
of `(i_x)_* 𝐙` by the sections description of the constant sheaf of Stacks 03P5. -/
instance discreteTopology_residueFibre {X : Scheme.{u}} (x : X) (U : X.Etale) :
    DiscreteTopology ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).left :=
  have : Subsingleton ↥((Functor.fromPUnit (Spec (X.residueField x))).obj
      ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).right) :=
    inferInstanceAs (Subsingleton ↥(Spec (X.residueField x)))
  have : Nonempty ↥((Functor.fromPUnit (Spec (X.residueField x))).obj
      ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).right) :=
    inferInstanceAs (Nonempty ↥(Spec (X.residueField x)))
  discreteTopology_of_etale_of_subsingleton
    ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).hom

/-- **A point of the fibre `U ×_X Spec κ(x)` lies over `x`.** The two projections agree after
composing with the structure morphisms, and `Spec κ(x) ⟶ X` has image `{x}`. -/
theorem hom_base_pullback_fst_fromSpecResidueField {X : Scheme.{u}} (x : X) (U : X.Etale)
    (y : ↥(pullback U.hom (X.fromSpecResidueField x))) :
    U.hom ((pullback.fst U.hom (X.fromSpecResidueField x)) y) = x := by
  have h := congrArg (fun φ : pullback U.hom (X.fromSpecResidueField x) ⟶ X => φ y)
    (pullback.condition (f := U.hom) (g := X.fromSpecResidueField x))
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at h
  exact h

/-! ### A finitely supported family as an element of a direct sum -/

/-- **A dependent family with finite support, as an element of the direct sum.** -/
def directSumOfFiniteSupport {ι : Type*} {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    (w : ∀ i, β i) (hw : {i | w i ≠ 0}.Finite) : DirectSum ι β :=
  letI : DecidableEq ι := Classical.decEq ι
  DirectSum.mk β hw.toFinset fun i => w i

/-- The component at `i` of `directSumOfFiniteSupport w hw` is `w i`. -/
@[simp]
theorem directSumOfFiniteSupport_apply {ι : Type*} {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    (w : ∀ i, β i) (hw : {i | w i ≠ 0}.Finite) (i : ι) :
    directSumOfFiniteSupport w hw i = w i := by
  classical
  by_cases h : i ∈ hw.toFinset
  · exact DirectSum.mk_apply_of_mem h
  · rw [directSumOfFiniteSupport, DirectSum.mk_apply_of_notMem h]
    exact (not_not.1 fun hi => h (hw.mem_toFinset.2 hi)).symm

/-! ### The order of vanishing on an irreducible étale neighbourhood -/

section Ord

variable {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Etale) [IsIntegral U.left]
  [IsLocallyNoetherian U.left]

private instance {Y : Scheme.{u}} [IsIntegral Y] : IsIntegral ((𝟭 Scheme).obj Y) := ‹_›

private instance {Y : Scheme.{u}} [IsLocallyNoetherian Y] :
    IsLocallyNoetherian ((𝟭 Scheme).obj Y) := ‹_›

private instance {Y : Scheme.{u}} [NoetherianSpace Y] : NoetherianSpace ((𝟭 Scheme).obj Y) := ‹_›

/-- **The order of vanishing at a point of `U` of an invertible global function on the generic
fibre `η ×_X U`**, for `U` an irreducible étale `X`-scheme. This is
`Stacks.EtaleCohomology.genericFibreOrd` at the structure morphism of `U`. -/
def etaleGenericFibreOrd (y : U.left) :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+ ℤ :=
  have : IsIntegral ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsIntegral U.left)
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (IsLocallyNoetherian U.left)
  genericFibreOrd (X := X) U.hom y

/-- **An invertible global function on `U` has order of vanishing zero at every point of `U`.** -/
theorem etaleGenericFibreOrd_restrict_eq_zero (y : U.left) (a : (Γ(U.left, ⊤))ˣ) :
    etaleGenericFibreOrd U y (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 :=
  genericFibreOrd_restrict_eq_zero (X := X) U.hom y a

/-- **The order of vanishing of an invertible global function on the generic fibre is nonzero at
only finitely many points of `U`**: a rational function on `U` has finitely many zeros and
poles. -/
theorem finite_support_etaleGenericFibreOrd [NoetherianSpace U.left]
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    {y : U.left | etaleGenericFibreOrd U y a ≠ 0}.Finite :=
  finite_support_genericFibreOrd (X := X) U.hom a

end Ord

/-! ### The second map of the fundamental exact sequence on sections -/

section Divisor

variable {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Etale) [IsIntegral U.left]
  [IsLocallyNoetherian U.left]

/-- **The `x`-component of the second map of the fundamental exact sequence of Stacks 03RI, on
sections over an irreducible étale `X`-scheme `U`**: an invertible global function on the generic
fibre `η ×_X U` is sent to the `𝐙`-valued map on the fibre `x ×_X U` taking a point of that fibre
to the order of vanishing, at its image in `U`, of the function read as a rational function on
`U`.

The map is locally constant because the fibre is discrete, and it is in general not constant: the
fibre has one point for each point of `U` over `x`, and the orders of vanishing there differ. -/
def residueFibreOrd (x : X) :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      LocallyConstant ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).left
        (ULift.{max (u + 1) v} ℤ) where
  toFun a :=
    ⟨fun y => ULift.up (etaleGenericFibreOrd U
      ((pullback.fst U.hom (X.fromSpecResidueField x)) y) a),
      IsLocallyConstant.of_discrete _⟩
  map_zero' := LocallyConstant.ext fun y => by
    change ULift.up (etaleGenericFibreOrd U _ 0) = _
    rw [map_zero]
    rfl
  map_add' a b := LocallyConstant.ext fun y => by
    change ULift.up (etaleGenericFibreOrd U _ (a + b)) = _
    rw [map_add]
    rfl

/-- The value of `residueFibreOrd U x a` at a point `y` of the fibre is the order of vanishing of
`a` at the image of `y` in `U`. -/
@[simp]
theorem residueFibreOrd_apply (x : X)
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ))
    (y : ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).left) :
    residueFibreOrd.{u, v} U x a y =
      ULift.up (etaleGenericFibreOrd U
        ((pullback.fst U.hom (X.fromSpecResidueField x)) y) a) :=
  rfl

/-- **An invertible global function on `U` has order of vanishing zero on every fibre.** This is
the composite of the first two maps of the fundamental exact sequence of Stacks 03RI being zero,
read on sections over `U`, component by component. -/
theorem residueFibreOrd_restrict_eq_zero (x : X) (a : (Γ(U.left, ⊤))ˣ) :
    residueFibreOrd.{u, v} U x (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 :=
  LocallyConstant.ext fun y => by
    rw [residueFibreOrd_apply, etaleGenericFibreOrd_restrict_eq_zero]
    rfl

/-- **The components of the second map are nonzero at only finitely many points of `X`.** A
rational function on `U` has finitely many zeros and poles, and every point of the fibre over `x`
lies over `x`, so a point of `X` at which the component is nonzero is the image of one of those
finitely many points of `U`.

This is the finiteness that makes the family of components an element of the direct sum
`⨁_{x ∈ X_0} ((i_x)_* 𝐙)(U)`. -/
theorem finite_support_residueFibreOrd [NoetherianSpace U.left]
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    {x : X | residueFibreOrd.{u, v} U x a ≠ 0}.Finite := by
  refine Set.Finite.subset
    ((finite_support_etaleGenericFibreOrd U a).image fun y => U.hom y) ?_
  intro x hx
  obtain ⟨y, hy⟩ : ∃ y, etaleGenericFibreOrd U
      ((pullback.fst U.hom (X.fromSpecResidueField x)) y) a ≠ 0 := by
    by_contra hc
    refine hx (LocallyConstant.ext fun y => ?_)
    rw [residueFibreOrd_apply, not_not.1 fun h => hc ⟨y, h⟩]
    rfl
  exact ⟨_, hy, hom_base_pullback_fst_fromSpecResidueField x U y⟩

/-- **The `x`-component of the second map of Stacks 03RI, as a map into the sections of
`(i_x)_* 𝐙`.** The identification of those sections with the locally constant `𝐙`-valued maps on
the fibre `x ×_X U` is the sections description of the constant sheaf, Stacks 03P5. -/
def integerSkyscraperDivisor (x : X) :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      (integerSkyscraper.{u, v} X x).obj.obj (op U) :=
  ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).inv.hom).comp
    (residueFibreOrd.{u, v} U x)

/-- **An invertible global function on `U` has trivial image in `((i_x)_* 𝐙)(U)`.** -/
theorem integerSkyscraperDivisor_restrict_eq_zero (x : X) (a : (Γ(U.left, ⊤))ˣ) :
    integerSkyscraperDivisor.{u, v} U x (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 := by
  rw [integerSkyscraperDivisor, AddMonoidHom.comp_apply,
    residueFibreOrd_restrict_eq_zero.{u, v} U x a, map_zero]

/-- **Only finitely many points of `X` carry a nonzero component of the second map.** -/
theorem finite_support_integerSkyscraperDivisor [NoetherianSpace U.left]
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    {x : X | integerSkyscraperDivisor.{u, v} U x a ≠ 0}.Finite :=
  (finite_support_residueFibreOrd.{u, v} U a).subset fun x hx hc =>
    hx (by rw [integerSkyscraperDivisor, AddMonoidHom.comp_apply, hc, map_zero])

end Divisor

/-! ### The sequence of Stacks 03RI on sections over an irreducible étale neighbourhood -/

section LeftEnd

variable {X : Scheme.{u}} [IsIntegral X] (U : X.Etale)

/-- **Exactness of the fundamental exact sequence of Stacks 03RI at `Γ(U, 𝒪_U^*)`, read on
sections over an étale `X`-scheme `U`.** On an integral scheme the generic fibre `η ×_X U` is
scheme-theoretically dense in `U`, so an invertible global function on `U` is determined by its
restriction to it.

This is the injectivity of the first map of the sequence
`0 → Γ(U, 𝒪_U^*) → Γ(η ×_X U, 𝒪^*) → ⨁_{x ∈ X_0} Γ(x ×_X U, 𝐙)`
displayed in the proof of the source. -/
@[stacks 03RI "exactness at Γ(U, 𝒪_U^*) of the sequence on sections over an étale X-scheme"]
theorem injective_restrict_genericFibre :
    Function.Injective (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom) := fun _ _ hab =>
  Units.ext (appTop_pullback_fst_injective (genericPointInclusion X) U.hom
    (congrArg Units.val hab))

end LeftEnd

section Sequence

variable {X : Scheme.{u}} [IsIntegral X] (U : X.Etale) [IsIntegral U.left]
  [IsLocallyNoetherian U.left] [NoetherianSpace U.left]

/-- **The second map of the fundamental exact sequence of Stacks 03RI, on sections over an
irreducible étale `X`-scheme `U`**: an invertible global function on the generic fibre `η ×_X U`
is sent to the family of its orders of vanishing, the member at a closed point `x` being the
locally constant `𝐙`-valued map on the fibre `x ×_X U` recording the order of vanishing at each
point of `U` over `x`.

The family has finite support, a rational function having finitely many zeros and poles, so it is
an element of the direct sum `⨁_{x ∈ X_0} ((i_x)_* 𝐙)(U)`, the third term of the sequence
displayed in the proof of the source. -/
@[stacks 03RI "the second map on sections over an irreducible étale X-scheme"]
def genericFibreDivisorSections :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      DirectSum ↥(closedPoints X)
        fun x : closedPoints X => (integerSkyscraper.{u, v} X x.1).obj.obj (op U) where
  toFun a := directSumOfFiniteSupport
    (fun x : closedPoints X => integerSkyscraperDivisor.{u, v} U x.1 a)
    ((finite_support_integerSkyscraperDivisor.{u, v} U a).preimage
      Subtype.val_injective.injOn)
  map_zero' := DFinsupp.ext fun x => by
    rw [directSumOfFiniteSupport_apply, map_zero, DFinsupp.zero_apply]
  map_add' _ _ := DFinsupp.ext fun x => by
    rw [directSumOfFiniteSupport_apply, DFinsupp.add_apply, directSumOfFiniteSupport_apply,
      directSumOfFiniteSupport_apply, map_add]

/-- The component at a closed point `x` of `genericFibreDivisorSections U a` is
`integerSkyscraperDivisor U x a`. -/
@[simp]
theorem genericFibreDivisorSections_apply
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) (x : closedPoints X) :
    genericFibreDivisorSections.{u, v} U a x = integerSkyscraperDivisor.{u, v} U x.1 a :=
  directSumOfFiniteSupport_apply _ _ x

/-- **The sequence of Stacks 03RI is a complex, read on sections over an irreducible étale
`X`-scheme `U`**: an invertible global function on `U` restricts to an invertible function on the
generic fibre with no zeros and no poles, so its family of orders of vanishing is zero.

Together with `Stacks.EtaleCohomology.injective_restrict_genericFibre` this is the sequence
`0 → Γ(U, 𝒪_U^*) → Γ(η ×_X U, 𝒪^*) → ⨁_{x ∈ X_0} Γ(x ×_X U, 𝐙)`
displayed in the proof of the source, exact at its left end and a complex at the middle. -/
@[stacks 03RI "the sequence on sections over an irreducible étale X-scheme is a complex"]
theorem genericFibreDivisorSections_restrict_eq_zero (a : (Γ(U.left, ⊤))ˣ) :
    genericFibreDivisorSections.{u, v} U (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 :=
  DFinsupp.ext fun x => by
    rw [genericFibreDivisorSections_apply.{u, v} U _ x,
      integerSkyscraperDivisor_restrict_eq_zero.{u, v} U x.1 a, DFinsupp.zero_apply]

end Sequence

/-! ### The hypotheses on `U` in the setting of the source -/

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **An étale scheme over a curve is locally Noetherian.** A curve is locally of finite type over
its base field and an étale morphism is locally of finite type, so the composite is, and a scheme
locally of finite type over a field is locally Noetherian.

This discharges the local Noetherianity hypothesis of
`Stacks.EtaleCohomology.genericFibreDivisorSections` in the setting of Stacks 03RI, where `X` is a
smooth curve over an algebraically closed field. -/
theorem isLocallyNoetherian_of_etale_over_isCurve (f : X ⟶ Spec (.of k)) [IsCurve k f]
    (U : X.Etale) : IsLocallyNoetherian U.left :=
  LocallyOfFiniteType.isLocallyNoetherian (U.hom ≫ f)

/-- **A quasi-compact étale scheme over a curve has a Noetherian space.** It is locally Noetherian
by `Stacks.EtaleCohomology.isLocallyNoetherian_of_etale_over_isCurve`, and a locally Noetherian
scheme with a compact space is Noetherian.

This discharges the Noetherianity hypothesis of
`Stacks.EtaleCohomology.genericFibreDivisorSections` in the setting of Stacks 03RI. -/
theorem noetherianSpace_of_etale_over_isCurve (f : X ⟶ Spec (.of k)) [IsCurve k f]
    (U : X.Etale) [CompactSpace U.left] : NoetherianSpace U.left :=
  have : IsLocallyNoetherian U.left := isLocallyNoetherian_of_etale_over_isCurve f U
  have : AlgebraicGeometry.IsNoetherian U.left := AlgebraicGeometry.IsNoetherian.mk
  inferInstance

end Curve

end Stacks.EtaleCohomology

end

module

public import Mathlib.Algebra.Category.Grp.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.PairCrystalCondition
public import StacksFrontier.AlgebraicGeometry.Crystalline.PointedComparisonIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorRestrictionIndependence

/-!
# The descent of `ℱ_T = M ⊗_{D,f} B` to the unpointed crystalline site

The proof of [Stacks, Proposition 60.17.4, Tag 07JH] attaches to an affine object `(U, T, δ)` of
`Cris(X/S)`, with `T = Spec(B)`, the module `ℱ_T = M ⊗_{D,f} B` for a *chosen* divided power map
`f : D → B`, and then argues that the choice does not matter: the comparisons `c_{f,g}` satisfy
`c_{f,f} = 1` and `c_{g,h} ∘ c_{f,g} = c_{f,h}`, "hence these maps are all isomorphisms and we see
that the module `ℱ_T` is independent of the choice of `f`".

Everything in that sentence was in the library, and the conclusion drawn from it was not: the
assignment was functorial only on the **pointed** site `Under Dt`, where the choice is part of the
object, and the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedComparisonIso.lean` records that "the descent
along the forgetful functor from the pointed site to `Cris(X/S)`" is not carried out, naming "a
construction of the quotient" as what is missing.  **This module carries out that descent.**

## The construction

For an object `T` of the unpointed site the descended module is the module of **compatible
families over all pointings**,

`ℱ_T = { (z_f)_{f : D ⟶ B} | c_{f,g}(z_f) = z_g for all f, g }`,

which is `Crystalline.PointedComparisonSystem.descendedSections` — an honest `B`-submodule of the
product, with no choice in its definition.  The cocycle and `c_{f,f} = 1` then say exactly that
evaluation at any one pointing

`ℱ_T ≃ M ⊗_{D,f} B`

is an isomorphism, which is `Crystalline.PointedComparisonSystem.descendedEval`: that *is* the
source's "the module `ℱ_T` is independent of the choice of `f`", with the independence now a
property of an object defined without choosing.  A limit over the pointings rather than a quotient
of their disjoint union, but the same descent — the indexing system is a connected groupoid, so
the two agree.

The restriction map along a morphism `u : T ⟶ T'` of the unpointed site is read through those
isomorphisms: `Crystalline.PointedComparisonSystem.descendedRestrictOf` transports
`Crystalline.pointedRestriction` along a pointing `f` of `T` and a pointing `f'` of `T'` with
`f' = f ∘ u`, which is the source's "choosing `f' = f ∘ a`".  That it does not depend on either
choice is `Crystalline.PointedComparisonSystem.descendedRestrictOf_indep`, and its proof is
`Crystalline.pointedRestriction_pointedComparison` — the verification the source omits —
together with the cocycle.

## The input datum

`Crystalline.PointedComparisonSystem` bundles what the construction consumes, and every field is
either a property of the pair `(M, ∇)` or a structural fact about the fixed object:

* `surjective_toQuotient` — the structural map `C → D/J_D` is surjective, which holds because the
  fixed object is one of `Cris(C/A)` rather than merely of `CRIS(C/A)`;
* `theta` and `isThetaMonomialFamily` — the coordinate operators of the connection and their
  composites `θ_K = ∏_i θ_i^{k_i}`, which item (07JD) supplies;
* `finite_notMem_pPowSmul` — the source's own "the sum is finite!", which
  `Crystalline.finite_thetaPow_notMem_pPowSmul` derives from the quasi-nilpotence condition
  (07JE);
* `Tmap` and `hasSum` — the semilinear Taylor comparison of two pointings of one object, whose
  existence is `Crystalline.exists_hasPointedTaylorSum`.

**No finiteness of the index type `ι` of the coordinates enters anywhere below.**

## Main definitions

* `Crystalline.PointedComparisonSystem` — the input datum above.
* `Crystalline.PointedComparisonSystem.comparison` — the comparison `c_{f,g}` of the system.
* `Crystalline.PointedComparisonSystem.descendedSections` — **the descended module `ℱ_T`**, the
  compatible families over all pointings of `T`.
* `Crystalline.PointedComparisonSystem.descendedEval` — **evaluation at a pointing, as a
  `B`-linear equivalence `ℱ_T ≃ M ⊗_{D,f} B`.**
* `Crystalline.pointedPush` — a morphism of the pointed site out of a pointing of `T` onto a
  prescribed pointing of `T'`, which is `Crystalline.pushPoint` with its target named rather than
  computed; it is what keeps `f ∘ u` out of the *types* below.
* `Crystalline.PointedComparisonSystem.descendedRestrictOf` — **the restriction map
  `ℱ_T → ℱ_{T'}`** of the descended assignment, semilinear over `u`.

## Main results

* `Crystalline.PointedComparisonSystem.comparison_self` and `..._comp` — `c_{f,f} = 1` and the
  cocycle, for the system.
* `Crystalline.PointedComparisonSystem.Tmap_pushedPointedComparisonMap` and
  `..._comparison_naturality` — **the comparison is natural in the object**: the restriction maps
  carry `c_{f,g}` to `c_{f∘u,g∘u}`, with the bottom map identified as the system's own comparison.
* `Crystalline.PointedComparisonSystem.descendedEval_descendedRestrictOf` — the restriction map
  of the descended assignment is `Crystalline.pointedRestriction` read through the evaluations.
* `Crystalline.PointedComparisonSystem.descendedRestrictOf_indep` — **the restriction map does
  not depend on the two chosen pointings.**
* `Crystalline.PointedComparisonSystem.descendedRestrictOf_id` and `..._comp` — **the descended
  assignment is functorial on the unpointed site.**
* `Crystalline.PointedComparisonSystem.descendedMap` and
  `Crystalline.PointedComparisonSystem.descendedMap_descendedRestrictOf` — **the construction is
  functorial in the pair**, the third verification the source omits ("We also omit the proof that
  this procedure is a functor"): a horizontal map of pairs descends and commutes with the
  restriction maps.  Its one input is that the map intertwines the two families of composite
  coordinate operators, which is horizontality read on the `θ_K`.
* `Crystalline.PointedComparisonSystem.span_range_descendedRestrictOf_eq_top` and
  `Crystalline.PointedComparisonSystem.existsUnique_descendedRestrictOf` — **the crystal condition
  for the descended assignment**: the restriction map generates, and `ℱ_{T'}` has the universal
  property of the base change `u^* ℱ_T`, so the canonical map `u^* ℱ_T → ℱ_{T'}` is an
  isomorphism.  These are `Crystalline.span_range_pointedRestriction_eq_top` and
  `Crystalline.existsUnique_pointedRestriction` transported along the evaluations.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
The tag is an equivalence of categories whose source is the crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)`; what is below is the object assignment of its quasi-inverse on
the *algebraic* site `CRIS(C/A)`, with values in modules over the varying section ring rather than
in quasi-coherent sheaves.  Two things separate the two and neither is touched here: the passage
from a `B`-module to a quasi-coherent sheaf on `Spec(B)` and from the affine site to
`Cris(X/S)`, and the functor of [Stacks, Lemma 60.17.3, Tag 07JG] out of that source category,
which `Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsQuasiCoherentToPairs.lean` still carries as a
datum.

What **is** closed is the descent: the three verifications the source omits
(`Crystalline.pointedRestriction_pointedComparison`,
`Crystalline.existsUnique_pointedRestriction` and
`Crystalline.pointedComparison_comp_eq_id`) are now joined into an assignment on the unpointed
site, which is what the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedComparisonIso.lean` and of
`StacksFrontier/AlgebraicGeometry/Crystalline/PairToCrystal.lean` record as absent.

[Stacks, Lemma 60.5.6, Tag 07HP] — the existence of a pointing — is **not** used: an object with
no pointing gets the zero module, and the statements below say what they say for every object.
Composing with that lemma is what makes the descended module nonzero, and that composition is not
performed here.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
-/

@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe u uI v w w'

namespace Crystalline

/-! ### A morphism of the pointed site onto a prescribed pointing -/

section Push

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X X' : DividedPowerThickening.{u, v, w} S}

/-- **A pointing pushed onto a prescribed pointing of the target.**  For a morphism `u : T ⟶ T'`
of thickenings, a pointing `f` of `T` and a pointing `f'` of `T'` with `f' = f ∘ u`, this is the
morphism `(T, f) ⟶ (T', f')` of the pointed site.

It is `Crystalline.pushPoint` with its target named instead of computed, which is what keeps the
composite `f ∘ u` out of the *types* of the statements below: `Crystalline.descendedRestrictOf`
would otherwise be a map whose type mentions `f ≫ u`, and the functoriality laws could not be
stated without transporting along `Category.assoc`. -/
abbrev pointedPush (f : Dt ⟶ X) (u : X ⟶ X') (f' : Dt ⟶ X') (hf : f ≫ u = f') :
    pointedOfHom f ⟶ pointedOfHom f' :=
  Under.homMk u hf

/-- At the computed target the pushed pointing is `Crystalline.pushPoint`. -/
theorem pointedPush_rfl (f : Dt ⟶ X) (u : X ⟶ X') :
    pointedPush f u (f ≫ u) rfl = pushPoint f u := rfl

/-- The ring map of the pushed pointing `pointedPush f u f' hf` is the ring map of `u`. -/
@[simp] theorem pointedHomRingHom_pointedPush (f : Dt ⟶ X) (u : X ⟶ X') (f' : Dt ⟶ X')
    (hf : f ≫ u = f') (b : X.ring.carrier) :
    pointedHomRingHom (pointedPush f u f' hf) b = u.hom b := rfl

/-- The pushed pointings compose: pushing along `u` and then along `v` is pushing along
`u ≫ v`. -/
theorem pointedPush_comp {X'' : DividedPowerThickening.{u, v, w} S} (f : Dt ⟶ X) (u : X ⟶ X')
    (f' : Dt ⟶ X') (hf : f ≫ u = f') (v : X' ⟶ X'') (f'' : Dt ⟶ X'')
    (hf' : f' ≫ v = f'') (hf'' : f ≫ (u ≫ v) = f'') :
    pointedPush f u f' hf ≫ pointedPush f' v f'' hf' = pointedPush f (u ≫ v) f'' hf'' := rfl

/-- Pushing along the identity is the identity. -/
theorem pointedPush_id (f : Dt ⟶ X) (hf : f ≫ 𝟙 X = f) :
    pointedPush f (𝟙 X) f hf = 𝟙 (pointedOfHom f) := rfl

end Push

/-! ### The system of Taylor comparisons -/

section System

variable {S : AffineCrystallineSituation.{u, v}} (Dt : DividedPowerThickening.{u, v, w} S)
  (M : Type w) [AddCommGroup M] [Module Dt.ring.carrier M] {ι : Type uI}
  (thetaPow : (ι →₀ ℕ) → (M → M)) (x : ι → Dt.ring.carrier)

/-- **The system of Taylor comparisons of a pair `(M, ∇)` over the pointed crystalline site.**

This is the whole input of the descent below.  The first four fields are the data and properties
of the pair and of the fixed object that the Taylor series of
[Stacks, Proposition 60.17.4, Tag 07JH] is built from; the last two are the comparison itself, one
semilinear map for each ordered pair of pointings of each object, together with the statement that
it carries the tag's series `∑_K ξ_{f,g}^{[K]} ⊗ θ_K(m)`.

Its existence at one pair of pointings is `Crystalline.exists_hasPointedTaylorSum`, so a term of
this structure is a choice of that map for every pair, and nothing more.  No finiteness of `ι`
is asked for. -/
structure PointedComparisonSystem where
  /-- The structural map `C → D/J_D` of the fixed object is surjective, which holds because that
  object is one of `Cris(C/A)`.  It is what makes two pointings of an object agree modulo the
  divided power ideal, `Crystalline.sub_pointRingHom_mem_ideal`. -/
  surjective_toQuotient : Function.Surjective Dt.toQuotient
  /-- The coordinate operators `θ_i` of the connection of the pair. -/
  theta : ι → (M → M)
  /-- The composite coordinate operators are `θ_K = ∏_i θ_i^{k_i}`, which item (07JD) of
  [Stacks, Tag 07JD] supplies through `Crystalline.exists_isThetaMonomialFamily`. -/
  isThetaMonomialFamily : IsThetaMonomialFamily M theta thetaPow
  /-- The source's own "the sum is finite!": at every exponent only finitely many composite
  operators take `m` outside `p^N M`.  This is what
  `Crystalline.finite_thetaPow_notMem_pPowSmul` derives from the quasi-nilpotence condition
  (07JE) of [Stacks, Tag 07JE]. -/
  finite_notMem_pPowSmul : ∀ (N : ℕ) (m : M),
    {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul S.p Dt.ring.carrier M N}.Finite
  /-- The semilinear Taylor comparison of two pointings of one object, whose existence is
  `Crystalline.exists_hasPointedTaylorSum`. -/
  Tmap : ∀ {X : DividedPowerThickening.{u, v, w} S} (f g : Dt ⟶ X),
    M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g)
  /-- The chosen map carries the Taylor series of the tag. -/
  hasSum : ∀ {X : DividedPowerThickening.{u, v, w} S} (f g : Dt ⟶ X) (m : M),
    HasPointedTaylorSum M S.p thetaPow g (pointedDiff f g x) m (Tmap f g m)

end System

/-! ### The datum is inhabited under the source's own hypotheses -/

section Inhabited

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  (M : Type w) [AddCommGroup M] [Module Dt.ring.carrier M] {ι : Type uI} [DecidableEq ι]
  {thetaPow : (ι →₀ ℕ) → (M → M)} {theta : ι → (M → M)}
  {delta : ι → (Dt.ring.carrier → Dt.ring.carrier)}
  {deltaPow : (ι →₀ ℕ) → (Dt.ring.carrier → Dt.ring.carrier)} (x : ι → Dt.ring.carrier)

omit [DecidableEq ι] in
/-- **The Taylor comparison of two pointings of any object exists**, from the hypotheses of
`Crystalline.exists_hasPointedTaylorSum` with the nilpotence of `p` discharged by
[Stacks, Tag 07HM]: it is part of the definition of a divided power thickening and not an
assumption.  This is the field `Tmap` of `Crystalline.PointedComparisonSystem` at one pair of
pointings. -/
theorem exists_pointedTaylorSum_of_taylorFormula
    (hDt : Function.Surjective Dt.toQuotient)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily Dt.ring.carrier delta deltaPow)
    (hthAdd : ∀ (i : ι) (y z : M), theta i (y + z) = theta i y + theta i z)
    (hleib : ∀ (i : ι) (a : Dt.ring.carrier) (m : M),
      theta i (a • m) = a • theta i m + delta i a • m)
    (hfin : ∀ (N : ℕ) (m : M),
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul S.p Dt.ring.carrier M N}.Finite)
    {X : DividedPowerThickening.{u, v, w} S} (f g : Dt ⟶ X)
    (htay : ∀ a : Dt.ring.carrier, ∃ t : Finset (ι →₀ ℕ),
      (pointRingHom (pointedOfHom f) a = ∑ J ∈ t,
          pointRingHom (pointedOfHom g) (deltaPow J a) *
            taylorMonomial X.ring (pointedDiff f g x) J) ∧
        ∀ J ∉ t, pointRingHom (pointedOfHom g) (deltaPow J a) *
          taylorMonomial X.ring (pointedDiff f g x) J = 0) :
    ∃ T : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g),
      ∀ m : M, HasPointedTaylorSum M S.p thetaPow g (pointedDiff f g x) m (T m) := by
  classical
  obtain ⟨N, hN⟩ := X.prime_nilpotent
  exact exists_hasPointedTaylorSum M S.p hDt f g x hfamM hfamD hthAdd hleib hN htay (hfin N)

/-- **The input datum of the descent is inhabited under the source's own hypotheses.**

Nothing in `Crystalline.PointedComparisonSystem` is an assumption beyond what the proof of
[Stacks, Proposition 60.17.4, Tag 07JH] has in hand at that point: the coordinate operators of the
connection with their composites, the Leibniz rule relating them to the operators `∂_i` of `D`,
the source's own "the sum is finite!", and Taylor's formula in the section ring of each object —
which is what `Crystalline.taylorFormula_polynomial` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorFormulaMonomials.lean` proves for the divided
power polynomial algebra.

So the descent below is not a statement about an empty structure, and the hypotheses it rests on
are named here rather than carried silently. -/
noncomputable def PointedComparisonSystem.ofTaylorFormula
    (hDt : Function.Surjective Dt.toQuotient)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily Dt.ring.carrier delta deltaPow)
    (hthAdd : ∀ (i : ι) (y z : M), theta i (y + z) = theta i y + theta i z)
    (hleib : ∀ (i : ι) (a : Dt.ring.carrier) (m : M),
      theta i (a • m) = a • theta i m + delta i a • m)
    (hfin : ∀ (N : ℕ) (m : M),
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul S.p Dt.ring.carrier M N}.Finite)
    (htay : ∀ {X : DividedPowerThickening.{u, v, w} S} (f g : Dt ⟶ X) (a : Dt.ring.carrier),
      ∃ t : Finset (ι →₀ ℕ),
      (pointRingHom (pointedOfHom f) a = ∑ J ∈ t,
          pointRingHom (pointedOfHom g) (deltaPow J a) *
            taylorMonomial X.ring (pointedDiff f g x) J) ∧
        ∀ J ∉ t, pointRingHom (pointedOfHom g) (deltaPow J a) *
          taylorMonomial X.ring (pointedDiff f g x) J = 0) :
    PointedComparisonSystem Dt M thetaPow x where
  surjective_toQuotient := hDt
  theta := theta
  isThetaMonomialFamily := hfamM
  finite_notMem_pPowSmul := hfin
  Tmap f g := (exists_pointedTaylorSum_of_taylorFormula M x hDt hfamM hfamD hthAdd hleib hfin
    f g (htay f g)).choose
  hasSum f g := (exists_pointedTaylorSum_of_taylorFormula M x hDt hfamM hfamD hthAdd hleib hfin
    f g (htay f g)).choose_spec

end Inhabited

section Descent

variable {S : AffineCrystallineSituation.{u, v}}

/-- **The objects of `CRIS(C/A)` that admit a pointing**, the full subcategory on which the descent
below is a functor with nonzero values.  [Stacks, Lemma 60.5.6, Tag 07HP] is the statement that
every object of the crystalline site admits one at a sufficiently large level, so this subcategory
is where that lemma places the source's objects; it is named rather than assumed, and nothing below
reproves it. -/
abbrev PointableThickening (Dt : DividedPowerThickening.{u, v, w} S) :=
  ObjectProperty.FullSubcategory
    (fun X : DividedPowerThickening.{u, v, w} S ↦ Nonempty (Dt ⟶ X))

namespace PointedComparisonSystem

variable {Dt : DividedPowerThickening.{u, v, w} S}
  {M : Type w} [AddCommGroup M] [Module Dt.ring.carrier M] {ι : Type uI} [DecidableEq ι]
  {thetaPow : (ι →₀ ℕ) → (M → M)} {x : ι → Dt.ring.carrier}
  (C : PointedComparisonSystem Dt M thetaPow x)
  {X X' X'' : DividedPowerThickening.{u, v, w} S}

/-- **The comparison `c_{f,g} : M ⊗_{D,f} B ⟶ M ⊗_{D,g} B` of the system**, that is
`Crystalline.pointedComparison` of its chosen semilinear map. -/
noncomputable def comparison (f g : Dt ⟶ X) :
    pointedSections M (pointedOfHom f) →ₗ[X.ring.carrier] pointedSections M (pointedOfHom g) :=
  pointedComparison M f g (C.Tmap f g)

omit [DecidableEq ι] in
/-- The comparison sends `b ⊗ m` to `b • Tmap f g m`. -/
@[simp] theorem comparison_tmul (f g : Dt ⟶ X)
    (b : TwistedScalars (pointRingHom (pointedOfHom f))) (m : M) :
    C.comparison f g (b ⊗ₜ[Dt.ring.carrier] m) = b.val • C.Tmap f g m := rfl

omit [DecidableEq ι] in
/-- The comparison sends `1 ⊗ m` to `Tmap f g m`. -/
@[simp] theorem comparison_one_tmul (f g : Dt ⟶ X) (m : M) :
    C.comparison f g ((1 : TwistedScalars (pointRingHom (pointedOfHom f)))
      ⊗ₜ[Dt.ring.carrier] m) = C.Tmap f g m :=
  pointedComparison_one_tmul M f g (C.Tmap f g) m

omit [DecidableEq ι] in
/-- **At one pointing the chosen map is the degree-zero comparison `m ↦ 1 ⊗ m`.**  Both carry the
Taylor series of the vanishing family `ξ_{f,f} = 0` — the system's own by its field `hasSum`, and
`Crystalline.pointedUnitComparison` by
`Crystalline.hasPointedTaylorSum_pointedUnitComparison` — and the sum of a Taylor series is
unique. -/
theorem Tmap_self (f : Dt ⟶ X) : C.Tmap f f = pointedUnitComparison M f := by
  obtain ⟨N, hN⟩ := X.prime_nilpotent
  refine LinearMap.ext fun m ↦ ?_
  let := pointedAlgebra f
  exact hasTaylorSum_unique S.p Dt.ring X.ring M thetaPow hN (pointedDiff f f x) m _ _
    (C.hasSum f f m)
    (hasPointedTaylorSum_pointedUnitComparison M S.p f x C.isThetaMonomialFamily.1 m)

omit [DecidableEq ι] in
/-- **`c_{f,f} = 1`**, the source's "It is also true that `c_{f,f} = 1`", for the system. -/
@[simp] theorem comparison_self (f : Dt ⟶ X) : C.comparison f f = LinearMap.id := by
  rw [comparison, C.Tmap_self f, pointedComparison_self]

omit [DecidableEq ι] in
/-- **The cocycle `c_{g,h} ∘ c_{f,g} = c_{f,h}`** for the system, by
`Crystalline.pointedComparison_comp_eq`.  Nilpotence of `p` in the object is not a hypothesis but
part of the definition of a divided power thickening, [Stacks, Tag 07HM]. -/
theorem comparison_comp (f g h : Dt ⟶ X) :
    (C.comparison g h).comp (C.comparison f g) = C.comparison f h := by
  classical
  obtain ⟨N, hN⟩ := X.prime_nilpotent
  exact pointedComparison_comp_eq M S.p C.surjective_toQuotient f g h x
    C.isThetaMonomialFamily hN (C.Tmap f g) (C.Tmap g h) (C.Tmap f h) (C.hasSum f g)
    (C.hasSum g h) (C.hasSum f h) (C.finite_notMem_pPowSmul N)

omit [DecidableEq ι] in
/-- The cocycle `c_{g,h} ∘ c_{f,g} = c_{f,h}`, evaluated at an element. -/
theorem comparison_comparison (f g h : Dt ⟶ X) (z : pointedSections M (pointedOfHom f)) :
    C.comparison g h (C.comparison f g z) = C.comparison f h z :=
  congrArg (fun c ↦ c z) (C.comparison_comp f g h)

omit [DecidableEq ι] in
/-- **The comparisons of the system are bijective.**  Both composites are the identity, by the
cocycle at `h = f` and `c_{f,f} = 1`. -/
theorem bijective_comparison (f g : Dt ⟶ X) : Function.Bijective (C.comparison f g) := by
  refine ⟨Function.LeftInverse.injective (g := C.comparison g f) fun z ↦ ?_,
    Function.RightInverse.surjective (g := C.comparison g f) fun z ↦ ?_⟩
  · rw [C.comparison_comparison f g f, C.comparison_self f, LinearMap.id_apply]
  · rw [C.comparison_comparison g f g, C.comparison_self g, LinearMap.id_apply]

/-- A property failing only on a finite set holds outside any finset containing that set. -/
private theorem forall_notMem_of_finite_toFinset_subset {α : Type*} {q : α → Prop}
    (hfin : {L | ¬ q L}.Finite) {s : Finset α} (hs : hfin.toFinset ⊆ s) (K : α) : K ∉ s → q K :=
  fun hK ↦ not_not.mp fun hc ↦ hK (hs (hfin.mem_toFinset.mpr hc))

omit [DecidableEq ι] in
/-- **The chosen map pushed along a morphism of thickenings is the chosen map of the pushed
pointings.**

`Crystalline.hasPointedTaylorSum_pointedRestriction` says that the pushed datum
`Crystalline.pushedPointedComparisonMap` carries the Taylor series of the pushed differences
`ξ_{f∘u,g∘u}`; the system's own map at the pushed pointings carries the same series; and the sum
of a Taylor series is unique.  The two nilpotence exponents of the two objects are taken at their
maximum, which costs nothing. -/
theorem Tmap_pushedPointedComparisonMap (f g : Dt ⟶ X) (u : X ⟶ X') :
    pushedPointedComparisonMap M f g u (C.Tmap f g) = C.Tmap (f ≫ u) (g ≫ u) := by
  obtain ⟨N₁, hN₁⟩ := X.prime_nilpotent
  obtain ⟨N₂, hN₂⟩ := X'.prime_nilpotent
  have hX : ((S.p : X.ring.carrier)) ^ max N₁ N₂ = 0 :=
    pow_eq_zero_of_le (le_max_left _ _) hN₁
  have hX' : ((S.p : X'.ring.carrier)) ^ max N₁ N₂ = 0 :=
    pow_eq_zero_of_le (le_max_right _ _) hN₂
  refine LinearMap.ext fun m ↦ ?_
  have hfin := C.finite_notMem_pPowSmul (max N₁ N₂) m
  let := pointedAlgebra (g ≫ u)
  exact hasTaylorSum_unique S.p Dt.ring X'.ring M thetaPow hX'
    (pointedDiff (f ≫ u) (g ≫ u) x) m _ _
    (hasPointedTaylorSum_pointedRestriction M S.p thetaPow C.surjective_toQuotient f g u x
      hX hX' m hfin.toFinset (forall_notMem_of_finite_toFinset_subset hfin subset_rfl)
      (C.hasSum f g m))
    (C.hasSum (f ≫ u) (g ≫ u) m)

omit [DecidableEq ι] in
/-- **The comparison is natural in the object of the site**, with the bottom map identified as the
system's own comparison of the pushed pointings: the square

```
M ⊗_{D,f} B   --- c_{f,g} --->   M ⊗_{D,g} B
     |                                |
     u                                u
     v                                v
M ⊗_{D,f'} B' - c_{f',g'} ->    M ⊗_{D,g'} B'
```

commutes, for prescribed pointings `f' = f ∘ u` and `g' = g ∘ u` of the target.  This is the
verification the source omits, `Crystalline.pointedRestriction_pointedComparison`, with
`Crystalline.PointedComparisonSystem.Tmap_pushedPointedComparisonMap` naming the bottom map. -/
theorem comparison_naturality (f g : Dt ⟶ X) (u : X ⟶ X') (f' g' : Dt ⟶ X')
    (hf : f ≫ u = f') (hg : g ≫ u = g') (z : pointedSections M (pointedOfHom f)) :
    pointedRestriction M (pointedPush g u g' hg) (C.comparison f g z) =
      C.comparison f' g' (pointedRestriction M (pointedPush f u f' hf) z) := by
  subst hf
  subst hg
  rw [comparison, comparison, ← C.Tmap_pushedPointedComparisonMap f g u]
  exact pointedRestriction_pointedComparison M f g u (C.Tmap f g) z

/-! ### The descended module -/

/-- **The descended module `ℱ_T` of [Stacks, Proposition 60.17.4, Tag 07JH]**: the compatible
families `(z_f)` over *all* pointings `f : D ⟶ B` of the object, a `B`-submodule of their
product.

No pointing is chosen, so the module depends on nothing but the object, which is the source's
"the module `ℱ_T` is independent of the choice of `f`" made into a definition; that it agrees with
`M ⊗_{D,f} B` for every pointing `f` is
`Crystalline.PointedComparisonSystem.descendedEval`.  An object with no pointing gets the zero
module. -/
def descendedSections (X : DividedPowerThickening.{u, v, w} S) :
    Submodule X.ring.carrier (∀ f : Dt ⟶ X, pointedSections M (pointedOfHom f)) where
  carrier := {z | ∀ f g : Dt ⟶ X, C.comparison f g (z f) = z g}
  add_mem' {z z'} hz hz' := fun f g ↦ by
    change C.comparison f g (z f + z' f) = z g + z' g
    rw [map_add, hz f g, hz' f g]
  zero_mem' := fun f g ↦ by
    change C.comparison f g 0 = 0
    rw [map_zero]
  smul_mem' b z hz := fun f g ↦ by
    change C.comparison f g (b • z f) = b • z g
    rw [map_smul, hz f g]

omit [DecidableEq ι] in
/-- A family `z` lies in the descended module if and only if `c_{f,g}(z_f) = z_g` for all
pointings `f` and `g`. -/
@[simp] theorem mem_descendedSections_iff
    {z : ∀ f : Dt ⟶ X, pointedSections M (pointedOfHom f)} :
    z ∈ C.descendedSections X ↔ ∀ f g : Dt ⟶ X, C.comparison f g (z f) = z g :=
  Iff.rfl

/-- **Evaluation at a pointing is an isomorphism `ℱ_T ≃ M ⊗_{D,f} B`.**

This is the conclusion of the paragraph of the proof of
[Stacks, Proposition 60.17.4, Tag 07JH] that ends "hence these maps are all isomorphisms and we
see that the module `ℱ_T` is independent of the choice of `f`": the inverse sends `z` to the
family `g ↦ c_{f,g}(z)`, which is compatible by the cocycle, and the two round trips are the
cocycle again and `c_{f,f} = 1`. -/
noncomputable def descendedEval (f : Dt ⟶ X) :
    ↥(C.descendedSections X) ≃ₗ[X.ring.carrier] pointedSections M (pointedOfHom f) where
  toFun z := z.val f
  map_add' z z' := rfl
  map_smul' b z := rfl
  invFun z := ⟨fun g ↦ C.comparison f g z, fun g h ↦ C.comparison_comparison f g h z⟩
  left_inv z := Subtype.ext (funext fun g ↦ z.property f g)
  right_inv z := by
    change C.comparison f f z = z
    rw [C.comparison_self f, LinearMap.id_apply]

omit [DecidableEq ι] in
/-- Evaluation at `f` sends a compatible family `z` to its component `z_f`. -/
@[simp] theorem descendedEval_apply (f : Dt ⟶ X) (z : ↥(C.descendedSections X)) :
    C.descendedEval f z = z.val f := rfl

omit [DecidableEq ι] in
/-- The inverse of evaluation at `f` sends `z` to the family `g ↦ c_{f,g}(z)`. -/
@[simp] theorem descendedEval_symm_apply (f g : Dt ⟶ X)
    (z : pointedSections M (pointedOfHom f)) :
    ((C.descendedEval f).symm z).val g = C.comparison f g z := rfl

omit [DecidableEq ι] in
/-- **The evaluations at two pointings differ by the comparison.**  This is the statement that
`Crystalline.PointedComparisonSystem.descendedEval` realises the whole family of comparisons at
once. -/
theorem comparison_descendedEval (f g : Dt ⟶ X) (z : ↥(C.descendedSections X)) :
    C.comparison f g (C.descendedEval f z) = C.descendedEval g z :=
  z.property f g

/-! ### The restriction maps of the descended assignment -/

/-- **The restriction map `ℱ_T → ℱ_{T'}` of the descended assignment**, read through the
evaluations at a pointing `f` of `T` and the pointing `f' = f ∘ u` of `T'` it pushes to.  This is
the source's "If `a : (U', T', δ') → (U, T, δ)` is a morphism of affine objects of `Cris(X/S)`,
then choosing `f' = f ∘ a` ...".

It is semilinear over the ring map underlying `u`, which is what it means for the comparison
`u^* ℱ_T → ℱ_{T'}` to be a map of `𝒪_{T'}`-modules.  That it does not depend on the two chosen
pointings is `Crystalline.PointedComparisonSystem.descendedRestrictOf_indep`. -/
noncomputable def descendedRestrictOf (u : X ⟶ X') (f : Dt ⟶ X) (f' : Dt ⟶ X')
    (hf : f ≫ u = f') :
    ↥(C.descendedSections X) →ₛₗ[u.hom.toRingHom] ↥(C.descendedSections X') where
  toFun z := (C.descendedEval f').symm
    (pointedRestriction M (pointedPush f u f' hf) (C.descendedEval f z))
  map_add' z z' := by
    change (C.descendedEval f').symm (pointedRestriction M (pointedPush f u f' hf)
        (C.descendedEval f (z + z'))) = _
    rw [map_add, map_add, map_add]
  map_smul' b z := by
    change (C.descendedEval f').symm (pointedRestriction M (pointedPush f u f' hf)
        (C.descendedEval f (b • z))) = _
    rw [map_smul, pointedRestriction_smul, pointedHomRingHom_pointedPush, map_smul]
    rfl

omit [DecidableEq ι] in
/-- The restriction map of the descended assignment is
`Crystalline.pointedRestriction` read through the evaluations. -/
@[simp] theorem descendedEval_descendedRestrictOf (u : X ⟶ X') (f : Dt ⟶ X) (f' : Dt ⟶ X')
    (hf : f ≫ u = f') (z : ↥(C.descendedSections X)) :
    C.descendedEval f' (C.descendedRestrictOf u f f' hf z) =
      pointedRestriction M (pointedPush f u f' hf) (C.descendedEval f z) :=
  (C.descendedEval f').apply_symm_apply _

omit [DecidableEq ι] in
/-- **The restriction map does not depend on the two chosen pointings**, which is the second of
the three verifications the source omits — "We omit the verification that this map is independent
of the choice of `f`".

The proof is `Crystalline.PointedComparisonSystem.comparison_naturality`, the naturality square, and
the cocycle: evaluating both maps at the second choice of target pointing turns one into the
other. -/
theorem descendedRestrictOf_indep (u : X ⟶ X') (f₁ : Dt ⟶ X) (f₁' : Dt ⟶ X')
    (hf₁ : f₁ ≫ u = f₁') (f₂ : Dt ⟶ X) (f₂' : Dt ⟶ X') (hf₂ : f₂ ≫ u = f₂')
    (z : ↥(C.descendedSections X)) :
    C.descendedRestrictOf u f₁ f₁' hf₁ z = C.descendedRestrictOf u f₂ f₂' hf₂ z := by
  refine (C.descendedEval f₂').injective ?_
  rw [C.descendedEval_descendedRestrictOf u f₂ f₂' hf₂,
    ← C.comparison_descendedEval f₁' f₂' (C.descendedRestrictOf u f₁ f₁' hf₁ z),
    C.descendedEval_descendedRestrictOf u f₁ f₁' hf₁, descendedEval_apply, descendedEval_apply,
    ← z.property f₁ f₂, C.comparison_naturality f₁ f₂ u f₁' f₂' hf₁ hf₂]

omit [DecidableEq ι] in
/-- **The restriction map along the identity is the identity**, the first functoriality law of the
descended assignment. -/
theorem descendedRestrictOf_id (f : Dt ⟶ X) (hf : f ≫ 𝟙 X = f)
    (z : ↥(C.descendedSections X)) : C.descendedRestrictOf (𝟙 X) f f hf z = z := by
  refine (C.descendedEval f).injective ?_
  rw [C.descendedEval_descendedRestrictOf (𝟙 X) f f hf, pointedPush_id,
    pointedRestriction_id, LinearMap.id_apply]

omit [DecidableEq ι] in
/-- **The restriction maps compose**, the second functoriality law: together with
`Crystalline.PointedComparisonSystem.descendedRestrictOf_id` and
`Crystalline.PointedComparisonSystem.descendedRestrictOf_indep` this is the statement that the
descended assignment is a functor on the unpointed crystalline site `CRIS(C/A)`. -/
theorem descendedRestrictOf_comp (u : X ⟶ X') (v : X' ⟶ X'') (f : Dt ⟶ X) (f' : Dt ⟶ X')
    (hf : f ≫ u = f') (f'' : Dt ⟶ X'') (hf' : f' ≫ v = f'') (hf'' : f ≫ (u ≫ v) = f'')
    (z : ↥(C.descendedSections X)) :
    C.descendedRestrictOf v f' f'' hf' (C.descendedRestrictOf u f f' hf z) =
      C.descendedRestrictOf (u ≫ v) f f'' hf'' z := by
  refine (C.descendedEval f'').injective ?_
  rw [C.descendedEval_descendedRestrictOf v f' f'' hf',
    C.descendedEval_descendedRestrictOf u f f' hf,
    C.descendedEval_descendedRestrictOf (u ≫ v) f f'' hf'',
    ← pointedPush_comp f u f' hf v f'' hf' hf'', pointedRestriction_comp,
    LinearMap.comp_apply]

/-! ### The crystal condition for the descended assignment -/

omit [DecidableEq ι] in
/-- **The surjectivity half of the crystal condition for the descended assignment**: the image of
the restriction map generates `ℱ_{T'}` over `B'`.  This is
`Crystalline.span_range_pointedRestriction_eq_top` transported along the evaluations, and like it
it carries no hypothesis — in particular no flatness. -/
theorem span_range_descendedRestrictOf_eq_top (u : X ⟶ X') (f : Dt ⟶ X) (f' : Dt ⟶ X')
    (hf : f ≫ u = f') :
    Submodule.span X'.ring.carrier
      (Set.range (C.descendedRestrictOf u f f' hf)) = ⊤ := by
  have hrange : Set.range (C.descendedRestrictOf u f f' hf) =
      ((C.descendedEval f').symm.toLinearMap) ''
        Set.range (pointedRestriction M (pointedPush f u f' hf)) := by
    refine Set.ext fun w ↦ ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      refine ⟨pointedRestriction M (pointedPush f u f' hf) (C.descendedEval f z), ⟨_, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, ← C.descendedEval_descendedRestrictOf u f f' hf,
        LinearEquiv.symm_apply_apply]
    · rintro ⟨y, ⟨y', rfl⟩, rfl⟩
      refine ⟨(C.descendedEval f).symm y', ?_⟩
      rw [LinearEquiv.coe_coe]
      refine (C.descendedEval f').injective ?_
      rw [C.descendedEval_descendedRestrictOf u f f' hf, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
  rw [hrange, ← Submodule.map_span,
    span_range_pointedRestriction_eq_top M (pointedPush f u f' hf), Submodule.map_top]
  exact LinearEquiv.range _

/-- **The semilinear datum of the universal property, read through the evaluation.**  A
`u`-semilinear map out of the descended module becomes, along the evaluation at a pointing `f`, a
map out of `M ⊗_{D,f} B` semilinear for the morphism of the pointed site; that is the datum
`Crystalline.existsUnique_pointedRestriction` extends. -/
noncomputable def descendedUnitDatum (u : X ⟶ X') (f : Dt ⟶ X) (f' : Dt ⟶ X')
    (hf : f ≫ u = f') {N : Type w'} [AddCommGroup N] [Module X'.ring.carrier N]
    (s : ↥(C.descendedSections X) →ₛₗ[u.hom.toRingHom] N) :
    pointedSections M (pointedOfHom f) →ₛₗ[pointedHomRingHom (pointedPush f u f' hf)] N where
  toFun y := s ((C.descendedEval f).symm y)
  map_add' y y' := by
    change s ((C.descendedEval f).symm (y + y')) = _
    rw [map_add, map_add]
  map_smul' b y := by
    change s ((C.descendedEval f).symm (b • y)) = _
    rw [map_smul, map_smulₛₗ s]
    rfl

omit [DecidableEq ι] in
/-- The datum `descendedUnitDatum u f f' hf s` sends `y` to `s ((descendedEval f).symm y)`. -/
@[simp] theorem descendedUnitDatum_apply (u : X ⟶ X') (f : Dt ⟶ X) (f' : Dt ⟶ X')
    (hf : f ≫ u = f') {N : Type w'} [AddCommGroup N] [Module X'.ring.carrier N]
    (s : ↥(C.descendedSections X) →ₛₗ[u.hom.toRingHom] N)
    (y : pointedSections M (pointedOfHom f)) :
    C.descendedUnitDatum u f f' hf s y = s ((C.descendedEval f).symm y) := rfl

omit [DecidableEq ι] in
/-- **The crystal condition for the descended assignment**, the source's "it is clear that there
exists a canonical isomorphism `a^*ℱ_T → ℱ_{T'}`": for every `B'`-module `N` and every
`u`-semilinear map out of `ℱ_T` there is exactly one `B'`-linear map out of `ℱ_{T'}` restricting
to it.  That is the universal property of `u^* ℱ_T`, so the canonical map `u^* ℱ_T → ℱ_{T'}` is an
isomorphism.

This is `Crystalline.existsUnique_pointedRestriction` transported along the evaluations, and it
carries no hypothesis. -/
theorem existsUnique_descendedRestrictOf (u : X ⟶ X') (f : Dt ⟶ X) (f' : Dt ⟶ X')
    (hf : f ≫ u = f') {N : Type w'} [AddCommGroup N] [Module X'.ring.carrier N]
    (s : ↥(C.descendedSections X) →ₛₗ[u.hom.toRingHom] N) :
    ∃! c : ↥(C.descendedSections X') →ₗ[X'.ring.carrier] N,
      ∀ z : ↥(C.descendedSections X), c (C.descendedRestrictOf u f f' hf z) = s z := by
  obtain ⟨c, hc, huniq⟩ := existsUnique_pointedRestriction M (pointedPush f u f' hf)
    (C.descendedUnitDatum u f f' hf s)
  refine ⟨c.comp (C.descendedEval f').toLinearMap, fun z ↦ ?_, fun c' hc' ↦ ?_⟩
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      C.descendedEval_descendedRestrictOf u f f' hf, hc (C.descendedEval f z)]
    show s ((C.descendedEval f).symm (C.descendedEval f z)) = s z
    rw [LinearEquiv.symm_apply_apply]
  · have hkey : c'.comp (C.descendedEval f').symm.toLinearMap = c := by
      refine huniq _ fun y ↦ ?_
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, descendedUnitDatum_apply,
        ← hc' ((C.descendedEval f).symm y)]
      refine congrArg c' ?_
      refine (C.descendedEval f').injective ?_
      rw [LinearEquiv.apply_symm_apply, C.descendedEval_descendedRestrictOf u f f' hf,
        LinearEquiv.apply_symm_apply]
    rw [← hkey]
    refine LinearMap.ext fun z ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]

/-! ### The descended assignment as a functor -/

/-- A pointing of a pointable object, chosen once; by
`Crystalline.PointedComparisonSystem.descendedRestrictOf_indep` nothing below depends on the
choice. -/
noncomputable def point (X : PointableThickening Dt) : Dt ⟶ X.obj := X.property.some

/-- **The restriction map of the descended assignment at the chosen pointings.**  By
`Crystalline.PointedComparisonSystem.descendedRestrictOf_indep` it is the restriction map of every
other pair of pointings too, which is what makes the functor below independent of the choices. -/
noncomputable def descendedRestrict {X X' : PointableThickening Dt} (u : X.obj ⟶ X'.obj) :
    ↥(C.descendedSections X.obj) →ₛₗ[u.hom.toRingHom] ↥(C.descendedSections X'.obj) :=
  C.descendedRestrictOf u (point X) (point X ≫ u) rfl

omit [DecidableEq ι] in
/-- The restriction map at the chosen pointings agrees with the restriction map at any pointings
`f` of `T` and `f'` of `T'` with `f ≫ u = f'`. -/
theorem descendedRestrict_eq {X X' : PointableThickening Dt} (u : X.obj ⟶ X'.obj)
    (f : Dt ⟶ X.obj) (f' : Dt ⟶ X'.obj) (hf : f ≫ u = f')
    (z : ↥(C.descendedSections X.obj)) :
    C.descendedRestrict u z = C.descendedRestrictOf u f f' hf z :=
  C.descendedRestrictOf_indep u _ _ rfl f f' hf z

/-- **The descent of the assignment `T ↦ M ⊗_{D,f} B` to the unpointed crystalline site**, as a
functor on the pointable objects of `CRIS(C/A)`.

This is the construction of the proof of [Stacks, Proposition 60.17.4, Tag 07JH] with the choice
of `f` eliminated: the value at an object is the module of compatible families over all its
pointings, the restriction map is the source's `u ⊗ 1` read through any pointing, and the two
functoriality laws are
`Crystalline.PointedComparisonSystem.descendedRestrictOf_id` and
`Crystalline.PointedComparisonSystem.descendedRestrictOf_comp` together with independence of the
choice.

The values are taken in abelian groups because the ring of scalars varies with the object; that
nothing is lost is `Crystalline.PointedComparisonSystem.descendedCrystal_map_smul`, the
semilinearity of the restriction maps, and
`Crystalline.PointedComparisonSystem.descendedEval`, which identifies each value with
`M ⊗_{D,f} B` as a module. -/
noncomputable def descendedCrystal : PointableThickening Dt ⥤ AddCommGrpCat.{w} where
  obj X := AddCommGrpCat.of ↥(C.descendedSections X.obj)
  map {X X'} u := AddCommGrpCat.ofHom (C.descendedRestrict u.hom).toAddMonoidHom
  map_id X := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z ↦ ?_)
    change C.descendedRestrict (InducedCategory.Hom.hom (𝟙 X)) z = z
    rw [ObjectProperty.FullSubcategory.id_hom,
      C.descendedRestrict_eq (𝟙 X.obj) (point X) (point X) (Category.comp_id _),
      C.descendedRestrictOf_id]
  map_comp {X X' X''} u v := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z ↦ ?_)
    change C.descendedRestrict (u ≫ v).hom z =
      C.descendedRestrict v.hom (C.descendedRestrict u.hom z)
    rw [ObjectProperty.FullSubcategory.comp_hom,
      C.descendedRestrict_eq v.hom (point X ≫ u.hom) ((point X ≫ u.hom) ≫ v.hom) rfl,
      C.descendedRestrict_eq u.hom (point X) (point X ≫ u.hom) rfl,
      C.descendedRestrictOf_comp u.hom v.hom (point X) (point X ≫ u.hom) rfl
        ((point X ≫ u.hom) ≫ v.hom) rfl (Category.assoc _ _ _).symm,
      C.descendedRestrict_eq (u.hom ≫ v.hom) (point X) ((point X ≫ u.hom) ≫ v.hom)
        (Category.assoc _ _ _).symm]

omit [DecidableEq ι] in
/-- The value of `descendedCrystal` at `X` is the descended module of `X`, as an abelian group. -/
@[simp] theorem descendedCrystal_obj (X : PointableThickening Dt) :
    C.descendedCrystal.obj X = AddCommGrpCat.of ↥(C.descendedSections X.obj) := rfl

omit [DecidableEq ι] in
/-- The map of `descendedCrystal` along `u` is the restriction map `descendedRestrict u.hom`. -/
@[simp] theorem descendedCrystal_map {X X' : PointableThickening Dt} (u : X ⟶ X')
    (z : ↥(C.descendedSections X.obj)) :
    (C.descendedCrystal.map u) z = C.descendedRestrict u.hom z := rfl

omit [DecidableEq ι] in
/-- **The restriction maps of the descended crystal are semilinear over the ring maps of the
site.**  The functor takes its values in abelian groups because the ring of scalars varies with
the object; this is the statement that the module structure is nevertheless respected, and it is
the small-site shape of `Crystalline.pointedRestriction_smul`. -/
theorem descendedCrystal_map_smul {X X' : PointableThickening Dt} (u : X.obj ⟶ X'.obj)
    (b : X.obj.ring.carrier) (z : ↥(C.descendedSections X.obj)) :
    C.descendedRestrict u (b • z) = u.hom b • C.descendedRestrict u z :=
  map_smulₛₗ (C.descendedRestrict u) b z

omit [DecidableEq ι] in
/-- **The crystal condition for the descended crystal**: at every morphism of the site the value
over the target has the universal property of the base change of the value over the source.  So
every comparison map `u^* ℱ_T → ℱ_{T'}` of the functor
`Crystalline.PointedComparisonSystem.descendedCrystal` is an isomorphism, with no hypothesis and
in particular no flatness — which is what it means for the functor to be a *crystal*. -/
theorem existsUnique_descendedRestrict {X X' : PointableThickening Dt} (u : X.obj ⟶ X'.obj)
    {N : Type w'} [AddCommGroup N] [Module X'.obj.ring.carrier N]
    (s : ↥(C.descendedSections X.obj) →ₛₗ[u.hom.toRingHom] N) :
    ∃! c : ↥(C.descendedSections X'.obj) →ₗ[X'.obj.ring.carrier] N,
      ∀ z : ↥(C.descendedSections X.obj), c (C.descendedRestrict u z) = s z := by
  obtain ⟨c, hc, huniq⟩ := C.existsUnique_descendedRestrictOf u (point X) (point X ≫ u) rfl s
  exact ⟨c, fun z ↦ by rw [C.descendedRestrict_eq u (point X) (point X ≫ u) rfl, hc z],
    fun c' hc' ↦ huniq c' fun z ↦ by
      rw [← C.descendedRestrict_eq u (point X) (point X ≫ u) rfl, hc' z]⟩

omit [DecidableEq ι] in
/-- **The image of the restriction map of the descended crystal generates.**  This is
`Crystalline.PointedComparisonSystem.span_range_descendedRestrictOf_eq_top` at the chosen
pointings. -/
theorem span_range_descendedRestrict_eq_top {X X' : PointableThickening Dt}
    (u : X.obj ⟶ X'.obj) :
    Submodule.span X'.obj.ring.carrier (Set.range (C.descendedRestrict u)) = ⊤ := by
  have hrange : Set.range (C.descendedRestrict u) =
      Set.range (C.descendedRestrictOf u (point X) (point X ≫ u) rfl) := rfl
  rw [hrange, C.span_range_descendedRestrictOf_eq_top]

end PointedComparisonSystem

end Descent

/-! ### Functoriality in the pair -/

section Functorial

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {M N : Type w} [AddCommGroup M] [Module Dt.ring.carrier M] [AddCommGroup N]
  [Module Dt.ring.carrier N] {ι : Type uI} [DecidableEq ι]
  {thetaPowM : (ι →₀ ℕ) → (M → M)} {thetaPowN : (ι →₀ ℕ) → (N → N)}
  {x : ι → Dt.ring.carrier}

/-- **A horizontal map of pairs, read on the sections over a pointed object**: the map `1 ⊗ φ` on
`M ⊗_{D,f} B`.  It is `B`-linear and not merely `D`-linear, because `φ` is `D`-linear and the
`B`-action is on the left factor; that is the content of its `map_smul'`, and it is the same
computation as `Crystalline.pairToCrystal_map_app_smul`. -/
noncomputable def pointedSectionsMap (phi : M →ₗ[Dt.ring.carrier] N) (T : PointedThickening Dt) :
    pointedSections M T →ₗ[T.right.ring.carrier] pointedSections N T where
  toFun := LinearMap.lTensor (TwistedScalars (pointRingHom T)) phi
  map_add' z z' := map_add _ z z'
  map_smul' b z := by
    change LinearMap.lTensor (TwistedScalars (pointRingHom T)) phi (b • z) =
      b • LinearMap.lTensor (TwistedScalars (pointRingHom T)) phi z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul c m => rw [TensorProduct.smul_tmul', LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.smul_tmul']
    | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]

/-- The map `1 ⊗ φ` sends `b ⊗ m` to `b ⊗ φ m`. -/
@[simp] theorem pointedSectionsMap_tmul (phi : M →ₗ[Dt.ring.carrier] N)
    (T : PointedThickening Dt) (b : TwistedScalars (pointRingHom T)) (m : M) :
    pointedSectionsMap phi T (b ⊗ₜ[Dt.ring.carrier] m) = b ⊗ₜ[Dt.ring.carrier] phi m := rfl

/-- **The map `1 ⊗ φ` commutes with the restriction maps of the pointed site**, both being
instances of `TensorProduct.map`. -/
theorem pointedSectionsMap_pointedRestriction (phi : M →ₗ[Dt.ring.carrier] N)
    {T T' : PointedThickening Dt} (u : T ⟶ T') (z : pointedSections M T) :
    pointedSectionsMap phi T' (pointedRestriction M u z) =
      pointedRestriction N u (pointedSectionsMap phi T z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b m => rw [pointedRestriction_tmul, pointedSectionsMap_tmul, pointedSectionsMap_tmul,
      pointedRestriction_tmul]
  | add z z' hz hz' => rw [map_add, map_add, map_add, map_add, hz, hz']

namespace PointedComparisonSystem

variable (C : PointedComparisonSystem Dt M thetaPowM x)
  (E : PointedComparisonSystem Dt N thetaPowN x) (phi : M →ₗ[Dt.ring.carrier] N)
  {X X' : DividedPowerThickening.{u, v, w} S}

omit [DecidableEq ι] in
/-- **A horizontal map of pairs commutes with the semilinear Taylor comparisons.**

Both sides are computed term by term, by `Crystalline.hasPointedTaylorSum_eq_sum` over a common
finite index set, and the terms agree because `φ` intertwines the two families of composite
coordinate operators.  That intertwining is the hypothesis `hcomm`: it is what it means for `φ` to
be horizontal, read on the operators `θ_K`, and it is the only thing about `φ` that is used. -/
theorem Tmap_comm (hcomm : ∀ (K : ι →₀ ℕ) (m : M), thetaPowN K (phi m) = phi (thetaPowM K m))
    (f g : Dt ⟶ X) (m : M) :
    E.Tmap f g (phi m) = pointedSectionsMap phi (pointedOfHom g) (C.Tmap f g m) := by
  classical
  obtain ⟨n, hn⟩ := X.prime_nilpotent
  set s : Finset (ι →₀ ℕ) := (C.finite_notMem_pPowSmul n m).toFinset ∪
    (E.finite_notMem_pPowSmul n (phi m)).toFinset with hs
  have hvanM := forall_notMem_of_finite_toFinset_subset (C.finite_notMem_pPowSmul n m)
    (Finset.subset_union_left (s₂ := (E.finite_notMem_pPowSmul n (phi m)).toFinset))
  have hvanN := forall_notMem_of_finite_toFinset_subset (E.finite_notMem_pPowSmul n (phi m))
    (Finset.subset_union_right (s₁ := (C.finite_notMem_pPowSmul n m).toFinset))
  rw [hasPointedTaylorSum_eq_sum N S.p thetaPowN g (pointedDiff f g x) hn (phi m) s hvanN
      (E.hasSum f g (phi m)),
    hasPointedTaylorSum_eq_sum M S.p thetaPowM g (pointedDiff f g x) hn m s hvanM
      (C.hasSum f g m), map_sum]
  exact Finset.sum_congr rfl fun K _ ↦ by rw [pointedSectionsMap_tmul, hcomm K m]

omit [DecidableEq ι] in
/-- **A horizontal map of pairs commutes with the comparisons `c_{f,g}`.**  Both sides are
`B`-linear maps out of `M ⊗_{D,f} B`, so it is enough to compare them on the generators `1 ⊗ m`,
where the identity is `Crystalline.PointedComparisonSystem.Tmap_comm`. -/
theorem comparison_pointedSectionsMap
    (hcomm : ∀ (K : ι →₀ ℕ) (m : M), thetaPowN K (phi m) = phi (thetaPowM K m))
    (f g : Dt ⟶ X) (z : pointedSections M (pointedOfHom f)) :
    E.comparison f g (pointedSectionsMap phi (pointedOfHom f) z) =
      pointedSectionsMap phi (pointedOfHom g) (C.comparison f g z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b m =>
      rw [pointedSectionsMap_tmul, comparison_tmul, comparison_tmul, map_smul,
        Tmap_comm C E phi hcomm f g m]
  | add z z' hz hz' => rw [map_add, map_add, map_add, map_add, hz, hz']

/-- **A horizontal map of pairs descends**, which is the first half of the source's "We also omit
the proof that this procedure is a functor": the map `1 ⊗ φ` carries compatible families over the
pointings of an object to compatible families, by
`Crystalline.PointedComparisonSystem.comparison_pointedSectionsMap`. -/
noncomputable def descendedMap
    (hcomm : ∀ (K : ι →₀ ℕ) (m : M), thetaPowN K (phi m) = phi (thetaPowM K m))
    (X : DividedPowerThickening.{u, v, w} S) :
    ↥(C.descendedSections X) →ₗ[X.ring.carrier] ↥(E.descendedSections X) where
  toFun z := ⟨fun f ↦ pointedSectionsMap phi (pointedOfHom f) (z.val f), fun f g ↦ by
    rw [comparison_pointedSectionsMap C E phi hcomm f g (z.val f), z.property f g]⟩
  map_add' z z' := Subtype.ext (funext fun f ↦ map_add _ (z.val f) (z'.val f))
  map_smul' b z := Subtype.ext (funext fun f ↦ map_smul _ b (z.val f))

omit [DecidableEq ι] in
/-- Evaluated at a pointing `f`, the descended map is `1 ⊗ φ` on `M ⊗_{D,f} B`. -/
@[simp] theorem descendedEval_descendedMap
    (hcomm : ∀ (K : ι →₀ ℕ) (m : M), thetaPowN K (phi m) = phi (thetaPowM K m))
    (f : Dt ⟶ X) (z : ↥(C.descendedSections X)) :
    E.descendedEval f (descendedMap C E phi hcomm X z) =
      pointedSectionsMap phi (pointedOfHom f) (C.descendedEval f z) := rfl

omit [DecidableEq ι] in
/-- **The descended map commutes with the restriction maps**, which is the second half of "this
procedure is a functor": the square of the descended assignment in the object and in the pair
commutes.  Together with
`Crystalline.PointedComparisonSystem.descendedMap` this is the naturality the source omits. -/
theorem descendedMap_descendedRestrictOf
    (hcomm : ∀ (K : ι →₀ ℕ) (m : M), thetaPowN K (phi m) = phi (thetaPowM K m))
    (u : X ⟶ X') (f : Dt ⟶ X) (f' : Dt ⟶ X') (hf : f ≫ u = f')
    (z : ↥(C.descendedSections X)) :
    descendedMap C E phi hcomm X' (C.descendedRestrictOf u f f' hf z) =
      E.descendedRestrictOf u f f' hf (descendedMap C E phi hcomm X z) := by
  refine (E.descendedEval f').injective ?_
  rw [descendedEval_descendedMap C E phi hcomm f',
    C.descendedEval_descendedRestrictOf u f f' hf,
    E.descendedEval_descendedRestrictOf u f f' hf,
    descendedEval_descendedMap C E phi hcomm f,
    pointedSectionsMap_pointedRestriction phi (pointedPush f u f' hf)]

end PointedComparisonSystem

end Functorial

end Crystalline

end

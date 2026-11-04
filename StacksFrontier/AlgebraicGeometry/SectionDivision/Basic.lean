module

public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic

/-!
# Dividing a section of an invertible module by a nonvanishing section

Let `(X, 𝒪_X)` be a ringed space all of whose stalks are local rings, let `L` be an invertible
sheaf of `𝒪_X`-modules and let `s` be a global section of `L`. Over any open `V` contained in
the nonvanishing locus `X_s`, multiplication by `s` is a bijection `𝒪_X(V) → L(V)`
(`Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen`, the trivialization clause of
[Stacks, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)). This file names its inverse,
`divBySection`, and records the algebra it satisfies.

The notation of [Stacks, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8) for this inverse is
`x ↦ x / s`: it is the device by which the proof of Tag 01N8 — and hence of Tag 01NA and of
Tag 01NE, the universal property of projective space — turns a family of generating sections of
an invertible module into honest functions on each nonvanishing locus. The two identities that
proof actually uses are `divBySection_trans`, which says `u/s = (u/t)·(t/s)` wherever both
denominators are nonvanishing, and `map_divBySection`, which says the quotient is compatible with
restriction.

## Main definitions

* `Stacks.SheafOfModules.divBySection`: for `V ≤ X_s` and `t ∈ L(V)`, the unique section
  `t / s ∈ 𝒪_X(V)` with `(t / s) · s|_V = t`.

## Main results

* `Stacks.SheafOfModules.smul_divBySection` and
  `Stacks.SheafOfModules.divBySection_eq_of_smul_eq`: the defining property and its uniqueness.
* `Stacks.SheafOfModules.divBySection_self`: `s / s = 1`.
* `Stacks.SheafOfModules.divBySection_smul` and `Stacks.SheafOfModules.divBySection_add`: the
  quotient is `𝒪_X(V)`-linear in the numerator.
* `Stacks.SheafOfModules.divBySection_trans`: the cocycle identity `u/s = (u/t)·(t/s)`.
* `Stacks.SheafOfModules.divBySection_mul_divBySection` and
  `Stacks.SheafOfModules.isUnit_divBySection`: on `X_s ∩ X_t` the quotient `t/s` is a unit with
  inverse `s/t`.
* `Stacks.SheafOfModules.map_divBySection`: compatibility with restriction.

## Implementation notes

`divBySection` is defined as the inverse of `Equiv.ofBijective` applied to the trivialization
bijection, so `smul_divBySection` is `Equiv.apply_symm_apply` and nothing about the
trivialization is re-derived here. Uniqueness is the injectivity half of the same bijection, and
every other statement in the file is uniqueness applied to an explicit witness.

**Other uses.** Five other files invert this same bijection
inline — `StacksFrontier/AlgebraicGeometry/FiniteTrivialize/Basic.lean`,
`StacksFrontier/AlgebraicGeometry/FiniteTrivialize/TargetCover.lean`,
`StacksFrontier/AlgebraicGeometry/SectionExtension/Basic.lean` (twice) and
`StacksFrontier/AlgebraicGeometry/AffineNonvanishing/Sum.lean` — each obtaining the
quotient as an anonymous `obtain` from surjectivity, whereas `divBySection` makes the
quotient a term with lemmas rather than a local existential.

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, the class
`Stacks.SheafOfModules.nonvanishingOpen` is defined for. It is *not*
`AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`; the bridge between the two is
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  (L : SheafOfModules.{u} (structureSheafRing X))
  [IsInvertible X.presheaf (structureSheafRing X).property L]

/-- The quotient `t / s` of a section `t` of `L` over an open `V` of the nonvanishing locus of a
global section `s`: the unique section of the structure sheaf over `V` whose product with `s|_V`
is `t`. -/
noncomputable def divBySection (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) (t : L.val.obj (op V)) : X.presheaf.obj (op V) :=
  (Equiv.ofBijective _ (bijective_smul_eval_of_le_nonvanishingOpen L s V hV)).symm t

/-- The defining property of the quotient: `(t / s) · s|_V = t`. -/
theorem smul_divBySection (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) (t : L.val.obj (op V)) :
    divBySection L s hV t • s.eval (op V) = t :=
  (Equiv.ofBijective _ (bijective_smul_eval_of_le_nonvanishingOpen L s V hV)).apply_symm_apply t

/-- The quotient is the *unique* section with the defining property. -/
theorem divBySection_eq_of_smul_eq (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) {t : L.val.obj (op V)} {c : X.presheaf.obj (op V)}
    (h : c • s.eval (op V) = t) : divBySection L s hV t = c :=
  (bijective_smul_eval_of_le_nonvanishingOpen L s V hV).1
    ((smul_divBySection L s hV t).trans h.symm)

/-- `s / s = 1`. -/
@[simp] theorem divBySection_self (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) : divBySection L s hV (s.eval (op V)) = 1 :=
  divBySection_eq_of_smul_eq L s hV (one_smul _ _)

/-- The quotient is homogeneous in the numerator: `(c · t) / s = c · (t / s)`. -/
theorem divBySection_smul (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) (c : X.presheaf.obj (op V)) (t : L.val.obj (op V)) :
    divBySection L s hV (c • t) = c * divBySection L s hV t :=
  divBySection_eq_of_smul_eq L s hV (by rw [mul_smul, smul_divBySection])

/-- The quotient is additive in the numerator. -/
theorem divBySection_add (s : L.sections) {V : Opens X.carrier}
    (hV : V ≤ nonvanishingOpen L s) (t t' : L.val.obj (op V)) :
    divBySection L s hV (t + t') = divBySection L s hV t + divBySection L s hV t' :=
  divBySection_eq_of_smul_eq L s hV (by rw [add_smul, smul_divBySection, smul_divBySection])

/-- **The cocycle identity.** Over an open on which two global sections `s` and `t` are both
nonvanishing, `u / s = (u / t) · (t / s)` for every section `u`. This is the computation that
makes the charts of Tag 01N8 agree on their overlaps. -/
theorem divBySection_trans (s t : L.sections) {V : Opens X.carrier}
    (hVs : V ≤ nonvanishingOpen L s) (hVt : V ≤ nonvanishingOpen L t)
    (u : L.val.obj (op V)) :
    divBySection L s hVs u
      = divBySection L t hVt u * divBySection L s hVs (t.eval (op V)) :=
  divBySection_eq_of_smul_eq L s hVs (by
    rw [mul_smul, smul_divBySection, smul_divBySection])

/-- Over an open on which both `s` and `t` are nonvanishing, `(t / s) · (s / t) = 1`. -/
theorem divBySection_mul_divBySection (s t : L.sections) {V : Opens X.carrier}
    (hVs : V ≤ nonvanishingOpen L s) (hVt : V ≤ nonvanishingOpen L t) :
    divBySection L s hVs (t.eval (op V)) * divBySection L t hVt (s.eval (op V)) = 1 := by
  rw [mul_comm, ← divBySection_trans L s t hVs hVt, divBySection_self]

/-- Over an open on which both `s` and `t` are nonvanishing, `t / s` is a unit. -/
theorem isUnit_divBySection (s t : L.sections) {V : Opens X.carrier}
    (hVs : V ≤ nonvanishingOpen L s) (hVt : V ≤ nonvanishingOpen L t) :
    IsUnit (divBySection L s hVs (t.eval (op V))) :=
  have h := divBySection_mul_divBySection L s t hVs hVt
  ⟨⟨_, divBySection L t hVt (s.eval (op V)), h, (mul_comm _ _).trans h⟩, rfl⟩

omit [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  [IsInvertible X.presheaf (structureSheafRing X).property L] in
/-- Restriction of a global section, written through the semilinear restriction map
`Stacks.SheafOfModules.TensorStalkRingedSpace.secRestr`. Stated separately because it is the
  spelling at which the restriction
of a scalar multiple is available. -/
theorem secRestr_sections_eval (s : L.sections) {V W : Opens X.carrier} (h : W ≤ V) :
    ((L.val).restrictₛₗ ((homOfLE h).op)) (s.eval (op V)) = s.eval (op W) :=
  PresheafOfModules.sections_property s (homOfLE h).op

/-- **The quotient is compatible with restriction.** -/
theorem map_divBySection (s : L.sections) {V W : Opens X.carrier} (h : W ≤ V)
    (hV : V ≤ nonvanishingOpen L s) (t : L.val.obj (op V)) :
    (X.presheaf.map (homOfLE h).op).hom (divBySection L s hV t)
      = divBySection L s (h.trans hV) (((L.val).restrictₛₗ ((homOfLE h).op)) t) :=
  (divBySection_eq_of_smul_eq L s (h.trans hV) (by
    rw [← secRestr_sections_eval L s h]
    exact (map_smulₛₗ ((L.val).restrictₛₗ ((homOfLE h).op)) _ _).symm.trans
      (congrArg _ (smul_divBySection L s hV t)))).symm

end Stacks.SheafOfModules

end

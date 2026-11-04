module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreBaseChangePushout
public import StacksFrontier.RingTheory.Localization.GenericFibreComponents
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic fibre of a base change, as a pushout of the function fields themselves

In Situation 0EDT let `X/B` and `Y/B` be good and integral and let `p : X ⟶ Y` be finite and
dominant. `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreBaseChangePushout` identifies the
generic fibre `G` of `X ×_Y V ⟶ V`, for `b : V ⟶ Y` a chart of `Y` through the generic point of a
prime divisor, as the base change of `Spec R(X)` along `R(Y) → R(V)` — but at the level of the
*global sections of the spectra*, that is as

`Algebra.IsPushout Γ(Spec κ(p ξ)) Γ(Spec κ(w)) Γ(Spec κ(ξ)) Γ(G)`.

This file moves that statement onto the fields themselves and adds the second hypothesis of the
field-theoretic step of **Stacks 0EQ4**, so that the step is available in the form the geometry of
Stacks 0EQ4 supplies:

* `Algebra.IsPushout R(Y) R(V) R(X) Γ(G)`, and
* `IsLocalization (Algebra.algebraMapSubmonoid Γ(X ×_Y V) Γ(V)⁰) Γ(G)`,

the two hypotheses of `Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout_of_isReduced`
that are about the geometry rather than about one chart. The last result of the file is that
lemma with both of them discharged: **the norm identity of Stacks 0EQ4 read on a chart.**

## Main results

* `AlgebraicGeometry.hom_comp_eq_of_isPushout_ofHom`,
  `AlgebraicGeometry.algebraIsPushout_of_isPushout_ofHom` and
  `AlgebraicGeometry.isLocalization_of_isPushout_ofHom`: a cocartesian square of `CommRingCat`
  whose four edges are `CommRingCat.ofHom` of ring homomorphisms, read as a base change of
  algebras for the `RingHom.toAlgebra` structures those homomorphisms define, and — when the
  left-hand edge is a fraction field — as a localization.
* `AlgebraicGeometry.isPushout_appTop_of_isPullback_spec_right` and
  `AlgebraicGeometry.isPushout_of_isPullback_specMap`: Mathlib's
  `AlgebraicGeometry.isPushout_appTop_of_isPullback` with one, respectively all three, of the
  corners `Γ(Spec R, ⊤)` replaced by `R`.
* `AlgebraicGeometry.Space.exists_eq_specMap_of_hom_siteObject`: **every morphism of the site
  between the spectra of two field-valued points is the spectrum of a homomorphism of their
  fields.** Nothing is assumed.
* `AlgebraicGeometry.Space.eq_specMap_residueFieldHom`: that homomorphism is the canonical one,
  `AlgebraicGeometry.Space.residueFieldHom`, as soon as the morphism sits in the square over the
  target space.
* `AlgebraicGeometry.Space.isPushout_appTop_of_isPullback_yoneda_fieldValuedPoint`: the global
  sections of a cartesian square of the site whose lower left corner is the spectrum of a field
  and whose two right-hand corners are affine form a cocartesian square with that field as a
  corner.
* `AlgebraicGeometry.Space.exists_isPushout_appTop_fibre_baseChange`: **the field transport.**
  The conclusion of
  `AlgebraicGeometry.Space.exists_isPullback_toScheme_fibre_baseChange` as a cocartesian square
  of the residue fields `κ(p ξ)`, `κ(w)`, `κ(ξ)` and the ring `Γ(G)` of the fibre.
* `AlgebraicGeometry.Space.norm_eq_finprod_norm_quotient_of_isPushout_fibre`: **the norm identity
  on a chart.** For `t` a rational function on `X`, the image of `Nm_{R(X)/R(Y)}(t)` in `R(V)` is
  the product, over the points of `X ×_Y V` dominating `V`, of the norms over `R(V)` of the images
  of `t` in the factors of the generic fibre.

## Implementation notes

### Why the transport is made on the categorical pushout

`Algebra.IsPushout K F L T` has no transport lemma along isomorphisms of the base `K` or of the
two middle corners `F`, `L`: `Algebra.IsPushout.of_equiv` moves only the fourth corner. So the
move across the three copies of `AlgebraicGeometry.Scheme.ΓSpecIso` is made on the *categorical*
pushout square in `CommRingCat`, where `CategoryTheory.IsPushout.of_iso` is free, and converted
back with Mathlib's `CommRingCat.isPushout_iff_isPushout`. That conversion needs each of the three
morphisms of fields presented as `Spec.map` of a ring homomorphism.

### That presentation is free, and the upstream notes overstate what it costs

Those notes say that what is still owed for the transport is the `Spec.map` clause for the
morphism `g` of the hypothesis, produced but not exposed by
`AlgebraicGeometry.Space.exists_isPullback_residueFieldMorphism`, and that exposing it means
adding a conclusion to that lemma. **Neither is needed.** Every morphism of the site between the
site objects of two field-valued points is `Spec.map` of a homomorphism of the two fields, with
*no* hypothesis at all and in three lines — `AlgebraicGeometry.Space` already builds the ring
homomorphism this way inside `AlgebraicGeometry.Space.existsUnique_isInducedResidueFieldHom`, out
of `Spec.fullyFaithful.preimage`, and nothing there uses the square. So the clause is recovered
after the fact from any `g` whatever, no lemma upstream has to be restated, and
`AlgebraicGeometry.Space.eq_specMap_residueFieldHom` then identifies the homomorphism with the
canonical `AlgebraicGeometry.Space.residueFieldHom` whenever `g` does sit in the square.

### `Γ(G)` as a localization is the backwards direction of a Mathlib iff

`Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout_of_isReduced` asks for
`IsLocalization (Algebra.algebraMapSubmonoid C O⁰) T` with `O = Γ(V)` and `C = Γ(X ×_Y V)`. That is
`Algebra.isLocalization_iff_isPushout` run from right to left on the *other* cartesian square the
pasting produces — the one presenting `G` as the fibre of `X ×_Y V ⟶ V` over `Spec R(V)` — whose
cocartesian image is `Algebra.IsPushout Γ(V) Γ(X ×_Y V) R(V) Γ(G)`. The only extra input is
`IsFractionRing Γ(V) R(V)`: that the chart's function field is the fraction field of its ring of
functions. `Stacks.GenericFibre.isPushout_of_localization` is the same statement in the forward
direction and is not what is needed here.

### What is assumed on the chart, and why none of it is the content of Stacks 0EQ4

`AlgebraicGeometry.Space.norm_eq_finprod_norm_quotient_of_isPushout_fibre` carries five chart-level
hypotheses: the two cartesian squares, affineness of `Γ(X ×_Y V)` and of `V`, `IsDomain Γ(V)`,
`IsFractionRing Γ(V) R(V)`, reducedness of `Γ(G)`, and `Module.Finite R(Y) R(X)`. In the proof of
Stacks 0EQ4 the chart `b : V ⟶ Y` is an affine étale neighbourhood of the generic point of a prime
divisor and `w` the generic point of one of its branches, so the first four are the integrality of
that branch, reducedness of `Γ(G)` comes from `X ×_Y V` being étale over the integral `X`, and the
finiteness of `R(X)/R(Y)` from `p` being finite — these are the "other halves" of the proof that
the identification of the fibre, which is a pasting of cartesian squares, does not need. None of
them is the identity being proved: the conclusion is an equation between a norm and a product of
norms, and no hypothesis mentions a norm or an order of vanishing.

`Module.Finite R(Y) R(X)` is stated for the algebra structure of the given `ψ`. By
`AlgebraicGeometry.Space.eq_specMap_residueFieldHom` that `ψ` is the canonical
`AlgebraicGeometry.Space.residueFieldHom` as soon as the morphism of the site presenting it sits
in the square over `Y`, and then the hypothesis *is*
`AlgebraicGeometry.Space.HasFiniteResidueFieldExtensionAt` of
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralDegree`, whose algebra structure
`AlgebraicGeometry.Space.residueFieldAlgebra` is that homomorphism's `RingHom.toAlgebra`. **That
predicate is derivable here and is not an open statement of this development.** Stacks 0AD5 is
proved, as `AlgebraicGeometry.Space.tfae_hasTranscendenceDegreeAt_eq_zero` of
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralGenericallyFiniteTfae`: its condition (2) is
`HasFiniteResidueFieldExtensionAt` and its condition (5) is that the generic point of `X` is the
only preimage of the generic point of `Y` — which is exactly the hypothesis that
`AlgebraicGeometry.Space.exists_isPullback_residueFieldMorphism_genericPoint` already discharges
for a finite `p`, through
`AlgebraicGeometry.Space.eq_genericPoint_of_pointsMap_eq_genericPoint`. It is a visible hypothesis
here only because this statement quantifies `ψ` freely, so no canonical algebra structure is
available to state it at; a consumer working at the two generic points reads it off Stacks 0AD5.

### What Stacks 0EQ4 still needs after this

The two plumbing steps the notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreBaseChangePushout` list are done, and so is
the field-theoretic step they feed. What remains is the third, **the coefficient identity**: for
each integral closed `Z ⊆ Y` of δ-dimension one less, both sides of
`p_* div(f) = div(Nm_{R(X)/R(Y)}(f))` have to be read at the chart, by
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_finsum_minimalPrimeOrd` (Stacks 0ENM), the left side
reindexed over the fibre of `|p|` by
`AlgebraicGeometry.Space.properPushforwardCoeff_principalDivisorCycleCoefficients_eq_finsum_fibre`
and `AlgebraicGeometry.Space.bijOn_chartSchemeToPoints_fibre`, and the scheme case
`Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite` (Stacks 02RT) applied branch by branch;
the result then discharges `AlgebraicGeometry.Space.ProperPushforwardNormRule` through
`AlgebraicGeometry.Space.properPushforward_principalDivisorCycle_eq_iff`. That step is not started
here.

### Stacks 0EQ4 can only ever be unconditional at one embedding family and one `g`

The registration of Stacks 0EQ4 in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisor` quantifies the two
families of Stacks 0ENK embeddings and the function `g` of the conclusion freely. As an *iff* that
is harmless; as the forward identity it is false, because the norm identity pins
`g = Nm_{R(X)/R(Y)}(f)` and at a free family of embeddings the order of vanishing is a different
function. So the identity can only become unconditional at
`AlgebraicGeometry.Space.PrimeDivisor.genericFractionEmbedding` with `g` the rational function
norm. No tag is claimed here, and the free-parameter form is deliberately not stated.

No Stacks tag is claimed. The source performs each step of this file inside the proof of
Stacks 0EQ4 without stating it as a result; the field-theoretic step is the one it states and
omits the proof of, and that step is
`Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout_of_isReduced`, which is already
proved in this development.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-! ### Reading a cocartesian square of `CommRingCat` as a base change of algebras -/

section Transport

variable {K F L T : Type u} [CommRing K] [CommRing F] [CommRing L] [CommRing T]

/-- **The two composites around a cocartesian square of rings agree.** This is the square's own
commutativity, read as an equation of ring homomorphisms; it is what makes the two scalar towers
of the `RingHom.toAlgebra` structures below hold. -/
theorem hom_comp_eq_of_isPushout_ofHom (φ : K →+* F) (ψ : K →+* L) (β : F →+* T) (α : L →+* T)
    (h : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom α)) :
    β.comp φ = α.comp ψ := by
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    using congrArg CommRingCat.Hom.hom h.w

/-- **A cocartesian square of `CommRingCat` is a base change of algebras.** For ring
homomorphisms `φ : K → F`, `ψ : K → L`, `β : F → T` and `α : L → T` whose square is a pushout in
`CommRingCat`, the ring `T` is the base change of `L` along `φ`, for the algebra structures the
four homomorphisms define.

This is Mathlib's `CommRingCat.isPushout_iff_isPushout` with the algebra structures named rather
than assumed, which is what a consumer transporting a pushout along isomorphisms of its corners
has: `Algebra.IsPushout` admits no such transport — `Algebra.IsPushout.of_equiv` moves only the
fourth corner — whereas `CategoryTheory.IsPushout.of_iso` is free. -/
theorem algebraIsPushout_of_isPushout_ofHom (φ : K →+* F) (ψ : K →+* L) (β : F →+* T)
    (α : L →+* T)
    (h : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom α)) :
    letI : Algebra K F := φ.toAlgebra
    letI : Algebra K L := ψ.toAlgebra
    letI : Algebra F T := β.toAlgebra
    letI : Algebra L T := α.toAlgebra
    letI : Algebra K T := (β.comp φ).toAlgebra
    haveI : IsScalarTower K F T := .of_algebraMap_eq' rfl
    haveI : IsScalarTower K L T := .of_algebraMap_eq'
      (hom_comp_eq_of_isPushout_ofHom φ ψ β α h)
    Algebra.IsPushout K F L T := by
  algebraize [φ, ψ, β, α, β.comp φ]
  have : IsScalarTower K F T := .of_algebraMap_eq' rfl
  have : IsScalarTower K L T := .of_algebraMap_eq'
    (hom_comp_eq_of_isPushout_ofHom φ ψ β α h)
  exact CommRingCat.isPushout_iff_isPushout.mp h

/-- **A cocartesian square of `CommRingCat` over a fraction field is a localization.** In the
situation of `AlgebraicGeometry.algebraIsPushout_of_isPushout_ofHom`, if `L` is the localization
of `K` at its nonzerodivisors then `T` is the localization of `F` at the image of those
nonzerodivisors.

Geometrically, with `K = Γ(V)` for `V` integral affine, `L = R(V)` its function field,
`F = Γ(U)` for a `V`-scheme `U` and `T = Γ(U ×_V Spec R(V))`: the ring of the fibre of `U → V`
over the generic point of `V` is `Γ(U)` with the nonzero elements of `Γ(V)` inverted. This is
Mathlib's `Algebra.isLocalization_iff_isPushout` from right to left;
`Stacks.GenericFibre.isPushout_of_localization` is the other direction. -/
theorem isLocalization_of_isPushout_ofHom (φ : K →+* F) (ψ : K →+* L) (β : F →+* T)
    (α : L →+* T)
    (h : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom α)) :
    letI : Algebra K F := φ.toAlgebra
    letI : Algebra K L := ψ.toAlgebra
    letI : Algebra F T := β.toAlgebra
    letI : Algebra L T := α.toAlgebra
    letI : Algebra K T := (β.comp φ).toAlgebra
    haveI : IsScalarTower K F T := .of_algebraMap_eq' rfl
    haveI : IsScalarTower K L T := .of_algebraMap_eq'
      (hom_comp_eq_of_isPushout_ofHom φ ψ β α h)
    IsFractionRing K L → IsLocalization (Algebra.algebraMapSubmonoid F K⁰) T := by
  algebraize [φ, ψ, β, α, β.comp φ]
  have : IsScalarTower K F T := .of_algebraMap_eq' rfl
  have : IsScalarTower K L T := .of_algebraMap_eq'
    (hom_comp_eq_of_isPushout_ofHom φ ψ β α h)
  intro hfrac
  have := hfrac
  exact (Algebra.isLocalization_iff_isPushout K⁰ L).mpr
    (algebraIsPushout_of_isPushout_ofHom φ ψ β α h)

end Transport

/-! ### Replacing the spectra of rings in a cartesian square by the rings -/

section SpecCorners

variable {K F L : Type u} [CommRing K] [CommRing F] [CommRing L]

/-- **The global sections of a cartesian square of schemes, with one spectrum replaced by its
ring.** For a cartesian square of schemes with `X` and `Z` affine and the remaining corner the
spectrum of a ring `T`, the square of global sections is cocartesian with `T` itself as a corner.

This is Mathlib's `AlgebraicGeometry.isPushout_appTop_of_isPullback` composed with
`AlgebraicGeometry.Scheme.ΓSpecIso` at that one corner. The two-corner form, for a square whose
bottom edge is `Spec` of a ring map and whose right edge is read through `Scheme.isoSpec`, is
`AlgebraicGeometry.isPushout_appTop_of_isPullback_specMap` of
`StacksFrontier.AlgebraicGeometry.Scheme.AffinePullbackGlobalSections`. -/
@[sga "3 V 4.1" "more general"]
theorem isPushout_appTop_of_isPullback_spec_right {Z X P : Scheme.{u}} {T : CommRingCat.{u}}
    [IsAffine X] [IsAffine Z] {fst : P ⟶ X} {snd : P ⟶ Spec T} {f : X ⟶ Z} {t : Spec T ⟶ Z}
    (h : IsPullback fst snd f t) :
    IsPushout f.appTop (t.appTop ≫ (Scheme.ΓSpecIso T).hom) fst.appTop
      ((Scheme.ΓSpecIso T).inv ≫ snd.appTop) :=
  (isPushout_appTop_of_isPullback h).of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso T)
    (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/-- **The global sections of a cartesian square of spectra of rings.** For a cartesian square

```
P        ⟶ Spec L
↓             ↓ Spec ψ
Spec F   ⟶ Spec K
```

whose two lower edges are the spectra of ring homomorphisms `ψ : K → L` and `φ : K → F`, the
square formed by `φ`, `ψ` and the two maps `F → Γ(P, ⊤)`, `L → Γ(P, ⊤)` on global sections is
cocartesian.

All three corners of the square other than `P` are replaced by their rings at once, which is the
form the fibre of Stacks 0EQ4 needs: there `K`, `F` and `L` are the function fields `R(Y)`,
`R(V)` and `R(X)`, and the conclusion has to be a statement about the fields and not about the
global sections of their spectra. -/
theorem isPushout_of_isPullback_specMap {P : Scheme.{u}}
    {fst : P ⟶ Spec (CommRingCat.of L)} {snd : P ⟶ Spec (CommRingCat.of F)} (φ : K →+* F)
    (ψ : K →+* L)
    (h : IsPullback fst snd (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom φ))) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ snd.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ fst.appTop) :=
  ((isPushout_appTop_of_isPullback h).of_iso (Scheme.ΓSpecIso (CommRingCat.of K))
    (Scheme.ΓSpecIso (CommRingCat.of L)) (Scheme.ΓSpecIso (CommRingCat.of F)) (Iso.refl _)
    (Scheme.ΓSpecIso_naturality _) (Scheme.ΓSpecIso_naturality _) (by simp) (by simp)).flip

end SpecCorners

namespace Space

/-! ### Every morphism of the site between spectra of fields is the spectrum of a map of fields -/

section SiteHom

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Every morphism of the site between the spectra of two field-valued points is the spectrum
of a homomorphism of their fields.** Nothing is assumed: the underlying scheme of the site object
of a field-valued point *is* the spectrum of its field, and `Spec` is fully faithful, so the
homomorphism is `Spec.fullyFaithful.preimage` of the morphism of schemes.

This is the clause that lets a square of field spectra be read back as a square of rings, through
`CommRingCat.isPushout_iff_isPushout`. The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreBaseChangePushout` record it as something a
producer of the morphism has to be restated to expose; it is recovered after the fact from an
arbitrary morphism, so no producer has to change. -/
theorem exists_eq_specMap_of_hom_siteObject {p : FieldValuedPoint B S hS X}
    {q : FieldValuedPoint B S hS Y} (g : p.siteObject B S hS X ⟶ q.siteObject B S hS Y) :
    ∃ φ : q.carrier →+* p.carrier,
      B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) :=
  ⟨((Spec.fullyFaithful.preimage (B.inclusion.map g.left)).unop).hom, by simp⟩

/-- **The homomorphism is the canonical one.** If a morphism `g` of the site sits in the square
over `Y` formed by the chosen monomorphic representatives of `x` and of its image, then the
homomorphism of residue fields whose spectrum it is, is
`AlgebraicGeometry.Space.residueFieldHom`.

This is the uniqueness half of
`AlgebraicGeometry.Space.existsUnique_isInducedResidueFieldHom`: the square determines the
homomorphism, so any `g` satisfying it presents the canonical one. It is what identifies the
`ψ` of the pushout square below with the map of function fields of Stacks 0END, and hence the
algebra structure used for `Module.Finite` with
`AlgebraicGeometry.Space.residueFieldAlgebra`. -/
theorem eq_specMap_residueFieldHom (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X)
    {g : (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hdecY
        (pointsMap B S hS X f x)).1.siteObject B S hS Y}
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X f x) =
      residueFieldMorphism B S hS X hdecX x ≫ f) :
    B.inclusion.map g.left =
      Spec.map (CommRingCat.ofHom (residueFieldHom B S hS X Y hY hdecX hdecY f x)) := by
  obtain ⟨φ, hφ⟩ := exists_eq_specMap_of_hom_siteObject B S hS g
  rw [hφ, (existsUnique_isInducedResidueFieldHom B S hS X Y hY hdecX hdecY f x).unique
    (show IsInducedResidueFieldHom B S hS X Y hdecX hdecY f x φ from ⟨g, hφ, hg⟩)
    (residueFieldHom_spec B S hS X Y hY hdecX hdecY f x)]

end SiteHom

/-! ### The global sections of the fibre over a field-valued point -/

section Fibre

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The global sections of the fibre of a morphism of the site over a field-valued point.**
For a cartesian square

```
G         ⟶ U
↓             ↓ pr
Spec κ(w) ⟶ V
```

of the site whose corners `U` and `V` have affine underlying scheme, the square of global
sections, with the corner `Γ(Spec κ(w), ⊤)` replaced by the field `κ(w)` itself, is cocartesian.

This is the second of the two squares that the pasting of
`AlgebraicGeometry.Space.exists_isPullback_toScheme_fibre_baseChange` produces, and it is the one
that exhibits `Γ(G)` as a localization of `Γ(U)`, by
`AlgebraicGeometry.isLocalization_of_isPushout_ofHom`. Nothing is asked of `V` beyond affineness —
in Stacks 0EQ4 it is a branch of an affine étale chart, and neither étaleness nor the chart
structure enters here. -/
theorem isPushout_appTop_of_isPullback_yoneda_fieldValuedPoint
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pw : FieldValuedPoint B S hS W}
    {U V G : BigFppfOver B S hS} {u : G ⟶ U} {q : G ⟶ pw.siteObject B S hS W}
    {pr : U ⟶ V} {iV : pw.siteObject B S hS W ⟶ V}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (h : IsPullback (yoneda.map u) (yoneda.map q) (yoneda.map pr) (yoneda.map iV)) :
    IsPushout ((BigFppfOver.toScheme B S hS).map pr).appTop
      (((BigFppfOver.toScheme B S hS).map iV).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of pw.carrier)).hom)
      ((BigFppfOver.toScheme B S hS).map u).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of pw.carrier)).inv ≫
        ((BigFppfOver.toScheme B S hS).map q).appTop) :=
  isPushout_appTop_of_isPullback_spec_right
    ((IsPullback.of_map_of_faithful yoneda h).map (BigFppfOver.toScheme B S hS))

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : X ⟶ Y}

/-- **The field transport: the generic fibre of a base change is the base change of the generic
fibre, as a square of the fields themselves.** In the situation of
`AlgebraicGeometry.Space.exists_isPullback_toScheme_fibre_baseChange` — `p : X ⟶ Y` relatively
representable between decent algebraic spaces, `x` a point of `X` whose chosen field-valued point
is the fibre of `p` over the chosen field-valued point of `p x`, and `b : V ⟶ Y` a morphism from a
representable space hitting `p x` at a point `w` — there is an object `G` of the site which is the
fibre of `X ×_Y V ⟶ V` over the chosen field-valued point of `w`, and homomorphisms of residue
fields `ψ : κ(p x) → κ(x)` and `φ : κ(p x) → κ(w)` making

```
κ(p x) ⟶ κ(x)
  ↓          ↓
κ(w)   ⟶ Γ(G)
```

cocartesian in `CommRingCat`.

In Stacks 0EQ4 `x` and `p x` are the generic points of the integral `X` and `Y`, so `κ(x)` and
`κ(p x)` are the function fields `R(X)` and `R(Y)` by Stacks 0END, and the conclusion is
`Algebra.IsPushout R(Y) R(V) R(X) Γ(G)` — the hypothesis
`Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout_of_isReduced` consumes after
`Algebra.IsPushout.symm`, and by
`AlgebraicGeometry.algebraIsPushout_of_isPushout_ofHom` that is exactly this square. The square
is stated in `CommRingCat` rather than as `Algebra.IsPushout` so that the algebra structures are
not fixed inside an existential: a consumer reads it off with whichever of the two transport
lemmas it needs, and the *same* square also carries the `Algebra κ(w) Γ(G)` structure that the
localization statement uses.

The first cartesian square is returned as well, since the localization statement is about it. -/
theorem exists_isPushout_appTop_fibre_baseChange
    (hrep : yoneda.relativelyRepresentable p) (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y) (x : points B S hS X)
    {g : (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hdecY
        (pointsMap B S hS X p x)).1.siteObject B S hS Y}
    (hfib : IsPullback (residueFieldMorphism B S hS X hdecX x) (yoneda.map g) p
      (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)))
    (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y) (w : points B S hS (yoneda.obj V))
    (hw : pointsMap B S hS (yoneda.obj V) b w = pointsMap B S hS X p x) :
    ∃ (G : BigFppfOver B S hS)
      (iV : (residueFieldRepresentative B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V)
          w).1.siteObject B S hS (yoneda.obj V) ⟶ V)
      (u : G ⟶ hrep.pullback b)
      (q : G ⟶ (residueFieldRepresentative B S hS (yoneda.obj V)
          (isDecentSpace_yoneda B S hS V) w).1.siteObject B S hS (yoneda.obj V))
      (r : G ⟶ (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X)
      (ψ : residueField B S hS Y hdecY (pointsMap B S hS X p x) →+*
        residueField B S hS X hdecX x)
      (φ : residueField B S hS Y hdecY (pointsMap B S hS X p x) →+*
        residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w),
      yoneda.map iV = residueFieldMorphism B S hS (yoneda.obj V)
          (isDecentSpace_yoneda B S hS V) w ∧
        IsPullback (yoneda.map u) (yoneda.map q) (yoneda.map (hrep.snd b)) (yoneda.map iV) ∧
        IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
          ((Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS (yoneda.obj V)
              (isDecentSpace_yoneda B S hS V) w))).inv ≫
            ((BigFppfOver.toScheme B S hS).map q).appTop)
          ((Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS X hdecX x))).inv ≫
            ((BigFppfOver.toScheme B S hS).map r).appTop) := by
  obtain ⟨G, iV, u, q, r, e, φ, hiV, hφ, hsq, hcart⟩ :=
    exists_isPullback_toScheme_fibre_baseChange B S hS hrep hY hdecX hdecY x hfib V b w hw
  obtain ⟨ψ, hψ⟩ := exists_eq_specMap_of_hom_siteObject B S hS g
  refine ⟨G, iV, u, q, r, ψ, φ, hiV, hsq, isPushout_of_isPullback_specMap φ ψ ?_⟩
  have h0 := (IsPullback.of_map_of_faithful yoneda hcart).map (BigFppfOver.toScheme B S hS)
  rwa [show (BigFppfOver.toScheme B S hS).map g = Spec.map (CommRingCat.ofHom ψ) from hψ,
    show (BigFppfOver.toScheme B S hS).map e = Spec.map (CommRingCat.ofHom φ) from hφ] at h0

end Fibre

/-! ### The norm identity at the chart -/

section Norm

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : X ⟶ Y}

/-- **The norm identity of Stacks 0EQ4, read on a chart.** Let `p : X ⟶ Y` be a relatively
representable morphism of decent algebraic spaces, `x` a point of `X`, `b : V ⟶ Y` a morphism from
a representable space and `w` a point of `V`; let `G` be the fibre of `X ×_Y V ⟶ V` over the
chosen field-valued point of `w`, presented by the two squares of
`AlgebraicGeometry.Space.exists_isPushout_appTop_fibre_baseChange`. Suppose `Γ(X ×_Y V)` and
`Γ(V)` are the global sections of affine schemes, `Γ(V)` is a domain with fraction field `κ(w)`,
`Γ(G)` is reduced and `κ(x)` is finite over `κ(p x)`. Then for every `t` in `κ(x)`

`φ(Nm_{κ(x)/κ(p x)}(t)) = ∏ Nm_{Γ(G)/P Γ(G) over κ(w)}(t)`,

the product being over the primes `P` of `Γ(X ×_Y V)` which contract to the zero ideal of `Γ(V)` —
that is over the irreducible components of `X ×_Y V` which dominate `V`.

In Stacks 0EQ4 this is the field-theoretic step whose proof the source omits, with its two
hypotheses about the geometry discharged: `x` and `p x` are the generic points of the integral `X`
and `Y`, so `κ(x)` and `κ(p x)` are `R(X)` and `R(Y)`, `V` is a branch of an affine étale chart of
`Y` through the generic point of a prime divisor `Z`, `κ(w)` is `R(V)`, and the factors of `Γ(G)`
are the function fields of the components of `X ×_Y V` over `V`. What remains between this and
Stacks 0EQ4 is the coefficient identity; see the implementation notes of this module. -/
theorem norm_eq_finprod_norm_quotient_of_isPushout_fibre
    (hrep : yoneda.relativelyRepresentable p)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y) (x : points B S hS X)
    (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y) (w : points B S hS (yoneda.obj V))
    {G : BigFppfOver B S hS}
    {iV : (residueFieldRepresentative B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V)
        w).1.siteObject B S hS (yoneda.obj V) ⟶ V}
    {u : G ⟶ hrep.pullback b}
    {q : G ⟶ (residueFieldRepresentative B S hS (yoneda.obj V)
        (isDecentSpace_yoneda B S hS V) w).1.siteObject B S hS (yoneda.obj V)}
    {r : G ⟶ (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X}
    {ψ : residueField B S hS Y hdecY (pointsMap B S hS X p x) →+* residueField B S hS X hdecX x}
    {φ : residueField B S hS Y hdecY (pointsMap B S hS X p x) →+*
      residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (hrep.pullback b))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsDomain Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    [_root_.IsReduced ↥Γ((BigFppfOver.toScheme B S hS).obj G, ⊤)]
    (hsq : IsPullback (yoneda.map u) (yoneda.map q) (yoneda.map (hrep.snd b)) (yoneda.map iV))
    (hpush : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
      ((Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS (yoneda.obj V)
          (isDecentSpace_yoneda B S hS V) w))).inv ≫
        ((BigFppfOver.toScheme B S hS).map q).appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS X hdecX x))).inv ≫
        ((BigFppfOver.toScheme B S hS).map r).appTop))
    (hfrac :
      letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w) :=
        (((BigFppfOver.toScheme B S hS).map iV).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS (yoneda.obj V)
            (isDecentSpace_yoneda B S hS V) w))).hom).hom.toAlgebra
      IsFractionRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w))
    (hfin :
      letI : Algebra (residueField B S hS Y hdecY (pointsMap B S hS X p x))
          (residueField B S hS X hdecX x) := ψ.toAlgebra
      Module.Finite (residueField B S hS Y hdecY (pointsMap B S hS X p x))
        (residueField B S hS X hdecX x)) :
    letI : Algebra (residueField B S hS Y hdecY (pointsMap B S hS X p x))
        (residueField B S hS X hdecX x) := ψ.toAlgebra
    letI : Algebra (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w)
        Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS (yoneda.obj V)
          (isDecentSpace_yoneda B S hS V) w))).inv ≫
        ((BigFppfOver.toScheme B S hS).map q).appTop).hom.toAlgebra
    ∀ t : residueField B S hS X hdecX x,
      φ (Algebra.norm (residueField B S hS Y hdecY (pointsMap B S hS X p x)) t) =
        ∏ᶠ (P : PrimeSpectrum Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback b), ⊤))
          (_ : Ideal.comap ((BigFppfOver.toScheme B S hS).map (hrep.snd b)).appTop.hom
            P.asIdeal = ⊥),
          Algebra.norm (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w)
            (Ideal.Quotient.mk
                (P.asIdeal.map ((BigFppfOver.toScheme B S hS).map u).appTop.hom)
              (((Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS X hdecX x))).inv ≫
                ((BigFppfOver.toScheme B S hS).map r).appTop).hom t)) := by
  let : Algebra (residueField B S hS Y hdecY (pointsMap B S hS X p x))
      (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w) := φ.toAlgebra
  let : Algebra (residueField B S hS Y hdecY (pointsMap B S hS X p x))
      (residueField B S hS X hdecX x) := ψ.toAlgebra
  let : Algebra (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w)
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS (yoneda.obj V)
        (isDecentSpace_yoneda B S hS V) w))).inv ≫
      ((BigFppfOver.toScheme B S hS).map q).appTop).hom.toAlgebra
  let : Algebra (residueField B S hS X hdecX x)
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS X hdecX x))).inv ≫
      ((BigFppfOver.toScheme B S hS).map r).appTop).hom.toAlgebra
  let : Algebra (residueField B S hS Y hdecY (pointsMap B S hS X p x))
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS (yoneda.obj V)
        (isDecentSpace_yoneda B S hS V) w))).inv ≫
      ((BigFppfOver.toScheme B S hS).map q).appTop).hom.comp φ).toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback b), ⊤) :=
    ((BigFppfOver.toScheme B S hS).map (hrep.snd b)).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w) :=
    (((BigFppfOver.toScheme B S hS).map iV).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (residueField B S hS (yoneda.obj V)
        (isDecentSpace_yoneda B S hS V) w))).hom).hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback b), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map u).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
    (((BigFppfOver.toScheme B S hS).map u).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map (hrep.snd b)).appTop.hom).toAlgebra
  have := hfin
  have h2 := isPushout_appTop_of_isPullback_yoneda_fieldValuedPoint B S hS hsq
  have : IsScalarTower (residueField B S hS Y hdecY (pointsMap B S hS X p x))
      (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w)
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) := .of_algebraMap_eq' rfl
  have : IsScalarTower (residueField B S hS Y hdecY (pointsMap B S hS X p x))
      (residueField B S hS X hdecX x) Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
    .of_algebraMap_eq' (hom_comp_eq_of_isPushout_ofHom φ ψ _ _ hpush)
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback b), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w)
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
    .of_algebraMap_eq' (hom_comp_eq_of_isPushout_ofHom _ _ _ _ h2)
  have : Algebra.IsPushout (residueField B S hS Y hdecY (pointsMap B S hS X p x))
      (residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w)
      (residueField B S hS X hdecX x) Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
    algebraIsPushout_of_isPushout_ofHom φ ψ _ _ hpush
  have : IsLocalization (Algebra.algebraMapSubmonoid
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback b), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)⁰)
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) :=
    isLocalization_of_isPushout_ofHom _ _ _ _
      h2 hfrac
  exact fun t => Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout_of_isReduced
    (O := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (C := Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback b), ⊤))
    (T := Γ((BigFppfOver.toScheme B S hS).obj G, ⊤)) _ _ _ t

end Norm

end Space

end AlgebraicGeometry

end

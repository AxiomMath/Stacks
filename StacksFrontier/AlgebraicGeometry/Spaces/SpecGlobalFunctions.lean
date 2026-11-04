module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions

/-!
# The canonical morphism from an algebraic space to the spectrum of its global functions

Let `X` be an algebraic space over a scheme `S` of a big fppf site, with `S` terminal, and
write `A = Γ(X, 𝒪_X)` for its ring of global regular functions.  Pullback of regular functions
is a bijection between morphisms of algebraic spaces `X ⟶ T` into an affine object `T` of the
site and ring homomorphisms `Γ(T, 𝒪_T) →+* A` (Stacks 05Z1,
`AlgebraicGeometry.Space.morphismToAffineEquiv`).  Feeding the *identity* of `A` into the
inverse of that bijection, with `T = Spec A`, produces the canonical morphism
`p : X ⟶ Spec(A)`.

Two things stand between that sentence and a definition.  The ring `A` is a ring of compatible
families of functions indexed by the small étale site of `X`, so it lives one universe up and
`Spec A` is not a priori a scheme of the working universe, let alone an object of the site.
Both are repaired here, with no hypothesis: a surjective étale chart of `X` embeds `A` into the
regular functions on a single scheme of the site, so `A` is isomorphic to a ring of the working
universe whose spectrum satisfies the site's size cutoff.

## Main definitions

* `AlgebraicGeometry.Space.GlobalFunctionsModel` is a ring of the working universe isomorphic
  to the global functions, whose spectrum is an object of the ambient big fppf site.
* `AlgebraicGeometry.Space.specGlobalFunctions` is the spectrum of such a model, as an object
  of the big fppf site over the terminal base.
* `AlgebraicGeometry.Space.toSpecGlobalFunctions` is the canonical morphism
  `p : X ⟶ Spec(A)`, and
  `AlgebraicGeometry.Space.specGlobalFunctionsGamma` is the ring homomorphism it is built
  from, namely the canonical identification `Γ(Spec A, 𝒪) ≅ A`.
* `AlgebraicGeometry.Space.CohomologyVanishingSituation.toSpecGlobalFunctionsOfChosenModel` is
  the morphism `p : X → Spec(A)` of Situation 07UY, formed at the model chosen here.  It is the
  presentation-parameterised
  `AlgebraicGeometry.Space.CohomologyVanishingSituation.toSpecGlobalFunctions` of
  `StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingBaseChange` — which asks for an
  affine object of the site together with a ring isomorphism from its functions onto `A` —
  specialized to the presentation
  `AlgebraicGeometry.Space.CohomologyVanishingSituation.specGlobalFunctions` that the chosen
  small model supplies.

## Main results

* `AlgebraicGeometry.Space.nonempty_globalFunctionsModel`: every algebraic space has such a
  model.  This is the unconditional size statement, and it is what makes `Spec A` an object of
  the site.
* `AlgebraicGeometry.Space.pullbackToGlobalFunctions_toSpecGlobalFunctions` and
  `AlgebraicGeometry.Space.eq_toSpecGlobalFunctions`: pullback of regular functions along the
  canonical morphism is the canonical identification `Γ(Spec A, 𝒪) ≅ A`, and it is the only
  morphism of algebraic spaces `X ⟶ Spec A` with that property.  Together these are what makes
  `toSpecGlobalFunctions` *canonical* rather than an arbitrary morphism to an arbitrary affine
  object.
* `AlgebraicGeometry.Space.toSpecGlobalFunctions_chart`: the chart formula.  On every étale
  scheme chart `V` of `X`, the value at `V` of the global function attached to
  `s ∈ Γ(Spec A, 𝒪)` is the pullback of `s` along the morphism of schemes `V ⟶ Spec A` induced
  by `p`.

## Implementation notes

The ring `A` of the source is a ring of the *next* universe: it is
`AlgebraicGeometry.Space.globalFunctions`, the sections of the structure presheaf of the small
étale site, and that site lives in `Type (u + 1)`.  A model of it is therefore not a
convenience but the only way to write `Spec A` as a scheme of the working universe.  The model
is produced from any surjective étale chart `V` of `X`: restriction of global functions to `V`
is injective, by
`AlgebraicGeometry.Space.injective_globalFunctionsChartRestriction_of_isSurjective`, so `A` is
isomorphic to its image, a subring of `Γ(V, 𝒪_V)`.  That subring is a ring of the
working universe and
`AlgebraicGeometry.Scheme.size_Spec_lt_of_injective_sections` — Stacks 000R (9) for a ring
injecting into the sections of an object of `Sch_κ` — puts its spectrum in the site.  No
cardinality hypothesis on the site beyond its own two fields is used.

The base is required to be terminal, as in Stacks 05Z1.  It is needed twice over: the
bijection of 05Z1 takes that hypothesis, and `Spec A` carries no canonical morphism to a
general base `S` — the canonical ring map runs `Γ(S, 𝒪_S) → A`, the wrong way to make `Spec A`
a scheme over `S` — so the structure morphism of the object `Spec A` of the site has to be the
one a terminal base supplies.

A model is a choice, and different surjective étale charts give different (isomorphic) models;
that is why the model is an explicit argument of
`AlgebraicGeometry.Space.specGlobalFunctions` and of
`AlgebraicGeometry.Space.toSpecGlobalFunctions` rather than being chosen inside them.  The
choice is made only in
`AlgebraicGeometry.Space.CohomologyVanishingSituation.globalFunctionsModel`, where a single
object `Spec A` is wanted for the space of a vanishing situation, and there the morphism is
pinned down all the same: `eq_toSpecGlobalFunctions` identifies it for every model.

**What is not proved here.** Stacks 07V4 says that in Situation 07UY the morphism `p` is
universally injective, and that is not proved.  By Stacks 03MX,
`AlgebraicGeometry.Space.universallyInjective_tfae`, and by the field-point criterion
`AlgebraicGeometry.Space.universallyInjective_of_fieldPoints`, it is enough to show that for
every field `K` of the site the map `X(Spec K) → Hom_{Ring}(A, K)` induced by `p` is
injective, that is, that the global functions separate the `K`-valued points of `X`.  Two
inputs are missing for that, and both are where the first cohomology hypothesis of the
situation is consumed:

* Stacks 07V1 for an algebraic space — two disjoint closed subsets of `|X|` are separated by a
  global function.  `StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation` proves
  the comaximality step on an affine scheme, the chart criterion for a vanishing locus, and the
  step which consumes the cohomology hypothesis — that in Situation 07UY every global regular
  function on a closed subspace extends to the whole space,
  `AlgebraicGeometry.Space.CohomologyVanishingSituation.surjective_sectionsMap_structureProjection`
  — and its docstring names the two steps that still separate those from 07V1 itself.
* Stacks 07V0 — the base change of the situation along a ring map `A → A'`, which is what
  reduces 07V4 to the case of `A` a field.  Nothing in the tree states it.

With those, the remaining steps of the source's proof are available: Stacks 0488, the lift of a
point of `|X|` to a `K`-valued point over a large algebraically closed field, is
`AlgebraicGeometry.Space.exists_lift_of_large_field`, and Stacks 07U5, that such a point is a
closed point of `|X|`, is
`AlgebraicGeometry.Space.isClosed_singleton_class_of_isAlgebraic_residueField` — the latter
under condition `(α)` of Stacks 03JX, so a bridge from the quasi-separatedness of the situation
to that decency condition is wanted as well.

## References

* [Stacks Project, Lemma 66.6.6 (Tag 05Z1)](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07V4](https://stacks.math.columbia.edu/tag/07V4)
* [Stacks Project, Tag 07V1](https://stacks.math.columbia.edu/tag/07V1)
* [Stacks Project, Tag 03MX](https://stacks.math.columbia.edu/tag/03MX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A small model of the ring of global functions -/

/-- A *small model* of the ring of global regular functions of a presheaf `F` on the big fppf
site of `S`: a ring of the working universe, whose spectrum is an object of the site, together
with a ring isomorphism onto the global functions.

The global functions themselves are a ring of the next universe, so this is what lets `Spec`
of them be an object of the site. -/
structure GlobalFunctionsModel (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The modelling ring, in the working universe. -/
  ring : CommRingCat.{u}
  /-- Its spectrum satisfies the size cutoff of the ambient big fppf site. -/
  contains : B.Contains (Spec ring)
  /-- The identification of the modelling ring with the global functions. -/
  equiv : ring ≃+* globalFunctions B S hS F

/-- **Every algebraic space has a small model of its global functions.** Restriction of global
functions to a surjective étale chart is injective, so the global functions are isomorphic to
their image, a subring of the regular functions on a single scheme of the site; and a ring
injecting into the sections of an object of `Sch_κ` has its spectrum in `Sch_κ`. -/
theorem nonempty_globalFunctionsModel (X : AlgebraicSpaces B S hS) :
    Nonempty (GlobalFunctionsModel B S hS X.obj) := by
  obtain ⟨U, φ, hsurj, hetale⟩ := X.property.exists_atlas
  let V : SmallEtale B S hS X.obj := ⟨CostructuredArrow.mk φ, hetale⟩
  let ρ := globalFunctionsChartRestriction B S hS X V
  have hinj : Function.Injective ρ :=
    injective_globalFunctionsChartRestriction_of_isSurjective B S hS X V
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X.obj X.property U φ).1 hsurj)
  refine ⟨{ ring := CommRingCat.of ρ.range
            contains := ?_
            equiv := (RingEquiv.ofBijective ρ.rangeRestrict
              ⟨fun a b hab => hinj (congrArg Subtype.val hab),
                ρ.rangeRestrict_surjective⟩).symm }⟩
  exact Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (p := CommRingCat.ofHom ρ.range.subtype) Subtype.val_injective U.left.property

/-! ### The spectrum of the global functions as an object of the site -/

variable (X : AlgebraicSpaces B S hS) (M : GlobalFunctionsModel B S hS X.obj)
    (hterminal : IsTerminal S)

/-- The spectrum of a small model of the global functions of `X`, as an object of the big fppf
site over the terminal base `S`.  Its structure morphism is the one the terminal base
supplies. -/
def specGlobalFunctions : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (hterminal.from (Spec M.ring)) : B.obj M.contains ⟶ B.obj hS)

/-- The scheme underlying `AlgebraicGeometry.Space.specGlobalFunctions` is the spectrum of the
model. -/
lemma toScheme_obj_specGlobalFunctions :
    (BigFppfOver.toScheme B S hS).obj (specGlobalFunctions B S hS X M hterminal) =
      Spec M.ring := rfl

/-- The scheme underlying `AlgebraicGeometry.Space.specGlobalFunctions` is affine. -/
instance isAffine_toScheme_obj_specGlobalFunctions :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      (specGlobalFunctions B S hS X M hterminal)) := by
  rw [toScheme_obj_specGlobalFunctions]
  infer_instance

/-- The canonical identification of the regular functions on the spectrum of the model with
the global functions of `X`: the `Γ`–`Spec` isomorphism followed by the model's
isomorphism. -/
def specGlobalFunctionsGamma :
    Γ((BigFppfOver.toScheme B S hS).obj (specGlobalFunctions B S hS X M hterminal), ⊤) →+*
      globalFunctions B S hS X.obj :=
  M.equiv.toRingHom.comp (Scheme.ΓSpecIso M.ring).hom.hom

/-- **The canonical morphism `p : X ⟶ Spec(A)`.** It is the morphism of algebraic spaces which
Stacks 05Z1 attaches to the canonical identification of the regular functions on `Spec A` with
the global functions `A` of `X`. -/
def toSpecGlobalFunctions : X ⟶ schemeSpace (specGlobalFunctions B S hS X M hterminal) :=
  (morphismToAffineEquiv B S hS X (specGlobalFunctions B S hS X M hterminal) hterminal).1.symm
    (specGlobalFunctionsGamma B S hS X M hterminal)

/-- **The canonical morphism acts on functions by the canonical identification.** Pullback of
regular functions along `AlgebraicGeometry.Space.toSpecGlobalFunctions` is
`AlgebraicGeometry.Space.specGlobalFunctionsGamma`. -/
lemma pullbackToGlobalFunctions_toSpecGlobalFunctions :
    pullbackToGlobalFunctions B S hS X (specGlobalFunctions B S hS X M hterminal)
        (toSpecGlobalFunctions B S hS X M hterminal) =
      specGlobalFunctionsGamma B S hS X M hterminal :=
  (morphismToAffineEquiv B S hS X (specGlobalFunctions B S hS X M hterminal)
    hterminal).1.apply_symm_apply _

/-- **The canonical morphism is the unique one acting on functions by the canonical
identification.** This, with
`AlgebraicGeometry.Space.pullbackToGlobalFunctions_toSpecGlobalFunctions`, is what pins
`AlgebraicGeometry.Space.toSpecGlobalFunctions` down. -/
lemma eq_toSpecGlobalFunctions
    (f : X ⟶ schemeSpace (specGlobalFunctions B S hS X M hterminal))
    (hf : pullbackToGlobalFunctions B S hS X (specGlobalFunctions B S hS X M hterminal) f =
      specGlobalFunctionsGamma B S hS X M hterminal) :
    f = toSpecGlobalFunctions B S hS X M hterminal :=
  (morphismToAffineEquiv B S hS X (specGlobalFunctions B S hS X M hterminal)
      hterminal).1.injective
    (hf.trans (pullbackToGlobalFunctions_toSpecGlobalFunctions B S hS X M hterminal).symm)

/-- **The chart formula for the canonical morphism.** The global function attached to
`s ∈ Γ(Spec A, 𝒪)` takes, at an étale scheme chart `V` of `X`, the value obtained by pulling
`s` back along the morphism of schemes `V ⟶ Spec A` that `p` induces. -/
lemma toSpecGlobalFunctions_chart (V : SmallEtale B S hS X.obj)
    (s : Γ((BigFppfOver.toScheme B S hS).obj
      (specGlobalFunctions B S hS X M hterminal), ⊤)) :
    (specGlobalFunctionsGamma B S hS X M hterminal s).1 (op V) =
      (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (yoneda.preimage
        (V.1.hom ≫ (toSpecGlobalFunctions B S hS X M hterminal).hom))))).hom s := by
  rw [← pullbackToGlobalFunctions_toSpecGlobalFunctions B S hS X M hterminal]
  exact (morphismToAffineEquiv B S hS X (specGlobalFunctions B S hS X M hterminal)
    hterminal).2 (toSpecGlobalFunctions B S hS X M hterminal) V s

/-! ### The morphism `p : X → Spec(A)` of Situation 07UY -/

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, m})

/-- The ring `A = Γ(X, 𝒪_X)` of a vanishing situation is the ring of global regular functions
of its space: both are the same subring of the product, over the étale charts, of the regular
functions on the chart. -/
def globalFunctionsRingEquiv :
    T.globalFunctions ≃+*
      Space.globalFunctions T.site T.base T.containsBase T.space.obj :=
  RingEquiv.refl _

/-- A chosen small model of the ring `A = Γ(X, 𝒪_X)` of a vanishing situation. -/
def globalFunctionsModel :
    GlobalFunctionsModel T.site T.base T.containsBase T.space.obj :=
  (nonempty_globalFunctionsModel T.site T.base T.containsBase T.space).some

/-- `Spec(A)` for a vanishing situation whose base is terminal, as an object of the ambient big
fppf site. -/
def specGlobalFunctions (hterminal : IsTerminal T.base) :
    BigFppfOver T.site T.base T.containsBase :=
  Space.specGlobalFunctions T.site T.base T.containsBase T.space T.globalFunctionsModel
    hterminal

/-- **The morphism `p : X → Spec(A)` of Situation 07UY**, for a situation whose base is
terminal: the canonical morphism from the space of the situation to the spectrum of its ring of
global functions, formed at the chosen small model.

It is `AlgebraicGeometry.Space.CohomologyVanishingSituation.toSpecGlobalFunctions`, which takes
an arbitrary affine presentation of `Spec A`, at the presentation
`AlgebraicGeometry.Space.CohomologyVanishingSituation.specGlobalFunctions` coming from the
model, and `AlgebraicGeometry.Space.eq_toSpecGlobalFunctions` pins the two together. -/
def toSpecGlobalFunctionsOfChosenModel (hterminal : IsTerminal T.base) :
    T.space ⟶ schemeSpace (T.specGlobalFunctions hterminal) :=
  Space.toSpecGlobalFunctions T.site T.base T.containsBase T.space T.globalFunctionsModel
    hterminal

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end

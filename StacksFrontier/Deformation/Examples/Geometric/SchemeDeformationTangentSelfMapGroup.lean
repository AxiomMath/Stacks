module

public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationTangentFiberAut

/-!
# The group law on the `Inf` term of the deformation sequence of a scheme

Let `k` be a field and `X` a scheme over `k`. The term `Inf(𝓓_X)` of the exact sequences of
[Stacks Project, Tag 06L5] and [Stacks Project, Tag 0E3V] is
`Deformation.localizedAutomorphismFunctorTangent`, a `k`-vector space whose addition is given by
`Deformation.naturalLocalizedTangentAddCommGroup` and whose scalar action is given by
`Deformation.naturalLocalizedTangentModule`. Neither is defined by a formula: both are
transported, by `Deformation.exists_naturalLocalizedAutomorphismTangentVectorSpace`, from the
group of automorphisms of the chosen pushforward to the dual numbers that die under reduction to
the residue field. What that transport leaves behind is
`Deformation.naturalLocalizedTangentModule_spec`, the statement of [Stacks Project, Tag 06JV]
(1): addition goes to composition in that group, and the scalar action goes to transport along
the canonical scaling `Deformation.tangentScaling` of the dual-number coordinate.

`StacksFrontier/Deformation/Examples/Geometric/SchemeDeformationTangentFiberAut.lean` identifies
the carrier of the `Inf` term with honest self-maps of the total space of a first-order
deformation of `X`, as **bijections of sets only**. This file carries the *addition* across
those bijections, which is what a torsor computation in the sequence consumes: an action of the
`Inf` term by conjugation is an additive action precisely because addition there is composition.

## Main results

* `Deformation.Examples.localizedTangentEquivFiberAut_add`: addition on the `Inf` term is
  composition in the automorphism group of the chosen first-order pushforward.
* `Deformation.Examples.localizedTangentEquivSelfMaps_add`: addition on the `Inf` term is
  composition of self-maps of the total space.
* `Deformation.Examples.localizedTangentEquivLiftsOverBaseTop_add`: the same, read on the set of
  global lifts of the identity of `X` that [Stacks Project, Tag 0CK2] acts on.
* `Deformation.Examples.localizedTangentEquivFiberAut_zero` and
  `Deformation.Examples.localizedTangentEquivSelfMaps_zero`: the zero of the `Inf` term is the
  identity self-map.

## Implementation notes

Each statement is `Deformation.naturalLocalizedTangentModule_spec` composed with the
multiplicativity of the remaining steps of the identification. Those steps are genuinely
multiplicative and not merely bijective, which is why the addition crosses them:
`MulEquiv.subgroupCongr` and `Subgroup.topEquiv` are isomorphisms of groups,
`Deformation.Examples.autFiberBaseMulEquiv` is one, and
`Deformation.Examples.fiberAutEquivSelfMaps_mul` records the group law of the last step even
though that step is packaged as an `Equiv`. The identification of
`Deformation.Examples.localizedTangentEquivFiberAut` with the composite is `rfl`, so each proof
is a rewrite by the spec followed by `map_mul`.

The module structures are supplied by `letI` in both the statement and the proof, as everywhere
in `Deformation.Examples`: they are `@[instance_reducible]` definitions depending on the chosen
pushforward and on condition (RS), not instances.

## References

* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X : Over (Spec (CommRingCat.of k))}

/-- The identification of `Deformation.Examples.localizedTangentEquivFiberAut` with the
composite it is defined to be, as a pointwise equation available to `rw`. -/
private theorem localizedTangentEquivFiberAut_apply
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀)
    (a : localizedAutomorphismFunctorTangent P) :
    localizedTangentEquivFiberAut hp P a =
      autFiberBaseMulEquiv
          (P.obj (dualNumbersUnder
            (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀)))
        (((MulEquiv.subgroupCongr
            (ker_transportAutHom_eq_top_of_isThin.{u, u, u} hp.cofibered P
              (isThin_specialFiber.{u, u, u} hp) _)).trans
          Subgroup.topEquiv) (localizedTangentEquivKernel P a)) := rfl

/-! ### Addition on the `Inf` term is composition -/

/-- **Addition on the `Inf` term of the deformation sequence of a scheme is composition of
automorphisms.** The term is carried onto the automorphism group of the chosen first-order
pushforward by `Deformation.Examples.localizedTangentEquivFiberAut`, and that bijection is
multiplicative: addition on the term is composition in the subgroup of infinitesimal
automorphisms by [Stacks Project, Tag 06JV] (1), and the two remaining steps of the
identification are isomorphisms of groups. -/
theorem localizedTangentEquivFiberAut_add
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    (hrs : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    ∀ a b : localizedAutomorphismFunctorTangent P,
      localizedTangentEquivFiberAut hp P (a + b) =
        localizedTangentEquivFiberAut hp P a * localizedTangentEquivFiberAut hp P b := by
  let := naturalLocalizedTangentAddCommGroup P hrs
  let := naturalLocalizedTangentModule P hrs
  intro a b
  rw [localizedTangentEquivFiberAut_apply, localizedTangentEquivFiberAut_apply,
    localizedTangentEquivFiberAut_apply, (naturalLocalizedTangentModule_spec P hrs).1 a b,
    map_mul, map_mul]

/-- **The zero of the `Inf` term is the identity automorphism.** -/
theorem localizedTangentEquivFiberAut_zero
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    (hrs : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    localizedTangentEquivFiberAut hp P 0 = 1 := by
  let := naturalLocalizedTangentAddCommGroup P hrs
  let := naturalLocalizedTangentModule P hrs
  rw [localizedTangentEquivFiberAut_apply, localizedTangentEquivKernel_eq_one P hrs,
    map_one, map_one]

/-! ### Addition on the `Inf` term is composition of self-maps -/

/-- **Addition on the `Inf` term of the deformation sequence of a scheme is composition of
self-maps of the total space.** This is the form a torsor computation consumes: the conjugation
action of the `Inf` term on a set of lifts is an *additive* action because the self-map attached
to a sum is the composite of the two self-maps.

For a scheme this is the infinitesimal-automorphism clause of [Stacks Project, Tag 0DY9] at the
term that actually appears in the sequence of [Stacks Project, Tag 0E3V]:
`Deformation.Examples.localizedTangentEquivSelfMaps` is a bijection of sets, and this says it
carries the addition of the `Inf` term to composition. -/
theorem localizedTangentEquivSelfMaps_add
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    (hrs : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    ∀ a b : localizedAutomorphismFunctorTangent P,
      (localizedTangentEquivSelfMaps hp P (a + b)).1 =
        (localizedTangentEquivSelfMaps hp P a).1 ≫ (localizedTangentEquivSelfMaps hp P b).1 := by
  let := naturalLocalizedTangentAddCommGroup P hrs
  let := naturalLocalizedTangentModule P hrs
  intro a b
  show (fiberAutEquivSelfMaps (firstOrderPushforward P)
      (localizedTangentEquivFiberAut hp P (a + b))).1 = _
  rw [localizedTangentEquivFiberAut_add hp hrs P a b]
  exact fiberAutEquivSelfMaps_mul (firstOrderPushforward P) _ _

/-- **The zero of the `Inf` term is the identity self-map.** -/
theorem localizedTangentEquivSelfMaps_zero
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    (hrs : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    (localizedTangentEquivSelfMaps hp P 0).1 = 𝟙 (firstOrderPushforward P).scheme := by
  let := naturalLocalizedTangentAddCommGroup P hrs
  let := naturalLocalizedTangentModule P hrs
  show (fiberAutEquivSelfMaps (firstOrderPushforward P)
      (localizedTangentEquivFiberAut hp P 0)).1 = _
  rw [localizedTangentEquivFiberAut_zero hp hrs P]
  rfl

/-! ### The scalar action on the `Inf` term is transport along the coordinate scaling -/

/-- **The scalar action on the `Inf` term of the deformation sequence of a scheme is transport
along the scaling of the infinitesimal coordinate.** This is the companion of
`Deformation.Examples.localizedTangentEquivFiberAut_add` for the second clause of
[Stacks Project, Tag 06JV] (1): the term is carried onto the automorphism group of the chosen
first-order pushforward by `Deformation.Examples.localizedTangentEquivFiberAut`, and the
automorphism attached to `c • a` is the one attached to `a` transported along
`Deformation.tangentScaling`, the self-map `ε ↦ cε` of the dual numbers under the base.

Unlike addition, the scalar action does not cross the identification as an algebraic operation
on the automorphism group: that group carries no scalar action. What crosses is the *transport*,
so the right-hand side names `Deformation.ChosenPushforwards.transportAutHom` rather than an
operation applied to `localizedTangentEquivFiberAut hp P a`. -/
theorem localizedTangentEquivFiberAut_smul
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    (hrs : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    ∀ (c : k) (a : localizedAutomorphismFunctorTangent P),
      localizedTangentEquivFiberAut hp P (c • a) =
        autFiberBaseMulEquiv
            (P.obj (dualNumbersUnder
              (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀)))
          (P.transportAutHom
            (tangentScaling (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
              (x := x₀) c) (localizedTangentEquivKernel P a).1) := by
  let := naturalLocalizedTangentAddCommGroup P hrs
  let := naturalLocalizedTangentModule P hrs
  intro c a
  rw [localizedTangentEquivFiberAut_apply]
  exact congrArg (autFiberBaseMulEquiv _) ((naturalLocalizedTangentModule_spec P hrs).2 c a)

/-- **The self-map of a scaled tangent vector, as a conjugation relation against the coordinate
scaling.** This is the form the homogeneity of the arrow `b` of [Stacks Project, Tag 0E3V]
consumes, and it is the whole of what the abstract torsor argument can be told about the scalar
action of the `Inf` term.

Write `σ_c` for the morphism of total spaces underlying the transport of the chosen first-order
pushforward along `Deformation.tangentScaling`, that is along `ε ↦ cε`. Then the self-map
attached to `c • a` and the self-map attached to `a` are conjugate across `σ_c`:

`α_{c • a} ≫ σ_c = σ_c ≫ α_a`.

This is `Deformation.ChosenPushforwards.map_transportHom` — the defining property of transport —
read on total spaces, where the contravariance of
`Deformation.Examples.SchemeDeformationCategory.Hom` reverses each composite, composed with
`Deformation.naturalLocalizedTangentModule_spec` (2), which says that the scalar action of the
tangent space *is* that transport.

Nothing here computes `σ_c`. That the conjugation relation forces the derivation attached to
`α_{c • a}` to be `c` times the one attached to `α_a` is a separate computation with the
coordinate of the dual numbers. -/
theorem localizedTangentEquivSelfMaps_smul_comp
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    (hrs : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    ∀ (c : k) (a : localizedAutomorphismFunctorTangent P),
      (localizedTangentEquivSelfMaps hp P (c • a)).1 ≫
          (P.map (tangentScaling
            (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀) c)).map =
        (P.map (tangentScaling
            (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀) c)).map ≫
          (localizedTangentEquivSelfMaps hp P a).1 := by
  let := naturalLocalizedTangentAddCommGroup P hrs
  let := naturalLocalizedTangentModule P hrs
  intro c a
  -- the scalar action of the tangent space is the transport, whose defining square is
  -- `map_transportHom`, read on total spaces
  rw [show (localizedTangentEquivSelfMaps hp P (c • a)).1 = (P.transportHom (tangentScaling c)
    (localizedTangentEquivKernel P a).1).map from
    congrArg (·.asIso.hom.val.map) ((naturalLocalizedTangentModule_spec P hrs).2 c a)]
  exact congrArg (·.map) (P.map_transportHom (tangentScaling c) (localizedTangentEquivKernel P a).1)

end Deformation.Examples

end

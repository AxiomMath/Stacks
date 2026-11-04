module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryFactorization
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.FiniteStalk
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardMono

/-!
# The minimal step of the factorization into glueings and squishings

The proof of [Stacks, Tag 0C1L] reaches, once the inductive splittings are exhausted, a finite
morphism `f : X' ⟶ X` of algebraic `k`-schemes which admits no proper intermediate
factorization. It then passes to the local algebra `A = 𝒪_{X, x} ⊂ (f_*𝒪_{X'})_x = B` at the
point where `f` is not an isomorphism, finds that the fibre `C = B ⧸ m_A B` has exactly two
`k`-subalgebras, concludes from [Stacks, Tag 0C1I] that `C` is `k × k` or `k[ε]`, and reads the
two cases as a glueing of two points respectively a squishing of a tangent vector.

This file carries out that passage, in both directions: from the geometry to the fibre, and from
the fibre back to the geometry. What it does **not** do is prove the sheaf-theoretic clauses of
`AlgebraicGeometry.IsGlueingTwoPoints` and `AlgebraicGeometry.IsSquishingTangentVector`; see the
implementation notes for exactly what of those predicates is delivered and what is not.

## Main definitions

* `Stacks.GlueSquishFactor.basePoint` is the image of the closed point under a rational point
  `Spec k ⟶ X`, the point at which all the stalks below are taken.
* `Stacks.GlueSquishFactor.stalkPushforwardMap` is the extension `A ⟶ B` of the source, and
  `Stacks.GlueSquishFactor.stalkFibreIdeal` is the ideal `m_A B` it is divided by.
* `Stacks.GlueSquishFactor.stalkConstMap` is the structure map `k ⟶ 𝒪_{X, x}` of a `k`-scheme.
* `Stacks.GlueSquishFactor.fromSpecPushforwardStalk` is the morphism
  `Spec (f_*𝒪_{X'})_x ⟶ X'` for an affine `f`, and
  `Stacks.GlueSquishFactor.pointOfStalkHom` is the point of `X'` it produces from a ring map out
  of that stalk.
* `Stacks.GlueSquishFactor.IsGlueingFibreSequenceAt` collects, for two rational points of `X'`
  over a point of `X`, the two germ-level clauses of
  `AlgebraicGeometry.IsGlueingTwoPoints` which express the short exact sequence
  `0 → 𝒪_X → f_*𝒪_{X'} → x_*k → 0`. It exists only so that the two results proving it need not
  repeat it verbatim.

## Main results

* `Stacks.GlueSquishFactor.exists_sub_stalkConstMap_mem_maximalIdeal` — the residue field of a
  `k`-scheme at a rational point is `k`, in the form in which [Stacks, Tag 0C1I] needs it.
* `Stacks.GlueSquishFactor.fibre_algEquiv_prod_or_dualNumber` — **the one-step classification at
  the stalk**: for a finite `f` and a point whose residue field is `k`, if the stalk extension
  `A ⊂ B` is proper and admits no intermediate `A`-subalgebra, then the fibre `B ⧸ m_A B` is
  `k × k` or the dual numbers `k[ε]`. This is the algebraic half of the minimal step with its
  hypotheses read off the geometry.
* `Stacks.GlueSquishFactor.fromSpecPushforwardStalk_comp` — the morphism out of
  `Spec (f_*𝒪_{X'})_x` lies over `Spec 𝒪_{X, x} ⟶ X`.
* `Stacks.GlueSquishFactor.pointOfStalkHom_comp` and
  `Stacks.GlueSquishFactor.stalkPushforwardMap_comp_eq` — a map out of the stalk which kills
  `m_A B` and is a map of `k`-algebras produces a point of `X'` lying over `x`.
* `Stacks.GlueSquishFactor.exists_affineOpen_pointOfStalkHom_ne` — distinct maps out of the
  stalk produce distinct points.
* `Stacks.GlueSquishFactor.fromSpecPushforwardStalk_eq` and
  `Stacks.GlueSquishFactor.pointOfStalkHom_eq` — the morphism out of `Spec (f_*𝒪_{X'})_x`, and
  hence the point it produces, does not depend on the affine open used to build it.
* `Stacks.GlueSquishFactor.germ_stalkClosedPointTo_pointOfStalkHom_of_mem` and
  `Stacks.GlueSquishFactor.sectionAt_pointOfStalkHom` — **the stalk-to-germ dictionary**:
  evaluation at the rational point attached to `χ : (f_*𝒪_{X'})_x ⟶ k` of a section of
  `𝒪_{X'}` over `f ⁻¹ᵁ W`, for *any* open `W ∋ x`, is `χ` applied to the germ of that section.
* `Stacks.GlueSquishFactor.exists_app_eq_of_germ_mem_range` — a section of `𝒪_{X'}` whose germ
  in `(f_*𝒪_{X'})_x` comes from `𝒪_{X, x}` is, on a smaller neighbourhood of `x`, in the image
  of `f.app`.
* `Stacks.GlueSquishFactor.exists_two_points_of_fibre_algEquiv_prod` and
  `Stacks.GlueSquishFactor.exists_tangentVector_of_fibre_algEquiv_dualNumber` — **the geometry
  recovered from the fibre**: a fibre `k × k` gives two distinct rational points of `X'` over
  `x`, and a fibre `k[ε]` gives a dual-number-valued point of `X'` contracted to `x` and defined
  over `k`.
* `Stacks.GlueSquishFactor.exists_two_points_sequence_of_stalkHom_ne` and
  `Stacks.GlueSquishFactor.exists_two_points_sequence_of_fibre_algEquiv_prod` — **the glueing
  case with its fibre sequence**: a fibre `k × k` gives the two points *together with* the two
  germ-level clauses of `AlgebraicGeometry.IsGlueingTwoPoints` that express the short exact
  sequence, i.e. `Stacks.GlueSquishFactor.IsGlueingFibreSequenceAt`.
* `Stacks.GlueSquishFactor.exists_glueing_or_squishing_data_of_minimal` — the two halves
  composed: a minimal `f` either identifies two distinct rational points over `x` or contracts a
  tangent vector to `x`.
* `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_fibre_algEquiv_prod` — **the glueing
  half of the one-step classification, reduced to one clause**: under the hypotheses of the
  minimal step, the inclusion `𝒪_X ⊂ f_*𝒪_{X'}` in its sectionwise form, and the single
  additional hypothesis that `f` restricts to an isomorphism over the complement of `x`,
  `AlgebraicGeometry.IsGlueingTwoPoints` holds in full.
* `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod` — the same
  with `𝒪_X ⊂ f_*𝒪_{X'}` in the sheaf form `Mono (pushforwardAlgebra f).hom` that
  `Stacks.GlueSquishFactor.IsAlmostIso` carries, the two being interchangeable by
  `Stacks.GlueSquishFactor.injective_app_of_mono_hom_pushforwardAlgebra`.

## Implementation notes

**From the geometry to the fibre.** The three algebra structures of
`Stacks.GlueSquishFactor.fibre_algEquiv_prod_or_dualNumber` are introduced with `letI` inside
the statement, matching `Stacks.GlueSquishFactor.module_finite_stalk_pushforward`, whose
conclusion supplies the `Module.Finite` hypothesis of
`Stacks.GlueSquishFactor.algEquiv_prod_or_dualNumber_of_minimal`. The `k`-algebra structure on
`B` is the one that factors through `A`, so that the scalar tower is `rfl`. The hypothesis that
the residue field at the point is `k` is carried as an explicit `hres` rather than as the
existence of a rational point, so that the statement need not mention a morphism `Spec k ⟶ X`
whose base point is the given point;
`Stacks.GlueSquishFactor.exists_sub_stalkConstMap_mem_maximalIdeal` supplies it at the base
point of any rational point, from `AlgebraicGeometry.sectionAt_constHom`: the value of a constant
section at a rational point is that constant, so a germ differs from the constant with its own
value by something that `AlgebraicGeometry.Scheme.stalkClosedPointTo` sends to `0`, hence by a
non-unit.

**From the fibre to the geometry.** A point of `X'` is produced from a ring map `χ` out of the
stalk `B` and not from a map out of the sections over some open: the stalk is the localisation of
`Γ(X', f ⁻¹ᵁ U)` at the prime of `Γ(X, U)` attached to `x`, so `Spec χ` followed by
`Spec (f_*𝒪_{X'})_x ⟶ Spec Γ(X', f ⁻¹ᵁ U) ≅ f ⁻¹ᵁ U ⟶ X'` is a morphism `Spec T ⟶ X'`, and
this is what makes the two clauses below come out of ring-level identities.

* *Lying over `x`.* `Stacks.GlueSquishFactor.fromSpecPushforwardStalk_comp` says the morphism
  `Spec B ⟶ X'` composed with `f` is `Spec (A ⟶ B)` followed by
  `AlgebraicGeometry.Scheme.fromSpecStalk`. So the composite of the produced point with `f`
  depends only on `A ⟶ B ⟶ T`, and that composite is the evaluation at `x` followed by `k ⟶ T`
  as soon as `χ` kills `m_A B` and is a map of `k`-algebras — because every germ at `x` is a
  constant modulo `m_A`. Then
  `AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk` identifies the result with
  `x` itself (for `T = k`) or with `dualNumberToBase k ≫ x` (for `T = k[ε]`). Rationality of the
  produced point, and the clause `θ ≫ (X' ↘ Spec k) = dualNumberToBase k`, are then formal
  consequences of `f` being defined over `k`.
* *Distinctness.* The two points of the glueing case are distinct because the two projections of
  `k × k` differ on the fibre. Transporting that to the points needs an affine open `U` small
  enough that the element of `B` where the two maps differ is a germ of a section over
  `f ⁻¹ᵁ U`: the germ map `Γ(X', f ⁻¹ᵁ U) ⟶ B` is not surjective, so distinctness of the maps
  out of `B` does not by itself give distinctness of the maps out of the sections. Shrinking `U`
  is harmless because the point produced does not depend on it, which is why
  `Stacks.GlueSquishFactor.exists_affineOpen_pointOfStalkHom_ne` is stated with the affine open
  existentially quantified.

**From the stalk to the germs.** The germ-level clauses of
`AlgebraicGeometry.IsGlueingTwoPoints` are phrased with `AlgebraicGeometry.sectionAt`, so
transporting the stalk-level fibre sequence of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryFactorization` to them needs
`AlgebraicGeometry.Scheme.stalkClosedPointTo (pointOfStalkHom f hU hx χ)` computed in terms of
`χ`. That is `Stacks.GlueSquishFactor.germ_stalkClosedPointTo_pointOfStalkHom`, and it is not an
instance of `AlgebraicGeometry.Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk`: the latter is
about `Spec.map χ ≫ X'.fromSpecStalk y` for a point `y` of `X'`, whereas `(f_*𝒪_{X'})_x` is not
a stalk of `X'` at all — it is semilocal, see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.FiniteStalk`. What replaces it is that
`Stacks.GlueSquishFactor.pointOfStalkHom` factors through
`AlgebraicGeometry.IsAffineOpen.fromSpec` of `f ⁻¹ᵁ U`, so
`AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec` and the monomorphy of `fromSpec` identify
`a.appLE (f ⁻¹ᵁ U) ⊤` with the germ followed by `χ`, and
`AlgebraicGeometry.germ_stalkClosedPointTo_appLE` turns that into the evaluation. The passage
from the chosen affine `U` to an arbitrary open `W ∋ x`, which the predicate quantifies over, is
`Stacks.GlueSquishFactor.pointOfStalkHom_eq` together with the fact that the base point of the
produced point specializes over `x`, hence lies in `f ⁻¹ᵁ W` for every such `W`
(`Stacks.GlueSquishFactor.pointOfStalkHom_mem_preimage_of_mem`).

**What is still missing in the minimal case.** `AlgebraicGeometry.IsGlueingTwoPoints` and
`AlgebraicGeometry.IsSquishingTangentVector` each ask for more than the data produced here. Of
the clauses of `AlgebraicGeometry.IsGlueingTwoPoints`, this file delivers `a ≠ b`, the
rationality of `a` and `b`, `a ≫ f = b ≫ f` (indeed both are `x`), and — in
`Stacks.GlueSquishFactor.exists_two_points_sequence_of_fibre_algEquiv_prod` — the two germ-level
clauses `Stacks.GlueSquishFactor.IsGlueingFibreSequenceAt` expressing exactness in the middle and
surjectivity onto the skyscraper. The third germ-level clause, injectivity, is
`Stacks.GlueSquishFactor.map_eq_zero_of_map_app_eq_zero` and needs only `𝒪_X ⊂ f_*𝒪_{X'}`. What
is *not* delivered is the clause `IsIso (f ∣_ U)` for `U` the complement of the glued point — it
is the hypothesis "`f` is an isomorphism away from a finite set" of
`Stacks.GlueSquishFactor.IsAlmostIso` only once one knows that the bad set is the single point
`x`, which is the case `n = 1` of the source's induction and not a statement about one point. Of
the clauses of `AlgebraicGeometry.IsSquishingTangentVector`, it delivers
`θ ≫ f = dualNumberToBase k ≫ x` and `θ ≫ (X' ↘ Spec k) = dualNumberToBase k`; it delivers
neither `IsClosedImmersion θ` nor the exact sequence. Both are supplied in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingProducer`, and the squishing side
is **not** an analogue of the glueing side there:
`AlgebraicGeometry.IsSquishingTangentVector` states its exactness as an honest
`CategoryTheory.ShortComplex.ShortExact` in the category of sheaves of abelian groups on `X`, not
as germ-local clauses, so a morphism of sheaves has to be *constructed* out of the stalk-level
results `Stacks.GlueSquishFactor.exists_algebraMap_eq_of_dualNumber_snd_eq_zero` and
`Stacks.GlueSquishFactor.exists_dualNumber_snd_eq` rather than read off them. Only the clause
pinning down the values of that morphism is germ-local, through
`AlgebraicGeometry.epsilonCoefficientAt`, and it is
`Stacks.GlueSquishFactor.epsilonCoefficientAt_pointOfStalkHom` — the `DualNumber k` reading of
`Stacks.GlueSquishFactor.germ_stalkClosedPointTo_pointOfStalkHom_of_mem`, which is why the germ
dictionary below is stated for an arbitrary local-ring target and not only for `k`. Of the
results below only `Stacks.GlueSquishFactor.exists_app_eq_of_germ_mem_range`, which mentions no
character, is shared between the two cases.

**The fibre as a set of points.** The missing sheaf clauses are statements about *all* the
points of `X'` over `x`, and the tree already has the dictionary they would be proved through:
for an integral — in particular a finite — morphism,
`AlgebraicGeometry.Scheme.Hom.exists_fibreEquivMaximalSpectrum` ([Stacks, Tag 0C3B]) identifies
the fibre `{y : X' // f y = x}` with the maximal spectrum of the same stalk `B` used here,
compatibly with residue fields. Since every maximal ideal of an integral extension of a local
ring contains `m_A B`, that maximal spectrum is the maximal spectrum of the fibre `B ⧸ m_A B`,
so a fibre `k × k` would say the morphism is bijective away from two points of `X'` and a fibre
`k[ε]` that it is bijective away from one. Nothing below uses this; it is recorded because it is
the natural next step and is easy to miss.

**What is still missing in [Stacks, Tag 0C1L] as a whole.** The *measure* of the induction — the
length of the coherent `𝒪_X`-module `f_*𝒪_{X'}/𝒪_X` — is not constructed anywhere, so the
hypothesis `hsplit` of `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` cannot be
discharged. What is in the tree is that this length is *finite* at every point, in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsLength`, and that the support of
the quotient is finite; what is not is the comparison of the measures of the two halves of a
splitting, which is additivity of length in
`0 → 𝒜/𝒪_X → f_*𝒪_{X'}/𝒪_X → f_*𝒪_{X'}/𝒜 → 0` together with a fibre sum over the points of
`Spec_X(𝒜)`.

A subalgebra `𝒜` for `Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_algebraHom` *is*
produced, from a single section, in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SubalgebraProducer`; what that producer
does not give is a *proper* `𝒜`, which is what the hypotheses `hne` and `hmin` of the results
below would have to be contradicted to obtain: a proper intermediate `A`-subalgebra of `B` has
to be spread out to a quasi-coherent subalgebra of `f_*𝒪_{X'}`, and that is the step this file
stops short of.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1I](https://stacks.math.columbia.edu/tag/0C1I)
* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
* [Stacks Project, Tag 0C1K](https://stacks.math.columbia.edu/tag/0C1K)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.GlueSquishFactor

/-- The map of stalks `𝒪_{X, x} ⟶ (f_*𝒪_{X'})_x` induced by a morphism `f : X' ⟶ X`; this is
the algebra structure of [Stacks, Tag 0C1L]'s local algebra extension `A ⊂ B`. -/
abbrev stalkPushforwardMap {X' X : Scheme.{u}} (f : X' ⟶ X) (x : X) :
    X.presheaf.stalk x ⟶ (f.base _* X'.presheaf).stalk x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.c

/-- The structure map `k ⟶ 𝒪_{X, x}` of a scheme over `k`: a constant global section,
followed by the germ at `x`. -/
def stalkConstMap {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] (x : X) :
    CommRingCat.of k ⟶ X.presheaf.stalk x :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ ⊤ (by simp) ≫
    X.presheaf.germ ⊤ x trivial

/-- **The base point of a rational point.** The image of the closed point of `Spec k` under a
morphism `Spec k ⟶ X`; the point of `X` at which [Stacks, Tag 0C1L] takes stalks. -/
abbrev basePoint {k : Type u} [Field k] {X : Scheme.{u}} (x : Spec (.of k) ⟶ X) : X :=
  x.base (IsLocalRing.closedPoint k)

/-- The ideal `m_x · (f_*𝒪_{X'})_x` of the stalk of the pushforward: the ideal the fibre
`C = B ⧸ m_A B` of [Stacks, Tag 0C1L] is the quotient by. -/
abbrev stalkFibreIdeal {X' X : Scheme.{u}} (f : X' ⟶ X) (x : X) :
    Ideal ((f.base _* X'.presheaf).stalk x) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map (stalkPushforwardMap f x).hom

/-- **The residue field of a `k`-scheme at a rational point is `k`.** Every germ at a rational
point `x` of a scheme over `k` is a constant modulo the maximal ideal of the stalk.

This is the hypothesis `hres` of
`Stacks.GlueSquishFactor.algEquiv_prod_or_dualNumber_of_minimal`, and it is the only place where
the rationality of the point `x` of [Stacks, Tag 0C1L] is used in the local algebra. -/
@[ega "I 3.4.5" "partial"]
theorem exists_sub_stalkConstMap_mem_maximalIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (x : Spec (.of k) ⟶ X) (hx : x.IsOver (Spec (.of k)))
    (a : X.presheaf.stalk (basePoint x)) :
    ∃ c : k, a - (stalkConstMap X (basePoint x)).hom c ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (basePoint x)) := by
  refine ⟨(Scheme.stalkClosedPointTo x).hom a, ?_⟩
  have hc : (Scheme.stalkClosedPointTo x).hom
      ((stalkConstMap X (basePoint x)).hom
        ((Scheme.stalkClosedPointTo x).hom a)) = (Scheme.stalkClosedPointTo x).hom a :=
    sectionAt_constHom x hx ⊤ trivial (by simp) _
  have hzero : (Scheme.stalkClosedPointTo x).hom
      (a - (stalkConstMap X (basePoint x)).hom
        ((Scheme.stalkClosedPointTo x).hom a)) = 0 := by
    rw [map_sub, hc, sub_self]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hunit := hu.map (Scheme.stalkClosedPointTo x).hom
  rw [hzero] at hunit
  exact zero_ne_one (isUnit_zero_iff.mp hunit)

/-- **The one-step classification of [Stacks, Tag 0C1L], at the stalk.** -/
theorem fibre_algEquiv_prod_or_dualNumber {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsFinite f] (pt : X)
    (hres : ∀ a : X.presheaf.stalk pt, ∃ c : k,
      a - (stalkConstMap X pt).hom c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk pt)) :
    letI : Algebra (X.presheaf.stalk pt) ((f.base _* X'.presheaf).stalk pt) :=
      (stalkPushforwardMap f pt).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk pt) := (stalkConstMap X pt).hom.toAlgebra
    letI : Algebra k ((f.base _* X'.presheaf).stalk pt) :=
      ((stalkPushforwardMap f pt).hom.comp (stalkConstMap X pt).hom).toAlgebra
    (⊥ : Subalgebra (X.presheaf.stalk pt) ((f.base _* X'.presheaf).stalk pt)) ≠ ⊤ →
      (∀ E : Subalgebra (X.presheaf.stalk pt) ((f.base _* X'.presheaf).stalk pt),
        E = ⊥ ∨ E = ⊤) →
      Nonempty (((f.base _* X'.presheaf).stalk pt ⧸
          stalkFibreIdeal f pt) ≃ₐ[k] k × k) ∨
        Nonempty (((f.base _* X'.presheaf).stalk pt ⧸
          stalkFibreIdeal f pt) ≃ₐ[k] DualNumber k) := by
  let : Algebra (X.presheaf.stalk pt) ((f.base _* X'.presheaf).stalk pt) :=
    (stalkPushforwardMap f pt).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk pt) := (stalkConstMap X pt).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk pt) :=
    ((stalkPushforwardMap f pt).hom.comp (stalkConstMap X pt).hom).toAlgebra
  have : IsScalarTower k (X.presheaf.stalk pt) ((f.base _* X'.presheaf).stalk pt) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite (X.presheaf.stalk pt) ((f.base _* X'.presheaf).stalk pt) :=
    module_finite_stalk_pushforward f pt
  intro hne hmin
  exact algEquiv_prod_or_dualNumber_of_minimal k _ _ hres hne hmin

/-! ### The spectrum of the stalk of the pushforward -/

/-- The sections of `f_*𝒪_{X'}` over `U`, pushed into the stalk at `x`, computed through the
sections of `𝒪_{X'}` over `f ⁻¹ᵁ U`. -/
theorem app_comp_germ_pushforward {X' X : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens) (x : X)
    (hx : x ∈ U) :
    f.app U ≫ (f.base _* X'.presheaf).germ U x hx =
      X.presheaf.germ U x hx ≫ stalkPushforwardMap f x :=
  (TopCat.Presheaf.stalkFunctor_map_germ U x hx f.c).symm

/-- **`Spec` of the stalk `(f_*𝒪_{X'})_x`, as a point of `X'`.** For an affine `f` and an
affine open `U ∋ x`, the preimage `f ⁻¹ᵁ U` is affine and the stalk is a localisation of its
sections, so the germ map gives a morphism `Spec (f_*𝒪_{X'})_x ⟶ f ⁻¹ᵁ U ⟶ X'`. -/
def fromSpecPushforwardStalk {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    Spec ((f.base _* X'.presheaf).stalk x) ⟶ X' :=
  Spec.map ((f.base _* X'.presheaf).germ U x hx) ≫ (hU.preimage f).fromSpec

/-- **The morphism out of the spectrum of the stalk lies over the corresponding morphism of
the base.** -/
theorem fromSpecPushforwardStalk_comp {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    fromSpecPushforwardStalk f hU hx ≫ f =
      Spec.map (stalkPushforwardMap f x) ≫ X.fromSpecStalk x := by
  have hfrom : (hU.preimage f).fromSpec ≫ f = Spec.map (f.app U) ≫ hU.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl,
      Scheme.Hom.appLE_eq_app]
  rw [fromSpecPushforwardStalk, Category.assoc, hfrom, ← Spec.map_comp_assoc,
    app_comp_germ_pushforward f U x hx, Spec.map_comp_assoc]
  rw [show Spec.map (X.presheaf.germ U x hx) ≫ hU.fromSpec = X.fromSpecStalk x from
    hU.fromSpecStalk_eq_fromSpecStalk hx]

/-! ### The points of `X'` attached to the fibre -/

/-- The value at a rational point of the constant section with value `c` is `c`, read in the
stalk. -/
theorem stalkClosedPointTo_stalkConstMap {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (x : Spec (.of k) ⟶ X) (hx : x.IsOver (Spec (.of k))) (c : k) :
    (Scheme.stalkClosedPointTo x).hom
        ((stalkConstMap X (basePoint x)).hom c) = c :=
  sectionAt_constHom x hx ⊤ trivial (by simp) c

/-- The maximal ideal of the stalk at a rational point is killed by evaluation at that point:
`AlgebraicGeometry.Scheme.stalkClosedPointTo` is a local homomorphism into a field. -/
theorem stalkClosedPointTo_eq_zero_of_mem_maximalIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    (x : Spec (.of k) ⟶ X)
    {y : X.presheaf.stalk (basePoint x)}
    (hy : y ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (basePoint x))) :
    (Scheme.stalkClosedPointTo x).hom y = 0 := by
  by_contra hne
  exact (IsLocalRing.mem_maximalIdeal y).mp hy
    (isUnit_of_map_unit (Scheme.stalkClosedPointTo x).hom y
      (isUnit_iff_ne_zero.mpr (show (Scheme.stalkClosedPointTo x).hom y ≠ (0 : k) from hne)))

/-- **A `k`-algebra map out of the fibre computes the evaluation at the point.** If `χ` kills
`m_A B` and is a map of `k`-algebras to `T`, then its composite with
`𝒪_{X, x} ⟶ (f_*𝒪_{X'})_x` is the evaluation at `x` followed by `k ⟶ T`: every germ at `x` is
a constant modulo `m_A`, and `χ` sees only that constant. -/
theorem stalkPushforwardMap_comp_eq {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X.Over (Spec (.of k))] (f : X' ⟶ X) (x : Spec (.of k) ⟶ X) (hx : x.IsOver (Spec (.of k)))
    {T : CommRingCat.{u}} (ι : CommRingCat.of k ⟶ T)
    (χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ T)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal
        (X.presheaf.stalk (basePoint x)),
      χ.hom ((stalkPushforwardMap f (basePoint x)).hom a) = 0)
    (hk : ∀ c : k, χ.hom ((stalkPushforwardMap f (basePoint x)).hom
      ((stalkConstMap X (basePoint x)).hom c)) = ι.hom c) :
    stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ ι := by
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  obtain ⟨c, hc⟩ := exists_sub_stalkConstMap_mem_maximalIdeal x hx a
  have hχ : χ.hom ((stalkPushforwardMap f (basePoint x)).hom a)
      = ι.hom c := by
    have h0 := hm _ hc
    rw [map_sub, map_sub, sub_eq_zero] at h0
    rw [h0, hk]
  have hval : (Scheme.stalkClosedPointTo x).hom a = c := by
    have h0 := stalkClosedPointTo_eq_zero_of_mem_maximalIdeal x hc
    rw [map_sub, sub_eq_zero, stalkClosedPointTo_stalkConstMap x hx] at h0
    exact h0
  change χ.hom ((stalkPushforwardMap f (basePoint x)).hom a)
    = ι.hom ((Scheme.stalkClosedPointTo x).hom a)
  rw [hχ, hval]

/-- **The point of `X'` attached to a ring map out of the stalk of `f_*𝒪_{X'}`.** -/
def pointOfStalkHom {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {T : CommRingCat.{u}}
    (χ : (f.base _* X'.presheaf).stalk x ⟶ T) : Spec T ⟶ X' :=
  Spec.map χ ≫ fromSpecPushforwardStalk f hU hx

/-- **The point attached to a `k`-algebra map out of the fibre lies over `x`.** -/
theorem pointOfStalkHom_comp {k : Type u} [Field k] {X' X : Scheme.{u}} [X.Over (Spec (.of k))]
    (f : X' ⟶ X) [IsAffineHom f] (x : Spec (.of k) ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (hx : basePoint x ∈ U) {T : CommRingCat.{u}}
    (ι : CommRingCat.of k ⟶ T)
    (χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ T)
    (hχ : stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ ι) :
    pointOfStalkHom f hU hx χ ≫ f = Spec.map ι ≫ x := by
  rw [pointOfStalkHom, Category.assoc, fromSpecPushforwardStalk_comp, ← Spec.map_comp_assoc, hχ,
    Spec.map_comp_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

/-- **Distinct maps out of the stalk give distinct points.** An affine open small enough to
see where the two maps differ separates the two points they define; the point does not depend
on the affine open, so this is a statement about the points themselves. -/
theorem exists_affineOpen_pointOfStalkHom_ne {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f]
    {x : X} {T : CommRingCat.{u}} {χ₁ χ₂ : (f.base _* X'.presheaf).stalk x ⟶ T} (h : χ₁ ≠ χ₂) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V),
      pointOfStalkHom f hV hxV χ₁ ≠ pointOfStalkHom f hV hxV χ₂ := by
  have hex : ∃ b, χ₁.hom b ≠ χ₂.hom b := by
    by_contra hcon
    push Not at hcon
    exact h (CommRingCat.hom_ext (RingHom.ext hcon))
  obtain ⟨b, hb⟩ := hex
  obtain ⟨W, hxW, s, hs⟩ := (f.base _* X'.presheaf).exists_germ_eq b
  obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxW
  refine ⟨V, hV, hxV, fun hEq => hb ?_⟩
  have hEq' : Spec.map ((f.base _* X'.presheaf).germ V x hxV ≫ χ₁) ≫ (hV.preimage f).fromSpec =
      Spec.map ((f.base _* X'.presheaf).germ V x hxV ≫ χ₂) ≫ (hV.preimage f).fromSpec := by
    simpa only [pointOfStalkHom, fromSpecPushforwardStalk, Spec.map_comp, Category.assoc]
      using hEq
  have hring : (f.base _* X'.presheaf).germ V x hxV ≫ χ₁ =
      (f.base _* X'.presheaf).germ V x hxV ≫ χ₂ :=
    Spec.map_injective ((cancel_mono (hV.preimage f).fromSpec).mp hEq')
  have hW : (f.base _* X'.presheaf).germ W x hxW ≫ χ₁ =
      (f.base _* X'.presheaf).germ W x hxW ≫ χ₂ := by
    rw [← TopCat.Presheaf.germ_res _ (homOfLE hVW) x hxV, Category.assoc, Category.assoc, hring]
  have happ := congrArg (fun t : (f.base _* X'.presheaf).obj (op W) ⟶ T => t.hom s) hW
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hs] using happ

/-! ### Evaluating a section at the point attached to a map out of the stalk -/

/-- Shrinking the affine open does not change the morphism out of `Spec (f_*𝒪_{X'})_x`. -/
theorem fromSpecPushforwardStalk_eq_of_le {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) {x : X} (hxV : x ∈ V)
    (hVU : V ≤ U) :
    fromSpecPushforwardStalk f hU (hVU hxV) = fromSpecPushforwardStalk f hV hxV := by
  have hres : (f.base _* X'.presheaf).map (homOfLE hVU).op =
      X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op := rfl
  rw [fromSpecPushforwardStalk, fromSpecPushforwardStalk,
    ← TopCat.Presheaf.germ_res (f.base _* X'.presheaf) (homOfLE hVU) x hxV, Spec.map_comp,
    Category.assoc, hres,
    IsAffineOpen.map_fromSpec (hU.preimage f) (hV.preimage f)
      (homOfLE (f.preimage_mono hVU)).op]

/-- **The morphism out of `Spec (f_*𝒪_{X'})_x` does not depend on the affine open.** The
analogue for the pushforward stalk of `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq`; it is
what makes `Stacks.GlueSquishFactor.pointOfStalkHom` a function of the ring map alone. -/
theorem fromSpecPushforwardStalk_eq {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) {x : X} (hxU : x ∈ U)
    (hxV : x ∈ V) :
    fromSpecPushforwardStalk f hU hxU = fromSpecPushforwardStalk f hV hxV := by
  obtain ⟨W, hW, hxW, hWle⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  exact (fromSpecPushforwardStalk_eq_of_le f hU hW hxW (hWle.trans inf_le_left)).trans
    (fromSpecPushforwardStalk_eq_of_le f hV hW hxW (hWle.trans inf_le_right)).symm

/-- **The point of `X'` attached to a map out of the stalk does not depend on the affine
open.** -/
theorem pointOfStalkHom_eq {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {x : X} (hxU : x ∈ U) (hxV : x ∈ V)
    {T : CommRingCat.{u}} (χ : (f.base _* X'.presheaf).stalk x ⟶ T) :
    pointOfStalkHom f hU hxU χ = pointOfStalkHom f hV hxV χ := by
  rw [pointOfStalkHom, pointOfStalkHom, fromSpecPushforwardStalk_eq f hU hV hxU hxV]

/-- The point attached to a map out of the stalk takes its values in `f ⁻¹ᵁ U`: it factors
through `AlgebraicGeometry.IsAffineOpen.fromSpec` of that open. -/
theorem pointOfStalkHom_mem_preimage {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {T : CommRingCat.{u}}
    (χ : (f.base _* X'.presheaf).stalk x ⟶ T) (t : Spec T) :
    (pointOfStalkHom f hU hx χ).base t ∈ f ⁻¹ᵁ U := by
  have hmem : (pointOfStalkHom f hU hx χ).base t ∈
      Set.range (hU.preimage f).fromSpec.base := ⟨_, rfl⟩
  rwa [(hU.preimage f).range_fromSpec] at hmem

/-- **The germ at the base point of the attached rational point is the map out of the stalk.**
For a ring map `χ : (f_*𝒪_{X'})_x ⟶ k`, evaluation of a section of `𝒪_{X'}` over `f ⁻¹ᵁ U` at
the rational point `Stacks.GlueSquishFactor.pointOfStalkHom f hU hx χ` is `χ` applied to the
germ of that section in `(f_*𝒪_{X'})_x`.

This is the identity that transports the stalk-level clauses of a minimal step to the germ-level
clauses of `AlgebraicGeometry.IsGlueingTwoPoints`: the predicate is phrased with
`AlgebraicGeometry.sectionAt`, and this computes `sectionAt` at the points the classification
produces.

The target is an arbitrary local ring `R`, not only a field: for `R = DualNumber k` the same
identity computes `AlgebraicGeometry.epsilonCoefficientAt` at the tangent vector attached to a
map of the stalk into the dual numbers. -/
theorem germ_stalkClosedPointTo_pointOfStalkHom {R : Type u} [CommRing R] [IsLocalRing R]
    {X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsAffineHom f] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk x ⟶ CommRingCat.of R) :
    X'.presheaf.germ (f ⁻¹ᵁ U) _
          (pointOfStalkHom_mem_preimage f hU hx χ (IsLocalRing.closedPoint R)) ≫
        Scheme.stalkClosedPointTo (pointOfStalkHom f hU hx χ) =
      (f.base _* X'.presheaf).germ U x hx ≫ χ := by
  set a := pointOfStalkHom f hU hx χ with ha
  set ψ : Γ(X', f ⁻¹ᵁ U) ⟶ CommRingCat.of R :=
    (f.base _* X'.presheaf).germ U x hx ≫ χ with hψ
  have hfac : a = Spec.map ψ ≫ (hU.preimage f).fromSpec := by
    rw [ha, pointOfStalkHom, fromSpecPushforwardStalk, hψ, Spec.map_comp, Category.assoc]
  have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U) :=
    (Scheme.preimage_eq_top_of_closedPoint_mem a
      (pointOfStalkHom_mem_preimage f hU hx χ (IsLocalRing.closedPoint R))).ge
  have happ : a.appLE (f ⁻¹ᵁ U) ⊤ hle = ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
    refine Spec.map_injective ((cancel_mono (hU.preimage f).fromSpec).mp ?_)
    rw [IsAffineOpen.SpecMap_appLE_fromSpec a (hU.preimage f)
        (isAffineOpen_top (Spec (CommRingCat.of R))) hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, Spec.map_comp, Category.assoc, ← hfac]
  rw [germ_stalkClosedPointTo_appLE a (f ⁻¹ᵁ U)
      (pointOfStalkHom_mem_preimage f hU hx χ (IsLocalRing.closedPoint R)),
    happ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The previous result for a morphism *presented* as a point attached to a map out of the
stalk. Stated with the equation as a hypothesis so that the affine open defining the point can
be changed without rewriting under the dependent membership proof of the germ. -/
theorem germ_stalkClosedPointTo_eq_pointOfStalkHom {R : Type u} [CommRing R] [IsLocalRing R]
    {X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsAffineHom f] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk x ⟶ CommRingCat.of R)
    (a : Spec (CommRingCat.of R) ⟶ X') (hae : a = pointOfStalkHom f hU hx χ)
    (hmem : a.base (IsLocalRing.closedPoint R) ∈ f ⁻¹ᵁ U) :
    X'.presheaf.germ (f ⁻¹ᵁ U) _ hmem ≫ Scheme.stalkClosedPointTo a =
      (f.base _* X'.presheaf).germ U x hx ≫ χ := by
  subst hae
  exact germ_stalkClosedPointTo_pointOfStalkHom f hU hx χ

/-- The image of the attached point under `f` specializes to `x`: the point factors through
`Spec 𝒪_{X, x} ⟶ X`, whose range is the set of such points ([Stacks, Tag 01J7]). -/
theorem pointOfStalkHom_specializes {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {T : CommRingCat.{u}}
    (χ : (f.base _* X'.presheaf).stalk x ⟶ T) (t : Spec T) :
    f.base ((pointOfStalkHom f hU hx χ).base t) ⤳ x := by
  have hcomp : pointOfStalkHom f hU hx χ ≫ f =
      Spec.map χ ≫ Spec.map (stalkPushforwardMap f x) ≫ X.fromSpecStalk x := by
    rw [pointOfStalkHom, Category.assoc, fromSpecPushforwardStalk_comp]
  have hbase := congrArg (fun g : Spec T ⟶ X => g.base t) hcomp
  have h : f.base ((pointOfStalkHom f hU hx χ).base t) ∈
      Set.range (X.fromSpecStalk x).base :=
    ⟨_, hbase.symm⟩
  rwa [Scheme.range_fromSpecStalk] at h

/-- The base point of the attached rational point lies in `f ⁻¹ᵁ W` for **every** open
`W ∋ x`, not only for the affine open used to define it. -/
theorem pointOfStalkHom_mem_preimage_of_mem {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {T : CommRingCat.{u}}
    (χ : (f.base _* X'.presheaf).stalk x ⟶ T) {W : X.Opens} (hxW : x ∈ W) (t : Spec T) :
    (pointOfStalkHom f hU hx χ).base t ∈ f ⁻¹ᵁ W :=
  (pointOfStalkHom_specializes f hU hx χ t).mem_open W.2 hxW

/-- **The germ identity over an arbitrary open.** The affine open `U` only enters through the
stalk at `x`, so the computation of
`AlgebraicGeometry.Scheme.stalkClosedPointTo (pointOfStalkHom f hU hx χ)` holds on the sections
over `f ⁻¹ᵁ W` for every open `W ∋ x`. This is the form the germ-level clauses of
`AlgebraicGeometry.IsGlueingTwoPoints`, which quantify over all such `W`, need, and — at
`R = DualNumber k` — the form in which the `ε`-coefficient clause of
`AlgebraicGeometry.IsSquishingTangentVector` needs it. -/
theorem germ_stalkClosedPointTo_pointOfStalkHom_of_mem {R : Type u} [CommRing R] [IsLocalRing R]
    {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f] {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) (χ : (f.base _* X'.presheaf).stalk x ⟶ CommRingCat.of R)
    {W : X.Opens} (hxW : x ∈ W) :
    X'.presheaf.germ (f ⁻¹ᵁ W) _
          (pointOfStalkHom_mem_preimage_of_mem f hU hx χ hxW (IsLocalRing.closedPoint R)) ≫
        Scheme.stalkClosedPointTo (pointOfStalkHom f hU hx χ) =
      (f.base _* X'.presheaf).germ W x hxW ≫ χ := by
  obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxW
  have hmemV := pointOfStalkHom_mem_preimage_of_mem f hU hx χ hxV (IsLocalRing.closedPoint R)
  have key := germ_stalkClosedPointTo_eq_pointOfStalkHom f hV hxV χ _
    (pointOfStalkHom_eq f hU hV hx hxV χ) hmemV
  have hres : (f.base _* X'.presheaf).map (homOfLE hVW).op =
      X'.presheaf.map (homOfLE (f.preimage_mono hVW)).op := rfl
  rw [← TopCat.Presheaf.germ_res X'.presheaf (homOfLE (f.preimage_mono hVW)) _ hmemV,
    Category.assoc, key,
    ← TopCat.Presheaf.germ_res (f.base _* X'.presheaf) (homOfLE hVW) x hxV, Category.assoc,
    hres]

/-- **Evaluation at the attached rational point is the map out of the stalk.** The `sectionAt`
form of `Stacks.GlueSquishFactor.germ_stalkClosedPointTo_pointOfStalkHom_of_mem`: the value at
`pointOfStalkHom f hU hx χ` of a section over `f ⁻¹ᵁ W` is `χ` of its germ in
`(f_*𝒪_{X'})_x`. -/
theorem sectionAt_pointOfStalkHom {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    [IsAffineHom f] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk x ⟶ CommRingCat.of k) {W : X.Opens} (hxW : x ∈ W)
    (s : Γ(X', f ⁻¹ᵁ W)) :
    AlgebraicGeometry.sectionAt (pointOfStalkHom f hU hx χ) (f ⁻¹ᵁ W)
        (pointOfStalkHom_mem_preimage_of_mem f hU hx χ hxW (IsLocalRing.closedPoint k)) s =
      χ.hom ((f.base _* X'.presheaf).germ W x hxW s) :=
  congrArg (fun t : Γ(X', f ⁻¹ᵁ W) ⟶ CommRingCat.of k => t.hom s)
    (germ_stalkClosedPointTo_pointOfStalkHom_of_mem f hU hx χ hxW)

/-! ### Exactness in the middle, transported from the stalk to the germs -/

/-- **A section whose germ comes from the base is, near the point, in the image of `f.app`.**
Let `s` be a section of `𝒪_{X'}` over `f ⁻¹ᵁ W` whose germ in `(f_*𝒪_{X'})_x` lies in the image
of `𝒪_{X, x} ⟶ (f_*𝒪_{X'})_x`. Then on some smaller open neighbourhood `V` of `x` the
restriction of `s` is `f.app V` of a section of `𝒪_X` over `V`.

This is what turns the stalk-level exactness statements
`Stacks.GlueSquishFactor.exists_algebraMap_eq_of_prod_fst_eq_snd` and
`Stacks.GlueSquishFactor.exists_algebraMap_eq_of_dualNumber_snd_eq_zero` into the germ-level
"exactness in the middle" clause of `AlgebraicGeometry.IsGlueingTwoPoints` respectively
`AlgebraicGeometry.IsSquishingTangentVector`, and it is independent of which character is used:
the element of `𝒪_{X, x}` the stalk statement produces is itself a germ, two germs of
`f_*𝒪_{X'}` which agree at `x` agree on a neighbourhood, and `f.app` commutes with
restriction. -/
theorem exists_app_eq_of_germ_mem_range {X' X : Scheme.{u}} (f : X' ⟶ X) {pt : X}
    (W : X.Opens) (hxW : pt ∈ W) (s : Γ(X', f ⁻¹ᵁ W))
    (hs : ∃ α : X.presheaf.stalk pt, (stalkPushforwardMap f pt).hom α =
      (f.base _* X'.presheaf).germ W pt hxW s) :
    ∃ (V : X.Opens) (hVW : V ≤ W) (_ : pt ∈ V) (t : Γ(X, V)),
      (X'.presheaf.map (homOfLE (f.preimage_mono hVW)).op).hom s = (f.app V).hom t := by
  obtain ⟨α, hα⟩ := hs
  obtain ⟨V₀, hxV₀, t₀, ht₀⟩ := X.presheaf.exists_germ_eq α
  have hgerm : (f.base _* X'.presheaf).germ V₀ pt hxV₀ ((f.app V₀).hom t₀) =
      (f.base _* X'.presheaf).germ W pt hxW s := by
    have h := congrArg (fun m : Γ(X, V₀) ⟶ (f.base _* X'.presheaf).stalk pt => m.hom t₀)
      (app_comp_germ_pushforward f V₀ pt hxV₀)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
    rw [h, ht₀, hα]
  obtain ⟨V, hxV, iV₀, iW, hVeq⟩ :=
    TopCat.Presheaf.germ_eq (f.base _* X'.presheaf) pt hxV₀ hxW _ _ hgerm
  refine ⟨V, iW.le, hxV, (X.presheaf.map iV₀.op).hom t₀, ?_⟩
  have hnat := congrArg (fun m : Γ(X, V₀) ⟶ Γ(X', f ⁻¹ᵁ V) => m.hom t₀) (f.naturality iV₀.op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hnat
  rw [hnat]
  exact hVeq.symm

/-! ### The geometric data of a minimal step -/

/-- A point of `X'` lying over a rational point of `X` is rational. -/
theorem isOver_of_comp_eq {k : Type u} [Field k] {X' X : Scheme.{u}} [X'.Over (Spec (.of k))]
    [X.Over (Spec (.of k))] {f : X' ⟶ X} (hf : f.IsOver (Spec (.of k)))
    {x : Spec (.of k) ⟶ X} (hx : x.IsOver (Spec (.of k)))
    {a : Spec (.of k) ⟶ X'} (ha : a ≫ f = x) : a.IsOver (Spec (.of k)) := by
  rw [Scheme.Hom.isOver_iff, ← hf.1, ← Category.assoc, ha, hx.1]

/-- A dual-number-valued point of `X'` contracted to a rational point of `X` is defined over
`k`: this is the clause `θ ≫ (X' ↘ Spec k) = dualNumberToBase k` of
`AlgebraicGeometry.IsSquishingTangentVector`. -/
theorem comp_structureMorphism_of_comp_eq {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] {f : X' ⟶ X}
    (hf : f.IsOver (Spec (.of k))) {x : Spec (.of k) ⟶ X} (hx : x.IsOver (Spec (.of k)))
    {θ : Spec (.of (DualNumber k)) ⟶ X'} (hθ : θ ≫ f = dualNumberToBase k ≫ x) :
    θ ≫ (X' ↘ Spec (.of k)) = dualNumberToBase k := by
  have hself : (Spec (.of k) ↘ Spec (.of k)) = 𝟙 (Spec (.of k)) := rfl
  rw [← hf.1, ← Category.assoc, hθ, Category.assoc, hx.1, hself, Category.comp_id]

/-- **A `k`-algebra map out of the fibre evaluates germs at the point.** Pulled back to the
stalk `B`, a `k`-algebra map `B ⧸ m_A B ⟶ T` composed with `𝒪_{X, x} ⟶ B` is the evaluation at
the rational point `x` followed by `k ⟶ T`. -/
theorem stalkPushforwardMap_comp_eq_of_fibreAlgHom {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X.Over (Spec (.of k))] (f : X' ⟶ X) (x : Spec (.of k) ⟶ X) (hx : x.IsOver (Spec (.of k)))
    (T : Type u) [CommRing T] [Algebra k T] :
    letI : Algebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk (basePoint x)) :=
      (stalkConstMap X (basePoint x)).hom.toAlgebra
    letI : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      ((stalkPushforwardMap f (basePoint x)).hom.comp
        (stalkConstMap X (basePoint x)).hom).toAlgebra
    ∀ ψ : ((f.base _* X'.presheaf).stalk (basePoint x) ⧸
        stalkFibreIdeal f (basePoint x)) →ₐ[k] T,
      stalkPushforwardMap f (basePoint x) ≫
          CommRingCat.ofHom (ψ.toRingHom.comp
            (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x)))) =
        Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k T) := by
  let : Algebra (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (basePoint x)) :=
    (stalkConstMap X (basePoint x)).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    ((stalkPushforwardMap f (basePoint x)).hom.comp
      (stalkConstMap X (basePoint x)).hom).toAlgebra
  intro ψ
  refine stalkPushforwardMap_comp_eq f x hx _ _ (fun a ha => ?_) (fun c => ?_)
  · change ψ (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x))
      ((stalkPushforwardMap f (basePoint x)).hom a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha), map_zero]
  · change ψ (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x))
        ((stalkPushforwardMap f (basePoint x)).hom
          ((stalkConstMap X (basePoint x)).hom c))) = algebraMap k T c
    rw [show (stalkPushforwardMap f (basePoint x)).hom
          ((stalkConstMap X (basePoint x)).hom c) =
        algebraMap k ((f.base _* X'.presheaf).stalk (basePoint x)) c
      from rfl, Ideal.Quotient.mk_algebraMap]
    exact ψ.commutes c

/-- A `k`-point of the stalk over the evaluation at `x` gives a point of `X'` mapping to `x`. -/
private theorem pointOfStalkHom_comp_eq_of_algebraMap_self {k : Type u} [Field k]
    {X' X : Scheme.{u}} [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsAffineHom f]
    (x : Spec (.of k) ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) (hxV : basePoint x ∈ V)
    {χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ CommRingCat.of k}
    (h : stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k k)) :
    pointOfStalkHom f hV hxV χ ≫ f = x := by
  have h := pointOfStalkHom_comp f x hV hxV _ χ h
  rwa [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at h

/-- **Two distinct `k`-points of the stalk give two distinct rational points of `X'` over
`x`.** This is the data of a glueing of two points: `a ≠ b` and `a ≫ f = b ≫ f`, both rational
over `k`. -/
theorem exists_two_points_of_stalkHom_ne {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsAffineHom f]
    (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X) (hx : x.IsOver (Spec (.of k)))
    {χ₁ χ₂ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶
      CommRingCat.of k}
    (h₁ : stalkPushforwardMap f (basePoint x) ≫ χ₁ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k k))
    (h₂ : stalkPushforwardMap f (basePoint x) ≫ χ₂ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k k))
    (hne : χ₁ ≠ χ₂) :
    ∃ a b : Spec (.of k) ⟶ X', a ≠ b ∧ a ≫ f = x ∧ b ≫ f = x ∧
      a.IsOver (Spec (.of k)) ∧ b.IsOver (Spec (.of k)) := by
  obtain ⟨V, hV, hxV, hVne⟩ := exists_affineOpen_pointOfStalkHom_ne f hne
  have ha := pointOfStalkHom_comp_eq_of_algebraMap_self f x hV hxV h₁
  have hb := pointOfStalkHom_comp_eq_of_algebraMap_self f x hV hxV h₂
  exact ⟨_, _, hVne, ha, hb, isOver_of_comp_eq hf hx ha, isOver_of_comp_eq hf hx hb⟩

/-- **The two germ-level clauses of `AlgebraicGeometry.IsGlueingTwoPoints` which express the
fibre sequence**, for a morphism `f`, a point `pt` of `X` and two rational points `a, b` of
`X'`: *exactness in the middle* of `0 → 𝒪_X → f_*𝒪_{X'} → pt_*k → 0` — a section of `𝒪_{X'}`
whose values at `a` and `b` agree comes, near `pt`, from `𝒪_X` — and *surjectivity* onto the
skyscraper — every element of `k` is the difference of the values of some section.

This is written out as a definition only to avoid repeating it verbatim in the two results
below; it is quoted, clause for clause, from `AlgebraicGeometry.IsGlueingTwoPoints`, with the
membership hypotheses universally quantified instead of derived from the glued point (they are
propositions, so the two readings agree). The third germ-level clause of the predicate,
injectivity, is `Stacks.GlueSquishFactor.map_eq_zero_of_map_app_eq_zero` and involves neither
`pt` nor the fibre. -/
def IsGlueingFibreSequenceAt {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X) (pt : X)
    (a b : Spec (CommRingCat.of k) ⟶ X') : Prop :=
  (∀ (W : X.Opens) (_ : pt ∈ W)
      (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ W)
      (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ W) (s : Γ(X', f ⁻¹ᵁ W)),
    AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ W) ha s -
        AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ W) hb s = 0 →
      ∃ (V : X.Opens) (hVW : V ≤ W) (_ : pt ∈ V) (t : Γ(X, V)),
        (X'.presheaf.map (homOfLE (f.preimage_mono hVW)).op).hom s = (f.app V).hom t) ∧
    ∀ c : k, ∃ (W : X.Opens) (_ : pt ∈ W)
        (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ W)
        (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ W) (s : Γ(X', f ⁻¹ᵁ W)),
      AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ W) ha s -
        AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ W) hb s = c

/-- **The two points of a glueing, together with the germ-level exactness of the fibre
sequence.** The hypotheses `hmid` and `hsurj` are the two stalk-level clauses — the image of
`𝒪_{X, x}` in `(f_*𝒪_{X'})_x` is exactly where the two characters agree, and their difference is
onto `k` — and the conclusion is the pair of rational points of `X'` over `x` *together with the
two germ-level clauses of `AlgebraicGeometry.IsGlueingTwoPoints` that constrain them*: exactness
in the middle, and surjectivity onto the skyscraper.

This is the transport that `Stacks.GlueSquishFactor.sectionAt_pointOfStalkHom` and
`Stacks.GlueSquishFactor.exists_app_eq_of_germ_mem_range` make possible: the predicate is phrased
with `AlgebraicGeometry.sectionAt`, and the first of those computes `sectionAt` at the produced
points as the character applied to the germ. The membership hypotheses `ha` and `hb` are
universally quantified rather than derived, which is harmless — they are propositions, so the
clause specialises to the proofs the predicate uses. -/
theorem exists_two_points_sequence_of_stalkHom_ne {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsAffineHom f]
    (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X) (hx : x.IsOver (Spec (.of k)))
    {χ₁ χ₂ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ CommRingCat.of k}
    (h₁ : stalkPushforwardMap f (basePoint x) ≫ χ₁ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k k))
    (h₂ : stalkPushforwardMap f (basePoint x) ≫ χ₂ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k k))
    (hne : χ₁ ≠ χ₂)
    (hmid : ∀ g : (f.base _* X'.presheaf).stalk (basePoint x), χ₁.hom g = χ₂.hom g →
      ∃ α : X.presheaf.stalk (basePoint x), (stalkPushforwardMap f (basePoint x)).hom α = g)
    (hsurj : ∀ c : k, ∃ g : (f.base _* X'.presheaf).stalk (basePoint x),
      χ₁.hom g - χ₂.hom g = c) :
    ∃ a b : Spec (.of k) ⟶ X', a ≠ b ∧ a ≫ f = x ∧ b ≫ f = x ∧
      a.IsOver (Spec (.of k)) ∧ b.IsOver (Spec (.of k)) ∧
      IsGlueingFibreSequenceAt f (basePoint x) a b := by
  obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show basePoint x ∈ (⊤ : X.Opens) from trivial)
  have ha := pointOfStalkHom_comp_eq_of_algebraMap_self f x hV hxV h₁
  have hb := pointOfStalkHom_comp_eq_of_algebraMap_self f x hV hxV h₂
  have hab : pointOfStalkHom f hV hxV χ₁ ≠ pointOfStalkHom f hV hxV χ₂ := by
    obtain ⟨V', hV', hxV', hV'ne⟩ := exists_affineOpen_pointOfStalkHom_ne f hne
    rw [pointOfStalkHom_eq f hV hV' hxV hxV' χ₁, pointOfStalkHom_eq f hV hV' hxV hxV' χ₂]
    exact hV'ne
  refine ⟨_, _, hab, ha, hb, isOver_of_comp_eq hf hx ha, isOver_of_comp_eq hf hx hb, ?_, ?_⟩
  · intro W hxW haW hbW s hs
    rw [sectionAt_pointOfStalkHom f hV hxV χ₁ hxW s, sectionAt_pointOfStalkHom f hV hxV χ₂ hxW s,
      sub_eq_zero] at hs
    exact exists_app_eq_of_germ_mem_range f W hxW s (hmid _ hs)
  · intro c
    obtain ⟨g, hg⟩ := hsurj c
    obtain ⟨W, hxW, s, hs⟩ := (f.base _* X'.presheaf).exists_germ_eq g
    refine ⟨W, hxW, pointOfStalkHom_mem_preimage_of_mem f hV hxV χ₁ hxW _,
      pointOfStalkHom_mem_preimage_of_mem f hV hxV χ₂ hxW _, s, ?_⟩
    rw [sectionAt_pointOfStalkHom f hV hxV χ₁ hxW s,
      sectionAt_pointOfStalkHom f hV hxV χ₂ hxW s, hs]
    exact hg

/-- **A dual-number-valued point of the stalk gives a tangent vector of `X'` contracted to
`x`.** This is the data of a squishing of a tangent vector: the two clauses
`θ ≫ f = dualNumberToBase k ≫ x` and `θ ≫ (X' ↘ Spec k) = dualNumberToBase k` of
`AlgebraicGeometry.IsSquishingTangentVector`. -/
theorem exists_tangentVector_of_stalkHom {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsAffineHom f]
    (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X) (hx : x.IsOver (Spec (.of k)))
    (χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶
      CommRingCat.of (DualNumber k))
    (hχ : stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k (DualNumber k))) :
    ∃ θ : Spec (.of (DualNumber k)) ⟶ X', θ ≫ f = dualNumberToBase k ≫ x ∧
      θ ≫ (X' ↘ Spec (.of k)) = dualNumberToBase k := by
  obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show basePoint x ∈ (⊤ : X.Opens) from trivial)
  have hcontract : pointOfStalkHom f hV hxV χ ≫ f = dualNumberToBase k ≫ x :=
    pointOfStalkHom_comp f x hV hxV _ χ hχ
  exact ⟨_, hcontract, comp_structureMorphism_of_comp_eq hf hx hcontract⟩

/-! ### The geometric data produced by the one-step classification -/

/-- The two projections of `k × k` give distinct maps out of the fibre of the stalk. -/
private theorem ofHom_fst_ne_snd {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]
    (I : Ideal B) (e : (B ⧸ I) ≃ₐ[k] k × k) :
    CommRingCat.ofHom (((AlgHom.fst k k k).comp e.toAlgHom).toRingHom.comp
        (Ideal.Quotient.mk I)) ≠
      CommRingCat.ofHom (((AlgHom.snd k k k).comp e.toAlgHom).toRingHom.comp
        (Ideal.Quotient.mk I)) := by
  intro hEq
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e.symm (1, 0))
  have h : (e (Ideal.Quotient.mk I b)).1 = (e (Ideal.Quotient.mk I b)).2 :=
    congrArg (fun t : CommRingCat.of B ⟶ CommRingCat.of k => t.hom b) hEq
  rw [hb, AlgEquiv.apply_symm_apply] at h
  exact one_ne_zero h

/-- **The glueing case of the one-step classification of [Stacks, Tag 0C1L].** If the fibre
`(f_*𝒪_{X'})_x ⧸ m_x (f_*𝒪_{X'})_x` is `k × k`, then `f` identifies two distinct rational
points of `X'` lying over `x`. -/
theorem exists_two_points_of_fibre_algEquiv_prod {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsAffineHom f]
    (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X) (hx : x.IsOver (Spec (.of k))) :
    letI : Algebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk (basePoint x)) :=
      (stalkConstMap X (basePoint x)).hom.toAlgebra
    letI : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      ((stalkPushforwardMap f (basePoint x)).hom.comp
        (stalkConstMap X (basePoint x)).hom).toAlgebra
    (((f.base _* X'.presheaf).stalk (basePoint x) ⧸
        stalkFibreIdeal f (basePoint x)) ≃ₐ[k] k × k) →
      ∃ a b : Spec (.of k) ⟶ X', a ≠ b ∧ a ≫ f = x ∧ b ≫ f = x ∧
        a.IsOver (Spec (.of k)) ∧ b.IsOver (Spec (.of k)) := by
  let : Algebra (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (basePoint x)) :=
    (stalkConstMap X (basePoint x)).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    ((stalkPushforwardMap f (basePoint x)).hom.comp
      (stalkConstMap X (basePoint x)).hom).toAlgebra
  intro e
  refine exists_two_points_of_stalkHom_ne f hf x hx
    (χ₁ := CommRingCat.ofHom
      (((AlgHom.fst k k k).comp e.toAlgHom).toRingHom.comp
        (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x)))))
    (χ₂ := CommRingCat.ofHom
      (((AlgHom.snd k k k).comp e.toAlgHom).toRingHom.comp
        (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x)))))
    (stalkPushforwardMap_comp_eq_of_fibreAlgHom f x hx k _)
    (stalkPushforwardMap_comp_eq_of_fibreAlgHom f x hx k _)
    (ofHom_fst_ne_snd _ e)

/-- **The glueing case of the one-step classification of [Stacks, Tag 0C1L], with the fibre
sequence.** The previous result strengthened by the two germ-level clauses of
`AlgebraicGeometry.IsGlueingTwoPoints` that express the short exact sequence
`0 → 𝒪_X → f_*𝒪_{X'} → x_*k → 0`: exactness in the middle and surjectivity onto the skyscraper.
The three stalk-level inputs are
`Stacks.GlueSquishFactor.exists_algebraMap_eq_of_prod_fst_eq_snd` and
`Stacks.GlueSquishFactor.exists_prod_fst_sub_snd_eq`, which is where the corrected trichotomy
`m_A B ⊆ A` is used, and they are carried to the germs by
`Stacks.GlueSquishFactor.exists_two_points_sequence_of_stalkHom_ne`.

Of the clauses of `AlgebraicGeometry.IsGlueingTwoPoints` what is still missing after this is the
clause `IsIso (f ∣_ U)` for `U` the complement of the single point `x` — a statement about the
whole bad set, not about one point; see the implementation notes of this file. -/
theorem exists_two_points_sequence_of_fibre_algEquiv_prod {k : Type u} [Field k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X)
    [IsFinite f] (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X)
    (hx : x.IsOver (Spec (.of k))) :
    letI : Algebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk (basePoint x)) :=
      (stalkConstMap X (basePoint x)).hom.toAlgebra
    letI : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      ((stalkPushforwardMap f (basePoint x)).hom.comp
        (stalkConstMap X (basePoint x)).hom).toAlgebra
    (⊥ : Subalgebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x))) ≠ ⊤ →
      (∀ E : Subalgebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)), E = ⊥ ∨ E = ⊤) →
      (((f.base _* X'.presheaf).stalk (basePoint x) ⧸
          stalkFibreIdeal f (basePoint x)) ≃ₐ[k] k × k) →
      ∃ a b : Spec (.of k) ⟶ X', a ≠ b ∧ a ≫ f = x ∧ b ≫ f = x ∧
        a.IsOver (Spec (.of k)) ∧ b.IsOver (Spec (.of k)) ∧
        IsGlueingFibreSequenceAt f (basePoint x) a b := by
  let : Algebra (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (basePoint x)) :=
    (stalkConstMap X (basePoint x)).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    ((stalkPushforwardMap f (basePoint x)).hom.comp
      (stalkConstMap X (basePoint x)).hom).toAlgebra
  have : IsScalarTower k (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    module_finite_stalk_pushforward f (basePoint x)
  intro hne hmin e
  refine exists_two_points_sequence_of_stalkHom_ne f hf x hx
    (χ₁ := CommRingCat.ofHom
      (((AlgHom.fst k k k).comp e.toAlgHom).toRingHom.comp
        (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x)))))
    (χ₂ := CommRingCat.ofHom
      (((AlgHom.snd k k k).comp e.toAlgHom).toRingHom.comp
        (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x)))))
    (stalkPushforwardMap_comp_eq_of_fibreAlgHom f x hx k _)
    (stalkPushforwardMap_comp_eq_of_fibreAlgHom f x hx k _) (ofHom_fst_ne_snd _ e)
    (fun g hg => exists_algebraMap_eq_of_prod_fst_eq_snd k _ _ hne hmin e hg)
    fun c => exists_prod_fst_sub_snd_eq k _ _ e c

/-- **The squishing case of the one-step classification of [Stacks, Tag 0C1L].** If the fibre
`(f_*𝒪_{X'})_x ⧸ m_x (f_*𝒪_{X'})_x` is the dual numbers `k[ε]`, then `f` contracts a tangent
vector of `X'` to the rational point `x`. -/
theorem exists_tangentVector_of_fibre_algEquiv_dualNumber {k : Type u} [Field k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X)
    [IsAffineHom f] (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X)
    (hx : x.IsOver (Spec (.of k))) :
    letI : Algebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk (basePoint x)) :=
      (stalkConstMap X (basePoint x)).hom.toAlgebra
    letI : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      ((stalkPushforwardMap f (basePoint x)).hom.comp
        (stalkConstMap X (basePoint x)).hom).toAlgebra
    (((f.base _* X'.presheaf).stalk (basePoint x) ⧸
        stalkFibreIdeal f (basePoint x)) ≃ₐ[k]
            DualNumber k) →
      ∃ θ : Spec (.of (DualNumber k)) ⟶ X', θ ≫ f = dualNumberToBase k ≫ x ∧
        θ ≫ (X' ↘ Spec (.of k)) = dualNumberToBase k := by
  let : Algebra (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (basePoint x)) :=
    (stalkConstMap X (basePoint x)).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    ((stalkPushforwardMap f (basePoint x)).hom.comp
      (stalkConstMap X (basePoint x)).hom).toAlgebra
  intro e
  exact exists_tangentVector_of_stalkHom f hf x hx
    (CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x)))))
    (stalkPushforwardMap_comp_eq_of_fibreAlgHom f x hx (DualNumber k) _)

/-- **The one-step classification of [Stacks, Tag 0C1L], as geometric data.** Let `f` be a
finite morphism of `k`-schemes and `x` a rational point of `X` such that the stalk extension
`𝒪_{X, x} ⊂ (f_*𝒪_{X'})_x` is proper and admits no intermediate subalgebra. Then either `f`
identifies two distinct rational points of `X'` lying over `x`, or it contracts a tangent
vector of `X'` to `x`.

This is the source's "thus `C = k × k` or `C = k[ε]` by Lemma [Stacks, Tag 0C1I]; in this case
`f` is correspondingly the glueing of two points or the squishing of a tangent vector", as far
as the *data* of the two elementary modifications is concerned. What is produced is the data
together with the clauses of `AlgebraicGeometry.IsGlueingTwoPoints` respectively
`AlgebraicGeometry.IsSquishingTangentVector` that constrain it — the two points are distinct,
rational, and have the same image `x`; the tangent vector is defined over `k` and is contracted
to `x` — and not the sheaf-theoretic clauses of those predicates; see the implementation notes
of this file. -/
theorem exists_glueing_or_squishing_data_of_minimal {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X)
    [IsFinite f] (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X)
    (hx : x.IsOver (Spec (.of k))) :
    letI : Algebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk (basePoint x)) :=
      (stalkConstMap X (basePoint x)).hom.toAlgebra
    letI : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      ((stalkPushforwardMap f (basePoint x)).hom.comp
        (stalkConstMap X (basePoint x)).hom).toAlgebra
    (⊥ : Subalgebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x))) ≠ ⊤ →
      (∀ E : Subalgebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)), E = ⊥ ∨ E = ⊤) →
      (∃ a b : Spec (.of k) ⟶ X', a ≠ b ∧ a ≫ f = x ∧ b ≫ f = x ∧
          a.IsOver (Spec (.of k)) ∧ b.IsOver (Spec (.of k))) ∨
        ∃ θ : Spec (.of (DualNumber k)) ⟶ X', θ ≫ f = dualNumberToBase k ≫ x ∧
          θ ≫ (X' ↘ Spec (.of k)) = dualNumberToBase k := by
  let : Algebra (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (basePoint x)) :=
    (stalkConstMap X (basePoint x)).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    ((stalkPushforwardMap f (basePoint x)).hom.comp
      (stalkConstMap X (basePoint x)).hom).toAlgebra
  intro hne hmin
  rcases fibre_algEquiv_prod_or_dualNumber f (basePoint x)
    (exists_sub_stalkConstMap_mem_maximalIdeal x hx) hne hmin with h | h
  · exact Or.inl (exists_two_points_of_fibre_algEquiv_prod f hf x hx h.some)
  · exact Or.inr (exists_tangentVector_of_fibre_algEquiv_dualNumber f hf x hx h.some)

/-! ### The glueing predicate, reduced to one clause -/

/-- **`AlgebraicGeometry.IsGlueingTwoPoints` for a minimal step, assuming only that `f` is an
isomorphism away from the single point `x`.** Let `f` be a finite morphism of algebraic
`k`-schemes with `𝒪_X ⊂ f_*𝒪_{X'}` — here in its literal form `hinj`, injectivity of `f.app` on
the sections over every open — let `x` be a rational point of `X` at which the stalk extension
`𝒪_{X, x} ⊂ (f_*𝒪_{X'})_x` is proper and minimal, and suppose its fibre is `k × k`. If moreover
`f` restricts to an isomorphism over the complement of `x`, then `f` really is the glueing of two
rational points of `X'`.

Every other clause of `AlgebraicGeometry.IsGlueingTwoPoints` is discharged: the data and its
constraints by `Stacks.GlueSquishFactor.exists_two_points_sequence_of_fibre_algEquiv_prod`, the
two germ-level clauses of the fibre sequence by the same result, and the third — injectivity — by
`Stacks.GlueSquishFactor.map_eq_zero_of_map_app_eq_zero`, which needs no fibre and no shrinking.

So the hypothesis `hiso` is exactly what separates the glueing half of the one-step
classification of [Stacks, Tag 0C1L] from the lemma: the hypothesis of
`Stacks.GlueSquishFactor.IsAlmostIso` gives an isomorphism away from *some* finite set, and
upgrading that to the complement of the single point `x` is the source's "we may assume that `f`
is not an isomorphism in exactly one point", which is a statement about the whole bad set. It is
not provable from the data here, and it is the only thing missing on this side. -/
theorem exists_isGlueingTwoPoints_of_fibre_algEquiv_prod {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X)
    [IsFinite f] (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X)
    (hx : x.IsOver (Spec (.of k)))
    (hX'ft : LocallyOfFiniteType (X' ↘ Spec (.of k)))
    (hX'qc : QuasiCompact (X' ↘ Spec (.of k)))
    (hXft : LocallyOfFiniteType (X ↘ Spec (.of k)))
    (hXqc : QuasiCompact (X ↘ Spec (.of k)))
    (hinj : ∀ W : X.Opens, Function.Injective (f.app W).hom)
    (hiso : ∃ U : X.Opens, (U : Set X) = {basePoint x}ᶜ ∧ IsIso (f ∣_ U)) :
    letI : Algebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk (basePoint x)) :=
      (stalkConstMap X (basePoint x)).hom.toAlgebra
    letI : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      ((stalkPushforwardMap f (basePoint x)).hom.comp
        (stalkConstMap X (basePoint x)).hom).toAlgebra
    (⊥ : Subalgebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x))) ≠ ⊤ →
      (∀ E : Subalgebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)), E = ⊥ ∨ E = ⊤) →
      (((f.base _* X'.presheaf).stalk (basePoint x) ⧸
          stalkFibreIdeal f (basePoint x)) ≃ₐ[k] k × k) →
      ∃ a b : Spec (.of k) ⟶ X', IsGlueingTwoPoints f a b := by
  let : Algebra (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (basePoint x)) :=
    (stalkConstMap X (basePoint x)).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    ((stalkPushforwardMap f (basePoint x)).hom.comp
      (stalkConstMap X (basePoint x)).hom).toAlgebra
  intro hne hmin e
  obtain ⟨a, b, hab, ha, hb, haO, hbO, hseqmid, hseqsurj⟩ :=
    exists_two_points_sequence_of_fibre_algEquiv_prod f hf x hx hne hmin e
  have hxp : (a ≫ f).base (IsLocalRing.closedPoint k) = basePoint x :=
    congrArg (fun g : Spec (CommRingCat.of k) ⟶ X => g.base (IsLocalRing.closedPoint k)) ha
  refine ⟨a, b, haO, hbO, hab, hf, hX'ft, hX'qc, hXft, hXqc, ha.trans hb.symm, inferInstance,
    ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hUset, hUiso⟩ := hiso
    exact ⟨U, by rw [hUset, hxp], hUiso⟩
  · rintro U _hU s ⟨V, hVU, hxV, hzero⟩
    exact ⟨V, hVU, hxV, map_eq_zero_of_map_app_eq_zero f hinj hVU s hzero⟩
  · intro U hU s hs
    obtain ⟨V, hVU, hxV, t, ht⟩ :=
      hseqmid U (by rw [← hxp]; exact hU) _ _ s hs
    exact ⟨V, hVU, by rw [hxp]; exact hxV, t, ht⟩
  · intro c
    obtain ⟨W, hxW, _, _, s, heq⟩ := hseqsurj c
    exact ⟨W, by rw [hxp]; exact hxW, s, heq⟩

/-- **The glueing half of the one-step classification with `𝒪_X ⊂ f_*𝒪_{X'}` in its sheaf
form.** `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_fibre_algEquiv_prod` with its
hypothesis `hinj` replaced by the monomorphy of `𝒪_X ⟶ f_*𝒪_{X'}` in the sheaves of commutative
rings on `X` — which is the clause of `Stacks.GlueSquishFactor.IsAlmostIso` that carries the
hypothesis `𝒪_X ⊂ f_*𝒪_{X'}` of [Stacks, Tag 0C1L].

The two readings of that hypothesis are the same by
`Stacks.GlueSquishFactor.injective_app_of_mono_hom_pushforwardAlgebra`. So of the hypotheses of
the source only `hiso` is not supplied by `Stacks.GlueSquishFactor.IsAlmostIso` together with
minimality of the stalk extension: `IsAlmostIso` gives an isomorphism away from *some* finite
set, and `hiso` asks for the complement of the single point `x`. -/
theorem exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod {k : Type u} [Field k]
    [IsAlgClosed k] {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) [IsFinite f] (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X)
    (hx : x.IsOver (Spec (.of k)))
    (hX'ft : LocallyOfFiniteType (X' ↘ Spec (.of k)))
    (hX'qc : QuasiCompact (X' ↘ Spec (.of k)))
    (hXft : LocallyOfFiniteType (X ↘ Spec (.of k)))
    (hXqc : QuasiCompact (X ↘ Spec (.of k)))
    (hmono : Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).hom)
    (hiso : ∃ U : X.Opens, (U : Set X) = {basePoint x}ᶜ ∧ IsIso (f ∣_ U)) :
    letI : Algebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk (basePoint x)) :=
      (stalkConstMap X (basePoint x)).hom.toAlgebra
    letI : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      ((stalkPushforwardMap f (basePoint x)).hom.comp
        (stalkConstMap X (basePoint x)).hom).toAlgebra
    (⊥ : Subalgebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x))) ≠ ⊤ →
      (∀ E : Subalgebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)), E = ⊥ ∨ E = ⊤) →
      (((f.base _* X'.presheaf).stalk (basePoint x) ⧸
          stalkFibreIdeal f (basePoint x)) ≃ₐ[k] k × k) →
      ∃ a b : Spec (.of k) ⟶ X', IsGlueingTwoPoints f a b := by
  let : Algebra (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (basePoint x)) :=
    (stalkConstMap X (basePoint x)).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    ((stalkPushforwardMap f (basePoint x)).hom.comp
      (stalkConstMap X (basePoint x)).hom).toAlgebra
  intro hne hmin e
  exact exists_isGlueingTwoPoints_of_fibre_algEquiv_prod f hf x hx hX'ft hX'qc hXft hXqc
    (fun W => injective_app_of_mono_hom_pushforwardAlgebra f hmono W) hiso hne hmin e

end Stacks.GlueSquishFactor

end

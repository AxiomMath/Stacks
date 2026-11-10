module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles

/-!
# The degree of a principal divisor on a proper curve, through the graph construction

Let `C = (S, δ)` be a Chow situation whose base is the spectrum of a field `k` with `δ = 0`, and
let `c : X ⟶ S` be proper with `X` integral of delta-dimension one — a proper curve over `k`.
Stacks 02RU says that `c_*div(f) = 0` for every invertible rational function `f` on `X`.

`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic` supplies the parts of that
statement independent of the graph construction of Stacks 02RQ, among them the reduction of
Stacks 02RU along a *proper dominant* morphism. This file supplies the graph construction's
contribution: the curve `Y`, the closure of the graph of a unit section representing `f` inside
`X ×_S ℙ¹_S`, carries `f` to a rational function `f_Y` with

  `c_*div_X(f) = (q ≫ p_{ℙ¹})_* div_Y(f_Y)`,

where `q : Y ⟶ ℙ¹_S` is the second projection. Since the right-hand side is a pushforward along
a morphism factoring through `ℙ¹_S`, Stacks 02RU for `X` follows from Stacks 02RU for `ℙ¹_S`
whenever `q` is dominant.

Two ingredients needed for that and absent from the repository are proved here. The first is the
representation of an invertible rational function by an *invertible section* on a dense open
(`Stacks.Chow.exists_dense_unit_section`): the common domain of representatives of `f` and
`f⁻¹` carries sections whose product represents `1`, and since the germ map at the generic point
of an integral scheme is injective that product is `1` on the nose. This is what the graph
construction of Stacks 02RQ takes as its input, every statement there being phrased for a unit
`g : Γ(X, U)ˣ`. The second is that the projection `q : Y ⟶ ℙ¹_S` is proper
(`Stacks.Chow.isProper_graphLineProjection`) — the companion of part (1) of Stacks 02RQ for the
other projection, proved the same way, `Y` being closed in `X ×_S ℙ¹_S`, which is proper over
`ℙ¹_S` when `X` is proper over `S`.

## Main results

* `Stacks.Chow.exists_dense_unit_section` — an invertible rational function on an integral scheme
  is represented by an invertible section on a dense open.
* `Stacks.Chow.graphLineProjection_comp` — `q` followed by `ℙ¹_S ⟶ S` is the structure morphism
  of `Y`.
* `Stacks.Chow.isProper_graphLineProjection` — `q : Y ⟶ ℙ¹_S` is proper.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_graph` — the pushforward to the base of
  the principal divisor of `f` on `X` equals the pushforward to the base of the principal divisor
  of `f_Y` on `Y`. This is part (5) of Stacks 02RQ composed with the functoriality of proper
  pushforward, and it holds for every delta-dimension `n`, with no hypothesis on `ℙ¹_S`.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_properDominant'` — the
  reduction along a proper dominant morphism with the factorisation supplied as an equation
  rather than definitionally.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_graph` — Stacks 02RU for `X`,
  conditional on Stacks 02RU for `ℙ¹_S` and on dominance of `q`.

## Implementation notes

### This is not Stacks 02RU, and bears no attribute for that tag

`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_graph` hypothesises four things
that Stacks 02RU does not, so it is a reduction and not the tag:

* `IsDominant (graphLineProjection c U ↑g)`. The Stacks proof splits here: if `q` is not
  dominant its image is a closed point, both fibres `Y₀` and `Y_∞` are empty, and `div_Y(f_Y)`
  vanishes by part (4) of Stacks 02RQ, which this repository does not have. The hypothesis is
  genuinely a case distinction, not an artefact: for `f` a constant in `k^*` the graph is
  horizontal and `q` is constant.
* `IsIntegral (relativeProjectiveLine C.S)` and the value `1` of its delta-dimension. Both are
  properties of `ℙ¹_k` that the repository does not prove. `ℙ¹_S` is covered by the two charts
  `Stacks.Chow.affineChart` and `Stacks.Chow.affineYChart`, each an open immersion from
  `𝔸¹_S`, so both are reachable from that cover; neither is reachable from
  `AlgebraicGeometry.projectiveLine`, whose base change to `S` is not identified with
  `Stacks.Chow.relativeProjectiveLine` anywhere.
* Stacks 02RU for `ℙ¹_S` itself, as the hypothesis that every nonzero rational function on
  `ℙ¹_S` has principal divisor of degree zero. The *arithmetic* form of this is proved:
  `Stacks.Chow.finsum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero` is exactly the statement for
  `RatFunc k`, with the finite places indexed by monic irreducible polynomials. What is missing
  is the identification of the closed points of `ℙ¹_k` with those polynomials together with the
  point at infinity, of `AlgebraicGeometry.Scheme.ord` with `Stacks.Chow.ordAt` and
  `Stacks.Chow.ordAtInfty`, and of the residue degrees with `Polynomial.natDegree`; that is the
  gap named in the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic`.

### The quasi-compactness hypothesis

`[QuasiCompact U.ι]` is carried by every statement here that mentions the graph. It is inherited
from part (2) of Stacks 02RQ and is not stated by the tag; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles`. It holds automatically in
the setting of Stacks 02RU, `X` being locally of finite type over a locally Noetherian base.

### The factorisation of the structure morphism of `Y`

`Stacks.Chow.graphBaseMorphism` is `p ≫ sX` definitionally but `q ≫ (ℙ¹_S ↘ S)` only up to
`CategoryTheory.Limits.pullback.condition`. Since the cycle group of `Y` depends on its
structure morphism, the reduction along a proper dominant morphism cannot be applied directly;
`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_properDominant'` restates it
with the factorisation as an equation, which `subst` then discharges.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 01RU](https://stacks.math.columbia.edu/tag/01RU)
* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.AlgebraicGeometry.GenericPointDecomposition (affineLine coordinate lineHom)

/-! ### An invertible rational function is an invertible section on a dense open -/

/-- The section of the structure sheaf on the domain of a partial map to the affine line given by
its coordinate. -/
private def partialMapSection {X : Scheme.{u}} (P : X.PartialMap (affineLine : Scheme.{u})) :
    Γ(X, (⟨P.domain, P.dense_domain⟩ : DenseOpen X).1) :=
  (⟨P.domain, P.dense_domain⟩ : DenseOpen X).1.topIso.hom (P.hom.appTop coordinate)

/-- A partial map to the affine line is the one attached to its own coordinate section: both
have the same domain, and a morphism to the affine line is determined by its coordinate. -/
private theorem partialMap_toRationalMap_eq_ofSection {X : Scheme.{u}}
    (P : X.PartialMap (affineLine : Scheme.{u})) :
    ofSection X ⟨P.domain, P.dense_domain⟩ (partialMapSection P) = P.toRationalMap := by
  let U : DenseOpen X := ⟨P.domain, P.dense_domain⟩
  let Q : X.PartialMap (affineLine : Scheme.{u}) :=
    ⟨P.domain, P.dense_domain,
      AffineSpace.homOfVector (specULiftZIsTerminal.from U.1.toScheme)
        (fun _ : ULift.{u} (Fin 1) ↦ U.1.topIso.inv (partialMapSection P))⟩
  change Q.toRationalMap = P.toRationalMap
  congr 1
  apply Scheme.PartialMap.ext Q P rfl
  apply AffineSpace.hom_ext
  · exact specULiftZIsTerminal.hom_ext _ _
  · intro i
    obtain rfl : i = (⟨0⟩ : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
    rw [Scheme.isoOfEq_rfl]
    simp only [Q, AffineSpace.homOfVector_appTop_coord]
    change CategoryTheory.ConcreteCategory.hom
        (CategoryTheory.CategoryStruct.comp U.1.topIso.hom U.1.topIso.inv)
      (P.hom.appTop coordinate) = P.hom.appTop coordinate
    simpa only [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.id_apply] using
      congrArg (fun g : Γ(U.1.toScheme, ⊤) ⟶ Γ(U.1.toScheme, ⊤) =>
        (CategoryTheory.ConcreteCategory.hom g) (P.hom.appTop coordinate)) U.1.topIso.hom_inv_id

/-- An invertible rational function and its inverse are represented by sections on one common
dense open: restrict representatives of the two to the intersection of their domains. -/
private theorem exists_common_open_sections {X : Scheme.{u}} [IsIntegral X]
    (f : (rationalFunctions X)ˣ) :
    ∃ (U : DenseOpen X) (s t : Γ(X, U.1)),
      ofSection X U s = (f : rationalFunctions X) ∧
      ofSection X U t = ((↑(f⁻¹)) : rationalFunctions X) := by
  let P := (↑f : rationalFunctions X).representative
  let Q := (↑(f⁻¹) : rationalFunctions X).representative
  let D : X.Opens := P.domain ⊓ Q.domain
  have hD : Dense (D : Set X) :=
    P.dense_domain.inter_of_isOpen_left Q.dense_domain P.domain.isOpen
  let P' := P.restrict D hD inf_le_left
  let Q' := Q.restrict D hD inf_le_right
  let U : DenseOpen X := ⟨P'.domain, P'.dense_domain⟩
  let UQ : DenseOpen X := ⟨Q'.domain, Q'.dense_domain⟩
  have hUQ : UQ = U := by
    apply Subtype.ext
    simp [U, UQ, P', Q']
  let s : Γ(X, U.1) := partialMapSection P'
  let t : Γ(X, U.1) := hUQ ▸ partialMapSection Q'
  refine ⟨U, s, t, (partialMap_toRationalMap_eq_ofSection P').trans ?_, ?_⟩
  · simp [P', P, Scheme.RationalMap.toRationalMap_representative]
  have hsection := (partialMap_toRationalMap_eq_ofSection Q').trans
    (show Q'.toRationalMap = ↑(f⁻¹) by
      simp [Q', Q, Scheme.RationalMap.toRationalMap_representative])
  dsimp [t]
  cases hUQ
  exact hsection

/-- An invertible rational function on an integral scheme is represented by an **invertible**
section on a dense open. This is the input shape of the graph construction of Stacks 02RQ, whose
statements are all phrased for a unit of `Γ(X, U)`.

The two sections representing `f` and `f⁻¹` on a common dense open have a product representing
`1`; since the germ map at the generic point is injective on an integral scheme, that product is
`1`. -/
theorem exists_dense_unit_section {X : Scheme.{u}} [IsIntegral X]
    (f : (rationalFunctions X)ˣ) :
    ∃ (U : DenseOpen X) (g : (Γ(X, U.1))ˣ),
      ofSection X U (g : Γ(X, U.1)) = (f : rationalFunctions X) := by
  obtain ⟨U, s, t, hs, ht⟩ := exists_common_open_sections f
  have hprod : ofSection X U (s * t) = 1 := by
    calc
      ofSection X U (s * t) = ofSection X U s * ofSection X U t := by
            rw [← ofSectionRingHom_apply X U (s * t), (ofSectionRingHom X U).map_mul,
              ofSectionRingHom_apply, ofSectionRingHom_apply]
      _ = 1 := by
            rw [hs, ht]
            exact f.mul_inv
  obtain ⟨x, hx⟩ := U.2.nonempty
  let _ : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  have hη : genericPoint X ∈ U.1 :=
    ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr (by simpa using ⟨x, hx⟩)
  let e := rationalFunctionsEquivFunctionField X
  have hprodGerm : X.presheaf.germ U.1 (genericPoint X) hη (s * t) = 1 := by
    calc
      X.presheaf.germ U.1 (genericPoint X) hη (s * t) = e.1 (ofSection X U (s * t)) :=
        (e.2 U (s * t) hη).symm
      _ = 1 := by
            rw [hprod]
            exact map_one e.1
  have hst : s * t = 1 := by
    apply (Scheme.germToFunctionField_injective X U.1)
    simpa using hprodGerm
  exact ⟨U, ⟨s, t, hst, (mul_comm t s).trans hst⟩, hs⟩

/-! ### The second projection of the graph -/

/-- The projection `q : Y ⟶ ℙ¹_S` followed by `ℙ¹_S ⟶ S` is the structure morphism of `Y`: the
two projections of `X ×_S ℙ¹_S` agree over `S`. -/
theorem graphLineProjection_comp {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    graphLineProjection sX U s ≫ (relativeProjectiveLine S ↘ S) = graphBaseMorphism sX U s := by
  change graphClosureι sX U s ≫ pullback.snd sX (relativeProjectiveLine S ↘ S) ≫
      (relativeProjectiveLine S ↘ S) =
    graphClosureι sX U s ≫ pullback.fst sX (relativeProjectiveLine S ↘ S) ≫ sX
  rw [← pullback.condition]

/-- The projection `q : Y ⟶ ℙ¹_S` is proper, the companion of part (1) of Stacks 02RQ for the
other projection: `Y` is closed in `X ×_S ℙ¹_S`, which is proper over `ℙ¹_S` as the base change
of the proper morphism `X ⟶ S`. -/
instance isProper_graphLineProjection {X S : Scheme.{u}} (sX : X ⟶ S) [IsProper sX]
    (U : X.Opens) (s : Γ(X, U)) : IsProper (graphLineProjection sX U s) := by
  change IsProper (graphClosureι sX U s ≫ pullback.snd sX (relativeProjectiveLine S ↘ S))
  infer_instance

/-- The relative projective line over a locally Noetherian base is locally Noetherian, being
locally of finite type over it. -/
instance isLocallyNoetherian_relativeProjectiveLine (S : Scheme.{u}) [IsLocallyNoetherian S] :
    IsLocallyNoetherian (relativeProjectiveLine S) :=
  LocallyOfFiniteType.isLocallyNoetherian (relativeProjectiveLine S ↘ S)

/-- The closure `Y` of a graph over a locally Noetherian base is locally Noetherian, being
locally of finite type over it. -/
instance isLocallyNoetherian_graphClosure {X S : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] [IsLocallyNoetherian S] (U : X.Opens) (s : Γ(X, U)) :
    IsLocallyNoetherian (graphClosure sX U s) :=
  letI : LocallyOfFiniteType (graphBaseMorphism sX U s) :=
    locallyOfFiniteType_graphBaseMorphism sX U s
  LocallyOfFiniteType.isLocallyNoetherian (graphBaseMorphism sX U s)

/-! ### Transporting the principal divisor to the graph -/

/-- The pushforward to the base of the principal divisor of `f` on `X` is the pushforward to the
base of the principal divisor of the induced rational function on the graph closure `Y`.

This is part (5) of Stacks 02RQ, `div_X(f) = p_*div_Y(f_Y)`, composed with the functoriality of
proper pushforward (Stacks 02R5) along `Y ⟶ X ⟶ S`. It is the step of the proof of Stacks 02RU
that replaces `X` by the curve `Y`, which also maps to `ℙ¹_S`. -/
theorem properPushforward_principalDivisorCycle_eq_graph
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [IsProper sX] [IsIntegral X]
    (U : X.Opens) (g : (Γ(X, U))ˣ) [QuasiCompact U.ι] (n : ℤ)
    (hn : schemeDeltaDimension C sX = (n : EInt))
    (f : (rationalFunctions X)ˣ) (hU : Dense (U : Set X))
    (hf : ofSection X ⟨U, hU⟩ ↑g = (f : rationalFunctions X))
    (hd : GraphPreimageDense sX U ↑g)
    (hYint : IsIntegral (graphClosure sX U ↑g))
    (hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g))
    (hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt)) :
    letI : IsIntegral (graphClosure sX U ↑g) := hYint
    letI : LocallyOfFiniteType (graphBaseMorphism sX U ↑g) := hYft
    properPushforward C sX (𝟙 C.S) sX (by simp) (n - 1)
        (principalDivisorCycle C sX hn ((rationalFunctionsEquivFunctionField X).1 ↑f)) =
      properPushforward C (graphBaseMorphism sX U ↑g) (𝟙 C.S) (graphBaseMorphism sX U ↑g)
        (by simp) (n - 1)
        (principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
          ((rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).1
            ↑(graphRationalFunction sX U g hd))) := by
  let _ : IsProper (graphProjection sX U ↑g) := graphProjection_isProper sX U ↑g
  rw [principalDivisorCycle_eq_properPushforward C sX U g n hn f hU hf hd hYint hYft
    (graphProjection_isProper sX U ↑g) hYdim]
  exact properPushforward_properPushforward C (graphBaseMorphism sX U ↑g) sX (𝟙 C.S)
    (graphProjection sX U ↑g) sX rfl (by simp) (n - 1) _

/-! ### Stacks 02RU conditional on the projective-line case -/

/-- The reduction of Stacks 02RU along a proper dominant morphism, with the factorisation of the
structure morphism supplied as an equation rather than definitionally.

`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_properDominant` states its
conclusion for the composite `q ≫ sP`; the structure morphism of the graph closure `Y` equals
that composite only up to `CategoryTheory.Limits.pullback.condition`, and the cycle group of `Y`
depends on it, so the equation is taken as a hypothesis and discharged by substitution. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_properDominant'
    (C : ChowSituation.{u}) {Y P : Scheme.{u}} [Subsingleton C.S] [Nonempty C.S]
    (hδ : ∀ s : C.S, C.dimensionFunction s = 0)
    (sY : Y ⟶ C.S) [IsProper sY] (sP : P ⟶ C.S) [IsProper sP]
    [IsIntegral Y] [IsIntegral P] [IsLocallyNoetherian Y] [IsLocallyNoetherian P]
    (q : Y ⟶ P) [IsProper q] [IsDominant q] (hq : q ≫ sP = sY)
    (hnY : schemeDeltaDimension C sY = ((1 : ℤ) : EInt))
    (hnP : schemeDeltaDimension C sP = ((1 : ℤ) : EInt))
    (hP : ∀ g : P.functionField, g ≠ 0 → principalDivisorDegree sP g = 0)
    (f : Y.functionField) (hf : f ≠ 0) :
    properPushforward C sY (𝟙 C.S) sY (by simp) 0 (principalDivisorCycle C sY hnY f) = 0 := by
  subst hq
  exact properPushforward_principalDivisorCycle_eq_zero_of_properDominant C hδ sP q hnY hnP hP f hf

/-- **Stacks 02RU, reduced to the projective line.** For a proper integral curve `c : X ⟶ S` over
the spectrum of a field with the zero dimension function, and an invertible rational function `f`
represented by a unit section on a dense open `U`, the pushforward of `div(f)` to the base
vanishes — *provided* the second projection `q : Y ⟶ ℙ¹_S` out of the graph closure is dominant
and Stacks 02RU holds for `ℙ¹_S`.

The proof is the Stacks argument: `c_*div_X(f)` is the pushforward of `div_Y(f_Y)` along the
structure morphism of `Y` (`Stacks.Chow.properPushforward_principalDivisorCycle_eq_graph`), that
morphism factors through `ℙ¹_S` through the proper dominant `q`, and the reduction along a proper
dominant morphism turns the vanishing into Stacks 02RU for `ℙ¹_S`.

This is **not** Stacks 02RU and carries no attribute: it hypothesises dominance of `q`,
integrality and delta-dimension one of `ℙ¹_S`, and Stacks 02RU for `ℙ¹_S`. See the implementation
notes of this file for what each of those still needs. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_graph
    (k : Type u) [Field k] (C : ChowSituation.{u}) (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (c : X ⟶ C.S) [IsProper c] [IsIntegral X]
    (hdim : schemeDeltaDimension C c = (1 : EInt))
    (U : X.Opens) [QuasiCompact U.ι] (g : (Γ(X, U))ˣ) (hU : Dense (U : Set X))
    (f : (rationalFunctions X)ˣ) (hf : ofSection X ⟨U, hU⟩ ↑g = (f : rationalFunctions X))
    (hPint : IsIntegral (relativeProjectiveLine C.S))
    (hPdim : schemeDeltaDimension C (relativeProjectiveLine C.S ↘ C.S) = (1 : EInt))
    (hP : ∀ h : (relativeProjectiveLine C.S).functionField, h ≠ 0 →
      principalDivisorDegree (relativeProjectiveLine C.S ↘ C.S) h = 0)
    (hdom : IsDominant (graphLineProjection c U ↑g)) :
    properPushforward C c (𝟙 C.S) c (by simp) 0
      (principalDivisorCycle C c hdim ((rationalFunctionsEquivFunctionField X).1 ↑f)) = 0 := by
  have _ : Subsingleton C.S := by rw [hS]; infer_instance
  have _ : Nonempty C.S := by rw [hS]; infer_instance
  have hd : GraphPreimageDense c U ↑g := dense_graphPreimage c U ↑g
  have hYint : IsIntegral (graphClosure c U ↑g) := isIntegral_graphClosure c U ↑g hU
  have hYft : LocallyOfFiniteType (graphBaseMorphism c U ↑g) :=
    locallyOfFiniteType_graphBaseMorphism c U ↑g
  have hYdim : schemeDeltaDimension C (graphBaseMorphism c U ↑g) = (1 : EInt) :=
    schemeDeltaDimension_graphClosure C c U g 1 hdim hU hYft
  have _ : IsProper (graphProjection c U ↑g) := graphProjection_isProper c U ↑g
  have _ : IsProper (graphBaseMorphism c U ↑g) :=
    inferInstanceAs (IsProper (graphProjection c U ↑g ≫ c))
  exact (properPushforward_principalDivisorCycle_eq_graph C c U g 1 hdim f hU hf hd hYint hYft
    hYdim).trans (properPushforward_principalDivisorCycle_eq_zero_of_properDominant' C hδ
    (graphBaseMorphism c U ↑g) (relativeProjectiveLine C.S ↘ C.S) (graphLineProjection c U ↑g)
    (graphLineProjection_comp c U ↑g) hYdim hPdim hP _
    (fun h => (graphRationalFunction c U g hd).ne_zero
      ((rationalFunctionsEquivFunctionField (graphClosure c U ↑g)).1.injective
        (h.trans (map_zero _).symm))))

/-- **Stacks 02RU, reduced to the projective line**, with the representing section eliminated.

The statement is that of Stacks 02RU verbatim, together with exactly four hypotheses the tag does
not state: integrality of `ℙ¹_S`, the value `1` of its delta-dimension, Stacks 02RU for `ℙ¹_S`,
and dominance of the second projection out of the graph closure of every unit section
representing `f`. The representing section itself is supplied by
`Stacks.Chow.exists_dense_unit_section`, and quasi-compactness of its inclusion comes for free
from local Noetherianity of `X`, which a proper morphism to the base of a Chow situation
provides.

This is **not** Stacks 02RU and carries no attribute; the four hypotheses, and what each of them
still needs, are discussed in the implementation notes of this file. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine
    (k : Type u) [Field k] (C : ChowSituation.{u}) (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (c : X ⟶ C.S) [IsProper c] [IsIntegral X]
    (hdim : schemeDeltaDimension C c = (1 : EInt))
    (hPint : IsIntegral (relativeProjectiveLine C.S))
    (hPdim : schemeDeltaDimension C (relativeProjectiveLine C.S ↘ C.S) = (1 : EInt))
    (hP : ∀ h : (relativeProjectiveLine C.S).functionField, h ≠ 0 →
      principalDivisorDegree (relativeProjectiveLine C.S ↘ C.S) h = 0)
    (f : (rationalFunctions X)ˣ)
    (hdom : ∀ (U : X.Opens) (hU : Dense (U : Set X)) (g : (Γ(X, U))ˣ),
      ofSection X ⟨U, hU⟩ ↑g = (f : rationalFunctions X) →
        IsDominant (graphLineProjection c U ↑g)) :
    properPushforward C c (𝟙 C.S) c (by simp) 0
      (principalDivisorCycle C c hdim ((rationalFunctionsEquivFunctionField X).1 ↑f)) = 0 := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian c
  obtain ⟨U, g, hg⟩ := exists_dense_unit_section f
  exact properPushforward_principalDivisorCycle_eq_zero_of_graph k C hS hδ c hdim U.1 g U.2 f hg
    hPint hPdim hP (hdom U.1 U.2 g hg)

end Stacks.Chow

end

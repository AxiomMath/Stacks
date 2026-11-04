module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.CanonicalDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp

/-!
# The sheaf of differentials of an algebraic space as a descent datum on a presentation

Let `pX : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `π : U ⟶ X` be a
presentation and let `s, t : R ⟶ U` satisfy `s ≫ π = t ≫ π`, the situation of an étale
presentation with `R = U ×_X U`.  Writing `p` for `U ⟶ Y` and `q` for `R ⟶ Y`, the comparison
maps of Stacks 04CX are

```
c_π : π^*Ω_{X/Y} ⟶ Ω_{U/Y},    c_s : s^*Ω_{U/Y} ⟶ Ω_{R/Y},    c_t : t^*Ω_{U/Y} ⟶ Ω_{R/Y},
```

and `c_s`, `c_t` are isomorphisms when `s` and `t` are étale, which is the étale-localization
clause of Stacks 04CU.  Their composite `α`, namely `c_s` followed by the inverse of `c_t`, is
the descent isomorphism `s^*Ω_{U/Y} ≅ t^*Ω_{U/Y}` of Stacks 04CW, and the results below
identify it with the canonical comparison of the two inverse images of `Ω_{X/Y}` — the
transition isomorphism of the canonical descent datum of Stacks 04W5.  So the module `α`
descends to is `Ω_{X/Y}`.

## Main definitions

* `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIso` is the descent isomorphism `α` of
  Stacks 04CW, built from two invertible comparison maps of Stacks 04CX.

## Main results

* `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.congr_left`: being a comparison map of
  Stacks 04CX is transported along an equality of the upper edges of the square.
* `AlgebraicGeometry.Space.canonicalComparison_comp_sheafOfDifferentialsMap`: the canonical
  comparison of the two inverse images of `Ω_{X/Y}`, followed by `c_t`, is `c_π` pulled back
  along `s` and followed by `c_s`.  No invertibility is needed for this.
* `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIso_canonicalComparison`: **`α` is the
  transition isomorphism of the canonical descent datum of `Ω_{X/Y}`**, so the module `α`
  descends to is `Ω_{X/Y}`.
* `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIso_canonicalDescentDatum_transition`: the
  same statement read in the vocabulary of Stacks 04W5, about the descent datum
  `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum` itself.

## Implementation notes

The comparison map of Stacks 04CX enters through its characterizing property
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`, which has at most one solution by
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`.  That is the form in which
Stacks 05Z7 is stated in `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsComp.lean`,
and the form in which the comparison maps are available.  Everything below is then a
consequence of uniqueness: the two routes from `(s ≫ π)^*Ω_{X/Y}` to `Ω_{R/Y}` are comparison
maps of the same triangle, the first by Stacks 05Z7 for the factorization through `s` and
transport along `s ≫ π = t ≫ π`, the second by Stacks 05Z7 for the factorization through `t`.

The canonical comparison is `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison`,
the pairwise isomorphism of the canonical descent datum of Stacks 04W5; at the two projections
of `U ×_X U` it is the transition isomorphism of the canonical descent datum of `Ω_{X/Y}`
relative to the one-member family `π`.

Invertibility of `c_s` and `c_t` is the étale-localization clause of Stacks 04CU; it is an
instance argument rather than derived from étaleness of `s` and `t`, because that invertibility
is not available here — it is a different clause from the identification
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`, which is unconditional.
It is used only to form `α`; the identity it is divided out of,
`AlgebraicGeometry.Space.canonicalComparison_comp_sheafOfDifferentialsMap`, holds
unconditionally.

## References

* [Stacks Project, Tag 04CW](https://stacks.math.columbia.edu/tag/04CW)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 05Z7](https://stacks.math.columbia.edu/tag/05Z7), the comparison maps of
  two stacked squares compose.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), étale localization of
  the sheaf of differentials.
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5), the canonical descent
  datum of a quasi-coherent module.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y U R : AlgebraicSpaces B S hS}

/-- Being a comparison map of Stacks 04CX for a square depends on the upper edge only through
its value, so it transports along an equality of upper edges. -/
theorem IsSheafOfDifferentialsMap.congr_left {X' Y' : AlgebraicSpaces B S hS} {g g₁ : X' ⟶ X}
    {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {c : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g p p' c) (h : g = g₁) :
    IsSheafOfDifferentialsMap B S hS g₁ p p'
      ((eqToIso (congrArg (fun r : X' ⟶ X =>
          (modulePullback B S hS r).obj (sheafOfDifferentials B S hS p)) h)).inv ≫ c) := by
  subst h
  simpa using hc

/-- **The canonical descent datum of `Ω_{X/Y}` is the one the comparison maps of Stacks 04CX
produce.**  Going from `s^*π^*Ω_{X/Y}` to `Ω_{R/Y}` through the canonical comparison of the two
inverse images and then `c_t` is the same as going through `c_π` pulled back along `s` and then
`c_s`.

Both routes are comparison maps of Stacks 04CX for the triangle `R ⟶ X` over `Y`, by Stacks 05Z7
for the two factorizations of `s ≫ π = t ≫ π` through `U`, and the comparison map of a square is
unique. -/
theorem canonicalComparison_comp_sheafOfDifferentialsMap (pX : X ⟶ Y) (π : U ⟶ X) (p : U ⟶ Y)
    {s t : R ⟶ U} (q : R ⟶ Y) (hπ : s ≫ π = t ≫ π)
    {cπ : (modulePullback B S hS π).obj (sheafOfDifferentials B S hS pX) ⟶
      sheafOfDifferentials B S hS p}
    {cs : (modulePullback B S hS s).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q}
    {ct : (modulePullback B S hS t).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q}
    (hcπ : IsSheafOfDifferentialsMap B S hS π pX p cπ)
    (hcs : IsSheafOfDifferentialsMap B S hS s p q cs)
    (hct : IsSheafOfDifferentialsMap B S hS t p q ct) :
    (QuasiCoherentDescent.canonicalComparison s t π π hπ
          (sheafOfDifferentials B S hS pX)).hom ≫
        (modulePullback B S hS t).map cπ ≫ ct =
      (modulePullback B S hS s).map cπ ≫ cs := by
  have hAs := isSheafOfDifferentialsMap_comp B S hS π s pX p q hcπ hcs
  have hAt := isSheafOfDifferentialsMap_comp B S hS π t pX p q hcπ hct
  have key := eq_of_isSheafOfDifferentialsMap B S hS (t ≫ π) pX q
    (IsSheafOfDifferentialsMap.congr_left B S hS hAs hπ) hAt
  rw [QuasiCoherentDescent.canonicalComparison_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← key, Iso.hom_inv_id_assoc, ← Category.assoc, Iso.hom_inv_id_app]
  exact Category.id_comp _

/-- **Stacks 04CW.** The descent isomorphism `α : s^*Ω_{U/Y} ⟶ Ω_{R/Y} ⟶ t^*Ω_{U/Y}` attached to
two invertible comparison maps of Stacks 04CX, which is what the étale-localization clause of
Stacks 04CU supplies when `s` and `t` are étale. -/
def sheafOfDifferentialsDescentIso {p : U ⟶ Y} {s t : R ⟶ U} {q : R ⟶ Y}
    (cs : (modulePullback B S hS s).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q)
    (ct : (modulePullback B S hS t).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q) [IsIso cs] [IsIso ct] :
    (modulePullback B S hS s).obj (sheafOfDifferentials B S hS p) ≅
      (modulePullback B S hS t).obj (sheafOfDifferentials B S hS p) :=
  asIso cs ≪≫ (asIso ct).symm

/-- **Stacks 04CW.** For a presentation `π : U ⟶ X` of an algebraic space over `Y` and
`s, t : R ⟶ U` with `s ≫ π = t ≫ π`, the descent isomorphism `α` is the transition isomorphism
of the canonical descent datum of `Ω_{X/Y}`: the comparison map `c_π : π^*Ω_{X/Y} ⟶ Ω_{U/Y}`
carries the canonical comparison of the two inverse images of `Ω_{X/Y}` to `α`.  So the module
`α` descends to is `Ω_{X/Y}`.

Invertibility of `c_s` and `c_t` is the étale-localization clause of Stacks 04CU; the identity
it is divided out of,
`AlgebraicGeometry.Space.canonicalComparison_comp_sheafOfDifferentialsMap`, needs no
invertibility. -/
@[stacks 04CW "the module `α` descends to is `Ω_{X/Y}`: `α` is the transition isomorphism of \
the canonical descent datum of `Ω_{X/Y}` on a presentation `π : U ⟶ X` of an algebraic space"]
theorem sheafOfDifferentialsDescentIso_canonicalComparison (pX : X ⟶ Y) (π : U ⟶ X) (p : U ⟶ Y)
    {s t : R ⟶ U} (q : R ⟶ Y) (hπ : s ≫ π = t ≫ π)
    {cπ : (modulePullback B S hS π).obj (sheafOfDifferentials B S hS pX) ⟶
      sheafOfDifferentials B S hS p}
    {cs : (modulePullback B S hS s).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q}
    {ct : (modulePullback B S hS t).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q}
    (hcπ : IsSheafOfDifferentialsMap B S hS π pX p cπ)
    (hcs : IsSheafOfDifferentialsMap B S hS s p q cs)
    (hct : IsSheafOfDifferentialsMap B S hS t p q ct) [IsIso cs] [IsIso ct] :
    (QuasiCoherentDescent.canonicalComparison s t π π hπ
          (sheafOfDifferentials B S hS pX)).hom ≫
        (modulePullback B S hS t).map cπ =
      (modulePullback B S hS s).map cπ ≫
        (sheafOfDifferentialsDescentIso B S hS cs ct).hom := by
  simp only [sheafOfDifferentialsDescentIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  rw [← Category.assoc, ← canonicalComparison_comp_sheafOfDifferentialsMap B S hS pX π p q hπ
    hcπ hcs hct]
  simp

/-- **Stacks 04CW in the vocabulary of Stacks 04W5.**  `α` is the transition isomorphism, at the
`i`-th pairwise fibre product, of the canonical descent datum of `Ω_{X/Y}` relative to a family
`(π j : V j ⟶ X)` of algebraic spaces over `X`: the module `α` descends to is `Ω_{X/Y}`.

This is `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIso_canonicalComparison` read through
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum_transition`; the extra input
`hM` is the one needed to form a canonical descent datum at all, and is a standing hypothesis of
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum`. -/
theorem sheafOfDifferentialsDescentIso_canonicalDescentDatum_transition (pX : X ⟶ Y)
    {I : Type v} (V : I → AlgebraicSpaces B S hS)
    (π : ∀ j, V j ⟶ X)
    (hM : (sheafOfDifferentials B S hS pX).IsQuasicoherentOnSite) (i : I) (p : V i ⟶ Y)
    (q : QuasiCoherentDescent.pair B S hS V π i i ⟶ Y)
    {cπ : (modulePullback B S hS (π i)).obj (sheafOfDifferentials B S hS pX) ⟶
      sheafOfDifferentials B S hS p}
    {cs : (modulePullback B S hS (QuasiCoherentDescent.pairFst B S hS V π i i)).obj
      (sheafOfDifferentials B S hS p) ⟶ sheafOfDifferentials B S hS q}
    {ct : (modulePullback B S hS (QuasiCoherentDescent.pairSnd B S hS V π i i)).obj
      (sheafOfDifferentials B S hS p) ⟶ sheafOfDifferentials B S hS q}
    (hcπ : IsSheafOfDifferentialsMap B S hS (π i) pX p cπ)
    (hcs : IsSheafOfDifferentialsMap B S hS
      (QuasiCoherentDescent.pairFst B S hS V π i i) p q cs)
    (hct : IsSheafOfDifferentialsMap B S hS
      (QuasiCoherentDescent.pairSnd B S hS V π i i) p q ct) [IsIso cs] [IsIso ct] :
    ((QuasiCoherentDescent.canonicalDescentDatum B S hS V π
            (sheafOfDifferentials B S hS pX) hM).transition i i).hom ≫
        (modulePullback B S hS (QuasiCoherentDescent.pairSnd B S hS V π i i)).map cπ =
      (modulePullback B S hS (QuasiCoherentDescent.pairFst B S hS V π i i)).map cπ ≫
        (sheafOfDifferentialsDescentIso B S hS cs ct).hom := by
  rw [QuasiCoherentDescent.canonicalDescentDatum_transition]
  exact sheafOfDifferentialsDescentIso_canonicalComparison B S hS pX (π i) p q
    (QuasiCoherentDescent.pair_condition B S hS V π i i) hcπ hcs hct

end AlgebraicGeometry.Space

end

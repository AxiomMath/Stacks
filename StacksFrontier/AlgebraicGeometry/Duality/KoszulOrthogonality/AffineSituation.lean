module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulVanishing.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
import all StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability

/-!
# [Stacks, Tag 09IR] in Situation [Stacks, Tag 08CZ]

Situation [Stacks, Tag 08CZ] fixes a commutative ring `A`, a finite sequence `f₁, …, f_r ∈ A`,
the affine scheme `X = Spec A` and the open subscheme `U = D(f₁) ∪ … ∪ D(f_r) ⊆ X`. Writing
`j : U ⟶ X` for the open immersion and `K` for the perfect object of `D(𝒪_X)` given by the Koszul
complex on `f₁, …, f_r` over `A`, [Stacks, Tag 09IR] (Bökstedt–Neeman, Proposition 6.1) asserts
that for `E ∈ D_QCoh(𝒪_X)` the following are equivalent:

1. `E = Rj_*(E|_U)`, and
2. `Hom_{D(𝒪_X)}(K[n], E) = 0` for all `n ∈ ℤ`.

This file proves both implications in that situation, with condition (2) written out literally as
vanishing of `Hom(K⟦n⟧, E)` for **every** integer `n`, and condition (1) read — as the source
intends — as invertibility of the **canonical unit** `E ⟶ Rj_*(E|_U)` of the derived adjunction
`j^* ⊣ Rj_*`, not as the mere existence of some isomorphism between the two objects.

The skeleton of both implications is
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/Abstract.lean`, which treats an
adjunction `L ⊣ R` of pretriangulated categories with `L` triangulated and `L K = 0`. Of the
three geometric inputs it isolates, two are discharged by results already in the library:

* `hKzero`, that `j^* K = 0`, is `Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject`
  — the sheafified Koszul complex on `f₁, …, f_r` restricts to zero on `⋃ᵢ D(f_i)`, proved in
  `StacksFrontier/AlgebraicGeometry/Duality/KoszulVanishing/OpenComplement.lean`;
* `hcounit`, that `Rj_*` is fully faithful, is the instance
  `Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit_app` of
  `StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/DerivedRestrictCounit.lean`, so it is
  found by instance synthesis and appears nowhere below.

Consequently the implication **(1) ⟹ (2)** is the formal half: `Hom(K⟦n⟧, Rj_* Z)` is
`Hom((j^*K)⟦n⟧, Z) = 0` once `j^* K = 0`, and the condition is invariant under the isomorphism
`E ≅ Rj_*(E|_U)` given by the unit.

The implication **(2) ⟹ (1)** is the content of the source's proof. The third input of the
abstract skeleton is the detection statement

> an object `M` of `D(𝒪_X)` with `M|_U = 0` and `Hom(K⟦n⟧, M) = 0` for all `n ∈ ℤ` is zero,

and it is proved, for `M` with quasi-coherent cohomology sheaves, in
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineComparison.lean`: the affine
derived Spec–Γ equivalence of [Stacks, Tag 06Z0] carries `M` to `N = RΓ(X, M)` in `D(A)`, the
Hom-vanishing to the Hom-vanishing against the Koszul object of `D(A)`, and the hypothesis
`M|_U = 0` to the statement that the cohomology modules of `N` are `f_i`-power torsion for every
`i`; and over a ring that forces `N = 0`, by
`Stacks.Koszul.Truncation.isZero_of_forall_hom_derivedKoszul_eq_zero` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineDetection.lean`. The quantifier
over quasi-coherent `M` only is what the source's own hypothesis `E ∈ D_QCoh(𝒪_X)` supplies: the
third vertex of the triangle `E ⟶ Rj_*(E|_U) ⟶ M` is quasi-coherent because `E` is and because
`Rj_*` preserves quasi-coherent cohomology along a quasi-compact open immersion
([Stacks, Tag 08D5]).

## Main results

* `Stacks.Koszul.Truncation.rightOrthogonal_koszulObject_iff` — condition (2) of
  [Stacks, Tag 09IR], written as vanishing of `Hom(K⟦n⟧, E)` for all `n ∈ ℤ`, is right
  orthogonality to the shift closure of `K`.
* `Stacks.Koszul.Truncation.hom_koszulObject_eq_zero_of_isIso_unit` — **(1) implies (2)**.
* `Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero` — **(2) implies (1)**.
* `Stacks.Koszul.Truncation.isIso_unit_iff_hom_koszulObject_eq_zero` — the equivalence of
  [Stacks, Tag 09IR] in the shape it had before the two implications were proved, taking the
  detection statement as an explicit assumption. Its docstring shows that assumption to be false
  as spelled, so the statement is vacuous; it is kept at its original signature only because that
  signature is not this file's to change, and consumers want the two tagged implications instead.

## Implementation notes

**Two `@[stacks 09IR]` sites, each with a clause string, and no bare tag.** The two implications
have different hypotheses — the forward one holds for every object of `D(𝒪_X)`, the reverse one
for the quasi-coherent ones the source speaks about — so they are tagged separately. Their union
is the statement of the tag. The equivalence
`Stacks.Koszul.Truncation.isIso_unit_iff_hom_koszulObject_eq_zero` is left untagged, as before: it
adds nothing to the two tagged halves, and it assumes a statement that its own docstring shows to
be false, so it says nothing. Its signature predates the two implications and is left exactly as
it was; bringing it into line is separate work on that declaration.

**Condition (2) is quantified over all of `ℤ`.** Every statement below reads
`∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ E), g = 0`, with `n` ranging over every integer and `g`
over every morphism. Restricting `n` to a half-line would weaken (2) and make the equivalence
false; `StacksFrontier/AlgebraicGeometry/Duality/KoszulTruncatedOrthogonality.lean` records explicit
counterexamples to the one-sided variants of the graded form of this statement in
[Stacks, Tag 0GEK].

**Condition (1) is invertibility of the unit.** The source's `E = Rj_*(E|_U)` is an equality of
objects, so the map it refers to is the canonical one; the statements below ask that
`(derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E` be an isomorphism, which
is the strong reading. Mere existence of an isomorphism `E ≅ Rj_*(E|_U)` is strictly weaker and is
not what is proved.

**Quasi-coherence is assumed exactly where the source assumes it.** The source states the
equivalence for `E ∈ D_QCoh(𝒪_X)`. The forward implication needs nothing, so it is stated for
every `E`, which is strictly stronger. The reverse implication carries the hypothesis, in the form
`DerivedCategoryB.derivedCategoryB _ E` — "every cohomology sheaf of `E` is quasi-coherent" — and
cannot do without it: for `r = 0` the open `U` is empty and the reverse implication reads "an
object of `D(𝒪_X)` with vanishing derived global sections is zero", which is false off the
quasi-coherent part. Concretely, on the spectrum of a discrete valuation ring with uniformizer
`t`, the sheaf with no sections over `X` and the fraction field over `D(t)` is nonzero, and global
sections is exact on that two-point space, so all its cohomology vanishes. This is the same
failure that the docstring of
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_counit_app` records for the counit
of the Spec–Γ adjunction.

**`K` is the Koszul object of the source, not an arbitrary perfect object.** Throughout, `K` is
`Stacks.Koszul.Truncation.koszulObject f`, the Koszul complex `K_•(f₁, …, f_r)` of
`StacksFrontier/RingTheory/Koszul/Defs.lean` re-indexed into non-positive cohomological degrees,
sheafified termwise by `AlgebraicGeometry.tilde.functor` and localized. Its perfectness is part of
the source's description of it but is used by neither implication, so it is not invoked.

**The two implications sit at different derived-category models.** The forward one carries free
`[HasDerivedCategory.{w} _]` binders and mentions `CategoryTheory.HasDerivedCategory.standard`
nowhere, so it is available at every model, in particular at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. The reverse one is stated at that
locally small model, because the affine derived Spec–Γ equivalence of [Stacks, Tag 06Z0] that its
proof goes through is available there and at no other model; it is also the only model at which
[Stacks, Tag 09IS] and [Stacks, Tag 0A9A], the consumers of this tag, have content.

## References

* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Stacks.Duality.OpenImmersion

universe w u

namespace Stacks.Koszul.Truncation

section AnyModel

variable {A : Type u} [CommRing A] {r : ℕ}
  [HasDerivedCategory.{w} (Spec (CommRingCat.of A)).Modules] (f : Fin r → A)
  [HasDerivedCategory.{w} (openComplement f).toScheme.Modules]

omit [HasDerivedCategory.{w} (openComplement f).toScheme.Modules] in
/-- **Condition (2) of [Stacks, Tag 09IR] as an orthogonality condition.** For an object `E` of
`D(𝒪_{Spec A})`, every morphism `K⟦n⟧ ⟶ E` out of every integer shift of the Koszul object
vanishes exactly when `E` is right orthogonal to the shift closure of `K`.

This is pure bookkeeping — `singleton K` is the one-member family — but it is what lets the two
implications below be stated in the source's own phrasing, with the quantifier over all of `ℤ`
visible in the statement rather than hidden inside `ObjectProperty.shiftClosure`.

Left to right, a shift `K⟦n⟧` lies in the shift closure of `K` via the identity isomorphism. Right
to left, an object of the shift closure comes with an isomorphism `Z ≅ K⟦n⟧`, and a morphism out
of `Z` vanishes exactly when its transport along that isomorphism does. -/
theorem rightOrthogonal_koszulObject_iff
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules) :
    ((singleton (koszulObject f)).shiftClosure ℤ).rightOrthogonal E ↔
      ∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ E), g = 0 := by
  refine ⟨fun h n g => h g ⟨koszulObject f, n, Iso.refl _, ofObj_apply _ ()⟩, ?_⟩
  rintro h Z g ⟨W, n, e, hW⟩
  rw [singleton_iff] at hW
  subst hW
  rw [← cancel_epi e.inv, comp_zero]
  exact h n _

/-- **[Stacks, Tag 09IR], the implication "(1) implies (2)".** In Situation [Stacks, Tag 08CZ],
if the canonical map `E ⟶ Rj_*(E|_U)` is invertible then `Hom_{D(𝒪_X)}(K[n], E) = 0` for every
`n ∈ ℤ`, where `K` is the sheafified Koszul complex on `f₁, …, f_r`.

There is nothing to assume. The Koszul object restricts to zero on `U = ⋃ᵢ D(f_i)` by
`Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject`, so a morphism `K⟦n⟧ ⟶ Rj_* Z`
is adjoint to a morphism out of `(j^* K)⟦n⟧ = 0` and hence zero; and `E` is isomorphic to
`Rj_*(E|_U)` through the unit, while the condition is closed under isomorphism. -/
@[stacks 09IR "(1) implies (2)"]
theorem hom_koszulObject_eq_zero_of_isIso_unit
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (h : IsIso ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E)) :
    ∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ E), g = 0 :=
  (rightOrthogonal_koszulObject_iff f E).1
    (rightOrthogonal_shiftClosure_singleton_of_isIso_unit
      (derivedRestrictPushforwardAdjunction (openComplement f).ι)
      (Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f) h)

/-- **The equivalence of [Stacks, Tag 09IR], with the detection hypothesis as an explicit
assumption.** In Situation [Stacks, Tag 08CZ], for an object `E` of `D(𝒪_X)` the canonical map
`E ⟶ Rj_*(E|_U)` is invertible if and only if `Hom_{D(𝒪_X)}(K[n], E) = 0` for every `n ∈ ℤ`,
assuming

> `hdet` : every object `M` of `D(𝒪_X)` with `M|_U = 0` and `Hom_{D(𝒪_X)}(K[n], M) = 0` for all
> `n ∈ ℤ` is zero.

It bears no `@[stacks]` attribute: the two implications of the tag are tagged individually, on
`Stacks.Koszul.Truncation.hom_koszulObject_eq_zero_of_isIso_unit` and
`Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero`, and both of those are proved
with no hypothesis beyond the source's own.

**`hdet` as stated here is false, and this statement is therefore vacuous.** Taking `r = 0` makes
`U` empty, so the restriction hypothesis on `M` is automatic and `K` is `𝒪_X[0]`; `hdet` then
reads "an object of `D(𝒪_X)` with vanishing derived global sections is zero", which fails off the
quasi-coherent part. On the spectrum of a discrete valuation ring with uniformizer `t`, the sheaf
of modules with no sections over `X` and the fraction field over `D(t)` is nonzero, and global
sections is exact on that two-point space, so all of its cohomology vanishes. The same failure is
recorded in the docstring of
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_counit_app` for the counit of the
Spec–Γ adjunction. What the source actually assumes is that `E` lie in `D_QCoh(𝒪_X)`, and that is
the hypothesis of `Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero`, which should
be preferred to this statement. This declaration is kept at its original signature only because
its interface is not this file's to change. -/
theorem isIso_unit_iff_hom_koszulObject_eq_zero
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hdet : ∀ M : DerivedCategory (Spec (CommRingCat.of A)).Modules,
      IsZero ((derivedRestrict (openComplement f).ι).obj M) →
      (∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ M), g = 0) → IsZero M) :
    IsIso ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E) ↔
      ∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ E), g = 0 :=
  ⟨hom_koszulObject_eq_zero_of_isIso_unit f E,
    fun h => isIso_unit_of_rightOrthogonal_shiftClosure_singleton
      (derivedRestrictPushforwardAdjunction (openComplement f).ι)
      (Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f) inferInstance
      (fun M hM hortho => hdet M hM ((rightOrthogonal_koszulObject_iff f M).1 hortho))
      ((rightOrthogonal_koszulObject_iff f E).2 h)⟩

end AnyModel

section LocallySmall

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)

/-- **[Stacks, Tag 09IR], the implication "(2) implies (1)".** In Situation [Stacks, Tag 08CZ],
let `E` be an object of `D_QCoh(𝒪_X)`, that is one whose cohomology sheaves are quasi-coherent.
If `Hom_{D(𝒪_X)}(K[n], E) = 0` for every `n ∈ ℤ` then the canonical map `E ⟶ Rj_*(E|_U)` is
invertible.

Take a distinguished triangle `E ⟶ Rj_*(E|_U) ⟶ M ⟶ E⟦1⟧`; the claim is that `M = 0`. Three
things are known about `M`.

* `M|_U = 0`, because `j^*` of the unit at `E` is a section of the counit at `E|_U`, which is
  invertible — `Rj_*` is fully faithful along an open immersion.
* `Hom(K⟦n⟧, M) = 0` for every `n`, because right orthogonality to the shifts of `K` is a
  triangulated subcategory and both `E` and `Rj_*(E|_U)` lie in it, the latter for the formal
  reason that `j^* K = 0`.
* The cohomology sheaves of `M` are quasi-coherent, because those of `E` are and `Rj_*` preserves
  quasi-coherent cohomology along a quasi-compact open immersion ([Stacks, Tag 08D5]).

Those three force `M = 0` by `Stacks.Koszul.Truncation.isZero_of_forall_hom_koszulObject_eq_zero`,
which is the source's argument: pass to `D(A)` along the affine comparison of [Stacks, Tag 06Z0]
and apply the Koszul detection statement over the ring. A distinguished triangle whose third
vertex vanishes has invertible first morphism. -/
@[stacks 09IR "(2) implies (1)"]
theorem isIso_unit_of_hom_koszulObject_eq_zero
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hE : DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf) E)
    (h : ∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ E), g = 0) :
    IsIso ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E) := by
  obtain ⟨M, b, c, hT⟩ := distinguished_cocone_triangle
    ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E)
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  have hLM : IsZero ((derivedRestrict (openComplement f).ι).obj M) :=
    Triangle.isZero₃_of_isIso₁ _
      ((derivedRestrict (openComplement f).ι).map_distinguished _ hT)
      (isIso_map_unit_of_isIso_counit
        (derivedRestrictPushforwardAdjunction (openComplement f).ι) E inferInstance)
  have hortho : ∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ M), g = 0 :=
    (rightOrthogonal_koszulObject_iff f M).1
      (ext_of_isTriangulatedClosed₃ _ _ hT ((rightOrthogonal_koszulObject_iff f E).2 h)
        (rightOrthogonal_shiftClosure_singleton_rightAdjoint_obj
          (derivedRestrictPushforwardAdjunction (openComplement f).ι)
          (Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f) _))
  have hQM := AlgebraicGeometry.derivedCategoryB_obj₃_of_distTriang _ hT hE
    (derivedCategoryB_derivedPushforward_openComplement f _
      (Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict
        (openComplement f).ι E hE))
  exact isZero_of_forall_hom_koszulObject_eq_zero f M hQM hLM hortho

end LocallySmall

end Stacks.Koszul.Truncation

end

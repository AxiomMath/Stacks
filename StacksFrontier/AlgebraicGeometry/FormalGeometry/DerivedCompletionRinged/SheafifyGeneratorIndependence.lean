module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoverDenseSheafifyLocal
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GeneratorIndependence
public import StacksFrontier.CategoryTheory.Sites.SieveObjectsCoverDense
import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification on a slice site is local for a covering sieve, and generator independence

Let `(𝒞, J)` be a site, let `V` be an object and let `S` be a covering sieve of `V`. On the slice
site `𝒞/V` the objects belonging to `S` are cover-dense,
`CategoryTheory.Sieve.isCoverDense_ι_overObjects`; hence by
`PresheafOfModules.sheafifyIsoOfRes` the sheafification of a presheaf of modules on `𝒞/V`
depends only on its restriction to those objects. That is the statement **sheafification on a
slice is local for a covering sieve**, in the form [Stacks, Tag 099E] needs it.

The consequence that tag draws is the **independence of the sheafification from the chosen
generators**. Let `(𝒞, 𝒪)` be a ringed site and let `f₁, …, f_r` and `g₁, …, g_s` be two finite
families of global sections of `𝒪` generating the *same* sheaf of ideals — in the source's
notation, two finitely generated ideals `I, I' ⊆ ℐ(V)` both generating `ℐ|_V`. The two objectwise
ideals `I𝒪(W)` and `I'𝒪(W)` need not agree, but
`AlgebraicGeometry.RingedSite.spanAgreementSieve_mem` says they agree above a covering sieve of
`V`. So any two presheaves of modules on `𝒞/V` built from the objectwise ideal — the complexes
`K^•_{V,I}` and `K^•_{V,I'}` of [Stacks, Tag 099E], whose value at `W/V` is `K(𝒪(W), I𝒪(W))` and
depends on the family only through that ideal — agree above that covering sieve, and therefore
have isomorphic sheafifications. That is what this file concludes, for a single presheaf and for
a complex of them.

## Main definitions

* `AlgebraicGeometry.RingedSite.sieveObjectsRestrict`: restriction of presheaves of modules on a
  slice site to the objects of a sieve.
* `AlgebraicGeometry.RingedSite.sheafifyIsoOfCoveringSieve`: **sheafification on a slice site is
  local for a covering sieve** — two presheaves of modules whose restrictions to the objects of a
  covering sieve are isomorphic have isomorphic sheafifications.
* `AlgebraicGeometry.RingedSite.sheafifyIsoOfEqOnCoveringSieve`: the same with the restrictions
  equal rather than merely isomorphic, which is the form in which agreement above a cover
  arises.
* `AlgebraicGeometry.RingedSite.sheafifyComplexIsoOfCoveringSieve`: the same for complexes,
  degreewise.
* `AlgebraicGeometry.RingedSite.sheafifyIsoOfGeneratorIndependence` and
  `AlgebraicGeometry.RingedSite.sheafifyComplexIsoOfGeneratorIndependence`: **independence of
  the sheafification from the chosen generators** — two presheaves of modules (or complexes of
  them) on `𝒞/V` which agree at every object where two finite generating families of the same
  sheaf of ideals span the same ideal of sections have isomorphic sheafifications.

## Main results

* `AlgebraicGeometry.RingedSite.sheafifyIsoOfCoveringSieve_hom_comp` and
  `AlgebraicGeometry.RingedSite.sheafifyIsoOfGeneratorIndependence_hom_comp`: **the resulting
  isomorphism of sheafifications is compatible with augmentations**, which is the
  "compatible with maps to `𝒪_U`" clause of [Stacks, Tag 099E].
* `AlgebraicGeometry.RingedSite.sectionSpan_eq_of_overObjects_spanAgreementSieve`: at every
  object of the slice site belonging to the span-agreement sieve the two families do span the
  same ideal of sections, which is the hypothesis the two `GeneratorIndependence` results above
  are meant to be fed.

## Implementation notes

The hypothesis of the generator-independence results is agreement of the two presheaves above
the span-agreement sieve, not above an arbitrary cover: that sieve is the one
`AlgebraicGeometry.RingedSite.spanAgreementSieve_mem` proves covering, and
`AlgebraicGeometry.RingedSite.sectionSpan_eq_of_overObjects_spanAgreementSieve` is what a
consumer uses to produce the agreement from a construction depending only on the objectwise
ideal. The construction of `K^•_{V,I}` itself as a presheaf complex on `𝒞/V` is not in this
file; its ring-level and site-level model is
`StacksFrontier/RingTheory/Cech/GenPairSite.lean` and
`StacksFrontier/RingTheory/Cech/GenPairCechPresheaf.lean`.

No `@[stacks]` attribute is attached. [Stacks, Tag 099E] asserts the existence of a *global* map
`K → 𝒪` in `D(𝒪)` together with the Čech identification over every object where `ℐ` is finitely
generated; what is settled here is the step of its proof which says the sheafification of
`K^•_{V,I}` does not depend on `I`, and that is not a clause of the tag.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe w v u

section Slice

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {V : C}
  (S : Sieve V) (R : Sheaf (J.over V) RingCat.{w})

/-- **Restriction of presheaves of modules on the slice site over `V` to the objects of a sieve
`S` on `V`.** -/
abbrev sieveObjectsRestrict :
    PresheafOfModules.{w} R.obj ⥤
      PresheafOfModules.{w} (S.overObjects.ι.op ⋙ R.obj) :=
  PresheafOfModules.pushforward₀ S.overObjects.ι R.obj

variable [HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Sheafification on a slice site is local for a covering sieve.** Two presheaves of modules
on `𝒞/V` whose restrictions to the objects of a covering sieve of `V` are isomorphic have
isomorphic sheafifications. -/
def sheafifyIsoOfCoveringSieve (hS : S ∈ J V) {F F' : PresheafOfModules.{w} R.obj}
    (e : (sieveObjectsRestrict S R).obj F ≅ (sieveObjectsRestrict S R).obj F') :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj F ≅
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj F' :=
  haveI := Sieve.isCoverDense_ι_overObjects S hS
  PresheafOfModules.sheafifyIsoOfRes e

/-- **Sheafification on a slice site is local for a covering sieve**, in the form in which
agreement above a cover arises: the two restrictions are equal, not merely isomorphic. -/
def sheafifyIsoOfEqOnCoveringSieve (hS : S ∈ J V) {F F' : PresheafOfModules.{w} R.obj}
    (h : (sieveObjectsRestrict S R).obj F = (sieveObjectsRestrict S R).obj F') :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj F ≅
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj F' :=
  sheafifyIsoOfCoveringSieve S R hS (eqToIso h)

/-- **The isomorphism of sheafifications produced by locality for a covering sieve is compatible
with augmentations.** If the given isomorphism of the restrictions is compatible with the
restrictions of two maps into a common presheaf of modules, so is the isomorphism of the
sheafifications. This is the compatibility [Stacks, Tag 099E] asks for, "compatible with maps to
`𝒪_U`". -/
theorem sheafifyIsoOfCoveringSieve_hom_comp (hS : S ∈ J V)
    {F F' A : PresheafOfModules.{w} R.obj}
    (e : (sieveObjectsRestrict S R).obj F ≅ (sieveObjectsRestrict S R).obj F')
    (a : F ⟶ A) (b : F' ⟶ A)
    (h : e.hom ≫ (sieveObjectsRestrict S R).map b = (sieveObjectsRestrict S R).map a) :
    (sheafifyIsoOfCoveringSieve S R hS e).hom ≫
        (PresheafOfModules.sheafification (𝟙 R.obj)).map b =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map a :=
  have := Sieve.isCoverDense_ι_overObjects S hS
  PresheafOfModules.sheafifyLiftRes_comp_sheafification_map e.hom a b h

variable {ι : Type*} {c : ComplexShape ι}
  [(PresheafOfModules.sheafification.{w} (𝟙 R.obj)).Additive]

/-- **Sheafification on a slice site is local for a covering sieve, for complexes.** Two
complexes of presheaves of modules on `𝒞/V` whose restrictions to the objects of a covering sieve
of `V` are isomorphic, by isomorphisms commuting with the differentials, have isomorphic
degreewise sheafifications. -/
def sheafifyComplexIsoOfCoveringSieve (hS : S ∈ J V)
    {F F' : HomologicalComplex (PresheafOfModules.{w} R.obj) c}
    (u : ∀ n, (sieveObjectsRestrict S R).obj (F.X n) ⟶ (sieveObjectsRestrict S R).obj (F'.X n))
    (hu : ∀ n m, c.Rel n m → u n ≫ (sieveObjectsRestrict S R).map (F'.d n m) =
      (sieveObjectsRestrict S R).map (F.d n m) ≫ u m) [∀ n, IsIso (u n)] :
    ((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex c).obj F ≅
      ((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex c).obj F' :=
  haveI := Sieve.isCoverDense_ι_overObjects S hS
  PresheafOfModules.sheafifyComplexIsoOfRes u hu

end Slice

section GeneratorIndependence

variable {X : RingedSite.{u, v, w}} {r s : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}))
  (g : Fin s → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}))
  (V : X.C)

/-- **At every object of the slice site belonging to the span-agreement sieve the two families
span the same ideal of sections.** This is the hypothesis a construction depending only on the
objectwise ideal needs in order to produce agreement above the cover. -/
theorem sectionSpan_eq_of_overObjects_spanAgreementSieve
    (W : (spanAgreementSieve f g V).overObjects.FullSubcategory) :
    sectionSpan f (op W.obj.left) = sectionSpan g (op W.obj.left) :=
  sectionSpan_eq_of_mem_spanAgreementSieve f g W.obj.hom W.property

variable (hfg : generatedIdealSheaf f = generatedIdealSheaf g)

include hfg

/-- The span-agreement sieve of two finite families of global sections generating the same sheaf
of ideals is covering, which is
`AlgebraicGeometry.RingedSite.exists_sieve_sectionSpan_eq` read as a statement about that sieve
rather than an existential. -/
theorem spanAgreementSieve_mem_of_generatedIdealSheaf_eq :
    spanAgreementSieve f g V ∈ X.J V :=
  spanAgreementSieve_mem f g V
    (fun j ↦ hfg ▸ globalSectionVal_mem_generatedIdealSheaf g j (op V))
    (fun i ↦ hfg ▸ globalSectionVal_mem_generatedIdealSheaf f i (op V))

variable (R : Sheaf (X.J.over V) RingCat.{w})
  [HasWeakSheafify (X.J.over V) AddCommGrpCat.{w}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Independence of the sheafification from the chosen generators.** If `f₁, …, f_r` and
`g₁, …, g_s` are two finite families of global sections of `𝒪` generating the same sheaf of
ideals, then two presheaves of modules on the slice site `𝒞/V` which agree at every object where
the two families span the same ideal of sections have isomorphic sheafifications: that locus
contains a covering sieve of `V`, and sheafification on a slice is local for a covering sieve.

This is the step of [Stacks, Tag 099E] which concludes that the sheafification of `K^•_{V,I}`
does not depend on the finitely generated ideal `I ⊆ ℐ(V)` generating `ℐ|_V`. -/
def sheafifyIsoOfGeneratorIndependence {F F' : PresheafOfModules.{w} R.obj}
    (e : (sieveObjectsRestrict (spanAgreementSieve f g V) R).obj F ≅
      (sieveObjectsRestrict (spanAgreementSieve f g V) R).obj F') :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj F ≅
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj F' :=
  sheafifyIsoOfCoveringSieve _ R
    (spanAgreementSieve_mem_of_generatedIdealSheaf_eq f g V hfg) e

/-- **Independence of the sheafification from the chosen generators**, with the two restrictions
equal rather than merely isomorphic — the form in which two presheaves built from the objectwise
ideal agree above the cover. -/
def sheafifyIsoOfEqGeneratorIndependence {F F' : PresheafOfModules.{w} R.obj}
    (h : (sieveObjectsRestrict (spanAgreementSieve f g V) R).obj F =
      (sieveObjectsRestrict (spanAgreementSieve f g V) R).obj F') :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj F ≅
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj F' :=
  sheafifyIsoOfGeneratorIndependence f g V hfg R (eqToIso h)

/-- **The generator-independence isomorphism is compatible with augmentations.** This is the
clause of [Stacks, Tag 099E] which asks the identification to be "compatible with maps to
`𝒪_U`": the two presheaf complexes carry augmentations onto the structure presheaf of the slice,
and the isomorphism of the sheafifications respects them as soon as the isomorphism above the
cover does. -/
theorem sheafifyIsoOfGeneratorIndependence_hom_comp
    {F F' A : PresheafOfModules.{w} R.obj}
    (e : (sieveObjectsRestrict (spanAgreementSieve f g V) R).obj F ≅
      (sieveObjectsRestrict (spanAgreementSieve f g V) R).obj F')
    (a : F ⟶ A) (b : F' ⟶ A)
    (h : e.hom ≫ (sieveObjectsRestrict (spanAgreementSieve f g V) R).map b =
      (sieveObjectsRestrict (spanAgreementSieve f g V) R).map a) :
    (sheafifyIsoOfGeneratorIndependence f g V hfg R e).hom ≫
        (PresheafOfModules.sheafification (𝟙 R.obj)).map b =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map a :=
  sheafifyIsoOfCoveringSieve_hom_comp _ R
    (spanAgreementSieve_mem_of_generatedIdealSheaf_eq f g V hfg) e a b h

variable {ι : Type*} {c : ComplexShape ι}
  [(PresheafOfModules.sheafification.{w} (𝟙 R.obj)).Additive]

/-- **Independence of the sheafification from the chosen generators, for complexes.** Two
complexes of presheaves of modules on `𝒞/V` which agree, compatibly with the differentials, at
every object where two finite generating families of the same sheaf of ideals span the same ideal
of sections have isomorphic degreewise sheafifications. This is the form in which
[Stacks, Tag 099E] uses it: the two complexes are `K^•_{V,I}` and `K^•_{V,I'}`. -/
def sheafifyComplexIsoOfGeneratorIndependence
    {F F' : HomologicalComplex (PresheafOfModules.{w} R.obj) c}
    (u : ∀ n, (sieveObjectsRestrict (spanAgreementSieve f g V) R).obj (F.X n) ⟶
      (sieveObjectsRestrict (spanAgreementSieve f g V) R).obj (F'.X n))
    (hu : ∀ n m, c.Rel n m →
      u n ≫ (sieveObjectsRestrict (spanAgreementSieve f g V) R).map (F'.d n m) =
        (sieveObjectsRestrict (spanAgreementSieve f g V) R).map (F.d n m) ≫ u m)
    [∀ n, IsIso (u n)] :
    ((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex c).obj F ≅
      ((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex c).obj F' :=
  sheafifyComplexIsoOfCoveringSieve _ R
    (spanAgreementSieve_mem_of_generatedIdealSheaf_eq f g V hfg) u hu

end GeneratorIndependence

end AlgebraicGeometry.RingedSite

end

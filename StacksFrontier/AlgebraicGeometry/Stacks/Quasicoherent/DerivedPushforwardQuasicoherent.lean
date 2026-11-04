module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# The derived direct image on the derived category with quasi-coherent cohomology

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks.
**Stacks 07BC** asserts that the total derived direct image `Rf_*` carries the two left columns
of the diagram

`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⟶ D⁺_{LQCoh^fbc}(𝒪_𝒳) ⟶ D(𝒪_𝒳)`

to the corresponding row for `𝒴`, commuting with the horizontal inclusions, and that it
therefore induces a functor

`Rf_{QCoh,*} : D⁺_QCoh(𝒪_𝒳) ⟶ D⁺_QCoh(𝒪_𝒴)`

on the Verdier quotients of **Stacks 07B6**.

This file contains the two preservation clauses, the two functors they cut out together with the
two commuting squares, and the induced functor on the Verdier quotients together with the square
that says it is induced by `Rf_*`. The last assertion of the source, that the functors
`Rⁱf_QCoh` of **Stacks 077A** are `Hⁱ ∘ Rf_{QCoh,*}`, is
`AlgebraicGeometry.Stack.derivedPushforwardQuasicoherentPlus_comp_plusCohomologyDerivedCategory`.

## Main definitions

* `AlgebraicGeometry.Stack.fppfDerivedPushforwardPlusOfStacks`: `Rf_* : D⁺(𝒪_𝒳) ⥤ D⁺(𝒪_𝒴)`,
  the total right derived functor of the direct image of **Stacks 06WE** on fppf modules, at
  module universe `u + 1`.
* `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChangePlus` and
  `AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentFlatBaseChangePlus`: the two left
  columns `D⁺_{LQCoh^fbc}(𝒪_𝒳)` and `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of the diagram, as
  subcategories of `D⁺(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.derivedCategoryQuasicoherentPlus` and
  `AlgebraicGeometry.Stack.toDerivedCategoryQuasicoherentPlus`: the bounded-below Verdier
  quotient `D⁺_QCoh(𝒪_𝒳)` of **Stacks 07B6** and its quotient functor.
* `AlgebraicGeometry.Stack.HasPushforwardCohomologySpectralSequence`: the existence of a
  spectral sequence `Rⁱf_*Hʲ(E) ⇒ Rⁱ⁺ʲf_*E` with a page in a given subcategory.
* `AlgebraicGeometry.Stack.DerivedPushforwardMapsDistinguished`: that `Rf_*` carries a
  distinguished triangle of `D⁺(𝒪_𝒳)` to a distinguished triangle of `D⁺(𝒪_𝒴)`.
* `AlgebraicGeometry.Stack.derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange` and
  `AlgebraicGeometry.Stack.derivedPushforwardPlusParasiticLocallyQuasicoherentFlatBaseChange`:
  the middle and left vertical arrows of the diagram of **Stacks 07BC**.
* `AlgebraicGeometry.Stack.derivedPushforwardQuasicoherentPlus`: `Rf_{QCoh,*}`, the functor
  induced on the Verdier quotients.

## Main results

* `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChangePlus_derivedPushforward`:
  `Rf_*` carries `D⁺_{LQCoh^fbc}(𝒪_𝒳)` into `D⁺_{LQCoh^fbc}(𝒪_𝒴)`.
* `AlgebraicGeometry.Stack.`
  `derivedParasiticLocallyQuasicoherentFlatBaseChangePlus_derivedPushforward`: the same for
  `D⁺_{Parasitic ∩ LQCoh^fbc}`.
* `AlgebraicGeometry.Stack.derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange_comp_ι` and
  `AlgebraicGeometry.Stack.`
  `derivedPushforwardPlusParasiticLocallyQuasicoherentFlatBaseChange_comp_ι`: the two commuting
  squares of the diagram.
* `AlgebraicGeometry.Stack.trW_fppfDerivedPushforwardPlus`: `Rf_*` carries the class of
  morphisms the Verdier quotient inverts into the corresponding class for `𝒴`.
* `AlgebraicGeometry.Stack.`
  `toDerivedCategoryQuasicoherentPlus_comp_derivedPushforwardQuasicoherentPlus`: the quotient
  square, which says that `Rf_{QCoh,*}` is the functor induced by `Rf_*`.

## Implementation notes

The module universe is `u + 1` throughout: a stack's underlying category has objects in
`Type (u + 1)`, so the direct image of **Stacks 06WE** on its fppf modules produces modules whose
sections lie there. The subcategory `LQCoh^fbc` is read at that universe by
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE`, whose flat base
change half is `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`; at module universe `u`
each of these constructions agrees definitionally with its counterpart without `UnivLE`, by
`AlgebraicGeometry.Stack.derivedCategoryQuasicoherentUnivLE_eq` and its companions.

The direct image is taken along the structure functor of the source: a 1-morphism
`f : 𝒳 ⟶ 𝒴` is a functor `G : 𝒳.val.val.obj ⥤ 𝒴.val.val.obj` together with the equality
`G ⋙ 𝒴.val.val.p = 𝒳.val.val.p` of `CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p`, and
`AlgebraicGeometry.Stack.moduleSheafPushforward` takes that equality as an argument. So the
source of `AlgebraicGeometry.Stack.fppfDerivedPushforwardPlusOfStacks` is `Mod(𝒪_𝒳)` itself,
and the two left columns of the diagram sit inside it with no transport.

The preservation clauses take three hypotheses:

* `AlgebraicGeometry.Stack.HasPushforwardCohomologySpectralSequence`, the spectral sequence
  `Rⁱf_*Hʲ(E) ⇒ Rⁱ⁺ʲf_*E` with a page in the subcategory, as an implication from
  quasi-compactness (**Stacks 050U**) and quasi-separatedness (**Stacks 04YW**) of `f`. It asks,
  through `CategoryTheory.SpectralSequence.AbutsTo`, for a finite filtration of each cohomology
  module whose graded pieces are the terms of the infinity page, so it does not say that the
  abutment lies in the subcategory; the step from the page to the abutment is part (4) of
  **Stacks 0132**.
* The weak Serre condition on the subcategory of `Mod(𝒪_𝒴)`, as an instance: for `LQCoh^fbc` it
  is the fppf half of part (2) of **Stacks 0771**; for `Parasitic ∩ LQCoh^fbc` it is that
  together with part (2) of **Stacks 0774**,
  `AlgebraicGeometry.Stack.isSerreClass_parasiticModules`.
* `AlgebraicGeometry.Stack.DerivedPushforwardMapsDistinguished`, that `Rf_*` carries a
  distinguished triangle to a distinguished triangle, for the induced functor on the quotients.

The right-hand column of the source's diagram is the unbounded derived category `D(𝒪_𝒳)`, with
the unbounded `Rf_*` as its vertical arrow; the middle-to-right square is read here in
`D⁺(𝒪_𝒳)`, as
`AlgebraicGeometry.Stack.derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange_comp_ι`.

## References

* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B7](https://stacks.math.columbia.edu/tag/07B7)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u w

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A functor carrying distinguished triangles to distinguished triangles carries the class of
morphisms with cone in `P` into the class of morphisms with cone in `Q`, as soon as it carries
`P` into `Q`.** Carrying distinguished triangles to distinguished triangles means that the image
of each distinguished triangle is distinguished for *some* choice of third morphism. -/
theorem trW_map_of_mapsDistinguished (F : C ⥤ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ T : Triangle C, T ∈ distTriang C →
      ∃ c : F.obj T.obj₃ ⟶ (F.obj T.obj₁)⟦(1 : ℤ)⟧,
        Triangle.mk (F.map T.mor₁) (F.map T.mor₂) c ∈ distTriang D)
    (hPQ : ∀ X, P X → Q (F.obj X)) {X Y : C} (s : X ⟶ Y) (hs : P.trW s) :
    Q.trW (F.map s) := by
  obtain ⟨Z, g, c, hT, hZ⟩ := hs
  obtain ⟨c', hT'⟩ := hF (Triangle.mk s g c) hT
  exact ⟨_, _, c', hT', hPQ Z hZ⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-! ### The derived direct image on `D⁺` -/

/-- The direct image of **Stacks 06WE** on the fppf modules of an algebraic stack along a
1-morphism `f : 𝒳 ⟶ 𝒴`, at module universe `u + 1`, taken along the structure functor of `𝒳`. -/
abbrev fppfModuleSheafPushforwardOfStacks (f : 𝒳 ⟶ 𝒴) :
    fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳 ⥤ fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴 :=
  moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)

/-- The direct image of **Stacks 06WE** on the fppf modules of an algebraic stack is
additive. -/
theorem additive_fppfModuleSheafPushforwardOfStacks (f : 𝒳 ⟶ 𝒴) :
    (fppfModuleSheafPushforwardOfStacks B S hS f).Additive :=
  additive_moduleSheafPushforward.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)

/-- The fppf modules of an algebraic stack have enough injectives at module universe
`u + 1`. -/
theorem enoughInjectives_fppfModulesUnivLESucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    EnoughInjectives (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵) :=
  enoughInjectives_fppfModuleSheavesSucc B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids

variable [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]

/-- **The total derived direct image on bounded-below derived categories of fppf modules of
algebraic stacks**,

`Rf_* : D⁺(𝒪_𝒳) ⥤ D⁺(𝒪_𝒴)`,

the total right derived functor of the direct image of **Stacks 06WE**. -/
def fppfDerivedPushforwardPlusOfStacks (f : 𝒳 ⟶ 𝒴) :
    DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳) ⥤
      DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴) :=
  letI := additive_fppfModuleSheafPushforwardOfStacks B S hS f
  letI := enoughInjectives_fppfModulesUnivLESucc B S hS 𝒳
  (fppfModuleSheafPushforwardOfStacks B S hS f).rightDerivedFunctorPlus

/-! ### The two left columns of the diagram -/

/-- The subcategory `D⁺_{LQCoh^fbc}(𝒪_𝒳) ⊆ D⁺(𝒪_𝒳)`: the bounded-below complexes of fppf
modules all of whose cohomology modules are locally quasi-coherent (**Stacks 06WJ**) with the
flat base change property (**Stacks 0762**). -/
abbrev derivedLocallyQuasicoherentFlatBaseChangePlus (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] :
    ObjectProperty (DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)) :=
  (derivedLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, u + 1, u + 2} B E h S hS
    𝒵).inverseImage DerivedCategory.Plus.ι

/-- The subcategory `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D⁺(𝒪_𝒳)`: the bounded-below complexes of
fppf modules all of whose cohomology modules are parasitic (**Stacks 0773**) *and* locally
quasi-coherent with the flat base change property. -/
abbrev derivedParasiticLocallyQuasicoherentFlatBaseChangePlus
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] :
    ObjectProperty (DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)) :=
  (derivedParasiticLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, u + 1, u + 2} B E h S hS
    𝒵).inverseImage DerivedCategory.Plus.ι

/-- The class of morphisms of `D⁺_{LQCoh^fbc}(𝒪_𝒳)` which the bounded-below Verdier quotient of
**Stacks 07B6** inverts: those whose cone, taken in `D⁺(𝒪_𝒳)`, lies in
`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
abbrev derivedQuasicoherentWPlus (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] :
    MorphismProperty
      (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒵).FullSubcategory :=
  MorphismProperty.inverseImage
    (derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒵).trW
    (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒵).ι

/-- The bounded-below Verdier quotient of **Stacks 07B6**,

`D⁺_QCoh(𝒪_𝒳) = D⁺_{LQCoh^fbc}(𝒪_𝒳) / D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`,

the localization of `D⁺_{LQCoh^fbc}(𝒪_𝒳)` at the morphisms whose cone lies in
`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
abbrev derivedCategoryQuasicoherentPlus (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] :=
  (derivedQuasicoherentWPlus B E h S hS 𝒵).Localization

/-- The quotient functor `D⁺_{LQCoh^fbc}(𝒪_𝒳) ⟶ D⁺_QCoh(𝒪_𝒳)` of the bounded-below Verdier
quotient of **Stacks 07B6**. -/
abbrev toDerivedCategoryQuasicoherentPlus (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] :
    (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒵).FullSubcategory ⥤
      derivedCategoryQuasicoherentPlus B E h S hS 𝒵 :=
  (derivedQuasicoherentWPlus B E h S hS 𝒵).Q

/-! ### The spectral sequence and the distinguished-triangle condition -/

/-- **The spectral sequence `Rⁱf_*Hʲ(E) ⇒ Rⁱ⁺ʲf_*E` with a page in `P`**: for every
bounded-below complex `K` of fppf modules on `𝒳` lying in the subcategory `Q`, there is a
cohomological spectral sequence in `Mod(𝒪_𝒴)` one of whose pages has all its terms in the
subcategory `P`, and which abuts, in the sense of `CategoryTheory.SpectralSequence.AbutsTo`, to
the cohomology modules of `Rf_*K`. -/
abbrev HasPushforwardCohomologySpectralSequence (f : 𝒳 ⟶ 𝒴)
    (Q : ObjectProperty (DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)))
    (P : ObjectProperty (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)) : Prop :=
  ∀ K, Q K → ∃ (r₀ r : ℤ) (hr : r₀ ≤ r)
      (sp : CohomologicalSpectralSequence (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴) r₀),
    (∀ pq : ℤ × ℤ, P ((sp.page r hr).X pq)) ∧
      SpectralSequence.AbutsTo sp fun n =>
        (DerivedCategory.homologyFunctor (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴) n).obj
          (DerivedCategory.Plus.ι.obj ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K))

/-- **The derived direct image carries distinguished triangles to distinguished triangles**: for
every distinguished triangle of `D⁺(𝒪_𝒳)`, its image under `Rf_*` is distinguished for *some*
choice of third morphism. -/
abbrev DerivedPushforwardMapsDistinguished (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ T : Triangle (DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)),
    T ∈ distTriang (DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)) →
      ∃ c : (fppfDerivedPushforwardPlusOfStacks B S hS f).obj T.obj₃ ⟶
          ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj T.obj₁)⟦(1 : ℤ)⟧,
        Triangle.mk ((fppfDerivedPushforwardPlusOfStacks B S hS f).map T.mor₁)
            ((fppfDerivedPushforwardPlusOfStacks B S hS f).map T.mor₂) c ∈
          distTriang (DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴))

/-! ### The two preservation clauses -/

/-- For a quasi-compact and quasi-separated 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, if
`LQCoh^fbc(𝒪_𝒴)` is a weak Serre subcategory and the spectral sequence `Rⁱf_*Hʲ(K) ⇒ Rⁱ⁺ʲf_*K`
has a page in `LQCoh^fbc(𝒪_𝒴)`, then the total derived direct image `Rf_*` carries
`D⁺_{LQCoh^fbc}(𝒪_𝒳)` into `D⁺_{LQCoh^fbc}(𝒪_𝒴)`. -/
@[stacks 07BC "for a quasi-compact quasi-separated f, the clause `Rf_* carries \
  D⁺_LQCoh^fbc(𝒪_𝒳) into D⁺_LQCoh^fbc(𝒪_𝒴)`, by the source's own argument over the spectral \
  sequence Rⁱf_*Hʲ(E) ⇒ Rⁱ⁺ʲf_*E with a page in LQCoh^fbc (Stacks 0771) and the weak Serre \
  condition on LQCoh^fbc (Stacks 0771 part (2), fppf half), neither of which this library has"]
theorem derivedLocallyQuasicoherentFlatBaseChangePlus_derivedPushforward
    [(locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, u + 1} B E h S hS
      𝒴).IsWeakSerreClass]
    (f : 𝒳 ⟶ 𝒴)
    (hss : IsQuasiCompactMorphism B S hS f → AlgebraicStacks.IsQuasiSeparated B S hS f →
      HasPushforwardCohomologySpectralSequence B S hS f
        (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳)
        (locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, u + 1} B E h S hS 𝒴))
    (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (K : DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳))
    (hK : derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K) :
    derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
      ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K) := by
  obtain ⟨r₀, r, hr, sp, hpage, habuts⟩ := hss hqc hqs K hK
  exact fun n => habuts.prop_of_prop_page _ hr hpage n

/-- For a quasi-compact and quasi-separated 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, if
`Parasitic ∩ LQCoh^fbc(𝒪_𝒴)` is a weak Serre subcategory and the spectral sequence
`Rⁱf_*Hʲ(K) ⇒ Rⁱ⁺ʲf_*K` has a page in it, then the total derived direct image `Rf_*` carries
`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` into `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)`. -/
@[stacks 07BC "for a quasi-compact quasi-separated f, the clause `Rf_* carries \
  D⁺_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) into D⁺_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒴)`, by the source's own \
  argument over the same spectral sequence with a page in Parasitic ∩ LQCoh^fbc (Stacks 0775 \
  with Stacks 0771) and the weak Serre condition on it (Stacks 0774 part (2), which this \
  library has, with Stacks 0771 part (2), which it does not)"]
theorem derivedParasiticLocallyQuasicoherentFlatBaseChangePlus_derivedPushforward
    [(parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
      locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, u + 1} B E h S hS
        𝒴).IsWeakSerreClass]
    (f : 𝒳 ⟶ 𝒴)
    (hss : IsQuasiCompactMorphism B S hS f → AlgebraicStacks.IsQuasiSeparated B S hS f →
      HasPushforwardCohomologySpectralSequence B S hS f
        (derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳)
        (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
          locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, u + 1} B E h S hS 𝒴))
    (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (K : DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳))
    (hK : derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K) :
    derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
      ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K) := by
  obtain ⟨r₀, r, hr, sp, hpage, habuts⟩ := hss hqc hqs K hK
  exact fun n => habuts.prop_of_prop_page _ hr hpage n

/-! ### The diagram -/

/-- The restriction of `Rf_* : D⁺(𝒪_𝒳) ⥤ D⁺(𝒪_𝒴)` to a functor
`D⁺_{LQCoh^fbc}(𝒪_𝒳) ⥤ D⁺_{LQCoh^fbc}(𝒪_𝒴)`, given that `Rf_*` carries the one into the
other. -/
@[stacks 07BC "the middle vertical functor D⁺_LQCoh^fbc(𝒪_𝒳) ⥤ D⁺_LQCoh^fbc(𝒪_𝒴) of the \
  diagram, over the preservation clause it restricts"]
def derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : ∀ K, derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K)) :
    (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳).FullSubcategory ⥤
      (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴).FullSubcategory :=
  (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴).lift
    ((derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳).ι ⋙
      fppfDerivedPushforwardPlusOfStacks B S hS f)
    fun K => hf K.obj K.property

/-- The middle vertical functor followed by the inclusion of `D⁺_{LQCoh^fbc}(𝒪_𝒴)` into
`D⁺(𝒪_𝒴)` is the inclusion of `D⁺_{LQCoh^fbc}(𝒪_𝒳)` followed by `Rf_*`. -/
@[stacks 07BC "the middle-to-right commuting square of the diagram, READ IN D⁺(𝒪_𝒳) AND NOT IN \
  THE SOURCE'S UNBOUNDED D(𝒪_𝒳): the unbounded right derived direct image is not constructed in \
  this library"]
def derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange_comp_ι (f : 𝒳 ⟶ 𝒴)
    (hf : ∀ K, derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K)) :
    derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange B E h S hS f hf ⋙
        (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴).ι ≅
      (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳).ι ⋙
        fppfDerivedPushforwardPlusOfStacks B S hS f :=
  (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴).liftCompιIso
    ((derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳).ι ⋙
      fppfDerivedPushforwardPlusOfStacks B S hS f)
    fun K => hf K.obj K.property

/-- The condition of lying in `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, read on an object of
`D⁺_{LQCoh^fbc}(𝒪_𝒳)`. -/
abbrev parasiticInDerivedLocallyQuasicoherentFlatBaseChangePlus
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] :
    ObjectProperty
      (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒵).FullSubcategory :=
  (derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒵).inverseImage
    (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒵).ι

/-- The restriction of the middle vertical functor to a functor
`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⥤ D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)`, given that `Rf_*` carries
the one into the other. -/
@[stacks 07BC "the left vertical functor D⁺_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) ⥤ \
  D⁺_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒴) of the diagram, over the two preservation clauses it \
  restricts"]
def derivedPushforwardPlusParasiticLocallyQuasicoherentFlatBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : ∀ K, derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K))
    (hpar : ∀ K, derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K)) :
    (parasiticInDerivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳).FullSubcategory ⥤
      (parasiticInDerivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴).FullSubcategory :=
  (parasiticInDerivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴).lift
    ((parasiticInDerivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳).ι ⋙
      derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange B E h S hS f hf)
    fun K => hpar K.obj.obj K.property

/-- The left vertical functor followed by
the inclusion of `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)` into `D⁺_{LQCoh^fbc}(𝒪_𝒴)` is the inclusion
of `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` followed by the middle vertical functor. -/
@[stacks 07BC "the left-to-middle commuting square of the diagram"]
def derivedPushforwardPlusParasiticLocallyQuasicoherentFlatBaseChange_comp_ι (f : 𝒳 ⟶ 𝒴)
    (hf : ∀ K, derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K))
    (hpar : ∀ K, derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K)) :
    derivedPushforwardPlusParasiticLocallyQuasicoherentFlatBaseChange B E h S hS f hf hpar ⋙
        (parasiticInDerivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴).ι ≅
      (parasiticInDerivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳).ι ⋙
        derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange B E h S hS f hf :=
  (parasiticInDerivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴).liftCompιIso
    ((parasiticInDerivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳).ι ⋙
      derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange B E h S hS f hf)
    fun K => hpar K.obj.obj K.property

/-! ### The induced functor on the Verdier quotients -/

/-- **The derived direct image inverts what the Verdier quotient inverts.** If `Rf_*` carries
distinguished triangles to distinguished triangles and carries
`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` into `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)`, then it carries a
morphism of `D⁺(𝒪_𝒳)` whose cone lies in `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` to one whose cone
lies in `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)`. -/
theorem trW_fppfDerivedPushforwardPlus (f : 𝒳 ⟶ 𝒴)
    (hdist : DerivedPushforwardMapsDistinguished B S hS f)
    (hpar : ∀ K, derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K))
    {X Y : DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)} (s : X ⟶ Y)
    (hs : (derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳).trW s) :
    (derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴).trW
      ((fppfDerivedPushforwardPlusOfStacks B S hS f).map s) :=
  ObjectProperty.trW_map_of_mapsDistinguished _ _ _ hdist hpar s hs

/-- **The derived direct image followed by the quotient functor inverts the class the Verdier
quotient of `𝒳` inverts.** -/
theorem derivedQuasicoherentWPlus_isInvertedBy (f : 𝒳 ⟶ 𝒴)
    (hf : ∀ K, derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K))
    (hdist : DerivedPushforwardMapsDistinguished B S hS f)
    (hpar : ∀ K, derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K)) :
    (derivedQuasicoherentWPlus B E h S hS 𝒳).IsInvertedBy
      (derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange B E h S hS f hf ⋙
        toDerivedCategoryQuasicoherentPlus B E h S hS 𝒴) := fun _ _ _ hs =>
  (derivedQuasicoherentWPlus B E h S hS 𝒴).Q_inverts _
    (trW_fppfDerivedPushforwardPlus B E h S hS f hdist hpar _ hs)

/-- The derived direct image

`Rf_{QCoh,*} : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴)`

that `Rf_*` induces on the bounded-below Verdier quotients of **Stacks 07B6**: the functor out of
the localization through which `D⁺_{LQCoh^fbc}(𝒪_𝒳) ⥤ D⁺_{LQCoh^fbc}(𝒪_𝒴) ⥤ D⁺_QCoh(𝒪_𝒴)`
factors. -/
@[stacks 07BC "the induced functor Rf_(QCoh,*) : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴) on the Verdier \
  quotients of Stacks 07B6, over the two preservation clauses and over the triangulatedness of \
  Rf_* (a Mathlib TODO for rightDerivedFunctorPlus)"]
def derivedPushforwardQuasicoherentPlus (f : 𝒳 ⟶ 𝒴)
    (hf : ∀ K, derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K))
    (hdist : DerivedPushforwardMapsDistinguished B S hS f)
    (hpar : ∀ K, derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K)) :
    derivedCategoryQuasicoherentPlus B E h S hS 𝒳 ⥤
      derivedCategoryQuasicoherentPlus B E h S hS 𝒴 :=
  Localization.Construction.lift
    (derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange B E h S hS f hf ⋙
      toDerivedCategoryQuasicoherentPlus B E h S hS 𝒴)
    (derivedQuasicoherentWPlus_isInvertedBy B E h S hS f hf hdist hpar)

/-- The functor `Rf_{QCoh,*}` on the Verdier quotients is induced by `Rf_*`: precomposing it
with the quotient functor of `𝒳` gives the middle vertical functor followed by the quotient
functor of `𝒴`. -/
@[stacks 07BC "the square identifying the induced functor on quotient categories, \
  Q_𝒳 ⋙ Rf_(QCoh,*) = Rf_*^LQCoh ⋙ Q_𝒴"]
theorem toDerivedCategoryQuasicoherentPlus_comp_derivedPushforwardQuasicoherentPlus
    (f : 𝒳 ⟶ 𝒴)
    (hf : ∀ K, derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K))
    (hdist : DerivedPushforwardMapsDistinguished B S hS f)
    (hpar : ∀ K, derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
      derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
        ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K)) :
    toDerivedCategoryQuasicoherentPlus B E h S hS 𝒳 ⋙
        derivedPushforwardQuasicoherentPlus B E h S hS f hf hdist hpar =
      derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange B E h S hS f hf ⋙
        toDerivedCategoryQuasicoherentPlus B E h S hS 𝒴 :=
  Localization.Construction.fac _ _

end AlgebraicGeometry.Stack

end

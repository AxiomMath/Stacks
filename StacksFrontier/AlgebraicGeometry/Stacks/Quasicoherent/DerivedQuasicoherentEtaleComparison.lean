module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.WeakSerreAcrossTopologies

/-!
# Comparing the derived categories of an algebraic stack on its fppf and étale sites

Let `𝒳` be an algebraic stack and abbreviate

`𝒫_𝒳 = Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`.

The comparison morphism `ε : 𝒳_fppf ⟶ 𝒳_étale` of **Stacks 07B8** is the identity of the
underlying category read for the two topologies: its direct image `ε_*` reads an fppf module as
an étale module without touching the presheaf, and its inverse image `ε^*` is fppf
sheafification.  Since `ε^*` is exact it induces a triangulated functor on derived categories,
and **Stacks 07B8** says that this functor fits into a commutative diagram

```
D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⟶ D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D(𝒪_𝒳)
          ↑ ε^*                          ↑ ε^*            ↑ ε^*
 D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)        ⟶ D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⟶ D(𝒳_étale, 𝒪_𝒳)
```

whose horizontal arrows are the inclusions of full subcategories.  This file builds that
diagram: the three vertical functors and the two commuting squares.

## Main definitions

* `AlgebraicGeometry.Stack.etaleModules`: the category `Mod(𝒳_étale, 𝒪_𝒳)`, the ambient category
  of the bottom row.
* `AlgebraicGeometry.Stack.epsilonPullback`: `ε^* : Mod(𝒳_étale, 𝒪_𝒳) ⥤ Mod(𝒪_𝒳)`, fppf
  sheafification, the left adjoint of the restriction
  `AlgebraicGeometry.Stack.fppfToEtaleModules`, which is `ε_*`.
* `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChangeEtale` and
  `AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale`: the two
  subcategories `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` and `D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)` of the bottom row.
* `AlgebraicGeometry.Stack.epsilonPullbackDerived`: the right-hand vertical arrow
  `ε^* : D(𝒳_étale, 𝒪_𝒳) ⥤ D(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.epsilonPullbackDerivedLocallyQuasicoherent` and
  `AlgebraicGeometry.Stack.epsilonPullbackDerivedParasitic`: the middle and the left vertical
  arrows of the diagram.

## Main results

* `AlgebraicGeometry.Stack.epsilonPullbackDerived_rightSquare`: **Stacks 07B8**, the right-hand
  square of the diagram commutes.
* `AlgebraicGeometry.Stack.epsilonPullbackDerived_leftSquare`: **Stacks 07B8**, the left-hand
  square of the diagram commutes.
* `AlgebraicGeometry.Stack.epsilonPullbackDerived_outerRectangle`: the outer rectangle, the
  composite of the two squares.
* `AlgebraicGeometry.Stack.derivedCategoryQuasicoherentEtaleEquivalence`: **Stacks 07B8**, the
  last assertion — the induced equivalence
  `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ≌ D_QCoh(𝒪_𝒳)` — from the source's
  "moreover the left two vertical arrows are equivalences".

## What is carried as a hypothesis

**Stacks 0771 part (1)**, that a module in `LQCoh^fbc(𝒪_𝒳)` is a sheaf for the fppf topology,
is not in this library: the file
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangePullback.lean`
has only part (3) of that proposition.  It is carried below as the hypothesis `hfppfSheaf`, in
exactly the source's form.  Everything the vertical arrows need rests on it: it is what lets
**Stacks 07A8** — which produces from `ε_*` and `ε^*` a pair of quasi-inverse equivalences
between a class `A` of fppf modules and its image `ε_*A` — be applied to
`A = LQCoh^fbc(𝒪_𝒳)`, because `hfppfSheaf` is precisely the statement that the subcategory
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)` *is* that image.

The source's "moreover, the left two vertical arrows are equivalences of triangulated
categories" is obtained in the source from Cohomology on Sites, Lemma **Stacks 07A8** together
with Derived Categories **Stacks 0D7W**.  Both are in this library — 0D7W as
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative` and the
second conclusion of 07A8 as
`Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfLE` — but they are stated
for a site whose objects and morphisms share a universe, which the big site underlying `𝒳` does
not.  The final equivalence of this file therefore carries that assertion as the hypothesis
`[G.IsEquivalence]` on the middle vertical arrow, together with `hW`, the matching of the two
inverted classes — which is the verification the source itself says it omits, that `ε^*`
carries complexes with parasitic cohomology to complexes with parasitic cohomology and
reflects that property.

## Implementation notes

The ambient categories of the two rows are `Mod(𝒪_𝒳)` and `Mod(𝒳_étale, 𝒪_𝒳)`; these are
`AlgebraicGeometry.Stack.fppfModules` and `AlgebraicGeometry.Stack.etaleModules`, both built
from `AlgebraicGeometry.FibredSite.ringStructureSheafCore`, whose underlying presheaf of rings
does not depend on which of the five topologies of **Stacks 06TP** is used.  Accordingly
`ε_* = AlgebraicGeometry.Stack.fppfToEtaleModules` changes nothing but the sheaf condition, and
`AlgebraicGeometry.Stack.fppfToEtaleModules_eq_pushforward` records that it is the instance here
of `Stacks.Cohomology.CompareTopologies.pushforward`, the `ε_*` of **Stacks 07A8**; `ε^*` is
likewise that file's `pullback`, which is why no second comparison of topologies is introduced.

Abelianness of the two module categories is not assumed: it is Mathlib's instance for sheaves
of modules, available as soon as abelian sheafification exists for the topology in question and
weak equivalences there are the locally bijective maps.  Both hold on each of the five sites
associated with an essentially small algebraic stack, by
`AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology` and
`AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_associatedTopology`; they are assumed as
instances rather than derived so that the file does not have to carry the smallness hypothesis.
Assuming `Abelian` itself would not do: the `Preadditive` structure underlying an assumed
abelian structure is opaque, and the exactness instances for `ε^*` would then be about a
different `Preadditive` structure from the one Mathlib's `Functor.mapDerivedCategory` consumes.

That `ε^*` carries each of the two subcategories of the bottom row into the corresponding
subcategory of the top row is checked on cohomology modules, through
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`: an exact functor commutes with the
homology of the derived category, so the cohomology modules of `ε^*K` are `ε^*` of those of
`K`.

Both squares are *equalities* of functors, not merely isomorphisms.  A lift of a functor to a
full subcategory composed with the inclusion of that subcategory is the functor itself, on the
nose — this is why Mathlib defines `CategoryTheory.ObjectProperty.liftCompιIso` as `Iso.refl`.

## References

* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B8](https://stacks.math.columbia.edu/tag/07B8)
* [Stacks Project, Tag 0D7W](https://stacks.math.columbia.edu/tag/0D7W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.CompareTopologies

universe u w t

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The category `Mod(𝒳_étale, 𝒪_𝒳)` of modules on the étale site associated with an algebraic
stack, the ambient category of the bottom row of the diagram of **Stacks 07B8**.  It is the
counterpart for the étale topology of `AlgebraicGeometry.Stack.fppfModules`. -/
abbrev etaleModules := SheafOfModules.{u}
  (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale)

/-- The étale site associated with an algebraic stack is coarser than its fppf site; this is the
inequality of topologies the comparison morphism `ε : 𝒳_fppf ⟶ 𝒳_étale` of **Stacks 07B8** is
made of. -/
abbrev etaleTopologyLeFppf :
    BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale ≤
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf :=
  BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale

/-- `ε_*`, the restriction of an fppf module to the étale site, is the instance here of the
`ε_*` of **Stacks 07A8**.  Neither functor touches the underlying presheaf of modules, so the
two agree on the nose. -/
theorem fppfToEtaleModules_eq_pushforward :
    fppfToEtaleModules B S hS 𝒳 =
      pushforward (etaleTopologyLeFppf B S hS 𝒳)
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) :=
  rfl

/-- **Stacks 0771 part (1) says that `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)` is the image of
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` under `ε_*`.**  Given an étale module which is locally
quasi-coherent with the flat base change property and which, by that part of the source, is a
sheaf for the fppf topology, the same presheaf of modules read as an fppf module lies in
`LQCoh^fbc(𝒪_𝒳)` and restricts back to the module one started with.

This is the one place the hypothesis `hfppfSheaf` is used; everything below goes through
**Stacks 07A8** from here. -/
theorem imageOfLE_of_locallyQuasicoherentFlatBaseChangeEtale
    (hfppfSheaf : ∀ N : etaleModules B S hS 𝒳,
      locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳 N →
        Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
          N.val.presheaf)
    {N : etaleModules B S hS 𝒳}
    (hN : locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳 N) :
    imageOfLE (etaleTopologyLeFppf B S hS 𝒳) _
      (locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳) N :=
  ⟨⟨N.val, hfppfSheaf N hN⟩, hN, ⟨Iso.refl _⟩⟩

/-- The parasitic half of the previous lemma: a module of `𝒫_𝒳 ⊆ Mod(𝒳_étale, 𝒪_𝒳)` is `ε_*` of
a module of `𝒫_𝒳 ⊆ Mod(𝒪_𝒳)`.  Being parasitic (**Stacks 0773**) is a condition on the sections
of the underlying presheaf of modules and so does not change when the sheaf condition is
strengthened from the étale to the fppf topology. -/
theorem imageOfLE_of_parasitic_locallyQuasicoherentFlatBaseChangeEtale
    (hfppfSheaf : ∀ N : etaleModules B S hS 𝒳,
      locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳 N →
        Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
          N.val.presheaf)
    {N : etaleModules B S hS 𝒳}
    (hN : (parasiticModules.{u, w, u} B S hS 𝒳 .etale ⊓
      locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳) N) :
    imageOfLE (etaleTopologyLeFppf B S hS 𝒳) _
      (parasiticModules.{u, w, u} B S hS 𝒳 .fppf ⊓
        locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳) N :=
  ⟨⟨N.val, hfppfSheaf N hN.2⟩, ⟨hN.1, hN.2⟩, ⟨Iso.refl _⟩⟩

section Modules

variable
  [(BigFppfOver.associatedTopology B S hS 𝒳.val.val.p
      .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}]

/-- **`ε^*`, the inverse image along the comparison morphism `ε : 𝒳_fppf ⟶ 𝒳_étale` of
Stacks 07B8.**  It is fppf sheafification of the underlying presheaf of modules, the left
adjoint of the restriction `AlgebraicGeometry.Stack.fppfToEtaleModules`; as such it is the
instance for `𝒳` of the `ε^*` of **Stacks 07A8**. -/
def epsilonPullback : etaleModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒳 :=
  pullback (etaleTopologyLeFppf B S hS 𝒳)
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)

/-- `ε^* ⊣ ε_*`. -/
def epsilonAdjunction :
    epsilonPullback B S hS 𝒳 ⊣ fppfToEtaleModules B S hS 𝒳 :=
  adjunction (etaleTopologyLeFppf B S hS 𝒳) _

/-- The functor `ε^*` is additive. -/
instance : (epsilonPullback B S hS 𝒳).Additive :=
  additive_pullback (etaleTopologyLeFppf B S hS 𝒳) _

/-- The functor `ε^*` preserves finite limits. -/
instance : PreservesFiniteLimits (epsilonPullback B S hS 𝒳) :=
  preservesFiniteLimits_pullback (etaleTopologyLeFppf B S hS 𝒳) _

/-- The functor `ε^*` preserves finite colimits. -/
instance : PreservesFiniteColimits (epsilonPullback B S hS 𝒳) :=
  preservesFiniteColimits_pullback (etaleTopologyLeFppf B S hS 𝒳) _

variable [(locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).IsClosedUnderIsomorphisms]

/-- **`ε^*` carries `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒳)`.**  By
`AlgebraicGeometry.Stack.imageOfLE_of_locallyQuasicoherentFlatBaseChangeEtale` the source
module is `ε_*` of a module of `LQCoh^fbc(𝒪_𝒳)`, and `ε^*ε_*` is the identity there — which is
the first paragraph of the proof of **Stacks 07A8**. -/
theorem locallyQuasicoherentFlatBaseChangeFppfModules_epsilonPullback_obj
    (hfppfSheaf : ∀ N : etaleModules B S hS 𝒳,
      locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳 N →
        Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
          N.val.presheaf)
    {N : etaleModules B S hS 𝒳}
    (hN : locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳 N) :
    locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳
      ((epsilonPullback B S hS 𝒳).obj N) :=
  prop_pullback_obj (etaleTopologyLeFppf B S hS 𝒳) _ _ inferInstance
    (imageOfLE_of_locallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳 hfppfSheaf hN)

variable [(parasiticModules.{u, w, u} B S hS 𝒳 .fppf).IsClosedUnderIsomorphisms]

/-- **`ε^*` carries `𝒫_𝒳 ⊆ Mod(𝒳_étale, 𝒪_𝒳)` into `𝒫_𝒳 ⊆ Mod(𝒪_𝒳)`**, by the same argument as
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModules_epsilonPullback_obj`
applied to the intersection with the parasitic modules. -/
theorem parasitic_locallyQuasicoherentFlatBaseChangeFppfModules_epsilonPullback_obj
    (hfppfSheaf : ∀ N : etaleModules B S hS 𝒳,
      locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳 N →
        Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
          N.val.presheaf)
    {N : etaleModules B S hS 𝒳}
    (hN : (parasiticModules.{u, w, u} B S hS 𝒳 .etale ⊓
      locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳) N) :
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf ⊓
        locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳)
      ((epsilonPullback B S hS 𝒳).obj N) :=
  prop_pullback_obj (etaleTopologyLeFppf B S hS 𝒳) _ _ inferInstance
    (imageOfLE_of_parasitic_locallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳 hfppfSheaf hN)

end Modules

section Derived

variable
  [(BigFppfOver.associatedTopology B S hS 𝒳.val.val.p
      .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS 𝒳.val.val.p
      .etale).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t} (etaleModules B S hS 𝒳)]

/-- The subcategory `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⊆ D(𝒳_étale, 𝒪_𝒳)`: complexes of étale modules
all of whose cohomology modules are locally quasi-coherent with the flat base change property.
This is the middle entry of the bottom row of the diagram of **Stacks 07B8**. -/
abbrev derivedLocallyQuasicoherentFlatBaseChangeEtale :
    ObjectProperty (DerivedCategory (etaleModules B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳)

/-- The subcategory `D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⊆ D(𝒳_étale, 𝒪_𝒳)`: complexes of étale modules all of
whose cohomology modules are parasitic (**Stacks 0773**) *and* locally quasi-coherent with the
flat base change property.  This is the left entry of the bottom row of the diagram of
**Stacks 07B8**. -/
abbrev derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale :
    ObjectProperty (DerivedCategory (etaleModules B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (parasiticModules.{u, w, u} B S hS 𝒳 .etale ⊓
      locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳)

omit [(BigFppfOver.associatedTopology B S hS 𝒳.val.val.p
    .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)] in
/-- The lower-left horizontal arrow of the diagram of **Stacks 07B8**:
`D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)`. -/
theorem derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale_le :
    derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳 ≤
      derivedLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳 :=
  fun _ hK n => (hK n).2

omit [(BigFppfOver.associatedTopology B S hS 𝒳.val.val.p
    .etale).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (etaleModules B S hS 𝒳)] in
/-- The upper-left horizontal arrow of the diagram of **Stacks 07B8**:
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒪_𝒳)`. -/
theorem derivedParasiticLocallyQuasicoherentFlatBaseChange_le :
    derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 ≤
      derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 :=
  fun _ hK n => (hK n).2

/-- **The right-hand vertical arrow of the diagram of Stacks 07B8**, the triangulated functor
`ε^* : D(𝒳_étale, 𝒪_𝒳) ⥤ D(𝒪_𝒳)` induced by the exact functor `ε^*` on modules. -/
@[stacks 07B8 "the right-hand vertical arrow ε^* : D(𝒳_étale, 𝒪_𝒳) ⥤ D(𝒪_𝒳) of the diagram"]
def epsilonPullbackDerived :
    DerivedCategory (etaleModules B S hS 𝒳) ⥤ DerivedCategory (fppfModules B S hS 𝒳) :=
  (epsilonPullback B S hS 𝒳).mapDerivedCategory

/-- The derived functor `ε^*` commutes with the shift. -/
instance : (epsilonPullbackDerived B S hS 𝒳).CommShift ℤ :=
  inferInstanceAs ((epsilonPullback B S hS 𝒳).mapDerivedCategory.CommShift ℤ)

/-- The derived functor `ε^*` is triangulated. -/
instance : (epsilonPullbackDerived B S hS 𝒳).IsTriangulated :=
  inferInstanceAs ((epsilonPullback B S hS 𝒳).mapDerivedCategory.IsTriangulated)

/-- The cohomology modules of `ε^*K` are `ε^*` of the cohomology modules of `K`: `ε^*` is exact,
so it commutes with the homology of the derived category. -/
def epsilonPullbackDerivedHomologyIso (n : ℤ) :
    epsilonPullbackDerived B S hS 𝒳 ⋙
        DerivedCategory.homologyFunctor (fppfModules B S hS 𝒳) n ≅
      DerivedCategory.homologyFunctor (etaleModules B S hS 𝒳) n ⋙ epsilonPullback B S hS 𝒳 :=
  (epsilonPullback B S hS 𝒳).mapDerivedCategoryHomologyIso n

/-- If `ε^*` carries `P` into `Q` on modules, it carries the cohomologically `P` complexes into the
cohomologically `Q` ones. -/
private theorem derivedCategoryB_epsilonPullbackDerived_obj
    {P : ObjectProperty (etaleModules B S hS 𝒳)} {Q : ObjectProperty (fppfModules B S hS 𝒳)}
    [Q.IsClosedUnderIsomorphisms] (hPQ : ∀ {N}, P N → Q ((epsilonPullback B S hS 𝒳).obj N))
    {K : DerivedCategory (etaleModules B S hS 𝒳)} (hK : DerivedCategoryB.derivedCategoryB P K) :
    DerivedCategoryB.derivedCategoryB Q ((epsilonPullbackDerived B S hS 𝒳).obj K) := fun n =>
  Q.prop_of_iso ((epsilonPullbackDerivedHomologyIso B S hS 𝒳 n).app K).symm
    (hPQ (hK n))

variable [(locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).IsClosedUnderIsomorphisms]
  [(parasiticModules.{u, w, u} B S hS 𝒳 .fppf).IsClosedUnderIsomorphisms]
  (hfppfSheaf : ∀ N : etaleModules B S hS 𝒳,
    locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳 N →
      Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
        N.val.presheaf)

include hfppfSheaf

omit [(parasiticModules.{u, w, u} B S hS 𝒳 .fppf).IsClosedUnderIsomorphisms] in
/-- `ε^*` carries `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` into `D_{LQCoh^fbc}(𝒪_𝒳)`: the cohomology
modules of `ε^*K` are `ε^*` of those of `K`, and `ε^*` carries `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)` into
`LQCoh^fbc(𝒪_𝒳)`. -/
theorem derivedLocallyQuasicoherentFlatBaseChange_epsilonPullbackDerived_obj
    {K : DerivedCategory (etaleModules B S hS 𝒳)}
    (hK : derivedLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳 K) :
    derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳
      ((epsilonPullbackDerived B S hS 𝒳).obj K) := by
  exact derivedCategoryB_epsilonPullbackDerived_obj B S hS 𝒳
    (locallyQuasicoherentFlatBaseChangeFppfModules_epsilonPullback_obj B E h S hS 𝒳
      hfppfSheaf) hK

/-- `ε^*` carries `D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)` into `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, by the same
argument as
`AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChange_epsilonPullbackDerived_obj`
applied to the intersection with the parasitic modules. -/
theorem derivedParasiticLocallyQuasicoherentFlatBaseChange_epsilonPullbackDerived_obj
    {K : DerivedCategory (etaleModules B S hS 𝒳)}
    (hK : derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳 K) :
    derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳
      ((epsilonPullbackDerived B S hS 𝒳).obj K) := by
  exact derivedCategoryB_epsilonPullbackDerived_obj B S hS 𝒳
    (parasitic_locallyQuasicoherentFlatBaseChangeFppfModules_epsilonPullback_obj
      B E h S hS 𝒳 hfppfSheaf) hK

/-- **Stacks 07B8, the middle vertical arrow of the diagram.**  The functor

`ε^* : D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⥤ D_{LQCoh^fbc}(𝒪_𝒳)`,

the corestriction to `D_{LQCoh^fbc}(𝒪_𝒳)` of `ε^*` on the ambient derived categories. -/
@[stacks 07B8 "the middle vertical arrow ε^* : D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⥤ \
  D_{LQCoh^fbc}(𝒪_𝒳) of the diagram"]
def epsilonPullbackDerivedLocallyQuasicoherent :
    (derivedLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).FullSubcategory ⥤
      (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory :=
  (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).lift
    ((derivedLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).ι ⋙
      epsilonPullbackDerived B S hS 𝒳)
    (fun K => derivedLocallyQuasicoherentFlatBaseChange_epsilonPullbackDerived_obj
      B E h S hS 𝒳 hfppfSheaf K.property)

/-- **Stacks 07B8, the left vertical arrow of the diagram.**  The functor

`ε^* : D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⥤ D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`,

the corestriction to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of `ε^*` on the ambient derived
categories. -/
@[stacks 07B8 "the left vertical arrow ε^* : D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⥤ \
  D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) of the diagram"]
def epsilonPullbackDerivedParasitic :
    (derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).FullSubcategory ⥤
      (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory :=
  (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).lift
    ((derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).ι ⋙
      epsilonPullbackDerived B S hS 𝒳)
    (fun K => derivedParasiticLocallyQuasicoherentFlatBaseChange_epsilonPullbackDerived_obj
      B E h S hS 𝒳 hfppfSheaf K.property)

omit [(parasiticModules.{u, w, u} B S hS 𝒳 .fppf).IsClosedUnderIsomorphisms] in
/-- **Stacks 07B8, the right-hand square of the diagram commutes.**  Going along the bottom row
from `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` into `D(𝒳_étale, 𝒪_𝒳)` and then up by `ε^*` is going up by
`ε^*` into `D_{LQCoh^fbc}(𝒪_𝒳)` and then along the top row into `D(𝒪_𝒳)`.

This is an equality of functors, not merely an isomorphism: the middle vertical arrow is by
construction the corestriction of `ε^*`. -/
@[stacks 07B8 "the right-hand square of the diagram: the inclusion \
  D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⊆ D(𝒳_étale, 𝒪_𝒳) followed by ε^* is ε^* followed by the \
  inclusion D_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)"]
theorem epsilonPullbackDerived_rightSquare :
    (derivedLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).ι ⋙
        epsilonPullbackDerived B S hS 𝒳 =
      epsilonPullbackDerivedLocallyQuasicoherent B E h S hS 𝒳 hfppfSheaf ⋙
        (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι :=
  rfl

/-- **Stacks 07B8, the left-hand square of the diagram commutes.**  Going along the bottom row
from `D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)` into `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` and then up by `ε^*` is going up
by `ε^*` into `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and then along the top row into
`D_{LQCoh^fbc}(𝒪_𝒳)`. -/
@[stacks 07B8 "the left-hand square of the diagram: the inclusion \
  D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) followed by ε^* is ε^* followed by the \
  inclusion D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒪_𝒳)"]
theorem epsilonPullbackDerived_leftSquare :
    ObjectProperty.ιOfLE
          (derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale_le B E h S hS 𝒳) ⋙
        epsilonPullbackDerivedLocallyQuasicoherent B E h S hS 𝒳 hfppfSheaf =
      epsilonPullbackDerivedParasitic B E h S hS 𝒳 hfppfSheaf ⋙
        ObjectProperty.ιOfLE
          (derivedParasiticLocallyQuasicoherentFlatBaseChange_le B E h S hS 𝒳) :=
  rfl

/-- **Stacks 07B8, the outer rectangle of the diagram commutes**: the composite of the two
squares, read from `D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)` to `D(𝒪_𝒳)`. -/
@[stacks 07B8 "the outer rectangle of the diagram, the composite of its two squares"]
theorem epsilonPullbackDerived_outerRectangle :
    (derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).ι ⋙
        epsilonPullbackDerived B S hS 𝒳 =
      epsilonPullbackDerivedParasitic B E h S hS 𝒳 hfppfSheaf ⋙
        (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι :=
  rfl

omit hfppfSheaf [(locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS
  𝒳).IsClosedUnderIsomorphisms] [(parasiticModules.{u, w, u} B S hS
  𝒳 .fppf).IsClosedUnderIsomorphisms] in
/-- The class of morphisms of `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` whose cone, taken in
`D(𝒳_étale, 𝒪_𝒳)`, lies in `D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)`: the étale counterpart of
`AlgebraicGeometry.Stack.derivedQuasicoherentW`, and the class inverted by the Verdier quotient
appearing in the last assertion of **Stacks 07B8**. -/
abbrev derivedQuasicoherentWEtale :
    MorphismProperty
      (derivedLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).FullSubcategory :=
  MorphismProperty.inverseImage
    (derivedParasiticLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).trW
    (derivedLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).ι

/-- The Verdier quotient

`D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)`

appearing in the last assertion of **Stacks 07B8**, formed exactly as
`AlgebraicGeometry.Stack.derivedCategoryQuasicoherent` is for the fppf site: as the
localization of `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` at the morphisms whose cone lies in
`D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)`. -/
abbrev derivedCategoryQuasicoherentEtale :=
  (derivedQuasicoherentWEtale B E h S hS 𝒳).Localization

/-- The quotient functor onto
`D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)`. -/
abbrev toDerivedCategoryQuasicoherentEtale :
    (derivedLocallyQuasicoherentFlatBaseChangeEtale B E h S hS 𝒳).FullSubcategory ⥤
      derivedCategoryQuasicoherentEtale B E h S hS 𝒳 :=
  (derivedQuasicoherentWEtale B E h S hS 𝒳).Q

/-- **Stacks 07B8, the last assertion.**  If the middle vertical arrow

`ε^* : D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⥤ D_{LQCoh^fbc}(𝒪_𝒳)`

is an equivalence of triangulated categories and matches the two classes of morphisms the
Verdier quotients invert, then it descends to an equivalence

`D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ≌ D_QCoh(𝒪_𝒳)`.

The two hypotheses are the source's own "moreover": `hG` is "the middle vertical arrow is an
equivalence of triangulated categories", which the source gets from **Stacks 07A8** together
with **Stacks 0D7W** — both of which the library has, but only for a site whose objects and
morphisms share a universe; see the module docstring — and
`hW` is the matching of the inverted classes, which comes from the compatibility of `ε^*` with
the left vertical arrow, the verification the source explicitly omits.

Given them the descent is formal: `ε^*` followed by the quotient functor of **Stacks 07B6** is
again a localization at the étale class, by transport of a localization along an equivalence of
the source category, and two localizations at one and the same class of morphisms are
canonically equivalent. -/
@[stacks 07B8 "the last assertion: the induced equivalence \
  D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳), given that the middle \
  vertical arrow is an equivalence matching the two inverted classes"]
def derivedCategoryQuasicoherentEtaleEquivalence
    (hG : (epsilonPullbackDerivedLocallyQuasicoherent B E h S hS 𝒳 hfppfSheaf).IsEquivalence)
    (hW : derivedQuasicoherentWEtale B E h S hS 𝒳 =
      (derivedQuasicoherentW B E h S hS 𝒳).inverseImage
        (epsilonPullbackDerivedLocallyQuasicoherent B E h S hS 𝒳 hfppfSheaf)) :
    derivedCategoryQuasicoherentEtale B E h S hS 𝒳 ≌
      derivedCategoryQuasicoherent B E h S hS 𝒳 := by
  have := hG
  set G := epsilonPullbackDerivedLocallyQuasicoherent B E h S hS 𝒳 hfppfSheaf with hGdef
  set W := derivedQuasicoherentW B E h S hS 𝒳 with hWdef
  set W' := derivedQuasicoherentWEtale B E h S hS 𝒳 with hW'def
  have hinv : W'.IsInvertedBy (G ⋙ toDerivedCategoryQuasicoherent B E h S hS 𝒳) := by
    intro X Y f hf
    rw [hW] at hf
    exact Localization.inverts W.Q W (G.map f) hf
  have hle : W ≤ W'.isoClosure.inverseImage G.asEquivalence.inverse := by
    intro X Y f hf
    refine W'.le_isoClosure _ ?_
    rw [hW, MorphismProperty.inverseImage_iff]
    exact (W.arrow_mk_iso_iff (Arrow.isoMk (G.asEquivalence.counitIso.app X).symm
      (G.asEquivalence.counitIso.app Y).symm
      (G.asEquivalence.counitIso.inv.naturality f).symm)).mp hf
  have hiso : G.asEquivalence.symm.functor ⋙
      (G ⋙ toDerivedCategoryQuasicoherent B E h S hS 𝒳) ≅ W.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.asEquivalence.counitIso W.Q ≪≫ Functor.leftUnitor _
  have : (G ⋙ toDerivedCategoryQuasicoherent B E h S hS 𝒳).IsLocalization W' :=
    Functor.IsLocalization.of_equivalence_source W.Q W
      (G ⋙ toDerivedCategoryQuasicoherent B E h S hS 𝒳) W'
      G.asEquivalence.symm hle hinv hiso
  exact Localization.uniq (toDerivedCategoryQuasicoherentEtale B E h S hS 𝒳)
    (G ⋙ toDerivedCategoryQuasicoherent B E h S hS 𝒳) W'

end Derived

end AlgebraicGeometry.Stack

end

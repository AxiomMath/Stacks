module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticColocalizationTriangle
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasicoherentPullbackExactness
public import StacksFrontier.CategoryTheory.Functor.Derived.InitialResolution

/-!
# Derived pullback of complexes with quasi-coherent cohomology on an algebraic stack

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`.  **Stacks 07BE** makes three
assertions about the inverse image `f^* = f^{-1}` of modules on the fppf sites.

1. *The commutative diagram.*  `f^*` is exact, and it carries `LQCoh^fbc(𝒪_𝒴)` into
   `LQCoh^fbc(𝒪_𝒳)`, so the induced functor `f^* : D(𝒪_𝒴) ⥤ D(𝒪_𝒳)` carries
   `D_{LQCoh^fbc}(𝒪_𝒴)` into `D_{LQCoh^fbc}(𝒪_𝒳)` and the square

   ```
   D_{LQCoh^fbc}(𝒪_𝒳)  ⟶  D(𝒪_𝒳)
          ↑ f^*                ↑ f^*
   D_{LQCoh^fbc}(𝒪_𝒴)  ⟶  D(𝒪_𝒴)
   ```

   commutes.
2. *Left derivability.*  The composite

   `D_{LQCoh^fbc}(𝒪_𝒴) --f^*--> D_{LQCoh^fbc}(𝒪_𝒳) --q_𝒳--> D_QCoh(𝒪_𝒳)`

   is left derivable with respect to the localization `D_{LQCoh^fbc}(𝒪_𝒴) ⟶ D_QCoh(𝒪_𝒴)` of
   **Stacks 07B6**, in the sense of **Stacks 05SV**; `Lf^*_QCoh` is by definition its left
   derived functor.
3. *Adjointness.*  For `f` quasi-compact and quasi-separated, `Lf^*_QCoh` is left adjoint to
   `Rf_{QCoh, *}` on `D^+_QCoh(𝒪_𝒳)`.

Assertions 1 and 2 are what is proved here.  Assertion 3 is not: it needs `Rf_{QCoh, *}`, the
derived pushforward of **Stacks 07BC**, which this library does not have.

## Main definitions

* `AlgebraicGeometry.Stack.fppfModulesPullback`: the inverse image `f^* : Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)`
  of **Stacks 06WE** at the module universe of
  `AlgebraicGeometry.Stack.fppfModules`, together with its additivity and left exactness.
* `AlgebraicGeometry.Stack.derivedFppfModulePullback`: the exact functor
  `f^* : D(𝒪_𝒴) ⥤ D(𝒪_𝒳)` it induces on the unbounded derived categories.
* `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentPullback`: **Stacks 07BE**, assertion 1 —
  the induced functor `D_{LQCoh^fbc}(𝒪_𝒴) ⥤ D_{LQCoh^fbc}(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChange_derivedFppfModulePullback`:
  **Stacks 07BE**, assertion 1 at the level of objects — `f^*K` has locally quasi-coherent
  cohomology with flat base change when `K` does.
* `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentPullback_comp_ι`: **Stacks 07BE**,
  the commutativity of the square.
* `AlgebraicGeometry.Stack.isLeftDerivable_toDerivedCategoryQuasicoherent_comp_pullback`:
  **Stacks 07BE**, assertion 2 — `q_𝒳 ∘ f^*` is left derivable with respect to the class of
  morphisms the Verdier quotient of **Stacks 07B6** inverts.
* `AlgebraicGeometry.Stack.FlatFppf.isLeftDerivable_of_parasiticFreePart`: the same conclusion
  with the colocalization hypothesis discharged from **Stacks 07BA**.

## Implementation notes

### How left derivability is obtained

The source's argument is: for `E` in `D_{LQCoh^fbc}(𝒪_𝒴)` the triangle `E' ⟶ E ⟶ P` of
**Stacks 07BA** has `E' ⟶ E` in the inverted class `S`, and `E' ⟶ E` is *cofinal* in `S/E`,
whence `E'` computes `LF`.  Cofinality of a single object together with the uniqueness that the
orthogonality `Hom(E', P') = 0` provides is exactly initiality of `E' ⟶ E` in `S/E`, and an
initial object of the index category makes the pro-object of **Stacks 05S9** essentially constant
for trivial reasons.  That is
`CategoryTheory.ObjectProperty.isLeftDerivable_trW_of_leftOrthogonal_resolutions` in
`StacksFrontier.CategoryTheory.Functor.Derived.InitialResolution`, and it is what is applied here,
inside the full subcategory `D_{LQCoh^fbc}(𝒪_𝒴)` of `D(𝒪_𝒴)`; the identification of the inverted
class `AlgebraicGeometry.Stack.derivedQuasicoherentW` with the class attached to the subcategory
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)` of `D_{LQCoh^fbc}(𝒪_𝒴)` is
`AlgebraicGeometry.Stack.derivedQuasicoherentW_eq_trW`.

Nothing about the functor being derived is used, so left derivability holds for `q_𝒳 ∘ f^*` and
for every other functor out of `D_{LQCoh^fbc}(𝒪_𝒴)` at once; the statement is nevertheless given
at `q_𝒳 ∘ f^*`, which is the composite the source names and the one whose left derived functor is
`Lf^*_QCoh`.

### The hypotheses carried, and why

*Exactness of `f^*`.*  Left exactness is unconditional and is proved here from
`AlgebraicGeometry.Stack.preservesFiniteLimits_modulePullback`, which holds at every module
universe; additivity likewise.  Right exactness is
`AlgebraicGeometry.Stack.preservesFiniteColimits_modulePullback`, which comes from the adjunction
of **Stacks 06WE** and is therefore available only at a module universe large enough for the two
sites — that is at `u + 1`, whereas `AlgebraicGeometry.Stack.fppfModules`, the category in which
**Stacks 07B6** and **Stacks 07BA** are stated in this library, is seated at the module universe
`u`.  It is carried as the instance hypothesis `[PreservesFiniteColimits …]`.

*`f^*` on modules preserves `LQCoh^fbc`.*  This is **Stacks 0771** part (3), which the source
cites as Cohomology of Stacks, Proposition 103.8.1.  The library has it for the inverse image of
*presheaves* of modules on the associated étale site, as
`AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_stackModulePresheafPullback`,
and even there with the flat base change half (**Stacks 0764** part (1)) assumed; matching that
functor with the inverse image of fppf *sheaves* of modules used here is a further identification
the library does not have.  It is therefore carried as the hypothesis `hpres`.

*The colocalization triangle.*
`AlgebraicGeometry.Stack.FlatFppf.isLeftDerivable_of_parasiticFreePart`
discharges the resolution hypothesis from **Stacks 07BA**,
`AlgebraicGeometry.Stack.FlatFppf.extensionProduct_parasiticFreePart`, and so carries that
result's own hypotheses: the derived module-level `Lg_!` of **Stacks 07AS** part (4) as
`Lsh`, `adj`, `hunit`, and **Stacks 07B9** parts (2)(a), (2)(c) as `hK'`.

*Triangulated structure.*  `D_{LQCoh^fbc}(𝒪_𝒴)` has to be a triangulated subcategory of
`D(𝒪_𝒴)` for the full subcategory to be pretriangulated at all, and
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)` has to be one for the inverted class to be the class attached to
it.  These are **Stacks 0771** and **Stacks 0774**, which the library does not have; as in
`AlgebraicGeometry.Stack.derivedQuasicoherentW_eq_trW` they are carried as instance hypotheses on
the two object properties.

### What is not proved

The adjointness of assertion 3 is absent, and so is the resulting functor `Lf^*_QCoh` on
`D_QCoh(𝒪_𝒴)`: passing from everywhere-definedness to a functor on the Verdier quotient is
**Stacks 05SW**, a separate statement.  What is delivered is the commutative square and the
left derivability, which is precisely the condition under which the source *defines*
`Lf^*_QCoh`.

## References

* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9)
* [Stacks Project, Tag 05SV](https://stacks.math.columbia.edu/tag/05SV)
* [Stacks Project, Tag 05SW](https://stacks.math.columbia.edu/tag/05SW)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
* [Stacks Project, Tag 07BE](https://stacks.math.columbia.edu/tag/07BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Stack

universe u w t t'

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat FlatFppf.isContinuous_inclusion_topology
  FlatFppf.isCocontinuous_inclusion_topology GrothendieckTopology.hasSheafify_addCommGrpCat
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (hE : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The inverse image `f^* : Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)` of modules on the fppf sites of two
algebraic stacks along a 1-morphism `f : 𝒳 ⟶ 𝒴`**, that is `AlgebraicGeometry.Stack.modulePullback`
(**Stacks 06WE**) at the module universe `u` of `AlgebraicGeometry.Stack.fppfModules`.

A 1-morphism of algebraic stacks is strictly over the big fppf category, so the structure sheaf
of `𝒳` is literally the restriction along `f` of the one of `𝒴` and the comparison of scalars is
an `CategoryTheory.eqToHom`. -/
abbrev fppfModulesPullback : fppfModules B S hS 𝒴 ⥤ fppfModules B S hS 𝒳 :=
  modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl

/-- The inverse image of modules along a 1-morphism of algebraic stacks is additive: it does not
change the modules of sections, only the object at which they are taken. -/
instance fppfModulesPullback_additive : (fppfModulesPullback B S hS f).Additive where
  map_add := rfl

/-- The inverse image of modules along a 1-morphism of algebraic stacks is left exact.  This is
`AlgebraicGeometry.Stack.preservesFiniteLimits_modulePullback`, which holds at every module
universe. -/
instance fppfModulesPullback_preservesFiniteLimits :
    PreservesFiniteLimits (fppfModulesPullback B S hS f) :=
  preservesFiniteLimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS _ _ _ _ _ _ _ _

section Derived

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t} (fppfModules B S hS 𝒴)]
  [PreservesFiniteColimits (fppfModulesPullback B S hS f)]

/-- **The exact functor `f^* : D(𝒪_𝒴) ⥤ D(𝒪_𝒳)`** induced on the unbounded derived categories by
the inverse image of modules along a 1-morphism of algebraic stacks.  Since `f^* = f^{-1}` is
exact it needs no derivation: it acts on complexes degreewise. -/
abbrev derivedFppfModulePullback :
    DerivedCategory (fppfModules B S hS 𝒴) ⥤ DerivedCategory (fppfModules B S hS 𝒳) :=
  (fppfModulesPullback B S hS f).mapDerivedCategory

variable [(locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒳).IsClosedUnderIsomorphisms]

/-- **Stacks 07BE, the first assertion, on objects.**  Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks and let `K` be an object of `D_{LQCoh^fbc}(𝒪_𝒴)`.  Then `f^*K` is an object of
`D_{LQCoh^fbc}(𝒪_𝒳)`.

Since `f^*` is exact its cohomology modules are the inverse images of those of `K`, so the
statement reduces degree by degree to the module-level **Stacks 0771** part (3) — that `f^*`
maps `LQCoh^fbc(𝒪_𝒴)` into `LQCoh^fbc(𝒪_𝒳)` — which is the hypothesis `hpres`. -/
@[stacks 07BE "the first assertion, that f^* carries D_LQCoh^fbc(𝒪_𝒴) into D_LQCoh^fbc(𝒪_𝒳), \
on objects; conditional on the module-level statement that f^* maps LQCoh^fbc(𝒪_𝒴) into \
LQCoh^fbc(𝒪_𝒳) (Stacks 0771 part (3), the source's Cohomology of Stacks, Proposition 103.8.1), \
carried as the hypothesis hpres"]
theorem derivedLocallyQuasicoherentFlatBaseChange_derivedFppfModulePullback
    (hpres : ∀ F : fppfModules B S hS 𝒴,
      locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒴 F →
        locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒳
          ((fppfModulesPullback B S hS f).obj F))
    (K : DerivedCategory (fppfModules B S hS 𝒴))
    (hK : derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴 K) :
    derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒳
      ((derivedFppfModulePullback B S hS f).obj K) := fun n =>
  (locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒳).prop_of_iso
    (((fppfModulesPullback B S hS f).mapDerivedCategoryHomologyIso n).app K).symm
    (hpres _ (hK n))

/-- **Stacks 07BE, the first assertion.**  The induced functor
`f^* : D_{LQCoh^fbc}(𝒪_𝒴) ⥤ D_{LQCoh^fbc}(𝒪_𝒳)`, the left vertical arrow of the square of the
source.  Its composite with the inclusion of `D_{LQCoh^fbc}(𝒪_𝒳)` into `D(𝒪_𝒳)` is the
composite of the inclusion of `D_{LQCoh^fbc}(𝒪_𝒴)` with `f^* : D(𝒪_𝒴) ⥤ D(𝒪_𝒳)`, which is the
commutativity of the square; see
`AlgebraicGeometry.Stack.derivedLocallyQuasicoherentPullback_comp_ι`. -/
@[stacks 07BE "the first assertion, the induced functor D_LQCoh^fbc(𝒪_𝒴) ⥤ D_LQCoh^fbc(𝒪_𝒳); \
conditional on the module-level Stacks 0771 part (3), carried as the hypothesis hpres"]
def derivedLocallyQuasicoherentPullback
    (hpres : ∀ F : fppfModules B S hS 𝒴,
      locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒴 F →
        locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒳
          ((fppfModulesPullback B S hS f).obj F)) :
    (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).FullSubcategory ⥤
      (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒳).FullSubcategory :=
  (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒳).lift
    ((derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).ι ⋙
      derivedFppfModulePullback B S hS f)
    fun K => derivedLocallyQuasicoherentFlatBaseChange_derivedFppfModulePullback B E hE S hS f
      hpres K.obj K.property

/-- **Stacks 07BE, the commutativity of the square.**  Restricting `f^*` to the subcategories of
complexes with locally quasi-coherent cohomology and flat base change and then including into
`D(𝒪_𝒳)` is the same as including into `D(𝒪_𝒴)` and applying `f^*`. -/
@[stacks 07BE "the commutativity of the square: the induced functor on D_LQCoh^fbc, followed by \
the inclusion into D(𝒪_𝒳), is the inclusion into D(𝒪_𝒴) followed by f^*; conditional on the \
module-level Stacks 0771 part (3), carried as the hypothesis hpres"]
theorem derivedLocallyQuasicoherentPullback_comp_ι
    (hpres : ∀ F : fppfModules B S hS 𝒴,
      locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒴 F →
        locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒳
          ((fppfModulesPullback B S hS f).obj F)) :
    derivedLocallyQuasicoherentPullback B E hE S hS f hpres ⋙
        (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒳).ι =
      (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).ι ⋙
        derivedFppfModulePullback B S hS f :=
  rfl

end Derived

section LeftDerivable

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒴)]

/-- The subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)` read inside `D_{LQCoh^fbc}(𝒪_𝒴)`: the
triangulated subcategory the Verdier quotient of **Stacks 07B6** divides by. -/
abbrev derivedParasiticInLocallyQuasicoherent : ObjectProperty
    (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).FullSubcategory :=
  (derivedParasiticLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).inverseImage
    (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).ι

/-- **A resolution of an object of `D_{LQCoh^fbc}(𝒪_𝒴)` in the sense of the Bousfield
colocalization of Stacks 07BA, read inside `D_{LQCoh^fbc}(𝒪_𝒴)`.**  An object `K` of
`D_{LQCoh^fbc}(𝒪_𝒴)` that is an extension, in `D(𝒪_𝒴)`, of an object of
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)` by an object of `D_{LQCoh^fbc}(𝒪_𝒴)` left orthogonal to it
receives a morphism of the inverted class `AlgebraicGeometry.Stack.derivedQuasicoherentW` from an
object left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)`.

The triangle is already a triangle of `D(𝒪_𝒴)` with all three terms in `D_{LQCoh^fbc}(𝒪_𝒴)`, and
`AlgebraicGeometry.Stack.derivedQuasicoherentW` is by definition tested on the image of a
morphism in `D(𝒪_𝒴)`, so no lifting of the triangle is needed. -/
theorem exists_derivedQuasicoherentW_leftOrthogonal_of_extensionProduct
    (K : (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).FullSubcategory)
    (hK : (((derivedParasiticLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).leftOrthogonal ⊓
        derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).extensionProduct
      (derivedParasiticLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴)) K.obj) :
    ∃ (K' : (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).FullSubcategory)
      (s : K' ⟶ K), derivedQuasicoherentW B E hE S hS 𝒴 s ∧
        (derivedParasiticInLocallyQuasicoherent B E hE S hS (𝒴 := 𝒴)).leftOrthogonal K' := by
  obtain ⟨K', P, a, b, c, hT, ⟨horth, hK'⟩, hP⟩ := hK
  refine ⟨⟨K', hK'⟩, ObjectProperty.homMk a, ⟨P, b, c, hT, hP⟩, ?_⟩
  intro Y g hY
  exact ObjectProperty.hom_ext _ (horth g.hom hY)

variable [(derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).IsTriangulated]
  [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).IsTriangulated]
  [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E hE S hS
    𝒴).IsClosedUnderIsomorphisms]

/-- **Stacks 07BE, the second assertion.**  Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks.
If every object of `D_{LQCoh^fbc}(𝒪_𝒴)` receives a morphism of the inverted class from an object
left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)` — the Bousfield colocalization of
**Stacks 07BA** — then every functor out of `D_{LQCoh^fbc}(𝒪_𝒴)`, in particular the composite

`D_{LQCoh^fbc}(𝒪_𝒴) --f^*--> D_{LQCoh^fbc}(𝒪_𝒳) --q_𝒳--> D_QCoh(𝒪_𝒳)`

the source names, is left derivable with respect to the class of morphisms that the Verdier
quotient `D_{LQCoh^fbc}(𝒪_𝒴) ⟶ D_QCoh(𝒪_𝒴)` of **Stacks 07B6** inverts, in the sense of
**Stacks 05SV**: the left derived functor is defined at every object.

The resolution is an initial object of the index category `S/E` of **Stacks 05S9**, which is the
source's assertion that `E' ⟶ E` is cofinal in `S/E`; see
`CategoryTheory.ObjectProperty.isLeftDerivable_trW_of_leftOrthogonal_resolutions`. -/
@[stacks 07BE "the second assertion, that q_𝒳 ∘ f^* is left derivable with respect to the \
localization D_LQCoh^fbc(𝒪_𝒴) → D_QCoh(𝒪_𝒴) of 07B6, i.e. that LF is defined at every object; \
conditional on the Bousfield colocalization of 07BA, carried as the hypothesis hres, and on \
0771 and 0774, carried as the triangulated-subcategory instances. The adjointness of \
Lf^*_QCoh with Rf_QCoh,* is NOT proved"]
theorem isLeftDerivable_toDerivedCategoryQuasicoherent_comp_pullback
    [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
    [PreservesFiniteColimits (fppfModulesPullback B S hS f)]
    [(locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒳).IsClosedUnderIsomorphisms]
    (hpres : ∀ F : fppfModules B S hS 𝒴,
      locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒴 F →
        locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒳
          ((fppfModulesPullback B S hS f).obj F))
    (hres : ∀ K : (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).FullSubcategory,
      ∃ (K' : (derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).FullSubcategory)
        (s : K' ⟶ K), derivedQuasicoherentW B E hE S hS 𝒴 s ∧
          (derivedParasiticInLocallyQuasicoherent B E hE S hS (𝒴 := 𝒴)).leftOrthogonal K') :
    (derivedLocallyQuasicoherentPullback B E hE S hS f hpres ⋙
        toDerivedCategoryQuasicoherent B E hE S hS 𝒳).IsLeftDerivable
      (derivedQuasicoherentW B E hE S hS 𝒴) := by
  have hW : derivedQuasicoherentW B E hE S hS 𝒴 =
      (derivedParasiticInLocallyQuasicoherent B E hE S hS (𝒴 := 𝒴)).trW :=
    derivedQuasicoherentW_eq_trW B E hE S hS 𝒴
  rw [hW]
  exact (derivedParasiticInLocallyQuasicoherent B E hE S hS
    (𝒴 := 𝒴)).isLeftDerivable_trW_of_leftOrthogonal_resolutions _
      fun K => by
        obtain ⟨K', s, hs, hK'⟩ := hres K
        exact ⟨K', s, hW ▸ hs, hK'⟩

namespace FlatFppf

/-- **Stacks 07BE, the second assertion, over Stacks 07BA.**  Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks and let `g : Sh(𝒴_{flat,fppf}) ⟶ Sh(𝒴_{fppf})` be the morphism of
ringed topoi of **Stacks 0788** (2).  Given the derived lower shriek `Lg_!` of **Stacks 07AS**
part (4) — carried, as in **Stacks 07BA**, as a functor `Lsh`, an adjunction `Lsh ⊣ g^*` and the
invertibility of its unit — and given that the parasitic-free part `Lg_! g^* K` of an object `K`
of `D_{LQCoh^fbc}(𝒪_𝒴)` is again in `D_{LQCoh^fbc}(𝒪_𝒴)` (**Stacks 07B9** (2)(a), (2)(c),
carried as `hK'`), the composite

`D_{LQCoh^fbc}(𝒪_𝒴) --f^*--> D_{LQCoh^fbc}(𝒪_𝒳) --q_𝒳--> D_QCoh(𝒪_𝒳)`

is left derivable with respect to the localization of **Stacks 07B6**.

The resolution hypothesis of
`AlgebraicGeometry.Stack.isLeftDerivable_toDerivedCategoryQuasicoherent_comp_pullback` is
discharged from **Stacks 07BA**,
`AlgebraicGeometry.Stack.FlatFppf.extensionProduct_parasiticFreePart`, through
`AlgebraicGeometry.Stack.exists_derivedQuasicoherentW_leftOrthogonal_of_extensionProduct`. -/
@[stacks 07BE "the second assertion, that q_𝒳 ∘ f^* is left derivable with respect to the \
localization D_LQCoh^fbc(𝒪_𝒴) → D_QCoh(𝒪_𝒴) of 07B6, with the colocalization input supplied by \
07BA; conditional on the derived module-level Lg_! of 07AS (4) and on 07B9 (2)(a), \
(2)(c), carried as Lsh, adj, hunit and hK', on the module-level 0771 (3), carried as hpres, and \
on 0771 and 0774, carried as the triangulated-subcategory instances. The adjointness of \
Lf^*_QCoh with Rf_QCoh,* is NOT proved"]
theorem isLeftDerivable_of_parasiticFreePart
    [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
    [HasDerivedCategory.{t'} (flatFppfModules B S hS 𝒴)]
    [PreservesFiniteColimits (fppfModulesPullback B S hS f)]
    [(locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒳).IsClosedUnderIsomorphisms]
    [(derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴).IsClosedUnderIsomorphisms]
    (Lsh : DerivedCategory (flatFppfModules B S hS 𝒴) ⥤ DerivedCategory (fppfModules B S hS 𝒴))
    (adj : Lsh ⊣ derivedModuleRestriction B S hS 𝒴) (hunit : IsIso adj.unit)
    (hpres : ∀ F : fppfModules B S hS 𝒴,
      locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒴 F →
        locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒳
          ((fppfModulesPullback B S hS f).obj F))
    (hK' : ∀ K : DerivedCategory (fppfModules B S hS 𝒴),
      derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴 K →
        derivedLocallyQuasicoherentFlatBaseChange B E hE S hS 𝒴
          (parasiticFreePart B S hS 𝒴 Lsh K)) :
    (derivedLocallyQuasicoherentPullback B E hE S hS f hpres ⋙
        toDerivedCategoryQuasicoherent B E hE S hS 𝒳).IsLeftDerivable
      (derivedQuasicoherentW B E hE S hS 𝒴) :=
  isLeftDerivable_toDerivedCategoryQuasicoherent_comp_pullback B E hE S hS f hpres
    fun K => exists_derivedQuasicoherentW_leftOrthogonal_of_extensionProduct B E hE S hS K
      (extensionProduct_parasiticFreePart B S hS 𝒴 Lsh adj E hE hunit K.obj K.property
        (hK' K.obj K.property))

end FlatFppf

end LeftDerivable

end AlgebraicGeometry.Stack

end

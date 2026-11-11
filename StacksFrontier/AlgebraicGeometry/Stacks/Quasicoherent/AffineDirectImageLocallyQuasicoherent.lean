module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonUnivLE
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The direct image along an affine 1-morphism of algebraic stacks on `LQCoh^fbc`

Let `f : 𝒳 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks over a scheme `S` in a big fppf
site, affine in the sense of **Stacks 0CHQ**.  **Stacks 0GQI** makes three assertions about the
direct image on the category `LQCoh^fbc(𝒪_𝒳)` of locally quasi-coherent modules with the flat
base change property:

1. `f_* : LQCoh^fbc(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒴)` is **exact**;
2. `f_*` **commutes with direct sums**;
3. the higher direct images `Rⁱf_*` **vanish** on `LQCoh^fbc(𝒪_𝒳)` for `i > 0`.

The source's proof of (3) reduces along the charts of `𝒴` to an affine morphism of algebraic
spaces (**Stacks 0GQH**), then to an affine morphism of schemes (**Stacks 071Y**), where the
vanishing is **Stacks 01XC**; (1) is then *deduced* from the vanishing of `R¹f_*`; and (2) is
**Stacks 01SB**.

**Stacks 0GQI** itself, in the source's default fppf setting and with all three assertions, is
`AlgebraicGeometry.Stack.stacks0GQI` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/AffineDirectImageFppfVanishing.lean`.  This
file is an étale-site companion at module universe `u + 1`: it delivers (1) as a theorem over
(3), which is the source's own deduction.  Assertion (3) is reduced to the objectwise statement
`AlgebraicGeometry.Stack.ObjectwiseIsZeroHigherDirectImage`, which is what the source's chart
reduction produces; assertion (2) is carried whole.  Both carried clauses are named and both are
described in the implementation notes.

## Main definitions

* `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChangeUnivLE`: membership in
  `LQCoh^fbc(𝒪_𝒳)` at module universe `u + 1`, the universe the higher direct images of module
  sheaves live in.  This is the conjunction
  `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChangeUnivLE_`
  `moduleSheafHigherDirectImage` (**Stacks 0771** part (4)(b)) already states inline.
* `AlgebraicGeometry.Stack.etaleModulesOfStack`, `AlgebraicGeometry.Stack.etaleModulesOfHomSource`,
  `AlgebraicGeometry.Stack.etaleModuleDirectImage`,
  `AlgebraicGeometry.Stack.etaleModuleHigherDirectImage`: `Mod(𝒪_𝒴)`, `Mod(𝒪_𝒳)`, `f_*` and
  `Rⁱf_*` on the étale sites, the étale counterparts of
  `AlgebraicGeometry.Stack.fppfModules` and `AlgebraicGeometry.Stack.fppfHigherDirectImage`.
* `AlgebraicGeometry.Stack.ObjectwiseIsZeroHigherDirectImage`: the carried input of assertion
  (3) — the sections of `Rⁱf_*ℱ` over every object of `𝒴` vanish.
* `AlgebraicGeometry.Stack.DirectImagePreservesDirectSums`: assertion (2) of **Stacks 0GQI**,
  carried.

## Main results

* `AlgebraicGeometry.Stack.isZero_etaleModuleHigherDirectImage_of_objectwise`: assertion (3)
  from the objectwise vanishing, by locality of the zero module on the étale site.
* `AlgebraicGeometry.Stack.shortExact_map_etaleModuleDirectImage_of_isZero_higherDirectImage`:
  **assertion (1) of Stacks 0GQI from assertion (3)**, the source's own deduction.
* `AlgebraicGeometry.Stack.stacks0GQI_of_objectwise_of_preservesDirectSums`: the three
  assertions of **Stacks 0GQI** together, over the two carried clauses.

## Implementation notes

### The category `LQCoh^fbc` and the topology

`LQCoh^fbc(𝒪_𝒳)` is read on the **étale** site, as
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeModules` and
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeEtaleModules` are, and as the library's
form of **Stacks 0771** part (4)(b) in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LocallyQuasicoherentFlatBaseChangeSummary.lean`
is.  The source's default topology is the fppf one, and the fppf reading is the one
`AlgebraicGeometry.Stack.stacks0GQI` is stated in; the two readings of the higher direct images
agree by **Stacks 0771** part (4)(a),
`AlgebraicGeometry.Stack.nonempty_etaleComparison_fppfModulesHigherDirectImage_iso`.  The
membership predicate is therefore the same conjunction that
`AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChangeUnivLE_`
`moduleSheafHigherDirectImage` uses — local quasi-coherence of **Stacks 06WJ** together with the
flat base change property of **Stacks 0762** read at section universe `u + 1` — and the
statements below compose with that theorem on the nose.

That `f_*` and the `Rⁱf_*` carry `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)` at all, which the
source gets from **Stacks 0771**, is exactly that theorem (in degree `0` through
`AlgebraicGeometry.Stack.moduleSheafHigherDirectImageZeroIso`); it is not restated here.

The source of `f` is presented strictly, its structure functor written as
`CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p`, which is the shape the higher direct
images of module sheaves are constructed in and the shape **Stacks 0771** part (4)(b) is stated
in.

### Assertion (3), and what is carried

`AlgebraicGeometry.Stack.ObjectwiseIsZeroHigherDirectImage` asks that the sections of `Rⁱf_*ℱ`
over every object of `𝒴` vanish.  This is precisely the output of steps 2–4 of the source's
proof: **Stacks 0GQH** (proved for the fppf higher direct image of `Mod(𝒪_𝒳)` as
`AlgebraicGeometry.Stack.restrictedFppfModulesHigherDirectImage`, and in derived form, over a base
change isomorphism, as `AlgebraicGeometry.Space.restrictedHigherDirectImageChartIso`) identifies
the restriction of `Rⁱf_*ℱ` to the small étale site of a chart `V` of `𝒴` with `Rⁱf'_*(ℱ|_U)`
for the base change `f' : U ⟶ V` of `f`, an affine morphism of algebraic spaces; the vanishing
of that is **Stacks 073H**, proved as
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_isAffineHom`.

What this file contributes to (3) is only the locality of the zero module,
`SheafOfModules.isZero_iff_forall_isZero_obj`: a sheaf of modules vanishes exactly when all of
its modules of sections do.  That is an *equivalence*, so
`AlgebraicGeometry.Stack.isZero_etaleModuleHigherDirectImage_of_objectwise` locates the content
of assertion (3) at the objects of `𝒴`, where **Stacks 0GQH** and **Stacks 073H** act, and does
not establish it.  Wiring the two tags in is not done here because
`AlgebraicGeometry.Space.restrictedHigherDirectImageChartIso` is stated for the cohomology of a
*total derived* direct image on ringed topoi, and its identification with
`CategoryTheory.Functor.rightDerived` of the degreewise direct image of **Stacks 06WE** — the
functor `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` is — is not available.

### Assertion (1), which is proved

The source's "the vanishing for `R¹f_*` implies exactness of `f_*`" is
`CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact` (**Stacks 015D**) part
(1): the direct image preserves finite limits, being a right adjoint, so vanishing of `Rⁱf_*` in
positive degrees on an object is right acyclicity of that object
(`CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus`, **Stacks 015C**),
and a short exact sequence whose outer terms are right acyclic is carried to a short exact
sequence.

Exactness is stated as preservation of short exact sequences of `Mod(𝒪_𝒳)`, which is how
`AlgebraicGeometry.Stack.stacks0GQI` states it too: `LQCoh^fbc(𝒪_𝒳)` is a weak Serre
subcategory of `Mod(𝒪_𝒳)` by **Stacks 0771** part (2)
(`AlgebraicGeometry.Stack.isWeakSerreClass_lqcohSheafFbcEtaleModules` at module universe `u`),
and the inclusion of a weak Serre subcategory is exact and reflects short exactness, so the two
readings agree.  Only the
outer terms of the sequence are asked to lie in `LQCoh^fbc(𝒪_𝒳)`, which is weaker than the
source's hypothesis and so gives a stronger statement.

### Assertion (2), which is carried

`AlgebraicGeometry.Stack.DirectImagePreservesDirectSums` is assertion (2) verbatim: for every
family in `LQCoh^fbc(𝒪_𝒳)`, indexed by an arbitrary type, `f_*` carries a coproduct cocone to a
coproduct cocone.  The source deduces it from **Stacks 01SB**, the identification of `f_*` on
quasi-coherent modules with restriction of scalars along `𝒪_𝒴 ⟶ f_*𝒪_𝒳`; this library carries
**Stacks 01SB** for schemes
(`StacksFrontier/AlgebraicGeometry/QcohLimits/RestrictScalars.lean`,
`StacksFrontier/AlgebraicGeometry/AffineQcohUnit/Equivalence.lean`), and this file does not transport
it to the étale site of an algebraic stack, so here the clause is assumed.  On the fppf sites at
module universe `u`, `AlgebraicGeometry.Stack.stacks0GQI` proves it from the sections formula over
objects lying over affine schemes instead.  It is stated as
`CategoryTheory.Limits.PreservesColimit` of the discrete diagram, which asks nothing about the
existence of the coproducts; no finiteness is imposed on the index type.

### Affineness

`hf` makes the statements the source's and is what would discharge the two carried clauses; the
reduction performed here consumes none of it, exactly as in
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom` for **Stacks
073H**.  Dropping it would turn each statement into one about an arbitrary 1-morphism, which is
not the source's and, with the carried clauses discharged, would be false.

## References

* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 071Y](https://stacks.math.columbia.edu/tag/071Y)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 0GQH](https://stacks.math.columbia.edu/tag/0GQH)
* [Stacks Project, Tag 0GQI](https://stacks.math.columbia.edu/tag/0GQI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u t s

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_associatedTopology_of_category_succ
  wEqualsLocallyBijective_associatedTopology_of_category_succ

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- Membership in `LQCoh^fbc(𝒪_𝒳)` at module universe `u + 1`: a presheaf of modules over the
structure sheaf of **Stacks 06TV** of a category fibred in groupoids which is locally
quasi-coherent (**Stacks 06WJ**) and has the flat base change property of **Stacks 0762** read
at section universe `u + 1`.

This is the conjunction `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChangeUnivLE_`
`moduleSheafHigherDirectImage` (**Stacks 0771** part (4)(b)) states inline;
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange` is the same conjunction with
the module universe pinned to the universe `u` of the schemes, which is below the universe the
higher direct images of module sheaves live in. -/
abbrev IsLocallyQuasicoherentWithFlatBaseChangeUnivLE {𝒵 : Type (u + 1)} [Category.{u} 𝒵]
    (p : 𝒵 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (F : PresheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) : Prop :=
  IsLocallyQuasicoherent B E h S hS p hp F ∧
    HasFlatBaseChangePropertyUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F

variable {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS}

/-- The category `Mod(𝒪_𝒴)` of modules on the étale site of an algebraic stack over `S`, at the
module universe `u + 1` in which the higher direct images of **Stacks 06WE** live.  This is the
étale counterpart of `AlgebraicGeometry.Stack.fppfModules`. -/
abbrev etaleModulesOfStack (𝒴 : AlgebraicStacks.{u, t} B S hS) :=
  SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))

/-- The category `Mod(𝒪_𝒳)` of modules on the étale site of the source of a 1-morphism of
algebraic stacks over `S`, with the source presented strictly: its structure functor is written
as the morphism's functor followed by the structure functor of the target, which is the shape
the higher direct images of module sheaves are constructed in. -/
abbrev etaleModulesOfHomSource (f : 𝒳 ⟶ 𝒴) :=
  SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
    (etaleTopology B) (etaleTopology_le_topology B))

/-- The direct image `f_* : Mod(𝒪_𝒳) ⟶ Mod(𝒪_𝒴)` of modules on the étale sites of a 1-morphism
of algebraic stacks over `S`: the direct image of **Stacks 06WE** at the étale topology of
**Stacks 06TP**. -/
abbrev etaleModuleDirectImage (f : 𝒳 ⟶ 𝒴) :
    etaleModulesOfHomSource B S hS f ⥤ etaleModulesOfStack B S hS 𝒴 :=
  moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
    (etaleTopology_le_topology B)

/-- The higher direct image `Rⁱf_* : Mod(𝒪_𝒳) ⟶ Mod(𝒪_𝒴)` of modules on the étale sites of a
1-morphism of algebraic stacks over `S`: the `i`-th right derived functor of the direct image of
**Stacks 06WE**.  This is the étale counterpart of
`AlgebraicGeometry.Stack.fppfHigherDirectImage`. -/
abbrev etaleModuleHigherDirectImage (f : 𝒳 ⟶ 𝒴) (i : ℕ) :
    etaleModulesOfHomSource B S hS f ⥤ etaleModulesOfStack B S hS 𝒴 :=
  moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
    (etaleTopology_le_topology B) i

/-! ### Assertion (3): vanishing of the higher direct images -/

/-- The carried input of assertion (3) of **Stacks 0GQI**: the sections of `Rⁱf_*ℱ` over every
object of `𝒴` vanish.

For an affine `f` and an `ℱ` in `LQCoh^fbc(𝒪_𝒳)` this is what steps 2–4 of the source's proof
produce — **Stacks 0GQH** identifies the restriction of `Rⁱf_*ℱ` to a chart of `𝒴` with the
higher direct image along the affine base change of `f` on algebraic spaces, and that vanishes
by **Stacks 073H**, `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_isAffineHom`.
-/
def ObjectwiseIsZeroHigherDirectImage (f : 𝒳 ⟶ 𝒴) (ℱ : etaleModulesOfHomSource B S hS f)
    (i : ℕ) : Prop :=
  ∀ y : 𝒴.val.val.obj,
    IsZero (((etaleModuleHigherDirectImage B S hS f i).obj ℱ).val.obj (Opposite.op y))

/-- **Assertion (3) of Stacks 0GQI from its objectwise form.**  If the sections of `Rⁱf_*ℱ` over
every object of `𝒴` vanish then `Rⁱf_*ℱ = 0`.

The step is the locality of the zero module, `SheafOfModules.isZero_iff_forall_isZero_obj`; it is
an equivalence, so this locates assertion (3) at the objects of `𝒴`, where **Stacks 0GQH** and
**Stacks 073H** act, rather than establishing it.  See the implementation notes of this file. -/
theorem isZero_etaleModuleHigherDirectImage_of_objectwise (f : 𝒳 ⟶ 𝒴) (i : ℕ)
    (ℱ : etaleModulesOfHomSource B S hS f)
    (hobj : ObjectwiseIsZeroHigherDirectImage B S hS f ℱ i) :
    IsZero ((etaleModuleHigherDirectImage B S hS f i).obj ℱ) :=
  (SheafOfModules.isZero_iff_forall_isZero_obj _ _).2 hobj

/-! ### Assertion (2): commutation with direct sums -/

/-- **Assertion (2) of Stacks 0GQI**, carried: the direct image along `f` carries a coproduct of
a family of members of `LQCoh^fbc(𝒪_𝒳)`, indexed by an arbitrary type, to a coproduct.

Nothing in this file proves this.  The source gets it from **Stacks 01SB**, which identifies
`f_*` on quasi-coherent modules with restriction of scalars along `𝒪_𝒴 ⟶ f_*𝒪_𝒳`; this library
states **Stacks 01SB** for schemes.  The fppf form of the assertion at module universe `u` is
part of `AlgebraicGeometry.Stack.stacks0GQI`.  Preservation is asked as
`CategoryTheory.Limits.PreservesColimit` of the discrete diagram, so the statement presupposes
no coproducts, and the index type is unrestricted. -/
def DirectImagePreservesDirectSums (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ {I : Type s} (ℱ : I → etaleModulesOfHomSource B S hS f),
    (∀ j, IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (ℱ j).val) →
    PreservesColimit (Discrete.functor ℱ) (etaleModuleDirectImage B S hS f)

/-! ### Assertion (1), and the three assertions of Stacks 0GQI together -/

section Affine

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Assertion (1) of Stacks 0GQI from assertion (3)**, which is the source's own deduction.

Let `f : 𝒳 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks over `S` and suppose the higher
direct images `Rⁱf_*` vanish in positive degrees on `LQCoh^fbc(𝒪_𝒳)`.  Then `f_*` carries a
short exact sequence of `𝒪_𝒳`-modules on `𝒳_étale` whose outer terms lie in `LQCoh^fbc(𝒪_𝒳)` to
a short exact sequence of `𝒪_𝒴`-modules on `𝒴_étale`; that is, `f_*` is exact on
`LQCoh^fbc(𝒪_𝒳)`.

The vanishing in positive degrees is right acyclicity for `f_*`, by **Stacks 015C** and left
exactness of the right adjoint `f_*`, and **Stacks 015D** part (1) turns right acyclicity of the
outer terms into short exactness of the image.  Affineness is what discharges `hvan` and is
consumed nowhere in the deduction, which is why the binder is written `_hf`.

This is the étale-site, module-universe-`u + 1` companion of assertion (1) of **Stacks 0GQI**;
the tag itself, with all three assertions on the fppf sites, is
`AlgebraicGeometry.Stack.stacks0GQI`. -/
theorem shortExact_map_etaleModuleDirectImage_of_isZero_higherDirectImage (f : 𝒳 ⟶ 𝒴)
    (_hf : AlgebraicStacks.IsAffineHom B S hS f)
    (hvan : ∀ (i : ℕ), 0 < i → ∀ ℱ : etaleModulesOfHomSource B S hS f,
      IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ℱ.val →
        IsZero ((etaleModuleHigherDirectImage B S hS f i).obj ℱ))
    (Sq : ShortComplex (etaleModulesOfHomSource B S hS f)) (hSq : Sq.ShortExact)
    (h₁ : IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) Sq.X₁.val)
    (h₃ : IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) Sq.X₃.val) :
    (Sq.map (etaleModuleDirectImage B S hS f)).ShortExact := by
  have : EnoughInjectives (etaleModulesOfHomSource B S hS f) :=
    enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
      (etaleTopology_le_topology B)
  have hac : ∀ ℱ : etaleModulesOfHomSource B S hS f,
      IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ℱ.val →
        (etaleModuleDirectImage B S hS f).rightAcyclic ℱ := by
    intro ℱ hℱ
    refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
      (etaleModuleDirectImage B S hS f) ℱ).2 inferInstance).2 fun i hi => ?_
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi.le).symm⟩
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ rfl ℱ).2
      (hvan n (by exact_mod_cast hi) ℱ hℱ)
  exact ((Functor.rightAcyclic_and_shortExact_map_of_shortExact
    (etaleModuleDirectImage B S hS f) Sq hSq).1 (hac _ h₁) (hac _ h₃)).2

/-- **The three assertions of Stacks 0GQI on the étale sites, over two carried clauses.** Let
`f : 𝒳 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks over `S`
(**Stacks 0CHQ**).  Then, on the category `LQCoh^fbc(𝒪_𝒳)` of locally quasi-coherent
`𝒪_𝒳`-modules with the flat base change property, read on the étale site:

1. `f_*` is exact — it carries a short exact sequence whose outer terms lie in `LQCoh^fbc(𝒪_𝒳)`
   to a short exact sequence;
2. `f_*` commutes with direct sums; and
3. `Rⁱf_*` vanishes for every `i > 0`.

Assertion (1) is *proved*, from assertion (3), which is the source's own deduction.  Assertion
(3) is the carried `hobj`, the objectwise vanishing that steps 2–4 of the source's proof produce
and assertion (2) is the carried `h01SB`; on the fppf sites at module universe `u` all three
assertions are proved outright as `AlgebraicGeometry.Stack.stacks0GQI`.  See the
implementation notes of this file for what each carried clause is and which tags would
discharge it.  Affineness is what discharges the two carried clauses and is consumed nowhere
below, which is why the binder is written `_hf`. -/
theorem stacks0GQI_of_objectwise_of_preservesDirectSums (f : 𝒳 ⟶ 𝒴)
    (_hf : AlgebraicStacks.IsAffineHom B S hS f)
    (hobj : ∀ (i : ℕ), 0 < i → ∀ ℱ : etaleModulesOfHomSource B S hS f,
      IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ℱ.val →
        ObjectwiseIsZeroHigherDirectImage B S hS f ℱ i)
    (h01SB : DirectImagePreservesDirectSums.{u, t, s} B E h S hS f) :
    (∀ Sq : ShortComplex (etaleModulesOfHomSource B S hS f), Sq.ShortExact →
        IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) Sq.X₁.val →
        IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) Sq.X₃.val →
        (Sq.map (etaleModuleDirectImage B S hS f)).ShortExact) ∧
      DirectImagePreservesDirectSums.{u, t, s} B E h S hS f ∧
      ∀ (i : ℕ), 0 < i → ∀ ℱ : etaleModulesOfHomSource B S hS f,
        IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
            (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ℱ.val →
          IsZero ((etaleModuleHigherDirectImage B S hS f i).obj ℱ) :=
  have hvan : ∀ (i : ℕ), 0 < i → ∀ ℱ : etaleModulesOfHomSource B S hS f,
      IsLocallyQuasicoherentWithFlatBaseChangeUnivLE B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ℱ.val →
        IsZero ((etaleModuleHigherDirectImage B S hS f i).obj ℱ) :=
    fun i hi ℱ hℱ =>
      isZero_etaleModuleHigherDirectImage_of_objectwise B S hS f i ℱ (hobj i hi ℱ hℱ)
  ⟨fun Sq hSq h₁ h₃ => shortExact_map_etaleModuleDirectImage_of_isZero_higherDirectImage
      B E h S hS f _hf hvan Sq hSq h₁ h₃, h01SB, hvan⟩

end Affine

end AlgebraicGeometry.Stack

end

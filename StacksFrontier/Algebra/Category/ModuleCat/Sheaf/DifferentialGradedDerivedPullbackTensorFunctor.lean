module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensorLeftDerived
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions

/-!
# The derived pullback-tensor functor `D(ℬ, d) ⥤ D(𝒜', d)`

Let `f` be a morphism of ringed sites, presented as a functor `u : C' ⥤ C` in the direction
opposite to `f` together with the structure map `σ` of its sheaves of rings; let `φ` be a
homomorphism of sheaves of differential graded algebras from `ℬ` on the target to `𝒜` on the
source, and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule. Tag 0FTF says that the functor
`ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE, followed by the localization functor
`K(Mod(𝒜', d)) → D(𝒜', d)`, has a left derived extension `D(ℬ, d) → D(𝒜', d)` whose value on a
good right differential graded `ℬ`-module `𝒫` is `f^*𝒫 ⊗_𝒜 𝒩`.

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackTensorLeftDerived.lean`
proves that statement in the source's own vocabulary for a derived functor: the left derived
functor is everywhere defined in the sense of Tag 05SV and every object represented by a good
module computes it in the sense of Tag 05SX. Neither notion produces a functor on the derived
categories. This file writes the functor down: `derivedPullbackTensor` is an honest functor
`D(ℬ, d) ⥤ D(𝒜', d)` between the development's own derived categories, carrying a counit which
is invertible at every good module, and it is the unique functor with that property up to a
unique isomorphism compatible with the counits.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GoodResolutionData.objectProperty` is the class of
  objects of `K(Mod(ℬ, d))` represented by a good right differential graded `ℬ`-module.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackTensor` is the left derived extension
  `D(ℬ, d) ⥤ D(𝒜', d)` of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`, as a functor.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackTensorCounit` is its counit, the
  canonical transformation from `ℳ ↦ L(f^*ℳ ⊗_𝒜 𝒩)` precomposed with the localization to the
  image of the functor of Tag 0FTE.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackTensorObjIso` is the identification of
  the value of the derived functor at a good module `𝒫` with `f^*𝒫 ⊗_𝒜 𝒩`.

## Main results

* `SheafOfModules.DifferentialGradedModule.hasPointwiseLeftDerivedFunctor_pullbackTensor` and
  `hasLeftDerivedFunctor_pullbackTensor`: the functor of Tag 0FTE followed by the localization
  functor has a pointwise left derived functor, hence a left derived functor, with respect to
  the quasi-isomorphisms of `K(Mod(ℬ, d))`.
* `SheafOfModules.DifferentialGradedModule.isLeftDerivedFunctor_derivedPullbackTensorCounit`:
  the counit exhibits `derivedPullbackTensor` as that left derived functor, i.e. as a right Kan
  extension along the localization functor.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedPullbackTensorCounit_app_of_isGood`:
  the counit is an isomorphism at every good right differential graded `ℬ`-module. This is the
  value clause of Tag 0FTF.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackTensorObjIso_naturality`: that
  identification is natural in the good module.
* `SheafOfModules.DifferentialGradedModule.isLeftDerivedFunctor_of_isIso_app_of_isGood` and
  `isIso_app_of_isLeftDerivedFunctor`: for a functor `Λ` of the derived categories equipped with
  a transformation to the image of the functor of Tag 0FTE, being the left derived functor and
  having an invertible transformation at every good module are the same condition.
* `SheafOfModules.DifferentialGradedModule.exists_iso_derivedPullbackTensor`: consequently any
  such `Λ` is isomorphic to `derivedPullbackTensor`, by an isomorphism carrying one
  transformation to the other.

## Implementation notes

**Nothing about a derived functor is carried.** The inputs are the ones of Tag 0FTF, and each is
the conclusion of a different tag: the construction of the pullback of differential graded
modules and of its differential graded extension (`PullbackData`, `PullbackData.HomotopyExtension`,
Tag 0FSA), the construction of the tensor product with a bimodule (`TensorFunctorData`), the
existence of good resolutions and the goodness of a cone (`GoodResolutionData`, Tags 0FSH and
0FSC), and the exactness of the functor of Tag 0FTE together with the acyclicity of the
pullback-tensor of a good acyclic module (`PullbackTensorExactnessData`, Tag 0FSI). None of them
mentions a derived category, a derived functor, or the value of a functor on a good module. In
particular the functor built here is not assumed to exist, nor is its value on a good module
assumed: both are proved.

**Where the construction comes from.** `CategoryTheory.LeftDerivedByResolutions`, in
`StacksFrontier/CategoryTheory/Localization/LeftDerivedByResolutions.lean`, does the general work:
for a class of morphisms with a right calculus of fractions and a class of objects which
resolves every object, a functor which inverts the morphisms of the class between resolving
objects has a pointwise total left derived functor, its counit is invertible on the resolving
objects, and the converse criterion and the uniqueness statement hold. The class of objects is
`GoodResolutionData.objectProperty`; that it resolves is Tag 0FSH; and the one computation,
that the functor inverts quasi-isomorphisms of good modules, is
`quasiIso_pullbackTensorFunctor_map_of_isGood`, already available. The derived functor itself is
Mathlib's `CategoryTheory.Functor.totalLeftDerived`, a right Kan extension along the
localization functor.

**Why the value on a good module is an isomorphism rather than an equality.** The value of a
right Kan extension at an object is a limit, and a limit is determined only up to canonical
isomorphism, so no equality of objects of `D(𝒜', d)` is available or claimed; what is proved is
that the counit, a morphism of `D(𝒜', d)` natural in the module, is invertible there. An
equality would also be the wrong statement to prove: it forces `eqToHom` into the compatibility
with homomorphisms, whereas naturality of the counit states that compatibility directly, and the
isomorphism is what every consumer of the identification actually uses.

**The standing hypothesis on the quasi-isomorphisms** is that they admit a right calculus of
fractions, which is Tag 0FT4 and is where a left derivability structure comes from. It is a
hypothesis here only because the sites are arbitrary: on a ringed site it is the instance
`SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasRightCalculusOfFractions` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedQuasiIsoMultiplicative.lean`,
proved there from the triangulated structure on `K(Mod(ℬ, d))`. Saturation of the
quasi-isomorphisms, which Tag 06XN needs and which the Tag 0FTF file therefore assumes, is not
needed here: the derivability structure replaces the appeal to Tag 06XN.

The two sheafification hypotheses on each site are the ones making its sheaves of modules
abelian, so that complexes of them have cohomology; they are the hypotheses under which
`quasiIsomorphisms` and `derivedCategory` are defined.

## References

* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 05SV](https://stacks.math.columbia.edu/tag/05SV)
* [Stacks Project, Tag 05SX](https://stacks.math.columbia.edu/tag/05SX)
-/

@[expose] public section

open CategoryTheory

universe t a a' m m' s z v u v' u'

namespace SheafOfModules

namespace DifferentialGradedModule

section Construction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J' AddCommGrpCat.{m'}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m'}]
  {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}

/-- The objects of the homotopy category `K(Mod(ℬ, d))` represented by a good right
differential graded `ℬ`-module: the class of objects which resolves every object and on which
the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` inverts the quasi-isomorphisms. -/
def GoodResolutionData.objectProperty (g : GoodResolutionData.{t, a', m', v', u'} B) :
    ObjectProperty (HomotopyCategory.{t, a', m'} B) :=
  fun Y => g.IsGood Y.as

/-- **Tag 0FSH on the homotopy category.** Every object of `K(Mod(ℬ, d))` receives a
quasi-isomorphism from an object represented by a good right differential graded `ℬ`-module:
this is the good resolution of the module representing it. -/
theorem GoodResolutionData.exists_objectProperty
    (g : GoodResolutionData.{t, a', m', v', u'} B) (X : HomotopyCategory.{t, a', m'} B) :
    ∃ (Y : HomotopyCategory.{t, a', m'} B) (_ : g.objectProperty Y) (ss : Y ⟶ X),
      quasiIsomorphisms.{t, a', m'} B ss := by
  obtain ⟨Q, p, hQ, hp⟩ := g.exists_isGood X.as
  exact ⟨(HomotopyCategory.quotient B).obj Q, hQ, (HomotopyCategory.quotient B).map p,
    (quasiIsomorphisms_quotient_map_iff p).2 hp⟩

/-- The functor induced on the homotopy categories by `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` carries a
quasi-isomorphism between objects represented by good modules to a quasi-isomorphism: the
morphism is the class of a homomorphism of good modules, to which
`quasiIso_pullbackTensorFunctor_map_of_isGood` applies. -/
theorem quasiIsomorphisms_pullbackTensor_map_of_objectProperty
    {P : PullbackData.{t, a, m, v, u, a', m'} φ} (E : P.HomotopyExtension)
    {D : TensorFunctorData.{t, a, m, z, s} A A' N}
    {g : GoodResolutionData.{t, a', m', v', u'} B}
    (hE : PullbackTensorExactnessData P D g)
    {X Y : HomotopyCategory.{t, a', m'} B} (ss : X ⟶ Y)
    (hss : quasiIsomorphisms.{t, a', m'} B ss) (hX : g.objectProperty X)
    (hY : g.objectProperty Y) :
    quasiIsomorphisms.{t, a, s} A' ((HomotopyCategory.pullbackTensor E D).map ss) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X.as ⟶ Y.as, (HomotopyCategory.quotient B).map ψ = ss :=
    ⟨(HomotopyCategory.quotient B).preimage ss, (HomotopyCategory.quotient B).map_preimage ss⟩
  subst hψ
  exact (quasiIsomorphisms_quotient_map_iff _).2
    (quasiIso_pullbackTensorFunctor_map_of_isGood hE ψ hX hY (hss ψ rfl))

/-- The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` followed by the localization functor
`K(Mod(𝒜', d)) → D(𝒜', d)` inverts the quasi-isomorphisms between objects represented by good
modules, the localization functor inverting the quasi-isomorphism of the previous lemma. This is
the hypothesis under which a resolving class computes a left derived functor. -/
theorem isIso_pullbackTensor_map_of_objectProperty
    {P : PullbackData.{t, a, m, v, u, a', m'} φ} (E : P.HomotopyExtension)
    {D : TensorFunctorData.{t, a, m, z, s} A A' N}
    {g : GoodResolutionData.{t, a', m', v', u'} B}
    (hE : PullbackTensorExactnessData P D g)
    {X Y : HomotopyCategory.{t, a', m'} B} (ss : X ⟶ Y)
    (hss : quasiIsomorphisms.{t, a', m'} B ss) (hX : g.objectProperty X)
    (hY : g.objectProperty Y) :
    IsIso ((HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A').map ss) :=
  (quasiIsomorphisms.{t, a, s} A').Q_inverts _
    (quasiIsomorphisms_pullbackTensor_map_of_objectProperty E hE ss hss hX hY)

variable {P : PullbackData.{t, a, m, v, u, a', m'} φ}
  {D : TensorFunctorData.{t, a, m, z, s} A A' N}
  {g : GoodResolutionData.{t, a', m', v', u'} B}

section Derived

variable [(quasiIsomorphisms.{t, a', m'} B).HasRightCalculusOfFractions]

/-- **Tag 0FTF, existence.** The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE followed by the
localization functor `K(Mod(𝒜', d)) → D(𝒜', d)` has a *pointwise* left derived functor with
respect to the quasi-isomorphisms of `K(Mod(ℬ, d))`: the good modules resolve every object and
the functor inverts the quasi-isomorphisms between them, which is what
`CategoryTheory.LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions` asks
for. -/
theorem hasPointwiseLeftDerivedFunctor_pullbackTensor (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g) :
    (HomotopyCategory.pullbackTensor E D ⋙
        toDerivedCategory A').HasPointwiseLeftDerivedFunctor (quasiIsomorphisms.{t, a', m'} B) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions
    (quasiIsomorphisms.{t, a', m'} B) g.objectProperty g.exists_objectProperty _
    (isIso_pullbackTensor_map_of_objectProperty E hE)

/-- The same functor has a left derived functor, i.e. a right Kan extension along the
localization functor `K(Mod(ℬ, d)) → D(ℬ, d)` exists. -/
theorem hasLeftDerivedFunctor_pullbackTensor (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g) :
    (HomotopyCategory.pullbackTensor E D ⋙
        toDerivedCategory A').HasLeftDerivedFunctor (quasiIsomorphisms.{t, a', m'} B) :=
  have := hasPointwiseLeftDerivedFunctor_pullbackTensor E hE
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

/-- **The derived pullback-tensor functor** `D(ℬ, d) ⥤ D(𝒜', d)`: the left derived extension of
the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE followed by the localization functor
`K(Mod(𝒜', d)) → D(𝒜', d)`, taken as the total left derived functor along the localization
functor `K(Mod(ℬ, d)) → D(ℬ, d)`. Its value on a good right differential graded `ℬ`-module `𝒫`
is `f^*𝒫 ⊗_𝒜 𝒩`, which is `derivedPullbackTensorObjIso`. -/
noncomputable def derivedPullbackTensor (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g) :
    derivedCategory.{t, a', m'} B ⥤ derivedCategory.{t, a, s} A' :=
  haveI := hasLeftDerivedFunctor_pullbackTensor E hE
  Functor.totalLeftDerived (HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A')
    (toDerivedCategory B) (quasiIsomorphisms.{t, a', m'} B)

/-- The counit of the derived pullback-tensor functor: the canonical transformation from the
composite `K(Mod(ℬ, d)) → D(ℬ, d) → D(𝒜', d)` to the composite
`K(Mod(ℬ, d)) → K(Mod(𝒜', d)) → D(𝒜', d)`, natural in the object of `K(Mod(ℬ, d))`. Its
component at a module `ℳ` is the comparison `f^*ℳ ⊗^L_𝒜 𝒩 → f^*ℳ ⊗_𝒜 𝒩`. -/
noncomputable def derivedPullbackTensorCounit (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g) :
    toDerivedCategory B ⋙ derivedPullbackTensor E hE ⟶
      HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A' :=
  haveI := hasLeftDerivedFunctor_pullbackTensor E hE
  Functor.totalLeftDerivedCounit (HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A')
    (toDerivedCategory B) (quasiIsomorphisms.{t, a', m'} B)

/-- The counit exhibits `derivedPullbackTensor` as the left derived functor of the functor of
Tag 0FTE followed by the localization functor: it is a right Kan extension along the
localization functor `K(Mod(ℬ, d)) → D(ℬ, d)`. -/
theorem isLeftDerivedFunctor_derivedPullbackTensorCounit (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g) :
    (derivedPullbackTensor E hE).IsLeftDerivedFunctor (derivedPullbackTensorCounit E hE)
      (quasiIsomorphisms.{t, a', m'} B) :=
  have := hasLeftDerivedFunctor_pullbackTensor E hE
  show (Functor.totalLeftDerived (HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A')
      (toDerivedCategory B) (quasiIsomorphisms.{t, a', m'} B)).IsLeftDerivedFunctor
    (Functor.totalLeftDerivedCounit (HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A')
      (toDerivedCategory B) (quasiIsomorphisms.{t, a', m'} B))
    (quasiIsomorphisms.{t, a', m'} B) from inferInstance

/-- **Tag 0FTF, the value on a good module.** At a good right differential graded `ℬ`-module the
counit of the derived pullback-tensor functor is an isomorphism: the good modules are a resolving
class on which the functor inverts the quasi-isomorphisms, and the counit of a left derived
functor is invertible on such a class. -/
theorem isIso_derivedPullbackTensorCounit_app_of_isGood (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    {Q : DifferentialGradedModule.{t, a', m'} B} (hQ : g.IsGood Q) :
    IsIso ((derivedPullbackTensorCounit E hE).app ((HomotopyCategory.quotient B).obj Q)) :=
  have := isLeftDerivedFunctor_derivedPullbackTensorCounit E hE
  LeftDerivedByResolutions.isIso_app_of_resolutions (quasiIsomorphisms.{t, a', m'} B)
    g.objectProperty g.exists_objectProperty _
    (isIso_pullbackTensor_map_of_objectProperty E hE)
    (toDerivedCategory B) (derivedPullbackTensor E hE) (derivedPullbackTensorCounit E hE)
    ((HomotopyCategory.quotient B).obj Q) hQ

/-- **Tag 0FTF, the value on a good module**, read as an isomorphism: the value of the derived
pullback-tensor functor at the image in `D(ℬ, d)` of a good right differential graded
`ℬ`-module `𝒫` is isomorphic to the image in `D(𝒜', d)` of `f^*𝒫 ⊗_𝒜 𝒩`, by the counit. -/
noncomputable def derivedPullbackTensorObjIso (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    {Q : DifferentialGradedModule.{t, a', m'} B} (hQ : g.IsGood Q) :
    (derivedPullbackTensor E hE).obj
        ((toDerivedCategory B).obj ((HomotopyCategory.quotient B).obj Q)) ≅
      (toDerivedCategory A').obj
        ((HomotopyCategory.quotient A').obj ((pullbackTensorFunctor P D).obj Q)) :=
  @asIso _ _ _ _ _ (isIso_derivedPullbackTensorCounit_app_of_isGood E hE hQ)

/-- The identification of the value at a good module is the counit. -/
@[simp]
theorem derivedPullbackTensorObjIso_hom (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    {Q : DifferentialGradedModule.{t, a', m'} B} (hQ : g.IsGood Q) :
    (derivedPullbackTensorObjIso E hE hQ).hom =
      (derivedPullbackTensorCounit E hE).app ((HomotopyCategory.quotient B).obj Q) :=
  rfl

/-- The identification of the value at a good module is natural in the good module: on the image
of a homomorphism `ψ` of good modules the derived functor is the image of `f^*ψ ⊗_𝒜 1`, read
through the two identifications. This is the compatibility with homomorphisms that the value
clause of Tag 0FTF asserts, and it is naturality of the counit. -/
theorem derivedPullbackTensorObjIso_naturality (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    {Q Q₂ : DifferentialGradedModule.{t, a', m'} B} (hQ : g.IsGood Q) (hQ₂ : g.IsGood Q₂)
    (ψ : Q ⟶ Q₂) :
    (derivedPullbackTensor E hE).map
          ((toDerivedCategory B).map ((HomotopyCategory.quotient B).map ψ)) ≫
        (derivedPullbackTensorObjIso E hE hQ₂).hom =
      (derivedPullbackTensorObjIso E hE hQ).hom ≫
        (toDerivedCategory A').map
          ((HomotopyCategory.quotient A').map ((pullbackTensorFunctor P D).map ψ)) := by
  simpa using (derivedPullbackTensorCounit E hE).naturality
    ((HomotopyCategory.quotient B).map ψ)

/-- The converse criterion: a functor `Λ` of the derived categories, together with a
transformation `β` to the image of the functor of Tag 0FTE which is invertible at every good
right differential graded `ℬ`-module, is the left derived functor of that composite. So being a
left derived extension of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` is exactly the condition of taking the prescribed
value on the good modules. -/
theorem isLeftDerivedFunctor_of_isIso_app_of_isGood (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Λ : derivedCategory.{t, a', m'} B ⥤ derivedCategory.{t, a, s} A')
    (β : toDerivedCategory B ⋙ Λ ⟶ HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A')
    (hβ : ∀ Q : DifferentialGradedModule.{t, a', m'} B, g.IsGood Q →
      IsIso (β.app ((HomotopyCategory.quotient B).obj Q))) :
    Λ.IsLeftDerivedFunctor β (quasiIsomorphisms.{t, a', m'} B) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (quasiIsomorphisms.{t, a', m'} B) g.objectProperty g.exists_objectProperty _
    (isIso_pullbackTensor_map_of_objectProperty E hE)
    (toDerivedCategory B) Λ β (fun X hX => hβ X.as hX)

/-- **Uniqueness of the derived pullback-tensor functor.** Any functor `Λ` of the derived
categories carrying a transformation to the image of the functor of Tag 0FTE which is invertible
at every good right differential graded `ℬ`-module is isomorphic to `derivedPullbackTensor`, by
an isomorphism carrying the counit to that transformation. -/
theorem exists_iso_derivedPullbackTensor (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Λ : derivedCategory.{t, a', m'} B ⥤ derivedCategory.{t, a, s} A')
    (β : toDerivedCategory B ⋙ Λ ⟶ HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A')
    (hβ : ∀ Q : DifferentialGradedModule.{t, a', m'} B, g.IsGood Q →
      IsIso (β.app ((HomotopyCategory.quotient B).obj Q))) :
    ∃ e : derivedPullbackTensor E hE ≅ Λ,
      Functor.whiskerLeft (toDerivedCategory B) e.hom ≫ β = derivedPullbackTensorCounit E hE := by
  have := isLeftDerivedFunctor_derivedPullbackTensorCounit E hE
  obtain ⟨e, he⟩ := LeftDerivedByResolutions.exists_leftDerivedIso_of_resolutions
    (quasiIsomorphisms.{t, a', m'} B) g.objectProperty g.exists_objectProperty
    (HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A')
    (HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A') (Iso.refl _)
    (isIso_pullbackTensor_map_of_objectProperty E hE)
    (toDerivedCategory B) (derivedPullbackTensor E hE) Λ (derivedPullbackTensorCounit E hE) β
    (fun X hX => hβ X.as hX)
  exact ⟨e, by simpa using he⟩

/-- Conversely, for any left derived functor of the functor of Tag 0FTE followed by the
localization functor, the structure transformation is invertible at every good right
differential graded `ℬ`-module. -/
theorem isIso_app_of_isLeftDerivedFunctor (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Λ : derivedCategory.{t, a', m'} B ⥤ derivedCategory.{t, a, s} A')
    (β : toDerivedCategory B ⋙ Λ ⟶ HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A')
    [Λ.IsLeftDerivedFunctor β (quasiIsomorphisms.{t, a', m'} B)]
    {Q : DifferentialGradedModule.{t, a', m'} B} (hQ : g.IsGood Q) :
    IsIso (β.app ((HomotopyCategory.quotient B).obj Q)) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions (quasiIsomorphisms.{t, a', m'} B)
    g.objectProperty g.exists_objectProperty _
    (isIso_pullbackTensor_map_of_objectProperty E hE)
    (toDerivedCategory B) Λ β ((HomotopyCategory.quotient B).obj Q) hQ

end Derived

end Construction

end DifferentialGradedModule

end SheafOfModules

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorCone
public import StacksFrontier.CategoryTheory.Functor.Derived.Computing

/-!
# The left derived extension of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`

Let `f` be a morphism of ringed sites, presented as a functor `u : C' ⥤ C` in the direction
opposite to `f` together with the structure map `σ : R' ⟶ f_*R` of its sheaves of rings. Let `𝒜`
and `𝒜'` be sheaves of differential graded `R`-algebras on the source, let `ℬ` be a sheaf of
differential graded `R'`-algebras on the target, let `φ : f⁻¹ℬ ⟶ 𝒜` be a homomorphism of sheaves
of differential graded algebras and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule. The
functor

`K(Mod(ℬ, d)) ⟶ K(Mod(𝒜', d))`, `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`

of Tag 0FTE, composed with the localization functor `K(Mod(𝒜', d)) → D(𝒜', d)`, has a left
derived extension `D(ℬ, d) → D(𝒜', d)` whose value on a good right differential graded
`ℬ`-module `𝒫` is `f^*𝒫 ⊗_𝒜 𝒩`. That is Tag 0FTF, and it is what
`isLeftDerivable_and_computesLeftDerived_pullbackTensor` says: the left derived functor is
everywhere defined, and every object of `K(Mod(ℬ, d))` represented by a good module computes it,
so that there the derived extension takes the value `f^*𝒫 ⊗_𝒜 𝒩` prescribed by the functor
itself.

The source's argument is run in full. The existence step is Derived Categories, Lemma 13.14.15,
Tag 06XN, which is available as
`Stacks.DerivedFunctor.Computing.leftDerived_everywhereDefined_and_computes`: for a class of
objects reachable from every object by an arrow of the localizing system, on which the functor
inverts the arrows of that system, the left derived functor is everywhere defined and every
object of the class computes it. Here the class is the good modules, reachability is Tag 0FSH,
and the verification that the functor inverts quasi-isomorphisms between good modules — the one
computation in the source's proof — is
`quasiIso_pullbackTensorFunctor_map_of_isGood`: the cone `𝒫''` of a quasi-isomorphism
`𝒫 → 𝒫'` of good modules is good by Tag 0FSC and acyclic, hence `f^*𝒫'' ⊗_𝒜 𝒩` is acyclic by
Tag 0FSI, hence `f^*𝒫 ⊗_𝒜 𝒩 → f^*𝒫' ⊗_𝒜 𝒩`, whose cone is that module, is a
quasi-isomorphism.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GoodResolutionData` carries the two clauses of the
  flat-resolution theory of right differential graded `ℬ`-modules which the source's proof uses:
  every module receives a quasi-isomorphism from a good one (Tag 0FSH) and the cone of a
  homomorphism of good modules is good (Tag 0FSC).
* `SheafOfModules.DifferentialGradedModule.PullbackTensorExactnessData` carries the two
  properties of the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` beyond its construction: it commutes with cones,
  which is the exactness of Tag 0FTE, and it carries a good acyclic module to an acyclic one,
  which is Tag 0FSI.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIso_pullbackTensorFunctor_map_of_isGood`: the
  functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` carries a quasi-isomorphism of good right differential graded
  `ℬ`-modules to a quasi-isomorphism. This is the computation of the source's proof.
* `SheafOfModules.DifferentialGradedModule.isLeftDerivable_and_computesLeftDerived_pullbackTensor`:
  Tag 0FTF through Tags 05SV and 05SX. The functor of Tag 0FTE followed by the localization
  functor `K(Mod(𝒜', d)) → D(𝒜', d)` has an everywhere defined left derived functor, and every
  object represented by a good right differential graded `ℬ`-module computes it. The tag itself
  is registered on
  `SheafOfModules.DifferentialGradedModule.isLeftDerived_derivedPullbackTensorRingedTopos`,
  along a morphism of ringed topoi.

## Implementation notes

**In what sense the derived extension is delivered.** The derived categories here are the
development's own: `SheafOfModules.DifferentialGradedModule.derivedCategory` of Tag 0FT5, the
localization of the homotopy category at the quasi-isomorphisms, with
`SheafOfModules.DifferentialGradedModule.toDerivedCategory` its localization functor. Nothing
about them is assumed. "Has a left derived extension `D(ℬ, d) → D(𝒜', d)` whose value on a good
module `𝒫` is `f^*𝒫 ⊗_𝒜 𝒩`" is therefore spelled in the source's own vocabulary for it:
`CategoryTheory.Functor.IsLeftDerivable` is Tag 05SV(2), `LF` is everywhere defined, and
`CategoryTheory.Functor.ComputesLeftDerived` is Tag 05SX(2), the object `X` computes `LF`, i.e.
the canonical map `LF(X) → F(X)` is an isomorphism. The conclusion of Tag 06XN is stated in
exactly those two notions, and the passage from an everywhere defined `LF` to a functor on the
localization is Derived Categories, Lemma 13.14.6, which is a different tag and is not used
here.

**What is carried, and why.** Three things, none of which mentions a derived functor. The
equivalence between being a quasi-isomorphism and having an acyclic cone is not among them: it
is `acyclic_cone_iff_quasiIso`. The triangulated structure its proof needs is the one on
Mathlib's homotopy category of cochain complexes of sheaves of modules, reached through the
identification of the cone's complex with a mapping cone, and not one on the homotopy category
of sheaf differential graded modules, which this development indeed does not have.

1. `GoodResolutionData.exists_isGood`, Tag 0FSH. The source invokes Lemma 24.23.7 for it.
   `SheafOfModules.DifferentialGradedModule.exists_good_quasiIso` in
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedResolutionToposTower.lean`
   supplies it: for every `M` it produces a quasi-isomorphism `Q ⟶ M` whose source satisfies
   `SheafOfModules.IsGoodToposBaseChange`, the goodness of Tag 0FSA, taking `M` as its only
   argument. The earlier `exists_flat_quasiIso` of
   `GoodDifferentialGradedResolutionTower.lean` keeps the ring and the module universe
   independent and concludes the graded-flatness and K-flatness clauses alone; the topos tower
   identifies the two universes and reaches the whole of goodness.
2. `GoodResolutionData.isGood_cone`, Tag 0FSC applied as the source applies Lemma 24.23.2: in
   the admissible short exact sequence given by a cone, two good terms force the third to be
   good. `GoodResolutionData` is the sub-package of
   `SheafOfModules.DifferentialGradedModule.GoodModuleData` which this file needs, without the
   carried derived category that this file does not need because it uses the real one.
   At conditions (1) and (2) of Tag 0FSA this clause is
   `SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_cone`, by two-out-of-three
   along the admissible short exact sequence of the cone, and
   `SheafOfModules.DifferentialGradedModule.GoodResolutionData.flat` is the resulting term of the
   structure. At the whole of Tag 0FSA — the reading Tag 0FSI below asks for, both packages
   sharing their `IsGood` — two-out-of-three no longer reaches it, condition (3) carrying an
   existential whose witness is itself a cone, and
   `SheafOfModules.DifferentialGradedModule.GoodResolutionData.ofIsGoodToposBaseChange` is this
   clause's one argument with the other two clauses discharged beside it.
   `SheafOfModules.cone_freeDGModule_isGoodToposBaseChange` is the case of it on which the tower
   of Tag 0FSH runs: a homomorphism whose source is a free differential graded module.
3. `PullbackTensorExactnessData`. Its `acyclic_pullbackTensor` is Tag 0FSI, the source's Lemma
   24.23.8, applied to the pullback-and-tensor of a good acyclic module.
   `SheafOfModules.DifferentialGradedModule.acyclic_pullbackTensor_of_isGood_of_acyclic` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodAcyclicDifferentialGradedPullbackTensor.lean`
   is that statement. The value `f^*𝒬 ⊗_𝒜 𝒩` of the functor at `𝒬` is a tensor product of `f^*𝒬`
   with `𝒩`, so clause (1) of Tag 0FSI reads off at it as soon as the pullback `f^*𝒬` is K-flat
   and acyclic, and those two are the two halves of clause (2) of the same tag: K-flatness of
   the pullback is condition (3) of goodness, through
   `SheafOfModules.DifferentialGradedModule.IsGood.baseChange`, and acyclicity of the pullback is
   `SheafOfModules.DifferentialGradedModule.acyclic_pullback_of_isGood_of_acyclic`. Condition (2)
   of goodness — K-flatness of `𝒬` itself — is not what the tensor product consumes: it is
   formed on `C`, over `𝒜`, and it is `f^*𝒬` that has to be K-flat there. Goodness in
   that form is `SheafOfModules.DifferentialGradedModule.IsGood`, whose condition (3) is
   quantified over the base changes a `PullbackData` presents. At
   `SheafOfModules.IsGoodToposBaseChange`, the goodness
   `GoodResolutionData.ofIsGoodToposBaseChange` installs, condition (3) is quantified over
   morphisms of ringed topoi, and the K-flatness it delivers is that of an object corepresenting
   `Q ↦ Hom_ℬ(𝒬, f_{*,ψ}Q)`; that reading is
   `SheafOfModules.DifferentialGradedModule.acyclic_pullbackTensor_of_isGoodToposBaseChange`.
   Next, `coneIso` is the
   exactness of the functor of Tag 0FTE. The source uses exactness through a distinguished
   triangle; what is needed and carried is only the identification of the cone of the image with
   the image of the cone, and that holds with no hypothesis at all:
   `SheafOfModules.DifferentialGradedModule.pullbackTensorConeComplexIso` composes
   `PullbackData.coneIso` with `TensorFunctorData.coneIso`, so
   `PullbackTensorExactnessData.ofAcyclicPullbackTensor` below takes Tag 0FSI as its one
   argument.

None of the three says anything about a left derived extension, about an object of `D(𝒜', d)`
attached to an object of `D(ℬ, d)`, or about the value of any functor on a good module: each is
a statement about homomorphisms of differential graded modules and about the cohomology of
complexes of sheaves of modules, and each is the conclusion of a different tag.

**The hypotheses on the quasi-isomorphisms, held throughout,** are Situation 13.14.1,
Tag 05S8: that the
localizing class is a saturated multiplicative system admitting a calculus of fractions. For the
quasi-isomorphisms of `K(Mod(ℬ, d))` that is Tag 0FT4, which this development does not prove —
`DifferentialGradedDerivedCategory.lean` records only
`quasiIsomorphisms_isMultiplicative` — so it appears as the hypotheses
`[MorphismProperty.HasRightCalculusOfFractions]` and `IsSaturatedMultiplicative`, which are
precisely what Tag 06XN consumes. Identities are in the class by
`CategoryTheory.MorphismProperty.HasRightCalculusOfFractions`, which extends
`CategoryTheory.MorphismProperty.IsMultiplicative`, so no separate hypothesis is needed for the
`ComputesLeftDerived` half.

The two sheafification hypotheses on each site are the ones that make the sheaves of modules
abelian, so that complexes of them have homology and `QuasiIso` can be written; they are the
same hypotheses under which `quasiIsomorphisms` and `derivedCategory` are defined.

The universes are those of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackTensor.lean`: the two
sites and their morphisms, the two algebra universes and the three module universes are
independent, while the two sheaves of rings share the universe `t` because the structure map of
the morphism of ringed sites relates them, and the two algebras on the source share the universe
`a` because `𝒩` is a bimodule between them.

## References

* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 06XN](https://stacks.math.columbia.edu/tag/06XN)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public section

open CategoryTheory

universe t a a' m m' s z v u v' u'

namespace SheafOfModules

namespace DifferentialGradedModule

/-! ### Good resolutions, carried as data -/

section CarriedData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The part of the flat-resolution theory of right differential graded `A`-modules which the
proof of Tag 0FTF uses: the class of good modules, the existence of a good resolution of every
module (Tag 0FSH) and the goodness of the cone of a homomorphism of good modules (Tag 0FSC).
These are three of the clauses of
`SheafOfModules.DifferentialGradedModule.GoodModuleData`, with the carried derived category and
the carried tensor product left out. -/
structure GoodResolutionData (A : DifferentialGradedAlgebra.{t, a} R) where
  /-- The good right differential graded `A`-modules: those which are flat and K-flat as graded
  modules and stay so after arbitrary base change. -/
  IsGood : DifferentialGradedModule.{t, a, m} A → Prop
  /-- Tag 0FSH: every right differential graded `A`-module receives a quasi-isomorphism from a
  good one. -/
  exists_isGood (M : DifferentialGradedModule.{t, a, m} A) :
    ∃ (P : DifferentialGradedModule.{t, a, m} A) (p : P ⟶ M),
      IsGood P ∧ QuasiIso p.toHomologicalComplex
  /-- Tag 0FSC: the cone of a homomorphism of good modules is good, two good terms of the
  admissible short exact sequence given by a cone forcing the third to be good. -/
  isGood_cone {P P' : DifferentialGradedModule.{t, a, m} A} (ψ : P ⟶ P') (hP : IsGood P)
      (hP' : IsGood P') : IsGood (cone ψ)

end CarriedData

/-! ### The left derived extension of pullback followed by tensor product -/

section LeftDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J' AddCommGrpCat.{m'}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m'}]
  {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}

/-- The two properties of the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE beyond its construction
which the proof of Tag 0FTF uses: it commutes with cones, which is its exactness, and it carries
a good acyclic right differential graded `ℬ`-module to an acyclic one, which is Tag 0FSI.
Neither mentions the homotopy categories or the derived categories. -/
structure PullbackTensorExactnessData (P : PullbackData.{t, a, m, v, u, a', m'} φ)
    (D : TensorFunctorData.{t, a, m, z, s} A A' N)
    (g : GoodResolutionData.{t, a', m', v', u'} B) where
  /-- The functor commutes with cones: the image of the cone of `ψ` is the cone of the image of
  `ψ`, as complexes of sheaves of modules. This is the exactness of Tag 0FTE, which the source
  uses through the distinguished triangle of a cone. -/
  coneIso {M M₂ : DifferentialGradedModule.{t, a', m'} B} (ψ : M ⟶ M₂) :
    ((pullbackTensorFunctor P D).obj (cone ψ)).complex ≅
      (cone ((pullbackTensorFunctor P D).map ψ)).complex
  /-- Tag 0FSI: `f^*𝒬 ⊗_𝒜 𝒩` is acyclic for a good acyclic right differential graded
  `ℬ`-module `𝒬`. -/
  acyclic_pullbackTensor {Q : DifferentialGradedModule.{t, a', m'} B} (hQ : g.IsGood Q)
      (hQac : Q.complex.Acyclic) : ((pullbackTensorFunctor P D).obj Q).complex.Acyclic

/-- **The exactness data of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` with its cone clause discharged.** The `coneIso`
clause holds at an arbitrary pullback and an arbitrary tensor product functor, by
`SheafOfModules.DifferentialGradedModule.pullbackTensorConeComplexIso`: the pullback commutes
with cones (`PullbackData.coneIso`) and so does the tensor product
(`TensorFunctorData.coneIso`). So the only argument this package still takes is Tag 0FSI, the
acyclicity of `f^*𝒬 ⊗_𝒜 𝒩` for a good acyclic `𝒬`. -/
noncomputable def PullbackTensorExactnessData.ofAcyclicPullbackTensor
    (P : PullbackData.{t, a, m, v, u, a', m'} φ)
    (D : TensorFunctorData.{t, a, m, z, s} A A' N)
    (g : GoodResolutionData.{t, a', m', v', u'} B)
    (hac : ∀ {Q : DifferentialGradedModule.{t, a', m'} B}, g.IsGood Q → Q.complex.Acyclic →
      ((pullbackTensorFunctor P D).obj Q).complex.Acyclic) :
    PullbackTensorExactnessData P D g where
  coneIso ψ := pullbackTensorConeComplexIso P D ψ
  acyclic_pullbackTensor hQ hQac := hac hQ hQac

/-- The computation in the proof of Tag 0FTF: the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` carries a
quasi-isomorphism `ψ : 𝒫 → 𝒫'` of *good* right differential graded `ℬ`-modules to a
quasi-isomorphism. The cone `𝒫''` of `ψ` is good because `𝒫` and `𝒫'` are, and acyclic because
`ψ` is a quasi-isomorphism; so `f^*𝒫'' ⊗_𝒜 𝒩` is acyclic; and that module is the cone of
`f^*𝒫 ⊗_𝒜 𝒩 → f^*𝒫' ⊗_𝒜 𝒩`, which is therefore a quasi-isomorphism. -/
theorem quasiIso_pullbackTensorFunctor_map_of_isGood
    {P : PullbackData.{t, a, m, v, u, a', m'} φ}
    {D : TensorFunctorData.{t, a, m, z, s} A A' N}
    {g : GoodResolutionData.{t, a', m', v', u'} B}
    (hE : PullbackTensorExactnessData P D g)
    {M M₂ : DifferentialGradedModule.{t, a', m'} B} (ψ : M ⟶ M₂) (hM : g.IsGood M)
    (hM₂ : g.IsGood M₂) (hψ : QuasiIso ψ.toHomologicalComplex) :
    QuasiIso ((pullbackTensorFunctor P D).map ψ).toHomologicalComplex :=
  (acyclic_cone_iff_quasiIso A' _).1 fun n =>
    (hE.acyclic_pullbackTensor (g.isGood_cone ψ hM hM₂)
      ((acyclic_cone_iff_quasiIso B ψ).2 hψ) n).of_iso (hE.coneIso ψ)

/-- **Stacks 0FTF.** The functor `K(Mod(ℬ, d)) ⟶ K(Mod(𝒜', d))`, `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE,
composed with the localization functor `K(Mod(𝒜', d)) → D(𝒜', d)`, has a left derived extension
`D(ℬ, d) → D(𝒜', d)` whose value on a good right differential graded `ℬ`-module `𝒫` is
`f^*𝒫 ⊗_𝒜 𝒩`: the left derived functor is everywhere defined, and the object of
`K(Mod(ℬ, d))` represented by a good module computes it, so that there the derived extension
agrees with the functor itself.

Both halves come from Tag 06XN applied to the class of objects represented by good modules.
That class is reachable from every object by a quasi-isomorphism, which is Tag 0FSH, and the
functor inverts the quasi-isomorphisms between its members by
`quasiIso_pullbackTensorFunctor_map_of_isGood`.

This is Tag 0FTF read through Tags 05SV and 05SX, the source's own vocabulary for a derived
functor, which hands back no functor of the derived categories.
`SheafOfModules.DifferentialGradedModule.exists_leftDerivedExtension_pullbackTensor` produces
that functor, needs no saturation of the quasi-isomorphisms, and gives the value on a good module
as an equality of objects. -/
theorem isLeftDerivable_and_computesLeftDerived_pullbackTensor
    {P : PullbackData.{t, a, m, v, u, a', m'} φ} (E : P.HomotopyExtension)
    {D : TensorFunctorData.{t, a, m, z, s} A A' N}
    {g : GoodResolutionData.{t, a', m', v', u'} B}
    (hE : PullbackTensorExactnessData P D g)
    [(quasiIsomorphisms.{t, a', m'} B).HasRightCalculusOfFractions]
    (hSat : (quasiIsomorphisms.{t, a', m'} B).IsSaturatedMultiplicative) :
    (HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A').IsLeftDerivable
        (quasiIsomorphisms.{t, a', m'} B) ∧
      ∀ Q : DifferentialGradedModule.{t, a', m'} B, g.IsGood Q →
        (HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A').ComputesLeftDerived
          (quasiIsomorphisms.{t, a', m'} B) ((HomotopyCategory.quotient B).obj Q) := by
  have h1 : ∀ X : HomotopyCategory.{t, a', m'} B,
      ∃ (X' : HomotopyCategory.{t, a', m'} B) (ss : X' ⟶ X),
        quasiIsomorphisms.{t, a', m'} B ss ∧
          X' ∈ {Y : HomotopyCategory.{t, a', m'} B | g.IsGood Y.as} := by
    intro X
    obtain ⟨Q, p, hQ, hp⟩ := g.exists_isGood X.as
    exact ⟨(HomotopyCategory.quotient B).obj Q, (HomotopyCategory.quotient B).map p,
      (quasiIsomorphisms_quotient_map_iff p).2 hp, hQ⟩
  have h2 : ∀ ⦃X X' : HomotopyCategory.{t, a', m'} B⦄ (ss : X ⟶ X'),
      quasiIsomorphisms.{t, a', m'} B ss →
        X ∈ {Y : HomotopyCategory.{t, a', m'} B | g.IsGood Y.as} →
          X' ∈ {Y : HomotopyCategory.{t, a', m'} B | g.IsGood Y.as} →
            IsIso ((HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A').map ss) := by
    intro X X' ss hss hX hX'
    obtain ⟨ψ, hψ⟩ : ∃ ψ : X.as ⟶ X'.as, (HomotopyCategory.quotient B).map ψ = ss :=
      ⟨(HomotopyCategory.quotient B).preimage ss,
        (HomotopyCategory.quotient B).map_preimage ss⟩
    subst hψ
    exact (quasiIsomorphisms.{t, a, s} A').Q_inverts _
      ((quasiIsomorphisms_quotient_map_iff _).2
        (quasiIso_pullbackTensorFunctor_map_of_isGood hE ψ hX hX' (hss ψ rfl)))
  have main := Stacks.DerivedFunctor.Computing.leftDerived_everywhereDefined_and_computes
    (HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A')
    (quasiIsomorphisms.{t, a', m'} B) hSat
    {Y : HomotopyCategory.{t, a', m'} B | g.IsGood Y.as} h1 h2
  exact ⟨main.1, fun Q hQ => main.2 _ hQ⟩

end LeftDerived

end DifferentialGradedModule

end SheafOfModules

end

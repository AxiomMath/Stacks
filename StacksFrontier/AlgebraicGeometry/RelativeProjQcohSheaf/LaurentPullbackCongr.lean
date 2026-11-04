module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleChartGlue
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleSmall

/-!
# The chart comparison of a Laurent algebra, in every integral degree

Let `g : T' ⟶ T` be a morphism of schemes, `L` an invertible `𝒪_T`-module and `L'` an invertible
`𝒪_{T'}`-module identified with `g^*L` by an isomorphism `e`. This file assembles the resulting
comparison

`g^*(L^{⊗ i}) ≅ (L')^{⊗ i}`

**in every integral degree `i`**, with its **multiplicativity** in every integral bidegree and
its **unit normalisation** in degree zero, and transports the map `ψ` of a quadruple and the
quadruple itself along it.

## Why this shape

A glueing argument for the functor `F_d` of Section 01NS holds a glueing datum of sheaves of
modules on `T` whose chart modules are the invertible modules of the given quadruples, and has
to produce the map `ψ` of a quadruple over `T` out of the maps given on the members of the
covering. The maps given there land in `(laurent (P a).L).piece i`; the glueing tool
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` wants morphisms into
the restriction of `(laurent G.glued).piece i`. The comparison between the two is exactly the
composite assembled here, with `L = G.glued`, `L' = (P a).L` and `e` the comparison the glueing
datum provides.

## Both halves of the composite were already in the tree, and so is one of its two spellings

The degreewise comparison of the integral tensor powers with the inverse image is
`...RelativeProjQcohSheaf.laurentPullback`, with multiplicativity
`...RelativeProjQcohSheaf.laurentPullback_mul` and degree-zero value
`...RelativeProjQcohSheaf.laurentPullback_zero`; the functoriality of the Laurent algebra in its
invertible module is `...RelativeProjQcohSheaf.LaurentCongr.congrIso`, with multiplicativity
`...LaurentAlgebraCongr.congrIso_mulSheaf` and degree-zero value `...LaurentCongr.congrIso_zero`
— the degreewise components of `...LaurentAlgebraCongr.laurentCongrIso`. Only the composite was
missing, and only at *this* spelling of the tensor-power comparison.

`...RelativeProjQcohSheaf.restrictLaurentPieceIso` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RestrictPullbackBridge` is the same
composite built from the **other** of the two parallel comparisons of the integral tensor powers
that this directory carries, `...RelativeProjQcohSheaf.LaurentPullback.pieceIso`. The duplication
is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentPullback.lean`, and it matters here:
the locality statements the glueing consumes —
`...RelativeProjQcohSheaf.mul_of_pullbackFamily_mul_cover` and
`...one_of_pullback_map_cover` — are written against
`...RelativeProjQcohSheaf.pullbackFamily`, which is built from `laurentPullback`, and no
identification of `pieceIso` with `laurentPullback` is stated anywhere. So the composite is
assembled here a second time, at the spelling those statements speak, and
`restrictLaurentPullbackCongrIso` is the restriction-vocabulary twin of
`restrictLaurentPieceIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullbackCongrIso`: **the chart
  comparison `g^*(L^{⊗ i}) ≅ (L')^{⊗ i}` in every integral degree** — the comparison of the
  integral tensor powers of Tag 01CU followed by the functoriality of the Laurent algebra in its
  invertible module.
* `...RelativeProjQcohSheaf.restrictLaurentPullbackCongrIso`: the same comparison with the
  inverse image along an open immersion replaced by
  `AlgebraicGeometry.Scheme.Modules.restrict`, which is the vocabulary the glueing tools are
  stated in.
* `...RelativeProjQcohSheaf.Twisting.pullbackCongr` and
  `...RelativeProjQcohSheaf.Quadruple.pullbackCongr`: **the map `ψ` of a quadruple, and the
  quadruple, pulled back along `g` and read through `e`.**
* `...RelativeProjQcohSheaf.Twisting.congrModuleInv`: the map `ψ` transported **backwards** along
  the comparison, which is the direction a glueing argument meets; it is not
  `...Twisting.congrModule` at `e.symm`, because the comparison attached to `e.symm` is a second
  recursion and is nowhere identified with the inverse of the one attached to `e`.
* `...RelativeProjQcohSheaf.chartLocalApp`: **the local datum the glueing of `ψ` consumes** — a
  family of homogeneous components over `a ≫ f` read as a morphism of the restrictions along `a`,
  which is the shape
  `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` takes in each
  degree.

## Main results

* `...RelativeProjQcohSheaf.laurentPullbackCongrIso_mul`: **the chart comparison is
  multiplicative in every integral bidegree**, in the
  `SheafOfModules.GradedAlgebra.mulSheaf` vocabulary that `...Twisting.app_mul` is stated in.
* `...RelativeProjQcohSheaf.laurentPullbackCongrIso_zero`: **its unit normalisation** — in degree
  zero it is the structure-sheaf comparison of Tag 01CD, both Laurent algebras having the
  identity of the structure sheaf as their unit.
* `...RelativeProjQcohSheaf.Twisting.pullbackCongr_app`: the components of the transported map
  are the pullback of the components composed with the chart comparison, so the transport is the
  composite and nothing else.
* `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_pullbackCongr`: the transported
  quadruple is strictly equivalent to the pullback, so it has the same class in `F_d(T')`.
* `...RelativeProjQcohSheaf.pullbackFamily_congrIso_of_restrictFunctor_map_eq` and
  `...pullbackFamily_eq_of_restrictFunctor_map_eq`: **a family whose restrictions along an open
  immersion are the local datum has that local family as its degreewise pullback**, read through
  the chart comparison. This is what makes a glued `ψ` meet the locality statements of
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TwistingLocal`, which are stated about
  `...RelativeProjQcohSheaf.pullbackFamily` while the glueing tool returns a morphism whose
  *restrictions* are known.
* `...RelativeProjQcohSheaf.chartLocalApp_eq_ofPullback`: **the local datum is
  `Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` of a morphism of inverse images**, which is
  what lets the compatibility hypothesis of the glueing tool be reduced, by
  `...ModuleHomGlue.localApp_ofPullback_eq_of_refinement`, to an equation of morphisms of sheaves
  of modules over a common refinement rather than of maps on sections.
* `...RelativeProjQcohSheaf.mul_of_chartLocal_cover`: **the multiplicativity
  `...Twisting.app_mul` of a glued family, from the maps given on the members of the covering**,
  in every integral bidegree.
* `...RelativeProjQcohSheaf.one_of_chartLocal_cover`: **the unit law `...Twisting.app_one` of a
  glued family, from the maps given on the members of the covering.**
* `...RelativeProjQcohSheaf.epi_of_chartLocal_cover`: **the surjectivity of a homogeneous
  component of a glued family, from the maps given on the members of the covering** — the
  condition `...Quadruple.epi_app_one` demands, at degree one.
* `...RelativeProjQcohSheaf.tensorMulTransport`: pushing a multiplication square through a pair
  of comparisons, in a bare monoidal category. Both multiplicativity proofs of this file are this
  one statement applied by `exact`.

## Implementation notes

The multiplicativity is proved by `exact` against `tensorMulTransport`, an abstract monoidal
helper with every object and morphism free. That is forced: the two sides mix
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`, through which the pieces of the
Laurent algebra are spelled, with `Stacks.RingedSpace.structureRingSheaf`, through which the
inverse image is; the two are equal by `rfl` and are not syntactically equal, so a goal
containing both is not type-correct at `implicit` transparency and `rw` — including the `rw`
inside `slice_lhs` — refuses it, reporting a missing pattern rather than the cause. For example, the
same proof written with `slice_lhs 1 3 => rw [laurentPullback_mul …]` fails with
`Application type mismatch: SheafedSpace.sheaf T'.toRingedSpace`. Every argument of the helper is
supplied explicitly; left to unification, the `exact` exhausts its heartbeats.

## What is still missing from step (1) of Tag 01NV

One thing, and it is not the comparison or its laws.

* **The compatibility hypothesis of
  `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`.** That tool asks
  for an equation over an open of `T` seen by two members of the covering; what the glueing
  problem supplies is the strict equivalence of the two quadruples over the intersection. It is
  no longer the *sections-versus-morphisms* step that is owed: the hypothesis for an arbitrary
  pair of members is reduced to an equation of morphisms of inverse images over a common
  refinement by `...ModuleHomGlue.localApp_ofPullback_eq_of_refinement`, with
  `chartLocalApp_eq_ofPullback` below putting the local datum in the shape that consumes, and the
  comparisons of the glued invertible module with the local ones are related by
  `...Quadruple.chartWitness` as an equation of morphisms by
  `...RelativeProjQcohSheaf.quadrupleGlueData_restrictFunctor_map_chartAdjunct`. What is owed is
  the assembly of those with `...Quadruple.strictlyEquivalentOver_of_common` at the refinement.
  **It is no longer the composition law for the chart comparison** — how
  `laurentPullbackCongrIso` along `k ≫ a` relates to the inverse image along `k` of the one along
  `a`. That law is `...RelativeProjQcohSheaf.laurentPullbackCongrIso_comp` of
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongrNaturality`, with
  `...laurentPullbackCongrIso_pullback` its form at a refinement of a single chart. Its two halves
  are the composition law of the comparison of the integral tensor powers,
  `...RelativeProjQcohSheaf.laurentPullback_comp` of
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor`, and the two laws of
  `...LaurentCongr.congrIso` that used to be absent: its naturality in the base scheme
  `...LaurentCongr.congrIso_laurentPullback`, which relates the inverse image along `k` of
  `congrIso e n` to `congrIso` of the inverse image of `e`, and its functoriality in the
  invertible module `...LaurentCongr.congrIso_trans`, which the composition law needs as well and
  which no note on this tag had named.

  What is owed is the two vocabulary crossings between the glueing datum and the inverse-image
  spelling the comparison is stated in: the identification `a^*G.glued ≅ (P a).L` that
  `chartLocalApp` consumes has to be read off `Stacks.SheafOfModules.ModulesGlueData.chartIso`,
  which is stated for `AlgebraicGeometry.Scheme.Modules.restrict` along `a` rather than for the
  inverse image, and the relation between two such identifications over a common refinement has to
  be read off `...RelativeProjQcohSheaf.quadrupleGlueData_restrictFunctor_map_chartAdjunct`, which
  is an equation of morphisms of restrictions over an open of `T` and not of inverse images along
  the two morphisms out of the refinement. Until those are made, the family
  `...RelativeProjQcohSheaf.chartLocalApp` cannot be fed to the tool and no glued `app` exists to
  apply the results below to.

All **three conditions on the glued family** are now below: the multiplicativity is
`mul_of_chartLocal_cover`, the unit law is `one_of_chartLocal_cover`, and the surjectivity of the
degree-one component is `epi_of_chartLocal_cover`. The unit law used to be owed because
`...RelativeProjQcohSheaf.one_of_pullback_map_cover` asks for the inverse image of the equation
rather than for the law of `...RelativeProjQcohSheaf.pullbackFamily`, with no
`pullbackFamily`-shaped unit statement to match
`...RelativeProjQcohSheaf.pullbackFamily_mul_iff`; that statement is now
`...RelativeProjQcohSheaf.pullbackFamily_one_iff`, with
`...one_of_pullbackFamily_one_cover` its locality form, in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TwistingLocal`.

## No tag is claimed

Nothing here states a clause of a tag: the file composes two comparisons this directory already
carries and transports a quadruple along the result.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T' T S : Scheme.{u}}

/-! ### The chart comparison in every integral degree -/

section Comparison

variable (g : T' ⟶ T) (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {L' : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf (isSheafStruct T') L']
  (e : (pullbackFunctor (ringedSpaceHom g)).obj L ≅ L')

/-- **The chart comparison `g^*(L^{⊗ i}) ≅ (L')^{⊗ i}` of the integral tensor powers**, for an
invertible module `L'` on the source identified with `g^*L` by `e`.

It is the comparison of the integral tensor powers of Tag 01CU
(`...RelativeProjQcohSheaf.laurentPullback`) followed by the functoriality of the Laurent algebra
in its invertible module (`...LaurentCongr.congrIso`, the degreewise component of
`...LaurentAlgebraCongr.laurentCongrIso`). -/
def laurentPullbackCongrIso (i : ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).obj ((laurent L).piece i) ≅ (laurent L').piece i :=
  asIso (laurentPullback g L i) ≪≫ congrIso e i

/-- The chart comparison is the comparison of the integral tensor powers followed by the
functoriality of the Laurent algebra, by definition. -/
theorem laurentPullbackCongrIso_hom (i : ℤ) :
    (laurentPullbackCongrIso g L e i).hom = laurentPullback g L i ≫ (congrIso e i).hom :=
  rfl

/-- **Pushing a multiplication square through a pair of comparisons**, stated in a bare monoidal
category so that the proof never has to look at the two interchangeable spellings of the
structure sheaf: if `c` carries `m` to `m'` through `v₁ ⊗ₘ v₂`, then composing `u₁ ⊗ₘ u₂` with
`v₁ ⊗ₘ v₂` and then `m'` is composing with `m` and then `c`.

Every object and morphism is free, and the statement is applied by `exact`. That is the cure this
directory prescribes for the two `rfl`-equal, syntactically distinct spellings
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` and
`Stacks.RingedSpace.structureRingSheaf` of the structure sheaf: a goal containing both is not
type-correct at `implicit` transparency and no `rw` applies to it. -/
theorem tensorMulTransport {C : Type*} [Category C] [MonoidalCategory C]
    {P₁ P₂ Q₁ Q₂ R₁ R₂ M N : C}
    (u₁ : P₁ ⟶ Q₁) (u₂ : P₂ ⟶ Q₂) (v₁ : Q₁ ⟶ R₁) (v₂ : Q₂ ⟶ R₂)
    (m : MonoidalCategoryStruct.tensorObj Q₁ Q₂ ⟶ M)
    (m' : MonoidalCategoryStruct.tensorObj R₁ R₂ ⟶ N) (c : M ⟶ N)
    (t : MonoidalCategoryStruct.tensorObj P₁ P₂ ⟶ M)
    (hc : m ≫ c = (v₁ ⊗ₘ v₂) ≫ m') (hmul : (u₁ ⊗ₘ u₂) ≫ m = t) :
    ((u₁ ≫ v₁) ⊗ₘ (u₂ ≫ v₂)) ≫ m' = t ≫ c := by
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, ← hc, ← hmul]
  simp only [Category.assoc]

/-- **The chart comparison is multiplicative in every integral bidegree**: it carries the
multiplication of the Laurent algebra of `L`, pulled back along `g`, to the multiplication of
the Laurent algebra of `L'`, through the comparison `g^*(X ⊗ Y) ≅ g^*X ⊗ g^*Y` of Tag 01CD.

This is the condition `...RelativeProjQcohSheaf.Twisting.app_mul` is stated against, and it is
the multiplicativity of the two halves composed: `...RelativeProjQcohSheaf.laurentPullback_mul`
for the comparison of the integral tensor powers and
`...LaurentAlgebraCongr.congrIso_mulSheaf` for the functoriality, the two being put in one
vocabulary by `...RelativeProjQcohSheaf.laurent_mulSheaf_eq`. -/
theorem laurentPullbackCongrIso_mul (i j : ℤ) :
    pullbackTensorComparison (ringedSpaceHom g) ((laurent L).piece i) ((laurent L).piece j) ≫
        ((laurentPullbackCongrIso g L e i).hom ⊗ₘ (laurentPullbackCongrIso g L e j).hom) ≫
          SheafOfModules.GradedAlgebra.mulSheaf (laurent L') i j =
      (pullbackFunctor (ringedSpaceHom g)).map
          (SheafOfModules.GradedAlgebra.mulSheaf (laurent L) i j) ≫
        (laurentPullbackCongrIso g L e (i + j)).hom := by
  have hmul := laurentPullback_mul g L i j
  have hc := LaurentAlgebraCongr.congrIso_mulSheaf e i j
  rw [laurent_mulSheaf_eq, laurent_mulSheaf_eq] at hc
  rw [laurent_mulSheaf_eq L' i j, laurent_mulSheaf_eq L i j]
  simp only [laurentPullbackCongrIso_hom]
  refine Eq.trans (congrArg (fun z => pullbackTensorComparison (ringedSpaceHom g)
    ((laurent L).piece i) ((laurent L).piece j) ≫ z) (tensorMulTransport
      (laurentPullback g L i) (laurentPullback g L j)
      (congrIso e i).hom (congrIso e j).hom
      (laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j) (laurentMul L' i j)
      (congrIso e (i + j)).hom
      ((laurentPullback g L i ⊗ₘ laurentPullback g L j) ≫
        laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j) hc rfl)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact Eq.trans (congrArg (fun z => z ≫ (congrIso e (i + j)).hom) hmul) (Category.assoc _ _ _)

/-- **The unit normalisation of the chart comparison**: in degree zero it is the structure-sheaf
comparison of Tag 01CD.

The degree-zero piece of a Laurent algebra is the structure sheaf on the nose, the comparison of
the integral tensor powers is the structure-sheaf comparison there
(`...RelativeProjQcohSheaf.laurentPullback_zero`) and the functoriality in the invertible module
is the identity there (`...LaurentCongr.congrIso_zero`). Together with
`...RelativeProjQcohSheaf.oneHom_laurent`, which says the unit of a Laurent algebra is the
identity of the structure sheaf, this is the condition
`...RelativeProjQcohSheaf.Twisting.app_one` is stated against. -/
theorem laurentPullbackCongrIso_zero :
    (laurentPullbackCongrIso g L e 0).hom = pullbackUnitComparison (ringedSpaceHom g) := by
  rw [laurentPullbackCongrIso_hom, congrIso_zero]
  exact (Category.comp_id _).trans (laurentPullback_zero g L)

end Comparison

/-- **The chart comparison in the restriction vocabulary the glueing tools are stated in**: the
restriction along an open immersion `a` of the degree-`i` piece of the Laurent algebra of `L` is
the degree-`i` piece of the Laurent algebra of any invertible module `L'` identified with
`a^*L`.

This is `...RelativeProjQcohSheaf.restrictLaurentPieceIso` with the comparison of the integral
tensor powers taken at the spelling
`...RelativeProjQcohSheaf.laurentPullback` — the one the locality statements
`...RelativeProjQcohSheaf.mul_of_pullbackFamily_mul_cover` and `...one_of_pullback_map_cover`
speak, through `...RelativeProjQcohSheaf.pullbackFamily`. The two spellings are two parallel
developments of one comparison and are not identified anywhere, which is why both composites
exist. -/
def restrictLaurentPullbackCongrIso {V : Scheme.{u}} (a : V ⟶ T) [IsOpenImmersion a]
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {L' : SheafOfModules.{u} (structureRingSheaf V.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible V.toRingedSpace.presheaf (isSheafStruct V) L']
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L') (i : ℤ) :
    Scheme.Modules.restrict ((laurent L).piece i) a ≅ (laurent L').piece i :=
  (Scheme.Modules.restrictFunctorIsoPullback a).app _ ≪≫ laurentPullbackCongrIso a L e i

/-! ### Transporting the map `ψ` and the quadruple -/

namespace Twisting

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {L' : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf (isSheafStruct T') L']

/-- **The map `ψ` of a quadruple, pulled back along `g : T' ⟶ T` and read on an invertible
module `L'` identified with `g^*L`**: the map of a quadruple over `g ≫ f` with invertible module
`L'`, whose components are the components of `ψ` carried across by the chart comparison.

It is `...RelativeProjQcohSheaf.Twisting.pullback` followed by
`...RelativeProjQcohSheaf.Twisting.congrModule`, so the multiplicativity and the unit
normalisation are those of the chart comparison
(`...RelativeProjQcohSheaf.laurentPullbackCongrIso_mul` and `...laurentPullbackCongrIso_zero`)
and nothing further is checked. -/
def pullbackCongr (ψ : Twisting f A d L) (g : T' ⟶ T)
    (e : (pullbackFunctor (ringedSpaceHom g)).obj L ≅ L') : Twisting (g ≫ f) A d L' :=
  (ψ.pullback g).congrModule e

/-- **The components of the transported map are the components of `ψ` carried across by the chart
comparison**: the contraction of the iterated inverse image, the inverse image of the component,
and then `...RelativeProjQcohSheaf.laurentPullbackCongrIso`. So
`...RelativeProjQcohSheaf.Twisting.pullbackCongr` is the composite and nothing else. -/
theorem pullbackCongr_app (ψ : Twisting f A d L) (g : T' ⟶ T)
    (e : (pullbackFunctor (ringedSpaceHom g)).obj L ≅ L') (i : ℤ) :
    (ψ.pullbackCongr g e).app i =
      compComparison g f (A.piece (i * d)) ≫
        (pullbackFunctor (ringedSpaceHom g)).map (ψ.app i) ≫
          (laurentPullbackCongrIso g L e i).hom := by
  simp only [pullbackCongr, Twisting.congrModule_app, Twisting.pullback_app,
    Twisting.pullbackApp, laurentPullbackCongrIso_hom, Category.assoc]

end Twisting

namespace Quadruple

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L' : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf (isSheafStruct T') L']

/-- **A quadruple pulled back along `g : T' ⟶ T` and read on an invertible module `L'`
identified with `g^*L`**: the quadruple over `g ≫ f` with invertible module `L'` and map
`...RelativeProjQcohSheaf.Twisting.pullbackCongr`.

It is `...RelativeProjQcohSheaf.Quadruple.pullback` followed by
`...RelativeProjQcohSheaf.Quadruple.congrModule`; the surjectivity of the degree-one component
survives because the chart comparison is an isomorphism. -/
def pullbackCongr (P : Quadruple f A d) (g : T' ⟶ T)
    (e : (pullbackFunctor (ringedSpaceHom g)).obj P.L ≅ L') : Quadruple (g ≫ f) A d :=
  (P.pullback g).congrModule e

/-- The invertible module of the transported pullback is the given one. -/
@[simp] theorem pullbackCongr_L (P : Quadruple f A d) (g : T' ⟶ T)
    (e : (pullbackFunctor (ringedSpaceHom g)).obj P.L ≅ L') :
    (P.pullbackCongr g e).L = L' :=
  rfl

/-- The map of the transported pullback is
`...RelativeProjQcohSheaf.Twisting.pullbackCongr`. -/
theorem pullbackCongr_twisting (P : Quadruple f A d) (g : T' ⟶ T)
    (e : (pullbackFunctor (ringedSpaceHom g)).obj P.L ≅ L') :
    (P.pullbackCongr g e).twisting = P.twisting.pullbackCongr g e :=
  rfl

/-- **The transported pullback is strictly equivalent to the pullback**, so the two have the same
class in `F_d(T')` and reading a quadruple on an invertible module identified with `g^*L` loses
nothing. The witness is `...LaurentAlgebraCongr.laurentCongrIso` of `e`. -/
theorem strictlyEquivalent_pullbackCongr (P : Quadruple f A d) (g : T' ⟶ T)
    (e : (pullbackFunctor (ringedSpaceHom g)).obj P.L ≅ L') :
    Quadruple.StrictlyEquivalent (P.pullback g) (P.pullbackCongr g e) :=
  (P.pullback g).strictlyEquivalent_congrModule e

end Quadruple


/-! ### Transporting a map backwards along the comparison -/

namespace Twisting

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {M M' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M']

/-- **The map `ψ` of a quadruple, transported backwards along an isomorphism `e : M ≅ M'` of
invertible modules**: its degree-`i` component is the component of `ψ` followed by the *inverse*
of the comparison `M^{⊗ i} ≅ (M')^{⊗ i}` of the `i`-th integral tensor powers.

This is `...RelativeProjQcohSheaf.Twisting.congrModule` read in the other direction, and it is
not that construction applied to `e.symm`: the comparison attached to `e.symm` is a second
recursion on the degree and is nowhere identified with the inverse of the comparison attached to
`e` — the implementation notes of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentAlgebraCongr.lean` record that the
identification is a further induction nothing needed. What is needed instead, and is available,
is the multiplicativity of the componentwise inverse,
`...LaurentAlgebraCongr.congrIso_inv_mulSheaf`.

This is the direction a glueing argument meets: the degreewise pullback of the glued family is
the local map followed by the *inverse* of the chart comparison
(`...RelativeProjQcohSheaf.pullbackFamily_eq_of_restrictFunctor_map_eq`), so the two laws of the
glued family over a member of the covering are the two laws of this transport. -/
def congrModuleInv (ψ : Twisting f A d M') (e : M ≅ M') : Twisting f A d M where
  app i := ψ.app i ≫ (congrIso e i).inv
  app_mul i j :=
    (tensorMulTransport (ψ.app i) (ψ.app j) (congrIso e i).inv (congrIso e j).inv
      (SheafOfModules.GradedAlgebra.mulSheaf (laurent M') i j)
      (SheafOfModules.GradedAlgebra.mulSheaf (laurent M) i j) (congrIso e (i + j)).inv
      (inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (A.mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫ ψ.app (i + j))
      (LaurentAlgebraCongr.congrIso_inv_mulSheaf e i j) (ψ.app_mul i j)).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun z => inv (pullbackTensorComparison (ringedSpaceHom f)
          (A.piece (i * d)) (A.piece (j * d))) ≫ z) (Category.assoc _ _ _)))
  app_one := by
    refine Eq.trans ?_ (ψ.app_one.trans ((oneHom_laurent M').trans (oneHom_laurent M).symm))
    rw [congrIso_zero]
    exact congrArg (fun z => Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
      (pullbackFunctor (ringedSpaceHom f)).map
        (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ z)
      (Category.comp_id (ψ.app 0))

/-- The components of the backwards transport are the components of `ψ` followed by the inverse
of the comparison of the integral tensor powers. -/
@[simp] theorem congrModuleInv_app (ψ : Twisting f A d M') (e : M ≅ M') (i : ℤ) :
    (ψ.congrModuleInv e).app i = ψ.app i ≫ (congrIso e i).inv :=
  rfl

end Twisting

/-! ### The local datum the glueing of `ψ` consumes, and what its pullback is -/

section Local

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {V : Scheme.{u}} {L' : SheafOfModules.{u} (structureRingSheaf V.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible V.toRingedSpace.presheaf (isSheafStruct V) L']

/-- **The local datum of the glueing of `ψ`**: a family of homogeneous components over `a ≫ f`
with values in the Laurent algebra of `L'`, read as a morphism of the restrictions along `a` of
the source and the target of a family over `f` with values in the Laurent algebra of `L`.

The source is transported by `...RelativeProjQcohSheaf.restrictPullbackFunctorCompIso` and the
target by `...RelativeProjQcohSheaf.restrictLaurentPullbackCongrIso`. This is exactly the shape
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` consumes in each
degree. -/
def chartLocalApp (f : T ⟶ S) (a : V ⟶ T) [IsOpenImmersion a]
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L')
    (q : ∀ i : ℤ, (pullbackFunctor (ringedSpaceHom (a ≫ f))).obj (A.piece (i * d)) ⟶
      (laurent L').piece i) (i : ℤ) :
    Scheme.Modules.restrict ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))) a ⟶
      Scheme.Modules.restrict ((laurent L).piece i) a :=
  (restrictPullbackFunctorCompIso f a (A.piece (i * d))).hom ≫ q i ≫
    (restrictLaurentPullbackCongrIso a L e i).inv

/-- Reassociating a five-fold composite, stated in a bare category with every object and
morphism free. `...RelativeProjQcohSheaf.chartLocalApp` and
`Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` of the corresponding morphism of inverse
images are this one reassociation apart, and the goal that says so mentions both of the two
`rfl`-equal, syntactically distinct spellings of the structure sheaf, so it is not type-correct
at `implicit` transparency and even `simp only [Category.assoc]` leaves it untouched. -/
private theorem reassocFivefold {C : Type*} [Category C] {M₁ M₂ M₃ N₁ N₂ N₃ : C}
    (h₁ : M₁ ⟶ M₂) (h₂ : M₂ ⟶ M₃) (q : M₃ ⟶ N₁) (v : N₁ ⟶ N₂) (w : N₂ ⟶ N₃) :
    (h₁ ≫ h₂) ≫ q ≫ v ≫ w = h₁ ≫ (h₂ ≫ q ≫ v) ≫ w := by
  simp only [Category.assoc]

/-- **The local datum of the glueing of `ψ` is the local datum of a morphism of inverse
images.** `...RelativeProjQcohSheaf.chartLocalApp` is
`Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` of the family `q` read with the contraction
of the iterated inverse image on the source and the chart comparison on the target, and nothing
else: both of its two restriction comparisons are the component of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` that `ofPullback` conjugates by.

This is what makes the compatibility hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` reachable through
`...ModuleHomGlue.localApp_ofPullback_eq_of_refinement`, whose hypothesis is an equation of
morphisms of sheaves of modules over a common refinement rather than of maps on sections. -/
theorem chartLocalApp_eq_ofPullback (f : T ⟶ S) (a : V ⟶ T) [IsOpenImmersion a]
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L')
    (q : ∀ i : ℤ, (pullbackFunctor (ringedSpaceHom (a ≫ f))).obj (A.piece (i * d)) ⟶
      (laurent L').piece i) (i : ℤ) :
    chartLocalApp f a A d L e q i =
      ModuleHomGlue.ofPullback a
        ((Scheme.Modules.pullbackComp a f).hom.app (A.piece (i * d)) ≫ q i ≫
          (laurentPullbackCongrIso a L e i).inv) :=
  reassocFivefold _ _ _ _ _

/-- Cancelling the two restriction comparisons out of a naturality square, stated in a bare
category with every object and morphism free. The two contractions of the iterated inverse image
and the chart comparison enter only as the morphisms `cc` and `lph` together with the equations
identifying them, so that the application needs no rewriting inside the category of sheaves of
modules. -/
private theorem cancelRestrictSquare {C : Type*} [Category C] {M₁ M₂ M₃ N₁ N₂ N₃ : C}
    (rM : M₁ ≅ M₂) (rN : N₁ ≅ N₂) (pc : M₂ ≅ M₃) (lp : N₂ ≅ N₃)
    (q : M₃ ⟶ N₃) (w : M₂ ⟶ N₂) (cc : M₃ ⟶ M₂) (lph : N₂ ⟶ N₃)
    (hcc : cc = pc.inv) (hlph : lph = lp.hom)
    (hnat : ((rM.hom ≫ pc.hom) ≫ q ≫ (rN ≪≫ lp).inv) ≫ rN.hom = rM.hom ≫ w) :
    cc ≫ w ≫ lph = q := by
  subst hcc
  subst hlph
  rw [Iso.trans_inv] at hnat
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hnat
  rw [← (cancel_epi rM.hom).mp hnat]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- **A family of homogeneous components whose restrictions along `a` are the local datum has
the given local family as its degreewise pullback**, read through the chart comparison: the
degreewise pullback `...RelativeProjQcohSheaf.pullbackFamily` of the family along `a`, followed
by the functoriality of the Laurent algebra, is the local family.

This is the step that makes the glueing of `ψ` meet the locality statements
`...RelativeProjQcohSheaf.mul_of_pullbackFamily_mul_cover` and
`...RelativeProjQcohSheaf.one_of_pullback_map_cover`: those are stated about `pullbackFamily`,
while what the glueing tool returns is a morphism whose *restrictions* are known. The passage
between the two is the naturality of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` together with
`...RelativeProjQcohSheaf.compComparison_eq_pullbackComp_inv`, which identifies the contraction
of the iterated inverse image that `pullbackFamily` is written with and Mathlib's composition
isomorphism that `restrictPullbackFunctorCompIso` is built from. Nothing else enters, and both
comparisons cancel. -/
theorem pullbackFamily_congrIso_of_restrictFunctor_map_eq (a : V ⟶ T) [IsOpenImmersion a]
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L')
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (q : ∀ i : ℤ, (pullbackFunctor (ringedSpaceHom (a ≫ f))).obj (A.piece (i * d)) ⟶
      (laurent L').piece i)
    (h : ∀ i, (Scheme.Modules.restrictFunctor a).map (app i) = chartLocalApp f a A d L e q i)
    (i : ℤ) :
    pullbackFamily app a i ≫ (congrIso e i).hom = q i := by
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback a).hom.naturality (app i)
  rw [h i] at hnat
  refine Eq.trans ?_ (cancelRestrictSquare
    ((Scheme.Modules.restrictFunctorIsoPullback a).app
      ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))))
    ((Scheme.Modules.restrictFunctorIsoPullback a).app ((laurent L).piece i))
    ((Scheme.Modules.pullbackComp a f).app (A.piece (i * d)))
    (laurentPullbackCongrIso a L e i) (q i)
    ((pullbackFunctor (ringedSpaceHom a)).map (app i))
    (compComparison a f (A.piece (i * d)))
    (laurentPullback a L i ≫ (congrIso e i).hom)
    (compComparison_eq_pullbackComp_inv a f (A.piece (i * d)))
    (laurentPullbackCongrIso_hom a L e i) hnat)
  simp only [pullbackFamily, Category.assoc]
  rfl

/-- **The degreewise pullback of a glued family is the local family transported backwards along
the chart comparison.** This is
`...RelativeProjQcohSheaf.pullbackFamily_congrIso_of_restrictFunctor_map_eq` with the comparison
moved to the other side, which is the form
`...RelativeProjQcohSheaf.Twisting.congrModuleInv` is stated at: when the local family is the map
of a quadruple over `a ≫ f`, the degreewise pullback of the glued family over that member of the
covering is `(ψ.congrModuleInv e).app`, and so satisfies both laws of a
`...RelativeProjQcohSheaf.Twisting`. -/
theorem pullbackFamily_eq_of_restrictFunctor_map_eq (a : V ⟶ T) [IsOpenImmersion a]
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L')
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (q : ∀ i : ℤ, (pullbackFunctor (ringedSpaceHom (a ≫ f))).obj (A.piece (i * d)) ⟶
      (laurent L').piece i)
    (h : ∀ i, (Scheme.Modules.restrictFunctor a).map (app i) = chartLocalApp f a A d L e q i)
    (i : ℤ) :
    pullbackFamily app a i = q i ≫ (congrIso e i).inv :=
  (Iso.eq_comp_inv (congrIso e i)).mpr
    (pullbackFamily_congrIso_of_restrictFunctor_map_eq a e app q h i)

/-- The degreewise pullback of a glued family is the backwards transport of the local map. -/
private theorem pullbackFamily_eq_congrModuleInv_app (a : V ⟶ T) [IsOpenImmersion a]
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L')
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (ψ : Twisting (a ≫ f) A d L')
    (h : ∀ i, (Scheme.Modules.restrictFunctor a).map (app i) = chartLocalApp f a A d L e ψ.app i) :
    pullbackFamily app a = (ψ.congrModuleInv e).app :=
  funext fun n => pullbackFamily_eq_of_restrictFunctor_map_eq a e app ψ.app h n

/-- **The multiplicativity of a glued family of homogeneous components, from the maps given on
the members of the covering.** If the restrictions of `app` along a covering family of open
immersions are the local data built from the maps `ψ k` of quadruples over the members, then
`app` satisfies the law `...RelativeProjQcohSheaf.Twisting.app_mul` in every integral bidegree.

Nothing new enters: `...RelativeProjQcohSheaf.pullbackFamily_eq_of_restrictFunctor_map_eq`
identifies the degreewise pullback of `app` with
`(...Twisting.congrModuleInv (e k)).app` of the local map, which satisfies the law because it is
the map of a `...RelativeProjQcohSheaf.Twisting`, and
`...RelativeProjQcohSheaf.mul_of_pullbackFamily_mul_cover` is the locality of the law. -/
theorem mul_of_chartLocal_cover
    {ι : Type*} {Z : ι → Scheme.{u}} (g : ∀ k, Z k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤)
    {Lc : ∀ k, SheafOfModules.{u} (structureRingSheaf (Z k).toRingedSpace)}
    [∀ k, Stacks.SheafOfModules.IsInvertible (Z k).toRingedSpace.presheaf
      (isSheafStruct (Z k)) (Lc k)]
    (e : ∀ k, (pullbackFunctor (ringedSpaceHom (g k))).obj L ≅ Lc k)
    (ψ : ∀ k, Twisting (g k ≫ f) A d (Lc k))
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (h : ∀ (k : ι) (i : ℤ), (Scheme.Modules.restrictFunctor (g k)).map (app i) =
      chartLocalApp f (g k) A d L (e k) (ψ k).app i)
    (i j : ℤ) :
    MonoidalCategoryStruct.tensorHom (app i) (app j) ≫ (laurent L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (A.mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
          app (i + j) :=
  mul_of_pullbackFamily_mul_cover app g hg i j fun k => by
    rw [pullbackFamily_eq_congrModuleInv_app (g k) (e k) app (ψ k) (h k)]
    exact ((ψ k).congrModuleInv (e k)).app_mul i j

/-- **The unit law of a glued family of homogeneous components, from the maps given on the members
of the covering.** If the restrictions of `app` along a covering family of open immersions are the
local data built from the maps `ψ k` of quadruples over the members, then `app` satisfies the law
`...RelativeProjQcohSheaf.Twisting.app_one`.

This is `...RelativeProjQcohSheaf.mul_of_chartLocal_cover` for the other law, and nothing new
enters there either: `...RelativeProjQcohSheaf.pullbackFamily_eq_of_restrictFunctor_map_eq`
identifies the degreewise pullback of `app` with `(...Twisting.congrModuleInv (e k)).app` of the
local map, which satisfies the law because it is the map of a
`...RelativeProjQcohSheaf.Twisting`, and
`...RelativeProjQcohSheaf.one_of_pullbackFamily_one_cover` is the locality of the law. -/
theorem one_of_chartLocal_cover
    {ι : Type*} {Z : ι → Scheme.{u}} (g : ∀ k, Z k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤)
    {Lc : ∀ k, SheafOfModules.{u} (structureRingSheaf (Z k).toRingedSpace)}
    [∀ k, Stacks.SheafOfModules.IsInvertible (Z k).toRingedSpace.presheaf
      (isSheafStruct (Z k)) (Lc k)]
    (e : ∀ k, (pullbackFunctor (ringedSpaceHom (g k))).obj L ≅ Lc k)
    (ψ : ∀ k, Twisting (g k ≫ f) A d (Lc k))
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (h : ∀ (k : ι) (i : ℤ), (Scheme.Modules.restrictFunctor (g k)).map (app i) =
      chartLocalApp f (g k) A d L (e k) (ψ k).app i) :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
        app 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent L) :=
  one_of_pullbackFamily_one_cover app g hg fun k => by
    rw [pullbackFamily_eq_congrModuleInv_app (g k) (e k) app (ψ k) (h k)]
    exact ((ψ k).congrModuleInv (e k)).app_one

/-- **The surjectivity of a homogeneous component of a glued family, from the maps given on the
members of the covering.** If the restrictions of `app` along a covering family of open
immersions are the local data built from the maps `ψ k`, and the degree-`n` component of each
`ψ k` is surjective, then so is the degree-`n` component of `app`. This is the condition
`...RelativeProjQcohSheaf.Quadruple.epi_app_one` demands, at `n = 1`.

It is `...RelativeProjQcohSheaf.epi_of_pullbackFamily_comp_epi_cover` with the chart comparison
as the isomorphism it allows on the target, and
`...RelativeProjQcohSheaf.pullbackFamily_congrIso_of_restrictFunctor_map_eq` identifying the
composite with the local map. -/
theorem epi_of_chartLocal_cover
    {ι : Type*} {Z : ι → Scheme.{u}} (g : ∀ k, Z k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤)
    {Lc : ∀ k, SheafOfModules.{u} (structureRingSheaf (Z k).toRingedSpace)}
    [∀ k, Stacks.SheafOfModules.IsInvertible (Z k).toRingedSpace.presheaf
      (isSheafStruct (Z k)) (Lc k)]
    (e : ∀ k, (pullbackFunctor (ringedSpaceHom (g k))).obj L ≅ Lc k)
    (ψ : ∀ k, Twisting (g k ≫ f) A d (Lc k))
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (h : ∀ (k : ι) (i : ℤ), (Scheme.Modules.restrictFunctor (g k)).map (app i) =
      chartLocalApp f (g k) A d L (e k) (ψ k).app i)
    (n : ℤ) (hepi : ∀ k, Epi ((ψ k).app n)) : Epi (app n) := by
  have : ∀ k : ι, IsIso ((congrIso (e k) n).hom) := fun k => inferInstance
  refine epi_of_pullbackFamily_comp_epi_cover app g hg n (fun k => (laurent (Lc k)).piece n)
    (fun k => (congrIso (e k) n).hom) fun k => ?_
  rw [pullbackFamily_congrIso_of_restrictFunctor_map_eq (g k) (e k) app (ψ k).app (h k) n]
  exact hepi k

end Local

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end

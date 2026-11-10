module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMap
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin class of a restricted form is the form wedged with the Gysin class of one

Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions and
let `i : Z ⟶ X` be the closed subscheme they cut out. [Stacks, Tag 0G88] says that for a class
`α ∈ H^q(X, Ω^p_{X/S})`

`γ^p(α|_Z) = i^{-1}α ∧ γ^0(1)` in `H^q(Z, ℋ^c_Z(Ω^{p+c}_{X/S}))`,

and its proof reduces the identity, "by general properties of cup products", to commutativity of
the square of sheaves on `Z`

```
i^{-1}Ω^p_X ⊗ Ω^0_Z --id ⊗ γ^0--> i^{-1}Ω^p_X ⊗ ℋ^c_Z(Ω^c_X)
      |                                        |
      | restriction                            | ∧
      v                                        v
   Ω^p_Z ⊗ Ω^0_Z ----∧----> Ω^p_Z ----γ^p----> ℋ^c_Z(Ω^{p+c}_X)
```

whose verification the source omits, remarking that the maps `γ^j_{f₁, …, f_c}` "are chosen
exactly such that this works and such that `1` maps to `d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)`". This
file proves that square, on the sections determined by a **global** `p`-form `ω` on `X`, which is
the case `q = 0` of the identity: the top-right path sends `ω ⊗ 1` to `ω ∧ γ^0(1)` and the
bottom path sends it to `γ^p(ω|_Z)`, and the two agree. The identity in a general cohomological
degree is `AlgebraicGeometry.Scheme.Hom.gysin_formRestriction_cupDegreeZero` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinPairing.lean`, which is where the tag is
registered; it is built on the wedge pairing with the local cohomology sheaf, whose route the
implementation notes below set out.

The proof is one instance of the functoriality of the class map `c_{f₁, …, f_c}` of
[Stacks, Tag 0G7Q] in its coefficient module — [Stacks, Tag 0G7T], available here as
`Stacks.Perfect.SupportedFraction.supportedFractionSource_natural` — applied to the morphism
`Ω^c_{X/S} ⟶ Ω^{p+c}_{X/S}` of left multiplication by `ω`. That is the precise sense in which the
Gysin maps "are chosen exactly such that this works": wedging with `ω` before taking the fraction
class and wedging with `ω` inside the local cohomology sheaf after it are the same thing,
because `ω ∧ (η / f₁ ⋯ f_c) = (ω ∧ η) / (f₁ ⋯ f_c)`.

## Main definitions

* `SheafOfModules.GradedAlgebra.leftMul`: left multiplication by a global homogeneous section of
  a sheaf of graded algebras, as a morphism of sheaves of modules. This is the mirror of
  `SheafOfModules.GradedAlgebra.rightMul`, which is the wedge factor of the Gysin formula.
* `AlgebraicGeometry.Scheme.Hom.formLeftWedgeHom`: left multiplication by a global relative
  differential form, as a morphism `Ω^q_{X/S} ⟶ Ω^{p+q}_{X/S}`.
* `AlgebraicGeometry.Scheme.Hom.supportedGysinFormulaHom`: the right-hand side
  `c_{f₁, …, f_c}(- ∧ d f₁ ∧ ⋯ ∧ d f_c)` of the Gysin formula of [Stacks, Tag 0G83], read with
  the class map in the shape `ℱ ⟶ i_*ℋ^c_T(ℱ)` in which it is functorial in `ℱ`.
* `AlgebraicGeometry.Scheme.Hom.supportedGysinUnitClass`: `γ^0(1)`, the class of the fraction
  `d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.supportedGysinFormulaHom_sectionsMap`: **the square of the proof
  of [Stacks, Tag 0G88]**, on the sections determined by a global `p`-form: the fraction class of
  `ω ∧ d f₁ ∧ ⋯ ∧ d f_c` is `ω ∧ γ^0(1)`.
* `AlgebraicGeometry.Scheme.Hom.gysin_formRestriction_eq_wedge_supportedGysinUnitClass`:
  **[Stacks, Tag 0G88] for `q = 0`**, stated for the Gysin map itself: any morphism `γ` out of
  `i_*Ω^p_{Z/S}` satisfying the Gysin formula of [Stacks, Tag 0G83] sends `ω|_Z` to
  `ω ∧ γ^0(1)`.

## Implementation notes

**What is proved here, and where the rest is.** The source's statement is about a class
`α ∈ H^q(X, Ω^p_{X/S})` in arbitrary cohomological degree, and its right-hand side is a cup
product. What is proved *in this file* is the degree `q = 0` case, where `α` is a global
`p`-form, the cup product with the degree-zero class `γ^0(1)` is ordinary multiplication, and
the identity is the commutative square the source's proof reduces the general case to. The
reduction of the general case to that square needs two further inputs, discussed in the two
bullets below; both are now in the library, and the tag is registered on the general-`q`
statement in `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinPairing.lean`. The bullets are
kept because they record which construction each input is and why the obvious routes to the
second one fail. They read "this library does not have"; that was true when they were written:

* the cup product `H^q(Z, 𝒜) × H^0(Z, ℬ) ⟶ H^q(Z, 𝒜 ⊗ ℬ)` of
  [Stacks, Section 0FKU] for sheaves of modules on the ringed space `(Z, i^{-1}𝒪_X)`, together
  with the statement that cupping with a degree-zero class is functoriality along the
  multiplication map — `Stacks.Cohomology.DerivedGlobalCupProduct` has the global cup product of
  [Stacks, Tag 0FKU], but not that normalization. **This one is now in the library**, as
  `Stacks.Cohomology.cupDegreeZero` of
  `StacksFrontier/AlgebraicGeometry/DeRham/Cohomology/DegreeZeroCupProduct.lean`: for a pairing
  given sectionwise as a `Stacks.BilinearMap` and a degree-zero class, that is a global section
  `u` of the second factor, it is `H^q` of `Stacks.Cohomology.rightMulHom`, the morphism
  `a ↦ μ(a, u)`, so the normalization *is* the definition; the degree-zero case, identifying it
  with the pairing on global sections, is `…cupDegreeZero_zero_toRightDerivedZero`, and the two
  functorialities are `…cupDegreeZero_naturality_left` and `…cupDegreeZero_compRight`. Only
  cupping with a degree-zero class is constructed, which is all the tag's right-hand side uses;
* the pairing `i^{-1}Ω^p_{X/S} ⊗_{i^{-1}𝒪_X} ℋ^c_Z(Ω^c_{X/S}) ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})` that the
  right vertical arrow of the square is. The source obtains it as the degree-`c` cohomology sheaf
  of the map of [Stacks, Tag 0G75] followed by the wedge product, using the vanishing of
  [Stacks, Tag 0G7N] above degree `c`. The map of Tag 0G75 is
  `Stacks.Cohomology.SupportedComplexes.supportedTensorMap`, which carries the invertibility
  `hpf` of the projection-formula map of [Stacks, Tag 0B53] — that is [Stacks, Tag 0B55] — as a
  hypothesis. That hypothesis *is* dischargeable: it is
  `isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed`, of
  `ProjectionFormulaClosedEmbeddingUnconditional.lean` in
  `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/`, which concludes
  `IsIso (projectionFormulaMap (closedSubsetInclusion X Z) E K)` for arbitrary
  `E` and `K`, read at `E := (derivedSupportedSectionsOnClosed X Z hZ).obj M`. What remains
  missing, after that, is the passage to the degree-`c` cohomology sheaf: it needs the
  identification `H^c(K|_Z ⊗^𝐋 M) = K|_Z ⊗ H^c(M)` for `M` with vanishing cohomology above `c`.
  Right t-exactness of the derived tensor product is available
  (`Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor`) but that top-degree identification
  is not: `Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingleIso` carries a
  K-flatness hypothesis on the left factor, which `Ω^p_{X/S}` does not satisfy, and
  `Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso` asks the same of the right factor.
  Instead of that pairing, the right vertical arrow is used here only through its value on the
  sections coming from a *global* `p`-form `ω`, where it is `i_*ℋ^c_T` applied to left
  multiplication by `ω` and no tensor product is needed;
* the glued Gysin map of [Stacks, Tag 0G86]. Only a *global* family of equations appears below,
  as in [Stacks, Tag 0G83]; `Stacks.Gysin.GysinChartData.gysinHom` glues the local maps but into
  an abstract target sheaf carried as a field of `Stacks.Gysin.GysinChartData`, not into the
  local cohomology sheaf.

**The route to the pairing, and what of these notes is out of date.** Three of the statements
above are weaker than the library's actual state, and the pairing is not blocked where they say
it is.

* The passage to the degree-`c` cohomology sheaf does **not** require the derived top-degree
  identification `H^c(K|_Z ⊗^𝐀 M) = K|_Z ⊗ H^c(M)`. In the equation-chart model that sheaf *is*
  a cokernel: `Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` identifies
  `cokernel (lastDif f ℱ)` with `i_*ℋ^c_T(ℱ)`, and it is an isomorphism, by
  `…isIso_cokernelLastDifToSupport`. Tensoring is right exact, so in this presentation the
  identification is the universal property of a cokernel and no K-flatness enters.
* Each term of the extended alternating Čech complex is
  `Stacks.Perfect.ExtendedAlternatingCech.restrictedModule f ℱ p s`, which is `j_*j^*ℱ` for the
  open immersion `j` of the principal intersection `⋂_k X.basicOpen (f (s k))`. A pairing of
  sheaves of modules therefore induces one on the Čech terms **on local sections, over every
  open**, by restricting the first argument along `j`: no excision, no base change for the class
  map (that is [Stacks, Tag 0G7U], whose two commutative diagrams
  `StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/EquationsBaseChange.lean` records as
  unproved) and no tensor product. On the fraction cochain
  `Stacks.Perfect.SupportedFraction.fractionCochain`, which divides by `∏ f` through
  `Ring.inverse` of a unit, that pairing is compatible with the class map for the cheapest of
  reasons: `Stacks.BilinearMap.map_smul_right`.
* Descending the pairing from the Čech term to the cokernel needs no local surjectivity argument
  either. A bilinear map out of a sheaf of modules is a morphism into the internal hom, which for
  sheaves of modules is `Stacks.SheafOfModules.sheafHom` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHom.lean` — a sheaf by
  `Stacks.PresheafOfModules.InternalHom.internalHom_isSheaf`, with evaluation pairing
  `Stacks.SheafOfModules.evalBilinear` — so `cokernel.desc` applies. Should the local route be
  wanted instead, `Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi` and
  `SheafOfModules.cokernel_isLocallySurjective` are unconditional, and
  `Stacks.BilinearMap.compLeftEquiv` and `…compRightEquiv` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Algebras.lean` are the transport along a local
  bijection.

Two further corrections. The vanishing of [Stacks, Tag 0G7N] *is* in the library, as
`Stacks.Perfect.isZero_homology_derivedSupportedSections_of_locallyCutOut` of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/LocalCohomologyVanishingDegrees.lean`;
it is [Stacks, Tag 0G7P], the vanishing *below* degree `c`, that is absent. And right exactness
of the sheaf tensor product is available, as
`Stacks.SheafOfModules.TensorLocalProperties.preservesColimit_parallelPair_tensorSheafLeft` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorProductRightExact.lean`, with the universal
property `Stacks.PresheafOfModules.tensorHomEquiv`.

**General `q` is proved elsewhere, by that route.** The pairing is
`Stacks.Perfect.CechPairing.supportPair` of
`StacksFrontier/AlgebraicGeometry/DeRham/Cohomology/SupportClassPairing.lean`, built exactly as the
three bullets above describe — the Čech-term pairing, its commutation with `lastDif`, its value
on `fractionCochain`, and its descent to the cokernel — and the tag in every cohomological
degree, **for the global family of equations this file is about**, is
`AlgebraicGeometry.Scheme.Hom.gysinMap_formRestriction_cupDegreeZero` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinPairing.lean`. That file is not where
[Stacks, Tag 0G88] is registered: the tag is stated in the setting of [Stacks, Tag 0G86], where
`Z` is only locally cut out by `c` equations, and it is proved at that generality — with an
equation-free pairing in place of this global one, at an arbitrary rank `c` — by
`Stacks.Gysin.conormalGysin_formRestriction_cupDegreeZero` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ConormalWedgeProjectionRank.lean`, which carries the
single `@[stacks 0G88]`. The statements below are the degree-zero case, and
`AlgebraicGeometry.Scheme.Hom.supportedGysinFormulaHom_sectionsMap_of_pair` of that file
re-derives the first of them from the pairing, so nothing here is left standing beside it.

**The presentation of the local cohomology sheaf.** The class map is used here in the shape
`Stacks.Perfect.SupportedFraction.supportedFractionSource`, `ℱ ⟶ i_*ℋ^c_T(ℱ)` with the target
`Stacks.Perfect.SupportedFraction.supportCohomologySheaf`, because that is the only shape in
which the library proves functoriality in `ℱ`, which is the whole content of the computation.
`AlgebraicGeometry.Scheme.Hom.formFractionClass`, out of which
`AlgebraicGeometry.Scheme.Hom.gysinMap` of [Stacks, Tag 0G83] is built, uses the other
presentation `localCohomologySheafOfComplex` of the same sheaf; the two class maps are identified,
by `Stacks.Perfect.supportedFractionSource_comp_supportCohomologyToPushforward`, but that
identification is not used below. The Gysin map enters below as a morphism `γ` *characterized* by
the Gysin formula rather than as `gysinMap` itself: the characterization is the own equation of
[Stacks, Tag 0G83], `AlgebraicGeometry.Scheme.Hom.formRestriction_comp_gysinMap`, transported to
this presentation, and taking it as a hypothesis assumes nothing about `γ` that the tag does not
already assert.

**A correction to a neighbouring file.** The implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/Globalisation.lean` state that the library does not
have the class map of [Stacks, Tag 0G7Q] and that the determinant rule of [Stacks, Tag 0G7S]
"has no declaration in this library". Both are out of date: the class map is
`Stacks.Perfect.FractionClass.fractionClass`, tagged `@[stacks 0G7Q]`, and the determinant rule
is `Stacks.Perfect.SupportedFraction.supportedFractionSource_eq_det_smul`.

**`leftMul` and `rightMul` are different morphisms.** `rightMul` fixes the second factor of the
graded multiplication and `leftMul` the first, and no graded commutativity is used: the identity
proved below needs only that `gysinWedgeHom` applied to `ω` and `leftMul ω` applied to the
equation wedge are *the same section*, namely the product of `ω` with `d f₁ ∧ ⋯ ∧ d f_c` in that
order, which holds by definition.

## References

* [Stacks Project, Tag 0G88](https://stacks.math.columbia.edu/tag/0G88)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
* [Stacks Project, Tag 0G75](https://stacks.math.columbia.edu/tag/0G75)
* [Stacks Project, Tag 0G7N](https://stacks.math.columbia.edu/tag/0G7N)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Perfect.CechDerivedSupport Stacks.Perfect.SupportedFraction

universe u

namespace SheafOfModules.GradedAlgebra

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}

/-- Left multiplication by a global section `ω` of the degree-`p` part of a sheaf of graded
algebras, as a morphism of sheaves of modules from the degree-`q` to the degree-`p + q` part.
This is the mirror of `SheafOfModules.GradedAlgebra.rightMul`, which fixes the second factor. -/
def leftMul (A : SheafOfModules.GradedAlgebra R) (p q : ℤ) (ω : (A.piece p).sections) :
    A.piece q ⟶ A.piece (p + q) where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun a => (A.mul p q).app U (ω.eval U) a
          map_add' := fun a b => map_add ((A.mul p q).app U (ω.eval U)) a b
          map_smul' := fun r a => (A.mul p q).map_smul_right U r (ω.eval U) a }
      naturality := by
        intro U V h
        ext a
        change (A.mul p q).app V (ω.eval V) ((A.piece q).val.map h a) =
          (A.piece (p + q)).val.map h ((A.mul p q).app U (ω.eval U) a)
        rw [(A.mul p q).naturality h, PresheafOfModules.sections_property ω h] }

/-- On sections over `U`, `leftMul p q ω` sends `a` to the product of `ω` restricted to `U`
with `a`. -/
@[simp]
theorem leftMul_app_apply (A : SheafOfModules.GradedAlgebra R) (p q : ℤ)
    (ω : (A.piece p).sections) (U : Cᵒᵖ) (a : (A.piece q).val.obj U) :
    (A.leftMul p q ω).val.app U a = (A.mul p q).app U (ω.eval U) a :=
  rfl

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Scheme.Hom

variable {X S Z : Scheme.{u}}

attribute [local instance] isQuasicoherent_relativeDifferentialForms

/-! ### Left multiplication by a global relative differential form -/

/-- Left multiplication by a global relative `p`-form `ω`, as a morphism of sheaves of modules
`Ω^q_{X/S} ⟶ Ω^{p+q}_{X/S}`. On a local section `η` of `Ω^q_{X/S}` it is the wedge `ω ∧ η`. -/
def formLeftWedgeHom (π : X ⟶ S) {p : ℤ} (ω : (relativeDifferentialForms π p).sections) (q : ℤ) :
    relativeDifferentialForms π q ⟶ relativeDifferentialForms π (p + q) :=
  (relativeDifferentialFormsAlgebra π).leftMul p q ω

/-- **The characterising equation.** On a local section `η` of `Ω^q_{X/S}`, left multiplication by
a global `p`-form `ω` is the wedge of `ω` with `η`. -/
@[simp]
theorem formLeftWedgeHom_app_apply (π : X ⟶ S) {p : ℤ}
    (ω : (relativeDifferentialForms π p).sections) (q : ℤ) (U : X.Opensᵒᵖ)
    (η : (relativeDifferentialForms π q).val.obj U) :
    (formLeftWedgeHom π ω q).val.app U η =
      ((relativeDifferentialFormsAlgebra π).mul p q).app U (ω.eval U) η :=
  rfl

/-- **Wedging on the right with the equations and wedging on the left with a global form give the
same section.** Both are the product `ω ∧ d f₁ ∧ ⋯ ∧ d f_c`, in that order; no graded
commutativity is involved. -/
theorem sectionsMap_gysinWedgeHom_eq (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) {p : ℤ}
    (ω : (relativeDifferentialForms π p).sections) :
    SheafOfModules.sectionsMap (gysinWedgeHom π f p) ω =
      SheafOfModules.sectionsMap (formLeftWedgeHom π ω (c : ℤ)) (equationsWedge π f) :=
  Subtype.ext (funext fun _ => rfl)

/-! ### The Gysin formula and the Gysin class of one -/

variable {d : ℕ}

/-- The right-hand side `c_{f₁, …, f_c}(ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c)` of the Gysin formula of
[Stacks, Tag 0G83], with the class map of [Stacks, Tag 0G7Q] read in the shape
`ℱ ⟶ i_*ℋ^c_T(ℱ)` of `Stacks.Perfect.SupportedFraction.supportedFractionSource`, in which it is
functorial in `ℱ`. -/
def supportedGysinFormulaHom (π : X ⟶ S) (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    relativeDifferentialForms π (p : ℤ) ⟶
      supportCohomologySheaf hT
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ((d + 1 : ℕ) : ℤ) :=
  gysinWedgeHom π f (p : ℤ) ≫
    supportedFractionSource f
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) hT hTf

/-- **`γ^0(1)`, the Gysin class of one**: the class of the fraction
`d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)` in `i_*ℋ^c_T(Ω^c_{X/S})`. By the Gysin formula of
[Stacks, Tag 0G83] at `p = 0` this is the image of `1` under `γ^0`, which is what the source's
proof says it is: the maps `γ^j_{f₁, …, f_c}` are chosen so that `1` goes to
`d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)`. -/
def supportedGysinUnitClass (π : X ⟶ S) (f : Fin (d + 1) → Γ(X, ⊤)) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    (supportCohomologySheaf hT
      (relativeDifferentialForms π ((d + 1 : ℕ) : ℤ)) ((d + 1 : ℕ) : ℤ)).sections :=
  SheafOfModules.sectionsMap
    (supportedFractionSource f (relativeDifferentialForms π ((d + 1 : ℕ) : ℤ)) hT hTf)
    (equationsWedge π f)

/-! ### The square of the proof of Tag 0G88 -/

/-- **Stacks Project, Tag 0G88: the square the proof reduces the identity to, on the sections of a
global `p`-form.** The fraction class of `ω ∧ d f₁ ∧ ⋯ ∧ d f_c` equals the image of
`γ^0(1) = d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)` under `i_*ℋ^c_T` applied to left multiplication by `ω`.

In the notation of the source's diagram, the section `ω ⊗ 1` of `i^{-1}Ω^p_X ⊗ Ω^0_Z` is carried
by the bottom path to `γ^p(ω|_Z)` — the left-hand side here, by the Gysin formula of
[Stacks, Tag 0G83] — and by the top-right path to `ω ∧ γ^0(1)`, the right-hand side. The proof is
functoriality of the class map in its coefficient module, [Stacks, Tag 0G7T], at the morphism
`Ω^c_{X/S} ⟶ Ω^{p+c}_{X/S}` of left multiplication by `ω`. -/
theorem supportedGysinFormulaHom_sectionsMap (π : X ⟶ S) (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ)
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    (ω : (relativeDifferentialForms π (p : ℤ)).sections) :
    SheafOfModules.sectionsMap (supportedGysinFormulaHom π f p hT hTf) ω =
      SheafOfModules.sectionsMap
        (supportCohomologySheafMap hT
          (formLeftWedgeHom π ω ((d + 1 : ℕ) : ℤ)) ((d + 1 : ℕ) : ℤ))
        (supportedGysinUnitClass π f hT hTf) := by
  have hnat := supportedFractionSource_natural f
    (formLeftWedgeHom π ω ((d + 1 : ℕ) : ℤ)) hT hTf
  rw [supportCohomologySheafFunctor_map] at hnat
  refine (SheafOfModules.sectionsMap_comp _ _ ω).trans ?_
  rw [sectionsMap_gysinWedgeHom_eq π f ω]
  refine (SheafOfModules.sectionsMap_comp _ _ _).symm.trans ?_
  refine (congrArg (fun ψ => SheafOfModules.sectionsMap ψ (equationsWedge π f)) hnat).trans ?_
  exact SheafOfModules.sectionsMap_comp _ _ _

/-- **Stacks Project, Tag 0G88 for `q = 0`, stated for the Gysin map.** Let `γ` be any morphism
`i_*Ω^p_{Z/S} ⟶ i_*ℋ^c_T(Ω^{p+c}_{X/S})` satisfying the Gysin formula of [Stacks, Tag 0G83] —
that is, whose composite with restriction of forms to `Z` is
`c_{f₁, …, f_c}(- ∧ d f₁ ∧ ⋯ ∧ d f_c)`, which is the equation
`AlgebraicGeometry.Scheme.Hom.formRestriction_comp_gysinMap` that determines the Gysin map. Then
for a global relative `p`-form `ω` on `X`

`γ^p(ω|_Z) = ω ∧ γ^0(1)`,

the right-hand side being `i_*ℋ^c_T` applied to left multiplication by `ω`, evaluated on the
Gysin class of one. -/
theorem gysin_formRestriction_eq_wedge_supportedGysinUnitClass (i : Z ⟶ X) (π : X ⟶ S)
    (f : Fin (d + 1) → Γ(X, ⊤)) (p : ℕ) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T)
    (γ : (Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) (p : ℤ)) ⟶
      supportCohomologySheaf hT
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ((d + 1 : ℕ) : ℤ))
    (hγ : formRestriction i π (p : ℤ) ≫ γ = supportedGysinFormulaHom π f p hT hTf)
    (ω : (relativeDifferentialForms π (p : ℤ)).sections) :
    SheafOfModules.sectionsMap γ
        (SheafOfModules.sectionsMap (formRestriction i π (p : ℤ)) ω) =
      SheafOfModules.sectionsMap
        (supportCohomologySheafMap hT
          (formLeftWedgeHom π ω ((d + 1 : ℕ) : ℤ)) ((d + 1 : ℕ) : ℤ))
        (supportedGysinUnitClass π f hT hTf) :=
  (congrArg (fun ψ => SheafOfModules.sectionsMap ψ ω) hγ).trans
    (supportedGysinFormulaHom_sectionsMap π f p hT hTf ω)

end AlgebraicGeometry.Scheme.Hom

end

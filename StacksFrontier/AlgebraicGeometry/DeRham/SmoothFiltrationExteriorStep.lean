module

public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplexDegreewise
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFiltration
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsLocalKunneth
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationExteriorStep
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationDegreewise

/-!
# The degreewise step of Section 50.12's filtration, for the de Rham pullback map

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, with `g : Y ⟶ S` the structure
morphism of the target. `StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationExteriorStep`
identifies the degree-`m` term of the `k`-th step of Section 50.12's filtration of the *complex*
`Ω^•_{X/S}` with the step at `k` of the filtration of the single *sheaf* `⋀^mΩ_{X/S}`, read over
the base ring sheaf `A = (f∘g)^{-1}𝒪_S`. It does so at generic binders, taking as a hypothesis
the factorization

`ι.f i = c i ≫ (⋀^i F ⟶ ⋀^iΩ_{X/S})|_A`

of the comparison `ι : P^• ⟶ Ω^•_{X/S}` through the exterior powers of `F`.

**This file instantiates that hypothesis** at `P^• = f^{-1}Ω^•_{Y/S}`, `ι = ρ` the de Rham
pullback map of [Stacks, Tag 0FKP], and `F = f^*Ω_{Y/S}` the subobject of the transitivity
sequence: the factorization is
`Stacks.DeRhamPullback.deRhamPullbackChain_f_exteriorPowerPullback`, whose second factor is the
degree-`n` component of the comparison of exterior algebras of [Stacks, Tag 0FLV], and that
comparison *is* the morphism on exterior algebras induced by `f^*Ω_{Y/S} ⟶ Ω_{X/S}`.

## Main definitions

* `Stacks.DeRhamSmooth.pulledBackDifferentialsAlgebras`: the tensor, exterior and symmetric
  algebras of `f^*Ω_{Y/S}`, the sheaf the filtration of `Ω^n_{X/S}` is cut out by.
* `Stacks.DeRhamSmooth.pulledBackFormsIso`: the comparison
  `f^*(⋀^nΩ_{Y/S}) ≅ ⋀^n(f^*Ω_{Y/S})` of [Stacks, Tag 01CI] at the relative differentials of
  `g`.
* `Stacks.DeRhamSmooth.pulledBackFormsComparison`: **the factorization `c n`** of the degree-`n`
  component of `ρ` through `⋀^n(f^*Ω_{Y/S})`: the comparison `f^{-1}Ω^n_{Y/S} ⟶ f^*Ω^n_{Y/S}`
  followed by that isomorphism.

## Main results

* `Stacks.DeRhamSmooth.relativeDifferentialFormsComparison_eq_exteriorMap`: the comparison of
  exterior algebras of [Stacks, Tag 0FLV] attached to the square of `f` over `S` is the
  morphism on exterior algebras induced by the canonical map `f^*Ω_{Y/S} ⟶ Ω_{X/S}`, which is
  the first map of the transitivity sequence.
* `Stacks.DeRhamSmooth.deRhamPullbackChain_f_eq_pulledBackFormsComparison_comp`: **the
  factorization hypothesis, instantiated at `ρ`.**
* `Stacks.DeRhamSmooth.mapSubobjects_wedgeFiltrationStep_eq_exteriorFiltration`:
  **the degree-`m` term of the `k`-th step of Section 50.12's filtration of `Ω^•_{X/S}` is the
  step at `k` of the filtration of `Ω^m_{X/S}` by the forms pulled back from `Y`**, read over
  `(f∘g)^{-1}𝒪_S` and pushed into the extension by zero of the de Rham complex.

## Implementation notes

**The hypothesis this file still carries, and where it is discharged.** The statement below
carries the epimorphy hypothesis of
`AlgebraicGeometry.SheafOfModules.mapSubobjects_wedgeFiltrationStep_eq_exteriorImageFiltration`,
that

`f^{-1}Ω^k_{Y/S} ⊗_A Ω^{m-k}_{X/S} ⟶ (⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{m-k}_{X/S})|_A`

is an epimorphism — the underived identity
`F ⊗_{𝒪_X} f^*G ≅ F ⊗_{f^{-1}𝒪_Y} f^{-1}G` of [Stacks, Tag 08DE] in surjective form. It is
**proved**, by `Stacks.DeRhamSmooth.epi_pulledBackFormsComparison_tensor_comp_laxComparison` of
`StacksFrontier.AlgebraicGeometry.DeRham.PulledBackFormsComparisonEpi`, and not through the
ringed-*topos* form of that identity
(`Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.spaceUnderivedLinearMixedTensorIso`), the
bridge from which to the `restrictScalars`-of-`tensorSheaf` spelling the lax comparison is
written in is indeed not available: it is proved from the local generation of a pullback of
sheaves of modules by the pullback-unit sections, which needs no such bridge. The hypothesis-free
form of the statement below is therefore
`Stacks.DeRhamSmooth.mapSubobjects_wedgeFiltrationStep_eq_exteriorFiltration'`, and it is what the
graded pieces of [Stacks, Section 0FMK] are built on
(`Stacks.DeRhamSmooth.mk_ι_app_f_eq`).

**Nothing here is a rewrite.** The three spellings of restriction of scalars along
`(f∘g)^{-1}𝒪_S ⟶ 𝒪_X` that meet in the statements —
`RingedSpaceModuleAdjunction.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase (f ≫ g))`,
`SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHom)` and the
degreewise terms of `AlgebraicGeometry.Scheme.Hom.deRhamComplex` — agree by definition but not
at reducible transparency, so the proofs are composed from `Eq.trans` and `congrArg` and the
types are ascribed rather than rewritten into place. This is the same discipline as in
`StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplexDegreewise`.

**Why the comparison of exterior algebras is the induced map, by `rfl`.**
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsComparison` is defined as the universal
descent of `relativeDifferentialsMap ≫ exteriorGenerator`, and
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map` is defined as the universal descent of
`f ≫ κ`; the two exterior-algebra packages involved,
`AlgebraicGeometry.Scheme.Modules.exteriorAlgebra` and the `exterior` field of
`SheafOfModules.ringedSpaceAlgebras`, are the same `SheafOfModules.algebras`, and
`IsExteriorAlgebra` is a proposition, so the universal-property arguments need not be matched.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FKP](https://stacks.math.columbia.edu/tag/0FKP)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.DeRhamSmooth

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The tensor, exterior and symmetric algebras of `f^*Ω_{Y/S}`, the first term of the
transitivity sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0`. Its exterior powers
`⋀^k(f^*Ω_{Y/S})` are the sheaves whose images in `Ω^n_{X/S}` cut out the filtration of
[Stacks, Section 0FMK]. -/
abbrev pulledBackDifferentialsAlgebras :
    _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier)
      (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁ :=
  _root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
    (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁

/-- **The comparison `f^*(⋀^nΩ_{Y/S}) ≅ ⋀^n(f^*Ω_{Y/S})` of [Stacks, Tag 01CI]** at the
relative differentials of `g`, in degree `n`. It is given a name of its own because the
statements below mention it inside the goals that identify the two filtrations, where the
inlined comparison is large enough to exhaust the default heartbeat budget in `whnf`. -/
def pulledBackFormsIso (n : ℕ) :
    (Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (n : ℤ)) ≅
      (pulledBackDifferentialsAlgebras f g).exteriorPower n :=
  (Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso f.toLRSHom.toShHom
    (Scheme.Hom.relativeDifferentialFormsAlgebra g)
    (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials g))
    (Scheme.Modules.exteriorAlgebra
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials g)))
    (Scheme.Modules.exteriorGenerator
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials g)))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (Scheme.Hom.relativeDifferentials g))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)).app (n : ℤ)

/-- **The factorization of the de Rham pullback map through the exterior powers of
`f^*Ω_{Y/S}`**: the comparison `f^{-1}Ω^n_{Y/S} ⟶ f^*Ω^n_{Y/S}` of
`StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageComparison`, followed by
`Stacks.DeRhamSmooth.pulledBackFormsIso`, read as a morphism of sheaves of
`(f∘g)^{-1}𝒪_S`-modules.

This is the morphism `c n` out of which `Stacks.DeRhamSmooth.deRhamSmoothFiltration` is read
on the exterior powers: the degree-`n` component of `ρ` is this followed by the restriction of
scalars of `⋀^n(f^*Ω_{Y/S}) ⟶ ⋀^nΩ_{X/S}`. -/
def pulledBackFormsComparison (n : ℕ) :
    (pulledBackDeRhamComplex f g).X n ⟶
      (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom
          (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).obj
        ((pulledBackDifferentialsAlgebras f g).exteriorPower n) :=
  Stacks.DeRhamDirectImage.relativeInverseImageToPullback f g
      (Scheme.Hom.relativeDifferentialForms g (n : ℤ)) ≫
    (_root_.SheafOfModules.restrictScalars.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map
      (pulledBackFormsIso f g n).hom

/-- **The comparison of exterior algebras of [Stacks, Tag 0FLV] attached to the square of `f`
over `S` is the morphism on exterior algebras induced by the first map of the transitivity
sequence.** Both are the unique unital homomorphism `⋀(f^*Ω_{Y/S}) ⟶ ⋀(Ω_{X/S})` extending the
canonical map `f^*Ω_{Y/S} ⟶ Ω_{X/S}` on differentials, and both are spelled as that universal
descent, so they agree by definition. -/
theorem relativeDifferentialFormsComparison_eq_exteriorMap :
    Scheme.Hom.relativeDifferentialFormsComparison f g (f ≫ g) (𝟙 S)
        (Category.comp_id (f ≫ g)).symm =
      (pulledBackDifferentialsAlgebras f g).exterior_isExteriorAlgebra.map
        (Scheme.Hom.deRhamAlgebras (f ≫ g)).exterior_isExteriorAlgebra
        (Scheme.Hom.relativeDifferentialsShortComplex f g).f :=
  rfl

/-- **The degree-`n` component of the de Rham pullback map factors through `⋀^n(f^*Ω_{Y/S})`,
in the form the wedge filtration consumes**: it is
`Stacks.DeRhamSmooth.pulledBackFormsComparison` followed by the restriction of scalars of the
degree-`n` component of the morphism on exterior algebras induced by `f^*Ω_{Y/S} ⟶ Ω_{X/S}`.

This is the hypothesis `hc` of
`AlgebraicGeometry.SheafOfModules.mapSubobjects_wedgeFiltrationStep_eq_exteriorImageFiltration`,
instantiated at `ρ`. It is
`Stacks.DeRhamPullback.deRhamPullbackChain_f_exteriorPowerPullback` with the second factor split
in two by functoriality of restriction of scalars, the comparison of exterior algebras being the
induced morphism by
`Stacks.DeRhamSmooth.relativeDifferentialFormsComparison_eq_exteriorMap`. -/
theorem deRhamPullbackChain_f_eq_pulledBackFormsComparison_comp (n : ℕ) :
    (Stacks.DeRhamPullback.deRhamPullbackChain f g).f n =
      pulledBackFormsComparison f g n ≫
        (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom
            (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map
          (((pulledBackDifferentialsAlgebras f g).exterior_isExteriorAlgebra.map
            (Scheme.Hom.deRhamAlgebras (f ≫ g)).exterior_isExteriorAlgebra
            (Scheme.Hom.relativeDifferentialsShortComplex f g).f).app (n : ℤ)) := by
  refine Eq.trans (Stacks.DeRhamPullback.deRhamPullbackChain_f_exteriorPowerPullback f g n) ?_
  refine Eq.trans (congrArg
    (fun t => Stacks.DeRhamDirectImage.relativeInverseImageToPullback f g
      (Scheme.Hom.relativeDifferentialForms g (n : ℤ)) ≫ t)
    (_root_.CategoryTheory.Functor.map_comp
      (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom
          (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g))))
      (pulledBackFormsIso f g n).hom
      (((pulledBackDifferentialsAlgebras f g).exterior_isExteriorAlgebra.map
        (Scheme.Hom.deRhamAlgebras (f ≫ g)).exterior_isExteriorAlgebra
        (Scheme.Hom.relativeDifferentialsShortComplex f g).f).app (n : ℤ)))) ?_
  exact (Category.assoc _ _ _).symm

/-! The abelian structures of the two categories of sheaves of modules, named rather than
searched for, exactly as in
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationExteriorStep`. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

/-- **The degree-`m` term of the `k`-th step of the filtration of Section 50.12 is the step at
`k` of the filtration of `Ω^m_{X/S}` by the forms pulled back from `Y`**, for `k ≥ 1`. On the
left the `k`-th step of `Stacks.DeRhamSmooth.deRhamSmoothFiltration`, evaluated in degree `m`;
on the right `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorFiltration` at `k`,
read over the base ring sheaf `(f∘g)^{-1}𝒪_S` and pushed into the degree-`m` term of the
extension by zero of the de Rham complex.

The epimorphy hypothesis is the surjective form of the underived identity of
[Stacks, Tag 08DE]; see the implementation notes. Nothing else is assumed: in particular `f` is
not assumed smooth. -/
theorem mapSubobjects_wedgeFiltrationStep_eq_exteriorFiltration
    (k m : ℕ) (hk0 : 0 < k) (hk : k ≤ m)
    (hepi : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
        (pulledBackFormsComparison f g k)).app
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (f ≫ g)))).X (m - k)) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf) X.sheaf
        (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
        ((pulledBackDifferentialsAlgebras f g).exteriorPower k)
        ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower (m - k)))) :
    (mapSubobjects (HomologicalComplex.eval _ (ComplexShape.up ℤ) (m : ℤ))
          (AlgebraicGeometry.SheafOfModules.deRhamComplexInt
            (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (f ≫ g))))).obj
        (AlgebraicGeometry.SheafOfModules.wedgeFiltrationStep
          (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (f ≫ g)))
          (pulledBackDeRhamComplex f g)
          (Stacks.DeRhamPullback.deRhamPullbackChain f g) (k : ℤ)) =
      (_root_.CategoryTheory.Subobject.map
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex
                (Scheme.Hom.deRhamAlgebras (f ≫ g))
                (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                  (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv).obj
        ((AlgebraicGeometry.SheafOfModules.exteriorPowerSubobjectRestriction
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) m).obj
          (Scheme.Hom.relativeDifferentialsExteriorFiltration f g m k)) :=
  AlgebraicGeometry.SheafOfModules.mapSubobjects_wedgeFiltrationStep_eq_exteriorImageFiltration
    (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))
    (pulledBackDifferentialsAlgebras f g)
    (Scheme.Hom.relativeDifferentialsShortComplex f g).f
    (pulledBackDeRhamComplex f g) (Stacks.DeRhamPullback.deRhamPullbackChain f g)
    (pulledBackFormsComparison f g) (deRhamPullbackChain_f_eq_pulledBackFormsComparison_comp f g)
    k m hk0 hk hepi

end Stacks.DeRhamSmooth

end

module

public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece.KunnethRetraction

/-!
# The graded pieces of the forms of a morphism of schemes

The graded pieces of the wedge filtration instantiated at the transitivity sequence
`0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` of a morphism of schemes: `gr^kΩ^n_{X/S}` and the
splitting-independent comparison onto it, globally and over an open on which the sequence splits.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance] SheafOfModules.monoidalSheaves
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

/-! ### The graded pieces of the forms of a morphism of schemes -/

namespace AlgebraicGeometry.Scheme.Hom

open _root_.AlgebraicGeometry.SheafOfModules

universe v

variable {X Y S : Scheme.{u}}

/-- **`gr^kΩ^n_{X/S}`**, the `k`-th graded piece of the filtration of `Ω^n_{X/S}` by the forms
pulled back from `Y`, for the total degree `n = k + 1 + m`. It is the image of
`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^{1+m}Ω_{X/S}` in `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`, hence
`F^kΩ^n_{X/S}/F^{k+1}Ω^n_{X/S}`
(`SheafOfModules.imageSubobject_exteriorGradedHom_eq`).

No splitting of the transitivity sequence enters: the filtration and its graded pieces are
defined for every `f`. This is the object whose identification with
`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^{n-k}_{X/Y}` is the content of [Stacks, Section 0FMK]. -/
noncomputable abbrev relativeDifferentialsExteriorGraded (f : X ⟶ Y) (g : Y ⟶ S) (k m : ℕ) :
    X.Modules :=
  _root_.SheafOfModules.exteriorGraded
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₂)
    (relativeDifferentialsShortComplex f g).f k m

/-- **The local Künneth comparison onto `gr^kΩ^n_{X/S}`**, attached to a splitting of the
transitivity sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` over an open `U` of `X`:

`⋀^k(f^*Ω_{Y/S})|_U ⊗_{𝒪_U} ⋀^{1+m}(Ω_{X/Y})|_U ⟶ gr^k(Ω^n_{X/S}|_U)`.

`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsSplittingToExteriorGraded_eq` proves that it
does not depend on the chosen splitting. -/
noncomputable abbrev relativeDifferentialsSplittingToExteriorGraded (f : X ⟶ Y) (g : Y ⟶ S)
    (U : X.Opens) (sp : (relativeDifferentialsShortComplexRestrict f g U).Splitting) (k m : ℕ) :=
  _root_.SheafOfModules.splittingToExteriorGraded
    (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
      (relativeDifferentialsShortComplexRestrict f g U).X₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
      (relativeDifferentialsShortComplexRestrict f g U).X₃)
    (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
      (relativeDifferentialsShortComplexRestrict f g U).X₂)
    sp k m

/-- **The local Künneth comparison onto the graded piece of the forms of a morphism of schemes
does not depend on the chosen splitting.** Over an open `U` of `X` any two splittings of
`0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` give the same morphism

`⋀^k(f^*Ω_{Y/S})|_U ⊗ ⋀^{1+m}(Ω_{X/Y})|_U ⟶ gr^k(Ω^n_{X/S}|_U)`,

because they differ by the unipotent transition automorphism of `Ω_{X/S}|_U`, whose `n`-th
exterior power is the identity on the `k`-th step of the filtration modulo the `(k+1)`-st. This
is the agreement of the local Künneth decompositions on the graded piece that
[Stacks, Section 0FMK] uses when it glues them; the decompositions themselves are
`AlgebraicGeometry.Scheme.Hom.exists_isIso_exteriorPowerProdHom_relativeDifferentials` and their
dependence on the splitting is
`AlgebraicGeometry.Scheme.Hom.exteriorPowerProdHom_relativeDifferentials_splitting_eq`. -/
theorem relativeDifferentialsSplittingToExteriorGraded_eq (f : X ⟶ Y) (g : Y ⟶ S) (U : X.Opens)
    (sp sp' : (relativeDifferentialsShortComplexRestrict f g U).Splitting) (k m : ℕ) :
    relativeDifferentialsSplittingToExteriorGraded f g U sp' k m =
      relativeDifferentialsSplittingToExteriorGraded f g U sp k m :=
  _root_.SheafOfModules.splittingToExteriorGraded_eq _ _ _ sp sp' k m

/-- **The splitting-free comparison onto `gr^kΩ^n_{X/S}`, in the shape [Stacks, Section 0FMK]
states it**: for `f : X ⟶ Y` smooth over a base `S` and `n = k + 1 + m`,

`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}`.

No splitting is chosen and nothing is assumed beyond smoothness of `f`: the transitivity sequence
`0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` is short exact
(`AlgebraicGeometry.Scheme.Hom.shortExact_relativeDifferentialsShortComplex`), so
`SheafOfModules.exteriorGradedQuotientComparison` applies, and
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsSplittingToExteriorGraded_eq` says the local
Künneth comparisons all agree with each other.

It is an isomorphism over every open on which the transitivity sequence splits
(`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsExteriorGradedComparisonRestrict`).
That those local isomorphisms glue to make *this* morphism one is
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsExteriorGradedComparison` in
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonGlobal`. -/
noncomputable def relativeDifferentialsExteriorGradedComparison (f : X ⟶ Y) (g : Y ⟶ S)
    [Smooth f] (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (relativeDifferentialsShortComplex f g).X₁).exteriorPower k)).obj
        ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₃).exterior.piece ((m + 1 : ℕ) : ℤ)) ⟶
      relativeDifferentialsExteriorGraded f g k m :=
  have hSE : (relativeDifferentialsShortComplex f g).ShortExact :=
    shortExact_relativeDifferentialsShortComplex f g
      (Stacks.Smooth.formallySmoothScheme_of_smooth f)
  _root_.SheafOfModules.exteriorGradedQuotientComparison
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₃)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₂)
    hSE.exact hSE.epi_g k m

/-- **The comparison onto `gr^kΩ^n_{X/S}` is an epimorphism**, for `f` smooth. [Stacks, Section
0FMK] asserts that it is an isomorphism; the injectivity half is proved over every open on which
the transitivity sequence splits
(`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsExteriorGradedComparisonRestrict`), and
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsSplittingToExteriorGraded_eq` is what makes
those local answers agree; the globalization is
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsExteriorGradedComparison` in
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonGlobal`, which gives invertibility
outright and so subsumes this half. -/
theorem epi_relativeDifferentialsExteriorGradedComparison (f : X ⟶ Y) (g : Y ⟶ S) [Smooth f]
    (k m : ℕ) : Epi (relativeDifferentialsExteriorGradedComparison f g k m) :=
  _root_.SheafOfModules.epi_exteriorGradedQuotientComparison _ _ _ _ _ k m

/-- **The local Künneth comparison onto the graded piece of the forms of a morphism of schemes is
a monomorphism.** It is a split monomorphism, the retraction being
`SheafOfModules.exteriorKunnethRetractionDescent` after the inclusion of the graded piece. -/
theorem mono_relativeDifferentialsSplittingToExteriorGraded (f : X ⟶ Y) (g : Y ⟶ S) (U : X.Opens)
    (sp : (relativeDifferentialsShortComplexRestrict f g U).Splitting) (k m : ℕ) :
    Mono (relativeDifferentialsSplittingToExteriorGraded f g U sp k m) :=
  _root_.SheafOfModules.mono_splittingToExteriorGraded _ _ _ sp k m

/-- **The comparison of [Stacks, Section 0FMK] over an open on which the transitivity sequence
splits**:

`⋀^k(f^*Ω_{Y/S})|_U ⊗_{𝒪_U} Ω^{m+1}_{X/Y}|_U ⟶ gr^k(Ω^n_{X/S}|_U)`,  `n = k + 1 + m`.

No smoothness is needed to state it: a splitting of the restricted sequence makes it short exact
all by itself.
`AlgebraicGeometry.Scheme.Hom.exists_nonempty_splitting_relativeDifferentialsRestrict`
provides such a splitting around every point of a smooth `f`. -/
noncomputable abbrev relativeDifferentialsExteriorGradedComparisonRestrict (f : X ⟶ Y) (g : Y ⟶ S)
    (U : X.Opens) (sp : (relativeDifferentialsShortComplexRestrict f g U).Splitting) (k m : ℕ) :=
  _root_.SheafOfModules.exteriorGradedQuotientComparison
    (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
      (relativeDifferentialsShortComplexRestrict f g U).X₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
      (relativeDifferentialsShortComplexRestrict f g U).X₃)
    (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
      (relativeDifferentialsShortComplexRestrict f g U).X₂)
    sp.exact sp.epi_g k m

/-- **`⋀^k(f^*Ω_{Y/S})|_U ⊗ Ω^{m+1}_{X/Y}|_U ≅ gr^k(Ω^n_{X/S}|_U)`**: the identification of the
graded pieces of [Stacks, Section 0FMK], over an open `U` of `X` on which the transitivity
sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` splits — which, for `f` smooth, is a
neighbourhood of every point
(`AlgebraicGeometry.Scheme.Hom.exists_nonempty_splitting_relativeDifferentialsRestrict`).

The comparison does not depend on the splitting
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsSplittingToExteriorGraded_eq`), so these
identifications agree with each other. That they glue to an isomorphism of the globally defined
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison` is
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsExteriorGradedComparison` in
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonGlobal`. -/
theorem isIso_relativeDifferentialsExteriorGradedComparisonRestrict (f : X ⟶ Y) (g : Y ⟶ S)
    (U : X.Opens) (sp : (relativeDifferentialsShortComplexRestrict f g U).Splitting) (k m : ℕ) :
    IsIso (relativeDifferentialsExteriorGradedComparisonRestrict f g U sp k m) :=
  _root_.SheafOfModules.isIso_exteriorGradedQuotientComparison_of_splitting _ _ _ _ _ sp k m

end AlgebraicGeometry.Scheme.Hom

end

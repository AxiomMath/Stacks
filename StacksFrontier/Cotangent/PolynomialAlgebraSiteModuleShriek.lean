module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriek
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmallOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek of sheaves of modules on the site of a polynomial algebra

Let `A → B` be a ring map, let `π` and `i` be as in Tag 08PR and let `𝒪` be the structure sheaf
of the site `C_{B/A}` of polynomial `A`-algebras augmented to `B`. Tag 08PU identifies the
cotangent complex of Tag 08PN with the derived lower shriek of the sheaf of `B̲`-modules
`i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲`. This file carries that identification at *linear* coefficients:
`L_nπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` is the degree `-n` cohomology of `L_{B/A}` as a `B`-module, and not
merely as an abelian group. It also records the two derived functors in which the source states
Tag 08PU and Tag 08QE — `Lπ_! : D(B̲) ⟶ D(B)` and the `Lπ_! : D(𝒪) ⟶ D(B)` of Tag 09CZ — on the
small model of the footnote-restricted site, and proves Tag 08QE there as an isomorphism in
`D(B)`.

**Which site.** As in `StacksFrontier/Cotangent/PolynomialAlgebraSiteCotangentComplex.lean`, every
statement here about `π_!` is about the point morphism of the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the footnote-restricted site, now with
coefficients in `ModuleCat.{u} B` rather than `AddCommGrpCat.{u}`; the restriction of the sets of
variables is the footnote to the source's section, and it is what makes the site small.

**The terminal object.** The polynomial algebra on no variables is `A`, and its augmentation is
the structure map `A → B`; this is an initial object of the category of augmentations, hence a
terminal object of the site. It is what makes `π^{-1}` have an exact right adjoint — sections
over `A → B` — and hence what proves Tag 08QE in `D(B)`.

## Main definitions

* `CommAlgCat.smallPolynomialCotangentModuleSheaf`: the sheaf `i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` on
  the small model of the restricted site, as a sheaf of `B`-modules.
* `CommAlgCat.boundedPolynomialBaseAugmentation` and `CommAlgCat.smallPolynomialBaseObj`: the
  augmentation `A → B`, as an object of the restricted category of polynomial augmentations and
  of the small model of the restricted site.
* `CommAlgCat.smallPolynomialModuleDerivedLowerShriek`: `Lπ_! : D(B̲) ⟶ D(B)` on the small
  model, the total left derived functor of the colimit at linear coefficients, and
  `CommAlgCat.smallPolynomialCotangentDerivedLowerShriek`: its value `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`, the
  right-hand side of Tag 08PU.
* `CommAlgCat.smallPolynomialDerivedLowerShriekWithCoefficients`: **Tag 09CZ** on the small
  model, `Lπ_! : D(O) ⟶ D(B)` for a sheaf of rings `O` on the site with a map `O ⟶ B̲`.

## Main results

* `CommAlgCat.standardResolutionCotangentModuleMooreComplexIso`: the Moore complex of
  `(i^*Ω_{𝒪/A})(P_•, ε)` for the standard resolution is the complex of `B`-modules underlying
  the cotangent complex of Tag 08PN.
* `CommAlgCat.standardResolutionModuleLeftDerivedCotangentComplexIso`: **Tag 08PU at linear
  coefficients**, read degreewise: the sections at the point of `L_nπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` are the
  degree `-n` cohomology of `L_{B/A}`, as `B`-modules.
* `CommAlgCat.isInitial_boundedPolynomialBaseAugmentation` and
  `CommAlgCat.isTerminal_smallPolynomialBaseObj`: the augmentation `A → B` is initial among
  polynomial `A`-algebras augmented to `B`, hence terminal in the site.
* `CommAlgCat.smallPolynomialModuleDerivedInverseImageCompLowerShriekIso`: **Tag 08QE in
  `D(B)`**, `Lπ_! ∘ π^{-1} = id`, at linear coefficients and on the small model.

## Implementation notes

**What separates the degreewise statement from the source's isomorphism in `D(B)`.** Both sides
of Tag 08PU are available here as objects of `D(B)`: the left-hand side is
`DerivedCategory.Q` of `CommAlgCat.cotangentComplex`, and the right-hand side is
`CommAlgCat.smallPolynomialCotangentDerivedLowerShriek`. What is missing is the *derived* form of
the computation of `Lπ_!` by a resolution, that is, a natural isomorphism
`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)` for a point resolution `U_•`. The computation available is
degreewise, `Stacks.ChaoticSite.ModuleValued.moduleLeftDerivedPointLowerShriekNatIso`: it
identifies `L_nπ_!(ℱ)` with `H_n(ℱ(U_•))` for each `n`, which does not identify the two objects
of `D(B)`, since a complex is not determined by its cohomology. Producing the derived form means
comparing the two filtrations of the double complex obtained by evaluating a projective
resolution of `ℱ` on `U_•` — the Moore complex of `ℱ(U_•)` is the one filtration and
`colim` of the resolution is the other — and that comparison is not in the library. Once it is
available, Tag 08PU in `D(B)` follows by applying `DerivedCategory.Q` to
`CommAlgCat.standardResolutionCotangentModuleMooreComplexIso`, which is already an isomorphism of
complexes of `B`-modules. The step `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}` of the source is the flatness of
`Ω_{𝒪/A}` over `𝒪`, `CommAlgCat.polynomialRelativeDifferentials_isFlat`, with
`CommAlgCat.free_kaehlerDifferential_polynomialSite` as its objectwise form.

**Universes.** Tag 09CZ asks for the site, the coefficient ring and the module sections in one
universe `u`, and the small model of the restricted site satisfies this: it is a genuinely small
category in `Type u`, so `Lπ_!` on sheaves of `B`-modules and the `Lπ_!` of Tag 09CZ are both
formed at `ModuleCat.{u} B`. This is the same convention as the abelian statements at
`AddCommGrpCat.{u}`, and it is why `CommAlgCat.smallPolynomialCotangentModulePresheaf`, whose
sections `B ⊗_{P,α} Ω[P⁄A]` are in `Type u`, is the model of `i^*Ω_{𝒪/A}` used rather than
`CommAlgCat.polynomialRelativeDifferentialsBaseChange`, whose sections are in `Type (u + 1)`.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe u

namespace CommAlgCat

/-! ### `i^*Ω_{𝒪/A}` as a sheaf of `B`-modules -/

section Site

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-- **`i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` as a sheaf of `B`-modules on the small model of the
footnote-restricted site**, with its sections `B ⊗_{P,α} Ω[P⁄A]` kept as `B`-modules rather than
forgotten to abelian groups. It is a sheaf because the topology of `C_{B/A}` is chaotic. -/
def smallPolynomialCotangentModuleSheaf :
    Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialSite A B κ))
      (ModuleCat.{u} (B : Type u)) where
  obj := smallPolynomialCotangentModulePresheaf A B κ
  property := by
    rw [GrothendieckTopology.trivial_eq_bot]
    exact Presheaf.isSheaf_bot _

end Site

/-! ### Tag 08PU at module coefficients -/

section Standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **The Moore complex of `(i^*Ω_{𝒪/A})(P_•, ε)` is the complex of `L_{B/A}`, as `B`-modules.**
For the standard resolution of `B` over `A`, evaluating `i^*Ω_{𝒪/A}` on the cosimplicial object
of the small model gives the simplicial `B`-module of Tag 08PN. -/
def standardResolutionCotangentModuleMooreComplexIso :
    (Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
          (standardResolutionSmallCosimplicialObject A B)).obj
        (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) ≅
      (alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
        (cotangentSimplicialModule.{u, u} A B).object :=
  (alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).mapIso
    (smallResolutionCotangentModuleIso (standardResolution.{u, u} A B).hom
        (standardResolutionVarCardinal A B)
        (standardResolution_isPolynomialAlgebraBelow A B) ≪≫
      standardResolutionOverDifferentialsIso A B)

/-- **Tag 08PU at the small model of the restricted site `C_{B/A}`, with `B`-linear
coefficients.** The sections at the point of `L_nπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` are the degree `-n`
cohomology of the cotangent complex `L_{B/A}` of Tag 08PN, as `B`-modules; here `π` is the point
morphism of the small model of the footnote-restricted site and `Lπ_!` is read degreewise, as
the left derived functors of the `π_!` of Tag 08PF on sheaves of `B`-modules.

The proof is the source's: Tag 08PT at linear coefficients computes `L_nπ_!` on the standard
resolution (`CommAlgCat.standardResolutionModuleLeftDerivedLowerShriekNatIso`), the evaluation of
`Ω_{𝒪/A} ⊗_𝒪 B̲` there is the simplicial `B`-module defining `L_{B/A}`
(`CommAlgCat.standardResolutionCotangentModuleMooreComplexIso`), and the cotangent complex is the
reindexing of that simplicial module's alternating face map complex. -/
@[stacks 08PU "L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) at linear coefficients, for the point morphism \
  of the small model of the footnote-restricted site C_{B/A} and with Lπ_! read degreewise, as \
  the left derived functors of the π_! of Tag 08PF on sheaves of B-modules: the sections at the \
  point of L_nπ_! are the degree -n cohomology of the cotangent complex of Tag 08PN, as \
  B-modules. The source's isomorphism in D(B) needs the derived form of Tag 08PT"]
def standardResolutionModuleLeftDerivedCotangentComplexIso (n : ℕ) :
    (Stacks.ChaoticSite.pointSections.{u, u + 1, u} (ModuleCat.{u} (B : Type u))).obj
        (((Stacks.ChaoticSite.ModuleValued.modulePointLowerShriek
              (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))
              (B : Type u)).leftDerived n).obj
          (smallPolynomialCotangentModuleSheaf A B (standardResolutionVarCardinal A B))) ≅
      (cotangentComplex.{u, u} A B).homology (-(n : ℤ)) :=
  (standardResolutionModuleLeftDerivedLowerShriekNatIso A B n).app
      (smallPolynomialCotangentModuleSheaf A B (standardResolutionVarCardinal A B)) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} (B : Type u))
        (ComplexShape.down ℕ) n).mapIso
      (standardResolutionCotangentModuleMooreComplexIso A B) ≪≫
    (((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
          (cotangentSimplicialModule.{u, u} A B).object).extendHomologyIso
        (ComplexShape.embeddingUpIntLE 0) (j := n) (j' := -(n : ℤ)) (by simp)).symm

end Standard

/-! ### The base algebra as a terminal object of the site -/

section Base

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-- The augmentation `A → B`, as an object of the restricted category of polynomial
augmentations: the polynomial algebra on no variables, augmented by the structure map of `B`. -/
def boundedPolynomialBaseAugmentation : BoundedPolynomialAugmentation A B κ :=
  boundedPolynomialModel A B κ ⟨∅, isEmptyElim⟩

/-- The structure map of an augmentation `α : P → B`, read as a morphism out of the
augmentation `A → B`. -/
def boundedPolynomialBaseHom (X : BoundedPolynomialAugmentation A B κ) :
    boundedPolynomialBaseAugmentation A B κ ⟶ X :=
  ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom (MvPolynomial.aeval (R := A)
      (isEmptyElim : (∅ : Set κ.out) → (X.obj.left : Type u))))
    (CommAlgCat.hom_ext (MvPolynomial.algHom_ext fun i => isEmptyElim i)))

/-- The augmentation `A → B` is initial among polynomial `A`-algebras augmented to `B`: an
augmentation `α : P → B` receives exactly one map from it, the structure map of `P`. -/
def isInitial_boundedPolynomialBaseAugmentation :
    IsInitial (boundedPolynomialBaseAugmentation A B κ) :=
  IsInitial.ofUniqueHom (boundedPolynomialBaseHom A B κ) fun _ _ =>
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext
      (CommAlgCat.hom_ext (MvPolynomial.algHom_ext fun i => isEmptyElim i)))

/-- The augmentation `A → B`, read as an object of the small model of the restricted site
`C_{B/A}`. -/
def smallPolynomialBaseObj : smallBoundedPolynomialSite A B κ :=
  op ((boundedPolynomialAugmentationEquiv A B κ).inverse.obj
    (boundedPolynomialBaseAugmentation A B κ))

/-- The augmentation `A → B` is a terminal object of the small model of the restricted site
`C_{B/A}`, the site being the opposite of the category of augmentations. -/
def isTerminal_smallPolynomialBaseObj : IsTerminal (smallPolynomialBaseObj A B κ) :=
  terminalOpOfInitial (IsInitial.isInitialObj _ _
    (isInitial_boundedPolynomialBaseAugmentation A B κ))

/-- The small model of the restricted site `C_{B/A}` has a terminal object. -/
instance hasTerminal_smallBoundedPolynomialSite :
    HasTerminal (smallBoundedPolynomialSite A B κ) :=
  (isTerminal_smallPolynomialBaseObj A B κ).hasTerminal

end Base

/-! ### Derived lower shriek on `D(B̲)` and on `D(𝒪)` -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-- **Derived lower shriek `Lπ_! : D(B̲) ⟶ D(B)` on the small model of the restricted site
`C_{B/A}`**: the total left derived functor of the colimit over the index category of
`B̲`-modules, which is the `π_!` of Tag 08PF by `Stacks.ChaoticSite.lowerShriekColimitIso`. -/
abbrev smallPolynomialModuleDerivedLowerShriek :
    DerivedCategory ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) ⥤
      DerivedCategory (ModuleCat.{u} (B : Type u)) :=
  Stacks.CategoryHomology.totalDerivedColimit (smallBoundedPolynomialSite A B κ)
    (ModuleCat.{u} (B : Type u))

/-- **`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` in `D(B)`**, the right-hand side of Tag 08PU: derived lower shriek
of the sheaf of `B̲`-modules `i^*Ω_{𝒪/A}`, placed in degree zero. -/
def smallPolynomialCotangentDerivedLowerShriek :
    DerivedCategory (ModuleCat.{u} (B : Type u)) :=
  (smallPolynomialModuleDerivedLowerShriek A B κ).obj
    ((DerivedCategory.singleFunctor _ 0).obj (smallPolynomialCotangentModulePresheaf A B κ))

/-- **Tag 09CZ on the small model of the restricted site `C_{B/A}`.** For a sheaf of rings `O` on
the site and a map `φ : O ⟶ B̲` to the constant sheaf of rings, derived lower shriek with
coefficients in `O` is the exact functor `Lπ_! : D(O) ⟶ D(B)`; all three of the site, the ring
and the module sections live in the universe `u`, as Tag 09CZ requires. -/
abbrev smallPolynomialDerivedLowerShriekWithCoefficients
    (O : (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ RingCat.{u})
    (φ : O ⟶ (Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj
      (RingCat.of (B : Type u))) :
    DerivedCategory (PresheafOfModules.{u} O) ⥤
      DerivedCategory (ModuleCat.{u} (B : Type u)) :=
  Stacks.ChaoticSite.derivedColimitWithCoefficients (B : Type u) O φ

/-- **Tag 08QE in `D(B)` at the small model of the restricted site `C_{B/A}`.** Derived lower
shriek of the inverse image of a `B`-module is that module: `Lπ_!(π^{-1}M) = M` in `D(B)`,
naturally in `M`. Here `π^{-1}` is the constant diagram and `Lπ_!` the total left derived
functor of the colimit, and the proof is that the augmentation `A → B` is a terminal object of
the site, so that `π^{-1}` has the exact right adjoint "sections over `A → B`". -/
@[stacks 08QE "in D(B), at module coefficients: Lπ_!(π^{-1}M) = M for the point morphism of \
  the small model of the footnote-restricted site C_{B/A}, with Lπ_! the total left derived \
  functor of the colimit on D(B̲) and π^{-1} the constant diagram"]
def smallPolynomialModuleDerivedInverseImageCompLowerShriekIso :
    (Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ :
          ModuleCat.{u} (B : Type u) ⥤ _).mapDerivedCategory ⋙
        Stacks.CategoryHomology.totalDerivedColimit (smallBoundedPolynomialSite A B κ)
          (ModuleCat.{u} (B : Type u)) ≅ 𝟭 _ :=
  Stacks.ChaoticSite.derivedConstCompColimitIso _ _ (Or.inr inferInstance)

end Derived

end CommAlgCat

end

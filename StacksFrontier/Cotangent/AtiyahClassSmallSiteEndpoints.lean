module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Cotangent.AtiyahClassSmallSite
public import StacksFrontier.Cotangent.DerivedLowerShriekRestrictedCoefficients
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteDifferentialsShriek
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteModuleShriek
import StacksCore.Tactic.StacksAttribute

/-!
# The displayed endpoints of the Atiyah triangle

The triangle of [Stacks, Tag 09DD] is displayed with its first and third terms identified:

`L_{B/A} ⊗^𝐋_B M → Lπ_!(P¹_{𝒪/A}(M)) → M → L_{B/A} ⊗^𝐋_B M[1]`.

This file identifies the third term, `Lπ_!(M̲) = M`.

The `Lπ_!` of the triangle is the functor `D(𝒪) ⟶ D(B)` of [Stacks, Tag 09CZ], so the
identification is *not* [Stacks, Tag 08QE] directly: 08QE computes
`Lπ_! : D(B̲) ⟶ D(B)`. The passage between the two at a sheaf which is a `B̲`-module is
`Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso`, which rests on the change
of coefficients of [Stacks, Tag 08QJ].

## Main results

* `CommAlgCat.smallPolynomialAtiyahTriangleObj₃Iso`: **`Lπ_!(M̲) = M`** for the Atiyah triangle
  on the small model of `C_{B/A}`.
* `CommAlgCat.smallAtiyahFirstVertexDiagramIso`: **the `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`,
  read as a diagram of `B`-modules, is `M ⊗_B i^*Ω_{𝒪/A}`** — the last step of the first
  displayed identification.

## Implementation notes

**On the sheafification inside `Stacks.sheafTensorRight`, for the first term.** The first term of
the Atiyah triangle is `Lπ_!` of `(Stacks.sheafTensorRight 𝒪 Ω).obj M̲`, and
`Stacks.sheafTensorRight` is by definition "forget to presheaves, tensor objectwise, sheafify"
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExactness.lean`). That last factor looks
like an obstruction on a chaotic site and is not one: every presheaf is a sheaf there, and the
triviality of the sheafification unit is already packaged as
`CategoryTheory.isIso_toSheafify _ (Presheaf.isSheaf_bot _)`, used in exactly this idiom at
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatTwoOutOfThree.lean:202` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LowerShriekForget.lean:359,368`; the
sheaf-of-modules form is
`Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective`. So a reader identifying the
first term should not rebuild it.

**What the first term needed.** That `M̲ ⊗_𝒪 Ω_{𝒪/A}` is the restriction of scalars of a
`B̲`-module — the hypothesis under which
`Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso` applies to the first term
as it does to the third — is `CommAlgCat.smallAtiyahFirstVertexRestrictionIso` below. Its naturality in the object of the
site needs no extra work: the projection formula `Stacks.FlatChangeOfRings.baseChangeNatIso` is already a natural
isomorphism of functors, and its component at the constant `B̲`-module `M` is exactly the needed
identification, with `TensorProduct.AlgebraTensorModule.cancelBaseChange` as its sections.

What that left was the *computation* of the resulting `B̲`-module on the standard resolution:

`Moore((M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A}))(P_•, ε)) ≅ L_{B/A} ⊗_B M`.

Two steps, neither categorical, both proved.

**Step A, the comparison of the two spellings of `Ω_{𝒪/A}` base-changed to `B̲`, is proved.**
`(Stacks.PullbackModel.extendScalars (CommAlgCat.smallPolynomialAugmentationComm _ _ _)).obj
Ω_{𝒪/A}` and `CommAlgCat.smallPolynomialCotangentModulePresheaf` both have sections
`B ⊗_P Ω[P⁄A]`, but the first spells them with
`CommRingCat.KaehlerDifferential (algebraMap A P)`, whose `Algebra A P` instance is
`RingHom.toAlgebra` of the structure map, and the second with `KaehlerDifferential A P` at the
instance `CommAlgCat` carries. (The `Stacks.PullbackModel.extendScalars` form and the
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` form appearing in
`CommAlgCat.smallAtiyahFirstVertexRestrictionIso` below agree on the nose, as do
`(CommAlgCat.smallAtiyahAugmentationComm A B κ).hom` and
`CommAlgCat.smallPolynomialAugmentationComm A B κ`.)

Although the comparison might seem to need constructing through the universal property, it is a
one-line transport along the equality of the two instances. The obstruction is real but local: `CommRingCat.KaehlerDifferential f` is
`letI := f.hom.toAlgebra; ModuleCat.of B (KaehlerDifferential A B)`, and `rw` at the instance
equality does fail with "motive is not type correct", because the instance occurs in the
`SMulCommClass` proof argument `ModuleCat.of` carries and not only in the carrier. What that
rules out is `rw`, not transport: generalising the instance to a *variable* and using `subst`
moves the proof argument along with the carrier and is well-typed. That is
`KaehlerDifferential.congrAlgebraIso`, whose proof is `by subst h; exact Iso.refl _`, with
`KaehlerDifferential.congrAlgebraIso_hom_D` matching the universal derivations. The instance
equality it is applied at is `CommAlgCat.algebraMap_toAlgebra_eq`.

The rest of step A is assembled from that:

* sectionwise, `CommAlgCat.kaehlerDifferentialSectionsIso`, with
  `CommAlgCat.kaehlerDifferentialSectionsIso_hom_d` and
  `CommAlgCat.kaehlerDifferentialSectionsIso_inv_D` on the universal derivations;
* objectwise on the site, `CommAlgCat.extendScalarsDifferentialsObjIso`, whose target is
  `CommAlgCat.overDifferentials`;
* its naturality in the object of the site,
  `CommAlgCat.extendScalarsDifferentialsObjIso_naturality`, checked through
  `CommAlgCat.extendScalarsDifferentialsObjIso_inv_naturality` on the pure differentials
  `1 ⊗ d p` with `CommAlgCat.overDifferentials_hom_ext` and
  `CommAlgCat.overDifferentialsPush_mk`;
* the assembled comparison of underlying abelian presheaves,
  `CommAlgCat.extendScalarsDifferentialsIso`, together with
  `CommAlgCat.smallPolynomialCotangentModulePresheaf_eq` identifying the spelling of its target.

All of these are in `StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentialsShriek.lean`.

**Step B is proved too**, in `StacksFrontier/Cotangent/AtiyahClassSmallSiteMoore.lean`. The
commutation of the extended Moore complex with an additive functor applied degreewise is
`Stacks.ChaoticSite.GeneralValued.mooreCochainMapHomologicalComplexIso`, taken at the functor
`- ⊗_B M`; composed with `CommAlgCat.standardResolutionCotangentMooreCochainIso`, the `M = B`
case, it is `CommAlgCat.smallAtiyahMooreTensorIso`, and
`CommAlgCat.nonempty_cotangentComplexDerivedTensorModule_iso` turns the resulting ordinary tensor
product into `L_{B/A} ⊗^𝐋_B M`, which is
`CommAlgCat.nonempty_smallAtiyahMooreDerivedTensorIso`.

**Nothing is owed now.** `StacksFrontier/Cotangent/AtiyahClassSmallSiteFirstVertexDerived.lean`
runs the whole derived chain and lands `CommAlgCat.smallAtiyahFirstVertexMooreIso`: the first
vertex *is* the extended Moore complex of `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})` on the standard
resolution. The comparison between that `B̲`-module read as a diagram of `B`-modules and
`CommAlgCat.smallPolynomialCotangentModulePresheaf A B κ ⋙ tensorLeft M` is
`CommAlgCat.smallAtiyahFirstVertexDiagramIso` below, and composing the three gives
`CommAlgCat.nonempty_smallAtiyahFirstVertexDerivedTensorIso`, the first displayed
identification.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (moduleSheaves)

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (M : ModuleCat.{u} (B : Type u))

/-- **`Lπ_!(M̲) = M` in `D(B)`: the third term of the Atiyah triangle on the small model of
`C_{B/A}` is `M` itself.** The `Lπ_!` here is the functor `D(𝒪) ⟶ D(B)` of [Stacks, Tag 09CZ];
`Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso` replaces it by
`Lπ_! : D(B̲) ⟶ D(B)` at the `𝒪`-module underlying the constant `B̲`-module `M`, and
[Stacks, Tag 08QE] computes that to be `M`. -/
def smallPolynomialAtiyahTriangleObj₃Iso :
    (smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).obj₃ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (B : Type u)) 0).obj M :=
  (Stacks.Atiyah.lowerShriek (O₂ := smallAtiyahStructureSheaf A B
          (standardResolutionVarCardinal A B)) (B : Type u)
        (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (PresheafOfModules.{u}
        (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B))) 0).app _) ≪≫
    Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso
      (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))
      (standardResolutionSmallCosimplicialObject A B)
      (isPointResolution_standardResolutionSmallCosimplicialObject A B)
      (isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian A B)
      ((Stacks.ChaoticSite.constantModulePresheafEquivalence (B : Type u)).inverse.obj
        ((Functor.const _).obj M)) ≪≫
    (Stacks.CategoryHomology.totalDerivedColimit _ (ModuleCat.{u} (B : Type u))).mapIso
      (DerivedCategory.Q.mapIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        ((Stacks.ChaoticSite.constantModulePresheafEquivalence
          (B : Type u)).counitIso.app ((Functor.const _).obj M)))) ≪≫
    (Stacks.CategoryHomology.totalDerivedColimit _ (ModuleCat.{u} (B : Type u))).mapIso
      (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
        (Functor.const (smallBoundedPolynomialSite A B
          (standardResolutionVarCardinal A B))ᵒᵖ :
            ModuleCat.{u} (B : Type u) ⥤ _) (ComplexShape.up ℤ) 0).app M).symm) ≪≫
    (Stacks.CategoryHomology.totalDerivedColimit _ (ModuleCat.{u} (B : Type u))).mapIso
      (((Functor.const (smallBoundedPolynomialSite A B
        (standardResolutionVarCardinal A B))ᵒᵖ :
          ModuleCat.{u} (B : Type u) ⥤ _).mapDerivedCategoryFactors.app
            ((HomologicalComplex.single (ModuleCat.{u} (B : Type u))
              (ComplexShape.up ℤ) 0).obj M)).symm) ≪≫
    (smallPolynomialModuleDerivedInverseImageCompLowerShriekIso A B
        (standardResolutionVarCardinal A B)).app
      (DerivedCategory.Q.obj ((HomologicalComplex.single (ModuleCat.{u} (B : Type u))
        (ComplexShape.up ℤ) 0).obj M)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} (B : Type u)) 0).app M).symm

/-! ### The first vertex: `M̲ ⊗_𝒪 Ω_{𝒪/A}` is the restriction of a `B̲`-module -/

variable (κ : Cardinal.{u})

/-- The constant sheaf of **commutative** rings `B̲` on the small model of `C_{B/A}`. The
coefficient map of derived lower shriek is a map of presheaves of rings; the projection formula
`Stacks.FlatChangeOfRings.baseChangeNatIso` needs it at the commutative spelling. -/
abbrev smallAtiyahConstantSheaf :
    Sheaf (⊥ : GrothendieckTopology (smallBoundedPolynomialSite A B κ)) CommRingCat.{u} :=
  ⟨(Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj
      ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).obj B), Presheaf.isSheaf_bot _⟩

/-- **The augmentation `𝒪 ⟶ B̲` as a map of sheaves of commutative rings.** Forgetting the
commutativity returns `CommAlgCat.smallPolynomialAugmentation`, on the nose. -/
def smallAtiyahAugmentationComm :
    smallAtiyahStructureSheaf A B κ ⟶ smallAtiyahConstantSheaf A B κ :=
  ⟨{ app X := (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map
        ((smallSiteToOver A B κ).obj X).hom
     naturality := by
       intro X Y f
       exact (congrArg
         (fun g : ((smallSiteToOver A B κ).obj X).left ⟶ B =>
           (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map g)
         (Over.w ((smallSiteToOver A B κ).map f))).trans (Category.comp_id _).symm }⟩

/-- A `B`-module read as a presheaf of modules over the constant presheaf of rings `B̲`. -/
abbrev smallAtiyahModuleOverConstant :
    PresheafOfModules.{u} ((Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj
      (RingCat.of (B : Type u))) :=
  (Stacks.ChaoticSite.constantModulePresheafEquivalence (B : Type u)).inverse.obj
    ((Functor.const _).obj M)

/-- **Piece 1 of the first vertex: `M̲ ⊗_𝒪 Ω_{𝒪/A}` is the `𝒪`-module underlying a
`B̲`-module.** The `B̲`-module is `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`, with sections
`M ⊗_B (B ⊗_P Ω[P⁄A])`, and the identification is the projection formula
`Stacks.FlatChangeOfRings.baseChangeNatIso`, sectionwise
`TensorProduct.AlgebraTensorModule.cancelBaseChange`: `M ⊗_B (B ⊗_P Ω[P⁄A]) ≅ M ⊗_P Ω[P⁄A]`.

This is what lets `Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso` be
applied to the first vertex of the Atiyah triangle, as it is to the third. -/
def smallAtiyahFirstVertexRestrictionIso :
    (Stacks.tensorRight (O := (smallAtiyahStructureSheaf A B κ).obj)
          (smallAtiyahRelativeDifferentialsPresheaf A B κ)).obj
        ((PresheafOfModules.restrictScalars (smallPolynomialAugmentation A B κ)).obj
          (smallAtiyahModuleOverConstant A B M κ)) ≅
      (PresheafOfModules.restrictScalars (smallPolynomialAugmentation A B κ)).obj
        ((Stacks.tensorRight (O := (smallAtiyahConstantSheaf A B κ).obj)
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
            (smallAtiyahAugmentationComm A B κ).hom).obj
              (smallAtiyahRelativeDifferentialsPresheaf A B κ))).obj
          (smallAtiyahModuleOverConstant A B M κ)) :=
  ((Stacks.FlatChangeOfRings.baseChangeNatIso (smallAtiyahAugmentationComm A B κ)
    (smallAtiyahRelativeDifferentialsPresheaf A B κ)).app
      (smallAtiyahModuleOverConstant A B M κ)).symm

/-- **The `B̲`-module attached to `M` by
`Stacks.ChaoticSite.constantModulePresheafEquivalence` has constant sections `M`.** It is
`Stacks.ChaoticSite.constantSectionsModulePresheafIso` at the small model of `C_{B/A}`; the
equivalence being reducible only where it is given, that identification is obtained from its
unit rather than from a reduction. -/
def smallAtiyahModuleOverConstantIso :
    Stacks.ChaoticSite.constantSectionsModulePresheaf
        (C := smallBoundedPolynomialSite A B κ) (B : Type u) M ≅
      smallAtiyahModuleOverConstant A B M κ :=
  Stacks.ChaoticSite.constantSectionsModulePresheafIso
    (C := smallBoundedPolynomialSite A B κ) (B : Type u) M

/-- **`B̲ ⊗_𝒪 Ω_{𝒪/A}` as the Atiyah machinery forms it is the base change of `Ω_{𝒪/A}` along
the augmentation as `StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentialsShriek.lean` forms
it**: the same presheaf of modules, on the nose. The two spellings differ only in which of the
two interchangeable names of the augmentation — `CommAlgCat.smallAtiyahAugmentationComm`, a
morphism of sheaves of commutative rings, and `CommAlgCat.smallPolynomialAugmentationComm`, the
underlying morphism of presheaves — is used to change the coefficients, so this is an identity;
it is stated here because `CommAlgCat.smallAtiyahAugmentationComm` is reducible only in this
file, and it is what lets `CommAlgCat.extendScalarsDifferentialsObjIso` compute the sections of
the former. -/
def smallAtiyahChangeOfRingsDifferentialsIso :
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
        (smallAtiyahAugmentationComm A B κ).hom).obj
          (smallAtiyahRelativeDifferentialsPresheaf A B κ) ≅
      (Stacks.PullbackModel.extendScalars (smallPolynomialAugmentationComm A B κ)).obj
        (smallPolynomialDifferentials A B κ) :=
  Iso.refl _

/-- **The `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`, read as a diagram of `B`-modules, is
`M ⊗_B i^*Ω_{𝒪/A}`**, i.e. `CommAlgCat.smallPolynomialCotangentModulePresheaf` tensored with `M`.
This is the comparison that identifies the first vertex of the Atiyah triangle with the first
displayed term of [Stacks, Tag 09DD]; the extended Moore complex of the right-hand side is
`L_{B/A} ⊗^𝐋_B M` by `CommAlgCat.nonempty_smallAtiyahMooreDerivedTensorIso`.

Both sides have sections `M ⊗_B (B ⊗_P Ω[P⁄A])` over `(P, α)`. The `M` factor of the left-hand
side is reached through `CommAlgCat.smallAtiyahModuleOverConstantIso`, which replaces the
`B̲`-module attached to `M` by the equivalence with the one whose sections are written out, and
`Stacks.ChaoticSite.constantModulePresheafEquivalenceFunctorObjIso` then reads off the sections
of the tensor product. The other factor is `CommAlgCat.extendScalarsDifferentialsObjIso` with
`CommAlgCat.extendScalarsDifferentialsObjIso_naturality`, which apply without bridging because
the Atiyah spelling of `B̲ ⊗_𝒪 Ω_{𝒪/A}` is theirs on the nose
(`CommAlgCat.smallAtiyahChangeOfRingsDifferentialsIso`). -/
def smallAtiyahFirstVertexDiagramIso :
    (Stacks.ChaoticSite.constantModulePresheafEquivalence (B : Type u)).functor.obj
        ((Stacks.tensorRight (O := (smallAtiyahConstantSheaf A B κ).obj)
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
            (smallAtiyahAugmentationComm A B κ).hom).obj
              (smallAtiyahRelativeDifferentialsPresheaf A B κ))).obj
          (smallAtiyahModuleOverConstant A B M κ)) ≅
      smallPolynomialCotangentModulePresheaf A B κ ⋙ MonoidalCategory.tensorLeft M :=
  (Stacks.ChaoticSite.constantModulePresheafEquivalence (B : Type u)).functor.mapIso
      ((Stacks.tensorRight (O := (smallAtiyahConstantSheaf A B κ).obj)
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
          (smallAtiyahAugmentationComm A B κ).hom).obj
            (smallAtiyahRelativeDifferentialsPresheaf A B κ))).mapIso
        (smallAtiyahModuleOverConstantIso A B M κ).symm) ≪≫
    Stacks.ChaoticSite.constantModulePresheafEquivalenceFunctorObjIso (B : Type u) _ _
      (fun V => (MonoidalCategory.tensorLeft M).mapIso
        (extendScalarsDifferentialsObjIso A B κ V))
      (by
        intro V W g
        have key :
            ((Stacks.tensorRight (O := (smallAtiyahConstantSheaf A B κ).obj)
                  ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
                    (smallAtiyahAugmentationComm A B κ).hom).obj
                      (smallAtiyahRelativeDifferentialsPresheaf A B κ))).obj
                (Stacks.ChaoticSite.constantSectionsModulePresheaf
                  (C := smallBoundedPolynomialSite A B κ) (B : Type u) M)).map g ≫
              ((MonoidalCategory.tensorLeft M).mapIso
                (extendScalarsDifferentialsObjIso A B κ W)).hom =
            ((MonoidalCategory.tensorLeft M).mapIso
                (extendScalarsDifferentialsObjIso A B κ V)).hom ≫
              (smallPolynomialCotangentModulePresheaf A B κ ⋙
                MonoidalCategory.tensorLeft M).map g := by
          apply ModuleCat.hom_ext
          apply TensorProduct.ext
          ext a b
          exact congrArg (fun y => a ⊗ₜ[(B : Type u)] y)
            (ConcreteCategory.congr_hom
              (extendScalarsDifferentialsObjIso_naturality A B κ g) b)
        exact fun x => ConcreteCategory.congr_hom key x)

end CommAlgCat

end

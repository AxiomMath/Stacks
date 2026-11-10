module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverseSeparator
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexComparison
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.AcyclicQuasiIso
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.SectionsOverBaseComplexComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RestrictScalarsCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# De Rham cohomology of a morphism of affine schemes

Let `φ : R ⟶ A` be a morphism of commutative rings and let `Spec φ : Spec A ⟶ Spec R` be the
induced morphism of affine schemes. This file proves [Stacks Project, Tag 0FLW]:

* `RΓ(Spec A, Ω^•_{Spec A/Spec R}) = Ω^•_{A/R}` in `D(R)`, and
* `H^i_{dR}(Spec A/Spec R) = H^i(Ω^•_{A/R})`.

The relative de Rham complex `Ω^•_{Spec A/Spec R}` is a complex of sheaves of
`(Spec φ)^{-1}𝒪_{Spec R}`-modules on `Spec A`, and `R` acts on its global sections through
`AlgebraicGeometry.Scheme.Hom.affineBaseRingMap`, so `RΓ` is the unbounded derived functor of
`R`-linear global sections, `Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver`, with
values in `D(R)` — which is the derived category the tag's first assertion names, and `R` is the
ring `H^0(Spec R, 𝒪)` over which the tag's second assertion reads de Rham cohomology.

The proof is the tag's own: the comparison `Γ ⟶ RΓ` is invertible because the terms of
`Ω^•_{Spec A/Spec R}` are acyclic (Serre vanishing on an affine scheme, [Stacks, Tag 01XB]) and
the complex is bounded below (Leray's acyclicity lemma, [Stacks, Tag 015E]); and the complex of
global sections is the algebraic de Rham complex, which is
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamSectionsComplexIso`.

## Main definitions

* `deRhamRingedSpace`: the ringed space `(Spec A, (Spec φ)^{-1}𝒪_{Spec R})`, in which the
  relative de Rham complex of `Spec φ` is a complex of modules over the structure sheaf.
* `derivedDeRhamSections`: `RΓ(Spec A, -) : D((Spec φ)^{-1}𝒪_{Spec R}) ⥤ D(R)`.
* `deRhamComplexInt`: `Ω^•_{Spec A/Spec R}` extended by zero to negative degrees, which is the
  shape in which it is an object of the derived category.
* `deRhamCohomologyOver`: `H^i_{dR}(Spec A/Spec R)`, as an `R`-module.

## Main results

* `derivedDeRhamSectionsIso`: **the first assertion of [Stacks, Tag 0FLW]** —
  `RΓ(Spec A, Ω^•_{Spec A/Spec R}) ≅ Ω^•_{A/R}` in `D(R)`.
* `deRhamCohomologyIsoInt` and `deRhamCohomologyIso`: **the second assertion** —
  `H^i_{dR}(Spec A/Spec R) ≅ H^i(Ω^•_{A/R})`, in every integer degree and, for a degree coming
  from `ℕ`, as the homology of the `ℕ`-indexed complex `Ω^•_{A/R}` itself.
* `rightAcyclic_deRhamComplex_X`: the sheaf `Ω^p_{Spec A/Spec R}` of relative differential
  `p`-forms is right acyclic for `R`-linear global sections.

## Implementation notes

**Where the acyclicity comes from, and why it needs a change of coefficient sheaf.** Serre
vanishing, [Stacks, Tag 01XB], is a statement about a quasi-coherent `𝒪_X`-module; the degree-`p`
term of the relative de Rham complex is the *restriction of scalars* of such a module along
`(Spec φ)^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}` — this is `AlgebraicGeometry.Scheme.Hom.deRhamComplex_X`,
an equality and not merely an isomorphism — and its cohomology is computed in a different abelian
category. The two computations agree by
`Stacks.Cohomology.ModuleComparison.hgroupRestrictScalarsIso`: by [Stacks, Tag 03FD] either one
is computed from the underlying sheaf of abelian groups alone, and restriction of scalars does
not change that sheaf. The quasi-coherence of `Ω^p_{Spec A/Spec R}` is
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms`, which holds for every
morphism of schemes.

**Why the complex is spelled `deRhamComplexNat`.** `AlgebraicGeometry.Scheme.Hom.deRhamComplex`
is ascribed the category of sheaves of modules over
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf ((TopCat.Sheaf.pullback _ f.base).obj
S.sheaf)`, while the derived-sections machinery is stated over
`structureSheafRing (deRhamRingedSpace φ)`. The two are equal by definition, but instance search
does not cross between them: an `Additive` instance declared in one spelling is not found at the
other. `deRhamComplexNat` is the same complex with the second ascription, and it is what the
statements below use.

**The module structure on de Rham cohomology.** `AlgebraicGeometry.SheafOfModules.deRhamCohomology`
in `StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic` is the cohomology of derived
global sections taken over `Γ(X, p^{-1}𝒪_S)`, not over `Γ(S, 𝒪_S)`. The tag reads
`H^i_{dR}(X/S)` as a module over `H^0(S, 𝒪_S)`, which for `S = Spec R` is `R`; that is the
reading used here, and the comparison between the two is a restriction of scalars along
`AlgebraicGeometry.Scheme.Hom.affineBaseRingMap` which the library does not record.

## References

* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen)
open Stacks.Cohomology.DerivedSectionsOverBase
  (sectionsOver derivedSectionsOver derivedSectionsOverUnit sectionsOverComplexComparison
    isIso_sectionsOverComplexComparison_app rightAcyclic_sectionsOver_of_isZero_hgroup)
open Stacks.Cohomology.ModuleComparison (hgroupRestrictScalarsIso)

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentialsIso

attribute [local instance 10000] HasDerivedCategory.standard

variable {R A : CommRingCat.{u}} (φ : R ⟶ A)

/-! ### The ringed space and the base ring -/

/-- **The ringed space `(Spec A, (Spec φ)^{-1}𝒪_{Spec R})`.** Sheaves of modules over its
structure sheaf are the sheaves of `(Spec φ)^{-1}𝒪_{Spec R}`-modules in which the relative de
Rham complex of `Spec φ` lives. -/
abbrev deRhamRingedSpace : RingedSpace.{u, u} :=
  RingedSpace.inverseImage (Spec R).toRingedSpace (Spec.map φ).base

/-- **The base ring map `R ⟶ Γ(Spec A, (Spec φ)^{-1}𝒪_{Spec R})`**, as a ring homomorphism. It
is the comparison along which global sections of the relative de Rham complex are `R`-modules,
and so the ring over which `RΓ(Spec A, Ω^•_{Spec A/Spec R})` is read. -/
abbrev deRhamBaseRingHom :
    ↥R →+* ↥((structureSheafRing (deRhamRingedSpace φ)).obj.obj
      (op (⊤ : Opens (deRhamRingedSpace φ).carrier))) :=
  (Scheme.Hom.affineBaseRingMap φ).hom

/-- **The morphism of sheaves of rings `(Spec φ)^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}`**, along which an
`𝒪_{Spec A}`-module is read as a sheaf of `(Spec φ)^{-1}𝒪_{Spec R}`-modules. The terms of the
relative de Rham complex are the restrictions of scalars of the sheaves of relative differential
forms along it. -/
abbrev deRhamCoefficientMap :=
  _root_.AlgebraicGeometry.SheafOfModules.underlyingRingHom
    (φ := _root_.AlgebraicGeometry.inverseImageStructureMap (Spec.map φ))

/-- Sheaves of `(Spec φ)^{-1}𝒪_{Spec R}`-modules have enough injectives, so their cohomology is
available. The module universe of `Stacks.LargeModuleUniverse.enoughInjectives` is not determined
by its arguments, so it is pinned here rather than left to instance search. -/
instance deRhamRingedSpace_enoughInjectives :
    EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing (deRhamRingedSpace φ))) :=
  Stacks.LargeModuleUniverse.enoughInjectives.{u, u} _

/-- **`R`-linear global sections of a sheaf of `(Spec φ)^{-1}𝒪_{Spec R}`-modules is the functor
whose complex-level lift is `deRhamSectionsComplex`.** The two spellings are the same functor. -/
theorem deRhamSectionsFunctor_eq :
    deRhamSectionsFunctor φ = sectionsOver (deRhamRingedSpace φ) (deRhamBaseRingHom φ) :=
  rfl

/-- The functor of `R`-linear global sections of sheaves of `(Spec φ)^{-1}𝒪_{Spec R}`-modules
is additive. -/
instance deRhamSectionsOver_additive :
    (sectionsOver (deRhamRingedSpace φ) (deRhamBaseRingHom φ)).Additive :=
  deRhamSectionsFunctor_additive φ

/-- The functor of `R`-linear global sections of sheaves of `(Spec φ)^{-1}𝒪_{Spec R}`-modules
preserves zero morphisms. -/
instance deRhamSectionsOver_preservesZeroMorphisms :
    (sectionsOver (deRhamRingedSpace φ) (deRhamBaseRingHom φ)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **`RΓ(Spec A, -) : D((Spec φ)^{-1}𝒪_{Spec R}) ⥤ D(R)`**: the unbounded derived functor of
`R`-linear global sections. This is the `RΓ` of [Stacks Project, Tag 0FLW], landing in the
derived category of `R`-modules. -/
abbrev derivedDeRhamSections :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (deRhamRingedSpace φ))) ⥤
      DerivedCategory (ModuleCat.{u} ↥R) :=
  derivedSectionsOver (deRhamRingedSpace φ) (deRhamBaseRingHom φ)

/-! ### The two complexes -/

/-- `Ω^•_{Spec A/Spec R}`, with its terms ascribed to sheaves of modules over the structure sheaf
of `deRhamRingedSpace φ`. This is `AlgebraicGeometry.Scheme.Hom.deRhamComplex` and not a second
complex: the two ascriptions are equal by definition. -/
abbrev deRhamComplexNat :
    CochainComplex (SheafOfModules.{u} (structureSheafRing (deRhamRingedSpace φ))) ℕ :=
  (Spec.map φ).deRhamComplex

/-- `Ω^•_{Spec A/Spec R}`, extended by zero to negative degrees: the shape in which the relative
de Rham complex is an object of the unbounded derived category. -/
def deRhamComplexInt :
    CochainComplex (SheafOfModules.{u} (structureSheafRing (deRhamRingedSpace φ))) ℤ :=
  (deRhamComplexNat φ).extend ComplexShape.embeddingUpNat

/-- The relative de Rham complex is bounded below: it is extended by zero from a complex indexed
by `ℕ`, so it is concentrated in nonnegative degrees. -/
theorem plus_deRhamComplexInt : CochainComplex.plus _ (deRhamComplexInt φ) :=
  ⟨0, by
    change CochainComplex.IsStrictlyGE
      ((deRhamComplexNat φ).extend ComplexShape.embeddingUpNat) 0
    infer_instance⟩

/-! ### Acyclicity of the sheaves of relative differential forms -/

/-- **Serre vanishing for a quasi-coherent sheaf read over the inverse image of the base
structure sheaf.** For a quasi-coherent `𝒪_{Spec A}`-module `G`, the cohomology groups
`H^q(Spec A, G)` computed in sheaves of `(Spec φ)^{-1}𝒪_{Spec R}`-modules vanish for `q > 0`.

This is [Stacks, Tag 01XB] on the affine scheme `Spec A`, transported along the change of
coefficient sheaf by `Stacks.Cohomology.ModuleComparison.hgroupRestrictScalarsIso`. -/
theorem isZero_hgroup_restrictScalars_of_isQuasicoherent
    (q : ℕ) (hq : 0 < q) (G : (Spec A).Modules) [G.IsQuasicoherent] :
    IsZero (Hgroup (structureSheafRing (deRhamRingedSpace φ)) ⊤ q
      ((_root_.SheafOfModules.restrictScalars (deRhamCoefficientMap φ)).obj G)) :=
  (Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine (Spec A) G q hq).of_iso
    (hgroupRestrictScalarsIso (deRhamCoefficientMap φ) ⊤ q G)

/-- **The sheaf `Ω^p_{Spec A/Spec R}` of relative differential `p`-forms has no higher cohomology
on `Spec A`.** It is the restriction of scalars of a quasi-coherent `𝒪_{Spec A}`-module, by
`AlgebraicGeometry.Scheme.Hom.deRhamComplex_X` together with
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms`. -/
theorem isZero_hgroup_deRhamComplex_X (p : ℕ) (q : ℕ) (hq : 0 < q) :
    IsZero (Hgroup (structureSheafRing (deRhamRingedSpace φ)) ⊤ q ((deRhamComplexNat φ).X p)) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (Spec.map φ) p
  rw [Scheme.Hom.deRhamComplex_X (Spec.map φ) p]
  exact isZero_hgroup_restrictScalars_of_isQuasicoherent φ q hq
    (Scheme.Hom.relativeDifferentialForms (Spec.map φ) (p : ℤ))

/-- **`Ω^p_{Spec A/Spec R}` is right acyclic for `R`-linear global sections**, in every degree
`p`. This is the hypothesis of Leray's acyclicity lemma. -/
theorem rightAcyclic_deRhamComplex_X (p : ℕ) :
    (sectionsOver (deRhamRingedSpace φ) (deRhamBaseRingHom φ)).rightAcyclic
      ((deRhamComplexNat φ).X p) :=
  rightAcyclic_sectionsOver_of_isZero_hgroup (deRhamRingedSpace φ) (deRhamBaseRingHom φ) _
    (isZero_hgroup_deRhamComplex_X φ p)

/-- The extension by zero of the relative de Rham complex has right acyclic terms in every
integer degree: the nonnegative ones carry a sheaf of relative differential forms, the others a
zero object. -/
theorem rightAcyclic_deRhamComplexInt_X (n : ℤ) :
    (sectionsOver (deRhamRingedSpace φ) (deRhamBaseRingHom φ)).rightAcyclic
      ((deRhamComplexInt φ).X n) :=
  Stacks.AcyclicQuasiIso.rightAcyclic_extend_X
    (sectionsOver (deRhamRingedSpace φ) (deRhamBaseRingHom φ))
    (deRhamComplexNat φ) (rightAcyclic_deRhamComplex_X φ) n

/-! ### Tag 0FLW -/

/-- **[Stacks Project, Tag 0FLW], the derived statement.** For a morphism of affine schemes
`Spec φ : Spec A ⟶ Spec R` the algebraic de Rham complex `Ω^•_{A/R}` computes the derived global
sections of the relative de Rham complex:
$$ R\Gamma(\operatorname{Spec} A, \Omega^\bullet_{\operatorname{Spec} A/\operatorname{Spec} R})
  = \Omega^\bullet_{A/R} \quad\text{in } D(R). $$

Both objects are read in `D(R)`: the left-hand side through
`Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver` along the base ring map
`AlgebraicGeometry.Scheme.Hom.affineBaseRingMap`, the right-hand side as the extension by zero of
`KaehlerDifferential.deRhamComplex`.

The comparison is the composite of three isomorphisms: the complex-level comparison
`deRhamSectionsComplexIso` of global differential forms with `Ω^•_{A/R}`, the interchange of
extension by zero with a degreewise functor, and the invertibility of
`Γ ⟶ RΓ` supplied by Leray's acyclicity lemma at a bounded below complex of acyclic terms. -/
@[stacks 0FLW "RΓ(Spec A, Ω^•) ≅ Ω^•_{A/R} in D(R)"]
def derivedDeRhamSectionsIso :
    DerivedCategory.Q.obj ((ringDeRhamComplex φ).extend ComplexShape.embeddingUpNat) ≅
      (derivedDeRhamSections φ).obj (DerivedCategory.Q.obj (deRhamComplexInt φ)) :=
  DerivedCategory.Q.mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} ↥R)).mapIso
          (deRhamSectionsComplexIso φ) ≪≫
        HomologicalComplex.mapHomologicalComplexExtendIso
          (sectionsOver (deRhamRingedSpace φ) (deRhamBaseRingHom φ))
          (deRhamComplexNat φ) ComplexShape.embeddingUpNat) ≪≫
    @asIso _ _ _ _ _ (isIso_sectionsOverComplexComparison_app _ _ (deRhamComplexInt φ)
      (plus_deRhamComplexInt φ) (rightAcyclic_deRhamComplexInt_X φ))

/-- **De Rham cohomology of a morphism of affine schemes**, `H^i_{dR}(Spec A/Spec R)`: the `i`-th
cohomology of the derived global sections of the relative de Rham complex, as an `R`-module. -/
abbrev deRhamCohomologyOver (i : ℤ) : ModuleCat.{u} ↥R :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} ↥R) i).obj
    ((derivedDeRhamSections φ).obj (DerivedCategory.Q.obj (deRhamComplexInt φ)))

/-- **[Stacks Project, Tag 0FLW], the cohomology statement.** De Rham cohomology of a morphism of
affine schemes is the cohomology of the algebraic de Rham complex:
`H^i_{dR}(Spec A/Spec R) = H^i(Ω^•_{A/R})`, in every integer degree. -/
@[stacks 0FLW "H^i_dR(Spec A/Spec R) ≅ H^i(Ω^•_{A/R})"]
def deRhamCohomologyIsoInt (i : ℤ) :
    ((ringDeRhamComplex φ).extend ComplexShape.embeddingUpNat).homology i ≅
      deRhamCohomologyOver φ i :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} ↥R) i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} ↥R) i).mapIso (derivedDeRhamSectionsIso φ)

/-- `deRhamCohomologyIsoInt` in a degree coming from `ℕ`, read on the homology of the `ℕ`-indexed
algebraic de Rham complex `Ω^•_{A/R} = (⋀^•_A Ω[A⁄R], d)` itself. -/
def deRhamCohomologyIso (p : ℕ) :
    (ringDeRhamComplex φ).homology p ≅ deRhamCohomologyOver φ (p : ℤ) :=
  ((ringDeRhamComplex φ).extendHomologyIso ComplexShape.embeddingUpNat
      (j := p) (j' := (p : ℤ)) rfl).symm ≪≫ deRhamCohomologyIsoInt φ (p : ℤ)

end Stacks.AlgebraicGeometry.AffineDifferentialsIso

end

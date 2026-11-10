module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechCohomologyIso
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.RingBase
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.GlobalSectionsOverGamma
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import
 StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.ModuleValuedAlternatingComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived global sections of a flat coherent module over an affine base

Let `A` be a commutative ring, `f : X ⟶ Spec A` a morphism of schemes and `F` a quasi-coherent
`𝒪_X`-module. For a finite family of affine opens covering `X` all of whose finite intersections
are again affine, this file identifies the `A`-linear alternating Čech complex
`Stacks.Cech.alternatingCechModuleComplex` with the derived global sections `RΓ(X, F)`, read as an
object of `D(A)`, and uses the identification to prove
[Stacks, Tag 07VK] (1): if moreover `A` is Noetherian, `f` is proper and `F` is coherent and flat
over `A`, then `RΓ(X, F)` is a perfect object of `D(A)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.derivedGlobalSectionsOverBase`: `RΓ(X, F)`
  as an object of `D(A)`, namely the image under restriction of scalars along
  `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` of the derived global sections over `Γ(X, 𝒪_X)`.
* `…ProperFlatGlobalSections.extendedAlternatingModuleComplex`: the `Γ(X, 𝒪_X)`-linear alternating
  Čech complex of the cover, extended by zero to integer degrees.
* `…ProperFlatGlobalSections.baseAlternatingCechComplex`: its restriction of scalars, an
  `A`-linear complex which `baseAlternatingCechComplexIsoExtend` identifies with the extension by
  zero of `Stacks.Cech.alternatingCechModuleComplex`.
* `…ProperFlatGlobalSections.derivedGlobalSections`: `RΓ(X, F)` over `Γ(X, 𝒪_X)`, as an object of
  the unbounded derived category.

## Main results

* `…ProperFlatGlobalSections.alternatingCechModuleComplexIso`: restriction of scalars along
  `A ⟶ Γ(X, 𝒪_X)` carries the `Γ(X, 𝒪_X)`-linear alternating Čech complex to the `A`-linear one,
  degreewise by the identity, and likewise for the usual Čech complex
  (`cechModuleComplexIso`) and compatibly with the canonical alternating-to-usual inclusion
  (`alternatingCechModuleComplexIso_inclusion`).
* `…ProperFlatGlobalSections.alternatingCechIsoDerivedGlobalSections`: **the alternating Čech
  complex of a cover with affine finite intersections computes derived global sections**, over
  `Γ(X, 𝒪_X)`, as an isomorphism in the unbounded derived category.
* `…ProperFlatGlobalSections.alternatingCechIsoDerivedGlobalSectionsOverBase`: the same
  isomorphism over the base ring `A`.
* `…ProperFlatGlobalSections.flat_baseAlternatingCechComplex_X` and
  `…ProperFlatGlobalSections.hasFlatRepresentative_derivedGlobalSectionsOverBase`: for `F` flat
  over `A` and `f` separated, the model is termwise flat, so `RΓ(X, F)` has a bounded termwise
  flat representative — which is finite Tor dimension. **Unconditional.**
* `…ProperFlatGlobalSections.homologyBaseAlternatingCechComplexIso` and
  `…ProperFlatGlobalSections.homologyDerivedGlobalSectionsOverBaseIso`: the cohomology of
  `RΓ(X, F)` is the homology of the model, and in a nonnegative degree it is `Hⁱ(X, F)`.
* `…ProperFlatGlobalSections.isPseudoCoherent_derivedGlobalSectionsOverBase`: `RΓ(X, F)` is
  pseudo-coherent, conditionally on the affine-base case of [Stacks, Tag 02O5].
* `…ProperFlatGlobalSections.isPerfect_derivedGlobalSectionsOverBase`: **[Stacks, Tag 07VK] (1)**
  for a supplied finite affine cover, conditionally on that same statement.
* `…ProperFlatGlobalSections.isPerfect_derivedGlobalSections`: **[Stacks, Tag 07VK] (1)**, with the
  finite affine cover produced from properness rather than supplied. **Unconditional**: the
  finiteness input is discharged by
  `AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`.

Clause (2) of [Stacks, Tag 07VK] — invertibility of the base-change map
`RΓ(X, F) ⊗^L_A A' ⟶ RΓ(X_{A'}, F_{A'})` — is
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.isIso_derivedGlobalSectionsBaseChangeMap`,
proved out of the `A`-linear Čech model built here: `baseAlternatingCechComplexIsoExtend` puts it
in the shape `Stacks.Cech.cechBaseChangeData` applies to, and
`StacksDraft.PseudoCoherence.isIso_extendScalarsDerivedCounit_app_of_flat` is the
[Stacks, Tag 06XY] step that identifies the ordinary extension of scalars of the model with the
derived one.

## Implementation notes

**The derived-category model.** Every statement below runs under
`CategoryTheory.HasDerivedCategory.standard`, activated here as a local instance, because that is
the model the Čech-to-derived-sections comparison and the finiteness results used here are proved
at. The scheme-wide instance
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` is a different one and results proved under
the two do not unify.

**Why restriction of scalars appears, and where.** `RΓ(X, F)` is intrinsically a complex of
modules over `Γ(X, 𝒪_X)`: it is the right derived functor of
`AlgebraicGeometry.moduleGlobalSections`. Reading it over `A` is postcomposition with
`ModuleCat.restrictScalars` along `Stacks.Cech.globalRingHom f`, which is exactly the functor
appearing in `AlgebraicGeometry.globalSectionsOver_eq_moduleGlobalSections_comp`. Restriction of
scalars is exact, so it induces a functor on unbounded derived categories and commutes with the
localization functor; `derivedGlobalSectionsOverBase` is the resulting object and no comparison of
two derived functors is needed.

**Why the Γ-linear Čech complex is used and not the `A`-linear one directly.** The
Čech-to-derived-sections transformation of [Stacks, Tag 01EQ] is linear over the ring of sections
on the covered open, so the complex it compares against is the `Γ(X, 𝒪_X)`-linear one of
`Stacks.Cohomology.CechSheaf`. Its restriction of scalars is, *degreewise on the nose*, the
`A`-linear complex of `Stacks.Cech`: the two module structures on the same group of cochains are
definitionally equal, which is what `alternatingCechModuleObj_restrictScalars` records. So
termwise flatness and boundedness are imported from the `A`-linear development without any
transport, and `alternatingCechModuleComplexIso` upgrades the degreewise identity to an
isomorphism of complexes, which is the form clause (2) consumes.

**The one hypothesis that is threaded, and where it is discharged.** Pseudo-coherence needs each
`Hⁱ(X, F)` to be a finite `A`-module. That is [Stacks, Tag 02O6], equivalently the affine-base
case of [Stacks, Tag 02O5], and it is carried through the intermediate lemmas below as the `Prop`
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`. Those lemmas
keep it as an explicit hypothesis so that they stay usable with any witness for it, and no
`@[stacks 02O5]` or `@[stacks 02O6]` attribute is attached to anything here. At the tagged
statement `isPerfect_derivedGlobalSections` the hypothesis is **discharged**, by
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`, which proves
that `Prop` with no hypothesis; so [Stacks, Tag 07VK] (1) is unconditional here. The
finite-Tor-dimension half does not need it, and nothing else here is hypothetical.

**Instance synthesis around `Functor.mapHomologicalComplex`.** `ModuleCat` carries several routes
to `CategoryTheory.Limits.HasZeroMorphisms`, and the one the statements below elaborate with is
not the one instance search finds when `Functor.mapHomologicalComplex_obj_d` is applied by `rw`.
The differential identities are therefore proved by `congrArg` against the structure lemmas of
`CochainComplex.of`, which tolerates the definitional difference, rather than by rewriting.

## References

* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Restriction of scalars along the structural map preserves finite limits**: it is the
identity on the underlying abelian groups. -/
local instance preservesFiniteLimits_baseRestriction {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom) :=
  Stacks.Cohomology.CechAcyclic.preservesFiniteLimits_restrictScalars _

/-- **Restriction of scalars along the structural map preserves finite colimits**: it has a left
adjoint, extension of scalars. -/
local instance preservesFiniteColimits_baseRestriction {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom) :=
  ⟨fun _ _ _ => ⟨inferInstance⟩⟩

/-- **Restriction of scalars along the structural map preserves homology**, being exact. -/
local instance preservesHomology_baseRestriction {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) :
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).PreservesHomology :=
  Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars _

section Bridge

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)

/-- **The degree-`p` alternating Čech cochains are the same `A`-module however the action is
built.** Restricting the `Γ(X, 𝒪_X)`-action of
`Stacks.Cohomology.CechSheaf.alternatingCochainModuleObj` along `Stacks.Cech.globalRingHom f`
gives the module `Stacks.Cech.alternatingCechModuleObj` of the `A`-linear development on the
nose. -/
theorem alternatingCechModuleObj_restrictScalars (p : ℕ) :
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        (alternatingCochainModuleObj ⊤ U hU F p) =
      Stacks.Cech.alternatingCechModuleObj f U F p :=
  rfl

/-- The same for the usual Čech cochains. -/
theorem cechModuleObj_restrictScalars (p : ℕ) :
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        (cechCochainModuleObj ⊤ U hU F p) =
      Stacks.Cech.cechModuleObj f U F p :=
  rfl

/-- The differentials of the two alternating Čech complexes agree after restriction of
scalars. -/
theorem alternatingCechModuleComplex_restrictScalars_d (p : ℕ) :
    (((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (alternatingModuleComplex ⊤ U hU F)).d p (p + 1) =
      (Stacks.Cech.alternatingCechModuleComplex f U F).d p (p + 1) :=
  (congrArg (fun g => (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).map g)
      (alternatingModuleComplex_d ⊤ U hU F p)).trans
    (Stacks.Cech.alternatingCechModuleComplex_d f U F p).symm

/-- The differentials of the two usual Čech complexes agree after restriction of scalars. -/
theorem cechModuleComplex_restrictScalars_d (p : ℕ) :
    (((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (cechModuleComplex ⊤ U hU F)).d p (p + 1) =
      (Stacks.Cech.cechModuleComplex f U F).d p (p + 1) :=
  (congrArg (fun g => (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).map g)
      (cechModuleComplex_d ⊤ U hU F p)).trans
    (Stacks.Cech.cechModuleComplex_d f U F p).symm

/-- **Restriction of scalars carries the `Γ(X, 𝒪_X)`-linear alternating Čech complex to the
`A`-linear one**, by the identity in each degree. -/
def alternatingCechModuleComplexIso :
    ((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (alternatingModuleComplex ⊤ U hU F) ≅
      Stacks.Cech.alternatingCechModuleComplex f U F :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro p q (rfl : p + 1 = q)
    rw [Iso.refl_hom, Iso.refl_hom, alternatingCechModuleComplex_restrictScalars_d f U hU F p]
    exact (Category.id_comp ((Stacks.Cech.alternatingCechModuleComplex f U F).d p (p + 1))).trans
      (Category.comp_id ((Stacks.Cech.alternatingCechModuleComplex f U F).d p (p + 1))).symm)

/-- The same comparison for the usual Čech complex. -/
def cechModuleComplexIso :
    ((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechModuleComplex ⊤ U hU F) ≅
      Stacks.Cech.cechModuleComplex f U F :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro p q (rfl : p + 1 = q)
    rw [Iso.refl_hom, Iso.refl_hom, cechModuleComplex_restrictScalars_d f U hU F p]
    exact (Category.id_comp ((Stacks.Cech.cechModuleComplex f U F).d p (p + 1))).trans
      (Category.comp_id ((Stacks.Cech.cechModuleComplex f U F).d p (p + 1))).symm)

/-- **The two comparisons are compatible with the canonical alternating-to-usual Čech
inclusion.** -/
theorem alternatingCechModuleComplexIso_inclusion :
    ((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (alternatingModuleInclusion ⊤ U hU F) ≫
        (cechModuleComplexIso f U hU F).hom =
      (alternatingCechModuleComplexIso f U hU F).hom ≫
        Stacks.Cech.alternatingCechModuleComplex_inclusion f U F := by
  refine HomologicalComplex.hom_ext _ _ (fun p => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  exact (Category.comp_id
      ((((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (alternatingModuleInclusion ⊤ U hU F)).f p)).trans
    (Category.id_comp
      ((Stacks.Cech.alternatingCechModuleComplex_inclusion f U F).f p)).symm

end Bridge

section DerivedIso

variable {X : Scheme.{u}} {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (F : X.Modules)

/-- The `Γ(X, 𝒪_X)`-linear alternating Čech complex, extended by zero to integer degrees. -/
def extendedAlternatingModuleComplex : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} Γ(X, ⊤))).obj
    (alternatingModuleComplex ⊤ U hU F)

/-- The degree-`m` term of the extended complex, for a nonnegative degree. -/
def extendedAlternatingModuleComplexXIso (m : ℕ) :
    (extendedAlternatingModuleComplex U hU F).X (m : ℤ) ≅
      alternatingCochainModuleObj ⊤ U hU F m :=
  (alternatingModuleComplex ⊤ U hU F).extendXIso ComplexShape.embeddingUpNat (i := m)
    (i' := (m : ℤ)) rfl

/-- The extended complex vanishes in every negative degree. -/
theorem isZero_extendedAlternatingModuleComplex_X_of_neg (p : ℤ) (hp : p < 0) :
    IsZero ((extendedAlternatingModuleComplex U hU F).X p) :=
  (alternatingModuleComplex ⊤ U hU F).isZero_extend_X ComplexShape.embeddingUpNat p
    (fun m (hm : (m : ℤ) = p) => by omega)

/-- The canonical inclusion of the extended alternating Čech complex into the extended Čech
complex of [Stacks, Tag 01EQ]. -/
def extendedAlternatingInclusion :
    extendedAlternatingModuleComplex U hU F ⟶
      (cechComplexIntFunctor X.ringCatSheaf ⊤ U hU).obj F :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} Γ(X, ⊤))).map
    (alternatingInclusionToCechComplex ⊤ U hU F)

/-- **[Stacks, Tag 01FM], extended to integer degrees and `Γ(X, 𝒪_X)`-linearly.** The inclusion
of the alternating Čech complex into the Čech complex of the cover is a quasi-isomorphism. -/
instance quasiIso_extendedAlternatingInclusion [LinearOrder I] :
    QuasiIso (extendedAlternatingInclusion U hU F) := by
  have : QuasiIso (alternatingInclusionToCechComplex ⊤ U hU F) :=
    ⟨fun p => quasiIsoAt_alternatingInclusionToCechComplex ⊤ U hU F p⟩
  exact inferInstanceAs
    (QuasiIso (HomologicalComplex.extendMap (alternatingInclusionToCechComplex ⊤ U hU F)
      ComplexShape.embeddingUpNat))

/-- **`RΓ(X, F)` over the ring of global functions**, as an object of the unbounded derived
category: the image of the bounded below derived global sections of [Stacks, Tag 01EQ] under the
inclusion of `D⁺` in `D`. -/
def derivedGlobalSections : DerivedCategory (ModuleCat.{u} Γ(X, ⊤)) :=
  DerivedCategory.Plus.ι.obj ((derivedGlobalSectionsFunctor X.ringCatSheaf ⊤).obj F)

/-- **[Stacks, Tag 01ET] for a cover of a scheme with affine finite intersections.** The
Čech-to-derived-global-sections comparison of [Stacks, Tag 01EQ] is an isomorphism for a
quasi-coherent module and a cover all of whose finite intersections are affine opens. -/
theorem isIso_cechToDerivedGlobalSections [F.IsQuasicoherent]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))) :
    IsIso ((cechToDerivedGlobalSections X.ringCatSheaf ⊤ U hU).app F) :=
  Stacks.Cohomology.CechAcyclic.isIso_cechToDerivedGlobalSections_app
    X.ringCatSheaf ⊤ U hU F (fun r s m hm =>
      (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
          X.ringCatSheaf (⨅ k, U (s k)) m F).2
        (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F
          (⨅ k, U (s k)) (haff r s) m hm))

/-- **The alternating Čech complex computes derived global sections.** For a quasi-coherent
`𝒪_X`-module and a cover of `X` by opens whose finite intersections are affine, the extended
alternating Čech complex of `Γ(X, 𝒪_X)`-modules is isomorphic to `RΓ(X, F)` in the derived
category of `Γ(X, 𝒪_X)`-modules.

This is [Stacks, Tag 01FM] — the alternating complex computes the Čech complex — followed by
[Stacks, Tag 01ET] — the Čech complex of a cover with affine intersections computes cohomology. -/
def alternatingCechIsoDerivedGlobalSections [LinearOrder I] [F.IsQuasicoherent]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))) :
    DerivedCategory.Q.obj (extendedAlternatingModuleComplex U hU F) ≅ derivedGlobalSections F :=
  (@asIso _ _ _ _ (DerivedCategory.Q.map (extendedAlternatingInclusion U hU F))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance)) ≪≫
    DerivedCategory.Plus.ι.mapIso
      (@asIso _ _ _ _ ((cechToDerivedGlobalSections X.ringCatSheaf ⊤ U hU).app F)
        (isIso_cechToDerivedGlobalSections U hU F haff))

end DerivedIso


section OverBase

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)

/-- **`RΓ(X, F)` as an object of `D(A)`.** Derived global sections over `Γ(X, 𝒪_X)`, read over the
base ring by the exact functor induced on unbounded derived categories by restriction of scalars
along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`.

The ring map is `Stacks.Cech.globalRingHom f`, which is the map appearing in
`AlgebraicGeometry.globalSectionsOver_eq_moduleGlobalSections_comp`. -/
def derivedGlobalSectionsOverBase : DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory.obj
    (derivedGlobalSections F)

/-- The `A`-linear model: restriction of scalars of the extended alternating Čech complex of
`Γ(X, 𝒪_X)`-modules. Its degree-`m` term is the degree-`m` term of
`Stacks.Cech.alternatingCechModuleComplex` for every `m : ℕ`, by
`alternatingCechModuleObj_restrictScalars`. -/
def baseAlternatingCechComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  ((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (extendedAlternatingModuleComplex U hU F)

/-- In a nonnegative degree the `A`-linear model is the corresponding term of the `A`-linear
alternating Čech complex of `Stacks.Cech`. -/
def baseAlternatingCechComplexXIso (m : ℕ) :
    (baseAlternatingCechComplex f U hU F).X (m : ℤ) ≅
      (Stacks.Cech.alternatingCechModuleComplex f U F).X m :=
  (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapIso
    (extendedAlternatingModuleComplexXIso U hU F m)

/-- The `A`-linear model vanishes in negative degrees. -/
theorem isZero_baseAlternatingCechComplex_X_of_neg (p : ℤ) (hp : p < 0) :
    IsZero ((baseAlternatingCechComplex f U hU F).X p) :=
  (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).map_isZero
    (isZero_extendedAlternatingModuleComplex_X_of_neg U hU F p hp)

/-- The `A`-linear model is concentrated in nonnegative degrees. -/
instance isStrictlyGE_baseAlternatingCechComplex :
    CochainComplex.IsStrictlyGE (baseAlternatingCechComplex f U hU F) 0 :=
  (CochainComplex.isStrictlyGE_iff _ _).2 (isZero_baseAlternatingCechComplex_X_of_neg f U hU F)

/-- **The `A`-linear model vanishes above the number of members of the cover.** -/
theorem isZero_baseAlternatingCechComplex_X_of_card_le [Fintype I] (p : ℤ)
    (hp : (Fintype.card I : ℤ) ≤ p) : IsZero ((baseAlternatingCechComplex f U hU F).X p) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ p)
  have : Subsingleton (Stacks.Cech.alternatingCechModuleObj f U F m) :=
    Stacks.Cech.subsingleton_alternatingSubmodule f U F (by exact_mod_cast hp)
  refine IsZero.of_iso ?_ (baseAlternatingCechComplexXIso f U hU F m)
  rw [Stacks.Cech.alternatingCechModuleComplex_X]
  exact ModuleCat.isZero_of_subsingleton _

/-- The `A`-linear model is concentrated in degrees at most the cardinality of the index type. -/
instance isStrictlyLE_baseAlternatingCechComplex [Fintype I] :
    CochainComplex.IsStrictlyLE (baseAlternatingCechComplex f U hU F)
      (Fintype.card I : ℤ) :=
  (CochainComplex.isStrictlyLE_iff _ _).2 fun p hp =>
    isZero_baseAlternatingCechComplex_X_of_card_le f U hU F p hp.le

/-- **[Stacks, Tag 01U4] for the Čech model.** For a separated morphism to an affine base and a
quasi-coherent module flat over that base, every term of the `A`-linear model is a flat
`A`-module. -/
theorem flat_baseAlternatingCechComplex_X [Finite I] [IsSeparated f] [F.IsQuasicoherent]
    (hUaff : ∀ i, IsAffineOpen (U i)) (hflat : IsFlatOver f.toLRSHom.toShHom F) (p : ℤ) :
    Module.Flat A ((baseAlternatingCechComplex f U hU F).X p) := by
  rcases lt_or_ge p 0 with hp | hp
  · have hsub : Subsingleton ((baseAlternatingCechComplex f U hU F).X p) :=
      ModuleCat.subsingleton_of_isZero (isZero_baseAlternatingCechComplex_X_of_neg f U hU F p hp)
    exact Module.Flat.of_linearEquiv
      (LinearEquiv.ofBijective (0 : (baseAlternatingCechComplex f U hU F).X p →ₗ[A] (Fin 0 → A))
        ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩)
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    have := Stacks.Cech.alternatingCechModuleComplex_flat f U F hUaff hflat m
    exact Module.Flat.of_linearEquiv (baseAlternatingCechComplexXIso f U hU F m).toLinearEquiv

/-- **The `A`-linear alternating Čech model computes `RΓ(X, F)` in `D(A)`.** Restriction of
scalars is exact, so it commutes with the localization functor; the isomorphism is therefore the
image of `alternatingCechIsoDerivedGlobalSections` under the induced functor on derived
categories. -/
def alternatingCechIsoDerivedGlobalSectionsOverBase [LinearOrder I] [F.IsQuasicoherent]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))) :
    DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU F) ≅
      derivedGlobalSectionsOverBase f F :=
  ((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategoryFactors.app
      (extendedAlternatingModuleComplex U hU F)).symm ≪≫
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory.mapIso
      (alternatingCechIsoDerivedGlobalSections U hU F haff)

/-- **The `A`-linear model is the extension by zero of the `A`-linear alternating Čech complex
of `Stacks.Cech`.** Restriction of scalars commutes with extension by zero
(`Stacks.DerivedIndexing.mapExtendIso`), and on the `ℕ`-indexed complexes the two developments
agree by `alternatingCechModuleComplexIso`. -/
def baseAlternatingCechComplexIsoExtend :
    baseAlternatingCechComplex f U hU F ≅
      (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)).obj
        (Stacks.Cech.alternatingCechModuleComplex f U F) :=
  (@Stacks.DerivedIndexing.mapExtendIso ℕ ℤ (ComplexShape.up ℕ) (ComplexShape.up ℤ)
      (ModuleCat.{u} Γ(X, ⊤)) (ModuleCat.{u} A) _ _ _ _ _ _
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom) inferInstance
      ComplexShape.embeddingUpNat (alternatingModuleComplex ⊤ U hU F)).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)).mapIso
      (alternatingCechModuleComplexIso f U hU F)

include hU in
/-- **`RΓ(X, F)` has finite Tor dimension.** For a separated morphism to an affine base, a finite
family of affine opens covering `X` whose finite intersections are affine, and a quasi-coherent
module flat over the base, the `A`-linear alternating Čech model is a bounded termwise flat
representative of `RΓ(X, F)`, supported in degrees `0` to the number of members of the cover.

This is the finite-Tor-dimension half of [Stacks, Tag 07VK] (1) and needs no Noetherian
hypothesis, no properness and no coherence. -/
theorem hasFlatRepresentative_derivedGlobalSectionsOverBase [Fintype I] [LinearOrder I]
    [IsSeparated f] [F.IsQuasicoherent] (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    StacksDraft.Perfect.HasFlatRepresentative.{u, u} (derivedGlobalSectionsOverBase f F) 0
      (Fintype.card I : ℤ) :=
  ⟨baseAlternatingCechComplex f U hU F,
    flat_baseAlternatingCechComplex_X f U hU F hUaff hflat,
    inferInstance, inferInstance,
    ⟨(alternatingCechIsoDerivedGlobalSectionsOverBase f U hU F haff).symm⟩⟩

end OverBase


section Finiteness

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)

/-- **In a nonnegative degree the homology of the `A`-linear model is the cohomology of `F`.**
Restriction of scalars is exact, extension by zero does not change homology, the alternating Čech
complex computes Čech cohomology ([Stacks, Tag 01FM]) and a cover with affine intersections
computes sheaf cohomology ([Stacks, Tag 01XD]). -/
def homologyBaseAlternatingCechComplexIso [LinearOrder I] [F.IsQuasicoherent]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))) (m : ℕ) :
    (baseAlternatingCechComplex f U hU F).homology (m : ℤ) ≅
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        ((((AlgebraicGeometry.moduleGlobalSections X)).rightDerived m).obj F) :=
  ShortComplex.mapHomologyIso ((extendedAlternatingModuleComplex U hU F).sc (m : ℤ))
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom) ≪≫
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapIso
      ((alternatingModuleComplex ⊤ U hU F).extendHomologyIso ComplexShape.embeddingUpNat
          (j := m) (j' := (m : ℤ)) rfl ≪≫
        alternatingCechHomologyModuleIso ⊤ U hU F m ≪≫
        (Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived X ⊤ U hU haff F m).symm)

include hU in
/-- **[Stacks, Tag 02O6] for the Čech model.** For `A` Noetherian, `f` proper and `F` coherent,
the homology of the `A`-linear alternating Čech model is a finite `A`-module in every nonnegative
degree.

Conditional on `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`,
the affine-base case of [Stacks, Tag 02O5]; see the implementation notes. -/
theorem moduleFinite_homology_baseAlternatingCechComplex [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] [LinearOrder I]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (haffineBase : ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) (m : ℕ) :
    Module.Finite A ((baseAlternatingCechComplex f U hU F).homology (m : ℤ)) := by
  have := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  have hplus : (((Scheme.Modules.pushforward f).rightDerivedPlus (m : ℤ)).obj F).IsCoherent :=
    haffineBase X (Spec (.of A)) f inferInstance inferInstance inferInstance F ‹_› m
  have hnat : (((Scheme.Modules.pushforward f).rightDerived m).obj F).IsCoherent :=
    CoherentDevissage.isCoherent_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) m).app F)
  have hfin : Module.Finite A
      ((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        (((AlgebraicGeometry.moduleGlobalSections X).rightDerived m).obj F)) :=
    ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isCoherent A f F m hnat
  exact Module.Finite.equiv
    (homologyBaseAlternatingCechComplexIso f U hU F haff m).toLinearEquiv.symm

end Finiteness


section Perfect

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)

/-- **The cohomology of `RΓ(X, F)` is the homology of the `A`-linear Čech model**, in every
integer degree. -/
def homologyDerivedGlobalSectionsOverBaseIso [LinearOrder I] [F.IsQuasicoherent]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (derivedGlobalSectionsOverBase f F) ≅
      (baseAlternatingCechComplex f U hU F).homology i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (alternatingCechIsoDerivedGlobalSectionsOverBase f U hU F haff).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app
      (baseAlternatingCechComplex f U hU F)

/-- The cohomology of `RΓ(X, F)` vanishes in a degree where the `A`-linear Čech model does. -/
private theorem isZero_homology_derivedGlobalSectionsOverBase_of_isZero_X [LinearOrder I]
    [F.IsQuasicoherent] (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (i : ℤ) (h : IsZero ((baseAlternatingCechComplex f U hU F).X i)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (derivedGlobalSectionsOverBase f F)) :=
  (ShortComplex.isZero_homology_of_isZero_X₂ _ h).of_iso
    (homologyDerivedGlobalSectionsOverBaseIso f U hU F haff i)

include hU in
/-- **`RΓ(X, F)` has no cohomology above the number of members of the cover.** The `A`-linear Čech
model vanishes there, so its homology does. -/
theorem isZero_homology_derivedGlobalSectionsOverBase_of_card_lt [Fintype I] [LinearOrder I]
    [F.IsQuasicoherent] (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (i : ℤ) (hi : (Fintype.card I : ℤ) < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (derivedGlobalSectionsOverBase f F)) :=
  isZero_homology_derivedGlobalSectionsOverBase_of_isZero_X f U hU F haff i
    (CochainComplex.isZero_of_isStrictlyLE (baseAlternatingCechComplex f U hU F)
      (Fintype.card I : ℤ) i hi)

include hU in
/-- **`RΓ(X, F)` has no cohomology in negative degrees.** -/
theorem isZero_homology_derivedGlobalSectionsOverBase_of_neg [LinearOrder I] [F.IsQuasicoherent]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (derivedGlobalSectionsOverBase f F)) :=
  isZero_homology_derivedGlobalSectionsOverBase_of_isZero_X f U hU F haff i
    (isZero_baseAlternatingCechComplex_X_of_neg f U hU F i hi)

include hU in
/-- **Every cohomology module of `RΓ(X, F)` is a finite `A`-module.** This is [Stacks, Tag 02O6],
conditionally on the affine-base case of [Stacks, Tag 02O5]; in negative degrees the cohomology
vanishes and no hypothesis is used. -/
theorem moduleFinite_homology_derivedGlobalSectionsOverBase [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] [LinearOrder I]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (haffineBase : ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (derivedGlobalSectionsOverBase f F)) := by
  have := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  rcases lt_or_ge i 0 with hi | hi
  · have := ModuleCat.subsingleton_of_isZero
      (isZero_homology_derivedGlobalSectionsOverBase_of_neg f U hU F haff i hi)
    infer_instance
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have := moduleFinite_homology_baseAlternatingCechComplex f U hU F haff haffineBase m
    exact Module.Finite.equiv
      (homologyDerivedGlobalSectionsOverBaseIso f U hU F haff m).toLinearEquiv.symm

include hU in
/-- **`RΓ(X, F)` is pseudo-coherent.** It is bounded above and has finite cohomology in every
degree, which over a Noetherian ring is pseudo-coherence by [Stacks, Tag 066E].

Conditional on `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`;
see the implementation notes. -/
theorem isPseudoCoherent_derivedGlobalSectionsOverBase [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] [Finite I] [LinearOrder I]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (haffineBase : ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (derivedGlobalSectionsOverBase f F) := by
  let _ : Fintype I := Fintype.ofFinite I
  have := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (derivedGlobalSectionsOverBase f F) 0 A).2.1.mpr
    ⟨⟨(Fintype.card I : ℤ), fun i hi =>
        isZero_homology_derivedGlobalSectionsOverBase_of_card_lt f U hU F haff i hi⟩,
      moduleFinite_homology_derivedGlobalSectionsOverBase f U hU F haff haffineBase⟩

include hU in
/-- **[Stacks, Tag 07VK] (1), with a finite affine cover supplied.** For `A` Noetherian,
`f : X ⟶ Spec A` proper and separated, and `F` coherent and flat over `A`, the derived global
sections `RΓ(X, F)` are a perfect object of `D(A)`: they are pseudo-coherent, by finiteness of the
cohomology modules and boundedness ([Stacks, Tag 066E]), and of finite Tor dimension, by the
bounded termwise flat alternating Čech representative; [Stacks, Tag 0658] concludes.

Conditional on `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`,
the affine-base case of [Stacks, Tag 02O5], which `isPerfect_derivedGlobalSections` discharges.
That is the only hypothesis here beyond the source's own, and the finite-Tor-dimension half
(`hasFlatRepresentative_derivedGlobalSectionsOverBase`) does not use it. -/
theorem isPerfect_derivedGlobalSectionsOverBase [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] [Finite I] [LinearOrder I] (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (haffineBase : ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) :
    StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f F) := by
  let _ : Fintype I := Fintype.ofFinite I
  have := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  exact (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u}
      (derivedGlobalSectionsOverBase f F)).1.mpr
    ⟨isPseudoCoherent_derivedGlobalSectionsOverBase f U hU F haff haffineBase,
      0, (Fintype.card I : ℤ),
      hasFlatRepresentative_derivedGlobalSectionsOverBase f U hU F hUaff haff hflat⟩

end Perfect


section Tag

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (F : X.Modules)

/-- **[Stacks, Tag 07VK] (1).** Let `A` be a Noetherian ring, let `f : X ⟶ Spec A` be proper and
let `F` be a coherent `𝒪_X`-module flat over `Spec A`. Then `RΓ(X, F)` is a perfect object of
`D(A)`.

The proof is the source's. Properness makes `X` quasi-compact, so the affine open cover of `X` has
a finite subcover `𝒰`; properness also makes `f` separated, so the finite intersections of members
of `𝒰` are affine. The alternating Čech complex of `𝒰` therefore computes `RΓ(X, F)`
([Stacks, Tag 01FM] and [Stacks, Tag 01ET]), is bounded, and is termwise flat over `A`
([Stacks, Tag 01U4]) — which is finite Tor dimension. Its cohomology modules are finite over `A`,
which is [Stacks, Tag 02O6], so it is pseudo-coherent ([Stacks, Tag 066E]); [Stacks, Tag 0658]
concludes.

**Unconditional.** The finiteness input — the affine-base case of [Stacks, Tag 02O5], carried
through the lemmas above as the `Prop`
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase` — is supplied
here by `AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`, the
hypothesis-free form of that tag. The finite-Tor-dimension half,
`hasFlatRepresentative_derivedGlobalSectionsOverBase`, never needed it. -/
@[stacks 07VK "(1)",
  sga "6 0 3.1" "affine-target flat case",
  sga "6 0 4.1" "special case",
  sga "6 XIV 2.2" "special case"]
theorem isPerfect_derivedGlobalSections [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f F) := by
  classical
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineOpenCover
  let V := C.openCover.finiteSubcover
  let T : X.AffineOpenCover.{u, u} :=
    { I₀ := V.I₀
      X i := C.X (C.openCover.idx i.1)
      f i := C.f (C.openCover.idx i.1)
      idx := V.idx
      covers := V.covers
      map_prop i := C.map_prop (C.openCover.idx i.1) }
  let _ : LinearOrder T.I₀ := linearOrderOfSTO WellOrderingRel
  have hU : (⊤ : X.Opens) = ⨆ i, (T.f i).opensRange := T.openCover.iSup_opensRange.symm
  have hUaff : ∀ i, IsAffineOpen ((T.f i).opensRange) := fun i => isAffineOpen_opensRange (T.f i)
  exact isPerfect_derivedGlobalSectionsOverBase f (fun i => (T.f i).opensRange) hU F hUaff
    (fun _ s => Stacks.Cech.inter_isAffineOpen f (fun i => (T.f i).opensRange) hUaff s) hflat
    ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase.{u}

end Tag

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end

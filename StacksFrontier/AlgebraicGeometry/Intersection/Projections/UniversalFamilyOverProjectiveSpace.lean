module

public import StacksFrontier.AlgebraicGeometry.BaseModuleOnScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModule
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.UniversalEndomorphismFamily
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.RationalMap
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Quasicoherent

/-!
# The universal family of projective transformations over the projective space of endomorphisms

Let `V` be a finite-dimensional vector space over a field `k`, let `E = End(V)` and let
`𝐏 = 𝐏(Eᵛ)` be the projective space of the dual of `E`. The source's universal family of
projective transformations is the partially defined morphism of relative projective spaces
attached to the map of quasi-coherent modules

`ψ : V ⊗ 𝒪_𝐏 ⟶ V ⊗ 𝒪_𝐏(1)`

obtained from the canonical `k`-linear map `V → Eᵛ ⊗ V = Hom(E, V)`, `v ↦ (g ↦ g v)`, and the
canonical `k`-linear map `Eᵛ → Γ(𝐏, 𝒪_𝐏(1))`. This file builds `ψ` and instantiates the general
construction of Tag 07ZG at it, so that the family

`𝐏(V ⊗ 𝒪_𝐏(1)) ⊇ U(ψ) --r_ψ--> 𝐏(V ⊗ 𝒪_𝐏)`

over `𝐏` exists.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceSections.degreeSectionLinear`: **the canonical map
  `Symⁿ(W) → Γ(𝐏(W), 𝒪(n))` as a `k`-linear map**, i.e. as a morphism of `ModuleCat k`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceSections.tensorGlobalSections`: the canonical
  pairing `Γ(𝐏, F) × Γ(𝐏, 𝒪(n)) → Γ(𝐏, F(n))`, bilinear over the global functions.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceSections.sectionPairing`: the `k`-bilinear map
  `W × V → Γ(𝐏(W), V ⊗ 𝒪(1))` it assembles with the two canonical maps.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafMap`: **the map of sheaves `ψ`**.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafDomain`: **the open `U(ψ)`**.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafProjection`: **the family `r_ψ`**.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceSections.structureMorphism_appTop_eq`: **the
  identification of the two scalar actions on the global sections of `𝐏(W)`.** Pulling a scalar
  back along the structure morphism `𝐏(W) ⟶ Spec k` gives the same global function as sending it
  into the degree-zero part of `Sym(W)` and taking the global section of Tag 01M7. This is what
  makes the degreewise section maps of Tag 01MP `k`-linear and not merely additive.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceSections.isQuasicoherent_twist`: a twist of a
  quasi-coherent module on `𝐏(W)` is quasi-coherent, by Tag 0GQM.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafProjection_comp_toBase`: **`r_ψ`
  is a morphism over `𝐏`**, so it is a family of maps of the fibres.

## Implementation notes

The scalar action that `AlgebraicGeometry.moduleSpecΓFunctor` puts on
`Γ(𝐏(W), M)` through `AlgebraicGeometry.projectiveSpaceOfModuleToSpec` is, by construction,
the action of the global function obtained by pulling the scalar back along the structure
morphism; that is `Stacks.AlgebraicGeometry.ProjectiveSpaceSections.smul_eq_scalarSection`, and
it holds by definitional unfolding. The content is
`structureMorphism_appTop_eq`, which identifies that global function with
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroRingToGlobalSections` of the image of
the scalar in `Sym⁰(W)`. Both are sections of the structure sheaf of `Proj`, hence functions into
the degree-zero homogeneous localizations, so they are compared pointwise: the first has value
`c / 1` by `Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val` together with the
naturality of `AlgebraicGeometry.Scheme.ΓSpecIso`, and the second by
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroRingToGlobalSections_stalk`.

With that in hand the degree-`n` section map of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` is `k`-linear, because it is the
`Sym⁰(W)`-linear map `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections`
of Tag 01M7 applied to the shifted module and `Sym⁰(W)` acts on global sections through
`degreeZeroRingToGlobalSections`. The scalar-transport step is isolated as
`degreeSection_smul_of_coe_eq_mul`, stated for an arbitrary graded ring: there the instance
arguments are variables, and the `Sym`-specific instances do not have to be unfolded to see the
degree-zero module structure.

The morphism `ψ` is written through the universal property
`Stacks.AlgebraicGeometry.BaseModuleOnScheme.homEquiv` of `V ⊗ 𝒪_𝐏`, which asks for a `k`-linear
map `V → Γ(𝐏, V ⊗ 𝒪_𝐏(1))`. Since `V ⊗ 𝒪_𝐏(1)` is the sheafified tensor product of `V ⊗ 𝒪_𝐏`
with `𝒪_𝐏(1)`, a global section of it is produced from a pair of global sections by the
sheafification unit; `tensorGlobalSections` packages that as a map bilinear over the global
functions, and `sectionPairing` restricts it to `k` on both sides using the two linearity
statements above. The `k`-linear map out of `V` is then the composite of
`AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndCoeff` with the lift of `sectionPairing`
to `Eᵛ ⊗_k V`.

Quasi-coherence of `V ⊗ 𝒪_𝐏(1)` — needed to feed `ψ` to Tag 07ZG's construction — is Tag 0GQM
for the site of opens of `Proj`, with the quasi-coherence of the twisting sheaf supplied by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_isQuasicoherent` and that of
`V ⊗ 𝒪_𝐏` by Tag 01BG.

Several declarations carry the module of global sections at a fixed spelling of the ring of
global functions (`globalFunctions`, `globalSections`, `twistObj`, `twistStructureSheaf`). The
ring of global functions of `Proj` has two spellings — the commutative one carried by the
structure sheaf and the one the indexing sheaf of rings of a sheaf of modules uses — and instance
search does not cross between them, so the modules a tensor product is formed from have to be
read at one of them throughout.

## What is not done here

The source displays the family with total space `𝐏 × 𝐏(V)` on both sides, using the
identifications `𝐏(V ⊗ 𝒪_𝐏) = 𝐏(V ⊗ 𝒪_𝐏(1)) = 𝐏 × 𝐏(V)`. The **first** of them is made, in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/UniversalFamilyProductSpace.lean`: the
target `𝐏(V ⊗ 𝒪_𝐏)` of the family is the fibre product of `𝐏` with the projective space of `V`
over `Spec k`, by Tag 01O3 over an arbitrary — in particular non-affine — base, which is
`AlgebraicGeometry.projectiveBundleBaseChangeComparison`. Its second factor is presented as the
projective bundle of `Ṽ` over `Spec k` rather than as
`AlgebraicGeometry.projectiveSpaceOfModule k V`; that file's own `What is not done here` records
why those two presentations are not yet identified over `Spec k`.

The **second** identification is not made. It is Tag 02NC, the invariance of a relative
homogeneous spectrum under twisting the graded algebra by an invertible module, and the only form
of it in this repository is the absolute graded-ring one,
`Stacks.GradedRing.InvertibleTwist.projTwistIsoGeneral`, over a commutative ring
rather than over a base scheme. So the *source* `U(ψ) ⊆ 𝐏(V ⊗ 𝒪_𝐏(1))` of the family is not an
open of `𝐏 × 𝐏(V)`, the family is not a partially defined self-map of one scheme, and the fibre
of this family over a point `[g]` of `𝐏` is not compared with `r_g` either; that comparison is
made over the affine cone `𝔸(E) = Spec Sym(Eᵛ)` in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/UniversalEndomorphismFamily.lean`.

## References

* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.BaseModuleOnScheme
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.SheafOfModules.TensorSheafification

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceSections

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable (k W : Type u) [CommRing k] [AddCommGroup W] [Module k W]

/-- The grading of the homogeneous coordinate ring `Sym_k(W)` of `𝐏(W)` by symmetric powers. -/
abbrev grading : ℕ → Submodule k (SymmetricAlgebra k W) :=
  fun n => SymPow.symmetricPower n k W

/-! ### The scalar action on global sections -/

/-- The structure morphism `𝐏(W) ⟶ Spec k` on global sections factors through the degree-zero
part of `Sym_k(W)`: it is `Spec` of `k → Sym⁰_k(W)` followed by
`AlgebraicGeometry.Proj.toSpecZero`. -/
theorem ΓSpecIso_inv_comp_structureMorphism_appTop :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (projectiveSpaceOfModuleToSpec k W).appTop =
      CommRingCat.ofHom (algebraMap k (grading k W 0)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (grading k W 0))).inv ≫
          (Proj.toSpecZero (grading k W)).appTop := by
  rw [Scheme.ΓSpecIso_inv_naturality_assoc, projectiveSpaceOfModuleToSpec]
  simp only [Scheme.Hom.appTop, Scheme.Hom.comp_app, Scheme.Hom.preimage_top]

/-- **A scalar pulled back along the structure morphism of `𝐏(W)` has value `c / 1` at every
point.** -/
theorem structureMorphism_appTop_val (c : k) (x : ProjectiveSpectrum.top (grading k W))
    (hx : x ∈ (⊤ : Opens (ProjectiveSpectrum.top (grading k W)))) :
    HomogeneousLocalization.val
        (((projectiveSpaceOfModuleToSpec k W).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)).1 ⟨x, hx⟩) =
      algebraMap (SymmetricAlgebra k W)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (algebraMap k _ c) := by
  have h := DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (ΓSpecIso_inv_comp_structureMorphism_appTop k W)) c
  refine Eq.trans (congrArg
    (fun s : Γ(AlgebraicGeometry.Proj (grading k W), ⊤) =>
      HomogeneousLocalization.val (s.1 ⟨x, hx⟩)) h) ?_
  refine Eq.trans (toSpecZero_appTop_val (grading k W) (algebraMap k (grading k W 0) c) x) ?_
  rw [SetLike.GradeZero.coe_algebraMap]

/-- The global section of Tag 01M7 attached to a degree-zero element has value `z / 1` at every
point, read in the ambient localization. -/
theorem degreeZeroRingToGlobalSections_val (z : grading k W 0)
    (x : ProjectiveSpectrum.top (grading k W))
    (hx : x ∈ (⊤ : Opens (ProjectiveSpectrum.top (grading k W)))) :
    HomogeneousLocalization.val
        ((degreeZeroRingToGlobalSections (grading k W) z).1 ⟨x, hx⟩) =
      algebraMap (SymmetricAlgebra k W)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (z : SymmetricAlgebra k W) := by
  rw [← Proj.stalkIso'_germ (grading k W) ⊤ x hx
      (degreeZeroRingToGlobalSections (grading k W) z),
    degreeZeroRingToGlobalSections_stalk, ← Localization.mk_one_eq_algebraMap]
  rfl

/-- **The two scalar actions on the global sections of `𝐏(W)` agree.** The global function
obtained by pulling a scalar back along the structure morphism `𝐏(W) ⟶ Spec k` is the global
section of Tag 01M7 attached to the image of that scalar in `Sym⁰_k(W)`. -/
theorem structureMorphism_appTop_eq (c : k) :
    (projectiveSpaceOfModuleToSpec k W).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) =
      degreeZeroRingToGlobalSections (grading k W) (algebraMap k (grading k W 0) c) := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨x, hx⟩ := x
  refine HomogeneousLocalization.val_injective _ ?_
  refine (structureMorphism_appTop_val k W c x hx).trans
    ((degreeZeroRingToGlobalSections_val k W (algebraMap k (grading k W 0) c) x hx).trans
      ?_).symm
  rw [SetLike.GradeZero.coe_algebraMap]

/-- A scalar acts on the global sections of a twist on `𝐏(W)` through the degree-zero global
section attached to its image in `Sym⁰_k(W)`. -/
theorem smul_twistGlobalSections (n : ℕ) (c : k)
    (s : AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGlobalSections (grading k W) n) :
    (c • (show (globalSectionsFunctor (projectiveSpaceOfModuleToSpec k W)).obj
        (twistingSheaf (grading k W) (n : ℤ)) from s) :
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGlobalSections (grading k W) n) =
      degreeZeroRingToGlobalSections (grading k W) (algebraMap k (grading k W 0) c) • s := by
  rw [← structureMorphism_appTop_eq]
  rfl

/-! ### The degree-`n` section map is `k`-linear -/

section Grading

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Scalars of degree zero move through the degree-`n` section map.** If a degree-`n` element
is the product of a degree-zero element with another degree-`n` element, then its global section
of `𝒪(n)` is the corresponding multiple. -/
theorem degreeSection_smul_of_coe_eq_mul (n : ℕ) (z : 𝒮 0) (a b : 𝒮 n)
    (hb : (b : S) = (z : S) * (a : S)) :
    AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 n b =
      degreeZeroRingToGlobalSections 𝒮 z •
        AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 n a := by
  let : Module (𝒮 0)
      ((associatedModuleSheaf 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))).val.obj (op ⊤)) :=
    Module.compHom _ (degreeZeroRingToGlobalSections 𝒮)
  have h : (⟨(b : S), mem_twistGrading_zero 𝒮 b⟩ :
        twistGrading (S := S) 𝒮 (n : ℤ) 0) =
      z • (⟨(a : S), mem_twistGrading_zero 𝒮 a⟩ :
        twistGrading (S := S) 𝒮 (n : ℤ) 0) :=
    Subtype.ext (show (b : S) = (z : S) • (a : S) by rw [hb, smul_eq_mul])
  show degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))
      ⟨(b : S), mem_twistGrading_zero 𝒮 b⟩ = _
  rw [h]
  exact map_smul (degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))) z _

end Grading

/-- The degree-`n` section map on `𝐏(W)` is `k`-homogeneous. -/
theorem degreeSection_smul (n : ℕ) (c : k) (a : grading k W n) :
    AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading k W) n (c • a) =
      degreeZeroRingToGlobalSections (grading k W) (algebraMap k (grading k W 0) c) •
        AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading k W) n a :=
  degreeSection_smul_of_coe_eq_mul (grading k W) n (algebraMap k (grading k W 0) c) a (c • a) (by
    rw [SetLike.GradeZero.coe_algebraMap, Submodule.coe_smul, Algebra.smul_def])

/-- A linear map between the carriers of two objects of `ModuleCat R` as a morphism of that
category. `ModuleCat.ofHom` is stated for `ModuleCat.of`, and the module instance of an object
given by a functor applied to an argument is not found by instance search at that spelling. -/
def ofLinearMap {R : CommRingCat.{u}} {A B : ModuleCat.{u} R} (f : A →ₗ[R] B) : A ⟶ B :=
  ModuleCat.ofHom f

/-- **The canonical map `Symⁿ(W) → Γ(𝐏(W), 𝒪(n))`, as a `k`-linear map**, that is, as a morphism
of `ModuleCat k` for the structure the global sections carry through the structure morphism of
`𝐏(W)`. -/
def degreeSectionLinear (n : ℕ) :
    ModuleCat.of (CommRingCat.of k) (grading k W n) ⟶
      (globalSectionsFunctor (projectiveSpaceOfModuleToSpec k W)).obj
        (twistingSheaf (grading k W) (n : ℤ)) :=
  ofLinearMap
    { toFun := AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading k W) n
      map_add' a b := map_add (degreeSectionHom (grading k W) n) a b
      map_smul' c a := by
        show AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading k W) n (c • a) = _
        rw [degreeSection_smul, ← smul_twistGlobalSections]
        rfl }

/-! ### The pairing of global sections with a twist -/

/-- The structure sheaf of `𝐏(W)` as a presheaf of commutative rings, the form the tensor
product of sheaves of modules is indexed by. -/
abbrev structurePresheaf : (Opens (ProjectiveSpectrum.top (grading k W)))ᵒᵖ ⥤ CommRingCat.{u} :=
  (ProjectiveSpectrum.Proj.structureSheaf (grading k W)).obj

/-- The structure presheaf of `𝐏(W)` is a sheaf of rings. -/
theorem isSheaf_structurePresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (ProjectiveSpectrum.top (grading k W)))
      (structureRingPresheaf (structurePresheaf k W)) :=
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (grading k W)))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (ProjectiveSpectrum.Proj.structureSheaf (grading k W))).property

/-- The ring of global functions on `𝐏(W)`. -/
abbrev globalFunctions : RingCat.{u} :=
  (structureRingPresheaf (structurePresheaf k W)).obj (op ⊤)

/-- The global sections of a module on `𝐏(W)`, as a module over the ring of global
functions. -/
abbrev globalSections (M : (projectiveSpaceOfModule k W).Modules) :
    ModuleCat.{u} (globalFunctions k W) :=
  M.val.obj (op ⊤)

/-- The global function a scalar becomes along the structure morphism of `𝐏(W)`. -/
def scalarSection (c : k) : globalFunctions k W :=
  (projectiveSpaceOfModuleToSpec k W).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)

/-- `F(n)`, the `n`-th twist of a module on `𝐏(W)`. -/
abbrev twistObj (F : (projectiveSpaceOfModule k W).Modules) (n : ℤ) :
    (projectiveSpaceOfModule k W).Modules :=
  twistSheafOfModules (grading k W) F n

/-- `𝒪(n)` on `𝐏(W)`. -/
abbrev twistStructureSheaf (n : ℤ) : (projectiveSpaceOfModule k W).Modules :=
  twistingSheaf (grading k W) n

/-- **The scalar action on the global sections of a module on `𝐏(W)` is the action of the
corresponding global function.** -/
theorem smul_eq_scalarSection (M : (projectiveSpaceOfModule k W).Modules) (c : k)
    (s : ((globalSectionsFunctor (projectiveSpaceOfModuleToSpec k W)).obj M :)) :
    c • s = scalarSection k W c • (show globalSections k W M from s) := rfl

/-- **The canonical pairing `Γ(𝐏, F) × Γ(𝐏, 𝒪(n)) → Γ(𝐏, F(n))`**, bilinear over the global
functions: the sheafification unit of the tensor product, on global sections. -/
def tensorGlobalSections (F : (projectiveSpaceOfModule k W).Modules) (n : ℤ) :
    globalSections k W F →ₗ[globalFunctions k W]
      globalSections k W (twistStructureSheaf k W n) →ₗ[globalFunctions k W]
        globalSections k W (twistObj k W F n) :=
  LinearMap.compr₂
    (TensorProduct.mk (globalFunctions k W) (globalSections k W F)
      (globalSections k W (twistStructureSheaf k W n)))
    (ModuleCat.Hom.hom ((toSheafify (structurePresheaf k W) (isSheaf_structurePresheaf k W)
      ((PresheafOfModules.tensorObj (O := (structurePresheaf k W)) (F.val)
        ((twistingSheaf (grading k W) n).val)))).app (op ⊤)))

/-- **A twist of a quasi-coherent module on `𝐏(W)` is quasi-coherent**, by Tag 0GQM: the twisting
sheaf is quasi-coherent by Tag 01MB and the twist is a tensor product with it. -/
instance isQuasicoherent_twist (F : (projectiveSpaceOfModule k W).Modules)
    [hF : F.IsQuasicoherent] (n : ℤ) : (twistObj k W F n).IsQuasicoherent :=
  letI h₁ : SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules.{u} (structureSheaf (structurePresheaf k W)
        (isSheaf_structurePresheaf k W)) from F) := hF
  letI h₂ : SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules.{u} (structureSheaf (structurePresheaf k W)
        (isSheaf_structurePresheaf k W)) from twistingSheaf (grading k W) n) :=
    associatedModuleSheaf_isQuasicoherent (grading k W) (twistGrading (grading k W) n)
  Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorSheaf'
    (structurePresheaf k W) (isSheaf_structurePresheaf k W) _ _

/-! ### The `k`-bilinear pairing `W × V → Γ(𝐏(W), V ⊗ 𝒪(1))` -/

/-- `W` as the degree-one part of `Sym_k(W)`. -/
def degreeOne : W →ₗ[k] grading k W 1 :=
  (SymmetricAlgebra.ι k W).codRestrict (grading k W 1) fun w => by
    simpa only [SymPow.symmetricPower, pow_one] using
      LinearMap.mem_range_self (SymmetricAlgebra.ι k W) w

variable (V : Type u) [AddCommGroup V] [Module k V]

/-- `V ⊗ 𝒪_{𝐏(W)}`, the constant module of a `k`-module on `𝐏(W)`. -/
abbrev constantModule : (projectiveSpaceOfModule k W).Modules :=
  tensorStructureSheaf (projectiveSpaceOfModuleToSpec k W) (ModuleCat.of (CommRingCat.of k) V)

/-- The global section of `V ⊗ 𝒪_{𝐏(W)}` attached to a vector. -/
def constantSection (v : V) : globalSections k W (constantModule k W V) :=
  toSections (projectiveSpaceOfModuleToSpec k W) (ModuleCat.of (CommRingCat.of k) V) v

/-- The constant section of `V ⊗ 𝒪_{𝐏(W)}` is additive in the vector. -/
theorem constantSection_add (v v' : V) :
    constantSection k W V (v + v') = constantSection k W V v + constantSection k W V v' :=
  map_add _ _ _

/-- The constant section of `c • v` is the global function `c` times the constant section of
`v`. -/
theorem constantSection_smul (c : k) (v : V) :
    constantSection k W V (c • v) = scalarSection k W c • constantSection k W V v :=
  (map_smul (ModuleCat.Hom.hom
    (toSections (projectiveSpaceOfModuleToSpec k W)
      (ModuleCat.of (CommRingCat.of k) V))) c v).trans
    (smul_eq_scalarSection k W (constantModule k W V) c _)

/-- **The canonical `k`-linear map `W → Γ(𝐏(W), 𝒪(1))`**, on elements: the global section of the
first twist attached to a degree-one element. -/
def twistSection (w : W) : globalSections k W (twistStructureSheaf k W ((1 : ℕ) : ℤ)) :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading k W) 1 (degreeOne k W w)

/-- The section of `𝒪(1)` attached to `w ∈ W` is additive in `w`. -/
theorem twistSection_add (w w' : W) :
    twistSection k W (w + w') = twistSection k W w + twistSection k W w' := by
  rw [twistSection, twistSection, twistSection, map_add]
  exact map_add (degreeSectionHom (grading k W) 1) _ _

/-- The section of `𝒪(1)` attached to `c • w` is the global function `c` times the section
attached to `w`. -/
theorem twistSection_smul (c : k) (w : W) :
    twistSection k W (c • w) = scalarSection k W c • twistSection k W w := by
  rw [twistSection, twistSection, map_smul, degreeSection_smul, ← structureMorphism_appTop_eq]
  rfl

/-- **The `k`-bilinear pairing `W × V → Γ(𝐏(W), V ⊗ 𝒪(1))`** out of which `ψ` is written: the
product of the canonical section of `𝒪(1)` attached to `w` with the constant section attached to
`v`. -/
def sectionPairing : W →ₗ[k] V →ₗ[k]
    ((globalSectionsFunctor (projectiveSpaceOfModuleToSpec k W)).obj
      (twistObj k W (constantModule k W V) ((1 : ℕ) : ℤ)) :) where
  toFun w :=
    { toFun v := tensorGlobalSections k W (constantModule k W V) ((1 : ℕ) : ℤ)
        (constantSection k W V v) (twistSection k W w)
      map_add' v v' := by rw [constantSection_add, map_add, LinearMap.add_apply]; rfl
      map_smul' c v := by
        rw [RingHom.id_apply, constantSection_smul, map_smul, LinearMap.smul_apply]
        exact (smul_eq_scalarSection k W
          (twistObj k W (constantModule k W V) ((1 : ℕ) : ℤ)) c _).symm }
  map_add' w w' := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.add_apply]
    show tensorGlobalSections k W (constantModule k W V) ((1 : ℕ) : ℤ)
        (constantSection k W V v) (twistSection k W (w + w')) = _
    rw [twistSection_add, map_add]
    rfl
  map_smul' c w := by
    refine LinearMap.ext fun v => ?_
    rw [RingHom.id_apply, LinearMap.smul_apply]
    show tensorGlobalSections k W (constantModule k W V) ((1 : ℕ) : ℤ)
        (constantSection k W V v) (twistSection k W (c • w)) = _
    rw [twistSection_smul, map_smul]
    exact (smul_eq_scalarSection k W
      (twistObj k W (constantModule k W V) ((1 : ℕ) : ℤ)) c _).symm

end Stacks.AlgebraicGeometry.ProjectiveSpaceSections

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

open Stacks.AlgebraicGeometry.ProjBundleSurjection
open Stacks.AlgebraicGeometry.ProjectiveSpaceSections
open Stacks.SymGraded

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- `Eᵛ`, the dual of the space of endomorphisms of `V`; its projective space `𝐏(Eᵛ)` is the
parameter space of the universal family. -/
abbrev dualEndSpace : Type u := Module.Dual k (V →ₗ[k] V)

/-- **The `k`-linear map `V → Γ(𝐏, V ⊗ 𝒪_𝐏(1))`** of the source: the canonical map
`V → Eᵛ ⊗ V`, `v ↦ (g ↦ g v)`, followed by the pairing of the canonical section of `𝒪_𝐏(1)` with
the constant section. -/
def universalEndSectionMap : ModuleCat.of (CommRingCat.of k) V ⟶
    (globalSectionsFunctor (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))).obj
      (twistObj k (dualEndSpace k V)
        (constantModule k (dualEndSpace k V) V) ((1 : ℕ) : ℤ)) :=
  ofLinearMap (TensorProduct.lift (sectionPairing k (dualEndSpace k V) V) ∘ₗ
    universalEndCoeff k V)

/-- **The map of sheaves `ψ : V ⊗ 𝒪_𝐏 ⟶ V ⊗ 𝒪_𝐏(1)` over the projective parameter space
`𝐏 = 𝐏(Eᵛ)`**, attached by the universal property of `V ⊗ 𝒪_𝐏` to the canonical `k`-linear map
`V → Γ(𝐏, V ⊗ 𝒪_𝐏(1))`. -/
@[stacks 0B2W "ψ : V ⊗ 𝒪_𝐏 → V ⊗ 𝒪_𝐏(1) over the projective parameter space 𝐏 = 𝐏(Eᵛ)"]
def universalEndSheafMap :
    constantModule k (dualEndSpace k V) V ⟶
      twistObj k (dualEndSpace k V) (constantModule k (dualEndSpace k V) V) ((1 : ℕ) : ℤ) :=
  ofSections (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
    (universalEndSectionMap k V)

/-- **The open `U(ψ) ⊆ 𝐏(V ⊗ 𝒪_𝐏(1))`** of the universal family over the projective parameter
space: Tag 07ZG's open for `Sym ψ`. -/
@[stacks 0B2W "U(ψ) ⊆ 𝐏(V ⊗ 𝒪_𝐏(1)) over the projective parameter space 𝐏 = 𝐏(Eᵛ); the \
identification of the twisted total space 𝐏(V ⊗ 𝒪_𝐏(1)) with the displayed 𝐏 × 𝐏(V) is not \
made, that being Tag 02NC over a base scheme, which this repository has only over a \
commutative ring"]
abbrev universalEndSheafDomain :
    (schemeProjectiveBundle
      (twistObj k (dualEndSpace k V) (constantModule k (dualEndSpace k V) V) ((1 : ℕ) : ℤ))
      (isQuasicoherentPieces_of_isQuasicoherent _)).scheme.Opens :=
  bundleMapDomain (universalEndSheafMap k V)

/-- **The universal family of projective transformations over the projective parameter space**,
`𝐏(V ⊗ 𝒪_𝐏(1)) ⊇ U(ψ) --r_ψ--> 𝐏(V ⊗ 𝒪_𝐏)`: the partially defined morphism of relative
projective spaces that Tag 07ZG attaches to `Sym ψ`. -/
@[stacks 0B2W "r_ψ : U(ψ) → 𝐏(V ⊗ 𝒪_𝐏) over the projective parameter space 𝐏 = 𝐏(Eᵛ); the \
target 𝐏(V ⊗ 𝒪_𝐏) is identified with the displayed 𝐏 × 𝐏(V) over 𝐏, but the source \
𝐏(V ⊗ 𝒪_𝐏(1)) is not, that being Tag 02NC over a base scheme, so r_ψ is not yet a partially \
defined self-map of one scheme"]
def universalEndSheafProjection :
    (universalEndSheafDomain k V).toScheme ⟶
      (schemeProjectiveBundle (constantModule k (dualEndSpace k V) V)
        (isQuasicoherentPieces_of_isQuasicoherent _)).scheme :=
  bundleRationalMap (universalEndSheafMap k V)

/-- **The universal family is a family over the parameter space `𝐏`**: `r_ψ` is a morphism over
`𝐏`, so it is a family of maps of the fibres and not merely a morphism of schemes. -/
@[stacks 0B2W "the universal family over 𝐏 = 𝐏(Eᵛ) is a morphism over 𝐏"]
theorem universalEndSheafProjection_comp_toBase :
    universalEndSheafProjection k V ≫
        schemeProjectiveBundleToBase (constantModule k (dualEndSpace k V) V)
          (isQuasicoherentPieces_of_isQuasicoherent _) =
      (universalEndSheafDomain k V).ι ≫
        schemeProjectiveBundleToBase
          (twistObj k (dualEndSpace k V)
            (constantModule k (dualEndSpace k V) V) ((1 : ℕ) : ℤ))
          (isQuasicoherentPieces_of_isQuasicoherent _) :=
  bundleRationalMap_comp_toBase (universalEndSheafMap k V)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end

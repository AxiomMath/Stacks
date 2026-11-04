module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Module.ProjResComplexFlat
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Stalks
public import StacksFrontier.CategoryTheory.Sites.Point.OpensConservativeFamily
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointFiberStalk
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointModuleFiberStalk
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.Local
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Restriction
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictScalars
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Relative Tor amplitude on affine schemes

Let `f : X = Spec A ⟶ S = Spec R` be the morphism of affine schemes corresponding to a ring map
`R → A`, let `M^•` be a complex of `A`-modules and let `E` be the associated object of `D(𝒪_X)`.
Stacks 0DHY compares the Tor amplitude of `E` over `f^{-1}𝒪_S` with the Tor amplitude of `M^•`
over `R`. Its proof reduces the sheaf side to the stalks by Stacks 09U9, identifies the stalk of
`f^{-1}𝒪_S` at a point `q ∈ Spec A` with `R_p` for `p = q ∩ R` and the stalk of `E` with `M^•_q`,
and globalises over the primes of `A` by Stacks 0B67.

This file carries the geometric setting of Stacks 0DHY — the relative ringed space
`(Spec A, f^{-1}𝒪_{Spec R})`, the structure map `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}` and the complex
of `f^{-1}𝒪_{Spec R}`-modules attached to `M^•` — and proves both parts of the comparison.

## Main definitions

* `AlgebraicGeometry.AffineRelativeTorAmplitude.relativeRingedSpace` is the ringed space
  `(Spec A, f^{-1}𝒪_{Spec R})`.
* `AlgebraicGeometry.AffineRelativeTorAmplitude.relativeStructureMap` is the canonical
  homomorphism `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}`.
* `AlgebraicGeometry.AffineRelativeTorAmplitude.relativeComplex` is the complex of
  `f^{-1}𝒪_{Spec R}`-modules attached to a complex of `A`-modules.
* `derTensorSite` is the derived tensor product of a ringed space, read at the
  universe-general ringed-site interface of Stacks 06YU.
* `relativeStalkIso` identifies the stalk of `f^{-1}𝒪_{Spec R}` at a prime `q` of `A` with the
  localisation `R_{q ∩ R}`.
* `relativePointFiberIso` is the same identification, read at the fibre of the point of the site
  of opens attached to `q`.
* `relativeRingStructureMap` and `relativeStalkStructureMap` are `relativeStructureMap` read for
  the underlying sheaves of rings, and the map it induces on the stalks at a prime `q` of `A`.
* `specStalkRingIso` identifies the `RingCat`-valued stalk of `𝒪_{Spec A}` at a prime `q` with
  the localisation `A_q`.
* `extendScalarsCompRestrictScalarsIso` compares extension of scalars along a ring homomorphism
  with extension of scalars along its composite with a ring isomorphism of the target.
* `tildeStalkRestrictScalarsIso` is Stacks 01HV read over a commutative ring isomorphic to the
  stalk ring, which is the form that composes with the fibre functors.
* `fiberToStalkRingHom` is the ring homomorphism `(f^{-1}𝒪_{Spec R})_q ⟶ 𝒪_{Spec A, q}` along
  which a fibre at a prime `q` of `A` is read.
* `relativeFiberFunctorIso` and `relativeFiberDerivedIso` identify the fibre of `relativeComplex`
  at a prime `q` of `A` with `A_q ⊗_A M^•` read over `R_{q ∩ R}`, degreewise and in the derived
  category.

## Main results

* `hasTorAmplitude_relativeComplex_iff`:
  **part (1) of Stacks 0DHY** — the complex of `f^{-1}𝒪_{Spec R}`-modules attached to `M^•` has
  Tor amplitude in `[a, b]` over `f^{-1}𝒪_{Spec R}` exactly when `M^•`, read as a complex of
  `R`-modules, has Tor amplitude in `[a, b]` over `R`.
* `locallyHasFiniteTorDimension_relativeComplex_iff`:
  **part (2) of Stacks 0DHY** — that complex locally has finite Tor dimension exactly when `M^•`,
  read as a complex of `R`-modules, has finite Tor dimension over `R`.
* `hasTorAmplitudeCanonical_derivedModuleFiber_iff`:
  the two sides of Stacks 0DHY agree at a single prime `q` of `A`.
* `hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF`:
  for an arbitrary cochain complex of modules over a commutative ring, Tor amplitude at the
  canonical derived tensor product (Stacks 0652) and the projective-resolution Tor amplitude
  (Stacks 0DJF) are the same condition.
* `hasTorAmplitudeCanonical_restrictScalars_iff_forall_isPrime`:
  a complex of `A`-modules has Tor amplitude in `[a, b]` over `R` exactly when its localisation
  at every prime `q` of `A` has Tor amplitude in `[a, b]` over `R_{q ∩ R}`. This is the module
  side of Stacks 0DHY.
* `locallyHasFiniteTorDimension_iff_hasFiniteTorDimension`:
  on a quasi-compact ringed space an object of `D(𝒪_X)` locally has finite Tor dimension exactly
  when it has finite Tor dimension. This is the step by which part (2) of Stacks 0DHY is reduced
  to part (1).
* `hasTorAmplitude_iff_forall_derivedModuleFiber`:
  Stacks 0DJJ at the derived tensor product of Stacks 06YU on a ringed space — Tor amplitude in
  `[a, b]` holds exactly when it holds at the derived fibre at every point of the site of opens.
  This is the sheaf side of Stacks 0DHY.
* `hasTorAmplitude_iff_forall_pointFiber`:
  the same criterion with only the *topological* points of `X` quantified over, those being a
  conservative family of points of the site of opens.
* `inverseImageStalkIso_inv_comp_eq_stalkMap`:
  the stalk map of `f : Spec A ⟶ Spec R` at a prime `q` of `A` factors through the stalk of
  `f^{-1}𝒪_{Spec R}`, the second factor being the stalk map of
  `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}`.
* `relativeStalkIso_inv_comp`:
  consequently that stalk map is, through `relativeStalkIso` and `Spec.stalkIso`, the
  localisation map `R_{q ∩ R} ⟶ A_q`.
* `specStalkRingIso_comp_commRingFiberStalkHom_eq_algebraMap`:
  the same identification at the fibre of the point of the site of opens attached to `q` and at
  the `RingCat`-valued stalks the module API uses: the ring homomorphism over which the fibre of
  `E` at `q` is a module is `algebraMap R_{q ∩ R} A_q` for
  `Localization.AtPrime.algebraOfLiesOver`, which is the algebra structure
  `StacksDraft.TorAmplitude.HasTorAmplitudeAt` measures Tor amplitude over.
* `specStalkRingIso_comp_germ_eq_algebraMap`:
  the companion identification on the other side, that the germ map `A ⟶ 𝒪_{Spec A, q}` is
  `algebraMap A A_q`.

## Implementation notes

The sheaf-level Tor-amplitude predicates used here are
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude` and its relatives, whose derived tensor product
is *pinned* to the canonical one of Stacks 06YU on the site of opens; no certificate is
quantified over, so none of the statements below is weakened by a degenerate derived tensor
product.

`derTensorSite` bridges the two derived-tensor-product interfaces. The ringed-site
form of Stacks 0DJJ is phrased for `Stacks.SheafOfModules.DerivedTensorProduct`, whose K-flat
side conditions read `Stacks.SheafOfModules.IsKFlat`, whereas the pinned
`Stacks.Cohomology.TorAmplitude.derTensor` inhabits
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, whose read
`Stacks.SheafOfModules.KFlat.KFlat`. The two predicates are the same condition on the site of
opens of a ringed space, so the whole structure transports field by field with the same
bifunctor, and the Tor-amplitude predicates of the two interfaces are then the same
proposition.

The fibre at a prime `q` of `A` is identified in three steps, each of which is an isomorphism of
functors transported degreewise by `CategoryTheory.NatIso.mapHomologicalComplex` and then to the
derived category by `CategoryTheory.Functor.mapDerivedCategoryFactors`: the fibre at the point of
the site of opens is the stalk (`Opens.moduleFiberStalkFunctorIsoOfCommRing`), the stalk does not
see a restriction of scalars
(`AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsFunctorIso`), and the stalk of an
associated sheaf is a base change along the germ map (Stacks 01HV).

`tildeStalkRestrictScalarsIso` exists because `Stacks.TildeStalk.tildeStalkFunctorIso` is stated
with the commutativity of the `RingCat`-valued stalk ring seated inside its right-hand side, so
that composing it with a restriction of scalars out of `ModuleCat 𝒪_{Spec A,q}` is not possible
directly. Pushing the base change along a ring isomorphism of the stalk ring by
`extendScalarsCompRestrictScalarsIso` removes the stalk ring from the coefficients of the base
change, and the resulting statement needs no `CommRing` instance on the stalk.

The additivity of `Stacks.sheafModuleFiberOfCommRing` is seated by hand inside
`relativeFiberDerivedIso`, together with the two exactness instances and the resulting
`PreservesZeroMorphisms` instances of the composites. Instance synthesis cannot find them here:
the sheaf argument is `(relativeRingedSpace R A).sheaf`, whose type is spelled `TopCat.Sheaf`
over a carrier that only unfolds at default transparency, so the generic instance does not match
at the transparency instance search uses.

The canonical-versus-projective-resolution bridge is proved for an *arbitrary* complex, not only
a bounded above one: `StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF` asks the
complex to be K-flat, bounded above and termwise flat, whereas
`CochainComplex.KFlat.exists_kFlat_resolution` resolves any complex by a K-flat one with no bound,
and at a K-flat complex the comparison field of
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` computes the derived tensor product
against the K-flat projective resolution of the module directly.

The two Tor-amplitude conventions used here are not the same spelling: the sheaf-level and the
Stacks 0652 predicates say `i ∉ Set.Icc a b`, while the Stacks 0DJF predicate says
`i < a ∨ b < i`. The translation is done explicitly where the two meet.

## References

* [Stacks Project, Lemma 36.10.4 (Tag 0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Lemma 20.48.9 (Tag 0DJJ)](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Section 20.26 (Tag 06YU)](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Lemma 15.66.11 (Tag 0B67)](https://stacks.math.columbia.edu/tag/0B67)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Definition 15.66.1 (Tag 0652)](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Lemma 15.66.2 (Tag 0DJF)](https://stacks.math.columbia.edu/tag/0DJF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect

universe u

namespace AlgebraicGeometry.AffineRelativeTorAmplitude

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **The morphism of affine schemes `Spec A ⟶ Spec R`** determined by the `R`-algebra
structure of `A`. -/
@[ega "IV 1.9.2"]
abbrev specMap : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- **The relative ringed space of `R → A`**: the space `Spec A` equipped with the inverse
image `f^{-1}𝒪_{Spec R}` of the structure sheaf of `Spec R` along `f : Spec A ⟶ Spec R`. This is
the ringed space over which the relative Tor amplitude of Stacks 0DHY is measured. -/
def relativeRingedSpace : RingedSpace.{u, u} :=
  RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace (specMap R A).base

/-- **The canonical homomorphism `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}`**: the morphism of sheaves of
rings adjoint, under the inverse-image/direct-image adjunction, to the structure-sheaf datum
`𝒪_{Spec R} ⟶ f_*𝒪_{Spec A}` of the morphism of schemes `f`. It is the homomorphism along which
an `𝒪_{Spec A}`-module is read as a module over `f^{-1}𝒪_{Spec R}`. -/
def relativeStructureMap :
    (relativeRingedSpace R A).sheaf ⟶ (Spec (CommRingCat.of A)).sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (specMap R A).base).homEquiv
      (Spec (CommRingCat.of R)).sheaf (Spec (CommRingCat.of A)).sheaf).symm
    ⟨(specMap R A).toLRSHom.toShHom.hom.c⟩

/-- **The complex of `f^{-1}𝒪_{Spec R}`-modules attached to a complex `M^•` of `A`-modules**:
the termwise associated sheaf `(M^n)^~` on `Spec A`, with scalars restricted along
`relativeStructureMap`. This is the object called `E` in Stacks 0DHY, read over
`f^{-1}𝒪_{Spec R}`. -/
def relativeComplex (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (OXMod.{u} (relativeRingedSpace R A)) ℤ :=
  ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology (Spec (CommRingCat.of A)).carrier)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (relativeStructureMap R A))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((tilde.functor (CommRingCat.of A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)

section ModuleSide

open StacksDraft.TorAmplitude CochainComplex.DerivedTensor CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

variable {S : Type u} [CommRing S]

/-- **The augmentation of the chosen projective resolution of `N` onto `N[0]` is a
quasi-isomorphism.** -/
private lemma projResComplex_quasiIso (N : ModuleCat.{u} S) :
    QuasiIso ((ProjectiveResolution.of N).π' :
      FaithfullyFlat.projResComplex N ⟶
        (CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N) := by
  show QuasiIso (HomologicalComplex.extendMap (ProjectiveResolution.of N).π
    ComplexShape.embeddingDownNat ≫ _)
  have hπ : QuasiIso (ProjectiveResolution.of N).π := ProjectiveResolution.quasiIso _
  have hπ' : QuasiIso (HomologicalComplex.extendMap (ProjectiveResolution.of N).π
      ComplexShape.embeddingDownNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 hπ
  infer_instance

/-- A quasi-isomorphism of cochain complexes induces an isomorphism on the cohomology in each
degree. -/
private noncomputable def homologyIsoOfQuasiIso
    {K L : CochainComplex (ModuleCat.{u} S) ℤ} (f : K ⟶ L) (hf : QuasiIso f) (i : ℤ) :
    K.homology i ≅ L.homology i :=
  have := hf
  have _h : IsIso (HomologicalComplex.homologyMap f i) :=
    (quasiIsoAt_iff_isIso_homologyMap f i).mp inferInstance
  asIso (HomologicalComplex.homologyMap f i)

/-- **For a K-flat complex `P`, the cohomology of `P ⊗^{L}_S N[0]` is the cohomology of the
termwise tensor product of `P` with a projective resolution of `N`.** Both `P` and the resolution
are K-flat, so the comparison field of the canonical derived tensor product identifies the
derived tensor product with the total tensor complex; the resolution is then replaced by `N[0]`
along its augmentation, which the localization functor inverts. -/
private noncomputable def canonicalHomologyIsoOfKFlat
    (P : CochainComplex (ModuleCat.{u} S) ℤ) (hP : P.KFlat) (N : ModuleCat.{u} S) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj
        (((canonicalDerivedTensorProduct S).tensor.obj (DerivedCategory.Q.obj P)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj N)) ≅
      FaithfullyFlat.derivedTensorHomology P N i :=
  have hL := FaithfullyFlat.projResComplex_kFlat N
  have hπ := projResComplex_quasiIso N
  have _hiso : IsIso (DerivedCategory.Q.map (ProjectiveResolution.of N).π') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} S) _).2 hπ
  (DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).mapIso
      (((canonicalDerivedTensorProduct S).tensor.obj (DerivedCategory.Q.obj P)).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app N ≪≫
          (asIso (DerivedCategory.Q.map (ProjectiveResolution.of N).π')).symm) ≪≫
        (canonicalDerivedTensorProduct S).comparison P (FaithfullyFlat.projResComplex N)
          hP hL) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) i).app _

/-- Tor amplitude at the canonical derived tensor product, written with the three certificate
arguments of Stacks 0652 spelled out. Both readings are equivalent to the flat-representative
condition of Stacks 0654, which is how they are compared. -/
private theorem hasTorAmplitudeCanonical_iff_explicit
    (E : DerivedCategory (ModuleCat.{u} S)) (a b : ℤ) :
    HasTorAmplitudeCanonical S E a b ↔
      HasTorAmplitude (canonicalDerivedTensorProduct S).tensor (canonicalTensorComparison S)
        (canonicalTensorIsLeftDerived S) E a b :=
  (hasTorAmplitudeCanonical_iff_hasFlatRepresentative S E a b).trans
    (hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison S)
      (canonicalTensorIsLeftDerived S) E a b).symm

/-- **For a K-flat complex, the Tor amplitude of Stacks 0652 is the Tor amplitude of Stacks
0DJF.** Both sides are the vanishing of the same cohomology modules outside `[a, b]`, in the two
conventions `i ∉ Set.Icc a b` and `i < a ∨ b < i`. -/
private theorem hasTorAmplitudeCanonical_iff_0DJF_of_kFlat
    (P : CochainComplex (ModuleCat.{u} S) ℤ) (hP : P.KFlat) (a b : ℤ) :
    HasTorAmplitudeCanonical S (DerivedCategory.Q.obj P) a b ↔
      FaithfullyFlat.HasTorAmplitude P a b := by
  rw [hasTorAmplitudeCanonical_iff_explicit]
  refine forall_congr' fun N => forall_congr' fun i => ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le]
  exact imp_congr_right fun _ => (canonicalHomologyIsoOfKFlat P hP N i).isZero_iff

/-- **The Tor amplitude of Stacks 0DJF depends only on the quasi-isomorphism class of the
complex.** Tensoring with the projective resolution of a module is tensoring with a K-flat
complex, so it carries a quasi-isomorphism to a quasi-isomorphism. -/
private theorem hasTorAmplitude0DJF_of_quasiIso
    {K L : CochainComplex (ModuleCat.{u} S) ℤ} (f : K ⟶ L) (hf : QuasiIso f) (a b : ℤ) :
    FaithfullyFlat.HasTorAmplitude K a b ↔ FaithfullyFlat.HasTorAmplitude L a b := by
  have key : ∀ (N : ModuleCat.{u} S) (i : ℤ),
      FaithfullyFlat.derivedTensorHomology K N i ≅
        FaithfullyFlat.derivedTensorHomology L N i := fun N i =>
    homologyIsoOfQuasiIso ((tensorRight (FaithfullyFlat.projResComplex N)).map f)
      (quasiIso_tensorRight_map (FaithfullyFlat.projResComplex_kFlat N) f) i
  exact ⟨fun h N i hi => (key N i).isZero_iff.mp (h N i hi),
    fun h N i hi => (key N i).isZero_iff.mpr (h N i hi)⟩

/-- Tor amplitude at the canonical derived tensor product depends only on the isomorphism class
of the object in `D(S)`, since by Stacks 0654 it is the existence of a flat representative. -/
private theorem hasTorAmplitudeCanonical_of_iso
    {K L : DerivedCategory (ModuleCat.{u} S)} (e : K ≅ L) (a b : ℤ)
    (h : HasTorAmplitudeCanonical S K a b) : HasTorAmplitudeCanonical S L a b := by
  rw [hasTorAmplitudeCanonical_iff_hasFlatRepresentative] at h ⊢
  exact hasFlatRepresentative_of_iso e h


/-- Tor amplitude at the canonical derived tensor product depends only on the isomorphism class
of the object in `D(S)`. -/
private theorem hasTorAmplitudeCanonical_iff_of_iso
    {K L : DerivedCategory (ModuleCat.{u} S)} (e : K ≅ L) (a b : ℤ) :
    HasTorAmplitudeCanonical S K a b ↔ HasTorAmplitudeCanonical S L a b :=
  ⟨BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b,
    BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b⟩

/-- **Tor amplitude at the canonical derived tensor product (Stacks 0652) and the
projective-resolution Tor amplitude (Stacks 0DJF) are the same condition, for an arbitrary
cochain complex of `S`-modules.**

Both predicates are invariant under quasi-isomorphism of the complex, so the comparison may be
made at a K-flat resolution of `K`, where it is `hasTorAmplitudeCanonical_iff_0DJF_of_kFlat`. No
bound on the complex is assumed. -/
public theorem hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonical S (DerivedCategory.Q.obj K) a b ↔
      FaithfullyFlat.HasTorAmplitude K a b := by
  obtain ⟨P, f, hP, -, hf, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} K
  have hiso : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} S) f).2 hf
  rw [← hasTorAmplitude0DJF_of_quasiIso f hf a b,
    ← hasTorAmplitudeCanonical_iff_0DJF_of_kFlat P hP a b]
  exact (hasTorAmplitudeCanonical_iff_of_iso (asIso (DerivedCategory.Q.map f)) a b).symm

end ModuleSide

section AtPrimes

open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-- **The module side of Stacks 0DHY.** A complex `M^•` of `A`-modules, read as a complex of
`R`-modules, has Tor amplitude in `[a, b]` over `R` if and only if for every prime `q` of `A`
the localisation of `M^•` at `q` has Tor amplitude in `[a, b]` over `R_{q ∩ R}`.

This is Stacks 0B67 read at the canonical derived tensor product of Stacks 0BYI, the translation
between the two Tor-amplitude spellings being
`hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF`. -/
public theorem hasTorAmplitudeCanonical_restrictScalars_iff_forall_isPrime
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) a b ↔
      ∀ (q : Ideal A) [q.IsPrime], HasTorAmplitudeAt R M q a b :=
  (hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b).trans
    (hasTorAmplitude_iff_localized_at_primes_iff_maximals R A M a b).1

end AtPrimes

section Compact

open Stacks.Cohomology.TorAmplitude
open AlgebraicGeometry.RingedSpace.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] restrictModules_preservesFiniteLimits
  restrictModules_preservesFiniteColimits

variable {X : RingedSpace.{u, u}}

/-- **On a quasi-compact ringed space, locally finite Tor dimension is finite Tor dimension.**
An object of `D(𝒪_X)` whose restriction to each member of some open covering has Tor amplitude in
some interval has Tor amplitude in a single interval on all of `X`.

A finite subcover exists by quasi-compactness, the finitely many intervals are contained in one
interval `[a₀, b₀]`, and Tor amplitude in a fixed interval is local on an open covering. The
converse is that Tor amplitude restricts to an open subspace.

This is the step by which part (2) of Stacks 0DHY — locally finite Tor dimension on
`(Spec A, f^{-1}𝒪_{Spec R})` — is reduced to part (1), the space `Spec A` being quasi-compact. -/
public theorem locallyHasFiniteTorDimension_iff_hasFiniteTorDimension [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u} X)) :
    LocallyHasFiniteTorDimension X E ↔ HasFiniteTorDimension X E := by
  classical
  constructor
  · rintro ⟨I, U, hsup, hfin⟩
    choose a b hab using hfin
    have hc : (Set.univ : Set X.carrier) ⊆ ⋃ i, (U i : Set X.carrier) := fun x _ =>
      Set.mem_iUnion.mpr (Opens.mem_iSup.mp (show x ∈ iSup U by rw [hsup]; trivial))
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
      (fun i => (U i : Set X.carrier)) (fun i => (U i).isOpen) hc
    obtain ⟨a₀, ha₀⟩ := (t.finite_toSet.image a).bddBelow
    obtain ⟨b₀, hb₀⟩ := (t.finite_toSet.image b).bddAbove
    refine ⟨a₀, b₀, hasTorAmplitude_of_iSup_eq_top X E a₀ b₀
      (fun i : (t : Set I) => U i.val) ?_ fun i => ?_⟩
    · refine le_antisymm le_top fun x _ => ?_
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
      obtain ⟨hit, hxi⟩ := Set.mem_iUnion.mp hi
      exact Opens.mem_iSup.mpr ⟨⟨i, hit⟩, hxi⟩
    · have hlow : a₀ ≤ a i.val := ha₀ ⟨i.val, i.property, rfl⟩
      have hhigh : b i.val ≤ b₀ := hb₀ ⟨i.val, i.property, rfl⟩
      exact fun F j hj => hab i.val F j fun hmem =>
        hj ⟨hlow.trans hmem.1, hmem.2.trans hhigh⟩
  · intro h
    exact ⟨PUnit, fun _ => ⊤, by simp, fun _ => hasFiniteTorDimension_restrictModules ⊤ E h⟩

end Compact

section DerivedTensorBridge

universe d

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- `HasDerivedCategory` at the spelling of the universe-general ringed-site interface, for the
same reason. -/
local instance hasDerivedCategorySiteModules :
    HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules.{u, u, u} X.ringedSite) :=
  inferInstanceAs (HasDerivedCategory.{d} (OXMod.{u} X))

/-- **The derived tensor product of a ringed space, read at the universe-general ringed-site
interface.** A ringed space is the ringed site of its opens, and the two spellings of
K-flatness for complexes of sheaves of modules — `Stacks.SheafOfModules.IsKFlat` and
`Stacks.SheafOfModules.KFlat.KFlat` — are the same condition there, so the canonical derived
tensor product of Stacks 06YU transports field by field, with the same bifunctor. -/
def derTensorSite :
    Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X.ringedSite where
  tensor := (Stacks.Cohomology.TorAmplitude.derTensor X).tensor
  comparison K L hK hL := (Stacks.Cohomology.TorAmplitude.derTensor X).comparison K L hK hL
  comparison_naturality f g hK hK' hL hL' :=
    (Stacks.Cohomology.TorAmplitude.derTensor X).comparison_naturality f g hK hK' hL hL'
  comparisonRight K L hL := (Stacks.Cohomology.TorAmplitude.derTensor X).comparisonRight K L hL
  comparisonRight_naturality f g hL hL' :=
    (Stacks.Cohomology.TorAmplitude.derTensor X).comparisonRight_naturality f g hL hL'
  comparisonRight_eq_comparison K L hK hL :=
    (Stacks.Cohomology.TorAmplitude.derTensor X).comparisonRight_eq_comparison K L hK hL
  comparisonLeft K L hK := (Stacks.Cohomology.TorAmplitude.derTensor X).comparisonLeft K L hK
  comparisonLeft_naturality f g hK hK' :=
    (Stacks.Cohomology.TorAmplitude.derTensor X).comparisonLeft_naturality f g hK hK'
  comparisonLeft_eq_comparison K L hK hL :=
    (Stacks.Cohomology.TorAmplitude.derTensor X).comparisonLeft_eq_comparison K L hK hL
  toTensor K L := (Stacks.Cohomology.TorAmplitude.derTensor X).toTensor K L
  toTensor_naturality f g := (Stacks.Cohomology.TorAmplitude.derTensor X).toTensor_naturality f g
  toTensor_eq_comparisonRight K L hL :=
    (Stacks.Cohomology.TorAmplitude.derTensor X).toTensor_eq_comparisonRight K L hL
  toTensor_eq_comparisonLeft K L hK :=
    (Stacks.Cohomology.TorAmplitude.derTensor X).toTensor_eq_comparisonLeft K L hK
  commShift₂ := (Stacks.Cohomology.TorAmplitude.derTensor X).commShift₂
  exact_left L := (Stacks.Cohomology.TorAmplitude.derTensor X).exact_left L
  exact_right K := (Stacks.Cohomology.TorAmplitude.derTensor X).exact_right K

end DerivedTensorBridge

section StalkwiseCriterion

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSpace.{u, u})

/-- **Tor amplitude at the derived tensor product of Stacks 06YU is detected at the fibres of
the points of the site of opens.** An object `E` of `D(𝒪_X)` has Tor amplitude in `[a, b]` if
and only if, for every point `Φ` of the site of opens of `X`, the derived fibre of `E` at `Φ`
has Tor amplitude in `[a, b]` over the fibre `𝒪_Φ` of the structure sheaf.

This is Stacks 0DJJ read at `Stacks.Cohomology.TorAmplitude.derTensor` through
`derTensorSite`. The side condition of the converse half is discharged by the conservative
family of points carried by the site of opens of a topological space. -/
theorem hasTorAmplitude_iff_forall_derivedModuleFiber (E : DerivedCategory (OXMod.{u} X))
    (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b ↔
      ∀ Φ : (Opens.grothendieckTopology X.carrier).Point.{u},
        StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
          ((Φ.presheafFiber (A := CommRingCat.{u})).obj X.sheaf.obj)
          ((Stacks.derivedModuleFiber Φ X.sheaf).obj E) a b :=
  ⟨fun h Φ =>
      Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber
        (derTensorSite X) E a b h Φ,
    fun h =>
      Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber
        (derTensorSite X) E a b
        (Opens.hasConservativeFamily_grothendieckTopology X.carrier) h⟩

open Stacks.SheafOfModules.DerivedTensorProduct
  (hasTorAmplitude_of_forall_derivedModuleFiber_family) in
/-- **Tor amplitude at the derived tensor product of Stacks 06YU is detected at the fibres of the
*topological* points.** An object `E` of `D(𝒪_X)` has Tor amplitude in `[a, b]` if and only if,
for every point `x` of the space `X`, the derived fibre of `E` at the point
`TopologicalSpace.Opens.pointGrothendieckTopology x` of the site of opens has Tor amplitude in
`[a, b]` over the fibre of the structure sheaf there.

Only the points of the space are quantified over, not all points of the site: the forward half is
`hasTorAmplitude_iff_forall_derivedModuleFiber` read at one point, and the converse is Stacks
0DJJ (2) tested on the conservative family that the points of a topological space form. -/
theorem hasTorAmplitude_iff_forall_pointFiber (E : DerivedCategory (OXMod.{u} X)) (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b ↔
      ∀ x : X.carrier, StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((Opens.pointGrothendieckTopology x).presheafFiber (A := CommRingCat.{u})).obj
          X.sheaf.obj)
        ((Stacks.derivedModuleFiber (Opens.pointGrothendieckTopology x) X.sheaf).obj E) a b :=
  ⟨fun h x => (hasTorAmplitude_iff_forall_derivedModuleFiber X E a b).1 h
      (Opens.pointGrothendieckTopology x),
    fun h => hasTorAmplitude_of_forall_derivedModuleFiber_family (derTensorSite X) E a b
      (fun x : X.carrier => Opens.pointGrothendieckTopology x)
      (Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X.carrier) h⟩

end StalkwiseCriterion

section Stalk

/-- **The image of a prime `q` of `A` under `Spec A ⟶ Spec R` is the prime `q ∩ R`.** -/
theorem specMap_base_asIdeal (q : PrimeSpectrum A) :
    ((specMap R A).base q).asIdeal = Ideal.under R q.asIdeal := rfl

/-- **The stalk of `f^{-1}𝒪_{Spec R}` at a prime `q` of `A` is the localisation `R_{q ∩ R}`.**
The stalk of an inverse-image sheaf at `q` is the stalk of `𝒪_{Spec R}` at the image point of
`q`, which is the prime `q ∩ R`, and the stalk of the structure sheaf of `Spec R` at a prime is
the localisation of `R` at that prime. -/
def relativeStalkIso (q : PrimeSpectrum A) :
    TopCat.Presheaf.stalk (relativeRingedSpace R A).presheaf q ≅
      CommRingCat.of (Localization.AtPrime (Ideal.under R q.asIdeal)) :=
  AlgebraicGeometry.RingedSpace.inverseImageStalkIso
      (Spec (CommRingCat.of R)).toRingedSpace (specMap R A).base q ≪≫
    Spec.stalkIso (CommRingCat.of R) ((specMap R A).base q)

/-- **The fibre of `f^{-1}𝒪_{Spec R}` at the point of the site of opens attached to a prime `q`
of `A` is the localisation `R_{q ∩ R}`.** This is `relativeStalkIso` read in the fibre language
that the stalkwise criterion `hasTorAmplitude_iff_forall_pointFiber` is stated in. -/
def relativePointFiberIso (q : PrimeSpectrum A) :
    ((Opens.pointGrothendieckTopology q).presheafFiber (A := CommRingCat.{u})).obj
        (relativeRingedSpace R A).sheaf.obj ≅
      CommRingCat.of (Localization.AtPrime (Ideal.under R q.asIdeal)) :=
  Opens.pointFiberStalkIso q (relativeRingedSpace R A).presheaf ≪≫ relativeStalkIso R A q

/-- **The homomorphism `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}` read for the underlying sheaves of
(not necessarily commutative) rings**, which is the form along which a complex of
`𝒪_{Spec A}`-modules is restricted to `f^{-1}𝒪_{Spec R}`. -/
noncomputable abbrev relativeRingStructureMap :
    (sheafCompose (Opens.grothendieckTopology (Spec (CommRingCat.of A)).carrier)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj (relativeRingedSpace R A).sheaf ⟶
      (sheafCompose (Opens.grothendieckTopology (Spec (CommRingCat.of A)).carrier)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Spec (CommRingCat.of A)).sheaf :=
  (sheafCompose (Opens.grothendieckTopology (Spec (CommRingCat.of A)).carrier)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (relativeStructureMap R A)

/-- **The map of stalks at a prime `q` of `A` induced by `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}`.** -/
noncomputable abbrev relativeStalkStructureMap (q : PrimeSpectrum A) :
    TopCat.Presheaf.stalk (relativeRingedSpace R A).presheaf q ⟶
      TopCat.Presheaf.stalk (Spec (CommRingCat.of A)).presheaf q :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u}
    (X := (Spec (CommRingCat.of A)).carrier) q).map (relativeStructureMap R A).hom

/-- **The triangle identity for the structure map of the relative ringed space.** On an open
`U ⊆ Spec R` the unit of the inverse-image/direct-image adjunction followed by
`relativeStructureMap` is the structure-sheaf datum of `f : Spec A ⟶ Spec R`.

Since `relativeStructureMap` is by definition the adjunct of that datum, this is the triangle
identity `η ≫ f_*(ε) = id` of the adjunction, read on sections. -/
private theorem relativeStructureMap_app_inverseImageProjection
    (U : Opens (Spec (CommRingCat.of R)).carrier) :
    (AlgebraicGeometry.RingedSpace.inverseImageProjection
        (Spec (CommRingCat.of R)).toRingedSpace (specMap R A).base).hom.c.app (Opposite.op U) ≫
      (relativeStructureMap R A).hom.app (Opposite.op ((Opens.map (specMap R A).base).obj U)) =
      (specMap R A).toLRSHom.toShHom.hom.c.app (Opposite.op U) :=
  congrArg (fun t => CategoryTheory.NatTrans.app (InducedCategory.Hom.hom t) (Opposite.op U))
    ((Adjunction.homEquiv_unit (adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (specMap R A).base) (f := relativeStructureMap R A)).symm.trans
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (specMap R A).base).homEquiv _ _).apply_symm_apply _))

/-- **The stalk map of `f : Spec A ⟶ Spec R` factors through the stalk of `f^{-1}𝒪_{Spec R}`.**
Composing the inverse of the inverse-image stalk comparison at a prime `q` of `A` with the stalk
map of `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}` gives the stalk map of `f` itself.

Both sides are determined by their effect on germs, where the statement is
`relativeStructureMap_app_inverseImageProjection`. -/
theorem inverseImageStalkIso_inv_comp_eq_stalkMap (q : PrimeSpectrum A) :
    (AlgebraicGeometry.RingedSpace.inverseImageStalkIso
          (Spec (CommRingCat.of R)).toRingedSpace (specMap R A).base q).inv ≫
        relativeStalkStructureMap R A q =
      (specMap R A).stalkMap q := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ relativeStalkStructureMap R A q)
        (AlgebraicGeometry.RingedSpace.germ_inverseImageStalkIso_inv
          (Spec (CommRingCat.of R)).toRingedSpace (specMap R A).base q U hU)).trans
      ((congrArg (fun t => t ≫ relativeStalkStructureMap R A q)
          (AlgebraicGeometry.PresheafedSpace.stalkMap_germ
            (AlgebraicGeometry.RingedSpace.inverseImageProjection
              (Spec (CommRingCat.of R)).toRingedSpace (specMap R A).base).hom U q hU)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => (AlgebraicGeometry.RingedSpace.inverseImageProjection
                (Spec (CommRingCat.of R)).toRingedSpace
                  (specMap R A).base).hom.c.app (Opposite.op U) ≫ t)
              (TopCat.Presheaf.stalkFunctor_map_germ
                ((Opens.map (specMap R A).base).obj U) q hU
                (relativeStructureMap R A).hom)).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun t => t ≫ (Spec (CommRingCat.of A)).presheaf.germ
                    ((Opens.map (specMap R A).base).obj U) q hU)
                  (relativeStructureMap_app_inverseImageProjection R A U)).trans
                (AlgebraicGeometry.PresheafedSpace.stalkMap_germ
                  (specMap R A).toLRSHom.toShHom.hom U q hU).symm))))))

/-- **The stalk map of `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}` at a prime `q` of `A` is the localisation
map `R_{q ∩ R} ⟶ A_q`**, read through `relativeStalkIso` and `Spec.stalkIso`.

By `inverseImageStalkIso_inv_comp_eq_stalkMap` the composite is the stalk map of `f`, and
`AlgebraicGeometry.localRingHom_comp_stalkIso` identifies that with `Localization.localRingHom`. -/
theorem relativeStalkIso_inv_comp (q : PrimeSpectrum A) :
    (relativeStalkIso R A q).inv ≫
        relativeStalkStructureMap R A q ≫ (Spec.stalkIso (CommRingCat.of A) q).hom =
      CommRingCat.ofHom (Localization.localRingHom (Ideal.under R q.asIdeal) q.asIdeal
        (algebraMap R A) rfl) := by
  have hfinal : (Spec.stalkIso (CommRingCat.of R) ((specMap R A).base q)).inv ≫
      ((specMap R A).stalkMap q ≫ (Spec.stalkIso (CommRingCat.of A) q).hom) =
      CommRingCat.ofHom (Localization.localRingHom (Ideal.under R q.asIdeal) q.asIdeal
        (algebraMap R A) rfl) := by
    show (Spec.stalkIso (CommRingCat.of R) (PrimeSpectrum.comap (algebraMap R A) q)).inv ≫
        ((specMap R A).stalkMap q ≫ (Spec.stalkIso (CommRingCat.of A) q).hom) =
        CommRingCat.ofHom (Localization.localRingHom
          (PrimeSpectrum.comap (algebraMap R A) q).asIdeal q.asIdeal (algebraMap R A) rfl)
    rw [← Scheme.localRingHom_comp_stalkIso]
    simp only [CommRingCat.hom_ofHom, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (Spec.stalkIso (CommRingCat.of R) ((specMap R A).base q)).inv ≫ t)
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ (Spec.stalkIso (CommRingCat.of A) q).hom)
            (inverseImageStalkIso_inv_comp_eq_stalkMap R A q)))).trans hfinal)

/-- **The same identification read at the fibre of the point of the site of opens attached to
`q`.** The fibre-to-stalk comparison followed by the stalk map of
`f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}` is, through `relativePointFiberIso` and `Spec.stalkIso`, the
localisation map `R_{q ∩ R} ⟶ A_q`. -/
theorem pointFiberStalkHom_comp_relativeStalkStructureMap (q : PrimeSpectrum A) :
    Opens.pointFiberStalkHom q (relativeRingedSpace R A).presheaf ≫
        relativeStalkStructureMap R A q ≫ (Spec.stalkIso (CommRingCat.of A) q).hom =
      (relativePointFiberIso R A q).hom ≫
        CommRingCat.ofHom (Localization.localRingHom (Ideal.under R q.asIdeal) q.asIdeal
          (algebraMap R A) rfl) :=
  ((relativePointFiberIso R A q).inv_comp_eq).mp
    (calc (relativePointFiberIso R A q).inv ≫
          Opens.pointFiberStalkHom q (relativeRingedSpace R A).presheaf ≫
            relativeStalkStructureMap R A q ≫ (Spec.stalkIso (CommRingCat.of A) q).hom
        = (relativeStalkIso R A q).inv ≫
            (Opens.pointFiberStalkInv q (relativeRingedSpace R A).presheaf ≫
              (Opens.pointFiberStalkHom q (relativeRingedSpace R A).presheaf ≫
                relativeStalkStructureMap R A q ≫
                  (Spec.stalkIso (CommRingCat.of A) q).hom)) := Category.assoc _ _ _
      _ = (relativeStalkIso R A q).inv ≫
            ((Opens.pointFiberStalkInv q (relativeRingedSpace R A).presheaf ≫
                Opens.pointFiberStalkHom q (relativeRingedSpace R A).presheaf) ≫
              (relativeStalkStructureMap R A q ≫
                (Spec.stalkIso (CommRingCat.of A) q).hom)) :=
          congrArg _ (Category.assoc _ _ _).symm
      _ = (relativeStalkIso R A q).inv ≫
            (𝟙 _ ≫ (relativeStalkStructureMap R A q ≫
              (Spec.stalkIso (CommRingCat.of A) q).hom)) :=
          congrArg _ (congrArg
            (fun t => t ≫ (relativeStalkStructureMap R A q ≫
              (Spec.stalkIso (CommRingCat.of A) q).hom))
            (Opens.pointFiberStalkIso q (relativeRingedSpace R A).presheaf).inv_hom_id)
      _ = (relativeStalkIso R A q).inv ≫
            (relativeStalkStructureMap R A q ≫ (Spec.stalkIso (CommRingCat.of A) q).hom) :=
          congrArg _ (Category.id_comp _)
      _ = _ := relativeStalkIso_inv_comp R A q)

/-- **The `RingCat`-valued stalk of `𝒪_{Spec A}` at a prime `q` is the localisation `A_q`.**
This is `Spec.stalkIso` composed with the comparison between the `RingCat`-valued and the
`CommRingCat`-valued stalk of the structure sheaf. -/
noncomputable def specStalkRingIso (q : PrimeSpectrum A) :
    TopCat.Presheaf.stalk (C := RingCat.{u})
        ((Spec (CommRingCat.of A)).presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) q ≅
      (forget₂ CommRingCat.{u} RingCat.{u}).obj
        (CommRingCat.of (Localization.AtPrime q.asIdeal)) :=
  SemilinearStalk.commStalkIso (Spec (CommRingCat.of A)).presheaf q ≪≫
    (forget₂ CommRingCat.{u} RingCat.{u}).mapIso (Spec.stalkIso (CommRingCat.of A) q)

/-- **The germ map `Γ(Spec A, ⊤) ⟶ 𝒪_{Spec A, q}` is the localisation map `A ⟶ A_q`**, read
through `specStalkRingIso` and the global sections isomorphism of Stacks 01HR. -/
theorem germ_comp_specStalkRingIso (q : PrimeSpectrum A) :
    TopCat.Presheaf.germ (C := RingCat.{u})
          ((Spec (CommRingCat.of A)).presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})
          ⊤ q trivial ≫
        (specStalkRingIso A q).hom =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
          CommRingCat.ofHom (algebraMap A (Localization.AtPrime q.asIdeal))) :=
  (Category.assoc _ _ _).symm.trans
    ((eq_whisker (Opens.germ_commStalkIso_hom (X := (Spec (CommRingCat.of A)).carrier) q
        (Spec (CommRingCat.of A)).presheaf ⊤ trivial) _).trans
      (((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).symm.trans
        (congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
          (Spec.germ_stalkMapIso_hom (R := CommRingCat.of A) q))))

/-- **The ring homomorphism `A ⟶ 𝒪_{Spec A, q}` is the localisation map `A ⟶ A_q`**, read
through `specStalkRingIso`.

The left-hand factor written out is `Stacks.TildeStalk.specStalkRingHom (CommRingCat.of A) q`,
the germ map along which the stalk of an associated sheaf is a base change by Stacks 01HV. -/
theorem specStalkRingIso_comp_germ_eq_algebraMap (q : PrimeSpectrum A) :
    (specStalkRingIso A q).hom.hom.comp
        ((TopCat.Presheaf.germ (C := RingCat.{u})
            ((Spec (CommRingCat.of A)).presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})
            ⊤ q trivial).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
      algebraMap A (Localization.AtPrime q.asIdeal) :=
  congrArg RingCat.Hom.hom
    ((whisker_eq _ (germ_comp_specStalkRingIso A q)).trans
      (((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).symm.trans
        (congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_assoc _))))

/-- **The module-theoretic form of the stalk identification of Stacks 0DHY.** The composite of
the fibre-to-stalk comparison of `f^{-1}𝒪_{Spec R}` at a prime `q` of `A` with the stalk map of
`f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}`, read at the `RingCat`-valued stalks that the module API uses,
is the localisation map `R_{q ∩ R} ⟶ A_q`.

This is `pointFiberStalkHom_comp_relativeStalkStructureMap` transported along the comparison
between the `RingCat`-valued and the `CommRingCat`-valued fibres and stalks. -/
theorem commRingFiberStalkHom_comp_specStalkRingIso (q : PrimeSpectrum A) :
    Opens.commRingFiberStalkHom q (relativeRingedSpace R A).sheaf ≫
        SemilinearStalk.ringStalkMap (relativeRingStructureMap R A).hom q ≫
          (specStalkRingIso A q).hom =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((relativePointFiberIso R A q).hom ≫ CommRingCat.ofHom
          (Localization.localRingHom (Ideal.under R q.asIdeal) q.asIdeal
            (algebraMap R A) rfl)) := by
  have h1 : SemilinearStalk.ringStalkMap (relativeRingStructureMap R A).hom q ≫
        (SemilinearStalk.commStalkIso (Spec (CommRingCat.of A)).presheaf q).hom =
      (SemilinearStalk.commStalkIso (relativeRingedSpace R A).presheaf q).hom ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map (relativeStalkStructureMap R A q) :=
    Opens.ringStalkMap_comp_commStalkIso (X := (Spec (CommRingCat.of A)).carrier) q
      (relativeStructureMap R A).hom
  have h2 : Opens.commRingFiberStalkHom q (relativeRingedSpace R A).sheaf ≫
        (SemilinearStalk.commStalkIso (relativeRingedSpace R A).presheaf q).hom =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        (Opens.pointFiberStalkHom q (relativeRingedSpace R A).presheaf) :=
    Opens.commRingFiberStalkHom_comp_commStalkIso (X := (Spec (CommRingCat.of A)).carrier) q
      (relativeRingedSpace R A).sheaf
  refine (whisker_eq _ (Category.assoc _ _ _).symm).trans ?_
  refine (whisker_eq _ (eq_whisker h1 _)).trans ?_
  refine (whisker_eq _ (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker h2 _).trans ?_
  refine (whisker_eq _ ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).symm).trans ?_
  refine ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).symm.trans ?_
  exact congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
    (pointFiberStalkHom_comp_relativeStalkStructureMap R A q)

/-- **Along a ring isomorphism of the target, extension of scalars is extension of scalars along
the composite followed by restriction of scalars.** Both sides are left adjoint to restriction of
scalars along `ρ`: for the right-hand side because restriction of scalars along a ring
isomorphism is an equivalence, whose inverse recomposed with restriction along `ε ∘ ρ` is
restriction along `ρ`.

This compares the base change `𝒪_{Spec A,q} ⊗_A M^•` computing the stalk of `M̃^•` by
Stacks 01HV with the base change `A_q ⊗_A M^•` appearing in
`StacksDraft.TorAmplitude.HasTorAmplitudeAt`, the ring isomorphism being
`specStalkRingIso`. -/
noncomputable def extendScalarsCompRestrictScalarsIso {B S S' : Type u} [CommRing B] [CommRing S]
    [CommRing S'] (ρ : B →+* S) (ε : S ≃+* S') :
    ModuleCat.extendScalars.{u, u, u} ρ ≅
      ModuleCat.extendScalars.{u, u, u} (ε.toRingHom.comp ρ) ⋙
        ModuleCat.restrictScalars.{u} ε.toRingHom :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ρ).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ε.toRingHom.comp ρ)).comp
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv ε).toAdjunction).ofNatIsoRight
      (ModuleCat.restrictScalarsComp'.{u} (ε.toRingHom.comp ρ) ε.symm.toRingHom ρ (by
        ext a
        exact (ε.symm_apply_apply (ρ a)).symm)).symm)

/-- **The ring homomorphism over which the fibre of `E` at a prime `q` of `A` is a module.**
Read through `relativePointFiberIso` and `specStalkRingIso`, the composite
`(f^{-1}𝒪_{Spec R})_q ⟶ 𝒪_{Spec A, q}` of the fibre-to-stalk comparison with the stalk map of
`f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}` is `algebraMap R_{q ∩ R} A_q` for the algebra structure
`Localization.AtPrime.algebraOfLiesOver`, which is the one
`StacksDraft.TorAmplitude.HasTorAmplitudeAt` measures Tor amplitude over. -/
theorem specStalkRingIso_comp_commRingFiberStalkHom_eq_algebraMap (q : PrimeSpectrum A) :
    letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
        (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
    (specStalkRingIso A q).hom.hom.comp
        ((SemilinearStalk.ringStalkMap (relativeRingStructureMap R A).hom q).hom.comp
          (Opens.commRingFiberStalkHom q (relativeRingedSpace R A).sheaf).hom) =
      (algebraMap (Localization.AtPrime (Ideal.under R q.asIdeal))
          (Localization.AtPrime q.asIdeal)).comp
        (relativePointFiberIso R A q).hom.hom :=
  congrArg RingCat.Hom.hom (commRingFiberStalkHom_comp_specStalkRingIso R A q)

end Stalk

section Fibre

open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- **Stacks 01HV read over a commutative ring isomorphic to the stalk ring.** For a ring
isomorphism `ε : 𝒪_{Spec B, x} ≅ S` and the composite `g = ε ∘ (B ⟶ 𝒪_{Spec B,x})`, the stalk at
`x` of the sheaf associated to a `B`-module is `S ⊗_B -` read over the stalk ring along `ε`:

`~ ⋙ (-)_x ≅ (S ⊗_B -) ⋙ restrictScalars ε`.

This is `Stacks.TildeStalk.tildeStalkFunctorIso` composed with
`extendScalarsCompRestrictScalarsIso`. Unlike that isomorphism, this one is stated with no
`CommRing` instance on the `RingCat`-valued stalk, so it composes with functors into
`ModuleCat 𝒪_{Spec B,x}`. -/
noncomputable def tildeStalkRestrictScalarsIso (B : CommRingCat.{u}) (x : (Spec B).carrier)
    {S : Type u} [CommRing S]
    (ε : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing (Spec B).toRingedSpace).obj x) ≃+* S)
    (g : B →+* S) (hg : ε.toRingHom.comp (Stacks.TildeStalk.specStalkRingHom B x) = g) :
    tilde.functor B ⋙ Stacks.TildeStalk.specStalkFunctor B x ≅
      ModuleCat.extendScalars.{u, u, u} g ⋙ ModuleCat.restrictScalars.{u} ε.toRingHom := by
  subst hg
  letI := Stacks.RingedSpace.structureStalkCommRing (Spec B).toRingedSpace x
  exact Stacks.TildeStalk.tildeStalkFunctorIso B x ≪≫
    extendScalarsCompRestrictScalarsIso (Stacks.TildeStalk.specStalkRingHom B x) ε

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **`specStalkRingIso` as a ring isomorphism** `𝒪_{Spec A, q} ≃+* A_q`. -/
noncomputable def specStalkRingEquiv (q : PrimeSpectrum A) :
    ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace).obj q) ≃+*
      Localization.AtPrime q.asIdeal :=
  (specStalkRingIso A q).ringCatIsoToRingEquiv

/-- **The ring homomorphism `(f^{-1}𝒪_{Spec R})_q ⟶ 𝒪_{Spec A, q}`** along which the fibre at a
prime `q` of `A` of a complex of `f^{-1}𝒪_{Spec R}`-modules is read: the fibre-to-stalk
comparison followed by the stalk map of `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}`. -/
noncomputable abbrev fiberToStalkRingHom (q : PrimeSpectrum A) :
    ToType ((forget₂ CommRingCat.{u} RingCat.{u}).obj
        (((Opens.pointGrothendieckTopology q).presheafFiber (A := CommRingCat.{u})).obj
          (relativeRingedSpace R A).sheaf.obj)) →+*
      ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace).obj q) :=
  (SemilinearStalk.ringStalkMap (X := (Spec (CommRingCat.of A)).carrier)
      (relativeRingStructureMap R A).hom q).hom.comp
    (Opens.commRingFiberStalkHom (X := (Spec (CommRingCat.of A)).carrier) q
      (relativeRingedSpace R A).sheaf).hom

/-- **The fibre at a prime `q` of `A` of an `𝒪_{Spec A}`-module read over `f^{-1}𝒪_{Spec R}` is
its stalk at `q`**, as a module over the fibre of `f^{-1}𝒪_{Spec R}` along
`fiberToStalkRingHom`, naturally in the module.

This composes `Opens.moduleFiberStalkFunctorIsoOfCommRing`, which identifies the fibre at the
point of the site of opens attached to `q` with the stalk at `q`, with
`AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsFunctorIso`, which says that a
restriction of scalars does not change the stalk. -/
noncomputable def relativeFiberRestrictScalarsIso (q : PrimeSpectrum A) :
    SheafOfModules.restrictScalars (relativeRingStructureMap R A) ⋙
        Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
          (relativeRingedSpace R A).sheaf ≅
      Stacks.TildeStalk.specStalkFunctor (CommRingCat.of A) q ⋙
        ModuleCat.restrictScalars.{u} (fiberToStalkRingHom R A q) :=
  Functor.isoWhiskerLeft (SheafOfModules.restrictScalars (relativeRingStructureMap R A))
      (Opens.moduleFiberStalkFunctorIsoOfCommRing (X := (Spec (CommRingCat.of A)).carrier) q
        (relativeRingedSpace R A).sheaf) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsFunctorIso
        (relativeRingStructureMap R A) q)
      (ModuleCat.restrictScalars.{u}
        (Opens.commRingFiberStalkHom (X := (Spec (CommRingCat.of A)).carrier) q
          (relativeRingedSpace R A).sheaf).hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Stacks.TildeStalk.specStalkFunctor (CommRingCat.of A) q)
      (ModuleCat.restrictScalarsComp'.{u}
        (Opens.commRingFiberStalkHom (X := (Spec (CommRingCat.of A)).carrier) q
          (relativeRingedSpace R A).sheaf).hom
        (SemilinearStalk.ringStalkMap (X := (Spec (CommRingCat.of A)).carrier)
          (relativeRingStructureMap R A).hom q).hom
        (fiberToStalkRingHom R A q) rfl).symm

/-- **The module-theoretic stalk identification of Stacks 0DHY.** The fibre at a prime `q` of `A`
of the sheaf associated to an `A`-module `N`, read over `f^{-1}𝒪_{Spec R}`, is `A_q ⊗_A N` read
over `R_{q ∩ R}` along `algebraMap R_{q ∩ R} A_q`, naturally in `N`.

This is `relativeFiberRestrictScalarsIso` composed with `tildeStalkRestrictScalarsIso`, the two
coefficient rings being identified by `specStalkRingIso_comp_germ_eq_algebraMap` and
`specStalkRingIso_comp_commRingFiberStalkHom_eq_algebraMap`. -/
noncomputable def relativeFiberFunctorIso (q : PrimeSpectrum A) :
    letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
        (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
    tilde.functor (CommRingCat.of A) ⋙
        (SheafOfModules.restrictScalars (relativeRingStructureMap R A) ⋙
          Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
            (relativeRingedSpace R A).sheaf) ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.AtPrime q.asIdeal)) ⋙
        (ModuleCat.restrictScalars.{u}
            (algebraMap (Localization.AtPrime (Ideal.under R q.asIdeal))
              (Localization.AtPrime q.asIdeal)) ⋙
          ModuleCat.restrictScalars.{u} (relativePointFiberIso R A q).hom.hom) :=
  letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
  Functor.isoWhiskerLeft (tilde.functor (CommRingCat.of A))
      (relativeFiberRestrictScalarsIso R A q) ≪≫
    (Functor.associator (tilde.functor (CommRingCat.of A))
      (Stacks.TildeStalk.specStalkFunctor (CommRingCat.of A) q)
      (ModuleCat.restrictScalars.{u} (fiberToStalkRingHom R A q))).symm ≪≫
    Functor.isoWhiskerRight
      (tildeStalkRestrictScalarsIso (CommRingCat.of A) q (specStalkRingEquiv A q)
        (algebraMap A (Localization.AtPrime q.asIdeal))
        (specStalkRingIso_comp_germ_eq_algebraMap A q))
      (ModuleCat.restrictScalars.{u} (fiberToStalkRingHom R A q)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.AtPrime q.asIdeal)))
      ((ModuleCat.restrictScalarsComp'.{u} (fiberToStalkRingHom R A q)
            (specStalkRingEquiv A q).toRingHom
            ((specStalkRingEquiv A q).toRingHom.comp (fiberToStalkRingHom R A q)) rfl).symm ≪≫
        ModuleCat.restrictScalarsCongr
          (specStalkRingIso_comp_commRingFiberStalkHom_eq_algebraMap R A q) ≪≫
        ModuleCat.restrictScalarsComp'.{u} (relativePointFiberIso R A q).hom.hom
          (algebraMap (Localization.AtPrime (Ideal.under R q.asIdeal))
            (Localization.AtPrime q.asIdeal))
          ((algebraMap (Localization.AtPrime (Ideal.under R q.asIdeal))
            (Localization.AtPrime q.asIdeal)).comp
              (relativePointFiberIso R A q).hom.hom) rfl)

/-- **The derived fibre of `relativeComplex` at a prime `q` of `A`.** It is the localisation
`A_q ⊗_A M^•` of the complex `M^•`, read over `R_{q ∩ R}` through
`algebraMap R_{q ∩ R} A_q` and `relativePointFiberIso`.

The fibre functor is exact, so its derived functor is computed degreewise
(`CategoryTheory.Functor.mapDerivedCategoryFactors`), and degreewise it is
`relativeFiberFunctorIso`. -/
noncomputable def relativeFiberDerivedIso (q : PrimeSpectrum A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
        (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
    (Stacks.derivedModuleFiber (Opens.pointGrothendieckTopology q)
        (relativeRingedSpace R A).sheaf).obj (DerivedCategory.Q.obj (relativeComplex R A M)) ≅
      DerivedCategory.Q.obj
        ((CochainComplex.restrictScalars (relativePointFiberIso R A q).hom.hom).obj
          ((CochainComplex.restrictScalars
              (algebraMap (Localization.AtPrime (Ideal.under R q.asIdeal))
                (Localization.AtPrime q.asIdeal))).obj
            ((CochainComplex.extendScalars
              (algebraMap A (Localization.AtPrime q.asIdeal))).obj M))) :=
  letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
  letI : (Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
      (relativeRingedSpace R A).sheaf).Additive :=
    Stacks.instAdditiveSheafModuleFiberOfCommRing
      (J := Opens.grothendieckTopology (relativeRingedSpace R A).carrier)
      (Opens.pointGrothendieckTopology q) (relativeRingedSpace R A).sheaf
  letI : PreservesFiniteLimits
      (Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
        (relativeRingedSpace R A).sheaf) :=
    Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
      (J := Opens.grothendieckTopology (relativeRingedSpace R A).carrier)
      (Opens.pointGrothendieckTopology q) (relativeRingedSpace R A).sheaf
  letI : PreservesFiniteColimits
      (Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
        (relativeRingedSpace R A).sheaf) :=
    Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
      (J := Opens.grothendieckTopology (relativeRingedSpace R A).carrier)
      (Opens.pointGrothendieckTopology q) (relativeRingedSpace R A).sheaf
  letI : (SheafOfModules.restrictScalars (relativeRingStructureMap R A) ⋙
      Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
        (relativeRingedSpace R A).sheaf).PreservesZeroMorphisms :=
    ⟨fun X Y => ((congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
            (Opens.pointGrothendieckTopology q) (relativeRingedSpace R A).sheaf).map φ)
          ((SheafOfModules.restrictScalars (relativeRingStructureMap R A)).map_zero X Y)).trans
        ((Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
          (relativeRingedSpace R A).sheaf).map_zero _ _))⟩
  letI : (tilde.functor (CommRingCat.of A) ⋙
      (SheafOfModules.restrictScalars (relativeRingStructureMap R A) ⋙
        Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
          (relativeRingedSpace R A).sheaf)).PreservesZeroMorphisms :=
    ⟨fun X Y => ((congrArg (fun φ => (SheafOfModules.restrictScalars
            (relativeRingStructureMap R A) ⋙
          Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
            (relativeRingedSpace R A).sheaf).map φ)
          ((tilde.functor (CommRingCat.of A)).map_zero X Y)).trans
        ((SheafOfModules.restrictScalars (relativeRingStructureMap R A) ⋙
          Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
            (relativeRingedSpace R A).sheaf).map_zero _ _))⟩
  (Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology q)
      (relativeRingedSpace R A).sheaf).mapDerivedCategoryFactors.app (relativeComplex R A M) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (relativeFiberFunctorIso R A q) (ComplexShape.up ℤ)).app M)

/-- **Canonical Tor amplitude is unchanged by restriction of scalars along a ring
isomorphism.** One direction is
`AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_restrictScalars_ringEquiv`,
and the other is the same statement for the inverse isomorphism, the two restrictions of
scalars cancelling. -/
public theorem hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff
    {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T)
    (K : CochainComplex (ModuleCat.{u} T) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonical S (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) a b ↔
      HasTorAmplitudeCanonical T (DerivedCategory.Q.obj K) a b := by
  have hid : RingHom.id T = e.toRingHom.comp e.symm.toRingHom :=
    RingHom.ext fun t => (e.apply_symm_apply t).symm
  have ecx : ((ModuleCat.restrictScalars.{u} e.symm.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars.{u} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ≅ K :=
    (NatIso.mapHomologicalComplex
      ((ModuleCat.restrictScalarsComp'.{u} e.symm.toRingHom e.toRingHom
          (RingHom.id T) hid).symm ≪≫
        ModuleCat.restrictScalarsId.{u} T) (ComplexShape.up ℤ)).app K ≪≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} T) (ComplexShape.up ℤ)).app K
  exact ⟨fun h => BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      ((ModuleCat.restrictScalars.{u} e.symm.toRingHom).mapDerivedCategoryFactors.app _ ≪≫
        DerivedCategory.Q.mapIso ecx) a b
      (BaseChangeTorAmplitude.hasTorAmplitudeCanonical_restrictScalars_ringEquiv e.symm _ a b h),
    fun h => BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      ((ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategoryFactors.app K) a b
      (BaseChangeTorAmplitude.hasTorAmplitudeCanonical_restrictScalars_ringEquiv e _ a b h)⟩

/-- **The two sides of Stacks 0DHY agree at a single prime.** The derived fibre of
`relativeComplex` at a prime `q` of `A` has Tor amplitude in `[a, b]` over the fibre of
`f^{-1}𝒪_{Spec R}` if and only if the localisation of `M^•` at `q` has Tor amplitude in `[a, b]`
over `R_{q ∩ R}`.

The derived fibre is that localisation by `relativeFiberDerivedIso`; the change of coefficient
ring along `relativePointFiberIso` is harmless because it is a ring isomorphism, and the two
Tor-amplitude conventions are compared by
`hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF`. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_iff (q : PrimeSpectrum A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonical
        (((Opens.pointGrothendieckTopology q).presheafFiber (A := CommRingCat.{u})).obj
          (relativeRingedSpace R A).sheaf.obj)
        ((Stacks.derivedModuleFiber (Opens.pointGrothendieckTopology q)
            (relativeRingedSpace R A).sheaf).obj
          (DerivedCategory.Q.obj (relativeComplex R A M))) a b ↔
      HasTorAmplitudeAt R M q.asIdeal a b := by
  let : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
  refine Iff.trans
    (hasTorAmplitudeCanonical_iff_of_iso (relativeFiberDerivedIso R A q M) a b) ?_
  refine Iff.trans (hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff
    (relativePointFiberIso R A q).commRingCatIsoToRingEquiv _ a b) ?_
  exact hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b

end Fibre

section MainStatements

open StacksDraft.TorAmplitude (HasTorAmplitudeCanonical HasFiniteTorDimensionCanonical)
open Stacks.Cohomology.TorAmplitude (LocallyHasFiniteTorDimension)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] Stacks.Cohomology.TorAmplitude.restrictModules_preservesFiniteLimits
  Stacks.Cohomology.TorAmplitude.restrictModules_preservesFiniteColimits

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **Stacks 0DHY, part (1).** Let `f : Spec A ⟶ Spec R` be the morphism of affine schemes of a
ring map `R → A`, let `M^•` be a complex of `A`-modules and let `E` be the complex of
`f^{-1}𝒪_{Spec R}`-modules attached to it. Then `E` has Tor amplitude in `[a, b]` over
`f^{-1}𝒪_{Spec R}` if and only if `M^•`, read as a complex of `R`-modules, has Tor amplitude in
`[a, b]` over `R`.

Tor amplitude on the sheaf side is tested at the fibres of the topological points by
`hasTorAmplitude_iff_forall_pointFiber`, where it becomes the Tor amplitude of the localisation
of `M^•` at each prime of `A` over the corresponding localisation of `R`
(`hasTorAmplitudeCanonical_derivedModuleFiber_iff`); that family of conditions is Tor amplitude
over `R` by `hasTorAmplitudeCanonical_restrictScalars_iff_forall_isPrime`. -/
@[stacks 0DHY "part (1)"]
theorem hasTorAmplitude_relativeComplex_iff (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude (relativeRingedSpace R A)
        (DerivedCategory.Q.obj (relativeComplex R A M)) a b ↔
      HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) a b := by
  refine (hasTorAmplitude_iff_forall_pointFiber (relativeRingedSpace R A)
      (DerivedCategory.Q.obj (relativeComplex R A M)) a b).trans
    (Iff.trans ?_ (hasTorAmplitudeCanonical_restrictScalars_iff_forall_isPrime R A M a b).symm)
  exact ⟨fun h p hp => (hasTorAmplitudeCanonical_derivedModuleFiber_iff R A ⟨p, hp⟩ M a b).1
      (h ⟨p, hp⟩),
    fun h x => (hasTorAmplitudeCanonical_derivedModuleFiber_iff R A x M a b).2
      (@h (x : PrimeSpectrum A).asIdeal (x : PrimeSpectrum A).isPrime)⟩

/-- **Stacks 0DHY, part (2).** In the situation of part (1), the complex `E` of
`f^{-1}𝒪_{Spec R}`-modules locally has finite Tor dimension if and only if `M^•`, read as a
complex of `R`-modules, has finite Tor dimension over `R`.

The space `Spec A` is quasi-compact, so locally finite Tor dimension is Tor amplitude in a
single interval (`locallyHasFiniteTorDimension_iff_hasFiniteTorDimension`), and part (1)
translates each interval. -/
@[stacks 0DHY "part (2)"]
theorem locallyHasFiniteTorDimension_relativeComplex_iff
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    LocallyHasFiniteTorDimension (relativeRingedSpace R A)
        (DerivedCategory.Q.obj (relativeComplex R A M)) ↔
      HasFiniteTorDimensionCanonical R (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) := by
  have : CompactSpace (relativeRingedSpace R A).carrier :=
    inferInstanceAs (CompactSpace (PrimeSpectrum A))
  exact (locallyHasFiniteTorDimension_iff_hasFiniteTorDimension
      (DerivedCategory.Q.obj (relativeComplex R A M))).trans
    ((exists_congr fun a => exists_congr fun b =>
        hasTorAmplitude_relativeComplex_iff R A M a b).trans
      (StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
        R (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M))).symm)

end MainStatements

end AlgebraicGeometry.AffineRelativeTorAmplitude

end

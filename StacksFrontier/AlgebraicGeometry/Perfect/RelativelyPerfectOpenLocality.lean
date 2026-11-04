module

public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectArrowIso
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionBaseTransport
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageArrowOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles

/-!
# Relative perfectness is local on the source

Let `f : X ⟶ S` be a morphism of schemes. Relative perfectness of an object `E` of `D(𝒪_X)` in
the sense of Stacks 0DI0 has two clauses: pseudo-coherence of `E`, and local finiteness of the Tor
dimension of `E` read over the inverse-image ringed space `(X, f⁻¹𝒪_S)`. This file proves that
both clauses, and hence relative perfectness, restrict along open immersions `ι : U ⟶ X` and glue
along coverings of `X` by open immersions, relative perfectness being read at the canonical
certificate families.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.inverseImageOpenMap`: for an open immersion `ι : U ⟶ X`, the
  open immersion `(U, (ι ≫ f)⁻¹𝒪_S) ⟶ (X, f⁻¹𝒪_S)` induced by the square `(ι, 𝟙 S)`.

## Main results

* `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_derivedPullback`: locally finite
  Tor dimension is preserved by derived pullback along any morphism of ringed spaces.
* `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_openImmersion_cover`: locally
  finite Tor dimension glues along a covering by open immersions.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_of_openImmersion_cover`: pseudo-coherence glues
  along a covering by open immersions.
* `AlgebraicGeometry.RingedSpace.openImmersionSquareModuleIso` and
  `derivedOpenImmersionSquareIso`: for a commutative square `ι ≫ b = a ≫ ψ` with `ι`, `ψ` open
  immersions and the range of `ι` the preimage of that of `ψ`, the functors `ι^* ⋙ a_*` and
  `b_* ⋙ ψ^*` agree, before and after deriving.
* `AlgebraicGeometry.Scheme.Hom.derivedScalarRestrictionOpenImmersionIso`: derived restriction
  of scalars commutes with restriction along an open immersion.
* `AlgebraicGeometry.Scheme.Hom.locallyHasFiniteTorDimension_torClause_comp_openImmersion` and
  `locallyHasFiniteTorDimension_torClause_of_openImmersion_cover`: the Tor clause of Stacks 0DI0
  restricts along open immersions and glues along coverings by them.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_comp_openImmersion` and
  `isPerfectRelativeTo_of_openImmersion_cover`: the same for relative perfectness; with the
  specialisations `isPerfectRelativeTo_opens_ι`, `isPerfectRelativeTo_of_iSup_eq_top`,
  `isPerfectRelativeTo_of_two_openImmersions` and `isPerfectRelativeTo_of_forall_mem`.

## References

* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 20.46.13 (Tag 09U7)](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Lemma 20.48.9 (Tag 09U8)](https://stacks.math.columbia.edu/tag/09U8)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Cohomology.TorAmplitude

open _root_.Stacks.AlgebraicGeometry AlgebraicGeometry.RingedSpace

/-- The comparison `Lg^* ⋙ Lf^* ≅ Lk^*` attached to a factorisation `f ≫ g = k`. -/
def derivedPullbackFactorIso {X Y Z : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z)
    (h : f ≫ g = k) : derivedPullback g ⋙ derivedPullback f ≅ derivedPullback k :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g ≪≫
    eqToIso (congrArg (fun m : X ⟶ Z => derivedPullback m) h)

/-- Finite Tor dimension is invariant under isomorphism. -/
theorem hasFiniteTorDimension_of_iso {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {E E' : DerivedCategory (OXMod.{u, u} X)} (e : E ≅ E') (h : HasFiniteTorDimension X E) :
    HasFiniteTorDimension X E' := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, FlatOpcycles.hasTorAmplitude_of_iso hab e.symm⟩

/-- **Locally finite Tor dimension is a pointwise condition.** An object of `D(𝒪_X)` locally has
finite Tor dimension exactly when every point has an open neighbourhood on which its restriction
has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_iff_forall_mem {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (E : DerivedCategory (OXMod.{u, u} X)) :
    LocallyHasFiniteTorDimension X E ↔ ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧
      HasFiniteTorDimension (X.restrict W.isOpenEmbedding)
        ((derivedRestrictModules X W).obj E) := by
  refine ⟨fun ⟨I, U, hU, hfin⟩ x => ?_, fun h => ?_⟩
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
    exact ⟨U i, hi, hfin i⟩
  · choose W hxW hW using h
    exact ⟨X.carrier, W, le_antisymm le_top fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩, hW⟩

/-- Locally finite Tor dimension is invariant under isomorphism. -/
theorem locallyHasFiniteTorDimension_of_iso {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {E E' : DerivedCategory (OXMod.{u, u} X)} (e : E ≅ E')
    (h : LocallyHasFiniteTorDimension X E) : LocallyHasFiniteTorDimension X E' := by
  rw [locallyHasFiniteTorDimension_iff_forall_mem] at h ⊢
  intro x
  obtain ⟨W, hxW, hW⟩ := h x
  exact ⟨W, hxW, hasFiniteTorDimension_of_iso ((derivedRestrictModules X W).mapIso e) hW⟩

/-- Finite Tor dimension of `Ls^*E` passes to any object isomorphic to `Lσ^*Ls^*E`. -/
private theorem hasFiniteTorDimension_of_derivedPullback_iso
    {A B D : AlgebraicGeometry.RingedSpace.{u, u}} (σ : A ⟶ B) (s : B ⟶ D)
    (E : DerivedCategory (OXMod.{u, u} D)) {F : DerivedCategory (OXMod.{u, u} A)}
    (e : F ≅ (derivedPullback σ).obj ((derivedPullback s).obj E))
    (h : HasFiniteTorDimension B ((derivedPullback s).obj E)) : HasFiniteTorDimension A F := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, FlatOpcycles.hasTorAmplitude_of_iso
    (Pullback.hasTorAmplitude_derivedPullback σ _ a b hab) e⟩

/-- Finite Tor dimension of the restriction to an open subspace is finite Tor dimension of the
derived pullback along a morphism into that subspace, transported along a factorisation. -/
theorem hasFiniteTorDimension_restrict_of_factor {X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (W : Opens X.carrier) (σ : X.restrict W.isOpenEmbedding ⟶ Y) (j : Y ⟶ X)
    (hσ : σ ≫ j = X.ofRestrict W.isOpenEmbedding) (E : DerivedCategory (OXMod.{u, u} X))
    (h : HasFiniteTorDimension Y ((derivedPullback j).obj E)) :
    HasFiniteTorDimension (X.restrict W.isOpenEmbedding) ((derivedRestrictModules X W).obj E) := by
  exact hasFiniteTorDimension_of_derivedPullback_iso σ j E
    ((derivedRestrictModulesIsoDerivedPullback X W).app E ≪≫
      ((derivedPullbackFactorIso σ j _ hσ).app E).symm) h

/-- **Finite Tor dimension pulls back around a commutative square.** If `Ls^*E` has finite Tor
dimension and `p ≫ q = r ≫ s`, then `Lp^*Lq^*E` has finite Tor dimension. -/
theorem hasFiniteTorDimension_derivedPullback_of_comm
    {A B C D : AlgebraicGeometry.RingedSpace.{u, u}}
    (p : A ⟶ C) (q : C ⟶ D) (r : A ⟶ B) (s : B ⟶ D) (hw : p ≫ q = r ≫ s)
    (E : DerivedCategory (OXMod.{u, u} D))
    (h : HasFiniteTorDimension B ((derivedPullback s).obj E)) :
    HasFiniteTorDimension A ((derivedPullback p).obj ((derivedPullback q).obj E)) := by
  exact hasFiniteTorDimension_of_derivedPullback_iso r s E
    ((derivedPullbackFactorIso p q _ hw).app E ≪≫
      ((derivedPullbackFactorIso r s _ rfl).app E).symm) h

/-- **Locally finite Tor dimension is preserved by derived pullback** along any morphism of
ringed spaces. -/
theorem locallyHasFiniteTorDimension_derivedPullback {X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (g : X ⟶ Y) (E : DerivedCategory (OXMod.{u, u} Y)) (h : LocallyHasFiniteTorDimension Y E) :
    LocallyHasFiniteTorDimension X ((derivedPullback g).obj E) :=
  (locallyHasFiniteTorDimension_iff_forall_mem ((derivedPullback g).obj E)).2 fun x => by
    obtain ⟨W, hxW, hW⟩ := (locallyHasFiniteTorDimension_iff_forall_mem E).1 h (g.hom.base x)
    refine ⟨(Opens.map g.hom.base).obj W, hxW, hasFiniteTorDimension_of_iso
      ((derivedRestrictModulesIsoDerivedPullback X _).app _).symm ?_⟩
    exact hasFiniteTorDimension_derivedPullback_of_comm _ g
      (Stacks.Cohomology.HigherDirectImage.restrictedMorphism g W) _
      (Stacks.Cohomology.HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion g W) E
      (hasFiniteTorDimension_of_iso ((derivedRestrictModulesIsoDerivedPullback Y W).app E) hW)

/-- **Finite Tor dimension pulls back along a factorisation.** If `Ls^*E` has finite Tor
dimension and `σ ≫ s = t`, then `Lt^*E` has finite Tor dimension. -/
theorem hasFiniteTorDimension_derivedPullback_of_factor
    {A B D : AlgebraicGeometry.RingedSpace.{u, u}}
    (σ : A ⟶ B) (s : B ⟶ D) (t : A ⟶ D) (hw : σ ≫ s = t) (E : DerivedCategory (OXMod.{u, u} D))
    (h : HasFiniteTorDimension B ((derivedPullback s).obj E)) :
    HasFiniteTorDimension A ((derivedPullback t).obj E) := by
  exact hasFiniteTorDimension_of_derivedPullback_iso σ s E
    ((derivedPullbackFactorIso σ s t hw).app E).symm h

/-- The image of an open of the source of an open immersion of ringed spaces, as an open of the
target. -/
def openImmersionImage {U X : AlgebraicGeometry.RingedSpace.{u, u}} (j : U ⟶ X)
    [AlgebraicGeometry.SheafedSpace.IsOpenImmersion j] (W : Opens U.carrier) : Opens X.carrier :=
  (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open (f := j.hom)).isOpenMap.functor.obj W

/-- The inclusion of the image of `W` factors through `W` followed by the open immersion. -/
theorem range_ofRestrict_openImmersionImage_subset {U X : AlgebraicGeometry.RingedSpace.{u, u}}
    (j : U ⟶ X) [AlgebraicGeometry.SheafedSpace.IsOpenImmersion j] (W : Opens U.carrier) :
    Set.range (X.ofRestrict (openImmersionImage j W).isOpenEmbedding).hom.base ⊆
      Set.range (U.ofRestrict W.isOpenEmbedding ≫ j).hom.base := by
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨⟨y, hy⟩, rfl⟩

/-- **Locally finite Tor dimension glues along a covering by open immersions.** If the open
immersions `j k : U k ⟶ X` cover `X` and every `Lj_k^*E` locally has finite Tor dimension, then so
does `E`. -/
theorem locallyHasFiniteTorDimension_of_openImmersion_cover
    {X : AlgebraicGeometry.RingedSpace.{u, u}} {κ : Type*}
    (U : κ → AlgebraicGeometry.RingedSpace.{u, u}) (j : ∀ k, U k ⟶ X)
    [∀ k, AlgebraicGeometry.SheafedSpace.IsOpenImmersion (j k)]
    (hcov : ∀ x : X.carrier, ∃ k, x ∈ Set.range (j k).hom.base)
    (E : DerivedCategory (OXMod.{u, u} X))
    (h : ∀ k, LocallyHasFiniteTorDimension (U k) ((derivedPullback (j k)).obj E)) :
    LocallyHasFiniteTorDimension X E :=
  (locallyHasFiniteTorDimension_iff_forall_mem E).2 fun x => by
    obtain ⟨k, y, rfl⟩ := hcov x
    obtain ⟨W, hyW, hW⟩ := (locallyHasFiniteTorDimension_iff_forall_mem _).1 (h k) y
    refine ⟨openImmersionImage (j k) W, ⟨y, hyW, rfl⟩, hasFiniteTorDimension_restrict_of_factor _
      (AlgebraicGeometry.RingedSpace.openImmersionLift ((U k).ofRestrict W.isOpenEmbedding ≫ j k)
        _ (range_ofRestrict_openImmersionImage_subset (j k) W))
      ((U k).ofRestrict W.isOpenEmbedding ≫ j k)
      (AlgebraicGeometry.RingedSpace.openImmersionLift_fac _ _ _) E ?_⟩
    exact hasFiniteTorDimension_of_iso
      (((derivedRestrictModulesIsoDerivedPullback (U k) W).app _) ≪≫
        (derivedPullbackFactorIso _ (j k) _ rfl).app E) hW

/-- **Locally finite Tor dimension glues along an open covering.** -/
theorem locallyHasFiniteTorDimension_of_iSup_eq_top {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {κ : Type*} (V : κ → Opens X.carrier) (hV : iSup V = ⊤) (E : DerivedCategory (OXMod.{u, u} X))
    (h : ∀ k, LocallyHasFiniteTorDimension (X.restrict (V k).isOpenEmbedding)
      ((derivedRestrictModules X (V k)).obj E)) :
    LocallyHasFiniteTorDimension X E :=
  locallyHasFiniteTorDimension_of_openImmersion_cover _
    (fun k => X.ofRestrict (V k).isOpenEmbedding)
    (fun x => by
      obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show x ∈ iSup V by rw [hV]; trivial)
      exact ⟨k, ⟨x, hk⟩, rfl⟩) E
    (fun k => locallyHasFiniteTorDimension_of_iso
      ((derivedRestrictModulesIsoDerivedPullback X (V k)).app E) (h k))

end Stacks.Cohomology.TorAmplitude


namespace AlgebraicGeometry.RingedSpace

open Stacks.Cohomology.TorAmplitude (derivedPullbackFactorIso openImmersionImage)

/-- The range of an open immersion of ringed spaces, as an open of the target. -/
abbrev openImmersionRange {U X : RingedSpace.{u, u}} (j : U ⟶ X)
    [SheafedSpace.IsOpenImmersion j] : Opens X.carrier :=
  openImmersionImage j ⊤

/-- The inclusion of the range of an open immersion factors through it. -/
theorem range_ofRestrict_openImmersionRange_subset {U X : RingedSpace.{u, u}} (j : U ⟶ X)
    [SheafedSpace.IsOpenImmersion j] :
    Set.range (X.ofRestrict (openImmersionRange j).isOpenEmbedding).hom.base ⊆
      Set.range j.hom.base := by
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨y, -, rfl⟩ := hz
  exact ⟨y, rfl⟩

/-- **Pseudo-coherence glues along a covering by open immersions.** If the open immersions
`j k : U k ⟶ X` cover `X` and every `Lj_k^*E` is pseudo-coherent, then so is `E`. -/
theorem isPseudoCoherent_of_openImmersion_cover {X : RingedSpace.{u, u}} {κ : Type*}
    (U : κ → RingedSpace.{u, u}) (j : ∀ k, U k ⟶ X) [∀ k, SheafedSpace.IsOpenImmersion (j k)]
    (hcov : ∀ x : X.carrier, ∃ k, x ∈ Set.range (j k).hom.base)
    (E : DerivedCategory (OXMod.{u, u} X))
    (h : ∀ k, IsPseudoCoherent (X := U k) ((derivedPullback (j k)).obj E)) :
    IsPseudoCoherent (X := X) E :=
  (isPseudoCoherent_iff_forall E).2 fun m => isPseudoCoherentFrom_of_local_restrict E m fun x => by
    obtain ⟨k, y, rfl⟩ := hcov x
    refine ⟨openImmersionRange (j k), ⟨y, trivial, rfl⟩, ?_⟩
    have hpc := KFlatDerivedPullback.isPseudoCoherent_derivedPullback
      (openImmersionLift (j k) _ (range_ofRestrict_openImmersionRange_subset (j k))) _ (h k)
    have e := (derivedPullbackFactorIso _ (j k) _ (openImmersionLift_fac (j k)
        (X.ofRestrict (openImmersionRange (j k)).isOpenEmbedding)
        (range_ofRestrict_openImmersionRange_subset (j k)))).app E ≪≫
        ((derivedRestrictModulesIsoDerivedPullback X (openImmersionRange (j k))).app E).symm
    exact (IsPseudoCoherent.of_iso hpc e).isPseudoCoherentFrom m

end AlgebraicGeometry.RingedSpace


namespace AlgebraicGeometry.RingedSpace

open Stacks.Cohomology.HigherDirectImage (restrictedMorphism preimageOpen moduleRestriction
  restrictedMorphism_comp_openSubspaceInclusion modulePushforwardRestrictIso restrictToOpen
  openSubspaceInclusion)

section OpenImmersionSquare

/-- The inclusion of an open subspace is an open immersion. -/
local instance isOpenImmersion_ofRestrict_opens (Z : RingedSpace.{u, u}) (W : Opens Z.carrier) :
    SheafedSpace.IsOpenImmersion (Z.ofRestrict W.isOpenEmbedding) :=
  SheafedSpace.IsOpenImmersion.ofRestrict Z W.isOpenEmbedding

/-- The inclusion of an open subspace is an open immersion, in the `restrictToOpen` spelling. -/
local instance isOpenImmersion_openSubspaceInclusion (Z : RingedSpace.{u, u})
    (W : Opens Z.carrier) : SheafedSpace.IsOpenImmersion (openSubspaceInclusion Z W) :=
  SheafedSpace.IsOpenImmersion.ofRestrict Z W.isOpenEmbedding

/-- Morphisms into the source of an open immersion are determined by their composites with it. -/
theorem openImmersion_cancel {A Y Z : RingedSpace.{u, u}} (j : Y ⟶ Z)
    [SheafedSpace.IsOpenImmersion j] {g h : A ⟶ Y} (e : g ≫ j = h ≫ j) : g = h := by
  have : Mono j.hom := PresheafedSpace.IsOpenImmersion.mono j.hom
  exact InducedCategory.hom_ext ((cancel_mono j.hom).1 (congrArg (fun t => t.hom) e))

/-- **An open immersion is an isomorphism onto the open subspace cut out by its range.** -/
def isoOfRange {Y Z : RingedSpace.{u, u}} (j : Y ⟶ Z) [SheafedSpace.IsOpenImmersion j]
    (W : Opens Z.carrier) (h : Set.range j.hom.base = W) : Y ≅ restrictToOpen Z W where
  hom := openImmersionLift (openSubspaceInclusion Z W) j (by
    rw [h]; rintro x hx; exact ⟨⟨x, hx⟩, rfl⟩)
  inv := openImmersionLift j (openSubspaceInclusion Z W) (by
    rw [h]; rintro _ ⟨⟨x, hx⟩, rfl⟩; exact hx)
  hom_inv_id := openImmersion_cancel j (by simp)
  inv_hom_id := openImmersion_cancel (openSubspaceInclusion Z W) (by simp)

/-- The isomorphism `isoOfRange j W h`, followed by the inclusion of `W`, is `j`. -/
@[reassoc (attr := simp)]
theorem isoOfRange_hom_ofRestrict {Y Z : RingedSpace.{u, u}} (j : Y ⟶ Z)
    [SheafedSpace.IsOpenImmersion j] (W : Opens Z.carrier) (h : Set.range j.hom.base = W) :
    (isoOfRange j W h).hom ≫ openSubspaceInclusion Z W = j :=
  openImmersionLift_fac (openSubspaceInclusion Z W) j _

variable {U X P Q : RingedSpace.{u, u}} (a : U ⟶ P) (b : X ⟶ Q) (ι : U ⟶ X) (ψ : P ⟶ Q)
  [SheafedSpace.IsOpenImmersion ι] [SheafedSpace.IsOpenImmersion ψ] (hsq : ι ≫ b = a ≫ ψ)
  (W : Opens Q.carrier) (hψ : Set.range ψ.hom.base = W)
  (hι : Set.range ι.hom.base = (preimageOpen b W : Set X.carrier))

/-- Cancelling isomorphisms on both sides of a commutative square. -/
private theorem comp_inv_eq_inv_comp_of_comm {A B C D : RingedSpace.{u, u}} (e : A ≅ B)
    (e' : C ≅ D) (r : B ⟶ D) (t : A ⟶ C) (h : e.hom ≫ r = t ≫ e'.hom) :
    r ≫ e'.inv = e.inv ≫ t := by
  rw [Iso.eq_inv_comp, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A composite through the inclusion of an open subspace. -/
private theorem comp_eq_of_fac {A B C D E F : RingedSpace.{u, u}} (e : A ⟶ B) (r : B ⟶ C)
    (incl : C ⟶ E) (inclB : B ⟶ D) (b : D ⟶ E) (ι : A ⟶ D) (t : A ⟶ F) (ψ : F ⟶ E)
    (hr : inclB ≫ b = r ≫ incl) (he : e ≫ inclB = ι) (hsq : ι ≫ b = t ≫ ψ) :
    (e ≫ r) ≫ incl = t ≫ ψ := by
  rw [Category.assoc, ← hr, ← Category.assoc, he, hsq]

include hsq in
/-- In a commutative square whose vertical edges are open immersions, the restriction of the
bottom edge to the range of the right one is the top edge, transported along the two
identifications of the sources of the open immersions with their ranges. -/
theorem restrictedMorphism_comp_isoOfRange_inv :
    restrictedMorphism b W ≫ (isoOfRange ψ W hψ).inv =
      (isoOfRange ι (preimageOpen b W) hι).inv ≫ a := by
  refine comp_inv_eq_inv_comp_of_comm _ _ _ _ (openImmersion_cancel (openSubspaceInclusion Q W) ?_)
  refine (comp_eq_of_fac _ _ _ _ b ι a ψ (restrictedMorphism_comp_openSubspaceInclusion b W)
    (isoOfRange_hom_ofRestrict ι _ hι) hsq).trans ?_
  exact (congrArg (fun t => a ≫ t) (isoOfRange_hom_ofRestrict ψ W hψ)).symm.trans
    (Category.assoc _ _ _).symm

/-- **Pushforward and pullback around a square whose vertical edges are open immersions.** For a
commutative square `ι ≫ b = a ≫ ψ` with `ι` and `ψ` open immersions, the range of `ι` being the
preimage of the range of `ψ`, the two composites `ι^* ⋙ a_*` and `b_* ⋙ ψ^*` of module functors
agree. -/
def openImmersionSquareModuleIso :
    modulePullback ι ⋙ modulePushforward a ≅ modulePushforward b ⋙ modulePullback ψ :=
  Functor.isoWhiskerRight (modulePullbackCongr (isoOfRange_hom_ofRestrict ι _ hι).symm ≪≫
      modulePullbackComp _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (modulePullbackIsoPushforwardInv (isoOfRange ι _ hι)) _ ≪≫
      modulePushforwardComp _ _ ≪≫
      eqToIso (congrArg modulePushforward
        (restrictedMorphism_comp_isoOfRange_inv a b ι ψ hsq W hψ hι).symm) ≪≫
      (modulePushforwardComp _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso X _).symm _ ≪≫
      modulePushforwardRestrictIso b W ≪≫
      Functor.isoWhiskerLeft _
        (Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso Q W)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (modulePullbackIsoPushforwardInv (isoOfRange ψ W hψ)).symm ≪≫
      (modulePullbackComp _ _).symm ≪≫
      modulePullbackCongr (isoOfRange_hom_ofRestrict ψ W hψ))

/-- Pullback along an open immersion of ringed spaces is left exact. -/
local instance preservesFiniteLimits_modulePullback_of_isOpenImmersion {Y Z : RingedSpace.{u, u}}
    (j : Y ⟶ Z) [SheafedSpace.IsOpenImmersion j] : PreservesFiniteLimits (modulePullback j) :=
  (modulePullback j).preservesFiniteLimits_of_preservesHomology

/-- **The square of module functors on derived categories.** Under the hypotheses of
`openImmersionSquareModuleIso`, with `a_*` and `b_*` exact, `D(a_*) ∘ Lι^*` and `Lψ^* ∘ D(b_*)`
agree. -/
def derivedOpenImmersionSquareIso [(modulePushforward a).Additive]
    [PreservesFiniteLimits (modulePushforward a)] [PreservesFiniteColimits (modulePushforward a)]
    [(modulePushforward b).Additive]
    [PreservesFiniteLimits (modulePushforward b)] [PreservesFiniteColimits (modulePushforward b)]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (modulePushforward a).mapDerivedCategory.obj ((derivedPullback ι).obj E) ≅
      (derivedPullback ψ).obj ((modulePushforward b).mapDerivedCategory.obj E) :=
  (modulePushforward a).mapDerivedCategory.mapIso
      ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso ι).app E) ≪≫
    Scheme.Hom.derivedSquareOfNatIso E (modulePullback ι) (modulePushforward a)
      (modulePushforward b) (modulePullback ψ)
      (openImmersionSquareModuleIso a b ι ψ hsq W hψ hι) ≪≫
    ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso ψ).app _).symm

end OpenImmersionSquare

end AlgebraicGeometry.RingedSpace


namespace AlgebraicGeometry.Scheme.Hom

open RingedSpace (openImmersionRange)

section OpenImmersion

variable {X S U : Scheme.{u}} (f : X ⟶ S) (ι : U ⟶ X) [IsOpenImmersion ι]

/-- The square `(ι, 𝟙 S)` from `ι ≫ f` to `f`, in the arrow category of ringed spaces. -/
def openArrowHom : ringedArrow (ι ≫ f) ⟶ ringedArrow f :=
  Arrow.homMk (Scheme.forgetToRingedSpace.map ι) (𝟙 _) (by
    rw [Category.comp_id]
    exact (Scheme.forgetToRingedSpace.map_comp ι f).symm)

/-- **The inverse-image ringed space of `ι ≫ f` is an open subspace of that of `f`**: the
morphism `(U, (ι ≫ f)⁻¹𝒪_S) ⟶ (X, f⁻¹𝒪_S)` induced by `ι`. -/
def inverseImageOpenMap :
    RingedSpace.inverseImage S.toRingedSpace (ι ≫ f).base ⟶
      RingedSpace.inverseImage S.toRingedSpace f.base :=
  RingedSpace.inverseImageArrowMap (openArrowHom f ι)

/-- The open immersion `ι`, read as a morphism of ringed spaces, is an open immersion. -/
instance isOpenImmersion_forgetToRingedSpace_map :
    SheafedSpace.IsOpenImmersion (Scheme.forgetToRingedSpace.map ι) :=
  (inferInstance : IsOpenImmersion ι)

/-- `inverseImageOpenMap f ι` is an open immersion. -/
instance isOpenImmersion_inverseImageOpenMap :
    SheafedSpace.IsOpenImmersion (inverseImageOpenMap f ι) :=
  haveI : SheafedSpace.IsOpenImmersion (openArrowHom f ι).left :=
    isOpenImmersion_forgetToRingedSpace_map ι
  haveI : IsIso (openArrowHom f ι).right := (inferInstance : IsIso (𝟙 S.toRingedSpace))
  RingedSpace.isOpenImmersion_inverseImageArrowMap (openArrowHom f ι)

omit [IsOpenImmersion ι] in
/-- The underlying map of `inverseImageOpenMap` is that of `ι`. -/
theorem inverseImageOpenMap_base : (inverseImageOpenMap f ι).hom.base = ι.base := rfl

omit [IsOpenImmersion ι] in
/-- The units `(U, 𝒪_U) ⟶ (U, (ι ≫ f)⁻¹𝒪_S)` and `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` form a commutative
square with `ι` and `inverseImageOpenMap`. -/
theorem forgetToRingedSpace_map_comp_arrowUnit :
    Scheme.forgetToRingedSpace.map ι ≫ arrowUnit f =
      arrowUnit (ι ≫ f) ≫ inverseImageOpenMap f ι :=
  RingedSpace.inverseImageArrowUnit.naturality (openArrowHom f ι)

/-- The range of `inverseImageOpenMap` is the open it cuts out. -/
theorem range_inverseImageOpenMap :
    Set.range (inverseImageOpenMap f ι).hom.base = (openImmersionRange (inverseImageOpenMap f ι) :
      Set (RingedSpace.inverseImage S.toRingedSpace f.base).carrier) :=
  Set.image_univ.symm

/-- The range of `ι` is the preimage under the unit of the range of `inverseImageOpenMap`. -/
theorem range_forgetToRingedSpace_map :
    Set.range (Scheme.forgetToRingedSpace.map ι).hom.base =
      (Stacks.Cohomology.HigherDirectImage.preimageOpen (arrowUnit f)
        (openImmersionRange (inverseImageOpenMap f ι)) : Set X.carrier) := by
  ext x
  exact ⟨fun ⟨y, hy⟩ => ⟨y, trivial, hy⟩, fun ⟨y, _, hy⟩ => ⟨y, hy⟩⟩


/-- Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` is additive, in the pushforward spelling. -/
local instance additive_modulePushforward_arrowUnit :
    (modulePushforward (arrowUnit f)).Additive :=
  inferInstanceAs (scalarRestriction f).Additive

/-- The square of `derivedScalarRestrictionOpenImmersionIso`, in the pushforward spelling. -/
def derivedScalarRestrictionOpenImmersionIso'
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (modulePushforward (arrowUnit (ι ≫ f))).mapDerivedCategory.obj
        ((derivedPullback (Scheme.forgetToRingedSpace.map ι)).obj E) ≅
      (derivedPullback (inverseImageOpenMap f ι)).obj
        ((modulePushforward (arrowUnit f)).mapDerivedCategory.obj E) :=
  haveI : SheafedSpace.IsOpenImmersion (X := U.toRingedSpace) (Y := X.toRingedSpace)
      (Scheme.forgetToRingedSpace.map ι) := isOpenImmersion_forgetToRingedSpace_map ι
  RingedSpace.derivedOpenImmersionSquareIso (arrowUnit (ι ≫ f)) (arrowUnit f)
    (Scheme.forgetToRingedSpace.map ι) (inverseImageOpenMap f ι)
    (forgetToRingedSpace_map_comp_arrowUnit f ι) _ (range_inverseImageOpenMap f ι)
    (range_forgetToRingedSpace_map f ι) E

/-- **Derived restriction of scalars commutes with restriction along an open immersion.** For
`ι : U ⟶ X` an open immersion, derived restriction of scalars along `ι ≫ f` of `Lι^*E` is the
derived pullback along `inverseImageOpenMap f ι` of derived restriction of scalars along `f` of
`E`. -/
def derivedScalarRestrictionOpenImmersionIso
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (derivedScalarRestriction (ι ≫ f)).obj ((derivedPullback ι.toLRSHom.toShHom).obj E) ≅
      (derivedPullback (inverseImageOpenMap f ι)).obj ((derivedScalarRestriction f).obj E) := by
  rw [derivedScalarRestriction_eq_mapDerivedCategory (ι ≫ f),
    derivedScalarRestriction_eq_mapDerivedCategory f]
  exact derivedScalarRestrictionOpenImmersionIso' f ι E

/-- **The Tor-dimension clause of Stacks 0DI0 restricts along an open immersion.** If
`D(f⁻¹𝒪_S ⟶ 𝒪_X)(E)` locally has finite Tor dimension on `(X, f⁻¹𝒪_S)`, then
`D((ι ≫ f)⁻¹𝒪_S ⟶ 𝒪_U)(Lι^*E)` locally has finite Tor dimension on `(U, (ι ≫ f)⁻¹𝒪_S)`, at the
canonical certificate families. -/
theorem locallyHasFiniteTorDimension_torClause_comp_openImmersion
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : RingedSpace.LocallyHasFiniteTorDimension (RingedSpace.inverseImage S.toRingedSpace f.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedScalarRestriction f).obj E)) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace (ι ≫ f).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedScalarRestriction (ι ≫ f)).obj ((derivedPullback ι.toLRSHom.toShHom).obj E)) :=
  Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_iso
    (derivedScalarRestrictionOpenImmersionIso f ι E).symm
    (Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_derivedPullback
      (inverseImageOpenMap f ι) _ h)

end OpenImmersion

/-- **The Tor-dimension clause of Stacks 0DI0 glues along a covering by open immersions.** If
open immersions `ι k : U k ⟶ X` cover `X` and the clause holds for every `Lι_k^*E` relative to
`ι k ≫ f`, then it holds for `E` relative to `f`. -/
theorem locallyHasFiniteTorDimension_torClause_of_openImmersion_cover {X S : Scheme.{u}}
    (f : X ⟶ S) {κ : Type*} (U : κ → Scheme.{u}) (ι : ∀ k, U k ⟶ X) [∀ k, IsOpenImmersion (ι k)]
    (hcov : ∀ x : X, ∃ k, x ∈ Set.range (ι k).base)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : ∀ k, RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace (ι k ≫ f).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedScalarRestriction (ι k ≫ f)).obj ((derivedPullback (ι k).toLRSHom.toShHom).obj E))) :
    RingedSpace.LocallyHasFiniteTorDimension (RingedSpace.inverseImage S.toRingedSpace f.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedScalarRestriction f).obj E) :=
  Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_openImmersion_cover
    (fun k => RingedSpace.inverseImage S.toRingedSpace (ι k ≫ f).base)
    (fun k => inverseImageOpenMap f (ι k)) hcov _
    (fun k => Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_iso
      (derivedScalarRestrictionOpenImmersionIso f (ι k) E) (h k))

section RelativelyPerfect

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]

/-- **Relative perfectness of Stacks 0DI0 restricts along an open immersion.** If `E` is
`S`-perfect on `X`, then `Lι^*E` is `S`-perfect on `U` for every open immersion `ι : U ⟶ X`,
relative perfectness being read at the canonical certificate families. -/
theorem isPerfectRelativeTo_comp_openImmersion {U : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    (ι ≫ f).IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback ι.toLRSHom.toShHom).obj E) :=
  ⟨isPseudoCoherent_derivedPullback ι E h.1,
    locallyHasFiniteTorDimension_torClause_comp_openImmersion f ι E h.2⟩

/-- **Relative perfectness restricts to an open subscheme.** -/
theorem isPerfectRelativeTo_opens_ι (V : X.Opens)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    (V.ι ≫ f).IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback V.ι.toLRSHom.toShHom).obj E) :=
  isPerfectRelativeTo_comp_openImmersion f V.ι E h

/-- **Relative perfectness of Stacks 0DI0 is local on the source.** If open immersions
`ι k : U k ⟶ X` cover `X` and every `Lι_k^*E` is `S`-perfect relative to `ι k ≫ f`, then `E` is
`S`-perfect, at the canonical certificate families. -/
theorem isPerfectRelativeTo_of_openImmersion_cover {κ : Type*} (U : κ → Scheme.{u})
    (ι : ∀ k, U k ⟶ X) [∀ k, IsOpenImmersion (ι k)]
    (hcov : ∀ x : X, ∃ k, x ∈ Set.range (ι k).base)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : ∀ k, (ι k ≫ f).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback (ι k).toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E :=
  have : ∀ k, SheafedSpace.IsOpenImmersion (ι k).toLRSHom.toShHom := fun k =>
    (inferInstance : IsOpenImmersion (ι k))
  ⟨RingedSpace.isPseudoCoherent_of_openImmersion_cover (fun k => (U k).toRingedSpace)
      (fun k => (ι k).toLRSHom.toShHom) hcov E (fun k => (h k).1),
    locallyHasFiniteTorDimension_torClause_of_openImmersion_cover f U ι hcov E
      (fun k => (h k).2)⟩

/-- **Relative perfectness is local on the source, for an open covering.** -/
theorem isPerfectRelativeTo_of_iSup_eq_top {κ : Type*} (V : κ → X.Opens) (hV : iSup V = ⊤)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : ∀ k, ((V k).ι ≫ f).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback (V k).ι.toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E :=
  isPerfectRelativeTo_of_openImmersion_cover f (fun k => (V k).toScheme) (fun k => (V k).ι)
    (fun x => by
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (show x ∈ iSup V by rw [hV]; trivial)
      exact ⟨k, by rw [Scheme.Opens.range_ι]; exact hk⟩) E h

/-- **Relative perfectness is local on the source, for a covering by two open immersions.** -/
theorem isPerfectRelativeTo_of_two_openImmersions {U V : Scheme.{u}} (ιU : U ⟶ X)
    (ιV : V ⟶ X) [IsOpenImmersion ιU] [IsOpenImmersion ιV]
    (hcov : Set.range ιU.base ∪ Set.range ιV.base = Set.univ)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hU : (ιU ≫ f).IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback ιU.toLRSHom.toShHom).obj E))
    (hV : (ιV ≫ f).IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback ιV.toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E := by
  have : ∀ b : Bool, IsOpenImmersion
      (Bool.rec (motive := fun b => Bool.rec V U b ⟶ X) ιV ιU b) := fun b => by
    cases b <;> assumption
  refine isPerfectRelativeTo_of_openImmersion_cover f (fun b => Bool.rec V U b)
    (fun b => Bool.rec (motive := fun b => Bool.rec V U b ⟶ X) ιV ιU b) (fun x => ?_) E
    (fun b => by cases b <;> assumption)
  rcases hcov.superset (Set.mem_univ x) with hx | hx
  exacts [⟨true, hx⟩, ⟨false, hx⟩]

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **The Tor-dimension clause of Stacks 0DI0 glues along a covering by two open
immersions.** -/
theorem locallyHasFiniteTorDimension_torClause_of_two_openImmersions {U V : Scheme.{u}}
    (ιU : U ⟶ X) (ιV : V ⟶ X) [IsOpenImmersion ιU] [IsOpenImmersion ιV]
    (hcov : Set.range ιU.base ∪ Set.range ιV.base = Set.univ)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hU : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace (ιU ≫ f).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedScalarRestriction (ιU ≫ f)).obj ((derivedPullback ιU.toLRSHom.toShHom).obj E)))
    (hV : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace (ιV ≫ f).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedScalarRestriction (ιV ≫ f)).obj ((derivedPullback ιV.toLRSHom.toShHom).obj E))) :
    RingedSpace.LocallyHasFiniteTorDimension (RingedSpace.inverseImage S.toRingedSpace f.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedScalarRestriction f).obj E) := by
  have : ∀ b : Bool, IsOpenImmersion
      (Bool.rec (motive := fun b => Bool.rec V U b ⟶ X) ιV ιU b) := fun b => by
    cases b <;> assumption
  refine locallyHasFiniteTorDimension_torClause_of_openImmersion_cover f (fun b => Bool.rec V U b)
    (fun b => Bool.rec (motive := fun b => Bool.rec V U b ⟶ X) ιV ιU b) (fun x => ?_) E
    (fun b => by cases b <;> assumption)
  rcases hcov.superset (Set.mem_univ x) with hx | hx
  exacts [⟨true, hx⟩, ⟨false, hx⟩]

/-- **Relative perfectness is a pointwise condition on the source.** If every point of `X` has
an open neighbourhood `V` with `E|_V` perfect relative to `V.ι ≫ f`, then `E` is `S`-perfect. -/
theorem isPerfectRelativeTo_of_forall_mem (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ (V.ι ≫ f).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback V.ι.toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E := by
  choose V hxV hV using h
  exact isPerfectRelativeTo_of_openImmersion_cover f (fun x => (V x).toScheme) (fun x => (V x).ι)
    (fun x => ⟨x, by rw [Scheme.Opens.range_ι]; exact hxV x⟩) E hV

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **The Tor-dimension clause of Stacks 0DI0 is a pointwise condition on the source.** -/
theorem locallyHasFiniteTorDimension_torClause_of_forall_mem
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace (V.ι ≫ f).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedScalarRestriction (V.ι ≫ f)).obj ((derivedPullback V.ι.toLRSHom.toShHom).obj E))) :
    RingedSpace.LocallyHasFiniteTorDimension (RingedSpace.inverseImage S.toRingedSpace f.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedScalarRestriction f).obj E) := by
  choose V hxV hV using h
  exact locallyHasFiniteTorDimension_torClause_of_openImmersion_cover f (fun x => (V x).toScheme)
    (fun x => (V x).ι) (fun x => ⟨x, by rw [Scheme.Opens.range_ι]; exact hxV x⟩) E hV

end RelativelyPerfect

end AlgebraicGeometry.Scheme.Hom

end

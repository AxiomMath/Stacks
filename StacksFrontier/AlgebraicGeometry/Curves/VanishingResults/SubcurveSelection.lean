module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeDivisibility
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Irreducible
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Vanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.Pushforward
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedIntersectionIdeal
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.Topology.Dimension.NowhereDense
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.FiniteRank
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionDegree
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteFlatLocallyFree
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Choosing a subcurve on which a map into the dualizing sheaf is injective

Let `X` be a reduced Noetherian scheme of dimension at most one, `Z ⊆ X` a closed subscheme with
ideal sheaf `ℐ`, and `ω` an `𝒪_X`-module admitting no nonzero map with zero-dimensional image from
a coherent module; the dualizing sheaf of a proper curve over a field is one, by duality, and so
is any twist of it by an invertible module. Given a nonzero map `φ : ℐ ⟶ ω`, this file produces a
connected closed subset `T ⊆ X` of dimension one, with reduced structure `Y`, and an injective
nonzero map into `ω` from the image `ℐ𝒪_Y` of `ℐ` in `𝒪_Y`. This is the step of the proof of
[Stacks, Tag 0E3E] which finds the subcurve `Y`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.NoZeroDimensionalImages`: the condition on `ω`.
* `AlgebraicGeometry.Scheme.IdealSheafData.idealToClosedSubscheme`: `ℐ_Z ⟶ 𝒪_X ⟶ 𝒪_Y`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_isPreconnected_mono`: the choice of `T`.
* `Stacks.Duality.noZeroDimensionalImages_dualizingSheafOverField`: the
  dualizing sheaf of a proper curve has no zero-dimensional images.
* `AlgebraicGeometry.Scheme.Modules.noZeroDimensionalImages_inverse_tensorLeft`: nor does its
  twist by the inverse of an invertible module.

## Implementation notes

The source takes for `Y` the union of the components on which `φ` is generically nonzero, shows
that `φ` factors through `ℐ𝒪_Y` because `ω` has no embedded points, and then passes to a connected
component. Here `T` is instead chosen minimal, for the Noetherian order on closed sets, among
those for which some nonzero map `ℐ ⟶ ω` kills `ℐ ∩ ℐ_T`. Minimality gives at once that the
induced map on `ℐ𝒪_T` is injective, that `T` is connected and that it has dimension one; the
three arguments are `exists_lt_of_not_mono`, `exists_add_of_disjoint` and
`eq_zero_of_topologicalKrullDim_support_le_zero`. The generic-point bookkeeping is done with
lengths of stalks: at the generic point of a component of the reduced subscheme `Y` the stalk of
`𝒪_Y` has length one.

## References

* [Stacks Project, Tag 0E3E](https://stacks.math.columbia.edu/tag/0E3E)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Lengths of stalks -/

/-- A monomorphism of modules does not increase the length of stalks. -/
theorem length_stalk_le_of_mono {A B : X.Modules} (f : A ⟶ B) [Mono f] (x : X) :
    Module.length (X.presheaf.stalk x) (A.presheaf.stalk x) ≤
      Module.length (X.presheaf.stalk x) (B.presheaf.stalk x) := by
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f) inferInstance inferInstance
  rw [length_stalk_add_of_shortExact hS x]
  exact le_self_add

/-- An epimorphism of modules does not increase the length of stalks. -/
theorem length_stalk_le_of_epi {A B : X.Modules} (f : A ⟶ B) [Epi f] (x : X) :
    Module.length (X.presheaf.stalk x) (B.presheaf.stalk x) ≤
      Module.length (X.presheaf.stalk x) (A.presheaf.stalk x) := by
  have hS : (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).ShortExact :=
    ShortComplex.shortExact_mk_kernel_ι f
  rw [length_stalk_add_of_shortExact hS x]
  exact le_add_self

/-- A stalk has length zero exactly off the support. -/
theorem length_stalk_eq_zero_iff (M : X.Modules) (x : X) :
    Module.length (X.presheaf.stalk x) (M.presheaf.stalk x) = 0 ↔
      x ∉ _root_.SheafOfModules.supp M := by
  rw [Module.length_eq_zero_iff]
  constructor
  · rintro h ⟨a, ha⟩
    exact ha (@Subsingleton.elim _ h a 0)
  · intro h
    exact subsingleton_stalk_of_notMem_supp M h

namespace Scheme.IdealSheafData

/-- The composite `ℐ_Z ⟶ 𝒪_X ⟶ 𝒪_Y` of the ideal sheaf of `Z` with the restriction to `Y`. -/
abbrev idealToClosedSubscheme (Z Y : X.IdealSheafData) :
    kernel (ambientToClosedSubscheme Z) ⟶ closedSubschemeStructureSheaf Y :=
  kernel.ι (ambientToClosedSubscheme Z) ≫ ambientToClosedSubscheme Y

/-- The structure sheaf of a closed subscheme, as a module on the ambient scheme, is supported on
the support of the subscheme. -/
theorem supp_closedSubschemeStructureSheaf (Y : X.IdealSheafData) :
    _root_.SheafOfModules.supp (closedSubschemeStructureSheaf Y) = (Y.support : Set X) :=
  Scheme.Modules.supp_pushforwardStructureSheaf_subschemeι Y

/-- **The stalk of `𝒪_Y` at the generic point of an irreducible component of a reduced closed
subscheme `Y` has length one**: it is the local ring of `Y` there, a field. -/
@[ega "IV 3.2.1" "a) ⇒ c)"]
theorem length_stalk_closedSubschemeStructureSheaf_of_mem_genericPoints (Y : X.IdealSheafData)
    [IsReduced Y.subscheme] {y : Y.subscheme} (hy : y ∈ genericPoints Y.subscheme) :
    Module.length (X.presheaf.stalk (Y.subschemeι y))
      ((closedSubschemeStructureSheaf Y).presheaf.stalk (Y.subschemeι y)) = 1 := by
  rw [length_stalk_pushforward_unit_of_isClosedImmersion Y.subschemeι y]
  let := (isField_stalk_of_closure_mem_irreducibleComponents Y.subscheme y hy).toField
  exact Module.length_eq_one _ _

/-- The structure sheaf of a locally Noetherian scheme is coherent, at the spelling of the union
sequence. -/
theorem isCoherent_ambientStructureSheaf [IsLocallyNoetherian X] :
    (ambientStructureSheaf X).IsCoherent :=
  Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit

/-- The structure sheaf of a closed subscheme of a locally Noetherian scheme, read on the ambient
scheme, is coherent. -/
theorem isCoherent_closedSubschemeStructureSheaf [IsLocallyNoetherian X] (Y : X.IdealSheafData) :
    (closedSubschemeStructureSheaf Y).IsCoherent :=
  Stacks.Chow.isCoherent_pushforwardStructureSheaf Y.subschemeι

/-- The ideal sheaf of a closed subscheme of a locally Noetherian scheme is coherent. -/
theorem isCoherent_kernel_ambientToClosedSubscheme [IsLocallyNoetherian X]
    (Z : X.IdealSheafData) : (kernel (ambientToClosedSubscheme Z)).IsCoherent :=
  Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules
    (isCoherent_ambientStructureSheaf (X := X)) (isCoherent_closedSubschemeStructureSheaf Z) _

/-- The coimage of `ℐ_Z ⟶ 𝒪_Y` is coherent. -/
theorem isCoherent_coimage_idealToClosedSubscheme [IsLocallyNoetherian X]
    (Z Y : X.IdealSheafData) : (Abelian.coimage (idealToClosedSubscheme Z Y)).IsCoherent :=
  Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel_modules
    (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules
      (isCoherent_kernel_ambientToClosedSubscheme Z) (isCoherent_closedSubschemeStructureSheaf Y) _)
    (isCoherent_kernel_ambientToClosedSubscheme Z) _

/-- The coimage of `ℐ_Z ⟶ 𝒪_Y` is supported on `Y`. -/
theorem supp_coimage_idealToClosedSubscheme_subset (Z Y : X.IdealSheafData) :
    _root_.SheafOfModules.supp (Abelian.coimage (idealToClosedSubscheme Z Y)) ⊆
      (Y.support : Set X) :=
  (supp_subset_of_mono (Abelian.factorThruCoimage (idealToClosedSubscheme Z Y))).trans
    (supp_closedSubschemeStructureSheaf Y).subset


end Scheme.IdealSheafData

/-! ### Modules annihilated by the ideal of a closed subscheme

A module `M` on `X` is annihilated by the ideal sheaf of a closed subscheme `Y` exactly when it is
a direct image `i_* M'` from `Y` ([Stacks, Tag 08KS],
`Stacks.ClosedImmersion.pushforward_essImage_iff`). The following lemmas record how this
condition behaves under submodules, quotients, direct sums and the lattice operations on closed
subschemes. -/

open Opposite in
/-- **A submodule of a module annihilated by `ℐ_Y` is annihilated by `ℐ_Y`.** -/
theorem essImage_pushforward_of_mono (Y : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N)
    [Mono f] (hN : (Scheme.Modules.pushforward Y.subschemeι).essImage N) :
    (Scheme.Modules.pushforward Y.subschemeι).essImage M := by
  rw [Stacks.ClosedImmersion.pushforward_essImage_iff] at hN ⊢
  intro U a ha m
  refine Scheme.Modules.injective_app_of_mono f U ?_
  rw [Scheme.Modules.Hom.app_smul, hN U a ha, map_zero]

/-! ### Torsion-freeness of the structure sheaf of a reduced closed subscheme -/

open Opposite in
/-- **On a reduced scheme a nonzero section has a nonzero germ at a generic point of an
irreducible component.** Its nonvanishing locus is a nonempty open set, which contains the
generic point of a component through any of its points. -/
theorem exists_mem_genericPoints_germ_ne_zero {Y : Scheme.{u}} [IsReduced Y] {V : Y.Opens}
    (t : Γ(Y, V)) (ht : t ≠ 0) :
    ∃ (y : Y) (hy : y ∈ V), y ∈ genericPoints Y ∧ Y.presheaf.germ V y hy t ≠ 0 := by
  have hb : Y.basicOpen t ≠ ⊥ := fun h => ht ((basicOpen_eq_bot_iff t).mp h)
  obtain ⟨z, hz⟩ : ∃ z, z ∈ Y.basicOpen t := by
    by_contra! h
    exact hb (eq_bot_iff.2 fun x hx => (h x hx).elim)
  let C : irreducibleComponents Y :=
    ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  have hηz : (genericPoints.ofComponent C).1 ⤳ z := specializes_iff_mem_closure.mpr <|
    (genericPoints.isGenericPoint_ofComponent C).symm ▸ mem_irreducibleComponent
  have hηb : (genericPoints.ofComponent C).1 ∈ Y.basicOpen t :=
    hηz.mem_open (Y.basicOpen t).isOpen hz
  have hηV : (genericPoints.ofComponent C).1 ∈ V := Y.basicOpen_le t hηb
  exact ⟨_, hηV, (genericPoints.ofComponent C).2, ((Y.mem_basicOpen t _ hηV).mp hηb).ne_zero⟩

/-- A module all of whose sections vanish is zero. -/
theorem Scheme.Modules.isZero_of_forall_sections {M : X.Modules}
    (h : ∀ (U : X.Opens) (s : Γ(M, U)), s = 0) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  exact (h U _).trans (h U _).symm

open Opposite in
/-- **A nonzero submodule of the structure sheaf of a reduced closed subscheme `Y` is nonzero at
a generic point of `Y`.** A nonzero section is a nonzero function on an open subset of `Y`, which
has a nonzero germ at a generic point of `Y`
(`AlgebraicGeometry.exists_mem_genericPoints_germ_ne_zero`), and then so does the section. -/
theorem Scheme.IdealSheafData.exists_mem_genericPoints_mem_supp (Y : X.IdealSheafData)
    [IsReduced Y.subscheme] {M : X.Modules} (f : M ⟶ closedSubschemeStructureSheaf Y) [Mono f]
    (hM : ¬ IsZero M) :
    ∃ y ∈ genericPoints Y.subscheme, Y.subschemeι y ∈ _root_.SheafOfModules.supp M := by
  obtain ⟨U, s, hs⟩ : ∃ (U : X.Opens) (s : Γ(M, U)), s ≠ 0 := by
    by_contra! h
    exact hM (Scheme.Modules.isZero_of_forall_sections h)
  have ht : f.app U s ≠ 0 := fun h0 =>
    hs (Scheme.Modules.injective_app_of_mono f U (h0.trans (map_zero _).symm))
  obtain ⟨y, hy, hgen, hgerm⟩ := exists_mem_genericPoints_germ_ne_zero
    (V := Y.subschemeι ⁻¹ᵁ U) (f.app U s) ht
  refine ⟨y, hgen, M.presheaf.germ U (Y.subschemeι y) hy s, fun h0 => hgerm ?_⟩
  obtain ⟨W, hW, iU, _iV, hres⟩ := TopCat.Presheaf.germ_eq M.presheaf (Y.subschemeι y) hy hy s 0
    (h0.trans (map_zero _).symm)
  rw [map_zero] at hres
  have hnat : (closedSubschemeStructureSheaf Y).presheaf.map iU.op (f.app U s) =
      f.app W (M.presheaf.map iU.op s) :=
    (ConcreteCategory.congr_hom (f.mapPresheaf.naturality iU.op) s).symm
  rw [hres, map_zero] at hnat
  have hgy := TopCat.Presheaf.germ_res_apply Y.subscheme.presheaf
    ((TopologicalSpace.Opens.map Y.subschemeι.base).map iU) y hW (f.app U s)
  rw [← hgy]
  show Y.subscheme.presheaf.germ _ y hW
    ((closedSubschemeStructureSheaf Y).presheaf.map iU.op (f.app U s)) = 0
  rw [hnat]
  exact map_zero _

/-! ### Lengths of images -/

/-- The image of a morphism has stalks no longer than those of its source. -/
theorem length_stalk_image_le_source {A B : X.Modules} (g : A ⟶ B) (x : X) :
    Module.length (X.presheaf.stalk x) ((Abelian.image g).presheaf.stalk x) ≤
      Module.length (X.presheaf.stalk x) (A.presheaf.stalk x) :=
  length_stalk_le_of_epi (Abelian.factorThruImage g) x

/-- The image of `f ≫ g` maps to zero in the cokernel of `g`. -/
private theorem image_ι_comp_cokernel_π_eq_zero {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) :
    Abelian.image.ι (f ≫ g) ≫ cokernel.π g = 0 := by
  rw [← cokernel.π_desc (f ≫ g) (cokernel.π g) (by simp), ← Category.assoc,
    kernel.condition, zero_comp]

/-- The image of a composite has stalks no longer than those of the image of its second
factor. -/
theorem length_stalk_image_comp_le {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (x : X) :
    Module.length (X.presheaf.stalk x) ((Abelian.image (f ≫ g)).presheaf.stalk x) ≤
      Module.length (X.presheaf.stalk x) ((Abelian.image g).presheaf.stalk x) := by
  have h := image_ι_comp_cokernel_π_eq_zero f g
  have : Mono (kernel.lift (cokernel.π g) (Abelian.image.ι (f ≫ g)) h) :=
    mono_of_mono_fac (kernel.lift_ι _ _ h)
  exact length_stalk_le_of_mono (kernel.lift (cokernel.π g) (Abelian.image.ι (f ≫ g)) h) x

/-- Lengths of stalks are invariant under isomorphism. -/
theorem length_stalk_eq_of_iso {A B : X.Modules} (e : A ≅ B) (x : X) :
    Module.length (X.presheaf.stalk x) (A.presheaf.stalk x) =
      Module.length (X.presheaf.stalk x) (B.presheaf.stalk x) :=
  le_antisymm (length_stalk_le_of_mono e.hom x) (length_stalk_le_of_mono e.inv x)

/-- Precomposing with an epimorphism does not shrink the image. -/
theorem length_stalk_image_le_image_comp_of_epi {A B C : X.Modules} (f : A ⟶ B) [Epi f]
    (g : B ⟶ C) (x : X) :
    Module.length (X.presheaf.stalk x) ((Abelian.image g).presheaf.stalk x) ≤
      Module.length (X.presheaf.stalk x) ((Abelian.image (f ≫ g)).presheaf.stalk x) := by
  have h := image_ι_comp_cokernel_π_eq_zero f g
  have hfac : Abelian.factorThruImage (f ≫ g) ≫
      kernel.lift (cokernel.π g) (Abelian.image.ι (f ≫ g)) h = f ≫ Abelian.factorThruImage g := by
    refine (cancel_mono (Abelian.image.ι g)).mp ?_
    simp
  have : Epi (kernel.lift (cokernel.π g) (Abelian.image.ι (f ≫ g)) h) := by
    have : Epi (f ≫ Abelian.factorThruImage g) := epi_comp _ _
    rw [← hfac] at this
    exact epi_of_epi (Abelian.factorThruImage (f ≫ g)) _
  exact length_stalk_le_of_epi (kernel.lift (cokernel.π g) (Abelian.image.ι (f ≫ g)) h) x

/-- Equal morphisms have images with stalks of equal length. -/
theorem length_stalk_image_congr {A B : X.Modules} {f g : A ⟶ B} (h : f = g) (x : X) :
    Module.length (X.presheaf.stalk x) ((Abelian.image f).presheaf.stalk x) =
      Module.length (X.presheaf.stalk x) ((Abelian.image g).presheaf.stalk x) := by
  rw [h]

/-- The stalk length of the source of a morphism is that of its kernel plus that of its image. -/
theorem length_stalk_eq_kernel_add_image {A B : X.Modules} (g : A ⟶ B) (x : X) :
    Module.length (X.presheaf.stalk x) (A.presheaf.stalk x) =
      Module.length (X.presheaf.stalk x) ((kernel g).presheaf.stalk x) +
        Module.length (X.presheaf.stalk x) ((Abelian.image g).presheaf.stalk x) := by
  have hS : (ShortComplex.mk (kernel.ι g) (cokernel.π (kernel.ι g))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  rw [length_stalk_add_of_shortExact hS x]
  exact congrArg _ (length_stalk_eq_of_iso (Abelian.coimageIsoImage g) x)

/-! ### Choosing the subcurve -/

/-- A module `ω` such that every map into it from a coherent module, whose image is supported in
dimension at most zero, vanishes. On a proper curve the dualizing sheaf has this property by
duality, since such an image has no first cohomology. -/
def Scheme.Modules.NoZeroDimensionalImages (ω : X.Modules) : Prop :=
  ∀ (Q : X.Modules), Q.IsCoherent → ∀ g : Q ⟶ ω,
    topologicalKrullDim (_root_.SheafOfModules.supp (Abelian.image g)) ≤ 0 → g = 0

namespace Scheme.IdealSheafData

open TopologicalSpace

/-- **A map `ℐ_Z ⟶ ω` factoring through `𝒪_Y` for a zero-dimensional `Y` vanishes**, when `ω`
has no nonzero map with zero-dimensional image from a coherent module: it factors through the
coimage of `ℐ_Z ⟶ 𝒪_Y`, a coherent module supported on `Y`. -/
theorem eq_zero_of_topologicalKrullDim_support_le_zero [IsLocallyNoetherian X]
    (Z Y : X.IdealSheafData) (hY : topologicalKrullDim (Y.support : Set X) ≤ 0)
    {ω : X.Modules} (hω : Scheme.Modules.NoZeroDimensionalImages ω)
    (φ : kernel (ambientToClosedSubscheme Z) ⟶ ω)
    (hφ : kernel.ι (idealToClosedSubscheme Z Y) ≫ φ = 0) : φ = 0 := by
  rw [← cokernel.π_desc _ φ hφ]
  have hsub : _root_.SheafOfModules.supp (Abelian.image (cokernel.desc _ φ hφ)) ⊆
      (Y.support : Set X) :=
    (Stacks.Chow.supp_subset_of_epi (Abelian.factorThruImage _)).trans
      (supp_coimage_idealToClosedSubscheme_subset Z Y)
  have hdim : topologicalKrullDim
      (_root_.SheafOfModules.supp (Abelian.image (cokernel.desc _ φ hφ))) ≤ 0 :=
    ((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans hY
  rw [hω _ (isCoherent_coimage_idealToClosedSubscheme Z Y) (cokernel.desc _ φ hφ) hdim, comp_zero]

end Scheme.IdealSheafData



/-- **The generic point of a component of a closed subspace is not in the closure of the rest of
the subspace.** For a closed embedding `i : Y → X` of a Noetherian space and a generic point `y`
of an irreducible component of `Y`, the point `i y` is not in the closure of
`range i \ closure {i y}`. -/
theorem _root_.Topology.IsClosedEmbedding.notMem_closure_range_diff {Y X : Type*}
    [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace.NoetherianSpace Y] {i : Y → X}
    (hi : Topology.IsClosedEmbedding i) {y : Y} (hy : y ∈ genericPoints Y) :
    i y ∉ closure (Set.range i \ closure {i y}) := by
  have hpre : i ⁻¹' closure {i y} = closure {y} := by
    rw [hi.isInducing.closure_eq_preimage_closure_image {y}, Set.image_singleton]
  have himg : Set.range i \ closure {i y} = i '' (closure {y})ᶜ := by
    rw [← hpre, Set.image_compl_preimage]
  rw [himg, hi.closure_image_eq]
  rintro ⟨z, hz, hzy⟩
  rw [hi.injective hzy] at hz
  exact not_subset_closure_compl_of_mem_irreducibleComponents hy subset_rfl
    (closure_minimal (Set.singleton_subset_iff.mpr hz) isClosed_closure)

/-- The coimage of a morphism between coherent modules is coherent. -/
theorem isCoherent_coimage [IsLocallyNoetherian X] {A B : X.Modules} (hA : A.IsCoherent)
    (hB : B.IsCoherent) (g : A ⟶ B) : (Abelian.coimage g).IsCoherent :=
  Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel_modules
    (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules hA hB g) hA _

namespace Scheme.IdealSheafData

open TopologicalSpace

/-- A map into `ℐ_Z` that dies in `𝒪_A` and in `𝒪_B` dies in `𝒪_{A ⊓ B}`. -/
private theorem comp_idealToClosedSubscheme_inf_eq_zero (Z A B : X.IdealSheafData)
    {W : X.Modules} (x : W ⟶ kernel (ambientToClosedSubscheme Z))
    (hA : x ≫ idealToClosedSubscheme Z A = 0) (hB : x ≫ idealToClosedSubscheme Z B = 0) :
    x ≫ idealToClosedSubscheme Z (A ⊓ B) = 0 := by
  simpa only [idealToClosedSubscheme, ← Category.assoc] using
    comp_ambientToClosedSubscheme_inf_eq_zero A B (x ≫ kernel.ι (ambientToClosedSubscheme Z))
      (by simpa only [idealToClosedSubscheme, Category.assoc] using hA)
      (by simpa only [idealToClosedSubscheme, Category.assoc] using hB)

/-- **If `φ : ℐ_Z ⟶ ω` kills `ℐ_Z ∩ ℐ_T` but is not injective on the coimage of `ℐ_Z ⟶ 𝒪_T`, it
kills `ℐ_Z ∩ ℐ_{T'}` for a smaller closed set `T'`.** The kernel of the induced map is a nonzero
submodule of `𝒪_T` for the reduced structure on `T`, so it is nonzero at the generic point `η` of
some component `C` of `T`, where the coimage has length at most one; hence `φ` vanishes at `η`.
For `T'` the closure of `T \ C`, the restriction of `φ` to `ℐ_Z ∩ ℐ_{T'}` factors through a
coherent module supported on `C`, as `ℐ_Z ∩ ℐ_{T'} ∩ ℐ_C ⊆ ℐ_Z ∩ ℐ_T`, with image vanishing at
`η`; that image is supported in dimension zero, so the restriction vanishes. -/
theorem exists_lt_of_not_mono [IsLocallyNoetherian X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (Z : X.IdealSheafData) (T : Closeds X)
    {ω : X.Modules} (hω : Scheme.Modules.NoZeroDimensionalImages ω)
    (φ : kernel (ambientToClosedSubscheme Z) ⟶ ω)
    (hφ : kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T)) ≫ φ = 0)
    (hmono : ¬ Mono (cokernel.desc _ φ hφ)) :
    ∃ T' : Closeds X, T' < T ∧
      kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T')) ≫ φ = 0 := by
  set Y := vanishingIdeal T with hY
  set β := idealToClosedSubscheme Z Y with hβ
  set ψ := cokernel.desc (kernel.ι β) φ hφ with hψ
  have hK : ¬ IsZero (kernel ψ) := fun h =>
    hmono (Preadditive.mono_of_kernel_zero (h.eq_of_src _ _))
  obtain ⟨y, hygen, hysupp⟩ := exists_mem_genericPoints_mem_supp Y
    (kernel.ι ψ ≫ Abelian.factorThruCoimage β) hK
  set η := Y.subschemeι y with hη
  -- `φ` vanishes at `η`.
  have hC1 : Module.length (X.presheaf.stalk η) ((Abelian.coimage β).presheaf.stalk η) ≤ 1 :=
    (length_stalk_le_of_mono (Abelian.factorThruCoimage β) η).trans
      (length_stalk_closedSubschemeStructureSheaf_of_mem_genericPoints Y hygen).le
  have hK1 : Module.length (X.presheaf.stalk η) ((kernel ψ).presheaf.stalk η) ≠ 0 :=
    fun h => (length_stalk_eq_zero_iff _ η).mp h hysupp
  have hψ0 : Module.length (X.presheaf.stalk η) ((Abelian.image ψ).presheaf.stalk η) = 0 := by
    by_contra hne
    have h := (add_le_add (Order.one_le_iff_ne_zero.mpr hK1)
      (Order.one_le_iff_ne_zero.mpr hne)).trans
        ((length_stalk_eq_kernel_add_image ψ η).symm.le.trans hC1)
    exact absurd h (by decide)
  have hφ0 : Module.length (X.presheaf.stalk η) ((Abelian.image φ).presheaf.stalk η) = 0 := by
    refine le_antisymm ?_ bot_le
    rw [← hψ0, ← cokernel.π_desc (kernel.ι β) φ hφ]
    exact length_stalk_image_comp_le _ _ η
  -- The component `C` through `η` and the rest `T'`.
  have hsT : (Y.support : Set X) = T := by rw [hY, coe_support_vanishingIdeal]
  have hηT : η ∈ (T : Set X) := by
    have : η ∈ Set.range Y.subschemeι := ⟨y, rfl⟩
    rwa [range_subschemeι, hsT] at this
  let C : Closeds X := ⟨closure {η}, isClosed_closure⟩
  let T' : Closeds X := ⟨closure ((T : Set X) \ closure {η}), isClosed_closure⟩
  have hCT : C ≤ T := closure_minimal (Set.singleton_subset_iff.mpr hηT) T.isClosed
  have hT'T : T' ≤ T := closure_minimal Set.sdiff_subset T.isClosed
  have hTsup : T = C ⊔ T' := by
    refine le_antisymm (fun x hx => ?_) (sup_le hCT hT'T)
    by_cases hxC : x ∈ closure {η}
    · exact Or.inl hxC
    · exact Or.inr (subset_closure ⟨hx, hxC⟩)
  have : NoetherianSpace Y.subscheme := Y.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  have hηT' : η ∉ (T' : Set X) := by
    have h := Y.subschemeι.isClosedEmbedding.notMem_closure_range_diff hygen
    rwa [range_subschemeι, hsT] at h
  refine ⟨T', lt_of_le_of_ne hT'T fun h => hηT' (h ▸ hηT), ?_⟩
  -- The restriction of `φ` to `ℐ_Z ∩ ℐ_{T'}` factors through `𝒪_C`.
  set β' := idealToClosedSubscheme Z (vanishingIdeal T') with hβ'
  set γ := kernel.ι β' ≫ idealToClosedSubscheme Z (vanishingIdeal C) with hγ
  have hfac : kernel.ι γ ≫ kernel.ι β' ≫ φ = 0 := by
    have h1 : (kernel.ι γ ≫ kernel.ι β') ≫ β = 0 := by
      have h := comp_idealToClosedSubscheme_inf_eq_zero Z (vanishingIdeal C) (vanishingIdeal T')
        (kernel.ι γ ≫ kernel.ι β')
        (by simpa only [hγ, Category.assoc] using kernel.condition γ)
        (by rw [Category.assoc, kernel.condition, comp_zero])
      rwa [← vanishingIdeal_sup, ← hTsup] at h
    rw [← Category.assoc, ← kernel.lift_ι β _ h1, Category.assoc, hφ, comp_zero]
  set ρ := cokernel.desc (kernel.ι γ) (kernel.ι β' ≫ φ) hfac with hρ
  have hQ : (Abelian.coimage γ).IsCoherent :=
    isCoherent_coimage (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules
      (isCoherent_kernel_ambientToClosedSubscheme Z) (isCoherent_closedSubschemeStructureSheaf _) _)
      (isCoherent_closedSubschemeStructureSheaf _) γ
  have hsubC : _root_.SheafOfModules.supp (Abelian.image ρ) ⊆ closure {η} := by
    refine (Stacks.Chow.supp_subset_of_epi (Abelian.factorThruImage ρ)).trans ?_
    refine (supp_subset_of_mono (Abelian.factorThruCoimage γ)).trans ?_
    rw [supp_closedSubschemeStructureSheaf, coe_support_vanishingIdeal]
    exact subset_rfl
  have hηS : η ∉ _root_.SheafOfModules.supp (Abelian.image ρ) := by
    refine (length_stalk_eq_zero_iff _ η).mp (le_antisymm ?_ bot_le)
    refine (length_stalk_image_le_image_comp_of_epi (cokernel.π (kernel.ι γ)) ρ η).trans ?_
    rw [length_stalk_image_congr (cokernel.π_desc _ _ hfac) η, ← hφ0]
    exact length_stalk_image_comp_le _ _ η
  have hft : (Abelian.image ρ).IsFiniteType := by
    have hep : Epi (Abelian.factorThruImage ρ) := inferInstance
    exact @Stacks.SheafOfModules.isFiniteType_of_epi'.{u} _ _ _ _ _ _ _ _ _
      (Abelian.factorThruImage ρ) hQ.isFiniteType hep
  have hcl : IsClosed (_root_.SheafOfModules.supp (Abelian.image ρ)) :=
    @_root_.SheafOfModules.isClosed_supp _ _ _ hft
  have hnd : IsNowhereDense (_root_.SheafOfModules.supp (Abelian.image ρ)) := by
    rw [hcl.isNowhereDense_iff_forall_irreducibleComponents_not_subset]
    intro D hD hDS
    exact hηS (hDS (hD.2 isIrreducible_singleton.closure (hDS.trans hsubC) (subset_closure rfl)))
  have hzero := hω _ hQ ρ (hnd.topologicalKrullDim_nonpos_of_le_one hcl hdim)
  rw [← cokernel.π_desc (kernel.ι γ) (kernel.ι β' ≫ φ) hfac, ← hρ, hzero, comp_zero]

/-- The vanishing ideals of two disjoint closed sets generate the unit ideal. -/
theorem vanishingIdeal_sup_eq_top_of_disjoint {T₁ T₂ : Closeds X}
    (h : Disjoint (T₁ : Set X) T₂) : vanishingIdeal T₁ ⊔ vanishingIdeal T₂ = ⊤ := by
  rw [← support_eq_bot_iff, support_sup]
  ext x
  simp only [Closeds.coe_inf, coe_support_vanishingIdeal, Closeds.coe_bot, Set.mem_empty_iff_false,
    iff_false]
  exact fun hx => Set.disjoint_left.mp h hx.1 hx.2

/-- **Splitting a map along a disconnection.** Let `T₁` and `T₂` be disjoint closed sets and let
`φ : ℐ_Z ⟶ ω` kill `ℐ_Z ∩ ℐ_{T₁ ∪ T₂}`. Then there is `φ₁` killing `ℐ_Z ∩ ℐ_{T₁}` and agreeing
with `φ` on `ℐ_Z ∩ ℐ_{T₂}`: the map `ℐ_Z ∩ ℐ_{T₂} ⟶ ℐ_Z / (ℐ_Z ∩ ℐ_{T₁})` is surjective, because
`ℐ_Z` is the sum of `ℐ_Z ∩ ℐ_{T₁}` and `ℐ_Z ∩ ℐ_{T₂}`, and its kernel lies in
`ℐ_Z ∩ ℐ_{T₁} ∩ ℐ_{T₂} = ℐ_Z ∩ ℐ_{T₁ ∪ T₂}`, which `φ` kills. -/
theorem exists_kills_of_disjoint (Z : X.IdealSheafData) {T₁ T₂ : Closeds X}
    (hd : Disjoint (T₁ : Set X) T₂) {ω : X.Modules} (φ : kernel (ambientToClosedSubscheme Z) ⟶ ω)
    (hφ : kernel.ι (idealToClosedSubscheme Z (vanishingIdeal (T₁ ⊔ T₂))) ≫ φ = 0) :
    ∃ φ₁ : kernel (ambientToClosedSubscheme Z) ⟶ ω,
      kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T₁)) ≫ φ₁ = 0 ∧
        kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T₂)) ≫ φ₁ =
          kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T₂)) ≫ φ := by
  set ι₁ := kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T₁)) with hι₁
  set ι₂ := kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T₂)) with hι₂
  have hsup := vanishingIdeal_sup_eq_top_of_disjoint hd
  have he : Epi (ι₂ ≫ cokernel.π ι₁) := by
    refine Preadditive.epi_of_cancel_zero _ fun {W} h hh => ?_
    have h0 := eq_zero_of_sup_eq_top Z _ _ hsup (cokernel.π ι₁ ≫ h)
      (by rw [← Category.assoc, cokernel.condition, zero_comp])
      (by rwa [← Category.assoc])
    exact (cancel_epi (cokernel.π ι₁)).mp (by rw [h0, comp_zero])
  have hk : kernel.ι (ι₂ ≫ cokernel.π ι₁) ≫ ι₂ ≫ φ = 0 := by
    set k := kernel.ι (ι₂ ≫ cokernel.π ι₁)
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift'
      (Abelian.monoIsKernelOfCokernel _ (colimit.isColimit (parallelPair ι₁ 0))) (k ≫ ι₂)
      (by rw [Category.assoc]; exact kernel.condition _)
    have hl' : l ≫ ι₁ = k ≫ ι₂ := hl
    have h1 : (k ≫ ι₂) ≫ idealToClosedSubscheme Z (vanishingIdeal (T₁ ⊔ T₂)) = 0 := by
      have h := comp_idealToClosedSubscheme_inf_eq_zero Z (vanishingIdeal T₁) (vanishingIdeal T₂)
        (k ≫ ι₂)
        (by rw [← hl', Category.assoc, kernel.condition, comp_zero])
        (by rw [Category.assoc, kernel.condition, comp_zero])
      rwa [← vanishingIdeal_sup] at h
    rw [← Category.assoc, ← kernel.lift_ι _ _ h1, Category.assoc, hφ, comp_zero]
  refine ⟨cokernel.π ι₁ ≫ Abelian.epiDesc (ι₂ ≫ cokernel.π ι₁) (ι₂ ≫ φ) hk, ?_, ?_⟩
  · rw [cokernel.condition_assoc, zero_comp]
  · rw [← Category.assoc, Abelian.comp_epiDesc]

/-- **A map killing `ℐ_Z ∩ ℐ_{T₁ ∪ T₂}`, for disjoint `T₁` and `T₂`, is a sum of one killing
`ℐ_Z ∩ ℐ_{T₁}` and one killing `ℐ_Z ∩ ℐ_{T₂}`.** -/
theorem exists_add_of_disjoint (Z : X.IdealSheafData) {T₁ T₂ : Closeds X}
    (hd : Disjoint (T₁ : Set X) T₂) {ω : X.Modules} (φ : kernel (ambientToClosedSubscheme Z) ⟶ ω)
    (hφ : kernel.ι (idealToClosedSubscheme Z (vanishingIdeal (T₁ ⊔ T₂))) ≫ φ = 0) :
    ∃ φ₁ φ₂ : kernel (ambientToClosedSubscheme Z) ⟶ ω,
      kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T₁)) ≫ φ₁ = 0 ∧
        kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T₂)) ≫ φ₂ = 0 ∧ φ₁ + φ₂ = φ := by
  obtain ⟨φ₁, h₁, h₁'⟩ := exists_kills_of_disjoint Z hd φ hφ
  obtain ⟨φ₂, h₂, h₂'⟩ := exists_kills_of_disjoint Z hd.symm φ (by rwa [sup_comm])
  refine ⟨φ₁, φ₂, h₁, h₂, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_sup_eq_top Z _ _ (vanishingIdeal_sup_eq_top_of_disjoint hd) _ ?_ ?_
  · simp only [Preadditive.comp_sub, Preadditive.comp_add, h₁, h₂', zero_add, sub_self]
  · simp only [Preadditive.comp_sub, Preadditive.comp_add, h₁', h₂, add_zero, sub_self]

/-- On a reduced scheme the composite `ℐ_Z ⟶ 𝒪_X ⟶ 𝒪_{Y_X}` for the reduced structure on all of
`X` is a monomorphism, so every map out of `ℐ_Z` kills its kernel. -/
theorem kernel_ι_idealToClosedSubscheme_vanishingIdeal_top [IsReduced X] (Z : X.IdealSheafData) :
    kernel.ι (idealToClosedSubscheme Z (vanishingIdeal ⊤)) = 0 := by
  have h : vanishingIdeal (⊤ : Closeds X) = ⊥ := by rw [vanishingIdeal_top, nilradical_eq_bot]
  have : IsIso (ambientToClosedSubscheme (vanishingIdeal (⊤ : Closeds X))) := by
    rw [h]
    exact isIso_ambientToPushforward _
  exact kernel.ι_of_mono _

/-- **Choosing the subcurve.** Let `X` be a Noetherian scheme of dimension at most one, `Z` a
closed subscheme and `φ : ℐ_Z ⟶ ω` nonzero killing `ℐ_Z ∩ ℐ_{T₀}` for a closed set `T₀`, where `ω`
admits no nonzero map with image supported in dimension zero from a coherent module. Then there is
a connected closed subset `T ⊆ T₀` of positive dimension and an injective nonzero map `ψ` into `ω`
from the image of `ℐ_Z` in `𝒪_T`, for the reduced structure on `T`.

The set `T` is chosen minimal among the closed subsets of `T₀` for which some nonzero map
`ℐ_Z ⟶ ω` kills `ℐ_Z ∩ ℐ_T`; it exists because `X` is Noetherian and `T₀` qualifies. Minimality
makes the induced map on the image injective (`exists_lt_of_not_mono`), forces `T` to be
connected (`exists_add_of_disjoint`) and of positive dimension
(`eq_zero_of_topologicalKrullDim_support_le_zero`). -/
theorem exists_isPreconnected_mono [IsLocallyNoetherian X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (Z : X.IdealSheafData) {ω : X.Modules}
    (hω : Scheme.Modules.NoZeroDimensionalImages ω) (T₀ : Closeds X)
    (φ : kernel (ambientToClosedSubscheme Z) ⟶ ω) (hφ : φ ≠ 0)
    (hφ₀ : kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T₀)) ≫ φ = 0) :
    ∃ T : Closeds X, T ≤ T₀ ∧ _root_.IsPreconnected (T : Set X) ∧
      ¬ topologicalKrullDim (T : Set X) ≤ 0 ∧
      ∃ ψ : Abelian.coimage (idealToClosedSubscheme Z (vanishingIdeal T)) ⟶ ω, Mono ψ ∧ ψ ≠ 0 := by
  let P : Set (Closeds X) := {T | T ≤ T₀ ∧ ∃ φ : kernel (ambientToClosedSubscheme Z) ⟶ ω,
    φ ≠ 0 ∧ kernel.ι (idealToClosedSubscheme Z (vanishingIdeal T)) ≫ φ = 0}
  obtain ⟨T, ⟨hTT₀, φ', hφ'0, hφ'⟩, hmin⟩ :=
    (wellFounded_lt (α := Closeds X)).has_min P ⟨T₀, le_rfl, φ, hφ, hφ₀⟩
  refine ⟨T, hTT₀, ?_, fun h => hφ'0 ?_, cokernel.desc _ φ' hφ', ?_, fun h => hφ'0 ?_⟩
  · rw [isPreconnected_closed_iff]
    intro t t' ht ht' hcov hne hne'
    by_contra! hempty
    let T₁ : Closeds X := ⟨T ∩ t, T.isClosed.inter ht⟩
    let T₂ : Closeds X := ⟨T ∩ t', T.isClosed.inter ht'⟩
    have hsup : T₁ ⊔ T₂ = T := by
      ext x
      simp only [Closeds.coe_sup, Set.mem_union]
      exact ⟨fun h => h.elim And.left And.left, fun hx => (hcov hx).elim
        (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)⟩
    have hd : Disjoint (T₁ : Set X) T₂ := Set.disjoint_left.2 fun x h₁ h₂ =>
      hempty.subset (⟨h₁.1, h₁.2, h₂.2⟩ : x ∈ (T : Set X) ∩ (t ∩ t'))
    obtain ⟨φ₁, φ₂, h₁, h₂, hsum⟩ := exists_add_of_disjoint Z hd φ' (by rwa [hsup])
    have hlt₁ : T₁ < T := by
      refine lt_of_le_of_ne (fun x hx => hx.1) fun h => ?_
      obtain ⟨x, hxT, hxt'⟩ := hne'
      have hx₁ : x ∈ (T₁ : Set X) := h ▸ hxT
      exact hempty.subset (⟨hxT, hx₁.2, hxt'⟩ : x ∈ (T : Set X) ∩ (t ∩ t'))
    have hlt₂ : T₂ < T := by
      refine lt_of_le_of_ne (fun x hx => hx.1) fun h => ?_
      obtain ⟨x, hxT, hxt⟩ := hne
      have hx₂ : x ∈ (T₂ : Set X) := h ▸ hxT
      exact hempty.subset (⟨hxT, hxt, hx₂.2⟩ : x ∈ (T : Set X) ∩ (t ∩ t'))
    by_cases hφ₁ : φ₁ = 0
    · refine hmin T₂ ⟨hlt₂.le.trans hTT₀, φ₂, fun h0 => hφ'0 ?_, h₂⟩ hlt₂
      rw [← hsum, hφ₁, h0, add_zero]
    · exact hmin T₁ ⟨hlt₁.le.trans hTT₀, φ₁, hφ₁, h₁⟩ hlt₁
  · refine eq_zero_of_topologicalKrullDim_support_le_zero Z _ ?_ hω φ' hφ'
    rwa [coe_support_vanishingIdeal]
  · by_contra hmono
    obtain ⟨T', hlt, hk⟩ := exists_lt_of_not_mono hdim Z T hω φ' hφ' hmono
    exact hmin T' ⟨hlt.le.trans hTT₀, φ', hφ'0, hk⟩ hlt
  · rw [← cokernel.π_desc _ φ' hφ', h, comp_zero]

end Scheme.IdealSheafData

/-! ### The dualizing sheaf has no zero-dimensional images -/

/-- The image of a morphism from a coherent module to a quasi-coherent one is coherent. -/
theorem isCoherent_image_of_isCoherent [IsLocallyNoetherian X] {Q ω : X.Modules}
    [ω.IsQuasicoherent] (hQ : Q.IsCoherent) (g : Q ⟶ ω) : (Abelian.image g).IsCoherent := by
  have : Q.IsQuasicoherent := isQuasicoherent_of_isCoherent Q
  have : (kernel g).IsQuasicoherent := Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel g
  have hK : (kernel g).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent hQ
      (kernel.ι g)
  have hC : (Abelian.coimage g).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel_modules hK hQ _
  let P : ObjectProperty X.Modules := fun M => M.IsCoherent
  let : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
  exact P.prop_of_iso (Abelian.coimageIsoImage g) hC

/-- **A quasi-coherent module admitting no nonzero map from a coherent module supported in
dimension zero has no nonzero map with zero-dimensional image from a coherent module.** Such a map
factors through its image, which is coherent. -/
theorem Scheme.Modules.noZeroDimensionalImages_of [IsLocallyNoetherian X] {ω : X.Modules}
    [ω.IsQuasicoherent]
    (h : ∀ Q : X.Modules, Q.IsCoherent →
      topologicalKrullDim (_root_.SheafOfModules.supp Q) ≤ 0 → ∀ g : Q ⟶ ω, g = 0) :
    Scheme.Modules.NoZeroDimensionalImages ω := fun Q hQ g hg => by
  rw [← Abelian.image.fac g, h _ (isCoherent_image_of_isCoherent hQ g) hg (Abelian.image.ι g),
    comp_zero]

/-- **The dualizing sheaf of a proper scheme of dimension at most one over a field has no nonzero
map from a coherent module supported in dimension zero**: such a module has no first cohomology
([Stacks, Tag 0AYT]), and clause (5) of [Stacks, Tag 0BS2] identifies maps into `ω_X` with
linear forms on the first cohomology. -/
theorem _root_.Stacks.Duality.noZeroDimensionalImages_dualizingSheafOverField {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) :
    Scheme.Modules.NoZeroDimensionalImages (Stacks.Duality.dualizingSheafOverField f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := Stacks.Duality.isQuasicoherent_dualizingSheafOverField f
  refine Scheme.Modules.noZeroDimensionalImages_of fun Q hQ hd g => ?_
  have := hQ
  have hz := isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k f Q hd 1 Nat.one_pos
  refine (Stacks.Duality.homDualizingSheafAddEquiv f hdim Q
    (isQuasicoherent_of_isCoherent Q)).injective ?_
  rw [map_zero]
  exact hz.eq_of_src _ _

/-- The support of a tensor product is contained in the support of the second factor: the stalk of
`ℒ ⊗ ℳ` is `ℒ_x ⊗ ℳ_x` ([Stacks, Tag 01CB]). -/
theorem notMem_supp_tensorSheaf_of_notMem (L M : X.Modules) {x : X}
    (hx : x ∉ _root_.SheafOfModules.supp M) :
    x ∉ _root_.SheafOfModules.supp
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj M)) := by
  rintro ⟨a, ha⟩
  have h1 := subsingleton_stalk_of_notMem_supp M hx
  let e := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x L M
  have hz : e a = 0 := by
    generalize e a = t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [@Subsingleton.elim _ h1 n 0]; exact TensorProduct.tmul_zero _ _
    | add t₁ t₂ h₁ h₂ => rw [h₁, h₂, add_zero]
  apply ha
  rw [← e.symm_apply_apply a, hz, map_zero]
  rfl

/-- **Twisting preserves the absence of zero-dimensional images.** If `ω` has no nonzero map with
zero-dimensional image from a coherent module, neither has `ℒ^{-1} ⊗ ω` for an invertible `ℒ`,
the value at `ω` of a quasi-inverse of `ℒ ⊗ -`: a map `g : 𝒬 ⟶ ℒ^{-1} ⊗ ω` corresponds to
`ℒ ⊗ 𝒬 ⟶ ω`, whose image is supported in that of `g`. -/
theorem Scheme.Modules.noZeroDimensionalImages_inverse_tensorLeft [IsLocallyNoetherian X]
    (L : X.Modules) [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {ω : X.Modules} (hω : Scheme.Modules.NoZeroDimensionalImages ω) :
    haveI : (Scheme.Modules.tensorLeft L).IsEquivalence :=
      (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ L).mp hL
    Scheme.Modules.NoZeroDimensionalImages
      ((Scheme.Modules.tensorLeft L).asEquivalence.inverse.obj ω) := by
  have : (Scheme.Modules.tensorLeft L).IsEquivalence :=
    (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ L).mp hL
  intro Q hQ g hg
  let E := (Scheme.Modules.tensorLeft L).asEquivalence
  have hLc : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  have hEQ : (E.functor.obj Q).IsCoherent :=
    @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace L Q hLc hQ
  have hfac : E.functor.map g ≫ E.counit.app ω =
      E.functor.map (Abelian.factorThruImage g) ≫
        (E.functor.map (Abelian.image.ι g) ≫ E.counit.app ω) := by
    rw [← Category.assoc, ← E.functor.map_comp, Abelian.image.fac]
  have hsub : _root_.SheafOfModules.supp (Abelian.image (E.functor.map g ≫ E.counit.app ω)) ⊆
      _root_.SheafOfModules.supp (Abelian.image g) := by
    intro x hx
    by_contra hx'
    refine (length_stalk_eq_zero_iff _ x).mp (le_antisymm ?_ bot_le) hx
    refine (le_of_eq (length_stalk_image_congr hfac x)).trans ?_
    refine (length_stalk_image_comp_le _ _ x).trans ((length_stalk_image_le_source _ x).trans ?_)
    exact ((length_stalk_eq_zero_iff _ x).mpr
      (notMem_supp_tensorSheaf_of_notMem L (Abelian.image g) hx')).le
  have h0 := hω _ hEQ (E.functor.map g ≫ E.counit.app ω)
    (((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans hg)
  exact E.functor.map_injective (by
    rw [Functor.map_zero]
    exact (cancel_mono (E.counit.app ω)).mp (by rw [h0, zero_comp]))

open Opposite in
/-- **A map out of `𝒪_X` into a module annihilated by `ℐ_Y` kills `ℐ_Y`**: it is multiplication of
a section by the image of `1`. -/
theorem Scheme.IdealSheafData.kernel_ι_comp_eq_zero_of_essImage (Y : X.IdealSheafData)
    {M : X.Modules} (hM : (Scheme.Modules.pushforward Y.subschemeι).essImage M)
    (g : Scheme.IdealSheafData.ambientStructureSheaf X ⟶ M) :
    kernel.ι (Scheme.IdealSheafData.ambientToClosedSubscheme Y) ≫ g = 0 := by
  rw [Stacks.ClosedImmersion.pushforward_essImage_iff] at hM
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  set a : Γ(X, U) := (kernel.ι (Scheme.IdealSheafData.ambientToClosedSubscheme Y)).app U s
  have ha : (Y.subschemeι.app U).hom a = 0 :=
    (Scheme.IdealSheafData.ambientToClosedSubscheme_app_apply Y U a).symm.trans
      ((Scheme.IdealSheafData.comp_app_apply _ _ U s).symm.trans
        (Scheme.IdealSheafData.app_apply_of_eq_zero (kernel.condition _) U s))
  have h1 : a • (show Γ(Scheme.IdealSheafData.ambientStructureSheaf X, U) from (1 : Γ(X, U))) =
      a := mul_one a
  show g.app U a = (0 : _ ⟶ M).app U s
  rw [Scheme.Modules.Hom.zero_app, ← h1, Scheme.Modules.Hom.app_smul, hM U a ha]
  rfl

end AlgebraicGeometry

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Characterizations of closed immersions of schemes

A morphism of schemes is a closed immersion precisely when, on affine opens of its target,
it is the spectrum of a quotient. Equivalently, its underlying map is a closed embedding and
the map on structure sheaves is surjective, with a quasi-coherent or locally generated kernel.

## Main definitions

* `Stacks.AlgebraicGeometry.ClosedImmersionTFAE.IsQuotientOverAffineOpen` records an
  isomorphism, over the canonical affine presentation of an open, with the spectrum of a
  quotient.

## Main results

* `Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae` gives all six
  characterizations of a closed immersion.
* `Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf` states that the
  ideal sheaf of a closed immersion of schemes is quasi-coherent.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.ClosedImmersionTFAE

/-- An affine-open restriction is the spectrum of a quotient of that open's ring of
sections, compatibly with its canonical presentation as a spectrum. -/
def IsQuotientOverAffineOpen {Z X : Scheme.{u}} (i : Z ⟶ X)
    (U : X.Opens) (hU : IsAffineOpen U) : Prop :=
  ∃ (I : Ideal Γ(X, U))
    (e : pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ I))),
    pullback.snd i U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-! ### The affine-local description -/

/-- Over an affine open of the target, a closed immersion is the spectrum of a quotient. -/
theorem isQuotientOverAffineOpen_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.Opens) (hU : IsAffineOpen U) :
    IsQuotientOverAffineOpen i U hU :=
  IsClosedImmersion.Spec_iff.mp (inferInstance :
    IsClosedImmersion (pullback.snd i U.ι ≫ hU.isoSpec.hom))

/-- A morphism which over an affine open of the target is the spectrum of a quotient restricts
to a closed immersion over that open. -/
theorem isClosedImmersion_morphismRestrict_of_isQuotientOverAffineOpen {Z X : Scheme.{u}}
    (i : Z ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (hq : IsQuotientOverAffineOpen i U hU) :
    IsClosedImmersion (i ∣_ U) := by
  obtain ⟨I, e, he⟩ := hq
  have hpq : IsClosedImmersion (pullback.snd i U.ι ≫ hU.isoSpec.hom) := by
    rw [he]
    infer_instance
  have hp : IsClosedImmersion (pullback.snd i U.ι) :=
    (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)
      (pullback.snd i U.ι) hU.isoSpec.hom).mp hpq
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (pullbackRestrictIsoRestrict i U).hom (i ∣_ U)).mp
  simpa only [pullbackRestrictIsoRestrict_hom_morphismRestrict] using hp

/-- A morphism which is the spectrum of a quotient over each member of an affine open cover of
its target is a closed immersion. -/
theorem isClosedImmersion_of_isQuotientOverAffineOpen_affineOpenCover {Z X : Scheme.{u}}
    (i : Z ⟶ X) (𝒰 : Scheme.AffineOpenCover.{u} X)
    (h : ∀ j : 𝒰.I₀,
      IsQuotientOverAffineOpen i (𝒰.f j).opensRange (isAffineOpen_opensRange (𝒰.f j))) :
    IsClosedImmersion i := by
  rw [IsClosedImmersion.isZariskiLocalAtTarget.iff_of_openCover 𝒰.openCover]
  intro j
  have : IsOpenImmersion (𝒰.f j) := 𝒰.map_prop j
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (morphismRestrictOpensRange i (𝒰.f j))).mp
      (isClosedImmersion_morphismRestrict_of_isQuotientOverAffineOpen i (𝒰.f j).opensRange
        (isAffineOpen_opensRange (𝒰.f j)) (h j))

/-! ### Surjectivity of the structure-sheaf map -/

/-- The structure-sheaf component of a closed immersion of schemes is locally surjective. -/
theorem isLocallySurjective_c_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : TopCat.Presheaf.IsLocallySurjective i.toLRSHom.c := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨V, hVU, i.app_surjective V hV (t |_ V), hxV⟩

/-- The map on structure sheaves of a closed immersion of schemes is an epimorphism of sheaves of
modules. -/
theorem epi_unitToPushforwardObjUnit_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom)) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    ⟨fun {_} s ↦ (isLocallySurjective_c_of_isClosedImmersion i).imageSieve_mem s⟩

/-- If the map on structure sheaves is an epimorphism of sheaves of modules, then the underlying
map of sheaves of rings is locally surjective. -/
theorem isLocallySurjective_c_of_epi_unitToPushforwardObjUnit {Z X : Scheme.{u}} (i : Z ⟶ X)
    [Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom))] :
    TopCat.Presheaf.IsLocallySurjective i.toLRSHom.c :=
  ⟨fun {_} s ↦ (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi
    (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.toLRSHom.toShHom))).imageSieve_mem s⟩

/-- A morphism of schemes whose underlying map is a closed embedding and whose map on structure
sheaves is surjective is surjective on stalks. -/
theorem surjectiveOnStalks_of_epi_unitToPushforwardObjUnit {Z X : Scheme.{u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.base)
    [Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom))] :
    SurjectiveOnStalks i := by
  refine ⟨fun z b ↦ ?_⟩
  have hc : Function.Surjective
      ((TopCat.Presheaf.stalkFunctor CommRingCat (i.base z)).map i.toLRSHom.c).hom :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks i.toLRSHom.c).mp
      (isLocallySurjective_c_of_epi_unitToPushforwardObjUnit i) (i.base z)
  have hiso : IsIso (Z.presheaf.stalkPushforward CommRingCat i.base z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      CommRingCat hi.isInducing Z.presheaf z
  obtain ⟨a, ha⟩ := hc ((asIso (Z.presheaf.stalkPushforward CommRingCat i.base z)).inv.hom b)
  refine ⟨a, ?_⟩
  change (Z.presheaf.stalkPushforward CommRingCat i.base z).hom
    (((TopCat.Presheaf.stalkFunctor CommRingCat (i.base z)).map i.toLRSHom.c).hom a) = b
  rw [ha]
  simp

/-- A morphism of schemes whose underlying map is a closed embedding and whose map on structure
sheaves is surjective is a closed immersion. -/
theorem isClosedImmersion_of_epi_unitToPushforwardObjUnit {Z X : Scheme.{u}} (i : Z ⟶ X)
    (h : Topology.IsClosedEmbedding i.base ∧
      Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom))) :
    IsClosedImmersion i :=
  have := h.2
  have := surjectiveOnStalks_of_epi_unitToPushforwardObjUnit i h.1
  ⟨h.1⟩

/-! ### Quasi-coherence of the ideal sheaf -/

/-- The ideal sheaf of a closed immersion of schemes is quasi-coherent. -/
theorem isQuasicoherent_idealSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsQuasicoherent :=
  have : ((SheafOfModules.pushforward i.toRingCatSheafHom).obj
      (SheafOfModules.unit Z.ringCatSheaf)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_restrictScalars_pushforwardRing
      i
  Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel
    (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)

/-! ### The equivalence -/

/-- The six equivalent descriptions of a closed immersion of schemes. -/
@[stacks 01QO, ega "I 4.2.2" "(b) closed case"]
theorem closedImmersion_tfae {Z X : Scheme.{u}} (i : Z ⟶ X) :
    List.TFAE [
      IsClosedImmersion i,
      ∀ (U : X.Opens) (hU : IsAffineOpen U), IsQuotientOverAffineOpen i U hU,
      ∃ (𝒰 : Scheme.AffineOpenCover.{u} X), ∀ j : 𝒰.I₀,
        IsQuotientOverAffineOpen i (𝒰.f j).opensRange
          (isAffineOpen_opensRange (𝒰.f j)),
      Topology.IsClosedEmbedding i.base ∧
        Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom)),
      (Topology.IsClosedEmbedding i.base ∧
        Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom))) ∧
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsQuasicoherent,
      Stacks.ClosedImmersion.IsClosedImmersion i.toLRSHom.toShHom] := by
  tfae_have 1 → 2 := fun hi U hU ↦
    have := hi
    isQuotientOverAffineOpen_of_isClosedImmersion i U hU
  tfae_have 2 → 3 := fun h ↦ ⟨X.affineOpenCover, fun j ↦ h _ _⟩
  tfae_have 3 → 1 := fun ⟨𝒰, h⟩ ↦
    isClosedImmersion_of_isQuotientOverAffineOpen_affineOpenCover i 𝒰 h
  tfae_have 1 → 5 := fun hi ↦
    have := hi
    ⟨⟨i.isClosedEmbedding, epi_unitToPushforwardObjUnit_of_isClosedImmersion i⟩,
      isQuasicoherent_idealSheaf i⟩
  tfae_have 5 → 4 := fun h ↦ h.1
  tfae_have 4 → 1 := fun h ↦ isClosedImmersion_of_epi_unitToPushforwardObjUnit i h
  tfae_have 5 → 6 := fun h ↦ by
    obtain ⟨q⟩ := h.2.nonempty_quasicoherentData
    exact (Stacks.ClosedImmersion.isClosedImmersion_iff _).mpr
      ⟨h.1.1, h.1.2, ⟨q.localGeneratorsData⟩⟩
  tfae_have 6 → 4 := fun h ↦ ⟨h.isClosedEmbedding, h.structureSheafMap_epi⟩
  tfae_finish

end Stacks.AlgebraicGeometry.ClosedImmersionTFAE

end

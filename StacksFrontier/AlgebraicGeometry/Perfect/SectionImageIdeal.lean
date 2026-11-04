module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Coherent.IdealSheafFiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Affine
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamilyIdealCovering
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal

/-!
# Pairing against a global section, as a morphism into the structure sheaf

Let `(X, 𝒪_X)` be a ringed space, let `L` and `N` be sheaves of `𝒪_X`-modules together with a
trivialization `ψ : L ⊗_{𝒪_X} N ≅ 𝒪_X`, and let `s` be a global section of `L`. Pairing against
`s` is then a morphism of sheaves of modules `N ⟶ 𝒪_X`, and this file builds it.

It is the morphism whose sections are `Stacks.SheafOfModules.tensorPairing`, the pairing of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationStalk.lean` through which the
nonvanishing locus of `s` is characterized. Having it as a morphism, rather than as a family of
maps on sections, is what lets the nonvanishing locus be compared with the vanishing locus of a
sheaf of ideals: the image of a morphism into the structure sheaf is a sheaf of ideals, while a
family of maps on sections is not the image of anything.

With that morphism in hand the file proves `AlgebraicGeometry.ExistsSectionImageIdeal`, the
sheaf of ideals attached to a global section of an invertible module that [Stacks, Tag 0GMM]
feeds to [Stacks, Tag 0F89]: a tensor inverse of the module exists by [Stacks, Tag 0B8K] and is
itself invertible, hence finite locally free of rank one by [Stacks, Tag 0B8M], and the image of
pairing against the section is the ideal asked for.

## Main definitions

* `Stacks.SheafOfModules.tmulLeftSection`: the morphism of presheaves of modules
  `N ⟶ L ⊗^{pre} N` sending a section `b` to `s|_W ⊗ b`.
* `Stacks.SheafOfModules.pairingSheafHom`: **pairing against `s`**, the morphism of sheaves of
  modules `N ⟶ 𝒪_X`. It is `tmulLeftSection` followed by the sheafification unit of the tensor
  product and then by the trivialization.

## Main results

* `Stacks.SheafOfModules.pairingSheafHom_val_app`: pairing against `s` is, on sections, exactly
  `Stacks.SheafOfModules.tensorPairing`. This holds by `rfl` and is the reason the construction
  is arranged as it is.
* `Stacks.SheafOfModules.mem_nonvanishingLocus_iff_exists_app_pairingSheafHom_eq_one`: the local
  criterion for membership in the nonvanishing locus, read through `pairingSheafHom`.
* `AlgebraicGeometry.coe_support_idealSheafDataOfHom_pairingSheafHom`: **the image of pairing
  against `s` is a sheaf of ideals whose support is the complement of `X_s`.**
* `AlgebraicGeometry.existsSectionImageIdeal`: **`AlgebraicGeometry.ExistsSectionImageIdeal`**,
  the sheaf of ideals with which [Stacks, Tag 0GMM] enters [Stacks, Tag 0F89].

## Implementation notes

The three steps of the composite live in three different presentations of the tensor product and
only the first of them is new. `tmulLeftSection` is built with
`PresheafOfModules.homMk` from the bilinear map `TensorProduct.mk`, whose naturality in the open
set is the compatibility of `s` with restriction
(`PresheafOfModules.sections_property`); the second step is the unit of the sheafification
adjunction, `Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit`, which is what
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` is built from; the third is
the trivialization. Because `tensorPairing` is literally the composite of the last two applied
to an elementary tensor, `pairingSheafHom_val_app` is `rfl`.

The intermediate type of the second step is the restriction of scalars along the identity
morphism of `𝒪_X` of the underlying presheaf of the sheafified tensor product. That is the same
presheaf of modules as the underlying presheaf itself, but not the same expression, so the
composite is assembled with the structure constructor rather than with `≫` alone.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : RingedSpace.{u, u}} {L N : _root_.SheafOfModules.{u} (structureSheafRing X)}

/-- Pairing the elementary tensor with `s` on the left: the bilinear map
`b ↦ s|_W ⊗ b` from the sections of `N` over `W` to those of the presheaf tensor product. -/
noncomputable def tmulLeftSectionₗ (s : L.sections) (U : (Opens X.carrier)ᵒᵖ) :
    N.val.obj U →ₗ[X.presheaf.obj U]
      TensorProduct (X.presheaf.obj U) (L.val.obj U) (N.val.obj U) :=
  TensorProduct.mk (X.presheaf.obj U) (L.val.obj U) (N.val.obj U) (s.eval U)

/-- `b ↦ s|_W ⊗ b` as a morphism of the underlying presheaves of abelian groups. Its naturality
is the compatibility of `s` with restriction. -/
noncomputable def tmulLeftSectionNat (s : L.sections) :
    N.val.presheaf ⟶
      (PresheafOfModules.tensorObj (O := X.presheaf) L.val N.val).presheaf where
  app U := AddCommGrpCat.ofHom (tmulLeftSectionₗ (N := N) s U).toAddMonoidHom
  naturality U V f := by
    ext b
    exact congrArg (fun a => a ⊗ₜ[X.presheaf.obj V] (N.val.restrictₛₗ f b))
      (PresheafOfModules.sections_property s f).symm

/-- **Tensoring with `s` on the left**: the morphism of presheaves of modules
`N ⟶ L ⊗^{pre} N` sending a section `b` over `W` to `s|_W ⊗ b`. -/
noncomputable def tmulLeftSection (s : L.sections) :
    N.val ⟶ PresheafOfModules.tensorObj (O := X.presheaf) L.val N.val :=
  PresheafOfModules.homMk (tmulLeftSectionNat (N := N) s)
    fun U r b => (tmulLeftSectionₗ (N := N) s U).map_smul r b

/-- **Pairing against `s`**: for a trivialization `ψ : L ⊗_{𝒪_X} N ≅ 𝒪_X` and a global section
`s` of `L`, the morphism of sheaves of modules `N ⟶ 𝒪_X` sending a section `b` over `W` to the
pairing of `s|_W` with `b`. -/
noncomputable def pairingSheafHom
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (structureSheafRing X))
    (s : L.sections) : N ⟶ _root_.SheafOfModules.unit (structureSheafRing X) where
  val := tmulLeftSection (N := N) s ≫
    sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) L.val N.val) ≫ ψ.hom.val

/-- **Pairing against `s` is `Stacks.SheafOfModules.tensorPairing` on sections.** -/
theorem pairingSheafHom_val_app
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (structureSheafRing X))
    (s : L.sections) (W : Opens X.carrier) (b : N.val.obj (op W)) :
    (pairingSheafHom ψ s).val.app (op W) b = tensorPairing ψ W (s.eval (op W)) b := rfl

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- **The nonvanishing locus, read through `pairingSheafHom`.** A point lies in the nonvanishing
locus of `s` exactly when some section of `N` near it pairs with `s` to the unit section. This is
`Stacks.SheafOfModules.mem_nonvanishingLocus_iff` with the pairing named as a morphism. -/
theorem mem_nonvanishingLocus_iff_exists_app_pairingSheafHom_eq_one
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (structureSheafRing X))
    (s : L.sections) (x : X.carrier) :
    x ∈ nonvanishingLocus L s ↔
      ∃ (W : Opens X.carrier) (_ : x ∈ W) (b : N.val.obj (op W)),
        (pairingSheafHom ψ s).val.app (op W) b = unitSection X W :=
  mem_nonvanishingLocus_iff ψ s x

end Stacks.SheafOfModules

namespace AlgebraicGeometry

open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.IdealPowerColimit

/-- **The sheaf of ideals cut out by a global section of an invertible module has for vanishing
locus the complement of the nonvanishing locus.** Let `M` be an `𝒪_X`-module with a
trivialization `ψ : M ⊗ N ≅ 𝒪_X` and let `s` be a global section of `M`. Then the image of
`N ⟶ 𝒪_X`, pairing against `s`, is a sheaf of ideals whose support is the complement of `X_s`.

Both inclusions are the local criterion
`Stacks.SheafOfModules.mem_nonvanishingLocus_iff`. If `s` pairs to `1` with a section of `N` over
a neighbourhood of `x`, then over an affine open inside that neighbourhood the ideal contains
`1`, so `x` is outside the support. Conversely, if `x` is outside the support then over some
affine open the ideal contains a section not vanishing at `x`; that section is a unit on its
basic open, and dividing by it produces a section of `N` pairing with `s` to `1` there. -/
theorem coe_support_idealSheafDataOfHom_pairingSheafHom {X : Scheme.{u}} {M N : X.Modules}
    [N.IsQuasicoherent]
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj M).obj N ≅
      _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (s : M.sections) :
    ((idealSheafDataOfHom N (pairingSheafHom ψ s)).support : Set X)
      = (X.nonvanishingSet M s)ᶜ := by
  have key : ∀ x : X, x ∈ X.nonvanishingSet M s ↔
      ∃ (W : X.Opens) (_ : x ∈ W) (b : Γ(N, W)),
        structureAppₗ (A := N) (pairingSheafHom ψ s) W b = (1 : Γ(X, W)) :=
    fun x => mem_nonvanishingLocus_iff ψ s x
  ext x
  simp only [SetLike.mem_coe, Set.mem_compl_iff]
  constructor
  · intro hx hxs
    obtain ⟨W, hxW, b, hb⟩ := (key x).mp hxs
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (W : Set X) from hxW) W.isOpen
    have h1 : (1 : Γ(X, V)) ∈ idealOfHom N (pairingSheafHom ψ s) V :=
      ⟨N.presheaf.map (homOfLE hVW).op b,
        (map_structureAppₗ (pairingSheafHom ψ s) hVW b).symm.trans
          (by rw [hb, map_one])⟩
    have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hVaff⟩) hxV).mp hx
    rw [Scheme.mem_zeroLocus_iff] at hz
    exact hz 1 h1 (by rwa [X.basicOpen_of_isUnit isUnit_one])
  · intro hxs
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    refine (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hVaff⟩) hxV).mpr ?_
    rw [Scheme.mem_zeroLocus_iff]
    rintro f ⟨b, rfl⟩ hxf
    set g := structureAppₗ (A := N) (pairingSheafHom ψ s) V b
    have hle : X.basicOpen g ≤ V := X.basicOpen_le g
    have hu : IsUnit ((X.presheaf.map (homOfLE hle).op).hom g) :=
      X.toRingedSpace.isUnit_res_basicOpen g
    refine hxs ((key x).mpr ⟨X.basicOpen g, hxf,
      (↑hu.unit⁻¹ : Γ(X, X.basicOpen g)) • N.presheaf.map (homOfLE hle).op b, ?_⟩)
    rw [map_smul, ← map_structureAppₗ (pairingSheafHom ψ s) hle b, smul_eq_mul]
    exact hu.val_inv_mul

/-- **The sheaf of ideals cut out by a global section of an invertible module.**  This is
`AlgebraicGeometry.ExistsSectionImageIdeal`, the input with which [Stacks, Tag 0GMM] enters
[Stacks, Tag 0F89]: for a global section `s` of an invertible `𝒪_X`-module `M` there is a
quasi-coherent sheaf of ideals which is of finite type, is the quotient of a finite locally free
module, and whose vanishing locus is the complement of the nonvanishing locus `X_s`.

The ideal is the image of pairing against `s`, a morphism `N ⟶ 𝒪_X` out of a tensor inverse `N`
of `M`; `N` exists by [Stacks, Tag 0B8K] and is itself invertible, hence finite locally free of
rank one by [Stacks, Tag 0B8M], hence quasi-coherent and of finite type.  The image of a
morphism into the structure sheaf is a sheaf of ideals
(`AlgebraicGeometry.idealSheafDataOfHom`), of finite type because `N` is
(`AlgebraicGeometry.isFiniteType_idealSheafDataOfHom`) and a quotient of `N`
(`AlgebraicGeometry.epi_toIdealPowOfHom`); its vanishing locus is the complement of `X_s` by
`AlgebraicGeometry.coe_support_idealSheafDataOfHom_pairingSheafHom`. -/
theorem exists_sectionImageIdeal_of_tensorIsoUnit {X : Scheme.{u}} (M N : X.Modules)
    (hqc : N.IsQuasicoherent) (hft : SheafOfModules.IsFiniteType.{u, u, u} N)
    (hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N)
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj M).obj N ≅
      _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (s : M.sections) :
    ∃ I : X.IdealSheafData,
      ((I.support : Set X) = (X.nonvanishingSet M s)ᶜ) ∧ (idealPow I 1).IsFiniteType ∧
        ∃ (E : X.Modules)
          (_ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
          (q : E ⟶ idealPow I 1), Epi q := by
  have := hqc
  have := hft
  exact ⟨idealSheafDataOfHom N (pairingSheafHom ψ s),
    coe_support_idealSheafDataOfHom_pairingSheafHom ψ s,
    Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_idealPow _ 1
      (isFiniteType_idealSheafDataOfHom N (pairingSheafHom ψ s)),
    N, hflf, toIdealPowOfHom N (pairingSheafHom ψ s),
    epi_toIdealPowOfHom N (pairingSheafHom ψ s)⟩

/-- For a global section `s` of an invertible `𝒪_X`-module `M` there is a sheaf of ideals of
finite type, the quotient of a finite locally free module, whose vanishing locus is the
complement of the nonvanishing locus `X_s`. -/
theorem existsSectionImageIdeal : ExistsSectionImageIdeal.{u} := by
  intro X M hM s
  have inv_iff := Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
  obtain ⟨N, ⟨ψ⟩⟩ := (inv_iff M).mp hM
  have hN : Stacks.Ample.IsInvertibleModule X N :=
    (inv_iff N).mpr ⟨M, ⟨Stacks.SheafOfModules.tensorSheafBraiding _ _ N M ≪≫ ψ⟩⟩
  have hrk : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf) N 1 :=
    Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X N
  exact exists_sectionImageIdeal_of_tensorIsoUnit M N
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule N)
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule N)
    (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (R := X.ringCatSheaf) N 1) ψ s

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Restriction
public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.ClosedSubspaceScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ideal sheaf of a closed immersion over an affine open

Let `X` be a scheme, let `i : Z ⟶ X` be a closed immersion of locally ringed spaces and let
`U = Spec R` be an affine open of `X`, with `R = Γ(X, U)`. Over `U` the immersion is the spectrum
of a quotient `R ⧸ I`, and the ideal sheaf `ℐ` of `i` restricts on `U` to the quasi-coherent sheaf
`I^~` attached to that same ideal `I`, compatibly with the two inclusions into `𝒪_U`.

## Main definitions

* `Stacks.ClosedImmersion.tildeIdealι` is the inclusion `I^~ ⟶ 𝒪_{Spec R}` of the quasi-coherent
  sheaf attached to an ideal `I ⊆ R` into the structure sheaf.

## Main results

* `Stacks.ClosedImmersion.exists_ideal_idealSheaf_restrict_iso_tilde`: for a closed immersion of
  schemes there is an ideal `I` of `Γ(X, U)` which both presents the fibre over `U` as
  `Spec (Γ(X, U) ⧸ I)` and satisfies `ℐ|_U = I^~`.
* `Stacks.ClosedImmersion.exists_ideal_idealSheaf_restrict_iso_tilde_of_locallyRingedSpace`: the
  same for a closed immersion of locally ringed spaces into a scheme, whose source is a scheme by
  `Stacks.ClosedImmersion.sourceScheme`.

## Implementation notes

The identification `ℐ|_U = I^~` is read as an isomorphism of `𝒪_U`-modules compatible with the
inclusions of the two sides into `𝒪_U`; since those inclusions are monomorphisms this says
exactly that the two are the same submodule of `𝒪_U`, which is what the equality of sheaves in
the source asserts. The sheaf `I^~` lives on `Spec Γ(X, U)` and is transported to `U` along the
canonical presentation `AlgebraicGeometry.IsAffineOpen.isoSpec`, which is the identification
`U = Spec R` that the source makes silently.

No derived functor enters. The isomorphism is the composite of three identifications, each of
which already comes with the compatibility that pins it down:

* restriction to an open of the target commutes with the ideal sheaf, the source being cut down
  to the preimage (`Stacks.Conormal.Restriction.restrictIdealSheafIso'`);
* the ideal sheaf is unchanged by an isomorphism of the source and, pulled back, by an
  isomorphism of the target (`Stacks.IdealSheafRestrict.pullbackIdealSheafIso` and
  `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource`), which together
  move the affine presentation of the fibre across;
* the ideal sheaf of `Spec (R ⧸ I) ⟶ Spec R` is `I^~`
  (`Stacks.ClosedImmersion.IdealSheafAffine.exists_tilde_iso_kernel_quotUnitHom`).

The affine presentation of the fibre is
`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuotientOverAffineOpen_of_isClosedImmersion`, so
the ideal produced here is the ideal of the affine-local description and not some other ideal
with the same associated sheaf; it is returned together with that presentation for exactly that
reason.

The inclusion of `I^~` into the structure sheaf is given its own name `tildeIdealι` with the
structure sheaf spelled as `SheafOfModules.unit (structureSheafRing (Spec R).toSheafedSpace)`. That
spelling is definitionally but not syntactically `SheafOfModules.unit (Spec R).ringCatSheaf`,
which is the one `AlgebraicGeometry.tildeSelf` produces, and a composite mentioning both is not
type-correct at the elaborator's implicit transparency; naming the composite forces the
conversion once, where it is checked at default transparency, so that no rewrite downstream has
to see through it.

## References

* [Stacks Project, Tag 01HQ](https://stacks.math.columbia.edu/tag/01HQ)
* [Stacks Project, Tag 01IH](https://stacks.math.columbia.edu/tag/01IH)
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-! ### The inclusion of `I^~` into the structure sheaf -/

/-- The inclusion of the quasi-coherent sheaf `I^~` attached to an ideal `I` of `R` into the
structure sheaf of `Spec R`: the sheaf attached to the inclusion `I ⟶ R` of modules, followed by
the identification of `R^~` with `𝒪_{Spec R}`. -/
abbrev tildeIdealι (R : CommRingCat.{u}) (I : Ideal R) :
    tilde (ModuleCat.of ↑R I) ⟶ SheafOfModules.unit (structureSheafRing (Spec R).toSheafedSpace) :=
  tilde.map (ModuleCat.ofHom (Submodule.subtype I)) ≫ tildeSelf.hom

/-- **The ideal sheaf of `Spec (R ⧸ I) ⟶ Spec R` is `I^~`**, compatibly with the two inclusions
into `𝒪_{Spec R}`. This is
`Stacks.ClosedImmersion.IdealSheafAffine.exists_tilde_iso_kernel_quotUnitHom` in the vocabulary
used here. -/
@[ega "II 1.4.10" "affine case"]
private theorem exists_tilde_iso_idealSheaf_quotientSpec (R : CommRingCat.{u}) (I : Ideal R) :
    ∃ e : tilde (ModuleCat.of ↑R I) ≅
        idealSheaf (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom,
      e.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)) =
        tildeIdealι R I :=
  IdealSheafAffine.exists_tilde_iso_kernel_quotUnitHom I

/-! ### Moving the affine presentation of the fibre across -/

section AffineModel

variable {A A' B : Scheme.{u}} (α : A' ≅ A) (g : A ⟶ B) (h : A' ⟶ B)
  (hh : h.toLRSHom.toShHom = (α.hom ≫ g).toLRSHom.toShHom)

/-- **The ideal sheaf is unchanged by an isomorphism of the source**, with the composite
presented as a separately named morphism `h` together with an equality of the underlying
morphisms of ringed spaces. That is the shape an affine presentation of a fibre supplies. -/
private def idealSheafIsoOfIsoSourceOfShHomEq :
    idealSheaf h.toLRSHom.toShHom ≅ idealSheaf g.toLRSHom.toShHom :=
  idealSheafCongr hh ≪≫
    Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource α g

/-- `idealSheafIsoOfIsoSourceOfShHomEq` commutes with the two inclusions into the structure
sheaf. Those inclusions are monomorphisms, so this determines the isomorphism. -/
private theorem idealSheafIsoOfIsoSourceOfShHomEq_hom_comp_ι :
    (idealSheafIsoOfIsoSourceOfShHomEq α g h hh).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom g.toLRSHom.toShHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom h.toLRSHom.toShHom)) :=
  by
  rw [idealSheafIsoOfIsoSourceOfShHomEq, Iso.trans_hom, Category.assoc,
    Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource_hom_comp_ι,
    idealSheafCongr_hom_kernel_ι hh]

end AffineModel

/-! ### A composition identity -/

/-- A purely categorical bookkeeping step: a morphism factored as `r ≫ p ≫ m`, composed with
`t ≫ u`, is `ρ` as soon as `m ≫ t = m'`, `p ≫ m' ≫ u = ι` and `r ≫ ι = ρ`. Stated for an
arbitrary category so that the associativity shuffling is done once, away from the sheaves of
modules it is applied to. -/
private theorem comp_eq_of_factors {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ : C}
    {x : A₀ ⟶ A₃} (r : A₀ ⟶ A₁) (p : A₁ ⟶ A₂) (m : A₂ ⟶ A₃) (t : A₃ ⟶ A₄) (u : A₄ ⟶ A₅)
    {m' : A₂ ⟶ A₄} {ι : A₁ ⟶ A₅} {ρ : A₀ ⟶ A₅} (hx : x = r ≫ p ≫ m) (h₁ : m ≫ t = m')
    (h₂ : p ≫ m' ≫ u = ι) (h₃ : r ≫ ι = ρ) :
    x ≫ t ≫ u = ρ := by
  rw [hx, Category.assoc, Category.assoc, ← Category.assoc m t u, h₁, h₂, h₃]

/-! ### The identification over an affine open -/

section Restrict

variable {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
  (ε : (f ⁻¹ᵁ U).toScheme ≅ Spec (CommRingCat.of (Γ(X, U) ⧸ I)))
  (hε : ((f ∣_ U) ≫ hU.isoSpec.hom).toLRSHom.toShHom =
    (ε.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)
  (eT : tilde (ModuleCat.of Γ(X, U) I) ≅
    idealSheaf (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)

/-- **The restriction of the ideal sheaf to an affine open is `I^~`.** The composite of the three
identifications described in the module docstring. -/
private def idealSheafRestrictTildeIso :
    (Scheme.Modules.restrictFunctor U.ι).obj (idealSheaf f.toLRSHom.toShHom) ≅
      (modulePullback hU.isoSpec.hom.toLRSHom.toShHom).obj (tilde (ModuleCat.of Γ(X, U) I)) :=
  Stacks.Conormal.Restriction.restrictIdealSheafIso' f U ≪≫
    (Stacks.IdealSheafRestrict.pullbackIdealSheafIso hU.isoSpec.hom (f ∣_ U)).symm ≪≫
      (modulePullback hU.isoSpec.hom.toLRSHom.toShHom).mapIso
        (idealSheafIsoOfIsoSourceOfShHomEq ε
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
          ((f ∣_ U) ≫ hU.isoSpec.hom) hε ≪≫ eT.symm)

/-- The ideal sheaf of `f ∣_ U`, transported across the affine presentation and then by `eT`, has
the inclusion of `I^~` as its image in the structure sheaf. -/
private theorem affineModelTildeIso_hom_comp_tildeIdealι
    (heT : eT.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)) =
      tildeIdealι Γ(X, U) I) :
    (idealSheafIsoOfIsoSourceOfShHomEq ε (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
          ((f ∣_ U) ≫ hU.isoSpec.hom) hε ≪≫ eT.symm).hom ≫ tildeIdealι Γ(X, U) I =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom ((f ∣_ U) ≫ hU.isoSpec.hom).toLRSHom.toShHom)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (idealSheafIsoOfIsoSourceOfShHomEq ε
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
            ((f ∣_ U) ≫ hU.isoSpec.hom) hε).hom ≫ z)
        ((Iso.inv_comp_eq eT).2 heT.symm)).trans
      (idealSheafIsoOfIsoSourceOfShHomEq_hom_comp_ι ε
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        ((f ∣_ U) ≫ hU.isoSpec.hom) hε))

/-- **`idealSheafRestrictTildeIso` commutes with the two inclusions into `𝒪_U`.** Those
inclusions are monomorphisms, so this determines the isomorphism, and it is what the equality of
sheaves of the source asserts. -/
private theorem idealSheafRestrictTildeIso_hom_comp_ι
    (heT : eT.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)) =
      tildeIdealι Γ(X, U) I) :
    (idealSheafRestrictTildeIso f U hU I ε hε eT).hom ≫
        (modulePullback hU.isoSpec.hom.toLRSHom.toShHom).map (tildeIdealι Γ(X, U) I) ≫
          (Stacks.IdealSheafRestrict.pullbackUnitIso hU.isoSpec.hom).hom =
      (Scheme.Modules.restrictFunctor U.ι).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom f.toLRSHom.toShHom))) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom :=
  comp_eq_of_factors (Stacks.Conormal.Restriction.restrictIdealSheafIso' f U).hom
    (Stacks.IdealSheafRestrict.pullbackIdealSheafIso hU.isoSpec.hom (f ∣_ U)).inv
    ((modulePullback hU.isoSpec.hom.toLRSHom.toShHom).map
      (idealSheafIsoOfIsoSourceOfShHomEq ε
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        ((f ∣_ U) ≫ hU.isoSpec.hom) hε ≪≫ eT.symm).hom)
    ((modulePullback hU.isoSpec.hom.toLRSHom.toShHom).map (tildeIdealι Γ(X, U) I))
    (Stacks.IdealSheafRestrict.pullbackUnitIso hU.isoSpec.hom).hom rfl
    (((modulePullback hU.isoSpec.hom.toLRSHom.toShHom).map_comp _ _).symm.trans
      (congrArg (modulePullback hU.isoSpec.hom.toLRSHom.toShHom).map
        (affineModelTildeIso_hom_comp_tildeIdealι f U hU I ε hε eT heT)))
    ((Iso.inv_comp_eq _).2
      (Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι hU.isoSpec.hom (f ∣_ U)).symm)
    (Stacks.Conormal.Restriction.restrictIdealSheafIso_hom_comp_ι f U)

end Restrict

/-! ### The affine-local description of the ideal sheaf -/

/-- **Stacks Project, Tag 01IN.** Let `f : Y ⟶ X` be a closed immersion of schemes and let
`U = Spec R` be an affine open of `X`, with `R = Γ(X, U)`. There is an ideal `I ⊆ R` which
presents the fibre `Y ×_X U` as `Spec (R ⧸ I)` over `Spec R` and for which the restriction of the
ideal sheaf of `f` to `U` is `I^~`, compatibly with the two inclusions into `𝒪_U`. -/
theorem exists_ideal_idealSheaf_restrict_iso_tilde {Y X : Scheme.{u}} (f : Y ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion f] (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback f U.ι ≅ Spec (CommRingCat.of (Γ(X, U) ⧸ I))),
      pullback.snd f U.ι ≫ hU.isoSpec.hom =
          e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
        ∃ φ : (Scheme.Modules.restrictFunctor U.ι).obj (idealSheaf f.toLRSHom.toShHom) ≅
            (modulePullback hU.isoSpec.hom.toLRSHom.toShHom).obj
              (tilde (ModuleCat.of Γ(X, U) I)),
          φ.hom ≫ (modulePullback hU.isoSpec.hom.toLRSHom.toShHom).map
                (tildeIdealι Γ(X, U) I) ≫
              (Stacks.IdealSheafRestrict.pullbackUnitIso hU.isoSpec.hom).hom =
            (Scheme.Modules.restrictFunctor U.ι).map
                (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
                  (structureSheafHom f.toLRSHom.toShHom))) ≫
              (Scheme.Modules.restrictUnitIso U.ι).hom := by
  obtain ⟨I, e, he⟩ :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuotientOverAffineOpen_of_isClosedImmersion
      f U hU
  obtain ⟨eT, heT⟩ := exists_tilde_iso_idealSheaf_quotientSpec Γ(X, U) I
  have hε : (f ∣_ U) ≫ hU.isoSpec.hom =
      ((pullbackRestrictIsoRestrict f U).symm ≪≫ e).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [← cancel_epi (pullbackRestrictIsoRestrict f U).hom, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc,
      pullbackRestrictIsoRestrict_hom_morphismRestrict_assoc]
    exact he
  have hsh := congrArg (fun z : (f ⁻¹ᵁ U).toScheme ⟶ Spec Γ(X, U) => z.toLRSHom.toShHom) hε
  exact ⟨I, e, he, idealSheafRestrictTildeIso f U hU I _ hsh eT,
    idealSheafRestrictTildeIso_hom_comp_ι f U hU I _ hsh eT heT⟩

/-- The affine-local description of the ideal sheaf for a closed immersion of locally ringed
spaces `i : Z ⟶ X` into a scheme: over an affine open `U = Spec R` of `X` there is an ideal
`I ⊆ R = Γ(X, U)` presenting the fibre over `U` as `Spec (R ⧸ I)`, and the kernel `ℐ` of
`𝒪_X ⟶ i_* 𝒪_Z` restricts on `U` to `I^~`.

The source `Z` is a scheme by `Stacks.ClosedImmersion.sourceScheme`, so `i` is a morphism of
schemes `Stacks.ClosedImmersion.sourceSchemeHom` with the same ideal sheaf, and this is
`Stacks.ClosedImmersion.exists_ideal_idealSheaf_restrict_iso_tilde` for that morphism. -/
@[stacks 01IN "kernel_on_affine_open"]
theorem exists_ideal_idealSheaf_restrict_iso_tilde_of_locallyRingedSpace (X : Scheme.{u})
    (Z : LocallyRingedSpace.{u}) (i : Z ⟶ X.toLocallyRingedSpace)
    [hi : IsClosedImmersion i.toShHom] (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback (sourceSchemeHom X Z i) U.ι ≅
        Spec (CommRingCat.of (Γ(X, U) ⧸ I))),
      pullback.snd (sourceSchemeHom X Z i) U.ι ≫ hU.isoSpec.hom =
          e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
        ∃ φ : (Scheme.Modules.restrictFunctor U.ι).obj (idealSheaf i.toShHom) ≅
            (modulePullback hU.isoSpec.hom.toLRSHom.toShHom).obj
              (tilde (ModuleCat.of Γ(X, U) I)),
          φ.hom ≫ (modulePullback hU.isoSpec.hom.toLRSHom.toShHom).map
                (tildeIdealι Γ(X, U) I) ≫
              (Stacks.IdealSheafRestrict.pullbackUnitIso hU.isoSpec.hom).hom =
            (Scheme.Modules.restrictFunctor U.ι).map
                (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
                  (structureSheafHom i.toShHom))) ≫
              (Scheme.Modules.restrictUnitIso U.ι).hom := by
  have : AlgebraicGeometry.IsClosedImmersion (sourceSchemeHom X Z i) :=
    ((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae
      (sourceSchemeHom X Z i)).out 6 1).mp hi
  exact exists_ideal_idealSheaf_restrict_iso_tilde (sourceSchemeHom X Z i) U hU

end Stacks.ClosedImmersion

end

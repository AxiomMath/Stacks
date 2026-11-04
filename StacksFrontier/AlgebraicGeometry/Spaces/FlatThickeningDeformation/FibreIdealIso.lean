module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.FibreTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardIdealLift

/-!
# The base ideal of `problem (ρ ≫ g)` is the restriction of that of `problem g`

For an isomorphism `ρ : X ≅ X₀` of algebraic spaces and `g : X₀ ⟶ Y`, the base ideal
`(ρ ≫ g)⁻¹𝒞_{Y/Y'}` of the extension problem `problem (ρ ≫ g)` is identified with the restriction
along `ρ` of the base ideal `g⁻¹𝒞_{Y/Y'}` of `problem g`, as modules over `(ρ ≫ g)⁻¹𝒪_Y`: a
section is sent to the unique section with the same image in `g⁻¹t⁻¹𝒪_{Y'}`, read through the
identification `(ρ ≫ g)⁻¹ ≅ ρ^* g⁻¹` of `fibreRingIso` (`fibreIdealApp`).

## Main definitions
* `AlgebraicGeometry.Space.FlatThickeningDeformation.fibreIdealIso`: the isomorphism
  `(problem (ρ ≫ g)).I ≅ (fibreScalarRes ρ g).obj (problem g).I`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1)
  {X X₀ : AlgebraicSpaces B S hS} (ρ : X ≅ X₀)
  (g : X₀ ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- `fibreRingIso` on the thickened base, as a map of sheaves of rings in the spelling of the
two extension problems. -/
def fibreAmbientMap :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor (problem (ρ.hom ≫ g) hZ).f.toToposHom).obj
          (problem (ρ.hom ≫ g) hZ).baseExtension) ⟶
      ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).sheafPushforwardContinuous
        RingCat.{u} (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X₀.1)).obj
        ((sheafCompose (SmallEtale.topology B S hS X₀.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((inverseImageCommRingFunctor (problem g hZ).f.toToposHom).obj
            (problem g hZ).baseExtension)) :=
  (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
    (fibreRingIso ρ g (baseExtension hZ).extension).hom

/-- On sections over `U`, `fibreAmbientMap ρ g` is the component of `fibreRingIso` at `U`. -/
theorem fibreAmbientMap_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ((smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).obj (baseExtension hZ).extension).obj.obj
      U) :
    (fibreAmbientMap hZ ρ g).hom.app U a =
      (fibreRingIso ρ g (baseExtension hZ).extension).hom.hom.app U a :=
  rfl

/-- The sectionwise maps `fibreIdealApp` lift `fibreAmbientMap ρ g` along the inclusions of the
base ideals of `problem (ρ ≫ g)` and `problem g`. -/
theorem isIdealLift_fibreIdealApp :
    SheafOfModules.IsIdealLift (F := smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
      (problem (ρ.hom ≫ g) hZ).idealInclusion (problem g hZ).idealInclusion
      (fibreAmbientMap hZ ρ g) (fibreIdealApp hZ ρ g) := fun U m =>
  (incl_fibreIdealApp hZ ρ g U m).trans (fibreAmbientMap_app hZ ρ g U _).symm

/-- The inclusion of the base ideal of `problem g₁` is injective on sections over every `V`. -/
theorem injective_fibreIdealInclusion {X₁ : AlgebraicSpaces B S hS}
    (g₁ : X₁ ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (V : (SmallEtale B S hS X₁.1)ᵒᵖ) :
    Function.Injective ((problem g₁ hZ).idealInclusion.val.app V) :=
  fun _ _ h => fibreIdeal_ext hZ g₁ h

/-- `fibreRingIso` commutes with the maps induced by the reduction `𝒪_{Y'} ⟶ 𝒪_Y` of the
thickening, as maps of sheaves of rings. -/
theorem fibreRingIso_reduction_comm :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).map (baseExtension hZ).reduction) ≫
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (fibreRingIso ρ g (smallEtaleRingedTopos B S hS _).O).hom =
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (fibreRingIso ρ g (baseExtension hZ).extension).hom ≫
      ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).sheafPushforwardContinuous
        RingCat.{u} (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X₀.1)).map
        ((sheafCompose (SmallEtale.topology B S hS X₀.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
          ((smallEtaleInverseImageRing B S hS g).map (baseExtension hZ).reduction)) := by
  have h := congrArg
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
    (fibreRingIso_naturality ρ g (baseExtension hZ).reduction)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- The inverse image along `g₁` of the reduction `𝒪_{Y'} ⟶ 𝒪_Y`, as a map of sheaves of rings,
is locally surjective. -/
instance isLocallySurjective_forget_inverseImage_baseReduction {X₁ : AlgebraicSpaces B S hS}
    (g₁ : X₁ ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X₁.1)
      ((sheafCompose (SmallEtale.topology B S hS X₁.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((smallEtaleInverseImageRing B S hS g₁).map (baseExtension hZ).reduction)).hom :=
  ⟨fun s => (isLocallySurjective_inverseImage_baseReduction hZ g₁).imageSieve_mem s⟩

/-- `fibreRingIso` on the reduced base, as a map of sheaves of rings in the spelling of the
two extension problems; pushing forward along it is `fibreScalarRes ρ g`. -/
def fibreReducedMap :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor (problem (ρ.hom ≫ g) hZ).f.toToposHom).obj
          (smallEtaleRingedTopos B S hS _).O) ⟶
      ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).sheafPushforwardContinuous
        RingCat.{u} (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X₀.1)).obj
        ((sheafCompose (SmallEtale.topology B S hS X₀.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((inverseImageCommRingFunctor (problem g hZ).f.toToposHom).obj
            (smallEtaleRingedTopos B S hS _).O)) :=
  (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
    (fibreRingIso ρ g (smallEtaleRingedTopos B S hS _).O).hom

/-- `fibreAmbientMap ρ g` and `fibreReducedMap ρ g` commute with the base reductions of
`problem (ρ ≫ g)` and `problem g`. -/
theorem fibreMaps_comm :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((inverseImageCommRingFunctor (problem (ρ.hom ≫ g) hZ).f.toToposHom).map
          (problem (ρ.hom ≫ g) hZ).baseReduction) ≫ fibreReducedMap hZ ρ g =
      fibreAmbientMap hZ ρ g ≫
        ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).sheafPushforwardContinuous
          RingCat.{u} (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X₀.1)).map
          ((sheafCompose (SmallEtale.topology B S hS X₀.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            ((inverseImageCommRingFunctor (problem g hZ).f.toToposHom).map
              (problem g hZ).baseReduction)) :=
  fibreRingIso_reduction_comm hZ ρ g

/-- The base reduction of `problem (ρ ≫ g)`, as a map of sheaves of rings, is locally
surjective. -/
instance : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((inverseImageCommRingFunctor (problem (ρ.hom ≫ g) hZ).f.toToposHom).map
          (problem (ρ.hom ≫ g) hZ).baseReduction)).hom :=
  isLocallySurjective_forget_inverseImage_baseReduction hZ (ρ.hom ≫ g)

/-- `fibreAmbientMap ρ g` is an isomorphism. -/
instance : IsIso (fibreAmbientMap hZ ρ g) := by
  unfold fibreAmbientMap; exact Functor.map_isIso _ _

/-- `fibreReducedMap ρ g` is an isomorphism. -/
instance : IsIso (fibreReducedMap hZ ρ g) := by
  unfold fibreReducedMap; exact Functor.map_isIso _ _

/-- The map of base ideals `(problem (ρ ≫ g)).I ⟶ (fibreScalarRes ρ g).obj (problem g).I`,
sectionwise `fibreIdealApp`. -/
def fibreIdealLift :
    (problem (ρ.hom ≫ g) hZ).I ⟶ (fibreScalarRes ρ g).obj (problem g hZ).I :=
  SheafOfModules.idealLift (fibreReducedMap hZ ρ g) (isIdealLift_fibreIdealApp hZ ρ g)
    (injective_fibreIdealInclusion hZ g) (fibreMaps_comm hZ ρ g)

/-- The map of base ideals `fibreIdealLift ρ g` is an isomorphism. -/
theorem isIso_fibreIdealLift : IsIso (fibreIdealLift hZ ρ g) :=
  SheafOfModules.isIso_idealLift _ _ _ _ fun U =>
    ⟨(isIdealLift_fibreIdealApp hZ ρ g).injective (injective_fibreIdealInclusion hZ g)
        (injective_fibreIdealInclusion hZ (ρ.hom ≫ g)) U,
      (isIdealLift_fibreIdealApp hZ ρ g).surjective (fibreReducedMap hZ ρ g)
        (injective_fibreIdealInclusion hZ g) (fibreMaps_comm hZ ρ g) (problem g hZ).idealZero
        (fun U a ha => ((problem (ρ.hom ≫ g) hZ).idealUniversal U a ha).exists) U⟩

/-- **The base ideal of `problem (ρ ≫ g)` is the restriction along `ρ` of that of `problem g`**,
as modules over `(ρ ≫ g)⁻¹𝒪_Y`. -/
def fibreIdealIso :
    (problem (ρ.hom ≫ g) hZ).I ≅ (fibreScalarRes ρ g).obj (problem g hZ).I :=
  haveI := isIso_fibreIdealLift hZ ρ g
  asIso (fibreIdealLift hZ ρ g)

end AlgebraicGeometry.Space.FlatThickeningDeformation

end

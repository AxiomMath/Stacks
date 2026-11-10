module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.DeformationSolution
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionEtaleRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingInverseImageKernel
public import StacksFrontier.CategoryTheory.Adjunction.UniversalArrowTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardDenseSubsiteFullyFaithful

/-!
# Transporting the solution of a deformation from its closed fibre to `X`

Let `Y ⊂ Y'` be a first order thickening of algebraic spaces, `ρ : X ≅ X₀` an isomorphism of
algebraic spaces and `g : X₀ ⟶ Y`. This file carries a solution of the extension problem of
[Stacks Project, Tag 08UF] attached to `g`
(`AlgebraicGeometry.Space.FlatThickeningDeformation.problem`)
to a solution of the problem attached to `ρ ≫ g`, along the restriction functor of the small
étale sites. It is applied in the proof of [Stacks Project, Tag 0D17] with `X₀ = X'_0` the closed
fibre of a deformation and `ρ` the identification of `X` with it.

The restricted extension is an extension of the restriction of the ring sheaf `𝒜₀` of the
solution, identified with `(ρ ≫ g)⁻¹𝒪'_Y` through the composition law of inverse images, so its
map on the base ideal is the restriction of the one of the solution. Its kernel is identified
with `(ρ ≫ g)^*𝒞_{Y/Y'}` by the adjoint transpose of that map; this transpose is an isomorphism
because the unit of extension of scalars is a universal arrow and universality survives the
restriction (`CategoryTheory.bijective_comp_map_of_transport`).

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1)

/-- The inverse image along `g` of the reduction `t⁻¹𝒪_{Y'} ⟶ 𝒪_Y` of the base extension is
locally surjective; this is the instance that makes maps out of the base ideal of `problem g`
linear over `g⁻¹𝒪_Y` as soon as they are over `g⁻¹t⁻¹𝒪_{Y'}`. -/
theorem isLocallySurjective_inverseImage_baseReduction {X : AlgebraicSpaces B S hS}
    (g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((smallEtaleInverseImageRing B S hS g).map (baseExtension hZ).reduction).hom := by
  let i₁ : HasSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} :=
    SmallEtale.instHasSheafify B S hS X.1 AddCommGrpCat.{u}
  let i₂ : (SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SmallEtale.instWEqualsLocallyBijective B S hS X.1 AddCommGrpCat.{u}
  exact isLocallySurjective_inverseImageCommRingFunctor_map
    (smallEtaleRingedToposHom B S hS g).toToposHom (baseExtension hZ).reduction
    (baseExtension hZ).locallySurjective

section RingTransport

variable {X X₀ W : AlgebraicSpaces B S hS} (ρ : X ≅ X₀) (g : X₀ ⟶ W)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for this `PreservesFiniteProducts` instance is heavy
/-- Restriction of sheaves of sets along `ρ` preserves finite products; found directly, as
instance search times out on it under Lean v4.35.0. -/
local instance (priority := high) preservesFiniteProducts_smallEtalePostcomp_FibreTransport
    {X X₀ : AlgebraicSpaces B S hS} (a : X ⟶ X₀) (ha : IsEtale B S hS a.hom) :
    Limits.PreservesFiniteProducts ((smallEtalePostcomp B S hS a ha).sheafPushforwardContinuous
      (Type u) (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X₀.1)) :=
  inferInstance

/-- The restriction functor of sheaves of rings along `ρ`. -/
abbrev fibreRingRes :=
  Deformation.AlgebraExtension.ringRes (J := SmallEtale.topology B S hS X₀.1)
    (SmallEtale.topology B S hS X.1)
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))

/-- **The inverse image along `ρ ≫ g` is the restriction along `ρ` of the inverse image along
`g`**, for sheaves of commutative rings on the small étale site of `W`: the composition law of
Stacks 03G8 followed by the identification of the inverse image along the étale `ρ` with
restriction (Stacks 03LV). -/
def fibreRingIso (A : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u}) :
    (smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).obj A ≅
      (fibreRingRes ρ).obj ((smallEtaleInverseImageRing B S hS g).obj A) :=
  ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS ρ.hom g).app A).symm ≪≫
    inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS X₀.1)
      (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
      (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
      (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
      ((smallEtaleInverseImageRing B S hS g).obj A)

/-- The isomorphism `fibreRingIso` is natural in the sheaf of rings `A`. -/
theorem fibreRingIso_naturality {A A' : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u}}
    (m : A ⟶ A') :
    (smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).map m ≫ (fibreRingIso ρ g A').hom =
      (fibreRingIso ρ g A).hom ≫
        (fibreRingRes ρ).map ((smallEtaleInverseImageRing B S hS g).map m) := by
  have hn := inverseImageCommRingRestrictionIso_naturality (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS X₀.1)
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
    (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
    ((smallEtaleInverseImageRing B S hS g).map m)
  have hc := ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS ρ.hom g).inv.naturality m)
  simp only [fibreRingIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.comp_map] at hc ⊢
  rw [← Category.assoc, hc, Category.assoc, hn, Category.assoc]

/-- On the structure sheaf, `fibreRingIso` is the ring datum of étale restriction. -/
theorem fibreRingIso_structureSheaf :
    fibreRingIso ρ g (smallEtaleRingedTopos B S hS W).O =
      (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ) g).α :=
  rfl

/-! ### Restriction of modules along `ρ` -/

/-- Restriction of `𝒪_{X₀}`-modules along `ρ`, as `𝒪_X`-modules. -/
abbrev fibreModuleRes :=
  etaleRestrictionModule B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)

/-- Restriction of sheaves of abelian groups along `ρ` is an equivalence: it is the equivalence
of sheaf categories induced by the equivalence of small étale sites. -/
instance isEquivalence_fibreSheafRes :
    ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).sheafPushforwardContinuous
      AddCommGrpCat.{u} (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS X₀.1)).IsEquivalence := by
  have := isDenseSubsite_smallEtalePostcomp_of_iso B S hS ρ
  let e := (SmallEtale.congr B S hS ((ObjectProperty.ι _).mapIso ρ)).symm
  have : e.inverse.IsDenseSubsite (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS X₀.1) := isDenseSubsite_smallEtalePostcomp_of_iso B S hS ρ
  exact (e.sheafCongr (SmallEtale.topology B S hS X₀.1) (SmallEtale.topology B S hS X.1)
    AddCommGrpCat.{u}).isEquivalence_functor

/-- Restriction of `𝒪_{X₀}`-modules along `ρ` is full. -/
instance full_fibreModuleRes : (fibreModuleRes ρ).Full := by
  have := isDenseSubsite_smallEtalePostcomp_of_iso B S hS ρ
  exact SheafOfModules.full_pushforward_of_iso
      (R := (sheafCompose (SmallEtale.topology B S hS X₀.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X₀).O) _
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
      (etaleRestrictionStructureSheafIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).symm)

/-- Restriction of `𝒪_{X₀}`-modules along `ρ` is faithful. -/
instance faithful_fibreModuleRes : (fibreModuleRes ρ).Faithful := by
  have := isDenseSubsite_smallEtalePostcomp_of_iso B S hS ρ
  exact SheafOfModules.faithful_pushforward_of_iso
      (R := (sheafCompose (SmallEtale.topology B S hS X₀.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X₀).O) _
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
      (etaleRestrictionStructureSheafIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).symm)

/-- Restriction of `𝒪_{X₀}`-modules along `ρ` is essentially surjective. -/
instance essSurj_fibreModuleRes : (fibreModuleRes ρ).EssSurj := by
  have := isDenseSubsite_smallEtalePostcomp_of_iso B S hS ρ
  exact SheafOfModules.essSurj_pushforward_of_iso
      (R := (sheafCompose (SmallEtale.topology B S hS X₀.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X₀).O) _
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
      (etaleRestrictionStructureSheafIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).symm)

/-- Restriction along `ρ` of modules over `g⁻¹𝒪_W`, as modules over `(ρ ≫ g)⁻¹𝒪_W`. -/
abbrev fibreScalarRes :
    SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X₀.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS W).O)) ⥤
    SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).obj (smallEtaleRingedTopos B S hS W).O)) :=
  SheafOfModules.pushforward.{u}
    (F := smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (fibreRingIso ρ g (smallEtaleRingedTopos B S hS W).O).hom)

/-- Restriction along `ρ` of modules over `g⁻¹𝒪_W` is full. -/
instance full_fibreScalarRes : (fibreScalarRes ρ g).Full := by
  have := isDenseSubsite_smallEtalePostcomp_of_iso B S hS ρ
  exact SheafOfModules.full_pushforward_of_iso
      (R := (sheafCompose (SmallEtale.topology B S hS X₀.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS W).O)) _
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
      (fibreRingIso ρ g (smallEtaleRingedTopos B S hS W).O))

/-- Restriction along `ρ` of modules over `g⁻¹𝒪_W` is faithful. -/
instance faithful_fibreScalarRes : (fibreScalarRes ρ g).Faithful := by
  have := isDenseSubsite_smallEtalePostcomp_of_iso B S hS ρ
  exact SheafOfModules.faithful_pushforward_of_iso
      (R := (sheafCompose (SmallEtale.topology B S hS X₀.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS W).O)) _
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
      (fibreRingIso ρ g (smallEtaleRingedTopos B S hS W).O))

/-- **Restriction along `ρ` commutes with restriction of scalars along the structure maps**:
both composites send an `𝒪_{X₀}`-module to its sections over the charts `ρ(U)`, with
`(ρ ≫ g)⁻¹𝒪_W` acting through `(ρ ≫ g)^♯` and through `g^♯`, which agree by the ring datum of
étale restriction. -/
def fibreResCommIso :
    fibreModuleRes ρ ⋙ SheafOfModules.restrictScalars
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (structureSharpInverseImage B S hS (ρ.hom ≫ g))) ≅
      SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS X₀.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map (structureSharpInverseImage B S hS g)) ⋙
        fibreScalarRes ρ g :=
  SheafOfModules.pushforwardRestrictScalarsIso
    (O := (sheafCompose (SmallEtale.topology B S hS X₀.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X₀).O)
    (A := (sheafCompose (SmallEtale.topology B S hS X₀.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS W).O))
    (O' := (sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)
    (A' := (sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).obj (smallEtaleRingedTopos B S hS W).O))
    _ _ _ _ (by
      have h := congrArg
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ) g).comm
      rw [Functor.map_comp, Functor.map_comp] at h
      exact h)

end RingTransport

/-! ### The base ideal, restricted along `ρ` -/

section IdealTransport

variable {X X₀ : AlgebraicSpaces B S hS} (ρ : X ≅ X₀)
  (g : X₀ ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- The image of a section of the base ideal of `problem (ρ ≫ g)` in the restriction of
`g⁻¹t⁻¹𝒪_{Y'}`. -/
abbrev fibreIdealImage (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : (problem (ρ.hom ≫ g) hZ).I.val.obj U) :
    ((smallEtaleInverseImageRing B S hS g).obj (baseExtension hZ).extension).obj.obj
      ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).op.obj U) :=
  (fibreRingIso ρ g (baseExtension hZ).extension).hom.hom.app U
    (show ((smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).obj
        (baseExtension hZ).extension).obj.obj U from
      (problem (ρ.hom ≫ g) hZ).idealInclusion.val.app U m)

/-- The image `fibreIdealImage` of a section of the base ideal of `problem (ρ ≫ g)` is killed by
the reduction `g⁻¹t⁻¹𝒪_{Y'} ⟶ g⁻¹𝒪_Y`. -/
theorem fibreIdealImage_reduction (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : (problem (ρ.hom ≫ g) hZ).I.val.obj U) :
    ((smallEtaleInverseImageRing B S hS g).map (baseExtension hZ).reduction).hom.app _
      (fibreIdealImage hZ ρ g U m) = 0 := by
  let x : ((smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).obj
      (baseExtension hZ).extension).obj.obj U :=
    (problem (ρ.hom ≫ g) hZ).idealInclusion.val.app U m
  have h0 : ((smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).map
      (baseExtension hZ).reduction).hom.app U x = 0 := (problem (ρ.hom ≫ g) hZ).idealZero U m
  refine (congrArg (fun φ => φ.hom.app U x)
    (fibreRingIso_naturality ρ g (baseExtension hZ).reduction)).symm.trans ?_
  change (fibreRingIso ρ g (smallEtaleRingedTopos B S hS _).O).hom.hom.app U
    (((smallEtaleInverseImageRing B S hS (ρ.hom ≫ g)).map (baseExtension hZ).reduction).hom.app U
      x) = 0
  rw [h0, map_zero]

/-- **The base ideal of `problem (ρ ≫ g)`, read on the restriction of that of `problem g`**: a
section is sent to the unique section of the base ideal of `problem g` over `ρ(U)` with the same
image in `g⁻¹t⁻¹𝒪_{Y'}`, read through `fibreRingIso`. -/
def fibreIdealApp (U : (SmallEtale B S hS X.1)ᵒᵖ) (m : (problem (ρ.hom ≫ g) hZ).I.val.obj U) :
    (problem g hZ).I.val.obj
      ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).op.obj U) :=
  ((problem g hZ).idealUniversal _ (fibreIdealImage hZ ρ g U m)
    (fibreIdealImage_reduction hZ ρ g U m)).exists.choose

/-- The section `fibreIdealApp` of the base ideal of `problem g` has image `fibreIdealImage` in
`g⁻¹t⁻¹𝒪_{Y'}`. -/
theorem incl_fibreIdealApp (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : (problem (ρ.hom ≫ g) hZ).I.val.obj U) :
    (show ((smallEtaleInverseImageRing B S hS g).obj (baseExtension hZ).extension).obj.obj
        ((smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).op.obj U) from
      (problem g hZ).idealInclusion.val.app _ (fibreIdealApp hZ ρ g U m)) =
      fibreIdealImage hZ ρ g U m :=
  ((problem g hZ).idealUniversal _ (fibreIdealImage hZ ρ g U m)
    (fibreIdealImage_reduction hZ ρ g U m)).exists.choose_spec

/-- Sections of the base ideal of `problem g` are determined by their image. -/
theorem fibreIdeal_ext {V : (SmallEtale B S hS X₀.1)ᵒᵖ} {n n' : (problem g hZ).I.val.obj V}
    (h : (show ((smallEtaleInverseImageRing B S hS g).obj (baseExtension hZ).extension).obj.obj V
        from (problem g hZ).idealInclusion.val.app V n) =
      (problem g hZ).idealInclusion.val.app V n') : n = n' := by
  have hz := (problem g hZ).idealZero V n
  exact ((problem g hZ).idealUniversal V _ hz).unique rfl h.symm

end IdealTransport

end AlgebraicGeometry.Space.FlatThickeningDeformation

end

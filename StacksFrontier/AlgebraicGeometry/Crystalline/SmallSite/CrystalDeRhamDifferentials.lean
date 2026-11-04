module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineOverAffineSubsite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineConnectionNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamSheafComplex

/-!
# The de Rham complex of a crystal in quasi-coherent modules on `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and a crystal in
quasi-coherent `𝒪_{X/S}`-modules `F` on the small crystalline site `Cris(X/S)`.  This module builds
the complex

`F → F ⊗_{𝒪_{X/S}} Ω¹_{X/S} → F ⊗_{𝒪_{X/S}} Ω²_{X/S} → ⋯`

of [Stacks, Proposition 60.23.1, Tag 07LM], with its genuine differentials: those of the canonical
connection `∇` of [Stacks, Lemma 60.15.1, Tag 07J6] on `F`, extended to all degrees by
`d(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω` ([Stacks, Section 60.15, Tag 07J5]; [Stacks, Tag 07I0]).

## The construction

The terms are the abelian sheaves `F ⊗ Ω^i_{X/S}` of `...SmallSite.tensorDifferentialFormsSheaf`,
the sheafifications of the presheaves `A ↦ F(A) ⊗ Ω^i_{X/S}(A)`.  Over an affine-over-affine object
`A` of `Cris(X/S)` — ambient scheme affine, lying over an affine open of the base — the canonical
connection is the ring-level connection `...SmallSite.AffineConnection.ringConnection`
(`∇(s) = p₁^* s - p₀^* s` read in `F(A) ⊗ Ω_{X/S}(A)`), its extensions
`...SmallSite.AffineConnection.extDiff` are natural (`...extDiff_naturality`) and compose to zero
(`...extDiff_comp_extDiff`).  The affine-over-affine objects are cover-dense in `Cris(X/S)`
(`...SmallSite.affineOverAffineι_isCoverDense`), so a morphism of presheaves into a sheaf may be
given on them alone (`...SmallSite.restrictHomEquivHom`): this is how the differentials are
assembled into morphisms of abelian sheaves, and how `d ∘ d = 0` is checked.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crystalDeRhamDifferential F hF i` — **the differential
  `F ⊗ Ω^i_{X/S} ⟶ F ⊗ Ω^{i+1}_{X/S}` of the de Rham complex of a crystal in quasi-coherent
  modules**, as a morphism of abelian sheaves on `Cris(X/S)`.
* `crystalDeRhamSheafData F hF` — the differentials with `d ∘ d = 0`.

## Main results

* `crystalDeRhamDifferential_app_toSheafify` — **the differential is the extension of the
  canonical connection**: on the sections over an affine-over-affine object it is the image of
  `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω`.
* `crystalDeRhamDifferential_comp` — consecutive differentials compose to zero.

## References

* [Stacks Project, Proposition 60.23.1, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Section 60.15, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AffineConnection

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))

/-! ### The sections of `F ⊗ Ω^i_{X/S}` over an object -/

/-- The sections of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` over an object, as a module over
the section ring in the small-site spelling. -/
instance moduleSmallFormRingSections (A : CrystallineThickening S) :
    Module (crysFormRing S A) (F.val.obj (op A)) :=
  inferInstanceAs (Module ((structureSheaf S).obj.obj (op A)) (F.val.obj (op A)))

/-- The sections of `F ⊗ Ω^i_{X/S}` over an object, in the small-site spelling. -/
def tensorFormsSectionsEquivSmall (i : ℕ) (A : CrystallineThickening S) :
    ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj (op A)) ≃+
      F.val.obj (op A) ⊗[crysFormRing S A]
        ⋀[crysFormRing S A]^i ↥((crysDifferentials S).obj (op A)) :=
  (TensorProduct.congr (LinearEquiv.refl _ (F.val.obj (op A))) (crysFormSections S i A)).toAddEquiv

/-- **The sections of the presheaf `F ⊗ Ω^i_{X/S}` over an object are `F(A) ⊗ ⋀^i Ω_{X/S}(A)`**, in
the spelling of the ring-level connection machinery. -/
def tensorFormsSectionsEquiv (i : ℕ) (A : CrystallineThickening S) :
    ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj (op A)) ≃+
      F.val.obj (op A) ⊗[GlobalCrystallineSituation.crysFormRing S A.obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S A.obj]^i
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op A.obj)) :=
  tensorFormsSectionsEquivSmall F i A

/-- **The transition maps of the presheaf `F ⊗ Ω^i_{X/S}` are `m ⊗ ω ↦ k^* m ⊗ k^* ω`**, read
through the identification of the sections. -/
theorem tensorFormsSectionsEquiv_map {A A' : CrystallineThickening S} (k : A ⟶ A') (i : ℕ)
    (y : F.val.obj (op A') ⊗[GlobalCrystallineSituation.crysFormRing S A'.obj]
      ⋀[GlobalCrystallineSituation.crysFormRing S A'.obj]^i
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op A'.obj))) :
    tensorFormsSectionsEquiv F i A ((tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).map k.op
          ((tensorFormsSectionsEquiv F i A').symm y)) =
      restrictForms F k i y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ((congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans
      (map_zero _)).trans (map_zero _).symm
  | tmul m ω => rfl
  | add x y hx hy =>
      exact ((congrArg _ ((congrArg _ (map_add _ x y)).trans (map_add _ _ _))).trans
        (map_add _ _ _)).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

/-! ### The differential over an affine-over-affine object -/

namespace AffineOverAffineCrystallineThickening

/-- The ambient scheme of an affine-over-affine object is affine. -/
instance isAffine_target (B : AffineOverAffineCrystallineThickening S) :
    IsAffine B.obj.obj.thickening.target.scheme :=
  B.property.1

/-- An affine open of the divided power base over which an affine-over-affine object lies. -/
def baseOpen (B : AffineOverAffineCrystallineThickening S) : S.S.scheme.Opens :=
  B.property.2.choose

/-- The chosen open of the base is affine. -/
theorem isAffineOpen_baseOpen (B : AffineOverAffineCrystallineThickening S) :
    IsAffineOpen B.baseOpen :=
  B.property.2.choose_spec.1

/-- The ambient scheme of an affine-over-affine object lies over the chosen open of the base. -/
theorem top_le_preimage_baseOpen (B : AffineOverAffineCrystallineThickening S) :
    (⊤ : B.obj.obj.thickening.target.scheme.Opens) ≤ B.obj.obj.toBase.hom ⁻¹ᵁ B.baseOpen :=
  B.property.2.choose_spec.2

end AffineOverAffineCrystallineThickening

open AffineOverAffineCrystallineThickening

variable {F} (hF : F.IsQuasicoherentOnSite)
include hF

/-- The base change of sections along `p₀` over an affine-over-affine object, for a crystal in
quasi-coherent modules, is bijective. -/
theorem bijective_crysExtensionSectionsMap_affine (B : AffineOverAffineCrystallineThickening S) :
    Function.Bijective (crysExtensionSectionsMap F B.obj) :=
  bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite F B.obj hF

/-- The base change of sections along `q₀` over an affine-over-affine object, for a crystal in
quasi-coherent modules, is injective. -/
theorem injective_crysSecondExtensionSectionsMap_affine
    (B : AffineOverAffineCrystallineThickening S) :
    Function.Injective (crysSecondExtensionSectionsMap F B.obj) :=
  (bijective_crysSecondExtensionSectionsMap_of_isQuasicoherentOnSite F B.obj hF).injective

/-- **The differential of the de Rham complex of `F` over an affine-over-affine object**: the
extension `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` of the canonical connection, on the sections of the
presheaf `F ⊗ Ω^i_{X/S}`. -/
def affineDeRhamDifferential (i : ℕ) (B : AffineOverAffineCrystallineThickening S) :
    ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj (op B.obj)) →+
      ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) (i + 1)).obj (op B.obj)) :=
  (tensorFormsSectionsEquiv F (i + 1) B.obj).symm.toAddMonoidHom.comp
    ((extDiff B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine hF B) i).comp
      (tensorFormsSectionsEquiv F i B.obj).toAddMonoidHom)

/-- The differential over an affine-over-affine object, read through the identification of
sections. -/
theorem tensorFormsSectionsEquiv_affineDeRhamDifferential (i : ℕ)
    (B : AffineOverAffineCrystallineThickening S) (x : ↥((tensorDifferentialForms
      (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj
        (op B.obj))) :
    tensorFormsSectionsEquiv F (i + 1) B.obj (affineDeRhamDifferential hF i B x) =
      extDiff B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine hF B) i (tensorFormsSectionsEquiv F i B.obj x) :=
  (tensorFormsSectionsEquiv F (i + 1) B.obj).apply_symm_apply _

/-- **The differential is natural** along the morphisms of the affine-over-affine subsite. -/
theorem affineDeRhamDifferential_naturality (i : ℕ)
    {B B' : AffineOverAffineCrystallineThickening S} (k : B ⟶ B')
    (x : ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj (op B'.obj))) :
    (tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) (i + 1)).map k.hom.op
        (affineDeRhamDifferential hF i B' x) =
      affineDeRhamDifferential hF i B ((tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).map k.hom.op x) := by
  refine (tensorFormsSectionsEquiv F (i + 1) B.obj).injective ?_
  have h1 := tensorFormsSectionsEquiv_map F k.hom (i + 1)
    (tensorFormsSectionsEquiv F (i + 1) B'.obj (affineDeRhamDifferential hF i B' x))
  rw [AddEquiv.symm_apply_apply] at h1
  have h2 := tensorFormsSectionsEquiv_map F k.hom i (tensorFormsSectionsEquiv F i B'.obj x)
  rw [AddEquiv.symm_apply_apply] at h2
  refine h1.trans ((congrArg (restrictForms F k.hom (i + 1))
    (tensorFormsSectionsEquiv_affineDeRhamDifferential hF i B' x)).trans
    ((extDiff_naturality B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
      B'.top_le_preimage_baseOpen B'.isAffineOpen_baseOpen
      (bijective_crysExtensionSectionsMap_affine hF B)
      (bijective_crysExtensionSectionsMap_affine hF B') k.hom i _).symm.trans ?_))
  exact (congrArg (extDiff B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
    (bijective_crysExtensionSectionsMap_affine hF B) i) h2.symm).trans
    (tensorFormsSectionsEquiv_affineDeRhamDifferential hF i B _).symm

/-- **Consecutive differentials over an affine-over-affine object compose to zero**: the canonical
connection is integrable. -/
theorem affineDeRhamDifferential_comp (i : ℕ) (B : AffineOverAffineCrystallineThickening S)
    (x : ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj (op B.obj))) :
    affineDeRhamDifferential hF (i + 1) B (affineDeRhamDifferential hF i B x) = 0 := by
  refine (tensorFormsSectionsEquiv F (i + 1 + 1) B.obj).injective ?_
  refine (tensorFormsSectionsEquiv_affineDeRhamDifferential hF (i + 1) B _).trans ?_
  refine (congrArg _ (tensorFormsSectionsEquiv_affineDeRhamDifferential hF i B x)).trans ?_
  exact (extDiff_comp_extDiff _ _ _ (injective_crysSecondExtensionSectionsMap_affine hF B) i
    _).trans (map_zero _).symm

/-! ### The differentials as morphisms of abelian sheaves -/

omit hF in
variable (F) in
/-- The abelian presheaf `F ⊗ Ω^i_{X/S}` at the coefficient universe `u + 1`; its sheafification is
`tensorDifferentialFormsSheaf F i`. -/
abbrev tensorFormsULift (i : ℕ) : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (PresheafOfModules.toPresheaf _).obj (tensorDifferentialForms (F.val : PresheafOfModules.{u}
    (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- **The differential on the affine-over-affine subsite**, as a morphism of abelian presheaves
there. -/
def affineDeRhamNat (i : ℕ) :
    (affineOverAffineι S).op ⋙ tensorFormsULift F i ⟶
      (affineOverAffineι S).op ⋙ tensorFormsULift F (i + 1) where
  app B := AddCommGrpCat.uliftFunctor.{u + 1, u}.map
    (AddCommGrpCat.ofHom (affineDeRhamDifferential hF i B.unop))
  naturality B B' k := by
    ext x
    exact congrArg ULift.up (affineDeRhamDifferential_naturality hF i k.unop x.down).symm

/-- The differential on the affine-over-affine subsite, followed by the sheafification unit. -/
def affineDeRhamToSheaf (i : ℕ) :
    (affineOverAffineι S).op ⋙ tensorFormsULift F i ⟶
      (affineOverAffineι S).op ⋙ (tensorDifferentialFormsSheaf F (i + 1)).obj :=
  affineDeRhamNat hF i ≫
    Functor.whiskerLeft (affineOverAffineι S).op
      (toSheafify (smallTopology S) (tensorFormsULift F (i + 1)))

/-- The differential, as a morphism from the presheaf `F ⊗ Ω^i_{X/S}` to the sheaf
`F ⊗ Ω^{i+1}_{X/S}`: the unique one restricting to `affineDeRhamToSheaf` on the cover-dense
affine-over-affine subsite. -/
def presheafDeRhamDifferential (i : ℕ) :
    tensorFormsULift F i ⟶ (tensorDifferentialFormsSheaf F (i + 1)).obj :=
  restrictHomEquivHom S (tensorFormsULift F i) (tensorDifferentialFormsSheaf F (i + 1))
    (affineDeRhamToSheaf hF i)

/-- **Stacks Project, Proposition 60.23.1, Tag 07LM, the differentials of the complex.**  The
differential `F ⊗ Ω^i_{X/S} ⟶ F ⊗ Ω^{i+1}_{X/S}` of the de Rham complex of a crystal in
quasi-coherent `𝒪_{X/S}`-modules, as a morphism of abelian sheaves on `Cris(X/S)`: over every
affine-over-affine object it is the extension `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` of the canonical
connection `∇` of [Stacks, Tag 07J6] (`crystalDeRhamDifferential_app_toSheafify`), and these
objects are cover-dense. -/
def crystalDeRhamDifferential (i : ℕ) :
    tensorDifferentialFormsSheaf F i ⟶ tensorDifferentialFormsSheaf F (i + 1) :=
  ObjectProperty.homMk (sheafifyLift (smallTopology S) (presheafDeRhamDifferential hF i)
    (tensorDifferentialFormsSheaf F (i + 1)).property)

/-- The differential, precomposed with the sheafification unit, is `presheafDeRhamDifferential`. -/
theorem toSheafify_crystalDeRhamDifferential (i : ℕ) :
    toSheafify (smallTopology S) (tensorFormsULift F i) ≫ (crystalDeRhamDifferential hF i).hom =
      presheafDeRhamDifferential hF i :=
  toSheafify_sheafifyLift _ _ _

/-- `presheafDeRhamDifferential` over an affine-over-affine object. -/
theorem presheafDeRhamDifferential_app (i : ℕ) (B : AffineOverAffineCrystallineThickening S)
    (x : ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj (op B.obj))) :
    (presheafDeRhamDifferential hF i).app (op B.obj) (ULift.up x) =
      (toSheafify (smallTopology S) (tensorFormsULift F (i + 1))).app (op B.obj)
        (ULift.up (affineDeRhamDifferential hF i B x)) := by
  have h := congrArg (fun α ↦ α.app (op B)) (sheafHom_restrict_eq S (affineDeRhamToSheaf hF i))
  exact ConcreteCategory.congr_hom h (ULift.up x)

/-- **The differential is the extension of the canonical connection**: on the sections over an
affine-over-affine object `A`, it carries the image of `x ∈ F(A) ⊗ Ω^i_{X/S}(A)` in
`F ⊗ Ω^i_{X/S}` to the image of `affineDeRhamDifferential x`, which on `m ⊗ ω` is
`∇(m) ∧ ω + m ⊗ d ω` (`...SmallSite.AffineConnection.extDiff_tmul`), with `∇` the canonical
connection `p₁^* m - p₀^* m` of [Stacks, Tag 07J6]
(`...SmallSite.AffineConnection.ringConnection`). -/
theorem crystalDeRhamDifferential_app_toSheafify (i : ℕ)
    (B : AffineOverAffineCrystallineThickening S)
    (x : ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj (op B.obj))) :
    (crystalDeRhamDifferential hF i).hom.app (op B.obj)
        ((toSheafify (smallTopology S) (tensorFormsULift F i)).app (op B.obj) (ULift.up x)) =
      (toSheafify (smallTopology S) (tensorFormsULift F (i + 1))).app (op B.obj)
        (ULift.up (affineDeRhamDifferential hF i B x)) := by
  have h := congrArg (fun α ↦ α.app (op B.obj)) (toSheafify_crystalDeRhamDifferential hF i)
  exact (ConcreteCategory.congr_hom h (ULift.up x)).trans (presheafDeRhamDifferential_app hF i B x)

/-- **Consecutive differentials compose to zero**, the canonical connection being integrable: the
composite vanishes on every affine-over-affine object, and those are cover-dense. -/
theorem crystalDeRhamDifferential_comp (i : ℕ) :
    crystalDeRhamDifferential hF i ≫ crystalDeRhamDifferential hF (i + 1) = 0 := by
  refine Sheaf.hom_ext (sheafify_hom_ext (smallTopology S) _ _
    (tensorDifferentialFormsSheaf F (i + 1 + 1)).property ?_)
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (crystalDeRhamDifferential hF (i + 1)).hom)
      (toSheafify_crystalDeRhamDifferential hF i))).trans ?_
  refine (hom_ext_of_app S (g := 0) (fun B ↦ ?_)).trans (comp_zero (f := toSheafify _ _)).symm
  ext x
  show (crystalDeRhamDifferential hF (i + 1)).hom.app (op B.obj)
      ((presheafDeRhamDifferential hF i).app (op B.obj) (ULift.up x.down)) = 0
  refine (congrArg ((crystalDeRhamDifferential hF (i + 1)).hom.app (op B.obj))
    (presheafDeRhamDifferential_app hF i B x.down)).trans ?_
  refine (crystalDeRhamDifferential_app_toSheafify hF (i + 1) B _).trans ?_
  refine (congrArg (fun y ↦ (toSheafify (smallTopology S) (tensorFormsULift F (i + 1 + 1))).app
    (op B.obj) (ULift.up y)) (affineDeRhamDifferential_comp hF i B x.down)).trans ?_
  exact map_zero _

/-- **The de Rham complex of a crystal in quasi-coherent modules**, as the datum
`CrystalDeRhamSheafData`: its differentials are `crystalDeRhamDifferential`, the extensions of the
canonical connection, and they compose to zero. -/
def crystalDeRhamSheafData : CrystalDeRhamSheafData S F where
  d := crystalDeRhamDifferential hF
  d_comp := crystalDeRhamDifferential_comp hF

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

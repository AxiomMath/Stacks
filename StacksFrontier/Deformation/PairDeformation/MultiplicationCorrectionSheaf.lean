module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.Deformation.PairDeformation.MultiplicationCorrection

/-!
# The multiplication correction of a sheaf of commutative rings

Let `R'` be a sheaf of commutative rings on a site, `L` a sheaf of `R'`-modules, `π : R' → L` a
derivation and `μ : L × L → R'` a symmetric `R'`-bilinear pairing with `π ∘ μ = 0`, all given
section by section and compatible with restriction. Correcting the multiplication of every ring
of sections by `x ⋆ y = x y - μ (π x) (π y)` gives a presheaf of commutative rings with the same
underlying presheaf of sets as `R'`, hence a sheaf.

## Main definitions

* `Deformation.PairDeformation.SheafMultiplicationCorrection`: the datum `(π, μ)`, natural in
  the open.
* `Deformation.PairDeformation.SheafMultiplicationCorrection.correctedSheaf`: the corrected sheaf
  of commutative rings.
* `Deformation.PairDeformation.SheafMultiplicationCorrection.homTo`: a map of sheaves of rings
  into `R'` killed by `π` is a map into the corrected sheaf.
* `Deformation.PairDeformation.SheafMultiplicationCorrection.homFrom`: a map of sheaves of rings
  out of `R'` killing the values of `μ` is a map out of the corrected sheaf.
* `Deformation.PairDeformation.SheafMultiplicationCorrection.correctedForgetIso`: the corrected
  sheaf and `R'` have the same underlying presheaf of abelian groups.

## Main results

* `Deformation.PairDeformation.SheafMultiplicationCorrection.derivation_mul`: on every section,
  `π` satisfies the Leibniz rule for the corrected multiplication.
* `Deformation.PairDeformation.SheafMultiplicationCorrection.derivation_map`: `π` commutes with
  the restriction maps of the corrected sheaf.

## Implementation notes

The rings take values in `CommRingCat.{max u v}` for a site `C : Type u` with
`Category.{v} C`, so that the sheaf condition of the corrected presheaf can be read off its
underlying presheaf of sets (`Presheaf.isSheaf_iff_isSheaf_forget`); the base's sites, with
`u = v`, are of this form.

## References

* [Stacks Project, Tag 0D4W](https://stacks.math.columbia.edu/tag/0D4W)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace Deformation.PairDeformation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]

/-- The sections of a sheaf of commutative rings act on the sections of a module over the
underlying sheaf of rings. -/
@[instance_reducible]
noncomputable def sheafSectionsModule {R' : Sheaf J CommRingCat.{max u v}}
    (L : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R'))
    (U : Cᵒᵖ) : Module (R'.obj.obj U) (L.val.obj U) :=
  inferInstanceAs (Module
    (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R').obj.obj U)
      (L.val.obj U))

attribute [local instance] sheafSectionsModule

/-- The datum of a multiplication correction of a sheaf of commutative rings `R'`: on every
section a derivation `π` into `L` and a symmetric pairing `μ` killed by `π`
(`MultiplicationCorrection`), both commuting with restriction. -/
structure SheafMultiplicationCorrection (R' : Sheaf J CommRingCat.{max u v})
    (L : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R')) where
  /-- The correction datum on the sections over `U`. -/
  correction : ∀ U : Cᵒᵖ, MultiplicationCorrection (R'.obj.obj U) (L.val.obj U)
  /-- The derivation commutes with restriction. -/
  derivation_map : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : R'.obj.obj U),
    (correction V).derivation (R'.obj.map f x) = L.val.map f ((correction U).derivation x)
  /-- The pairing commutes with restriction. -/
  pairing_map : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a b : L.val.obj U),
    R'.obj.map f ((correction U).pairing a b) =
      (correction V).pairing (L.val.map f a) (L.val.map f b)

namespace SheafMultiplicationCorrection

variable {R' : Sheaf J CommRingCat.{max u v}}
  {L : SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R')}
  (c : SheafMultiplicationCorrection R' L)

/-- The restriction map of `R'`, as a map of corrected rings. -/
noncomputable def restriction {U V : Cᵒᵖ} (f : U ⟶ V) :
    CorrectedRing (c.correction U) →+* CorrectedRing (c.correction V) where
  toFun x := CorrectedRing.toCorrected _ (R'.obj.map f (CorrectedRing.ofCorrected _ x))
  map_one' := map_one (R'.obj.map f).hom
  map_mul' x y := by
    apply CorrectedRing.ofCorrected_injective (c.correction V)
    simp only [CorrectedRing.ofCorrected_toCorrected, CorrectedRing.ofCorrected_mul, map_sub,
      map_mul, c.pairing_map, c.derivation_map]
  map_zero' := map_zero (R'.obj.map f).hom
  map_add' x y := map_add (R'.obj.map f).hom _ _

/-- On underlying sections of `R'`, the restriction map of corrected rings is the restriction
map of `R'`. -/
@[simp]
theorem ofCorrected_restriction {U V : Cᵒᵖ} (f : U ⟶ V) (x : CorrectedRing (c.correction U)) :
    CorrectedRing.ofCorrected _ (c.restriction f x) =
      R'.obj.map f (CorrectedRing.ofCorrected _ x) := rfl

/-- The corrected presheaf of commutative rings: the rings of sections of `R'` with the
corrected multiplication, and the restriction maps of `R'`. -/
noncomputable def correctedPresheaf : Cᵒᵖ ⥤ CommRingCat.{max u v} where
  obj U := CommRingCat.of (CorrectedRing (c.correction U))
  map f := CommRingCat.ofHom (c.restriction f)
  map_id U := by
    ext x
    exact congr($(R'.obj.map_id U) (CorrectedRing.ofCorrected (c.correction U) x))
  map_comp {U _ _} f g := by
    ext x
    exact congr($(R'.obj.map_comp f g) (CorrectedRing.ofCorrected (c.correction U) x))

/-- The corrected presheaf has the same underlying presheaf of sets as `R'`. -/
noncomputable def correctedForgetTypeIso :
    c.correctedPresheaf ⋙ forget CommRingCat.{max u v} ≅ R'.obj ⋙ forget CommRingCat.{max u v} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **The corrected sheaf of commutative rings.** Its sheaf condition is that of `R'`, since
the two have the same underlying presheaf of sets. -/
noncomputable def correctedSheaf : Sheaf J CommRingCat.{max u v} where
  obj := c.correctedPresheaf
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget CommRingCat.{max u v}),
      Presheaf.isSheaf_of_iso_iff c.correctedForgetTypeIso,
      ← Presheaf.isSheaf_iff_isSheaf_forget (s := forget CommRingCat.{max u v})]
    exact R'.property

/-- The sections of the corrected sheaf over `U` are the corrected ring of sections of `R'`
over `U`. -/
theorem correctedSheaf_obj (U : Cᵒᵖ) :
    c.correctedSheaf.obj.obj U = CommRingCat.of (CorrectedRing (c.correction U)) := rfl

/-- The restriction maps of the corrected sheaf are the maps `restriction` of corrected rings. -/
theorem correctedSheaf_map_apply {U V : Cᵒᵖ} (f : U ⟶ V) (x : CorrectedRing (c.correction U)) :
    c.correctedSheaf.obj.map f x = c.restriction f x := rfl

/-- **The corrected sheaf has the same underlying presheaf of abelian groups as `R'`.** -/
noncomputable def correctedForgetIso :
    c.correctedSheaf.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v} ⋙
        forget₂ RingCat.{max u v} AddCommGrpCat.{max u v} ≅
      R'.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v} ⋙
        forget₂ RingCat.{max u v} AddCommGrpCat.{max u v} :=
  NatIso.ofComponents (fun U => (CorrectedRing.equiv (c.correction U)).symm.toAddCommGrpIso)
    (fun _ => rfl)

/-- **`π` is a derivation for the corrected multiplication**, on every section, with the
action of `R'` on `L`. -/
theorem derivation_mul (U : Cᵒᵖ) (x y : CorrectedRing (c.correction U)) :
    (c.correction U).derivation (CorrectedRing.ofCorrected (c.correction U) (x * y)) =
      CorrectedRing.ofCorrected (c.correction U) x •
          (c.correction U).derivation (CorrectedRing.ofCorrected (c.correction U) y) +
        CorrectedRing.ofCorrected (c.correction U) y •
          (c.correction U).derivation (CorrectedRing.ofCorrected (c.correction U) x) :=
  CorrectedRing.derivation_ofCorrected_mul _ x y

/-- `π` commutes with the restriction maps of the corrected sheaf. -/
theorem derivation_map_correctedSheaf {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : CorrectedRing (c.correction U)) :
    (c.correction V).derivation
        (CorrectedRing.ofCorrected (c.correction V) (c.correctedSheaf.obj.map f x)) =
      L.val.map f ((c.correction U).derivation (CorrectedRing.ofCorrected (c.correction U) x)) :=
  c.derivation_map f _

/-- **A map of sheaves of rings into `R'` killed by `π` is a map into the corrected sheaf.** -/
noncomputable def homTo {S : Sheaf J CommRingCat.{max u v}} (φ : S ⟶ R')
    (hφ : ∀ (U : Cᵒᵖ) (s : S.obj.obj U), (c.correction U).derivation (φ.hom.app U s) = 0) :
    S ⟶ c.correctedSheaf :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (CorrectedRing.ringHomTo _ (φ.hom.app U).hom (hφ U))
      naturality U V f := by
        ext s
        exact congr($(φ.hom.naturality f) s) }

/-- On underlying sections of `R'`, the map `homTo φ hφ` into the corrected sheaf is `φ`. -/
@[simp]
theorem ofCorrected_homTo_app {S : Sheaf J CommRingCat.{max u v}} (φ : S ⟶ R')
    (hφ : ∀ (U : Cᵒᵖ) (s : S.obj.obj U), (c.correction U).derivation (φ.hom.app U s) = 0)
    (U : Cᵒᵖ) (s : S.obj.obj U) :
    CorrectedRing.ofCorrected (c.correction U) ((c.homTo φ hφ).hom.app U s) = φ.hom.app U s := rfl

/-- **A map of sheaves of rings out of `R'` killing the values of `μ` is a map out of the
corrected sheaf.** -/
noncomputable def homFrom {T : Sheaf J CommRingCat.{max u v}} (χ : R' ⟶ T)
    (hχ : ∀ (U : Cᵒᵖ) (a b : L.val.obj U), χ.hom.app U ((c.correction U).pairing a b) = 0) :
    c.correctedSheaf ⟶ T :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (CorrectedRing.ringHomFrom _ (χ.hom.app U).hom (hχ U))
      naturality U V f := by
        ext x
        exact congr($(χ.hom.naturality f) (CorrectedRing.ofCorrected (c.correction U) x)) }

/-- The map `homFrom χ hχ` out of the corrected sheaf is `χ` applied to the underlying section
of `R'`. -/
@[simp]
theorem homFrom_app {T : Sheaf J CommRingCat.{max u v}} (χ : R' ⟶ T)
    (hχ : ∀ (U : Cᵒᵖ) (a b : L.val.obj U), χ.hom.app U ((c.correction U).pairing a b) = 0)
    (U : Cᵒᵖ) (x : CorrectedRing (c.correction U)) :
    (c.homFrom χ hχ).hom.app U x = χ.hom.app U (CorrectedRing.ofCorrected (c.correction U) x) := rfl

/-- Composing `homTo` with `homFrom` gives the composite of the original maps. -/
theorem homTo_comp_homFrom {S T : Sheaf J CommRingCat.{max u v}} (φ : S ⟶ R')
    (hφ : ∀ (U : Cᵒᵖ) (s : S.obj.obj U), (c.correction U).derivation (φ.hom.app U s) = 0)
    (χ : R' ⟶ T)
    (hχ : ∀ (U : Cᵒᵖ) (a b : L.val.obj U), χ.hom.app U ((c.correction U).pairing a b) = 0) :
    c.homTo φ hφ ≫ c.homFrom χ hχ = φ ≫ χ := by
  ext U s
  rfl

end SheafMultiplicationCorrection

end Deformation.PairDeformation

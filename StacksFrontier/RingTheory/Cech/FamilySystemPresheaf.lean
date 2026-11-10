module

public import StacksFrontier.RingTheory.Cech.FamilySystemDiagram
public import StacksFrontier.RingTheory.Cech.PairCechColimit

/-!
# The presheaf of Čech complexes of a family system

Let `R` be a presheaf of commutative rings on a category `C` and `F` a family system on it.
This file assembles the filtered diagrams `Stacks.CechFamilySystem.cechDiagram` into a single
complex of presheaves of `R`-modules,

`Stacks.CechFamilySystem.cechComplexPresheaf F :
  CochainComplex (PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) ℤ`,

whose value over an object `V` is, degreewise, the filtered colimit over the nonempty finite
sets of distinguished families over `V` of the extended alternating Čech complexes of their
product families, together with its augmentation onto `R` placed in degree zero.

The value over `V` depends on `F` and `V` alone, the colimit being taken over all the indices,
so the restriction maps compose on the nose and the result is a presheaf. Two families spanning
the same ideal have Čech complexes that are quasi-isomorphic and not isomorphic
(`AlgebraicGeometry.RingedSite.isEmpty_iso_sheafifiedCech_oneFamily`), and no choice of
generating family is functorial (`Stacks.FunctorialCechFamily.isEmpty_functorialGenerators`).

## Main definitions

* `Stacks.CechFamilySystem.cechTermPresheaf`: the degree-`n` term, the degreewise colimit.
* `Stacks.CechFamilySystem.cechComplexPresheafNat` and
  `Stacks.CechFamilySystem.cechComplexPresheaf`: the complex, in nonnegative and in integer
  degrees.
* `Stacks.CechFamilySystem.cechAugmentationNat` and
  `Stacks.CechFamilySystem.cechAugmentation`: its augmentation onto `R`.

## Main results

* `Stacks.CechFamilySystem.transportDesc_id` and
  `Stacks.CechFamilySystem.transportDesc_comp`: the restriction maps of the degreewise colimit
  are functorial on the nose.
* `Stacks.CechFamilySystem.isColimit_sectionsCoconeNat`: the sections over an object are the
  colimit of the diagram there.

## Implementation notes

This generalises `Stacks.PairSite.cechComplexPair` from the category of pairs to an arbitrary
presheaf of rings carrying a family system. The transitions of the diagram need not be
quasi-isomorphisms here, since distinguished families over one object need not span one ideal
of sections; no quasi-isomorphism statement is proved.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CechFamilySystem

open FamilySystem

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}} (F : FamilySystem R)

/-- The presheaf of rings a presheaf of modules over `R` is indexed by. -/
abbrev ringPresheaf : Cᵒᵖ ⥤ RingCat.{u} := R ⋙ forget₂ CommRingCat RingCat

/-! ### The degreewise maps, typed through the diagram -/

/-- The degree-`n` component of the transport along an arrow of the base category. -/
def cechTransportTerm {V W : Cᵒᵖ} (a : V ⟶ W) (n : ℕ) (S : F.GenSet V) :
    (cechTermDiagram F V n).obj S ⟶
      (ModuleCat.restrictScalars (R.map a).hom).obj
        ((cechTermDiagram F W n).obj (GenSet.map a S)) :=
  (cechTransport F a S).f n

/-- The degree-`n` component of the differential of a Čech complex of the diagram. -/
def cechDiffTerm (V : Cᵒᵖ) (n : ℕ) (S : F.GenSet V) :
    (cechTermDiagram F V n).obj S ⟶ (cechTermDiagram F V (n + 1)).obj S :=
  ((cechDiagram F V).obj S).d n (n + 1)

/-- The degree-zero identification of a Čech complex of the diagram with the ring of
sections. -/
def cechAugTerm (V : Cᵒᵖ) (S : F.GenSet V) :
    (cechTermDiagram F V 0).obj S ⟶ ModuleCat.of (R.obj V) (R.obj V) :=
  (LocalCohomology.cechZeroIso (fam S) (ModuleCat.of (R.obj V) (R.obj V))).hom

/-- The transitions of the diagram commute with the transport, degreewise. -/
theorem cechTransportTerm_naturality {V W : Cᵒᵖ} (a : V ⟶ W) {S T : F.GenSet V} (h : S ⟶ T)
    (n : ℕ) :
    (cechTermDiagram F V n).map h ≫ cechTransportTerm F a n T =
      cechTransportTerm F a n S ≫
        (ModuleCat.restrictScalars (R.map a).hom).map
          ((cechTermDiagram F W n).map (homOfLE (GenSet.map_monotone a (leOfHom h)))) :=
  HomologicalComplex.congr_hom (cechDiagram_map_comp_cechTransport F a h) n

/-- The transitions of the diagram commute with the Čech differentials. -/
theorem cechDiffTerm_naturality (V : Cᵒᵖ) {S T : F.GenSet V} (h : S ⟶ T) (n : ℕ) :
    (cechTermDiagram F V n).map h ≫ cechDiffTerm F V n T =
      cechDiffTerm F V n S ≫ (cechTermDiagram F V (n + 1)).map h :=
  ((cechDiagram F V).map h).comm n (n + 1)

/-- The Čech differentials of the diagram compose to zero. -/
theorem cechDiffTerm_comp_cechDiffTerm (V : Cᵒᵖ) (n : ℕ) (S : F.GenSet V) :
    cechDiffTerm F V n S ≫ cechDiffTerm F V (n + 1) S = 0 :=
  HomologicalComplex.d_comp_d _ n (n + 1) (n + 1 + 1)

/-- The transport is a map of complexes, degreewise. -/
theorem cechDiffTerm_comp_cechTransportTerm {V W : Cᵒᵖ} (a : V ⟶ W) (n : ℕ) (S : F.GenSet V) :
    cechDiffTerm F V n S ≫ cechTransportTerm F a (n + 1) S =
      cechTransportTerm F a n S ≫
        (ModuleCat.restrictScalars (R.map a).hom).map (cechDiffTerm F W n (GenSet.map a S)) :=
  ((cechTransport F a S).comm n (n + 1)).symm

/-- The transitions of the diagram respect the degree-zero identification. -/
theorem cechAugTerm_naturality (V : Cᵒᵖ) {S T : F.GenSet V} (h : S ⟶ T) :
    (cechTermDiagram F V 0).map h ≫ cechAugTerm F V T = cechAugTerm F V S :=
  PairSite.cechZeroIso_cechGenMap (fam S) (fam T) _ _ (ModuleCat.of (R.obj V) (R.obj V))

/-- The underlying ring map of a restriction, as a map of modules over the source ring. -/
def ringTransport {V W : Cᵒᵖ} (a : V ⟶ W) :
    ModuleCat.of (R.obj V) (R.obj V) ⟶
      (ModuleCat.restrictScalars (R.map a).hom).obj (ModuleCat.of (R.obj W) (R.obj W)) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map a).hom).obj (ModuleCat.of (R.obj W) (R.obj W)))
    (CechRingBaseChange.ofRingHom (R.map a).hom)

/-- **The transport factors through the change of rings.** -/
theorem cechTransport_eq {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) :
    cechTransport F a S =
      CechRingBaseChange.complexMap (R.map a).hom (fam S) ≫
        ((ModuleCat.restrictScalars (R.map a).hom).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            (Cech.cechGenMap (CechRingBaseChange.mapFamily (R.map a).hom (fam S))
              (fam (GenSet.map a S)) (idxMap a S) (exists_dvd_map_fam a S) (R.obj W)) :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext rfl

/-- **The transport respects the degree-zero identification.** -/
theorem cechTransportTerm_comp_cechAugTerm {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) :
    cechTransportTerm F a 0 S ≫
        (ModuleCat.restrictScalars (R.map a).hom).map (cechAugTerm F W (GenSet.map a S)) =
      cechAugTerm F V S ≫ ringTransport a := by
  change (cechTransport F a S).f 0 ≫
      (ModuleCat.restrictScalars (R.map a).hom).map
        (LocalCohomology.cechZeroIso (fam (GenSet.map a S))
          (ModuleCat.of (R.obj W) (R.obj W))).hom =
    (LocalCohomology.cechZeroIso (fam S) (ModuleCat.of (R.obj V) (R.obj V))).hom ≫
      ringTransport a
  rw [cechTransport_eq, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Category.assoc, ← Functor.map_comp,
    PairSite.cechZeroIso_cechGenMap (CechRingBaseChange.mapFamily (R.map a).hom (fam S))
      (fam (GenSet.map a S)) (idxMap a S) (exists_dvd_map_fam a S)
      (ModuleCat.of (R.obj W) (R.obj W))]
  exact PairSite.cechZeroIso_complexMap (R.map a).hom (fam S)

/-! ### The degreewise colimit -/

/-- The cocone whose descent is the restriction map of the degree-`n` term. -/
def transportCocone {V W : Cᵒᵖ} (a : V ⟶ W) (n : ℕ) : Cocone (cechTermDiagram F V n) where
  pt := (ModuleCat.restrictScalars (R.map a).hom).obj (colimit (cechTermDiagram F W n))
  ι :=
    { app := fun S =>
        cechTransportTerm F a n S ≫
          (ModuleCat.restrictScalars (R.map a).hom).map
            (colimit.ι (cechTermDiagram F W n) (GenSet.map a S))
      naturality := fun S T h => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, ← Category.assoc, cechTransportTerm_naturality F a h n,
          Category.assoc, ← Functor.map_comp, colimit.w] }

/-- **The restriction map of the degree-`n` term**: the descent of the transport to the
colimit. -/
def transportDesc {V W : Cᵒᵖ} (a : V ⟶ W) (n : ℕ) :
    (colimit (cechTermDiagram F V n) : ModuleCat.{u} (R.obj V)) ⟶
      (ModuleCat.restrictScalars (R.map a).hom).obj
        (colimit (cechTermDiagram F W n) : ModuleCat.{u} (R.obj W)) :=
  colimit.desc _ (transportCocone F a n)

/-- The restriction map of the degree-`n` term, on the leg of the colimit at `S`. -/
@[simp]
theorem ι_transportDesc {V W : Cᵒᵖ} (a : V ⟶ W) (n : ℕ) (S : F.GenSet V) :
    colimit.ι (cechTermDiagram F V n) S ≫ transportDesc F a n =
      cechTransportTerm F a n S ≫
        (ModuleCat.restrictScalars (R.map a).hom).map
          (colimit.ι (cechTermDiagram F W n) (GenSet.map a S)) :=
  colimit.ι_desc _ _

/-- The descended transport, read on the elements of a leg of the colimit. -/
theorem transportDesc_ι_apply {V W : Cᵒᵖ} (a : V ⟶ W) (n : ℕ) (S : F.GenSet V)
    (x : (cechTermDiagram F V n).obj S) :
    (transportDesc F a n).hom ((colimit.ι (cechTermDiagram F V n) S).hom x) =
      (colimit.ι (cechTermDiagram F W n) (GenSet.map a S)).hom
        (((cechTransport F a S).f n).hom x) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι_transportDesc F a n S)) x

/-- The transitions of the colimit, read on elements. -/
theorem colimit_ι_apply_of_le (V : Cᵒᵖ) (n : ℕ) {S T : F.GenSet V} (h : S ⟶ T)
    (x : (cechTermDiagram F V n).obj S) :
    (colimit.ι (cechTermDiagram F V n) T).hom ((((cechDiagram F V).map h).f n).hom x) =
      (colimit.ι (cechTermDiagram F V n) S).hom x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (colimit.w (cechTermDiagram F V n) h)) x

/-- **The descended transport along an identity is the identity.** -/
theorem transportDesc_id (V : Cᵒᵖ) (n : ℕ) :
    transportDesc F (𝟙 V) n =
      (ModuleCat.restrictScalarsId' ((R.map (𝟙 V)).hom)
          (congrArg CommRingCat.Hom.hom (R.map_id V))).inv.app
        (colimit (cechTermDiagram F V n) : ModuleCat.{u} (R.obj V)) := by
  refine colimit.hom_ext fun S => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Eq.trans (transportDesc_ι_apply F (𝟙 V) n S x) ?_
  refine Eq.trans (congrArg
    (fun y => (colimit.ι (cechTermDiagram F V n) (GenSet.map (𝟙 V) S)).hom y)
    (cechTransport_id_apply F V S n x)) ?_
  exact colimit_ι_apply_of_le F V n (homOfLE (GenSet.map_id S).ge) x

/-- **The descended transports compose on the nose.** -/
theorem transportDesc_comp {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (n : ℕ) :
    transportDesc F (a ≫ b) n =
      transportDesc F a n ≫
        (ModuleCat.restrictScalars (R.map a).hom).map (transportDesc F b n) ≫
          (ModuleCat.restrictScalarsComp' (R.map a).hom (R.map b).hom (R.map (a ≫ b)).hom
              (congrArg CommRingCat.Hom.hom (R.map_comp a b))).inv.app
            (colimit (cechTermDiagram F Y n) : ModuleCat.{u} (R.obj Y)) := by
  refine colimit.hom_ext fun S => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Eq.trans (transportDesc_ι_apply F (a ≫ b) n S x) ?_
  refine Eq.trans ?_ (congrArg (fun y => (transportDesc F b n).hom y)
    (transportDesc_ι_apply F a n S x)).symm
  refine Eq.trans ?_ (transportDesc_ι_apply F b n (GenSet.map a S)
    (((cechTransport F a S).f n).hom x)).symm
  refine Eq.trans ?_ (congrArg
    (fun y => (colimit.ι (cechTermDiagram F Y n) (GenSet.map b (GenSet.map a S))).hom y)
    (cechTransport_comp_apply F a b S n x)).symm
  exact (colimit_ι_apply_of_le F Y n (homOfLE (GenSet.map_map a b S).ge)
    (((cechTransport F (a ≫ b) S).f n).hom x)).symm

/-- **The degree-`n` term of the presheaf of Čech complexes.** -/
def cechTermPresheaf (n : ℕ) : PresheafOfModules.{u} (ringPresheaf (R := R)) where
  obj V := (colimit (cechTermDiagram F V n) : ModuleCat.{u} (R.obj V))
  map {_ _} a := transportDesc F a n
  map_id V := transportDesc_id F V n
  map_comp {_ _ _} a b := transportDesc_comp F a b n

/-- The sections of the degree-`n` term over `V` are the colimit of the degree-`n` diagram. -/
@[simp]
theorem cechTermPresheaf_obj (n : ℕ) (V : Cᵒᵖ) :
    (cechTermPresheaf F n).obj V = colimit (cechTermDiagram F V n) := rfl

/-- The restriction maps of the degree-`n` term are the descended transports. -/
@[simp]
theorem cechTermPresheaf_map (n : ℕ) {V W : Cᵒᵖ} (a : V ⟶ W) :
    (cechTermPresheaf F n).map a = transportDesc F a n := rfl

/-! ### The differential -/

/-- The cocone whose descent is the differential. -/
def diffCocone (V : Cᵒᵖ) (n : ℕ) : Cocone (cechTermDiagram F V n) where
  pt := (colimit (cechTermDiagram F V (n + 1)) : ModuleCat.{u} (R.obj V))
  ι :=
    { app := fun S => cechDiffTerm F V n S ≫ colimit.ι (cechTermDiagram F V (n + 1)) S
      naturality := fun S T h => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, ← Category.assoc, cechDiffTerm_naturality F V h n,
          Category.assoc, colimit.w] }

/-- **The differential of the degree-`n` term**, descended to the colimit. -/
def diffDesc (V : Cᵒᵖ) (n : ℕ) :
    (colimit (cechTermDiagram F V n) : ModuleCat.{u} (R.obj V)) ⟶
      (colimit (cechTermDiagram F V (n + 1)) : ModuleCat.{u} (R.obj V)) :=
  colimit.desc _ (diffCocone F V n)

/-- The descended differential, on the leg of the colimit at `S`. -/
@[simp]
theorem ι_diffDesc (V : Cᵒᵖ) (n : ℕ) (S : F.GenSet V) :
    colimit.ι (cechTermDiagram F V n) S ≫ diffDesc F V n =
      cechDiffTerm F V n S ≫ colimit.ι (cechTermDiagram F V (n + 1)) S :=
  colimit.ι_desc _ _

/-- **The descended differentials commute with the descended transports.** -/
theorem transportDesc_comp_diffDesc {V W : Cᵒᵖ} (a : V ⟶ W) (n : ℕ) :
    transportDesc F a n ≫ (ModuleCat.restrictScalars (R.map a).hom).map (diffDesc F W n) =
      diffDesc F V n ≫ transportDesc F a (n + 1) := by
  refine colimit.hom_ext fun S => ?_
  rw [← Category.assoc, ι_transportDesc, Category.assoc, ← Functor.map_comp, ι_diffDesc,
    ← Category.assoc, ι_diffDesc, Category.assoc, ι_transportDesc, Functor.map_comp,
    ← Category.assoc, ← cechDiffTerm_comp_cechTransportTerm, Category.assoc]

/-- **The differential of the presheaf of Čech complexes.** -/
def cechDiffPresheaf (n : ℕ) : cechTermPresheaf F n ⟶ cechTermPresheaf F (n + 1) where
  app V := diffDesc F V n
  naturality {_ _} a := transportDesc_comp_diffDesc F a n

/-- **The descended differentials compose to zero.** -/
theorem diffDesc_comp_diffDesc (V : Cᵒᵖ) (n : ℕ) :
    diffDesc F V n ≫ diffDesc F V (n + 1) = 0 := by
  refine colimit.hom_ext fun S => ?_
  rw [← Category.assoc, ι_diffDesc, Category.assoc, ι_diffDesc, ← Category.assoc,
    cechDiffTerm_comp_cechDiffTerm, zero_comp, comp_zero]

/-! ### The complex -/

/-- **The presheaf of Čech complexes of a family system**, in nonnegative degrees. -/
def cechComplexPresheafNat :
    CochainComplex (PresheafOfModules.{u} (ringPresheaf (R := R))) ℕ :=
  CochainComplex.of (cechTermPresheaf F) (cechDiffPresheaf F) fun n =>
    PresheafOfModules.hom_ext fun V => diffDesc_comp_diffDesc F V n

/-- The degree-`n` term of the presheaf of Čech complexes is `cechTermPresheaf F n`. -/
@[simp]
theorem cechComplexPresheafNat_X (n : ℕ) :
    (cechComplexPresheafNat F).X n = cechTermPresheaf F n := rfl

/-- The differential from degree `n` to `n + 1` is `cechDiffPresheaf F n`. -/
@[simp]
theorem cechComplexPresheafNat_d (n : ℕ) :
    (cechComplexPresheafNat F).d n (n + 1) = cechDiffPresheaf F n :=
  CochainComplex.of_d _ _ n

/-- **The presheaf of Čech complexes of a family system**, in integer degrees. -/
abbrev cechComplexPresheaf :
    CochainComplex (PresheafOfModules.{u} (ringPresheaf (R := R))) ℤ :=
  (cechComplexPresheafNat F).extend ComplexShape.embeddingUpNat

/-! ### The augmentation -/

/-- The cocone whose descent is the augmentation. -/
def augCocone (V : Cᵒᵖ) : Cocone (cechTermDiagram F V 0) where
  pt := ModuleCat.of (R.obj V) (R.obj V)
  ι :=
    { app := fun S => cechAugTerm F V S
      naturality := fun S T h => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, cechAugTerm_naturality] }

/-- **The augmentation of the degree-zero term**, descended to the colimit. -/
def augDesc (V : Cᵒᵖ) :
    (colimit (cechTermDiagram F V 0) : ModuleCat.{u} (R.obj V)) ⟶
      ModuleCat.of (R.obj V) (R.obj V) :=
  colimit.desc _ (augCocone F V)

/-- The descended augmentation, on the leg of the colimit at `S`. -/
@[simp]
theorem ι_augDesc (V : Cᵒᵖ) (S : F.GenSet V) :
    colimit.ι (cechTermDiagram F V 0) S ≫ augDesc F V = cechAugTerm F V S :=
  colimit.ι_desc _ _

/-- **The descended augmentations commute with the descended transports.** -/
theorem transportDesc_comp_augDesc {V W : Cᵒᵖ} (a : V ⟶ W) :
    transportDesc F a 0 ≫ (ModuleCat.restrictScalars (R.map a).hom).map (augDesc F W) =
      augDesc F V ≫ ringTransport a := by
  refine colimit.hom_ext fun S => ?_
  rw [← Category.assoc, ι_transportDesc, Category.assoc, ← Functor.map_comp, ι_augDesc,
    ← Category.assoc, ι_augDesc, cechTransportTerm_comp_cechAugTerm]

/-- **The augmentation of the degree-zero term onto `R`.** -/
def cechAugZero : cechTermPresheaf F 0 ⟶ PresheafOfModules.unit (ringPresheaf (R := R)) where
  app V := augDesc F V
  naturality {_ _} a := transportDesc_comp_augDesc F a

/-- **The augmentation of the presheaf of Čech complexes onto `R`**, in nonnegative degrees. -/
def cechAugmentationNat :
    cechComplexPresheafNat F ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
        (PresheafOfModules.unit (ringPresheaf (R := R))) :=
  (CochainComplex.toSingle₀Equiv _ _).symm (cechAugZero F)

/-- **The augmentation of the presheaf of Čech complexes onto `R`**, in integer degrees. -/
def cechAugmentation :
    cechComplexPresheaf F ⟶ (CochainComplex.singleFunctor _ 0).obj
      (PresheafOfModules.unit (ringPresheaf (R := R))) :=
  HomologicalComplex.extendMap (cechAugmentationNat F) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      (PresheafOfModules.unit (ringPresheaf (R := R))) 0 0 rfl).hom

/-- Cancellation of isomorphisms in a composite of morphisms in a category. -/
private theorem comp_comp_inv_comp_inv_hom_hom {𝒞 : Type*} [Category 𝒞] {A B C D E F : 𝒞}
    (a : A ⟶ B) (b : B ⟶ C) (e₁ : D ≅ C) (e₂ : E ≅ D) (g : C ⟶ F) :
    (a ≫ (b ≫ e₁.inv) ≫ e₂.inv) ≫ e₂.hom ≫ e₁.hom ≫ g = a ≫ b ≫ g := by
  simp

/-- The augmentation in degree zero is `cechAugZero F`, followed by the identification of the
degree-zero object of the single complex. -/
theorem cechAugmentationNat_f_zero :
    (cechAugmentationNat F).f 0 =
      cechAugZero F ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
        (PresheafOfModules.unit (ringPresheaf (R := R)))).inv :=
  HomologicalComplex.mkHomToSingle_f _ fun i hi => by simp at hi

/-- **The augmentation in degree zero**: the descended augmentation of the degree-zero term,
read through the identification of the degree-zero term of the extension by zero. -/
theorem cechAugmentation_f_zero :
    (cechAugmentation F).f 0 =
      ((cechComplexPresheafNat F).extendXIso ComplexShape.embeddingUpNat
          (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom ≫
        cechAugZero F ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
            (PresheafOfModules.unit (ringPresheaf (R := R)))).inv := by
  have h1 : (cechAugmentation F).f 0 =
      (HomologicalComplex.extendMap (cechAugmentationNat F) ComplexShape.embeddingUpNat).f 0 ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
            (PresheafOfModules.unit (ringPresheaf (R := R))) 0 0
            (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom.f 0 := rfl
  rw [h1, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl),
    cechAugmentationNat_f_zero]
  exact comp_comp_inv_comp_inv_hom_hom (𝒞 := PresheafOfModules.{u} (ringPresheaf (R := R)))
    _ _ _ _ _

/-! ### The sections over an object are the colimit -/

/-- **The sections of the `ℕ`-graded presheaf of Čech complexes over an object**, written over
that object's own ring of sections. -/
abbrev sectionsNat (V : Cᵒᵖ) : CochainComplex (ModuleCat.{u} (R.obj V)) ℕ :=
  ((PresheafOfModules.evaluation (ringPresheaf (R := R)) V).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (cechComplexPresheafNat F)

/-- The differential of the sections over `V` from degree `n` to `n + 1` is `diffDesc F V n`. -/
theorem sectionsNat_d (V : Cᵒᵖ) (n : ℕ) : (sectionsNat F V).d n (n + 1) = diffDesc F V n :=
  congrArg (fun w => (PresheafOfModules.evaluation (ringPresheaf (R := R)) V).map w)
    (cechComplexPresheafNat_d F n)

/-- **The sections over an object, as a cocone on the diagram there.** -/
def sectionsCoconeNat (V : Cᵒᵖ) : Cocone (cechDiagram F V) where
  pt := sectionsNat F V
  ι :=
    { app := fun S =>
        { f := fun n => colimit.ι (cechTermDiagram F V n) S
          comm' := fun n m hnm => by
            obtain rfl : n + 1 = m := hnm
            exact Eq.trans (congrArg (fun w => colimit.ι (cechTermDiagram F V n) S ≫ w)
              (sectionsNat_d F V n)) (ι_diffDesc F V n S) }
      naturality := fun S T h =>
        HomologicalComplex.hom_ext _ _ fun n =>
          (colimit.w (cechTermDiagram F V n) h).trans (Category.comp_id _).symm }

/-- **The leg of the sections cocone at one index.** -/
def sectionsLegNat (V : Cᵒᵖ) (S : F.GenSet V) :
    Cech.cechComplex (fam S) (R.obj V) ⟶ sectionsNat F V :=
  (sectionsCoconeNat F V).ι.app S

/-- The degree-`n` component of the leg at `S` is the colimit inclusion at `S`. -/
@[simp]
theorem sectionsLegNat_f (V : Cᵒᵖ) (S : F.GenSet V) (n : ℕ) :
    (sectionsLegNat F V S).f n = colimit.ι (cechTermDiagram F V n) S := rfl

/-- **The sections over an object are the colimit of the diagram there.** -/
def isColimit_sectionsCoconeNat (V : Cᵒᵖ) : IsColimit (sectionsCoconeNat F V) := by
  refine HomologicalComplex.isColimitOfEval _ _ fun n => ?_
  exact IsColimit.ofIsoColimit (colimit.isColimit (cechTermDiagram F V n))
    (Cocone.ext (Iso.refl _) fun S => Category.comp_id _)

end Stacks.CechFamilySystem

end

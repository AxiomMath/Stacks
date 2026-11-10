module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.Transport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseFactorisation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheaf

/-!
# Flat deformations of a scheme over a first order thickening of the base

A flat deformation of `f : X ⟶ S` over a first order thickening `t : S ⟶ S'` is a pair
`(f' : X' ⟶ S', a : X ≅ X' ×_{S'} S)` as in [Stacks Project, Tag 0D14]
(`Stacks.Thickenings.FlatDeformation`, with `FlatDeformation.ofPair` and `FlatDeformation.a`).
This file attaches to it a solution of the deformation problem `FlatDeformation.problem`
(`FlatDeformation.toSolution`), and proves that the kernel map of that problem does not depend on
the deformation (`FlatDeformation.idealMap_eq`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.Thickenings

/-- A composite of morphisms of sheaves of modules on a section. -/
theorem sheafOfModules_comp_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} R} (l : M ⟶ N) (m : N ⟶ P) (U : Cᵒᵖ)
    (a : M.val.obj U) :
    ((l ≫ m).val.app U).hom a = (m.val.app U).hom ((l.val.app U).hom a) :=
  rfl

/-- Restriction of scalars along two equal composites gives the same module. -/
def restrictScalarsCompIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R R₁ R₂ R₃ : Sheaf J RingCat.{u}} (β : R ⟶ R₁) (γ : R₁ ⟶ R₃) (α : R ⟶ R₂) (δ : R₂ ⟶ R₃)
    (h : β ≫ γ = α ≫ δ) (M : SheafOfModules.{u} R₃) :
    (SheafOfModules.restrictScalars β).obj ((SheafOfModules.restrictScalars γ).obj M) ≅
      (SheafOfModules.restrictScalars α).obj ((SheafOfModules.restrictScalars δ).obj M) where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) (fun U r m =>
    congrArg (fun φ : R ⟶ R₃ => (φ.hom.app U).hom r • (show M.val.obj U from m)) h)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) (fun U r m =>
    (congrArg (fun φ : R ⟶ R₃ => (φ.hom.app U).hom r • (show M.val.obj U from m)) h).symm)⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

variable {X S S' : Scheme.{u}}

/-- **A flat deformation of `f : X ⟶ S` over `S ⊂ S'`**: a flat morphism `f' : X' ⟶ S'` together
with an identification `X ≅ X' ×_{S'} S` over `S`, recorded as a morphism `i : X ⟶ X'` making the
square `i ≫ f' = f ≫ t` cartesian. -/
structure FlatDeformation (t : S ⟶ S') (f : X ⟶ S) where
  /-- The deformed scheme. -/
  X' : Scheme.{u}
  /-- Its morphism to the thickened base. -/
  f' : X' ⟶ S'
  /-- The deformation is flat over the thickened base. -/
  [flat : Flat f']
  /-- The identification of `X` with the fibre of `X'` over `S`. -/
  i : X ⟶ X'
  /-- The square is cartesian: `X = X' ×_{S'} S`. -/
  isPullback : IsPullback i f f' t

attribute [instance] FlatDeformation.flat

namespace FlatDeformation

variable {t : S ⟶ S'} {f : X ⟶ S}

/-- **An isomorphism of flat deformations**: an isomorphism of the deformed schemes over `S'`
compatible with the identifications of `X` with their fibres over `S`. -/
structure Iso (D₁ D₂ : FlatDeformation t f) where
  /-- The isomorphism of the deformed schemes. -/
  e : D₁.X' ≅ D₂.X'
  /-- It is compatible with the identifications of `X`. -/
  comm_i : D₁.i ≫ e.hom = D₂.i
  /-- It is a morphism over `S'`. -/
  comm_f' : e.hom ≫ D₂.f' = D₁.f'

/-- Isomorphism of flat deformations is an equivalence relation. -/
def setoid (t : S ⟶ S') (f : X ⟶ S) : Setoid (FlatDeformation t f) where
  r D₁ D₂ := Nonempty (Iso D₁ D₂)
  iseqv :=
    { refl D := ⟨⟨CategoryTheory.Iso.refl _, Category.comp_id _, Category.id_comp _⟩⟩
      symm := fun ⟨φ⟩ => ⟨⟨φ.e.symm, by
        rw [← φ.comm_i, Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id], by
        rw [Iso.symm_hom, Iso.inv_comp_eq, φ.comm_f']⟩⟩
      trans := fun ⟨φ⟩ ⟨ψ⟩ => ⟨⟨φ.e ≪≫ ψ.e, by
        rw [Iso.trans_hom, ← Category.assoc, φ.comm_i, ψ.comm_i], by
        rw [Iso.trans_hom, Category.assoc, ψ.comm_f', φ.comm_f']⟩⟩ }

/-- **The set of isomorphism classes of flat deformations.** -/
abbrev Classes (t : S ⟶ S') (f : X ⟶ S) : Type _ := Quotient (setoid t f)

/-! ### Flat deformations are the pairs `(f', a)` of the source -/

section Pair

variable (D : FlatDeformation t f)

/-- The identification `a : X ≅ X' ×_{S'} S` of a flat deformation. -/
def a : X ≅ pullback D.f' t := D.isPullback.isoPullback

/-- The identification `a` is over `S`. -/
@[reassoc (attr := simp)]
theorem a_hom_snd : D.a.hom ≫ pullback.snd D.f' t = f :=
  IsPullback.isoPullback_hom_snd _

/-- The identification `a` followed by the projection to `X'` is `i`. -/
@[reassoc (attr := simp)]
theorem a_hom_fst : D.a.hom ≫ pullback.fst D.f' t = D.i :=
  IsPullback.isoPullback_hom_fst _

/-- **The flat deformation attached to a pair `(f', a)`** of a flat morphism `f' : X' ⟶ S'` and
an isomorphism `a : X ≅ X' ×_{S'} S` over `S`. -/
def ofPair {X' : Scheme.{u}} (f' : X' ⟶ S') [Flat f'] (a : X ≅ pullback f' t)
    (ha : a.hom ≫ pullback.snd f' t = f) : FlatDeformation t f where
  X' := X'
  f' := f'
  i := a.hom ≫ pullback.fst f' t
  isPullback := IsPullback.of_iso_pullback ⟨by rw [← ha]; simp [pullback.condition]⟩ a rfl ha

/-- The identification `a` of the flat deformation attached to a pair `(f', a)` is `a`. -/
@[simp]
theorem ofPair_a {X' : Scheme.{u}} (f' : X' ⟶ S') [Flat f'] (a : X ≅ pullback f' t)
    (ha : a.hom ≫ pullback.snd f' t = f) : (ofPair f' a ha).a = a :=
  CategoryTheory.Iso.ext (pullback.hom_ext ((a_hom_fst _).trans rfl) ((a_hom_snd _).trans ha.symm))

/-- **Isomorphisms of flat deformations are the isomorphisms of pairs `(f', a)`**: isomorphisms
`e : X'₁ ≅ X'₂` over `S'` with `(e ×_{S'} S) ∘ a₁ = a₂`. -/
theorem nonempty_iso_iff (D₁ D₂ : FlatDeformation t f) :
    Nonempty (Iso D₁ D₂) ↔ ∃ (e : D₁.X' ≅ D₂.X') (h : e.hom ≫ D₂.f' = D₁.f'),
      D₁.a.hom ≫ pullback.map D₁.f' t D₂.f' t e.hom (𝟙 S) (𝟙 S') (by simp [h]) (by simp) =
        D₂.a.hom := by
  constructor
  · rintro ⟨φ⟩
    refine ⟨φ.e, φ.comm_f', pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, pullback.lift_fst, a_hom_fst_assoc, φ.comm_i, a_hom_fst]
    · rw [Category.assoc, pullback.lift_snd, a_hom_snd_assoc, Category.comp_id, a_hom_snd]
  · rintro ⟨e, h, ha⟩
    refine ⟨⟨e, ?_, h⟩⟩
    simpa only [Category.assoc, pullback.lift_fst, a_hom_fst_assoc, a_hom_fst] using
      congrArg (· ≫ pullback.fst D₂.f' t) ha

end Pair

variable (D : FlatDeformation t f)

/-- The morphism `i : X ⟶ X'` of a flat deformation over a closed immersion `t` is a closed
immersion. -/
instance [IsClosedImmersion t] : IsClosedImmersion D.i :=
  MorphismProperty.of_isPullback D.isPullback.flip inferInstance

/-- Over a first order thickening, the ideal of `X` in a flat deformation has square zero. -/
theorem ker_sq [IsClosedImmersion t] (hst : t.ker ^ 2 = ⊥) : D.i.ker ^ 2 = ⊥ :=
  ker_pow_eq_bot_of_isPullback D.isPullback inferInstance hst

/-- Over a first order thickening, the morphism `i : X ⟶ X'` of a flat deformation is
surjective. -/
theorem surjective [IsClosedImmersion t] (hst : t.ker ^ 2 = ⊥) : Surjective D.i := by
  have : Surjective t := ⟨(IsFirstOrderThickening.isThickening ⟨inferInstance, hst⟩).2⟩
  exact MorphismProperty.of_isPullback D.isPullback.flip inferInstance

/-- Over a first order thickening, the morphism `i : X ⟶ X'` of a flat deformation is a
homeomorphism on underlying spaces. -/
theorem isIso_base [IsClosedImmersion t] (hst : t.ker ^ 2 = ⊥) : IsIso D.i.base :=
  TopCat.isIso_of_bijective_of_isClosedMap D.i.base
    ⟨D.i.isClosedEmbedding.injective, (D.surjective hst).surj⟩ D.i.isClosedEmbedding.isClosedMap

omit D in
/-- A first order thickening of schemes is a homeomorphism on underlying spaces. -/
theorem isIso_base_of_firstOrder {Y Y' : Scheme.{u}} (j : Y ⟶ Y') [IsClosedImmersion j]
    (hj : j.ker ^ 2 = ⊥) : IsIso j.base :=
  TopCat.isIso_of_bijective_of_isClosedMap j.base
    ⟨j.isClosedEmbedding.injective, (IsFirstOrderThickening.isThickening ⟨inferInstance, hj⟩).2⟩
    j.isClosedEmbedding.isClosedMap

/-- The canonical isomorphism `f^*𝒞_{S/S'} ≅ 𝒞_{X/X'}` of a flat deformation. -/
def conormalIso [IsClosedImmersion t] : pullbackConormalModule f t ≅ conormalModules D.i :=
  @asIso _ _ _ _ (Stacks.Immersion.immersionConormalSheafMap D.i t f D.f'
      (Stacks.Immersion.toShHom_square D.isPullback.w))
    (Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat D.i t f D.f' D.isPullback)

/-! ### The solution of the extension problem attached to a flat deformation -/

section Solution

open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap
  sheafAdjunction structureSheafMap)
open FlatDeformation

variable [IsClosedImmersion t] (hst : t.ker ^ 2 = ⊥) (D : FlatDeformation t f) [IsIso D.i.base]

/-- The structure sheaf of the deformed scheme, carried to the space of `X`. -/
abbrev sheaf : TopCat.Sheaf CommRingCat.{u} X :=
  transported D.i

/-- The reduction of the deformation, on the space of `X`. -/
abbrev reduction : sheaf D ⟶ X.sheaf :=
  transportedReduction D.i

/-- The reduction of a flat deformation is locally surjective as a morphism of sheaves of
rings. -/
instance isLocallySurjective_forget₂_reduction :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (reduction D)).hom :=
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (reduction D).hom :=
    isLocallySurjective_transportedReduction D.i
  isLocallySurjective_forget₂_map _

/-- The map from the thickened base ring into the deformation, on the space of `X`. -/
def baseRingMap : thickenedBaseRing t f ⟶ sheaf D :=
  ((sheafAdjunction (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom)).homEquiv _ _).symm
    (transportedBase D.i D.isPullback.w)

omit [IsClosedImmersion t] in
/-- The map from the thickened base ring followed by the reduction is the structure map
`(t ∘ f)⁻¹𝒪_{S'} ⟶ 𝒪_X`. -/
theorem baseRingMap_comp_reduction :
    baseRingMap D ≫ reduction D =
      inverseImageStructureMap (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom) := by
  refine ((sheafAdjunction (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom)).homEquiv _ _).injective ?_
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
  refine (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ?_
  exact (transportedBase_comp_reduction D.i D.isPullback.w).trans
    (Stacks.Sheaves.RingedSpaceDifferentials.homEquiv_inverseImageStructureMap _).symm

/-- The map from the thickened base ring, read through the inverse image along the identity. -/
abbrev baseMap : rebuilt f (thickenedBaseRing t f) ⟶ sheaf D :=
  (idIso f (thickenedBaseRing t f)).hom ≫ baseRingMap D

omit [IsClosedImmersion t] in
/-- The base map followed by the reduction is the reduction of the thickened base followed by
the structure map of `f`. -/
theorem baseMap_comp_reduction : baseMap D ≫ reduction D =
    rebuiltReduction t f ≫ (structureHom f).fSharpInverseImage :=
  ((Category.assoc _ _ _).trans (congrArg ((idIso f (thickenedBaseRing t f)).hom ≫ ·)
    (baseRingMap_comp_reduction D))).trans
    (rebuiltReduction_comp_fSharpInverseImage t f).symm

/-- The identification of `f^*𝒞_{S/S'}` with the ideal of `X` in the deformation. -/
def kernelIncl :
    (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (reduction D))).obj (conormalModule t f) ⟶
      SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (sheaf D)) :=
  kernelInclusion D.i (D.ker_sq hst) D.conormalIso

/-- On sections, `kernelIncl` is `kernelSection`. -/
theorem kernelIncl_app (U : X.Opens) (m : Γ(conormalModule t f, U)) :
    (kernelIncl hst D).val.app (op U) m =
      kernelSection D.i (D.ker_sq hst) D.conormalIso U m :=
  rfl

/-- The reduction kills the image of `kernelIncl`. -/
theorem reduction_kernelIncl (U : X.Opens) (m : Γ(conormalModule t f, U)) :
    (reduction D).hom.app (op U) ((kernelIncl hst D).val.app (op U) m) = 0 :=
  transportedReduction_kernelSection D.i (D.ker_sq hst) D.conormalIso U m

/-- `kernelIncl` is injective on sections. -/
theorem kernelIncl_injective (U : X.Opens) :
    Function.Injective ((kernelIncl hst D).val.app (op U)) :=
  kernelSection_injective D.i (D.ker_sq hst) D.conormalIso U

/-- Every section of the deformation killed by the reduction lies in the image of
`kernelIncl`. -/
theorem exists_kernelIncl_eq (U : X.Opens) (a : (sheaf D).presheaf.obj (op U))
    (ha : (reduction D).hom.app (op U) a = 0) :
    ∃ m, (kernelIncl hst D).val.app (op U) m = a :=
  exists_kernelSection_eq D.i (D.ker_sq hst) D.conormalIso U a ha

omit [IsClosedImmersion t] in
/-- The base map on the ideal of the thickened base lands in the ideal of `X` in the
deformation. -/
theorem reduction_baseMap_of_mem (U : X.Opensᵒᵖ) (a : (idealKernel t f).val.obj U) :
    (reduction D).hom.app U ((baseMap D).hom.app U a.1) = 0 := by
  have h := congrArg (fun φ => φ.hom.app U a.1) (baseMap_comp_reduction D)
  refine h.trans ?_
  change (structureHom f).fSharpInverseImage.hom.app U ((rebuiltReduction t f).hom.app U a.1) = 0
  rw [show (rebuiltReduction t f).hom.app U a.1 = 0 from a.2]
  exact map_zero _

omit [IsClosedImmersion t] in
/-- `baseMap_comp_reduction` on the underlying sheaves of rings. -/
theorem forget₂_baseMap_comp_reduction :
    (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (baseMap D) ≫
      (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (reduction D) =
    rebuiltReductionRing t f ≫
      (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage :=
  ((Functor.map_comp _ _ _).symm.trans (congrArg _ (baseMap_comp_reduction D))).trans
    (Functor.map_comp _ _ _)

/-- There is a unique morphism from the ideal of the thickened base to `f^*𝒞_{S/S'}`, linear
over the thickened base ring, whose composite with `kernelIncl` is the base map on the
ideal. -/
theorem existsUnique_idealMapLift : ∃! l : idealKernel t f ⟶ (SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (baseMap D))).obj ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (reduction D))).obj (conormalModule t f)),
    l ≫ (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (baseMap D))).map (kernelIncl hst D) =
      SheafOfModules.kerIota _ ≫ SheafOfModules.unitToRestrictScalarsObjUnit
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (baseMap D)) :=
  Stacks.SheafOfModules.existsUnique_factorThrough
    ((SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (baseMap D))).map (kernelIncl hst D))
    (fun U => kernelIncl_injective hst D U.unop)
    (SheafOfModules.kerIota _ ≫ SheafOfModules.unitToRestrictScalarsObjUnit
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (baseMap D)))
    (fun U a => exists_kernelIncl_eq hst D U.unop _ (reduction_baseMap_of_mem D U a))

/-- The action of the ideal of the thickened base on the deformation, as a morphism of modules
over the thickened base ring. -/
def idealMapLift : idealKernel t f ⟶ (SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (baseMap D))).obj ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (reduction D))).obj (conormalModule t f)) :=
  (existsUnique_idealMapLift hst D).exists.choose

/-- The value of the action of the ideal on a section. -/
def idealMapLiftApp (U : X.Opensᵒᵖ) (a : (idealKernel t f).val.obj U) :
    ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (reduction D))).obj (conormalModule t f)).val.obj U :=
  ((idealMapLift hst D).val.app U).hom a

/-- `kernelIncl` sends `idealMapLiftApp U a` to the image of `a` under the base map. -/
theorem kernelIncl_idealMapLift (U : X.Opensᵒᵖ) (a : (idealKernel t f).val.obj U) :
    ((kernelIncl hst D).val.app U).hom (idealMapLiftApp hst D U a) =
      ((baseMap D).hom.app U).hom a.1 := by
  have h := congrArg (fun φ => (φ.val.app U).hom a)
    (existsUnique_idealMapLift hst D).exists.choose_spec
  have h1 : (((idealMapLift hst D ≫ (SheafOfModules.restrictScalars ((sheafCompose
      (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (baseMap D))).map (kernelIncl hst D)).val.app U).hom a) =
      ((((SheafOfModules.restrictScalars ((sheafCompose
      (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (baseMap D))).map (kernelIncl hst D)).val.app U).hom
        (((idealMapLift hst D).val.app U).hom a)) :=
    sheafOfModules_comp_app_apply _ _ U a
  have h2 : (((SheafOfModules.kerIota _ ≫ SheafOfModules.unitToRestrictScalarsObjUnit
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (baseMap D))).val.app U).hom a) = ((baseMap D).hom.app U).hom a.1 := rfl
  exact h1.symm.trans (h.trans h2)

/-- **The map `c` of the deformation problem determined by a flat deformation**: the action of
the ideal of the thickened base on the deformation, read through `f^*𝒞_{S/S'} ≅ 𝒞_{X/X'}`. -/
def idealMap : ideal t f hst ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage)).obj (conormalModule t f) :=
  (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
    (rebuiltReductionRing t f)).preimage
    ((Stacks.SheafOfModules.ChangeOfRings.restrictScalarsLiftedSheafIso (rebuiltReductionRing t f)
      (idealKernel t f) (smul_idealKernel_eq_zero t f hst)).hom ≫ idealMapLift hst D ≫
      (restrictScalarsCompIso _ _ _ _ (forget₂_baseMap_comp_reduction D)
        (conormalModule t f)).hom)

/-- On sections, `idealMap` is `idealMapLiftApp`. -/
theorem idealMap_app (U : X.Opensᵒᵖ) (a : (ideal t f hst).val.obj U) :
    ((idealMap hst D).val.app U).hom a = idealMapLiftApp hst D U a :=
  congrArg (fun φ => (φ.val.app U).hom (show ((SheafOfModules.restrictScalars
      (rebuiltReductionRing t f)).obj (ideal t f hst)).val.obj U from a))
    ((Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      (rebuiltReductionRing t f)).map_preimage
      ((Stacks.SheafOfModules.ChangeOfRings.restrictScalarsLiftedSheafIso
        (rebuiltReductionRing t f) (idealKernel t f) (smul_idealKernel_eq_zero t f hst)).hom ≫
        idealMapLift hst D ≫
        (restrictScalarsCompIso _ _ _ _ (forget₂_baseMap_comp_reduction D)
          (conormalModule t f)).hom))

/-- `idealMap` followed by `kernelIncl` is the inclusion of the ideal of the thickened base
followed by the base map. -/
theorem kernelIncl_idealMap (U : X.Opensᵒᵖ) (a : (ideal t f hst).val.obj U) :
    ((kernelIncl hst D).val.app U).hom (((idealMap hst D).val.app U).hom a) =
      ((baseMap D).hom.app U).hom (((idealInclusion t f hst).val.app U).hom a) :=
  (congrArg _ (idealMap_app hst D U a)).trans (kernelIncl_idealMapLift hst D U a)

/-- **The solution of the deformation problem attached to a flat deformation.** -/
def toSolution (c : ideal t f hst ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage)).obj (conormalModule t f))
    (hc : c = idealMap hst D) : (problem t f hst c).CompatibleFirstOrderThickening where
  extension := sheaf D
  reduction := reduction D
  locallySurjective := isLocallySurjective_transportedReduction D.i
  squareZero := transportedReduction_ker_sq D.i (D.ker_sq hst)
  baseMap := baseMap D
  baseMap_reduction := baseMap_comp_reduction D
  kernelInclusion := kernelIncl hst D
  kernelZero U a := reduction_kernelIncl hst D U.unop a
  kernelUniversal U a ha := by
    obtain ⟨m, hm⟩ := exists_kernelIncl_eq hst D U.unop a ha
    exact ⟨m, hm, fun m' hm' => kernelIncl_injective hst D U.unop (hm'.trans hm.symm)⟩
  baseMap_ideal U a := by
    subst hc
    exact (kernelIncl_idealMap hst D U a).symm

/-! ### The canonical elements of `f^*𝒞_{S/S'}` -/

/-- The image in `f^*𝒞_{S/S'}` of a section `j` of the ideal of `S` in `S'`: the pullback of its
conormal class. -/
def canonicalSection (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0) :
    Γ(conormalModule t f, (Opens.map (f.base ≫ t.base)).obj W) :=
  (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    f.toLRSHom.toShHom).unit.app (Stacks.Conormal.conormalSheaf t)).val.app (op (t ⁻¹ᵁ W))).hom
    (Stacks.Conormal.conormalClass t W (le_refl _) j hj)

omit [IsIso D.i.base] in
/-- The canonical map `f^*𝒞_{S/S'} ⟶ 𝒞_{X/X'}` sends the canonical section of `j` to the
conormal class of `f'^♯ j`. -/
theorem immersionConormalSheafMap_canonicalSection {X' : Scheme.{u}} (i : X ⟶ X')
    [IsClosedImmersion i] (f' : X' ⟶ S') (comm : i ≫ f' = f ≫ t)
    (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0) :
    (Scheme.Modules.Hom.app (show pullbackConormalModule f t ⟶ conormalModules i from
        Stacks.Immersion.immersionConormalSheafMap i t f f' (Stacks.Immersion.toShHom_square comm))
        ((Opens.map (f.base ≫ t.base)).obj W)).hom (canonicalSection W j hj) =
      Stacks.Conormal.conormalClass i (f' ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, comm]; rfl)
        ((f'.app W).hom j) (Stacks.Conormal.app_app_eq_zero_of_square comm W j hj) := by
  have h := Stacks.Conormal.conormalClass_immersionConormalSheafMap i t f f' comm W
    ((Opens.map (f.base ≫ t.base)).obj W)
    (by rw [← Scheme.Hom.comp_preimage, comm]; rfl) le_rfl j hj
  rw [Adjunction.homEquiv_unit] at h
  refine Eq.trans ?_ h
  exact (modules_map_self (Stacks.Conormal.conormalSheaf i) _ _).symm

omit [IsIso D.i.base] in
/-- `conormalIso` sends the canonical section of `j` to the conormal class of `f'^♯ j`. -/
theorem conormalIso_canonicalSection (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0) :
    (D.conormalIso.hom.app ((Opens.map (f.base ≫ t.base)).obj W)).hom
        (canonicalSection W j hj) =
      Stacks.Conormal.conormalClass D.i (D.f' ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, D.isPullback.w]; rfl)
        ((D.f'.app W).hom j) (Stacks.Conormal.app_app_eq_zero_of_square D.isPullback.w W j hj) := by
  have h := Stacks.Conormal.conormalClass_immersionConormalSheafMap D.i t f D.f' D.isPullback.w W
    ((Opens.map (f.base ≫ t.base)).obj W)
    (by rw [← Scheme.Hom.comp_preimage, D.isPullback.w]; rfl) le_rfl j hj
  rw [Adjunction.homEquiv_unit] at h
  refine Eq.trans ?_ h
  exact (modules_map_self (Stacks.Conormal.conormalSheaf D.i) _ _).symm

/-- `kernelIncl` sends the canonical section of `j` to the image of `j` under
`transportedBase`. -/
theorem kernelIncl_canonicalSection (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0) :
    ((kernelIncl hst D).val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
        (canonicalSection W j hj) =
      ((transportedBase D.i D.isPullback.w).hom.app (op W)).hom j := by
  change kernelSection D.i (D.ker_sq hst) D.conormalIso _ _ = _
  rw [transportedBase_app]
  refine (kernelSection_eq_of_conormalClass D.i (D.ker_sq hst) D.conormalIso _ _ (D.f' ⁻¹ᵁ W)
    (toAmbient_comm D.i D.isPullback.w W).le _ _ (conormalIso_canonicalSection D W j hj)).trans ?_
  exact congrArg (fun g => (D.X'.presheaf.map g).hom ((D.f'.app W).hom j))
    (Subsingleton.elim _ _)

omit [IsClosedImmersion t] in
/-- The map from the thickened base ring sends the image of `j` under the unit to the image of
`j` under `transportedBase`. -/
theorem baseRingMap_pullbackUnitApp (W : S'.Opens) (j : Γ(S', W)) :
    ((baseRingMap D).hom.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
        ((pullbackUnitApp (f.base ≫ t.base) S'.sheaf W).hom j) =
      ((transportedBase D.i D.isPullback.w).hom.app (op W)).hom j := by
  have h : (sheafAdjunction (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom)).homEquiv _ _
      (baseRingMap D) = transportedBase D.i D.isPullback.w :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  exact congr($(h).hom.app (op W) j)

/-- The image of a section of `𝒪_{S'}` under the unit, as a section of the thickened base ring. -/
abbrev unitSection (W : S'.Opens) (j : Γ(S', W)) :
    (rebuilt f (thickenedBaseRing t f)).obj.obj (op ((Opens.map (f.base ≫ t.base)).obj W)) :=
  (pullbackUnitApp (f.base ≫ t.base) S'.sheaf W).hom j

omit [IsClosedImmersion t] in
/-- The base map sends `unitSection W j` to the image of `j` under `transportedBase`. -/
theorem baseMap_unitSection (W : S'.Opens) (j : Γ(S', W)) :
    ((baseMap D).hom.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom (unitSection W j) =
      ((transportedBase D.i D.isPullback.w).hom.app (op W)).hom j :=
  (congrArg ((baseRingMap D).hom.app _).hom (idIso_hom_app_apply f _ _ _)).trans
    (baseRingMap_pullbackUnitApp D W j)

omit [IsClosedImmersion t] [IsIso D.i.base] in
/-- The reduction of the thickened base kills `unitSection W j` when `j` vanishes on `S`. -/
theorem rebuiltReduction_unitSection (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0) :
    ((rebuiltReduction t f).hom.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
      (unitSection W j) = 0 := by
  refine (rebuiltReduction_app_apply t f _ _).trans ?_
  refine (baseStructureMap_pullbackUnitApp t.toLRSHom.toShHom f.toLRSHom.toShHom W j).trans ?_
  change ((pullbackUnitApp f.base S.sheaf (t ⁻¹ᵁ W)).hom ((t.app W).hom j)) = 0
  rw [hj]
  exact map_zero _

/-- The image of a section of the ideal of `S` in `S'` under the unit, as a section of the ideal of
the thickened base. -/
abbrev idealSection (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0) :
    (ideal t f hst).val.obj (op ((Opens.map (f.base ≫ t.base)).obj W)) :=
  (show (idealKernel t f).val.obj (op ((Opens.map (f.base ≫ t.base)).obj W)) from
    ⟨unitSection W j, rebuiltReduction_unitSection W j hj⟩)

/-- **The map `c` of a flat deformation on the canonical sections**: the class of `j` goes to the
pullback of the conormal class of `j`. -/
theorem idealMap_idealSection (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0) :
    ((idealMap hst D).val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
        (idealSection hst W j hj) = canonicalSection W j hj := by
  refine kernelIncl_injective hst D _ ?_
  refine (kernelIncl_idealMap hst D _ _).trans ?_
  exact (baseMap_unitSection D W j).trans (kernelIncl_canonicalSection hst D W j hj).symm

omit [IsIso D.i.base] in
/-- **Two morphisms out of the ideal of the thickened base agreeing on the canonical sections are
equal.** -/
theorem ideal_hom_ext {M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (rebuilt f (reducedBaseRing f)))}
    (c₁ c₂ : ideal t f hst ⟶ M)
    (h : ∀ (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0),
      (c₁.val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom (idealSection hst W j hj) =
        (c₂.val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom (idealSection hst W j hj)) :
    c₁ = c₂ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext
    (LinearMap.ext fun a => ?_))
  have key : ∀ x : U.unop, ∃ (V : Opens X) (_ : x.1 ∈ V) (hVU : V ≤ U.unop),
      M.val.map (homOfLE hVU).op ((c₁.val.app U).hom a) =
        M.val.map (homOfLE hVU).op ((c₂.val.app U).hom a) := by
    intro x
    let a' : (idealKernel t f).val.obj U := a
    have ha : (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap f.toLRSHom.toShHom
        t.toLRSHom.toShHom).hom.app U a'.1 = 0 :=
      (rebuiltReduction_app_apply t f U a'.1).symm.trans a'.2
    obtain ⟨W, hW, j, hj, V, hxV, hVU, hVW, hres⟩ :=
      exists_eq_pullbackUnitApp_of_baseStructureMap_eq_zero f.toLRSHom.toShHom
        (t.isEmbedding.isInducing) U.unop _ ha x.1 x.2
    refine ⟨V, hxV, hVU, ?_⟩
    have hsec : (ideal t f hst).val.map (homOfLE hVU).op a =
        (ideal t f hst).val.map (homOfLE hVW).op (idealSection hst W j hj) :=
      Subtype.ext hres
    have e₁ := ConcreteCategory.congr_hom (c₁.val.naturality (homOfLE hVU).op) a
    have e₂ := ConcreteCategory.congr_hom (c₂.val.naturality (homOfLE hVU).op) a
    have f₁ := ConcreteCategory.congr_hom (c₁.val.naturality (homOfLE hVW).op)
      (idealSection hst W j hj)
    have f₂ := ConcreteCategory.congr_hom (c₂.val.naturality (homOfLE hVW).op)
      (idealSection hst W j hj)
    change (c₁.val.app (op V)).hom ((ideal t f hst).val.map (homOfLE hVU).op a) =
      M.val.map (homOfLE hVU).op ((c₁.val.app U).hom a) at e₁
    change (c₂.val.app (op V)).hom ((ideal t f hst).val.map (homOfLE hVU).op a) =
      M.val.map (homOfLE hVU).op ((c₂.val.app U).hom a) at e₂
    change (c₁.val.app (op V)).hom ((ideal t f hst).val.map (homOfLE hVW).op _) =
      M.val.map (homOfLE hVW).op ((c₁.val.app _).hom _) at f₁
    change (c₂.val.app (op V)).hom ((ideal t f hst).val.map (homOfLE hVW).op _) =
      M.val.map (homOfLE hVW).op ((c₂.val.app _).hom _) at f₂
    rw [← e₁, ← e₂, hsec, f₁, f₂]
    exact congrArg (M.val.map (homOfLE hVW).op) (h W j hj)
  choose V hxV hVU hV using key
  exact TopCat.Sheaf.eq_of_locally_eq' (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    V U.unop (fun x => homOfLE (hVU x))
    (fun x hx => (Opens.mem_iSup).mpr ⟨⟨x, hx⟩, hxV _⟩) _ _ hV

/-- **The map `c` does not depend on the flat deformation.** -/
theorem idealMap_eq (D' : FlatDeformation t f) [IsIso D'.i.base] :
    idealMap hst D = idealMap hst D' :=
  ideal_hom_ext hst _ _ fun W j hj =>
    (idealMap_idealSection hst D W j hj).trans (idealMap_idealSection hst D' W j hj).symm

omit [IsIso D.i.base] in
include hst in
/-- **Morphisms out of `f^*𝒞_{S/S'}` are determined by their values on the canonical
sections.** -/
theorem conormalModule_hom_ext {N : X.Modules} (α β : pullbackConormalModule f t ⟶ N)
    (h : ∀ (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0),
      (α.app _).hom (canonicalSection W j hj) = (β.app _).hom (canonicalSection W j hj)) :
    α = β := by
  have := isIso_base_of_firstOrder t hst
  refine ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    f.toLRSHom.toShHom).homEquiv _ _).injective ?_
  have key : ∀ V : S'.Opens, Scheme.Modules.Hom.app
      (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      f.toLRSHom.toShHom).homEquiv _ _) α) (t ⁻¹ᵁ V) =
      Scheme.Modules.Hom.app (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      f.toLRSHom.toShHom).homEquiv _ _) β) (t ⁻¹ᵁ V) := by
    intro V
    ext z
    obtain ⟨r, hr, rfl⟩ := exists_conormalClass_eq t hst V z
    refine (congrArg (fun φ => (Scheme.Modules.Hom.app φ (t ⁻¹ᵁ V)).hom _)
      (Adjunction.homEquiv_unit _ _ _ α)).trans ?_
    refine Eq.trans ?_ (congrArg (fun φ => (Scheme.Modules.Hom.app φ (t ⁻¹ᵁ V)).hom _)
      (Adjunction.homEquiv_unit _ _ _ β)).symm
    exact h V r hr
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  rw [← preimage_toAmbient t U]
  exact key _

omit [IsClosedImmersion t] [IsIso D.i.base] in
/-- **Ideal identifications induce morphisms of modules**: given two extensions of `𝒪_X` whose
ideals are identified with `M₁` and `M₂`, a morphism of extensions over `𝒪_X` induces an
`𝒪_X`-linear morphism `M₁ ⟶ M₂` compatible with the two identifications. -/
theorem exists_hom_of_kernel {A₁ A₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (red₁ : A₁ ⟶ X.sheaf) (red₂ : A₂ ⟶ X.sheaf)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        red₁).hom]
    {M₁ M₂ : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)}
    (ι₁ : (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map red₁)).obj M₁ ⟶
      SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj A₁))
    (ι₂ : (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map red₂)).obj M₂ ⟶
      SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj A₂))
    (hinj : ∀ U, Function.Injective (ι₂.val.app U))
    (hsurj : ∀ U (a : A₂.obj.obj U), red₂.hom.app U a = 0 → ∃ m, ι₂.val.app U m = a)
    (hred₁ : ∀ U m, red₁.hom.app U (ι₁.val.app U m) = 0)
    (θ : A₁ ⟶ A₂) (hθ : θ ≫ red₂ = red₁) :
    ∃ δ : M₁ ⟶ M₂, ∀ (U : X.Opensᵒᵖ) (m : M₁.val.obj U),
      (ι₂.val.app U).hom ((δ.val.app U).hom m) = θ.hom.app U ((ι₁.val.app U).hom m) := by
  have hθ' : (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        θ ≫ (sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).map red₂ =
      (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        red₁ ≫ 𝟙 _ :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg _ hθ).trans (Category.comp_id _).symm)
  obtain ⟨l, hl, -⟩ := Stacks.SheafOfModules.existsUnique_factorThrough
    ((SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map θ)).map ι₂) hinj
    (ι₁ ≫ SheafOfModules.unitToRestrictScalarsObjUnit ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map θ))
    (fun U z => hsurj U _ ((congrArg (fun φ => φ.hom.app U ((ι₁.val.app U).hom z)) hθ).trans
      (hred₁ U z)))
  obtain ⟨δ, hδ⟩ := (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
      red₁)).map_surjective (l ≫ (restrictScalarsCompIso _ _ _ _ hθ' M₂).hom ≫
        (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).map red₁)).map (restrictScalarsIdIso _).hom)
  exact ⟨δ, fun U m => (congrArg (ι₂.val.app U).hom
    (congrArg (fun φ => (φ.val.app U).hom m) hδ)).trans
      (congrArg (fun φ => (φ.val.app U).hom m) hl)⟩

omit [IsIso D.i.base] in
include hst in
/-- **A morphism of extensions of `𝒪_X` compatible with two identifications of their ideals with
`f^*𝒞_{S/S'}` on the canonical sections is compatible with them everywhere.** -/
theorem kernel_comm_of_canonical {A₁ A₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (red₁ : A₁ ⟶ X.sheaf) (red₂ : A₂ ⟶ X.sheaf)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        red₁).hom]
    (ι₁ : (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map red₁)).obj (conormalModule t f) ⟶
      SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj A₁))
    (ι₂ : (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map red₂)).obj (conormalModule t f) ⟶
      SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj A₂))
    (hinj : ∀ U, Function.Injective (ι₂.val.app U))
    (hsurj : ∀ U (a : A₂.obj.obj U), red₂.hom.app U a = 0 → ∃ m, ι₂.val.app U m = a)
    (hred₁ : ∀ U m, red₁.hom.app U (ι₁.val.app U m) = 0)
    (θ : A₁ ⟶ A₂) (hθ : θ ≫ red₂ = red₁)
    (h : ∀ (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0),
      θ.hom.app _ ((ι₁.val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
        (canonicalSection W j hj)) =
      (ι₂.val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom (canonicalSection W j hj))
    (U : X.Opensᵒᵖ) (m : (conormalModule t f).val.obj U) :
    θ.hom.app U ((ι₁.val.app U).hom m) = (ι₂.val.app U).hom m := by
  obtain ⟨δ, hδ⟩ := exists_hom_of_kernel red₁ red₂ ι₁ ι₂ hinj hsurj hred₁ θ hθ
  have hδ1 : δ = 𝟙 _ := by
    refine conormalModule_hom_ext hst (show pullbackConormalModule f t ⟶
      pullbackConormalModule f t from δ) (𝟙 _) fun W j hj => hinj _ ?_
    exact (hδ _ _).trans (h W j hj)
  rw [← hδ U m, hδ1]
  rfl

end Solution







end FlatDeformation

end Stacks.Thickenings

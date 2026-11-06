module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModules
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheafPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.GModuleBimultiplicative

/-!
# Pairings of finite locally constant abelian sheaves from pairings of finite `G`-modules

Let `e` be an equivalence between the finite locally constant sheaves of sets on a site and the
finite continuous `G`-sets, and `E` the equivalence of Tag 0DV5 (2) it induces between finite
locally constant abelian sheaves and finite discrete `G`-modules
(`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence`). A
`G`-equivariant map `P : M × N → L` of finite discrete `G`-modules, additive in each variable,
gives on sections over every `U` a biadditive pairing
`E⁻¹(M)(U) × E⁻¹(N)(U) → E⁻¹(L)(U)` which commutes with restriction. Applied to the invariant
pairing `⟨ρ(g) x, ρ^∨(g) y⟩ = ⟨x, y⟩` this is the pairing of coefficients
`ℱ_ρ ⊗ ℱ_{ρ^∨} → ℤ/ℓ^kℤ` of the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The argument is the transport of the source: `P` is a bimultiplicative morphism of commutative
group objects of continuous `G`-sets
(`CategoryTheory.isBimultiplicative_preimage_internalGModule`), which the product-preserving
functors `e⁻¹` and the inclusion carry to a bimultiplicative morphism of commutative group objects
of sheaves of sets (`CategoryTheory.IsBimultiplicative.map`), read on sections by
`CategoryTheory.Sites.AbelianSheaf.sectionsPairing`.

## Main definitions

* `Stacks.ConstantSheaf.finiteLocallyConstantPairing`: the pairing of sections.

## Main results

* `Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj_obj`:
  the abelian sheaf `E⁻¹(A)` is the one read off from `e⁻¹` of the group object of `A`.
* `Stacks.ConstantSheaf.finiteLocallyConstantPairing_naturality`: the pairing commutes with
  restriction.

## Implementation notes

Sheaves of sets carry the cartesian structure `.ofHasFiniteProducts` of
`CategoryTheory.Sites.AbelianSheaf.equivalence` throughout, activated through the same local
instances as in the construction of the equivalence; mixing it with Mathlib's
`CartesianMonoidalCategory.fullSubcategory` structure does not typecheck. The identification of
`E⁻¹(A)` is proved by unfolding the five equivalences `E` is composed of with `simp only` and then
`rfl`; a bare `rfl` times out.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe v u u' w

/- The cartesian structures of Tag 0DV5 (2), exactly as in
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence`. -/
attribute [local instance] cartesianMonoidalSheafType braidedSheafType
  braidedContinuousGSetIsFinite braidedι_continuousGSetIsFinite
  cartesianMonoidalContinuousGSet braidedContinuousGSet

namespace Stacks.ConstantSheaf

open scoped Obj

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (G : Type u') [Group G] [TopologicalSpace G]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
  (e : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory ≌
      (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory)

attribute [local instance] braidedFiniteLocallyConstantSetSheaf
  braidedι_finiteLocallyConstantSetSheaf

/-- The commutative group object of continuous `G`-sets attached to a finite discrete `G`-module
by `CategoryTheory.commGrpContinuousGSetEquivalence`, whose underlying `G`-set is finite. -/
abbrev finiteGModuleCommGrpProp (A : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory) :
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).commGrpProp.FullSubcategory :=
  ⟨(commGrpContinuousGSetEquivalence.{u', w} (G := G)).inverse.obj A.obj,
    (ObjectProperty.prop_of_iso (ContinuousGAddCommGrp.isFinite.{u', w} G)
      ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).counitIso.app A.obj).symm A.property :)⟩

/-- The commutative group object of finite continuous `G`-sets attached to a finite discrete
`G`-module by Tag 0DV5 (2). -/
def finiteGModuleCommGrp (A : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory) :
    CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory :=
  ObjectProperty.pullCommGrpSub _ (finiteGModuleCommGrpProp G A)

/-- **The finite locally constant abelian sheaf attached to `A` by Tag 0DV5 (2)** is the abelian
sheaf read off from the commutative group object to which `e⁻¹` carries the group object of `A`. -/
theorem finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj_obj
    (A : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory) :
    letI : e.inverse.Braided := .ofChosenFiniteProducts _
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj A).obj =
      (Sites.AbelianSheaf.externalSheaf J).obj
        ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.obj
          (e.inverse.mapCommGrp.obj (finiteGModuleCommGrp G A))) := by
  simp only [finiteLocallyConstantAbelianEquivalenceOfSetEquivalence, Equivalence.trans_inverse,
    Functor.comp_obj, Equivalence.congrFullSubcategory_inverse, ObjectProperty.lift_obj_obj,
    Equivalence.symm_inverse, Equivalence.mapCommGrp_inverse, ObjectProperty.commGrpEquivalence,
    Sites.AbelianSheaf.equivalence, ObjectProperty.ι_obj]
  rfl

section GSet

variable {G}

attribute [local instance] braidedGsetPresheaf

/-- The morphism of presheaves on the one-object category of `G` given by an equivariant map
`M × N → L` of the underlying sets of three discrete `G`-modules. -/
def gsetPresheafPairing (M N L : ContinuousGAddCommGrp.{u', w} G)
    (P : M.obj.obj.V →+ N.obj.obj.V →+ L.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.V) (b : N.obj.obj.V),
      P ((M.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.ρ g).asHom.hom b) = (L.obj.obj.ρ g).asHom.hom (P a b)) :
    gsetPresheaf.obj (internalGModule M).X ⊗ gsetPresheaf.obj (internalGModule N).X ⟶
      gsetPresheaf.obj (internalGModule L).X where
  app _ := TypeCat.ofHom fun p => P p.1 p.2
  naturality _ _ g := by
    ext p
    exact hP g p.1 p.2

open scoped Obj in
/-- The internal pairing of continuous `G`-sets given by an equivariant biadditive map. -/
theorem isBimultiplicative_gsetPresheafPairing (M N L : ContinuousGAddCommGrp.{u', w} G)
    (P : M.obj.obj.V →+ N.obj.obj.V →+ L.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.V) (b : N.obj.obj.V),
      P ((M.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.ρ g).asHom.hom b) = (L.obj.obj.ρ g).asHom.hom (P a b)) :
    IsBimultiplicative (gsetPresheafFullyFaithful.preimage
      (Functor.OplaxMonoidal.δ gsetPresheaf (internalGModule M).X (internalGModule N).X ≫
        gsetPresheafPairing M N L P hP)) :=
  isBimultiplicative_preimage_internalGModule M N L _ P fun _ _ => rfl

/-- The commutative group object of continuous `G`-sets attached to a discrete `G`-module by
`CategoryTheory.commGrpContinuousGSetEquivalence` is isomorphic to its internalization. -/
def commGrpContinuousGSetEquivalenceInverseIso (M : ContinuousGAddCommGrp.{u', w} G) :
    (commGrpContinuousGSetEquivalence.{u', w} (G := G)).inverse.obj M ≅ internalGModule M :=
  externalGModuleFullyFaithful.preimageIso
    ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).counitIso.app M ≪≫
      (externalInternalGModuleIso M).symm)

end GSet

section Finite

variable {G}

attribute [local instance] braidedGsetPresheaf

/-- The internal pairing of continuous `G`-sets given by an equivariant biadditive map, between the
commutative group objects attached to the modules by
`CategoryTheory.commGrpContinuousGSetEquivalence`. -/
def commGrpPairing (M N L : ContinuousGAddCommGrp.{u', w} G)
    (P : M.obj.obj.V →+ N.obj.obj.V →+ L.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.V) (b : N.obj.obj.V),
      P ((M.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.ρ g).asHom.hom b) = (L.obj.obj.ρ g).asHom.hom (P a b)) :
    ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).inverse.obj M).X ⊗
        ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).inverse.obj N).X ⟶
      ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).inverse.obj L).X :=
  ((commGrpContinuousGSetEquivalenceInverseIso M).hom.hom.hom.hom ⊗ₘ
      (commGrpContinuousGSetEquivalenceInverseIso N).hom.hom.hom.hom) ≫
    gsetPresheafFullyFaithful.preimage
      (Functor.OplaxMonoidal.δ gsetPresheaf (internalGModule M).X (internalGModule N).X ≫
        gsetPresheafPairing M N L P hP) ≫
      (commGrpContinuousGSetEquivalenceInverseIso L).inv.hom.hom.hom

/-- `Stacks.ConstantSheaf.commGrpPairing` is bimultiplicative. -/
theorem isBimultiplicative_commGrpPairing (M N L : ContinuousGAddCommGrp.{u', w} G)
    (P : M.obj.obj.V →+ N.obj.obj.V →+ L.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.V) (b : N.obj.obj.V),
      P ((M.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.ρ g).asHom.hom b) = (L.obj.obj.ρ g).asHom.hom (P a b)) :
    IsBimultiplicative (commGrpPairing M N L P hP) :=
  (isBimultiplicative_gsetPresheafPairing M N L P hP).comp _ _ _

/-- The internal pairing of finite continuous `G`-sets given by an equivariant biadditive map of
finite discrete `G`-modules, between their group objects `finiteGModuleCommGrp`. -/
def finiteGModulePairing (M N L : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.obj.ρ g).asHom.hom b) =
        (L.obj.obj.obj.ρ g).asHom.hom (P a b)) :
    (finiteGModuleCommGrp G M).X ⊗ (finiteGModuleCommGrp G N).X ⟶ (finiteGModuleCommGrp G L).X :=
  (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).fullyFaithfulι.preimage
    (Functor.OplaxMonoidal.δ (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι _ _ ≫
      ((ObjectProperty.commGrpιObjIso _ (finiteGModuleCommGrpProp G M)).hom.hom.hom.hom.hom ⊗ₘ
        (ObjectProperty.commGrpιObjIso _ (finiteGModuleCommGrpProp G N)).hom.hom.hom.hom.hom) ≫
      commGrpPairing M.obj N.obj L.obj P hP ≫
        (ObjectProperty.commGrpιObjIso _ (finiteGModuleCommGrpProp G L)).inv.hom.hom.hom.hom)

/-- `Stacks.ConstantSheaf.finiteGModulePairing` is bimultiplicative. -/
theorem isBimultiplicative_finiteGModulePairing
    (M N L : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.obj.ρ g).asHom.hom b) =
        (L.obj.obj.obj.ρ g).asHom.hom (P a b)) :
    IsBimultiplicative (finiteGModulePairing M N L P hP) :=
  IsBimultiplicative.preimage _ ((isBimultiplicative_commGrpPairing _ _ _ P hP).comp _ _ _
    (ha := (ObjectProperty.commGrpιObjIso _
      (finiteGModuleCommGrpProp G M)).hom.hom.hom.hom.isMonHom_hom)
    (hb := (ObjectProperty.commGrpιObjIso _
      (finiteGModuleCommGrpProp G N)).hom.hom.hom.hom.isMonHom_hom)
    (hc := (ObjectProperty.commGrpιObjIso _
      (finiteGModuleCommGrpProp G L)).inv.hom.hom.hom.isMonHom_hom))

end Finite

section Sheaf

variable {G}

/-- The internal pairing of sheaves of sets attached by `e⁻¹` to an equivariant biadditive map of
finite discrete `G`-modules. -/
def finiteLocallyConstantInternalPairing
    (M N L : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.obj.ρ g).asHom.hom b) =
        (L.obj.obj.obj.ρ g).asHom.hom (P a b)) :
    letI : e.inverse.Braided := .ofChosenFiniteProducts _
    ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.obj
          (e.inverse.mapCommGrp.obj (finiteGModuleCommGrp G M))).X ⊗
        ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.obj
          (e.inverse.mapCommGrp.obj (finiteGModuleCommGrp G N))).X ⟶
      ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.obj
          (e.inverse.mapCommGrp.obj (finiteGModuleCommGrp G L))).X :=
  letI : e.inverse.Braided := .ofChosenFiniteProducts _
  Functor.LaxMonoidal.μ (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι _ _ ≫
    (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.map
      (Functor.LaxMonoidal.μ e.inverse _ _ ≫ e.inverse.map (finiteGModulePairing M N L P hP))

omit [∀ (U : C), HasWeakSheafify (J.over U) AddCommGrpCat] in
/-- `Stacks.ConstantSheaf.finiteLocallyConstantInternalPairing` is bimultiplicative. -/
theorem isBimultiplicative_finiteLocallyConstantInternalPairing
    (M N L : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.obj.ρ g).asHom.hom b) =
        (L.obj.obj.obj.ρ g).asHom.hom (P a b)) :
    IsBimultiplicative (finiteLocallyConstantInternalPairing J e M N L P hP) :=
  let : e.inverse.Braided := .ofChosenFiniteProducts _
  ((isBimultiplicative_finiteGModulePairing M N L P hP).map e.inverse).map _

/-- The identification of
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj_obj`, as
an isomorphism. -/
abbrev finiteLocallyConstantInverseObjIso
    (A : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory) :
    letI : e.inverse.Braided := .ofChosenFiniteProducts _
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj A).obj ≅
      (Sites.AbelianSheaf.externalSheaf J).obj
        ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.obj
          (e.inverse.mapCommGrp.obj (finiteGModuleCommGrp G A))) :=
  eqToIso (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj_obj J G e A)

/-- **The pairing of sections of finite locally constant abelian sheaves** attached by the
equivalence of Tag 0DV5 (2) to an equivariant biadditive map `M × N → L` of finite discrete
`G`-modules: on sections over every `U` it is biadditive, and it commutes with restriction
(`Stacks.ConstantSheaf.finiteLocallyConstantPairing_naturality`). -/
def finiteLocallyConstantPairing
    (M N L : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.obj.ρ g).asHom.hom b) =
        (L.obj.obj.obj.ρ g).asHom.hom (P a b)) (U : Cᵒᵖ) :
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj M).obj.obj.obj U →+
      ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj N).obj.obj.obj
          U →+
        ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj L).obj.obj.obj
          U :=
  ((((Sites.AbelianSheaf.sectionsPairing
      (isBimultiplicative_finiteLocallyConstantInternalPairing J e M N L P hP) U).comp
      ((finiteLocallyConstantInverseObjIso J e M).hom.hom.app U).hom).compl₂
      ((finiteLocallyConstantInverseObjIso J e N).hom.hom.app U).hom).compr₂
    ((finiteLocallyConstantInverseObjIso J e L).inv.hom.app U).hom)

/-- **The pairing of sections commutes with restriction.** -/
theorem finiteLocallyConstantPairing_naturality
    (M N L : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.obj.ρ g).asHom.hom b) =
        (L.obj.obj.obj.ρ g).asHom.hom (P a b)) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj M).obj.obj.obj
      U)
    (y : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj N).obj.obj.obj
      U) :
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj L).obj.obj.map f
        (finiteLocallyConstantPairing J e M N L P hP U x y) =
      finiteLocallyConstantPairing J e M N L P hP V
        (((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj M).obj.obj.map
          f x)
        (((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj N).obj.obj.map
          f y) := by
  simp only [finiteLocallyConstantPairing, AddMonoidHom.compr₂_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply]
  rw [← ConcreteCategory.comp_apply,
    ← ((finiteLocallyConstantInverseObjIso J e L).inv.hom.naturality f),
    ConcreteCategory.comp_apply, Sites.AbelianSheaf.sectionsPairing_naturality]
  congr 2

end Sheaf

end Stacks.ConstantSheaf

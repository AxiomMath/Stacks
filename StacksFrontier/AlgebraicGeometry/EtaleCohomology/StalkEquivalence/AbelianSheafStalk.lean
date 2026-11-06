module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
public import Mathlib.Topology.Constructions.SumProd
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.SheafStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian étale sheaves on the spectrum of a field as continuous Galois modules

Let `K` be a field, let `sbar` be a geometric point of `Spec K` and let `G` be the absolute
Galois group at `sbar`.  Taking the stalk at `sbar` is an equivalence from the category of
abelian sheaves on the small étale site of `Spec K` to the category of discrete `G`-modules,
that is, abelian groups carrying a continuous action of `G`.

The equivalence is obtained from the corresponding equivalence for sheaves of sets
(`AlgebraicGeometry.etaleSheafStalkEquivalence`) by transporting internal commutative group
objects: an abelian sheaf is a sheaf of sets with a commutative group law, a discrete
`G`-module is a continuous `G`-set with a commutative group law, and an equivalence of
categories with finite products carries the one notion to the other.

## Main definitions

* `CategoryTheory.ContinuousGAddCommGrp` — abelian groups with a continuous action of `G`,
  that is, discrete `G`-modules, together with `CategoryTheory.ContinuousGAddCommGrp.forget`
  the underlying abelian group and `CategoryTheory.ContinuousGAddCommGrp.forgetAction` the
  underlying continuous `G`-set.
* `CategoryTheory.commGrpContinuousGSetEquivalence` — commutative group objects in continuous
  `G`-sets are discrete `G`-modules.
* `CategoryTheory.natIsoOfForgetAddCommGrpCat` — a natural isomorphism of abelian-group-valued
  functors recovered from one of their underlying set-valued functors.
* `AlgebraicGeometry.abelianEtaleStalkFunctor` — the abelian-group-valued stalk at a geometric
  point, with `AlgebraicGeometry.abelianEtaleStalkGerm` the germ of a section.
* `AlgebraicGeometry.abelianEtaleStalkEquivalence` — the equivalence itself.
* `AlgebraicGeometry.abelianEtaleSheafStalkEquivalence` — the equivalence packaged with its
  identification with the stalk functor and the description of the Galois action on germs.

## Main results

* `AlgebraicGeometry.ContinuousGSet.hasFiniteProducts` — continuous `G`-sets have finite products,
  computed on underlying sets.
* `AlgebraicGeometry.abelianEtaleStalkForgetIso` — the underlying set of the abelian stalk is
  the stalk of the underlying sheaf of sets.

## Implementation notes

The two comparisons between internal and external commutative groups are
`CategoryTheory.Sites.AbelianSheaf.equivalence` on the sheaf side and
`CategoryTheory.commGrpContinuousGSetEquivalence` on the Galois side; both rest on the
sectionwise comparison `CategoryTheory.Sites.AbelianSheaf.presheafCommGrp`, applied to the site
in the first case and to the one-object category of `G` in the second.  Forgetting the group
law commutes with both on the nose, which is recorded by
`AlgebraicGeometry.abelianEquivalenceOfGSetEquivalence_comp_forgetAction`, so the comparison of
the abelian equivalence with the stalk functor reduces to the set-valued comparison together
with the fact that the forgetful functor of abelian groups preserves the filtered colimit
defining the stalk.  The transport is stated for an arbitrary equivalence of a topos of sheaves
of sets with continuous `G`-sets.

## References

* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

/-- Sets are given the discrete topology when forming continuous actions. -/
local instance discreteForget₂Type : HasForget₂ (Type w) TopCat.{w} where
  forget₂ := TopCat.discrete
  forget_comp := rfl

/-- Abelian groups are given the discrete topology when forming continuous actions. -/
local instance discreteForget₂AddCommGrpCat : HasForget₂ AddCommGrpCat.{w} TopCat.{w} where
  forget₂ := CategoryTheory.forget AddCommGrpCat.{w} ⋙ TopCat.discrete
  forget_comp := rfl

/-- Sheaves of sets have finite products, hence a cartesian monoidal structure. -/
local instance cartesianMonoidalSheafType {C : Type*} [Category* C]
    (J : GrothendieckTopology C) : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts

/-- The braiding of the cartesian monoidal structure on sheaves of sets. -/
local instance braidedSheafType {C : Type*} [Category* C] (J : GrothendieckTopology C) :
    BraidedCategory (Sheaf J (Type w)) := .ofCartesianMonoidalCategory

namespace AlgebraicGeometry

section Defs

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The inclusion of continuous `G`-sets into all actions of `G` on sets. -/
abbrev ContinuousGSet.toAction : ContinuousGSet.{u, w} G ⥤ Action (Type w) G :=
  (ObjectProperty.ι _ : DiscreteContAction (Type w) G ⥤ ContAction (Type w) G) ⋙
    (ObjectProperty.ι _ : ContAction (Type w) G ⥤ Action (Type w) G)

end Defs

end AlgebraicGeometry

namespace CategoryTheory

section Defs

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- Continuous actions of `G` on abelian groups in an independent universe, regarded as actions
on discrete topological spaces: the category of discrete `G`-modules. -/
abbrev ContinuousGAddCommGrp := DiscreteContAction AddCommGrpCat.{w} G

/-- The inclusion of discrete `G`-modules into all actions of `G` on abelian groups. -/
abbrev ContinuousGAddCommGrp.toAction :
    ContinuousGAddCommGrp.{u, w} G ⥤ Action AddCommGrpCat.{w} G :=
  (ObjectProperty.ι _ : DiscreteContAction AddCommGrpCat.{w} G ⥤
      ContAction AddCommGrpCat.{w} G) ⋙
    (ObjectProperty.ι _ : ContAction AddCommGrpCat.{w} G ⥤ Action AddCommGrpCat.{w} G)

/-- The underlying abelian group of a discrete `G`-module. -/
abbrev ContinuousGAddCommGrp.forget :
    ContinuousGAddCommGrp.{u, w} G ⥤ AddCommGrpCat.{w} :=
  ContinuousGAddCommGrp.toAction G ⋙ Action.forget AddCommGrpCat.{w} G

/-- The underlying continuous `G`-set of a discrete `G`-module. -/
def ContinuousGAddCommGrp.forgetAction :
    ContinuousGAddCommGrp.{u, w} G ⥤ AlgebraicGeometry.ContinuousGSet.{u, w} G where
  obj M := ⟨⟨((CategoryTheory.forget AddCommGrpCat.{w}).mapAction G).obj M.obj.obj,
    M.obj.property⟩, ⟨rfl⟩⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    (((CategoryTheory.forget AddCommGrpCat.{w}).mapAction G).map f.hom.hom))

/-- Forgetting the action of a discrete `G`-module and then its abelian group structure is
forgetting its abelian group structure and then the action. -/
theorem ContinuousGAddCommGrp.forgetAction_comp_forget :
    ContinuousGAddCommGrp.forgetAction.{u, w} G ⋙ AlgebraicGeometry.ContinuousGSet.forget G =
      ContinuousGAddCommGrp.forget.{u, w} G ⋙ CategoryTheory.forget AddCommGrpCat.{w} := rfl

end Defs

end CategoryTheory

namespace AlgebraicGeometry

section Products

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The product of a finite family of continuous `G`-sets, acting coordinatewise. -/
def ContinuousGSet.piObj {I : Type} [Finite I] (X : I → ContinuousGSet.{u, w} G) :
    ContinuousGSet.{u, w} G := by
  let A : Action (Type w) G :=
    { V := ∀ i, (X i).obj.obj.V
      ρ :=
        { toFun := fun g ↦ .of (↾fun x i ↦ (ConcreteCategory.hom ((X i).obj.obj.ρ g).asHom) (x i))
          map_one' := End.ext <| ConcreteCategory.hom_ext _ _ fun x ↦ funext fun i ↦
            ConcreteCategory.congr_hom (congrArg End.asHom (X i).obj.obj.ρ.map_one) (x i)
          map_mul' g h := End.ext <| ConcreteCategory.hom_ext _ _ fun x ↦ funext fun i ↦
            ConcreteCategory.congr_hom (congrArg End.asHom ((X i).obj.obj.ρ.map_mul g h))
              (x i) } }
  refine ⟨⟨A, ?_⟩, ⟨rfl⟩⟩
  have : DiscreteTopology ((forget₂ (Action (Type w) G) TopCat).obj A) := ⟨rfl⟩
  apply (Action.isContinuous_def A).2
  apply continuous_prod_of_discrete_right.mpr
  intro x
  let (i : I) : TopologicalSpace (X i).obj.obj.V := ⊥
  have (i : I) : DiscreteTopology (X i).obj.obj.V := ⟨rfl⟩
  have ht : (Pi.topologicalSpace : TopologicalSpace (∀ i, (X i).obj.obj.V)) = ⊥ :=
    DiscreteTopology.eq_bot
  have h : @Continuous G (∀ i, (X i).obj.obj.V) _ Pi.topologicalSpace
      (fun g i ↦ (ConcreteCategory.hom ((X i).obj.obj.ρ g).asHom) (x i)) :=
    continuous_pi fun i ↦ (X i).obj.property.continuous_smul.comp
      (continuous_id.prodMk continuous_const)
  rwa [ht] at h

/-- The projections out of the coordinatewise product of continuous `G`-sets. -/
def ContinuousGSet.piFan {I : Type} [Finite I] (X : I → ContinuousGSet.{u, w} G) : Fan X :=
  Fan.mk (ContinuousGSet.piObj X)
    fun i ↦ ObjectProperty.homMk (ObjectProperty.homMk
      { hom := ↾fun x ↦ x i, comm := fun _ ↦ rfl })

/-- The coordinatewise product of continuous `G`-sets is their product. -/
def ContinuousGSet.piFanIsLimit {I : Type} [Finite I] (X : I → ContinuousGSet.{u, w} G) :
    IsLimit (ContinuousGSet.piFan X) := by
  refine Fan.IsLimit.mk _ (fun S ↦ ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ↾fun x i ↦ (S.π.app ⟨i⟩).hom.hom.hom x
      comm := ?_ })) ?_ ?_
  · exact fun g ↦ ConcreteCategory.hom_ext _ _ fun x ↦ funext fun i ↦
      ConcreteCategory.congr_hom ((S.π.app ⟨i⟩).hom.hom.comm g) x
  · intro S i
    rfl
  · intro S m hm
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact ConcreteCategory.congr_hom
      (congrArg (fun f : S.pt ⟶ X i ↦ f.hom.hom.hom) (hm i)) x

/-- The product of continuous `G`-sets is computed on underlying sets. -/
def ContinuousGSet.forgetPiIsLimit {I : Type} [Finite I] (X : I → ContinuousGSet.{u, w} G) :
    IsLimit ((ContinuousGSet.forget G).mapCone (ContinuousGSet.piFan X)) := by
  refine IsLimit.mk (fun S ↦ ↾fun x i ↦ S.π.app ⟨i⟩ x) ?_ ?_
  · intro S i; rfl
  · exact fun S m hm ↦ ConcreteCategory.hom_ext _ _ fun x ↦ funext fun i ↦
      ConcreteCategory.congr_hom (hm ⟨i⟩) x

/-- Continuous `G`-sets have finite products. -/
instance ContinuousGSet.hasFiniteProducts :
    HasFiniteProducts (ContinuousGSet.{u, w} G) where
  out n :=
    { has_limit F := by
        let X := fun i : Fin n ↦ F.obj ⟨i⟩
        have : HasLimit (Discrete.functor X) := ⟨⟨_, ContinuousGSet.piFanIsLimit X⟩⟩
        exact hasLimit_of_iso
          (show Discrete.functor X ≅ F from Discrete.natIso fun _ ↦ Iso.refl _) }

/-- The underlying set functor of continuous `G`-sets preserves finite products. -/
instance ContinuousGSet.forget_preservesFiniteProducts :
    PreservesFiniteProducts (ContinuousGSet.forget.{u, w} G) where
  preserves n :=
    { preservesLimit {F} := by
        let X := fun i : Fin n ↦ F.obj ⟨i⟩
        have : PreservesLimit (Discrete.functor X) (ContinuousGSet.forget G) :=
          preservesLimit_of_preserves_limit_cone (ContinuousGSet.piFanIsLimit X)
            (ContinuousGSet.forgetPiIsLimit X)
        exact preservesLimit_of_iso_diagram _
          (show Discrete.functor X ≅ F from Discrete.natIso fun _ ↦ Iso.refl _) }

/-- The inclusion of continuous `G`-sets into all `G`-actions on sets preserves finite
products. -/
instance ContinuousGSet.toAction_preservesFiniteProducts :
    PreservesFiniteProducts (ContinuousGSet.toAction.{u, w} G) where
  preserves n := Action.preservesLimitsOfShape_of_preserves _ (by
    have : PreservesLimitsOfShape (Discrete (Fin n)) (ContinuousGSet.forget.{u, w} G) :=
      inferInstance
    exact preservesLimitsOfShape_of_natIso (Functor.associator _ _ _).symm)

end Products

end AlgebraicGeometry

/-- Continuous `G`-sets have finite products, hence a cartesian monoidal structure. -/
local instance cartesianMonoidalContinuousGSet (G : Type u) [Group G] [TopologicalSpace G] :
    CartesianMonoidalCategory (AlgebraicGeometry.ContinuousGSet.{u, w} G) :=
  .ofHasFiniteProducts

/-- The braiding of the cartesian monoidal structure on continuous `G`-sets. -/
local instance braidedContinuousGSet (G : Type u) [Group G] [TopologicalSpace G] :
    BraidedCategory (AlgebraicGeometry.ContinuousGSet.{u, w} G) :=
  .ofCartesianMonoidalCategory

namespace CategoryTheory

section Transport

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Abelian presheaves are the same thing as commutative group objects in presheaves of sets:
the operations of an abelian presheaf are read sectionwise and conversely. -/
def presheafAbelianEquivalence {C : Type*} [Category* C] :
    (C ⥤ AddCommGrpCat.{w}) ≌ CommGrp (C ⥤ Type w) where
  functor := Sites.AbelianSheaf.presheafCommGrp
  inverse := Sites.AbelianSheaf.abelianPresheaves
  unitIso := NatIso.ofComponents fun F ↦ NatIso.ofComponents fun X ↦
    AddEquiv.toAddCommGrpIso
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
  counitIso := NatIso.ofComponents fun R ↦ CommGrp.mkIso (Iso.refl R.X)
    (by ext X x; rfl) (by ext X x; rfl)

/-- The multiplication of a commutative group object pulled back along a fully faithful
cartesian functor is, after applying that functor again, the original multiplication. -/
theorem mul_mapCommGrp_pullCommGrp {C : Type*} [Category* C]
    [CartesianMonoidalCategory C] [BraidedCategory C] {D : Type*} [Category* D]
    [CartesianMonoidalCategory D] [BraidedCategory D] {F : C ⥤ D} [F.Braided]
    (hF : F.FullyFaithful) (X : C) [GrpObj (F.obj X)] [IsCommMonObj (F.obj X)] :
    MonObj.mul (X := (F.mapCommGrp.obj (Sites.AbelianSheaf.pullCommGrp hF X)).X) =
      MonObj.mul (X := F.obj X) := by
  let : GrpObj X := hF.grpObj X
  show Functor.LaxMonoidal.μ F X X ≫ F.map
      (hF.preimage (Functor.OplaxMonoidal.δ F X X ≫ MonObj.mul (X := F.obj X))) =
    MonObj.mul (X := F.obj X)
  rw [hF.map_preimage]
  simp

/-- A continuous `G`-set, regarded as a presheaf of sets on the one-object category of `G`. -/
abbrev gsetPresheaf : AlgebraicGeometry.ContinuousGSet.{u, w} G ⥤ (SingleObj G ⥤ Type w) :=
  AlgebraicGeometry.ContinuousGSet.toAction G ⋙
    (Action.functorCategoryEquivalence (Type w) G).functor

/-- A discrete `G`-module, regarded as an abelian presheaf on the one-object category
of `G`. -/
abbrev gmodulePresheaf :
    ContinuousGAddCommGrp.{u, w} G ⥤ (SingleObj G ⥤ AddCommGrpCat.{w}) :=
  ContinuousGAddCommGrp.toAction G ⋙
    (Action.functorCategoryEquivalence AddCommGrpCat.{w} G).functor

/-- Regarding a continuous `G`-set as a presheaf on the one-object category of `G` is fully
faithful. -/
def gsetPresheafFullyFaithful : (gsetPresheaf.{u, w} (G := G)).FullyFaithful :=
  ((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)).comp
    (Action.functorCategoryEquivalence (Type w) G).fullyFaithfulFunctor

/-- Regarding a discrete `G`-module as an abelian presheaf on the one-object category of `G` is
fully faithful. -/
def gmodulePresheafFullyFaithful : (gmodulePresheaf.{u, w} (G := G)).FullyFaithful :=
  ((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)).comp
    (Action.functorCategoryEquivalence AddCommGrpCat.{w} G).fullyFaithfulFunctor

/-- The braided monoidal structure of `gsetPresheaf`, from its preservation of finite
products. -/
local instance : (gsetPresheaf.{u, w} (G := G)).Braided := .ofChosenFiniteProducts _

/-- Read the internal commutative group operations of a continuous `G`-set sectionwise as a
discrete `G`-module. -/
def externalGModule :
    CommGrp (AlgebraicGeometry.ContinuousGSet.{u, w} G) ⥤ ContinuousGAddCommGrp.{u, w} G where
  obj R := ⟨⟨(Action.functorCategoryEquivalence AddCommGrpCat.{w} G).inverse.obj
      (Sites.AbelianSheaf.abelianPresheaves.obj (gsetPresheaf.mapCommGrp.obj R)),
    R.X.obj.property⟩, ⟨rfl⟩⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    ((Action.functorCategoryEquivalence AddCommGrpCat.{w} G).inverse.map
      (Sites.AbelianSheaf.abelianPresheaves.map (gsetPresheaf.mapCommGrp.map f))))

/-- Reading internal commutative group operations sectionwise and then regarding the result as
an abelian presheaf on the one-object category of `G` is reading the operations of the
associated presheaf of sets sectionwise. -/
theorem externalGModule_comp_gmodulePresheaf :
    externalGModule.{u, w} (G := G) ⋙ gmodulePresheaf (G := G) =
      gsetPresheaf.mapCommGrp ⋙ Sites.AbelianSheaf.abelianPresheaves := rfl

/-- Reading the operations of an internal commutative group in presheaves of sets sectionwise
is fully faithful. -/
def abelianPresheavesFullyFaithful (C : Type*) [Category* C] :
    (Sites.AbelianSheaf.abelianPresheaves :
      CommGrp (C ⥤ Type w) ⥤ (C ⥤ AddCommGrpCat.{w})).FullyFaithful := by
  have h : (presheafAbelianEquivalence.{w} (C := C)).inverse =
      (Sites.AbelianSheaf.abelianPresheaves :
        CommGrp (C ⥤ Type w) ⥤ (C ⥤ AddCommGrpCat.{w})) := rfl
  rw [← h]
  exact presheafAbelianEquivalence.fullyFaithfulInverse

/-- Reading internal commutative group operations sectionwise is fully faithful. -/
def externalGModuleFullyFaithful :
    (externalGModule.{u, w} (G := G)).FullyFaithful := by
  letI : (gmodulePresheaf.{u, w} (G := G)).Faithful :=
    gmodulePresheafFullyFaithful.faithful
  refine Functor.FullyFaithful.ofCompFaithful (G := gmodulePresheaf.{u, w} (G := G)) ?_
  rw [externalGModule_comp_gmodulePresheaf]
  exact gsetPresheafFullyFaithful.mapCommGrp.comp
    (abelianPresheavesFullyFaithful.{w} (SingleObj G))

/-- The group operations of a discrete `G`-module, internalized in continuous `G`-sets. -/
def internalGModule (M : ContinuousGAddCommGrp.{u, w} G) :
    CommGrp (AlgebraicGeometry.ContinuousGSet.{u, w} G) := by
  letI : GrpObj (gsetPresheaf.obj ((ContinuousGAddCommGrp.forgetAction G).obj M)) :=
    Sites.AbelianSheaf.presheafGrpObj (gmodulePresheaf.obj M)
  letI : IsCommMonObj (gsetPresheaf.obj ((ContinuousGAddCommGrp.forgetAction G).obj M)) :=
    (Sites.AbelianSheaf.presheafCommGrp.obj (gmodulePresheaf.obj M)).comm
  exact Sites.AbelianSheaf.pullCommGrp (gsetPresheafFullyFaithful.{u, w} (G := G))
    ((ContinuousGAddCommGrp.forgetAction G).obj M)

/-- Internalizing the operations of a discrete `G`-module and reading them back off recovers
the module. -/
def externalInternalGModuleIso (M : ContinuousGAddCommGrp.{u, w} G) :
    externalGModule.obj (internalGModule M) ≅ M := by
  refine ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Action.mkIso
    (AddEquiv.toAddCommGrpIso
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := ?_ }) fun _ ↦ ?_))
  · intro x y
    let : GrpObj (gsetPresheaf.obj ((ContinuousGAddCommGrp.forgetAction G).obj M)) :=
      Sites.AbelianSheaf.presheafGrpObj (gmodulePresheaf.obj M)
    let : IsCommMonObj (gsetPresheaf.obj ((ContinuousGAddCommGrp.forgetAction G).obj M)) :=
      (Sites.AbelianSheaf.presheafCommGrp.obj (gmodulePresheaf.obj M)).comm
    exact congrArg (fun m ↦ (ConcreteCategory.hom (m.app PUnit.unit)) (x, y))
      (mul_mapCommGrp_pullCommGrp (gsetPresheafFullyFaithful.{u, w} (G := G))
        ((ContinuousGAddCommGrp.forgetAction G).obj M))
  · rfl

/-- Reading internal commutative group operations sectionwise is an equivalence. -/
instance externalGModule_isEquivalence :
    (externalGModule.{u, w} (G := G)).IsEquivalence :=
  letI := (externalGModuleFullyFaithful.{u, w} (G := G)).full
  letI := (externalGModuleFullyFaithful.{u, w} (G := G)).faithful
  letI : (externalGModule.{u, w} (G := G)).EssSurj :=
    ⟨fun M ↦ ⟨internalGModule M, ⟨externalInternalGModuleIso M⟩⟩⟩
  {}

/-- **Discrete `G`-modules are the commutative group objects in continuous `G`-sets.** -/
def commGrpContinuousGSetEquivalence :
    CommGrp (AlgebraicGeometry.ContinuousGSet.{u, w} G) ≌ ContinuousGAddCommGrp.{u, w} G :=
  externalGModule.asEquivalence

/-- Forgetting the group law of a commutative group object in continuous `G`-sets is forgetting
the action of the corresponding discrete `G`-module. -/
theorem commGrpContinuousGSetEquivalence_comp_forgetAction :
    (commGrpContinuousGSetEquivalence.{u, w} (G := G)).functor ⋙
        ContinuousGAddCommGrp.forgetAction G =
      CommGrp.forget (AlgebraicGeometry.ContinuousGSet.{u, w} G) := rfl

end Transport

section AdditiveNatIso

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {F H : C ⥤ AddCommGrpCat.{w}} [H.Additive]

omit [Preadditive C] [HasBinaryBiproducts C] [H.Additive] in
/-- Naturality of an isomorphism of underlying set-valued functors, read on elements. -/
theorem natIsoForget_apply
    (α : F ⋙ CategoryTheory.forget AddCommGrpCat ≅ H ⋙ CategoryTheory.forget AddCommGrpCat)
    {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    α.hom.app Y ((F.map f).hom x) = (H.map f).hom (α.hom.app X x) :=
  ConcreteCategory.congr_hom (α.hom.naturality f) x

omit [HasBinaryBiproducts C] in
/-- An isomorphism of underlying set-valued functors sends zero to zero. -/
theorem natIsoForget_zero
    (α : F ⋙ CategoryTheory.forget AddCommGrpCat ≅ H ⋙ CategoryTheory.forget AddCommGrpCat)
    (X : C) : α.hom.app X (0 : F.obj X) = (0 : H.obj X) := by
  have h := natIsoForget_apply α (0 : X ⟶ X) (0 : F.obj X)
  rw [map_zero, H.map_zero] at h
  exact h

omit [HasBinaryBiproducts C] in
/-- A functor whose underlying set-valued functor agrees with an additive one annihilates zero
morphisms. -/
theorem natIsoForget_map_zero
    (α : F ⋙ CategoryTheory.forget AddCommGrpCat ≅ H ⋙ CategoryTheory.forget AddCommGrpCat)
    {X Y : C} : F.map (0 : X ⟶ Y) = 0 := by
  ext x
  apply (ConcreteCategory.bijective_of_isIso (α.hom.app Y)).1
  show α.hom.app Y ((F.map (0 : X ⟶ Y)).hom x) = α.hom.app Y (0 : F.obj Y)
  rw [natIsoForget_apply α (0 : X ⟶ Y) x, H.map_zero, natIsoForget_zero α]
  rfl

/-- An isomorphism of underlying set-valued functors, into an additive functor, is additive. -/
theorem natIsoForget_add
    (α : F ⋙ CategoryTheory.forget AddCommGrpCat ≅ H ⋙ CategoryTheory.forget AddCommGrpCat)
    (X : C) (x y : F.obj X) :
    α.hom.app X (x + y) = α.hom.app X x + α.hom.app X y := by
  let : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ natIsoForget_map_zero α⟩
  let z := (F.map (biprod.inl : X ⟶ X ⊞ X)).hom x + (F.map biprod.inr).hom y
  have hx : (F.map (biprod.fst : X ⊞ X ⟶ X)).hom z = x := by
    simp [z, ← AddCommGrpCat.comp_apply, ← F.map_comp]
  have hy : (F.map (biprod.snd : X ⊞ X ⟶ X)).hom z = y := by
    simp [z, ← AddCommGrpCat.comp_apply, ← F.map_comp]
  have hsum : (F.map (biprod.fst + biprod.snd : X ⊞ X ⟶ X)).hom z = x + y := by
    simp [z, ← AddCommGrpCat.comp_apply, ← F.map_comp, Preadditive.comp_add]
  have h := natIsoForget_apply α (biprod.fst + biprod.snd : X ⊞ X ⟶ X) z
  have h₁ := natIsoForget_apply α (biprod.fst : X ⊞ X ⟶ X) z
  have h₂ := natIsoForget_apply α (biprod.snd : X ⊞ X ⟶ X) z
  rw [hsum, H.map_add, AddCommGrpCat.hom_add, AddMonoidHom.add_apply, ← h₁, ← h₂, hx, hy] at h
  exact h

/-- **A natural isomorphism of abelian-group-valued functors obtained from one of their
underlying set-valued functors**, when the target is additive. -/
def natIsoOfForgetAddCommGrpCat
    (α : F ⋙ CategoryTheory.forget AddCommGrpCat ≅ H ⋙ CategoryTheory.forget AddCommGrpCat) :
    F ≅ H :=
  NatIso.ofComponents (fun X ↦ AddEquiv.toAddCommGrpIso
    { __ := (α.app X).toEquiv
      map_add' := natIsoForget_add α X }) (by
    intro X Y f
    ext x
    exact natIsoForget_apply α f x)

/-- The lifted isomorphism is the given one on elements. -/
theorem natIsoOfForgetAddCommGrpCat_hom_apply
    (α : F ⋙ CategoryTheory.forget AddCommGrpCat ≅ H ⋙ CategoryTheory.forget AddCommGrpCat)
    (X : C) (x : F.obj X) :
    ConcreteCategory.hom ((natIsoOfForgetAddCommGrpCat α).hom.app X) x = α.hom.app X x := rfl

/-- The inverse of the lifted isomorphism is the given inverse on elements. -/
theorem natIsoOfForgetAddCommGrpCat_inv_apply
    (α : F ⋙ CategoryTheory.forget AddCommGrpCat ≅ H ⋙ CategoryTheory.forget AddCommGrpCat)
    (X : C) (y : H.obj X) :
    ConcreteCategory.hom ((natIsoOfForgetAddCommGrpCat α).inv.app X) y = α.inv.app X y := rfl

end AdditiveNatIso

end CategoryTheory

namespace AlgebraicGeometry

section Stalk

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The forgetful functor of abelian groups preserves the filtered colimit over the pointed
étale neighbourhoods of a geometric point. -/
instance forget_preservesFiberColimits :
    PreservesColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ
      (CategoryTheory.forget AddCommGrpCat.{max u v}) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink.{u, v, u, v}
      (CategoryTheory.forget AddCommGrpCat.{max u v})
  exact Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{u} (geometricPointFiber B S hS s).Elementsᵒᵖ)
    (CategoryTheory.forget AddCommGrpCat.{max u v})

/-- **The abelian-group-valued étale stalk at a geometric point**, as a functor on abelian
sheaves on the small étale site: the colimit, taken in abelian groups, over the category of
pointed étale neighbourhoods of the point. -/
def abelianEtaleStalkFunctor :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
  sheafToPresheaf _ _ ⋙ etaleStalkPresheafFunctor B S hS s AddCommGrpCat.{max u v}

/-- The abelian-group-valued étale stalk functor is additive. -/
instance abelianEtaleStalkFunctor_additive :
    (abelianEtaleStalkFunctor.{u, v} B S hS s).Additive := by
  unfold abelianEtaleStalkFunctor etaleStalkPresheafFunctor
  infer_instance

/-- The germ at the geometric point of a section of an abelian sheaf over a pointed étale
neighbourhood, as an element of the abelian stalk. -/
def abelianEtaleStalkGerm
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max u v})
    (U : (geometricPointFiber B S hS s).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    (abelianEtaleStalkFunctor.{u, v} B S hS s).obj F :=
  ConcreteCategory.hom (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
    (sheafToPresheaf _ _).obj F) (op U)) t

/-- **The underlying set of the abelian stalk is the stalk of the underlying sheaf of
sets.** -/
def abelianEtaleStalkForgetIso :
    sheafCompose (SmallEtale.topology B S hS) (CategoryTheory.forget AddCommGrpCat.{max u v}) ⋙
        etaleStalkFunctor.{u, v} B S hS s ≅
      abelianEtaleStalkFunctor.{u, v} B S hS s ⋙
        CategoryTheory.forget AddCommGrpCat.{max u v} :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj
      (CategoryOfElements.π (geometricPointFiber B S hS s)).op)
    (preservesColimitNatIso (CategoryTheory.forget AddCommGrpCat.{max u v})).symm

/-- The comparison of stalks carries the germ of a section to its germ. -/
theorem abelianEtaleStalkForgetIso_germ
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max u v})
    (U : (geometricPointFiber B S hS s).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    (abelianEtaleStalkForgetIso.{u, v} B S hS s).hom.app F
        (etaleStalkGerm.{u, v} B S hS s
          ((sheafCompose (SmallEtale.topology B S hS)
            (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F) U t) =
      abelianEtaleStalkGerm.{u, v} B S hS s F U t :=
  ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv (CategoryTheory.forget AddCommGrpCat.{max u v})
      ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ F.obj) (op U)) t

end Stalk

section GenericTransport

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {G : Type u} [Group G] [TopologicalSpace G]
  (e : Sheaf J (Type w) ≌ ContinuousGSet.{u, w} G)
  [e.functor.Braided] [e.inverse.Braided]

/-- **Transport of an equivalence of a topos of sheaves of sets with continuous `G`-sets to
abelian sheaves and discrete `G`-modules**, by passing to commutative group objects on both
sides. -/
def abelianEquivalenceOfGSetEquivalence :
    Sheaf J AddCommGrpCat.{w} ≌ ContinuousGAddCommGrp.{u, w} G :=
  ((Sites.AbelianSheaf.equivalence J).trans e.mapCommGrp).trans
    commGrpContinuousGSetEquivalence

/-- The transported equivalence is the given one after forgetting abelian group structures. -/
theorem abelianEquivalenceOfGSetEquivalence_comp_forgetAction :
    (abelianEquivalenceOfGSetEquivalence J e).functor ⋙
        ContinuousGAddCommGrp.forgetAction G =
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w}) ⋙ e.functor := rfl

/-- The transported equivalence is the given one on underlying sets. -/
theorem abelianEquivalenceOfGSetEquivalence_comp_forget :
    ((abelianEquivalenceOfGSetEquivalence J e).functor ⋙
          ContinuousGAddCommGrp.forget G) ⋙ CategoryTheory.forget AddCommGrpCat.{w} =
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w}) ⋙
        (e.functor ⋙ ContinuousGSet.forget G) := rfl

/-- The Galois action on the transported object is the given one on elements. -/
theorem abelianEquivalenceOfGSetEquivalence_rho_apply
    (F : Sheaf J AddCommGrpCat.{w}) (σ : G)
    (x : ((abelianEquivalenceOfGSetEquivalence J e).functor.obj F).obj.obj.V) :
    ConcreteCategory.hom
        (((abelianEquivalenceOfGSetEquivalence J e).functor.obj F).obj.obj.ρ σ).asHom x =
      ConcreteCategory.hom
        ((e.functor.obj
          ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj F)).obj.obj.ρ σ).asHom x :=
  rfl

end GenericTransport

section Field

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- The equivalence of sheaves of sets on the small étale site of the spectrum of a field with
continuous Galois sets, the first component of `AlgebraicGeometry.etaleSheafStalkEquivalence`. -/
@[sga "4½ Arcata 2.4.4", sga "7 XIII 1.2.2" "more general"]
abbrev etaleGSetEquivalence :
    smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK ≌
      ContinuousGSet.{u, max u v} (GeometricPoint.absoluteGaloisGroup sbar) :=
  (etaleSheafStalkEquivalence.{u, v} B K hK sbar).1

/-- The braided monoidal structure of the functor of `etaleGSetEquivalence`. -/
local instance : (etaleGSetEquivalence.{u, v} B K hK sbar).functor.Braided :=
  .ofChosenFiniteProducts _
/-- The braided monoidal structure of the inverse of `etaleGSetEquivalence`. -/
local instance : (etaleGSetEquivalence.{u, v} B K hK sbar).inverse.Braided :=
  .ofChosenFiniteProducts _

/-- **Taking the stalk at a geometric point is an equivalence from abelian sheaves on the small
étale site of the spectrum of a field to discrete modules over the absolute Galois group at that
point.**  The equivalence for sheaves of sets is transported through commutative group objects
on both sides. -/
@[sga "4 VIII 2.2" "partial"]
def abelianEtaleStalkEquivalence :
    Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v} ≌
      ContinuousGAddCommGrp.{u, max u v} (GeometricPoint.absoluteGaloisGroup sbar) :=
  abelianEquivalenceOfGSetEquivalence _ (etaleGSetEquivalence.{u, v} B K hK sbar)

/-- The underlying set of the abelian stalk equivalence is the set-valued stalk functor. -/
def abelianEtaleStalkEquivalenceForgetIso :
    ((abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor ⋙
          ContinuousGAddCommGrp.forget (GeometricPoint.absoluteGaloisGroup sbar)) ⋙
        CategoryTheory.forget AddCommGrpCat.{max u v} ≅
      abelianEtaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar ⋙
        CategoryTheory.forget AddCommGrpCat.{max u v} :=
  Functor.isoWhiskerLeft
      (sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
        (CategoryTheory.forget AddCommGrpCat.{max u v}))
      (etaleSheafStalkEquivalence.{u, v} B K hK sbar).2.1 ≪≫
    abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar

/-- **The abelian stalk equivalence is given by taking stalks.** -/
def abelianEtaleStalkEquivalenceIso :
    (abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor ⋙
        ContinuousGAddCommGrp.forget (GeometricPoint.absoluteGaloisGroup sbar) ≅
      abelianEtaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar :=
  letI : HasBinaryBiproducts
      (Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}) :=
    .of_hasBinaryProducts
  natIsoOfForgetAddCommGrpCat (abelianEtaleStalkEquivalenceForgetIso.{u, v} B K hK sbar)

/-- The comparison with the stalk functor is the set-valued comparison followed by the
identification of underlying sets of stalks. -/
theorem abelianEtaleStalkEquivalenceForgetIso_app_hom_apply
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})
    (x : (((abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor ⋙
      ContinuousGAddCommGrp.forget (GeometricPoint.absoluteGaloisGroup sbar)) ⋙
        CategoryTheory.forget AddCommGrpCat.{max u v}).obj F) :
    ConcreteCategory.hom
        ((abelianEtaleStalkEquivalenceForgetIso.{u, v} B K hK sbar).app F).hom x =
      ConcreteCategory.hom
        ((abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar).app F).hom
        (ConcreteCategory.hom
          (((etaleSheafStalkEquivalence.{u, v} B K hK sbar).2.1).app
            ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
              (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F)).hom x) := rfl

/-- The inverse comparison with the stalk functor, read on elements. -/
theorem abelianEtaleStalkEquivalenceForgetIso_app_inv_apply
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})
    (y : (abelianEtaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar ⋙
      CategoryTheory.forget AddCommGrpCat.{max u v}).obj F) :
    ConcreteCategory.hom
        ((abelianEtaleStalkEquivalenceForgetIso.{u, v} B K hK sbar).app F).inv y =
      ConcreteCategory.hom
        (((etaleSheafStalkEquivalence.{u, v} B K hK sbar).2.1).app
          ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
            (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F)).inv
        (ConcreteCategory.hom
          ((abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar).app F).inv y) := rfl

/-- The Galois action on the abelian stalk is the Galois action on the stalk of the underlying
sheaf of sets. -/
theorem abelianEtaleStalkEquivalence_rho_apply
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (x : (((abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor.obj F).obj.obj.V : _)) :
    ConcreteCategory.hom
        (((abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor.obj F).obj.obj.ρ σ).asHom x =
      ConcreteCategory.hom
        (((etaleGSetEquivalence.{u, v} B K hK sbar).functor.obj
          ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
            (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F)).obj.obj.ρ σ).asHom x := rfl

/-- The comparison with the stalk functor, read on elements. -/
theorem abelianEtaleStalkEquivalenceIso_app_hom_apply
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})
    (x : (((abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor ⋙
      ContinuousGAddCommGrp.forget (GeometricPoint.absoluteGaloisGroup sbar))).obj F) :
    ConcreteCategory.hom
        ((abelianEtaleStalkEquivalenceIso.{u, v} B K hK sbar).app F).hom x =
      ConcreteCategory.hom
        ((abelianEtaleStalkEquivalenceForgetIso.{u, v} B K hK sbar).app F).hom x := rfl

/-- The inverse comparison with the stalk functor, read on elements. -/
theorem abelianEtaleStalkEquivalenceIso_app_inv_apply
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})
    (y : (abelianEtaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F) :
    ConcreteCategory.hom
        ((abelianEtaleStalkEquivalenceIso.{u, v} B K hK sbar).app F).inv y =
      ConcreteCategory.hom
        ((abelianEtaleStalkEquivalenceForgetIso.{u, v} B K hK sbar).app F).inv y := rfl

/-- For a geometric point of the spectrum of a field, taking stalks is an equivalence from abelian
sheaves on the small étale site to discrete modules over the absolute Galois group at that point,
naturally identified with the abelian-group-valued stalk functor, and the Galois action on a germ
changes the geometric lift of the étale neighbourhood by precomposition. -/
@[stacks 04JQ, sga "4 VIII 2.2"]
def abelianEtaleSheafStalkEquivalence :
    Σ e : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v} ≌
        ContinuousGAddCommGrp.{u, max u v} (GeometricPoint.absoluteGaloisGroup sbar),
      { α : e.functor ⋙
            ContinuousGAddCommGrp.forget (GeometricPoint.absoluteGaloisGroup sbar) ≅
          abelianEtaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar //
        ∀ (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})
          (σ : GeometricPoint.absoluteGaloisGroup sbar),
          letI := GeometricPoint.residueFieldAlgebra sbar
          ∀ (τ : Gal(sbar.residueField /
              (Spec (.of K)).residueField (sbar.hom default)))
            (_hτ : ∀ a : GeometricPoint.separableClosure sbar,
              (σ a : sbar.residueField) = τ (a : sbar.residueField))
            (U : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements)
            (q : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U.1)
            (_hq : q.1 = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ U.2.1)
            (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)),
            let V : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements := ⟨q⟩
            ConcreteCategory.hom (α.app F).hom
                (ConcreteCategory.hom ((e.functor.obj F).obj.obj.ρ σ).asHom
                  (ConcreteCategory.hom (α.app F).inv
                    (abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F U t))) =
              abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F V t } := by
  refine ⟨abelianEtaleStalkEquivalence.{u, v} B K hK sbar,
    abelianEtaleStalkEquivalenceIso.{u, v} B K hK sbar, ?_⟩
  intro F σ τ hτ U q hq t
  have h := (etaleSheafStalkEquivalence.{u, v} B K hK sbar).2.2
    ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
      (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F) σ τ hτ U q hq t
  have hU := abelianEtaleStalkForgetIso_germ.{u, v} B (Spec (.of K)) hK sbar F U t
  have hV := abelianEtaleStalkForgetIso_germ.{u, v} B (Spec (.of K)) hK sbar F ⟨q⟩ t
  have hinv : ∀ x : (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj
      ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
        (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F), ConcreteCategory.hom
      ((abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar).app F).inv
      (ConcreteCategory.hom
        ((abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar).app F).hom x) = x :=
    fun x ↦ ConcreteCategory.congr_hom
      ((abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar).app F).hom_inv_id x
  have hcinv : ConcreteCategory.hom
      ((abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar).app F).inv
      (abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F U t) =
        etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
          ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
            (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F) U t :=
    (congrArg (fun z ↦ ConcreteCategory.hom
      ((abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar).app F).inv z) hU).symm.trans
      (hinv _)
  have hA : ConcreteCategory.hom
      ((abelianEtaleStalkEquivalenceIso.{u, v} B K hK sbar).app F).inv
      (abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F U t) =
        ConcreteCategory.hom
          (((etaleSheafStalkEquivalence.{u, v} B K hK sbar).2.1).app
            ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
              (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F)).inv
          (etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
            ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
              (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F) U t) :=
    (abelianEtaleStalkEquivalenceIso_app_inv_apply.{u, v} B K hK sbar F _).trans
      ((abelianEtaleStalkEquivalenceForgetIso_app_inv_apply.{u, v} B K hK sbar F _).trans
        (congrArg (fun z ↦ ConcreteCategory.hom
          (((etaleSheafStalkEquivalence.{u, v} B K hK sbar).2.1).app
            ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
              (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F)).inv z) hcinv))
  have hmid := (congrArg (fun z ↦ ConcreteCategory.hom
      (((abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor.obj F).obj.obj.ρ σ).asHom z)
      hA).trans (abelianEtaleStalkEquivalence_rho_apply.{u, v} B K hK sbar F σ _)
  refine Eq.trans (abelianEtaleStalkEquivalenceIso_app_hom_apply.{u, v} B K hK sbar F _) ?_
  refine Eq.trans
    (abelianEtaleStalkEquivalenceForgetIso_app_hom_apply.{u, v} B K hK sbar F _) ?_
  refine Eq.trans (congrArg (fun z ↦ ConcreteCategory.hom
      ((abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar).app F).hom
      (ConcreteCategory.hom
        (((etaleSheafStalkEquivalence.{u, v} B K hK sbar).2.1).app
          ((sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
            (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F)).hom z)) hmid) ?_
  exact Eq.trans (congrArg (fun z ↦ ConcreteCategory.hom
    ((abelianEtaleStalkForgetIso.{u, v} B (Spec (.of K)) hK sbar).app F).hom z) h) hV

end Field

end AlgebraicGeometry

end

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.MonCat.Colimits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.GroupTopology

/-!
# Colimits in the category of topological groups

This file introduces the category `TopGrp` of topological groups and continuous group
homomorphisms and shows that it has all small colimits, and that these are computed on underlying
groups.

The colimit of a diagram `F : J ⥤ TopGrp` has as its carrier the colimit `colimitMon F` of the
underlying diagram of monoids; it is a *group* because the colimit cocone factors through the units
(`isUnit_colimitMon`), and it is topologised by the finest group topology making all the structure
maps continuous, namely `⨆ j, GroupTopology.coinduced (colimitMonIota F j)`.

That colimits commute with the forgetful functor to groups is the statement that
`TopGrp.forgetToGrpCat` preserves colimits, which follows from an adjunction: the forgetful functor
is a left adjoint, its right adjoint `TopGrp.indiscrete` equipping a group with the indiscrete
(chaotic) topology.

## Main results

* `TopGrp`: the category of topological groups.
* `TopGrp.forgetToGrpCatAdjunction`: the forgetful functor to groups is left adjoint to the
  indiscrete-topology functor.
* `TopGrp.hasColimits` (Stacks 0B21, first part): the category of topological groups has colimits.
* `TopGrp.forgetToGrpCat_preservesColimits` (Stacks 0B21, second part): colimits of topological
  groups commute with the forgetful functor to the category of groups.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

/-- The category of topological groups: a bundled group with a topology making the group
operations continuous. -/
structure TopGrp : Type (u + 1) where
  /-- The underlying type of a topological group. -/
  carrier : Type u
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]

namespace TopGrp

attribute [instance] group topologicalSpace isTopologicalGroup

/-- An object of `TopGrp` is used as a type through its carrier. -/
instance : CoeSort TopGrp (Type u) := ⟨carrier⟩

/-- Bundle a topological group as an object of `TopGrp`. -/
abbrev of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : TopGrp := ⟨G⟩

/-- Morphisms of topological groups are the continuous group homomorphisms. -/
instance : Category TopGrp.{u} where
  Hom G H := G →ₜ* H
  id G := ContinuousMonoidHom.id G
  comp f g := g.comp f

/-- A morphism of topological groups acts as a function between the underlying types. -/
instance instFunLike (G H : TopGrp.{u}) : FunLike (G ⟶ H) G H :=
  inferInstanceAs (FunLike (G →ₜ* H) G H)

/-- A morphism of topological groups preserves multiplication and the unit. -/
instance instMonoidHomClass (G H : TopGrp.{u}) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs (MonoidHomClass (G →ₜ* H) G H)

/-- A morphism of topological groups is continuous. -/
instance instContinuousMapClass (G H : TopGrp.{u}) : ContinuousMapClass (G ⟶ H) G H :=
  inferInstanceAs (ContinuousMapClass (G →ₜ* H) G H)

/-- Two morphisms of topological groups that agree pointwise are equal. -/
@[ext] theorem hom_ext {G H : TopGrp.{u}} {f g : G ⟶ H} (h : ∀ x : G, f x = g x) : f = g :=
  ContinuousMonoidHom.ext h

/-- The forgetful functor from topological groups to groups. -/
def forgetToGrpCat : TopGrp.{u} ⥤ GrpCat.{u} where
  obj G := .of G
  map f := GrpCat.ofHom f.toMonoidHom

/-- The forgetful functor from topological groups to monoids. -/
def forgetToMonCat : TopGrp.{u} ⥤ MonCat.{u} where
  obj G := .of G
  map f := MonCat.ofHom f.toMonoidHom

/-- A group with the indiscrete (chaotic) topology, as a topological group. -/
def indiscreteObj (G : GrpCat.{u}) : TopGrp.{u} :=
  letI : TopologicalSpace G := ⊤
  letI : IsTopologicalGroup G :=
    { continuous_mul := continuous_top, continuous_inv := continuous_top }
  .of G

/-- The functor equipping a group with the indiscrete (chaotic) topology. Every group
homomorphism into an indiscrete topological group is continuous, so this is functorial. -/
def indiscrete : GrpCat.{u} ⥤ TopGrp.{u} where
  obj := indiscreteObj
  map f := ⟨f.hom, continuous_top⟩

/-- The forgetful functor to groups is left adjoint to the indiscrete-topology functor: a group
homomorphism out of the underlying group of a topological group `G` is the same thing as a
continuous homomorphism from `G` to the indiscrete topological group on the target. -/
def forgetToGrpCatAdjunction : forgetToGrpCat.{u} ⊣ indiscrete.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ⟨f.hom, continuous_top⟩
          invFun := fun f => GrpCat.ofHom f.toMonoidHom
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; rfl }

/-- **Stacks 0B21**, second part. Colimits of topological groups commute with the forgetful functor
to the category of groups: the forgetful functor is a left adjoint, hence preserves colimits. -/
@[stacks 0B21 "commutation with the forgetful functor to groups"]
instance forgetToGrpCat_preservesColimits : PreservesColimits forgetToGrpCat.{u} :=
  forgetToGrpCatAdjunction.leftAdjoint_preservesColimits

section Colimits

variable {J : Type u} [SmallCategory J] (F : J ⥤ TopGrp.{u})

/-- The colimit of the diagram of monoids underlying a diagram of topological groups. -/
noncomputable abbrev colimitMon : MonCat.{u} := colimit (F ⋙ forgetToMonCat)

/-- The `j`-th structure map into the colimit of the underlying monoids. -/
noncomputable abbrev colimitMonIota (j : J) : ↥(F.obj j) →* ↥(colimitMon F) :=
  (colimit.ι (F ⋙ forgetToMonCat) j).hom

/-- Every element of the colimit of the underlying monoids of a diagram of topological groups is
invertible: since each `F.obj j` is a group, the colimit cocone factors through the units, and the
resulting endomorphism of the colimit is the identity by the universal property. -/
theorem isUnit_colimitMon (x : ↥(colimitMon F)) : IsUnit x := by
  let c : Cocone (F ⋙ forgetToMonCat) :=
    { pt := MonCat.of (↥(colimitMon F))ˣ
      ι :=
        { app := fun j => MonCat.ofHom (colimitMonIota F j).toHomUnits
          naturality := fun {j j'} g => by
            ext y
            exact Units.ext (ConcreteCategory.congr_hom (colimit.w (F ⋙ forgetToMonCat) g) y) } }
  refine ⟨(colimit.desc (F ⋙ forgetToMonCat) c).hom x, ConcreteCategory.congr_hom
    (colimit.hom_ext fun j => ?_ :
      colimit.desc (F ⋙ forgetToMonCat) c ≫ MonCat.ofHom (Units.coeHom ↥(colimitMon F))
        = 𝟙 (colimitMon F)) x⟩
  rw [← Category.assoc, colimit.ι_desc, Category.comp_id]
  ext y
  rfl

/-- The group structure on the colimit of the underlying monoids. -/
noncomputable local instance colimitGroup : Group ↥(colimitMon F) :=
  groupOfIsUnit (isUnit_colimitMon F)

/-- The topology of the colimit: the finest group topology for which every structure map is
continuous. -/
noncomputable def colimitGroupTopology : GroupTopology ↥(colimitMon F) :=
  ⨆ j, GroupTopology.coinduced (colimitMonIota F j)

/-- The colimit of a diagram of topological groups, as a topological group. -/
noncomputable def colimitObj : TopGrp.{u} :=
  letI := (colimitGroupTopology F).toTopologicalSpace
  letI := (colimitGroupTopology F).toIsTopologicalGroup
  .of ↥(colimitMon F)

/-- The structure maps into the colimit are continuous, since the colimit topology is coarser than
each topology coinduced from them. -/
theorem continuous_colimitMonIota (j : J) :
    Continuous[_, (colimitGroupTopology F).toTopologicalSpace] (colimitMonIota F j) :=
  continuous_le_rng (GroupTopology.toTopologicalSpace_le.2 (le_iSup _ j))
    (GroupTopology.coinduced_continuous _)

/-- The colimit cocone of a diagram of topological groups. -/
noncomputable def colimitCocone : Cocone F where
  pt := colimitObj F
  ι :=
    { app := fun j => ⟨colimitMonIota F j, continuous_colimitMonIota F j⟩
      naturality := fun {j j'} g => by
        ext y
        exact ConcreteCategory.congr_hom (colimit.w (F ⋙ forgetToMonCat) g) y }

/-- The homomorphism out of the colimit of the underlying monoids induced by a cocone. -/
noncomputable abbrev colimitMonDesc (s : Cocone F) : ↥(colimitMon F) →* ↥(s.pt) :=
  (colimit.desc (F ⋙ forgetToMonCat) (forgetToMonCat.mapCocone s)).hom

/-- The homomorphism induced by a cocone is continuous: the topology induced along it is a group
topology for which every structure map is continuous, hence coarser than the colimit topology. -/
theorem continuous_colimitMonDesc (s : Cocone F) :
    Continuous[(colimitGroupTopology F).toTopologicalSpace, _] (colimitMonDesc F s) := by
  set φ := colimitMonDesc F s
  refine continuous_iff_le_induced.2 ((GroupTopology.toTopologicalSpace_le
    (y := ⟨TopologicalSpace.induced φ inferInstance, isTopologicalGroup_induced φ⟩)).2
    (iSup_le fun j => sInf_le ?_))
  rw [Set.mem_ofPred_eq, ← continuous_iff_coinduced_le, continuous_induced_rng]
  exact (map_continuous (s.ι.app j)).congr fun y =>
    (ConcreteCategory.congr_hom (colimit.ι_desc (forgetToMonCat.mapCocone s) j) y).symm

/-- The colimit cocone is a colimit: descent and its uniqueness both come from the colimit of the
underlying monoids. -/
noncomputable def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := ⟨colimitMonDesc F s, continuous_colimitMonDesc F s⟩
  fac s j := by
    ext y
    exact ConcreteCategory.congr_hom (colimit.ι_desc (forgetToMonCat.mapCocone s) j) y
  uniq s m w := by
    have hm : MonCat.ofHom m.toMonoidHom
        = colimit.desc (F ⋙ forgetToMonCat) (forgetToMonCat.mapCocone s) := by
      refine colimit.hom_ext fun j => ?_
      ext z
      refine (DFunLike.congr_fun (w j) z).trans ?_
      exact (ConcreteCategory.congr_hom (colimit.ι_desc (forgetToMonCat.mapCocone s) j) z).symm
    ext y
    exact ConcreteCategory.congr_hom hm y

/-- **Stacks 0B21**, first part. The category of topological groups has colimits. -/
@[stacks 0B21 "existence of colimits"]
noncomputable instance hasColimits : HasColimits TopGrp.{u} where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk { cocone := colimitCocone F, isColimit := colimitIsColimit F } }

end Colimits

end TopGrp

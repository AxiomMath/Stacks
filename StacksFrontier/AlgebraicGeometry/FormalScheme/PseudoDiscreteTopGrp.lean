module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.PseudoDiscreteTopCat
public import StacksFrontier.Topology.Algebra.GroupColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-discrete sheaves of topological groups

Let `X` be a topological space with a basis of quasi-compact opens. The source (Stacks,
Section 87.2, Tag 0AHY) endows every sheaf of groups on `X` with the structure of a sheaf of
topological groups, the *pseudo-discrete* one, and states that this construction is adjoint to
the forgetful functor and induces an equivalence between the category of sheaves of groups and
the category of pseudo-discrete sheaves of topological groups. This file proves both statements.

The forgetful functor `TopGrp ⥤ GrpCat` preserves limits, being right adjoint to the
discrete-topology functor (`TopGrp.discreteAdjunction`); this is what makes the underlying
presheaf of groups of a sheaf of topological groups a sheaf.

## Main definitions

* `TopGrp.discrete` and `TopGrp.discreteAdjunction`: the discrete topological group on a group,
  left adjoint to the forgetful functor.
* `AlgebraicGeometry.pseudoDiscreteGroup`: the pseudo-discrete presheaf of topological groups.
* `AlgebraicGeometry.pseudoDiscreteGroupSheafAdjunction`: pseudo-discretisation of sheaves of
  groups is left adjoint to forgetting the topology.
* `AlgebraicGeometry.pseudoDiscreteGroupSheafEquivalence`: it is an equivalence between sheaves
  of groups and pseudo-discrete sheaves of topological groups.

## References

* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open TopCat.Presheaf.SheafCondition
open scoped Topology

universe u

namespace TopGrp

/-- The discrete topology on a group is a group topology. -/
theorem isTopologicalGroup_bot (G : GrpCat.{u}) : @IsTopologicalGroup G ⊥ _ :=
  letI : TopologicalSpace G := ⊥
  haveI : DiscreteTopology G := ⟨rfl⟩
  { continuous_mul := continuous_of_discreteTopology
    continuous_inv := continuous_of_discreteTopology }

/-- A group with the discrete topology, as a topological group. -/
def discreteObj (G : GrpCat.{u}) : TopGrp.{u} where
  carrier := G
  topologicalSpace := ⊥
  isTopologicalGroup := isTopologicalGroup_bot G

/-- Every group homomorphism out of a discrete topological group is continuous. -/
def discreteHom {G : GrpCat.{u}} {H : TopGrp.{u}} (f : G →* H) : discreteObj G ⟶ H :=
  (⟨f, continuous_bot⟩ : discreteObj G →ₜ* H)

/-- The functor equipping a group with the discrete topology. -/
def discrete : GrpCat.{u} ⥤ TopGrp.{u} where
  obj := discreteObj
  map {G H} f := discreteHom (H := discreteObj H) f.hom

/-- The discrete-topology functor is left adjoint to the forgetful functor to groups: every group
homomorphism out of a discrete topological group is continuous. -/
def discreteAdjunction : discrete.{u} ⊣ forgetToGrpCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G H =>
        { toFun := fun f => GrpCat.ofHom (f.toMonoidHom : G →* H)
          invFun := fun f => discreteHom f.hom
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; rfl }

/-- The forgetful functor from topological groups to groups preserves limits, being a right
adjoint. -/
instance forgetToGrpCat_preservesLimits : PreservesLimits forgetToGrpCat.{u} :=
  discreteAdjunction.rightAdjoint_preservesLimits

end TopGrp

namespace AlgebraicGeometry

variable {X : TopCat.{u}}

/-- The underlying presheaf of sets of a presheaf of groups. -/
abbrev groupSets (F : X.Presheaf GrpCat.{u}) : X.Presheaf (Type u) :=
  F ⋙ forget GrpCat.{u}

/-- The pseudo-discrete topology is a group topology. -/
theorem isTopologicalGroup_pseudoDiscreteTopologySet (F : X.Presheaf GrpCat.{u})
    (U : Opens X) :
    @IsTopologicalGroup (F.obj (op U)) (pseudoDiscreteTopologySet (groupSets F) U) _ := by
  refine isTopologicalGroup_iInf fun V => ?_
  let : TopologicalSpace (F.obj (op V.1)) := ⊥
  have : DiscreteTopology (F.obj (op V.1)) := ⟨rfl⟩
  have : IsTopologicalGroup (F.obj (op V.1)) :=
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }
  exact isTopologicalGroup_induced (F.map (homOfLE V.2.2).op).hom

/-- The sections of a presheaf of groups over `U`, as a topological group with the
pseudo-discrete topology. -/
def pseudoDiscreteGroupObj (F : X.Presheaf GrpCat.{u}) (U : Opens X) : TopGrp.{u} :=
  letI : TopologicalSpace (F.obj (op U)) := pseudoDiscreteTopologySet (groupSets F) U
  haveI := isTopologicalGroup_pseudoDiscreteTopologySet F U
  TopGrp.of (F.obj (op U))

/-- A continuous group homomorphism between topological groups, as a morphism of `TopGrp`. -/
abbrev topGrpHom {A B : TopGrp.{u}} (f : A →* B) (hf : Continuous f) : A ⟶ B :=
  (⟨f, hf⟩ : A →ₜ* B)

/-- The *pseudo-discrete presheaf of topological groups* attached to a presheaf of groups. -/
def pseudoDiscreteGroup (F : X.Presheaf GrpCat.{u}) : X.Presheaf TopGrp.{u} where
  obj U := pseudoDiscreteGroupObj F U.unop
  map i := topGrpHom (A := pseudoDiscreteGroupObj F _) (B := pseudoDiscreteGroupObj F _)
    (F.map i).hom (continuous_pseudoDiscreteTopologySet_map (groupSets F) (leOfHom i.unop))
  map_id U := TopGrp.hom_ext fun s => congrArg (fun g => g.hom s) (F.map_id U)
  map_comp f g := TopGrp.hom_ext fun s => congrArg (fun h => h.hom s) (F.map_comp f g)

/-- A presheaf of topological groups is *pseudo-discrete* when its group of sections over every
quasi-compact open is discrete. -/
def IsPseudoDiscreteGroup (G : X.Presheaf TopGrp.{u}) : Prop :=
  ∀ U : Opens X, IsCompact (U : Set X) → DiscreteTopology (G.obj (op U))

/-- The pseudo-discretisation is pseudo-discrete. -/
theorem isPseudoDiscreteGroup_pseudoDiscreteGroup (F : X.Presheaf GrpCat.{u}) :
    IsPseudoDiscreteGroup (pseudoDiscreteGroup F) :=
  fun _ hU => ⟨pseudoDiscreteTopologySet_eq_bot (groupSets F) hU⟩

/-- Pseudo-discretisation as a functor from presheaves of groups to presheaves of topological
groups. -/
def pseudoDiscreteGroupFunctor : X.Presheaf GrpCat.{u} ⥤ X.Presheaf TopGrp.{u} where
  obj F := pseudoDiscreteGroup F
  map η :=
    { app := fun U => topGrpHom (A := pseudoDiscreteGroupObj _ _)
        (B := pseudoDiscreteGroupObj _ _) (η.app U).hom
        (continuous_pseudoDiscreteTopologySet_app
          (Functor.whiskerRight η (forget GrpCat.{u})) U.unop)
      naturality := fun _ _ i => TopGrp.hom_ext fun s =>
        congrArg (fun h => h.hom s) (η.naturality i) }

/-- Forgetting the topology of the pseudo-discretisation gives back the presheaf of groups. -/
def pseudoDiscreteGroupCompForgetIso (F : X.Presheaf GrpCat.{u}) :
    pseudoDiscreteGroup F ⋙ TopGrp.forgetToGrpCat.{u} ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable [PrespectralSpace X]

/-- **A morphism of presheaves of groups into a sheaf of topological groups is continuous for
the pseudo-discrete topology.** -/
theorem continuous_app_of_isSheaf_topGrp (F : X.Presheaf GrpCat.{u})
    {G : X.Presheaf TopGrp.{u}} (hG : G.IsSheaf)
    (η : F ⟶ G ⋙ TopGrp.forgetToGrpCat.{u}) (U : Opens X) :
    Continuous[pseudoDiscreteTopologySet (groupSets F) U, (G.obj (op U)).topologicalSpace]
      (η.app (op U)).hom := by
  let cover : CompactOpenLE U → Opens X := fun V => V.1
  have hle : ∀ W : OpensLeCover cover, W.obj ≤ U :=
    fun W => W.property.choose_spec.trans W.property.choose.2.2
  let leg : ∀ W : OpensLeCover cover, F.obj (op U) →* G.obj (op W.obj) := fun W =>
    (η.app (op W.obj)).hom.comp (F.map (homOfLE (hle W)).op).hom
  have hnat : ∀ {V W : Opens X} (hWV : W ≤ V) (hVU : V ≤ U),
      F.map (homOfLE (hWV.trans hVU)).op ≫ η.app (op W) =
        F.map (homOfLE hVU).op ≫ η.app (op V) ≫
          (G ⋙ TopGrp.forgetToGrpCat).map (homOfLE hWV).op := by
    intro V W hWV hVU
    rw [← η.naturality, ← Category.assoc, ← F.map_comp]
    rfl
  have hcont : ∀ W : OpensLeCover cover,
      Continuous[pseudoDiscreteTopologySet (groupSets F) U, (G.obj (op W.obj)).topologicalSpace]
        (leg W) := by
    intro W
    let i := W.property.choose
    have hWi : W.obj ≤ i.1 := W.property.choose_spec
    have hfun : ⇑(leg W) = (G.map (homOfLE hWi).op) ∘ (η.app (op i.1)).hom ∘
        (F.map (homOfLE i.2.2).op).hom := by
      funext s
      exact congrArg (fun g => g.hom s) (hnat hWi i.2.2)
    rw [hfun]
    have h₁ := continuous_pseudoDiscreteTopologySet_restrict (groupSets F) i.2.1 i.2.2
    have h₂ : Continuous[⊥, (G.obj (op i.1)).topologicalSpace] (η.app (op i.1)).hom :=
      continuous_bot
    exact @Continuous.comp _ _ _ (pseudoDiscreteTopologySet (groupSets F) U)
      (G.obj (op i.1)).topologicalSpace (G.obj (op W.obj)).topologicalSpace _ _
      (map_continuous (G.map (homOfLE hWi).op))
      (@Continuous.comp _ _ _ (pseudoDiscreteTopologySet (groupSets F) U) ⊥
        (G.obj (op i.1)).topologicalSpace _ _ h₂ h₁)
  let c : Cone ((ObjectProperty.ι _ : OpensLeCover cover ⥤ Opens X).op ⋙ G) :=
    { pt := pseudoDiscreteGroupObj F U
      π :=
        { app := fun W => topGrpHom (A := pseudoDiscreteGroupObj F U) (leg W.unop) (hcont W.unop)
          naturality := by
            intro W W' f
            refine TopGrp.hom_ext fun s => ?_
            exact (congrArg (fun g => g.hom s)
              (hnat (leOfHom f.unop.hom) (hle W.unop))).trans rfl } }
  let lim := (hG.isSheafOpensLeCover cover).some
  have hsup : U ≤ iSup cover := (iSup_compactOpenLE U).ge
  have hGr : TopCat.Presheaf.IsSheaf (G ⋙ TopGrp.forgetToGrpCat.{u}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ hG
  have key : ⇑(η.app (op U)).hom = (G.map (homOfLE hsup).op) ∘ (lim.lift c) := by
    funext s
    refine TopCat.Sheaf.eq_of_locally_eq'
      (⟨G ⋙ TopGrp.forgetToGrpCat, hGr⟩ : TopCat.Sheaf GrpCat X) cover U
      (fun V => homOfLE V.2.2) hsup _ _ fun V => ?_
    let W : OpensLeCover cover := ⟨V.1, V, le_rfl⟩
    have hfac : (G.map ((opensLeCoverCocone cover).ι.app W).op) ((lim.lift c) s) = leg W s :=
      congrArg (fun g => g s) (lim.fac c (op W))
    have hL : ((G ⋙ TopGrp.forgetToGrpCat).map (homOfLE V.2.2).op).hom
        ((η.app (op U)).hom s) = leg W s :=
      (congrArg (fun g => g.hom s) (η.naturality (homOfLE V.2.2).op)).symm
    have hR : ((G ⋙ TopGrp.forgetToGrpCat).map (homOfLE V.2.2).op).hom
        ((G.map (homOfLE hsup).op) ((lim.lift c) s)) = leg W s :=
      (congrArg (fun g => g ((lim.lift c) s))
        (G.map_comp (homOfLE hsup).op (homOfLE V.2.2).op)).symm.trans hfac
    exact hL.trans hR.symm
  rw [key]
  exact @Continuous.comp _ _ _ (pseudoDiscreteTopologySet (groupSets F) U)
    (G.obj (op (iSup cover))).topologicalSpace (G.obj (op U)).topologicalSpace _ _
    (map_continuous (G.map (homOfLE hsup).op)) (map_continuous (lim.lift c))

/-- On a space with a basis of quasi-compact opens, the pseudo-discrete presheaf of topological
groups attached to a sheaf of groups is a sheaf of topological groups. -/
theorem isSheaf_pseudoDiscreteGroup_of_isSheaf (F : X.Presheaf GrpCat.{u}) (hF : F.IsSheaf) :
    (pseudoDiscreteGroup F).IsSheaf := by
  have hFs : (groupSets F).IsSheaf :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ (forget GrpCat.{u}) hF
  refine (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover _).2 fun ι cover => ?_
  let grpLimit := (hF.isSheafOpensLeCover cover).some
  let fgt := TopGrp.forgetToGrpCat.{u}
  refine ⟨IsLimit.mk (fun cone => topGrpHom
    (B := pseudoDiscreteGroupObj F (iSup cover)) (grpLimit.lift (fgt.mapCone cone)).hom ?_)
    (fun cone V => ?_) ?_⟩
  · refine continuous_pseudoDiscreteSet_gluing_of_isSheaf (groupSets F) hFs cover _
      fun V => ?_
    have hfac : ⇑(F.map ((opensLeCoverCocone cover).ι.app V).op).hom ∘
        ⇑(grpLimit.lift (fgt.mapCone cone)).hom = ⇑(cone.π.app (op V)) := by
      funext t
      exact congrArg (fun g => g.hom t) (grpLimit.fac (fgt.mapCone cone) (op V))
    exact hfac ▸ map_continuous (cone.π.app (op V))
  · exact TopGrp.hom_ext fun t =>
      congrArg (fun g => g.hom t) (grpLimit.fac (fgt.mapCone cone) V)
  · intro cone morphism hfac
    exact TopGrp.hom_ext fun t => congrArg (fun g => g.hom t)
      (grpLimit.uniq (fgt.mapCone cone) (fgt.map morphism) fun V => congrArg fgt.map (hfac V))

variable (X) in
/-- Pseudo-discretisation as a functor from sheaves of groups to sheaves of topological
groups. -/
def pseudoDiscreteGroupSheafFunctor :
    Sheaf (Opens.grothendieckTopology X) GrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) TopGrp.{u} :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ pseudoDiscreteGroupFunctor)
    fun F => isSheaf_pseudoDiscreteGroup_of_isSheaf F.obj F.property

variable (X) in
/-- Forgetting the topology of a sheaf of topological groups. -/
noncomputable abbrev sheafForgetTopGrp :
    Sheaf (Opens.grothendieckTopology X) TopGrp.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) GrpCat.{u} :=
  sheafCompose _ TopGrp.forgetToGrpCat.{u}

/-- The bijection between morphisms out of a pseudo-discretisation and morphisms into the
underlying sheaf of groups. -/
noncomputable def pseudoDiscreteGroupSheafHomEquiv
    (F : Sheaf (Opens.grothendieckTopology X) GrpCat.{u})
    (G : Sheaf (Opens.grothendieckTopology X) TopGrp.{u}) :
    ((pseudoDiscreteGroupSheafFunctor X).obj F ⟶ G) ≃ (F ⟶ (sheafForgetTopGrp X).obj G) where
  toFun φ := ObjectProperty.homMk
    ((pseudoDiscreteGroupCompForgetIso F.obj).inv ≫
      Functor.whiskerRight φ.hom TopGrp.forgetToGrpCat)
  invFun ψ := ObjectProperty.homMk
    { app := fun U => topGrpHom (A := pseudoDiscreteGroupObj F.obj U.unop) (ψ.hom.app U).hom
        (continuous_app_of_isSheaf_topGrp F.obj G.property ψ.hom U.unop)
      naturality := fun _ _ i => TopGrp.hom_ext fun s =>
        congrArg (fun h => h.hom s) (ψ.hom.naturality i) }
  left_inv φ := by
    ext
    rfl
  right_inv ψ := by
    ext
    rfl

/-- **Stacks 0AHY**: on a space with a basis of quasi-compact opens, pseudo-discretisation of
sheaves of groups is left adjoint to the forgetful functor from sheaves of topological groups to
sheaves of groups. -/
@[stacks 0AHY "the pseudo-discrete construction on sheaves of groups is adjoint to the \
forgetful functor"]
noncomputable def pseudoDiscreteGroupSheafAdjunction :
    pseudoDiscreteGroupSheafFunctor X ⊣ sheafForgetTopGrp X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pseudoDiscreteGroupSheafHomEquiv
      homEquiv_naturality_left_symm := by
        intros
        ext
        rfl
      homEquiv_naturality_right := by
        intros
        ext
        rfl }

variable (X) in
/-- The full subcategory of pseudo-discrete sheaves of topological groups. -/
abbrev PseudoDiscreteGroupSheaf :=
  ObjectProperty.FullSubcategory
    fun G : Sheaf (Opens.grothendieckTopology X) TopGrp.{u} => IsPseudoDiscreteGroup G.obj

/-- On the sections of a pseudo-discrete sheaf of topological groups, the given topology is the
pseudo-discrete topology of the underlying sheaf of groups. -/
theorem pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteGroup {G : X.Presheaf TopGrp.{u}}
    (hG : G.IsSheaf) (hpd : IsPseudoDiscreteGroup G) (U : Opens X) :
    pseudoDiscreteTopologySet (groupSets (G ⋙ TopGrp.forgetToGrpCat.{u})) U =
      (G.obj (op U)).topologicalSpace := by
  refine le_antisymm ?_ ?_
  · exact continuous_id_iff_le.1
      (by exact continuous_app_of_isSheaf_topGrp _ hG (𝟙 (G ⋙ TopGrp.forgetToGrpCat.{u})) U)
  · refine le_iInf fun V => continuous_iff_le_induced.1 ?_
    have hV := hpd V.1 V.2.1
    exact @Continuous.comp _ _ _ (G.obj (op U)).topologicalSpace
      (G.obj (op V.1)).topologicalSpace ⊥ _ id (continuous_id_of_le hV.eq_bot.le)
      (map_continuous (G.map (homOfLE V.2.2).op))

/-- The isomorphism between a pseudo-discrete sheaf of topological groups and the
pseudo-discretisation of its underlying sheaf of groups. -/
noncomputable def pseudoDiscreteGroupForgetIso (G : PseudoDiscreteGroupSheaf X) :
    (pseudoDiscreteGroupSheafFunctor X).obj ((sheafForgetTopGrp X).obj G.obj) ≅ G.obj :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun U =>
      { hom := topGrpHom
          (A := pseudoDiscreteGroupObj (G.obj.obj ⋙ TopGrp.forgetToGrpCat) U.unop)
          (B := G.obj.obj.obj U) (MonoidHom.id _) (by
            have := pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteGroup G.obj.property
              G.property U.unop
            exact continuous_id_of_le this.le)
        inv := topGrpHom (A := G.obj.obj.obj U)
          (B := pseudoDiscreteGroupObj (G.obj.obj ⋙ TopGrp.forgetToGrpCat) U.unop)
          (MonoidHom.id _) (by
            have := pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteGroup G.obj.property
              G.property U.unop
            exact continuous_id_of_le this.ge)
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

variable (X) in
/-- **Stacks 0AHY**: on a space with a basis of quasi-compact opens, pseudo-discretisation is an
equivalence between the category of sheaves of groups and the category of pseudo-discrete sheaves
of topological groups; its inverse forgets the topology. -/
@[stacks 0AHY "equivalence between sheaves of groups and pseudo-discrete sheaves of topological \
groups"]
noncomputable def pseudoDiscreteGroupSheafEquivalence :
    Sheaf (Opens.grothendieckTopology X) GrpCat.{u} ≌ PseudoDiscreteGroupSheaf X :=
  CategoryTheory.Equivalence.mk
    (ObjectProperty.lift
      (fun G : Sheaf (Opens.grothendieckTopology X) TopGrp.{u} => IsPseudoDiscreteGroup G.obj)
      (pseudoDiscreteGroupSheafFunctor X)
      fun F => isPseudoDiscreteGroup_pseudoDiscreteGroup F.obj)
    (ObjectProperty.ι
      (fun G : Sheaf (Opens.grothendieckTopology X) TopGrp.{u} => IsPseudoDiscreteGroup G.obj) ⋙
        sheafForgetTopGrp X)
    (NatIso.ofComponents
      (fun F => ObjectProperty.isoMk _ (pseudoDiscreteGroupCompForgetIso F.obj).symm)
      (fun _ => by ext; rfl))
    (NatIso.ofComponents (fun G => ObjectProperty.isoMk _ (pseudoDiscreteGroupForgetIso G))
      (fun _ => by ext; rfl))

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.PseudoDiscreteSheaf
public import StacksFrontier.Topology.Algebra.RingLimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-discrete sheaves of topological rings

Let `X` be a topological space with a basis of quasi-compact opens. The source (Stacks,
Section 87.2, Tag 0AHY) endows every sheaf of rings `𝒪` on `X` with the structure of a sheaf of
topological rings, the *pseudo-discrete* one, and states that "the construction given above is an
adjoint to the forgetful functor and induces an equivalence between the category of sheaves of
rings and the category of pseudo-discrete sheaves of topological rings". This file proves both
statements.

The key point is `AlgebraicGeometry.continuous_app_of_isSheaf`: a morphism of presheaves of rings
from `F` to the underlying presheaf of rings of a *sheaf* of topological rings `G` is continuous
for the pseudo-discrete topologies on the sections of `F`. Indeed, the sections of `G` over `U`
carry the topology induced from the product of the sections over the quasi-compact opens
`V ⊆ U` (these cover `U`, and `G` is a sheaf of topological rings), and the composite
`F(U) → F(V) → G(V)` is continuous because `F(V)` is discrete.

## Main definitions

* `AlgebraicGeometry.pseudoDiscreteSheafFunctor`: pseudo-discretisation of sheaves of rings.
* `AlgebraicGeometry.pseudoDiscreteSheafAdjunction`: it is left adjoint to forgetting the topology.
* `AlgebraicGeometry.pseudoDiscreteSheafEquivalence`: it is an equivalence between sheaves of rings
  and pseudo-discrete sheaves of topological rings.

## References

* [EGA 0, 3.8.1]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open TopCat.Presheaf.SheafCondition
open scoped Topology

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}} [PrespectralSpace X]

/-- On a space with a basis of quasi-compact opens, the quasi-compact opens contained in an open
`U` cover it. -/
theorem iSup_compactOpenLE (U : Opens X) : iSup (fun V : CompactOpenLE U => V.1) = U := by
  refine le_antisymm (iSup_le fun V => V.2.2) fun x hx => ?_
  obtain ⟨V, ⟨hVo, hVc⟩, hxV, hVU⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx U.isOpen
  exact Opens.mem_iSup.2 ⟨⟨⟨V, hVo⟩, hVc, hVU⟩, hxV⟩

/-- **A morphism of presheaves of rings into a sheaf of topological rings is continuous for the
pseudo-discrete topology.** Given a presheaf of rings `F` and a sheaf of topological rings `G`, any
morphism from `F` to the underlying presheaf of rings of `G` is continuous on sections over every
open, for the pseudo-discrete topology on the sections of `F`. -/
theorem continuous_app_of_isSheaf (F : X.Presheaf CommRingCat.{u})
    {G : X.Presheaf TopCommRingCat.{u}} (hG : G.IsSheaf)
    (η : F ⟶ G ⋙ forget₂ TopCommRingCat CommRingCat) (U : Opens X) :
    Continuous[pseudoDiscreteTopology F U, (G.obj (op U)).isTopologicalSpace]
      (η.app (op U)).hom := by
  let cover : CompactOpenLE U → Opens X := fun V => V.1
  have hle : ∀ W : OpensLeCover cover, W.obj ≤ U :=
    fun W => W.property.choose_spec.trans W.property.choose.2.2
  let leg : ∀ W : OpensLeCover cover, F.obj (op U) →+* G.obj (op W.obj) := fun W =>
    (η.app (op W.obj)).hom.comp (F.map (homOfLE (hle W)).op).hom
  have hnat : ∀ {V W : Opens X} (hWV : W ≤ V) (hVU : V ≤ U),
      F.map (homOfLE (hWV.trans hVU)).op ≫ η.app (op W) =
        F.map (homOfLE hVU).op ≫ η.app (op V) ≫
          (G ⋙ forget₂ TopCommRingCat CommRingCat).map (homOfLE hWV).op := by
    intro V W hWV hVU
    rw [← η.naturality, ← Category.assoc, ← F.map_comp]
    rfl
  have hcont : ∀ W : OpensLeCover cover,
      Continuous[pseudoDiscreteTopology F U, (G.obj (op W.obj)).isTopologicalSpace] (leg W) := by
    intro W
    let i := W.property.choose
    have hWi : W.obj ≤ i.1 := W.property.choose_spec
    have hfun : ⇑(leg W) = (G.map (homOfLE hWi).op).1 ∘ (η.app (op i.1)).hom ∘
        (F.map (homOfLE i.2.2).op).hom := by
      funext s
      exact congrArg (fun g => g.hom s) (hnat hWi i.2.2)
    rw [hfun]
    have h₁ := continuous_pseudoDiscreteTopology_restrict F i.2.1 i.2.2
    have h₂ : Continuous[⊥, (G.obj (op i.1)).isTopologicalSpace] (η.app (op i.1)).hom :=
      continuous_bot
    exact @Continuous.comp _ _ _ (pseudoDiscreteTopology F U) (G.obj (op i.1)).isTopologicalSpace
      (G.obj (op W.obj)).isTopologicalSpace _ _ (G.map (homOfLE hWi).op).2
      (@Continuous.comp _ _ _ (pseudoDiscreteTopology F U) ⊥ (G.obj (op i.1)).isTopologicalSpace
        _ _ h₂ h₁)
  let c : Cone ((ObjectProperty.ι _ : OpensLeCover cover ⥤ Opens X).op ⋙ G) :=
    { pt := pseudoDiscreteObj F U
      π :=
        { app := fun W => ⟨leg W.unop, hcont W.unop⟩
          naturality := by
            intro W W' f
            refine Subtype.ext (RingHom.ext fun s => ?_)
            exact (congrArg (fun g => g.hom s)
              (hnat (leOfHom f.unop.hom) (hle W.unop))).trans rfl } }
  let lim := (hG.isSheafOpensLeCover cover).some
  have hsup : U ≤ iSup cover := (iSup_compactOpenLE U).ge
  have hGr : TopCat.Presheaf.IsSheaf (G ⋙ forget₂ TopCommRingCat CommRingCat) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ hG
  have key : ⇑(η.app (op U)).hom = (G.map (homOfLE hsup).op).1 ∘ (lim.lift c).1 := by
    funext s
    refine TopCat.Sheaf.eq_of_locally_eq'
      (⟨G ⋙ forget₂ TopCommRingCat CommRingCat, hGr⟩ : TopCat.Sheaf CommRingCat X) cover U
      (fun V => homOfLE V.2.2) hsup _ _ fun V => ?_
    let W : OpensLeCover cover := ⟨V.1, V, le_rfl⟩
    have hfac : (G.map ((opensLeCoverCocone cover).ι.app W).op).1 ((lim.lift c).1 s) = leg W s :=
      congrArg (fun g => g.1 s) (lim.fac c (op W))
    have hL : ((G ⋙ forget₂ TopCommRingCat CommRingCat).map (homOfLE V.2.2).op).hom
        ((η.app (op U)).hom s) = leg W s :=
      (congrArg (fun g => g.hom s) (η.naturality (homOfLE V.2.2).op)).symm
    have hR : ((G ⋙ forget₂ TopCommRingCat CommRingCat).map (homOfLE V.2.2).op).hom
        ((G.map (homOfLE hsup).op).1 ((lim.lift c).1 s)) = leg W s :=
      (congrArg (fun g => g.1 ((lim.lift c).1 s))
        (G.map_comp (homOfLE hsup).op (homOfLE V.2.2).op)).symm.trans hfac
    exact hL.trans hR.symm
  rw [key]
  exact @Continuous.comp _ _ _ (pseudoDiscreteTopology F U)
    (G.obj (op (iSup cover))).isTopologicalSpace (G.obj (op U)).isTopologicalSpace _ _
    (G.map (homOfLE hsup).op).2 (lim.lift c).2

/-- Forgetting the topology of the pseudo-discretisation gives back the presheaf of rings. -/
def pseudoDiscreteCompForgetIso (F : X.Presheaf CommRingCat.{u}) :
    pseudoDiscrete F ⋙ forget₂ TopCommRingCat CommRingCat ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable (X) in
/-- Pseudo-discretisation as a functor from sheaves of rings to sheaves of topological rings. -/
def pseudoDiscreteSheafFunctor :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) TopCommRingCat.{u} :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ pseudoDiscreteFunctor)
    fun F => isSheaf_pseudoDiscrete_of_isSheaf F.obj F.property

variable (X) in
/-- Forgetting the topology of a sheaf of topological rings. -/
noncomputable abbrev sheafForgetTopology :
    Sheaf (Opens.grothendieckTopology X) TopCommRingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  sheafCompose _ (forget₂ TopCommRingCat CommRingCat)

/-- The bijection between morphisms out of a pseudo-discretisation and morphisms into the
underlying sheaf of rings. -/
noncomputable def pseudoDiscreteSheafHomEquiv
    (F : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (G : Sheaf (Opens.grothendieckTopology X) TopCommRingCat.{u}) :
    ((pseudoDiscreteSheafFunctor X).obj F ⟶ G) ≃ (F ⟶ (sheafForgetTopology X).obj G) where
  toFun φ := ObjectProperty.homMk
    ((pseudoDiscreteCompForgetIso F.obj).inv ≫
      Functor.whiskerRight φ.hom (forget₂ TopCommRingCat CommRingCat))
  invFun ψ := ObjectProperty.homMk
    { app := fun U => ⟨(ψ.hom.app U).hom, continuous_app_of_isSheaf F.obj G.property ψ.hom U.unop⟩
      naturality := fun _ _ i => Subtype.ext (congrArg CommRingCat.Hom.hom (ψ.hom.naturality i)) }
  left_inv φ := by
    ext
    rfl
  right_inv ψ := by
    ext
    rfl

/-- **Stacks 0AHY**: on a space with a basis of quasi-compact opens, pseudo-discretisation of
sheaves of rings is left adjoint to the forgetful functor from sheaves of topological rings to
sheaves of rings. -/
@[stacks 0AHY "the pseudo-discrete construction is adjoint to the forgetful functor"]
noncomputable def pseudoDiscreteSheafAdjunction :
    pseudoDiscreteSheafFunctor X ⊣ sheafForgetTopology X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pseudoDiscreteSheafHomEquiv
      homEquiv_naturality_left_symm := by
        intros
        ext
        rfl
      homEquiv_naturality_right := by
        intros
        ext
        rfl }

variable (X) in
/-- The full subcategory of pseudo-discrete sheaves of topological rings. -/
abbrev PseudoDiscreteSheaf :=
  ObjectProperty.FullSubcategory
    fun G : Sheaf (Opens.grothendieckTopology X) TopCommRingCat.{u} => IsPseudoDiscrete G.obj

/-- On the sections of a pseudo-discrete sheaf of topological rings, the given topology is the
pseudo-discrete topology of the underlying sheaf of rings. -/
theorem pseudoDiscreteTopology_eq_of_isPseudoDiscrete {G : X.Presheaf TopCommRingCat.{u}}
    (hG : G.IsSheaf) (hpd : IsPseudoDiscrete G) (U : Opens X) :
    pseudoDiscreteTopology (G ⋙ forget₂ TopCommRingCat CommRingCat) U =
      (G.obj (op U)).isTopologicalSpace := by
  refine le_antisymm ?_ ?_
  · exact continuous_id_iff_le.1
      (by exact continuous_app_of_isSheaf _ hG (𝟙 (G ⋙ forget₂ TopCommRingCat CommRingCat)) U)
  · refine le_iInf fun V => continuous_iff_le_induced.1 ?_
    have hV := hpd V.1 V.2.1
    exact @Continuous.comp _ _ _ (G.obj (op U)).isTopologicalSpace
      (G.obj (op V.1)).isTopologicalSpace ⊥ _ id (continuous_id_of_le hV.eq_bot.le)
      (G.map (homOfLE V.2.2).op).2

/-- The isomorphism between a pseudo-discrete sheaf of topological rings and the
pseudo-discretisation of its underlying sheaf of rings. -/
noncomputable def pseudoDiscreteForgetIso (G : PseudoDiscreteSheaf X) :
    (pseudoDiscreteSheafFunctor X).obj ((sheafForgetTopology X).obj G.obj) ≅ G.obj :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun U =>
      { hom := ⟨RingHom.id _, by
          have := pseudoDiscreteTopology_eq_of_isPseudoDiscrete G.obj.property G.property U.unop
          exact continuous_id_of_le this.le⟩
        inv := ⟨RingHom.id _, by
          have := pseudoDiscreteTopology_eq_of_isPseudoDiscrete G.obj.property G.property U.unop
          exact continuous_id_of_le this.ge⟩
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

variable (X) in
/-- **Stacks 0AHY**: on a space with a basis of quasi-compact opens, pseudo-discretisation is an
equivalence between the category of sheaves of rings and the category of pseudo-discrete sheaves
of topological rings; its inverse forgets the topology. -/
@[stacks 0AHY "equivalence between sheaves of rings and pseudo-discrete sheaves of topological \
rings"]
noncomputable def pseudoDiscreteSheafEquivalence :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} ≌ PseudoDiscreteSheaf X :=
  CategoryTheory.Equivalence.mk
    (ObjectProperty.lift
      (fun G : Sheaf (Opens.grothendieckTopology X) TopCommRingCat.{u} => IsPseudoDiscrete G.obj)
      (pseudoDiscreteSheafFunctor X) fun F => isPseudoDiscrete_pseudoDiscrete F.obj)
    (ObjectProperty.ι
      (fun G : Sheaf (Opens.grothendieckTopology X) TopCommRingCat.{u} => IsPseudoDiscrete G.obj) ⋙
        sheafForgetTopology X)
    (NatIso.ofComponents
      (fun F => ObjectProperty.isoMk _ (pseudoDiscreteCompForgetIso F.obj).symm)
      (fun _ => by ext; rfl))
    (NatIso.ofComponents (fun G => ObjectProperty.isoMk _ (pseudoDiscreteForgetIso G))
      (fun _ => by ext; rfl))

end AlgebraicGeometry

end

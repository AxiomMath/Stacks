module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.PseudoDiscreteEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-discrete sheaves of topological spaces

Let `X` be a topological space with a basis of quasi-compact opens. The source (Stacks,
Section 87.2, Tag 0AHY) endows every sheaf of sets `𝓕` on `X` with the structure of a sheaf of
topological spaces: the sections over a quasi-compact open are discrete, and the sections over an
arbitrary open `U` carry the topology induced from the product of the sections over the
quasi-compact opens contained in `U`. It states that this construction "is an adjoint to the
forgetful functor and induces an equivalence between the category of sheaves of sets and the
category of pseudo-discrete sheaves of topological spaces". This file proves both statements; the
case of sheaves of rings is `StacksFrontier.AlgebraicGeometry.FormalScheme.PseudoDiscreteEquivalence`.

## Main definitions

* `AlgebraicGeometry.pseudoDiscreteTopologySet`: the pseudo-discrete topology on the sections of
  a presheaf of sets.
* `AlgebraicGeometry.pseudoDiscreteSet`: the pseudo-discrete presheaf of topological spaces.
* `AlgebraicGeometry.pseudoDiscreteSetSheafAdjunction`: pseudo-discretisation of sheaves of sets
  is left adjoint to forgetting the topology.
* `AlgebraicGeometry.pseudoDiscreteSetSheafEquivalence`: it is an equivalence between sheaves of
  sets and pseudo-discrete sheaves of topological spaces.

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

variable {X : TopCat.{u}}

/-! ### The pseudo-discrete topology on the sections of a presheaf of sets -/

/-- A presheaf of topological spaces is *pseudo-discrete* when its space of sections over every
quasi-compact open is discrete. -/
def IsPseudoDiscreteTop (G : X.Presheaf TopCat.{u}) : Prop :=
  ∀ U : Opens X, IsCompact (U : Set X) → DiscreteTopology (G.obj (op U))

/-- The *pseudo-discrete topology* on the sections of a presheaf of sets over an open `U`: the
topology induced from the product of the discrete topologies on the sections over the
quasi-compact opens contained in `U`, written as an infimum of induced topologies. -/
@[instance_reducible]
def pseudoDiscreteTopologySet (F : X.Presheaf (Type u)) (U : Opens X) :
    TopologicalSpace (F.obj (op U)) :=
  ⨅ V : CompactOpenLE U, TopologicalSpace.induced (F.map (homOfLE V.2.2).op) ⊥

/-- Restriction to a quasi-compact open is continuous for the pseudo-discrete topology on the
source and the discrete topology on the target. -/
theorem continuous_pseudoDiscreteTopologySet_restrict (F : X.Presheaf (Type u))
    {U V : Opens X} (hV : IsCompact (V : Set X)) (hVU : V ≤ U) :
    Continuous[pseudoDiscreteTopologySet F U, ⊥] (F.map (homOfLE hVU).op) :=
  continuous_iff_le_induced.2
    (iInf_le (fun W : CompactOpenLE U => TopologicalSpace.induced (F.map (homOfLE W.2.2).op) ⊥)
      ⟨V, hV, hVU⟩)

/-- The pseudo-discrete topology on the sections over a quasi-compact open is discrete. -/
theorem pseudoDiscreteTopologySet_eq_bot (F : X.Presheaf (Type u)) {U : Opens X}
    (hU : IsCompact (U : Set X)) : pseudoDiscreteTopologySet F U = ⊥ := by
  have hid : ⇑(F.map (homOfLE (le_refl U)).op) = id :=
    funext fun a => F.map_id_apply (op U) a
  refine le_antisymm ((continuous_iff_le_induced.1
    (continuous_pseudoDiscreteTopologySet_restrict F hU le_rfl)).trans_eq ?_) bot_le
  rw [hid]
  exact @induced_id _ ⊥

/-- Restriction between arbitrary opens is continuous for the pseudo-discrete topologies. -/
theorem continuous_pseudoDiscreteTopologySet_map (F : X.Presheaf (Type u)) {U V : Opens X}
    (h : V ≤ U) :
    Continuous[pseudoDiscreteTopologySet F U, pseudoDiscreteTopologySet F V]
      (F.map (homOfLE h).op) := by
  refine continuous_iInf_rng.2 fun W => continuous_induced_rng.2 ?_
  have hfun : ⇑(F.map (homOfLE W.2.2).op) ∘ ⇑(F.map (homOfLE h).op)
      = ⇑(F.map (homOfLE (W.2.2.trans h)).op) := by
    funext s
    exact (F.map_comp_apply _ _ s).symm
  rw [hfun]
  exact continuous_pseudoDiscreteTopologySet_restrict F W.2.1 (W.2.2.trans h)

/-- A morphism of presheaves of sets is continuous for the pseudo-discrete topologies. -/
theorem continuous_pseudoDiscreteTopologySet_app {F G : X.Presheaf (Type u)} (η : F ⟶ G)
    (U : Opens X) :
    Continuous[pseudoDiscreteTopologySet F U, pseudoDiscreteTopologySet G U] (η.app (op U)) := by
  refine continuous_iInf_rng.2 fun V => continuous_induced_rng.2 ?_
  have hfun : ⇑(G.map (homOfLE V.2.2).op) ∘ ⇑(η.app (op U))
      = ⇑(η.app (op V.1)) ∘ ⇑(F.map (homOfLE V.2.2).op) := by
    funext s
    exact (NatTrans.naturality_apply η (homOfLE V.2.2).op s).symm
  rw [hfun]
  exact @Continuous.comp _ _ _ (pseudoDiscreteTopologySet F U) ⊥ ⊥ _ _ continuous_bot
    (continuous_pseudoDiscreteTopologySet_restrict F V.2.1 V.2.2)

/-! ### The pseudo-discrete presheaf of topological spaces -/

/-- A continuous map between topological spaces, as a morphism of `TopCat`. -/
abbrev topCatHom {A B : TopCat.{u}} (f : A → B) (hf : Continuous f) : A ⟶ B :=
  TopCat.ofHom ⟨f, hf⟩

/-- The sections of a presheaf of sets over `U`, as a topological space with the pseudo-discrete
topology. -/
def pseudoDiscreteSetObj (F : X.Presheaf (Type u)) (U : Opens X) : TopCat.{u} :=
  @TopCat.of (F.obj (op U)) (pseudoDiscreteTopologySet F U)

/-- The *pseudo-discrete presheaf of topological spaces* attached to a presheaf of sets: the same
sets of sections and restriction maps, with the pseudo-discrete topology on each set of
sections. -/
def pseudoDiscreteSet (F : X.Presheaf (Type u)) : X.Presheaf TopCat.{u} where
  obj U := pseudoDiscreteSetObj F U.unop
  map i := topCatHom (A := pseudoDiscreteSetObj F _) (B := pseudoDiscreteSetObj F _) (F.map i)
    (continuous_pseudoDiscreteTopologySet_map F (leOfHom i.unop))
  map_id U := by
    ext s
    exact F.map_id_apply U s
  map_comp f g := by
    ext s
    exact F.map_comp_apply f g s

/-- The pseudo-discretisation is pseudo-discrete. -/
theorem isPseudoDiscreteTop_pseudoDiscreteSet (F : X.Presheaf (Type u)) :
    IsPseudoDiscreteTop (pseudoDiscreteSet F) :=
  fun _ hU => ⟨pseudoDiscreteTopologySet_eq_bot F hU⟩

/-- Pseudo-discretisation as a functor from presheaves of sets to presheaves of topological
spaces. -/
def pseudoDiscreteSetFunctor : X.Presheaf (Type u) ⥤ X.Presheaf TopCat.{u} where
  obj F := pseudoDiscreteSet F
  map η :=
    { app := fun U => topCatHom (A := pseudoDiscreteSetObj _ _) (B := pseudoDiscreteSetObj _ _)
        (η.app U) (continuous_pseudoDiscreteTopologySet_app η U.unop)
      naturality := fun _ _ i => by
        ext s
        exact NatTrans.naturality_apply η i s }

/-- Forgetting the topology of the pseudo-discretisation gives back the presheaf of sets. -/
def pseudoDiscreteSetCompForgetIso (F : X.Presheaf (Type u)) :
    pseudoDiscreteSet F ⋙ forget TopCat.{u} ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-! ### The sheaf condition -/

variable [PrespectralSpace X]

/-- A function out of a topological space into the sections of a sheaf of sets over the union of
an open covering is continuous for the pseudo-discrete topology as soon as its composites with the
restrictions to the members of the covering are continuous for the pseudo-discrete topologies. -/
theorem continuous_pseudoDiscreteSet_gluing_of_isSheaf (F : X.Presheaf (Type u))
    (hF : F.IsSheaf) {ι : Type u} (cover : ι → Opens X) {T : Type u} [TopologicalSpace T]
    (glue : T → F.obj (op (iSup cover)))
    (hglue : ∀ V : OpensLeCover cover,
      Continuous[_, pseudoDiscreteTopologySet F V.obj]
        (F.map (homOfLE (V.property.choose_spec.trans
          (le_iSup cover V.property.choose))).op ∘ glue)) :
    Continuous[_, pseudoDiscreteTopologySet F (iSup cover)] glue := by
  refine continuous_iInf_rng.2 fun compactOpen => continuous_induced_rng.2 ?_
  let _ : ∀ V, TopologicalSpace (F.obj V) := fun _ => ⊥
  let patches := {V : OpensLeCover cover //
    IsCompact (V.obj : Set X) ∧ V.obj ≤ compactOpen.1}
  have hcover : (compactOpen.1 : Set X) ⊆ ⋃ patch : patches, (patch.1.obj : Set X) := by
    intro point hpoint
    obtain ⟨index, hindex⟩ := Opens.mem_iSup.1 (compactOpen.2.2 hpoint)
    obtain ⟨small, ⟨hopen, hcompact⟩, hpointSmall, hsmall⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open
        (show point ∈ (compactOpen.1 ⊓ cover index : Opens X) from ⟨hpoint, hindex⟩)
        (compactOpen.1 ⊓ cover index).isOpen
    exact Set.mem_iUnion.2 ⟨⟨⟨⟨small, hopen⟩, index, fun _ hx => (hsmall hx).2⟩,
      hcompact, fun _ hx => (hsmall hx).1⟩, hpointSmall⟩
  obtain ⟨finitePatches, hfiniteCover⟩ := compactOpen.2.1.elim_finite_subcover
    (fun patch : patches => (patch.1.obj : Set X)) (fun patch => patch.1.obj.isOpen) hcover
  let toPatch : ∀ patch : patches, T → F.obj (op patch.1.obj) := fun patch =>
    F.map (homOfLE (patch.1.property.choose_spec.trans
      (le_iSup cover patch.1.property.choose))).op ∘ glue
  let restriction := F.map (homOfLE compactOpen.2.2).op ∘ glue
  change Continuous restriction
  refine continuous_iff_continuousAt.2 fun t => ?_
  refine Filter.EventuallyEq.continuousAt (y := restriction t) ?_
  have heventually : ∀ patch ∈ finitePatches,
      ∀ᶠ t' in 𝓝 t, toPatch patch t' = toPatch patch t := by
    intro patch hpatch
    have hcontinuous := hglue patch.1
    rw [pseudoDiscreteTopologySet_eq_bot F patch.2.1] at hcontinuous
    exact (hcontinuous.isOpen_preimage {_}
      (@isOpen_discrete _ ⊥ (discreteTopology_bot _) _)).mem_nhds (Set.mem_singleton _)
  filter_upwards [(finitePatches.eventually_all).2 heventually] with t' ht'
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨F, hF⟩ : TopCat.Sheaf (Type u) X)
    (fun patch : ↥finitePatches => patch.1.1.obj) compactOpen.1
    (fun patch => homOfLE patch.1.2.2) ?_ (restriction t') (restriction t) ?_
  · intro point hpoint
    obtain ⟨patch, hpointPatch⟩ := Set.mem_iUnion.1 (hfiniteCover hpoint)
    obtain ⟨hmem, hpointPatch⟩ := Set.mem_iUnion.1 hpointPatch
    exact Opens.mem_iSup.2 ⟨⟨patch, hmem⟩, hpointPatch⟩
  · intro patch
    have hcomp : ∀ t'', F.map (homOfLE patch.1.2.2).op (restriction t'') =
        toPatch patch.1 t'' := fun t'' =>
      (F.map_comp_apply _ _ (glue t'')).symm
    exact (hcomp t').trans ((ht' patch.1 patch.2).trans (hcomp t).symm)

/-- On a space with a basis of quasi-compact opens, the pseudo-discrete presheaf of topological
spaces attached to a sheaf of sets is a sheaf of topological spaces. -/
theorem isSheaf_pseudoDiscreteSet_of_isSheaf (F : X.Presheaf (Type u)) (hF : F.IsSheaf) :
    (pseudoDiscreteSet F).IsSheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover _).2 fun ι cover => ?_
  let setLimit := (hF.isSheafOpensLeCover cover).some
  refine ⟨IsLimit.mk (fun cone => topCatHom (B := pseudoDiscreteSetObj F (iSup cover))
    (setLimit.lift ((forget TopCat).mapCone cone)) ?_) (fun cone V => ?_) ?_⟩
  · refine continuous_pseudoDiscreteSet_gluing_of_isSheaf F hF cover _ fun V => ?_
    have hfac : ⇑(F.map ((opensLeCoverCocone cover).ι.app V).op) ∘
        ⇑(setLimit.lift ((forget TopCat).mapCone cone)) = ⇑((cone.π.app (op V)).hom) := by
      funext t
      exact congrArg (fun g => g t) (setLimit.fac ((forget TopCat).mapCone cone) (op V))
    exact hfac ▸ (cone.π.app (op V)).hom.continuous
  · ext t
    exact congrArg (fun g => g t) (setLimit.fac ((forget TopCat).mapCone cone) V)
  · intro cone morphism hfac
    ext t
    exact congrArg (fun g => g t) (setLimit.uniq ((forget TopCat).mapCone cone)
      ((forget TopCat).map morphism) fun V => congrArg (forget TopCat).map (hfac V))

/-! ### The adjunction and the equivalence -/

/-- **A morphism of presheaves of sets into a sheaf of topological spaces is continuous for the
pseudo-discrete topology.** -/
theorem continuous_app_of_isSheaf_topCat (F : X.Presheaf (Type u))
    {G : X.Presheaf TopCat.{u}} (hG : G.IsSheaf) (η : F ⟶ G ⋙ forget TopCat.{u})
    (U : Opens X) :
    Continuous[pseudoDiscreteTopologySet F U, (G.obj (op U)).str] (η.app (op U)) := by
  let cover : CompactOpenLE U → Opens X := fun V => V.1
  have hle : ∀ W : OpensLeCover cover, W.obj ≤ U :=
    fun W => W.property.choose_spec.trans W.property.choose.2.2
  let leg : ∀ W : OpensLeCover cover, F.obj (op U) → G.obj (op W.obj) := fun W =>
    η.app (op W.obj) ∘ F.map (homOfLE (hle W)).op
  have hnat : ∀ {V W : Opens X} (hWV : W ≤ V) (hVU : V ≤ U) (s : F.obj (op U)),
      η.app (op W) (F.map (homOfLE (hWV.trans hVU)).op s) =
        G.map (homOfLE hWV).op (η.app (op V) (F.map (homOfLE hVU).op s)) := by
    intro V W hWV hVU s
    rw [show (homOfLE (hWV.trans hVU)).op = (homOfLE hVU).op ≫ (homOfLE hWV).op from rfl,
      F.map_comp_apply]
    exact NatTrans.naturality_apply η (homOfLE hWV).op _
  have hcont : ∀ W : OpensLeCover cover,
      Continuous[pseudoDiscreteTopologySet F U, (G.obj (op W.obj)).str] (leg W) := by
    intro W
    let i := W.property.choose
    have hWi : W.obj ≤ i.1 := W.property.choose_spec
    have hfun : leg W = G.map (homOfLE hWi).op ∘ η.app (op i.1) ∘ F.map (homOfLE i.2.2).op := by
      funext s
      exact hnat hWi i.2.2 s
    rw [hfun]
    have h₁ := continuous_pseudoDiscreteTopologySet_restrict F i.2.1 i.2.2
    have h₂ : Continuous[⊥, (G.obj (op i.1)).str] (η.app (op i.1)) := continuous_bot
    exact @Continuous.comp _ _ _ (pseudoDiscreteTopologySet F U) (G.obj (op i.1)).str
      (G.obj (op W.obj)).str _ _ (G.map (homOfLE hWi).op).hom.continuous
      (@Continuous.comp _ _ _ (pseudoDiscreteTopologySet F U) ⊥ (G.obj (op i.1)).str
        _ _ h₂ h₁)
  let c : Cone ((ObjectProperty.ι _ : OpensLeCover cover ⥤ Opens X).op ⋙ G) :=
    { pt := pseudoDiscreteSetObj F U
      π :=
        { app := fun W => topCatHom (A := pseudoDiscreteSetObj F U) (leg W.unop) (hcont W.unop)
          naturality := by
            intro W W' f
            ext s
            exact hnat (leOfHom f.unop.hom) (hle W.unop) s } }
  let lim := (hG.isSheafOpensLeCover cover).some
  have hsup : U ≤ iSup cover := (iSup_compactOpenLE U).ge
  have hGr : TopCat.Presheaf.IsSheaf (G ⋙ forget TopCat.{u}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ hG
  have key : ⇑(η.app (op U)) = G.map (homOfLE hsup).op ∘ lim.lift c := by
    funext s
    refine TopCat.Sheaf.eq_of_locally_eq'
      (⟨G ⋙ forget TopCat.{u}, hGr⟩ : TopCat.Sheaf (Type u) X) cover U
      (fun V => homOfLE V.2.2) hsup _ _ fun V => ?_
    let W : OpensLeCover cover := ⟨V.1, V, le_rfl⟩
    have hfac : G.map ((opensLeCoverCocone cover).ι.app W).op (lim.lift c s) = leg W s :=
      congrArg (fun g => g s) (lim.fac c (op W))
    have hL : G.map (homOfLE V.2.2).op (η.app (op U) s) = leg W s :=
      (NatTrans.naturality_apply η (homOfLE V.2.2).op s).symm
    have hR : G.map (homOfLE V.2.2).op (G.map (homOfLE hsup).op (lim.lift c s)) = leg W s :=
      (congrArg (fun g => g (lim.lift c s))
        (G.map_comp (homOfLE hsup).op (homOfLE V.2.2).op)).symm.trans hfac
    exact hL.trans hR.symm
  rw [key]
  exact @Continuous.comp _ _ _ (pseudoDiscreteTopologySet F U)
    (G.obj (op (iSup cover))).str (G.obj (op U)).str _ _
    (G.map (homOfLE hsup).op).hom.continuous (lim.lift c).hom.continuous

variable (X) in
/-- Pseudo-discretisation as a functor from sheaves of sets to sheaves of topological spaces. -/
def pseudoDiscreteSetSheafFunctor :
    Sheaf (Opens.grothendieckTopology X) (Type u) ⥤
      Sheaf (Opens.grothendieckTopology X) TopCat.{u} :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ pseudoDiscreteSetFunctor)
    fun F => isSheaf_pseudoDiscreteSet_of_isSheaf F.obj F.property

variable (X) in
/-- Forgetting the topology of a sheaf of topological spaces. -/
noncomputable abbrev sheafForgetTopCat :
    Sheaf (Opens.grothendieckTopology X) TopCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) (Type u) :=
  sheafCompose _ (forget TopCat.{u})

/-- The bijection between morphisms out of a pseudo-discretisation and morphisms into the
underlying sheaf of sets. -/
noncomputable def pseudoDiscreteSetSheafHomEquiv
    (F : Sheaf (Opens.grothendieckTopology X) (Type u))
    (G : Sheaf (Opens.grothendieckTopology X) TopCat.{u}) :
    ((pseudoDiscreteSetSheafFunctor X).obj F ⟶ G) ≃ (F ⟶ (sheafForgetTopCat X).obj G) where
  toFun φ := ObjectProperty.homMk
    ((pseudoDiscreteSetCompForgetIso F.obj).inv ≫ Functor.whiskerRight φ.hom (forget TopCat))
  invFun ψ := ObjectProperty.homMk
    { app := fun U => topCatHom (A := pseudoDiscreteSetObj F.obj U.unop) (ψ.hom.app U)
        (continuous_app_of_isSheaf_topCat F.obj G.property ψ.hom U.unop)
      naturality := fun _ _ i => by
        ext s
        exact NatTrans.naturality_apply ψ.hom i s }
  left_inv φ := by
    ext
    rfl
  right_inv ψ := by
    ext
    rfl

/-- **Stacks 0AHY**: on a space with a basis of quasi-compact opens, pseudo-discretisation of
sheaves of sets is left adjoint to the forgetful functor from sheaves of topological spaces to
sheaves of sets. -/
@[stacks 0AHY "the pseudo-discrete construction on sheaves of sets is adjoint to the forgetful \
functor"]
noncomputable def pseudoDiscreteSetSheafAdjunction :
    pseudoDiscreteSetSheafFunctor X ⊣ sheafForgetTopCat X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pseudoDiscreteSetSheafHomEquiv
      homEquiv_naturality_left_symm := by
        intros
        ext
        rfl
      homEquiv_naturality_right := by
        intros
        ext
        rfl }

variable (X) in
/-- The full subcategory of pseudo-discrete sheaves of topological spaces. -/
abbrev PseudoDiscreteTopSheaf :=
  ObjectProperty.FullSubcategory
    fun G : Sheaf (Opens.grothendieckTopology X) TopCat.{u} => IsPseudoDiscreteTop G.obj

/-- On the sections of a pseudo-discrete sheaf of topological spaces, the given topology is the
pseudo-discrete topology of the underlying sheaf of sets. -/
theorem pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteTop {G : X.Presheaf TopCat.{u}}
    (hG : G.IsSheaf) (hpd : IsPseudoDiscreteTop G) (U : Opens X) :
    pseudoDiscreteTopologySet (G ⋙ forget TopCat.{u}) U = (G.obj (op U)).str := by
  refine le_antisymm ?_ ?_
  · exact continuous_id_iff_le.1
      (by exact continuous_app_of_isSheaf_topCat _ hG (𝟙 (G ⋙ forget TopCat.{u})) U)
  · refine le_iInf fun V => continuous_iff_le_induced.1 ?_
    have hV := hpd V.1 V.2.1
    exact @Continuous.comp _ _ _ (G.obj (op U)).str (G.obj (op V.1)).str ⊥ _ id
      (continuous_id_of_le hV.eq_bot.le) (G.map (homOfLE V.2.2).op).hom.continuous

/-- The isomorphism between a pseudo-discrete sheaf of topological spaces and the
pseudo-discretisation of its underlying sheaf of sets. -/
noncomputable def pseudoDiscreteSetForgetIso (G : PseudoDiscreteTopSheaf X) :
    (pseudoDiscreteSetSheafFunctor X).obj ((sheafForgetTopCat X).obj G.obj) ≅ G.obj :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun U =>
      { hom := topCatHom (A := pseudoDiscreteSetObj (G.obj.obj ⋙ forget TopCat) U.unop)
          (B := G.obj.obj.obj U) id (by
            have := pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteTop G.obj.property G.property
              U.unop
            exact continuous_id_of_le this.le)
        inv := topCatHom (A := G.obj.obj.obj U)
          (B := pseudoDiscreteSetObj (G.obj.obj ⋙ forget TopCat) U.unop) id (by
            have := pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteTop G.obj.property G.property
              U.unop
            exact continuous_id_of_le this.ge)
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

variable (X) in
/-- **Stacks 0AHY**: on a space with a basis of quasi-compact opens, pseudo-discretisation is an
equivalence between the category of sheaves of sets and the category of pseudo-discrete sheaves of
topological spaces; its inverse forgets the topology. -/
@[stacks 0AHY "equivalence between sheaves of sets and pseudo-discrete sheaves of topological \
spaces"]
noncomputable def pseudoDiscreteSetSheafEquivalence :
    Sheaf (Opens.grothendieckTopology X) (Type u) ≌ PseudoDiscreteTopSheaf X :=
  CategoryTheory.Equivalence.mk
    (ObjectProperty.lift
      (fun G : Sheaf (Opens.grothendieckTopology X) TopCat.{u} => IsPseudoDiscreteTop G.obj)
      (pseudoDiscreteSetSheafFunctor X) fun F => isPseudoDiscreteTop_pseudoDiscreteSet F.obj)
    (ObjectProperty.ι
      (fun G : Sheaf (Opens.grothendieckTopology X) TopCat.{u} => IsPseudoDiscreteTop G.obj) ⋙
        sheafForgetTopCat X)
    (NatIso.ofComponents
      (fun F => ObjectProperty.isoMk _ (pseudoDiscreteSetCompForgetIso F.obj).symm)
      (fun _ => by ext; rfl))
    (NatIso.ofComponents (fun G => ObjectProperty.isoMk _ (pseudoDiscreteSetForgetIso G))
      (fun _ => by ext; rfl))

end AlgebraicGeometry

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.Topology.Simplicial.Augmentation

/-!
# The constant simplicial topological space

For a topological space `X`, the simplicial site of the constant simplicial space maps to the
site of open subsets of `X`. The resulting geometric morphism has constant cosimplicial inverse
image, degree-zero lower shriek, and direct image given by an equalizer of the two degree-one
maps.

## Main definitions

* `Stacks.Topology.Simplicial.constantSpace`: the constant simplicial space on a space.
* `Stacks.Topology.Simplicial.constantSiteFunctor`: a simplicial open is sent to its underlying
  open of `X`.
* `Stacks.Topology.Simplicial.constantMorphism`: the associated morphism of topoi.
* `Stacks.Topology.Simplicial.constantLowerShriek`: the degree-zero component of a simplicial
  sheaf.
* `Stacks.Topology.Simplicial.constantFaceMap`: the map from the degree-zero sheaf to the
  degree-one sheaf induced by a vertex of the one-simplex.

## Main results

* `Stacks.Topology.Simplicial.constantSiteFunctor_isContinuous` and
  `constantSiteFunctor_isCocontinuous`: the two site properties.
* `Stacks.Topology.Simplicial.constantMorphism_inverseImage_isoRestriction`: the geometric
  inverse image is restriction along the site functor.
* `Stacks.Topology.Simplicial.constantMorphism_inverseImage_component`: inverse image is
  computed degreewise.
* `Stacks.Topology.Simplicial.constantMorphism_inverseImage_transition`: every transition map is
  the identity under the component isomorphisms.
* `Stacks.Topology.Simplicial.constantLowerShriek_adjunction`: lower shriek is the degree-zero
  component.
* `Stacks.Topology.Simplicial.constantMorphism_pushforwardEqualizer`: direct image is computed
  from the two transition maps of the sheaf system.

## Implementation notes

The geometric morphism is the augmentation morphism for the identity augmentation of the
constant simplicial space. Its degreewise inverse-image description is expressed by natural
isomorphisms; these retain naturality in the sheaf. The two maps in the direct-image equalizer
are the two vertex transition maps.

## References

* [Stacks Project, Tag 09W3](https://stacks.math.columbia.edu/tag/09W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Simplicial

universe u

namespace Stacks.Topology.Simplicial

add_to_stacks 09W3 "the morphism of topoi" augmentationMorphism

/-- The constant simplicial topological space on a topological space. -/
abbrev constantSpace (X : TopCat.{u}) : SimplicialObject TopCat.{u} :=
  (SimplicialObject.const TopCat).obj X

/-- The functor from the simplicial-open site of the constant simplicial space to
the site of open subsets of its value. -/
@[stacks 09W3 "the functor on sites"]
def constantSiteFunctor (X : TopCat.{u}) :
    SimplicialOpen (constantSpace X) ⥤ Opens X where
  obj U := U.toOpens
  map f := homOfLE (by simpa using (SimplicialOpen.Hom.le f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

namespace ConstantSpace

/-- The inclusion of degree zero is left adjoint to the constant-site functor. -/
noncomputable def constantSiteLevelAdjunction (X : TopCat.{u}) :
    levelFunctor (constantSpace X) (op ⦋0⦌) ⊣ constantSiteFunctor X := by
  let F := levelFunctor (constantSpace X) (op ⦋0⦌)
  have homUnique (U : Opens X) (V : SimplicialOpen (constantSpace X))
      (f g : F.obj U ⟶ V) : f = g := by
    apply SimplicialOpen.Hom.ext
    apply Quiver.Hom.unop_inj
    exact (SimplexCategory.eq_const_to_zero f.base.unop).trans
      (SimplexCategory.eq_const_to_zero g.base.unop).symm
  refine Adjunction.mkOfHomEquiv {
    homEquiv := fun U V => {
      toFun := fun f => homOfLE (by
        intro x hx
        change x ∈ V.toOpens
        simpa [constantSpace] using SimplicialOpen.Hom.le f hx)
      invFun := fun g => by
        let b : (F.obj U).degree ⟶ V.degree :=
          (SimplexCategory.const V.degree.unop ⦋0⦌ (0 : Fin 1)).op
        refine { base := b, le := ?_ }
        intro x hx
        have h := g.le hx
        dsimp [constantSiteFunctor] at h
        have hb : (constantSpace X).map b = 𝟙 X := by
          change ((Functor.const SimplexCategoryᵒᵖ).obj X).map b = 𝟙 X
          exact Functor.const_obj_map _ _ _
        rwa [hb]
      left_inv := fun f => homUnique U V _ _
      right_inv := fun g => Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm _ _ := homUnique _ _ _ _
    homEquiv_naturality_right _ _ := Subsingleton.elim _ _ }

end ConstantSpace

open ConstantSpace

/-- The constant-site functor preserves sheaves. -/
@[stacks 09W3 "the functor is continuous", instance]
theorem constantSiteFunctor_isContinuous (X : TopCat.{u}) :
    (constantSiteFunctor X).IsContinuous
      (SimplicialOpen.grothendieckTopology (constantSpace X))
      (Opens.grothendieckTopology X) := by
  have : (levelFunctor (constantSpace X) (op ⦋0⦌)).IsCocontinuous
      (Opens.grothendieckTopology X)
      (SimplicialOpen.grothendieckTopology (constantSpace X)) := by
    simpa [constantSpace] using
      (levelFunctor_isCocontinuous_mk (constantSpace X) 0)
  exact (constantSiteLevelAdjunction X).isContinuous_of_isCocontinuous _ _

/-- The constant-site functor lifts covers. -/
@[stacks 09W3 "the functor is cocontinuous", instance]
theorem constantSiteFunctor_isCocontinuous (X : TopCat.{u}) :
    (constantSiteFunctor X).IsCocontinuous
      (SimplicialOpen.grothendieckTopology (constantSpace X))
      (Opens.grothendieckTopology X) := by
  refine ⟨fun {U S} hS => ?_⟩
  let R : Presieve U := fun V f =>
    ∃ e : V.degree = U.degree, f.base = eqToHom e ∧ S ((constantSiteFunctor X).map f)
  have hR : SimplicialOpen.IsCovering U R := by
    refine ⟨fun V f hf => ⟨hf.1, hf.2.1⟩, fun x hx => ?_⟩
    rw [Opens.mem_grothendieckTopology] at hS
    obtain ⟨W, g, hg, hxW⟩ := hS x hx
    let V : SimplicialOpen (constantSpace X) := ⟨U.degree, W⟩
    let f : V ⟶ U :=
      { base := 𝟙 U.degree
        le := by
          dsimp [V]
          have h := g.le
          dsimp [constantSiteFunctor] at h
          simpa [constantSpace] using h }
    have hmap : (constantSiteFunctor X).map f = g := Subsingleton.elim _ _
    refine ⟨V, f, ⟨rfl, rfl, hmap ▸ hg⟩, x, hxW, ?_⟩
    simp [f, constantSpace]
  rw [SimplicialOpen.mem_grothendieckTopology]
  exact ⟨R, hR, fun V f hf => hf.2.2⟩

/-- The canonical geometric morphism for the constant simplicial space. -/
noncomputable abbrev constantMorphism (X : TopCat.{u}) :
    MorphismOfTopoi
      (Sheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) (Type u))
      (TopCat.Sheaf (Type u) X) :=
  (augmentationMorphism (constantSpace X) X (𝟙 _)).toMorphismOfTopoi

/-- The restriction of a reconstructed presheaf along a morphism of simplicial opens is, on
components, the transition map followed by restriction inside the source degree. -/
theorem SheafSystemEquivalence.toPresheaf_map_comp_componentIso_hom
    {Y : SimplicialObject TopCat.{u}} {A : Type*} [Category A]
    (E : SheafSystemEquivalence Y A) (S : SimplicialSheafSystem Y A)
    {U V : SimplicialOpen Y} (g : V ⟶ U) :
    (E.toPresheaf.obj S).map g.op ≫ ((E.componentIso V.degree).app S).hom.app (op V.toOpens) =
      ((E.componentIso U.degree).app S).hom.app (op U.toOpens) ≫
        (S.transition g.base).app (op U.toOpens) ≫
          ((TopCat.Sheaf.forget A (Y.obj V.degree)).obj (S.component V.degree)).map
            (homOfLE (SimplicialOpen.Hom.le g)).op := by
  let W : SimplicialOpen Y := ⟨V.degree, (Opens.map (Y.map g.base)).obj U.toOpens⟩
  let i : V ⟶ W := (levelFunctor Y V.degree).map (homOfLE (SimplicialOpen.Hom.le g))
  let t : W ⟶ U := SimplicialSheafSystem.transitionHom g.base U.toOpens
  have hg : g = i ≫ t := SimplicialOpen.Hom.ext _ _ (Category.id_comp g.base).symm
  have hmap : (E.toPresheaf.obj S).map g.op =
      (E.toPresheaf.obj S).map t.op ≫ (E.toPresheaf.obj S).map i.op := by
    rw [← Functor.map_comp, ← op_comp, ← hg]
  have hβ : (E.toPresheaf.obj S).map i.op ≫
        ((E.componentIso V.degree).app S).hom.app (op V.toOpens) =
      ((E.componentIso V.degree).app S).hom.app
          (op ((Opens.map (Y.map g.base)).obj U.toOpens)) ≫
        ((TopCat.Sheaf.forget A (Y.obj V.degree)).obj (S.component V.degree)).map
          (homOfLE (SimplicialOpen.Hom.le g)).op :=
    ((E.componentIso V.degree).hom.app S).naturality (homOfLE (SimplicialOpen.Hom.le g)).op
  have hE : (E.toPresheaf.obj S).map t.op ≫
        ((E.componentIso V.degree).app S).hom.app
          (op ((Opens.map (Y.map g.base)).obj U.toOpens)) =
      ((E.componentIso U.degree).app S).hom.app (op U.toOpens) ≫
        (S.transition g.base).app (op U.toOpens) :=
    E.transition_compatibility S g.base (op U.toOpens)
  exact (hmap =≫ _).trans <| (Category.assoc _ _ _).trans <| (_ ≫= hβ).trans <|
    (Category.assoc _ _ _).symm.trans <| (hE =≫ _).trans (Category.assoc _ _ _)

/-- Pasting three commuting squares in a row gives a commuting rectangle of triple composites. -/
private theorem comp_comp_comp_comm_of_squares {C : Type*} [Category C]
    {A A' B B' D D' E E' : C} (f : A ⟶ A') (g : E ⟶ E') {a : A ⟶ B} {a' : A' ⟶ B'}
    {b : B ⟶ D} {b' : B' ⟶ D'} {c : D ⟶ E} {c' : D' ⟶ E'} {u : B ⟶ B'} {v : D ⟶ D'}
    (h₁ : f ≫ a' = a ≫ u) (h₂ : u ≫ b' = b ≫ v) (h₃ : v ≫ c' = c ≫ g) :
    f ≫ a' ≫ b' ≫ c' = (a ≫ b ≫ c) ≫ g := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

namespace ConstantSpace

/-- Direct image along an identity map is the identity functor. -/
noncomputable def identityPushforwardIso (X : TopCat.{u}) :
    TopCat.Sheaf.pushforward (Type u) (𝟙 X) ≅ 𝟭 (TopCat.Sheaf (Type u) X) := by
  change (Opens.map (𝟙 X)).sheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology X) ≅ _
  exact Functor.sheafPushforwardContinuousIso (Opens.mapId X) (Type u)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology X) ≪≫
    Functor.sheafPushforwardContinuousId (Type u) (Opens.grothendieckTopology X)

/-- Inverse image along an identity map is the identity functor. -/
noncomputable def identityPullbackIso (X : TopCat.{u}) :
    TopCat.Sheaf.pullback (Type u) (𝟙 X) ≅ 𝟭 (TopCat.Sheaf (Type u) X) :=
  Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 X))
    ((Adjunction.id).ofNatIsoRight (identityPushforwardIso X).symm)

/-- Each component of the inverse image of the constant morphism is the original sheaf. -/
noncomputable def constantInverseImageComponent (X : TopCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    (constantMorphism X).inverseImage ⋙
      (sheafEquivalenceSimplicialSheafSystem (constantSpace X)
        (Type u)).toEquivalence.functor ⋙
        SimplicialSheafSystem.componentFunctor (constantSpace X) (Type u) n ≅
      𝟭 (TopCat.Sheaf (Type u) X) :=
  augmentationMorphism_inverseImage_component (constantSpace X) X (𝟙 _) n ≪≫
    identityPullbackIso X

/-- Under `constantInverseImageComponent`, every transition map of the inverse image becomes an
identity. -/
theorem constantInverseImageTransition (X : TopCat.{u})
    (F : TopCat.Sheaf (Type u) X) {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (V : (Opens X)ᵒᵖ) :
    let S := (sheafEquivalenceSimplicialSheafSystem (constantSpace X)
        (Type u)).toEquivalence.functor.obj
        ((constantMorphism X).inverseImage.obj F)
    (S.transition φ).app V ≫
      ((TopCat.Sheaf.forget (Type u) X).map
        ((constantInverseImageComponent X n).app F).hom).app
        (op ((Opens.map (𝟙 X)).obj V.unop)) =
      ((TopCat.Sheaf.forget (Type u) X).map
        ((constantInverseImageComponent X m).app F).hom).app V := by
  have h := augmentationMorphism_inverseImage_transition
    (constantSpace X) X (𝟙 _) F φ V
  have ht : (augmentationPullbackTransition (constantSpace X) X (𝟙 _) F φ).app V =
      𝟙 (((TopCat.Sheaf.pullback (Type u) (𝟙 X)).obj F).obj.obj V) := by
    change (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 X)).homEquiv F
      ((TopCat.Sheaf.pullback (Type u) (𝟙 X)).obj F)).symm
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 X)).unit.app F ≫
          eqToHom (by rfl))).hom.app V = _
    simp only [eqToHom_refl, Category.comp_id, Adjunction.homEquiv_symm_unit]
    rfl
  simp only [ht] at h
  exact congrArg (fun f => f ≫
      ((TopCat.Sheaf.forget (Type u) X).map
        ((identityPullbackIso X).app F).hom).app V) h

/-- The component at a simplicial open of the identification of the inverse image of a sheaf
with its restriction along the constant-site functor. -/
noncomputable def inverseImageRestrictionAppIso (X : TopCat.{u}) (F : TopCat.Sheaf (Type u) X)
    (U : (SimplicialOpen (constantSpace X))ᵒᵖ) :
    ((sheafToPresheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) (Type u)).obj
        ((constantMorphism X).inverseImage.obj F)).obj U ≅
      ((sheafToPresheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) (Type u)).obj
        (((constantSiteFunctor X).sheafPushforwardContinuous (Type u)
          (SimplicialOpen.grothendieckTopology (constantSpace X))
          (Opens.grothendieckTopology X)).obj F)).obj U :=
  (((sheafEquivalenceSimplicialSheafSystem (constantSpace X) (Type u)).underlyingPresheafIso.app
      ((constantMorphism X).inverseImage.obj F)).app U).symm ≪≫
    (((sheafEquivalenceSimplicialSheafSystem (constantSpace X) (Type u)).componentIso
      U.unop.degree).app ((sheafEquivalenceSimplicialSheafSystem (constantSpace X)
        (Type u)).toEquivalence.functor.obj ((constantMorphism X).inverseImage.obj F))).app
      (op U.unop.toOpens) ≪≫
    ((TopCat.Sheaf.forget (Type u) ((constantSpace X).obj U.unop.degree)).mapIso
      ((constantInverseImageComponent X U.unop.degree).app F)).app (op U.unop.toOpens)

/-- `inverseImageRestrictionAppIso` is natural in the simplicial open. -/
theorem inverseImageRestrictionAppIso_naturality (X : TopCat.{u}) (F : TopCat.Sheaf (Type u) X)
    {U V : (SimplicialOpen (constantSpace X))ᵒᵖ} (f : U ⟶ V) :
    ((sheafToPresheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) (Type u)).obj
        ((constantMorphism X).inverseImage.obj F)).map f ≫
        (inverseImageRestrictionAppIso X F V).hom =
      (inverseImageRestrictionAppIso X F U).hom ≫
        ((sheafToPresheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) (Type u)).obj
          (((constantSiteFunctor X).sheafPushforwardContinuous (Type u)
            (SimplicialOpen.grothendieckTopology (constantSpace X))
            (Opens.grothendieckTopology X)).obj F)).map f := by
  let E := sheafEquivalenceSimplicialSheafSystem (constantSpace X) (Type u)
  let I := (constantMorphism X).inverseImage.obj F
  let S := E.toEquivalence.functor.obj I
  let n := V.unop.degree
  let W := (Opens.map ((constantSpace X).map f.unop.base)).obj U.unop.toOpens
  let h : op W ⟶ op V.unop.toOpens := (homOfLE (SimplicialOpen.Hom.le f.unop)).op
  let γ := fun (k : SimplexCategoryᵒᵖ) (O : Opens ((constantSpace X).obj k)) =>
    ((TopCat.Sheaf.forget (Type u) ((constantSpace X).obj k)).map
      ((constantInverseImageComponent X k).app F).hom).app (op O)
  have hα : ((sheafToPresheaf _ (Type u)).obj I).map f ≫
        ((E.underlyingPresheafIso.app I).app V).inv =
      ((E.underlyingPresheafIso.app I).app U).inv ≫ (E.toPresheaf.obj S).map f :=
    (E.underlyingPresheafIso.app I).inv.naturality f
  have hβ := E.toPresheaf_map_comp_componentIso_hom S f.unop
  rw [Quiver.Hom.op_unop] at hβ
  have hγ : ((TopCat.Sheaf.forget (Type u) ((constantSpace X).obj n)).obj (S.component n)).map h ≫
      γ n V.unop.toOpens =
      γ n W ≫ ((TopCat.Sheaf.forget (Type u) ((constantSpace X).obj n)).obj F).map h :=
    ((TopCat.Sheaf.forget (Type u) ((constantSpace X).obj n)).map
      ((constantInverseImageComponent X n).app F).hom).naturality h
  have hT : (S.transition f.unop.base).app (op U.unop.toOpens) ≫ γ n W =
      γ U.unop.degree U.unop.toOpens :=
    constantInverseImageTransition X F f.unop.base (op U.unop.toOpens)
  exact comp_comp_comp_comm_of_squares _ _ hα hβ
    ((Category.assoc _ _ _).trans <| (_ ≫= hγ).trans <|
      (Category.assoc _ _ _).symm.trans (hT =≫ _))

/-- `inverseImageRestrictionAppIso` is natural in the sheaf. -/
theorem inverseImageRestrictionAppIso_natural (X : TopCat.{u}) {F G : TopCat.Sheaf (Type u) X}
    (f : F ⟶ G) (U : (SimplicialOpen (constantSpace X))ᵒᵖ) :
    ((constantMorphism X).inverseImage.map f).hom.app U ≫
        (inverseImageRestrictionAppIso X G U).hom =
      (inverseImageRestrictionAppIso X F U).hom ≫
        (((constantSiteFunctor X).sheafPushforwardContinuous (Type u)
          (SimplicialOpen.grothendieckTopology (constantSpace X))
          (Opens.grothendieckTopology X)).map f).hom.app U := by
  let E := sheafEquivalenceSimplicialSheafSystem (constantSpace X) (Type u)
  let I := (constantMorphism X).inverseImage
  let n := U.unop.degree
  let O := U.unop.toOpens
  let sf := E.toEquivalence.functor.map (I.map f)
  have hα : (I.map f).hom.app U ≫ ((E.underlyingPresheafIso.app (I.obj G)).app U).inv =
      ((E.underlyingPresheafIso.app (I.obj F)).app U).inv ≫ (E.toPresheaf.map sf).app U :=
    congrArg (fun q => q.app U) (E.underlyingPresheafIso.inv.naturality (I.map f))
  have hβ : (E.toPresheaf.map sf).app U ≫
        ((E.componentIso n).app (E.toEquivalence.functor.obj (I.obj G))).hom.app (op O) =
      ((E.componentIso n).app (E.toEquivalence.functor.obj (I.obj F))).hom.app (op O) ≫
        ((SimplicialSheafSystem.componentFunctor (constantSpace X) (Type u) n ⋙
          TopCat.Sheaf.forget (Type u) ((constantSpace X).obj n)).map sf).app (op O) :=
    congrArg (fun q => q.app (op O)) ((E.componentIso n).hom.naturality sf)
  have hγ : ((SimplicialSheafSystem.componentFunctor (constantSpace X) (Type u) n ⋙
        TopCat.Sheaf.forget (Type u) ((constantSpace X).obj n)).map sf).app (op O) ≫
        ((TopCat.Sheaf.forget (Type u) ((constantSpace X).obj n)).map
          ((constantInverseImageComponent X n).app G).hom).app (op O) =
      ((TopCat.Sheaf.forget (Type u) ((constantSpace X).obj n)).map
          ((constantInverseImageComponent X n).app F).hom).app (op O) ≫
        ((TopCat.Sheaf.forget (Type u) ((constantSpace X).obj n)).map f).app (op O) :=
    congrArg (fun q => ((TopCat.Sheaf.forget (Type u) ((constantSpace X).obj n)).map q).app (op O))
      ((constantInverseImageComponent X n).hom.naturality f)
  exact comp_comp_comp_comm_of_squares _ _ hα hβ hγ

end ConstantSpace

/-- The canonical morphism has inverse image given by restriction along the
constant-site functor, naturally in the sheaf. -/
@[stacks 09W3 "inverse image is restriction along the functor"]
noncomputable def constantMorphism_inverseImage_isoRestriction (X : TopCat.{u}) :
    (constantMorphism X).inverseImage ≅
    (constantSiteFunctor X).sheafPushforwardContinuous (Type u)
        (SimplicialOpen.grothendieckTopology (constantSpace X))
        (Opens.grothendieckTopology X) :=
  NatIso.ofComponents
    (fun F => (fullyFaithfulSheafToPresheaf _ (Type u)).preimageIso
      (NatIso.ofComponents (inverseImageRestrictionAppIso X F)
        (fun f => inverseImageRestrictionAppIso_naturality X F f)))
    (fun f => by
      apply (fullyFaithfulSheafToPresheaf _ (Type u)).map_injective
      simp only [Functor.FullyFaithful.preimageIso_hom, Functor.map_comp]
      exact NatTrans.ext (funext fun U => inverseImageRestrictionAppIso_natural X f U))

/-- Inverse image of a sheaf is the same sheaf in every simplicial degree,
naturally in the sheaf. -/
@[stacks 09W3 "part (1): constant cosimplicial inverse image"]
noncomputable def constantMorphism_inverseImage_component (X : TopCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    (constantMorphism X).inverseImage ⋙
      (sheafEquivalenceSimplicialSheafSystem (constantSpace X)
        (Type u)).toEquivalence.functor ⋙
        SimplicialSheafSystem.componentFunctor (constantSpace X) (Type u) n ≅
      𝟭 (TopCat.Sheaf (Type u) X) :=
  constantInverseImageComponent X n

/-- The component identifications respect every cosimplicial transition: the
transition maps of inverse image become identity maps of the original sheaf. -/
@[stacks 09W3 "part (1): constant transition maps"]
theorem constantMorphism_inverseImage_transition (X : TopCat.{u})
    (F : TopCat.Sheaf (Type u) X) {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (V : (Opens X)ᵒᵖ) :
    let S := (sheafEquivalenceSimplicialSheafSystem (constantSpace X)
        (Type u)).toEquivalence.functor.obj
        ((constantMorphism X).inverseImage.obj F)
    (S.transition φ).app V ≫
      ((TopCat.Sheaf.forget (Type u) X).map
        ((constantMorphism_inverseImage_component X n).app F).hom).app V =
      ((TopCat.Sheaf.forget (Type u) X).map
        ((constantMorphism_inverseImage_component X m).app F).hom).app V :=
  constantInverseImageTransition X F φ V

/-- Lower shriek takes the degree-zero sheaf. -/
@[stacks 09W3 "part (2): lower shriek is the degree-zero component"]
def constantLowerShriek (X : TopCat.{u}) :
    Sheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) (Type u) ⥤
      TopCat.Sheaf (Type u) X :=
  (sheafEquivalenceSimplicialSheafSystem (constantSpace X) (Type u)).toEquivalence.functor ⋙
    SimplicialSheafSystem.componentFunctor (constantSpace X) (Type u) (op ⦋0⦌)

namespace ConstantSpace

/-- The degree-zero component functor is the sheafified left Kan extension along the
constant-site functor. -/
noncomputable def constantLowerShriek_isoKanExtension (X : TopCat.{u}) :
    constantLowerShriek X ≅
      CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback
        (constantSiteFunctor X) (Type u)
        (SimplicialOpen.grothendieckTopology (constantSpace X))
        (Opens.grothendieckTopology X) := by
  let F := levelFunctor (constantSpace X) (op ⦋0⦌)
  let J := Opens.grothendieckTopology X
  let K := SimplicialOpen.grothendieckTopology (constantSpace X)
  haveI : F.IsCocontinuous J K := by
    simpa [F, constantSpace] using
      (levelFunctor_isCocontinuous_mk (constantSpace X) 0)
  exact (inverseImageIsoComponent (constantSpace X) 0).symm ≪≫
    F.sheafPullbackCocontinuousIsoLan (Type u) J K (constantSiteLevelAdjunction X)

end ConstantSpace

/-- **Stacks 09W3.** Lower shriek is left adjoint to the inverse image of the constant
morphism. -/
@[stacks 09W3 "the lower-shriek adjunction"]
noncomputable def constantLowerShriek_adjunction (X : TopCat.{u}) :
    constantLowerShriek X ⊣ (constantMorphism X).inverseImage := by
  let G := constantSiteFunctor X
  let J := SimplicialOpen.grothendieckTopology (constantSpace X)
  let K := Opens.grothendieckTopology X
  letI : G.IsContinuous J K := constantSiteFunctor_isContinuous X
  exact Adjunction.ofNatIsoRight
    (Adjunction.ofNatIsoLeft
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G (Type u) J K)
      (constantLowerShriek_isoKanExtension X).symm)
    (constantMorphism_inverseImage_isoRestriction X).symm

/-- The map from the degree-zero sheaf to the degree-one sheaf induced by a
vertex of the one-simplex. -/
noncomputable def constantFaceMap (X : TopCat.{u})
    (G : Sheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) (Type u))
    (i : Fin 2) :
    componentSheaf (constantSpace X) G (op ⦋0⦌) ⟶
      componentSheaf (constantSpace X) G (op ⦋1⦌) :=
  let φ : (op ⦋1⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋0⦌ :=
    (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op
  let S :=
    (sheafEquivalenceSimplicialSheafSystem (constantSpace X)
      (Type u)).toEquivalence.functor.obj G
  (StacksFMap.equivSheafHom (𝟙 X) (S.component (op ⦋1⦌))
    (S.component (op ⦋0⦌))).toFun (S.transition φ)

/-- The direct image of a sheaf on the constant simplicial space is the
equalizer of its two vertex transition maps from degree zero to degree one. -/
@[stacks 09W3 "part (3): direct image as an equalizer"]
noncomputable def constantMorphism_pushforwardEqualizer (X : TopCat.{u})
    (G : Sheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) (Type u)) :
    (constantMorphism X).pushforward.obj G ≅
      equalizer (constantFaceMap X G 0) (constantFaceMap X G 1) := by
  have hBasis : Opens.IsBasis (Set.range fun U : Opens X => U) := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    exact ⟨U, ⟨U, rfl⟩, hx, le_rfl⟩
  have hface (i : Fin 2) :
      augmentationFaceMap (constantSpace X) X (𝟙 _) G i = constantFaceMap X G i := by
    apply Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ hBasis
    intro U
    simp only [augmentationFaceMap, constantFaceMap, constantSpace,
      TopCat.Sheaf.pushforward]
    rfl
  exact (augmentationMorphism_pushforwardEqualizer (constantSpace X) X (𝟙 _) G).trans
    (eqToIso (by rw [hface 0, hface 1]; rfl))

end Stacks.Topology.Simplicial

end

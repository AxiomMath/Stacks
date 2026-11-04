module

public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.Topology.Sheaves.Functors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms
public import StacksFrontier.Topology.Simplicial.ComponentSite
public import StacksFrontier.Topology.Simplicial.Morphisms

/-!
# Degreewise functoriality of sheaves on a simplicial space

For a morphism of simplicial topological spaces, the direct and inverse images of sheaves on
the simplicial site are computed degree by degree. We express the identifications as natural
isomorphisms of functors, using the equivalence with systems of component sheaves. Pulling a
sheaf back to a component therefore commutes with pullback along a morphism of simplicial
spaces, which is the commutative square of topoi formed by the two simplicial topoi and their
degreewise topoi.

## Main definitions

* `Stacks.Topology.Simplicial.pushforwardComponentIso`: a component of the direct image is the
  direct image of that component.
* `Stacks.Topology.Simplicial.pullbackComponentIso`: a component of the inverse image is the
  inverse image of that component.
* `Stacks.Topology.Simplicial.componentPullbackNaturalityIso`: restriction to a component
  commutes with inverse image along a morphism of simplicial spaces.

## Implementation notes

The first two natural isomorphisms respectively state parts (1) and (2) of Stacks 09VP. The
inverse image is the left adjoint of the direct image of the morphism of sites of Stacks 09VN.
The equivalence with systems of sheaves is the one supplied by Stacks 09VM. As in that morphism
of sites, sheaves are set-valued in the universe of the simplicial spaces.

Commutativity of morphisms of topoi is expressed on their inverse-image functors. The component
inclusions use their cocontinuous sheaf pullback, while the horizontal maps use the inverse
images associated to the map of simplicial sites and to the map of spaces. Each natural
isomorphism includes naturality in the sheaf, not merely an objectwise identification.

## References

* [Stacks Project, Tag 09VP](https://stacks.math.columbia.edu/tag/09VP)
* [Stacks Project, Tag 09W2](https://stacks.math.columbia.edu/tag/09W2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Topology.Simplicial

/-- **Stacks 09VP, part (1).** The component in degree `n` of direct image along a
morphism of simplicial spaces is the direct image along its degree-`n` component. -/
@[stacks 09VP "part (1)"]
noncomputable def pushforwardComponentIso
    {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ) :
    letI : IsMorphismOfSites.{u} (SimplicialOpen.pullback f)
      (SimplicialOpen.grothendieckTopology X)
      (SimplicialOpen.grothendieckTopology Y) :=
        SimplicialOpen.pullback_isMorphismOfSites f
    (SimplicialOpen.pullback f).sheafPushforwardContinuous
        (Type u) (SimplicialOpen.grothendieckTopology X)
        (SimplicialOpen.grothendieckTopology Y) ⋙
      (sheafEquivalenceSimplicialSheafSystem X (Type u)).toEquivalence.functor ⋙
      SimplicialSheafSystem.componentFunctor X (Type u) n ≅
    (sheafEquivalenceSimplicialSheafSystem Y (Type u)).toEquivalence.functor ⋙
      SimplicialSheafSystem.componentFunctor Y (Type u) n ⋙
        TopCat.Sheaf.pushforward (Type u) (f.app n) := by
  let pushforwardComponentForgetIso :
        letI : IsMorphismOfSites.{u} (SimplicialOpen.pullback f)
          (SimplicialOpen.grothendieckTopology X)
          (SimplicialOpen.grothendieckTopology Y) :=
            SimplicialOpen.pullback_isMorphismOfSites f
        (((SimplicialOpen.pullback f).sheafPushforwardContinuous
            (Type u) (SimplicialOpen.grothendieckTopology X)
            (SimplicialOpen.grothendieckTopology Y) ⋙
          (sheafEquivalenceSimplicialSheafSystem X (Type u)).toEquivalence.functor) ⋙
          SimplicialSheafSystem.componentFunctor X (Type u) n) ⋙
          TopCat.Sheaf.forget (Type u) (X.obj n) ≅
        (((sheafEquivalenceSimplicialSheafSystem Y (Type u)).toEquivalence.functor ⋙
          SimplicialSheafSystem.componentFunctor Y (Type u) n) ⋙
          TopCat.Sheaf.pushforward (Type u) (f.app n)) ⋙
          TopCat.Sheaf.forget (Type u) (X.obj n) := by
      let v := SimplicialOpen.pullback f
      let Jx := SimplicialOpen.grothendieckTopology X
      let Jy := SimplicialOpen.grothendieckTopology Y
      let Eₓ := sheafEquivalenceSimplicialSheafSystem X (Type u)
      let Eᵧ := sheafEquivalenceSimplicialSheafSystem Y (Type u)
      let Qₓ := componentPresheafFunctor X (Type u) n
      let Qᵧ := componentPresheafFunctor Y (Type u) n
      let Hₓ := sheafToPresheaf Jx (Type u)
      let Hᵧ := sheafToPresheaf Jy (Type u)
      let cₓ := SimplicialSheafSystem.componentFunctor X (Type u) n
      let cᵧ := SimplicialSheafSystem.componentFunctor Y (Type u) n
      let Fₓ := TopCat.Sheaf.forget (Type u) (X.obj n)
      let Fᵧ := TopCat.Sheaf.forget (Type u) (Y.obj n)
      letI : IsMorphismOfSites.{u} v Jx Jy := SimplicialOpen.pullback_isMorphismOfSites f
      let p := v.sheafPushforwardContinuous (Type u) Jx Jy
      let W := TopCat.Presheaf.pushforward (Type u) (f.app n)
      have hv :
          (Functor.whiskeringLeft (SimplicialOpen X)ᵒᵖ (SimplicialOpen Y)ᵒᵖ
            (Type u)).obj v.op ⋙ Qₓ = Qᵧ ⋙ W :=
        rfl
      calc
        (((p ⋙ Eₓ.toEquivalence.functor) ⋙ cₓ) ⋙ Fₓ) ≅
            p ⋙ (Eₓ.toEquivalence.functor ⋙ (cₓ ⋙ Fₓ)) :=
          Functor.isoWhiskerRight (Functor.associator _ _ _) Fₓ ≪≫
            Functor.associator p (Eₓ.toEquivalence.functor ⋙ cₓ) Fₓ ≪≫
            Functor.isoWhiskerLeft p (Functor.associator _ _ _)
        _ ≅ p ⋙ (Eₓ.toEquivalence.functor ⋙ (Eₓ.toPresheaf ⋙ Qₓ)) :=
          Functor.isoWhiskerLeft p
            (Functor.isoWhiskerLeft Eₓ.toEquivalence.functor (Eₓ.componentIso n).symm)
        _ ≅ (p ⋙ Eₓ.toEquivalence.functor) ⋙ (Eₓ.toPresheaf ⋙ Qₓ) :=
          (Functor.associator _ _ _).symm
        _ ≅ (p ⋙ (Eₓ.toEquivalence.functor ⋙ Eₓ.toPresheaf)) ⋙ Qₓ :=
          Functor.isoWhiskerRight (Functor.associator _ _ _) Qₓ
        _ ≅ (p ⋙ Hₓ) ⋙ Qₓ :=
          Functor.isoWhiskerRight (Functor.isoWhiskerLeft p Eₓ.underlyingPresheafIso) Qₓ
        _ ≅ (Hᵧ ⋙ (Functor.whiskeringLeft (SimplicialOpen X)ᵒᵖ
            (SimplicialOpen Y)ᵒᵖ (Type u)).obj v.op) ⋙ Qₓ :=
          Functor.isoWhiskerRight
            (v.sheafPushforwardContinuousCompSheafToPresheafIso (Type u) Jx Jy) Qₓ
        _ ≅ Hᵧ ⋙ (Qᵧ ⋙ W) :=
          Functor.isoWhiskerLeft Hᵧ (eqToIso hv) ≪≫ Functor.associator Hᵧ Qᵧ W
        _ ≅ (Hᵧ ⋙ Qᵧ) ⋙ W := (Functor.associator Hᵧ Qᵧ W).symm
        _ ≅ ((Eᵧ.toEquivalence.functor ⋙ Eᵧ.toPresheaf) ⋙ Qᵧ) ⋙ W :=
          Functor.isoWhiskerRight (Functor.isoWhiskerRight Eᵧ.underlyingPresheafIso.symm Qᵧ) W
        _ ≅ (Eᵧ.toEquivalence.functor ⋙ (Eᵧ.toPresheaf ⋙ Qᵧ)) ⋙ W :=
          Functor.isoWhiskerRight (Functor.associator _ _ _) W
        _ ≅ (Eᵧ.toEquivalence.functor ⋙ (cᵧ ⋙ Fᵧ)) ⋙ W :=
          Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft Eᵧ.toEquivalence.functor (Eᵧ.componentIso n)) W
        _ ≅ ((Eᵧ.toEquivalence.functor ⋙ cᵧ) ⋙ Fᵧ) ⋙ W :=
          Functor.isoWhiskerRight (Functor.associator _ _ _).symm W
        _ ≅ (Eᵧ.toEquivalence.functor ⋙ cᵧ) ⋙ (Fᵧ ⋙ W) := Functor.associator _ _ _
        _ ≅ (Eᵧ.toEquivalence.functor ⋙ cᵧ) ⋙
            (TopCat.Sheaf.pushforward (Type u) (f.app n) ⋙ Fₓ) :=
          Functor.isoWhiskerLeft (Eᵧ.toEquivalence.functor ⋙ cᵧ)
            (TopCat.Sheaf.pushforwardForgetIso (Type u) (f.app n))
        _ ≅ ((Eᵧ.toEquivalence.functor ⋙ cᵧ) ⋙
            TopCat.Sheaf.pushforward (Type u) (f.app n)) ⋙ Fₓ :=
          (Functor.associator _ _ _).symm
  letI : IsMorphismOfSites.{u} (SimplicialOpen.pullback f)
      (SimplicialOpen.grothendieckTopology X)
      (SimplicialOpen.grothendieckTopology Y) :=
        SimplicialOpen.pullback_isMorphismOfSites f
  exact Functor.fullyFaithfulCancelRight
    (TopCat.Sheaf.forget (Type u) (X.obj n)) pushforwardComponentForgetIso

attribute [-instance] CategoryTheory.CostructuredArrow.instSmallOfLocallySmall in
open CategoryTheory.Functor in
/-- **Stacks 09VP, part (2).** The component in degree `n` of inverse image along a
morphism of simplicial spaces is the inverse image along its degree-`n` component. -/
@[stacks 09VP "part (2)"]
noncomputable def pullbackComponentIso
    {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ) :
    letI : IsMorphismOfSites.{u} (SimplicialOpen.pullback f)
      (SimplicialOpen.grothendieckTopology X)
      (SimplicialOpen.grothendieckTopology Y) :=
        SimplicialOpen.pullback_isMorphismOfSites f
    (SimplicialOpen.pullback f).sheafPullback
        (Type u) (SimplicialOpen.grothendieckTopology X)
        (SimplicialOpen.grothendieckTopology Y) ⋙
      (sheafEquivalenceSimplicialSheafSystem Y (Type u)).toEquivalence.functor ⋙
      SimplicialSheafSystem.componentFunctor Y (Type u) n ≅
    (sheafEquivalenceSimplicialSheafSystem X (Type u)).toEquivalence.functor ⋙
      SimplicialSheafSystem.componentFunctor X (Type u) n ⋙
      TopCat.Sheaf.pullback (Type u) (f.app n) := by
  classical
  obtain ⟨⟨k⟩⟩ := n
  let n' : SimplexCategoryᵒᵖ := Opposite.op (SimplexCategory.mk k)
  let iX := levelFunctor X n'
  let iY := levelFunctor Y n'
  let g := Opens.map (f.app n')
  let v := SimplicialOpen.pullback f
  let JX := SimplicialOpen.grothendieckTopology X
  let JY := SimplicialOpen.grothendieckTopology Y
  let JXn := Opens.grothendieckTopology (X.obj n')
  let JYn := Opens.grothendieckTopology (Y.obj n')
  let EX := sheafEquivalenceSimplicialSheafSystem X (Type u)
  let EY := sheafEquivalenceSimplicialSheafSystem Y (Type u)
  let cX := SimplicialSheafSystem.componentFunctor X (Type u) n'
  let cY := SimplicialSheafSystem.componentFunctor Y (Type u) n'
  letI : IsMorphismOfSites.{u} v JX JY :=
    SimplicialOpen.pullback_isMorphismOfSites f
  letI : CategoryTheory.Functor.IsContinuous iX JXn JX :=
    levelFunctor_isContinuous_mk X k
  letI : CategoryTheory.Functor.IsContinuous iY JYn JY :=
    levelFunctor_isContinuous_mk Y k
  letI : CategoryTheory.Functor.IsCocontinuous iX JXn JX :=
    levelFunctor_isCocontinuous_mk X k
  letI : CategoryTheory.Functor.IsCocontinuous iY JYn JY :=
    levelFunctor_isCocontinuous_mk Y k
  have hsq : iX ⋙ v = g ⋙ iY := rfl
  have hfinal :
      ∀ U : SimplicialOpen X,
        (CostructuredArrow.map₂ (S := iX) (T := U) (U := iY) (V := v.obj U)
          (F := g) (G := v) (eqToHom hsq.symm) (𝟙 (v.obj U))).Final := by
    intro U
    let F := CostructuredArrow.map₂ (S := iX) (T := U) (U := iY)
      (V := v.obj U) (F := g) (G := v) (eqToHom hsq.symm) (𝟙 (v.obj U))
    change F.Final
    refine ⟨fun Z => ?_⟩
    let W₀ : Opens (X.obj n') :=
      (Opens.map (X.map Z.hom.base)).obj U.toOpens
    let c₀ : CostructuredArrow iX U := CostructuredArrow.mk
      ({ base := Z.hom.base, le := le_rfl } : iX.obj W₀ ⟶ U)
    have hV : Z.left ≤ (Opens.map (f.app n')).obj W₀ := by
      intro y hy
      have hy' := SimplicialOpen.Hom.le Z.hom hy
      change f.app U.degree (Y.map Z.hom.base y) ∈ U.toOpens at hy'
      change X.map Z.hom.base (f.app n' y) ∈ U.toOpens
      have hnat₀ := f.naturality Z.hom.base
      change Y.map Z.hom.base ≫ f.app U.degree =
        f.app n' ≫ X.map Z.hom.base at hnat₀
      have hnat : X.map Z.hom.base (f.app n' y) =
          f.app U.degree (Y.map Z.hom.base y) :=
        (congrArg (fun q : Y.obj n' ⟶ X.obj U.degree => q y) hnat₀).symm
      rwa [hnat]
    let q : Z.left ⟶ g.obj c₀.left := homOfLE hV
    have hq : iY.map q ≫ v.map c₀.hom = Z.hom := by
      apply SimplicialOpen.Hom.ext
      change 𝟙 (iY.obj Z.left).degree ≫ Z.hom.base = Z.hom.base
      simp
    let a : Z ⟶ F.obj c₀ := CostructuredArrow.homMk q hq
    let T : StructuredArrow Z F := StructuredArrow.mk a
    have hT : ∀ E : StructuredArrow Z F, Unique (E ⟶ T) := fun E =>
      { default := by
          have hom_comp_base {U V W : SimplicialOpen Y} (a : U ⟶ V) (b : V ⟶ W) :
              (a ≫ b).base = a.base ≫ b.base := rfl
          have eqHom_base {A B : SimplicialOpen Y} (e : A = B) :
              (eqToHom e : A ⟶ B).base = eqToHom (congrArg SimplicialOpen.degree e) := by
            cases e
            rfl
          have eqhom_component_base :
              (eqToHom (Functor.congr_obj hsq.symm E.right.left)).base = 𝟙 n' := by
            rw [eqHom_base]
            exact eqToHom_refl _ _
          let c := E.right
          have hb : c.hom.base = Z.hom.base := by
            have h := congrArg (fun e : SimplicialOpen.Hom _ _ => e.base) E.hom.w
            have h' := h.symm
            simp [F, hom_comp_base, eqhom_component_base] at h'
            simpa [c, iX, iY, g, v, levelFunctor,
              SimplicialOpen.pullback, Category.id_comp] using h'.symm
          have hc : c.left ≤ W₀ := by
            intro x hx
            change X.map Z.hom.base x ∈ U.toOpens
            have hx' := SimplicialOpen.Hom.le c.hom hx
            change X.map c.hom.base x ∈ U.toOpens at hx'
            rwa [hb] at hx'
          let r : c ⟶ c₀ := CostructuredArrow.homMk (homOfLE hc) (by
            apply SimplicialOpen.Hom.ext
            change 𝟙 (iX.obj c.left).degree ≫ Z.hom.base = c.hom.base
            rw [hb]
            exact Category.id_comp _)
          exact StructuredArrow.homMk r
            (CostructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))
        uniq := fun _ =>
          StructuredArrow.hom_ext _ _ (CostructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)) }
    exact isConnected_of_isTerminal _
      ((Limits.isTerminalEquivUnique (Functor.empty.{0} (StructuredArrow Z F)) T).symm hT)
  have hbc :=
    nonempty_sheafPushforwardContinuousCompCocontinuousIso_and_leftAdjointCompPullbackIso_of_final
      (Type u) JXn JYn JX JY iX iY g v hsq hfinal
  have hpush :
      g.sheafPushforwardContinuous (Type u) JXn JYn ⋙
          iX.sheafPushforwardCocontinuous (Type u) JXn JX ≅
        iY.sheafPushforwardCocontinuous (Type u) JYn JY ⋙
          v.sheafPushforwardContinuous (Type u) JX JY := Classical.choice hbc.1
  let adjIX : iX.sheafPushforwardContinuous (Type u) JXn JX ⊣
      iX.sheafPushforwardCocontinuous (Type u) JXn JX :=
    (iX.sheafAdjunctionPullbackCocontinuous (Type u) JXn JX).ofNatIsoLeft
      (iX.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u) JXn JX)
  let adjIY : iY.sheafPushforwardContinuous (Type u) JYn JY ⊣
      iY.sheafPushforwardCocontinuous (Type u) JYn JY :=
    (iY.sheafAdjunctionPullbackCocontinuous (Type u) JYn JY).ofNatIsoLeft
      (iY.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u) JYn JY)
  have hsysX : iX.sheafPushforwardContinuous (Type u) JXn JX ≅
      EX.toEquivalence.functor ⋙ cX :=
    (iX.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type u) JXn JX).symm ≪≫
      inverseImageIsoComponent X k
  have hsysY : iY.sheafPushforwardContinuous (Type u) JYn JY ≅
      EY.toEquivalence.functor ⋙ cY :=
    (iY.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type u) JYn JY).symm ≪≫
      inverseImageIsoComponent Y k
  change v.sheafPullback (Type u) JX JY ⋙ EY.toEquivalence.functor ⋙ cY ≅
    EX.toEquivalence.functor ⋙ cX ⋙ TopCat.Sheaf.pullback (Type u) (f.app n')
  exact Functor.isoWhiskerLeft (v.sheafPullback (Type u) JX JY) hsysY.symm ≪≫
    (v.sheafAdjunctionContinuous (Type u) JX JY |>.comp adjIY).leftAdjointUniq
      ((adjIX.comp (g.sheafAdjunctionContinuous (Type u) JXn JYn)).ofNatIsoRight hpush) ≪≫
    Functor.isoWhiskerRight hsysX (g.sheafPullback (Type u) JXn JYn)

/-- **Stacks 09W2.** Restriction to the `n`-th component commutes, naturally in the sheaf, with
inverse image along a map of simplicial spaces. -/
@[stacks 09W2]
noncomputable def componentPullbackNaturalityIso
    {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) (n : ℕ) :
    letI : IsMorphismOfSites.{u} (SimplicialOpen.pullback f)
      (SimplicialOpen.grothendieckTopology X)
      (SimplicialOpen.grothendieckTopology Y) :=
        SimplicialOpen.pullback_isMorphismOfSites f
    (levelFunctor X (op (SimplexCategory.mk n))).sheafPullbackCocontinuous
        (Type u) (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
        (SimplicialOpen.grothendieckTopology X) ⋙
      TopCat.Sheaf.pullback (Type u) (f.app (op (SimplexCategory.mk n))) ≅
    (SimplicialOpen.pullback f).sheafPullback
        (Type u) (SimplicialOpen.grothendieckTopology X)
        (SimplicialOpen.grothendieckTopology Y) ⋙
      (levelFunctor Y (op (SimplexCategory.mk n))).sheafPullbackCocontinuous
        (Type u) (Opens.grothendieckTopology (Y.obj (op (SimplexCategory.mk n))))
        (SimplicialOpen.grothendieckTopology Y) := by
  letI : IsMorphismOfSites.{u} (SimplicialOpen.pullback f)
      (SimplicialOpen.grothendieckTopology X)
      (SimplicialOpen.grothendieckTopology Y) :=
    SimplicialOpen.pullback_isMorphismOfSites f
  let p := TopCat.Sheaf.pullback (Type u) (f.app (op (SimplexCategory.mk n)))
  let hX := inverseImageIsoComponent X n
  let hY := inverseImageIsoComponent Y n
  exact
    Functor.isoWhiskerRight hX p ≪≫
      (pullbackComponentIso f (op (SimplexCategory.mk n))).symm ≪≫
      Functor.isoWhiskerLeft
        ((SimplicialOpen.pullback f).sheafPullback
          (Type u) (SimplicialOpen.grothendieckTopology X)
          (SimplicialOpen.grothendieckTopology Y)) hY.symm

end Stacks.Topology.Simplicial

end

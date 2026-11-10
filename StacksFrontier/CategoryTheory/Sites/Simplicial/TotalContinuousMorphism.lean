module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousFunctor

/-!
# The total morphism of topoi of a morphism between simplicial sites, continuous case

Let `h` be a morphism between simplicial sites in the continuous case: in each simplicial degree
`n` a morphism of sites `h_n : C_n → C'_n`, given by a functor `v_n : C'_n ⥤ C_n`, the `v_n`
commuting strictly with the transition functors. Applying them degreewise gives a continuous
functor `v_total` between the total sites. This file shows that `v_total` defines a morphism of
sites, hence a morphism of topoi `h_total : Sh(C_total) → Sh(C'_total)`, that the square formed by
`h_total`, `h_n` and the two component morphisms `g_n`, `g'_n` commutes, and that
`(g'_n)^{-1} ∘ h_{total,*} = h_{n,*} ∘ g_n^{-1}`. These equalities of morphisms of topoi are stated
as isomorphisms of functors.

## Main definitions

* `CategoryTheory.SimplicialSite.Morphism.componentIso`: the commutation of the component
  inclusions with `v_n` and `v_total`, as an isomorphism with identity components.
* `CategoryTheory.SimplicialSite.Morphism.totalMorphism`: the morphism of total topoi.

## Main results

* `CategoryTheory.SimplicialSite.Morphism.guitartExact_componentSquare`: the square formed by the
  component inclusions, `v_n` and `v_total` is Guitart exact.
* `CategoryTheory.SimplicialSite.Morphism.totalFunctor_isMorphismOfSites`: `v_total` defines a
  morphism of sites `C_total → C'_total`.
* `CategoryTheory.SimplicialSite.Morphism.totalComponentPushforwardIso`: the square of morphisms of
  topoi commutes, in the form of an isomorphism of direct images.
* `CategoryTheory.SimplicialSite.Morphism.totalComponentInverseImageIso`: the same square in the
  form of an isomorphism of inverse images.
* `CategoryTheory.SimplicialSite.Morphism.totalPushforwardRestrictIso`: inverse image to a
  component after direct image along `h_total` is direct image along `h_n` after inverse image to
  the component.

## References

* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 09WC](https://stacks.math.columbia.edu/tag/09WC)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe u

namespace CategoryTheory

attribute [local implicit_reducible] CategoryTheory.SimplicialSite.totalPseudofunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc

namespace Pseudofunctor.CoGrothendieck

variable {𝒮 : Type*} [Category* 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat}

attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The image of a morphism of the fibre over `S`, followed by a morphism of the total category out
of that fibre, is the morphism with the same base whose fibre component is the composite. -/
theorem ι_map_comp_mk (S : 𝒮) {Z' Z : F.obj ⟨Opposite.op S⟩} (x : Z' ⟶ Z) {Y : CoGrothendieck F}
    (f : S ⟶ Y.base) (y : Z ⟶ (F.map f.op.toLoc).toFunctor.obj Y.fiber) :
    (ι F S).map x ≫ (⟨f, y⟩ : (ι F S).obj Z ⟶ Y) = (⟨f, x ≫ y⟩ : (ι F S).obj Z' ⟶ Y) := by
  refine Hom.ext _ _ (Category.id_comp f) ?_
  change (x ≫ (F.mapId ⟨Opposite.op S⟩).inv.toNatTrans.app Z) ≫
      (F.map (𝟙 S).op.toLoc).toFunctor.map y ≫
        (F.mapComp f.op.toLoc (𝟙 S).op.toLoc).inv.toNatTrans.app Y.fiber = _
  simp only [op_id, Quiver.Hom.id_toLoc, Category.assoc, ← NatTrans.naturality_assoc,
    Cat.Hom.id_toFunctor, Functor.id_map, mapComp_id_right_inv_app, Functor.id_obj,
    Bicategory.Strict.rightUnitor_eqToIso, eqToIso.inv, PrelaxFunctor.map₂_eqToHom,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  simp only [Category.comp_id, eqToHom_naturality, Functor.id_obj, eqToHom_naturality_assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app, Cat.Hom.id_toFunctor, categoryStruct_comp_base]
  exact (Category.assoc x y _).symm

end Pseudofunctor.CoGrothendieck

namespace SimplicialSite.Morphism

variable {C C' : SimplicialSite.{u}}

/-- The inclusion of the component of degree `b` followed by the functor between the total
categories is the functor of degree `b` followed by the inclusion of the component of the target,
by an isomorphism whose components are identities. -/
def componentIso (h : SimplicialSite.Morphism C C') (b : SimplexCategoryᵒᵖ) :
    (h.hom.app b.unop).toFunctor ⋙ CoGrothendieck.ι C.totalPseudofunctor b ≅
      CoGrothendieck.ι C'.totalPseudofunctor b ⋙ h.totalFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun u =>
    (Category.comp_id _).trans ((h.ι_map_totalFunctor b u).symm.trans (Category.id_comp _).symm)

/-- The square formed by the functor of degree `b`, the two component inclusions of that degree,
and the functor between the total categories. -/
abbrev componentSquare (h : SimplicialSite.Morphism C C') (b : SimplexCategoryᵒᵖ) :
    TwoSquare (h.hom.app b.unop).toFunctor (CoGrothendieck.ι C'.totalPseudofunctor b)
      (CoGrothendieck.ι C.totalPseudofunctor b) h.totalFunctor :=
  (h.componentIso b).hom

/-- The square formed by the functor of degree `b`, the two component inclusions and the functor
between the total categories is Guitart exact. -/
theorem guitartExact_componentSquare (h : SimplicialSite.Morphism C C') (b : SimplexCategoryᵒᵖ) :
    (h.componentSquare b).GuitartExact := by
  constructor
  intro U Y g
  let w := h.componentSquare b
  let f : b ⟶ Y.base := g.base
  let Z : C'.totalPseudofunctor.obj ⟨Opposite.op b⟩ :=
    (C'.totalPseudofunctor.map f.op.toLoc).toFunctor.obj Y.fiber
  have hobj : (h.hom.app b.unop).toFunctor.obj Z =
      (C.totalPseudofunctor.map f.op.toLoc).toFunctor.obj
        ((h.hom.app Y.base.unop).toFunctor.obj Y.fiber) :=
    h.app_obj_map f.unop Y.fiber
  let a : U ⟶ (h.hom.app b.unop).toFunctor.obj Z := g.fiber ≫ eqToHom hobj.symm
  let b₀ : (CoGrothendieck.ι C'.totalPseudofunctor b).obj Z ⟶ Y := ⟨f, 𝟙 _⟩
  have hiff : ∀ {X₁ : C'.totalPseudofunctor.obj ⟨Opposite.op b⟩}
      (a' : U ⟶ (h.hom.app b.unop).toFunctor.obj X₁) (u : X₁ ⟶ Z),
      (CoGrothendieck.ι C.totalPseudofunctor b).map a' ≫ w.app X₁ ≫
          h.totalFunctor.map
            (⟨f, u⟩ : (CoGrothendieck.ι C'.totalPseudofunctor b).obj X₁ ⟶ Y) = g ↔
        a' ≫ (h.hom.app b.unop).toFunctor.map u = a := by
    intro X₁ a' u
    have hcomp := (congrArg ((CoGrothendieck.ι C.totalPseudofunctor b).map a' ≫ ·)
      (Category.id_comp (h.totalFunctor.map
        (⟨f, u⟩ : (CoGrothendieck.ι C'.totalPseudofunctor b).obj X₁ ⟶ Y)))).trans
      (CoGrothendieck.ι_map_comp_mk b (Y := h.totalFunctor.obj Y)
        a' f ((h.hom.app b.unop).toFunctor.map u ≫ eqToHom hobj))
    refine (iff_of_eq (congrArg (· = g) hcomp)).trans ⟨fun e => ?_, fun e => ?_⟩
    · have := CoGrothendieck.Hom.congr e
      simp only [eqToHom_refl, Category.comp_id] at this
      exact (comp_eqToHom_iff hobj _ _).mp ((Category.assoc _ _ _).trans this)
    · refine CoGrothendieck.Hom.ext _ _ rfl ?_
      exact ((Category.assoc _ _ _).symm.trans
        ((comp_eqToHom_iff hobj _ _).mpr e)).trans (by simp; rfl)
  have comm : (CoGrothendieck.ι C.totalPseudofunctor b).map a ≫ w.app Z ≫
      h.totalFunctor.map b₀ = g :=
    (hiff a (𝟙 Z)).2 (by rw [Functor.map_id, Category.comp_id])
  let P : w.StructuredArrowRightwards g :=
    TwoSquare.StructuredArrowRightwards.mk w g Z a b₀ comm
  have hterminal : ∀ Q : w.StructuredArrowRightwards g, Nonempty (Q ⟶ P) := by
    intro Q
    obtain ⟨X₁, a', b', hcomm, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective Q
    obtain ⟨f', u⟩ := b'
    have hbase : f' = f := by
      have hh : 𝟙 b ≫ 𝟙 b ≫ f' = g.base := congrArg CoGrothendieck.Hom.base hcomm
      exact ((Category.id_comp f').symm.trans (Category.id_comp (𝟙 b ≫ f')).symm).trans hh
    subst hbase
    have hfib : a' ≫ (h.hom.app b.unop).toFunctor.map u = a := (hiff a' u).1 hcomm
    have htri : (CoGrothendieck.ι C'.totalPseudofunctor b).map u ≫ b₀ =
        (⟨f, u⟩ : (CoGrothendieck.ι C'.totalPseudofunctor b).obj X₁ ⟶ Y) :=
      (CoGrothendieck.ι_map_comp_mk b u f _).trans (congrArg _ (Category.comp_id u))
    exact ⟨StructuredArrow.homMk (CostructuredArrow.homMk u htri)
      (CostructuredArrow.hom_ext _ _ hfib)⟩
  have : Nonempty (w.StructuredArrowRightwards g) := ⟨P⟩
  apply zigzag_isConnected
  intro Q₁ Q₂
  obtain ⟨p₁⟩ := hterminal Q₁
  obtain ⟨p₂⟩ := hterminal Q₂
  exact (Zigzag.of_hom p₁).trans (Zigzag.of_inv p₂)

/-- The square of direct images formed by `h_{n,*}`, `g'_{n,*}`, `g_{n,*}` and the restriction
along the functor between the total categories commutes. -/
def componentPushforwardSquareIso (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    letI := (h.isMorphismOfSites n).isContinuous
    letI : (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).IsCocontinuous
        (C.coverage n).toGrothendieck C.totalTopology :=
      SimplicialSiteSituation.componentFunctor_isCocontinuous
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
    letI : (CoGrothendieck.ι C'.totalPseudofunctor (Opposite.op n)).IsCocontinuous
        (C'.coverage n).toGrothendieck C'.totalTopology :=
      SimplicialSiteSituation.componentFunctor_isCocontinuous
        (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n
    (h.hom.app n).toFunctor.sheafPushforwardContinuous (Type u) (C'.coverage n).toGrothendieck
        (C.coverage n).toGrothendieck ⋙
      (CoGrothendieck.ι C'.totalPseudofunctor (Opposite.op n)).sheafPushforwardCocontinuous
        (Type u) (C'.coverage n).toGrothendieck C'.totalTopology ≅
    (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).sheafPushforwardCocontinuous
        (Type u) (C.coverage n).toGrothendieck C.totalTopology ⋙
      h.totalFunctor.sheafPushforwardContinuous (Type u) C'.totalTopology C.totalTopology :=
  letI := (h.isMorphismOfSites n).isContinuous
  letI : (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).IsCocontinuous
      (C.coverage n).toGrothendieck C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
  letI : (CoGrothendieck.ι C'.totalPseudofunctor (Opposite.op n)).IsCocontinuous
      (C'.coverage n).toGrothendieck C'.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n
  haveI := h.guitartExact_componentSquare (Opposite.op n)
  (Functor.fullyFaithfulCancelRight (sheafToPresheaf C'.totalTopology (Type u))
    (Functor.isoWhiskerLeft (sheafToPresheaf (C.coverage n).toGrothendieck (Type u))
      (asIso ((h.componentSquare (Opposite.op n)).op.ranBaseChange (D := Type u))))).symm

/-- Inverse image along a component after inverse image along the functor between the total
categories is the inverse image along the functor of that degree after inverse image along the
component of the target. -/
def sheafPullbackComponentIso (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    letI := (h.isMorphismOfSites n).isContinuous
    h.totalFunctor.sheafPullback (Type u) C'.totalTopology C.totalTopology ⋙
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).inverseImage ≅
      (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).inverseImage ⋙
        (h.hom.app n).toFunctor.sheafPullback (Type u) (C'.coverage n).toGrothendieck
          (C.coverage n).toGrothendieck :=
  letI := (h.isMorphismOfSites n).isContinuous
  ((h.totalFunctor.sheafAdjunctionContinuous (Type u) C'.totalTopology C.totalTopology).comp
      (SimplicialSiteSituation.componentMorphism
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).adj).leftAdjointUniq
    (((SimplicialSiteSituation.componentMorphism
        (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).adj.comp
      ((h.hom.app n).toFunctor.sheafAdjunctionContinuous (Type u)
        (C'.coverage n).toGrothendieck (C.coverage n).toGrothendieck)).ofNatIsoRight
      (h.componentPushforwardSquareIso n))

/-- The inverse image along the functor between the total categories is left exact. -/
theorem preservesFiniteLimits_sheafPullback_totalFunctor (h : SimplicialSite.Morphism C C') :
    PreservesFiniteLimits
      (h.totalFunctor.sheafPullback (Type u) C'.totalTopology C.totalTopology) := by
  constructor
  intro J _ _
  constructor
  intro K
  suffices PreservesLimit K
      (h.totalFunctor.sheafPullback (Type u) C'.totalTopology C.totalTopology ⋙
        sheafToPresheaf C.totalTopology (Type u)) from
    preservesLimit_of_reflects_of_preserves _ (sheafToPresheaf C.totalTopology (Type u))
  apply preservesLimit_of_evaluation
  intro X
  let n : SimplexCategory := X.unop.base.unop
  let := (h.isMorphismOfSites n).isContinuous
  have h₀ := (h.isMorphismOfSites n).preservesFiniteLimits
  have h₀' := (SimplicialSiteSituation.componentMorphism
    (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).preservesFiniteLimits
  let i := CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)
  let : i.IsCocontinuous (C.coverage n).toGrothendieck C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
  let : i.IsContinuous (C.coverage n).toGrothendieck C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
  let e₁ : sheafToPresheaf C.totalTopology (Type u) ⋙ (evaluation _ _).obj X ≅
      i.sheafPushforwardContinuous (Type u) (C.coverage n).toGrothendieck C.totalTopology ⋙
        sheafToPresheaf (C.coverage n).toGrothendieck (Type u) ⋙
          (evaluation _ _).obj (Opposite.op X.unop.fiber) := Iso.refl _
  let e : h.totalFunctor.sheafPullback (Type u) C'.totalTopology C.totalTopology ⋙
        sheafToPresheaf C.totalTopology (Type u) ⋙ (evaluation _ _).obj X ≅
      ((SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).inverseImage ⋙
        (h.hom.app n).toFunctor.sheafPullback (Type u) (C'.coverage n).toGrothendieck
          (C.coverage n).toGrothendieck) ⋙
        sheafToPresheaf (C.coverage n).toGrothendieck (Type u) ⋙
          (evaluation _ _).obj (Opposite.op X.unop.fiber) :=
    Functor.isoWhiskerLeft _ e₁ ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft _
        (i.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u)
          (C.coverage n).toGrothendieck C.totalTopology).symm ≪≫
          h.sheafPullbackComponentIso n) _
  have h₁ : PreservesFiniteLimits
      ((SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).inverseImage ⋙
        (h.hom.app n).toFunctor.sheafPullback (Type u) (C'.coverage n).toGrothendieck
          (C.coverage n).toGrothendieck) := @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₀' h₀
  have h₂ : PreservesFiniteLimits
      (sheafToPresheaf (C.coverage n).toGrothendieck (Type u) ⋙
        (evaluation _ (Type u)).obj (Opposite.op X.unop.fiber)) := comp_preservesFiniteLimits _ _
  have h₃ := @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂
  exact @preservesLimit_of_natIso _ _ _ _ _ _ K _ _ e.symm
    ((h₃.preservesFiniteLimits J).preservesLimit)

/-- **The functor between the total categories is a morphism of sites.** -/
theorem totalFunctor_isMorphismOfSites (h : SimplicialSite.Morphism C C') :
    h.totalFunctor.IsMorphismOfSites C'.totalTopology C.totalTopology :=
  (Functor.isMorphismOfSites_iff_preservesFiniteLimits _ _ _).mpr
    h.preservesFiniteLimits_sheafPullback_totalFunctor

/-- The morphism between the total topoi induced by a morphism between simplicial sites in the
continuous case: the morphism of topoi of the morphism of sites defined by the functor between the
total categories. -/
def totalMorphism (h : SimplicialSite.Morphism C C') :
    MorphismOfTopoi
      (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u))
      (Sheaf (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u)) :=
  h.totalFunctor_isMorphismOfSites.morphismOfTopoi

/-- The square formed by the total morphism of topoi, the morphism of topoi in simplicial degree
`n`, and the two component morphisms of that degree commutes, as witnessed by a natural isomorphism
of direct-image functors. -/
def totalComponentPushforwardIso (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    ((SimplicialSiteMorphism.ofMorphismOfSites h).componentMorphism n).pushforward ⋙
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).pushforward ≅
      (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).pushforward ⋙
        h.totalMorphism.pushforward :=
  h.componentPushforwardSquareIso n

/-- The same square, as a natural isomorphism of inverse-image functors. -/
def totalComponentInverseImageIso (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    h.totalMorphism.inverseImage ⋙
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).inverseImage ≅
      (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).inverseImage ⋙
        ((SimplicialSiteMorphism.ofMorphismOfSites h).componentMorphism n).inverseImage :=
  h.sheafPullbackComponentIso n

/-- Inverse image to the component of simplicial degree `n`, applied to the direct image along the
total morphism, is the direct image in degree `n` applied to the inverse image to the component of
that degree. -/
def totalPushforwardRestrictIso (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    h.totalMorphism.pushforward ⋙
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).inverseImage ≅
      (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).inverseImage ⋙
        ((SimplicialSiteMorphism.ofMorphismOfSites h).componentMorphism n).pushforward := by
  let v := (h.hom.app n).toFunctor
  let i := CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)
  let i' := CoGrothendieck.ι C'.totalPseudofunctor (Opposite.op n)
  let Jn := (C.coverage n).toGrothendieck
  let Jn' := (C'.coverage n).toGrothendieck
  letI : v.IsContinuous Jn' Jn := (h.isMorphismOfSites n).isContinuous
  letI : i.IsCocontinuous Jn C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
  letI : i'.IsCocontinuous Jn' C'.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n
  letI : i.IsContinuous Jn C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
  letI : i'.IsContinuous Jn' C'.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n
  letI : (v ⋙ i).IsContinuous Jn' C.totalTopology :=
    Functor.isContinuous_comp v i Jn' Jn C.totalTopology
  change h.totalFunctor.sheafPushforwardContinuous (Type u) C'.totalTopology C.totalTopology ⋙
      i'.sheafPullbackCocontinuous (Type u) Jn' C'.totalTopology ≅
    i.sheafPullbackCocontinuous (Type u) Jn C.totalTopology ⋙
      v.sheafPushforwardContinuous (Type u) Jn' Jn
  exact Functor.isoWhiskerLeft _
      (i'.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u) Jn' C'.totalTopology) ≪≫
    Functor.sheafPushforwardContinuousComp' (h.componentIso (Opposite.op n)).symm (Type u)
      Jn' C'.totalTopology C.totalTopology ≪≫
    (Functor.sheafPushforwardContinuousComp v i (Type u) Jn' Jn C.totalTopology).symm ≪≫
    Functor.isoWhiskerRight
      (i.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u) Jn C.totalTopology).symm _

end SimplicialSite.Morphism

end CategoryTheory

end

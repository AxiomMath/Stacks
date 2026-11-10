module

public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.PushforwardSquareMate
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphism

/-!
# Beck–Chevalley for the degreewise square of a morphism between simplicial sites, case (A)

Let `h` be a morphism between simplicial sites in the continuous case of Stacks 09WE, given in
simplicial degree `n` by a functor `v_n : C'_n ⥤ C_n` representing a morphism of sites, and let
`v_total : C'_total ⥤ C_total` be the induced functor of total sites. The total morphism of topoi
`h_{total}`, the degreewise morphism `h_n` and the two component morphisms `g_n`, `g'_n` form the
commutative square of Stacks 0D96, witnessed by the isomorphism `totalComponentPushforwardIso`
of composite direct images. Its mate along the adjunctions `g_n^{-1} ⊣ g_{n,*}` and
`g'^{-1}_n ⊣ g'_{n,*}` is a comparison

`(g'_n)^{-1} ∘ h_{total,*} ⟶ h_{n,*} ∘ g_n^{-1}`

of functors on sheaves of sets, and this file proves that it is invertible.

## Main definitions

* `CategoryTheory.sheafPushforwardContinuousSquareIso`: the square of direct images attached to
  a Guitart exact square of site functors whose horizontal functors are continuous.
* `CategoryTheory.SimplicialSite.Morphism.totalComponentPushforwardMate`: the mate.

## Main results

* `CategoryTheory.sheafPushforwardContinuousSquareMate_app_hom`: on underlying presheaves the
  mate of that square is the square of site functors itself, whiskered by the sheaf.
* `CategoryTheory.SimplicialSite.Morphism.isIso_totalComponentPushforwardMate`: the mate is an
  isomorphism.

## Implementation notes

In case (A) the direct images `h_{n,*}` and `h_{total,*}` are restriction along `v_n` and
`v_total`, and the inverse images of the component morphisms are, up to the comparison of left
adjoints, restriction along the component inclusions. So both sides of the mate are restriction
along the two composites `i'_n ⋙ v_total` and `v_n ⋙ i_n` of the square of site functors, and the
mate is the square itself: the comparison of direct images is the base change of right Kan
extensions along that square, whose composite with the counit is the square followed by the
counit, and the triangle identity of the right Kan extension along `i_n` removes the unit.

## References

* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe u

namespace CategoryTheory

section ContinuousSquare

variable {A A' B B' : Type u} [SmallCategory A] [SmallCategory A'] [SmallCategory B]
  [SmallCategory B']
  (JA : GrothendieckTopology A) (JA' : GrothendieckTopology A') (JB : GrothendieckTopology B)
  (JB' : GrothendieckTopology B')
  (i : A ⥤ B) (i' : A' ⥤ B') (v : A' ⥤ A) (T : B' ⥤ B)
  [hi : i.IsContinuous JA JB] [hi' : i.IsCocontinuous JA JB] [hj : i'.IsContinuous JA' JB']
  [hj' : i'.IsCocontinuous JA' JB'] [hv : v.IsContinuous JA' JA] [hT : T.IsContinuous JB' JB]
  (w : TwoSquare v i' i T)

/-- The square of direct images of sheaves of sets attached to a square of site functors
`w : v ⋙ i ⟶ i' ⋙ T` with continuous horizontal functors `v`, `T` and cocontinuous vertical
functors `i`, `i'`, when `w` is Guitart exact: the base change of right Kan extensions along the
opposite square. -/
def sheafPushforwardContinuousSquareIso [w.GuitartExact] :
    v.sheafPushforwardContinuous (Type u) JA' JA ⋙
        i'.sheafPushforwardCocontinuous (Type u) JA' JB' ≅
      i.sheafPushforwardCocontinuous (Type u) JA JB ⋙
        T.sheafPushforwardContinuous (Type u) JB' JB :=
  (Functor.fullyFaithfulCancelRight (sheafToPresheaf JB' (Type u))
    (Functor.isoWhiskerLeft (sheafToPresheaf JA (Type u))
      (asIso (w.op.ranBaseChange (D := Type u))))).symm

omit hi hj in
/-- On underlying presheaves, the inverse of the square of direct images is the base change of
right Kan extensions. -/
theorem sheafPushforwardContinuousSquareIso_inv_app_hom [w.GuitartExact] (G : Sheaf JA (Type u)) :
    ((sheafPushforwardContinuousSquareIso JA JA' JB JB' i i' v T w).inv.app G).hom =
      w.op.ranBaseChange.app G.obj :=
  (sheafToPresheaf JB' (Type u)).map_preimage _

/-- **On underlying presheaves, the mate of the square of direct images is the square of site
functors**: along the adjunctions `i^{-1} ⊣ i_*` and `i'^{-1} ⊣ i'_*`, the mate
`T_* ⋙ i'^{-1} ⟶ i^{-1} ⋙ v_*` of `sheafPushforwardContinuousSquareIso` is restriction along
`w`. -/
theorem sheafPushforwardContinuousSquareMate_app_hom [w.GuitartExact] (F : Sheaf JB (Type u)) :
    (((mateEquiv (i.sheafAdjunctionCocontinuous (Type u) JA JB)
        (i'.sheafAdjunctionCocontinuous (Type u) JA' JB')).symm
        (TwoSquare.mk _ _ _ _
          (sheafPushforwardContinuousSquareIso JA JA' JB JB' i i' v T w).inv)).app
          F).hom =
      Functor.whiskerRight w.op F.obj := by
  have hR : ∀ {X : A'ᵒᵖ ⥤ Type u} {Y : B'ᵒᵖ ⥤ Type u} (y : i'.op ⋙ Y ⟶ X),
      Functor.whiskerLeft i'.op ((i'.op.ranAdjunction (Type u)).homEquiv Y X y) ≫
        (i'.op.ranAdjunction (Type u)).counit.app X = y := by
    intro X Y y
    have h := (i'.op.ranAdjunction (Type u)).homEquiv_counit
      (g := (i'.op.ranAdjunction (Type u)).homEquiv Y X y)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hε : ∀ G : Sheaf JA' (Type u),
      ((i'.sheafAdjunctionCocontinuous (Type u) JA' JB').counit.app G).hom =
        (i'.op.ranAdjunction (Type u)).counit.app G.obj :=
    Functor.sheafAdjunctionCocontinuous_counit_app_hom _ _ _ _
  have hη : ((i.sheafAdjunctionCocontinuous (Type u) JA JB).unit.app F).hom =
      (i.op.ranAdjunction (Type u)).unit.app F.obj :=
    Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ F
  have hTr : Functor.whiskerLeft i.op ((i.op.ranAdjunction (Type u)).unit.app F.obj) ≫
      (i.op.ranAdjunction (Type u)).counit.app (i.op ⋙ F.obj) = 𝟙 _ :=
    (i.op.ranAdjunction (Type u)).left_triangle_components F.obj
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map, Category.id_comp,
    Functor.map_id, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom]
  change Functor.whiskerLeft i'.op (Functor.whiskerLeft T.op
      ((i.sheafAdjunctionCocontinuous (Type u) JA JB).unit.app F).hom) ≫
    Functor.whiskerLeft i'.op ((sheafPushforwardContinuousSquareIso JA JA' JB JB' i i' v T
      w).inv.app ((i.sheafPushforwardContinuous (Type u) JA JB).obj F)).hom ≫
    ((i'.sheafAdjunctionCocontinuous (Type u) JA' JB').counit.app
      ((v.sheafPushforwardContinuous (Type u) JA' JA).obj
        ((i.sheafPushforwardContinuous (Type u) JA JB).obj F))).hom = _
  rw [hη, sheafPushforwardContinuousSquareIso_inv_app_hom, hε]
  have hB : Functor.whiskerLeft i'.op (w.op.ranBaseChange.app (i.op ⋙ F.obj)) ≫
      (i'.op.ranAdjunction (Type u)).counit.app (v.op ⋙ i.op ⋙ F.obj) =
      ((Functor.RightExtension.mk _ (i.op.ranCounit.app (i.op ⋙ F.obj))).compTwoSquare
        w.op).hom :=
    hR _
  change Functor.whiskerLeft i'.op (Functor.whiskerLeft T.op
      ((i.op.ranAdjunction (Type u)).unit.app F.obj)) ≫
    (Functor.whiskerLeft i'.op (w.op.ranBaseChange.app (i.op ⋙ F.obj)) ≫
      (i'.op.ranAdjunction (Type u)).counit.app (v.op ⋙ i.op ⋙ F.obj)) = _
  rw [hB]
  refine NatTrans.ext (funext fun X => ?_)
  have n1 : ((i.op.ranAdjunction (Type u)).unit.app F.obj).app (T.op.obj (i'.op.obj X)) ≫
      (i.op.ran.obj (i.op ⋙ F.obj)).map (w.op.app X) =
      F.obj.map (w.op.app X) ≫
        ((i.op.ranAdjunction (Type u)).unit.app F.obj).app (i.op.obj (v.op.obj X)) :=
    (((i.op.ranAdjunction (Type u)).unit.app F.obj).naturality (w.op.app X)).symm
  have t1 := Functor.ranCounit_app_app_ranAdjunction_unit_app_app i.op F.obj (v.op.obj X)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  change ((i.op.ranAdjunction (Type u)).unit.app F.obj).app (T.op.obj (i'.op.obj X)) ≫
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight w.op (i.op.ran.obj (i.op ⋙ F.obj)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft v.op (i.op.ranCounit.app (i.op ⋙ F.obj))).app X = _
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  rw [reassoc_of% n1, t1]
  exact Category.comp_id _

/-- **Beck–Chevalley for a Guitart exact square with continuous horizontal functors.** The mate
`T_* ⋙ i'^{-1} ⟶ i^{-1} ⋙ v_*` of the square of direct images is an isomorphism as soon as the
square of site functors is an isomorphism. -/
theorem isIso_sheafPushforwardContinuousSquareMate [w.GuitartExact] [IsIso w] :
    IsIso ((mateEquiv (i.sheafAdjunctionCocontinuous (Type u) JA JB)
        (i'.sheafAdjunctionCocontinuous (Type u) JA' JB')).symm
        (TwoSquare.mk _ _ _ _
          (sheafPushforwardContinuousSquareIso JA JA' JB JB' i i' v T w).inv)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← ObjectProperty.isIso_hom_iff, sheafPushforwardContinuousSquareMate_app_hom]
  have : IsIso w.op := by
    change IsIso (NatTrans.op w)
    infer_instance
  exact (Functor.isoWhiskerRight (asIso w.op) F.obj).isIso_hom

end ContinuousSquare

namespace SimplicialSite.Morphism

variable {C C' : SimplicialSite.{u}}

/-- The canonical comparison `(g'_n)^{-1} ∘ h_{total,*} ⟶ h_{n,*} ∘ g_n^{-1}` of sheaves of sets
in case (A): the mate of the square of direct images of Stacks 0D96 along the adjunctions of the
two component morphisms of degree `n`. -/
abbrev totalComponentPushforwardMate (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :=
  (mateEquiv (SimplicialSiteSituation.componentMorphism
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).adj
      (SimplicialSiteSituation.componentMorphism
        (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).adj).symm
    (TwoSquare.mk _ _ _ _ (h.totalComponentPushforwardIso n).inv)

/-- **The Beck–Chevalley property of the degreewise square of Stacks 0D96, case (A).** The mate
of the square of direct images along the two component morphisms of simplicial degree `n` is an
isomorphism: the canonical comparison `(g'_n)^{-1} h_{total,*} ⟶ h_{n,*} g_n^{-1}` of sheaves of
sets is invertible. -/
theorem isIso_totalComponentPushforwardMate (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    IsIso (totalComponentPushforwardMate h n) := by
  let v := (h.hom.app n).toFunctor
  let i := CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)
  let i' := CoGrothendieck.ι C'.totalPseudofunctor (Opposite.op n)
  let Jn := (C.coverage n).toGrothendieck
  let Jn' := (C'.coverage n).toGrothendieck
  let : v.IsContinuous Jn' Jn := (h.isMorphismOfSites n).isContinuous
  let : i.IsCocontinuous Jn C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
  let : i'.IsCocontinuous Jn' C'.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n
  let : i.IsContinuous Jn C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
  let : i'.IsContinuous Jn' C'.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n
  let : h.totalFunctor.IsContinuous C'.totalTopology C.totalTopology :=
    h.totalFunctor_isContinuous
  have := h.guitartExact_componentSquare (Opposite.op n)
  have : IsIso (h.componentSquare (Opposite.op n)) :=
    inferInstanceAs (IsIso (h.componentIso (Opposite.op n)).hom)
  have key : IsIso ((mateEquiv (i.sheafAdjunctionCocontinuous (Type u) Jn C.totalTopology)
      (i'.sheafAdjunctionCocontinuous (Type u) Jn' C'.totalTopology)).symm
      (TwoSquare.mk _ _ _ _ (h.totalComponentPushforwardIso n).inv)) :=
    isIso_sheafPushforwardContinuousSquareMate Jn Jn' C.totalTopology C'.totalTopology
      i i' v h.totalFunctor (h.componentSquare (Opposite.op n))
      (hi := SimplicialSiteSituation.componentFunctor_isContinuous
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
      (hi' := SimplicialSiteSituation.componentFunctor_isCocontinuous
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
      (hj := SimplicialSiteSituation.componentFunctor_isContinuous
        (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n)
      (hj' := SimplicialSiteSituation.componentFunctor_isCocontinuous
        (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n)
      (hv := (h.isMorphismOfSites n).isContinuous) (hT := h.totalFunctor_isContinuous)
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  unfold totalComponentPushforwardMate
  rw [mateEquiv_symm_natTrans_app_leftAdjointUniq
    (SimplicialSiteSituation.componentMorphism (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).adj
    (i.sheafAdjunctionCocontinuous (Type u) Jn C.totalTopology)
    (SimplicialSiteSituation.componentMorphism (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).adj
    (i'.sheafAdjunctionCocontinuous (Type u) Jn' C'.totalTopology)
    (TwoSquare.mk _ _ _ _ (h.totalComponentPushforwardIso n).inv) F]
  have : IsIso ((Adjunction.leftAdjointUniq
      (SimplicialSiteSituation.componentMorphism (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).adj
      (i'.sheafAdjunctionCocontinuous (Type u) Jn' C'.totalTopology)).hom.app
        (h.totalMorphism.pushforward.obj F)) :=
    Iso.isIso_hom ((Adjunction.leftAdjointUniq
      (SimplicialSiteSituation.componentMorphism (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).adj
      (i'.sheafAdjunctionCocontinuous (Type u) Jn' C'.totalTopology)).app
        (h.totalMorphism.pushforward.obj F))
  have : IsIso ((Adjunction.leftAdjointUniq
      (SimplicialSiteSituation.componentMorphism (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).adj
      (i.sheafAdjunctionCocontinuous (Type u) Jn C.totalTopology)).inv.app F) :=
    Iso.isIso_inv ((Adjunction.leftAdjointUniq
      (SimplicialSiteSituation.componentMorphism (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).adj
      (i.sheafAdjunctionCocontinuous (Type u) Jn C.totalTopology)).app F)
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso'
    (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ key F) inferInstance)

end SimplicialSite.Morphism

end CategoryTheory

end

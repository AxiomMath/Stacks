module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCoproduct

/-!
# Smooth lifts over a disjoint union (Stacks 0CJU)

A family of smooth lifts `ξ l` of representable étale opens `N l` of `W`, whose bases and ambient
spaces are represented by objects with coproducts in the big fppf site, glues to a smooth lift
over the disjoint union of the `N l` in the spaces-étale site of `W`, with ambient space the
disjoint union of the ambient spaces. This is the first step of the descent of smooth lifts along
an arbitrary covering in the proof of Stacks 0CJU: it reduces to a covering by a single
morphism.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_sigma_lift`: the glued smooth lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An étale covering stays one after precomposing its members with isomorphisms. -/
theorem Space.IsEtaleCovering.iso_comp {K : Type u} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X X' : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : ∀ k, X' k ≅ X k) {f : ∀ k, X k ⟶ F}
    (h : Space.IsEtaleCovering B S hS X f) (hX' : ∀ k, IsAlgebraicSpace B S hS (X' k)) :
    Space.IsEtaleCovering B S hS X' (fun k => (i k).hom ≫ f k) := by
  refine ⟨h.target_isAlgebraicSpace, hX', fun k =>
    Space.isEtale_comp B S hS (Space.isEtale_of_isIso B S hS _) (h.etale k), ?_⟩
  refine Set.eq_univ_of_forall fun y => ?_
  have hy : y ∈ ⋃ k, Set.range (Space.pointsMap B S hS (X k) (f k)) := by
    rw [h.jointly_surjective]; trivial
  obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.1 hy
  refine Set.mem_iUnion.2 ⟨k, Space.pointsMap B S hS _ (i k).inv z, ?_⟩
  have hz := congrFun (Space.pointsMap_comp B S hS _ (i k).inv (i k).hom).symm z
  rw [Iso.inv_hom_id, Space.pointsMap_id] at hz
  rw [Space.pointsMap_comp, Function.comp_apply]
  exact congrArg (Space.pointsMap B S hS (X k) (f k)) hz

end AlgebraicGeometry

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- Sections of a presheaf isomorphic to a summand of a coproduct cofan are separated by the leg. -/
private theorem eq_of_comp_cofan_eq {L : Type u} {F : L → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (n : L → BigFppfOver B S hS) (i : ∀ l, yoneda.obj (n l) ≅ F l) {V' : BigFppfOver B S hS}
    (c : ∀ l, n l ⟶ V') (hV : IsColimit (Cofan.mk V' c)) (k : L) {V : BigFppfOver B S hS}
    {a a' : (F k).obj (Opposite.op V)} (h : (i k).inv.app _ a ≫ c k = (i k).inv.app _ a' ≫ c k) :
    a = a' := by
  have := Space.SpacesEtale.mono_cofan_inj n c hV k
  simpa using congrArg ((i k).hom.app _) ((cancel_mono (c k)).1 h)

/-- **Smooth lifts glue over a disjoint union.** -/
theorem exists_sigma_lift {L : Type u} (ξ : L → EtaleSmoothLift B S hS ι hι W x hx)
    (nN nA : L → BigFppfOver B S hS) (iN : ∀ l, yoneda.obj (nN l) ≅ (ξ l).base.obj.left.obj)
    (iA : ∀ l, yoneda.obj (nA l) ≅ (ξ l).ambient.obj) {VN VA : BigFppfOver B S hS}
    (cN : ∀ l, nN l ⟶ VN) (cA : ∀ l, nA l ⟶ VA) (hVN : IsColimit (Cofan.mk VN cN))
    (hVA : IsColimit (Cofan.mk VA cA)) :
    ∃ (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber
        (Space.SpacesEtale.sigmaRep (fun l => (ξ l).base) nN iN cN hVN))
      (m : ∀ l, ξ l ⟶ ζ.1), ∀ l, (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift
        (Space.SpacesEtale.sigmaRepι (fun l => (ξ l).base) nN iN cN hVN l) (m l) := by
  classical
  let X := Space.SpacesEtale.sigmaRep (fun l => (ξ l).base) nN iN cN hVN
  let ιX := Space.SpacesEtale.sigmaRepι (fun l => (ξ l).base) nN iN cN hVN
  let Y := schemeSpace VA
  let e : ∀ l, (ξ l).ambient ⟶ Y := fun l => ObjectProperty.homMk ((iA l).inv ≫ yoneda.map (cA l))
  let il : ∀ l, nN l ⟶ nA l := fun l =>
    yoneda.preimage ((iN l).hom ≫ (ξ l).inclusion.hom ≫ (iA l).inv)
  have hil : ∀ l, yoneda.map (il l) = (iN l).hom ≫ (ξ l).inclusion.hom ≫ (iA l).inv :=
    fun l => yoneda.map_preimage _
  let incV : VN ⟶ VA := Cofan.IsColimit.desc hVN (fun l => il l ≫ cA l)
  have hinc : ∀ l, cN l ≫ incV = il l ≫ cA l := fun l => Cofan.IsColimit.fac hVN _ l
  let incl : X.obj.left ⟶ Y := schemeSpaceMap incV
  have hincl : ∀ l, (ξ l).inclusion ≫ e l = (ιX l).hom.left ≫ incl := by
    intro l
    refine ObjectProperty.hom_ext _ ?_
    change (ξ l).inclusion.hom ≫ (iA l).inv ≫ yoneda.map (cA l) =
      ((iN l).inv ≫ yoneda.map (cN l)) ≫ yoneda.map incV
    rw [Category.assoc, ← Functor.map_comp, hinc, Functor.map_comp, hil]
    simp
  have hpb : ∀ l, IsPullback (ξ l).inclusion (ιX l).hom.left (e l) incl := by
    intro l
    have h := (BigFppfOver.isPullback_cofan_desc hVN hVA il incV hinc l).map yoneda
    refine Space.isPullback_of_isPullback_hom B S hS ?_
    refine h.of_iso (iN l) (iA l) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [hil]; simp
    · change yoneda.map (cN l) ≫ 𝟙 _ = (iN l).hom ≫ ((iN l).inv ≫ yoneda.map (cN l))
      simp
    · change yoneda.map (cA l) ≫ 𝟙 _ = (iA l).hom ≫ ((iA l).inv ≫ yoneda.map (cA l))
      simp
    · simp; rfl
  have he : Space.IsEtaleCovering B S hS (fun l => (ξ l).ambient.obj) (fun l => (e l).hom) :=
    Space.IsEtaleCovering.iso_comp (fun l => (iA l).symm)
      (Space.SpacesEtale.isEtaleCovering_yoneda_map nA cA hVA) (fun l => (ξ l).ambient.property)
  have heX : Space.IsEtaleCovering B S hS (fun l => (ξ l).base.obj.left.obj)
      (fun l => (ιX l).hom.left.hom) :=
    Space.IsEtaleCovering.iso_comp (fun l => (iN l).symm)
      (Space.SpacesEtale.isEtaleCovering_yoneda_map nN cN hVN)
      (fun l => (ξ l).base.obj.left.property)
  have hinj : ∀ (k : L) (V : BigFppfOver B S hS) (a a' : (ξ k).ambient.obj.obj (Opposite.op V)),
      (e k).hom.app _ a = (e k).hom.app _ a' → a = a' :=
    fun k _ _ _ h => eq_of_comp_cofan_eq nA iA cA hVA k h
  have hdisj : ∀ (k l : L), k ≠ l → ∀ (V : BigFppfOver B S hS)
      (a : (ξ k).ambient.obj.obj (Opposite.op V)) (b : (ξ l).ambient.obj.obj (Opposite.op V)),
      (e k).hom.app _ a = (e l).hom.app _ b → IsEmpty ((BigFppfOver.toScheme B S hS).obj V) :=
    fun k l hkl V a b h => Space.SpacesEtale.isEmpty_of_comp_eq_cofan nA cA hVA hkl _ _ h
  have hdisjN : ∀ (k l : L), k ≠ l → ∀ (V : BigFppfOver B S hS)
      (a : (ξ k).base.obj.left.obj.obj (Opposite.op V))
      (b : (ξ l).base.obj.left.obj.obj (Opposite.op V)),
      (ιX k).hom.left.hom.app _ a = (ιX l).hom.left.hom.app _ b →
        IsEmpty ((BigFppfOver.toScheme B S hS).obj V) :=
    fun k l hkl V a b h => Space.SpacesEtale.isEmpty_of_comp_eq_cofan nN cN hVN hkl _ _ h
  have hinjN : ∀ (k : L) (V : BigFppfOver B S hS)
      (a a' : (ξ k).base.obj.left.obj.obj (Opposite.op V)),
      (ιX k).hom.left.hom.app _ a = (ιX k).hom.left.hom.app _ a' → a = a' :=
    fun k _ _ _ h => eq_of_comp_cofan_eq nN iN cN hVN k h
  obtain ⟨G, ψ, -⟩ := exists_hom_of_isEtaleCovering he
    (disjointGluing e hinj hdisj (fun l => (ξ l).ambientMap))
  let β : ∀ l, (algebraicSpaceStackFunctor.{u, w} B S hS).map (ιX l).hom.left ≫
        (((algebraicSpaceStackFunctor.{u, w} B S hS).map X.obj.hom ≫ x) ≫ ι) ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (ιX l).hom.left ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map incl ≫ G) := fun l =>
    eqToHom (gluing_left_leg (ιX l)).symm ≫ (ξ l).comm.hom ≫
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map (ξ l).inclusion ◁ inv (ψ l)) ≫
        eqToHom (gluing_right_leg G (hincl l)).symm
  obtain ⟨α, hα⟩ := exists_hom₂_of_isEtaleCovering (fun l => (ιX l).hom.left) heX β
    (fun k l V a b hab => by
      by_cases hkl : k = l
      · subst hkl
        obtain rfl := hinjN k V a b hab
        rfl
      · have hV := hdisjN k l hkl V a b hab
        have := isHomLift_localComp (ιX k).hom.left (β k) V a _ hab
        have := isHomLift_localComp (ιX l).hom.left (β l) V b _ rfl
        exact AlgebraicStacks.hom_eq_of_isEmpty 𝒳' hV (𝟙 V) _ _)
  have hcoh : ∀ l, (ξ l).comm.hom ≫
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map (ξ l).inclusion ◁ inv (ψ l)) =
        eqToHom (gluing_left_leg (ιX l)) ≫
          ((algebraicSpaceStackFunctor.{u, w} B S hS).map (ιX l).hom.left ◁ α) ≫
            eqToHom (gluing_right_leg G (hincl l)) := by
    intro l
    rw [hα l]
    simp only [β, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      eqToHom_trans, Category.comp_id]
  let GD : GluingDatum.{u, w, u} (hι := hι) (hx := hx) X :=
    { ambient := Y
      inclusion := incl
      ambientMap := G
      isSmooth_ambientMap := isSmooth_of_isEtaleCovering G e he
        (fun l => AlgebraicStacks.isSmooth_of_twoIso B S hS (asIso (ψ l)).symm
          (ξ l).isSmooth_ambientMap)
      comm := asIso α
      K := L
      ξ := ξ
      base := ιX
      e := e
      inclusion_comp := hincl
      isPullback := hpb
      isEtaleCovering := he
      γ := fun l => inv (ψ l)
      coherence := hcoh }
  refine ⟨⟨GD.glue, rfl⟩, GD.glueHom, fun l => ?_⟩
  change (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift
    ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).map (GD.glueHom l)) (GD.glueHom l)
  infer_instance

end EtaleSmoothLift

end AlgebraicGeometry.Stack

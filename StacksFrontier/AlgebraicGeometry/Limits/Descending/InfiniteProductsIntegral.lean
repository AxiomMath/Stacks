module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Infinite products of integral morphisms

The product over a scheme `S` of an arbitrary family of schemes integral over `S` is again
integral over `S`. The product over `S` is the categorical product of the objects `Over.mk (f i)`
in `Over S`; its existence follows from `AlgebraicGeometry.hasProduct_of_isAffineHom`, since an
integral morphism is affine.

## Main results

* `AlgebraicGeometry.isIntegralHom_product`: the structure morphism of the product over `S` of a
  family of integral morphisms is integral.

## Implementation notes

Affineness of the structure morphism is read off from the projection onto the empty subproduct,
which is the terminal object of `Over S`. Integrality of a section over an affine open `U` is
then obtained by writing the product as the limit of its finite subproducts, pulling the section
back to a finite stage, where the corresponding structure morphism is integral because
integrality is stable under finite products.

## References

* [Stacks Project, Tag 0CNK](https://stacks.math.columbia.edu/tag/0CNK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Limits.ProductsFromFiniteCofiltered

universe u v

namespace AlgebraicGeometry

/-- The structure morphism of the product in `Over K` of a finite family of integral morphisms
is integral. -/
@[ega "II 6.1.5" "(iv), special case"]
private theorem isIntegralHom_over_finiteProduct {K : Scheme.{u}} {α : Type v} [Finite α]
    (Y : α → Over K) [HasFiniteProducts (Over K)]
    (hY : ∀ a, IsIntegralHom (Y a).hom) : IsIntegralHom (∏ᶜ Y).hom := by
  classical
  have := Fintype.ofFinite α
  have : MorphismProperty.RespectsIso @IsIntegralHom :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ (Y : α → Over K), (∀ a, IsIntegralHom (Y a).hom) →
      IsIntegralHom (∏ᶜ Y).hom) ?_ ?_ ?_ α Y hY
  · intro α β _ e ih Z hZ
    have : HasProduct (fun a : α => Z (e a)) :=
      hasProduct_of_equiv_of_iso Z (fun a => Z (e a)) e (fun _ => Iso.refl _)
    let e' : (∏ᶜ fun a : α => Z (e a)) ≅ ∏ᶜ Z := Pi.whiskerEquiv e fun _ => Iso.refl _
    have hSource := ih (fun a : α => Z (e a)) (fun a => hZ (e a))
    have : IsIso e'.hom.left := (Over.forget K).map_isIso e'.hom
    have hcomp : IsIntegralHom ((e'.hom).left ≫ (∏ᶜ Z).hom) := e'.hom.w.symm ▸ hSource
    exact (MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom
      (e'.hom).left (∏ᶜ Z).hom).mp hcomp
  · intro Y hY
    have hP : IsTerminal (∏ᶜ Y) := IsTerminal.ofUniqueHom
      (fun X => Pi.lift fun a => isEmptyElim a)
      (by intro X f; apply Pi.hom_ext; intro a; exact isEmptyElim a)
    let e : (∏ᶜ Y) ≅ ⊤_ (Over K) := hP.uniqueUpToIso terminalIsTerminal
    let eT : (⊤_ (Over K)) ≅ Over.mk (𝟙 K) := terminalIsTerminal.uniqueUpToIso Over.mkIdTerminal
    have hT : IsIntegralHom (Over.mk (𝟙 K)).hom := inferInstanceAs (IsIntegralHom (𝟙 K))
    have : IsIso eT.hom.left := (Over.forget K).map_isIso eT.hom
    have htop : IsIntegralHom (⊤_ (Over K)).hom := by
      have hcomp : IsIntegralHom (eT.hom.left ≫ (Over.mk (𝟙 K)).hom) := inferInstance
      exact eT.hom.w ▸ hcomp
    have : IsIso e.hom.left := (Over.forget K).map_isIso e.hom
    have hcomp : IsIntegralHom (e.hom.left ≫ (⊤_ (Over K)).hom) := inferInstance
    exact e.hom.w ▸ hcomp
  · intro α _ ih Y hY
    have : HasProduct (fun a : α => Y (some a)) := inferInstance
    let R : Over K := ∏ᶜ (fun a : α => Y (some a))
    let e := overOptionProductIso (K := K) (α := α) Y
    have hR : IsIntegralHom R.hom := ih (fun a : α => Y (some a)) (fun a => hY (some a))
    have : IsIntegralHom (Limits.pullback.fst (Y none).hom R.hom) := inferInstance
    have hpb : IsIntegralHom (Limits.pullback.fst (Y none).hom R.hom ≫ (Y none).hom) := by
      have : IsIntegralHom (Y none).hom := hY none
      infer_instance
    have hB : IsIntegralHom (Y none ⨯ R).hom := by
      have hEq : (Over.prodLeftIsoPullback (Y none) R).hom ≫
          (Limits.pullback.fst (Y none).hom R.hom ≫ (Y none).hom) = (Y none ⨯ R).hom := by
        calc
          _ = ((Over.prodLeftIsoPullback (Y none) R).hom ≫
              Limits.pullback.fst (Y none).hom R.hom) ≫ (Y none).hom := by
                simp
          _ = (prod.fst (X := Y none) (Y := R)).left ≫ (Y none).hom := by
                rw [Over.prodLeftIsoPullback_hom_fst]
          _ = (Y none ⨯ R).hom := (prod.fst (X := Y none) (Y := R)).w
      rw [← hEq]
      infer_instance
    have : IsIso e.hom.left := (Over.forget K).map_isIso e.hom
    have hcomp : IsIntegralHom ((e.hom).left ≫ (Y none ⨯ R).hom) := inferInstance
    exact e.hom.w ▸ hcomp

/-- **Stacks Project, Tag 0CNK.** The product over a scheme of an arbitrary family of integral
morphisms is integral over the base. -/
@[stacks 0CNK]
theorem isIntegralHom_product {I : Type u} (S : Scheme.{u})
    (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ S) [∀ i, IsIntegralHom (f i)] :
    letI : HasProduct (fun i ↦ Over.mk (f i)) := hasProduct_of_isAffineHom S T f
    IsIntegralHom (∏ᶜ (fun i ↦ Over.mk (f i))).hom := by
  have : HasProduct (fun i ↦ Over.mk (f i)) := hasProduct_of_isAffineHom S T f
  let g := (∏ᶜ (fun i ↦ Over.mk (f i))).hom
  have hAffine : IsAffineHom g := by
    let J₀ : (Finset (Discrete I))ᵒᵖ := Opposite.op ∅
    let E := (liftToFinsetObj (Discrete.functor (fun i ↦ Over.mk (f i)))).obj J₀
    let p := (finiteSubproductsCone (fun i ↦ Over.mk (f i))).π.app J₀ |>.left
    have hp : IsAffineHom p := isAffineHom_finiteSubproductsCone_π_app S T f J₀
    have hEterm : IsTerminal E :=
      IsTerminal.ofUniqueHom (fun Y => Pi.lift (fun x => isEmptyElim x)) fun Y m =>
        Pi.hom_ext _ _ fun x => isEmptyElim x
    have hT : IsTerminal (Over.mk (𝟙 S)) :=
      IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom) fun Y m =>
        Over.OverMorphism.ext (by simpa using m.w)
    let e : E ≅ Over.mk (𝟙 S) := hEterm.uniqueUpToIso hT
    let eS : E.left ≅ S := (Over.forget S).mapIso e
    have hE : IsAffineHom E.hom := by
      rw [← Over.w e.hom]
      have hi : IsAffineHom eS.hom := inferInstance
      simpa [eS] using hi
    have heq : p ≫ E.hom = g := by
      simpa [p, E, J₀, g, finiteSubproductsCone] using
        (Over.w ((finiteSubproductsCone (fun i ↦ Over.mk (f i))).π.app J₀))
    have : IsAffineHom p := hp
    have : IsAffineHom E.hom := hE
    have hcomp : IsAffineHom (p ≫ E.hom) := inferInstance
    rw [← heq]
    exact hcomp
  refine { toIsAffineHom := hAffine, isIntegral_app := ?_ }
  intro U hU s
  classical
  let D := liftToFinsetObj (Discrete.functor (fun i => Over.mk (f i)))
  let coneOver := finiteSubproductsCone (fun i => Over.mk (f i))
  let D' := D ⋙ Over.forget S
  let X := (∏ᶜ (fun i => Over.mk (f i))).left
  let cMapped : Cone D' := (Over.forget S).mapCone coneOver
  let c' : Cone D' := { pt := X, π := cMapped.π }
  have hcMapped : IsLimit cMapped :=
    isLimitOfPreserves (Over.forget S) (finiteSubproductsConeIsLimit (fun i => Over.mk (f i)))
  have ec : cMapped ≅ c' := Cone.ext (Iso.refl _) (by intro J; rfl)
  have hc' : IsLimit c' := IsLimit.ofIsoLimit hcMapped ec
  let J₀ : (Finset (Discrete I))ᵒᵖ := Opposite.op ∅
  let E₀ := D.obj J₀
  have hEterm : IsTerminal E₀ :=
    IsTerminal.ofUniqueHom (fun Y => Pi.lift fun x => isEmptyElim x) fun Y m =>
      Pi.hom_ext _ _ fun x => isEmptyElim x
  have hT : IsTerminal (Over.mk (𝟙 S)) :=
    IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom) fun Y m =>
      Over.OverMorphism.ext (by simpa using m.w)
  let e : E₀ ≅ Over.mk (𝟙 S) := hEterm.uniqueUpToIso hT
  let eS : E₀.left ≅ S := (Over.forget S).mapIso e
  let V : E₀.left.Opens := eS.hom ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage eS.hom
  let hcV := isLimitOpensCone D' c' hc' J₀ V
  have hStage (J : (Finset (Discrete I))ᵒᵖ) : IsIntegralHom (D.obj J).hom := by
    simpa [D, liftToFinsetObj] using
      isIntegralHom_over_finiteProduct (fun x : J.unop => Over.mk (f x.1.as))
        (fun x => inferInstanceAs (IsIntegralHom (f x.1.as)))
  have hMapAffine (J : Over J₀) : IsAffineHom (D'.map J.hom) := by
    have : IsAffineHom (D.obj J₀).hom := (hStage J₀).toIsAffineHom
    have hcomp : IsAffineHom ((D'.map J.hom) ≫ (D.obj J₀).hom) := by
      show IsAffineHom ((D.map J.hom).left ≫ (D.obj J₀).hom)
      rw [Over.w (D.map J.hom)]
      exact (hStage J.left).toIsAffineHom
    exact IsAffineHom.of_comp (D'.map J.hom) (D.obj J₀).hom
  let Eo := opensDiagram D' J₀ V
  let d := opensCone D' c' J₀ V
  have (J : Over J₀) : IsAffine (Eo.obj J) :=
    have : IsAffineHom (D'.map J.hom) := hMapAffine J
    hV.preimage (D'.map J.hom)
  have heqES : (D.obj J₀).hom = eS.hom := by
    dsimp only [eS]
    simpa using (Over.w e.hom).symm
  let p := c'.π.app J₀
  have hg0 : p ≫ (D.obj J₀).hom = g := by
    show (coneOver.π.app J₀).left ≫ (D.obj J₀).hom = coneOver.pt.hom
    exact Over.w (coneOver.π.app J₀)
  have hg : p ≫ eS.hom = g := by
    rw [← heqES]
    exact hg0
  have hOpen : (c'.π.app J₀) ⁻¹ᵁ V = g ⁻¹ᵁ U := by
    show p ⁻¹ᵁ (eS.hom ⁻¹ᵁ U) = g ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_preimage, hg]
  let gpre : X.Opens := g ⁻¹ᵁ U
  let eX : d.pt ≅ (gpre.toScheme) := c'.pt.isoOfEq hOpen
  let s' : Γ(d.pt, ⊤) := (eX.hom.appTop).hom (gpre.topIso.inv.hom s)
  obtain ⟨J, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit Eo d hcV s'
  let q : Scheme := (D.obj J.left).left
  let qhom : q ⟶ S := (D.obj J.left).hom
  have hcompJ : (D'.map J.hom) ≫ eS.hom = qhom := by
    show (D.map J.hom).left ≫ eS.hom = (D.obj J.left).hom
    rw [← heqES]
    exact Over.w (D.map J.hom)
  have hJopen : (D'.map J.hom) ⁻¹ᵁ V = qhom ⁻¹ᵁ U := by
    show (D'.map J.hom) ⁻¹ᵁ (eS.hom ⁻¹ᵁ U) = qhom ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_preimage, hcompJ]
  let qpre : q.Opens := qhom ⁻¹ᵁ U
  let eOpen : Eo.obj J ≅ qpre.toScheme := q.isoOfEq hJopen
  let tBase : Γ(q, qpre) := qpre.topIso.hom (eOpen.inv.appTop t)
  have htBase : (qhom.app U).hom.IsIntegralElem tBase :=
    (hStage J.left).isIntegral_app U hU tBase
  have htE : ((eOpen.hom.appTop).hom.comp
      (qpre.topIso.inv.hom.comp (qhom.app U).hom)).IsIntegralElem t := by
    have h := (htBase.map qpre.topIso.inv.hom).map (eOpen.hom.appTop).hom
    convert h using 1
    simp only [tBase, Iso.hom_inv_id_apply]
    have he : eOpen.inv.appTop ≫ eOpen.hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop]
      simp
    show t = (eOpen.inv.appTop ≫ eOpen.hom.appTop) t
    rw [he]
    rfl
  have htC : (((d.π.app J).appTop).hom.comp
      ((eOpen.hom.appTop).hom.comp
        (qpre.topIso.inv.hom.comp (qhom.app U).hom))).IsIntegralElem
      (((d.π.app J).appTop).hom t) := htE.map ((d.π.app J).appTop).hom
  rw [ht] at htC
  let Jt : Over J₀ := Over.mk (𝟙 J₀)
  let m : J ⟶ Jt := Over.homMk J.hom
  have hOpenT : (D'.map Jt.hom) ⁻¹ᵁ V = V := by
    apply SetLike.ext
    intro x
    simp [Jt]
  let eT : Eo.obj Jt ≅ V.toScheme := (D'.obj J₀).isoOfEq hOpenT
  have heT : eT.hom ≫ V.ι = (opensDiagramι D' J₀ V).app Jt := by
    show ((D'.obj J₀).isoOfEq hOpenT).hom ≫ V.ι = _
    exact Scheme.isoOfEq_hom_ι _ _
  have heOpen : eOpen.hom ≫ qpre.ι = (opensDiagramι D' J₀ V).app J := by
    show (q.isoOfEq hJopen).hom ≫ qpre.ι = _
    exact Scheme.isoOfEq_hom_ι _ _
  have hNat : Eo.map m ≫ (opensDiagramι D' J₀ V).app Jt =
      (opensDiagramι D' J₀ V).app J ≫ D'.map J.hom := by
    simpa [Eo, m] using (opensDiagramι D' J₀ V).naturality m
  have hProj : d.π.app Jt ≫ (opensDiagramι D' J₀ V).app Jt =
      (c'.π.app J₀ ⁻¹ᵁ V).ι ≫ c'.π.app J₀ := by
    dsimp [d, opensCone, opensDiagramι, Jt]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hStageBase : d.π.app Jt ≫ eT.hom ≫ V.ι =
      (c'.π.app J₀ ⁻¹ᵁ V).ι ≫ c'.π.app J₀ := by
    rw [heT]
    exact hProj
  have hbase : d.π.app J ≫ Eo.map m ≫ eT.hom ≫ V.ι ≫ eS.hom =
      (c'.π.app J₀ ⁻¹ᵁ V).ι ≫ g := by
    have hConeBase : d.π.app J ≫ Eo.map m ≫ eT.hom ≫ V.ι ≫ eS.hom =
        d.π.app Jt ≫ eT.hom ≫ V.ι ≫ eS.hom := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ eT.hom ≫ V.ι ≫ eS.hom) (d.w m)
    have hStageBaseS : d.π.app Jt ≫ eT.hom ≫ V.ι ≫ eS.hom =
        (c'.π.app J₀ ⁻¹ᵁ V).ι ≫ g := by
      calc
        _ = ((c'.π.app J₀ ⁻¹ᵁ V).ι ≫ c'.π.app J₀) ≫ eS.hom :=
          congrArg (fun k => k ≫ eS.hom) hStageBase
        _ = (c'.π.app J₀ ⁻¹ᵁ V).ι ≫ g := by
          rw [Category.assoc, hg]
    exact hConeBase.trans hStageBaseS
  have hRestrictStage : eOpen.hom ≫ (qhom ∣_ U) =
      Eo.map m ≫ eT.hom ≫ (eS.hom ∣_ U) := by
    apply (cancel_mono U.ι).1
    show eOpen.hom ≫ ((qhom ∣_ U) ≫ U.ι) =
      Eo.map m ≫ eT.hom ≫ ((eS.hom ∣_ U) ≫ U.ι)
    rw [morphismRestrict_ι, morphismRestrict_ι]
    calc
      _ = (opensDiagramι D' J₀ V).app J ≫ qhom := by
        show (eOpen.hom ≫ qpre.ι) ≫ qhom = _
        rw [heOpen]
      _ = (opensDiagramι D' J₀ V).app J ≫ D'.map J.hom ≫ eS.hom := by
        rw [hcompJ]
      _ = Eo.map m ≫ (opensDiagramι D' J₀ V).app Jt ≫ eS.hom := by
        rw [reassoc_of% hNat]
      _ = Eo.map m ≫ eT.hom ≫ V.ι ≫ eS.hom := by
        simpa [Category.assoc] using
          (congrArg (fun k => Eo.map m ≫ k ≫ eS.hom) heT).symm
  have hEX : eX.hom ≫ (g ⁻¹ᵁ U).ι = (c'.π.app J₀ ⁻¹ᵁ V).ι := by
    show (c'.pt.isoOfEq hOpen).hom ≫ (g ⁻¹ᵁ U).ι = _
    exact Scheme.isoOfEq_hom_ι c'.pt hOpen
  have hscheme : d.π.app J ≫ eOpen.hom ≫ (qhom ∣_ U) = eX.hom ≫ (g ∣_ U) := by
    apply (cancel_mono U.ι).1
    show d.π.app J ≫ (eOpen.hom ≫ (qhom ∣_ U)) ≫ U.ι = (eX.hom ≫ (g ∣_ U)) ≫ U.ι
    rw [hRestrictStage]
    show d.π.app J ≫ Eo.map m ≫ eT.hom ≫ ((eS.hom ∣_ U) ≫ U.ι) =
      eX.hom ≫ ((g ∣_ U) ≫ U.ι)
    rw [morphismRestrict_ι, morphismRestrict_ι, hbase]
    show (c'.π.app J₀ ⁻¹ᵁ V).ι ≫ g = (eX.hom ≫ (g ⁻¹ᵁ U).ι) ≫ g
    rw [hEX]
    rfl
  let φ : Γ(d.pt, ⊤) →+* Γ(X, gpre) :=
    (gpre.topIso.hom).hom.comp (eX.inv.appTop).hom
  let fC : Γ(S, U) →+* Γ(d.pt, ⊤) :=
    ((d.π.app J).appTop).hom.comp
      ((eOpen.hom.appTop).hom.comp
        (qpre.topIso.inv.hom.comp (qhom.app U).hom))
  have hTargetInt : (φ.comp fC).IsIntegralElem (φ s') := htC.map φ
  have hq : qpre.topIso.inv.hom.comp (qhom.app U).hom =
      ((qhom ∣_ U).appTop).hom.comp U.topIso.inv.hom := by
    have hsq : U.topIso.hom ≫ qhom.appLE U qpre le_rfl =
        (qhom.resLE U qpre le_rfl).appTop ≫ qpre.topIso.hom :=
      (arrowResLEAppIso qhom U qpre le_rfl).hom.w
    have hUtop : U.topIso.inv ≫ U.topIso.hom = 𝟙 _ := U.topIso.inv_hom_id
    have hVtop : qpre.topIso.hom ≫ qpre.topIso.inv = 𝟙 _ := qpre.topIso.hom_inv_id
    have hcat' : qhom.appLE U qpre le_rfl ≫ qpre.topIso.inv =
        U.topIso.inv ≫ (qhom.resLE U qpre le_rfl).appTop := by
      have h1 : qhom.appLE U qpre le_rfl =
          U.topIso.inv ≫ ((qhom.resLE U qpre le_rfl).appTop ≫ qpre.topIso.hom) := by
        calc
          _ = (U.topIso.inv ≫ U.topIso.hom) ≫ qhom.appLE U qpre le_rfl := by
            rw [hUtop]
            simp
          _ = U.topIso.inv ≫ (U.topIso.hom ≫ qhom.appLE U qpre le_rfl) := by
            simp only [Category.assoc]
          _ = U.topIso.inv ≫ ((qhom.resLE U qpre le_rfl).appTop ≫ qpre.topIso.hom) :=
            congrArg (fun k => U.topIso.inv ≫ k) hsq
      calc
        _ = (U.topIso.inv ≫ ((qhom.resLE U qpre le_rfl).appTop ≫ qpre.topIso.hom)) ≫
            qpre.topIso.inv := congrArg (fun k => k ≫ qpre.topIso.inv) h1
        _ = U.topIso.inv ≫ (qhom.resLE U qpre le_rfl).appTop := by
          simp only [Category.assoc, hVtop, Category.comp_id]
    have hcat : qhom.app U ≫ qpre.topIso.inv = U.topIso.inv ≫ (qhom ∣_ U).appTop := by
      simpa only [qhom.app_eq_appLE, ← Scheme.Hom.resLE_eq_morphismRestrict] using hcat'
    simpa only [CommRingCat.hom_comp, RingHom.comp_assoc] using
      congrArg CommRingCat.Hom.hom hcat
  have hAppEq : ((d.π.app J).appTop).hom.comp
      ((eOpen.hom.appTop).hom.comp (((qhom ∣_ U).appTop).hom)) =
      (eX.hom.appTop).hom.comp (((g ∣_ U).appTop).hom) := by
    have h := congrArg (fun k : Scheme.Hom _ _ => k.appTop) hscheme
    simp only [Scheme.Hom.comp_appTop] at h
    simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom h
  have hgRestrict : gpre.topIso.hom.hom.comp
      (((g ∣_ U).appTop).hom.comp U.topIso.inv.hom) = (g.app U).hom := by
    have hsq : U.topIso.hom ≫ g.appLE U gpre le_rfl =
        (g.resLE U gpre le_rfl).appTop ≫ gpre.topIso.hom :=
      (arrowResLEAppIso g U gpre le_rfl).hom.w
    have hcat' : U.topIso.inv ≫ (g.resLE U gpre le_rfl).appTop ≫ gpre.topIso.hom =
        g.appLE U gpre le_rfl := by
      rw [← hsq, Iso.inv_hom_id_assoc]
    have hcat : U.topIso.inv ≫ (g ∣_ U).appTop ≫ gpre.topIso.hom = g.app U := by
      simpa only [← Scheme.Hom.resLE_eq_morphismRestrict, g.app_eq_appLE] using hcat'
    simpa only [CommRingCat.hom_comp, RingHom.comp_assoc] using
      congrArg CommRingCat.Hom.hom hcat
  have hMap : φ.comp fC = (g.app U).hom := by
    dsimp only [φ, fC]
    rw [hq]
    calc
      _ = (gpre.topIso.hom.hom).comp
          ((eX.inv.appTop).hom.comp
            (((((d.π.app J).appTop).hom.comp
              ((eOpen.hom.appTop).hom.comp ((qhom ∣_ U).appTop).hom))).comp
              U.topIso.inv.hom)) := by
          simp only [← RingHom.comp_assoc]
      _ = (gpre.topIso.hom.hom).comp
          ((eX.inv.appTop).hom.comp
            ((((eX.hom.appTop).hom.comp ((g ∣_ U).appTop).hom)).comp
              U.topIso.inv.hom)) := by rw [hAppEq]
      _ = (gpre.topIso.hom.hom).comp
          (((eX.inv.appTop).hom.comp (eX.hom.appTop).hom).comp
            (((g ∣_ U).appTop).hom.comp U.topIso.inv.hom)) := by
          simp only [RingHom.comp_assoc]
      _ = (gpre.topIso.hom.hom).comp
          (((g ∣_ U).appTop).hom.comp U.topIso.inv.hom) := by
          have hid : (eX.inv.appTop).hom.comp (eX.hom.appTop).hom = RingHom.id _ := by
            have hidCat : eX.hom.appTop ≫ eX.inv.appTop = 𝟙 _ := by
              rw [← Scheme.Hom.comp_appTop]
              simp
            simpa only [CommRingCat.hom_comp, CommRingCat.hom_id] using
              congrArg CommRingCat.Hom.hom hidCat
          rw [hid]
          simp
      _ = (g.app U).hom := hgRestrict
  have hElt : φ s' = s := by
    have hIso : (eX.inv.appTop).hom.comp (eX.hom.appTop).hom = RingHom.id _ := by
      have hIsoCat : eX.hom.appTop ≫ eX.inv.appTop = 𝟙 _ := by
        rw [← Scheme.Hom.comp_appTop]
        simp
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_id] using
        congrArg CommRingCat.Hom.hom hIsoCat
    have hOpenIso : gpre.topIso.hom.hom.comp gpre.topIso.inv.hom = RingHom.id _ := by
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_id] using
        congrArg CommRingCat.Hom.hom gpre.topIso.inv_hom_id
    have hComp : (gpre.topIso.hom.hom).comp
        ((eX.inv.appTop).hom.comp
          ((eX.hom.appTop).hom.comp gpre.topIso.inv.hom)) = RingHom.id _ := by
      calc
        _ = (gpre.topIso.hom.hom).comp
            (((eX.inv.appTop).hom.comp (eX.hom.appTop).hom).comp gpre.topIso.inv.hom) := by
          simp only [RingHom.comp_assoc]
        _ = (gpre.topIso.hom.hom).comp ((RingHom.id _).comp gpre.topIso.inv.hom) := by
          rw [hIso]
        _ = (gpre.topIso.hom.hom).comp gpre.topIso.inv.hom := by simp
        _ = RingHom.id _ := hOpenIso
    show ((gpre.topIso.hom.hom).comp
      ((eX.inv.appTop).hom.comp
        ((eX.hom.appTop).hom.comp gpre.topIso.inv.hom))) s = s
    simpa only [RingHom.id_apply] using congrArg (fun k => k s) hComp
  rw [← hMap, ← hElt]
  exact hTargetInt

end AlgebraicGeometry

end

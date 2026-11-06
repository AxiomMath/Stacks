module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.Deformation.FormalObject.HomEquivalenceMain
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism.RepresentedRestriction

/-!
# Morphisms from a represented functor and formal objects (Stacks 06SK)

For a complete local algebra `R`, morphisms over the Artinian base from the restriction of
the functor represented by `R` to a category cofibered in groupoids are equivalent to formal
objects over `R`.

The Stacks construction, carried out here, factors the equivalence in two steps. The
restriction of the represented functor is the unit of the completion adjunction of Stacks
06HA, so morphisms out of it into `p` correspond to morphisms out of `R` into the completion
of `p`; and a morphism out of the represented object in the completed category is, by
2-Yoneda, an object of the completion over `R`, i.e. a formal object over `R`. Concretely
the equivalence evaluates a morphism at the canonical Artinian quotient points of `R`,
which is how its inverse and all its coherences are produced.

## Main results

* `Deformation.representableMorphismFormalObjectEquivalence`: **Stacks 06SK**, the
  equivalence of categories.

## Implementation notes

The restricted represented functor is `Deformation.restrictedCoyoneda`. Its associated
cofibered set is the category of elements. The right-hand category is the strict fibre of
`Deformation.FormalObject.projection` over `R`. The equivalence evaluates a morphism at the
canonical Artinian quotient points of `R`. The evaluation isomorphisms lie over the identity
of each quotient, and commute with quotient transition arrows and with morphisms of
represented morphisms. The compatibility with Stacks 06HA records the source's construction
as completion followed by 2-Yoneda evaluation.

## References

* [Stacks Project, Tag 06SK](https://stacks.math.columbia.edu/tag/06SK)
-/

universe u v w uF vF

namespace Deformation

open CategoryTheory

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

@[expose] public section

-- Resource bound, not a logical one: the quotient-level coherences of the equivalence
-- compose five isomorphisms of based functors, whose `whnf` cost exceeds the default budget.
-- Without it, elaboration reports `(deterministic) timeout at `whnf`` at the declaration header and
-- inside the `transition_comm` field.  Splitting the field proofs into separate
-- declarations does not help: each of them alone is already larger than the default
-- 200000-heartbeat budget.
set_option maxHeartbeats 1600000 in
/-- Morphisms from the restriction of the functor represented by `R` to a category
cofibered in groupoids are canonically equivalent to formal objects over `R`. -/
@[stacks 06SK]
public noncomputable def representableMorphismFormalObjectEquivalence
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    RepresentableMorphismFormalObjectEquivalence p R := by
  let hq := representedProjection_cofibered R
  let H := completionHomEquivalence p
    (representedProjection R) hp hq
  let C := representedHomPrecompositionEquivalence p R
  let V := evaluationEquivalence
    (formalObjectProjection_isCofiberedInGroupoids p hp) R
  let E := (C.symm.trans H.equiv).trans V
  let levelIsoData : ∀ (φ : BasedFunctor
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p)) (n : ℕ),
      { i : Iso (φ.obj ((restrictedCoyoneda R).elementsMk (AdicTruncation.obj R n)
          (canonicalQuotientPoint R n)))
          ((E.functor.obj φ).1.level n) //
        p.IsHomLift (𝟙 (AdicTruncation.obj R n)) i.hom } := by
    intro φ n
    let ψ := C.inverse.obj φ
    let P := adicPushforwardChoice (representedProjection R) hq
    let X : (coyoneda.obj (Opposite.op R)).Elements := representedIdentityElement R
    let Xb : (BasedCategory.ofFunctor (representedProjection R)).obj := X
    let qpt : (restrictedCoyoneda R).Elements :=
      (restrictedCoyoneda R).elementsMk (AdicTruncation.obj R n) (canonicalQuotientPoint R n)
    let qptb : (BasedCategory.ofFunctor
        (Functor.Elements.π (restrictedCoyoneda R))).obj := qpt
    let qptR : (BasedCategory.ofFunctor
        (Restriction.projection (p := representedProjection R))).obj :=
      (restrictedRepresentableInclusion R).obj qpt
    change { i : Iso (φ.obj qptb) ((E.functor.obj φ).1.level n) //
      p.IsHomLift (𝟙 (AdicTruncation.obj R n)) i.hom }
    have hlevel :
        (((unitBasedFunctor (representedProjection R) hq).comp
          (completionMap ψ)).obj Xb).level n =
          ψ.obj (P.level X n) := by
      change ((completionMap ψ).obj
        ((completionUnit (representedProjection R) hq).functor.obj X)).level n = _
      rw [completionMap_obj_level]
      rw [(completionUnit (representedProjection R) hq).level X n]
    have htarget : (E.functor.obj φ).1.level n = ψ.obj (P.level X n) := by
      change (V.functor.obj (H.equiv.functor.obj ψ)).1.level n = _
      rw [H.forward ψ]
      change ((evaluation (q := FormalObject.projection (p := p)) R).obj
        ((unitBasedFunctor (representedProjection R) hq).comp
          (completionMap ψ))).1.level n = _
      change (((unitBasedFunctor (representedProjection R) hq).comp
        (completionMap ψ)).obj Xb).level n = _
      exact hlevel
    have hpt : (representedRestrictionInverse R).obj (P.level X n) = qpt :=
      representedRestrictionInverse_adicLevel_eq R hq n
    let qptL := (restrictedRepresentableInclusion R).obj
      ((representedRestrictionInverse R).obj (P.level X n))
    have heqR : qptR = qptL := by
      dsimp [qptR, qptL]
      exact congrArg (restrictedRepresentableInclusion R).obj hpt.symm
    have heqFun : (C.functor.obj ψ).obj qptb = ψ.obj qptR := by
      dsimp [C, representedHomPrecompositionEquivalence,
        basedPrecompositionEquivalence, qptR]
      rfl
    let hrest := representedRestrictionCounitIso R (P.level X n)
    let hi₂ : (C.functor.obj ψ).obj qptb ≅ ψ.obj (P.level X n) :=
      (eqToIso heqFun) ≪≫ (eqToIso (congrArg ψ.obj heqR)) ≪≫ ψ.mapIso hrest
    let ciso := C.counitIso.app φ
    let hi₁ : (C.functor.obj ψ).obj qptb ≅ φ.obj qptb := by
      refine ⟨ciso.hom.app qptb, ciso.inv.app qptb, ?_, ?_⟩
      · have h := congrArg (fun t => t.app qptb) ciso.hom_inv_id
        exact h
      · have h := congrArg (fun t => t.app qptb) ciso.inv_hom_id
        exact h
    have h1 : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) hi₁.symm.hom := by
      change p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (ciso.inv.app qptb)
      exact ciso.inv.isHomLift' qptb
    have hrestLift :
        (Restriction.projection (p := representedProjection R)).IsHomLift
          (𝟙 (P.level X n).base) hrest.hom := by
      change (Restriction.projection (p := representedProjection R)).IsHomLift
        (𝟙 ((Restriction.projection
          (p := representedProjection R)).obj (P.level X n))) hrest.hom
      exact (representedRestrictionCounitBasedIso R).hom.isHomLift' (P.level X n)
    have h2raw : (BasedCategory.ofFunctor p).p.IsHomLift
        (𝟙 (P.level X n).base) (ψ.map hrest.hom) :=
      (ψ.isHomLift_iff (𝟙 (P.level X n).base) hrest.hom).2 hrestLift
    have h2raw' : p.IsHomLift (𝟙 (P.level X n).base) (ψ.map hrest.hom) := h2raw
    have hbase : (P.level X n).base = AdicTruncation.obj R n := by
      simpa [representedRestrictionInverse] using congrArg
        (fun z : (restrictedCoyoneda R).Elements => z.obj) hpt
    have hfunbase : p.obj ((C.functor.obj ψ).obj qptb) = AdicTruncation.obj R n := by
      rw [heqFun]
      calc
        p.obj (ψ.obj qptR) =
            (Restriction.projection
              (p := representedProjection R)).obj qptR := ψ.w_obj qptR
        _ = AdicTruncation.obj R n := rfl
    have hfunCast : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (eqToHom heqFun) :=
      IsHomLift.eqToHom_domain_lift_id (p := p) heqFun hfunbase
    have h2castSource :
        (Restriction.projection (p := representedProjection R)).IsHomLift
          (𝟙 (AdicTruncation.obj R n)) (eqToHom heqR) := by
      apply IsHomLift.eqToHom_domain_lift_id (p :=
        Restriction.projection (p := representedProjection R)) heqR
      rfl
    have h2cast : p.IsHomLift (𝟙 (AdicTruncation.obj R n))
        (ψ.map (eqToHom heqR)) := by
      let : (BasedCategory.ofFunctor (Restriction.projection
          (p := representedProjection R))).p.IsHomLift
          (𝟙 (AdicTruncation.obj R n)) (eqToHom heqR) := h2castSource
      have h := ψ.preserves_isHomLift (𝟙 (AdicTruncation.obj R n)) (eqToHom heqR)
      change p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (ψ.map (eqToHom heqR))
      exact h
    have h2rawQ : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (ψ.map hrest.hom) := by
      rw [← hbase]
      exact h2raw'
    have hc₀₁ : p.IsHomLift (𝟙 (AdicTruncation.obj R n) ≫
        𝟙 (AdicTruncation.obj R n)) (eqToHom heqFun ≫ ψ.map (eqToHom heqR)) := by
      let : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (eqToHom heqFun) := hfunCast
      let : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (ψ.map (eqToHom heqR)) := h2cast
      exact IsHomLift.comp (p := p) (f := 𝟙 (AdicTruncation.obj R n))
        (g := 𝟙 (AdicTruncation.obj R n)) (φ := eqToHom heqFun)
        (ψ := ψ.map (eqToHom heqR))
    have h01 : p.IsHomLift (𝟙 (AdicTruncation.obj R n))
        (eqToHom heqFun ≫ ψ.map (eqToHom heqR)) := by
      rw [← Category.id_comp (𝟙 (AdicTruncation.obj R n))]
      exact hc₀₁
    have hmap : ψ.map (eqToHom heqR) = eqToHom (congrArg ψ.obj heqR) :=
      eqToHom_map ψ.toFunctor heqR
    have hrestMapHom : (ψ.mapIso hrest).hom = ψ.map hrest.hom :=
      CategoryTheory.Functor.mapIso_hom ψ.toFunctor hrest
    have hArrow : hi₂.hom =
        (eqToHom heqFun ≫ ψ.map (eqToHom heqR)) ≫ ψ.map hrest.hom := by
      dsimp [hi₂]
      rw [← hmap, hrestMapHom, ← Category.assoc]
    have h2 : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) hi₂.hom := by
      let : p.IsHomLift (𝟙 (AdicTruncation.obj R n))
          (eqToHom heqFun ≫ ψ.map (eqToHom heqR)) := h01
      let : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (ψ.map hrest.hom) := h2rawQ
      have hc := IsHomLift.comp (p := p) (f := 𝟙 (AdicTruncation.obj R n))
        (g := 𝟙 (AdicTruncation.obj R n))
        (φ := eqToHom heqFun ≫ ψ.map (eqToHom heqR)) (ψ := ψ.map hrest.hom)
      rw [hArrow]
      rw [← Category.id_comp (𝟙 (AdicTruncation.obj R n))]
      exact hc
    have hfinalBase : p.obj (ψ.obj (P.level X n)) = AdicTruncation.obj R n := by
      calc
        p.obj (ψ.obj (P.level X n)) =
            (Restriction.projection
              (p := representedProjection R)).obj (P.level X n) := ψ.w_obj (P.level X n)
        _ = AdicTruncation.obj R n := by exact hbase
    have hfinalCast : p.IsHomLift (𝟙 (AdicTruncation.obj R n))
        (eqToHom htarget.symm) :=
      IsHomLift.eqToHom_domain_lift_id (p := p) htarget.symm hfinalBase
    let iso := hi₁.symm ≪≫ hi₂ ≪≫ eqToIso htarget.symm
    have hIsoArrow : iso.hom =
        (hi₁.symm.hom ≫ hi₂.hom) ≫ eqToHom htarget.symm :=
      (Category.assoc _ _ _).symm
    have hcomp : p.IsHomLift (𝟙 (AdicTruncation.obj R n) ≫
        𝟙 (AdicTruncation.obj R n)) (hi₁.symm.hom ≫ hi₂.hom) := by
      let : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) hi₁.symm.hom := h1
      let : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) hi₂.hom := h2
      exact IsHomLift.comp (p := p) (f := 𝟙 (AdicTruncation.obj R n))
        (g := 𝟙 (AdicTruncation.obj R n)) (φ := hi₁.symm.hom) (ψ := hi₂.hom)
    have hcompFinal : p.IsHomLift (𝟙 (AdicTruncation.obj R n) ≫
        𝟙 (AdicTruncation.obj R n))
        ((hi₁.symm.hom ≫ hi₂.hom) ≫ eqToHom htarget.symm) := by
      have hcompId : p.IsHomLift (𝟙 (AdicTruncation.obj R n))
          (hi₁.symm.hom ≫ hi₂.hom) := by
        rw [← Category.id_comp (𝟙 (AdicTruncation.obj R n))]
        exact hcomp
      let : p.IsHomLift (𝟙 (AdicTruncation.obj R n))
          (hi₁.symm.hom ≫ hi₂.hom) := hcompId
      let : p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (eqToHom htarget.symm) := hfinalCast
      exact IsHomLift.comp (p := p) (f := 𝟙 (AdicTruncation.obj R n))
        (g := 𝟙 (AdicTruncation.obj R n))
        (φ := hi₁.symm.hom ≫ hi₂.hom) (ψ := eqToHom htarget.symm)
    refine ⟨iso, ?_⟩
    rw [hIsoArrow]
    change p.IsHomLift (𝟙 (AdicTruncation.obj R n))
      ((hi₁.symm.hom ≫ hi₂.hom) ≫ eqToHom htarget.symm)
    rw [← Category.id_comp (𝟙 (AdicTruncation.obj R n))]
    exact hcompFinal
  let mapCommProof :
      ∀ {φ ψ : BasedFunctor
        (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
        (BasedCategory.ofFunctor p)} (t : φ ⟶ ψ) (n : ℕ),
        t.toNatTrans.app ((restrictedCoyoneda R).elementsMk (AdicTruncation.obj R n)
          (canonicalQuotientPoint R n)) ≫
            (levelIsoData ψ n).val.hom =
          (levelIsoData φ n).val.hom ≫ ((E.functor.map t).1).app n := fun {φ ψ} t n => by
      let ψ₁ := C.inverse.obj φ
      let ψ₂ := C.inverse.obj ψ
      let s := C.inverse.map t
      let qpt : (restrictedCoyoneda R).Elements :=
        (restrictedCoyoneda R).elementsMk (AdicTruncation.obj R n) (canonicalQuotientPoint R n)
      let qptb : (BasedCategory.ofFunctor
          (Functor.Elements.π (restrictedCoyoneda R))).obj := qpt
      let P := adicPushforwardChoice (representedProjection R) hq
      let U := completionUnit (representedProjection R) hq
      let Z₁ : FormalObject p := (E.functor.obj φ).val
      let Z₂ : FormalObject p := (E.functor.obj ψ).val
      let X : (coyoneda.obj (Opposite.op R)).Elements := representedIdentityElement R
      let Xb : (BasedCategory.ofFunctor (representedProjection R)).obj := X
      let qptR := (restrictedRepresentableInclusion R).obj qpt
      let qptL := (restrictedRepresentableInclusion R).obj
        ((representedRestrictionInverse R).obj (P.level X n))
      have hpt : (representedRestrictionInverse R).obj (P.level X n) = qpt :=
        representedRestrictionInverse_adicLevel_eq R hq n
      have heqR : qptR = qptL := by
        dsimp [qptR, qptL]
        exact congrArg (restrictedRepresentableInclusion R).obj hpt.symm
      have heqFun₁ : (C.functor.obj ψ₁).obj qptb = ψ₁.obj qptR := by
        dsimp [C, representedHomPrecompositionEquivalence,
          basedPrecompositionEquivalence, qptR]
        rfl
      have heqFun₂ : (C.functor.obj ψ₂).obj qptb = ψ₂.obj qptR := by
        dsimp [C, representedHomPrecompositionEquivalence,
          basedPrecompositionEquivalence, qptR]
        rfl
      have htarget₁ : Z₁.level n = ψ₁.obj (P.level X n) := by
        change (V.functor.obj (H.equiv.functor.obj ψ₁)).1.level n = _
        rw [H.forward ψ₁]
        change ((evaluation (q := FormalObject.projection (p := p)) R).obj
          ((unitBasedFunctor (representedProjection R) hq).comp
            (completionMap ψ₁))).1.level n = _
        change ((completionMap ψ₁).obj
          ((completionUnit (representedProjection R) hq).functor.obj X)).level n = _
        rw [completionMap_obj_level]
        rw [(completionUnit (representedProjection R) hq).level X n]
      have htarget₂ : Z₂.level n = ψ₂.obj (P.level X n) := by
        change (V.functor.obj (H.equiv.functor.obj ψ₂)).1.level n = _
        rw [H.forward ψ₂]
        change ((evaluation (q := FormalObject.projection (p := p)) R).obj
          ((unitBasedFunctor (representedProjection R) hq).comp
            (completionMap ψ₂))).1.level n = _
        change ((completionMap ψ₂).obj
          ((completionUnit (representedProjection R) hq).functor.obj X)).level n = _
        rw [completionMap_obj_level]
        rw [(completionUnit (representedProjection R) hq).level X n]
      have htargetUnit₁ : Z₁.level n =
          ψ₁.obj ((U.functor.obj X).level n) := by
        change (V.functor.obj (H.equiv.functor.obj ψ₁)).1.level n = _
        rw [H.forward ψ₁]
        change ((evaluation (q := FormalObject.projection (p := p)) R).obj
          ((unitBasedFunctor (representedProjection R) hq).comp
            (completionMap ψ₁))).1.level n = _
        change ((completionMap ψ₁).obj
          (U.functor.obj X)).level n = _
        rw [completionMap_obj_level]
      have htargetUnit₂ : Z₂.level n =
          ψ₂.obj ((U.functor.obj X).level n) := by
        change (V.functor.obj (H.equiv.functor.obj ψ₂)).1.level n = _
        rw [H.forward ψ₂]
        change ((evaluation (q := FormalObject.projection (p := p)) R).obj
          ((unitBasedFunctor (representedProjection R) hq).comp
            (completionMap ψ₂))).1.level n = _
        change ((completionMap ψ₂).obj
          (U.functor.obj X)).level n = _
        rw [completionMap_obj_level]
      let hrest := representedRestrictionCounitIso R (P.level X n)
      let ciso₁ := C.counitIso.app φ
      let ciso₂ := C.counitIso.app ψ
      let hi₁₁ : Iso ((C.functor.obj ψ₁).obj qptb) (φ.obj qptb) := by
        refine ⟨ciso₁.hom.app qptb, ciso₁.inv.app qptb, ?_, ?_⟩
        · exact congrArg (fun t => t.app qptb) ciso₁.hom_inv_id
        · exact congrArg (fun t => t.app qptb) ciso₁.inv_hom_id
      let hi₁₂ : Iso ((C.functor.obj ψ₂).obj qptb) (ψ.obj qptb) := by
        refine ⟨ciso₂.hom.app qptb, ciso₂.inv.app qptb, ?_, ?_⟩
        · exact congrArg (fun t => t.app qptb) ciso₂.hom_inv_id
        · exact congrArg (fun t => t.app qptb) ciso₂.inv_hom_id
      let hi₂₁ := eqToIso heqFun₁ ≪≫ eqToIso (congrArg ψ₁.obj heqR) ≪≫ ψ₁.mapIso hrest
      let hi₂₂ := eqToIso heqFun₂ ≪≫ eqToIso (congrArg ψ₂.obj heqR) ≪≫ ψ₂.mapIso hrest
      have hHomOne : (levelIsoData φ n).val.hom =
          (hi₁₁.symm.hom ≫ hi₂₁.hom) ≫ eqToHom htarget₁.symm := by
        dsimp [levelIsoData, Iso.trans, Iso.symm, eqToIso]
        exact (Category.assoc _ _ _).symm
      have hHomTwo : (levelIsoData ψ n).val.hom =
          (hi₁₂.symm.hom ≫ hi₂₂.hom) ≫ eqToHom htarget₂.symm := by
        dsimp [levelIsoData, Iso.trans, Iso.symm, eqToIso]
        exact (Category.assoc _ _ _).symm
      have hfm := H.forward_map s X
      have hEMap : ((E.functor.map t).1).app n =
          ((H.equiv.functor.map s).app Xb).app n := by
        rfl
      have hfmN := congrArg (fun f => f.app n) hfm
      let fwd₁ := congrArg (fun f => f.obj Xb) (H.forward ψ₁)
      let fwd₂ := congrArg (fun f => f.obj Xb) (H.forward ψ₂)
      change ((H.equiv.functor.map s).app Xb).app n =
        ((eqToHom fwd₁ ≫
          (completionNatTrans s).app
            ((completionUnit (representedProjection R) hq).functor.obj X) ≫
          eqToHom fwd₂.symm).app n) at hfmN
      change ((H.equiv.functor.map s).app Xb).app n =
        (eqToHom fwd₁).app n ≫
          ((completionNatTrans s).app
            (U.functor.obj X)).app n ≫
          (eqToHom fwd₂.symm).app n at hfmN
      have hcompApp :
          ((completionNatTrans s).app
            (U.functor.obj X)).app n =
          ((completionNatTrans s).toNatTrans.app
            (U.functor.obj X)).app n := rfl
      rw [hcompApp, completionNatTrans_app_level] at hfmN
      have hmapFinalUnit : ((E.functor.map t).1).app n =
          eqToHom htargetUnit₁ ≫ s.app ((U.functor.obj X).level n) ≫
            eqToHom htargetUnit₂.symm := by
        rw [hEMap]
        let formalLevel : (BasedCategory.ofFunctor
            (FormalObject.projection (p := p))).obj ⥤ F := {
          obj := fun ξ => ξ.level n
          map := fun f => f.app n
          map_id := by intro X; rfl
          map_comp := by intro X Y Z f g; rfl }
        have hlevelEq₁ : ((H.equiv.functor.obj ψ₁).obj Xb).level n =
            (((unitBasedFunctor (representedProjection R) hq).comp
              (completionMap ψ₁)).obj Xb).level n :=
          congrArg (fun Z => Z.level n) fwd₁
        have hlevelEq₂ : ((H.equiv.functor.obj ψ₂).obj Xb).level n =
            (((unitBasedFunctor (representedProjection R) hq).comp
              (completionMap ψ₂)).obj Xb).level n :=
          congrArg (fun Z => Z.level n) fwd₂
        have hfwd₁ : (eqToHom fwd₁).app n = eqToHom hlevelEq₁ := by
          change formalLevel.map (eqToHom fwd₁) = _
          exact eqToHom_map formalLevel fwd₁
        have hfwd₂ : (eqToHom fwd₂.symm).app n = eqToHom hlevelEq₂.symm := by
          change formalLevel.map (eqToHom fwd₂.symm) = _
          exact eqToHom_map formalLevel fwd₂.symm
        have hleftCast : (eqToHom fwd₁).app n ≫
            eqToHom (completionMap_obj_level ψ₁
              (U.functor.obj X) n) = eqToHom htargetUnit₁ := by
          rw [hfwd₁]
          exact (eqToHom_trans hlevelEq₁
            (completionMap_obj_level ψ₁
              (U.functor.obj X) n)).trans (by
            have hproof : hlevelEq₁.trans
                (completionMap_obj_level ψ₁
                  (U.functor.obj X) n) = htargetUnit₁ := Subsingleton.elim _ _
            exact congrArg eqToHom hproof)
        have hrightCast :
            eqToHom (completionMap_obj_level ψ₂
              (U.functor.obj X) n).symm ≫ (eqToHom fwd₂.symm).app n =
              eqToHom htargetUnit₂.symm := by
          rw [hfwd₂]
          exact (eqToHom_trans
            (completionMap_obj_level ψ₂
              (U.functor.obj X) n).symm hlevelEq₂.symm).trans (by
            have hproof : (completionMap_obj_level ψ₂
                (U.functor.obj X) n).symm.trans hlevelEq₂.symm = htargetUnit₂.symm :=
              Subsingleton.elim _ _
            exact congrArg eqToHom hproof)
        have hfmN' : ((H.equiv.functor.map s).app Xb).app n =
            eqToHom htargetUnit₁ ≫ s.app ((U.functor.obj X).level n) ≫
              eqToHom htargetUnit₂.symm := by
          let a := (eqToHom fwd₁).app n
          let b := eqToHom (completionMap_obj_level ψ₁
            (U.functor.obj X) n)
          let c := s.app ((U.functor.obj X).level n)
          let d := eqToHom (completionMap_obj_level ψ₂
            (U.functor.obj X) n).symm
          let e := (eqToHom fwd₂.symm).app n
          change ((H.equiv.functor.map s).app Xb).app n =
            a ≫ ((b ≫ c ≫ d) ≫ e) at hfmN
          change a ≫ b = eqToHom htargetUnit₁ at hleftCast
          change d ≫ e = eqToHom htargetUnit₂.symm at hrightCast
          have hcast : ((a ≫ b) ≫ c) ≫ (d ≫ e) =
              (eqToHom htargetUnit₁ ≫ c) ≫ eqToHom htargetUnit₂.symm := by
            rw [hleftCast, hrightCast]
            rfl
          have hreassoc : a ≫ ((b ≫ c ≫ d) ≫ e) =
              ((a ≫ b) ≫ c) ≫ (d ≫ e) := compReassocFive a b c d e
          have hassoc := Category.assoc (eqToHom htargetUnit₁) c
            (eqToHom htargetUnit₂.symm)
          exact hfmN.trans (hreassoc.trans (hcast.trans hassoc))
        exact hfmN'
      let hUlevel := U.level X n
      have hmapU₁ : ψ₁.toFunctor.map (eqToHom hUlevel) =
          eqToHom (congrArg ψ₁.obj hUlevel) := eqToHom_map ψ₁.toFunctor hUlevel
      have hmapU₂ : ψ₂.toFunctor.map (eqToHom hUlevel) =
          eqToHom (congrArg ψ₂.obj hUlevel) := eqToHom_map ψ₂.toFunctor hUlevel
      have hnatU :
          ψ₁.toFunctor.map (eqToHom hUlevel) ≫ s.app (P.level X n) =
            s.app ((U.functor.obj X).level n) ≫ ψ₂.toFunctor.map (eqToHom hUlevel) :=
        s.toNatTrans.naturality (eqToHom hUlevel)
      have hmapUnit : s.app ((U.functor.obj X).level n) =
          ψ₁.toFunctor.map (eqToHom hUlevel) ≫ s.app (P.level X n) ≫
            eqToHom (congrArg ψ₂.obj hUlevel).symm := by
        calc
          s.app ((U.functor.obj X).level n) =
              s.app ((U.functor.obj X).level n) ≫ 𝟙 _ := by simp
          _ = (s.app ((U.functor.obj X).level n) ≫ ψ₂.toFunctor.map (eqToHom hUlevel)) ≫
              eqToHom (congrArg ψ₂.obj hUlevel).symm := by
            rw [hmapU₂]
            simp [Category.assoc]
          _ = (ψ₁.toFunctor.map (eqToHom hUlevel) ≫ s.app (P.level X n)) ≫
              eqToHom (congrArg ψ₂.obj hUlevel).symm := by rw [← hnatU]
          _ = ψ₁.toFunctor.map (eqToHom hUlevel) ≫ s.app (P.level X n) ≫
              eqToHom (congrArg ψ₂.obj hUlevel).symm := Category.assoc _ _ _
      have hleftCastP : eqToHom htargetUnit₁ ≫
          ψ₁.toFunctor.map (eqToHom hUlevel) = eqToHom htarget₁ := by
        rw [hmapU₁]
        exact (eqToHom_trans htargetUnit₁ (congrArg ψ₁.obj hUlevel)).trans (by
          have hproof : htargetUnit₁.trans (congrArg ψ₁.obj hUlevel) = htarget₁ :=
            Subsingleton.elim _ _
          exact congrArg eqToHom hproof)
      have hrightCastP : eqToHom (congrArg ψ₂.obj hUlevel).symm ≫
          eqToHom htargetUnit₂.symm = eqToHom htarget₂.symm :=
        (eqToHom_trans (congrArg ψ₂.obj hUlevel).symm htargetUnit₂.symm).trans (by
          have hproof : (congrArg ψ₂.obj hUlevel).symm.trans htargetUnit₂.symm =
              htarget₂.symm := Subsingleton.elim _ _
          exact congrArg eqToHom hproof)
      let a := eqToHom htargetUnit₁
      let b := ψ₁.toFunctor.map (eqToHom hUlevel)
      let c := s.app (P.level X n)
      let d := eqToHom (congrArg ψ₂.obj hUlevel).symm
      let e := eqToHom htargetUnit₂.symm
      have hchainP : a ≫ ((b ≫ c ≫ d) ≫ e) =
          ((a ≫ b) ≫ c) ≫ (d ≫ e) := compReassocFive a b c d e
      have hcastP : ((a ≫ b) ≫ c) ≫ (d ≫ e) =
          (eqToHom htarget₁ ≫ c) ≫ eqToHom htarget₂.symm := by
        have hleft : a ≫ b = eqToHom htarget₁ := by
          dsimp [a, b]
          rw [eqToHom_map ψ₁.toFunctor hUlevel]
          exact (eqToHom_trans htargetUnit₁ (congrArg ψ₁.obj hUlevel)).trans (by
            have hproof : htargetUnit₁.trans (congrArg ψ₁.obj hUlevel) = htarget₁ :=
              Subsingleton.elim _ _
            exact congrArg eqToHom hproof)
        have hright : d ≫ e = eqToHom htarget₂.symm := by
          dsimp [d, e]
          exact (eqToHom_trans (congrArg ψ₂.obj hUlevel).symm htargetUnit₂.symm).trans (by
            have hproof : (congrArg ψ₂.obj hUlevel).symm.trans htargetUnit₂.symm =
                htarget₂.symm := Subsingleton.elim _ _
            exact congrArg eqToHom hproof)
        have hleftPost := congrArg
          (fun z => (z ≫ c) ≫ (d ≫ e)) hleft
        have hrightPost := congrArg
          (fun z => (eqToHom htarget₁ ≫ c) ≫ z) hright
        exact hleftPost.trans hrightPost
      have hmapFinalP : ((E.functor.map t).1).app n =
          eqToHom htarget₁ ≫ s.app (P.level X n) ≫ eqToHom htarget₂.symm := by
        calc
          _ = eqToHom htargetUnit₁ ≫ s.app ((U.functor.obj X).level n) ≫
              eqToHom htargetUnit₂.symm := hmapFinalUnit
          _ = eqToHom htarget₁ ≫ s.app (P.level X n) ≫ eqToHom htarget₂.symm := by
            rw [hmapUnit]
            change a ≫ ((b ≫ c ≫ d) ≫ e) =
              eqToHom htarget₁ ≫ c ≫ eqToHom htarget₂.symm
            exact hchainP.trans (hcastP.trans
              (Category.assoc (eqToHom htarget₁) c (eqToHom htarget₂.symm)))
      let r : qptR ⟶ P.level X n := eqToHom heqR ≫ hrest.hom
      have hhi₂₁ : hi₂₁.hom = eqToHom heqFun₁ ≫ ψ₁.map r := by
        dsimp [hi₂₁, Iso.trans_hom]
        have hmap : ψ₁.map (eqToHom heqR ≫ hrest.hom) =
            ψ₁.map (eqToHom heqR) ≫ ψ₁.map hrest.hom := ψ₁.map_comp (eqToHom heqR) hrest.hom
        have hrestMapHom : (ψ₁.mapIso hrest).hom = ψ₁.map hrest.hom := rfl
        rw [hrestMapHom, ← eqToHom_map ψ₁.toFunctor heqR, ← hmap]
      have hhi₂₂ : hi₂₂.hom = eqToHom heqFun₂ ≫ ψ₂.map r := by
        dsimp [hi₂₂, Iso.trans_hom]
        have hmap : ψ₂.map (eqToHom heqR ≫ hrest.hom) =
            ψ₂.map (eqToHom heqR) ≫ ψ₂.map hrest.hom := ψ₂.map_comp (eqToHom heqR) hrest.hom
        have hrestMapHom : (ψ₂.mapIso hrest).hom = ψ₂.map hrest.hom := rfl
        rw [hrestMapHom, ← eqToHom_map ψ₂.toFunctor heqR, ← hmap]
      have hCstep : (C.functor.map s).app qptb ≫ eqToHom heqFun₂ =
          eqToHom heqFun₁ ≫ s.app qptR := by
        change s.app qptR ≫ eqToHom heqFun₂ =
          eqToHom heqFun₁ ≫ s.app qptR
        change s.app qptR ≫ 𝟙 _ = 𝟙 _ ≫ s.app qptR
        simp
      have hJ : (C.functor.map s).app qptb ≫ hi₂₂.hom =
          hi₂₁.hom ≫ s.app (P.level X n) := by
        rw [hhi₂₂, hhi₂₁]
        calc
          _ = ((C.functor.map s).app qptb ≫ eqToHom heqFun₂) ≫
                ψ₂.map r := by simp only [Category.assoc]
          _ = (eqToHom heqFun₁ ≫ s.app qptR) ≫ ψ₂.map r := by rw [hCstep]
          _ = eqToHom heqFun₁ ≫ (ψ₁.map r ≫ s.app (P.level X n)) := by
            simpa only [Category.assoc] using
              congrArg (fun z => eqToHom heqFun₁ ≫ z)
                (s.toNatTrans.naturality r).symm
          _ = (eqToHom heqFun₁ ≫ ψ₁.map r) ≫ s.app (P.level X n) :=
            (Category.assoc _ _ _).symm
      have hlast :
          ((ciso₁.inv.app qptb ≫ hi₂₁.hom) ≫ s.app (P.level X n)) ≫
              eqToHom htarget₂.symm =
            (levelIsoData φ n).val.hom ≫ ((E.functor.map t).1).app n := by
        have hcancel : eqToHom htarget₁.symm ≫ eqToHom htarget₁ = 𝟙 _ := by
          calc
            _ = eqToHom (htarget₁.symm.trans htarget₁) := eqToHom_trans _ _
            _ = 𝟙 _ := by
              rw [show htarget₁.symm.trans htarget₁ = rfl by
                apply Subsingleton.elim]
              rfl
        let a := ciso₁.inv.app qptb ≫ hi₂₁.hom
        let b := s.app (P.level X n)
        let c := eqToHom htarget₂.symm
        let d := eqToHom htarget₁.symm
        let e := eqToHom htarget₁
        calc
          _ = a ≫ (b ≫ c) := Category.assoc _ _ _
          _ = a ≫ ((d ≫ e) ≫ (b ≫ c)) := by
            calc
              _ = a ≫ (𝟙 _ ≫ (b ≫ c)) :=
                congrArg (fun z => a ≫ z) (Category.id_comp (b ≫ c)).symm
              _ = a ≫ ((d ≫ e) ≫ (b ≫ c)) :=
                congrArg (fun z => a ≫ (z ≫ (b ≫ c))) hcancel.symm
          _ = a ≫ (d ≫ (e ≫ (b ≫ c))) :=
            congrArg (fun z => a ≫ z) (Category.assoc d e (b ≫ c))
          _ = (a ≫ d) ≫ (e ≫ (b ≫ c)) := (Category.assoc _ _ _).symm
          _ = (a ≫ d) ≫ ((E.functor.map t).1).app n :=
            congrArg (fun z => (a ≫ d) ≫ z) hmapFinalP.symm
          _ = (levelIsoData φ n).val.hom ≫ ((E.functor.map t).1).app n :=
            congrArg (fun z => z ≫ ((E.functor.map t).1).app n) hHomOne.symm
      have hnat : t.app qptb ≫ ciso₂.inv.app qptb =
          ciso₁.inv.app qptb ≫ (C.functor.map s).app qptb := by
        exact congrArg (fun α => α.app qptb) (C.counitIso.inv.naturality t)
      have hJ' : (ciso₁.inv.app qptb ≫ (C.functor.map s).app qptb) ≫ hi₂₂.hom =
          (ciso₁.inv.app qptb ≫ hi₂₁.hom) ≫ s.app (P.level X n) := by
        simpa only [Category.assoc] using
          congrArg (fun z => ciso₁.inv.app qptb ≫ z) hJ
      exact calc
        t.app qptb ≫ (levelIsoData ψ n).val.hom =
            t.app qptb ≫
              ((ciso₂.inv.app qptb ≫ hi₂₂.hom) ≫ eqToHom htarget₂.symm) :=
          congrArg (fun z => t.app qptb ≫ z) hHomTwo
        _ = (t.app qptb ≫ (ciso₂.inv.app qptb ≫ hi₂₂.hom)) ≫
            eqToHom htarget₂.symm := (Category.assoc _ _ _).symm
        _ = ((t.app qptb ≫ ciso₂.inv.app qptb) ≫ hi₂₂.hom) ≫
            eqToHom htarget₂.symm :=
          congrArg (fun z => z ≫ eqToHom htarget₂.symm)
            (Category.assoc _ _ _).symm
        _ = ((ciso₁.inv.app qptb ≫ (C.functor.map s).app qptb) ≫ hi₂₂.hom) ≫
            eqToHom htarget₂.symm :=
          congrArg (fun z => (z ≫ hi₂₂.hom) ≫ eqToHom htarget₂.symm) hnat
        _ = ((ciso₁.inv.app qptb ≫ hi₂₁.hom) ≫ s.app (P.level X n)) ≫
            eqToHom htarget₂.symm :=
          congrArg (fun z => z ≫ eqToHom htarget₂.symm) hJ'
        _ = (levelIsoData φ n).val.hom ≫ ((E.functor.map t).1).app n := hlast
  refine {
    quotientPoint := canonicalQuotientPoint R
    quotientPoint_hom := canonicalQuotientPoint_hom R
    projectionPoint := canonicalQuotientPoint_transition R
    equivalence := E
    levelIso := fun φ n => (levelIsoData φ n).val
    levelIso_over := fun φ n => (levelIsoData φ n).property
    transition_comm := ?_
    map_comm := mapCommProof
    completionComparison := ?_ }
  · intro φ n
    dsimp [levelIsoData, Iso.trans_hom, eqToIso.hom]
    let ψ := C.inverse.obj φ
    let P := adicPushforwardChoice (representedProjection R) hq
    let U := completionUnit (representedProjection R) hq
    let ψF : Restriction
        (p := representedProjection R) ⥤ F := ψ.toFunctor
    let X : (coyoneda.obj (Opposite.op R)).Elements := representedIdentityElement R
    let qpt (m : ℕ) : (restrictedCoyoneda R).Elements :=
      (restrictedCoyoneda R).elementsMk (AdicTruncation.obj R m) (canonicalQuotientPoint R m)
    let qptb (m : ℕ) : (BasedCategory.ofFunctor
        (Functor.Elements.π (restrictedCoyoneda R))).obj := qpt m
    let PlevelB (m : ℕ) : (BasedCategory.ofFunctor
        (Restriction.projection (p := representedProjection R))).obj :=
      P.level X m
    let qptR (m : ℕ) : (BasedCategory.ofFunctor
        (Restriction.projection (p := representedProjection R))).obj :=
      (restrictedRepresentableInclusion R).obj (qptb m)
    have hpt (m : ℕ) : (representedRestrictionInverse R).obj (P.level X m) = qpt m :=
      representedRestrictionInverse_adicLevel_eq R hq m
    have hptB (m : ℕ) : (representedRestrictionInverseBased R).obj (PlevelB m) = qptb m := by
      change (representedRestrictionInverse R).obj (P.level X m) = qpt m
      exact hpt m
    let qptL (m : ℕ) := (restrictedRepresentableInclusion R).obj
      ((representedRestrictionInverseBased R).obj (PlevelB m))
    have heqR (m : ℕ) : qptR m = qptL m := by
      dsimp [qptR, qptL]
      exact congrArg (restrictedRepresentableInclusion R).obj (hptB m).symm
    let hrest (m : ℕ) :=
      (BasedFunctor.toFunctorIso (representedRestrictionInverseBased R)
        (restrictedRepresentableInclusion R)
        (representedRestrictionBasedEquivalence R).counitIso).app (PlevelB m)
    have hrestEq (m : ℕ) : hrest m = representedRestrictionCounitIso R (P.level X m) := by
      rfl
    let qtrans := Functor.Elements.homMk (x := qpt (n + 1)) (y := qpt n)
      (AdicTruncation.transition R n) (canonicalQuotientPoint_transition R n)
    let qtransb : qptb (n + 1) ⟶ qptb n := qtrans
    let rL := eqToHom (heqR (n + 1)).symm ≫
      (restrictedRepresentableInclusion R).map qtransb ≫ eqToHom (heqR n)
    let g : P.level X (n + 1) ⟶ P.level X n :=
      (hrest (n + 1)).inv ≫ rL ≫ (hrest n).hom
    let ut : P.level X (n + 1) ⟶ P.level X n :=
      eqToHom (U.level X (n + 1)).symm ≫
        (U.functor.obj X).transition n ≫ eqToHom (U.level X n)
    have hg : g = ut := by
      let L := P.level X (n + 1)
      have : (representedProjection R).IsHomLift (P.baseMap X (n + 1))
          (P.inclusion X (n + 1)) := P.inclusion_lift X (n + 1)
      have hc := IsHomLift.codomain_eq (representedProjection R)
        (P.baseMap X (n + 1)) (P.inclusion X (n + 1))
      have hcomplete : artinianToComplete.obj L.base =
          artinianToComplete.obj
            ((AdicTruncation.functor (n + 1)).obj ((representedProjection R).obj X)) :=
        L.obj_eq.symm.trans hc
      have hbaseX : L.base =
          (AdicTruncation.functor (n + 1)).obj ((representedProjection R).obj X) :=
        artinianToComplete_obj_injective hcomplete
      have hincl : (P.inclusion X (n + 1)).hom = L.obj.val := by
        have h := (P.inclusion X (n + 1)).map_val
        change X.val ≫ (P.inclusion X (n + 1)).hom = L.obj.val at h
        simpa [X, representedIdentityElement] using h
      have hfac := IsHomLift.fac' (representedProjection R) (P.baseMap X (n + 1))
        (P.inclusion X (n + 1))
      have hfac' : (P.inclusion X (n + 1)).hom =
          P.baseMap X (n + 1) ≫ eqToHom hc.symm := by
        simpa [representedProjection, Functor.Elements.π] using hfac
      have hcast : eqToHom hc.symm ≫ eqToHom L.obj_eq ≫
          artinianToComplete.map (eqToHom hbaseX) = 𝟙 _ := by
        simp [eqToHom_map]
      have hpoint : L.obj.val ≫ eqToHom L.obj_eq ≫
          artinianToComplete.map (eqToHom hbaseX) = P.baseMap X (n + 1) := by
        calc
          _ = (P.inclusion X (n + 1)).hom ≫ eqToHom L.obj_eq ≫
              artinianToComplete.map (eqToHom hbaseX) :=
            congrArg (fun f => f ≫ eqToHom L.obj_eq ≫
              artinianToComplete.map (eqToHom hbaseX)) hincl.symm
          _ = (P.baseMap X (n + 1) ≫ eqToHom hc.symm) ≫ eqToHom L.obj_eq ≫
              artinianToComplete.map (eqToHom hbaseX) :=
            congrArg (fun f => f ≫ eqToHom L.obj_eq ≫
              artinianToComplete.map (eqToHom hbaseX)) hfac'
          _ = P.baseMap X (n + 1) ≫ (eqToHom hc.symm ≫ eqToHom L.obj_eq ≫
              artinianToComplete.map (eqToHom hbaseX)) := by
            simp [Category.assoc]
          _ = P.baseMap X (n + 1) := by rw [hcast]; exact Category.comp_id _
      have hsurj : Function.Surjective ((P.level X (n + 1)).obj.val).hom := by
        intro y
        let e := eqToHom L.obj_eq ≫
          artinianToComplete.map (eqToHom hbaseX)
        obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.hom y)
        have hinj : Function.Injective e.hom := by
          have hleft : Function.LeftInverse (fun z => (asIso e).inv.hom z) e.hom := by
            intro z
            have hh := congrArg (fun f => f.hom z) (asIso e).hom_inv_id
            change (asIso e).inv.hom ((asIso e).hom.hom z) = z at hh
            exact hh
          exact hleft.injective
        refine ⟨x, ?_⟩
        apply hinj
        have hh := congrArg (fun f => f.hom x) hpoint
        change e.hom ((P.level X (n + 1)).obj.val.hom x) =
          (P.baseMap X (n + 1)).hom x at hh
        calc
          e.hom ((P.level X (n + 1)).obj.val.hom x) =
              (P.baseMap X (n + 1)).hom x := hh
          _ = e.hom y := by rw [P.baseMap_hom]; exact hx
      have hcomp : (P.level X (n + 1)).obj.val ≫ g.obj.hom =
          (P.level X (n + 1)).obj.val ≫ ut.obj.hom := by
        have hg' := g.obj.map_val
        have hut' := ut.obj.map_val
        change (P.level X (n + 1)).obj.val ≫ g.obj.hom =
          (P.level X n).obj.val at hg'
        change (P.level X (n + 1)).obj.val ≫ ut.obj.hom =
          (P.level X n).obj.val at hut'
        exact hg'.trans hut'.symm
      have hval : g.obj.hom = ut.obj.hom := by
        apply CompleteLocalAlgCat.Hom.ext
        apply AlgHom.ext
        intro y
        obtain ⟨x, hx⟩ := hsurj y
        have hh := congrArg (fun f => f.hom x) hcomp
        simpa [CompleteLocalAlgCat.comp_hom, hx] using hh
      have hmaps : eqToHom (P.level X (n + 1)).obj_eq ≫
          artinianToComplete.map g.base =
          eqToHom (P.level X (n + 1)).obj_eq ≫
            artinianToComplete.map ut.base := by
        have hgcomm := g.comm
        have hutcomm := ut.comm
        change eqToHom (P.level X (n + 1)).obj_eq ≫
            artinianToComplete.map g.base = g.obj.hom ≫
              eqToHom (P.level X n).obj_eq at hgcomm
        change eqToHom (P.level X (n + 1)).obj_eq ≫
            artinianToComplete.map ut.base = ut.obj.hom ≫
              eqToHom (P.level X n).obj_eq at hutcomm
        calc
          _ = g.obj.hom ≫ eqToHom (P.level X n).obj_eq := hgcomm
          _ = ut.obj.hom ≫ eqToHom (P.level X n).obj_eq := by rw [hval]
          _ = _ := hutcomm.symm
      have hmap : artinianToComplete.map g.base =
          artinianToComplete.map ut.base := by
        calc
          _ = eqToHom (P.level X (n + 1)).obj_eq.symm ≫
              (eqToHom (P.level X (n + 1)).obj_eq ≫
                artinianToComplete.map g.base) := by simp
          _ = eqToHom (P.level X (n + 1)).obj_eq.symm ≫
              (eqToHom (P.level X (n + 1)).obj_eq ≫
                artinianToComplete.map ut.base) := by rw [hmaps]
          _ = _ := by simp
      have hbase : g.base = ut.base := by
        apply ArtinianLocalAlgCat.Hom.ext
        apply AlgHom.ext
        intro x
        have hh := congrArg (fun f => f.hom x) hmap
        simpa [artinianToComplete] using hh
      exact Restriction.Hom.ext
        (Functor.Elements.hom_ext hval) hbase
    let Z : FormalObject p := (E.functor.obj φ).1
    have htarget (m : ℕ) : Z.level m =
        ψF.obj (P.level X m) := by
      change (V.functor.obj (H.equiv.functor.obj ψ)).1.level m = _
      rw [H.forward ψ]
      change ((evaluation (q := FormalObject.projection (p := p)) R).obj
        ((unitBasedFunctor (representedProjection R) hq).comp
          (completionMap ψ))).1.level m = _
      change (((unitBasedFunctor (representedProjection R) hq).comp
        (completionMap ψ)).obj X).level m = _
      change ((completionMap ψ).obj
        (U.functor.obj X)).level m = _
      rw [completionMap_obj_level]
      rw [U.level X m]
    let Y : (BasedCategory.ofFunctor
        (FormalObject.projection (p := Restriction.projection))).obj :=
      U.functor.obj X
    let T : FormalObject p :=
      (completionMap ψ).toFunctor.obj Y
    have hFormal :
        T = Z := by
      change (completionMap ψ).toFunctor.obj Y =
        (V.functor.obj (H.equiv.functor.obj ψ)).1
      rw [H.forward ψ]
      rfl
    have htargetU (m : ℕ) : Z.level m =
        ψF.obj ((U.functor.obj X).level m) := by
      calc
        _ = ψF.obj (P.level X m) := htarget m
        _ = ψF.obj ((U.functor.obj X).level m) := congrArg ψF.obj (U.level X m).symm
    have hlevelPath (m : ℕ) :
        completionMap_obj_level ψ
          Y m =
          (congrArg (fun Z => Z.level m) hFormal).trans (htargetU m) := by
      apply Subsingleton.elim
    have hTtransport :
        eqToHom (congrArg (fun Z => Z.level (n + 1)) hFormal).symm ≫
          T.transition n ≫
          eqToHom (congrArg (fun Z => Z.level n) hFormal) =
            Z.transition n := formalObject_transition_transport hFormal n
    have hTlevel (m : ℕ) : T.level m =
        ψF.obj ((U.functor.obj X).level m) :=
      (congrArg (fun W => W.level m) hFormal).trans (htargetU m)
    have hTmap : T.transition n =
        eqToHom (completionMap_obj_level ψ Y (n + 1)) ≫
          ψF.map ((U.functor.obj X).transition n) ≫
          eqToHom (completionMap_obj_level ψ Y n).symm := completionMap_obj_transition ψ Y n
    have hTmap' : T.transition n = eqToHom (hTlevel (n + 1)) ≫
        ψF.map ((U.functor.obj X).transition n) ≫ eqToHom (hTlevel n).symm :=
      hTmap
    have hT' : Z.transition n =
        eqToHom (htarget (n + 1)) ≫ ψF.map ut ≫ eqToHom (htarget n).symm := by
      let f₁ := congrArg (fun Z => Z.level (n + 1)) hFormal
      let f₀ := congrArg (fun Z => Z.level n) hFormal
      let t₁ := htarget (n + 1)
      let t₀ := htarget n
      let u₁ := congrArg ψF.obj
        (U.level X (n + 1)).symm
      let u₀ := congrArg ψF.obj
        (U.level X n).symm
      have hleft : eqToHom f₁.symm ≫ eqToHom (hTlevel (n + 1)) =
          eqToHom (t₁.trans u₁) := by
        calc
          _ = eqToHom (f₁.symm.trans (hTlevel (n + 1))) := eqToHom_trans _ _
          _ = _ := congrArg eqToHom (Subsingleton.elim _ _)
      have hright : eqToHom (hTlevel n).symm ≫ eqToHom f₀ =
          eqToHom (u₀.symm.trans t₀.symm) := by
        calc
          _ = eqToHom ((hTlevel n).symm.trans f₀) := eqToHom_trans _ _
          _ = _ := congrArg eqToHom (Subsingleton.elim _ _)
      have hmapu₁ : ψF.map (eqToHom (U.level X (n + 1)).symm) = eqToHom u₁ := eqToHom_map ψF _
      have hmapu₀ : ψF.map (eqToHom (U.level X n)) = eqToHom u₀.symm := by
        calc
          _ = eqToHom (congrArg ψF.obj (U.level X n)) :=
            eqToHom_map ψF _
          _ = eqToHom u₀.symm := congrArg eqToHom (Subsingleton.elim _ _)
      have hmaput : ψF.map ut =
            ψF.map (eqToHom (U.level X (n + 1)).symm) ≫
            ψF.map ((U.functor.obj X).transition n) ≫
            ψF.map (eqToHom (U.level X n)) := by
        dsimp [ut]
        calc
          _ = ψF.map (eqToHom (U.level X (n + 1)).symm) ≫
              ψF.map ((U.functor.obj X).transition n ≫ eqToHom (U.level X n)) :=
            ψF.map_comp _ _
          _ = ψF.map (eqToHom (U.level X (n + 1)).symm) ≫
              (ψF.map ((U.functor.obj X).transition n) ≫
                ψF.map (eqToHom (U.level X n))) :=
            congrArg
              (fun f => ψF.map (eqToHom (U.level X (n + 1)).symm) ≫ f)
              (ψF.map_comp _ _)
          _ = _ := rfl
      have hmiddle : eqToHom u₁ ≫
          ψF.map ((U.functor.obj X).transition n) ≫ eqToHom u₀.symm =
          ψF.map (eqToHom (U.level X (n + 1)).symm) ≫
            ψF.map ((U.functor.obj X).transition n) ≫
            ψF.map (eqToHom (U.level X n)) := by
        calc
          _ = (eqToHom u₁ ≫ ψF.map ((U.functor.obj X).transition n)) ≫
              eqToHom u₀.symm := (Category.assoc _ _ _).symm
          _ = (ψF.map (eqToHom (U.level X (n + 1)).symm) ≫
                ψF.map ((U.functor.obj X).transition n)) ≫ eqToHom u₀.symm :=
            congrArg
              (fun f => (f ≫ ψF.map ((U.functor.obj X).transition n)) ≫ eqToHom u₀.symm)
              hmapu₁.symm
          _ = (ψF.map (eqToHom (U.level X (n + 1)).symm) ≫
              ψF.map ((U.functor.obj X).transition n)) ≫
              ψF.map (eqToHom (U.level X n)) :=
            congrArg (fun f =>
              (ψF.map (eqToHom (U.level X (n + 1)).symm) ≫
                ψF.map ((U.functor.obj X).transition n)) ≫ f) hmapu₀.symm
          _ = _ := Category.assoc _ _ _
      have hTcast : eqToHom f₁.symm ≫ T.transition n ≫ eqToHom f₀ =
          eqToHom t₁ ≫ ψF.map ut ≫ eqToHom t₀.symm := by
        have hTmapCast := congrArg
          (fun f => eqToHom f₁.symm ≫ f ≫ eqToHom f₀) hTmap'
        have hpathL : f₁.symm.trans (hTlevel (n + 1)) = t₁.trans u₁ :=
          Subsingleton.elim _ _
        have hpathR : (hTlevel n).symm.trans f₀ = u₀.symm.trans t₀.symm :=
          Subsingleton.elim _ _
        have hreassoc :
            eqToHom f₁.symm ≫
              (eqToHom (hTlevel (n + 1)) ≫
                ψF.map ((U.functor.obj X).transition n) ≫
                eqToHom (hTlevel n).symm) ≫ eqToHom f₀ =
            ((eqToHom f₁.symm ≫ eqToHom (hTlevel (n + 1))) ≫
              ψF.map ((U.functor.obj X).transition n)) ≫
                (eqToHom (hTlevel n).symm ≫ eqToHom f₀) := compReassocFive _ _ _ _ _
        calc
          _ = eqToHom f₁.symm ≫
              (eqToHom (hTlevel (n + 1)) ≫
                ψF.map ((U.functor.obj X).transition n) ≫
                eqToHom (hTlevel n).symm) ≫ eqToHom f₀ := by
            simpa only [Category.assoc] using hTmapCast
          _ = ((eqToHom f₁.symm ≫ eqToHom (hTlevel (n + 1))) ≫
              ψF.map ((U.functor.obj X).transition n)) ≫
                (eqToHom (hTlevel n).symm ≫ eqToHom f₀) := hreassoc
          _ = eqToHom (t₁.trans u₁) ≫
              ψF.map ((U.functor.obj X).transition n) ≫
              eqToHom (u₀.symm.trans t₀.symm) := by
            rw [eqToHom_trans, eqToHom_trans, hpathL, hpathR]
            simp only [Category.assoc]
          _ = eqToHom (t₁.trans u₁) ≫
              ψF.map ((U.functor.obj X).transition n) ≫
              eqToHom (u₀.symm.trans t₀.symm) := by rw [hpathL, hpathR]
          _ = eqToHom t₁ ≫ eqToHom u₁ ≫
              ψF.map ((U.functor.obj X).transition n) ≫
              eqToHom u₀.symm ≫ eqToHom t₀.symm := by
            have hleftCast : eqToHom (t₁.trans u₁) = eqToHom t₁ ≫ eqToHom u₁ :=
              (eqToHom_trans _ _).symm
            have hrightCast : eqToHom (u₀.symm.trans t₀.symm) =
                eqToHom u₀.symm ≫ eqToHom t₀.symm := (eqToHom_trans _ _).symm
            rw [hleftCast, hrightCast]
            simp only [Category.assoc]
          _ = eqToHom t₁ ≫
              ψF.map (eqToHom (U.level X (n + 1)).symm) ≫
              ψF.map ((U.functor.obj X).transition n) ≫
              ψF.map (eqToHom (U.level X n)) ≫ eqToHom t₀.symm := by
            simpa only [Category.assoc] using
              congrArg (fun f => eqToHom t₁ ≫ f ≫ eqToHom t₀.symm) hmiddle
          _ = eqToHom t₁ ≫ ψF.map ut ≫ eqToHom t₀.symm := by
            simpa only [Category.assoc] using
              congrArg (fun f => eqToHom t₁ ≫ f ≫ eqToHom t₀.symm) hmaput.symm
      calc
        _ = eqToHom f₁.symm ≫ T.transition n ≫ eqToHom f₀ := hTtransport.symm
        _ = _ := hTcast
    let ciso := C.counitIso.app φ
    have heqFun (m : ℕ) : (C.functor.obj ψ).obj (qptb m) = ψ.obj (qptR m) := by
      dsimp [C, representedHomPrecompositionEquivalence,
        basedPrecompositionEquivalence, qptR]
      rfl
    let hi₂ (m : ℕ) : (C.functor.obj ψ).obj (qptb m) ≅
        ψ.obj (PlevelB m) :=
      (eqToIso (heqFun m)) ≪≫
        (eqToIso (congrArg ψ.obj (heqR m))) ≪≫ ψ.mapIso (hrest m)
    have hArrow (m : ℕ) : (hi₂ m).hom =
        (eqToHom (heqFun m) ≫ ψ.map (eqToHom (heqR m))) ≫
          ψ.map (hrest m).hom := by
      have hmap : ψ.map (eqToHom (heqR m)) =
          eqToHom (congrArg ψ.obj (heqR m)) := eqToHom_map ψ.toFunctor (heqR m)
      have hrestMapHom : (ψ.mapIso (hrest m)).hom = ψ.map (hrest m).hom :=
        CategoryTheory.Functor.mapIso_hom ψ.toFunctor (hrest m)
      change eqToHom (heqFun m) ≫
        eqToHom (congrArg ψ.obj (heqR m)) ≫ (ψ.mapIso (hrest m)).hom = _
      rw [hrestMapHom, ← hmap]
      simp only [Category.assoc]
    have hCmap : (C.functor.obj ψ).map qtransb =
        ψ.map ((restrictedRepresentableInclusion R).map qtransb) := by
      dsimp [C, representedHomPrecompositionEquivalence,
        basedPrecompositionEquivalence]
      rfl
    have hnatC : φ.map qtrans ≫ ciso.inv.app (qpt n) =
        ciso.inv.app (qpt (n + 1)) ≫ (C.functor.obj ψ).map qtrans := ciso.inv.naturality qtrans
    have hcore :
        (restrictedRepresentableInclusion R).map qtransb ≫
          eqToHom (heqR n) ≫ (hrest n).hom =
        eqToHom (heqR (n + 1)) ≫ (hrest (n + 1)).hom ≫ ut := by
      have hcore' : rL ≫ (hrest n).hom = (hrest (n + 1)).hom ≫ ut := by
        have hh := congrArg (fun f => (hrest (n + 1)).hom ≫ f) hg
        dsimp [g] at hh
        have hcancel := (hrest (n + 1)).hom_inv_id
        calc
          _ = ((hrest (n + 1)).hom ≫ (hrest (n + 1)).inv) ≫
              rL ≫ (hrest n).hom := by
            rw [hcancel]
            simp only [Category.id_comp]
          _ = (hrest (n + 1)).hom ≫
              ((hrest (n + 1)).inv ≫ rL ≫ (hrest n).hom) := (Category.assoc _ _ _).symm
          _ = (hrest (n + 1)).hom ≫ ut := hh
      have hcast : eqToHom (heqR (n + 1)) ≫
          eqToHom (heqR (n + 1)).symm = 𝟙 _ := by
        simp
      have hcoreCast : eqToHom (heqR (n + 1)) ≫ rL =
          (restrictedRepresentableInclusion R).map qtransb ≫ eqToHom (heqR n) := by
        dsimp [rL]
        calc
          _ = (eqToHom (heqR (n + 1)) ≫ eqToHom (heqR (n + 1)).symm) ≫
              (restrictedRepresentableInclusion R).map qtransb ≫ eqToHom (heqR n) :=
            (Category.assoc (eqToHom (heqR (n + 1)))
              (eqToHom (heqR (n + 1)).symm)
              ((restrictedRepresentableInclusion R).map qtransb ≫ eqToHom (heqR n))).symm
          _ = _ := by rw [hcast]; simp only [Category.id_comp]
      calc
        _ = (eqToHom (heqR (n + 1)) ≫ rL) ≫ (hrest n).hom := by
          rw [hcoreCast]
          exact (Category.assoc _ _ _).symm
        _ = eqToHom (heqR (n + 1)) ≫ (rL ≫ (hrest n).hom) := Category.assoc _ _ _
        _ = eqToHom (heqR (n + 1)) ≫ ((hrest (n + 1)).hom ≫ ut) :=
          congrArg (fun f => eqToHom (heqR (n + 1)) ≫ f) hcore'
        _ = _ := rfl
    have hbridge : (C.functor.obj ψ).map qtransb ≫ (hi₂ n).hom =
        (hi₂ (n + 1)).hom ≫ ψ.map ut := by
      rw [hArrow n, hArrow (n + 1)]
      have hcoreMap := congrArg ψ.map hcore
      have hcoreMap' :
          ψ.map ((restrictedRepresentableInclusion R).map qtransb) ≫
            ψ.map (eqToHom (heqR n)) ≫ ψ.map (hrest n).hom =
          ψ.map (eqToHom (heqR (n + 1))) ≫ ψ.map (hrest (n + 1)).hom ≫ ψ.map ut := by
        calc
          _ = ψ.map (((restrictedRepresentableInclusion R).map qtransb ≫
                eqToHom (heqR n)) ≫ (hrest n).hom) := by
              rw [← ψ.map_comp, ← ψ.map_comp]
              simp only [Category.assoc]
          _ = ψ.map (eqToHom (heqR (n + 1)) ≫
                ((hrest (n + 1)).hom ≫ ut)) := hcoreMap
          _ = ψ.map (eqToHom (heqR (n + 1))) ≫
                ψ.map (hrest (n + 1)).hom ≫ ψ.map ut := by
            calc
              _ = ψ.map (eqToHom (heqR (n + 1))) ≫
                    ψ.map ((hrest (n + 1)).hom ≫ ut) := ψ.map_comp _ _
              _ = _ := congrArg
                (fun f => ψ.map (eqToHom (heqR (n + 1))) ≫ f) (ψ.map_comp _ _)
      have hfunRefl (m : ℕ) : heqFun m = rfl := Subsingleton.elim _ _
      have hCmapCast : (C.functor.obj ψ).map qtransb ≫ eqToHom (heqFun n) =
          eqToHom (heqFun (n + 1)) ≫
            ψ.map ((restrictedRepresentableInclusion R).map qtransb) := by
        have hconj : (C.functor.obj ψ).map qtransb =
            eqToHom (heqFun (n + 1)) ≫
              ψ.map ((restrictedRepresentableInclusion R).map qtransb) ≫
              eqToHom (heqFun n).symm := by
          apply (conj_eqToHom_iff_heq
            ((C.functor.obj ψ).map qtransb)
            (ψ.map ((restrictedRepresentableInclusion R).map qtransb))
            (heqFun (n + 1)) (heqFun n)).2
          cases hCmap
          rfl
        have hconj' : (C.functor.obj ψ).map qtransb =
            (eqToHom (heqFun (n + 1)) ≫
              ψ.map ((restrictedRepresentableInclusion R).map qtransb)) ≫
              eqToHom (heqFun n).symm :=
          hconj.trans (Category.assoc _ _ _).symm
        exact (comp_eqToHom_iff (heqFun n) _ _).2 hconj'
      calc
        _ = (C.functor.obj ψ).map qtransb ≫
              (eqToHom (heqFun n) ≫
                (ψ.map (eqToHom (heqR n)) ≫ ψ.map (hrest n).hom)) :=
          congrArg (fun f => (C.functor.obj ψ).map qtransb ≫ f)
            (Category.assoc (eqToHom (heqFun n)) (ψ.map (eqToHom (heqR n)))
              (ψ.map (hrest n).hom))
        _ = ((C.functor.obj ψ).map qtransb ≫ eqToHom (heqFun n)) ≫
              (ψ.map (eqToHom (heqR n)) ≫ ψ.map (hrest n).hom) :=
          (Category.assoc ((C.functor.obj ψ).map qtransb)
            (eqToHom (heqFun n))
            (ψ.map (eqToHom (heqR n)) ≫ ψ.map (hrest n).hom)).symm
        _ = (((C.functor.obj ψ).map qtransb ≫ eqToHom (heqFun n)) ≫
              ψ.map (eqToHom (heqR n))) ≫ ψ.map (hrest n).hom :=
          (Category.assoc ((C.functor.obj ψ).map qtransb ≫ eqToHom (heqFun n))
            (ψ.map (eqToHom (heqR n))) (ψ.map (hrest n).hom)).symm
        _ = (eqToHom (heqFun (n + 1)) ≫
              ψ.map ((restrictedRepresentableInclusion R).map qtransb)) ≫
              ψ.map (eqToHom (heqR n)) ≫ ψ.map (hrest n).hom := by
          rw [hCmapCast]
          exact Category.assoc _ _ _
        _ = eqToHom (heqFun (n + 1)) ≫
              (ψ.map ((restrictedRepresentableInclusion R).map qtransb) ≫
                ψ.map (eqToHom (heqR n)) ≫ ψ.map (hrest n).hom) := Category.assoc _ _ _
        _ = eqToHom (heqFun (n + 1)) ≫
              (ψ.map (eqToHom (heqR (n + 1))) ≫
                ψ.map (hrest (n + 1)).hom ≫ ψ.map ut) :=
          congrArg (fun f => eqToHom (heqFun (n + 1)) ≫ f) hcoreMap'
        _ = (eqToHom (heqFun (n + 1)) ≫
              ψ.map (eqToHom (heqR (n + 1)))) ≫
              (ψ.map (hrest (n + 1)).hom ≫ ψ.map ut) :=
          (Category.assoc (eqToHom (heqFun (n + 1)))
            (ψ.map (eqToHom (heqR (n + 1))))
            (ψ.map (hrest (n + 1)).hom ≫ ψ.map ut)).symm
        _ = ((eqToHom (heqFun (n + 1)) ≫
              ψ.map (eqToHom (heqR (n + 1)))) ≫
              ψ.map (hrest (n + 1)).hom) ≫ ψ.map ut :=
          (Category.assoc
            (eqToHom (heqFun (n + 1)) ≫ ψ.map (eqToHom (heqR (n + 1))))
            (ψ.map (hrest (n + 1)).hom) (ψ.map ut)).symm
    have hbridgeRaw : (C.functor.obj ψ).map qtrans ≫ (hi₂ n).hom =
        (hi₂ (n + 1)).hom ≫ ψ.map ut := by
      simpa only [qtransb] using hbridge
    dsimp only [Iso.trans, Iso.symm, eqToIso] at ⊢
    rw [← hrestEq n, ← hrestEq (n + 1)]
    have hT'' : (E.functor.obj φ).1.transition n =
        eqToHom (htarget (n + 1)) ≫ ψ.map ut ≫ eqToHom (htarget n).symm := by
      simpa only [Z, ψF] using hT'
    rw [hT'']
    have hnatCb : φ.map qtransb ≫ ciso.inv.app (qptb n) =
        ciso.inv.app (qptb (n + 1)) ≫ (C.functor.obj ψ).map qtransb := by
      simpa only [qtransb] using hnatC
    let a := ciso.inv.app (qptb (n + 1))
    let b := (hi₂ (n + 1)).hom
    let c := eqToHom (htarget (n + 1)).symm
    let d := eqToHom (htarget (n + 1))
    let u := ψ.map ut
    let v := eqToHom (htarget n).symm
    have hcancel : c ≫ d = 𝟙 (ψ.obj (PlevelB (n + 1))) := by
      dsimp [c, d]
      calc
        _ = eqToHom ((htarget (n + 1)).symm.trans (htarget (n + 1))) :=
          eqToHom_trans _ _
        _ = eqToHom rfl := congrArg eqToHom (Subsingleton.elim _ _)
        _ = 𝟙 _ := eqToHom_refl _ _
    calc
      _ = ciso.inv.app (qptb (n + 1)) ≫
          ((C.functor.obj ψ).map qtransb ≫ (hi₂ n).hom) ≫
          eqToHom (htarget n).symm := by
        calc
          _ = (φ.map qtransb ≫ ciso.inv.app (qptb n)) ≫
                ((hi₂ n).hom ≫ eqToHom (htarget n).symm) := by
            calc
              _ = (φ.map qtransb ≫ ciso.inv.app (qptb n)) ≫
                    (hi₂ n).hom ≫ eqToHom (htarget n).symm :=
                compReassocFour (φ.map qtransb) (ciso.inv.app (qptb n))
                  (hi₂ n).hom (eqToHom (htarget n).symm)
              _ = (φ.map qtransb ≫ ciso.inv.app (qptb n)) ≫
                    ((hi₂ n).hom ≫ eqToHom (htarget n).symm) :=
                rfl
          _ = (ciso.inv.app (qptb (n + 1)) ≫ (C.functor.obj ψ).map qtransb) ≫
                ((hi₂ n).hom ≫ eqToHom (htarget n).symm) :=
            congrArg (fun f => f ≫ ((hi₂ n).hom ≫ eqToHom (htarget n).symm)) hnatCb
          _ = _ := by
            calc
              _ = ciso.inv.app (qptb (n + 1)) ≫
                    ((C.functor.obj ψ).map qtransb ≫
                      ((hi₂ n).hom ≫ eqToHom (htarget n).symm)) :=
                Category.assoc _ _ _
              _ = ciso.inv.app (qptb (n + 1)) ≫
                    (((C.functor.obj ψ).map qtransb ≫ (hi₂ n).hom) ≫
                      eqToHom (htarget n).symm) :=
                congrArg (fun f => ciso.inv.app (qptb (n + 1)) ≫ f)
                  (Category.assoc _ _ _).symm
              _ = _ := rfl
      _ = ciso.inv.app (qptb (n + 1)) ≫
          (hi₂ (n + 1)).hom ≫ ψ.map ut ≫ eqToHom (htarget n).symm := by
        rw [hbridge]
        exact congrArg (fun f => ciso.inv.app (qptb (n + 1)) ≫ f)
          (Category.assoc (hi₂ (n + 1)).hom (ψ.map ut)
            (eqToHom (htarget n).symm))
      _ = (a ≫ b ≫ c) ≫ (d ≫ u ≫ v) := by
        change a ≫ b ≫ u ≫ v = (a ≫ b ≫ c) ≫ (d ≫ u ≫ v)
        have hcancelRight : b ≫ c ≫ d = b := by
          calc
            _ = b ≫ (c ≫ d) := rfl
            _ = b ≫ 𝟙 _ := congrArg (fun f => b ≫ f) hcancel
            _ = b := Category.comp_id _
        calc
          _ = a ≫ ((b ≫ c ≫ d) ≫ (u ≫ v)) := by
            rw [hcancelRight]
          _ = ((a ≫ b) ≫ c) ≫ (d ≫ (u ≫ v)) :=
            compReassocFive a b c d (u ≫ v)
          _ = _ := by
            exact congrArg (fun f => f ≫ (d ≫ (u ≫ v)))
              (Category.assoc a b c)
  · intro hp' hq'
    have hhp : hp' = hp := Subsingleton.elim _ _
    have hhq : hq' = hq := Subsingleton.elim _ _
    subst hp'
    subst hq'
    let Cfun := C.functor
    let Cinv := C.inverse
    let Hinv := H.equiv.inverse
    let Hfun := H.equiv.functor
    let Vfun := V.functor
    let K := Hfun ⋙ Vfun
    change Hinv ⋙ Cfun ⋙ Cinv ⋙ Hfun ⋙ Vfun ≅ evaluation
      (q := FormalObject.projection (p := p)) R
    exact
      Functor.isoWhiskerRight (Functor.associator Hinv Cfun Cinv) K ≪≫
      Functor.associator Hinv (Cfun ⋙ Cinv) K ≪≫
      Functor.isoWhiskerLeft Hinv (Functor.isoWhiskerRight C.unitIso.symm K) ≪≫
      Functor.isoWhiskerLeft Hinv (Functor.leftUnitor K) ≪≫
      (Functor.associator Hinv Hfun Vfun).symm ≪≫
      Functor.isoWhiskerRight H.equiv.counitIso Vfun ≪≫
      Functor.leftUnitor Vfun

end
end Deformation

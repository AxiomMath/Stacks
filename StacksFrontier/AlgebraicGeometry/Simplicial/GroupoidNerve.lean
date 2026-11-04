module

public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
import StacksCore.Tactic.StacksAttribute

/-!
# The simplicial scheme associated to a groupoid scheme

A groupoid scheme over a scheme `S` has a nerve, regarded as a simplicial object in schemes over
`S`. Its `n`-simplices are the strings of `n` composable arrows and its simplicial operators are
given by restriction of such strings.

The nerve is built degreewise as an iterated fibre product of the arrow scheme along the source
and target maps, and the identification of its generalized points with strings of composable
arrows in the groupoid of generalized points is produced by induction on the degree. That
identification is natural in the test scheme, so by Yoneda it determines all the simplicial
operators at once, and the low-degree formulas of the source are read off from it. Coskeletality
follows from coskeletality of the nerve of a category, transported along the pointwise
identification and reflected by the co-Yoneda embedding.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.GroupoidSimplicialScheme`: the complete specification of the
  nerve of a groupoid scheme — the simplicial scheme, its canonical identifications in degrees
  zero, one and two, the low-degree face and degeneracy formulas, the functor-of-points
  description, and `2`-coskeletality.

## Main results

* `Stacks.Groupoids.GroupoidScheme.groupoidSimplicialScheme`: every groupoid scheme has such a
  nerve.

## Implementation notes

The assertion for every degree is expressed by an equivalence between the generalized points of
the degree-`n` scheme and the type of functors `Fin (n + 1) ⥤ (G.Evaluation T)ᵒᵖ`, so that an
`n`-simplex is precisely a string of `n` composable arrows. Since the equivalence is natural in
the test scheme, Yoneda turns it into a canonical scheme-level identification with the iterated
fibre product, whose degree-zero, degree-one and degree-two coordinates agree with the displayed
scheme isomorphisms. Compatibility with every morphism of the simplex category records all face
and degeneracy formulas simultaneously; the displayed low-degree fields record the source's
parts (1)--(5) literally, and the last field is part (6), expressed by the intrinsic
right-Kan-extension formulation of being `2`-coskeletal.

## References

* [Stacks Project, Tag 07TN](https://stacks.math.columbia.edu/tag/07TN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject

universe u

namespace Stacks.Groupoids.GroupoidScheme

private structure NerveDegree {S : Scheme.{u}} (G : GroupoidScheme S) where
  space : Over S
  lastVertex : space ⟶ G.objects

@[sga "3 V 1.2" "special case"]
private noncomputable def nerveDegree {S : Scheme.{u}}
    (G : GroupoidScheme S) : ℕ → NerveDegree G
  | 0 => ⟨G.objects, 𝟙 _⟩
  | 1 => ⟨G.arrows, G.target⟩
  | n + 2 =>
      let tail := nerveDegree G (n + 1)
      ⟨pullback G.source tail.lastVertex,
        pullback.fst G.source tail.lastVertex ≫ G.target⟩

private noncomputable def nervePointsZero {S : Scheme.{u}} (G : GroupoidScheme S)
    (T : Over S) : (T ⟶ (nerveDegree G 0).space) ≃
      ComposableArrows (G.Evaluation T)ᵒᵖ 0 where
  toFun x := ComposableArrows.mk₀ (Opposite.op x)
  invFun F := (F.obj' 0).unop
  left_inv _ := rfl
  right_inv F := ComposableArrows.ext₀ rfl

private lemma nerveEvaluation_eqToHom_arrow_comp {S : Scheme.{u}}
    (G : GroupoidScheme S) {T : Over S}
    {x y z : G.Evaluation T} (h : x = y) (f : y ⟶ z) :
  (eqToHom h ≫ f).arrow = f.arrow := by
  cases h
  simp

private lemma nerveEvaluationHom_op_heq {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} {x x' y y' : G.Evaluation T} (hx : x = x') (hy : y = y')
    (f : G.EvaluationHom x y) (g : G.EvaluationHom x' y') (ha : f.arrow = g.arrow) :
    HEq (Opposite.op f) (Opposite.op g) := by
  cases hx
  cases hy
  exact heq_of_eq (congrArg Opposite.op (EvaluationHom.ext ha))

private noncomputable def nervePointArrowEquiv {S : Scheme.{u}}
    (G : GroupoidScheme S) (T : Over S) :
    (T ⟶ G.arrows) ≃ Arrow (G.Evaluation T)ᵒᵖ where
  toFun f := Arrow.mk (Opposite.op ({ arrow := f, source_eq := rfl, target_eq := rfl } :
    G.EvaluationHom (f ≫ G.source) (f ≫ G.target)))
  invFun f := f.hom.unop.arrow
  left_inv _ := rfl
  right_inv f := by
    have hL : Opposite.op (f.hom.unop.arrow ≫ G.target) = f.left := by
      simpa using congrArg Opposite.op f.hom.unop.target_eq
    have hR : Opposite.op (f.hom.unop.arrow ≫ G.source) = f.right := by
      simpa using congrArg Opposite.op f.hom.unop.source_eq
    refine Arrow.ext hL hR ?_
    apply (CategoryTheory.conj_eqToHom_iff_heq' _ _ _ _).2
    exact nerveEvaluationHom_op_heq G (congrArg Opposite.unop hR)
      (congrArg Opposite.unop hL) _ f.hom.unop rfl

private noncomputable def evaluationRestriction {S : Scheme.{u}}
    (G : GroupoidScheme S) {T T' : Over S} (f : T' ⟶ T) :
    G.Evaluation T ⥤ G.Evaluation T' where
  obj x := f ≫ x
  map {x y} g :=
    { arrow := f ≫ g.arrow
      source_eq := by simpa [Category.assoc] using congrArg (fun k => f ≫ k) g.source_eq
      target_eq := by simpa [Category.assoc] using congrArg (fun k => f ≫ k) g.target_eq }
  map_id := by
    intro x
    apply EvaluationHom.ext
    change f ≫ (x ≫ G.identity) = (f ≫ x) ≫ G.identity
    simp [Category.assoc]
  map_comp := by
    intro x y z g h
    apply EvaluationHom.ext
    let g₀ : G.EvaluationHom x y := g
    let h₀ : G.EvaluationHom y z := h
    have hlift : f ≫ pullback.lift h₀.arrow g₀.arrow
        (h₀.source_eq.trans g₀.target_eq.symm) =
        pullback.lift (f ≫ h₀.arrow) (f ≫ g₀.arrow) (by
          simpa [Category.assoc] using congrArg (fun k => f ≫ k)
            (h₀.source_eq.trans g₀.target_eq.symm)) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
      · simp only [Category.assoc, pullback.lift_snd]
    change f ≫ (pullback.lift h₀.arrow g₀.arrow _ ≫ G.comp) =
      pullback.lift (f ≫ h₀.arrow) (f ≫ g₀.arrow) _ ≫ G.comp
    calc
      _ = (f ≫ pullback.lift h₀.arrow g₀.arrow
          (h₀.source_eq.trans g₀.target_eq.symm)) ≫ G.comp := Category.assoc _ _ _
      _ = pullback.lift (f ≫ h₀.arrow) (f ≫ g₀.arrow) _ ≫ G.comp :=
        congrArg (fun k => k ≫ G.comp) hlift

private lemma nervePointArrowEquiv_naturality {S : Scheme.{u}}
    (G : GroupoidScheme S) {T T' : Over S} (f : T' ⟶ T)
    (a : T ⟶ G.arrows) :
    ((evaluationRestriction G f).op.mapArrow).obj (nervePointArrowEquiv G T a) =
      nervePointArrowEquiv G T' (f ≫ a) := by
  have hL : (((evaluationRestriction G f).op.mapArrow).obj
      (nervePointArrowEquiv G T a)).left =
      (nervePointArrowEquiv G T' (f ≫ a)).left := by
    show Opposite.op (f ≫ a ≫ G.target) =
      Opposite.op ((f ≫ a) ≫ G.target)
    congr 1
  have hR : (((evaluationRestriction G f).op.mapArrow).obj
      (nervePointArrowEquiv G T a)).right =
      (nervePointArrowEquiv G T' (f ≫ a)).right := by
    show Opposite.op (f ≫ a ≫ G.source) =
      Opposite.op ((f ≫ a) ≫ G.source)
    congr 1
  have hHom : (((evaluationRestriction G f).op.mapArrow).obj
      (nervePointArrowEquiv G T a)).hom =
      eqToHom hL ≫ (nervePointArrowEquiv G T' (f ≫ a)).hom ≫ eqToHom hR.symm := by
    apply (CategoryTheory.conj_eqToHom_iff_heq' _ _ _ _).2
    exact nerveEvaluationHom_op_heq G (congrArg Opposite.unop hR)
      (congrArg Opposite.unop hL) _ _ rfl
  exact Arrow.ext hL hR hHom

private noncomputable def nervePointsOne {S : Scheme.{u}} (G : GroupoidScheme S)
    (T : Over S) : (T ⟶ (nerveDegree G 1).space) ≃
      ComposableArrows (G.Evaluation T)ᵒᵖ 1 :=
  (nervePointArrowEquiv G T).trans ComposableArrows.arrowEquiv.symm

private lemma nervePointsOne_naturality {S : Scheme.{u}} (G : GroupoidScheme S)
    {T T' : Over S} (f : T' ⟶ T) (a : T ⟶ G.arrows) :
      ((evaluationRestriction G f).op.mapComposableArrows 1).obj
        (nervePointsOne G T a) = nervePointsOne G T' (f ≫ a) := by
  apply ComposableArrows.arrowEquiv.injective
  show ((evaluationRestriction G f).op.mapArrow).obj
      (nervePointArrowEquiv G T a) = nervePointArrowEquiv G T' (f ≫ a)
  exact nervePointArrowEquiv_naturality G f a

private noncomputable def nervePullbackPoints {S : Scheme.{u}} (T : Over S)
    {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (T ⟶ pullback f g) ≃
      { p : (T ⟶ X) × (T ⟶ Y) // p.1 ≫ f = p.2 ≫ g } where
  toFun x := ⟨(x ≫ pullback.fst f g, x ≫ pullback.snd f g), by
    simpa only [Category.assoc] using congrArg (fun t => x ≫ t) pullback.condition⟩
  invFun p := pullback.lift p.val.1 p.val.2 p.property
  left_inv x := by
    apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd]
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨a, b⟩, h⟩
    simp [pullback.lift_fst, pullback.lift_snd]

private structure NervePointData {S : Scheme.{u}} (G : GroupoidScheme S)
    (T : Over S) (n : ℕ) where
  equiv : (T ⟶ (nerveDegree G n).space) ≃ ComposableArrows (G.Evaluation T)ᵒᵖ n
  obj_zero (x : T ⟶ (nerveDegree G n).space) :
    (equiv x).obj' 0 = Opposite.op (x ≫ (nerveDegree G n).lastVertex)

private noncomputable def nervePointData {S : Scheme.{u}} (G : GroupoidScheme S)
    (T : Over S) : (n : ℕ) → NervePointData G T n
  | 0 =>
      { equiv := nervePointsZero G T
        obj_zero _ := rfl }
  | 1 =>
      { equiv := nervePointsOne G T
        obj_zero := by
          intro x
          change (nervePointArrowEquiv G T x).left = _
          rfl }
  | n + 2 => by
      let tail := nervePointData G T (n + 1)
      let pullbackPoints := nervePullbackPoints T G.source (nerveDegree G (n + 1)).lastVertex
      let toNerve : (T ⟶ (nerveDegree G (n + 2)).space) →
          ComposableArrows (G.Evaluation T)ᵒᵖ (n + 2) := fun x => by
        let p := pullbackPoints x
        let a := p.val.1
        let t := p.val.2
        let E := nervePointArrowEquiv G T a
        have hArrowRight : E.right =
            (Opposite.op (a ≫ G.source : G.Evaluation T) : (G.Evaluation T)ᵒᵖ) := rfl
        have hpOp : (Opposite.op (a ≫ G.source : G.Evaluation T) :
            (G.Evaluation T)ᵒᵖ) =
            Opposite.op (t ≫ (nerveDegree G (n + 1)).lastVertex : G.Evaluation T) :=
          congrArg (fun z : G.Evaluation T => Opposite.op z) p.property
        let h : E.right = (tail.equiv t).left :=
          hArrowRight.trans (hpOp.trans (tail.obj_zero t).symm)
        exact (tail.equiv t).precomp (E.hom ≫ eqToHom h)
      let fromNerve : ComposableArrows (G.Evaluation T)ᵒᵖ (n + 2) →
          (T ⟶ (nerveDegree G (n + 2)).space) := fun F => by
        let tailSimplex := F.δ₀
        let tailPoint := tail.equiv.symm tailSimplex
        let edgePoint := (nervePointArrowEquiv G T).symm
          (Arrow.mk (F.map' 0 1 (by decide) (by omega)))
        have hTail := Equiv.apply_symm_apply tail.equiv tailSimplex
        have hTailObj : (tail.equiv tailPoint).obj' 0 = F.obj' 1 := by
          change (tail.equiv tailPoint).left = tailSimplex.left
          rw [hTail]
        have hEdge := (nervePointArrowEquiv G T).right_inv
          (Arrow.mk (F.map' 0 1 (by decide) (by omega)))
        have hEndPoint : (nervePointArrowEquiv G T edgePoint).right =
            (tail.equiv tailPoint).left := (congrArg Arrow.right hEdge).trans hTailObj.symm
        have hsource : (edgePoint ≫ G.source : G.Evaluation T) =
            (tailPoint ≫ (nerveDegree G (n + 1)).lastVertex : G.Evaluation T) := by
          apply Opposite.op_injective
          calc
            Opposite.op (edgePoint ≫ G.source) =
                (nervePointArrowEquiv G T edgePoint).right := rfl
            _ = (tail.equiv tailPoint).left := hEndPoint
            _ = Opposite.op (tailPoint ≫ (nerveDegree G (n + 1)).lastVertex) :=
              tail.obj_zero tailPoint
        exact pullbackPoints.symm ⟨(edgePoint, tailPoint), hsource⟩
      let e : (T ⟶ (nerveDegree G (n + 2)).space) ≃
          ComposableArrows (G.Evaluation T)ᵒᵖ (n + 2) := {
        toFun := toNerve
        invFun := fromNerve
        left_inv := by
          intro x
          dsimp [fromNerve, toNerve]
          apply pullbackPoints.injective
          rw [pullbackPoints.apply_symm_apply]
          apply Subtype.ext
          apply Prod.ext
          · let p := pullbackPoints x
            let E := nervePointArrowEquiv G T p.val.1
            let h : E.right = (tail.equiv p.val.2).left :=
              (congrArg Opposite.op p.property).trans (tail.obj_zero p.val.2).symm
            apply (nervePointArrowEquiv G T).injective
            simp only [Equiv.apply_symm_apply]
            change Arrow.mk (E.hom ≫ eqToHom h) = E
            rw [Arrow.arrow_mk_comp_eqToHom]
            exact Arrow.mk_eq E
          · simp only [Equiv.symm_apply_apply]
        right_inv := by
          intro F
          dsimp [fromNerve, toNerve]
          rw [pullbackPoints.apply_symm_apply]
          let tailSimplex := F.δ₀
          let tailPoint := tail.equiv.symm tailSimplex
          let edgePoint := (nervePointArrowEquiv G T).symm
            (Arrow.mk (F.map' 0 1 (by decide) (by omega)))
          have hTail : tail.equiv tailPoint = tailSimplex :=
            Equiv.apply_symm_apply tail.equiv tailSimplex
          have hTailObj : (tail.equiv tailPoint).obj' 0 = F.obj' 1 := by
            simpa [tailSimplex] using congrArg
              (fun X : ComposableArrows (G.Evaluation T)ᵒᵖ (n + 1) => X.obj' 0) hTail
          have hEdge := (nervePointArrowEquiv G T).right_inv
            (Arrow.mk (F.map' 0 1 (by decide) (by omega)))
          have hEndPoint : (nervePointArrowEquiv G T edgePoint).right =
              (tail.equiv tailPoint).left := (congrArg Arrow.right hEdge).trans hTailObj.symm
          have hsource : (edgePoint ≫ G.source : G.Evaluation T) =
              (tailPoint ≫ (nerveDegree G (n + 1)).lastVertex : G.Evaluation T) := by
            apply Opposite.op_injective
            calc
              Opposite.op (edgePoint ≫ G.source) =
                  (nervePointArrowEquiv G T edgePoint).right := rfl
              _ = (tail.equiv tailPoint).left := hEndPoint
              _ = Opposite.op (tailPoint ≫ (nerveDegree G (n + 1)).lastVertex) :=
                tail.obj_zero tailPoint
          change (tail.equiv tailPoint).precomp
              ((nervePointArrowEquiv G T edgePoint).hom ≫
                eqToHom ((congrArg Opposite.op hsource).trans
                  (tail.obj_zero tailPoint).symm)) = F
          refine ComposableArrows.ext_succ (h₀ := ?_) (h := ?_) (w := ?_)
          · change (nervePointArrowEquiv G T edgePoint).left = F.obj' 0
            exact congrArg Arrow.left hEdge
          · rw [ComposableArrows.precomp_δ₀]
            exact hTail
          · dsimp [ComposableArrows.precomp]
            have hEdgeMap := (Arrow.mk_eq_mk_iff
              (nervePointArrowEquiv G T edgePoint).hom
              (F.map' 0 1 (by decide) (by omega))).1 hEdge
            rcases hEdgeMap with ⟨hL, hR, hMap⟩
            have hMapTransport : eqToHom hR.symm ≫
                eqToHom hEndPoint = eqToHom hTailObj.symm := by
              rw [eqToHom_trans]
            calc
              _ = eqToHom hL ≫ F.map' 0 1 (by decide) (by omega) ≫
                    (eqToHom hR.symm ≫ eqToHom hEndPoint) := by
                rw [hMap]
                simp [Category.assoc]
              _ = eqToHom hL ≫ F.map' 0 1 (by decide) (by omega) ≫ eqToHom hTailObj.symm := by
                simpa only [Category.assoc] using congrArg
                  (fun k => eqToHom hL ≫ F.map' 0 1 (by decide) (by omega) ≫ k)
                  hMapTransport
        }
      refine ⟨e, ?_⟩
      intro x
      change (nervePointArrowEquiv G T (pullbackPoints x).val.1).left = _
      rfl

private lemma nervePointData_naturality {S : Scheme.{u}} (G : GroupoidScheme S)
    {T T' : Over S} (f : T' ⟶ T) (n : ℕ) (x : T ⟶ (nerveDegree G n).space) :
    ((evaluationRestriction G f).op.mapComposableArrows n).obj
        ((nervePointData G T n).equiv x) =
      (nervePointData G T' n).equiv (f ≫ x) := by
  induction n with
  | zero =>
      show ((evaluationRestriction G f).op.mapComposableArrows 0).obj
          (nervePointsZero G T x) = nervePointsZero G T' (f ≫ x)
      rfl
  | succ n ih =>
      cases n with
      | zero =>
          exact nervePointsOne_naturality G f x
      | succ n =>
          let D := nervePointData G T (n + 1)
          let D' := nervePointData G T' (n + 1)
          let P := nervePullbackPoints T G.source (nerveDegree G (n + 1)).lastVertex
          let P' := nervePullbackPoints T' G.source (nerveDegree G (n + 1)).lastVertex
          let p := P x
          let p' := P' (f ≫ x)
          let E := nervePointArrowEquiv G T p.val.1
          let E' := nervePointArrowEquiv G T' p'.val.1
          have hpSecond : p'.val.2 = f ≫ p.val.2 := Category.assoc _ _ _
          have h : E.right = (D.equiv p.val.2).left :=
            (congrArg (fun z : G.Evaluation T => Opposite.op z) p.property).trans
              (D.obj_zero p.val.2).symm
          have h' : E'.right = (D'.equiv p'.val.2).obj 0 :=
            (congrArg (fun z : G.Evaluation T' => Opposite.op z) p'.property).trans
              (D'.obj_zero p'.val.2).symm
          have hArrow :
              ((evaluationRestriction G f).op.mapArrow).obj E = E' :=
            nervePointArrowEquiv_naturality G f p.val.1
          have hTailEq :
              ((evaluationRestriction G f).op.mapComposableArrows (n + 1)).obj
                  (D.equiv p.val.2) = D'.equiv p'.val.2 :=
            (ih p.val.2).trans (congrArg D'.equiv hpSecond.symm)
          have hZero :
              (evaluationRestriction G f).op.obj E.left = E'.left :=
            congrArg Arrow.left hArrow
          show ((evaluationRestriction G f).op.mapComposableArrows (n + 2)).obj
              ((D.equiv p.val.2).precomp (E.hom ≫ eqToHom h)) =
            (D'.equiv p'.val.2).precomp (E'.hom ≫ eqToHom h')
          refine ComposableArrows.ext_succ (h₀ := hZero) (h := hTailEq) (w := ?_)
          · dsimp [ComposableArrows.precomp, evaluationRestriction,
              Functor.mapComposableArrows]
            have hArrowMk : Arrow.mk
                ((evaluationRestriction G f).op.map E.hom) = Arrow.mk E'.hom := by
              calc
                _ = ((evaluationRestriction G f).op.mapArrow).obj E := by
                  simp only [Functor.mapArrow_obj]
                _ = E' := hArrow
                _ = Arrow.mk E'.hom := (Arrow.mk_eq E').symm
            have hArrowData := (Arrow.mk_eq_mk_iff
              ((evaluationRestriction G f).op.map E.hom) E'.hom).1 hArrowMk
            rcases hArrowData with ⟨hL, hR, hMap⟩
            have hTailObj :
                (((evaluationRestriction G f).op.mapComposableArrows (n + 1)).obj
                    (D.equiv p.val.2)).obj 0 = (D'.equiv p'.val.2).obj 0 :=
              congrArg (fun A : ComposableArrows (G.Evaluation T')ᵒᵖ (n + 1) => A.obj 0)
                hTailEq
            have hMapEnd :
                (evaluationRestriction G f).op.obj E.right =
                  (((evaluationRestriction G f).op.mapComposableArrows (n + 1)).obj
                    (D.equiv p.val.2)).obj 0 := by
              show (evaluationRestriction G f).op.obj E.right =
                (evaluationRestriction G f).op.obj ((D.equiv p.val.2).obj 0)
              exact congrArg (fun z => (evaluationRestriction G f).op.obj z) h
            have hComp : eqToHom hR.symm ≫ eqToHom hMapEnd =
                eqToHom h' ≫ eqToHom hTailObj.symm := by
              rw [eqToHom_trans, eqToHom_trans]
            have hLeft : hL = hZero := by
              apply Subsingleton.elim
            show (evaluationRestriction G f).op.map
                (E.hom ≫ eqToHom h) =
              eqToHom hZero ≫ (E'.hom ≫ eqToHom h') ≫
                eqToHom (Functor.congr_obj hTailEq.symm 0)
            rw [Functor.map_comp, hMap, eqToHom_map, hLeft]
            simp only [Category.assoc]
            exact congrArg (fun k => eqToHom hZero ≫ E'.hom ≫ k) hComp

private lemma nerveUnop_comp_eqToHom {C : Type*} [Category C]
    {x y z : Cᵒᵖ} (f : x ⟶ y) (h : y = z) :
    (f ≫ eqToHom h).unop = eqToHom (congrArg Opposite.unop h.symm) ≫ f.unop := by
  cases h
  simp

private noncomputable def nerveOperator {S : Scheme.{u}} (G : GroupoidScheme S)
    {m n : ℕ} (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (nerveDegree G n).space ⟶ (nerveDegree G m).space :=
  let T := (nerveDegree G n).space
  let Φ := α.toOrderHom.monotone.functor
  (nervePointData G T m).equiv.symm
    (ComposableArrows.whiskerLeft ((nervePointData G T n).equiv (𝟙 T)) Φ)

private lemma nerveOperator_point {S : Scheme.{u}} (G : GroupoidScheme S)
    {m n : ℕ} (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (T : Over S)
    (x : T ⟶ (nerveDegree G n).space) :
    (nervePointData G T m).equiv (x ≫ nerveOperator G α) =
      ComposableArrows.whiskerLeft ((nervePointData G T n).equiv x)
        α.toOrderHom.monotone.functor := by
  let X := (nerveDegree G n).space
  let Φ := α.toOrderHom.monotone.functor
  let eN := (nervePointData G X n).equiv
  let eM := (nervePointData G X m).equiv
  have hn := nervePointData_naturality G x n (𝟙 X)
  have hm := nervePointData_naturality G x m (nerveOperator G α)
  rw [← hm]
  show ((evaluationRestriction G x).op.mapComposableArrows m).obj
      (eM ((nervePointData G X m).equiv.symm
        (ComposableArrows.whiskerLeft ((nervePointData G X n).equiv (𝟙 X)) Φ))) =
    ComposableArrows.whiskerLeft ((nervePointData G T n).equiv x) Φ
  rw [Equiv.apply_symm_apply]
  calc
    _ = ComposableArrows.whiskerLeft
        (((evaluationRestriction G x).op.mapComposableArrows n).obj (eN (𝟙 X))) Φ := by
          rfl
    _ = ComposableArrows.whiskerLeft ((nervePointData G T n).equiv x) Φ := by
          simpa only [eN, X, Category.comp_id] using congrArg
            (fun A => ComposableArrows.whiskerLeft A Φ) hn

private alias overHom_ext := Stacks.Groupoids.overHom_ext

private lemma nerveOperator_id {S : Scheme.{u}} (G : GroupoidScheme S)
    (n : ℕ) : nerveOperator G (𝟙 (SimplexCategory.mk n)) = 𝟙 _ := by
  apply overHom_ext
  intro T x
  apply (nervePointData G T n).equiv.injective
  rw [nerveOperator_point]
  simp only [ComposableArrows.whiskerLeft, SimplexCategory.id_toOrderHom]
  rfl

private lemma nerveOperator_comp {S : Scheme.{u}} (G : GroupoidScheme S)
    {k m n : ℕ} (β : SimplexCategory.mk k ⟶ SimplexCategory.mk m)
    (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    nerveOperator G (β ≫ α) = nerveOperator G α ≫ nerveOperator G β := by
  apply overHom_ext
  intro T x
  apply (nervePointData G T k).equiv.injective
  have hα := nerveOperator_point G α T x
  have hβ := nerveOperator_point G β T (x ≫ nerveOperator G α)
  have hβα := nerveOperator_point G (β ≫ α) T x
  symm
  calc
    (nervePointData G T k).equiv ((x ≫ nerveOperator G α) ≫ nerveOperator G β) =
        ComposableArrows.whiskerLeft
          ((nervePointData G T m).equiv (x ≫ nerveOperator G α))
          β.toOrderHom.monotone.functor := hβ
    _ = ComposableArrows.whiskerLeft
          (ComposableArrows.whiskerLeft ((nervePointData G T n).equiv x)
            α.toOrderHom.monotone.functor) β.toOrderHom.monotone.functor := by rw [hα]
    _ = ComposableArrows.whiskerLeft ((nervePointData G T n).equiv x)
          (β.toOrderHom.monotone.functor ⋙ α.toOrderHom.monotone.functor) := rfl
    _ = ComposableArrows.whiskerLeft ((nervePointData G T n).equiv x)
          (β ≫ α).toOrderHom.monotone.functor := by
            rw [SimplexCategory.comp_toOrderHom]
            rfl
    _ = (nervePointData G T k).equiv (x ≫ nerveOperator G (β ≫ α)) := hβα.symm

private noncomputable def nerveSimplicialScheme {S : Scheme.{u}}
    (G : GroupoidScheme S) : SimplicialObject (Over S) where
  obj i := (nerveDegree G i.unop.len).space
  map {i j} α := nerveOperator G α.unop
  map_id i := by
    simpa using nerveOperator_id G i.unop.len
  map_comp {i j k} α β := by
    simpa using nerveOperator_comp G β.unop α.unop

private lemma nervePoints_two_first {S : Scheme.{u}} (G : GroupoidScheme S)
    (T : Over S) (x : T ⟶ (nerveDegree G 2).space) :
    (((nervePointData G T 2).equiv x).map
      (homOfLE (show (0 : Fin 3) ≤ 1 by decide))).unop.arrow =
        x ≫ pullback.fst G.source G.target := by
  let tail := nervePointData G T 1
  let p := nervePullbackPoints T G.source G.target x
  let E := nervePointArrowEquiv G T p.val.1
  have h : E.right = (tail.equiv p.val.2).left :=
    (congrArg (fun z : G.Evaluation T => Opposite.op z) p.property).trans
      (tail.obj_zero p.val.2).symm
  show (((tail.equiv p.val.2).precomp (E.hom ≫ eqToHom h)).map
      (homOfLE (show (0 : Fin 3) ≤ 1 by decide))).unop.arrow =
    x ≫ pullback.fst G.source G.target
  have hEdge : (E.hom ≫ eqToHom h).unop.arrow = p.val.1 := by
    rw [nerveUnop_comp_eqToHom]
    exact nerveEvaluation_eqToHom_arrow_comp G
      (congrArg Opposite.unop h.symm) E.hom.unop
  calc
    _ = (E.hom ≫ eqToHom h).unop.arrow := by
      simp [ComposableArrows.precomp, ComposableArrows.Precomp.map]
    _ = p.val.1 := hEdge
    _ = x ≫ pullback.fst G.source G.target := rfl

private lemma nervePoints_two_second {S : Scheme.{u}} (G : GroupoidScheme S)
    (T : Over S) (x : T ⟶ (nerveDegree G 2).space) :
    (((nervePointData G T 2).equiv x).map
      (homOfLE (show (1 : Fin 3) ≤ 2 by decide))).unop.arrow =
        x ≫ pullback.snd G.source G.target := by
  let tail := nervePointData G T 1
  let p := nervePullbackPoints T G.source G.target x
  let E := nervePointArrowEquiv G T p.val.1
  have h : E.right = (tail.equiv p.val.2).left :=
    (congrArg (fun z : G.Evaluation T => Opposite.op z) p.property).trans
      (tail.obj_zero p.val.2).symm
  show (((tail.equiv p.val.2).precomp (E.hom ≫ eqToHom h)).map
      (homOfLE (show (1 : Fin 3) ≤ 2 by decide))).unop.arrow =
    x ≫ pullback.snd G.source G.target
  calc
    _ = ((tail.equiv p.val.2).map
          (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).unop.arrow := by
      simp [ComposableArrows.precomp, ComposableArrows.Precomp.map]
    _ = p.val.2 := rfl
    _ = x ≫ pullback.snd G.source G.target := rfl

private lemma nerveOperator_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    {n : ℕ} (α : SimplexCategory.mk 1 ⟶ SimplexCategory.mk n)
    (T : Over S) (x : T ⟶ (nerveDegree G n).space) :
    x ≫ nerveOperator G α =
      (((nervePointData G T n).equiv x).map
        (α.toOrderHom.monotone.functor.map
          (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))).unop.arrow :=
  congrArg (fun F : ComposableArrows (G.Evaluation T)ᵒᵖ 1 =>
    (F.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).unop.arrow)
      (nerveOperator_point G α T x)

private lemma nerveOperator_delta_two_zero {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    nerveOperator G (SimplexCategory.δ (0 : Fin 3)) =
      pullback.snd G.source G.target := by
  apply overHom_ext
  intro T x
  rw [nerveOperator_arrow]
  exact nervePoints_two_second G T x

private lemma nerveOperator_delta_two_two {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    nerveOperator G (SimplexCategory.δ (2 : Fin 3)) =
      pullback.fst G.source G.target := by
  apply overHom_ext
  intro T x
  rw [nerveOperator_arrow]
  exact nervePoints_two_first G T x

private lemma nerveOperator_delta_two_one {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    nerveOperator G (SimplexCategory.δ (1 : Fin 3)) = G.comp := by
  apply overHom_ext
  intro T x
  rw [nerveOperator_arrow]
  let F := (nervePointData G T 2).equiv x
  show (F.map (homOfLE (show (0 : Fin 3) ≤ 2 by decide))).unop.arrow = x ≫ G.comp
  have h := F.map_comp (homOfLE (show (0 : Fin 3) ≤ 1 by decide))
    (homOfLE (show (1 : Fin 3) ≤ 2 by decide))
  have h' := congrArg (fun f : F.obj 0 ⟶ F.obj 2 => f.unop.arrow) h
  refine h'.trans ?_
  show pullback.lift
    (F.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide))).unop.arrow
    (F.map (homOfLE (show (1 : Fin 3) ≤ 2 by decide))).unop.arrow _ ≫ G.comp = _
  dsimp only [F]
  simp only [nervePoints_two_first, nervePoints_two_second]
  congr 1
  apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd] <;> rfl

/-- A degeneracy `[2] ⟶ [1]` is determined by the arrows it sends to the two edges of a
composable pair. -/
private lemma nerveOperator_eq_lift {S : Scheme.{u}} (G : GroupoidScheme S)
    (α : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 1) {a b : G.arrows ⟶ G.arrows}
    (h : a ≫ G.source = b ≫ G.target)
    (ha : ∀ (T : Over S) (x : T ⟶ G.arrows),
      (((nervePointData G T 1).equiv x).map (α.toOrderHom.monotone.functor.map
        (homOfLE (show (0 : Fin 3) ≤ 1 by decide)))).unop.arrow = x ≫ a)
    (hb : ∀ (T : Over S) (x : T ⟶ G.arrows),
      (((nervePointData G T 1).equiv x).map (α.toOrderHom.monotone.functor.map
        (homOfLE (show (1 : Fin 3) ≤ 2 by decide)))).unop.arrow = x ≫ b) :
    nerveOperator G α = pullback.lift (f := G.source) (g := G.target) a b h := by
  apply overHom_ext
  intro T x
  dsimp only [nerveDegree] at x ⊢
  apply pullback.hom_ext (f := G.source) (g := G.target)
  · simp only [Category.assoc, pullback.lift_fst]
    refine (nervePoints_two_first G T (x ≫ nerveOperator G α)).symm.trans ?_
    exact (congrArg (fun F : ComposableArrows (G.Evaluation T)ᵒᵖ 2 =>
      (F.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide))).unop.arrow)
      (nerveOperator_point G α T x)).trans (ha T x)
  · simp only [Category.assoc, pullback.lift_snd]
    refine (nervePoints_two_second G T (x ≫ nerveOperator G α)).symm.trans ?_
    exact (congrArg (fun F : ComposableArrows (G.Evaluation T)ᵒᵖ 2 =>
      (F.map (homOfLE (show (1 : Fin 3) ≤ 2 by decide))).unop.arrow)
      (nerveOperator_point G α T x)).trans (hb T x)

private lemma nerveOperator_sigma_one_zero {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    nerveOperator G (SimplexCategory.σ (0 : Fin 2)) =
      pullback.lift (f := G.source) (g := G.target) (G.target ≫ G.identity) (𝟙 G.arrows) (by
        simp [Category.assoc, G.source_identity]) :=
  nerveOperator_eq_lift G _ _
    (fun T x => congrArg (fun f => f.unop.arrow) (((nervePointData G T 1).equiv x).map_id 0))
    (fun _ _ => rfl)

private lemma nerveOperator_sigma_one_one {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    nerveOperator G (SimplexCategory.σ (1 : Fin 2)) =
      pullback.lift (f := G.source) (g := G.target) (𝟙 G.arrows) (G.source ≫ G.identity) (by
        simp [Category.assoc, G.target_identity]) :=
  nerveOperator_eq_lift G _ _ (fun _ _ => rfl)
    (fun T x => congrArg (fun f => f.unop.arrow) (((nervePointData G T 1).equiv x).map_id 1))

private lemma nerveOperator_sigma_zero {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    nerveOperator G (SimplexCategory.σ (0 : Fin 1)) = G.identity := by
  apply overHom_ext
  intro T x
  rw [nerveOperator_arrow]
  rfl

private lemma nerveOperator_delta_one_zero {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    nerveOperator G (SimplexCategory.δ (0 : Fin 2)) = G.source := by
  apply overHom_ext
  intro T x
  exact congrArg (fun F : ComposableArrows (G.Evaluation T)ᵒᵖ 0 => (F.obj 0).unop)
    (nerveOperator_point G (SimplexCategory.δ (0 : Fin 2)) T x)

private lemma nerveOperator_delta_one_one {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    nerveOperator G (SimplexCategory.δ (1 : Fin 2)) = G.target := by
  apply overHom_ext
  intro T x
  exact congrArg (fun F : ComposableArrows (G.Evaluation T)ᵒᵖ 0 => (F.obj 0).unop)
    (nerveOperator_point G (SimplexCategory.δ (1 : Fin 2)) T x)

private noncomputable def nervePointsSimplicialSet {S : Scheme.{u}}
    (G : GroupoidScheme S) (T : Over S) : SimplicialObject (Type _) :=
  nerveSimplicialScheme G ⋙ coyoneda.obj (op T)

private noncomputable def nervePointsIsoNerve {S : Scheme.{u}}
    (G : GroupoidScheme S) (T : Over S) :
    nervePointsSimplicialSet G T ≅ CategoryTheory.nerve (G.Evaluation T)ᵒᵖ :=
  NatIso.ofComponents
    (fun i => Equiv.toIso (nervePointData G T i.unop.len).equiv)
    (by
      intro i j α
      ext x
      change (nervePointData G T j.unop.len).equiv
          (x ≫ nerveOperator G α.unop) = _
      exact nerveOperator_point G α.unop T x)

private lemma nervePointsSimplicialSet_isCoskeletal {S : Scheme.{u}}
    (G : GroupoidScheme S) (T : Over S) :
    (nervePointsSimplicialSet G T).IsCoskeletal 2 := by
  let e := nervePointsIsoNerve G T
  let N := CategoryTheory.nerve (G.Evaluation T)ᵒᵖ
  have hN : N.IsCoskeletal 2 := inferInstance
  let L := (SimplexCategory.Truncated.inclusion 2).op
  have h := (Functor.isRightKanExtension_iff_of_iso₂
      (L := L) (F₁' := nervePointsSimplicialSet G T) (F₂' := N)
      (F₁ := L ⋙ nervePointsSimplicialSet G T) (F₂ := L ⋙ N)
      (α₁ := 𝟙 _) (α₂ := 𝟙 _) (Functor.isoWhiskerLeft L e) e (by
        simp [Functor.isoWhiskerLeft_hom]))
  exact (SimplicialObject.isCoskeletal_iff _ _).2 (h.mpr hN.isRightKanExtension)

private lemma nerveSimplicialScheme_isCoskeletal {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    (nerveSimplicialScheme G).IsCoskeletal 2 := by
  let X := nerveSimplicialScheme G
  let L := (SimplexCategory.Truncated.inclusion 2).op
  let E : Functor.RightExtension L (L ⋙ X) := Functor.RightExtension.mk X (𝟙 _)
  have hE : E.IsPointwiseRightKanExtension := by
    intro y
    apply coyonedaJointlyReflectsLimits
      (F := StructuredArrow.proj y L ⋙ L ⋙ X) (c := E.coneAt y)
    intro T
    let Q := coyoneda.obj T
    let P := nervePointsSimplicialSet G T.unop
    let EP : Functor.RightExtension L (L ⋙ P) := Functor.RightExtension.mk P (𝟙 _)
    let : P.IsCoskeletal 2 := nervePointsSimplicialSet_isCoskeletal G T.unop
    have hp : EP.IsPointwiseRightKanExtension :=
      Functor.isPointwiseRightKanExtensionOfIsRightKanExtension P (𝟙 _)
    let α := Functor.associator (StructuredArrow.proj y L ⋙ L) X Q
    have hcone : (Cone.postcompose α.hom).obj (Q.mapCone (E.coneAt y)) ≅ EP.coneAt y := by
      refine Cone.ext (Iso.refl _) ?_
      intro g
      simp [E, EP, P, Q, α, Functor.RightExtension.coneAt,
        Functor.RightExtension.mk, nervePointsSimplicialSet,
        Functor.associator]
    exact (IsLimit.equivOfNatIsoOfIso α (Q.mapCone (E.coneAt y)) (EP.coneAt y)
      hcone).symm (hp y)
  exact ⟨by simpa [E] using hE.isRightKanExtension⟩

/-- The complete specification of the simplicial scheme which is the nerve of a groupoid
scheme. -/
structure GroupoidSimplicialScheme {S : Scheme.{u}}
    (G : GroupoidScheme S) where
  /-- The simplicial scheme over `S`. -/
  simplicialScheme : SimplicialObject (Over S)
  /-- In degree zero the nerve is the object scheme. -/
  objectsIso : simplicialScheme.obj (op (SimplexCategory.mk 0)) ≅ G.objects
  /-- In degree one the nerve is the arrow scheme. -/
  arrowsIso : simplicialScheme.obj (op (SimplexCategory.mk 1)) ≅ G.arrows
  /-- In degree two the nerve is the scheme of composable pairs. -/
  composablePairsIso : simplicialScheme.obj (op (SimplexCategory.mk 2)) ≅
    pullback G.source G.target
  /-- The degree-zero degeneracy is the identity-arrow map. -/
  sigma_zero : simplicialScheme.σ 0 ≫ arrowsIso.hom = objectsIso.hom ≫ G.identity
  /-- The zeroth degree-one face is the source map. -/
  delta_one_zero : simplicialScheme.δ 0 ≫ objectsIso.hom = arrowsIso.hom ≫ G.source
  /-- The first degree-one face is the target map. -/
  delta_one_one : simplicialScheme.δ 1 ≫ objectsIso.hom = arrowsIso.hom ≫ G.target
  /-- Inserting an identity before an arrow is the zeroth degree-one degeneracy. -/
  sigma_one_zero : simplicialScheme.σ 0 ≫ composablePairsIso.hom =
    pullback.lift (arrowsIso.hom ≫ G.target ≫ G.identity) arrowsIso.hom (by
      simp only [Category.assoc, G.source_identity, Category.comp_id])
  /-- Inserting an identity after an arrow is the first degree-one degeneracy. -/
  sigma_one_one : simplicialScheme.σ 1 ≫ composablePairsIso.hom =
    pullback.lift arrowsIso.hom (arrowsIso.hom ≫ G.source ≫ G.identity) (by
      simp only [Category.assoc, G.target_identity, Category.comp_id])
  /-- The zeroth degree-two face forgets the first arrow. -/
  delta_two_zero : simplicialScheme.δ 0 ≫ arrowsIso.hom =
    composablePairsIso.hom ≫ pullback.snd G.source G.target
  /-- The middle degree-two face composes the two arrows. -/
  delta_two_one : simplicialScheme.δ 1 ≫ arrowsIso.hom =
    composablePairsIso.hom ≫ G.comp
  /-- The last degree-two face forgets the second arrow. -/
  delta_two_two : simplicialScheme.δ 2 ≫ arrowsIso.hom =
    composablePairsIso.hom ≫ pullback.fst G.source G.target
  /-- On every test scheme, the `n`-simplices are naturally the strings of `n` composable
  arrows in the groupoid of points. -/
  pointEquiv (n : ℕ) (T : Over S) :
    (T ⟶ simplicialScheme.obj (op (SimplexCategory.mk n))) ≃
      ComposableArrows (G.Evaluation T)ᵒᵖ n
  /-- Naturality in the test scheme on vertices of every string. -/
  pointEquiv_naturality_obj (n : ℕ) {T T' : Over S} (f : T' ⟶ T)
      (x : T ⟶ simplicialScheme.obj (op (SimplexCategory.mk n)))
      (i : Fin (n + 1)) :
    ((pointEquiv n T' (f ≫ x)).obj i).unop =
      f ≫ ((pointEquiv n T x).obj i).unop
  /-- Naturality in the test scheme on arrows of every string. -/
  pointEquiv_naturality_map (n : ℕ) {T T' : Over S} (f : T' ⟶ T)
      (x : T ⟶ simplicialScheme.obj (op (SimplexCategory.mk n)))
      (i j : Fin (n + 1)) (h : i ≤ j) :
    ((pointEquiv n T' (f ≫ x)).map (homOfLE h)).unop.arrow =
      f ≫ ((pointEquiv n T x).map (homOfLE h)).unop.arrow
  /-- In degree zero, the sole vertex is the displayed object coordinate. -/
  pointEquiv_zero (T : Over S)
      (x : T ⟶ simplicialScheme.obj (op (SimplexCategory.mk 0))) :
    ((pointEquiv 0 T x).obj 0).unop = x ≫ objectsIso.hom
  /-- In degree one, the unique edge is the displayed arrow coordinate. -/
  pointEquiv_one (T : Over S)
      (x : T ⟶ simplicialScheme.obj (op (SimplexCategory.mk 1))) :
    ((pointEquiv 1 T x).map (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).unop.arrow =
      x ≫ arrowsIso.hom
  /-- In degree two, the first edge is the first projection of the displayed pair. -/
  pointEquiv_two_first (T : Over S)
      (x : T ⟶ simplicialScheme.obj (op (SimplexCategory.mk 2))) :
    ((pointEquiv 2 T x).map (homOfLE (show (0 : Fin 3) ≤ 1 by decide))).unop.arrow =
      x ≫ composablePairsIso.hom ≫ pullback.fst G.source G.target
  /-- In degree two, the second edge is the second projection of the displayed pair. -/
  pointEquiv_two_second (T : Over S)
      (x : T ⟶ simplicialScheme.obj (op (SimplexCategory.mk 2))) :
    ((pointEquiv 2 T x).map (homOfLE (show (1 : Fin 3) ≤ 2 by decide))).unop.arrow =
      x ≫ composablePairsIso.hom ≫ pullback.snd G.source G.target
  /-- The point description commutes with every simplicial operator. -/
  pointEquiv_map {m n : ℕ} (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
      (T : Over S) (x : T ⟶ simplicialScheme.obj (op (SimplexCategory.mk n))) :
    pointEquiv m T (x ≫ simplicialScheme.map α.op) =
      (pointEquiv n T x).whiskerLeft α.toOrderHom.monotone.functor
  /-- The nerve is the `2`-coskeleton of its `2`-truncation. -/
  isCoskeletal : SimplicialObject.IsCoskeletal simplicialScheme 2

private lemma nerve_comp_refl_hom {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y}
    (h : f = g) : f ≫ (Iso.refl Y).hom = (Iso.refl X).hom ≫ g :=
  (Category.comp_id _).trans (h.trans (Category.id_comp _).symm)

private lemma groupoid_delta_two_two {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    (nerveSimplicialScheme G).δ (2 : Fin 3) ≫ (Iso.refl G.arrows).hom =
      (Iso.refl (pullback G.source G.target)).hom ≫ pullback.fst G.source G.target :=
  nerve_comp_refl_hom (nerveOperator_delta_two_two G)

private lemma groupoidSimplicialScheme_exists {S : Scheme.{u}}
    (G : GroupoidScheme S) : Nonempty (GroupoidSimplicialScheme G) := by
  let X := nerveSimplicialScheme G
  refine ⟨{
    simplicialScheme := X
    objectsIso := Iso.refl G.objects
    arrowsIso := Iso.refl G.arrows
    composablePairsIso := Iso.refl (pullback G.source G.target)
    sigma_zero :=
      nerve_comp_refl_hom (nerveOperator_sigma_zero G)
    delta_one_zero :=
      nerve_comp_refl_hom (nerveOperator_delta_one_zero G)
    delta_one_one :=
      nerve_comp_refl_hom (nerveOperator_delta_one_one G)
    sigma_one_zero := by
      refine nerve_comp_refl_hom ((nerveOperator_sigma_one_zero G).trans ?_)
      congr 1
    sigma_one_one := by
      refine nerve_comp_refl_hom ((nerveOperator_sigma_one_one G).trans ?_)
      congr 1
    delta_two_zero := nerve_comp_refl_hom (nerveOperator_delta_two_zero G)
    delta_two_one := nerve_comp_refl_hom (nerveOperator_delta_two_one G)
    delta_two_two := groupoid_delta_two_two G
    pointEquiv := fun n T => (nervePointData G T n).equiv
    pointEquiv_naturality_obj := by
      intro n T T' f x i
      have h := nervePointData_naturality G f n x
      calc
        (((nervePointData G T' n).equiv (f ≫ x)).obj i).unop =
            (((evaluationRestriction G f).op.obj
              (((nervePointData G T n).equiv x).obj i)).unop) :=
                congrArg (fun A => (A.obj i).unop) h.symm
        _ = f ≫ (((nervePointData G T n).equiv x).obj i).unop := rfl
    pointEquiv_naturality_map := by
      intro n T T' f x i j hij
      have h := nervePointData_naturality G f n x
      calc
        (((nervePointData G T' n).equiv (f ≫ x)).map (homOfLE hij)).unop.arrow =
            (((evaluationRestriction G f).op.map
              (((nervePointData G T n).equiv x).map (homOfLE hij))).unop.arrow) :=
                congrArg (fun A => (A.map (homOfLE hij)).unop.arrow) h.symm
        _ = f ≫ (((nervePointData G T n).equiv x).map (homOfLE hij)).unop.arrow := rfl
    pointEquiv_zero := fun T x =>
      congrArg Opposite.unop ((nervePointData G T 0).obj_zero x)
    pointEquiv_one _ _ := rfl
    pointEquiv_two_first := fun T x =>
      (nervePoints_two_first G T x).trans
        (congrArg (fun f => x ≫ f) (Category.id_comp (pullback.fst G.source G.target))).symm
    pointEquiv_two_second := fun T x =>
      (nervePoints_two_second G T x).trans
        (congrArg (fun f => x ≫ f) (Category.id_comp (pullback.snd G.source G.target))).symm
    pointEquiv_map := by
      intro m n α T x
      show (nervePointData G T m).equiv (x ≫ nerveOperator G α) = _
      exact nerveOperator_point G α T x
    isCoskeletal := nerveSimplicialScheme_isCoskeletal G
  }⟩

/-- **Stacks 07TN.** The simplicial scheme associated to a groupoid scheme. -/
@[stacks 07TN]
noncomputable def groupoidSimplicialScheme {S : Scheme.{u}}
    (G : GroupoidScheme S) : GroupoidSimplicialScheme G :=
  Classical.choice (by exact groupoidSimplicialScheme_exists G)

end Stacks.Groupoids.GroupoidScheme

end

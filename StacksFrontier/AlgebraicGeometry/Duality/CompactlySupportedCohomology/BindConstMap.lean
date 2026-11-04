module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.CompositionLowerShriek
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.OpenImmersionCovariance

/-!
# Extending a functor with values in pro-objects to morphisms into a constant pro-object

Let `G : 𝒞 ⥤ Pro-𝒟` and let `P = (M_n)` be a pro-object of `𝒞`. The pro-object
`CategoryTheory.ProSeq.bindObj G P` has functor of points `L ↦ colim_n Hom(G M_n, L)`; this is
the composition `Rg_! Rf_! K` of [Stacks, Tag 0G54] for `G = Rg_!` and `P = Rf_! K`. A morphism
`φ : P ⟶ K` into a constant pro-object is represented by some `a : M_n ⟶ K`, and `G` applied to
`φ` is the morphism `bindObj G P ⟶ G K` whose action on functors of points is
`Hom(G K, L) ⟶ Hom(G M_n, L) ⟶ colim_m Hom(G M_m, L)`; it does not depend on the representative.

## Main definitions

* `CategoryTheory.ProSeq.bindConstMap`: `G` applied to `φ : P ⟶ K`, a morphism
  `bindObj G P ⟶ G K`.

## Main results

* `CategoryTheory.ProSeq.bindConstMap_unop_hom_eq`: its action on functors of points through any
  representative `a : M_n ⟶ K` of `φ`.

## References

* [Stacks Project, Tag 0G54](https://stacks.math.columbia.edu/tag/0G54)
* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u'

namespace CategoryTheory.Pro

variable {𝒟 : Type u} [Category.{v} 𝒟]

/-- The backward components of the levelwise pro-isomorphism attached to an isomorphism `e` of
functors of points represent `e`: the class of `ψ n : G_{β n} ⟶ F_n` is the image under `e` of
the class of the identity of `F_n`. -/
public lemma seqStage_proIsoOfSeqHomColimIso_ψ {F G : ℕᵒᵖ ⥤ 𝒟} (e : seqHomColim F ≅ seqHomColim G)
    (n : ℕ) :
    seqStage G ((proIsoOfSeqHomColimIso e).ψ n) = e.hom.app _ (seqStage F (𝟙 (F.obj (op n)))) := by
  have hs := Classical.choose_spec (exists_sequentialRep e.hom)
  refine (seqStage_transition G _ _).trans ?_
  exact (hs n).symm

end CategoryTheory.Pro

namespace CategoryTheory.ProSeq

variable {𝒞 : Type u'} [Category.{v} 𝒞] {𝒟 : Type u} [Category.{v} 𝒟]

/-- The class in `colim_n Hom(M_n, K)` of a morphism `φ : P ⟶ K` into a constant pro-object, for
the inverse sequence `M = seqOf P` giving `P`. -/
public def constHomClass {P : ProSeq 𝒞} {K : 𝒞} (φ : P ⟶ const.obj K) :
    (Pro.seqHomColim (seqOf P)).obj K :=
  (Pro.seqHomColimIso (seqOf P)).hom.app K
    ((ofSeqOfIso P).hom.unop.hom.app K (homConstEquiv P K φ))

/-- A representative `M_n ⟶ K` of a morphism `φ : P ⟶ K` into a constant pro-object. -/
public def constHomRep {P : ProSeq 𝒞} {K : 𝒞} (φ : P ⟶ const.obj K) :
    Σ n : ℕ, (seqOf P).obj (op n) ⟶ K :=
  ⟨(Pro.seqStage_surjective (seqOf P) K (constHomClass φ)).choose,
    (Pro.seqStage_surjective (seqOf P) K (constHomClass φ)).choose_spec.choose⟩

/-- `CategoryTheory.ProSeq.constHomRep φ` represents `φ`. -/
public lemma seqStage_constHomRep {P : ProSeq 𝒞} {K : 𝒞} (φ : P ⟶ const.obj K) :
    Pro.seqStage (seqOf P) (constHomRep φ).2 = constHomClass φ :=
  ((Pro.seqStage_surjective (seqOf P) K (constHomClass φ)).choose_spec.choose_spec).symm

variable (G : 𝒞 ⥤ ProSeq 𝒟)

/-- The action of `G` applied to `a : M_n ⟶ K` on functors of points, followed by the leg of the
colimit `colim_m Hom(G M_m, -)` at `n`. -/
public abbrev bindConstLeg {P : ProSeq 𝒞} {K : 𝒞} {n : ℕ} (a : (seqOf P).obj (op n) ⟶ K) :
    (G.obj K).points ⟶ (bindObj G P).points :=
  (pointsFunctor G).map a.op ≫ colimit.ι ((seqOf P).rightOp ⋙ pointsFunctor G) n

/-- Two morphisms `M_n ⟶ K`, `M_m ⟶ K` with the same class give the same leg. -/
public lemma bindConstLeg_eq {P : ProSeq 𝒞} {K : 𝒞} {n m : ℕ} (a : (seqOf P).obj (op n) ⟶ K)
    (b : (seqOf P).obj (op m) ⟶ K) (h : Pro.seqStage (seqOf P) a = Pro.seqStage (seqOf P) b) :
    bindConstLeg G a = bindConstLeg G b := by
  obtain ⟨k, hn, hm, e⟩ := Pro.seqStage_eq (seqOf P) a b h
  have w : ∀ {j : ℕ} (c : (seqOf P).obj (op j) ⟶ K) (hj : j ≤ k), bindConstLeg G c =
      ((pointsFunctor G).map c.op ≫ ((seqOf P).rightOp ⋙ pointsFunctor G).map (homOfLE hj)) ≫
        colimit.ι ((seqOf P).rightOp ⋙ pointsFunctor G) k := fun c hj => by
    rw [Category.assoc, colimit.w]; rfl
  have key : (pointsFunctor G).map a.op ≫ ((seqOf P).rightOp ⋙ pointsFunctor G).map (homOfLE hn) =
      (pointsFunctor G).map b.op ≫ ((seqOf P).rightOp ⋙ pointsFunctor G).map (homOfLE hm) := by
    simp only [Functor.comp_map, Functor.rightOp_map, ← Functor.map_comp, ← op_comp]
    exact congrArg (fun t => (pointsFunctor G).map t.op) e
  rw [w a hn, w b hm, key]

/-- The identification `CategoryTheory.ProSeq.bindObjPointsIso` for the chosen sequence of `P` is
the identity on the legs `CategoryTheory.ProSeq.bindConstLeg`. -/
public lemma bindConstLeg_comp_bindObjPointsIso_hom {P : ProSeq 𝒞} {K : 𝒞} {n : ℕ}
    (a : (seqOf P).obj (op n) ⟶ K) :
    bindConstLeg G a ≫ (bindObjPointsIso G (ofSeqOfIso P)).hom = bindConstLeg G a := by
  set e := proIsoOfIso (ofSeqOfIso P ≪≫ (ofSeqOfIso P).symm)
  have h₁ : bindConstLeg G a ≫ (bindObjPointsIso G (ofSeqOfIso P)).hom =
      bindConstLeg G (e.ψ n ≫ a) := by
    change (pointsFunctor G).map a.op ≫ colimit.ι ((seqOf P).rightOp ⋙ pointsFunctor G) n ≫
      colimitMapOfProIso (pointsFunctor G) e = _
    rw [ι_colimitMapOfProIso, ← Category.assoc, ← Functor.map_comp]
    rfl
  have hid : (Pro.seqHomColimIso (seqOf P)).symm ≪≫
      ((IsSequentialProObject 𝒞).ι.mapIso (ofSeqOfIso P ≪≫ (ofSeqOfIso P).symm).unop).symm ≪≫
        Pro.seqHomColimIso (seqOf P) = Iso.refl _ := by
    rw [Iso.self_symm_id]
    ext1
    change (Pro.seqHomColimIso (seqOf P)).inv ≫
      ((IsSequentialProObject 𝒞).ι.map (𝟙 (of (seqOf P)).unop) ≫
        (Pro.seqHomColimIso (seqOf P)).hom) = 𝟙 _
    rw [CategoryTheory.Functor.map_id]
    exact (congrArg ((Pro.seqHomColimIso (seqOf P)).inv ≫ ·) (Category.id_comp _)).trans
      (Iso.inv_hom_id _)
  have h₂ : Pro.seqStage (seqOf P) (e.ψ n) = Pro.seqStage (seqOf P) (𝟙 _) := by
    refine (Pro.seqStage_proIsoOfSeqHomColimIso_ψ _ n).trans ?_
    rw [hid]
    rfl
  refine h₁.trans (bindConstLeg_eq G _ _ ?_)
  rw [← Pro.seqHomColim_map_seqStage, h₂, Pro.seqHomColim_map_seqStage, Category.id_comp]

/-- **`G` applied to a morphism `φ : P ⟶ K` into a constant pro-object**, as a morphism
`bindObj G P ⟶ G K` of pro-objects: on functors of points it is
`Hom(G K, L) ⟶ Hom(G M_n, L) ⟶ colim_m Hom(G M_m, L)` for a representative `a : M_n ⟶ K` of
`φ`. For `G = Rf_!` and `P = Ri_! K'` this is `Rf_!` applied to `Ri_! K' ⟶ K`, the source being
`Rf_! Ri_! K'` of [Stacks, Tag 0G54]. -/
public def bindConstMap {P : ProSeq 𝒞} {K : 𝒞} (φ : P ⟶ const.obj K) :
    bindObj G P ⟶ G.obj K :=
  (ObjectProperty.homMk (bindConstLeg G (constHomRep φ).2)).op

/-- `CategoryTheory.ProSeq.bindConstMap G φ` on functors of points, through any representative of
`φ`. -/
public lemma bindConstMap_unop_hom_eq {P : ProSeq 𝒞} {K : 𝒞} (φ : P ⟶ const.obj K) {n : ℕ}
    (a : (seqOf P).obj (op n) ⟶ K) (h : Pro.seqStage (seqOf P) a = constHomClass φ) :
    (bindConstMap G φ).unop.hom = bindConstLeg G a :=
  bindConstLeg_eq G _ _ ((seqStage_constHomRep φ).trans h.symm)

end CategoryTheory.ProSeq

end

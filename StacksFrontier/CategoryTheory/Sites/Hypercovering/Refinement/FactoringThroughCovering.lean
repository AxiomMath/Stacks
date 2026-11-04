module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Refinement.MatchingDegreeOne
import all StacksFrontier.CategoryTheory.Sites.Hypercovering.Refinement.DegreewiseProducts
import all StacksFrontier.CategoryTheory.Sites.Hypercovering.Refinement.MatchingDegreeOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Refining a hypercovering: higher matching maps and the refinement

The matching maps of `Hom(C[k], -)` in degrees `n + 1` with `n > 0`
(`constPowerMap_matching_prop_pos`), the refinement of a hypercovering is a hypercovering
(`isHypercovering_refinementByCovering`), and Tag 01GJ,
`exists_hypercovering_map_factoring_through_covering`.
-/

public section

universe w v u
universe w'
universe a b c d
universe w₂ u₁ v₁

open CategoryTheory CategoryTheory.Limits Simplicial SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

/- The two local attribute changes of `Refinement.DegreewiseProducts`, for the reasons given
there. -/
attribute [local implicit_reducible] CategoryTheory.SimplicialObject.power
attribute [-instance] CategoryTheory.Limits.FormalCoproduct.instHasProductsOfShape

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The degree-`(n + 1)` matching map of `Hom(C[k], -)` at a covering morphism is covering, for
`n > 0`: there the matching object is itself a finite power of the target and the matching map a
coordinate projection, by `power_cosk_unit_isProjection` (Tag 0B16). Companion of
`constPowerMap_matching_prop_zero`. -/
private theorem constPowerMap_matching_prop_pos
    {E : Type u₁} [Category.{v₁} E] [HasFiniteLimits E]
    [∀ (m : ℕ) (F : SimplicialObject.Truncated E m),
      (SimplexCategory.Truncated.inclusion m).op.HasPointwiseRightKanExtension F]
    (P : MorphismProperty E) [P.ContainsIdentities] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange]
    (k : ℕ) {Y Z : E} (u : Z ⟶ Y) (hu : P u)
    [∀ r : SimplexCategoryᵒᵖ, Finite ((simplexPowerIndex.{w} k).obj r.unop)]
    (n : ℕ) (hpos : 0 < n) :
    P
      (pullback.lift
        (f := (((SimplicialObject.coskAdj n).unit.app
          (((SimplicialObject.const (E)).obj Y).power
            (simplexPowerIndex.{w} k))).app
            (Opposite.op (SimplexCategory.mk (n + 1)))))
        (g := (((SimplicialObject.Truncated.cosk n).map
          ((SimplicialObject.truncation n).map (constPowerMap u (simplexPowerIndex.{w} k)))).app
            (Opposite.op (SimplexCategory.mk (n + 1)))))
        ((constPowerMap u (simplexPowerIndex.{w} k)).app
          (Opposite.op (SimplexCategory.mk (n + 1))))
        (((SimplicialObject.coskAdj n).unit.app
          (((SimplicialObject.const (E)).obj Z).power
            (simplexPowerIndex.{w} k))).app
            (Opposite.op (SimplexCategory.mk (n + 1))))
        (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality
          (constPowerMap u (simplexPowerIndex.{w} k)))
          (Opposite.op (SimplexCategory.mk (n + 1))))) := by
  classical
  let : ∀ r : SimplexCategoryᵒᵖ,
      Fintype ((simplexPowerIndex.{w} k).obj r.unop) := fun _ => Fintype.ofFinite _
  let D := E
  let U : CosimplicialObject (Type w) := simplexPowerIndex.{w} k
  let PZ : SimplicialObject D := ((SimplicialObject.const D).obj Z).power U
  let PY : SimplicialObject D := ((SimplicialObject.const D).obj Y).power U
  let b : PZ ⟶ PY := constPowerMap u U
  show P
      (pullback.lift
        (f := (((SimplicialObject.coskAdj n).unit.app PY).app
          (Opposite.op (SimplexCategory.mk (n + 1)))))
        (g := (((SimplicialObject.Truncated.cosk n).map
          ((SimplicialObject.truncation n).map b)).app
            (Opposite.op (SimplexCategory.mk (n + 1)))))
        (b.app (Opposite.op (SimplexCategory.mk (n + 1))))
        (((SimplicialObject.coskAdj n).unit.app PZ).app
          (Opposite.op (SimplexCategory.mk (n + 1))))
        (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality b)
          (Opposite.op (SimplexCategory.mk (n + 1)))))
  let : ∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F :=
    fun F =>
      (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
        (C := D)).2 (fun _ => inferInstance) n hpos F
  obtain ⟨S, e, he, hnat⟩ :=
    power_cosk_unit_isProjection (D := D) k n hpos
  let dN := Opposite.op (SimplexCategory.mk (n + 1))
  let α := U.obj (SimplexCategory.mk (n + 1))
  let β := ↥S
  let γ := {a : α // a ∉ S}
  let eSum : β ⊕ γ ≃ α := Equiv.sumCompl (fun a : α => a ∈ S)
  let : Fintype γ := Fintype.ofFinite _
  let : HasProduct (fun _ : β => Y) := inferInstance
  let : HasProduct (fun _ : γ => Y) := inferInstance
  let : HasProduct (fun _ : β => Z) := inferInstance
  let : HasProduct (fun _ : γ => Z) := inferInstance
  have hRestr (W : E) : Pi.map' (fun s : β => s.1) (fun _ => 𝟙 W) =
      (piSplitIso eSum (fun _ : α => W)).hom ≫ prod.fst := by
    apply Pi.hom_ext
    intro s
    simp only [Functor.flip_obj_obj, Pi.map'_comp_π, Category.comp_id, piSplitIso,
      piReindexIso, eqToHom_refl, piSumIso, Iso.trans_hom, prod.comp_lift, limit.lift_π,
      BinaryFan.mk_pt, BinaryFan.mk_fst, Category.assoc, Fan.mk_pt, Fan.mk_π_app]
    rw [Equiv.sumCompl_apply_inl]
  have hunit (W : E) :
      (((SimplicialObject.coskAdj n).unit.app (((SimplicialObject.const D).obj W).power U)).app
        dN) ≫ (e W).hom =
        (piSplitIso eSum (fun _ : α => W)).hom ≫ prod.fst := by
    rw [← hRestr W]
    exact (he W).trans (by simp; rfl)
  let splitY := piSplitIso eSum (fun _ : α => Y)
  let splitZ := piSplitIso eSum (fun _ : α => Z)
  have hunitY := hunit Y
  have hunitZ := hunit Z
  have hbapp : ∀ m : SimplexCategoryᵒᵖ,
      b.app m = CategoryTheory.Limits.Pi.map (fun _ => u) := by
    intro m
    rfl
  have hcosk :
      (((SimplicialObject.Truncated.cosk n).map
        ((SimplicialObject.truncation n).map b)).app dN) ≫ (e (Y)).hom =
        (e Z).hom ≫ CategoryTheory.Limits.Pi.map (fun _ : β => u) :=
    hnat Z (Y) u b hbapp
  let mβ : (∏ᶜ fun _ : β => Z) ⟶ ∏ᶜ fun _ : β => Y :=
    CategoryTheory.Limits.Pi.map fun _ : β => u
  let mγ : (∏ᶜ fun _ : γ => Z) ⟶ ∏ᶜ fun _ : γ => Y :=
    CategoryTheory.Limits.Pi.map fun _ : γ => u
  have hcoord (a : α) :
      b.app dN ≫ Pi.π (fun _ : α => Y) a = Pi.π (fun _ : α => Z) a ≫ u := by
    dsimp [b, constPowerMap, PY, PZ, SimplicialObject.power]
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using
      (CategoryTheory.Limits.Pi.map_π (fun _ : α => u) a)
  let eFullY : PY.obj dN ≅ (∏ᶜ fun _ : β => Y) ⨯ (∏ᶜ fun _ : γ => Y) := splitY
  let eFullZ : PZ.obj dN ≅ (∏ᶜ fun _ : β => Z) ⨯ (∏ᶜ fun _ : γ => Z) := splitZ
  have hsplitMap : b.app dN ≫ eFullY.hom = eFullZ.hom ≫ prod.map mβ mγ := by
    apply prod.hom_ext
    · apply Pi.hom_ext
      intro s
      simp only [eFullY, eFullZ, splitY, splitZ, mβ, Category.assoc, prod.map_fst, Limits.Pi.map_π]
      rw [piSplitIso_fst_π eSum (fun _ : α => Y) s,
        reassoc_of% piSplitIso_fst_π eSum (fun _ : α => Z) s, hcoord]
    · apply Pi.hom_ext
      intro s
      simp only [eFullY, eFullZ, splitY, splitZ, mγ, Category.assoc, prod.map_snd, Limits.Pi.map_π]
      rw [piSplitIso_snd_π eSum (fun _ : α => Y) s,
        reassoc_of% piSplitIso_snd_π eSum (fun _ : α => Z) s, hcoord]
  let fOld := (((SimplicialObject.coskAdj n).unit.app PY).app dN)
  let gOld := (((SimplicialObject.Truncated.cosk n).map
    ((SimplicialObject.truncation n).map b)).app dN)
  let pNew := pullback.map fOld gOld prod.fst mβ eFullY.hom (e Z).hom
    (e (Y)).hom (by simpa [eFullY] using hunitY) (by simpa using hcosk)
  let : IsIso eFullY.hom := inferInstance
  let : IsIso (e Z).hom := inferInstance
  let : IsIso (e (Y)).hom := inferInstance
  let ePB : pullback fOld gOld ≅ pullback prod.fst mβ := asIso pNew
  let eTarget := ePB.trans (pullbackProdFstIso mβ)
  let mOld := pullback.lift (b.app dN)
    (((SimplicialObject.coskAdj n).unit.app PZ).app dN)
    (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality b) dN)
  have hmOldFst : mOld ≫ pullback.fst fOld gOld = b.app dN :=
    pullback.lift_fst (f := fOld) (g := gOld)
      (b.app dN)
      (((SimplicialObject.coskAdj n).unit.app PZ).app dN)
      (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality b) dN)
  have hmOldSnd : mOld ≫ pullback.snd fOld gOld =
      ((SimplicialObject.coskAdj n).unit.app PZ).app dN :=
    pullback.lift_snd (f := fOld) (g := gOld)
      (b.app dN)
      (((SimplicialObject.coskAdj n).unit.app PZ).app dN)
      (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality b) dN)
  have hmOld : mOld ≫ eTarget.hom =
      eFullZ.hom ≫ prod.map (𝟙 _) mγ := by
    have hfst : (mOld ≫ eTarget.hom) ≫ prod.fst =
        (((SimplicialObject.coskAdj n).unit.app PZ).app dN) ≫ (e Z).hom := by
      have hpNew : pNew ≫ pullback.snd prod.fst mβ =
          pullback.snd fOld gOld ≫ (e Z).hom := by
        dsimp [pNew, pullback.map]
        simp only [pullback.lift_snd]
      simp [eTarget, ePB, pullbackProdFstIso, hpNew, reassoc_of% hmOldSnd]
    have hpNewFst : pNew ≫ pullback.fst prod.fst mβ =
        pullback.fst fOld gOld ≫ eFullY.hom := by
      dsimp [pNew, pullback.map]
      simp only [pullback.lift_fst]
    apply prod.hom_ext
    · calc
        _ = (((SimplicialObject.coskAdj n).unit.app PZ).app dN) ≫ (e Z).hom := hfst
        _ = splitZ.hom ≫ prod.fst := hunitZ
        _ = (eFullZ.hom ≫ prod.map (𝟙 _) mγ) ≫ prod.fst := by
              simp [eFullZ, Category.assoc]
    · simp [eTarget, ePB, pullbackProdFstIso, reassoc_of% hpNewFst, reassoc_of% hmOldFst,
        reassoc_of% hsplitMap]
  have hmCover : P (mOld ≫ eTarget.hom) := by
    rw [hmOld]
    have hmβ : P mβ :=
      prop_piMap (P := P) (A := fun _ : β => Z)
        (B := fun _ : β => Y) (f := fun _ => u) (hf := fun _ => hu)
    have hmγ : P mγ :=
      prop_piMap (P := P) (A := fun _ : γ => Z)
        (B := fun _ : γ => Y) (f := fun _ => u) (hf := fun _ => hu)
    have hid : P (𝟙 (∏ᶜ fun _ : β => Z)) :=
      prop_of_isIso P (𝟙 _)
    have hprod := CategoryTheory.MorphismProperty.prod_map P _ _ hid hmγ
    exact (P.cancel_left_of_respectsIso eFullZ.hom _).2 hprod
  exact (P.cancel_right_of_respectsIso mOld eTarget.hom).1 hmCover

/-! ### The refinement as data

Tag 01GJ asserts that a refinement exists. The refinement is in fact constructed, and a consumer
may need it by name rather than under an existential quantifier: the descent route of Tag 0DAX
has to exhibit an isomorphism between the composite of the refinement with `yonedaFormal` and a
concretely named simplicial object, which no existential statement can supply. The declarations
below therefore expose the construction — the refining hypercovering, its morphism to `K` and the
factorisation of its degree-`k` component through the covering — as data, and the tagged theorem
is read off from them.
-/

section RefinementData

variable {X : C} (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (k : ℕ)
  {Z : FormalCoproduct.{w} (Over X)}
  (u : Z ⟶ K.obj (Opposite.op (SimplexCategory.mk k)))


/-- **The refinement is a hypercovering.** The degree-zero component of `Hom(C[k], u)` is `u`
read through `Limits.productUniqueIso`, and its matching maps are covering by
`constPowerMap_matching_prop_zero` and `constPowerMap_matching_prop_pos`;
Tag 01GH for fibre products then applies. -/
theorem isHypercovering_refinementByCovering (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (hK : IsHypercovering J K) (hu : IsCoveringOver J u) :
    IsHypercovering J (refinementByCovering.{w} K k u) := by
  let b : constSimplexPower.{w} Z k ⟶
      constSimplexPower.{w} (K.obj (Opposite.op (SimplexCategory.mk k))) k :=
    constSimplexPowerMap.{w} u k
  let zero := Opposite.op (SimplexCategory.mk 0)
  let : Unique ((simplexPowerIndex.{w} k).obj (SimplexCategory.mk 0)) := by
    show Unique (ULift (SimplexCategory.mk k ⟶ SimplexCategory.mk 0))
    infer_instance
  let eZ : (∏ᶜ fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 0) => Z) ≅ Z :=
    CategoryTheory.Limits.productUniqueIso _
  let eY : (∏ᶜ fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 0) =>
      K.obj (Opposite.op (SimplexCategory.mk k))) ≅
      K.obj (Opposite.op (SimplexCategory.mk k)) :=
    CategoryTheory.Limits.productUniqueIso _
  let eZfull : (constSimplexPower.{w} Z k).obj zero ≅ Z := eZ
  let eYfull : (constSimplexPower.{w} (K.obj (Opposite.op (SimplexCategory.mk k))) k).obj zero ≅
      K.obj (Opposite.op (SimplexCategory.mk k)) := eY
  have hpow0 : b.app zero ≫ eYfull.hom = eZfull.hom ≫ u := by
    show CategoryTheory.Limits.Pi.map (fun _ => u) ≫ eY.hom = eZ.hom ≫ u
    exact piMap_comp_productUniqueIso_hom u
  have hb0 : IsCoveringOver J (b.app zero) := by
    rw [← isCoveringOver_comp_iso_iff J (b.app zero) eYfull, hpow0]
    exact (isCoveringOver_iso_comp_iff J eZfull u).2 hu
  have hmatching : ∀ n : ℕ, IsCoveringOver J
      (pullback.lift
        (f := (((SimplicialObject.coskAdj n).unit.app
          (constSimplexPower.{w} (K.obj (Opposite.op (SimplexCategory.mk k))) k)).app
          (Opposite.op (SimplexCategory.mk (n + 1)))))
        (g := (((SimplicialObject.Truncated.cosk n).map
          ((SimplicialObject.truncation n).map b)).app
            (Opposite.op (SimplexCategory.mk (n + 1)))))
        (b.app (Opposite.op (SimplexCategory.mk (n + 1))))
        (((SimplicialObject.coskAdj n).unit.app (constSimplexPower.{w} Z k)).app
          (Opposite.op (SimplexCategory.mk (n + 1))))
        (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality b)
          (Opposite.op (SimplexCategory.mk (n + 1))))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact (coveringOverProperty_iff J _).1
        (constPowerMap_matching_prop_zero (coveringOverProperty J X) k u
          ((coveringOverProperty_iff J u).2 hu))
    · exact (coveringOverProperty_iff J _).1
        (constPowerMap_matching_prop_pos (coveringOverProperty J X) k u
          ((coveringOverProperty_iff J u).2 hu) n hpos)
  exact isHypercovering_fibreProduct J (constSimplexPowerUnit.{w} K k) b hK hb0 hmatching

end RefinementData

/-- **Stacks Project, Tag 01GJ.** A covering of the term in any fixed degree of a
hypercovering can be refined by a morphism from another hypercovering, whose component in that
degree factors through the covering. -/
@[stacks 01GJ, sga "4 V 7.3.2" "2)"]
public theorem exists_hypercovering_map_factoring_through_covering
    (J : Pretopology C) [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering J K) (k : ℕ)
    {Z : FormalCoproduct.{w} (Over X)}
    (u : Z ⟶ K.obj (Opposite.op (SimplexCategory.mk k)))
    (hu : IsCoveringOver J u) :
    ∃ (L : SimplicialObject (FormalCoproduct.{w} (Over X))),
      IsHypercovering J L ∧
        ∃ (f : L ⟶ K) (g : L.obj (Opposite.op (SimplexCategory.mk k)) ⟶ Z),
          g ≫ u = f.app (Opposite.op (SimplexCategory.mk k)) :=
  ⟨refinementByCovering.{w} K k u, isHypercovering_refinementByCovering K k u J hK hu,
    refinementByCoveringMap.{w} K k u, refinementByCoveringFactor.{w} K k u,
    refinementByCoveringFactor_comp.{w} K k u⟩

end Stacks.CategoryTheory.Hypercovering

module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge

/-!
# The descent-data bridge, relative to an equivalence relation on generalized points

`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge` converts between the two
shapes of the descent data occurring in the middle paragraph of Stacks 0APL: an isomorphism of
literal fibre products `V ×_S X ≅ X ×_S V`, and an `AlgebraicGeometry.DescentDatum`. In both
directions the bookkeeping is done with a morphism of schemes `b : V ⟶ Y` which the gluing
isomorphism leaves invariant, and the cocycle condition is derived from the fact that morphisms
into `V` are determined by their composites with `V ⟶ X` and with `b`.

For a *formal* algebraic space the chart is not a scheme, so there is no such `b`: the
morphism the gluing isomorphism leaves invariant is a morphism of sheaves out of `V`, and its
composites can only be formed with morphisms out of objects of a size-bounded site. This file
states the two directions of the bridge with the morphism `b` replaced by an arbitrary relation
`R` between generalized points of `V`, stable under precomposition. In the forward direction
`R` has to be an equivalence relation, and the extensionality of morphisms into `V` is needed
at **one** test object only, the left-associated triple product on which the cocycle condition
lives, rather than at every scheme.

## Main results

* `AlgebraicGeometry.exists_transition_of_pullbackIso_of_rel`: the forward direction. An
  isomorphism of literal fibre products respecting the projections to `X` and preserving the
  relation `R` is the gluing isomorphism of a descent datum, for whose action `R` relates every
  generalized point to its translate.
* `AlgebraicGeometry.DescentData.exists_descent_of_isEffective_of_rel`: the backward direction.
  If a descent datum is effective and its action preserves `R`, the descended scheme `W₀`
  comes with an isomorphism `X ×_S W₀ ≅ V` over `X` along which the two projections of the
  self-fibre product of `X ×_S W₀` over `W₀` are related by `R`.

## References

* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 0AQD](https://stacks.math.columbia.edu/tag/0AQD)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The forward direction of the descent-data bridge, relative to an equivalence relation.**
Let `g : X ⟶ S` be a morphism of schemes and `pₛ : V ⟶ X` a scheme over `X`, and let `R` be an
equivalence relation between generalized points of `V` which is stable under precomposition. An
isomorphism `Θ : V ×_S X ≅ X ×_S V` of literal fibre products whose `X`-components are the
expected ones (`hΘ1` and `hΘ2`) and which relates its two `V`-components by `R` (`hΘ3`) is the
gluing isomorphism of a descent datum on `V` relative to `g`, for whose action `R` relates every
generalized point to its translate.

The cocycle condition is the only thing that needs an argument, and `hext` is what it needs:
two generalized points of `V` over `X ×_S X ×_S X`, defined on the left-associated triple
product, which are related by `R` and agree after `pₛ` are equal. This is
`AlgebraicGeometry.exists_transition_of_pullbackIso` with the invariant morphism `b` replaced
by `R`; that statement is the case where `R` is equality after composing with `b`. -/
theorem exists_transition_of_pullbackIso_of_rel {T₀ X₀ V₀ : Scheme.{u}} (g : X₀ ⟶ T₀)
    (pₛ : V₀ ⟶ X₀) (R : ∀ {Z : Scheme.{u}}, (Z ⟶ V₀) → (Z ⟶ V₀) → Prop)
    (hRcomp : ∀ {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (a₁ a₂ : Z ⟶ V₀), R a₁ a₂ → R (k ≫ a₁) (k ≫ a₂))
    (hRsymm : ∀ {Z : Scheme.{u}} (a₁ a₂ : Z ⟶ V₀), R a₁ a₂ → R a₂ a₁)
    (hRtrans : ∀ {Z : Scheme.{u}} (a₁ a₂ a₃ : Z ⟶ V₀), R a₁ a₂ → R a₂ a₃ → R a₁ a₃)
    (Θ : pullback (pₛ ≫ g) g ≅ pullback g (pₛ ≫ g))
    (hΘ1 : Θ.hom ≫ pullback.fst g (pₛ ≫ g) = pullback.fst (pₛ ≫ g) g ≫ pₛ)
    (hΘ2 : Θ.hom ≫ pullback.snd g (pₛ ≫ g) ≫ pₛ = pullback.snd (pₛ ≫ g) g)
    (hΘ3 : R (Θ.hom ≫ pullback.snd g (pₛ ≫ g)) (pullback.fst (pₛ ≫ g) g))
    (hext : ∀ a₁ a₂ : ((Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g) ⨯ Over.mk g ⟶
        (Over.map g).obj (Over.mk pₛ),
      R a₁.left a₂.left → a₁.left ≫ pₛ = a₂.left ≫ pₛ → a₁ = a₂) :
    ∃ φ : Over.mk (prod.map (structureMap g (Over.mk pₛ)) (𝟙 (Over.mk g))) ≅
        Over.mk (prod.map (𝟙 (Over.mk g)) (structureMap g (Over.mk pₛ))),
      (prod.map φ.hom.left (𝟙 (Over.mk g)) ≫ prodMapLastTwo φ.hom.left =
        prodMapFirstThird φ.hom.left) ∧
      ∀ {Z : Over T₀} (v : Z ⟶ (Over.map g).obj (Over.mk pₛ)) (x : Z ⟶ Over.mk g),
        R (gluingAction (Over.mk pₛ) φ.hom.left v x).left v.left := by
  have hA1 : (Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g)).hom ≫
      pullback.fst (pₛ ≫ g) g =
        (prod.fst : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  have hA2 : (Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g)).hom ≫
      pullback.snd (pₛ ≫ g) g =
        (prod.snd : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have hB1 : (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).inv ≫
      (prod.fst : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left =
        pullback.fst g (pₛ ≫ g) :=
    Over.prodLeftIsoPullback_inv_fst _ _
  have hB2 : (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).inv ≫
      (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left =
        pullback.snd g (pₛ ≫ g) :=
    Over.prodLeftIsoPullback_inv_snd _ _
  set e : ((Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g).left ≅
      (Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ)).left :=
    Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g) ≪≫ Θ ≪≫
      (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).symm with he
  have key1 : e.hom ≫ (prod.fst : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left =
      (prod.fst : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left ≫ pₛ := by
    simp only [he, Iso.trans_hom, Iso.symm_hom, Category.assoc, hB1]
    rw [hΘ1, ← Category.assoc, hA1]
  have hB2p : (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).inv ≫
      (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left ≫ pₛ =
        pullback.snd g (pₛ ≫ g) ≫ pₛ := by rw [← Category.assoc, hB2]
  have key2 : e.hom ≫ (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left ≫ pₛ =
      (prod.snd : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left := by
    simp only [he, Iso.trans_hom, Iso.symm_hom, Category.assoc, hB2p]
    rw [hΘ2, hA2]
  have key3e : e.hom ≫ (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left =
      (Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g)).hom ≫
        Θ.hom ≫ pullback.snd g (pₛ ≫ g) := by
    simp only [he, Iso.trans_hom, Iso.symm_hom, Category.assoc, hB2]
  have key3 : R (e.hom ≫ (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left)
      (prod.fst : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left := by
    rw [key3e, ← hA1]
    exact hRcomp _ _ _ hΘ3
  have hover : e.hom ≫ (Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ)).hom =
      ((Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g).hom := by
    rw [← Over.w (prod.fst : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ Over.mk g),
      ← Category.assoc, key1, Category.assoc]
    exact Over.w (prod.fst : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _)
  have h1 : (Over.isoMk e hover).hom ≫ prod.fst = prod.fst ≫ structureMap g (Over.mk pₛ) := by
    refine Over.OverMorphism.ext ?_
    simpa using key1
  have h2 : (Over.isoMk e hover).hom ≫ prod.snd ≫ structureMap g (Over.mk pₛ) = prod.snd := by
    refine Over.OverMorphism.ext ?_
    simpa using key2
  have hinv : ∀ {Z : Over T₀} (v : Z ⟶ (Over.map g).obj (Over.mk pₛ)) (x : Z ⟶ Over.mk g),
      R (gluingAction (Over.mk pₛ) (Over.isoMk e hover).hom v x).left v.left := by
    intro Z v x
    have h := hRcomp (prod.lift v x).left _ _ key3
    have hv : (prod.lift v x).left ≫
        (prod.fst : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left = v.left := by
      rw [← Over.comp_left, prod.lift_fst]
    rw [hv] at h
    simpa only [gluingAction, Over.comp_left, Over.isoMk_hom_left, Category.assoc] using h
  have hw : (Over.isoMk e hover).hom ≫
      prod.map (𝟙 (Over.mk g)) (structureMap g (Over.mk pₛ)) =
      prod.map (structureMap g (Over.mk pₛ)) (𝟙 (Over.mk g)) := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.map_fst, Category.comp_id, prod.map_fst]
      exact h1
    · rw [Category.assoc, prod.map_snd, prod.map_snd, Category.comp_id]
      exact h2
  have hs : ∀ {Z' : Over T₀} (w : Z' ⟶ (Over.map g).obj (Over.mk pₛ)) (y' : Z' ⟶ Over.mk g),
      (gluingAction (Over.mk pₛ) (Over.isoMk e hover).hom w y').left ≫ pₛ = y'.left :=
    fun w y' => by
      simpa using congrArg (fun t => Over.Hom.left t)
        (gluingAction_comp_structureMap (Over.mk pₛ) (Over.isoMk e hover).hom h2 w y')
  -- the cocycle law at the universal generalized point of the triple product
  set φ := (Over.isoMk e hover).hom with hφ
  set v₀ := ((prod.fst : ((Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _) ≫
    prod.fst) with hv₀
  set x₀ := ((prod.fst : ((Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _) ≫
    prod.snd) with hx₀
  set y₀ := (prod.snd : ((Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _) with hy₀
  have hact : gluingAction (Over.mk pₛ) φ (gluingAction (Over.mk pₛ) φ v₀ x₀) y₀ =
      gluingAction (Over.mk pₛ) φ v₀ y₀ := by
    refine hext _ _ ?_ ?_
    · exact hRtrans _ _ _ (hRtrans _ _ _ (hinv _ y₀) (hinv v₀ x₀))
        (hRsymm _ _ (hinv v₀ y₀))
    · rw [hs, hs]
  have hA1' := gluingAction_cocycleLhs_fst (Over.mk pₛ) φ v₀ x₀ y₀ h1 h2
  have hB1' := gluingAction_cocycleRhs_fst (Over.mk pₛ) φ v₀ x₀ y₀ h1
  have hA2' := gluingAction_cocycleLhs_snd (Over.mk pₛ) φ v₀ x₀ y₀
  have hB2' := gluingAction_cocycleRhs_snd (Over.mk pₛ) φ v₀ x₀ y₀
  rw [hv₀, hx₀, hy₀, prodLift_triple_eq_id, Category.id_comp] at hA1' hB1' hA2' hB2'
  refine ⟨Over.isoMk (Over.isoMk e hover) hw, ?_, ?_⟩
  · change prod.map φ (𝟙 (Over.mk g)) ≫ prodMapLastTwo φ = prodMapFirstThird φ
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, hA1', hB1']
    · rw [Category.assoc, hA2', hB2', hact]
  · exact hinv

namespace DescentData

/-- **The backward direction of the descent-data bridge, relative to a relation.** Let `D` be a
descent datum relative to `g : X ⟶ S` and let `R` be a relation between generalized points of
its scheme which relates the translate of every generalized point to the point itself. If `D` is
effective then there are a scheme `W₀`, a morphism `w₀ : W₀ ⟶ S` and an isomorphism
`α₀ : X ×_S W₀ ≅ V` over `X` along which the second and the first projection of the self-fibre
product of `X ×_S W₀` over `W₀` are related by `R`.

This is `AlgebraicGeometry.DescentData.exists_descent_of_isEffective` with the invariant
morphism `b` replaced by `R`; no property of `R` is needed. -/
theorem exists_descent_of_isEffective_of_rel {S X : Scheme.{u}} {g : X ⟶ S}
    (D : DescentDatum g) (R : ∀ {Z : Scheme.{u}}, (Z ⟶ D.over.left) → (Z ⟶ D.over.left) → Prop)
    (hb : ∀ {Z : Over S} (v : Z ⟶ (Over.map g).obj D.over) (x : Z ⟶ Over.mk g),
      R (D.act v x).left v.left)
    (hEff : DescentData.IsEffective D) :
    ∃ (W₀ : Scheme.{u}) (w₀ : W₀ ⟶ S) (α₀ : pullback g w₀ ≅ D.over.left),
      α₀.hom ≫ D.over.hom = pullback.fst g w₀ ∧
      R (pullback.snd (pullback.snd g w₀) (pullback.snd g w₀) ≫ α₀.hom)
        (pullback.fst (pullback.snd g w₀) (pullback.snd g w₀) ≫ α₀.hom) := by
  obtain ⟨W, ⟨ε⟩⟩ := hEff
  obtain ⟨ι, hπ⟩ := exists_iso_canonical_over g W
  have hιw : ι.inv.left ≫ (DescentDatum.over ((canonicalFunctor g).obj W)).hom =
      pullback.snd W.hom g := Over.w ι.inv
  have hιw' : ι.hom.left ≫ pullback.snd W.hom g =
      (DescentDatum.over ((canonicalFunctor g).obj W)).hom := Over.w ι.hom
  have hsym1 : (pullbackSymmetry g W.hom).hom ≫ pullback.snd W.hom g = pullback.fst g W.hom :=
    pullbackSymmetry_hom_comp_snd g W.hom
  have hsym2 : (pullbackSymmetry g W.hom).hom ≫ pullback.fst W.hom g = pullback.snd g W.hom :=
    pullbackSymmetry_hom_comp_fst g W.hom
  have hεw : ((DescentDatum.forget g).map ε.hom).left ≫ D.over.hom =
      (DescentDatum.over ((canonicalFunctor g).obj W)).hom := Over.w _
  have hequiv : ∀ {Z : Over S}
      (v : Z ⟶ (Over.map g).obj (DescentDatum.over ((canonicalFunctor g).obj W)))
      (x : Z ⟶ Over.mk g),
      DescentDatum.act ((canonicalFunctor g).obj W) v x ≫
          (Over.map g).map ((DescentDatum.forget g).map ε.hom) =
        D.act (v ≫ (Over.map g).map ((DescentDatum.forget g).map ε.hom)) x :=
    (DescentDatum.hom_comm_iff ((canonicalFunctor g).obj W) D
      ((DescentDatum.forget g).map ε.hom)).mp (ε.hom.comm () ())
  have hpt : ∀ (Z : Over S) (k : Z.left ⟶ pullback g W.hom),
      k ≫ pullback.fst g W.hom ≫ g = Z.hom →
      ∃ (v : Z ⟶ (Over.map g).obj (DescentDatum.over ((canonicalFunctor g).obj W)))
        (x : Z ⟶ Over.mk g),
        v.left = k ≫ (pullbackSymmetry g W.hom).hom ≫ ι.inv.left ∧
        x.left = k ≫ pullback.fst g W.hom := by
    intro Z k hk
    refine ⟨Over.homMk (k ≫ (pullbackSymmetry g W.hom).hom ≫ ι.inv.left) ?_,
      Over.homMk (k ≫ pullback.fst g W.hom) ?_, rfl, rfl⟩
    · change (k ≫ (pullbackSymmetry g W.hom).hom ≫ ι.inv.left) ≫
        (DescentDatum.over ((canonicalFunctor g).obj W)).hom ≫ g = Z.hom
      rw [Category.assoc, Category.assoc, ← Category.assoc ι.inv.left, hιw,
        ← Category.assoc (pullbackSymmetry g W.hom).hom, hsym1]
      exact hk
    · rw [Category.assoc]
      exact hk
  refine ⟨W.left, W.hom, pullbackSymmetry g W.hom ≪≫ ((Over.forget X).mapIso ι).symm ≪≫
    (Over.forget X).mapIso ((DescentDatum.forget g).mapIso ε), ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Over.forget_map, Category.assoc]
    rw [hεw, hιw, hsym1]
  · have hcond : pullback.fst g W.hom ≫ g = pullback.snd g W.hom ≫ W.hom :=
      pullback.condition
    have hκ : pullback.fst (pullback.snd g W.hom) (pullback.snd g W.hom) ≫
        pullback.snd g W.hom =
        pullback.snd (pullback.snd g W.hom) (pullback.snd g W.hom) ≫ pullback.snd g W.hom :=
      pullback.condition
    have hcommon : pullback.snd (pullback.snd g W.hom) (pullback.snd g W.hom) ≫
        pullback.fst g W.hom ≫ g =
        (Over.mk (pullback.fst (pullback.snd g W.hom) (pullback.snd g W.hom) ≫
          pullback.fst g W.hom ≫ g)).hom := by
      change _ = pullback.fst (pullback.snd g W.hom) (pullback.snd g W.hom) ≫
        pullback.fst g W.hom ≫ g
      rw [hcond, ← Category.assoc, ← Category.assoc, hκ]
    obtain ⟨v₁, x₁, hv₁, hx₁⟩ := hpt (Over.mk (pullback.fst (pullback.snd g W.hom)
        (pullback.snd g W.hom) ≫ pullback.fst g W.hom ≫ g))
      (pullback.fst (pullback.snd g W.hom) (pullback.snd g W.hom)) rfl
    obtain ⟨v₂, x₂, hv₂, hx₂⟩ := hpt (Over.mk (pullback.fst (pullback.snd g W.hom)
        (pullback.snd g W.hom) ≫ pullback.fst g W.hom ≫ g))
      (pullback.snd (pullback.snd g W.hom) (pullback.snd g W.hom)) hcommon
    have hinvhom : ι.inv.left ≫ ι.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, ι.inv_hom_id]; rfl
    have hcancelf : ι.inv.left ≫ ι.hom.left ≫ pullback.fst W.hom g = pullback.fst W.hom g := by
      rw [← Category.assoc, hinvhom, Category.id_comp]
    have hact2 : (DescentDatum.act ((canonicalFunctor g).obj W) v₁ x₂).left ≫
        (DescentDatum.over ((canonicalFunctor g).obj W)).hom = x₂.left := by
      simpa only [Over.comp_left, Over.homMk_left] using congrArg (fun t => Over.Hom.left t)
        (DescentDatum.act_comp_structureMap ((canonicalFunctor g).obj W) v₁ x₂)
    have hCact : DescentDatum.act ((canonicalFunctor g).obj W) v₁ x₂ = v₂ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono ι.hom.left]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hπ, hv₁, hv₂]
        simp only [Category.assoc, hcancelf, hsym2]
        exact hκ
      · rw [Category.assoc, Category.assoc, hιw', hact2, hv₂]
        simp only [Category.assoc, hιw, hsym1]
        exact hx₂
    have h3 := hb (v₁ ≫ (Over.map g).map ((DescentDatum.forget g).map ε.hom)) x₂
    rw [← hequiv v₁ x₂, hCact] at h3
    simp only [Over.comp_left, Over.map_map_left, hv₁, hv₂] at h3
    simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Over.forget_map, Category.assoc] using h3

end DescentData

end AlgebraicGeometry

end

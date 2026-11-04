module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitOpenLift
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitPreserving

/-!
# Reduction of the surjectivity in the limit preservation of the contraction functor

In the proof of Stacks 0GI5 the surjectivity of `colim F(V_i) ⟶ F(V)` is étale local
(`AlgebraicGeometry.Artin.ContractionSituation.exists_stage_of_localLift`) and holds near the
points outside `Z` (`AlgebraicGeometry.Artin.ContractionSituation.exists_localLift_of_not_mem`).
This file reduces the remaining case to two statements about any property `P` of elements:

* a *core* statement: an element over the limit of any system which has `P` comes from a stage;
* a *local* statement: every point of `Z` has an étale neighbourhood `V ×_{V_i} N`, `N` affine and
  étale over a stage, on which the restriction of `ξ` has `P`.

In the source, `P` is "the formal component factors through an affine formal algebraic space
étale over `W`", the local statement is the reduction to an affine `W`, and the core statement is
the algebra of the last part of the proof.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.baseChangeDiagram`,
  `AlgebraicGeometry.Artin.ContractionSituation.baseChangeCone`: the base change
  `k ↦ V_k ×_{V_i} N` of the system along an étale `N ⟶ V_i`, with its limit `V ×_{V_i} N`.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_stage_of_core`: the reduction.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ LocallyNoetherianOver B S hS}
  (κ : Cone D)

section BaseChange

variable {i : I} {N : BigFppfOver B S hS} (q : N ⟶ (D.obj i).obj)
  (hq : Etale ((BigFppfOver.toScheme B S hS).map q))

/-- The base change `k ↦ V_k ×_{V_i} N` of the system along an étale `q : N ⟶ V_i`, as a diagram
of locally Noetherian objects over the stages above `i`. -/
noncomputable def baseChangeDiagram : Over i ⥤ LocallyNoetherianOver B S hS :=
  ObjectProperty.lift _ (overBaseChangeDiagram (D ⋙ ObjectProperty.ι _) i q) fun h =>
    isLocallyNoetherian_pullback_of_etale_right _ q hq (D.obj h.left).property

/-- The base change `V ×_{V_i} N` of the limit, as a cone over `baseChangeDiagram`. -/
noncomputable def baseChangeCone : Cone (baseChangeDiagram q hq) where
  pt := ⟨pullback (κ.π.app i).hom q,
    isLocallyNoetherian_pullback_of_etale_right _ q hq κ.pt.property⟩
  π :=
    { app := fun h => ObjectProperty.homMk
        ((overBaseChangeCone (D ⋙ ObjectProperty.ι _) ((ObjectProperty.ι _).mapCone κ) i q).π.app h)
      naturality := fun _ _ φ => ObjectProperty.hom_ext _
        ((overBaseChangeCone (D ⋙ ObjectProperty.ι _) ((ObjectProperty.ι _).mapCone κ) i
          q).π.naturality φ) }

variable {κ}

/-- The base change of a limit along an étale morphism into a stage is a limit. -/
noncomputable def isLimitBaseChangeCone
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ)) :
    IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone (baseChangeCone κ q hq)) :=
  isLimitMapOverBaseChangeCone (D ⋙ ObjectProperty.ι _) ((ObjectProperty.ι _).mapCone κ) i q
    (BigFppfOver.toScheme B S hS) hκ

omit [IsCofiltered I] in
/-- If every stage `V_k` and `N` are affine, then every object `V_k ×_{V_i} N` of
`baseChangeDiagram` is affine. -/
theorem isAffine_baseChangeDiagram_obj
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N)) (h : Over i) :
    IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj ((baseChangeDiagram q hq).obj h)) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj h.left).obj) := hD h.left
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj) := hD i
  exact isAffine_pullback (D.map h.hom).hom q

omit [IsCofiltered I] in
/-- If every stage `V_k`, the limit `V` and `N` are affine, then the point `V ×_{V_i} N` of
`baseChangeCone` is affine. -/
theorem isAffine_baseChangeCone_pt
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt))
    (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N)) :
    IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (baseChangeCone κ q hq).pt) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj) := hpt
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (((Functor.const I).obj κ.pt).obj i).obj) := hpt
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj) := hD i
  exact isAffine_pullback (κ.π.app i).hom q

end BaseChange

section Lift

variable {κ} (c : ContractionSituation B S hS)
  (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))

omit [IsCofiltered I] in
include hD in
/-- **A local lift from an element over a stage of the base-changed system**: if `y ∈ F(V_k ×_{V_i}
N)` restricts on `V ×_{V_i} N` to the restriction of `ξ`, then `V_k ×_{V_i} N ⟶ V_k` and `y` are a
local lift of `ξ` at `k` whose image in `V` contains that of `V ×_{V_i} N`. -/
theorem exists_localLift_of_baseChange {ξ : Triple c κ.pt.obj} {i : I} {N : BigFppfOver B S hS}
    (q : N ⟶ (D.obj i).obj) (hq : Etale ((BigFppfOver.toScheme B S hS).map q))
    (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N)) (h : Over i)
    (y : Triple c ((baseChangeDiagram q hq).obj h).obj)
    (hy : mapTriple c ((baseChangeCone κ q hq).π.app h).hom y =
      mapTriple c (pullback.fst (κ.π.app i).hom q) ξ) :
    ∃ L : LocalLift c κ ξ h.left,
      Set.range ((BigFppfOver.toScheme B S hS).map (pullback.fst (κ.π.app i).hom q)).base ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map
          (pullback.snd L.e.hom (κ.π.app h.left).hom)).base := by
  have hw : (κ.π.app h.left).hom ≫ (D.map h.hom).hom = (κ.π.app i).hom :=
    congrArg (fun k => k.hom) (κ.w h.hom)
  let E' := (baseChangeDiagram q hq).obj h
  let e' : E' ⟶ D.obj h.left := ObjectProperty.homMk (pullback.fst (D.map h.hom).hom q)
  let π' : pullback (κ.π.app i).hom q ⟶ pullback (D.map h.hom).hom q :=
    ((baseChangeCone κ q hq).π.app h).hom
  let m : pullback (pullback.fst (D.map h.hom).hom q) (κ.π.app h.left).hom ⟶
      pullback (κ.π.app i).hom q :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.snd _ _) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, hw])
  have hπ₁ : π' ≫ pullback.fst (D.map h.hom).hom q =
      pullback.fst (κ.π.app i).hom q ≫ (κ.π.app h.left).hom := pullback.lift_fst _ _ _
  have hπ₂ : π' ≫ pullback.snd (D.map h.hom).hom q = pullback.snd (κ.π.app i).hom q :=
    pullback.lift_snd _ _ _
  have hmπ : m ≫ π' = pullback.fst (pullback.fst (D.map h.hom).hom q) (κ.π.app h.left).hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hπ₁, pullback.lift_fst_assoc]
      exact pullback.condition.symm
    · rw [Category.assoc, hπ₂, pullback.lift_snd]
  have hm₁ : m ≫ pullback.fst (κ.π.app i).hom q =
      pullback.snd (pullback.fst (D.map h.hom).hom q) (κ.π.app h.left).hom :=
    pullback.lift_fst _ _ _
  have hagree : mapTriple c (pullback.fst e'.hom (κ.π.app h.left).hom) y =
      mapTriple c (pullback.snd e'.hom (κ.π.app h.left).hom) ξ := by
    refine (congrArg (fun φ => mapTriple c φ y) hmπ.symm).trans ?_
    refine (mapTriple_comp c m π' y).trans ?_
    refine (congrArg (mapTriple c m) hy).trans ?_
    refine (mapTriple_comp c m _ ξ).symm.trans ?_
    exact congrArg (fun φ => mapTriple c φ ξ) hm₁
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj h.left).obj) := hD h.left
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj) := hD i
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj N) := hN
  refine ⟨LocalLift.mk E' e' (etale_pullback_fst _ q hq) (isAffine_pullback (D.map h.hom).hom q)
    y hagree, ?_⟩
  rintro _ ⟨z₀, rfl⟩
  have e₁ : (BigFppfOver.toScheme B S hS).map π' ≫
      (BigFppfOver.toScheme B S hS).map (pullback.fst (D.map h.hom).hom q) =
      (BigFppfOver.toScheme B S hS).map (pullback.fst (κ.π.app i).hom q) ≫
        (BigFppfOver.toScheme B S hS).map (κ.π.app h.left).hom := by
    rw [← Functor.map_comp, ← Functor.map_comp, hπ₁]
  obtain ⟨z, -, hz⟩ := exists_pullback_point (pullback.fst (D.map h.hom).hom q)
    (κ.π.app h.left).hom (((BigFppfOver.toScheme B S hS).map π').base z₀)
    (((BigFppfOver.toScheme B S hS).map (pullback.fst (κ.π.app i).hom q)).base z₀)
    (congrArg (fun φ => φ.base z₀) e₁)
  exact ⟨z, hz⟩

/-- **The surjectivity of the limit preservation, reduced to a core and a local statement** about a
property `P` of elements: if every element with `P` over the limit of any system comes from a stage
(`hcore`), and every point of `Z` has an étale neighbourhood `V ×_{V_i} N` on which `ξ` has `P`
(`hfactor`), then `ξ` comes from a stage. Points outside `Z` are handled by
`AlgebraicGeometry.Artin.ContractionSituation.exists_localLift_of_not_mem`, and the local lifts are
glued by `AlgebraicGeometry.Artin.ContractionSituation.exists_stage_of_localLift`. -/
theorem exists_stage_of_core (c : ContractionSituation B S hS)
    (P : (V : LocallyNoetherianOver B S hS) → Triple c V.obj → Prop)
    (hcore : ∀ (J : Type u) [Category.{u} J] [IsCofiltered J]
      (D' : J ⥤ LocallyNoetherianOver B S hS) (κ' : Cone D'),
      IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ') →
      (∀ j, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D'.obj j))) →
      IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ'.pt) →
      ∀ ξ' : Triple c κ'.pt.obj, P κ'.pt ξ' →
        ∃ (j : J) (y : Triple c (D'.obj j).obj), mapTriple c (κ'.π.app j).hom y = ξ')
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt)) (ξ : Triple c κ.pt.obj)
    (hfactor : ∀ v : (LocallyNoetherianOver.toScheme B S hS).obj κ.pt,
      (Space.schemePointsHomeomorph B S hS κ.pt.obj).symm v ∈ ξ.Z →
      ∃ (i : I) (N : BigFppfOver B S hS) (q : N ⟶ (D.obj i).obj)
        (hq : Etale ((BigFppfOver.toScheme B S hS).map q)),
        IsAffine ((BigFppfOver.toScheme B S hS).obj N) ∧
        v ∈ Set.range ((BigFppfOver.toScheme B S hS).map (pullback.fst (κ.π.app i).hom q)).base ∧
        P (baseChangeCone κ q hq).pt (mapTriple c (pullback.fst (κ.π.app i).hom q) ξ)) :
    ∃ (i : I) (y : Triple c (D.obj i).obj), mapTriple c (κ.π.app i).hom y = ξ := by
  refine exists_stage_of_localLift hκ hD hpt ξ fun v => ?_
  by_cases hv : (Space.schemePointsHomeomorph B S hS κ.pt.obj).symm v ∈ ξ.Z
  · obtain ⟨i, N, q, hq, hN, hvr, hP⟩ := hfactor v hv
    obtain ⟨h, y, hy⟩ := hcore (Over i) (baseChangeDiagram q hq) (baseChangeCone κ q hq)
      (isLimitBaseChangeCone q hq hκ) (isAffine_baseChangeDiagram_obj q hq hD hN)
      (isAffine_baseChangeCone_pt q hq hD hpt hN) _ hP
    obtain ⟨L, hL⟩ := exists_localLift_of_baseChange c hD q hq hN h y hy
    exact ⟨h.left, L, hL hvr⟩
  · exact exists_localLift_of_not_mem c hκ hD hpt ξ v hv

end Lift

/-- **Limit preservation of the contraction functor from a core and a local statement** (Stacks
0GI5, with the last part of the source's proof isolated in `hcore` and the reduction to an affine
`W` in `hfactor`). -/
theorem limitPreserving_contractionFunctor_of_core (c : ContractionSituation B S hS)
    (P : (V : LocallyNoetherianOver B S hS) → Triple c V.obj → Prop)
    (hcore : ∀ (J : Type u) [Category.{u} J] [IsCofiltered J]
      (D' : J ⥤ LocallyNoetherianOver B S hS) (κ' : Cone D'),
      IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ') →
      (∀ j, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D'.obj j))) →
      IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ'.pt) →
      ∀ ξ' : Triple c κ'.pt.obj, P κ'.pt ξ' →
        ∃ (j : J) (y : Triple c (D'.obj j).obj), mapTriple c (κ'.π.app j).hom y = ξ')
    (hfactor : ∀ (J : Type u) [Category.{u} J] [IsCofiltered J]
      (D : J ⥤ LocallyNoetherianOver B S hS) (κ : Cone D),
      IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ) →
      (∀ j, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj j))) →
      IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt) →
      ∀ (ξ : Triple c κ.pt.obj) (v : (LocallyNoetherianOver.toScheme B S hS).obj κ.pt),
      (Space.schemePointsHomeomorph B S hS κ.pt.obj).symm v ∈ ξ.Z →
      ∃ (i : J) (N : BigFppfOver B S hS) (q : N ⟶ (D.obj i).obj)
        (hq : Etale ((BigFppfOver.toScheme B S hS).map q)),
        IsAffine ((BigFppfOver.toScheme B S hS).obj N) ∧
        v ∈ Set.range ((BigFppfOver.toScheme B S hS).map (pullback.fst (κ.π.app i).hom q)).base ∧
        P (baseChangeCone κ q hq).pt (mapTriple c (pullback.fst (κ.π.app i).hom q) ξ)) :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (LocallyNoetherianOver.toScheme B S hS)
      (contractionFunctor c) :=
  limitPreserving_contractionFunctor_of_exists_stage c fun J _ _ D κ hκ hD hpt ξ =>
    exists_stage_of_core (κ := κ) c P hcore hκ hD hpt ξ (hfactor J D κ hκ hD hpt ξ)

end AlgebraicGeometry.Artin.ContractionSituation

end

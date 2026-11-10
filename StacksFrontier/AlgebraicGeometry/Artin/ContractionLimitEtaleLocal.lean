module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitInjectivity
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleSheafPropertyUnconditional
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleOverlap
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsBigFppfExistence

/-!
# Surjectivity in the limit preservation of Artin's contraction functor is étale local

In the situation of Stacks 0GH8 let `V = lim V_i` be a cofiltered limit of affine locally
Noetherian schemes over `S`. The proof of Stacks 0GI5 reduces the surjectivity of
`colim F(V_i) ⟶ F(V)` to an étale local question: an element `ξ ∈ F(V)` comes from a stage as
soon as every point of `V` has an étale neighbourhood `E ×_{V_i} V`, with `E ⟶ V_i` étale, on
which `ξ` comes from `F(E)`. The proof is the one sketched in the footnote of the source: the
finitely many neighbourhoods are moved to a common stage, they cover a later stage, the local
elements agree on the overlaps at a later stage by the injectivity, and they glue by the sheaf
property of Stacks 0GHG.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.existsUnique_mapTriple_eq_of_etale`: the sheaf
  property of `F` for any jointly surjective family of étale morphisms.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 0GHG](https://stacks.math.columbia.edu/tag/0GHG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The sheaf property of the contraction functor for a jointly surjective étale family**
(Stacks 0GHG), for any family, not only a chosen covering family of the site: such a family
generates the same sieve as a chosen one. -/
theorem existsUnique_mapTriple_eq_of_etale (c : ContractionSituation B S hS)
    {X : LocallyNoetherianOver B S hS} {α : Type u} (Y : α → LocallyNoetherianOver B S hS)
    (f : ∀ a, Y a ⟶ X) (het : ∀ a, Etale ((LocallyNoetherianOver.toScheme B S hS).map (f a)))
    (hsurj : ∀ x : (LocallyNoetherianOver.toScheme B S hS).obj X,
      ∃ a, x ∈ Set.range ((LocallyNoetherianOver.toScheme B S hS).map (f a)).base)
    (t : ∀ a, Triple c (Y a).obj)
    (ht : ∀ (a b : α) (Z : LocallyNoetherianOver B S hS) (ga : Z ⟶ Y a) (gb : Z ⟶ Y b),
      ga ≫ f a = gb ≫ f b → mapTriple c ga.hom (t a) = mapTriple c gb.hom (t b)) :
    ∃! s : Triple c X.obj, ∀ a, mapTriple c (f a).hom s = t a := by
  let E : PreZeroHypercover.{u + 1} X := ⟨ULift.{u + 1} α, fun a => Y a.down, fun a => f a.down⟩
  have hE : (E.map (LocallyNoetherianOver.toSchemes B S hS ⋙ B.inclusion)).presieve₀ ∈
      Scheme.etalePrecoverage
        (B.inclusion.obj ((LocallyNoetherianOver.toSchemes B S hS).obj X)) := by
    refine (Scheme.presieve₀_mem_precoverage_iff _).2 ⟨fun x => ?_, fun a => het a.down⟩
    obtain ⟨a, hx⟩ := hsurj x
    exact ⟨⟨a⟩, hx⟩
  obtain ⟨E', hE', hgen⟩ := LocallyNoetherianOver.exists_isEtaleCovering_generate_eq B S hS E hE
  have hsh : E'.presieve₀.IsSheafFor (contractionFunctor c) :=
    contractionFunctor_satisfiesEtaleSheafProperty B S hS c ⟨X, E'⟩ hE'
  have hsh' : E.presieve₀.IsSheafFor (contractionFunctor c) := by
    rw [Presieve.isSheafFor_iff_generate] at hsh ⊢
    rwa [hgen] at hsh
  have := (Presieve.isSheafFor_arrows_iff _ _).1 hsh' (fun a => t a.down)
    (fun a b Z ga gb h => ht a.down b.down Z ga gb h)
  obtain ⟨s, hs, hu⟩ := this
  exact ⟨s, fun a => hs ⟨a⟩, fun s' hs' => hu s' fun a => hs' a.down⟩

/-- The second projection of a fibre product along an étale morphism is étale. -/
theorem etale_pullback_snd {V Vi Vj : BigFppfOver B S hS} (f : Vi ⟶ V) (g : Vj ⟶ V)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f)) :
    Etale ((BigFppfOver.toScheme B S hS).map (pullback.snd f g)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback f g).map (BigFppfOver.toScheme B S hS)) hf

/-- A fibre product of affine objects over an affine object is affine. -/
theorem isAffine_pullback {V Vi Vj : BigFppfOver B S hS} (f : Vi ⟶ V) (g : Vj ⟶ V)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Vi)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Vj)] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback f g)) :=
  IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS) f g).hom

/-- A fibre product along an étale morphism, with locally Noetherian first factor, is locally
Noetherian (the first projection is a base change of the étale morphism). -/
theorem isLocallyNoetherian_pullback_of_etale_right {V Vi Vj : BigFppfOver B S hS} (f : Vi ⟶ V)
    (g : Vj ⟶ V) (hg : Etale ((BigFppfOver.toScheme B S hS).map g))
    (hi : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Vi)) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (pullback f g)) := by
  have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.snd f g))
      ((BigFppfOver.toScheme B S hS).map (pullback.fst f g))
      ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map f) :=
    ((IsPullback.of_hasPullback f g).map _).flip
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (pullback.fst f g)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian
    ((BigFppfOver.toScheme B S hS).map (pullback.fst f g))

/-- The first projection of a fibre product along an étale morphism is étale. -/
theorem etale_pullback_fst {V Vi Vj : BigFppfOver B S hS} (f : Vi ⟶ V) (g : Vj ⟶ V)
    (hg : Etale ((BigFppfOver.toScheme B S hS).map g)) :
    Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst f g)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback f g).map (BigFppfOver.toScheme B S hS)).flip hg

/-- A pair of points with the same image lifts to a point of the fibre product. -/
theorem exists_pullback_point {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : (BigFppfOver.toScheme B S hS).obj X) (y : (BigFppfOver.toScheme B S hS).obj Y)
    (h : ((BigFppfOver.toScheme B S hS).map f).base x =
      ((BigFppfOver.toScheme B S hS).map g).base y) :
    ∃ z, ((BigFppfOver.toScheme B S hS).map (pullback.fst f g)).base z = x ∧
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f g)).base z = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  refine ⟨((PreservesPullback.iso (BigFppfOver.toScheme B S hS) f g).inv).base z, ?_, ?_⟩
  · rw [← hz₁, ← PreservesPullback.iso_inv_fst (BigFppfOver.toScheme B S hS) f g]
    rfl
  · rw [← hz₂, ← PreservesPullback.iso_inv_snd (BigFppfOver.toScheme B S hS) f g]
    rfl

section Local

variable (c : ContractionSituation B S hS)
  {I : Type u} [Category.{u} I] {D : I ⥤ LocallyNoetherianOver B S hS} (κ : Cone D)

/-- **An étale local lift at a stage** of an element `ξ ∈ F(V)`, `V` the vertex of `κ`: an affine
`E` étale over the stage `V_i` and an element of `F(E)` whose restriction to `E ×_{V_i} V` is the
restriction of `ξ`. -/
structure LocalLift (ξ : Triple c κ.pt.obj) (i : I) where
  /-- The étale neighbourhood at the stage. -/
  E : LocallyNoetherianOver B S hS
  /-- Its structure morphism to the stage. -/
  e : E ⟶ D.obj i
  /-- The structure morphism is étale. -/
  etale : Etale ((BigFppfOver.toScheme B S hS).map e.hom)
  /-- The neighbourhood is affine. -/
  affine : IsAffine ((BigFppfOver.toScheme B S hS).obj E.obj)
  /-- The local element. -/
  y : Triple c E.obj
  /-- Its restriction to `E ×_{V_i} V` is the restriction of `ξ`. -/
  agree : mapTriple c (pullback.fst e.hom (κ.π.app i).hom) y =
    mapTriple c (pullback.snd e.hom (κ.π.app i).hom) ξ

variable {c κ}

/-- The base change of a local lift to a later stage. -/
noncomputable def LocalLift.baseChange {ξ : Triple c κ.pt.obj} {i j : I} (L : LocalLift c κ ξ i)
    (f : j ⟶ i) (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i))) :
    LocalLift c κ ξ j where
  E := LocallyNoetherianOver.overlap B S hS L.e (D.map f) L.etale
  e := LocallyNoetherianOver.overlapSnd B S hS L.e (D.map f) L.etale
  etale := etale_pullback_snd L.e.hom (D.map f).hom L.etale
  affine := by
    have := L.affine
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj) := hD i
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj) := hD j
    exact isAffine_pullback L.e.hom (D.map f).hom
  y := mapTriple c (pullback.fst L.e.hom (D.map f).hom) L.y
  agree := by
    have hw : (κ.π.app j).hom ≫ (D.map f).hom = (κ.π.app i).hom :=
      congrArg (fun k => k.hom) (κ.w f)
    let m : pullback (pullback.snd L.e.hom (D.map f).hom) (κ.π.app j).hom ⟶
        pullback L.e.hom (κ.π.app i).hom :=
      pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, hw])
    change mapTriple c (pullback.fst (pullback.snd L.e.hom (D.map f).hom) (κ.π.app j).hom)
      (mapTriple c (pullback.fst L.e.hom (D.map f).hom) L.y) = _
    have h1 : m ≫ pullback.fst L.e.hom (κ.π.app i).hom =
        pullback.fst (pullback.snd L.e.hom (D.map f).hom) (κ.π.app j).hom ≫
          pullback.fst L.e.hom (D.map f).hom := pullback.lift_fst _ _ _
    have h2 : m ≫ pullback.snd L.e.hom (κ.π.app i).hom =
        pullback.snd (pullback.snd L.e.hom (D.map f).hom) (κ.π.app j).hom :=
      pullback.lift_snd _ _ _
    rw [← mapTriple_comp, ← h1, mapTriple_comp, L.agree, ← mapTriple_comp, h2]
    rfl

/-- The base change of a local lift covers the same points of the limit. -/
theorem LocalLift.range_subset_baseChange {ξ : Triple c κ.pt.obj} {i j : I}
    (L : LocalLift c κ ξ i) (f : j ⟶ i)
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i))) :
    Set.range ((BigFppfOver.toScheme B S hS).map (pullback.snd L.e.hom (κ.π.app i).hom)).base ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (L.baseChange f hD).e.hom (κ.π.app j).hom)).base := by
  have hw : (κ.π.app j).hom ≫ (D.map f).hom = (κ.π.app i).hom :=
    congrArg (fun k => k.hom) (κ.w f)
  let m : pullback L.e.hom (κ.π.app i).hom ⟶
      pullback (pullback.snd L.e.hom (D.map f).hom) (κ.π.app j).hom :=
    pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ (κ.π.app j).hom) (by
      rw [Category.assoc, hw, pullback.condition])) (pullback.snd _ _) (pullback.lift_snd _ _ _)
  change _ ⊆ Set.range ((BigFppfOver.toScheme B S hS).map
    (pullback.snd (pullback.snd L.e.hom (D.map f).hom) (κ.π.app j).hom)).base
  rintro _ ⟨p, rfl⟩
  refine ⟨((BigFppfOver.toScheme B S hS).map m).base p, ?_⟩
  have e : (BigFppfOver.toScheme B S hS).map m ≫ (BigFppfOver.toScheme B S hS).map
      (pullback.snd (pullback.snd L.e.hom (D.map f).hom) (κ.π.app j).hom) =
      (BigFppfOver.toScheme B S hS).map (pullback.snd L.e.hom (κ.π.app i).hom) := by
    rw [← Functor.map_comp, pullback.lift_snd]
  rw [← e]
  rfl

section Overlap

variable [IsCofiltered I] (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
  (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
  (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt))

include hκ hD hpt in
/-- **Two local lifts at a stage agree on their overlap at a later stage**: both restrict to `ξ`
on the overlap over the limit, so the injectivity half of Stacks 0GI5, applied to the base change
of the system to the overlap, makes them agree at a later stage. -/
theorem LocalLift.exists_agree {ξ : Triple c κ.pt.obj} {k : I} (L₁ L₂ : LocalLift c κ ξ k) :
    ∃ (j : I) (g : j ⟶ k), ∀ (Y : LocallyNoetherianOver B S hS) (a₁ : Y ⟶ L₁.E) (a₂ : Y ⟶ L₂.E)
      (b : Y ⟶ D.obj j), a₁ ≫ L₁.e = b ≫ D.map g → a₂ ≫ L₂.e = b ≫ D.map g →
        mapTriple c a₁.hom L₁.y = mapTriple c a₂.hom L₂.y := by
  have := L₁.affine
  have := L₂.affine
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj k).obj) := hD k
  let O := pullback L₁.e.hom L₂.e.hom
  let n₀ : O ⟶ (D.obj k).obj := pullback.fst L₁.e.hom L₂.e.hom ≫ L₁.e.hom
  have hn₀ : Etale ((BigFppfOver.toScheme B S hS).map n₀) := by
    have := etale_pullback_fst L₁.e.hom L₂.e.hom L₂.etale
    have := L₁.etale
    rw [Functor.map_comp]
    infer_instance
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj O) := isAffine_pullback _ _
  let E := D ⋙ ObjectProperty.ι _
  let D' : Over k ⥤ LocallyNoetherianOver B S hS :=
    ObjectProperty.lift _ (overBaseChangeDiagram E k n₀) fun h =>
      isLocallyNoetherian_pullback_of_etale_right _ n₀ hn₀ (D.obj h.left).property
  let P : LocallyNoetherianOver B S hS :=
    ⟨pullback (κ.π.app k).hom n₀,
      isLocallyNoetherian_pullback_of_etale_right _ n₀ hn₀ κ.pt.property⟩
  let κ' : Cone D' :=
    { pt := P
      π :=
        { app := fun h => ObjectProperty.homMk
            ((overBaseChangeCone E ((ObjectProperty.ι _).mapCone κ) k n₀).π.app h)
          naturality := fun h h' φ => ObjectProperty.hom_ext _
            ((overBaseChangeCone E ((ObjectProperty.ι _).mapCone κ) k n₀).π.naturality φ) } }
  have hκ' : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ') :=
    isLimitMapOverBaseChangeCone E ((ObjectProperty.ι _).mapCone κ) k n₀
      (BigFppfOver.toScheme B S hS) hκ
  have hD' : ∀ h, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D'.obj h)) := fun h => by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj h.left).obj) := hD h.left
    exact isAffine_pullback (D.map h.hom).hom n₀
  have hpt' : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ'.pt) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj) := hpt
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (((Functor.const I).obj κ.pt).obj k).obj) := hpt
    exact isAffine_pullback (κ.π.app k).hom n₀
  let h₀ : Over k := Over.mk (𝟙 k)
  let s₀ : (D'.obj h₀).obj ⟶ O := pullback.snd (D.map (𝟙 k)).hom n₀
  let t₁ := mapTriple c (s₀ ≫ pullback.fst L₁.e.hom L₂.e.hom) L₁.y
  let t₂ := mapTriple c (s₀ ≫ pullback.snd L₁.e.hom L₂.e.hom) L₂.y
  -- both restrict to `ξ` over the limit
  have hsnd : (κ'.π.app h₀).hom ≫ s₀ = pullback.snd (κ.π.app k).hom n₀ := pullback.lift_snd _ _ _
  have hc₁ : (pullback.snd (κ.π.app k).hom n₀ ≫ pullback.fst L₁.e.hom L₂.e.hom) ≫ L₁.e.hom =
      pullback.fst (κ.π.app k).hom n₀ ≫ (κ.π.app k).hom := by
    rw [Category.assoc]
    exact pullback.condition.symm
  have hc₂ : (pullback.snd (κ.π.app k).hom n₀ ≫ pullback.snd L₁.e.hom L₂.e.hom) ≫ L₂.e.hom =
      pullback.fst (κ.π.app k).hom n₀ ≫ (κ.π.app k).hom := by
    rw [Category.assoc, ← pullback.condition]
    exact pullback.condition.symm
  have hcomp : ∀ {T : BigFppfOver B S hS} (r : T ⟶ (D'.obj h₀).obj),
      mapTriple c r t₁ = mapTriple c r t₂ ↔
        mapTriple c (r ≫ s₀ ≫ pullback.fst L₁.e.hom L₂.e.hom) L₁.y =
          mapTriple c (r ≫ s₀ ≫ pullback.snd L₁.e.hom L₂.e.hom) L₂.y := fun r => by
    simp only [t₁, t₂, mapTriple_comp]
  have hlim : mapTriple c (κ'.π.app h₀).hom t₁ = mapTriple c (κ'.π.app h₀).hom t₂ := by
    refine (hcomp _).2 ?_
    rw [← Category.assoc, ← Category.assoc, hsnd,
      ← pullback.lift_fst _ _ hc₁, ← pullback.lift_fst _ _ hc₂, mapTriple_comp, mapTriple_comp,
      L₁.agree, L₂.agree, ← mapTriple_comp, ← mapTriple_comp, pullback.lift_snd,
      pullback.lift_snd]
  obtain ⟨j', f, hf⟩ := exists_mapTriple_eq_of_isLimit c hκ' hD' hpt' h₀ t₁ t₂ hlim
  have hm : (D'.map f).hom ≫ s₀ = pullback.snd (D.map j'.hom).hom n₀ := pullback.lift_snd _ _ _
  have hf' := (hcomp _).1 hf
  rw [← Category.assoc, ← Category.assoc, hm] at hf'
  refine ⟨j'.left, j'.hom, fun Y a₁ a₂ b h₁ h₂ => ?_⟩
  have h₁' : a₁.hom ≫ L₁.e.hom = b.hom ≫ (D.map j'.hom).hom := congrArg (fun k => k.hom) h₁
  have h₂' : a₂.hom ≫ L₂.e.hom = b.hom ≫ (D.map j'.hom).hom := congrArg (fun k => k.hom) h₂
  have hab : a₁.hom ≫ L₁.e.hom = a₂.hom ≫ L₂.e.hom := h₁'.trans h₂'.symm
  have hcond : b.hom ≫ (D.map j'.hom).hom = pullback.lift a₁.hom a₂.hom hab ≫ n₀ := by
    rw [pullback.lift_fst_assoc]
    exact h₁'.symm
  let hY : Y.obj ⟶ pullback (D.map j'.hom).hom n₀ :=
    pullback.lift b.hom (pullback.lift a₁.hom a₂.hom hab) hcond
  calc mapTriple c a₁.hom L₁.y
      = mapTriple c (hY ≫ pullback.snd (D.map j'.hom).hom n₀ ≫
          pullback.fst L₁.e.hom L₂.e.hom) L₁.y := by
        rw [pullback.lift_snd_assoc, pullback.lift_fst]
    _ = mapTriple c hY (mapTriple c (pullback.snd (D.map j'.hom).hom n₀ ≫
          pullback.fst L₁.e.hom L₂.e.hom) L₁.y) := mapTriple_comp _ _ _ _
    _ = mapTriple c hY (mapTriple c (pullback.snd (D.map j'.hom).hom n₀ ≫
          pullback.snd L₁.e.hom L₂.e.hom) L₂.y) := by rw [hf']
    _ = mapTriple c a₂.hom L₂.y := by
        rw [← mapTriple_comp, pullback.lift_snd_assoc, pullback.lift_snd]

include hκ hD hpt in
/-- **Surjectivity in the limit preservation of the contraction functor is étale local** (the
first reduction in the surjectivity half of the proof of Stacks 0GI5): an element `ξ ∈ F(V)`, `V`
the limit, comes from a stage as soon as every point of `V` lies in the image of an étale
neighbourhood `E ×_{V_i} V` on which `ξ` comes from `F(E)`, for some stage `V_i` and some affine
`E` étale over it. -/
theorem exists_stage_of_localLift (ξ : Triple c κ.pt.obj)
    (H : ∀ v : (LocallyNoetherianOver.toScheme B S hS).obj κ.pt, ∃ (i : I)
      (L : LocalLift c κ ξ i), v ∈ Set.range ((BigFppfOver.toScheme B S hS).map
        (pullback.snd L.e.hom (κ.π.app i).hom)).base) :
    ∃ (i : I) (y : Triple c (D.obj i).obj), mapTriple c (κ.π.app i).hom y = ξ := by
  classical
  choose i₀ L₀ hL₀ using H
  have : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt) := hpt
  have hopen : ∀ v, IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (L₀ v).e.hom (κ.π.app (i₀ v)).hom)).base) := fun v => by
    have := etale_pullback_snd (L₀ v).e.hom (κ.π.app (i₀ v)).hom (L₀ v).etale
    exact ((BigFppfOver.toScheme B S hS).map _).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover _ fun v => (hopen v).mem_nhds (hL₀ v)
  -- a common stage
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (t.image i₀)
  have φ : ∀ v : t, k ⟶ i₀ v := fun v => (hk (Finset.mem_image_of_mem i₀ v.2)).some
  let L₁ : ∀ v : t, LocalLift c κ ξ k := fun v => (L₀ v).baseChange (φ v) hD
  have hcov₁ : ∀ x : (LocallyNoetherianOver.toScheme B S hS).obj κ.pt, ∃ v : t,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (L₁ v).e.hom (κ.π.app k).hom)).base := fun x => by
    have hx : x ∈ (⊤ : Set _) := Set.mem_univ x
    rw [← ht, Set.mem_iUnion₂] at hx
    obtain ⟨v, hv, hxv⟩ := hx
    exact ⟨⟨v, hv⟩, (L₀ v).range_subset_baseChange (φ ⟨v, hv⟩) hD hxv⟩
  -- the images of the neighbourhoods cover a later stage
  let X := D ⋙ LocallyNoetherianOver.toScheme B S hS
  have : ∀ i, IsAffine (X.obj i) := hD
  have : IsLocallyNoetherian (X.obj k) := (D.obj k).property
  have : IsNoetherian (X.obj k) := {}
  have hUo : IsOpen (⋃ v : t, Set.range ((BigFppfOver.toScheme B S hS).map (L₁ v).e.hom).base) :=
    isOpen_iUnion fun v => by
      have := (L₁ v).etale
      exact ((BigFppfOver.toScheme B S hS).map _).isOpenMap.isOpen_range
  let Uk : (X.obj k).Opens := ⟨_, hUo⟩
  have hpre : (LocallyNoetherianOver.toScheme B S hS).map (κ.π.app k) ⁻¹ᵁ Uk =
      (LocallyNoetherianOver.toScheme B S hS).map (κ.π.app k) ⁻¹ᵁ ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.map_top, TopologicalSpace.Opens.coe_top, Set.mem_univ,
      iff_true]
    obtain ⟨v, p, hp⟩ := hcov₁ x
    have e : (BigFppfOver.toScheme B S hS).map (pullback.fst (L₁ v).e.hom (κ.π.app k).hom) ≫
        (BigFppfOver.toScheme B S hS).map (L₁ v).e.hom =
        (BigFppfOver.toScheme B S hS).map (pullback.snd (L₁ v).e.hom (κ.π.app k).hom) ≫
          (BigFppfOver.toScheme B S hS).map (κ.π.app k).hom := by
      rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
    refine Set.mem_iUnion.2 ⟨v, ((BigFppfOver.toScheme B S hS).map
      (pullback.fst (L₁ v).e.hom (κ.π.app k).hom)).base p, ?_⟩
    rw [← hp]
    exact congrArg (fun φ => φ.base p) e
  obtain ⟨j₁, g₁, hg₁⟩ := exists_map_preimage_eq_map_preimage X
    ((LocallyNoetherianOver.toScheme B S hS).mapCone κ) hκ (i := k) (U := Uk) (V := ⊤)
    (TopologicalSpace.NoetherianSpace.isCompact _)
    (TopologicalSpace.NoetherianSpace.isCompact _) hpre
  -- the local elements agree on the overlaps at a later stage
  have hag := fun p : t × t => LocalLift.exists_agree hκ hD hpt (L₁ p.1) (L₁ p.2)
  choose ja ga hga using hag
  obtain ⟨Sv, hSv⟩ := IsCofiltered.inf_objs_exists
    (insert (Over.mk g₁) (Finset.univ.image fun p : t × t => Over.mk (ga p)))
  have m₁ : Sv ⟶ Over.mk g₁ := (hSv (Finset.mem_insert_self _ _)).some
  have mp : ∀ p : t × t, Sv ⟶ Over.mk (ga p) := fun p =>
    (hSv (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ p)))).some
  let j := Sv.left
  let g : j ⟶ k := Sv.hom
  let L₂ : ∀ v : t, LocalLift c κ ξ j := fun v => (L₁ v).baseChange g hD
  -- the base changes cover the stage `j`
  have hsurj : ∀ x : (LocallyNoetherianOver.toScheme B S hS).obj (D.obj j), ∃ v : t,
      x ∈ Set.range ((LocallyNoetherianOver.toScheme B S hS).map (L₂ v).e).base := fun x => by
    have hx : ((LocallyNoetherianOver.toScheme B S hS).map (D.map g)).base x ∈ Uk := by
      have hgm : g = m₁.left ≫ g₁ := (Over.w m₁).symm
      change x ∈ X.map g ⁻¹ᵁ Uk
      rw [hgm, Functor.map_comp, Scheme.Hom.comp_preimage, hg₁]
      simp
    obtain ⟨v, p, hp⟩ := Set.mem_iUnion.1 hx
    obtain ⟨z, -, hz⟩ := exists_pullback_point (L₁ v).e.hom (D.map g).hom p x hp
    exact ⟨v, z, hz⟩
  -- the local elements at the stage `j` are compatible
  have hcompat : ∀ (v w : t) (Y : LocallyNoetherianOver B S hS) (a : Y ⟶ (L₂ v).E)
      (b : Y ⟶ (L₂ w).E), a ≫ (L₂ v).e = b ≫ (L₂ w).e →
        mapTriple c a.hom (L₂ v).y = mapTriple c b.hom (L₂ w).y := by
    intro v w Y a b hvw
    let m := (mp (v, w)).left
    have hm : m ≫ ga (v, w) = g := Over.w (mp (v, w))
    refine (mapTriple_comp c a.hom _ (L₁ v).y).symm.trans (Eq.trans ?_
      (mapTriple_comp c b.hom _ (L₁ w).y))
    refine hga (v, w) Y
      (a ≫ LocallyNoetherianOver.overlapFst B S hS (L₁ v).e (D.map g) (L₁ v).etale)
      (b ≫ LocallyNoetherianOver.overlapFst B S hS (L₁ w).e (D.map g) (L₁ w).etale)
      (a ≫ (L₂ v).e ≫ D.map m) ?_ ?_
    · simp only [Category.assoc, ← Functor.map_comp, hm]
      exact congrArg (a ≫ ·)
        (LocallyNoetherianOver.overlapFst_comp_f B S hS (L₁ v).e (D.map g) (L₁ v).etale)
    · simp only [Category.assoc, ← Functor.map_comp, hm]
      rw [← Category.assoc, hvw, Category.assoc]
      exact congrArg (b ≫ ·)
        (LocallyNoetherianOver.overlapFst_comp_f B S hS (L₁ w).e (D.map g) (L₁ w).etale)
  obtain ⟨s, hs, -⟩ := existsUnique_mapTriple_eq_of_etale c (fun v : t => (L₂ v).E)
    (fun v => (L₂ v).e) (fun v => (L₂ v).etale) hsurj (fun v => (L₂ v).y) hcompat
  refine ⟨j, s, ?_⟩
  -- its restriction to the limit is `ξ`, by uniqueness of amalgamations over the limit
  let P : t → LocallyNoetherianOver B S hS := fun v =>
    LocallyNoetherianOver.overlap B S hS (L₂ v).e (κ.π.app j) (L₂ v).etale
  let q : ∀ v, P v ⟶ κ.pt := fun v =>
    LocallyNoetherianOver.overlapSnd B S hS (L₂ v).e (κ.π.app j) (L₂ v).etale
  have hqet : ∀ v, Etale ((LocallyNoetherianOver.toScheme B S hS).map (q v)) := fun v =>
    etale_pullback_snd _ _ (L₂ v).etale
  have hqsurj : ∀ x : (LocallyNoetherianOver.toScheme B S hS).obj κ.pt, ∃ v,
      x ∈ Set.range ((LocallyNoetherianOver.toScheme B S hS).map (q v)).base := fun x => by
    obtain ⟨v, hv⟩ := hcov₁ x
    exact ⟨v, (L₁ v).range_subset_baseChange g hD hv⟩
  obtain ⟨s', -, huniq⟩ := existsUnique_mapTriple_eq_of_etale c P q hqet hqsurj
    (fun v => mapTriple c (q v).hom ξ) (fun v w Y a b h => by
      have h' : a.hom ≫ (q v).hom = b.hom ≫ (q w).hom := congrArg (fun φ => φ.hom) h
      rw [← mapTriple_comp, ← mapTriple_comp, h'])
  have h1 : mapTriple c (κ.π.app j).hom s = s' := huniq _ fun v => by
    have hc : (q v).hom ≫ (κ.π.app j).hom =
        pullback.fst (L₂ v).e.hom (κ.π.app j).hom ≫ (L₂ v).e.hom := pullback.condition.symm
    refine (mapTriple_comp c (q v).hom (κ.π.app j).hom s).symm.trans ?_
    refine (congrArg (fun φ => mapTriple c φ s) hc).trans ?_
    refine (mapTriple_comp c _ _ s).trans ?_
    refine (congrArg (mapTriple c (pullback.fst (L₂ v).e.hom (κ.π.app j).hom)) (hs v)).trans ?_
    exact (L₂ v).agree
  exact h1.trans (huniq _ fun v => rfl).symm

end Overlap

end Local

end AlgebraicGeometry.Artin.ContractionSituation

end

module

public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Surjectivity descends to a finite stage

Let a scheme be the limit of a cofiltered diagram of schemes with affine transition morphisms. A
locally finitely presented morphism over one stage which becomes surjective after base change to
the limit is already surjective after base change to some later stage.

## Main results

* `AlgebraicGeometry.exists_surjective_baseChange_of_surjective_limitBaseChange` descends
  surjectivity from the inverse limit to a finite stage.

## Implementation notes

Schemes over the chosen stage and their base changes are represented by `CategoryTheory.Over` and
`CategoryTheory.Over.pullback`. A morphism `g : i ⟶ i₀` expresses that `i` is a stage later than
`i₀` in the cofiltered indexing category. This is the categorical form of the source's directed
indexing set.

The argument is by contradiction: if the morphism misses a point at every stage, then the
constructible complement of its image is covered by finitely many affine schemes mapping into the
target, and the inverse limit of the resulting diagram of nonempty quasi-compact schemes is
nonempty, producing a point of the limit outside the image — contradicting surjectivity there.

## References

* [Stacks Project, Tag 07RR](https://stacks.math.columbia.edu/tag/07RR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A point of a base change lies in the image of the base-changed morphism exactly when its
image in the original target lies in the image of the original morphism. -/
private lemma mem_range_overPullback_map {B : Scheme.{u}} (X Y : Over B) (f : X ⟶ Y)
    {T : Scheme.{u}} (g : T ⟶ B) (y : ((Over.pullback g).obj Y).left) :
    y ∈ Set.range (((Over.pullback g).map f).left.base) ↔
      (pullback.fst Y.hom g).base y ∈ Set.range f.left.base := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(pullback.fst X.hom g).base x, ?_⟩
    have h := congrArg (fun q => q.base x) (overPullback_map_left_fst g f)
    simpa [Scheme.Hom.comp_base, TopCat.coe_comp] using h.symm
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
    let q := pullback.fst Y.hom g
    have hq : q ≫ Y.hom = pullback.snd Y.hom g ≫ g := pullback.condition
    let φ : pullback f.left q ⟶ ((Over.pullback g).obj X).left :=
      pullback.lift (pullback.fst f.left q)
        (pullback.snd f.left q ≫ pullback.snd Y.hom g) (by
          calc
            pullback.fst f.left q ≫ X.hom =
                pullback.fst f.left q ≫ f.left ≫ Y.hom := by rw [← f.w]
            _ = pullback.snd f.left q ≫ q ≫ Y.hom := pullback.condition_assoc Y.hom
            _ = pullback.snd f.left q ≫ pullback.snd Y.hom g ≫ g := by
              simpa [Category.assoc] using congrArg (fun h => pullback.snd f.left q ≫ h) hq)
    have hφfst : φ ≫ pullback.fst X.hom g = pullback.fst f.left q := pullback.lift_fst _ _ _
    have hφsnd : φ ≫ pullback.snd X.hom g =
        pullback.snd f.left q ≫ pullback.snd Y.hom g := pullback.lift_snd _ _ _
    have hmap : φ ≫ ((Over.pullback g).map f).left = pullback.snd f.left q := by
      apply pullback.hom_ext
      · rw [Category.assoc, overPullback_map_left_fst]
        calc
          φ ≫ pullback.fst X.hom g ≫ f.left = (φ ≫ pullback.fst X.hom g) ≫ f.left := rfl
          _ = pullback.fst f.left q ≫ f.left := by rw [hφfst]
          _ = pullback.snd f.left q ≫ q := pullback.condition
          _ = pullback.snd f.left q ≫ pullback.fst Y.hom g := rfl
      · rw [Category.assoc, overPullback_map_left_snd, hφsnd]
    refine ⟨φ.base z, ?_⟩
    show (φ ≫ ((Over.pullback g).map f).left).base z = y
    rw [hmap]
    exact hz₂

/-- **Stacks Project, Tag 07RR.** If a locally finitely presented morphism over a stage of a
cofiltered inverse system becomes surjective over the inverse limit, then it is surjective at
some later stage. -/
@[stacks 07RR]
theorem exists_surjective_baseChange_of_surjective_limitBaseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (S : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    (c : Cone S) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (S.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (S.obj i₀)] [QuasiSeparatedSpace (S.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    [Surjective ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀),
      Surjective ((Over.pullback (S.map g)).map f₀).left := by
  classical
  let E : Set Y₀.left := Set.range f₀.left.base
  have hEcompl : Topology.IsLocallyConstructible Eᶜ :=
    (show Topology.IsLocallyConstructible E by
      simpa [E] using f₀.left.isLocallyConstructible_image Topology.IsLocallyConstructible.univ
      ).isConstructible.compl.isLocallyConstructible
  let 𝒰 := (Y₀.left.affineCover).finiteSubcover
  have hU : ∀ k : 𝒰.I₀, ∃ (T : Scheme.{u}) (_ : IsAffine T) (_ : CompactSpace T)
      (t : T ⟶ Y₀.left), Set.range t.base = (Eᶜ ∩ Set.range (𝒰.f k).base) := by
    intro k
    let V := 𝒰.f k
    have hconstructible : Topology.IsConstructible (V.base ⁻¹' Eᶜ) := by
      have hlocal : Topology.IsLocallyConstructible (V.base ⁻¹' Eᶜ) :=
        hEcompl.preimage_of_isOpenEmbedding V.isOpenEmbedding
      exact hlocal.isConstructible
    obtain ⟨T, hTA, hTC, t, ht⟩ := exists_affine_scheme_with_range hconstructible
    refine ⟨T, hTA, hTC, t ≫ V, ?_⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ht]
    rw [Set.image_preimage_eq_inter_range]
  choose T hTAffine hT t ht using hU
  by_contra hns
  push Not at hns
  let J := Over i₀
  let G : J ⥤ Over Y₀.left := Over.post S ⋙ Over.pullback Y₀.hom
  let F (k : 𝒰.I₀) : J ⥤ Scheme := G ⋙ Over.pullback (t k) ⋙ Over.forget (T k)
  let Ylim := (Over.pullback (c.π.app i₀)).obj Y₀
  have hlimE : ∀ y : Ylim.left, (pullback.fst Y₀.hom (c.π.app i₀)).base y ∈ E := by
    intro y
    exact (mem_range_overPullback_map X₀ Y₀ f₀ (c.π.app i₀) y).1
      (((Over.pullback (c.π.app i₀)).map f₀).left.surjective y)
  have hpairE : ∀ p : c.pt, ∀ y : Y₀.left,
      (c.π.app i₀).base p = Y₀.hom.base y → y ∈ E := by
    intro p y hp
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback p y hp
    let e := pullbackSymmetry (c.π.app i₀) Y₀.hom
    have hcoord : (pullback.fst Y₀.hom (c.π.app i₀)).base (e.hom.base z) = y := by
      calc
        _ = (e.hom ≫ pullback.fst Y₀.hom (c.π.app i₀)).base z :=
          (Scheme.Hom.comp_apply _ _ _).symm
        _ = (pullback.snd (c.π.app i₀) Y₀.hom).base z := by rw [pullbackSymmetry_hom_comp_fst]
        _ = y := hz₂
    exact hcoord ▸ hlimE (e.hom.base z)
  have hstage : ∀ j : J, ∃ k : 𝒰.I₀, Nonempty ((F k).obj j) := by
    intro j
    obtain ⟨y, hy⟩ : ∃ y : ((Over.pullback (S.map j.hom)).obj Y₀).left,
        y ∉ Set.range (((Over.pullback (S.map j.hom)).map f₀).left.base) := by
      have hnot : ¬ Function.Surjective (((Over.pullback (S.map j.hom)).map f₀).left.base) := by
        intro hs
        exact hns j.left j.hom ⟨hs⟩
      by_contra h
      apply hnot
      intro y
      by_contra hy
      exact h ⟨y, hy⟩
    have hyE : (pullback.fst Y₀.hom (S.map j.hom)).base y ∉ E := by
      intro hyE
      exact hy ((mem_range_overPullback_map X₀ Y₀ f₀ (S.map j.hom) y).2 hyE)
    have hcover : (pullback.fst Y₀.hom (S.map j.hom)).base y ∈
        ⋃ k, Set.range (𝒰.f k).base := by
      rw [𝒰.iUnion_range]
      exact Set.mem_univ _
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hcover
    obtain ⟨z, hz⟩ := hk
    have hyT : (pullback.fst Y₀.hom (S.map j.hom)).base y ∈ Set.range (t k).base := by
      rw [ht k]
      exact ⟨hyE, ⟨z, hz⟩⟩
    obtain ⟨w, hw⟩ := hyT
    let e := pullbackSymmetry Y₀.hom (S.map j.hom)
    let zG := e.hom.base y
    have hzG : (pullback.snd (S.map j.hom) Y₀.hom).base zG =
        (pullback.fst Y₀.hom (S.map j.hom)).base y := by
      calc
        _ = (e.hom ≫ pullback.snd (S.map j.hom) Y₀.hom).base y :=
          (Scheme.Hom.comp_apply _ _ _).symm
        _ = (pullback.fst Y₀.hom (S.map j.hom)).base y := by rw [pullbackSymmetry_hom_comp_snd]
    have hpair : Nonempty ((F k).obj j) := by
      show Nonempty (pullback (C := Scheme) (pullback.snd (S.map j.hom) Y₀.hom) (t k))
      obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback zG w (hzG.trans hw.symm)
      exact ⟨p⟩
    exact ⟨k, hpair⟩
  have hgood : ∃ k : 𝒰.I₀, ∀ j : J, Nonempty ((F k).obj j) := by
    by_contra h
    have hempty : ∀ k : 𝒰.I₀, ∃ j : J, IsEmpty ((F k).obj j) := by
      intro k
      by_contra hk
      have hall : ∀ j : J, Nonempty ((F k).obj j) := by
        intro j
        by_contra hne
        exact hk ⟨j, not_nonempty_iff.mp hne⟩
      exact h ⟨k, hall⟩
    choose jₖ hjₖ using hempty
    let objs : Finset J := Finset.univ.image jₖ
    obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists objs
    obtain ⟨k, hp⟩ := hstage j
    have hmap : Nonempty ((F k).obj (jₖ k)) := by
      obtain ⟨a⟩ := hj (Finset.mem_image_of_mem jₖ (Finset.mem_univ k))
      exact Nonempty.map ((F k).map a) hp
    exact (hjₖ k).false (Classical.choice hmap)
  obtain ⟨k₀, hgood₀⟩ := hgood
  let cOver := (Over.conePost S i₀).obj c
  let cG := (Over.pullback Y₀.hom).mapCone cOver
  let cF := (Over.forget (T k₀)).mapCone ((Over.pullback (t k₀)).mapCone cG)
  have hcF : IsLimit cF := isLimitOfPreserves _ (isLimitOfPreserves _
    (isLimitOfPreserves (Over.pullback Y₀.hom) (Over.isLimitConePost i₀ hc)))
  let F₀ := F k₀
  have : ∀ {j j' : J} (a : j ⟶ j'), IsAffineHom (F₀.map a) := by
    intro j j' a
    have : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) Y₀.hom :=
      ⟨fun pb hf => isAffineHom_isStableUnderBaseChange.of_isPullback pb hf⟩
    have : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) (t k₀) :=
      ⟨fun pb hf => isAffineHom_isStableUnderBaseChange.of_isPullback pb hf⟩
    have h₀ : IsAffineHom (((Over.post S).map a).left) := by
      show IsAffineHom (S.map a.left)
      infer_instance
    have h₁ : IsAffineHom ((Over.pullback Y₀.hom).map ((Over.post S).map a)).left :=
      MorphismProperty.overPullbackMap (P := @IsAffineHom) Y₀.hom _ h₀
    have h₂ : IsAffineHom
        ((Over.pullback (t k₀)).map ((Over.pullback Y₀.hom).map ((Over.post S).map a))).left :=
      MorphismProperty.overPullbackMap (P := @IsAffineHom) (t k₀) _ h₁
    simpa [F₀, F, G] using h₂
  have : ∀ j : J, CompactSpace (F₀.obj j) := by
    intro j
    have : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) Y₀.hom :=
      ⟨fun pb hf => isAffineHom_isStableUnderBaseChange.of_isPullback pb hf⟩
    have : CompactSpace (T k₀) := hT k₀
    have : IsAffineHom ((Over.post S).obj j).hom := by
      show IsAffineHom (S.map j.hom)
      infer_instance
    have : IsAffineHom (G.obj j).hom := by
      dsimp [G]
      exact MorphismProperty.pullback_snd _ _ inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ (t k₀))
  have : ∀ j : J, Nonempty (F₀.obj j) := hgood₀
  obtain ⟨p⟩ := Scheme.nonempty_of_isLimit F₀ cF hcF
  let ybase := (cG.pt.hom).base ((pullback.fst cG.pt.hom (t k₀)).base p)
  let tbase := (t k₀).base ((pullback.snd cG.pt.hom (t k₀)).base p)
  have htbase : tbase ∉ E := by
    have hpT : ((t k₀).base ((pullback.snd cG.pt.hom (t k₀)).base p)) ∈
        Set.range (t k₀).base := ⟨_, rfl⟩
    rw [ht k₀] at hpT
    exact hpT.1
  let zG := (pullback.fst cG.pt.hom (t k₀)).base p
  have hpair : (cG.pt.hom).base zG =
      (t k₀).base ((pullback.snd cG.pt.hom (t k₀)).base p) := by
    have hcond : pullback.fst cG.pt.hom (t k₀) ≫ cG.pt.hom =
        pullback.snd cG.pt.hom (t k₀) ≫ t k₀ := pullback.condition
    have h := congrArg (fun q => q.base p) hcond
    simpa [Scheme.Hom.comp_base, TopCat.coe_comp] using h
  have hpair' : ybase = tbase := by
    simpa [ybase, tbase, zG] using hpair
  have hybase : ybase ∈ E := by
    let pLim := (pullback.fst cOver.pt.hom Y₀.hom).base zG
    let y₀ := cG.pt.hom.base zG
    have hlim : (c.π.app i₀).base pLim = Y₀.hom.base y₀ := by
      show cOver.pt.hom ((pullback.fst cOver.pt.hom Y₀.hom).base zG) =
        Y₀.hom ((pullback.snd cOver.pt.hom Y₀.hom).base zG)
      have h := congrArg (fun q => q zG)
        (pullback.condition : pullback.fst cOver.pt.hom Y₀.hom ≫ cOver.pt.hom =
          pullback.snd cOver.pt.hom Y₀.hom ≫ Y₀.hom)
      simpa only [Scheme.Hom.comp_apply] using h
    exact hpairE pLim y₀ hlim
  exact htbase (hpair'.symm ▸ hybase)

end AlgebraicGeometry

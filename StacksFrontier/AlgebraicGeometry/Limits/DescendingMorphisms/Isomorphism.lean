module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion

/-!
# Isomorphisms descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of schemes with affine transition morphisms. A
morphism between quasi-compact and quasi-separated schemes over one stage, locally of finite
presentation there, is an isomorphism after base change to the limit only if it is already an
isomorphism after base change to some later stage.

## Main results

* `AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange` descends an isomorphism
  from the limit to a stage of the diagram.

## Implementation notes

The indexing category for descent is essentially small relative to the scheme universe,
expressing the set-sized inverse systems in the source. A morphism `g : i ⟶ i₀` expresses that
`i` is a stage later than `i₀`; applying `CategoryTheory.Over.pullback` to `S.map g` gives the
source's `fᵢ`. The cone leg at `i₀` similarly gives the limiting morphism `f`. The index objects,
index morphisms, and schemes have independent universes.

After descending the closed immersion using Tag 01ZP, the proof applies Tag 01ZM to descend its
inverse as a section over the target. A monomorphism with a section is an isomorphism.

## References

* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Base change of an isomorphism to a later stage, expressed through the direct base change
rather than the iterated one. -/
private lemma isIso_overPullback_map_of_isLimit {I : Type v} [Category.{w} I] [IsCofiltered I]
    (S : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    (c : Cone S) (i₀ i : I) (h : i ⟶ i₀) {X₀ Y₀ : Over (S.obj i₀)} (f₀ : X₀ ⟶ Y₀)
    [IsIso ((Over.pullback (c.π.app i₀)).map f₀).left] :
    IsIso ((Over.pullback (c.π.app i)).map ((Over.pullback (S.map h)).map f₀)).left := by
  have h1 : MorphismProperty.isomorphisms Scheme.{u}
      ((Over.pullback (c.π.app i ≫ S.map h)).map f₀).left := by
    rw [c.w h]
    exact inferInstance
  exact (overPullback_map_comp_iff (MorphismProperty.isomorphisms Scheme.{u}) (S.map h)
    (c.π.app i) f₀).1 h1

/-- A monomorphism of finite presentation over a stage which becomes an isomorphism over the limit
acquires a section, hence becomes an isomorphism, at some later stage. -/
private lemma exists_isIso_structural_baseChange {I : Type v} [Category.{w} I] [IsCofiltered I]
    [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) (hX : FinitePresentation X.hom)
    [Mono X.hom] [IsIso ((Over.pullback (c.π.app i)).obj X).hom] :
    ∃ (j : I) (e : j ⟶ i), IsIso ((Over.pullback (D.map e)).obj X).hom := by
  let Y : Over (D.obj i) := Over.mk (𝟙 _)
  let F := Over.pullback (c.π.app i)
  let a : F.obj Y ⟶ F.obj X := Over.homMk ((F.obj Y).hom ≫ inv (F.obj X).hom) (by simp)
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ :=
    exists_morphism_after_baseChange D c hc i Y X
      (by dsimp [Y]; exact ⟨inferInstance, inferInstance, inferInstance⟩) hX a
  let G := Over.pullback (D.map e)
  have : IsIso (G.obj Y).hom := by dsimp [G, Y]; infer_instance
  have : Mono (G.obj X).hom := by dsimp [G]; infer_instance
  have : IsSplitEpi (G.obj X).hom := IsSplitEpi.mk'
    { section_ := inv (G.obj Y).hom ≫ g.left
      id := by rw [Category.assoc, Over.w g]; exact IsIso.inv_hom_id (G.obj Y).hom }
  exact ⟨j, e, isIso_of_mono_of_isSplitEpi _⟩

/-- Base change of a structure morphism along a composite is the iterated base change. -/
private lemma isIso_structural_pullback_comp_iff {B C S : Scheme.{u}} (q : B ⟶ C) (p : C ⟶ S)
    (X : Over S) :
    IsIso ((Over.pullback (q ≫ p)).obj X).hom ↔
      IsIso ((Over.pullback q).obj ((Over.pullback p).obj X)).hom := by
  let e := (Over.pullbackComp q p).app X
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  rw [← e.hom.w]
  exact isIso_comp_left_iff _ _

/-- Swapping the factors of the inner pullback does not change whether the outer second
projection is an isomorphism. -/
private lemma isIso_pullback_snd_symmetry_iff {X Y S B : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ S)
    (q : B ⟶ S) :
    IsIso (pullback.snd f (pullback.snd q p)) ↔ IsIso (pullback.snd f (pullback.fst p q)) := by
  let e := pullbackSymmetry q p
  have h : e.hom ≫ pullback.fst p q = pullback.snd q p := by simp [e]
  rw [← h]
  show IsIso ((Over.pullback (e.hom ≫ pullback.fst p q)).obj (Over.mk f)).hom ↔ _
  rw [isIso_structural_pullback_comp_iff]
  show IsIso (pullback.snd (pullback.snd f (pullback.fst p q)) e.hom) ↔ _
  have cond := pullback.condition (f := pullback.snd f (pullback.fst p q)) (g := e.hom)
  rw [← isIso_comp_right_iff _ e.hom, ← cond, isIso_comp_left_iff]

/-- The base change of a morphism over `S` is an isomorphism exactly when the base change of its
source along the first projection is. -/
private lemma isIso_overPullback_map_iff {S B : Scheme.{u}} (q : B ⟶ S) (X Y : Over S)
    (f : X ⟶ Y) :
    IsIso ((Over.pullback q).map f).left ↔ IsIso (pullback.snd f.left (pullback.fst Y.hom q)) := by
  have sq : IsPullback (pullback.fst X.hom q) ((Over.pullback q).map f).left f.left
      (pullback.fst Y.hom q) := overPullback_isPullback q X Y f
  rw [← sq.isoPullback_hom_snd]
  exact isIso_comp_left_iff _ _

/-- The closed-immersion case: a closed immersion of finite presentation over a stage which
becomes an isomorphism over the limit is an isomorphism at some later stage. -/
private lemma exists_isIso_baseChange_of_isClosedImmersion {I : Type v} [Category.{w} I]
    [IsCofiltered I] [EssentiallySmall.{u} I] (S : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    (c : Cone S) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (S.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (S.obj i₀)] [QuasiSeparatedSpace (S.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    [IsIso ((Over.pullback (c.π.app i₀)).map f₀).left]
    (hclosed : IsClosedImmersion f₀.left) :
    ∃ (i : I) (g : i ⟶ i₀), IsIso ((Over.pullback (S.map g)).map f₀).left := by
  have := hclosed
  let V := Over.post S ⋙ Over.pullback Y₀.hom
  let H := Over.pullback Y₀.hom ⋙ Over.forget _
  let D := V ⋙ Over.forget _
  let cD := H.mapCone ((Over.conePost S i₀).obj c)
  have hcD : IsLimit cD := isLimitOfPreserves H (Over.isLimitConePost i₀ hc)
  let idI : Over i₀ := Over.mk (𝟙 i₀)
  let p : D.obj idI ⟶ Y₀.left := (V.obj idI).hom
  let X : Over (D.obj idI) := (Over.pullback p).obj (Over.mk f₀.left)
  have hp (k : Over i₀) (g : k ⟶ idI) : D.map g ≫ p = (V.obj k).hom := (V.map g).w
  have hlim : cD.π.app idI ≫ p = pullback.snd (c.π.app i₀) Y₀.hom := by
    simp [cD, H, idI, p, V, Functor.mapCone_π_app, Over.conePost, pullback.lift_snd]
  have {j k : Over i₀} (g : j ⟶ k) : IsAffineHom (D.map g) :=
    isAffineHom_baseChangeDiagram_map S i₀ Y₀ g
  have (k : Over i₀) : IsAffineHom (V.obj k).hom :=
    isAffineHom_baseChangeDiagram_snd S i₀ Y₀ k
  have (k : Over i₀) : CompactSpace (D.obj k) := compactSpace_baseChangeDiagram_obj S i₀ Y₀ k
  have (k : Over i₀) : QuasiSeparatedSpace (D.obj k) :=
    quasiSeparatedSpace_baseChangeDiagram_obj S i₀ Y₀ k
  have : LocallyOfFinitePresentation X.hom := by dsimp [X]; infer_instance
  have : IsClosedImmersion X.hom := by dsimp [X]; infer_instance
  have : IsIso ((Over.pullback (cD.π.app idI)).obj X).hom := by
    apply (isIso_structural_pullback_comp_iff (cD.π.app idI) p (Over.mk f₀.left)).mp
    rw [hlim]
    show IsIso (pullback.snd f₀.left (pullback.snd (c.π.app i₀) Y₀.hom))
    exact (isIso_pullback_snd_symmetry_iff f₀.left Y₀.hom (c.π.app i₀)).mpr
      ((isIso_overPullback_map_iff (c.π.app i₀) X₀ Y₀ f₀).mp inferInstance)
  obtain ⟨k, g, hk⟩ := exists_isIso_structural_baseChange D cD hcD idI X
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hdirect := (isIso_structural_pullback_comp_iff (D.map g) p (Over.mk f₀.left)).mpr hk
  rw [hp] at hdirect
  change IsIso (pullback.snd f₀.left (pullback.snd (S.map k.hom) Y₀.hom)) at hdirect
  exact ⟨k.left, k.hom, (isIso_overPullback_map_iff (S.map k.hom) X₀ Y₀ f₀).mpr
    ((isIso_pullback_snd_symmetry_iff f₀.left Y₀.hom (S.map k.hom)).mp hdirect)⟩

/-- A scheme affine over a quasi-compact quasi-separated scheme is quasi-compact and
quasi-separated. -/
private lemma compactSpace_and_quasiSeparatedSpace_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    CompactSpace X ∧ QuasiSeparatedSpace X :=
  have : IsSeparated f := IsSeparated.of_isAffineHom f
  ⟨QuasiCompact.compactSpace_of_compactSpace f, quasiSeparatedSpace_of_quasiSeparated f⟩

/-- If the base change of a finitely presented morphism to the inverse limit is an isomorphism,
then its base change to some stage is already an isomorphism. -/
@[stacks 081E]
lemma exists_isIso_baseChange_of_isIso_limitBaseChange
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (S : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    (c : Cone S) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (S.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (S.obj i₀)] [QuasiSeparatedSpace (S.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    [IsIso ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀), IsIso ((Over.pullback (S.map g)).map f₀).left := by
  have : IsClosedImmersion ((Over.pullback (c.π.app i₀)).map f₀).left := inferInstance
  obtain ⟨i, hi, hci⟩ := exists_isClosedImmersion_baseChange_of_isLimit S c hc i₀ X₀ Y₀ f₀
  let Xᵢ : Over (S.obj i) := (Over.pullback (S.map hi)).obj X₀
  let Yᵢ : Over (S.obj i) := (Over.pullback (S.map hi)).obj Y₀
  let fᵢ : Xᵢ ⟶ Yᵢ := (Over.pullback (S.map hi)).map f₀
  have : IsIso ((Over.pullback (c.π.app i)).map fᵢ).left :=
    isIso_overPullback_map_of_isLimit S c i₀ i hi f₀
  have : LocallyOfFinitePresentation fᵢ.left := by
    dsimp [fᵢ]
    exact MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) (S.map hi) f₀
      inferInstance
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_isAffineHom (S.map hi)
  have hbc (Z : Over (S.obj i₀)) [CompactSpace Z.left] [QuasiSeparatedSpace Z.left] :
      CompactSpace ((Over.pullback (S.map hi)).obj Z).left ∧
        QuasiSeparatedSpace ((Over.pullback (S.map hi)).obj Z).left :=
    have : IsAffineHom (pullback.fst Z.hom (S.map hi)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback Z.hom (S.map hi)).flip inferInstance
    compactSpace_and_quasiSeparatedSpace_of_isAffineHom (pullback.fst Z.hom (S.map hi))
  obtain ⟨_, _⟩ := hbc X₀
  obtain ⟨_, _⟩ := hbc Y₀
  obtain ⟨k, g, hIso⟩ :=
    exists_isIso_baseChange_of_isClosedImmersion S c hc i Xᵢ Yᵢ fᵢ hci
  refine ⟨k, g ≫ hi, ?_⟩
  rw [S.map_comp]
  exact (overPullback_map_comp_iff (MorphismProperty.isomorphisms Scheme.{u}) (S.map hi)
    (S.map g) f₀).2 hIso

end AlgebraicGeometry

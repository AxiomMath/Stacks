module

public import Mathlib.Algebra.Free
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Tactic.CategoryTheory.CategoryStar
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic

/-!
# Descent of morphisms along a limit with scheme-theoretically dominant projections

`Mathlib.AlgebraicGeometry.AffineTransitionLimit` develops inverse limits of schemes with affine
transition morphisms for an index category at the *same* universe as the schemes, and
`StacksDraft.AlgebraicGeometry.F3.LimitUniverse.AffineTransitionLimit` frees the index universe at
the cost of `CategoryTheory.InitiallySmall.{u}` on the index.  That cofinality hypothesis cannot
be dropped in general: `Ordinal.{u}` is a directed preorder no `u`-small subset of which is
cofinal, and over it there is a system of nonempty affine schemes with affine transitions whose
limit is the empty scheme (`StacksDraft.AlgebraicGeometry.F3b.SmallnessNecessary`).

It *can* be dropped when the projections out of the limit are scheme-theoretically dominant.  On
an affine open of the base every stage then injects into the limit, so the colimit of rings is the
union of the images of the stages and a `u`-small family of stages already exhausts it; the cone
therefore stays a limit cone after restriction to a `u`-small subsystem, and the results of
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` apply to that subsystem.  Note that the
subsystem is **not** claimed to be cofinal, so every statement below is arranged to need only
stages that the subsystem reaches.

## Main results

* `AlgebraicGeometry.isLimit_of_isLimit_overPullback`: a cone over a cofiltered diagram of
  schemes over a base is a limit cone as soon as its base change along every member of an open
  cover of the base is.
* `AlgebraicGeometry.isLimit_of_isLimit_globalSections`: a cone over a diagram of affine schemes
  with affine vertex is a limit cone as soon as global sections take it to a colimit cocone of
  rings.
* `AlgebraicGeometry.exists_small_directed_factor`: a `u`-small family of elements of a directed
  preorder factors through a `u`-small directed preorder mapping monotonically to it.
* `AlgebraicGeometry.exists_eq_ι_app_of_isColimit`: every element of a filtered colimit of
  commutative rings comes from one of the stages.
* `AlgebraicGeometry.exists_small_isLimit_whisker_of_isSchemeTheoreticallyDominant`: an inverse
  limit of schemes affine and scheme-theoretically dominant over a base stays a limit after
  restriction to a `u`-small subsystem, with no hypothesis relating the index universe to the
  scheme universe.
* `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant` and
  `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant`: the
  two halves of Stacks Tag 01ZC at a free index universe, with dominance of the projections in
  place of a cofinality hypothesis.
* `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant_slice`
  and
  `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant_slice`:
  the same two statements for a system indexed by a slice of the opposite preorder, which is the
  shape in which the systems of Tag 0CNQ arise.

## Implementation notes

The reduction to a `u`-small index produces a subsystem indexed by a `u`-small directed preorder
`J` together with a monotone map `J →o I`, and nothing more; in particular there is no map from a
given stage of `I` into the subsystem.  The injectivity half is therefore stated for stages
`i, j` fixed in advance, and the reduction is run over the tail above an upper bound of them, so
that the subsystem maps to both.

## References

* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Over

/-- A slice of a thin category is thin. -/
instance isThin {C : Type*} [Category C] [Quiver.IsThin C] (X : C) :
    Quiver.IsThin (Over X) :=
  fun _ _ ↦ ⟨fun _ _ ↦ by ext; exact Subsingleton.elim _ _⟩

/-- In a thin cofiltered category, restriction of slices along `g : X ⟶ Y` is initial. -/
instance initial_map {C : Type*} [Category C] [Quiver.IsThin C] [IsCofiltered C] {X Y : C}
    (g : X ⟶ Y) : (Over.map g).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d ↦ ?_) (fun {_ c} s s' ↦ ?_)
  · exact ⟨Over.mk (IsCofiltered.minToLeft X d.left),
      ⟨Over.homMk (IsCofiltered.minToRight X d.left) (Subsingleton.elim _ _)⟩⟩
  · exact ⟨c, 𝟙 _, by rw [Subsingleton.elim s s']⟩

end CategoryTheory.Over

namespace AlgebraicGeometry

/-! ### Limits of schemes affine over a base -/

section AffineOverBase

/-- Base change along `g` of a morphism of `Over S` is a pullback square of the underlying
morphisms. -/
lemma overPullback_map_isPullback {S T : Scheme.{u}} (g : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom g) ((Over.pullback g).map f).left
      f.left (pullback.fst Y.hom g) := by
  apply IsPullback.flip
  apply IsPullback.of_right _ _ (IsPullback.of_hasPullback Y.hom g).flip
  · simpa only [Over.pullback_map_left, pullback.lift_snd, f.w] using
      (IsPullback.of_hasPullback X.hom g).flip
  · exact pullback.lift_fst _ _ _

/-- The base changes along an open cover of the base jointly reflect isomorphisms of schemes over
the base. -/
lemma jointlyReflectIsomorphisms_overPullback {S : Scheme.{u}} (U : S.OpenCover) :
    JointlyReflectIsomorphisms (fun i => Over.pullback (U.f i)) := by
  constructor
  intro X Y f hf
  have : IsIso f.left := by
    apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
      (U.pullback₁ Y.hom)
    intro i
    have _ : IsIso ((Over.pullback (U.f i)).map f) := hf i
    have : IsIso ((Over.pullback (U.f i)).map f).left :=
      (Over.forget (U.X i)).map_isIso ((Over.pullback (U.f i)).map f)
    show IsIso (pullback.snd f.left (pullback.fst Y.hom (U.f i)))
    let h := overPullback_map_isPullback (U.f i) f
    have hcomp : pullback.snd f.left (pullback.fst Y.hom (U.f i)) =
        h.isoPullback.inv ≫ ((Over.pullback (U.f i)).map f).left := by
      simp
    rw [hcomp]
    infer_instance
  have : IsIso ((Over.forget S).map f) := this
  exact isIso_of_reflects_iso f (Over.forget S)

attribute [local instance] IsCofiltered.isConnected in
/-- A cone over a cofiltered diagram of schemes over `S` is a limit cone as soon as its base
change along every member of an open cover of `S` is. -/
noncomputable def isLimit_of_isLimit_overPullback
    {J : Type*} [Category* J] [IsCofiltered J] {S : Scheme.{u}}
    (D : J ⥤ Over S) (c : Cone D) (U : S.OpenCover) [HasLimit D]
    (hc : ∀ i, IsLimit ((Over.pullback (U.f i)).mapCone c)) : IsLimit c :=
  (jointlyReflectIsomorphisms_overPullback U).jointlyReflectsLimit hc

/-- A cone over a diagram of affine schemes with affine vertex is a limit cone as soon as global
sections take it to a colimit cocone of rings. -/
noncomputable def isLimit_of_isLimit_globalSections
    {J : Type*} [Category* J] (D : J ⥤ Scheme.{u}) (c : Cone D)
    [∀ j, IsAffine (D.obj j)] [IsAffine c.pt]
    (hc : IsLimit (Scheme.Γ.rightOp.mapCone c)) : IsLimit c := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec :=
    D.whiskerLeft ΓSpec.adjunction.unit
  have (j : J) : IsIso (α.app j) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  apply (IsLimit.postcomposeHomEquiv (asIso α) c).toFun
  apply (isLimitOfPreserves Scheme.Spec hc).ofIsoLimit
  refine Cone.ext (asIso c.pt.toSpecΓ).symm ?_
  intro j
  symm
  change inv c.pt.toSpecΓ ≫ (c.π.app j ≫ (D.obj j).toSpecΓ) =
    Scheme.Spec.map (Scheme.Γ.rightOp.map (c.π.app j))
  rw [Scheme.toSpecΓ_naturality, IsIso.inv_hom_id_assoc]
  rfl

end AffineOverBase

/-! ### Reduction to a `u`-small index -/

section SmallIndex

/-- A family of elements of a directed preorder, indexed by a nonempty type `α` in the universe
`u`, factors through a `u`-small nonempty directed preorder over it.  The small preorder is the
free magma on `α`, ordered by the pointwise supremum map into `I`. -/
lemma exists_small_directed_factor
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    {α : Type u} [Nonempty α] (s : α → I) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (e : J →o I) (a : α → J), e ∘ a = s := by
  classical
  let sup (i j : I) := (exists_ge_ge i j).choose
  have hsup (i j : I) : i ≤ sup i j ∧ j ≤ sup i j := (exists_ge_ge i j).choose_spec
  let e : FreeMagma α → I := FreeMagma.rec s (fun _ _ i j => sup i j)
  let _ : Preorder (FreeMagma α) := Preorder.lift e
  have : Nonempty (FreeMagma α) := Nonempty.map FreeMagma.of inferInstance
  have : IsDirected (FreeMagma α) (· ≤ ·) := ⟨fun i j =>
    ⟨FreeMagma.mul i j, (hsup (e i) (e j)).1, (hsup (e i) (e j)).2⟩⟩
  exact ⟨FreeMagma α, inferInstance, inferInstance, inferInstance,
    ⟨e, fun _ _ h => h⟩, FreeMagma.of, rfl⟩

/-- Every element of a filtered colimit of commutative rings comes from one of the stages. -/
lemma exists_eq_ι_app_of_isColimit
    {J : Type*} [Category* J] [IsFiltered J]
    {A : J ⥤ CommRingCat.{u}} (c : Cocone A) (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (y : A.obj j), (c.ι.app j).hom y = x := by
  classical
  let ρ (j : J) : A.obj j →+* c.pt := (c.ι.app j).hom
  let R : Subring c.pt := ⨆ j, (ρ j).range
  have hR (j : J) (y : A.obj j) : (c.ι.app j).hom y ∈ R :=
    le_iSup (fun j => (ρ j).range) j ⟨y, rfl⟩
  let d : Cocone A := {
    pt := CommRingCat.of R
    ι := {
      app j := CommRingCat.ofHom ((c.ι.app j).hom.codRestrict R (hR j))
      naturality i j f := by
        ext x
        exact Subtype.ext <| congrArg (fun f : A.obj i ⟶ c.pt => f.hom x) (c.w f) } }
  let e : CommRingCat.of R ⟶ c.pt := CommRingCat.ofHom R.subtype
  have he : hc.desc d ≫ e = 𝟙 c.pt := by
    apply hc.hom_ext
    intro j
    rw [← Category.assoc, hc.fac]
    rfl
  have hd : Directed (· ≤ ·) (fun j => ((ρ j).range : Subring c.pt)) := by
    intro i j
    refine ⟨IsFiltered.max i j, ?_, ?_⟩
    · rintro x ⟨y, rfl⟩
      refine ⟨(A.map (IsFiltered.leftToMax i j)).hom y, ?_⟩
      exact congrArg (fun f : A.obj i ⟶ c.pt => f.hom y)
        (c.w (IsFiltered.leftToMax i j))
    · rintro x ⟨y, rfl⟩
      refine ⟨(A.map (IsFiltered.rightToMax i j)).hom y, ?_⟩
      exact congrArg (fun f : A.obj j ⟶ c.pt => f.hom y)
        (c.w (IsFiltered.rightToMax i j))
  have hx : x ∈ R := by
    have he' := congrArg (fun f : c.pt ⟶ c.pt => f.hom x) he
    change ((hc.desc d).hom x).val = x at he'
    rw [← he']
    exact ((hc.desc d).hom x).property
  have : Nonempty J := IsFiltered.nonempty
  exact (Subring.mem_iSup_of_directed hd).mp hx

/-- A family of filtered colimits of rings, each with injective structure maps, is already the
colimit of its restriction to a single `u`-small directed preorder. -/
private lemma exists_small_isColimit_whisker_of_injective
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {K : Type u} {A : K → I ⥤ CommRingCat.{u}}
    (c : ∀ k, Cocone (A k)) (hc : ∀ k, IsColimit (c k))
    (hi : ∀ k i, Function.Injective ((c k).ι.app i).hom) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (e : J →o I), ∀ k, Nonempty (IsColimit ((c k).whisker e.monotone.functor)) := by
  classical
  choose s x hx using fun k => exists_eq_ι_app_of_isColimit (c k) (hc k)
  let seed : Option (Σ k, (c k).pt) → I :=
    fun t => t.elim (Classical.choice inferInstance) (fun t => s t.1 t.2)
  obtain ⟨J, _, _, _, e, a, ha⟩ := exists_small_directed_factor seed
  refine ⟨J, inferInstance, inferInstance, inferInstance, e, fun k => ?_⟩
  let c' := (c k).whisker e.monotone.functor
  have ht : IsColimit ((forget CommRingCat).mapCocone c') := by
    apply Types.FilteredColimit.isColimitOf'
    · intro y
      refine ⟨a (some ⟨k, y⟩), ?_⟩
      show ∃ z : (A k).obj (e (a (some ⟨k, y⟩))),
        y = ((c k).ι.app (e (a (some ⟨k, y⟩)))).hom z
      rw [show e (a (some ⟨k, y⟩)) = s k y from congrFun ha (some ⟨k, y⟩)]
      exact ⟨x k y, (hx k y).symm⟩
    · intro j p q hpq
      have h : p = q := hi k (e j) hpq
      subst q
      exact ⟨j, 𝟙 _, rfl⟩
  have : ReflectsColimit (e.monotone.functor ⋙ A k) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact ⟨isColimitOfReflects (forget CommRingCat) ht⟩

attribute [local instance] IsCofiltered.isConnected in
/-- **A limit of schemes affine and scheme-theoretically dominant over a base stays a limit after
restriction to a `u`-small cofinal-enough subsystem.**

The index `I` is an arbitrary nonempty directed preorder, with no condition relating its universe
to that of the schemes; the conclusion produces a `u`-small nonempty directed preorder `J` and a
monotone `e : J →o I` along which the cone restricts to a limit cone.  This is what makes the
results of this file available at a free index universe without a cofinality hypothesis: on each
affine open of `S` the stages inject into the limit, so the ring colimit is the union of their
images and a `u`-small family of stages exhausts it. -/
lemma exists_small_isLimit_whisker_of_isSchemeTheoreticallyDominant
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffineHom (D.obj i).hom] [IsAffineHom c.pt.hom]
    [∀ i, QuasiCompact (c.π.app i).left]
    [∀ i, IsSchemeTheoreticallyDominant (c.π.app i).left] :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (e : J →o I), Nonempty (IsLimit (c.whisker e.monotone.functor.op)) := by
  classical
  let U := S.affineCover
  let B (k : U.I₀) := Over.pullback (U.f k) ⋙ Over.forget _
  let cU (k : U.I₀) := (B k).mapCone c
  have hU (k : U.I₀) : IsLimit (cU k) := isLimitOfPreserves (B k) hc
  have _ (k : U.I₀) (i : Iᵒᵖ) : IsAffine ((D ⋙ B k).obj i) := by
    show IsAffine (pullback (D.obj i).hom (U.f k))
    infer_instance
  have _ (k : U.I₀) : IsAffine (cU k).pt := by
    show IsAffine (pullback c.pt.hom (U.f k))
    infer_instance
  let A (k : U.I₀) := (opOpEquivalence I).inverse ⋙
    ((D ⋙ B k) ⋙ Scheme.Γ.rightOp).leftOp
  let r (k : U.I₀) : Cocone (A k) :=
    (coconeLeftOpOfCone (Scheme.Γ.rightOp.mapCone (cU k))).whisker
      (opOpEquivalence I).inverse
  have hr (k : U.I₀) : IsColimit (r k) :=
    (Functor.Final.isColimitWhiskerEquiv _ _).symm
      (isColimitCoconeLeftOpOfCone _ (isLimitOfPreserves Scheme.Γ.rightOp (hU k)))
  have hi (k : U.I₀) (i : I) : Function.Injective ((r k).ι.app i).hom := by
    let q := ((Over.pullback (U.f k)).map (c.π.app (op i))).left
    have : IsSchemeTheoreticallyDominant q :=
      IsSchemeTheoreticallyDominant.of_isPullback
        (overPullback_map_isPullback (U.f k) (c.π.app (op i)))
    have _ : QuasiCompact q := MorphismProperty.overPullbackMap
      (P := @QuasiCompact) (U.f k) (c.π.app (op i)) inferInstance
    exact q.app_injective ⊤
  obtain ⟨J, _, _, _, e, he⟩ := exists_small_isColimit_whisker_of_injective r hr hi
  let E := e.monotone.functor.op
  have _ (i : Jᵒᵖ) (j : Jᵒᵖ) (a : i ⟶ j) :
      IsAffineHom (((E ⋙ D) ⋙ Over.forget S).map a) := by
    show IsAffineHom ((D.map (E.map a)).left)
    have : IsAffineHom ((D.map (E.map a)).left ≫ (D.obj (E.obj j)).hom) := by
      rw [(D.map (E.map a)).w]
      infer_instance
    exact IsAffineHom.of_comp _ (D.obj (E.obj j)).hom
  have _ : HasLimit ((E ⋙ D) ⋙ Over.forget S) :=
    hasLimit_of_isCofiltered_of_isAffineHom _
  have _ : HasLimit (E ⋙ D) := hasLimit_of_created _ (Over.forget S)
  refine ⟨J, inferInstance, inferInstance, inferInstance, e, ⟨?_⟩⟩
  apply isLimit_of_isLimit_overPullback (E ⋙ D) (c.whisker E) U
  intro k
  apply isLimitOfReflects (Over.forget _)
  have _ : IsAffine ((Over.forget (U.X k)).mapCone
      ((Over.pullback (U.f k)).mapCone (c.whisker E))).pt := by
    show IsAffine (pullback c.pt.hom (U.f k))
    infer_instance
  have _ (j : Jᵒᵖ) :
      IsAffine ((((E ⋙ D) ⋙ Over.pullback (U.f k)) ⋙ Over.forget (U.X k)).obj j) := by
    show IsAffine (pullback (D.obj (E.obj j)).hom (U.f k))
    infer_instance
  apply isLimit_of_isLimit_globalSections
  apply isLimitOfCoconeLeftOpOfCone
  apply (Functor.Final.isColimitWhiskerEquiv (opOpEquivalence J).inverse _).toFun
  exact (he k).some

end SmallIndex

/-! ### The tail of a directed preorder as a slice -/

section Tail

/-- The upper set above `i`, opposite, as a subcategory of the slice of `Iᵒᵖ` over `op i`. -/
def tailToOver {I : Type v} [Preorder I] (i : I) :
    (Set.Ici i)ᵒᵖ ⥤ Over (op i) where
  obj j := Over.mk ((homOfLE (unop j).property).op)
  map a := Over.homMk ((homOfLE (leOfHom a.unop)).op) (Subsingleton.elim _ _)

/-- An upper set of a directed preorder is directed. -/
lemma directed_tail {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (i : I) :
    IsDirected (Set.Ici i) (· ≤ ·) := by
  constructor
  intro j k
  obtain ⟨l, hj, hk⟩ := exists_ge_ge j.val k.val
  exact ⟨⟨l, j.property.trans hj⟩, hj, hk⟩

/-- The comparison of the tail above `i` with the slice over `op i` is initial, so a limit cone
over the slice restricts to a limit cone over the tail. -/
lemma initial_tailToOver {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (i : I) : (tailToOver i).Initial := by
  have _ : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  have _ := directed_tail i
  apply Functor.initial_of_exists_of_isCofiltered
  · intro k
    exact ⟨op ⟨unop k.left, leOfHom k.hom.unop⟩,
      ⟨Over.homMk (𝟙 _) (Subsingleton.elim _ _)⟩⟩
  · intro k l a b
    exact ⟨l, 𝟙 _, Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

end Tail

/-! ### The two halves of Tag 01ZC under dominance -/

section Dominant

/-- Under dominance, a limit over `Iᵒᵖ` stays a limit after restriction along a `u`-small directed
preorder mapping monotonically into the tail above `i₀`. -/
private lemma exists_small_isLimit_whisker_tail
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)]
    [∀ i, IsSchemeTheoreticallyDominant (c.π.app i)] (i₀ : I) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (e : J →o I), (∀ j, i₀ ≤ e j) ∧ Nonempty (IsLimit (c.whisker e.monotone.functor.op)) := by
  have _ : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have _ := directed_tail i₀
  have _ := initial_tailToOver i₀
  let E := tailToOver i₀
  let P : (Set.Ici i₀)ᵒᵖ ⥤ Over (D.obj (op i₀)) := E ⋙ Over.post D
  let cP : Cone P := ((Over.conePost D (op i₀)).obj c).whisker E
  have hcP : IsLimit cP := (Functor.Initial.isLimitWhiskerEquiv E _).symm
    (Over.isLimitConePost (op i₀) hc)
  have _ (j : (Set.Ici i₀)ᵒᵖ) : IsAffineHom (P.obj j).hom :=
    inferInstanceAs (IsAffineHom (D.map (E.obj j).hom))
  have _ : IsAffineHom cP.pt.hom := EventualLimit.isAffineHom_π_app D c hc (op i₀)
  have _ (j : (Set.Ici i₀)ᵒᵖ) : QuasiCompact (cP.π.app j).left := by
    show QuasiCompact (c.π.app (E.obj j).left)
    have _ := EventualLimit.isAffineHom_π_app D c hc (E.obj j).left
    infer_instance
  have _ (j : (Set.Ici i₀)ᵒᵖ) : IsSchemeTheoreticallyDominant (cP.π.app j).left :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (c.π.app (E.obj j).left))
  obtain ⟨J, _, _, _, e, ⟨he⟩⟩ :=
    exists_small_isLimit_whisker_of_isSchemeTheoreticallyDominant P cP hcP
  exact ⟨J, inferInstance, inferInstance, inferInstance,
    ⟨fun j ↦ (e j).val, fun _ _ h ↦ e.monotone h⟩, fun j ↦ (e j).property,
    ⟨isLimitOfPreserves (Over.forget (D.obj (op i₀))) he⟩⟩

attribute [local instance] IsCofiltered.isConnected in
/-- **Stacks Project, Tag 01ZC, surjectivity half, with no cofinality hypothesis on the index.**
A morphism from the limit to a scheme locally of finite presentation over the base factors
through some stage, provided the projections out of the limit are scheme-theoretically dominant.

This is `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` with the
index universe independent of the scheme universe, and
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall`
with dominance of the projections in place of `CategoryTheory.InitiallySmall`. -/
theorem Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S X : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (τ : D ⟶ (Functor.const Iᵒᵖ).obj S) (f : X ⟶ S)
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, IsSchemeTheoreticallyDominant (c.π.app i)]
    [LocallyOfFinitePresentation f]
    (a : c.pt ⟶ X) (ha : c.π ≫ τ = (Functor.const Iᵒᵖ).map (a ≫ f)) :
    ∃ (i : Iᵒᵖ) (g : D.obj i ⟶ X), c.π.app i ≫ g = a ∧ g ≫ f = τ.app i := by
  classical
  obtain ⟨J, _, _, _, e, he, ⟨hlim⟩⟩ :=
    exists_small_isLimit_whisker_tail D c hc (Classical.arbitrary I)
  let F : Jᵒᵖ ⥤ Iᵒᵖ := e.monotone.functor.op
  let _ {x y : Jᵒᵖ} (g : x ⟶ y) : IsAffineHom ((F ⋙ D).map g) := by
    dsimp; infer_instance
  have _ (x : Jᵒᵖ) : CompactSpace ((F ⋙ D).obj x) := by dsimp; infer_instance
  have _ (x : Jᵒᵖ) : QuasiSeparatedSpace ((F ⋙ D).obj x) := by dsimp; infer_instance
  obtain ⟨j, g, hg₁, hg₂⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (F ⋙ D)
      ({ app x := τ.app (F.obj x), naturality := fun x y g ↦ τ.naturality (F.map g) })
      f (c.whisker F) hlim a (by ext x; exact NatTrans.congr_app ha (F.obj x))
  exact ⟨F.obj j, g, hg₁, hg₂⟩

attribute [local instance] IsCofiltered.isConnected in
/-- **Stacks Project, Tag 01ZC, injectivity half, with no cofinality hypothesis on the index.**
Two morphisms out of the stage `op i₀` to a scheme locally of finite type over the base which
agree after composition with the projection from the limit agree at some later stage, provided
the projections out of the limit are scheme-theoretically dominant.

This is
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_initiallySmall`
with dominance of the projections in place of `CategoryTheory.InitiallySmall`.  The two morphisms
are taken at one and the same stage because the `u`-small subsystem produced by the reduction is
not claimed to be cofinal; see
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant_slice`
for the form with two stages. -/
theorem Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S X : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (τ : D ⟶ (Functor.const Iᵒᵖ).obj S) (f : X ⟶ S)
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)]
    [∀ i, IsSchemeTheoreticallyDominant (c.π.app i)]
    [LocallyOfFiniteType f]
    (i₀ : I)
    (a b : D.obj (op i₀) ⟶ X) (ha : τ.app (op i₀) = a ≫ f) (hb : τ.app (op i₀) = b ≫ f)
    (hab : c.π.app (op i₀) ≫ a = c.π.app (op i₀) ≫ b) :
    ∃ (k : I) (hk : i₀ ≤ k),
      D.map (homOfLE hk).op ≫ a = D.map (homOfLE hk).op ≫ b := by
  classical
  obtain ⟨J, _, _, _, e, he, ⟨hlim⟩⟩ := exists_small_isLimit_whisker_tail D c hc i₀
  let F : Jᵒᵖ ⥤ Iᵒᵖ := e.monotone.functor.op
  let _ {x y : Jᵒᵖ} (g : x ⟶ y) : IsAffineHom ((F ⋙ D).map g) := by dsimp; infer_instance
  have _ (x : Jᵒᵖ) : CompactSpace ((F ⋙ D).obj x) := by dsimp; infer_instance
  let j₀ : Jᵒᵖ := op (Classical.arbitrary J)
  let d : F.obj j₀ ⟶ op i₀ := (homOfLE (he (unop j₀))).op
  obtain ⟨k, hik, hjk, hk⟩ :=
    Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType (F ⋙ D)
      ({ app x := τ.app (F.obj x), naturality := fun x y g ↦ τ.naturality (F.map g) })
      f (c.whisker F) hlim
      (i := j₀) (D.map d ≫ a) (by
        show τ.app (F.obj j₀) = _
        rw [Category.assoc, ← ha]
        exact (τ.naturality d).symm)
      (j := j₀) (D.map d ≫ b) (by
        show τ.app (F.obj j₀) = _
        rw [Category.assoc, ← hb]
        exact (τ.naturality d).symm)
      (by
        show c.π.app (F.obj j₀) ≫ _ = c.π.app (F.obj j₀) ≫ _
        rwa [← Category.assoc, ← Category.assoc, c.w d])
  refine ⟨e (unop k), he _, ?_⟩
  rw [Subsingleton.elim hik hjk] at hk
  change D.map (F.map hik) ≫ D.map d ≫ a = D.map (F.map hik) ≫ D.map d ≫ b at hk
  rw [← Category.assoc, ← Category.assoc, ← D.map_comp] at hk
  rwa [show (homOfLE (he (unop k))).op = F.map hik ≫ d from Subsingleton.elim _ _]

attribute [local instance] IsCofiltered.isConnected in
/-- The surjectivity half of Tag 01ZC under dominance, for a system indexed by the slice of the
opposite preorder over `op i₀`. -/
theorem Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant_slice
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {i₀ : I}
    {S X : Scheme.{u}} (A : Over (op i₀) ⥤ Scheme.{u})
    (τ : A ⟶ (Functor.const (Over (op i₀))).obj S) (f : X ⟶ S)
    (c : Cone A) (hc : IsLimit c)
    [∀ {j k : Over (op i₀)} (g : j ⟶ k), IsAffineHom (A.map g)]
    [∀ j, CompactSpace (A.obj j)] [∀ j, QuasiSeparatedSpace (A.obj j)]
    [∀ j, IsSchemeTheoreticallyDominant (c.π.app j)]
    [LocallyOfFinitePresentation f]
    (a : c.pt ⟶ X) (ha : c.π ≫ τ = (Functor.const _).map (a ≫ f)) :
    ∃ (j : Over (op i₀)) (g : A.obj j ⟶ X), c.π.app j ≫ g = a ∧ g ≫ f = τ.app j := by
  have _ : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have _ := directed_tail i₀
  have _ := initial_tailToOver i₀
  let E := tailToOver i₀
  have hc' : IsLimit (c.whisker E) := (Functor.Initial.isLimitWhiskerEquiv E c).symm hc
  let _ {x y : (Set.Ici i₀)ᵒᵖ} (g : x ⟶ y) : IsAffineHom ((E ⋙ A).map g) := by
    dsimp; infer_instance
  have _ (x : (Set.Ici i₀)ᵒᵖ) : CompactSpace ((E ⋙ A).obj x) := by dsimp; infer_instance
  have _ (x : (Set.Ici i₀)ᵒᵖ) : QuasiSeparatedSpace ((E ⋙ A).obj x) := by dsimp; infer_instance
  have _ (x : (Set.Ici i₀)ᵒᵖ) : IsSchemeTheoreticallyDominant ((c.whisker E).π.app x) :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (c.π.app (E.obj x)))
  obtain ⟨x, g, h₁, h₂⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant (E ⋙ A)
      (c.whisker E) hc'
      ({ app y := τ.app (E.obj y), naturality := fun y z g ↦ τ.naturality (E.map g) }) f a
      (by ext y; exact NatTrans.congr_app ha (E.obj y))
  exact ⟨E.obj x, g, h₁, h₂⟩

attribute [local instance] IsCofiltered.isConnected in
/-- The injectivity half of Tag 01ZC under dominance, for a system indexed by the slice of the
opposite preorder over `op i₀`, with the two morphisms taken at two arbitrary stages of the
slice. -/
theorem Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant_slice
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {i₀ : I}
    {S X : Scheme.{u}} (A : Over (op i₀) ⥤ Scheme.{u})
    (τ : A ⟶ (Functor.const (Over (op i₀))).obj S) (f : X ⟶ S)
    (c : Cone A) (hc : IsLimit c)
    [∀ {j k : Over (op i₀)} (g : j ⟶ k), IsAffineHom (A.map g)]
    [∀ j, CompactSpace (A.obj j)]
    [∀ j, IsSchemeTheoreticallyDominant (c.π.app j)]
    [LocallyOfFiniteType f]
    {i : Over (op i₀)} (a : A.obj i ⟶ X) (ha : τ.app i = a ≫ f)
    {j : Over (op i₀)} (b : A.obj j ⟶ X) (hb : τ.app j = b ≫ f)
    (hab : c.π.app i ≫ a = c.π.app j ≫ b) :
    ∃ (k : Over (op i₀)) (hik : k ⟶ i) (hjk : k ⟶ j),
      A.map hik ≫ a = A.map hjk ≫ b := by
  obtain ⟨m, hmi, hmj⟩ := exists_ge_ge (unop i.left) (unop j.left)
  have hm : i₀ ≤ m := (leOfHom i.hom.unop).trans hmi
  have _ : Nonempty (Set.Ici m) := ⟨⟨m, le_rfl⟩⟩
  have _ := directed_tail m
  have _ := initial_tailToOver m
  let G : (Set.Ici m)ᵒᵖ ⥤ Over (op i₀) := tailToOver m ⋙ Over.map ((homOfLE hm).op)
  have hG : G.Initial := inferInstance
  have hc' : IsLimit (c.whisker G) := (Functor.Initial.isLimitWhiskerEquiv G c).symm hc
  let _ {x y : (Set.Ici m)ᵒᵖ} (g : x ⟶ y) : IsAffineHom ((G ⋙ A).map g) := by
    dsimp; infer_instance
  have _ (x : (Set.Ici m)ᵒᵖ) : CompactSpace ((G ⋙ A).obj x) := by dsimp; infer_instance
  have _ (x : (Set.Ici m)ᵒᵖ) : IsSchemeTheoreticallyDominant ((c.whisker G).π.app x) :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (c.π.app (G.obj x)))
  let di : G.obj (op ⟨m, le_rfl⟩) ⟶ i := Over.homMk ((homOfLE hmi).op) (Subsingleton.elim _ _)
  let dj : G.obj (op ⟨m, le_rfl⟩) ⟶ j := Over.homMk ((homOfLE hmj).op) (Subsingleton.elim _ _)
  have hτ {x : Over (op i₀)} (d : G.obj (op ⟨m, le_rfl⟩) ⟶ x) :
      τ.app (G.obj (op ⟨m, le_rfl⟩)) = A.map d ≫ τ.app x := by
    have h := τ.naturality d
    simp only [Functor.const_obj_map] at h
    exact h.symm
  obtain ⟨k, hk, hkeq⟩ :=
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant (G ⋙ A) (c.whisker G) hc'
      ({ app y := τ.app (G.obj y), naturality := fun y z g ↦ τ.naturality (G.map g) }) f
      ⟨m, le_rfl⟩ (A.map di ≫ a) (A.map dj ≫ b)
      (by rw [Category.assoc, ← ha]; exact hτ di)
      (by rw [Category.assoc, ← hb]; exact hτ dj)
      (by
        show c.π.app (G.obj (op ⟨m, le_rfl⟩)) ≫ _ = c.π.app (G.obj (op ⟨m, le_rfl⟩)) ≫ _
        rwa [← Category.assoc, ← Category.assoc, c.w di, c.w dj])
  refine ⟨G.obj (op k), G.map (homOfLE hk).op ≫ di, G.map (homOfLE hk).op ≫ dj, ?_⟩
  rwa [A.map_comp, A.map_comp, Category.assoc, Category.assoc]

end Dominant

end AlgebraicGeometry

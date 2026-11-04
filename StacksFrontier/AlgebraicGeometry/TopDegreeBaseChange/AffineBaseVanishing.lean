module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.Basic
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.Limits.ProperFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimensionQuasicoherent

/-!
# Vanishing above the fibre dimension over an arbitrary affine base

Let `g : X ⟶ Y` be proper onto an affine scheme — with **no** Noetherian hypothesis — and suppose
every fibre of `g` has topological Krull dimension at most `d`. Then

`Hⁱ(X, F) = 0` for every `i > d` and every quasi-coherent `F` on `X`,

and so every stalk of `Rⁱ g_* F` vanishes ([Stacks, Tag 0E7D]). When the base is Noetherian this is
`FibreDimension.isZero_rightDerivedPlus_moduleGlobalSections_of_affine_base_of_isQuasicoherent`
(from [Stacks, Tag 02V7] and the colimit argument of [Stacks, Tags 01PK, 01FF]).

The passage from the Noetherian base to the general one is the pair of limit reductions the
source's proof makes, in the source's order.

* **Finite type to finite presentation.** A proper morphism onto a quasi-compact quasi-separated
  scheme is a directed inverse limit of proper morphisms of *finite presentation* with closed
  immersions for transitions and projections ([Stacks, Tag 09ZR]); the fibre bound holds at some
  stage ([Stacks, Tag 05M5]); and the cohomology upstairs is the cohomology of the direct image
  along the closed immersion, which is affine ([Stacks, Tag 089W]).
* **Arbitrary base to Noetherian base.** An affine scheme is the inverse limit of the spectra of
  the finitely generated subalgebras of its ring of global functions, all of them Noetherian; a
  morphism of finite presentation descends to one of the stages ([Stacks, Tag 01ZM] part (1)),
  its properness is recovered at a later stage ([Stacks, Tag 081F]), the fibre bound at a later
  stage still ([Stacks, Tag 05M5]), and the resulting comparison morphism is affine, so
  [Stacks, Tag 089W] identifies the two cohomologies again.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `exists_isClosedImmersion_isProper_finitePresentation_fiber_dim_le`: the first reduction — a
  proper morphism with bounded fibres is a closed immersion followed by a proper morphism of
  finite presentation with bounded fibres.
* `exists_isProper_isLocallyNoetherian_model`: the second — a proper morphism of finite
  presentation with bounded fibres onto an affine base is an affine morphism followed by a proper
  morphism with bounded fibres onto an affine *locally Noetherian* base.
* `isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_affineBase`: **the vanishing itself**, over
  an arbitrary affine base.
* `cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le`: the same, for every proper
  morphism onto an affine scheme whose fibres have dimension at most `d`.

## Implementation notes

**Why the cohomology never has to be compared across a limit.** The identification of
`Rᵈ g_* F` with the pullback of its model at a stage — clause (c) of [Stacks, Tag 0EX3] — is not
available in this development, and it is not needed: in both reductions the comparison morphism
`X ⟶ X'` built from the descent is *affine*, and for an affine morphism the cohomology of `F` on
`X` is the cohomology of `a_* F` on `X'` ([Stacks, Tag 089W],
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`). So each reduction replaces the
pair `(X, F)` by a pair `(X', a_* F)` with the same cohomology, and the vanishing is read off at
the Noetherian stage. The direct image `a_* F` is quasi-coherent because `a` is affine, which is
why the statement proved is about quasi-coherent and not merely finitely presented modules.

**The fibre bound has to be chased through the stages.** Neither [Stacks, Tag 01ZM] nor
[Stacks, Tag 081F] preserves it, and the bound at the limit does not by itself bound the fibres
of a stage — only the fibres over the image of the limit. [Stacks, Tag 05M5] repairs this at a
later stage, and `exists_stage_fiber_dim_le` applies it to the system of base changes of a fixed
morphism `T ⟶ D(i)` along the transitions, indexed by `CategoryTheory.Over i`; the two cones it
needs are the ones `CategoryTheory.Limits.Cone.overPost` and
`CategoryTheory.Limits.IsLimit.overPost` produce, and the limit projection it compares against is
identified with the base change of `T ⟶ D(i)` along `c.π.app i` by
`IsLimit.hom_ext`. Properness is chased the same way, by [Stacks, Tag 081F] applied to the
`CategoryTheory.Over` presentation of `T ⟶ D(i)`.

**The Noetherian presentation is `AlgebraicGeometry.affineStageCone`**, the inverse limit of the
spectra of the finitely generated subalgebras of `Γ(Y, ⊤)`, whose vertex is `Y` itself; its
stages are affine, Noetherian and of finite type over `ℤ`.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

/-! ### Chasing properness and the fibre bound through the stages -/

/-- **The projections of the base changes of a system of schemes over a fixed base.** For
`g : T ⟶ S` the natural transformation whose component at `A ⟶ S` is
`A ×_S T ⟶ A`. -/
def baseChangeProjection {S T : Scheme.{u}} (g : T ⟶ S) :
    Over.pullback g ⋙ Over.forget T ⟶ Over.forget S where
  app A := pullback.fst A.hom g
  naturality _ _ _ := pullback.lift_fst _ _ _

/-- Base change along `g` of a morphism over `S` is a pullback square of the two projections. -/
theorem baseChangeProjection_isPullback {S T : Scheme.{u}} (g : T ⟶ S)
    {A B : Over S} (e : A ⟶ B) :
    IsPullback ((Over.pullback g).map e).left (pullback.fst A.hom g)
      (pullback.fst B.hom g) e.left := by
  have h1 : ((Over.pullback g).map e).left ≫ pullback.snd B.hom g
      = pullback.snd A.hom g := pullback.lift_snd _ _ _
  have h2 : ((Over.pullback g).map e).left ≫ pullback.fst B.hom g
      = pullback.fst A.hom g ≫ e.left := pullback.lift_fst _ _ _
  refine IsPullback.of_right (t := (IsPullback.of_hasPullback B.hom g).flip) ?_ h2
  rw [h1, Over.w e]
  exact (IsPullback.of_hasPullback A.hom g).flip

/-- **Isomorphic objects of `CategoryTheory.Over Y` have homeomorphic fibres**, hence fibres of
equal dimension. -/
theorem topologicalKrullDim_fiber_eq_of_over_iso {X X' Y : Scheme.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y} (e : Over.mk f ≅ Over.mk g) (y : Y) :
    topologicalKrullDim (f.fiber y) = topologicalKrullDim (g.fiber y) :=
  (Scheme.homeoOfIso ((Over.forget _).mapIso
    ((Over.pullback (Y.fromSpecResidueField y)).mapIso e))).isHomeomorph.topologicalKrullDim_eq _

/-- **[Stacks, Tag 05M5] for the base changes of one morphism to a stage.** Let `c` be a limit
cone over a cofiltered system `D` of schemes with affine transitions, let `g : T ⟶ D(i)` be of
finite type, and let `f : X ⟶ c.pt` be the base change of `g` along `c.π.app i`. If every fibre
of `f` has dimension at most `d`, then for some `j ⟶ i` every fibre of the base change of `g`
along `D.map (j ⟶ i)` has dimension at most `d`.

The system [Stacks, Tag 05M5] is applied to is indexed by `CategoryTheory.Over i`: the base
system is `D` restricted along `CategoryTheory.Over.forget i`, which has the same limit because
that functor is initial, and the total system is its base change along `g`, whose limit is
computed by `CategoryTheory.Limits.IsLimit.overPost` and the preservation of limits by
`CategoryTheory.Over.pullback` and `CategoryTheory.Over.forget`. The closed-immersion hypothesis
of the tag holds because each square of base changes is a pullback
(`baseChangeProjection_isPullback`), so the comparison morphism is an isomorphism. -/
theorem exists_stage_fiber_dim_le {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) {T X : Scheme.{u}} (g : T ⟶ D.obj i)
    [LocallyOfFiniteType g] [QuasiCompact g]
    (f : X ⟶ c.pt) (a : X ⟶ T)
    (sq : IsPullback f a (c.π.app i) g) (d : ℕ)
    (hd : ∀ y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ (j : I) (e : j ⟶ i),
      ∀ y, topologicalKrullDim ((pullback.fst (D.map e) g).fiber y) ≤
        (d : WithBot ℕ∞) := by
  let B : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D
  let E : Over i ⥤ Scheme.{u} := Over.post D ⋙ Over.pullback g ⋙ Over.forget T
  let t : E ⟶ B := Functor.whiskerLeft (Over.post D) (baseChangeProjection g)
  let cB : Cone B := c.whisker (Over.forget i)
  let hcB : IsLimit cB := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  let cE : Cone E := (Over.forget T).mapCone ((Over.pullback g).mapCone (c.overPost i))
  let hcE : IsLimit cE := isLimitOfPreserves (Over.forget T)
    (isLimitOfPreserves (Over.pullback g) (hc.overPost i))
  have ht (j : Over i) : t.app j = pullback.fst (D.map j.hom) g := rfl
  let _ : ∀ {j k : Over i} (e : j ⟶ k), IsAffineHom (B.map e) := fun _ => inferInstance
  let _ : ∀ j, CompactSpace (B.obj j) := fun j => ‹∀ i, CompactSpace (D.obj i)› j.left
  let _ : ∀ j, QuasiSeparatedSpace (B.obj j) :=
    fun j => ‹∀ i, QuasiSeparatedSpace (D.obj i)› j.left
  let _ : ∀ j, LocallyOfFiniteType (t.app j) := fun j => by
    rw [ht]
    exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback (D.map j.hom) g).flip inferInstance
  let _ : ∀ j, QuasiCompact (t.app j) := fun j => by
    rw [ht]
    exact MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (D.map j.hom) g).flip inferInstance
  let _ : ∀ {j k : Over i} (e : j ⟶ k),
      IsClosedImmersion (pullback.lift (E.map e) (t.app j) (t.naturality e)) := fun {j k} e => by
    have h := baseChangeProjection_isPullback g ((Over.post D).map e)
    change IsPullback (E.map e) (t.app j) (t.app k) (B.map e) at h
    have heq : pullback.lift (E.map e) (t.app j) (t.naturality e) = h.isoPullback.hom := by
      refine pullback.hom_ext ?_ ?_
      · simp only [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      · simp only [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
    rw [heq]
    infer_instance
  have hlim : hcB.lift ((Cone.postcompose t).obj cE) = pullback.fst (c.π.app i) g := by
    refine hcB.hom_ext fun j => ?_
    rw [hcB.fac]
    exact (baseChangeProjection g).naturality ((c.overPost i).π.app j)
  have hbound : ∀ y, topologicalKrullDim
      ((hcB.lift ((Cone.postcompose t).obj cE)).fiber y) ≤ (d : WithBot ℕ∞) := by
    intro y
    rw [hlim]
    exact (topologicalKrullDim_fiber_eq_of_over_iso
      (Over.isoMk sq.isoPullback (by exact sq.isoPullback_hom_fst)) y).symm.trans_le (hd y)
  obtain ⟨j, hj⟩ :=
    AlgebraicGeometry.exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall
      E B t cE hcE cB hcB d hbound
  exact ⟨j.left, j.hom, hj⟩

/-- **[Stacks, Tag 081F] for the base changes of one morphism to a stage.** In the situation of
`exists_stage_fiber_dim_le`, if the base change `f` of `g` along `c.π.app i` is proper then the
base change of `g` along `D.map (j ⟶ i)` is proper for some `j ⟶ i`.

The tag is applied to the morphism `Over.mk g ⟶ Over.mk (𝟙 (D.obj i))` of
`CategoryTheory.Over (D.obj i)`, whose base change along a morphism of schemes has underlying
morphism the base change of `g`; `CategoryTheory.Over.w` identifies the two. -/
theorem exists_isProper_pullback_snd {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) {T X : Scheme.{u}} (g : T ⟶ D.obj i)
    [LocallyOfFiniteType g] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ c.pt) (hf : IsProper f) (a : X ⟶ T)
    (sq : IsPullback f a (c.π.app i) g) :
    ∃ (j : I) (e : j ⟶ i), IsProper (pullback.snd g (D.map e)) := by
  let X₀ := Over.mk g
  let Y₀ := Over.mk (𝟙 (D.obj i))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk g
  have _ : LocallyOfFiniteType f₀.left := ‹LocallyOfFiniteType g›
  have _ : IsProper (pullback.snd g (c.π.app i)) := by
    apply (MorphismProperty.cancel_left_of_respectsIso (@IsProper)
      sq.flip.isoPullback.hom _).mp
    simpa using hf
  have _ : IsProper ((Over.pullback (c.π.app i)).map f₀).left := by
    apply (MorphismProperty.cancel_right_of_respectsIso (@IsProper) _
      (pullback.snd (𝟙 (D.obj i)) (c.π.app i))).mp
    show IsProper (((Over.pullback (c.π.app i)).map f₀).left ≫
      ((Over.pullback (c.π.app i)).obj Y₀).hom)
    rw [Over.w]
    show IsProper (pullback.snd g (c.π.app i))
    infer_instance
  have _ : CompactSpace X₀.left := ‹CompactSpace T›
  have _ : QuasiSeparatedSpace X₀.left := ‹QuasiSeparatedSpace T›
  have _ : CompactSpace Y₀.left := ‹∀ i, CompactSpace (D.obj i)› i
  have _ : QuasiSeparatedSpace Y₀.left := ‹∀ i, QuasiSeparatedSpace (D.obj i)› i
  obtain ⟨j, e, he⟩ :=
    AlgebraicGeometry.exists_isProper_baseChange_of_isLimit D c i hc X₀ Y₀ f₀
  refine ⟨j, e, ?_⟩
  let _ := he
  have h : IsProper (((Over.pullback (D.map e)).map f₀).left ≫
    pullback.snd (𝟙 (D.obj i)) (D.map e)) := by infer_instance
  change IsProper (((Over.pullback (D.map e)).map f₀).left ≫
    ((Over.pullback (D.map e)).obj Y₀).hom) at h
  rw [Over.w] at h
  change IsProper (pullback.snd g (D.map e)) at h
  exact h

/-- **A base change to a stage is a base change to any earlier stage.** If `f` is the base change
of `g : T ⟶ D(i)` along `c.π.app i`, then for `e : j ⟶ i` it is also the base change of
`T ×_{D(i)} D(j) ⟶ D(j)` along `c.π.app j`. -/
theorem isPullback_stage_lift {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (e : j ⟶ i) {T X : Scheme.{u}} (g : T ⟶ D.obj i)
    (f : X ⟶ c.pt) (a : X ⟶ T)
    (sq : IsPullback f a (c.π.app i) g) :
    ∃ a' : X ⟶ pullback g (D.map e),
      IsPullback f a' (c.π.app j) (pullback.snd g (D.map e)) := by
  have hw : a ≫ g = (f ≫ c.π.app j) ≫ D.map e := by
    rw [Category.assoc, c.w]
    exact sq.w.symm
  refine ⟨pullback.lift a (f ≫ c.π.app j) hw, IsPullback.flip ?_⟩
  apply IsPullback.of_right (t := IsPullback.of_hasPullback g (D.map e))
  · simpa only [pullback.lift_fst, c.w] using sq.flip
  · simp only [pullback.lift_snd]

/-! ### The two models -/

/-- **A proper morphism with bounded fibres is a closed immersion into a proper morphism of
finite presentation with bounded fibres.** This is the first reduction of the proof of
[Stacks, Tag 0E7D]: [Stacks, Tag 09ZR] presents the morphism as an inverse limit of proper
morphisms of finite presentation over the same base, with closed immersions for transitions and
projections, and [Stacks, Tag 05M5] produces a stage at which the fibre bound holds.

The base system of [Stacks, Tag 05M5] is the constant system at `Y`, whose limit cone is
`CategoryTheory.Limits.constCone`; the index category is cofiltered, hence connected, which is
what makes that cone a limit. -/
theorem exists_isClosedImmersion_isProper_finitePresentation_fiber_dim_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (d : ℕ)
    (hd : ∀ y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ (T : Scheme.{u}) (g : T ⟶ Y) (a : X ⟶ T),
      IsProper g ∧ FinitePresentation g ∧ IsClosedImmersion a ∧ a ≫ g = f ∧
      (∀ y, topologicalKrullDim (g.fiber y) ≤ (d : WithBot ℕ∞)) := by
  obtain ⟨I, hI, hne, hdir, D, t, p, hc, hpt, ht, hD, hp⟩ :=
    AlgebraicGeometry.exists_isLimit_isProper_finitePresentation_isClosedImmersion f
  let _ := hI
  let _ := hne
  let _ := hdir
  let _ : IsCofiltered Iᵒᵖ := inferInstance
  let _ : CategoryTheory.IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  let B := (Functor.const Iᵒᵖ).obj Y
  let cB := constCone Iᵒᵖ Y
  let hcB := isLimitConstCone Iᵒᵖ Y
  let cD := Cone.mk X p
  let _ : ∀ i, IsProper (t.app i) := fun i => (ht i).1
  let _ : ∀ {i j : Iᵒᵖ} (e : i ⟶ j), IsAffineHom (B.map e) := fun _ => by
    show IsAffineHom (𝟙 Y)
    infer_instance
  let _ : ∀ i : Iᵒᵖ, CompactSpace (B.obj i) := fun _ => ‹CompactSpace Y›
  let _ : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (B.obj i) := fun _ => ‹QuasiSeparatedSpace Y›
  let _ : ∀ i, LocallyOfFiniteType (t.app i) := fun _ => inferInstance
  let _ : ∀ i, QuasiCompact (t.app i) := fun _ => inferInstance
  let _ : ∀ {i j : Iᵒᵖ} (e : i ⟶ j), IsClosedImmersion (D.map e) := fun {i j} e => hD i j e
  let _ : ∀ {i j : Iᵒᵖ} (e : i ⟶ j),
      IsClosedImmersion (pullback.lift (D.map e) (t.app i) (t.naturality e)) := fun {i j} e => by
    have _ : IsClosedImmersion (pullback.lift (D.map e) (t.app i) (t.naturality e) ≫
        pullback.fst (t.app j) (B.map e)) := by
      rw [pullback.lift_fst]
      exact hD i j e
    exact IsClosedImmersion.of_comp _ (pullback.fst (t.app j) (B.map e))
  have hfac : ∀ i : Iᵒᵖ, p.app i ≫ t.app i = f := fun i => by
    simpa using congrArg (fun η : (Functor.const Iᵒᵖ).obj X ⟶ B => NatTrans.app η i) hpt
  have hlim : hcB.lift ((Cone.postcompose t).obj cD) = f := by
    refine hcB.hom_ext fun j => ?_
    rw [hcB.fac]
    exact (hfac j).trans (Category.comp_id f).symm
  obtain ⟨i, hi⟩ :=
    AlgebraicGeometry.exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall
      D B t cD hc cB hcB d (fun y => le_of_eq_of_le
        (congrArg (fun m : X ⟶ Y => topologicalKrullDim (Scheme.Hom.fiber m y)) hlim) (hd y))
  exact ⟨D.obj i, t.app i, p.app i, (ht i).1, (ht i).2, hp i, hfac i, hi⟩

/-- **A proper morphism of finite presentation with bounded fibres onto an affine base is an
affine morphism into a proper morphism with bounded fibres onto an affine Noetherian base.** This
is the second reduction of the proof of [Stacks, Tag 0E7D].

`AlgebraicGeometry.affineStageCone` presents `Y` as the inverse limit of the spectra of the
finitely generated subalgebras of `Γ(Y, ⊤)`, all affine and Noetherian;
[Stacks, Tag 01ZM] part (1) descends `f` to a morphism of finite presentation over a stage;
`exists_isProper_pullback_snd` recovers properness at a later stage and
`exists_stage_fiber_dim_le` the fibre bound at a later stage still. The comparison morphism is
affine because it is a base change of a limit projection, and those are affine when the
transition morphisms are (`isAffineHom_π_app`). -/
theorem exists_isProper_isLocallyNoetherian_model_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, IsAffine (D.obj i)] [∀ i, IsLocallyNoetherian (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) (hf : IsProper f) (hfp : FinitePresentation f) (d : ℕ)
    (hd : ∀ y : c.pt, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ (T S : Scheme.{u}) (a : X ⟶ T) (g : T ⟶ S),
      IsAffine S ∧ IsLocallyNoetherian S ∧ IsAffineHom a ∧ IsProper g ∧
      (∀ s : S, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) := by
  let _ := hf
  obtain ⟨i, X₀, hX₀, ⟨eX⟩⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc
      (Over.mk f) hfp
  let _ : LocallyOfFinitePresentation X₀.hom := hX₀.1
  let _ : QuasiCompact X₀.hom := hX₀.2.1
  let _ : QuasiSeparated X₀.hom := hX₀.2.2
  let _ : CompactSpace X₀.left := (quasiCompact_iff_compactSpace X₀.hom).mp inferInstance
  let _ : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  let e₀ : Over.mk f ≅ Over.mk (pullback.fst (c.π.app i) X₀.hom) :=
    eX ≪≫ Over.isoMk (pullbackSymmetry X₀.hom (c.π.app i))
      (by exact pullbackSymmetry_hom_comp_fst X₀.hom (c.π.app i))
  let a₀ := e₀.hom.left ≫ pullback.snd (c.π.app i) X₀.hom
  have sq₀ : IsPullback f a₀ (c.π.app i) X₀.hom := IsPullback.of_over_iso e₀
  obtain ⟨j, ej, hj⟩ := exists_isProper_pullback_snd D c hc i X₀.hom f hf a₀ sq₀
  let g₁ := pullback.snd X₀.hom (D.map ej)
  let _ : IsProper g₁ := hj
  obtain ⟨a₁, sq₁⟩ := isPullback_stage_lift D c ej X₀.hom f a₀ sq₀
  obtain ⟨k, ek, hk⟩ := exists_stage_fiber_dim_le D c hc j g₁ f a₁ sq₁ d hd
  obtain ⟨a₂, sq₂⟩ := isPullback_stage_lift D c ek g₁ f a₁ sq₁
  let _ : IsAffineHom (c.π.app k) :=
    AlgebraicGeometry.EventualLimit.isAffineHom_π_app D c hc k
  let _ : IsAffineHom a₂ := MorphismProperty.of_isPullback sq₂ inferInstance
  exact ⟨_, D.obj k, a₂ ≫ (pullbackSymmetry g₁ (D.map ek)).hom,
    pullback.fst (D.map ek) g₁, inferInstance, inferInstance, inferInstance, inferInstance, hk⟩

/-- **The model over a Noetherian base, for an affine base.**
`exists_isProper_isLocallyNoetherian_model_of_isLimit` at the presentation
`AlgebraicGeometry.affineStageCone` of `Y` as the inverse limit of the spectra of the finitely
generated subalgebras of `Γ(Y, ⊤)`, whose vertex is `Y` itself and whose stages are affine and
Noetherian. -/
theorem exists_isProper_isLocallyNoetherian_model {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    (hf : IsProper f) (hfp : FinitePresentation f) (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ (T S : Scheme.{u}) (a : X ⟶ T) (g : T ⟶ S),
      IsAffine S ∧ IsLocallyNoetherian S ∧ IsAffineHom a ∧ IsProper g ∧
      (∀ s : S, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) :=
  exists_isProper_isLocallyNoetherian_model_of_isLimit
    (specAdjoinFinsetDiagram (Γ(Y, ⊤) : Type u)) (affineStageCone Y)
    (isLimit_affineStageCone Y) f hf hfp d hd

/-! ### The vanishing -/

/-- **Restriction of scalars reflects zero objects**, because it does not change the carrier of a
module: both sides are zero exactly when that carrier is a subsingleton. -/
theorem isZero_of_isZero_restrictScalars {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat.{u} S)
    (h : IsZero ((ModuleCat.restrictScalars φ.hom).obj M)) : IsZero M :=
  have hs : Subsingleton ↥((ModuleCat.restrictScalars φ.hom).obj M) :=
    ModuleCat.isZero_iff_subsingleton.mp h
  ModuleCat.isZero_iff_subsingleton.mpr hs

/-- **Cohomology vanishes where the cohomology of an affine direct image does**, because the two
agree up to restriction of scalars by [Stacks, Tag 089W]. -/
theorem isZero_rightDerivedPlus_of_isZero_pushforward {X T : Scheme.{u}} (a : X ⟶ T)
    [IsAffineHom a] (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
    (h : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerivedPlus
      (q : ℤ)).obj ((Scheme.Modules.pushforward a).obj F))) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus
      (q : ℤ)).obj F) :=
  (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Stacks.Cohomology.AffineBase.moduleGlobalSections X) q F).1
    (isZero_of_isZero_restrictScalars a.appTop _
      (IsZero.of_iso
        ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
          (Stacks.Cohomology.AffineBase.moduleGlobalSections T) q _).2 h)
        (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward a F q)))

/-- Vanishing above `d` for `F` follows from that of its affine direct image above `d`. -/
private theorem isZero_rightDerivedPlus_of_pushforward_vanishing {X T : Scheme.{u}} (a : X ⟶ T)
    [IsAffineHom a] (d : ℕ) (F : X.Modules) (hF : F.IsQuasicoherent)
    (h : ∀ q : ℕ, d < q → ((Scheme.Modules.pushforward a).obj F).IsQuasicoherent →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerivedPlus
        (q : ℤ)).obj ((Scheme.Modules.pushforward a).obj F)))
    (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus i).obj F) := by
  have _ := hF
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ i by omega)
  exact isZero_rightDerivedPlus_of_isZero_pushforward a F q
    (h q (by omega) (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom a F hF))

/-- **Vanishing above the fibre dimension, for a proper morphism of finite presentation onto an
arbitrary affine base.** `exists_isProper_isLocallyNoetherian_model` replaces the pair `(X, F)`
by its model `(T, a_* F)` over an affine Noetherian base, whose cohomology is the same by
[Stacks, Tag 089W] — the comparison morphism `a` being affine — and whose direct image `a_* F` is
quasi-coherent for the same reason; the vanishing over the Noetherian base is
`FibreDimension.isZero_rightDerivedPlus_moduleGlobalSections_of_affine_base_of_isQuasicoherent`. -/
theorem isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_finitePresentation
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [IsProper f] (hf : FinitePresentation f)
    (d : ℕ) (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (i : ℤ) (hi : (d : ℤ) < i) (F : X.Modules) (hF : F.IsQuasicoherent) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus i).obj F) := by
  obtain ⟨T, S, a, g, haff, hnoeth, ha, hg, hdim⟩ :=
    exists_isProper_isLocallyNoetherian_model f ‹IsProper f› hf d hd
  let _ := haff
  let _ := hnoeth
  let _ := ha
  let _ := hg
  refine isZero_rightDerivedPlus_of_pushforward_vanishing a d F hF (fun q hq hqc => ?_) i hi
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated g
  exact
    FibreDimension.isZero_rightDerivedPlus_moduleGlobalSections_of_affine_base_of_isQuasicoherent
      g hdim _ (p := q) hq

/-- **Vanishing above the fibre dimension over an arbitrary affine base.** For `f : X ⟶ Y` proper
onto an affine scheme — with no Noetherian hypothesis — all of whose fibres have topological
Krull dimension at most `d`, and `F` quasi-coherent, `Hⁱ(X, F) = 0` for every `i > d`.

`exists_isClosedImmersion_isProper_finitePresentation_fiber_dim_le` replaces `(X, F)` by a model
`(T, a_* F)` with `T ⟶ Y` proper of finite presentation and `a` a closed immersion, hence affine;
[Stacks, Tag 089W] identifies the two cohomologies and
`isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_finitePresentation` concludes. -/
theorem isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_affineBase
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [IsProper f]
    (d : ℕ) (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (i : ℤ) (hi : (d : ℤ) < i) (F : X.Modules) (hF : F.IsQuasicoherent) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus i).obj F) := by
  obtain ⟨T, g, a, hg, hfp, ha, _, hdim⟩ :=
    exists_isClosedImmersion_isProper_finitePresentation_fiber_dim_le f d hd
  let _ := hg
  let _ := ha
  refine isZero_rightDerivedPlus_of_pushforward_vanishing a d F hF (fun q hq hqc => ?_) i hi
  exact isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_finitePresentation g hfp d hdim
    (q : ℤ) (by exact_mod_cast hq) _ hqc

/-- **The hypothesis `hcoh` of [Stacks, Tag 0E7D], discharged.** A proper morphism onto an affine
scheme all of whose fibres have dimension at most `d` has vanishing cohomology of quasi-coherent
modules above `d`.

This is the shape the hypothesis of
`exists_isAffineOpen_vanishing_of_cohomology_vanishing` and of
`isZero_stalk_rightDerivedPlus_of_cohomology_vanishing` is written in, so it can be supplied to
either of them directly. -/
theorem cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le (d : ℕ) :
    ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X₀).rightDerivedPlus i).obj
          F) :=
  fun g _ _ hfib i hi F hF =>
    isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_affineBase g d hfib i hi F hF

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end

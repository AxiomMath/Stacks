module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssSurjSquareStepBridged
public import
    StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectEssSurjSquare

/-!
# Moving the inductive hypotheses of Stacks 09RJ to the stage the comparison was found at

`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjSquareStepBridged.lean` is the
elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ.  It is run
at a stage `W` of the system and needs the two inductive hypotheses `αU`, `αV` **at that stage**,
while `AlgebraicGeometry.Space.exists_interStageIso_projHom_of_isColim` of the module
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjectsUnconditionalInterComparison`
produces the comparison isomorphism `c` at a stage of its own choosing.  This is the source's
"after increasing `i` we can find an isomorphism": the inductive hypotheses have to be carried to
the stage the comparison was found at, and because `AlgebraicGeometry.Space.edsBridgeFst` is
*built from* `αU`, carrying `αU` changes it and the change has to be shown to cancel.

**This file is the geometry and the algebra of that move.**  It identifies the two restrictions of
the descended object at two stages with its single restriction along the projection `s` of the
limit to the base stage, states the pasting coherence of the faces of the cube that the
cancellation rests on, and provides every respelling and every piece of free-category algebra the
cancellation needs.  What it does **not** yet contain is the cancellation itself; see "What is not
here", which records three arrangements and why each exceeds the budget.

## The shape of the move, and why no transition morphism is needed

In the geometry of Situation 09RH at the square, a stage is a triple `(p, q, q')` — a morphism
`p : W ⟶ W₀`, the transition `q : W ⟶ W_b` to the base stage with `q ≫ p_b = p`, and the
projection `q' : W' ⟶ W` from the limit with `q' ≫ p = p'` — factoring the *fixed* projection
`s : W' ⟶ W_b`, `s = q' ≫ q`.  The base stage `p_b`, the limit `p'`, the projection `s` and the
two descended objects `A_b`, `Bo_b` are the same at every stage; only the triple varies.

So the move is between two such triples **over the same `s`**, and it needs no morphism between
the two stages and no comparison of the two factorisations: both restrictions of `A_b` are
compared with the single restriction along `s`, by the composition comparison of the
pseudofunctoriality datum.  That is a correction to the expectation that the move is a transport
along a transition morphism of the system — the transition morphism exists in the application, but
nothing below uses it, and in particular the two stages need not be comparable in the index.

## Main definitions

* `AlgebraicGeometry.Space.edsTransitionOpenComp` and `…edsTransitionEtaleComp`: the composition
  comparison identifying the restriction to the limit of the object at the stage with the
  restriction of the object at the base stage along `s`, over the open subspace and over the étale
  algebraic space.  **Composed with the inverse of the same comparison at another stage this is the
  move itself**: it carries an inductive hypothesis from one stage to another.
* `AlgebraicGeometry.Space.edsTransitionOpenSquare` and `…edsTransitionEtaleSquare`: the square
  isomorphisms of the faces of the cube over `s`.  These are the **stage-independent** factors:
  they mention `p_b`, `p'` and `s` and not the stage at all.

## Main results

* `AlgebraicGeometry.Space.edsTransitionOpenSquare_prism` and `…edsTransitionEtaleSquare_prism`:
  **the pasting coherence the cancellation rests on.**  The faces of the cube over `q` and over
  `q'` paste to the face over `s`; this is
  `AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism` at the prism of the
  intersections over the open subspaces, respectively over the étale algebraic spaces, of the
  square over `W'`, over `W` and over `W_b`.  Composed with the derived pullback of the inductive
  hypothesis along `edsFst`, respectively `edsSnd`, this says that `α` and `β` factor through the
  stage-independent square isomorphism over `s`, with everything stage-dependent collected into
  the one factor `AlgebraicGeometry.Space.edsTransitionOpenComp`, respectively
  `…edsTransitionEtaleComp` — and the invariance is read off that factorisation by
  `AlgebraicGeometry.Space.edsTransitionConj₄` and `…edsTransitionNormalise₄`.
* The nine crossings between the prism's spelling of a component of a natural isomorphism and the
  bridge's, one per declaration: `AlgebraicGeometry.Space.edsBridgeOpenSquare_inv_eq`,
  `…edsBridgeEtaleSquare_inv_eq`, `…edsBridgeEtaleSquare'_hom`,
  `…edsTransitionOpenSquare_hom_eq`, `…edsTransitionEtaleSquare_hom_eq`,
  `…edsBridgeInterComp_hom_eq_open`, `…edsBridgeInterComp_hom_eq_etale`,
  `…edsTransitionOpenComp_hom_eq`, `…edsTransitionEtaleComp_hom_eq`, and the four of them read at
  an isomorphism rather than at a morphism (`…edsBridgeOpenSquare_mapIso_inv_eq`,
  `…edsBridgeEtaleSquare_mapIso_inv_eq`, `…edsTransitionOpenComp_mapIso_hom_eq`,
  `…edsTransitionEtaleComp_mapIso_hom_eq`).
* `AlgebraicGeometry.Space.edsTransitionConj₄`, `…edsTransitionConj₅`,
  `…edsTransitionNormalise₄`, `…edsTransitionNormalise₅`, `…edsTransitionCompInvCongr` and
  `AlgebraicGeometry.Space.eq_comp₃_comp₂_congr`: **the whole algebra of the cancellation**, for
  free isomorphisms of a free category.  Together they say: a conjugate whose first three factors
  compose to an isomorphism `Θ` is `Θ` followed by the rest (`…Conj₄`, `…Conj₅`), and the normal
  form does not see which of two isomorphisms with a common target was used (`…Normalise₄`,
  `…Normalise₅`), which is the invariance.

## The hypotheses carried, and why each is an input rather than part of the conclusion

*`hsq`, `pb`, `p`, `p'`, `q`, `q'`, `hq`, `hq'`, `s`, `hs`, `hsp`: the geometry of Situation 09RH
at the square, at one stage.*  The triple `(p, q, q')` factors `s`, and `hs` is that
factorisation, which in Situation 09RH is the composition law of the system at the index.  `s` is
an argument rather than the composite for the reason recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectDescentBridgeOverlap.lean`.  A second
stage is an instantiation of the same declarations at a second triple over the same `s`, so no
declaration below carries two.

*`Ab`, `Bb`: the two objects descended at the base stage.*  Unchanged from
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom`.

No `Prop` binder stands in for missing mathematics, and no coherence of the pseudofunctoriality
datum is assumed: the one coherence used,
`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism`, is a theorem about the
structure's own fields.

## What is not here

*The cancellation, and so the invariance of `AlgebraicGeometry.Space.edsBridgeFst` and
`…edsBridgeSnd` and the square step with its data at two stages.*  Every ingredient is above and
the mathematics is settled — the pasting coherence, the stage-independent factor, the nine
crossings and the algebra — but assembling them needs the prism **restated in the spelling of the
bridge**, and that restatement does not pass the kernel.  The costs are as follows:

* the prism at the arguments of the square in its own spelling (the components of the natural
  isomorphisms, `e.hom.app M`) costs **48,027** heartbeats on the open side and **48,038** on the
  étale side;
* each crossing into the bridge's spelling (`(e.app M).hom`), stated **with its natural
  isomorphism and its object written out** and proved by `CategoryTheory.Iso.app_hom` or
  `…Iso.app_inv` alone, costs between **46,363** and **54,763**, of which about 45,000 is the
  elaboration of this file's `variable` block;
* **the prism restated in the bridge's spelling does not pass the kernel.**  Each of three
  arrangements ends in `error: (kernel) deterministic timeout`: proving the
  restatement by `AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism` directly
  (**over 200,000**, the elaborator timing out first, at `whnf` on the open side and at `isDefEq`
  on the étale side); assembling it from the nine crossings by
  `AlgebraicGeometry.Space.eq_comp₃_comp₂_congr`, so that no declaration crosses more than one
  component (**2,460,000** / **2,455,478**); and the same by `simpa only` with the nine crossings
  as the simp set (**2,405,696** / **2,403,351**).  The last two reach the kernel with the
  elaboration done, so the obstruction is the kernel's check of one `isDefEq` between two
  composites of comparisons of total left derived functors that differ at five objects, each by
  one
  `CategoryTheory.Functor.comp_obj`.  The cost is not the sum of the five: a single check that
  differs in five places explores far more than five that differ in one, and there is no
  arrangement in which fewer than one check carries all five, because the objects of an equation
  are tied together by its type.

  With that restatement in hand the rest is immediate: the factorisation of `α` costs **81,460**
  and of `β` **89,647**, the invariance
  **157,927** and **188,431**, and the square step with its data at two stages **62,611**.

*The induction of Stacks 08GP and the affine base case.*  Running the induction needs, besides the
square step, the base change of Situation 09RH along an arbitrary quasi-compact quasi-separated
algebraic space étale over `X₀`, the colimit statement of Stacks 09RI for the resulting system of
intersections, and the transport of the affine base case to the chart; none is assumed below.

*Stacks 09RI.*  Nothing below mentions a system, a colimit or a
`AlgebraicGeometry.Space.DescentSituation.RingModel`.

## Implementation notes

The coherence used is the horizontal pasting of two square isomorphisms,
`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism`.  The cube identity
`…squareIso_cube` is *not* needed: the two sides of the invariance differ along one of the two
members of the square at a time.

Every crossing between the prism's spelling and the bridge's is its own declaration, with its
natural isomorphism and its object written out, for the reason recorded in the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjSquareStepBridged.lean`; and
the crossings are stated **with the bridge's side first**, so that the equation's type — and with
it the spelling of every object it mentions — is the bridge's.  The four `…mapIso…` crossings
restate four of the others with the derived pullback written as
`CategoryTheory.Functor.mapIso`, so that the head of the bridge side is `CategoryTheory.Iso.inv`
or `…Iso.hom` and the matching that determines an implicit isomorphism is first-order.

All the algebra is stated at free isomorphisms of a free category, so that no composite of
comparisons of total left derived functors is ever traversed; the measurements above are what
forced that, and `AlgebraicGeometry.Space.edsTransitionConj₄` takes its hypothesis in the
bridge's spelling for the same reason — with the hypothesis in the prism's spelling and the six
isomorphisms left to unification the kernel again does not finish.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Lemma 75.9.1 (Tag 08GN)](https://stacks.math.columbia.edu/tag/08GN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

/-! ### The algebra, at free isomorphisms of a free category

The four declarations of this section are about free isomorphisms of a free category.  They are
stated and named rather than inlined for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectDescentBridgeOverlap.lean`: the
isomorphisms they are applied to are composites of comparisons of total left derived functors, and
an application of a named identity costs a head unification where the same step taken by `rw` or
`simp` on the terms themselves sends the elaborator into the unfolding of those functors.

The first two take the hypothesis in the spelling of the bridge — its factors written as
`CategoryTheory.Iso.inv` and `…Iso.hom` of the very isomorphisms in question — because with the
hypothesis in the prism's spelling and the six isomorphisms left to unification the kernel does
not finish; see "Implementation notes".  Getting the pasting coherence into that spelling is what
the crossings of the last two sections are for. -/

/-- **A fourfold conjugate factors through any isomorphism its first three factors compose to.**
Applied to `AlgebraicGeometry.Space.edsBridgeFst`, with the pasting coherence
`AlgebraicGeometry.Space.edsTransitionOpenSquare_prism` as its hypothesis, this says that `α`
factors through the square isomorphism over `s`. -/
theorem edsTransitionConj₄ {C : Type*} [Category C] {X₁ X₂ Z₁ A₁ T K : C}
    (iA : X₁ ≅ X₂) (mA : X₁ ≅ Z₁) (k₁ : Z₁ ≅ A₁) (k₂ : A₁ ≅ T) (Θ : X₂ ≅ K) (g : A₁ ≅ K)
    (h : mA.inv ≫ iA.hom ≫ Θ.hom = k₁.hom ≫ g.hom) :
    edsBridgeConj₄ iA mA k₁ k₂ = Θ ≪≫ g.symm ≪≫ k₂ := by
  have hk : k₁.hom = mA.inv ≫ iA.hom ≫ Θ.hom ≫ g.inv := by simp [reassoc_of% h]
  refine Iso.ext ?_
  simp only [edsBridgeConj₄, Iso.trans_hom, Iso.symm_hom, Category.assoc, hk]
  simp

/-- **A fivefold conjugate factors through any isomorphism its first three factors compose to.**
The same for `AlgebraicGeometry.Space.edsBridgeSnd`, which has one factor more. -/
theorem edsTransitionConj₅ {C : Type*} [Category C] {X₁ X₂ Z₁ A₁ A₂ T K : C}
    (iA : X₁ ≅ X₂) (mA : X₁ ≅ Z₁) (k₁ : Z₁ ≅ A₁) (k₂ : A₁ ≅ A₂) (k₃ : A₂ ≅ T) (Θ : X₂ ≅ K)
    (g : A₁ ≅ K) (h : mA.inv ≫ iA.hom ≫ Θ.hom = k₁.hom ≫ g.hom) :
    edsBridgeConj₅ iA mA k₁ k₂ k₃ = Θ ≪≫ g.symm ≪≫ k₂ ≪≫ k₃ :=
  edsTransitionConj₄ iA mA k₁ (k₂ ≪≫ k₃) Θ g h

/-- **Rewriting all five factors of an equation between a threefold and a twofold composite.**
Every variable is free, and the five equations come **before** the equation being rewritten, so
that the conclusion is in their spelling: that is how the prism is restated in the spelling of the
bridge without any one declaration having to cross more than it already carries. -/
theorem eq_comp₃_comp₂_congr {T : Type*} [Category T] {a b c d e : T}
    {f₁ f₁' : a ⟶ b} {f₂ f₂' : b ⟶ c} {f₃ f₃' : c ⟶ d} {g₁ g₁' : a ⟶ e} {g₂ g₂' : e ⟶ d}
    (h₁ : f₁ = f₁') (h₂ : f₂ = f₂') (h₃ : f₃ = f₃') (h₄ : g₁ = g₁') (h₅ : g₂ = g₂')
    (h : f₁' ≫ f₂' ≫ f₃' = g₁' ≫ g₂') :
    f₁ ≫ f₂ ≫ f₃ = g₁ ≫ g₂ := by
  rw [h₁, h₂, h₃, h₄, h₅]
  exact h

/-- **The normal form does not see which of two isomorphisms with a common target was used.**  The
two copies of the first one cancel.  This is the algebra of the invariance of
`AlgebraicGeometry.Space.edsBridgeFst` under the move between stages: the two isomorphisms are
`AlgebraicGeometry.Space.edsTransitionOpenComp` at the two stages. -/
theorem edsTransitionNormalise₄ {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A A₁ M T : C} {X : D} (Θ : X ≅ F.obj M) (g : A ≅ M) (g₁ : A₁ ≅ M) (κ : A₁ ≅ T) :
    Θ ≪≫ (F.mapIso g).symm ≪≫ F.mapIso (g ≪≫ g₁.symm ≪≫ κ) =
      Θ ≪≫ (F.mapIso g₁).symm ≪≫ F.mapIso κ := by
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.map_comp]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  simp

/-- `AlgebraicGeometry.Space.edsTransitionNormalise₄` with one more factor after the carried
isomorphism, which is the shape `AlgebraicGeometry.Space.edsBridgeSnd` has. -/
theorem edsTransitionNormalise₅ {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A A₁ M T : C} {X Y : D} (Θ : X ≅ F.obj M) (g : A ≅ M) (g₁ : A₁ ≅ M) (κ : A₁ ≅ T)
    (k₃ : F.obj T ≅ Y) :
    Θ ≪≫ (F.mapIso g).symm ≪≫ F.mapIso (g ≪≫ g₁.symm ≪≫ κ) ≪≫ k₃ =
      Θ ≪≫ (F.mapIso g₁).symm ≪≫ F.mapIso κ ≪≫ k₃ := by
  simpa only [Iso.trans_assoc] using
    congrArg (· ≪≫ k₃) (edsTransitionNormalise₄ F Θ g g₁ κ)

/-- Equal isomorphisms have equal `α ∘ β⁻¹`.  Stated at free isomorphisms so that the invariance
can be read on the right-hand side of the square step's `hfac` — the only place where `α` and `β`
are consumed — without the composite being traversed. -/
theorem edsTransitionCompInvCongr {C : Type*} [Category C] {X Y Z : C} {a a' : X ≅ Z}
    {b b' : Y ≅ Z} (ha : a = a') (hb : b = b') : a.hom ≫ b.inv = a'.hom ≫ b'.inv := by
  rw [ha, hb]

/-! ### The geometry of one stage

Everything below is stated for **one** stage `(p, q, q')` factoring the projection `s`.  That is
all the geometry the move needs: the move between two stages is the composite of the comparison
for one with the inverse of the comparison for the other, and nothing below has to see both at
once. -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {Wb W W' : AlgebraicSpaces B S hS} (pb : Wb ⟶ W₀) (p : W ⟶ W₀) (p' : W' ⟶ W₀)
  (q : W ⟶ Wb) (q' : W' ⟶ W) (hq : q ≫ pb = p) (hq' : q' ≫ p = p')
  (s : W' ⟶ Wb) (hs : s = q' ≫ q) (hsp : s ≫ pb = p')
  (Ab : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsOpen B S hS (edsPreimage hsq pb)))))
  (Bb : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsEtale B S hS (edsPreimage hsq pb)))))

/-! ### The stage-independent square isomorphisms over `s` -/

/-- **The square isomorphism of the face of the cube over `s` through the open subspace**:
`Ls_P^*(A_b|_{P_b}) ≅ (Ls_U^*A_b)|_{P'}`.  It depends on the base stage, on the limit and on the
projection `s`, and **not on the stage** the square step is run at: it is the normal form
`AlgebraicGeometry.Space.edsBridgeFst` factors through. -/
def edsTransitionOpenSquare :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p' s hsp)).obj
        (edsBridgeInterOpenObj hsq pb Ab) ≅
      (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p'))).obj
        ((smallEtaleDerivedModulePullback B S hS
          (edsPreimageOpenMap hsq pb p' s hsp)).obj Ab) :=
  ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq pb p' s hsp)
    (edsPreimageInterMap hsq pb p' s hsp) (edsFst B S hS (edsPreimage hsq pb))
    (edsFst_comp_edsPreimageOpenMap hsq pb p' s hsp)).app Ab

/-- **The square isomorphism of the face of the cube over `s` through the étale algebraic
space.**  The normal form `AlgebraicGeometry.Space.edsBridgeSnd` factors through; it does not
depend on the stage. -/
def edsTransitionEtaleSquare :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p' s hsp)).obj
        (edsBridgeInterEtaleObj hsq pb Bb) ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p'))).obj
        ((smallEtaleDerivedModulePullback B S hS
          (edsPreimageEtaleMap hsq pb p' s hsp)).obj Bb) :=
  ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq pb p' s hsp)
    (edsPreimageInterMap hsq pb p' s hsp) (edsSnd B S hS (edsPreimage hsq pb))
    (edsSnd_comp_edsPreimageEtaleMap hsq pb p' s hsp)).app Bb

/-! ### The composition comparisons that carry an inductive hypothesis between stages -/

/-- **The composition comparison of the factorisation `r_U ≫ t_U = s_U` of the maps of open
subspaces**: the restriction to the limit of the object at the stage is the restriction of the
object at the base stage along `s`.  Composed with the inverse of the same comparison for another
stage, this is the move that carries the inductive hypothesis `αU` from one stage to another. -/
def edsTransitionOpenComp :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq p p' q' hq')).obj
        (edsBridgeOpenObj hsq pb p q hq Ab) ≅
      (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq pb p' s hsp)).obj Ab :=
  ((DerivedPullbackComposition.canonical B S hS).iso
    (edsPreimageOpenMap hsq p p' q' hq') (edsPreimageOpenMap hsq pb p q hq)
    (edsPreimageOpenMap hsq pb p' s hsp)
    (edsPreimageOpenMap_comp_edsPreimageOpenMap hsq pb p p' q q' hq hq' s hs hsp)).app Ab

/-- **The composition comparison of the factorisation `r_V ≫ t_V = s_V` of the maps of étale
algebraic spaces.**  The move that carries the inductive hypothesis `αV` between stages. -/
def edsTransitionEtaleComp :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq p p' q' hq')).obj
        (edsBridgeEtaleObj hsq pb p q hq Bb) ≅
      (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq pb p' s hsp)).obj Bb :=
  ((DerivedPullbackComposition.canonical B S hS).iso
    (edsPreimageEtaleMap hsq p p' q' hq') (edsPreimageEtaleMap hsq pb p q hq)
    (edsPreimageEtaleMap hsq pb p' s hsp)
    (edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq pb p p' q q' hq hq' s hs hsp)).app Bb

/-! ### The prism identities, in the prism's own spelling -/

/-- **The two faces of the cube over `q` and over `q'` through the open subspace paste to the face
over `s`.**  This is `AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism` for the
prism of the intersections over the open subspaces of the square over `W'`, over `W` and over
`W_b`.  It is stated in the prism's own spelling — the components of the natural isomorphisms —
and the five crossings into the spelling of the bridge are the declarations below. -/
theorem edsTransitionOpenSquare_prism :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).map
          (((DerivedPullbackComposition.canonical B S hS).squareIso
            (edsFst B S hS (edsPreimage hsq p)) (edsPreimageOpenMap hsq pb p q hq)
            (edsPreimageInterMap hsq pb p q hq) (edsFst B S hS (edsPreimage hsq pb))
            (edsFst_comp_edsPreimageOpenMap hsq pb p q hq)).inv.app Ab) ≫
        ((DerivedPullbackComposition.canonical B S hS).iso
            (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
            (edsPreimageInterMap hsq pb p' s hsp)
            (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s
              hs hsp)).hom.app
          ((smallEtaleDerivedModulePullback B S hS
            (edsFst B S hS (edsPreimage hsq pb))).obj Ab) ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso
            (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq pb p' s hsp)
            (edsPreimageInterMap hsq pb p' s hsp) (edsFst B S hS (edsPreimage hsq pb))
            (edsFst_comp_edsPreimageOpenMap hsq pb p' s hsp)).hom.app Ab =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq p p' q' hq')
          (edsPreimageInterMap hsq p p' q' hq') (edsFst B S hS (edsPreimage hsq p))
          (edsFst_comp_edsPreimageOpenMap hsq p p' q' hq')).hom.app
        ((smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq pb p q hq)).obj Ab) ≫
      (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p'))).map
        (((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageOpenMap hsq p p' q' hq') (edsPreimageOpenMap hsq pb p q hq)
          (edsPreimageOpenMap hsq pb p' s hsp)
          (edsPreimageOpenMap_comp_edsPreimageOpenMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app Ab) :=
  (DerivedPullbackComposition.canonical B S hS).squareIso_prism
    (edsFst B S hS (edsPreimage hsq p')) (edsFst B S hS (edsPreimage hsq p))
    (edsFst B S hS (edsPreimage hsq pb))
    (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p' s hsp)
    (edsPreimageOpenMap hsq p p' q' hq') (edsPreimageOpenMap hsq pb p q hq)
    (edsPreimageOpenMap hsq pb p' s hsp)
    (edsFst_comp_edsPreimageOpenMap hsq p p' q' hq')
    (edsFst_comp_edsPreimageOpenMap hsq pb p q hq)
    (edsFst_comp_edsPreimageOpenMap hsq pb p' s hsp)
    (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s hs hsp)
    (edsPreimageOpenMap_comp_edsPreimageOpenMap hsq pb p p' q q' hq hq' s hs hsp) Ab

/-- **The two faces of the cube over `q` and over `q'` through the étale algebraic space paste to
the face over `s`**, in the prism's own spelling. -/
theorem edsTransitionEtaleSquare_prism :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).map
          (((DerivedPullbackComposition.canonical B S hS).squareIso
            (edsSnd B S hS (edsPreimage hsq p)) (edsPreimageEtaleMap hsq pb p q hq)
            (edsPreimageInterMap hsq pb p q hq) (edsSnd B S hS (edsPreimage hsq pb))
            (edsSnd_comp_edsPreimageEtaleMap hsq pb p q hq)).inv.app Bb) ≫
        ((DerivedPullbackComposition.canonical B S hS).iso
            (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
            (edsPreimageInterMap hsq pb p' s hsp)
            (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s
              hs hsp)).hom.app
          ((smallEtaleDerivedModulePullback B S hS
            (edsSnd B S hS (edsPreimage hsq pb))).obj Bb) ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso
            (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq pb p' s hsp)
            (edsPreimageInterMap hsq pb p' s hsp) (edsSnd B S hS (edsPreimage hsq pb))
            (edsSnd_comp_edsPreimageEtaleMap hsq pb p' s hsp)).hom.app Bb =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q' hq')
          (edsPreimageInterMap hsq p p' q' hq') (edsSnd B S hS (edsPreimage hsq p))
          (edsSnd_comp_edsPreimageEtaleMap hsq p p' q' hq')).hom.app
        ((smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq pb p q hq)).obj Bb) ≫
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p'))).map
        (((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageEtaleMap hsq p p' q' hq') (edsPreimageEtaleMap hsq pb p q hq)
          (edsPreimageEtaleMap hsq pb p' s hsp)
          (edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app Bb) :=
  (DerivedPullbackComposition.canonical B S hS).squareIso_prism
    (edsSnd B S hS (edsPreimage hsq p')) (edsSnd B S hS (edsPreimage hsq p))
    (edsSnd B S hS (edsPreimage hsq pb))
    (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p' s hsp)
    (edsPreimageEtaleMap hsq p p' q' hq') (edsPreimageEtaleMap hsq pb p q hq)
    (edsPreimageEtaleMap hsq pb p' s hsp)
    (edsSnd_comp_edsPreimageEtaleMap hsq p p' q' hq')
    (edsSnd_comp_edsPreimageEtaleMap hsq pb p q hq)
    (edsSnd_comp_edsPreimageEtaleMap hsq pb p' s hsp)
    (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s hs hsp)
    (edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq pb p p' q q' hq hq' s hs hsp) Bb

/-! ### The crossings between the two spellings, one per declaration

Each of these is `CategoryTheory.Iso.app_hom` or `CategoryTheory.Iso.app_inv` with its natural
isomorphism and its object written out.  **The spelling of the bridge is written first**, so that
the equation's type — and with it the spelling of every object it mentions — is the bridge's; the
crossing of the objects is then carried by the same declaration as the crossing of the
component.  `AlgebraicGeometry.Space.edsBridgeOpenSquare'_hom` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjSquareStepBridged.lean` is
already in that form and is reused rather than restated. -/

/-- The crossing for `AlgebraicGeometry.Space.edsBridgeOpenSquare`, on inverses. -/
theorem edsBridgeOpenSquare_inv_eq :
    (edsBridgeOpenSquare hsq pb p q hq Ab).inv =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsFst B S hS (edsPreimage hsq p)) (edsPreimageOpenMap hsq pb p q hq)
          (edsPreimageInterMap hsq pb p q hq) (edsFst B S hS (edsPreimage hsq pb))
          (edsFst_comp_edsPreimageOpenMap hsq pb p q hq)).inv.app Ab :=
  Iso.app_inv ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsFst B S hS (edsPreimage hsq p)) (edsPreimageOpenMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p q hq) (edsFst B S hS (edsPreimage hsq pb))
    (edsFst_comp_edsPreimageOpenMap hsq pb p q hq)) Ab

/-- The crossing for `AlgebraicGeometry.Space.edsBridgeEtaleSquare`, on inverses. -/
theorem edsBridgeEtaleSquare_inv_eq :
    (edsBridgeEtaleSquare hsq pb p q hq Bb).inv =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p)) (edsPreimageEtaleMap hsq pb p q hq)
          (edsPreimageInterMap hsq pb p q hq) (edsSnd B S hS (edsPreimage hsq pb))
          (edsSnd_comp_edsPreimageEtaleMap hsq pb p q hq)).inv.app Bb :=
  Iso.app_inv ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p)) (edsPreimageEtaleMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p q hq) (edsSnd B S hS (edsPreimage hsq pb))
    (edsSnd_comp_edsPreimageEtaleMap hsq pb p q hq)) Bb

/-- The crossing for `AlgebraicGeometry.Space.edsBridgeEtaleSquare'`, on homs.  Only the inverse
is in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjSquareStepBridged.lean`. -/
theorem edsBridgeEtaleSquare'_hom :
    (edsBridgeEtaleSquare' hsq pb p p' q q' hq hq' Bb).hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q' hq')
          (edsPreimageInterMap hsq p p' q' hq') (edsSnd B S hS (edsPreimage hsq p))
          (edsSnd_comp_edsPreimageEtaleMap hsq p p' q' hq')).hom.app
        (edsBridgeEtaleObj hsq pb p q hq Bb) :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q' hq')
    (edsPreimageInterMap hsq p p' q' hq') (edsSnd B S hS (edsPreimage hsq p))
    (edsSnd_comp_edsPreimageEtaleMap hsq p p' q' hq'))
    (edsBridgeEtaleObj hsq pb p q hq Bb)

/-- The crossing for `AlgebraicGeometry.Space.edsTransitionOpenSquare`. -/
theorem edsTransitionOpenSquare_hom_eq :
    (edsTransitionOpenSquare hsq pb p' s hsp Ab).hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq pb p' s hsp)
          (edsPreimageInterMap hsq pb p' s hsp) (edsFst B S hS (edsPreimage hsq pb))
          (edsFst_comp_edsPreimageOpenMap hsq pb p' s hsp)).hom.app Ab :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq pb p' s hsp)
    (edsPreimageInterMap hsq pb p' s hsp) (edsFst B S hS (edsPreimage hsq pb))
    (edsFst_comp_edsPreimageOpenMap hsq pb p' s hsp)) Ab

/-- The crossing for `AlgebraicGeometry.Space.edsTransitionEtaleSquare`. -/
theorem edsTransitionEtaleSquare_hom_eq :
    (edsTransitionEtaleSquare hsq pb p' s hsp Bb).hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq pb p' s hsp)
          (edsPreimageInterMap hsq pb p' s hsp) (edsSnd B S hS (edsPreimage hsq pb))
          (edsSnd_comp_edsPreimageEtaleMap hsq pb p' s hsp)).hom.app Bb :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq pb p' s hsp)
    (edsPreimageInterMap hsq pb p' s hsp) (edsSnd B S hS (edsPreimage hsq pb))
    (edsSnd_comp_edsPreimageEtaleMap hsq pb p' s hsp)) Bb

/-- The crossing for `AlgebraicGeometry.Space.edsBridgeInterComp` at the object over the open
subspace. -/
theorem edsBridgeInterComp_hom_eq_open :
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
        (edsBridgeInterOpenObj hsq pb Ab)).hom =
      ((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
          (edsPreimageInterMap hsq pb p' s hsp)
          (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app (edsBridgeInterOpenObj hsq pb Ab) :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).iso
    (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p' s hsp)
    (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s hs hsp))
    (edsBridgeInterOpenObj hsq pb Ab)

/-- The crossing for `AlgebraicGeometry.Space.edsBridgeInterComp` at the object over the étale
algebraic space. -/
theorem edsBridgeInterComp_hom_eq_etale :
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
        (edsBridgeInterEtaleObj hsq pb Bb)).hom =
      ((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
          (edsPreimageInterMap hsq pb p' s hsp)
          (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app (edsBridgeInterEtaleObj hsq pb Bb) :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).iso
    (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p' s hsp)
    (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s hs hsp))
    (edsBridgeInterEtaleObj hsq pb Bb)

/-- The crossing for `AlgebraicGeometry.Space.edsTransitionOpenComp`. -/
theorem edsTransitionOpenComp_hom_eq :
    (edsTransitionOpenComp hsq pb p p' q q' hq hq' s hs hsp Ab).hom =
      ((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageOpenMap hsq p p' q' hq') (edsPreimageOpenMap hsq pb p q hq)
          (edsPreimageOpenMap hsq pb p' s hsp)
          (edsPreimageOpenMap_comp_edsPreimageOpenMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app Ab :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).iso
    (edsPreimageOpenMap hsq p p' q' hq') (edsPreimageOpenMap hsq pb p q hq)
    (edsPreimageOpenMap hsq pb p' s hsp)
    (edsPreimageOpenMap_comp_edsPreimageOpenMap hsq pb p p' q q' hq hq' s hs hsp)) Ab

/-- The crossing for `AlgebraicGeometry.Space.edsTransitionEtaleComp`. -/
theorem edsTransitionEtaleComp_hom_eq :
    (edsTransitionEtaleComp hsq pb p p' q q' hq hq' s hs hsp Bb).hom =
      ((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageEtaleMap hsq p p' q' hq') (edsPreimageEtaleMap hsq pb p q hq)
          (edsPreimageEtaleMap hsq pb p' s hsp)
          (edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app Bb :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).iso
    (edsPreimageEtaleMap hsq p p' q' hq') (edsPreimageEtaleMap hsq pb p q hq)
    (edsPreimageEtaleMap hsq pb p' s hsp)
    (edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq pb p p' q q' hq hq' s hs hsp)) Bb

/-! ### The two crossings that have to be read at an isomorphism

The first and the last factor of the prism are derived pullbacks of components, and the equation
`AlgebraicGeometry.Space.edsTransitionConj₄` and `…edsTransitionConj₅` take has them as the
`CategoryTheory.Iso.inv`, respectively `…Iso.hom`, of an isomorphism.  So those two crossings are
stated with the derived pullback written as `CategoryTheory.Functor.mapIso`. -/

/-- `AlgebraicGeometry.Space.edsBridgeOpenSquare_inv_eq` under the derived pullback along `r_P`,
read at the isomorphism. -/
theorem edsBridgeOpenSquare_mapIso_inv_eq :
    ((smallEtaleDerivedModulePullback B S hS
        (edsPreimageInterMap hsq p p' q' hq')).mapIso
          (edsBridgeOpenSquare hsq pb p q hq Ab)).inv =
      (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).map
        (((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsFst B S hS (edsPreimage hsq p)) (edsPreimageOpenMap hsq pb p q hq)
          (edsPreimageInterMap hsq pb p q hq) (edsFst B S hS (edsPreimage hsq pb))
          (edsFst_comp_edsPreimageOpenMap hsq pb p q hq)).inv.app Ab) :=
  congrArg (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).map
    (edsBridgeOpenSquare_inv_eq hsq pb p q hq Ab)

/-- `AlgebraicGeometry.Space.edsBridgeEtaleSquare_inv_eq` under the derived pullback along `r_P`,
read at the isomorphism. -/
theorem edsBridgeEtaleSquare_mapIso_inv_eq :
    ((smallEtaleDerivedModulePullback B S hS
        (edsPreimageInterMap hsq p p' q' hq')).mapIso
          (edsBridgeEtaleSquare hsq pb p q hq Bb)).inv =
      (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).map
        (((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p)) (edsPreimageEtaleMap hsq pb p q hq)
          (edsPreimageInterMap hsq pb p q hq) (edsSnd B S hS (edsPreimage hsq pb))
          (edsSnd_comp_edsPreimageEtaleMap hsq pb p q hq)).inv.app Bb) :=
  congrArg (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).map
    (edsBridgeEtaleSquare_inv_eq hsq pb p q hq Bb)

/-- `AlgebraicGeometry.Space.edsTransitionOpenComp_hom_eq` under the derived pullback along
`edsFst`, read at the isomorphism. -/
theorem edsTransitionOpenComp_mapIso_hom_eq :
    ((smallEtaleDerivedModulePullback B S hS
        (edsFst B S hS (edsPreimage hsq p'))).mapIso
          (edsTransitionOpenComp hsq pb p p' q q' hq hq' s hs hsp Ab)).hom =
      (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p'))).map
        (((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageOpenMap hsq p p' q' hq') (edsPreimageOpenMap hsq pb p q hq)
          (edsPreimageOpenMap hsq pb p' s hsp)
          (edsPreimageOpenMap_comp_edsPreimageOpenMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app Ab) :=
  congrArg (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p'))).map
    (edsTransitionOpenComp_hom_eq hsq pb p p' q q' hq hq' s hs hsp Ab)

/-- `AlgebraicGeometry.Space.edsTransitionEtaleComp_hom_eq` under the derived pullback along
`edsSnd`, read at the isomorphism. -/
theorem edsTransitionEtaleComp_mapIso_hom_eq :
    ((smallEtaleDerivedModulePullback B S hS
        (edsSnd B S hS (edsPreimage hsq p'))).mapIso
          (edsTransitionEtaleComp hsq pb p p' q q' hq hq' s hs hsp Bb)).hom =
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p'))).map
        (((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageEtaleMap hsq p p' q' hq') (edsPreimageEtaleMap hsq pb p q hq)
          (edsPreimageEtaleMap hsq pb p' s hsp)
          (edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app Bb) :=
  congrArg (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p'))).map
    (edsTransitionEtaleComp_hom_eq hsq pb p p' q q' hq hq' s hs hsp Bb)

end AlgebraicGeometry.Space

end

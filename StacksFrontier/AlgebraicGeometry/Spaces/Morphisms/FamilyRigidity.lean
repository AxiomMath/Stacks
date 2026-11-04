module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rigidity of a family of complete fibres

Let `L` and `Y` be algebraic spaces over a scheme `S` contained in a big fppf site, let `Z` be
an algebraic space separated over the base, and let `h : L × Y ⟶ Z` be a morphism.  Say that
`h` is *contracted* over a part of `Y` when its restriction to the part of `L × Y` lying there
does not depend on the `L` coordinate.  This file proves that contraction spreads from a part
of `Y` whose point set is dense to all of `Y`, provided `L × Y` is reduced and the projection
`L × Y ⟶ Y` has a section: `h` then factors through the projection.

Two observations make this much cheaper than the route of Stacks 0AEL.

*The factorization needs no descent at all.*  A projection with a section is a split
epimorphism, hence the coequalizer of its own kernel pair in any category whatsoever.  So no
fppf-local surjectivity, no flatness and no finite presentation enter: the only thing to check
is that the two morphisms `L × L × Y ⟶ L × Y` which read off one or the other of the two `L`
coordinates become equal after composing with `h`.  When `L` is projective space over a field
the required section is a rational point.

*Agreement is checked topologically.*  The agreement locus of two morphisms into a space
separated over the base is a closed subspace (Stacks 084N), so it is everything as soon as it
contains a part with dense point set and the source is reduced (Stacks 03JJ).  No
scheme-theoretic density, and in particular no density of rational points, is needed.

## Main definitions

* `AlgebraicGeometry.Space.fibrePairFst` and `AlgebraicGeometry.Space.fibrePairSnd`: the two
  morphisms `L × (L × Y) ⟶ L × Y` given on points by `(a, b, y) ↦ (b, y)` and
  `(a, b, y) ↦ (a, y)`.  They are the kernel pair of the projection `L × Y ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.eq_comp_snd_of_fibrePair_eq`: a morphism out of `L × Y` which
  coequalizes `fibrePairFst` and `fibrePairSnd` factors through the projection to `Y`, as soon
  as that projection has a section.  This is pure category theory.
* `AlgebraicGeometry.Space.eq_of_eq_on_dense`: two morphisms from a reduced algebraic space to
  an algebraic space separated over the base which agree on a part with dense point set are
  equal.  This is Stacks 084N fed by Stacks 03JJ, with the openness hypothesis of 084N dropped
  — that hypothesis is not used in its proof.
* `AlgebraicGeometry.Space.eq_comp_snd_of_fibrePair_eq_on_dense` and
  `AlgebraicGeometry.Space.exists_eq_comp_snd_of_contracted_on_dense`: **family rigidity**, with
  the density read on `L × (L × Y)`.
* `AlgebraicGeometry.Space.dense_range_pointsMap_prod_map_id`: the part of `L × Y` over a dense
  part of `Y` is dense, when the projection is open on points.
* `AlgebraicGeometry.Space.exists_eq_comp_snd_of_contracted_on_dense_base`: **family rigidity
  with the density read on the base**, which is the form a contraction step consumes.  Stacks
  0AEJ produces an open neighbourhood of a point of `Y` over which a proper family collapses,
  and an open subspace of an irreducible `Y` has dense point set.

## Implementation notes

What is *not* proved here is the geometric input, that a single collapsed fibre forces the
nearby ones to collapse.  Stacks 0AEJ —
`AlgebraicGeometry.Space.exists_isOpenSubspace_isClosedSubspace_isFinite_of_isProper` — gives
an open neighbourhood over which the family factors through a *finite* closed subspace; turning
that into a contraction needs, in addition, that a morphism from a projective line over a field
to a scheme finite over that field is constant, that is `Γ(ℙ¹_K, 𝒪) = K`.  So the hypothesis
`hc` below is where that input enters, and it is a hypothesis of these lemmas rather than
something they discharge.

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEL](https://stacks.math.columbia.edu/tag/0AEL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

/-! ### The kernel pair of a product projection -/

section Categorical

variable {C : Type*} [Category.{v} C] {L Y Z : C}

variable (L Y) in
/-- The first of the two morphisms `L × (L × Y) ⟶ L × Y`: forget the outer `L` coordinate,
that is `(a, b, y) ↦ (b, y)`. -/
def fibrePairFst [HasBinaryProduct L Y] [HasBinaryProduct L (L ⨯ Y)] :
    L ⨯ (L ⨯ Y) ⟶ L ⨯ Y :=
  prod.snd

variable (L Y) in
/-- The second of the two morphisms `L × (L × Y) ⟶ L × Y`: keep the outer `L` coordinate and
discard the inner one, that is `(a, b, y) ↦ (a, y)`. -/
def fibrePairSnd [HasBinaryProduct L Y] [HasBinaryProduct L (L ⨯ Y)] :
    L ⨯ (L ⨯ Y) ⟶ L ⨯ Y :=
  prod.lift prod.fst (prod.snd ≫ prod.snd)

variable [HasBinaryProduct L Y] [HasBinaryProduct L (L ⨯ Y)]

/-- The `L` coordinate of `fibrePairFst L Y` is the inner `L` coordinate of `L × (L × Y)`. -/
@[reassoc (attr := simp)]
theorem fibrePairFst_comp_fst :
    fibrePairFst L Y ≫ (prod.fst : L ⨯ Y ⟶ L) = prod.snd ≫ prod.fst :=
  rfl

/-- The `Y` coordinate of `fibrePairFst L Y` is the `Y` coordinate of `L × (L × Y)`. -/
@[reassoc (attr := simp)]
theorem fibrePairFst_comp_snd :
    fibrePairFst L Y ≫ (prod.snd : L ⨯ Y ⟶ Y) = prod.snd ≫ prod.snd :=
  rfl

/-- The `L` coordinate of `fibrePairSnd L Y` is the outer `L` coordinate of `L × (L × Y)`. -/
@[reassoc (attr := simp)]
theorem fibrePairSnd_comp_fst :
    fibrePairSnd L Y ≫ (prod.fst : L ⨯ Y ⟶ L) = prod.fst :=
  prod.lift_fst _ _

/-- The `Y` coordinate of `fibrePairSnd L Y` is the `Y` coordinate of `L × (L × Y)`. -/
@[reassoc (attr := simp)]
theorem fibrePairSnd_comp_snd :
    fibrePairSnd L Y ≫ (prod.snd : L ⨯ Y ⟶ Y) = prod.snd ≫ prod.snd :=
  prod.lift_snd _ _

/-- `AlgebraicGeometry.Space.fibrePairFst` and `AlgebraicGeometry.Space.fibrePairSnd` are the
kernel pair of the projection: any two morphisms into `L × Y` which agree after projecting to
`Y` are the two components of a single morphism into `L × (L × Y)`. -/
theorem exists_comp_fibrePair_eq {W : C} (a b : W ⟶ L ⨯ Y)
    (hab : a ≫ (prod.snd : L ⨯ Y ⟶ Y) = b ≫ prod.snd) :
    ∃ w : W ⟶ L ⨯ (L ⨯ Y), w ≫ fibrePairFst L Y = b ∧ w ≫ fibrePairSnd L Y = a := by
  refine ⟨prod.lift (a ≫ prod.fst) b, prod.lift_snd _ _, prod.hom_ext ?_ ?_⟩
  · rw [Category.assoc, fibrePairSnd_comp_fst, prod.lift_fst]
  · rw [Category.assoc, fibrePairSnd_comp_snd, ← Category.assoc, prod.lift_snd, hab]

/-- **A morphism which does not distinguish the two `L` coordinates factors through `Y`.**
If the projection `L × Y ⟶ Y` has a section `σ` and `h : L × Y ⟶ Z` coequalizes the kernel
pair of the projection, then `h` is the projection followed by `σ ≫ h`.

A split epimorphism is the coequalizer of its own kernel pair: the pair of morphisms
`prod.snd ≫ σ` and the identity of `L × Y` agree after projecting to `Y`, so `h` does not
distinguish them. -/
theorem eq_comp_snd_of_fibrePair_eq (σ : Y ⟶ L ⨯ Y) (hσ : σ ≫ prod.snd = 𝟙 Y) (h : L ⨯ Y ⟶ Z)
    (hh : fibrePairFst L Y ≫ h = fibrePairSnd L Y ≫ h) :
    h = prod.snd ≫ σ ≫ h := by
  obtain ⟨w, hw₁, hw₂⟩ := exists_comp_fibrePair_eq ((prod.snd : L ⨯ Y ⟶ Y) ≫ σ)
    (𝟙 (L ⨯ Y)) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  calc h = (w ≫ fibrePairFst L Y) ≫ h := by rw [hw₁, Category.id_comp]
    _ = (w ≫ fibrePairSnd L Y) ≫ h := by rw [Category.assoc, Category.assoc, hh]
    _ = prod.snd ≫ σ ≫ h := by rw [hw₂, Category.assoc]

/-- The converse: a morphism which factors through the projection coequalizes the kernel
pair. -/
theorem fibrePair_eq_of_eq_comp_snd (g : Y ⟶ Z) :
    fibrePairFst L Y ≫ ((prod.snd : L ⨯ Y ⟶ Y) ≫ g) =
      fibrePairSnd L Y ≫ (prod.snd ≫ g) := by
  rw [← Category.assoc, ← Category.assoc, fibrePairFst_comp_snd, fibrePairSnd_comp_snd]

variable (Y) in
/-- A point of `L` over a terminal object gives a section of the projection `L × Y ⟶ Y`.  For
`L` projective space over a field this is a rational point, which always exists:
`AlgebraicGeometry.exists_section_projectiveSpaceOver`. -/
def prodSectionOfPoint {T : C} (ht : IsTerminal T) (pt : T ⟶ L) [HasBinaryProduct L Y] :
    Y ⟶ L ⨯ Y :=
  prod.lift (ht.from Y ≫ pt) (𝟙 Y)

omit [HasBinaryProduct L Y] [HasBinaryProduct L (L ⨯ Y)] in
/-- `prodSectionOfPoint Y ht pt` is a section of the projection `L × Y ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem prodSectionOfPoint_comp_snd {T : C} (ht : IsTerminal T) (pt : T ⟶ L)
    [HasBinaryProduct L Y] :
    prodSectionOfPoint Y ht pt ≫ (prod.snd : L ⨯ Y ⟶ Y) = 𝟙 Y :=
  prod.lift_snd _ _

end Categorical

/-! ### Contraction over a part of the base -/

section Contracted

variable {C : Type*} [Category.{v} C] {L J Y Z : C}

variable [HasBinaryProduct L J] [HasBinaryProduct L Y]

/-- Multiplying a monomorphism by an object keeps it a monomorphism. -/
theorem mono_prod_map_id (j : J ⟶ Y) [Mono j] : Mono (prod.map (𝟙 L) j) where
  right_cancellation {_W} a b hab := by
    have h₁ : a ≫ (prod.fst : L ⨯ J ⟶ L) = b ≫ prod.fst := by
      simpa using congrArg (· ≫ (prod.fst : L ⨯ Y ⟶ L)) hab
    have h₂ : a ≫ (prod.snd : L ⨯ J ⟶ J) = b ≫ prod.snd :=
      (cancel_mono j).1 (by simpa using congrArg (· ≫ (prod.snd : L ⨯ Y ⟶ Y)) hab)
    exact prod.hom_ext h₁ h₂

variable [HasBinaryProduct L (L ⨯ J)] [HasBinaryProduct L (L ⨯ Y)]

/-- The two `L` coordinates are read off compatibly with a change of base along `j`: the first
reading. -/
theorem prodMap_comp_fibrePairFst (j : J ⟶ Y) :
    prod.map (𝟙 L) (prod.map (𝟙 L) j) ≫ fibrePairFst L Y =
      fibrePairFst L J ≫ prod.map (𝟙 L) j :=
  prod.map_snd _ _

/-- The two `L` coordinates are read off compatibly with a change of base along `j`: the second
reading. -/
theorem prodMap_comp_fibrePairSnd (j : J ⟶ Y) :
    prod.map (𝟙 L) (prod.map (𝟙 L) j) ≫ fibrePairSnd L Y =
      fibrePairSnd L J ≫ prod.map (𝟙 L) j := by
  refine prod.hom_ext ?_ ?_ <;> simp

/-- **Contraction over a part of the base is contraction of both readings there.** If the
restriction of `h : L × Y ⟶ Z` along `j : J ⟶ Y` does not depend on the `L` coordinate — that
is, `L × J ⟶ L × Y ⟶ Z` factors through the projection `L × J ⟶ J` — then the two readings of
the two `L` coordinates agree after restricting to `L × L × J`. -/
theorem fibrePair_comp_eq_of_contracted (j : J ⟶ Y) (c : J ⟶ Z) (h : L ⨯ Y ⟶ Z)
    (hc : prod.map (𝟙 L) j ≫ h = prod.snd ≫ c) :
    prod.map (𝟙 L) (prod.map (𝟙 L) j) ≫ fibrePairFst L Y ≫ h =
      prod.map (𝟙 L) (prod.map (𝟙 L) j) ≫ fibrePairSnd L Y ≫ h := by
  rw [← Category.assoc, prodMap_comp_fibrePairFst, ← Category.assoc,
    prodMap_comp_fibrePairSnd, Category.assoc, Category.assoc, hc]
  exact fibrePair_eq_of_eq_comp_snd c

end Contracted

/-! ### Agreement on a part with dense point set -/

section Dense

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {T X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Two morphisms agreeing on a dense part are equal.** Let `X` be a reduced algebraic space
over `S` and `Y` an algebraic space separated over an algebraic space `T` by `q`.  Two
morphisms `f, g : X ⟶ Y` over `q` which agree on a subfunctor of `X` whose point set is dense
are equal.

The agreement locus is a closed subspace of `X` by Stacks 084N, so it contains the
scheme-theoretic image of the dense part, which is everything by Stacks 03JJ.  No openness of
the dense part is used; neither is its algebraicity. -/
@[ega "I 7.2.2.1" "more general"]
theorem eq_of_eq_on_dense (hT : IsAlgebraicSpace B S hS T) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun W : Scheme.{u} => IsReduced W))
    (q : Y ⟶ T) (hq : IsSeparated B S hS q) (f g : X ⟶ Y) (hfg : f ≫ q = g ≫ q)
    (U : Subfunctor X) (hdense : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hU : U.ι ≫ f = U.ι ≫ g) :
    f = g := by
  refine (eqSubfunctor_eq_top_iff B S hS q f g hfg).1 (top_le_iff.1 ?_)
  calc (⊤ : Subfunctor X)
      = schemeTheoreticImageSubfunctor B S hS U.ι :=
        (schemeTheoreticImageSubfunctor_ι_eq_top_of_dense B S hS hX hXred U hdense).symm
    _ ≤ eqSubfunctor B S hS q f g hfg :=
        schemeTheoreticImageSubfunctor_le B S hS U.ι
          (isClosedSubspace_eqSubfunctor B S hS hT hX hY q f g hfg hq)
          (by
            rw [Subfunctor.range_ι]
            exact (le_eqSubfunctor_iff B S hS q f g hfg U).2 hU)

end Dense

/-! ### Family rigidity -/

section Rigidity

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {T L Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Family rigidity.** Let `L`, `Y` and `Z` be algebraic spaces over `S`, with `Z` separated
over a terminal `T` by `q`, let `h : L × Y ⟶ Z` be a morphism, and suppose the projection
`L × Y ⟶ Y` has a section `σ`.  If `L × (L × Y)` is reduced and `h` does not distinguish the
two `L` coordinates on a part of `L × (L × Y)` whose point set is dense, then `h` factors
through the projection to `Y`, by `σ ≫ h`.

The hypothesis is checked on a dense part and the conclusion holds everywhere: that is the
content.  The factorization itself is formal once the two readings agree, by
`AlgebraicGeometry.Space.eq_comp_snd_of_fibrePair_eq`. -/
theorem eq_comp_snd_of_fibrePair_eq_on_dense [HasBinaryProduct L Y]
    [HasBinaryProduct L (L ⨯ Y)]
    (hT : IsAlgebraicSpace B S hS T) (ht : IsTerminal T)
    (hZ : IsAlgebraicSpace B S hS Z)
    (hLY : IsAlgebraicSpace B S hS (L ⨯ (L ⨯ Y)))
    (hred : HasEtaleLocalProperty B S hS (L ⨯ (L ⨯ Y)) (fun W : Scheme.{u} => IsReduced W))
    (q : Z ⟶ T) (hq : IsSeparated B S hS q) (h : L ⨯ Y ⟶ Z)
    (σ : Y ⟶ L ⨯ Y) (hσ : σ ≫ prod.snd = 𝟙 Y)
    (U : Subfunctor (L ⨯ (L ⨯ Y)))
    (hdense : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hU : U.ι ≫ fibrePairFst L Y ≫ h = U.ι ≫ fibrePairSnd L Y ≫ h) :
    h = prod.snd ≫ σ ≫ h :=
  eq_comp_snd_of_fibrePair_eq σ hσ h
    (eq_of_eq_on_dense B S hS hT hLY hZ hred q hq _ _ (ht.hom_ext _ _) U hdense hU)

/-- **Family rigidity, in the form a contraction argument consumes.** Let `L`, `J`, `Y` and `Z`
be algebraic spaces over `S`, with `Z` separated over a terminal `T` by `q`, and let
`h : L × Y ⟶ Z`.  Suppose

* the projection `L × Y ⟶ Y` has a section `σ` — for `L` a projective space over a field, a
  rational point;
* `L × (L × Y)` is reduced;
* `j : J ⟶ Y` is a monomorphism over which `h` is *contracted*, that is `L × J ⟶ L × Y ⟶ Z`
  factors through the projection `L × J ⟶ J`;
* the part `L × (L × J)` of `L × (L × Y)` has dense point set.

Then `h` factors through the projection `L × Y ⟶ Y`.

So a contraction over a dense part of the base is a contraction over all of it.  Nothing is
assumed about `L` beyond the existence of the section, and nothing about the topology of `Y`
beyond the density that is hypothesis four. -/
theorem exists_eq_comp_snd_of_contracted_on_dense {J : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    [HasBinaryProduct L J] [HasBinaryProduct L Y] [HasBinaryProduct L (L ⨯ J)]
    [HasBinaryProduct L (L ⨯ Y)]
    (hT : IsAlgebraicSpace B S hS T) (ht : IsTerminal T)
    (hZ : IsAlgebraicSpace B S hS Z)
    (hLY : IsAlgebraicSpace B S hS (L ⨯ (L ⨯ Y)))
    (hred : HasEtaleLocalProperty B S hS (L ⨯ (L ⨯ Y)) (fun W : Scheme.{u} => IsReduced W))
    (q : Z ⟶ T) (hq : IsSeparated B S hS q) (h : L ⨯ Y ⟶ Z)
    (σ : Y ⟶ L ⨯ Y) (hσ : σ ≫ prod.snd = 𝟙 Y)
    (j : J ⟶ Y) [Mono j] (c : J ⟶ Z) (hc : prod.map (𝟙 L) j ≫ h = prod.snd ≫ c)
    (hdense : Dense (Set.range (pointsMap B S hS (L ⨯ (L ⨯ J))
      (prod.map (𝟙 L) (prod.map (𝟙 L) j))))) :
    ∃ g : Y ⟶ Z, h = prod.snd ≫ g := by
  have := mono_prod_map_id (L := L) j
  have hm := mono_prod_map_id (L := L) (prod.map (𝟙 L) j)
  set m : L ⨯ (L ⨯ J) ⟶ L ⨯ (L ⨯ Y) := prod.map (𝟙 L) (prod.map (𝟙 L) j) with hmdef
  refine ⟨σ ≫ h, eq_comp_snd_of_fibrePair_eq_on_dense B S hS hT ht hZ hLY hred q hq h σ hσ
    (Subfunctor.range m) ?_ ?_⟩
  · rw [range_pointsMap_ι_range B S hS m]
    exact hdense
  · apply (cancel_epi (Subfunctor.toRange m)).1
    have key (k : L ⨯ (L ⨯ Y) ⟶ Z) :
        Subfunctor.toRange m ≫ (Subfunctor.range m).ι ≫ k = m ≫ k := by
      rw [← Category.assoc (Subfunctor.toRange m), Subfunctor.toRange_ι]
    rw [key, key]
    exact fibrePair_comp_eq_of_contracted j c h hc

end Rigidity

/-! ### Density of the part lying over a dense part of the base -/

section Density

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {L J Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [HasBinaryProduct L J]
  [HasBinaryProduct L Y]

/-- The part of `L × Y` lying over a part `J` of `Y` is `L × J`: the square
`L × J ⟶ L × Y ⟶ Y`, `L × J ⟶ J ⟶ Y` is cartesian. -/
theorem isPullback_prod_map_id (j : J ⟶ Y) :
    IsPullback (prod.map (𝟙 L) j) (prod.snd : L ⨯ J ⟶ J) (prod.snd : L ⨯ Y ⟶ Y) j := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun s => prod.lift (s.fst ≫ prod.fst) s.snd) (fun s => ?_) (fun s => by simp)
    (fun s m hm₁ hm₂ => ?_))
  · refine prod.hom_ext (by simp) ?_
    simpa using (PullbackCone.condition s).symm
  · refine prod.hom_ext ?_ (by simpa using hm₂)
    simpa using congrArg (fun k => k ≫ (prod.fst : L ⨯ Y ⟶ L)) hm₁

/-- **The part of `L × Y` over a dense part of `Y` is dense**, provided the projection
`L × Y ⟶ Y` is an open map on points — which it is when `L` is flat and locally of finite
presentation over the base.

A nonempty open set of points of `L × Y` has open nonempty image in `|Y|`, so it meets the
dense part; the point of `L × Y` found there lifts to `L × J` by Stacks 03H4. -/
theorem dense_range_pointsMap_prod_map_id (j : J ⟶ Y)
    (hopen : IsOpenMap (pointsMap B S hS (L ⨯ Y) (prod.snd : L ⨯ Y ⟶ Y)))
    (hdense : Dense (Set.range (pointsMap B S hS J j))) :
    Dense (Set.range (pointsMap B S hS (L ⨯ J) (prod.map (𝟙 L) j))) := by
  refine Dense.mono ?_ (hdense.preimage hopen)
  rintro x ⟨y, hy⟩
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS
    (isPullback_prod_map_id B S hS j) x y hy.symm
  exact ⟨w, hw⟩

/-- The two-step version: the part of `L × (L × Y)` over a dense part of `Y` is dense. -/
theorem dense_range_pointsMap_prod_map_id_two [HasBinaryProduct L (L ⨯ J)]
    [HasBinaryProduct L (L ⨯ Y)] (j : J ⟶ Y)
    (hopen : IsOpenMap (pointsMap B S hS (L ⨯ Y) (prod.snd : L ⨯ Y ⟶ Y)))
    (hopen' : IsOpenMap (pointsMap B S hS (L ⨯ (L ⨯ Y)) (prod.snd : L ⨯ (L ⨯ Y) ⟶ L ⨯ Y)))
    (hdense : Dense (Set.range (pointsMap B S hS J j))) :
    Dense (Set.range (pointsMap B S hS (L ⨯ (L ⨯ J))
      (prod.map (𝟙 L) (prod.map (𝟙 L) j)))) :=
  dense_range_pointsMap_prod_map_id B S hS _ hopen'
    (dense_range_pointsMap_prod_map_id B S hS j hopen hdense)

end Density

/-! ### Family rigidity over a dense part of the base -/

section RigidityBase

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {T L J Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Family rigidity, with the density read on the base.** Let `L`, `J`, `Y` and `Z` be
algebraic spaces over `S`, with `Z` separated over a terminal `T` by `q`, and let
`h : L × Y ⟶ Z`.  Suppose

* the projection `L × Y ⟶ Y` has a section `σ`;
* the projections off an `L` factor are open on points — they are, when `L` is flat and
  locally of finite presentation over the base;
* `L × (L × Y)` is reduced;
* `j : J ⟶ Y` is a monomorphism with dense point set over which `h` is contracted, that is
  `L × J ⟶ L × Y ⟶ Z` factors through the projection `L × J ⟶ J`.

Then `h` factors through the projection `L × Y ⟶ Y`: the contraction spreads from the dense
part of the base to all of it.

This is the form the contraction step of a factorization argument consumes.  Stacks 0AEJ
produces an open neighbourhood of a point of `Y` over which the family collapses, and an open
subspace of an irreducible `Y` has dense point set; this lemma turns that into a global
factorization without any further density, and in particular without the density of rational
points. -/
theorem exists_eq_comp_snd_of_contracted_on_dense_base [HasBinaryProduct L J]
    [HasBinaryProduct L Y] [HasBinaryProduct L (L ⨯ J)] [HasBinaryProduct L (L ⨯ Y)]
    (hT : IsAlgebraicSpace B S hS T) (ht : IsTerminal T)
    (hZ : IsAlgebraicSpace B S hS Z)
    (hLY : IsAlgebraicSpace B S hS (L ⨯ (L ⨯ Y)))
    (hred : HasEtaleLocalProperty B S hS (L ⨯ (L ⨯ Y)) (fun W : Scheme.{u} => IsReduced W))
    (hopen : IsOpenMap (pointsMap B S hS (L ⨯ Y) (prod.snd : L ⨯ Y ⟶ Y)))
    (hopen' : IsOpenMap (pointsMap B S hS (L ⨯ (L ⨯ Y)) (prod.snd : L ⨯ (L ⨯ Y) ⟶ L ⨯ Y)))
    (q : Z ⟶ T) (hq : IsSeparated B S hS q) (h : L ⨯ Y ⟶ Z)
    (σ : Y ⟶ L ⨯ Y) (hσ : σ ≫ prod.snd = 𝟙 Y)
    (j : J ⟶ Y) [Mono j] (c : J ⟶ Z) (hc : prod.map (𝟙 L) j ≫ h = prod.snd ≫ c)
    (hdense : Dense (Set.range (pointsMap B S hS J j))) :
    ∃ g : Y ⟶ Z, h = prod.snd ≫ g :=
  exists_eq_comp_snd_of_contracted_on_dense B S hS hT ht hZ hLY hred q hq h σ hσ j c hc
    (dense_range_pointsMap_prod_map_id_two B S hS j hopen hopen' hdense)

end RigidityBase

end AlgebraicGeometry.Space

end

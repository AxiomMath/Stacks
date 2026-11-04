module

public import StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension

/-!
# Smoothness of the Hilbert schemes of points on a smooth relative curve

Let `X ⟶ S` be smooth of relative dimension one and suppose that every Hilbert functor of points
`Hilb^d_{X/S}` is representable, say by `H d` over `S`. Then `H d` is smooth over `S` of relative
dimension `d`.

The proof is the one of the source, by induction on `d`. In degree `0` the only degree-`0` family
over any base is the empty one, so `H 0` is terminal over `S` and its structure morphism is an
isomorphism. For the step, `H d ×_S X ⟶ S` is smooth of relative dimension `d + 1`, being the
composition of the base change of `X ⟶ S` with the structure morphism of `H d`, and point
addition `H d ×_S X ⟶ H (d + 1)` is finite locally free of degree `d + 1`
([Stacks Tag 0B9G](https://stacks.math.columbia.edu/tag/0B9G)), hence surjective, flat and locally
of finite presentation. Smoothness of `H (d + 1) ⟶ S` is therefore descent along point addition
([Stacks Tag 05B5](https://stacks.math.columbia.edu/tag/05B5)). The source leaves the relative
dimension to the reader; it is read off the fibres, which is the second half of the argument here:
the fibres of point addition are zero-dimensional because it is finite, so the fibre dimension of
`H (d + 1) ⟶ S` equals that of `H d ×_S X ⟶ S`, namely `d + 1`, by the dimension formula for a
composition with a flat first factor ([Stacks Tag 02JS](https://stacks.math.columbia.edu/tag/02JS)).

## Main results

* `Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq` — a smooth morphism all of
  whose fibres have dimension `n` at every point is smooth of relative dimension `n`. This is the
  converse of `AlgebraicGeometry.fiberDimensionAt_eq_of_smoothOfRelativeDimension`.
* `Stacks.Hilbert.isIso_hom_of_representsHilbertFunctorOfRank_zero` — a scheme representing
  `Hilb^0_{X/S}` is `S`.
* `Stacks.Hilbert.smoothOfRelativeDimension_of_represents` — **Stacks Tag 0B9H**: the
  representing schemes `Hilb^d_{X/S}` are smooth over `S` of relative dimension `d`.
* `Stacks.Hilbert.isSeparated_of_isPointAddition_zero` — a point-addition morphism
  `Hilb^0_{X/S} ×_S X ⟶ Hilb^1_{X/S}` exists only for a separated `X ⟶ S`.

## Implementation notes

*Representability is a hypothesis of the tag.* The source assumes that the functors
`Hilb^d_{X/S}` are representable and speaks about the representing schemes; accordingly the
statement takes a family `H : ℕ → Over S` together with
`Stacks.Hilbert.RepresentsHilbertFunctorOfRank X (H d) d` for every `d`, and concludes about every
such family. Nothing is chosen: no existence statement is used to produce `H`.
The whole family is needed, not just the degree in question, because the induction climbs from
degree `0` and each step uses the representing schemes of two consecutive degrees — exactly as in
the source, whose proof reads "assume the lemma holds for `d`".

*Why `X ⟶ S` is assumed separated.* The induction needs an actual point-addition morphism
`H d ×_S X ⟶ H (d + 1)`. Its construction, `Stacks.Hilbert.addPoint`, adds the graph of the
universal relative point to the universal family and so needs that graph to be a closed
subscheme; for the universal point this is equivalent to separatedness of `X ⟶ S`, as explained
in `StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition`. Smoothness of relative dimension
one does not supply it. Only the construction needs it: the degree statement of Tag 0B9G holds for
any point-addition morphism, and so does
`Stacks.Hilbert.smoothOfRelativeDimension_of_isPointAddition` here, which is the form of the
result with the morphisms supplied rather than constructed.

The hypothesis is not merely convenient for the construction: by
`Stacks.Hilbert.isSeparated_of_isPointAddition_zero` a point-addition morphism in degree `0`
exists only for a separated `X ⟶ S`, since `Hilb^0_{X/S}` is `S` and the point component of the
identity point of `S ×_S X` is the identity of `X`, whose graph is the diagonal. With
`Stacks.Hilbert.isPointAddition_addPoint` this makes separatedness of `X ⟶ S` *equivalent* to the
existence of the degree-`0` point-addition morphism, so the induction of the source cannot be
started without it. The source reaches the same place through its assertion that
`Hilb^1_{X/S} = X`, which is likewise equivalent to separatedness: a degree-`1` family on `T` is a
relative point of `X` whose graph is a closed immersion, and taking `T = X` with the identity
point reads that condition as the diagonal being a closed immersion.

*The statement is false without a separation hypothesis.* Dropping `[IsSeparated X.hom]` is not
a matter of finding another proof: the tag as printed has counterexamples. Let `k` be a field,
`A = ∏_{n ∈ ℕ} k`, `S = Spec A`, `e_n ∈ A` the idempotents, `I = ⨁_n k` the ideal they generate,
`S' = ⋃_n D(e_n) = ⨆_n Spec k` (open, not quasi-compact) and `Z = V(I)`. Let `X` be two copies
of `𝔸¹_S` glued along `𝔸¹_{S'}`; it is smooth of relative dimension one over `S`, and not
separated (not even quasi-separated). For `T` over `S` write `T'` for the inverse image of `S'`.
If `d ≥ 1` and `D ∈ Hilb^d_{X/S}(T)` then `T'` is closed in `T`. Suppose `t ∉ T'` lies in its
closure. As `D ⟶ T` is open and surjective, a point `p` of `D` over `t` lies in the closure of
`D_{T'}`; say `p = ι₁ q` for the first chart `ι₁ : 𝔸¹_T ⟶ X_T`, so `p` is not in the second
chart `ι₂`, the charts meeting over `T'` only. Then `q` is in the closure of
`ι₁⁻¹ D_{T'} = ι₂⁻¹ D_{T'}`, so `ι₂ q ∈ D` and `q ∈ W = ι₁⁻¹ D ∩ ι₂⁻¹ D`. The two `T`-morphisms
`ι₁, ι₂ : W ⟶ D` agree on `W_{T'}` and `D ⟶ T` is finite, hence separated, so they agree on the
closure of `W_{T'}`, which contains `q`: but `ι₁ q = p ≠ ι₂ q`. Since a morphism landing in `Z`
set-theoretically factors through `V(I)` (an idempotent vanishing at every point is zero), this
gives `Hilb^d_{X/S} ≅ Hilb^d_{𝔸¹_{S'}/S'} ⊔ Hilb^d_{(𝔸¹ ⊔ 𝔸¹)_Z/Z}` for `d ≥ 1`, which is
representable (by `𝔸^d_{S'} ⊔ ⨆_{a+b=d} 𝔸^d_Z`), and `Hilb^0_{X/S} = S`. But for `d ≥ 1` the
open and closed piece `𝔸^d_Z` is not locally of finite presentation over `S`, since `Z ⟶ S` is
not at any point of `Z` (`I` is not finitely generated near it), so `Hilb^d_{X/S}` is not smooth
over `S`. Note that the counterexample is not quasi-separated; whether quasi-separatedness of
`X ⟶ S` suffices is not settled here. The counterexample is machine-checked, for `k = 𝔽₂`, in
`StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothnessCounterexample`
(`Stacks.Hilbert.NonSeparated.not_forall_smoothOfRelativeDimension_of_represents`), where the
failure of smoothness is read off from openness instead: the pieces over `Z` are open in
`Hilb^d_{X/S}` and map into `Z`, which has empty interior, while a smooth morphism is open.

*The relative dimension.* `AlgebraicGeometry.SmoothOfRelativeDimension d` is a property of the
morphism, so the conclusion asserts both halves of the source's "smooth over `S` of relative
dimension `d`" at once; smoothness alone is
`AlgebraicGeometry.SmoothOfRelativeDimension.smooth`.

## References

* [Stacks Project, Tag 0B9H](https://stacks.math.columbia.edu/tag/0B9H)
* [Stacks Project, Tag 0B9G](https://stacks.math.columbia.edu/tag/0B9G)
* [Stacks Project, Tag 05B5](https://stacks.math.columbia.edu/tag/05B5)
* [Stacks Project, Tag 02JS](https://stacks.math.columbia.edu/tag/02JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-- The fibres of a finite morphism are zero-dimensional at every point: a finite morphism is
locally quasi-finite and of finite type at every point. -/
private theorem fiberDimensionAt_eq_zero_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (x : X) : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 0 := by
  refine (quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x).mp ⟨?_, f.quasiFiniteAt x⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, f.finiteType_appLE hU hV hVU⟩

/-- **The relative dimension of a smooth morphism is read off its fibres.** A smooth morphism all
of whose fibres have dimension `n` at every point is smooth of relative dimension `n`.

A standard smooth chart through a point presents the morphism as a relative global complete
intersection, whose fibre dimension is the number of variables minus the number of relations,
that is the dimension of the chart's presentation; the chart computes the fibre dimension on the
scheme itself because the chart maps are open immersions. So the hypothesis forces every chart to
have dimension `n`.

This is the converse of `AlgebraicGeometry.fiberDimensionAt_eq_of_smoothOfRelativeDimension`. -/
theorem smoothOfRelativeDimension_of_fiberDimensionAt_eq {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (n : ℕ)
    (hdim : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (n : WithBot ℕ∞)) :
    SmoothOfRelativeDimension n f := by
  classical
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ := Smooth.exists_isStandardSmooth f x
  let A := ToType Γ(S, U)
  let B := ToType Γ(X, V)
  let : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  let hs : Algebra.IsStandardSmooth A B := hstd.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype σ := Fintype.ofFinite σ
  let g : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (f.appLE U V hVU).hom)
  let j : Spec (.of B) ⟶ X := hV.fromSpec
  let i : Spec (.of A) ⟶ S := hU.fromSpec
  have : IsOpenImmersion j := hV.isOpenImmersion_fromSpec
  have : IsOpenImmersion i := hU.isOpenImmersion_fromSpec
  have hcomp : j ≫ f = g ≫ i := (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU).symm
  let q : Spec (.of B) := hV.primeIdealOf ⟨x, hxV⟩
  have hq : j q = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  let : P.toPresentation.IsRelativeGlobalCompleteIntersection :=
    P.isRelativeGlobalCompleteIntersection
  have hdimChart := fiberDimensionAt_eq_card_sub_card P.toPresentation q
  have hchart := fiberDimensionAt_eq_of_open_square j f g i hcomp q
  have hPn : (P.dimension : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    change _ = ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞) at hdimChart
    rw [show ((P.dimension : ℕ) : WithBot ℕ∞) = ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞) from
      rfl, ← hdimChart, hchart, hq]
    exact hdim x
  exact ⟨U, hU, V, hV, hxV, hVU,
    P.isStandardSmoothOfRelativeDimension (by exact_mod_cast hPn)⟩

end Stacks.Smooth

namespace Stacks.Morphisms

/-- **A morphism with empty source is finite locally free of degree `0`.** The direct image of
the structure sheaf is the zero module, which is free on an empty index type.

This is `Stacks.Morphisms.isFiniteLocallyFreeOfRank_zero_of_isEmpty` without the hypothesis that
the target be affine; the affine proof computes the module of global sections, this one works
with the pushforward sheaf directly. -/
theorem isFiniteLocallyFreeOfRank_zero_of_isEmpty_source {Z T : Scheme.{u}} (g : Z ⟶ T)
    [IsEmpty Z] : IsFiniteLocallyFreeOfRank g 0 := by
  have hpush : IsZero (pushforwardStructureSheaf g) := by
    refine (IsZero.iff_id_eq_zero _).2 (Scheme.Modules.hom_ext _ _ fun U => ?_)
    have : Subsingleton Γ(pushforwardStructureSheaf g, U) :=
      inferInstanceAs (Subsingleton Γ(Z, g ⁻¹ᵁ U))
    ext x
    exact Subsingleton.elim _ _
  have hfree : IsZero (_root_.SheafOfModules.free (R := T.ringCatSheaf) PEmpty.{u + 1}) := by
    refine (IsZero.iff_id_eq_zero _).2 ((_root_.SheafOfModules.freeHomEquiv _).injective ?_)
    funext a
    exact a.elim
  exact .mk (toIsAffineHom := inferInstance)
    (toIsFiniteLocallyFreeOfRank := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (hfree.iso hpush)
      (SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv PEmpty.{u + 1} 0
        (Equiv.equivOfIsEmpty _ _)))

/-- **The source of a degree-`0` finite locally free morphism is empty.** Its rank function is
constantly `0`, while every point of the source forces the rank at its image to be at least
one. -/
theorem isEmpty_of_isFiniteLocallyFreeOfRank_zero {Z T : Scheme.{u}} (g : Z ⟶ T)
    [h : IsFiniteLocallyFreeOfRank g 0] : IsEmpty Z := by
  obtain ⟨hfin, hflat, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree g 0)
  let : IsFinite g := hfin
  let : Flat g := hflat
  refine ⟨fun z => ?_⟩
  have h1 := g.one_le_finrank_map z
  have h0 := (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g 0).mp h (g z)
  omega

end Stacks.Morphisms

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-! ### Degree-zero families -/

/-- A degree-`0` Hilbert family is the empty subscheme: its ideal sheaf is the unit ideal. -/
theorem HilbertFamily.ideal_eq_top {X T : Over S} (D : HilbertFamily X T 0) : D.ideal = ⊤ := by
  have := D.isFiniteLocallyFreeOfRank
  have he : IsEmpty D.ideal.subscheme :=
    Stacks.Morphisms.isEmpty_of_isFiniteLocallyFreeOfRank_zero
      (D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom)
  rw [← D.ideal.ker_subschemeι]
  exact @Scheme.ker_eq_top_of_isEmpty _ _ D.ideal.subschemeι he

/-- The empty subscheme is a degree-`0` Hilbert family, so `Hilb^0_{X/S}` has a point over every
base. -/
def familyZero (X T : Over S) : HilbertFamily X T 0 where
  ideal := ⊤
  isFiniteLocallyFreeOfRank :=
    have : IsEmpty (⊤ : ((Over.pullback T.hom).obj X).left.IdealSheafData).subscheme :=
      inferInstance
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_zero_of_isEmpty_source _

/-- **`S` represents `Hilb^0_{X/S}`.** Over any base the empty subscheme is a degree-`0` family
and no other ideal sheaf is one, while `S` is terminal over itself; the two one-element sets
correspond, naturally because both ideals are the unit ideal. -/
def representsHilbertFunctorOfRankZero (X : Over S) :
    RepresentsHilbertFunctorOfRank X (Over.mk (𝟙 S)) 0 where
  family {T} :=
    { toFun := fun _ => familyZero X T
      invFun := fun _ => Over.homMk T.hom
      left_inv := fun _ => Over.mkIdTerminal.hom_ext _ _
      right_inv := fun D => HilbertFamily.ext (HilbertFamily.ideal_eq_top D).symm }
  naturality g f := by simp [familyZero]

/-- A scheme representing `Hilb^0_{X/S}` is terminal over `S`: two maps into it are equal. -/
private theorem hom_ext_of_represents_zero {X H T : Over S}
    (hH : RepresentsHilbertFunctorOfRank X H 0) (a b : T ⟶ H) : a = b :=
  hH.family.injective (HilbertFamily.ext
    ((HilbertFamily.ideal_eq_top _).trans (HilbertFamily.ideal_eq_top _).symm))

/-- **`Hilb^0_{X/S}` is `S`.** A scheme over `S` representing the degree-`0` Hilbert functor has
an isomorphism as structure morphism: a degree-`0` family is the empty one and nothing else, so
such a scheme is terminal over `S`. -/
theorem isIso_hom_of_representsHilbertFunctorOfRank_zero {X H : Over S}
    (hH : RepresentsHilbertFunctorOfRank X H 0) : IsIso H.hom := by
  let T₀ : Over S := Over.mk (𝟙 S)
  let q₀ : T₀ ⟶ H := hH.family.symm (familyZero X T₀)
  let r : H ⟶ T₀ := Over.homMk H.hom
  have hrq : r ≫ q₀ = 𝟙 H := hom_ext_of_represents_zero hH _ _
  have hqr : q₀ ≫ r = 𝟙 T₀ := Over.mkIdTerminal.hom_ext _ _
  let : IsIso r := ⟨q₀, hrq, hqr⟩
  exact (Over.forget S).map_isIso r

/-- **A point-addition morphism in degree zero forces `X ⟶ S` to be separated.** Let `H₀`
represent `Hilb^0_{X/S}`, let `H₁` represent `Hilb^1_{X/S}` and let `f : H₀ ×_S X ⟶ H₁` be a
point-addition morphism. Then `X ⟶ S` is separated.

A point-addition morphism places the graph of the point component of each of its source's points
inside a Hilbert family, so that graph is a closed immersion. In degree `0` the scheme `H₀` is
terminal over `S`, so the second projection identifies `H₀ ×_S X` with `X`, and the point
component of the identity point of `H₀ ×_S X` becomes the identity of `X`, whose graph is the
diagonal of `X ⟶ S`. -/
theorem isSeparated_of_isPointAddition_zero {X H₀ H₁ : Over S}
    (hH₀ : RepresentsHilbertFunctorOfRank X H₀ 0)
    (hH₁ : RepresentsHilbertFunctorOfRank X H₁ 1) {f : H₀ ⨯ X ⟶ H₁}
    (hf : IsPointAddition hH₀ hH₁ f) : IsSeparated X.hom := by
  have hci : IsClosedImmersion (pointGraph X (H₀ ⨯ X) (𝟙 (H₀ ⨯ X) ≫ prod.snd)) :=
    hf.isClosedImmersion_pointGraph (H₀ ⨯ X) (𝟙 _)
  rw [Category.id_comp] at hci
  -- a degree-`0` family is the empty one, so `H₀` is terminal over `S`
  let g : X ⟶ H₀ ⨯ X := prod.lift (hH₀.family.symm (familyZero X X)) (𝟙 X)
  have hgs : g ≫ prod.snd = 𝟙 X := prod.lift_snd _ _
  have hsg : (prod.snd : H₀ ⨯ X ⟶ X) ≫ g = 𝟙 (H₀ ⨯ X) := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, Category.id_comp]
      exact hom_ext_of_represents_zero hH₀ _ _
    · rw [Category.assoc, Category.id_comp, hgs, Category.comp_id]
  have : IsIso g := ⟨prod.snd, hgs, hsg⟩
  have : IsIso g.left := (Over.forget S).map_isIso g
  -- the base-change comparison map along an isomorphism is a monomorphism, hence separated
  have : Mono (familyBaseChangeMap X g) := by
    constructor
    intro W a b hab
    refine pullback.hom_ext ?_ ?_
    · simpa only [Category.assoc, familyBaseChangeMap_comp_fst] using
        congrArg (fun m => m ≫ pullback.fst X.hom (H₀ ⨯ X).hom) hab
    · refine (cancel_mono g.left).mp ?_
      simpa only [Category.assoc, familyBaseChangeMap_comp_snd] using
        congrArg (fun m => m ≫ pullback.snd X.hom (H₀ ⨯ X).hom) hab
  have : IsSeparated (familyBaseChangeMap X g) := inferInstance
  have hgraph := pointGraph_comp_familyBaseChangeMap X g (prod.snd : H₀ ⨯ X ⟶ X)
  rw [hgs] at hgraph
  have : IsClosedImmersion (pointGraph X X (𝟙 X) ≫ familyBaseChangeMap X g) := by
    rw [hgraph]; infer_instance
  have hpg : IsClosedImmersion (pointGraph X X (𝟙 X)) :=
    IsClosedImmersion.of_comp _ (familyBaseChangeMap X g)
  have hdiag : pointGraph X X (𝟙 X) = pullback.diagonal X.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [pointGraph_comp_fst, pullback.diagonal_fst, Over.id_left]
    · rw [pointGraph_comp_snd, pullback.diagonal_snd]
  rw [hdiag] at hpg
  exact ⟨hpg⟩

/-! ### Smoothness of the Hilbert schemes -/

variable {X : Over S} [SmoothOfRelativeDimension 1 X.hom]

/-- The product `H ×_S X` is smooth over `S` of relative dimension `d + 1` when `H` is smooth of
relative dimension `d`: its first projection is the base change of `X ⟶ S`. -/
private theorem smoothOfRelativeDimension_prod_hom {d : ℕ} (H : Over S)
    [SmoothOfRelativeDimension d H.hom] : SmoothOfRelativeDimension (d + 1) (H ⨯ X).hom := by
  have hpull : SmoothOfRelativeDimension 1 (pullback.fst H.hom X.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback H.hom X.hom).flip inferInstance
  have hsq : IsPullback (Over.prodLeftIsoPullback H X).hom
      ((prod.fst : H ⨯ X ⟶ H).left) (pullback.fst H.hom X.hom) (𝟙 H.left) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id, Over.prodLeftIsoPullback_hom_fst]⟩
  have hfst : SmoothOfRelativeDimension 1 ((prod.fst : H ⨯ X ⟶ H).left) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hsq hpull
  let : SmoothOfRelativeDimension 1 ((prod.fst : H ⨯ X ⟶ H).left) := hfst
  have hcomp : SmoothOfRelativeDimension (1 + d)
      ((prod.fst : H ⨯ X ⟶ H).left ≫ H.hom) := inferInstance
  rw [Over.w (prod.fst : H ⨯ X ⟶ H), Nat.add_comm 1 d] at hcomp
  exact hcomp

/-- **Stacks Project, Tag 0B9H, with the point-addition morphisms supplied.** Let `X ⟶ S` be
smooth of relative dimension one, let `H d` represent `Hilb^d_{X/S}` for every `d`, and let
`add d` be the point-addition morphism `H d ×_S X ⟶ H (d + 1)`. Then `H d` is smooth over `S` of
relative dimension `d`.

The induction starts at `H 0`, which is `S`. For the step, `H d ×_S X` is smooth of relative
dimension `d + 1` over `S` and point addition is finite locally free of degree `d + 1`
(Tag 0B9G), hence surjective, flat and locally of finite presentation; smoothness descends along
it (Tag 05B5). The relative dimension is then read off the fibres: point addition is finite, so
its fibres are zero-dimensional and the dimension formula for a composition whose first factor is
flat (Tag 02JS) transfers the fibre dimension `d + 1` from `H d ×_S X` to `H (d + 1)`. -/
theorem smoothOfRelativeDimension_of_isPointAddition (H : ℕ → Over S)
    (hH : ∀ d : ℕ, RepresentsHilbertFunctorOfRank X (H d) d)
    (add : ∀ d : ℕ, H d ⨯ X ⟶ H (d + 1))
    (hadd : ∀ d : ℕ, IsPointAddition (hH d) (hH (d + 1)) (add d)) (d : ℕ) :
    SmoothOfRelativeDimension d (H d).hom := by
  induction d with
  | zero =>
      have : IsIso (H 0).hom := isIso_hom_of_representsHilbertFunctorOfRank_zero (hH 0)
      infer_instance
  | succ d ih =>
      let p := (add d).left
      let q := (H (d + 1)).hom
      let : SmoothOfRelativeDimension d (H d).hom := ih
      have hsource : SmoothOfRelativeDimension (d + 1) (H d ⨯ X).hom :=
        smoothOfRelativeDimension_prod_hom (H d)
      have hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p (d + 1) :=
        (hadd d).isFiniteLocallyFreeOfRank_left
      let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p (d + 1) := hrank
      obtain ⟨hfin, hflat, hfp⟩ :=
        (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p).mp
          (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p (d + 1))
      let : IsFinite p := hfin
      let : Flat p := hflat
      let : LocallyOfFinitePresentation p := hfp
      have hsurj : Surjective p := by
        refine p.one_le_finrank_iff_surjective.mp fun y => ?_
        rw [(Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq p (d + 1)).mp
          hrank y]
        exact Nat.succ_le_succ (Nat.zero_le d)
      let : Surjective p := hsurj
      have hpq : p ≫ q = (H d ⨯ X).hom := Over.w (add d)
      have hsource' : SmoothOfRelativeDimension (d + 1) (p ≫ q) := by rw [hpq]; exact hsource
      let : Smooth (p ≫ q) := hsource'.smooth
      have hsmooth : Smooth q := Stacks.Smooth.smooth_of_comp_of_fppf p q
      let : Smooth q := hsmooth
      refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq q (d + 1) fun y => ?_
      obtain ⟨x, rfl⟩ := p.surjective y
      have hformula := topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt p q x
        (Flat.stalkMap p x)
      rw [fiberDimensionAt_eq_of_smoothOfRelativeDimension (p ≫ q) (d + 1) x,
        Stacks.Smooth.fiberDimensionAt_eq_zero_of_isFinite p x, zero_add] at hformula
      exact hformula.symm

/-- **Stacks Project, Tag 0B9H.** Let `X ⟶ S` be a smooth morphism of schemes of relative
dimension one such that the functors `Hilb^d_{X/S}` are representable, say by `H d` over `S`.
Then the schemes `H d` are smooth over `S` of relative dimension `d`.

Representability is the tag's own hypothesis, carried here as the family `hH`. Separatedness of
`X ⟶ S` is what makes the point-addition morphism of Tag 0B9G available, and by
`Stacks.Hilbert.isSeparated_of_isPointAddition_zero` it is equivalent to the existence of that
morphism in degree `0`, so the induction cannot be started without it. The form of the result
which takes those morphisms as data instead is
`Stacks.Hilbert.smoothOfRelativeDimension_of_isPointAddition`.

*Correction.* The printed statement has no separatedness hypothesis and is false without one:
`Stacks.Hilbert.NonSeparated.not_smooth_hilbertScheme_doubledLine` is a smooth non-separated
relative curve all of whose Hilbert functors are representable, with no `Hilb^d` of positive
degree smooth. Apart from `[IsSeparated X.hom]` the binders are exactly the tag's: `X ⟶ S` smooth
of relative dimension one, and a representing scheme `H d` of `Hilb^d_{X/S}` for every `d`. -/
@[stacks 0B9H "corrected statement: adds the hypothesis that X -> S is separated, which the \
printed statement omits and needs (the source uses it through Hilb^1 = X and Tag 0B9G; without it \
the statement is false, see Stacks.Hilbert.NonSeparated.not_smooth_hilbertScheme_doubledLine); \
representability is the tag's own hypothesis"]
theorem smoothOfRelativeDimension_of_represents [IsSeparated X.hom] (H : ℕ → Over S)
    (hH : ∀ d : ℕ, RepresentsHilbertFunctorOfRank X (H d) d) (d : ℕ) :
    SmoothOfRelativeDimension d (H d).hom :=
  smoothOfRelativeDimension_of_isPointAddition H hH
    (fun d => addPoint (hH d) (hH (d + 1)))
    (fun d => isPointAddition_addPoint (hH d) (hH (d + 1))) d

end Stacks.Hilbert

end

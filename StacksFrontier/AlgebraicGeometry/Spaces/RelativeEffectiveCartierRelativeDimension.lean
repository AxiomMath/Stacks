module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart

/-!
# The relative dimension of a relative effective Cartier divisor on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces which is locally of finite type and of
relative dimension `r + 1`, and let `D ⊆ X` be a relative effective Cartier divisor on `X/Y`
(Stacks 0EPP): an effective Cartier divisor with `D ⟶ Y` flat. Then `D ⟶ Y` has relative
dimension `r`. If `f` has relative dimension `0`, then `D` is empty.

This is the relative dimension of `p|_D` which Stacks 0ERE presupposes when it writes the flat
pullback `(p|_D)^*` along the restriction of a flat morphism `p` of relative dimension `r` to a
relative effective Cartier divisor.

## Main results

* `AlgebraicGeometry.Space.hasRelativeDimension_comp_of_isRelativeEffectiveCartierDivisor`: the
  restriction `D ⟶ Y` has relative dimension `r` when `f` has relative dimension `r + 1`.
* `AlgebraicGeometry.Space.isEmpty_points_of_isRelativeEffectiveCartierDivisor`: in relative
  dimension zero the divisor has no points.

## Implementation notes

Relative dimension at a point of an algebraic space is read on one pointed pair of étale charts
(Stacks 04NM, `AlgebraicGeometry.Space.hasRelativeDimensionAt_pointsMap_iff`). Given a point of
`D`, choose such a pair `U ⟶ V` for `f` at its image in `X`. By Stacks 083C the inverse image
of `D` on `U` is the closed subscheme of an effective Cartier ideal sheaf `I`; it is an étale
chart of `D`, the point lifts to it by Stacks 03H4, and flatness of `D ⟶ Y` makes the closed
subscheme of `I` flat over `V`. So `I` is a relative effective Cartier divisor for the scheme
morphism `U ⟶ V`, which has relative dimension `r + 1` because every point of `U` lies over a
point of `X`; the scheme case,
`Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor`,
gives the relative dimension `r` of the chart of `D ⟶ Y`.

## References

* [Stacks Project, Tag 0EPP](https://stacks.math.columbia.edu/tag/0EPP)
* [Stacks Project, Tag 0ERE](https://stacks.math.columbia.edu/tag/0ERE)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image of a closed subspace `E ⊆ X` on an étale scheme chart `g : h_U ⟶ X`,
presented as the range of `h_R ⟶ h_U`, is an étale chart of `E`: the induced morphism
`h_R ⟶ E` is étale and sits in a cartesian square over `g`. -/
theorem exists_isPullback_of_preimage_eq_range (X : AlgebraicSpaces B S hS)
    (E : ClosedSubspaces B S hS X.1) {U R : BigFppfOver B S hS}
    (g : yoneda.obj U ⟶ X.1) (hg : IsEtale B S hS g) (j : R ⟶ U)
    [Mono j] (hpre : E.1.preimage g = Subfunctor.range (yoneda.map j)) :
    ∃ a : yoneda.obj R ⟶ E.1.toFunctor,
      IsEtale B S hS a ∧ IsPullback (yoneda.map j) a g E.1.ι := by
  have hrange : Subfunctor.range (yoneda.map j) ≤ E.1.preimage g := hpre.ge
  let k : yoneda.obj R ⟶ (E.1.preimage g).toFunctor := Subfunctor.lift (yoneda.map j) hrange
  have hk : k ≫ (E.1.preimage g).ι = yoneda.map j := Subfunctor.lift_ι _ hrange
  have : Epi k := by
    rw [NatTrans.epi_iff_epi_app]
    intro t
    refine ConcreteCategory.epi_of_surjective _ fun z => ?_
    obtain ⟨w, hw⟩ : z.val ∈ (Subfunctor.range (yoneda.map j)).obj t := by
      rw [← hpre]
      exact z.property
    exact ⟨w, Subtype.ext hw⟩
  have : Mono k := by
    refine ⟨fun {Z} f₁ f₂ h => (cancel_mono (yoneda.map j)).1 ?_⟩
    simpa only [Category.assoc, hk] using congrArg (· ≫ (E.1.preimage g).ι) h
  have : IsIso k := isIso_of_mono_of_epi k
  let a : yoneda.obj R ⟶ E.1.toFunctor := k ≫ E.1.fromPreimage g
  have hcart : IsPullback (yoneda.map j) a g E.1.ι := by
    have hsquare : IsPullback k (yoneda.map j) (E.1.preimage g).ι (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp [hk]⟩
    simpa [a, Category.assoc] using
      (hsquare.paste_horiz (Subfunctor.isPullback_preimage g E.1)).flip
  have hR : IsAlgebraicSpace B S hS (yoneda.obj R) := isAlgebraicSpace_yoneda B S hS R
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hcart' : IsPullback (ObjectProperty.homMk (yoneda.map j) :
        (⟨_, hR⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hU⟩)
      (ObjectProperty.homMk a : (⟨_, hR⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, E.2.1⟩)
      (ObjectProperty.homMk g : (⟨_, hU⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (ObjectProperty.homMk E.1.ι : (⟨_, E.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) hcart
  exact ⟨a, isEtale_of_isPullback B S hS _ _ _ _ hcart' hg, hcart⟩

/-- **A relative effective Cartier divisor read on one pair of étale charts.** For a point `x`
of a relative effective Cartier divisor `E` on `X/Y`, with `f : X ⟶ Y` locally of finite type,
there is a morphism of schemes `g : U ⟶ V` locally of finite type (the morphism of a pair of
étale charts of `f`), a relative effective Cartier divisor `I` for `g` (the inverse image of
`E`), and a point `u` of `I` such that

* `g` has relative dimension `d` whenever `f` has, and
* the relative dimension of `E ⟶ Y` at `x` is the local dimension at `u` of the fibre of
  `I ⟶ V`. -/
theorem exists_chart_isRelativeEffectiveCartierDivisor {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hft : IsLocallyOfFiniteType B S hS f.hom)
    (E : ClosedSubspaces B S hS X.1) (hE : IsRelativeEffectiveCartierDivisor B S hS f E)
    (x : points B S hS E.1.toFunctor) :
    ∃ (U V : Scheme.{u}) (g : U ⟶ V) (_ : LocallyOfFiniteType g) (I : U.IdealSheafData)
      (w : I.subscheme),
      Stacks.Divisors.IsRelativeEffectiveCartierDivisor g I ∧
      (∀ d : ℕ, HasRelativeDimension d B S hS f.hom → RelativeDimension g d) ∧
      ∀ d : ℕ∞, HasRelativeDimensionAt d B S hS (E.1.ι ≫ f.hom) x ↔
        topologicalKrullDimAt ((I.subschemeι ≫ g).fiber ((I.subschemeι ≫ g) w))
          ((I.subschemeι ≫ g).asFiber w) = (d : WithBot ℕ∞) := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS X.2 Y.2 f.hom
    (pointsMap B S hS E.1.toFunctor E.1.ι x)
  obtain ⟨I, R, j, e, hI, hmap, hpre⟩ :=
    hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS X E hE.1 c.U c.a
      (isEtale_of_presheaf_etale B S hS c.a_etale)
  have : Mono j := by
    have : Mono (T.map j) := by
      change Mono ((BigFppfOver.toScheme B S hS).map j)
      rw [hmap]
      infer_instance
    exact T.mono_of_mono_map inferInstance
  obtain ⟨a, ha, hcart⟩ := exists_isPullback_of_preimage_eq_range B S hS X E c.a
    (isEtale_of_presheaf_etale B S hS c.a_etale) j hpre
  obtain ⟨w, -, hw₂⟩ := exists_point_of_isPullback_presheaf B S hS hcart
    (c.representative.class B S hS (yoneda.obj c.U)) x (by rw [c.maps_to])
  have hcomm : yoneda.map (j ≫ c.h) ≫ c.b = a ≫ (E.1.ι ≫ f.hom) := by
    rw [Functor.map_comp, Category.assoc, c.comm, ← Category.assoc, hcart.w, Category.assoc]
  have : LocallyOfFiniteType (T.map c.h) := hft c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  have hfac : T.map (j ≫ c.h) = e.hom ≫ (I.subschemeι ≫ T.map c.h) := by
    change (BigFppfOver.toScheme B S hS).map (j ≫ c.h) = _
    rw [Functor.map_comp, hmap, Category.assoc]
  have hflat : Flat (T.map (j ≫ c.h)) :=
    hE.2 R c.V a c.b (j ≫ c.h) (presheaf_etale_of_isEtale B S hS ha) c.b_etale hcomm
  have hflatI : Flat (I.subschemeι ≫ T.map c.h) := by
    rw [hfac] at hflat
    simpa using (inferInstance : Flat (e.inv ≫ e.hom ≫ I.subschemeι ≫ T.map c.h))
  refine ⟨_, _, T.map c.h, inferInstance, I, e.hom (pointsEquivScheme B S hS R w), ⟨hI, hflatI⟩,
    fun d hd => ?_, fun d => ?_⟩
  · rw [relativeDimension_iff_forall_topologicalKrullDimAt]
    intro y
    exact_mod_cast (hasRelativeDimensionAt_pointsMap_iff B S hS (d : ℕ∞) f.hom c.U c.V c.a c.b
      c.h c.a_etale c.b_etale c.comm y).1 (hd _)
  · have key := hasRelativeDimensionAt_pointsMap_iff B S hS d (E.1.ι ≫ f.hom) R c.V a c.b
      (j ≫ c.h) (presheaf_etale_of_isEtale B S hS ha) c.b_etale hcomm
      (pointsEquivScheme B S hS R w)
    rwa [Equiv.symm_apply_apply, hw₂, hfac, fiberDimensionAt_comp_openImmersion] at key

/-- **The relative dimension of a relative effective Cartier divisor.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces locally of finite type and of relative dimension `r + 1`, and let
`E ⊆ X` be a relative effective Cartier divisor on `X/Y` (Stacks 0EPP). Then `E ⟶ Y` has
relative dimension `r`. -/
theorem hasRelativeDimension_comp_of_isRelativeEffectiveCartierDivisor
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hft : IsLocallyOfFiniteType B S hS f.hom)
    (r : ℕ) (hf : HasRelativeDimension (r + 1) B S hS f.hom)
    (E : ClosedSubspaces B S hS X.1) (hE : IsRelativeEffectiveCartierDivisor B S hS f E) :
    HasRelativeDimension r B S hS (E.1.ι ≫ f.hom) := by
  intro x
  obtain ⟨U, V, g, _, I, w, hI, hdim, hiff⟩ :=
    exists_chart_isRelativeEffectiveCartierDivisor B S hS f hft E hE x
  have hrel :=
    Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
      g r (hdim (r + 1) hf) I hI
  rw [relativeDimension_iff_forall_topologicalKrullDimAt] at hrel
  exact (hiff r).2 (by exact_mod_cast hrel w)

/-- **In relative dimension zero a relative effective Cartier divisor is empty.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces locally of finite type and of relative
dimension `0`, and let `E ⊆ X` be a relative effective Cartier divisor on `X/Y`. Then `E` has no
points. -/
theorem isEmpty_points_of_isRelativeEffectiveCartierDivisor {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hft : IsLocallyOfFiniteType B S hS f.hom)
    (hf : HasRelativeDimension 0 B S hS f.hom)
    (E : ClosedSubspaces B S hS X.1) (hE : IsRelativeEffectiveCartierDivisor B S hS f E) :
    IsEmpty (points B S hS E.1.toFunctor) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, V, g, _, I, w, hI, hdim, -⟩ :=
    exists_chart_isRelativeEffectiveCartierDivisor B S hS f hft E hE x
  have h0 :=
    Stacks.Divisors.isEmpty_subscheme_of_isRelativeEffectiveCartierDivisor_of_relativeDimension_zero
      g (hdim 0 hf) I hI
  exact h0.false w

end AlgebraicGeometry.Space

end

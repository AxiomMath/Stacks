module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Over
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.StandardCovering

/-!
# The étale site axioms

Let `B` be a big étale site containing a scheme `S`. The covering families specified for the
small étale category of `S`, for the big affine étale category over `S`, and for the small
affine étale category of `S` each satisfy the site axioms: they contain the singleton family
of an isomorphism, they are closed under composition, and they are stable under base change.

For the big étale category over `S` itself there is nothing to prove beyond the axioms for `B`,
since its covering families are by definition those of `B`.

## Main results

* `AlgebraicGeometry.SmallEtale.isSite` — the small étale covering families form a site.
* `AlgebraicGeometry.BigAffineEtale.isSite` — the standard étale covering families of affine
  objects over `S` form a site.
* `AlgebraicGeometry.SmallAffineEtale.isSite` — the covering families of the small affine
  étale category form a site.

## Implementation notes

That a class of covering families is a site is `CategoryTheory.IsSite` applied to the
family-valued covering predicate, which retains the chosen indexed families rather than only
the Grothendieck topology they generate.

In each case the three axioms are transported from the corresponding axioms for `B`. Base
change is the delicate one: the pullbacks are formed in `B`, and then shown to lie in the
relevant full subcategory — étale over `S` because étale morphisms are stable under base
change and composition, affine because the base change of a standard étale covering of an
affine object is again one. The resulting square is reflected back into the subcategory by
faithfulness of the inclusions.

## References

* [Stacks Project, Tag 021C](https://stacks.math.columbia.edu/tag/021C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A pullback square over the image of `f` and `g` in the base commutes over the slice base. -/
private theorem over_hom_comp_eq_of_isPullback {C : Type*} [Category C] {T : C} {A U V : Over T}
    (f : A ⟶ U) (g : V ⟶ U) {P : C} {π₁ : P ⟶ A.left} {π₂ : P ⟶ V.left}
    (h : IsPullback π₁ π₂ f.left g.left) : π₁ ≫ A.hom = π₂ ≫ V.hom := by
  rw [← Over.w f, reassoc_of% h.w, Over.w g]

/-- A pullback square of underlying morphisms lifts to a pullback square in the slice category. -/
private theorem isPullback_over_homMk {C : Type*} [Category C] {T : C} {A U V : Over T}
    (f : A ⟶ U) (g : V ⟶ U) {P : C} {π₁ : P ⟶ A.left} {π₂ : P ⟶ V.left}
    (h : IsPullback π₁ π₂ f.left g.left) :
    IsPullback (Over.homMk π₁ (over_hom_comp_eq_of_isPullback f g h) : Over.mk (π₂ ≫ V.hom) ⟶ A)
      (Over.homMk π₂ : Over.mk (π₂ ≫ V.hom) ⟶ V) f g :=
  IsPullback.of_map_of_faithful (Over.forget T) h

/-- **Stacks 021C, small étale site.** The étale covering families on the
small étale category of a scheme satisfy the axioms of a site. -/
@[stacks 021C "small_etale_site"]
public lemma SmallEtale.isSite (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : IsSite (SmallEtale.IsCovering B S hS) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    exact B.coverings_isSite.1
      ((SmallEtale.inclusion B S hS ⋙ BigEtaleOver.forget B S hS).map f)
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    simpa [SmallEtale.IsCovering, BigEtaleOver.IsCovering, PreZeroHypercover.map,
      PreZeroHypercover.bind, PreZeroHypercover.pushforward] using
      B.coverings_isSite.2.1 _ h𝒰 _ h𝒱 (fun i =>
        congrArg (SmallEtale.inclusion B S hS ⋙ BigEtaleOver.forget B S hS).obj (h i))
  · intro 𝒰 h𝒰 V g
    let E : Covering B.Scheme :=
      ⟨𝒰.1.obj.left,
        𝒰.2.map (SmallEtale.inclusion B S hS ⋙ BigEtaleOver.forget B S hS)⟩
    obtain ⟨P, p₁, p₂, hpb, hcov⟩ :=
      B.coverings_isSite.2.2 E h𝒰 V.obj.left g.hom.left
    dsimp [E, PreZeroHypercover.map] at P p₁ p₂ hpb hcov
    have hEtale (i : 𝒰.2.I₀) : Etale (B.inclusion.map (p₂ i)) :=
      ((Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp (by
        simpa only [AlgebraicGeometry.IsEtaleCovering, Scheme.etalePrecoverage,
          PreZeroHypercover.presieve₀, PreZeroHypercover.map] using hcov.1)).2 i
    let Q (i : 𝒰.2.I₀) : SmallEtale B S hS :=
      ⟨Over.mk (p₂ i ≫ V.obj.hom), by
        show Etale (B.inclusion.map (p₂ i ≫ V.obj.hom))
        rw [Functor.map_comp]
        have := hEtale i
        infer_instance⟩
    have hpb' (i : 𝒰.2.I₀) : IsPullback (p₁ i) (p₂ i) (𝒰.2.f i).hom.left g.hom.left := hpb i
    let q₁ (i : 𝒰.2.I₀) : Q i ⟶ 𝒰.2.X i :=
      ObjectProperty.homMk (Over.homMk (p₁ i) (over_hom_comp_eq_of_isPullback _ _ (hpb' i)))
    let q₂ (i : 𝒰.2.I₀) : Q i ⟶ V := ObjectProperty.homMk (Over.homMk (p₂ i) rfl)
    refine ⟨Q, q₁, q₂, fun i ↦ ?_, ?_⟩
    · exact IsPullback.of_map_of_faithful (SmallEtale.inclusion B S hS)
        (isPullback_over_homMk _ _ (hpb' i))
    · simpa [SmallEtale.IsCovering, BigEtaleOver.IsCovering, PreZeroHypercover.map, Q,
        q₂] using hcov

/-- **Stacks 021C, big affine étale site.** The standard étale covering families of
affine objects over `S` satisfy the site axioms. -/
@[stacks 021C "big_affine_etale_site"]
public lemma BigAffineEtale.isSite (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) : IsSite (BigAffineEtale.IsCovering B S hS) := by
  let K := BigAffineEtale.inclusion B S hS ⋙ BigEtaleOver.forget B S hS
  have cover_iff (E : Covering (BigAffineEtale B S hS)) :
      BigAffineEtale.IsCovering B S hS E ↔
        BigEtaleSite.IsStandardEtaleCovering B ⟨K.obj E.1, E.2.map K⟩ := by
    simp [BigAffineEtale.IsCovering, BigEtaleOver.IsStandardEtaleCovering,
      BigEtaleOver.IsCovering, BigEtaleSite.IsStandardEtaleCovering,
      PreZeroHypercover.map, Functor.comp_map, K]
  refine ⟨?_, ?_, ?_⟩
  · intro U V f inst
    have : IsAffine (B.inclusion.obj (K.obj U)) := U.property
    have h := BigEtaleSite.isStandardEtaleCovering_singleton B (K.map f)
    simpa [BigAffineEtale.IsCovering, BigEtaleOver.IsStandardEtaleCovering,
      BigEtaleOver.IsCovering, BigEtaleSite.IsStandardEtaleCovering,
      PreZeroHypercover.map, PreZeroHypercover.singleton, Functor.comp_map, K] using h
  · intro E hE F hF h
    have hE' := (cover_iff E).mp hE
    have hF' (i : E.2.I₀) := (cover_iff (F i)).mp (hF i)
    have hh (i : E.2.I₀) : K.obj (F i).1 = (E.2.map K).X i :=
      congrArg K.obj (h i)
    have hc := BigEtaleSite.isStandardEtaleCovering_comp B
      ⟨K.obj E.1, E.2.map K⟩ hE'
      (fun i ↦ ⟨K.obj (F i).1, (F i).2.map K⟩) hF' hh
    simpa [BigAffineEtale.IsCovering, BigEtaleOver.IsStandardEtaleCovering,
      BigEtaleOver.IsCovering, BigEtaleSite.IsStandardEtaleCovering, K,
      PreZeroHypercover.map, PreZeroHypercover.bind,
      PreZeroHypercover.pushforward] using hc
  · intro E hE V g
    have hE' := (cover_iff E).mp hE
    have : IsAffine (B.inclusion.obj (K.obj V)) := V.property
    obtain ⟨P, π₁, π₂, hpb, hcov⟩ :=
      BigEtaleSite.isStandardEtaleCovering_baseChange B
        ⟨K.obj E.1, E.2.map K⟩ hE' (K.obj V) (K.map g)
    have hpbB (i : E.2.I₀) :
        IsPullback (π₁ i) (π₂ i) ((E.2.map K).f i) (K.map g) :=
      IsPullback.of_map_of_faithful B.inclusion (hpb i)
    let Q (i : E.2.I₀) : BigAffineEtale B S hS :=
      ⟨Over.mk (π₂ i ≫ V.obj.hom), hcov.2.2.2 i⟩
    let p₁ (i : E.2.I₀) : Q i ⟶ E.2.X i :=
      ObjectProperty.homMk <| Over.homMk (π₁ i) (over_hom_comp_eq_of_isPullback _ _ (hpbB i))
    let p₂ (i : E.2.I₀) : Q i ⟶ V :=
      ObjectProperty.homMk <| Over.homMk (π₂ i) rfl
    refine ⟨Q, p₁, p₂, fun i ↦ ?_, ?_⟩
    · exact IsPullback.of_map_of_faithful (BigAffineEtale.inclusion B S hS)
        (isPullback_over_homMk _ _ (hpbB i))
    · simpa [BigAffineEtale.IsCovering, BigEtaleOver.IsStandardEtaleCovering,
        BigEtaleOver.IsCovering, BigEtaleSite.IsStandardEtaleCovering,
        PreZeroHypercover.map, Functor.comp_map, K, Q, p₂] using hcov

/-- A covering of the small affine étale category is sent to a standard étale covering. -/
private theorem isStandardEtaleCovering_of_smallAffineEtale
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (E : Covering (SmallAffineEtale B S hS)) (hE : SmallAffineEtale.IsCovering B S hS E) :
    BigEtaleSite.IsStandardEtaleCovering B
      ⟨(SmallAffineEtale.inclusion B S hS ⋙ SmallEtale.inclusion B S hS ⋙
          BigEtaleOver.forget B S hS).obj E.1,
        E.2.map (SmallAffineEtale.inclusion B S hS ⋙ SmallEtale.inclusion B S hS ⋙
          BigEtaleOver.forget B S hS)⟩ :=
  ⟨hE.1, SmallAffineEtale.isAffine_toScheme_obj B S hS E.1, hE.2,
    fun i ↦ SmallAffineEtale.isAffine_toScheme_obj B S hS (E.2.X i)⟩

/-- **Stacks 021C, small affine étale site.** The standard étale covering families on
the small affine étale category of a scheme satisfy the axioms of a site. -/
@[stacks 021C "small_affine_etale_site"]
public theorem SmallAffineEtale.isSite (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    IsSite (SmallAffineEtale.IsCovering B S hS) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    show B.IsCovering _ ∧ Finite PUnit
    constructor
    · have : IsAffine (B.inclusion.obj
            ((SmallAffineEtale.inclusion B S hS ⋙
              SmallEtale.inclusion B S hS ⋙
              BigEtaleOver.forget B S hS).obj U)) :=
          SmallAffineEtale.isAffine_toScheme_obj B S hS U
      exact (BigEtaleSite.isStandardEtaleCovering_singleton B
        ((SmallAffineEtale.inclusion B S hS ⋙
          SmallEtale.inclusion B S hS ⋙
          BigEtaleOver.forget B S hS).map f)).1
    · infer_instance
  · intro E hE F hF h
    change B.IsCovering _ ∧ Finite _
    let G := SmallAffineEtale.inclusion B S hS ⋙
      SmallEtale.inclusion B S hS ⋙
      BigEtaleOver.forget B S hS
    have hstdE := isStandardEtaleCovering_of_smallAffineEtale B S hS E hE
    have hstdF := fun i ↦ isStandardEtaleCovering_of_smallAffineEtale B S hS (F i) (hF i)
    have hcomp := BigEtaleSite.isStandardEtaleCovering_comp B
      ⟨G.obj E.1, E.2.map G⟩ hstdE
      (fun i ↦ ⟨G.obj (F i).1, (F i).2.map G⟩) hstdF
      (fun i ↦ congrArg G.obj (h i))
    constructor
    · convert hcomp.1 using 1
      congr 1
      dsimp [G]
      refine PreZeroHypercover.ext (x := _) (y := _) rfl (by rfl) ?_
      apply heq_of_eq
      funext ij
      rcases ij with ⟨i, j⟩
      simp [PreZeroHypercover.map, PreZeroHypercover.bind, PreZeroHypercover.pushforward]
    · exact hcomp.2.2.1
  · intro E hE V g
    let G := SmallAffineEtale.inclusion B S hS ⋙
      SmallEtale.inclusion B S hS ⋙
      BigEtaleOver.forget B S hS
    have hstdE := isStandardEtaleCovering_of_smallAffineEtale B S hS E hE
    have : IsAffine (B.inclusion.obj (G.obj V)) :=
      SmallAffineEtale.isAffine_toScheme_obj B S hS V
    obtain ⟨P, p₁, p₂, hp, hstdP⟩ :=
      BigEtaleSite.isStandardEtaleCovering_baseChange B
        ⟨G.obj E.1, E.2.map G⟩ hstdE (G.obj V) (G.map g)
    dsimp only [PreZeroHypercover.map] at P p₁ p₂ hp
    have hetale (i : E.2.I₀) : Etale (B.inclusion.map (p₂ i)) := by
      apply MorphismProperty.IsStableUnderBaseChange.of_isPullback (hp i)
      have : Etale (B.inclusion.map E.1.obj.obj.hom) := E.1.obj.property
      have hc : Etale (B.inclusion.map (G.map (E.2.f i)) ≫
          B.inclusion.map E.1.obj.obj.hom) := by
        rw [← B.inclusion.map_comp,
          show G.map (E.2.f i) ≫ E.1.obj.obj.hom = (E.2.X i).obj.obj.hom by simp [G]]
        exact (E.2.X i).obj.property
      exact Etale.of_comp (B.inclusion.map (G.map (E.2.f i)))
        (B.inclusion.map E.1.obj.obj.hom)
    let Q₀ (i : E.2.I₀) : BigEtaleOver B S hS :=
      Over.mk (p₂ i ≫ V.obj.obj.hom)
    have hQ₀ (i : E.2.I₀) : Etale (B.inclusion.map (Q₀ i).hom) := by
      have := hetale i
      show Etale ((B.inclusion.map (p₂ i)) ≫
        B.inclusion.map V.obj.obj.hom)
      infer_instance
    let Q₁ (i : E.2.I₀) : SmallEtale B S hS := ⟨Q₀ i, hQ₀ i⟩
    let Q (i : E.2.I₀) : SmallAffineEtale B S hS := ⟨Q₁ i, hstdP.2.2.2 i⟩
    have hpb (i : E.2.I₀) :
        IsPullback (p₁ i) (p₂ i) (G.map (E.2.f i)) (G.map g) :=
      IsPullback.of_map_of_faithful B.inclusion (hp i)
    let q₁ (i : E.2.I₀) : Q i ⟶ E.2.X i :=
      ⟨⟨Over.homMk (p₁ i) (over_hom_comp_eq_of_isPullback _ _ (hpb i))⟩⟩
    let q₂ (i : E.2.I₀) : Q i ⟶ V := ⟨⟨Over.homMk (p₂ i)⟩⟩
    refine ⟨Q, q₁, q₂, fun i ↦ ?_, ?_⟩
    · exact IsPullback.of_map_of_faithful (SmallAffineEtale.inclusion B S hS ⋙
        SmallEtale.inclusion B S hS) (isPullback_over_homMk _ _ (hpb i))
    · show B.IsCovering _ ∧ Finite _
      refine ⟨?_, hstdP.2.2.1⟩
      convert hstdP.1 using 1
      congr 1

end AlgebraicGeometry

module

public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued

/-!
# A uniformly bounded fppf covering family is refined by one surjective flat morphism

`AlgebraicGeometry.BigFppfOver.exists_surjective_etale_sigma_of_etaleCover` replaces a
uniformly bounded family of étale morphisms covering an object of the big fppf site of `S` by a
single surjective étale morphism out of one object of the site, namely the coproduct of the
family. This file proves the same statement for the morphisms the fppf topology is made of:
flat and locally of finite presentation.

## Main results

* `AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_flat_lfp`: a jointly surjective family
  of flat morphisms locally of finite presentation of the site generates a covering sieve.
* `AlgebraicGeometry.BigFppfOver.exists_surjective_flat_sigma_of_flatCover`: a uniformly
  bounded family of morphisms into an object of the big fppf site of `S`, flat and locally of
  finite presentation on underlying schemes and jointly surjective, is refined by a single
  surjective flat morphism locally of finite presentation out of one object of the site.
* `AlgebraicGeometry.BigFppfOver.exists_affine_flat_mem_sieve_of_mem_topology`: through every
  point of the base of a covering sieve there passes an arrow of the sieve whose source is
  affine of size at most that of the base.
* `AlgebraicGeometry.BigFppfOver.exists_flat_singleton_refinement_of_mem_topology`: **a
  covering sieve of the big fppf site of `S` is refined by a single surjective flat morphism
  locally of finite presentation out of one object of the site**, presented as the coproduct of
  a family of arrows of the sieve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A uniformly bounded fppf covering of an object of the site is refined by a single
surjective flat morphism locally of finite presentation out of one object of the site.**

Given a family `g : X i ⟶ T` of morphisms flat and locally of finite presentation on underlying
schemes whose images cover `T`, and whose index type and members are bounded by one cardinal
below the cutoff, the coproduct `V` of the `X i` lies in the site and the induced `q : V ⟶ T`
is surjective, flat and locally of finite presentation. -/
theorem exists_surjective_flat_sigma_of_flatCover {ι : Type u} (X : ι → BigFppfOver B S hS)
    (T : BigFppfOver B S hS) (g : ∀ i, X i ⟶ T)
    (hgf : ∀ i, Flat ((toScheme B S hS).map (g i)))
    (hgp : ∀ i, LocallyOfFinitePresentation ((toScheme B S hS).map (g i)))
    (hcov : ∀ x : (toScheme B S hS).obj T, ∃ i, x ∈ Set.range ((toScheme B S hS).map (g i)))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hX : ∀ i, ((toScheme B S hS).obj (X i)).size ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (j : ∀ i, X i ⟶ V) (q : V ⟶ T),
      (∀ i, j i ≫ q = g i) ∧
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (j i))) ∧
      (∀ x : (toScheme B S hS).obj V, ∃ i, x ∈ Set.range ((toScheme B S hS).map (j i))) ∧
      Surjective ((toScheme B S hS).map q) ∧
      Flat ((toScheme B S hS).map q) ∧
      LocallyOfFinitePresentation ((toScheme B S hS).map q) ∧
      Nonempty (IsColimit (Cofan.mk V j)) := by
  obtain ⟨V, j, hjopen, hjcov, -, ⟨hjsite⟩, -⟩ :=
    exists_isColimitUliftYoneda_of_size_le B S hS X hμ hι hX
  let 𝒰 : ((toScheme B S hS).obj V).OpenCover.{u} :=
    { I₀ := ι
      X := fun i => (toScheme B S hS).obj (X i)
      f := fun i => (toScheme B S hS).map (j i)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hjcov, hjopen⟩ }
  have hfac : ∀ i, 𝒰.f i ≫ (toScheme B S hS).map (Cofan.IsColimit.desc hjsite g) =
      (toScheme B S hS).map (g i) := fun i =>
    ((toScheme B S hS).map_comp _ _).symm.trans
      (congrArg (toScheme B S hS).map (Cofan.IsColimit.fac hjsite g i))
  refine ⟨V, j, Cofan.IsColimit.desc hjsite g, fun i => Cofan.IsColimit.fac hjsite g i,
    hjopen, hjcov, ?_, ?_, ?_, ⟨hjsite⟩⟩
  · refine (surjective_iff _).2 fun t => ?_
    obtain ⟨i, y, rfl⟩ := hcov t
    exact ⟨(toScheme B S hS).map (j i) y, by rw [← hfac i]; rfl⟩
  · have : IsZariskiLocalAtSource (@Flat.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
    exact IsZariskiLocalAtSource.of_openCover 𝒰 fun i => hfac i ▸ hgf i
  · have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
    exact IsZariskiLocalAtSource.of_openCover 𝒰 fun i => hfac i ▸ hgp i

/-! ### Refining a covering sieve by one surjective flat morphism -/

/-- **A jointly surjective family of flat morphisms locally of finite presentation of the big
fppf site of `S` generates a covering sieve.** -/
theorem ofArrows_mem_topology_of_flat_lfp {U : BigFppfOver B S hS} {I : Type u}
    (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ U)
    (hcov : ∀ x : (toScheme B S hS).obj U,
      ∃ i, x ∈ Set.range ((toScheme B S hS).map (v i)).base)
    (hflat : ∀ i, Flat ((toScheme B S hS).map (v i)))
    (hlfp : ∀ i, LocallyOfFinitePresentation ((toScheme B S hS).map (v i))) :
    Sieve.ofArrows V v ∈ BigFppfOver.topology B S hS U := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let E : PreZeroHypercover.{u + 1} U.left :=
    ⟨ULift.{u + 1} I, fun i => (V i.down).left, fun i => (v i.down).left⟩
  have heq : E.presieve₀ =
      Presieve.ofArrows (fun i => (V i).left) (fun i => (v i).left) := by
    funext Z g
    exact propext ⟨by rintro ⟨i⟩; exact ⟨i.down⟩, by rintro ⟨i⟩; exact ⟨ULift.up i⟩⟩
  rw [Sieve.ofArrows, ← heq]
  apply B.generate_mem_topology_of_isFppfCovering E
  rw [IsFppfCovering, Precoverage.mem_comap_iff, heq, Presieve.map_ofArrows,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨hcov, fun i => ⟨hflat i, hlfp i⟩⟩

/-- **Through every point of the base of a covering sieve of the big fppf site of `S` there
passes an arrow of the sieve, flat and locally of finite presentation, with affine source of
size at most that of the base.** -/
theorem exists_affine_flat_mem_sieve_of_mem_topology {T : BigFppfOver B S hS} {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T) (x : (toScheme B S hS).obj T) :
    ∃ (X : BigFppfOver B S hS) (g : X ⟶ T),
      R.arrows g ∧
      IsAffine ((toScheme B S hS).obj X) ∧
      ((toScheme B S hS).obj X).size ≤ ((toScheme B S hS).obj T).size ∧
      Flat ((toScheme B S hS).map g) ∧
      LocallyOfFinitePresentation ((toScheme B S hS).map g) ∧
      x ∈ Set.range ((toScheme B S hS).map g) := by
  classical
  obtain ⟨c, q, hqR, hqf, hqp, y, hy⟩ := BigFppfOver.exists_mem_of_mem_topology B S hS hR x
  obtain ⟨A, hA, hyA, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (toScheme B S hS).obj c) (x := y) (U := (⊤ : ((toScheme B S hS).obj c).Opens)) trivial
  have : IsAffine (A : Scheme.{u}) := hA
  have hAsize : B.Contains (A : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion A.ι c.left.property
  let f : B.obj hAsize ⟶ c.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj hAsize) ⟶ B.inclusion.obj c.left from A.ι)
  let X : BigFppfOver B S hS := Over.mk (f ≫ c.hom)
  let incl : X ⟶ c := Over.homMk f (by simp [X])
  have hinclmap : (toScheme B S hS).map incl = A.ι := B.inclusion.map_preimage _
  have hmap : (toScheme B S hS).map (incl ≫ q) = A.ι ≫ (toScheme B S hS).map q := by
    rw [Functor.map_comp, hinclmap]
  have := hqf
  have := hqp
  refine ⟨X, incl ≫ q, R.downward_closed hqR incl, inferInstanceAs (IsAffine (A : Scheme.{u})),
    ?_, hmap ▸ inferInstance, hmap ▸ inferInstance, ⟨⟨y, hyA⟩, by rwa [hmap]⟩⟩
  have : IsAffine ((toScheme B S hS).obj X) := inferInstanceAs (IsAffine (A : Scheme.{u}))
  exact Scheme.size_le_of_locallyOfFiniteType (A.ι ≫ (toScheme B S hS).map q)

/-- **A covering sieve of the big fppf site of `S` is refined by a single surjective flat
morphism locally of finite presentation out of one object of the site, presented as the
coproduct of a family of arrows of the sieve.** -/
theorem exists_flat_singleton_refinement_of_mem_topology (T : BigFppfOver B S hS) {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T) :
    ∃ (ι : Type u) (X : ι → BigFppfOver B S hS) (V : BigFppfOver B S hS)
      (j : ∀ i, X i ⟶ V) (q : V ⟶ T) (g : ∀ i, X i ⟶ T),
      (∀ i, R.arrows (g i)) ∧
      (∀ i, j i ≫ q = g i) ∧
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (j i))) ∧
      (∀ x : (toScheme B S hS).obj V, ∃ i, x ∈ Set.range ((toScheme B S hS).map (j i))) ∧
      Surjective ((toScheme B S hS).map q) ∧
      Flat ((toScheme B S hS).map q) ∧
      LocallyOfFinitePresentation ((toScheme B S hS).map q) ∧
      Nonempty (IsColimit (Cofan.mk V j)) := by
  classical
  choose X g hgR hgaff hgsize hgf hgp hgcov using
    fun x : (toScheme B S hS).obj T => exists_affine_flat_mem_sieve_of_mem_topology B S hS hR x
  obtain ⟨V, j, q, hjq, hjopen, hjcov, hqsurj, hqf, hqp, hcolim⟩ :=
    exists_surjective_flat_sigma_of_flatCover B S hS X T g hgf hgp (fun x => ⟨x, hgcov x⟩)
      (B.cutoff_isStrongPrelimit T.left.property) (Scheme.mk_le_two_pow_size _)
      fun x => (hgsize x).trans (Cardinal.cantor _).le
  exact ⟨_, X, V, j, q, g, hgR, hjq, hjopen, hjcov, hqsurj, hqf, hqp, hcolim⟩

end BigFppfOver

end AlgebraicGeometry

end

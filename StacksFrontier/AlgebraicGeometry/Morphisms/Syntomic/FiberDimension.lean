module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Local
public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Fibre dimension of a syntomic morphism

For a relative global complete intersection presentation, the local dimension of the fibre at
every point is the number of variables minus the number of relations. Consequently the local
fibre dimension of a syntomic morphism is locally constant on the source, and a syntomic
morphism of constant fibre dimension `d` is said to be syntomic of relative dimension `d`.

## Main definitions

* `AlgebraicGeometry.SyntomicOfRelativeDimension` expresses syntomicity with constant fibre
  dimension `d`.

## Main results

* `AlgebraicGeometry.fiberDimensionAt_eq_card_sub_card` computes the dimension at a point of
  every fibre of a relative global complete intersection presentation.
* `AlgebraicGeometry.isLocallyConstant_fiberDimensionAt` gives local constancy of the pointwise
  fibre dimension of a syntomic morphism.

## Implementation notes

The chosen presentation is indexed by arbitrary finite types, so its numbers of variables and
relations are `Nat.card ι` and `Nat.card σ`. The point of the fibre over `f x` corresponding to
`x` is `f.asFiber x`, and its dimension is `topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)`,
valued in `WithBot ℕ∞`. `SyntomicOfRelativeDimension` is an abbreviation so its two conditions
can be used directly.

Local constancy is reduced to the affine case by `fiberDimensionAt_eq_of_open_square`, which
transports the fibre dimension across a commutative square of open immersions; this is what
lets the computation on a standard syntomic chart be read back on `X`.

## References

* [Stacks Project, Tag 02K0](https://stacks.math.columbia.edu/tag/02K0)
* [Stacks Project, Tag 02K1](https://stacks.math.columbia.edu/tag/02K1)
* [Stacks Project, Tag 02K2](https://stacks.math.columbia.edu/tag/02K2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A global complete intersection over a field has the same dimension at every point of its
spectrum. -/
private lemma localDimension_eq_of_globalCompleteIntersection
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (h : IsGlobalCompleteIntersection k A) (x : PrimeSpectrum A) :
    TopologicalSpace.localKrullDim (PrimeSpectrum A) x = ringKrullDim A := by
  classical
  rcases h with hzero | ⟨n, c, rel, e, hcn, hdim⟩
  · have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨x⟩
    exact False.elim (not_subsingleton_iff_nontrivial.mpr this hzero)
  have : Algebra.FiniteType k A :=
    IsGlobalCompleteIntersection.finiteType k
      (Or.inr ⟨n, c, rel, e, hcn, hdim⟩ : IsGlobalCompleteIntersection k A)
  obtain ⟨g, hg, hle⟩ :=
    PrimeSpectrum.exists_notMem_topologicalKrullDim_basicOpen_le_localKrullDim x
  have hne : ¬ Subsingleton (Localization.Away g) := by
    intro hs
    have hx : x ∈ Set.range (PrimeSpectrum.comap
        (algebraMap A (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hg
    obtain ⟨y, hy⟩ := hx
    have : Nontrivial (Localization.Away g) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨y⟩
    exact (not_subsingleton_iff_nontrivial.mpr this) hs
  have hdimloc := gci_localization_dim k A g n c rel e hdim hne
  have hlow : ringKrullDim A ≤
      TopologicalSpace.localKrullDim (PrimeSpectrum A) x := by
    rw [hdim, ← hdimloc]
    exact (PrimeSpectrum.ringKrullDim_le_topologicalKrullDim_basicOpen g _).trans hle
  have hupp : TopologicalSpace.localKrullDim (PrimeSpectrum A) x ≤ ringKrullDim A := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    exact le_iSup _ x
  exact le_antisymm hupp hlow

/-- Every fibre of a relative global complete intersection presentation is a global complete
intersection over the residue field. -/
private lemma globalCompleteIntersection_fiber
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι σ : Type*} [Finite ι] [Finite σ] (P : Algebra.Presentation R S ι σ)
    [P.IsRelativeGlobalCompleteIntersection] (p : Ideal R) [p.IsPrime] :
    IsGlobalCompleteIntersection p.ResidueField (p.Fiber S) := by
  classical
  rcases subsingleton_or_nontrivial (p.Fiber S) with h | h
  · exact Or.inl h
  have hdim :=
    ‹P.IsRelativeGlobalCompleteIntersection›.ringKrullDim_fiber_add_card_eq_card p h
  obtain ⟨hcn, hd⟩ := WithBot.le_and_eq_tsub_of_add_natCast_eq hdim
  let Q := (P.baseChange p.ResidueField).reindex
    (Finite.equivFin ι).symm (Finite.equivFin σ).symm
  exact Or.inr ⟨Nat.card ι, Nat.card σ, Q.relation,
    ((Ideal.quotientEquivAlgOfEq p.ResidueField Q.span_range_relation_eq_ker).trans
      (Q.quotientEquiv.restrictScalars p.ResidueField)).symm, hcn, hd⟩

/-- **Stacks 02K0.** For a presentation
`S = R[x₁, …, xₙ]/(f₁, …, fᶜ)` which is a relative global complete intersection, the
dimension at every point of the fibre of `Spec S → Spec R` is `n - c`. -/
@[stacks 02K0]
lemma fiberDimensionAt_eq_card_sub_card
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {ι σ : Type*} [Finite ι] [Finite σ] (P : Algebra.Presentation R S ι σ)
    [P.IsRelativeGlobalCompleteIntersection] (x : Spec (.of S)) :
    let f : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞) := by
  classical
  dsimp only
  let f : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let p : PrimeSpectrum R := f x
  let e := (Spec.fiberToSpecResidueFieldIso R S p).hom.left.homeomorph
  let y : PrimeSpectrum (p.asIdeal.Fiber S) := e (f.asFiber x)
  have hdim := localDimension_eq_of_globalCompleteIntersection
    (globalCompleteIntersection_fiber P p.asIdeal) y
  have hring :=
    ‹P.IsRelativeGlobalCompleteIntersection›.ringKrullDim_fiber_add_card_eq_card
      p.asIdeal (PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨y⟩)
  obtain ⟨_, hd⟩ := WithBot.le_and_eq_tsub_of_add_natCast_eq hring
  calc
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
        topologicalKrullDimAt (PrimeSpectrum (p.asIdeal.Fiber S)) y :=
      topologicalKrullDimAt_eq_of_homeomorph e _
    _ = TopologicalSpace.localKrullDim (PrimeSpectrum (p.asIdeal.Fiber S)) y :=
      TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim _ _
    _ = ringKrullDim (p.asIdeal.Fiber S) := hdim
    _ = _ := hd

/-- On a morphism of affine schemes carrying a relative global complete intersection
presentation, the fibre dimension is the number of variables minus the number of relations. -/
private lemma fiberDimensionAt_affine_eq_card
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (hAlg : algebraMap Γ(S, ⊤) Γ(X, ⊤) = f.appTop.hom)
    {n c : ℕ} (P : Algebra.Presentation Γ(S, ⊤) Γ(X, ⊤) (Fin n) (Fin c))
    [P.IsRelativeGlobalCompleteIntersection] (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      ((Nat.card (Fin n) - Nat.card (Fin c) : ℕ) : WithBot ℕ∞) := by
  let g : Spec Γ(X, ⊤) ⟶ Spec Γ(S, ⊤) := Spec.map f.appTop
  let j : Spec Γ(X, ⊤) ⟶ X := X.isoSpec.inv
  let i : Spec Γ(S, ⊤) ⟶ S := S.isoSpec.inv
  have : IsOpenImmersion j := inferInstance
  have : IsOpenImmersion i := inferInstance
  let q : Spec Γ(X, ⊤) := X.isoSpec.hom x
  have hq : j q = x := by
    simp [q, j]
  have hmap : f.appTop = CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)) :=
    congrArg CommRingCat.ofHom hAlg.symm
  have hcomp : j ≫ f = g ≫ i := by
    simpa [j, i, g] using (Scheme.isoSpec_inv_naturality f).symm
  have hdim := fiberDimensionAt_eq_card_sub_card P q
  rw [← hmap] at hdim
  calc
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
        topologicalKrullDimAt (g.fiber (g q)) (g.asFiber q) := by
      rw [← hq]
      exact (fiberDimensionAt_eq_of_open_square j f g i hcomp q).symm
    _ = ((Nat.card (Fin n) - Nat.card (Fin c) : ℕ) : WithBot ℕ∞) := by
      simpa [g] using hdim

/-- The local dimension of the fibre of a syntomic morphism is locally constant on its source. -/
@[stacks 02K1]
lemma isLocallyConstant_fiberDimensionAt {X S : Scheme.{u}} (f : X ⟶ S) (hf : Syntomic f) :
    IsLocallyConstant (fun x : X => topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVtop⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  let Vₐ : S.affineOpens := ⟨V, hV⟩
  obtain ⟨U, hxU, hUV, hstd⟩ := ((syntomicAt_tfae f x Vₐ hxV).out 1 2).mp (hf x)
  let g := f.resLE Vₐ.1 U.1 hUV
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine Vₐ.1.toScheme := Vₐ.2
  let : Algebra Γ(Vₐ.1, ⊤) Γ(U.1, ⊤) := g.appTop.hom.toAlgebra
  have hAlg : algebraMap Γ(Vₐ.1, ⊤) Γ(U.1, ⊤) = g.appTop.hom :=
    RingHom.algebraMap_toAlgebra _
  have hRGC : Algebra.IsRelativeGlobalCompleteIntersection Γ(Vₐ.1, ⊤) Γ(U.1, ⊤) := hstd
  rcases hRGC.out with ⟨n, c, P, hP⟩
  have : P.IsRelativeGlobalCompleteIntersection := hP
  have key (z : U.1.toScheme) : topologicalKrullDimAt (f.fiber (f (U.1.ι z)))
      (f.asFiber (U.1.ι z)) = ((Nat.card (Fin n) - Nat.card (Fin c) : ℕ) : WithBot ℕ∞) :=
    (fiberDimensionAt_eq_of_open_square U.1.ι f g Vₐ.1.ι (f.resLE_comp_ι hUV).symm z).symm.trans
      (fiberDimensionAt_affine_eq_card g hAlg P z)
  refine ⟨U.1, U.1.2, hxU, fun y hy => ?_⟩
  exact (key ⟨y, hy⟩).trans (key ⟨x, hxU⟩).symm

/-- A syntomic morphism whose fibres have local dimension `d` at every point. -/
@[stacks 02K2] abbrev SyntomicOfRelativeDimension (d : ℕ) {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Syntomic f ∧ ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)

end AlgebraicGeometry

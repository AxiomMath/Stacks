module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.KInjectiveTowerQuasiIso
public import StacksCore.Tactic.StacksAttribute

/-!
# The map from a complex into a candidate K-injective complex

Let `A` be an abelian category and let `K` be a cochain complex of objects of `A`. Suppose given
an inverse system `𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ` together with maps
`f n : τ_{≥ -n} K ⟶ 𝓘ₙ` forming a commutative ladder over the canonical truncation maps
`K ⟶ τ_{≥ -n} K`. The maps `K ⟶ τ_{≥ -n} K ⟶ 𝓘ₙ` then form a cone on `𝓘`, so they induce a
single map `K ⟶ lim 𝓘` compatible with the projections, and it is the only such map.

This is the displayed arrow `ℱ• → ℐ•` of Stacks 070P: for the tower of Stacks 070F, whose
complexes are bounded below with injective terms and whose transition maps are degreewise split
surjections, the limit `ℐ• = lim 𝓘` is K-injective by Stacks 070L, and the arrow produced here
is the candidate resolution. It need not be a quasi-isomorphism; Stacks 070Q gives a criterion,
which is recorded here for this arrow in `quasiIso_toLimitOfTruncGEResolutions`.

## Main definitions

* `CochainComplex.toLimitOfTruncGEResolutions`: the map `K ⟶ lim 𝓘` induced by resolutions of
  the truncations of `K`.

## Main results

* `CochainComplex.toLimitOfTruncGEResolutions_π`: it is compatible with the projections.
* `CochainComplex.eq_toLimitOfTruncGEResolutions`: it is the unique such map.
* `Stacks.Cohomology.quasiIso_toLimitOfTruncGEResolutions`: on a ringed site it is a
  quasi-isomorphism under the cohomology vanishing hypotheses of Stacks 070Q.

## References

* [Stacks Project, Tag 070P](https://stacks.math.columbia.edu/tag/070P)
* [Stacks Project, Tag 070F](https://stacks.math.columbia.edu/tag/070F)
* [Stacks Project, Tag 070Q](https://stacks.math.columbia.edu/tag/070Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **Stacks Project, Tag 070P**, the displayed arrow `ℱ• → ℐ•`. Given an inverse system `𝓘` of
cochain complexes and maps `f n : τ_{≥ -n} K ⟶ 𝓘ₙ` commuting with the canonical truncation maps
of `K`, this is the induced map `K ⟶ lim 𝓘`. For the tower of Stacks 070F the target is the
candidate K-injective complex of Stacks 070L. -/
@[stacks 070P]
def toLimitOfTruncGEResolutions (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit 𝓘]
    (K : CochainComplex A ℤ) (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ 𝓘.obj ⟨n⟩)
    (hladder : ∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫
      𝓘.map (homOfLE (Nat.le_succ n)).op = K.πTruncGE (-(n : ℤ)) ≫ f n) :
    K ⟶ limit 𝓘 :=
  limit.lift 𝓘
    { pt := K
      π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj K) (G := 𝓘)
        (fun n => K.πTruncGE (-(n : ℤ)) ≫ f n) (fun n => by simpa using (hladder n).symm) }

variable {𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ} [HasLimit 𝓘] {K : CochainComplex A ℤ}
  {f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ 𝓘.obj ⟨n⟩}
  {hladder : ∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫
    𝓘.map (homOfLE (Nat.le_succ n)).op = K.πTruncGE (-(n : ℤ)) ≫ f n}

/-- The arrow of Stacks 070P composed with the `n`-th projection is `K ⟶ τ_{≥ -n} K ⟶ 𝓘ₙ`. -/
@[simp]
lemma toLimitOfTruncGEResolutions_π (n : ℕ) :
    toLimitOfTruncGEResolutions 𝓘 K f hladder ≫ limit.π 𝓘 ⟨n⟩ =
      K.πTruncGE (-(n : ℤ)) ≫ f n :=
  limit.lift_π (F := 𝓘) _ (Opposite.op n)

/-- The arrow of Stacks 070P is the only map `K ⟶ lim 𝓘` compatible with the projections. -/
lemma eq_toLimitOfTruncGEResolutions (γ : K ⟶ limit 𝓘)
    (hγ : ∀ n : ℕ, γ ≫ limit.π 𝓘 ⟨n⟩ = K.πTruncGE (-(n : ℤ)) ≫ f n) :
    γ = toLimitOfTruncGEResolutions 𝓘 K f hladder := by
  refine limit.hom_ext fun j => ?_
  obtain ⟨n⟩ := j
  rw [hγ n, toLimitOfTruncGEResolutions_π]

end CochainComplex

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 070Q** for the arrow of Stacks 070P. On a ringed site, if `𝓘` is an
inverse system of K-injective complexes with degreewise split-epimorphic transition maps
resolving the truncations `τ_{≥ -n} K`, and if a subset `B` of the objects covers every object
with `H^p(V, H^q(K)) = 0` for `V ∈ B`, `p > d` and `q < 0`, then the canonical map
`K ⟶ lim 𝓘` is a quasi-isomorphism. -/
theorem quasiIso_toLimitOfTruncGEResolutions {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} O)]
    (K : CochainComplex (SheafOfModules.{u} O) ℤ)
    (𝓘 : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} O) ℤ)
    (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ 𝓘.obj ⟨n⟩)
    (hf : ∀ n : ℕ, QuasiIso (f n))
    (hcompat : ∀ n : ℕ,
      K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫ 𝓘.map (homOfLE (Nat.le_succ n)).op =
        K.πTruncGE (-(n : ℤ)) ≫ f n)
    (h𝓘 : ∀ n : ℕ, (𝓘.obj ⟨n⟩).IsKInjective)
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((𝓘.map (homOfLE (Nat.le_succ n)).op).f i))
    [HasLimit 𝓘] (B : Set C) (d : ℕ)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ V : C, B V → ∀ p : ℕ, d < p → ∀ q : ℤ, q < 0 →
      IsZero (moduleCohomology O V p
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) q).obj
          (DerivedCategory.Q.obj K)))) :
    QuasiIso (CochainComplex.toLimitOfTruncGEResolutions 𝓘 K f hcompat) :=
  quasiIso_to_limit_of_truncGE_resolutions O K 𝓘 f hf hcompat h𝓘 hsplit _
    CochainComplex.toLimitOfTruncGEResolutions_π B d hB hvan

end Stacks.Cohomology

end

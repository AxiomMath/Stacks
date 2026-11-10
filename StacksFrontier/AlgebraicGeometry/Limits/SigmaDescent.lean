module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Coproduct

/-!
# Descending morphisms along an arbitrary coproduct of schemes

The category of schemes is finitary extensive, and
`StacksFrontier.CategoryTheory.Limits.BinaryCoproductDescent` records what that gives for a
*binary* coproduct: a morphism `T ⟶ X ⨿ Y` decomposes `T` into two summands, over each of
which a morphism out of `T` may be built or compared. Schemes have the same property for a
coproduct indexed by an arbitrary small type, which is not an instance of extensivity as
Mathlib states it. It is proved here directly: the pullbacks of `f : T ⟶ ∐ X` along the
coprojections are open immersions with pairwise disjoint images covering `T`, so they
exhibit `T` as a coproduct by `AlgebraicGeometry.nonempty_isColimit_cofanMk_of`.

## Main definitions

* `AlgebraicGeometry.isColimitCofanPullbackSigma`: the pullbacks of a morphism into a
  coproduct of schemes along the coprojections exhibit its source as that coproduct.

## Main results

* `AlgebraicGeometry.hom_ext_of_sigma_cases`: two morphisms out of `T` agree as soon as they
  agree over each summand.
* `AlgebraicGeometry.exists_lift_of_sigma_cases`: a pair of morphisms out of `T` factors
  through a pair of morphisms out of `R` as soon as it does so over each summand.
* `AlgebraicGeometry.etale_sigmaDesc`: a morphism out of a coproduct of schemes is étale as
  soon as all of its components are.

## Implementation notes

The "case" form of the two descent statements takes for the data over a summand an arbitrary
test scheme `W` with a morphism `i : W ⟶ T` and a factorization of `i ≫ f` through the
coprojection of that summand, rather than the chosen pullback: that is the form in which a
caller can supply the hypothesis, the chosen pullback being an instance of it by
`CategoryTheory.Limits.pullback.condition`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {σ : Type*} [Small.{u} σ] {X : σ → Scheme.{u}}

/-- The preimage of two disjoint open subschemes along a morphism are disjoint. -/
theorem disjoint_preimage_opens_of_disjoint {Y Z : Scheme.{u}} (f : Y ⟶ Z) {U V : Z.Opens}
    (h : Disjoint U V) : Disjoint (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) := by
  rw [← TopologicalSpace.Opens.coe_disjoint] at h ⊢
  simpa using h.preimage f.base

/-- The images of the coprojections of a coproduct of schemes cover it. -/
theorem iSup_opensRange_sigmaι_of_small : ⨆ i, (Sigma.ι X i).opensRange = ⊤ := by
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨i, y, rfl⟩ := (sigmaOpenCover X).exists_eq x
  simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion]
  exact ⟨i, y, rfl⟩

/-- **The pullbacks of a morphism into a coproduct of schemes form a coproduct.** Base change
along `f : T ⟶ ∐ X` turns the coproduct cofan on the `X i` into a coproduct cofan on the
fibre products `T ×_{∐ X} X i`. -/
noncomputable def isColimitCofanPullbackSigma {T : Scheme.{u}} (f : T ⟶ ∐ X) :
    IsColimit (Cofan.mk T fun i ↦ pullback.fst f (Sigma.ι X i)) := by
  refine (nonempty_isColimit_cofanMk_of (fun i ↦ pullback.fst f (Sigma.ι X i)) ?_ ?_).some
  · simp only [Scheme.Hom.opensRange_pullbackFst]
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover X).exists_eq (f.base x)
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion]
    exact ⟨i, y, hy⟩
  · intro i j hij
    simp only [Function.onFun, Scheme.Hom.opensRange_pullbackFst]
    exact disjoint_preimage_opens_of_disjoint f (disjoint_opensRange_sigmaι X i j hij)

/-- Two morphisms out of `T` agree as soon as they agree after base change along `f` to each
summand of a coproduct. -/
theorem hom_ext_of_pullback_sigma {T Z : Scheme.{u}} (f : T ⟶ ∐ X) (a b : T ⟶ Z)
    (h : ∀ i : σ, pullback.fst f (Sigma.ι X i) ≫ a = pullback.fst f (Sigma.ι X i) ≫ b) :
    a = b :=
  Cofan.IsColimit.hom_ext (isColimitCofanPullbackSigma f) a b h

/-- **Two morphisms out of `T` agree as soon as they agree over each summand** of a coproduct
into which `T` maps. The data over a summand is a test scheme `W` with a morphism to `T`
whose composite with `f` factors through that coprojection. -/
theorem hom_ext_of_sigma_cases {T Z : Scheme.{u}} (f : T ⟶ ∐ X) (a b : T ⟶ Z)
    (h : ∀ (i : σ) (W : Scheme.{u}) (p : W ⟶ T) (g : W ⟶ X i),
      p ≫ f = g ≫ Sigma.ι X i → p ≫ a = p ≫ b) :
    a = b :=
  hom_ext_of_pullback_sigma f a b fun i ↦
    h i _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition

/-- **A pair of morphisms out of `T` factors through a pair of morphisms out of `R` as soon as
it does so over each summand** of a coproduct into which `T` maps. The data over a summand is
as in `AlgebraicGeometry.hom_ext_of_sigma_cases`. -/
theorem exists_lift_of_sigma_cases {T R A C : Scheme.{u}} (f : T ⟶ ∐ X)
    (r : R ⟶ A) (s : R ⟶ C) (a : T ⟶ A) (b : T ⟶ C)
    (h : ∀ (i : σ) (W : Scheme.{u}) (p : W ⟶ T) (g : W ⟶ X i), p ≫ f = g ≫ Sigma.ι X i →
      ∃ l : W ⟶ R, l ≫ r = p ≫ a ∧ l ≫ s = p ≫ b) :
    ∃ l : T ⟶ R, l ≫ r = a ∧ l ≫ s = b := by
  choose l hl₁ hl₂ using fun i ↦
    h i _ (pullback.fst f (Sigma.ι X i)) (pullback.snd _ _) pullback.condition
  refine ⟨Cofan.IsColimit.desc (isColimitCofanPullbackSigma f) l, ?_, ?_⟩ <;>
    refine hom_ext_of_pullback_sigma f _ _ fun i ↦ ?_ <;>
    rw [← Category.assoc,
      show pullback.fst f (Sigma.ι X i) ≫
          Cofan.IsColimit.desc (isColimitCofanPullbackSigma f) l = l i from
        Cofan.IsColimit.fac (isColimitCofanPullbackSigma f) l i]
  · exact hl₁ i
  · exact hl₂ i

/-- A morphism out of a coproduct of schemes is étale as soon as all of its components
are. -/
theorem etale_sigmaDesc {T : Scheme.{u}} (α : ∀ i, X i ⟶ T) (hα : ∀ i, Etale (α i)) :
    Etale (Sigma.desc α) := by
  refine IsZariskiLocalAtSource.of_openCover (P := @Etale) (𝒰 := sigmaOpenCover X) fun i ↦ ?_
  have h : (sigmaOpenCover X).f i ≫ Sigma.desc α = α i := Sigma.ι_comp_desc α i
  rw [h]
  exact hα i

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorRepresentableLocal
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.RingTheory.Norm.Projective
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field

/-!
# Hilbert families and disjoint unions

This file collects the bookkeeping needed to work with Hilbert families when either the base or
the ambient scheme is a disjoint union.

* An ideal sheaf is glued from ideal sheaves on finitely many open and closed pieces with
  pairwise disjoint images: `Stacks.Hilbert.comap_glueIdeal`.
* Global functions on a scheme which is the disjoint union of two open pieces are pairs of
  functions on the pieces: `Stacks.Hilbert.bijective_prod_appTop_of_isCompl`.
* Ranks of finite locally free modules add up in products:
  `Stacks.Hilbert.isFiniteLocallyFreeOfRank_prod`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-! ### Modules -/

/-- A finite locally free module of rank `d` is finite locally free. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] {d : ℕ} (h : Module.IsFiniteLocallyFreeOfRank R M d) :
    Module.IsFiniteLocallyFree R M := by
  obtain ⟨ι, f, hspan, hb⟩ := h
  exact ⟨ι, f, hspan, fun i ↦ ⟨Module.Free.of_basis (hb i).some,
    Module.Finite.of_basis (hb i).some⟩⟩

/-- **Ranks add up in products.** -/
theorem isFiniteLocallyFreeOfRank_prod {R M N : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {a b : ℕ}
    (hM : Module.IsFiniteLocallyFreeOfRank R M a) (hN : Module.IsFiniteLocallyFreeOfRank R N b) :
    Module.IsFiniteLocallyFreeOfRank R (M × N) (a + b) := by
  have := Module.IsFiniteLocallyFreeOfRank.finite hM
  have := Module.IsFiniteLocallyFreeOfRank.finite hN
  have := (Module.finite_and_projective_of_isFiniteLocallyFree
    (isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank hM)).2
  have := (Module.finite_and_projective_of_isFiniteLocallyFree
    (isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank hN)).2
  refine Module.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq _ fun p ↦ ?_
  rw [Module.rankAtStalk_prod, Pi.add_apply,
    Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank a hM,
    Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank b hN]

/-! ### Disjoint unions of schemes -/

/-- Two open immersions with complementary images exhibit their target as a coproduct. -/
theorem isIso_coprod_desc_of_isCompl {A₁ A₂ B : Scheme.{u}} (f : A₁ ⟶ B) (g : A₂ ⟶ B)
    [IsOpenImmersion f] [IsOpenImmersion g] (h : IsCompl f.opensRange g.opensRange) :
    IsIso (coprod.desc f g) := by
  obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl f g h
  let e := (coprodIsCoprod A₁ A₂).coconePointUniqueUpToIso hc
  have he : coprod.desc f g = e.hom := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc]
      exact ((coprodIsCoprod A₁ A₂).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.left⟩).symm
    · rw [coprod.inr_desc]
      exact ((coprodIsCoprod A₁ A₂).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.right⟩).symm
  exact he ▸ e.isIso_hom

/-- **Global functions on a disjoint union.** If two open immersions have complementary images,
pulling back global functions along them identifies the functions on the target with pairs of
functions on the sources. -/
theorem bijective_prod_appTop_of_isCompl {A₁ A₂ B : Scheme.{u}} (f : A₁ ⟶ B) (g : A₂ ⟶ B)
    [IsOpenImmersion f] [IsOpenImmersion g] (h : IsCompl f.opensRange g.opensRange) :
    Function.Bijective (RingHom.prod f.appTop.hom g.appTop.hom) :=
  have := isIso_coprod_desc_of_isCompl f g h
  bijective_prod_appTop f g

/-- An open immersion whose image is closed is a closed immersion. -/
theorem isClosedImmersion_of_isOpenImmersion {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (h : IsClosed (Set.range f)) : IsClosedImmersion f :=
  IsClosedImmersion.of_isPreimmersion f h

/-! ### Gluing ideal sheaves along open and closed pieces -/

section Glue

variable {B : Scheme.{u}}

/-- The pushforward of an ideal sheaf is the kernel of its inclusion composed with `j`. -/
private theorem map_eq_ker_subschemeι_comp {A : Scheme.{u}} (j : A ⟶ B) (I : A.IdealSheafData) :
    I.map j = (I.subschemeι ≫ j).ker := by
  rw [← Scheme.IdealSheafData.map_ker, I.ker_subschemeι]

/-- Pulling back the pushforward of an ideal sheaf along a closed immersion recovers it. -/
theorem comap_map_of_isClosedImmersion {A : Scheme.{u}} (j : A ⟶ B) [IsClosedImmersion j]
    (I : A.IdealSheafData) : (I.map j).comap j = I := by
  have hpb : IsPullback I.subschemeι (𝟙 I.subscheme) j (I.subschemeι ≫ j) := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.snd) (fun s ↦ ?_) (fun s ↦ ?_)
      (fun s m _ hm ↦ ?_)⟩⟩
    · exact (cancel_mono j).mp (by rw [Category.assoc, s.condition])
    · simp
    · simpa using hm
  rw [map_eq_ker_subschemeι_comp, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← hpb.isoPullback_inv_fst,
    Scheme.Hom.ker_comp_of_isIso, I.ker_subschemeι]

/-- Pulling back the pushforward of an ideal sheaf along a closed immersion with image disjoint
from the image of an open immersion gives the unit ideal. -/
theorem comap_map_eq_top_of_disjoint {A A' : Scheme.{u}} (j : A ⟶ B) (j' : A' ⟶ B)
    [IsClosedImmersion j'] (h : Disjoint (Set.range j) (Set.range j')) (I : A'.IdealSheafData) :
    (I.map j').comap j = ⊤ := by
  rw [map_eq_ker_subschemeι_comp, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have : IsEmpty ↑(Limits.pullback j (I.subschemeι ≫ j')) := by
    rw [Scheme.isEmpty_pullback_iff]
    refine h.mono_right ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  exact Scheme.ker_eq_top_of_isEmpty _

/-- Pulling back along an open immersion commutes with finite intersections of ideal sheaves. -/
theorem comap_iInf_of_isOpenImmersion {A : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j]
    {ι : Type*} [Finite ι] (I : ι → B.IdealSheafData) :
    (⨅ i, I i).comap j = ⨅ i, (I i).comap j := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_iInf,
    Scheme.IdealSheafData.ideal_iInf]
  simp only [iInf_apply, Ideal.comap_iInf, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

/-- The ideal sheaf glued from ideal sheaves on finitely many open and closed pieces. -/
def glueIdeal {ι : Type*} {A : ι → Scheme.{u}} (j : ∀ i, A i ⟶ B)
    (I : ∀ i, (A i).IdealSheafData) : B.IdealSheafData :=
  ⨅ i, (I i).map (j i)

/-- **Gluing ideal sheaves.** Over finitely many pieces which are open and closed in `B` and
have pairwise disjoint images, the glued ideal sheaf restricts to the given ones. -/
theorem comap_glueIdeal {ι : Type*} [Finite ι] {A : ι → Scheme.{u}} (j : ∀ i, A i ⟶ B)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i)) (Set.range (j i')))
    (I : ∀ i, (A i).IdealSheafData) (k : ι) : (glueIdeal j I).comap (j k) = I k := by
  rw [glueIdeal, comap_iInf_of_isOpenImmersion]
  refine le_antisymm (iInf_le_of_le k (comap_map_of_isClosedImmersion _ _).le) (le_iInf fun i ↦ ?_)
  obtain rfl | hik := eq_or_ne i k
  · exact (comap_map_of_isClosedImmersion _ _).ge
  · rw [comap_map_eq_top_of_disjoint _ _ (hdisj hik.symm)]
    exact le_top

end Glue

end Stacks.Hilbert

end

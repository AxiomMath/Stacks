module
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChangeDecomposition
import all StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChangeDecomposition

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.FiniteExistence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Approximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FiniteCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Scheme.ReductionMap
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedLocallyClosed
public import StacksFrontier.Topology.Stratification.RefineConstructible
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Reduction

/-!
# A finite étale thickening after a surjective base change

For a quasi-finite morphism of finite presentation `f : Y ⟶ X` of affine schemes, there is a
surjective morphism `g : X' ⟶ X` locally of finite type from an affine scheme such that the base
change `Y ×_X X'` contains a thickening of a scheme finite étale over `X'`.

## Main results

* `AlgebraicGeometry.exists_surjective_affine_baseChange_thickening_finiteEtale_general`: after a
  surjective base change `g : X' ⟶ X` locally of finite type with `X'` affine, the pullback of
  `f` contains a thickening `Z' ⟶ Y ×_X X'` with `Z'` finite étale over `X'`.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

private lemma exists_thickening_finiteEtale_of_finite_family_general
    {Y X : Scheme.{u}} (f : Y ⟶ X) {n : ℕ}
    (S : Fin n → Scheme.{u}) [∀ i, IsAffine (S i)]
    (g : ∀ i, S i ⟶ X) (hgft : ∀ i, LocallyOfFiniteType (g i))
    (hg : (⋃ i, Set.range (g i).base) = Set.univ)
    (Z : Fin n → Scheme.{u}) (j : ∀ i, Z i ⟶ pullback f (g i))
    (hj : ∀ i, IsClosedImmersion (j i) ∧ Function.Surjective (j i))
    (hfin : ∀ i, IsFinite (j i ≫ pullback.snd f (g i)))
    (het : ∀ i, Etale (j i ≫ pullback.snd f (g i))) :
    ∃ (X' : Scheme.{u}) (_ : IsAffine X') (g : X' ⟶ X),
      Surjective g ∧ LocallyOfFiniteType g ∧ ∃ (Z' : Scheme.{u}) (i : Z' ⟶ pullback f g),
        (IsClosedImmersion i ∧ Function.Surjective i) ∧
        IsFinite (i ≫ pullback.snd f g) ∧ Etale (i ≫ pullback.snd f g) := by
  let hp := isPullback_sigmaDesc_left f g
  let e := hp.isoPullback
  let j' := (Sigma.desc fun i => j i ≫ Sigma.ι (fun i => pullback f (g i)) i) ≫ e.hom
  have hj' : IsClosedImmersion
      (Sigma.desc fun i => j i ≫ Sigma.ι (fun i => pullback f (g i)) i) :=
    property_sigmaMap _ j (fun i => (hj i).1)
  have hj's : Surjective ((Sigma.desc fun i => j i ≫ Sigma.ι (fun i => pullback f (g i)) i)) :=
    property_sigmaMap _ j (fun i => ⟨(hj i).2⟩)
  have hq : j' ≫ pullback.snd f (Sigma.desc g) =
      Sigma.desc (fun i => (j i ≫ pullback.snd f (g i)) ≫ Sigma.ι S i) := by
    dsimp [j', e]
    rw [Category.assoc, hp.isoPullback_hom_snd]
    exact Sigma.hom_ext _ _ fun i => by simp
  refine ⟨∐ S, inferInstance, Sigma.desc g,
    Surjective.sigmaDesc_of_union_range_eq_univ hg,
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) hgft, ∐ Z, j', ?_, ?_⟩
  · exact ⟨inferInstance, (show Surjective j' from inferInstance).surj⟩
  · rw [hq]
    exact ⟨property_sigmaMap _ _ hfin, property_sigmaMap _ _ het⟩

private lemma exists_thickening_finiteEtale_of_split_reductions_general
    {Y X : Scheme.{u}} (f : Y ⟶ X) {n : ℕ}
    (S : Fin n → Scheme.{u}) (s : ∀ i, S i ⟶ X) [∀ i, IsAffine (S i)]
    (hsft : ∀ i, LocallyOfFiniteType (s i))
    (hcover : (⋃ i, Set.range (s i).base) = Set.univ)
    (hsplit : ∀ i, ∃ (S' : Scheme.{u}) (g : S' ⟶ S i),
        Surjective g ∧ IsAffineHom g ∧ LocallyOfFiniteType g ∧
        ∃ (m : ℕ)
          (q : (pullback f (g ≫ s i)).nilradical.subscheme ⟶
            S'.nilradical.subscheme)
          (e : (pullback f (g ≫ s i)).nilradical.subscheme ≅
            ∐ (fun _ : Fin m ↦ S'.nilradical.subscheme)),
          q ≫ S'.nilradical.subschemeι =
              (pullback f (g ≫ s i)).nilradical.subschemeι ≫
                pullback.snd f (g ≫ s i) ∧
          e.hom ≫ Sigma.desc (fun _ : Fin m ↦ 𝟙 S'.nilradical.subscheme) = q) :
    ∃ (X' : Scheme.{u}) (_ : IsAffine X') (g : X' ⟶ X),
      Surjective g ∧ LocallyOfFiniteType g ∧ ∃ (Z' : Scheme.{u}) (i : Z' ⟶ pullback f g),
        (IsClosedImmersion i ∧ Function.Surjective i) ∧
        IsFinite (i ≫ pullback.snd f g) ∧ Etale (i ≫ pullback.snd f g) := by
  classical
  choose T g hg ha hgft m q e hq he using hsplit
  let : ∀ i, IsAffineHom (g i) := ha
  let : ∀ i, IsAffine (T i) := fun i => isAffine_of_isAffineHom (g i)
  let A (i) := (T i).nilradical.subscheme
  have : ∀ i, IsAffine (A i) := fun i => isAffine_of_isAffineHom (T i).nilradical.subschemeι
  let h (i) : A i ⟶ X := (T i).nilradical.subschemeι ≫ (g i ≫ s i)
  let Z (i) := (pullback f (g i ≫ s i)).nilradical.subscheme
  have hlocal (i) : ∃ j : Z i ⟶ pullback f (h i),
      (IsClosedImmersion j ∧ Function.Surjective j) ∧
        IsFinite (j ≫ pullback.snd f (h i)) ∧ Etale (j ≫ pullback.snd f (h i)) := by
    obtain ⟨j, hj, hfin, het⟩ := exists_thickening_finiteEtale_over_reduction
      (pullback.snd f (g i ≫ s i)) (q i) (hq i) (e i) (he i)
    let a := pullbackLeftPullbackSndIso f (g i ≫ s i) (T i).nilradical.subschemeι
    have : IsClosedImmersion j := hj.1
    have : Surjective j := ⟨hj.2⟩
    refine ⟨j ≫ a.hom, ⟨inferInstance, (show Surjective (j ≫ a.hom) from inferInstance).surj⟩,
      ?_⟩
    simpa only [a, h, Category.assoc, pullbackLeftPullbackSndIso_hom_snd] using And.intro hfin het
  choose j hj hfin het using hlocal
  have hhft : ∀ i, LocallyOfFiniteType (h i) := fun i => by
    have := hgft i
    have := hsft i
    dsimp only [h]
    infer_instance
  refine exists_thickening_finiteEtale_of_finite_family_general f A h hhft
    (Set.eq_univ_of_forall fun x => ?_) Z j hj hfin het
  have hx : x ∈ ⋃ i, Set.range (s i).base := by rw [hcover]; trivial
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
  obtain ⟨z, hz⟩ := (hg i).surj y
  obtain ⟨w, hw⟩ := (Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical (T i)).2 z
  refine Set.mem_iUnion.mpr ⟨i, w, ?_⟩
  change (s i) ((g i) ((T i).nilradical.subschemeι w)) = x
  rw [hw, hz, hy]

/-- For a quasi-finite morphism `f : Y ⟶ X` of finite presentation between affine schemes, there
is a surjective morphism `g : X' ⟶ X` locally of finite type, with `X'` affine, and a thickening
`i : Z' ⟶ Y ×_X X'` such that the composite `Z' ⟶ X'` is finite and étale. -/
public theorem exists_surjective_affine_baseChange_thickening_finiteEtale_general
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffine Y] [IsAffine X]
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]
    (hfp : FinitePresentation f) :
    ∃ (X' : Scheme.{u}) (_ : IsAffine X') (g : X' ⟶ X),
      Surjective g ∧ LocallyOfFiniteType g ∧
      ∃ (Z' : Scheme.{u}) (i : Z' ⟶ pullback f g),
        Stacks.Thickenings.IsThickening i ∧
        IsFinite (i ≫ pullback.snd f g) ∧
        Etale (i ≫ pullback.snd f g) := by
  obtain ⟨n, S, s, hS, _, hcover, hsplit⟩ :=
    exists_finite_affine_stratification_split_reduction f hfp
  let : ∀ i, IsAffine (S i) := fun i => (hS i).1
  exact exists_thickening_finiteEtale_of_split_reductions_general f S s
    (fun i => by have := (hS i).2.1; infer_instance) hcover (fun i => by
    obtain ⟨T, g, hg, hfree, m, q, e, hq, he⟩ := hsplit i
    have : IsFinite g :=
      ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp
        hfree).1
    exact ⟨T, g, hg, hfree.toIsAffineHom, inferInstance, m, q, e, hq, he⟩)

end AlgebraicGeometry

end

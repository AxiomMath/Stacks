module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackRigidification
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSiteCoverings

/-!
# Descent of homomorphisms of quasi-coherent modules along fppf covering sieves

`StacksFrontier/AlgebraicGeometry/Quot/PicardStackRigidification.lean` states Descent,
Proposition 023T for the modules on the small étale sites of the schemes of the big fppf site as
the predicate `AlgebraicGeometry.Space.ModuleHomFppfDescent`, which the descent statements of
Stacks 0D29 consume.  This file proves that statement for **quasi-coherent** modules, which is
the generality of the source, from the unconditional full faithfulness of fpqc descent of
quasi-coherent modules on algebraic spaces (Stacks 04W8).

## Main results

* `AlgebraicGeometry.Space.moduleHomRefine_eq_restrictForm`: the restriction to a refinement of
  `PicardStackRigidification.lean` is the restricted reading of
  `Spaces/Descent/QuasiCoherent/FpqcChartFullness.lean`.
* `AlgebraicGeometry.Space.isPairwiseCompatible_restrictForm_of_moduleHomFamilyCompatible`: a
  compatible family, restricted to a family factoring through it, is pairwise compatible in the
  sense of Stacks 04W3.
* `AlgebraicGeometry.Space.existsUnique_modulePullback_map_eq_of_refinement`: a compatible
  family of homomorphisms of the inverse images of two quasi-coherent modules along a family
  refined by an fpqc covering descends uniquely.
* `AlgebraicGeometry.Space.existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible`:
  **Descent, Proposition 023T** in the form of `AlgebraicGeometry.Space.ModuleHomFppfDescent`,
  for quasi-coherent modules.

## Implementation notes

`AlgebraicGeometry.Space.ModuleHomFppfDescent` quantifies over *all* modules on the small étale
site, with no quasi-coherence; the source's Proposition 023T is about quasi-coherent modules, and
that is the statement proved here.  The modules the Picard stack applies it to — the structure
sheaf and the pullback of an invertible module — are quasi-coherent.

In the proof of `…isPairwiseCompatible_restrictForm_of_moduleHomFamilyCompatible` the restricted
family is an *opaque* family `w` together with its defining equation, rather than the
`fun k ↦ …` it equals: with the lambda in place the kernel does not finish checking the step
that reads the pairwise condition off the canonical comparison.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 0D29](https://stacks.math.columbia.edu/tag/0D29)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open QuasiCoherentDescent in
/-- The restriction of a homomorphism of inverse images to a refinement is its restricted
reading through the comparison of Stacks 03LU. -/
theorem moduleHomRefine_eq_restrictForm {V W Z : AlgebraicSpaces B S hS} {a : W ⟶ V}
    {q : V ⟶ Z} {k : W ⟶ Z} (hk : a ≫ q = k) (M N : Modules.{u, u} B S hS Z.1 Z.2)
    (v : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N) :
    moduleHomRefine hk M N v = restrictForm B S hS a q k hk v :=
  restrictPullbackHom_eq_restrictForm a hk v

/-- Two restrictions of members of a compatible family along maps agreeing over `X` coincide. -/
private theorem restrictForm_eq_of_moduleHomFamilyCompatible {ι : Type*}
    {X : AlgebraicSpaces B S hS} {Ui : ι → AlgebraicSpaces B S hS} {p : ∀ i, Ui i ⟶ X}
    {M N : Modules.{u, u} B S hS X.1 X.2}
    {α : ∀ i, (modulePullback B S hS (p i)).obj M ⟶ (modulePullback B S hS (p i)).obj N}
    (hα : ModuleHomFamilyCompatible M N p α) {Y : AlgebraicSpaces B S hS} {i j : ι}
    {a : Y ⟶ Ui i} {b : Y ⟶ Ui j} {k : Y ⟶ X} (ha : a ≫ p i = k) (hb : b ≫ p j = k) :
    QuasiCoherentDescent.restrictForm B S hS a (p i) k ha (α i) =
      QuasiCoherentDescent.restrictForm B S hS b (p j) k hb (α j) := by
  subst ha
  have h := hα Y i j a b (hb.symm ▸ rfl)
  rw [moduleHomRefine_eq_restrictForm, moduleHomRefine_eq_restrictForm] at h
  exact h

open QuasiCoherentDescent in
/-- A compatible family, restricted to a family of algebraic spaces each member of which factors
through a member of the original one, is pairwise compatible in the sense of Stacks 04W3. -/
theorem isPairwiseCompatible_restrictForm_of_moduleHomFamilyCompatible {ι J : Type*}
    {X : AlgebraicSpaces B S hS} {Ui : ι → AlgebraicSpaces B S hS} (p : ∀ i, Ui i ⟶ X)
    {Xk : J → AlgebraicSpaces B S hS} (v : ∀ k, Xk k ⟶ X) (ik : J → ι)
    (t : ∀ k, Xk k ⟶ Ui (ik k)) (hvt : ∀ k, t k ≫ p (ik k) = v k)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (α : ∀ i, (modulePullback B S hS (p i)).obj M ⟶ (modulePullback B S hS (p i)).obj N)
    (hα : ModuleHomFamilyCompatible M N p α)
    (w : ∀ k, (modulePullback B S hS (v k)).obj M ⟶ (modulePullback B S hS (v k)).obj N)
    (hw : ∀ k, w k = restrictForm B S hS (t k) (p (ik k)) (v k) (hvt k) (α (ik k))) :
    IsPairwiseCompatible B S hS Xk v w := by
  intro k l
  have hρk : pairFst B S hS Xk v k l ≫ v k =
      (pairFst B S hS Xk v k l ≫ t k) ≫ p (ik k) := by
    rw [Category.assoc, hvt k]
  have hρl : pairSnd B S hS Xk v k l ≫ v l =
      (pairFst B S hS Xk v k l ≫ t k) ≫ p (ik k) :=
    (pair_condition B S hS Xk v k l).symm.trans hρk
  have hab : (pairFst B S hS Xk v k l ≫ t k) ≫ p (ik k) =
      (pairSnd B S hS Xk v k l ≫ t l) ≫ p (ik l) := by
    rw [Category.assoc, Category.assoc, hvt k, hvt l]
    exact pair_condition B S hS Xk v k l
  refine canonicalComparison_naturality_of_restrictForm_eq B S hS _ _ (v k) (v l)
    ((pairFst B S hS Xk v k l ≫ t k) ≫ p (ik k)) hρk hρl _ (w k) (w l) ?_
  rw [hw k, hw l,
    restrictForm_comp B S hS (pairFst B S hS Xk v k l) (t k) (p (ik k)) (v k) (hvt k) _ rfl
      _ hρk rfl,
    restrictForm_comp B S hS (pairSnd B S hS Xk v k l) (t l) (p (ik l)) (v l) (hvt l) _ rfl
      _ hρl hab.symm]
  exact restrictForm_eq_of_moduleHomFamilyCompatible hα _ hab.symm

open QuasiCoherentDescent in
/-- **Descent of homomorphisms of quasi-coherent modules along a family refined by an fpqc
covering.**  Let `(p i : U i ⟶ X)` be a family of algebraic spaces over `X` and let
`(v k : X k ⟶ X)` be an fpqc covering each member of which factors as `t k ≫ p (ik k)`.  For two
quasi-coherent `𝒪_X`-modules, a family of homomorphisms `(p i)^*M ⟶ (p i)^*N` compatible in the
sense of `AlgebraicGeometry.Space.ModuleHomFamilyCompatible` is the family of inverse images of
exactly one homomorphism `M ⟶ N`.

The family is restricted to the covering, where it is pairwise compatible and descends by the
fullness half of Stacks 04W8; the descended homomorphism has the prescribed inverse images
because they agree after pullback along the base change of the covering to each `U i`, which is
again an fpqc covering, by the faithfulness half. -/
theorem existsUnique_modulePullback_map_eq_of_refinement {ι J : Type*}
    {X : AlgebraicSpaces B S hS} {Ui : ι → AlgebraicSpaces B S hS} (p : ∀ i, Ui i ⟶ X)
    {Xk : J → AlgebraicSpaces B S hS} (v : ∀ k, Xk k ⟶ X)
    (hv : IsFpqcCovering B S hS fun k ↦ (v k).hom) (ik : J → ι) (t : ∀ k, Xk k ⟶ Ui (ik k))
    (hvt : ∀ k, t k ≫ p (ik k) = v k)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (α : ∀ i, (modulePullback B S hS (p i)).obj M ⟶ (modulePullback B S hS (p i)).obj N)
    (hα : ModuleHomFamilyCompatible M N p α) :
    ∃! b : M ⟶ N, ∀ i, (modulePullback B S hS (p i)).map b = α i := by
  obtain ⟨w, hw⟩ : ∃ w : ∀ k, (modulePullback B S hS (v k)).obj M ⟶
      (modulePullback B S hS (v k)).obj N,
      ∀ k, w k = restrictForm B S hS (t k) (p (ik k)) (v k) (hvt k) (α (ik k)) :=
    ⟨_, fun _ ↦ rfl⟩
  have hwc := isPairwiseCompatible_restrictForm_of_moduleHomFamilyCompatible p v ik t hvt α hα
    w hw
  obtain ⟨b, hb⟩ := exists_modulePullback_map_eq_of_isFpqcCovering B S hS
    (reprFpqcHomSurjective B S hS) Xk v hv w hwc hM hN
  refine ⟨b, fun i ↦ ?_, fun b' hb' ↦ ?_⟩
  · refine modulePullback_map_injective_of_isFpqcCovering B S hS
      (reprFpqcHomInjective B S hS) _ (fun k ↦ fiberSnd (v k) (p i))
      (isFpqcCovering_pullback B S hS v (p i) hv) _ _ fun k ↦ ?_
    have hcond : fiberFst (v k) (p i) ≫ v k = fiberSnd (v k) (p i) ≫ p i :=
      (AlgebraicSpaces.isPullback_fiberProduct B S hS (v k) (p i)).w
    have hρ : (fiberFst (v k) (p i) ≫ t k) ≫ p (ik k) = fiberSnd (v k) (p i) ≫ p i := by
      rw [Category.assoc, hvt k, hcond]
    have hfk : fiberFst (v k) (p i) ≫ v k = (fiberFst (v k) (p i) ≫ t k) ≫ p (ik k) := by
      rw [Category.assoc, hvt k]
    refine factorForm_injective B S hS (fiberSnd (v k) (p i)) (p i) _ hρ.symm ?_
    rw [← restrictForm_eq, ← restrictForm_eq, restrictForm_map,
      ← restrictForm_map B S hS (fiberFst (v k) (p i)) (v k) _ hfk b, hb k, hw k,
      restrictForm_comp B S hS (fiberFst (v k) (p i)) (t k) (p (ik k)) (v k) (hvt k) _ rfl _
        hfk rfl]
    exact restrictForm_eq_of_moduleHomFamilyCompatible hα _ hρ.symm
  · refine modulePullback_map_injective_of_isFpqcCovering B S hS
      (reprFpqcHomInjective B S hS) Xk v hv b' b fun k ↦ ?_
    rw [hb k, hw k, ← restrictForm_map B S hS (t k) (p (ik k)) (v k) (hvt k) b', hb' (ik k)]

open QuasiCoherentDescent in
/-- **Descent of homomorphisms of quasi-coherent modules along an fppf covering sieve: Descent,
Proposition 023T** on the small étale sites of the schemes of the big fppf site.  For a scheme
`V` of the site, two quasi-coherent `𝒪_V`-modules `M` and `N`, and a family `r i : U i ⟶ V`
generating a covering sieve for the fppf topology, every compatible family of homomorphisms
`r_i^*M ⟶ r_i^*N` is the family of restrictions of exactly one homomorphism `M ⟶ N`.

This is `AlgebraicGeometry.Space.ModuleHomFppfDescent` for quasi-coherent modules, which is the
generality of the source.  The covering sieve contains a covering family of the site, an fppf
covering of the represented algebraic space by
`AlgebraicGeometry.Space.isFppfCovering_yonedaMap_of_isCovering`, each member of which factors
through some `r i`; `AlgebraicGeometry.Space.existsUnique_modulePullback_map_eq_of_refinement`
concludes. -/
theorem existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible
    (V : BigFppfOver B S hS)
    (M N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj V).1
      ((schemeSpaceFunctor B S hS).obj V).2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    {ι : Type*} (U : ι → BigFppfOver B S hS) (r : ∀ i, U i ⟶ V)
    (hr : Sieve.generate (Presieve.ofArrows U r) ∈ BigFppfOver.topology B S hS V)
    (α : ∀ i, (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (r i))).obj M ⟶
      (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (r i))).obj N)
    (hα : ModuleHomFamilyCompatible M N (fun i ↦ (schemeSpaceFunctor B S hS).map (r i)) α) :
    ∃! b : M ⟶ N, ∀ i,
      (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (r i))).map b = α i := by
  classical
  have hmem : Sieve.overEquiv V (Sieve.generate (Presieve.ofArrows U r)) ∈ B.topology V.left :=
    (GrothendieckTopology.mem_over_iff _ _).1 hr
  obtain ⟨E, hE, hEle⟩ := exists_covering_le_of_isSite B.IsCovering B.isSite B.precoverage
    (fun _ _ ↦ Iff.rfl) _ hmem
  have hfac : ∀ k : E.I₀, ∃ (i : ι) (t : (Over.mk (E.f k ≫ V.hom) : BigFppfOver B S hS) ⟶ U i),
      t ≫ r i = Over.homMk (E.f k) := by
    intro k
    have h := hEle _ _ (Presieve.ofArrows.mk k)
    rw [Sieve.overEquiv_iff] at h
    obtain ⟨Z, g, h', hh', hgh⟩ := h
    obtain ⟨i⟩ := hh'
    exact ⟨i, g, hgh⟩
  choose ik t ht using hfac
  have hv : IsFpqcCovering B S hS fun k ↦
      ((schemeSpaceFunctor B S hS).map
        (Over.homMk (E.f k) : (Over.mk (E.f k ≫ V.hom) : BigFppfOver B S hS) ⟶ V)).hom :=
    isFpqcCovering_of_isFppfCovering B S hS _ _
      (isFppfCovering_yonedaMap_of_isCovering B S hS V E hE)
  exact existsUnique_modulePullback_map_eq_of_refinement
    (fun i ↦ (schemeSpaceFunctor B S hS).map (r i))
    (fun k ↦ (schemeSpaceFunctor B S hS).map
      (Over.homMk (E.f k) : (Over.mk (E.f k ≫ V.hom) : BigFppfOver B S hS) ⟶ V)) hv ik
    (fun k ↦ (schemeSpaceFunctor B S hS).map (t k))
    (fun k ↦ by rw [← Functor.map_comp, ht k]) hM hN α hα

end AlgebraicGeometry.Space

end

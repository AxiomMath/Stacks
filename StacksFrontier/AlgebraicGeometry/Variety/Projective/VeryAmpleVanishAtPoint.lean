module

public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.SchemeModulesSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.SheafGradedRationalPoint
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.Basic

/-!
# A very ample section vanishing at a rational point and at no other given point

**This file is Stacks Tag 0B58.** Let `k` be an infinite field, `X` a scheme of finite type over
`k`, `L` a very ample invertible `𝒪_X`-module, `x` a `k`-rational point of `X` and
`x₁, …, xₙ` finitely many points of `X` distinct from `x`. Then there is a global section of `L`
vanishing at `x` and at none of the `xⱼ`.

The source reduces the lemma to `X = 𝐏ʳ_k` with `L = 𝒪(1)` by unfolding the definition of a very
ample invertible sheaf. That reduction is what is carried out here, in the form the definition of
very ampleness this repository has actually gives: Stacks Tag 01VM says that `L` is very ample
for `X ⟶ Spec k` when there are a quasi-coherent `𝒪_{Spec k}`-module `E` and an immersion
`i : X ⟶ 𝐏(E)` over `Spec k` with `L ≅ i^* 𝒪_{𝐏(E)}(1)`, and over the affine base `Spec k`
`Stacks.VeryAmpleAffineBase.exists_immersion_proj_of_isRelativelyVeryAmple` turns `𝐏(E)` into the
absolute homogeneous spectrum `Proj Γ(Spec k, Sym(E))`. So the ambient projective space of the
source's proof is an absolute `Proj` of a graded ring over `k`, not a projective space of a
finite-dimensional vector space, and the hyperplane argument has to be run over an arbitrary
graded ring; that is
`StacksFrontier/AlgebraicGeometry/Variety/Projective/GradedRationalPoint.lean`, with its hypotheses
discharged for this graded ring in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/SheafGradedRationalPoint.lean`.

Three facts about the graded ring of global sections of `Sym(E)` are what make the discharge
possible: it is generated in degree one over its degree-zero part
(`Stacks.Tag01VMRelativeVeryAmple.adjoin_symAlgebra_eq_top`); the structure map from `Γ(Spec k)`
is a bijection onto its degree-zero part, so the nonzero degree-zero elements are units
(`Stacks.SymGraded.bijective_smul_one`, the degree-zero piece of `Sym(E)` being the structure
sheaf); and every point of its `Proj` omits a degree-one element
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_mem_degreeOne_notMem`).

The degree-one element the hyperplane argument produces is then turned into a global section of
`L`: it gives the global section `v / 1` of `𝒪(1)` on `Proj`, whose nonvanishing locus is the
standard open `D₊(v)` by
`Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen`; Stacks Tag 0H78
(`Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff`) carries the nonvanishing locus
back along the immersion, and `Stacks.Ample.nonvanishingLocus_congr` carries it across
`L ≅ i^* 𝒪(1)`.

## Main results

* `AlgebraicGeometry.exists_globalSection_vanishing_at_rationalPoint`: **Stacks Tag 0B58.**

## Implementation notes

The rational point is `AlgebraicGeometry.IsRationalPoint`, the condition `κ(x) = k` of the
source, and `AlgebraicGeometry.ptOfIsRationalPoint` turns it into the section
`Spec k ⟶ X` of the structure morphism that the hyperplane theorem consumes. Composing with the
immersion gives a section of the structure morphism of `Proj Γ(Spec k, Sym(E))`, which by
`Stacks.SheafGradedRationalPoint.toSpecBase_gamma_eq` is the morphism to `Spec k` built out of
the degree-zero structure map; that equality is the only place the two descriptions of the base
morphism have to be matched.

That the images of the `xⱼ` stay distinct from the image of `x` is injectivity of the immersion
on points, `AlgebraicGeometry.Scheme.Hom.isEmbedding` of
`AlgebraicGeometry.IsPreimmersion`.

**Finite type is a hypothesis of the tag but is not used.** The source needs it nowhere in this
lemma either: what the proof uses is very ampleness, which is where the immersion into a
projective space comes from. It is kept so that the statement is the tag's.

The nonvanishing locus is computed in three spellings, which is why there are three transports in
the last step: `Stacks.SheafOfModules.nonvanishingOpen` on the ringed space underlying `Proj`,
which is what the twisting-sheaf calculus is stated for;
`Stacks.SheafOfModules.nonvanishingLocus` on the same ringed space; and
`Stacks.Ample.nonvanishingLocus` on a scheme, which is what Tag 0H78 and the transport along an
isomorphism of modules are stated for. `Stacks.SchemeModulesSpelling.nonvanishingLocus_eq`
crosses the last step.

## References

* [Stacks Project, Tag 0B58](https://stacks.math.columbia.edu/tag/0B58)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.Ample
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.Tag01VMRelativeVeryAmple

universe u w

namespace AlgebraicGeometry

/-- **Stacks Tag 0B58.** Let `k` be an infinite field, `X` a scheme of finite type over `k`, `L` a
very ample invertible `𝒪_X`-module, `x` a `k`-rational point of `X` and `xs` finitely many points
of `X` distinct from `x`. Then some global section of `L` vanishes at `x` and at none of the
`xs j`.

Very ampleness is Stacks Tag 01VM, `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, for the
structure morphism `X ⟶ Spec k`; a `k`-rational point is `AlgebraicGeometry.IsRationalPoint`,
the condition `κ(x) = k`; and "vanishes at" is the complement of
`Stacks.Ample.nonvanishingLocus`, the `X_s` of Stacks Tag 01CY. -/
@[stacks 0B58]
theorem exists_globalSection_vanishing_at_rationalPoint
    {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType fX] [QuasiCompact fX]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple fX L)
    {ι : Type w} [Finite ι] (x : X) (xs : ι → X)
    (hx : AlgebraicGeometry.IsRationalPoint fX x) (hne : ∀ j, x ≠ xs j) :
    ∃ s : Γ(L, ⊤), x ∉ nonvanishingLocus L s ∧ ∀ j, xs j ∈ nonvanishingLocus L s := by
  classical
  have hS : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  obtain ⟨E, hE, α, hα, hover, ⟨e⟩⟩ :=
    Stacks.VeryAmpleAffineBase.exists_immersion_proj_of_isRelativelyVeryAmple hS fX L hL
  have := hE
  have := hα
  -- the graded ring of global sections of `Sym(E)` and its two standing properties
  have hgen := adjoin_symAlgebra_eq_top E (⊤ : (Spec (CommRingCat.of k)).Opens) hS
  have hbij := Stacks.SymGraded.bijective_smul_one E
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)
    (⊤ : (Spec (CommRingCat.of k)).Opens)
  -- the rational point, read on `Proj` as a section of the structure morphism
  have hsec : (AlgebraicGeometry.ptOfIsRationalPoint fX x hx ≫ α) ≫
      Stacks.VeryAmpleAffineBase.projStructureHom (symAlgebra E) hS = 𝟙 _ := by
    rw [Category.assoc, hover]
    exact AlgebraicGeometry.ptOfIsRationalPoint_comp fX x hx
  have hpt : ∀ a, (AlgebraicGeometry.ptOfIsRationalPoint fX x hx ≫ α).base a = α.base x := by
    intro a
    change α.base ((AlgebraicGeometry.ptOfIsRationalPoint fX x hx).base a) = α.base x
    rw [AlgebraicGeometry.ptOfIsRationalPoint_apply]
  have hinj : Function.Injective α.base := α.isEmbedding.injective
  -- the degree-one equation of the rational point
  obtain ⟨v, hv, hvq, hvqs⟩ :=
    Stacks.SheafGradedRationalPoint.exists_mem_degreeOne_forall_notMem (symAlgebra E) hS hbij
      hgen (α.base x) (AlgebraicGeometry.ptOfIsRationalPoint fX x hx ≫ α) hsec hpt
      (fun j => α.base (xs j)) (fun j hc => hne j (hinj hc))
  -- its nonvanishing locus on `Proj` is the standard open it cuts out
  have hcov : ∀ y : ProjectiveSpectrum.top
      ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)),
      ∃ g, g ∈ (symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens) 1 ∧
        y ∈ ProjectiveSpectrum.basicOpen
          ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) g := by
    intro y
    obtain ⟨g, hg, hgy⟩ := AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_mem_degreeOne_notMem
      ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) hgen y.not_irrelevant_le
    exact ⟨g, hg, hgy⟩
  let hinv : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj
        ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens))).presheaf
      (structureSheafRing (AlgebraicGeometry.Proj
        ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens))).toRingedSpace).property
      (Stacks.ProjTwistSection.twistingModule
        ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) 1) :=
    Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf
      ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) hgen 1
  have hdict := Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen
    ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) v hv hcov
  have hiff : ∀ y : AlgebraicGeometry.Proj
      ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)),
      y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (AlgebraicGeometry.Proj
            ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens))).toRingedSpace)
          (Stacks.ProjTwistSection.twistingModule
            ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) 1)
          (Stacks.ProjTwistSection.homogeneousSection
            ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) v hv) ↔
        v ∉ y.asHomogeneousIdeal := by
    intro y
    change y ∈ Stacks.SheafOfModules.nonvanishingOpen (X := _) _ _ ↔ _
    rw [hdict]
    exact Iff.rfl
  -- carry the section back to `X`
  have hmem : ∀ y : X, y ∈ nonvanishingLocus L
        (e.symm.hom.app ⊤
          (Stacks.NonvanishingPullback.pullbackGlobalSection α
            (Stacks.ProjTwistSection.twistingModule
              ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) 1)
            ((Stacks.ProjTwistSection.homogeneousSection
              ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) v hv).eval
                (op ⊤)))) ↔
      v ∉ (α.base y).asHomogeneousIdeal := by
    intro y
    refine Iff.trans (Set.ext_iff.mp (Stacks.Ample.nonvanishingLocus_congr e.symm
      (Stacks.NonvanishingPullback.pullbackGlobalSection α
        (Stacks.ProjTwistSection.twistingModule
          ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) 1)
        ((Stacks.ProjTwistSection.homogeneousSection
          ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) v hv).eval (op ⊤)))) y)
      ?_
    refine Iff.trans (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff α
      (Stacks.ProjTwistSection.twistingModule
        ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) 1)
      ((Stacks.ProjTwistSection.homogeneousSection
        ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) v hv).eval (op ⊤)) y) ?_
    refine Iff.trans (Set.ext_iff.mp (Stacks.SchemeModulesSpelling.nonvanishingLocus_eq
      (AlgebraicGeometry.Proj ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)))
      (Stacks.ProjTwistSection.twistingModule
        ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) 1)
      (Stacks.ProjTwistSection.homogeneousSection
        ((symAlgebra E).grading (⊤ : (Spec (CommRingCat.of k)).Opens)) v hv))
      (α.base y)).symm ?_
    exact hiff (α.base y)
  exact ⟨_, fun hc => (hmem x).mp hc hvq, fun j => (hmem (xs j)).mpr (hvqs j)⟩

end AlgebraicGeometry

end

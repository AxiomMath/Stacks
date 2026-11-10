module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorOrdinaryLocal
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.ZariskiSquares
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.TwoChartCover

/-!
# The canonical map of Stacks 0F16 at `𝒪^{perf}` along the squares of Example 0EVH

Let `p` be a prime and `S` a scheme over `𝔽_p`. For two elements `f₁, f₂` of a ring `A`, the
almost blow up square of More on Flatness, Example 0EVH has base `X = Spec A`, centre
`Z = Spec (A/(f₁, f₂))`, modification `X' = Proj A[T₀,T₁]/(f₂T₀ - f₁T₁)` and exceptional corner
`E = 𝐏¹_Z`. This file shows that the canonical map of Stacks 0F16 at `𝒪^{perf}` along such a square
is a quasi-isomorphism.

## Main results

* `AlgebraicGeometry.BigHOver.quasiIso_cSquare_perfectionModule_of_twoGenerator`: the canonical map
  of Stacks 0F16 at `𝒪^{perf}` along a square of the shape of Example 0EVH is a
  quasi-isomorphism.

## References

* [Stacks Project, Tag 0EWT](https://stacks.math.columbia.edu/tag/0EWT)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 0EVJ](https://stacks.math.columbia.edu/tag/0EVJ)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.AlmostBlowUp

section Exceptional

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- The two variables of the exceptional projective line are homogeneous of degree one, and every
homogeneous element of positive degree lies in the ideal they generate. -/
theorem exceptional_two_charts :
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) (centerRing A f₁ f₂)) ∈ exceptionalGrading A f₁ f₂ 1 ∧
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) (centerRing A f₁ f₂)) ∈
        exceptionalGrading A f₁ f₂ 1 ∧
      ∀ n, 0 < n → ∀ a ∈ exceptionalGrading A f₁ f₂ n,
        a ∈ Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1} :=
  ⟨(MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X _ _),
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X _ _),
    fun n hn a ha ↦ AlgebraicGeometry.Proj.mem_span_pair_of_mem_map_homogeneousSubmodule
      (exceptionalGrading A f₁ f₂) (RingHom.id _) (fun _ a ha ↦ ⟨a, ha, rfl⟩) n hn a ha⟩

end Exceptional

section Modification

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- The two variables of the projective hypersurface `Proj A[T₀,T₁]/(f₂T₀ - f₁T₁)` are homogeneous
of degree one, and every homogeneous element of positive degree lies in the ideal they
generate. -/
theorem modification_two_charts :
    Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X 0) ∈ modificationGrading A f₁ f₂ 1 ∧
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X 1) ∈
        modificationGrading A f₁ f₂ 1 ∧
      ∀ n, 0 < n → ∀ a ∈ modificationGrading A f₁ f₂ n,
        a ∈ Ideal.span {Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X 0),
          Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X 1)} := by
  have hX (i : Fin 2) :
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ∈
        modificationGrading A f₁ f₂ 1 :=
    AddSubgroup.mem_map.mpr ⟨MvPolynomial.X i,
      (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X A i), rfl⟩
  exact ⟨hX 0, hX 1, AlgebraicGeometry.Proj.mem_span_pair_of_mem_map_homogeneousSubmodule
    (modificationGrading A f₁ f₂) (Ideal.Quotient.mk (relationIdeal A f₁ f₂))
    (fun _ a ha ↦ AddSubgroup.mem_map.mp ha)⟩

end Modification

end Stacks.AlmostBlowUp

namespace AlgebraicGeometry.BigHOver

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] MvPolynomial.gradedAlgebra

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

include hSp in
/-- Over a quasi-compact quasi-separated object every section of `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is the stage `n`
image of a global function, for some `n`. -/
theorem exists_awnStageFun_eq_of_qcqs (X : BigHOver B S hS)
    [CompactSpace ((BigHOver.toScheme B S hS).obj X)]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X)]
    (y : Γ(((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalization, ⊤)) :
    ∃ (n : ℕ) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)), awnStageFun B S hS p hSp n X a = y := by
  obtain ⟨x', hx'⟩ := (bijective_awnComparison_app B S hS p hSp X).2 y
  obtain ⟨n, a, rfl⟩ := exists_colimitStage_eq B S hS p X x'
  exact ⟨n, a, (awnComparison_colimitStage B S hS p hSp n X a).symm.trans hx'⟩

include hSp in
/-- **Restriction of `𝒪^{perf}` along a morphism to a quasi-compact quasi-separated object which
is surjective on functions is surjective.** -/
theorem surjective_awnSections_map_of_surjective_of_qcqs {V W : BigHOver B S hS} (f : W ⟶ V)
    [CompactSpace ((BigHOver.toScheme B S hS).obj W)]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj W)]
    (hf : Function.Surjective ((BigHOver.toScheme B S hS).map f).appTop) :
    Function.Surjective ((awnSections B S hS).map f.op) := by
  intro y
  obtain ⟨n, b, hb⟩ := exists_awnStageFun_eq_of_qcqs p hSp W y
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨awnStageFun B S hS p hSp n V a, ?_⟩
  have h := NatTrans.naturality_apply (perfectionStage B S hS p hSp n) f.op a
  exact ((congrArg ((awnSections B S hS).map f.op)
    (perfectionStage_app_apply B S hS p hSp n (op V) a).symm).trans h.symm).trans
      ((perfectionStage_app_apply B S hS p hSp n (op W) _).trans hb)

variable [HasSheafify (fppfTopology B S hS) AddCommGrpCat.{u + 1}]
  [(fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (SheafOfModules.{u + 1} (perfectionRing B S hS))]

include hSp in
/-- **The squares of Example 0EVH.** At a square of the shape of More on Flatness, Example 0EVH,
the canonical map of Stacks 0F16 at `𝒪^{perf}` is a quasi-isomorphism. -/
theorem quasiIso_cSquare_perfectionModule_of_twoGenerator (sq : GeneratorAlmostBlowUpSquare B S hS)
    (h : IsTwoGeneratorAlmostBlowUpModel ((BigHOver.toScheme B S hS).map sq.square.f₂₄)
      ((BigHOver.toScheme B S hS).map sq.square.f₃₄))
    (Rs : InjectiveResolution (perfectionModule B S hS)) :
    QuasiIso (Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquare sq.square
      Rs.cochainComplex) := by
  obtain ⟨A, hA, f₁, f₂, iX, iX', iZ, hb, hz⟩ := h
  let := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
  let K := BigHOver.toScheme B S hS
  obtain ⟨hm₀, hm₁, hmspan⟩ := Stacks.AlmostBlowUp.modification_two_charts A f₁ f₂
  have := quasiIso_sections_map_ι'_of_iso_proj p hSp sq.square.X₂
    (Stacks.AlmostBlowUp.modificationGrading A f₁ f₂) hm₀ hm₁ hmspan iX' Rs
  have hm := Stacks.AlmostBlowUp.twoGenerator_isPullback A f₁ f₂
  have hm' : IsPullback (Stacks.AlmostBlowUp.exceptionalToModification A f₁ f₂ ≫ iX'.inv)
      (Stacks.AlmostBlowUp.exceptionalToCenter A f₁ f₂ ≫ iZ.inv) (K.map sq.square.f₂₄)
      (K.map sq.square.f₃₄) := by
    refine hm.of_iso (Iso.refl _) iX'.symm iZ.symm iX.symm (by simp) (by simp) ?_ ?_
    · exact (CommSq.vert_inv ⟨hb⟩).w
    · exact (CommSq.vert_inv ⟨hz⟩).w
  let eE := sq.isPullback.isoIsPullback _ _ hm'
  have heE : eE.hom ≫ Stacks.AlmostBlowUp.exceptionalToCenter A f₁ f₂ ≫ iZ.inv =
      K.map sq.square.f₁₃ :=
    sq.isPullback.isoIsPullback_hom_snd _ _ hm'
  obtain ⟨he₀, he₁, hespan⟩ := Stacks.AlmostBlowUp.exceptional_two_charts A f₁ f₂
  have := quasiIso_sections_map_ι'_of_iso_proj p hSp sq.square.X₁
    (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂) he₀ he₁ hespan eE Rs
  have := quasiIso_sections_map_ι'_perfectionModule B S hS p hSp _ sq.isAffine_center Rs
  have := quasiIso_sections_map_ι'_perfectionModule B S hS p hSp _ sq.isAffine_base Rs
  have hΓ : Function.Surjective (K.map sq.square.f₁₃).appTop := by
    rw [← heE, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    exact (ConcreteCategory.bijective_of_isIso (eE.hom.app ⊤)).2.comp
      ((Stacks.AlmostBlowUp.bijective_appTop_exceptionalToCenter A f₁ f₂).2.comp
        (ConcreteCategory.bijective_of_isIso (iZ.inv.app ⊤)).2)
  have hcover := AlgebraicGeometry.Proj.basicOpen_sup_basicOpen_eq_top
    (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂) hespan
  have : CompactSpace (Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)) := by
    refine ⟨?_⟩
    have h₀ := (Proj.isAffineOpen_basicOpen (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)
      _ he₀ one_pos).isCompact
    have h₁ := (Proj.isAffineOpen_basicOpen (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)
      _ he₁ one_pos).isCompact
    have hu := congrArg (fun U : (Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)).Opens ↦
      (U : Set (Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂)))) hcover
    simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top] at hu
    exact hu ▸ h₀.union h₁
  have : QuasiSeparatedSpace (K.obj sq.square.X₁) := eE.hom.isOpenEmbedding.quasiSeparatedSpace
  have : CompactSpace (K.obj sq.square.X₁) :=
    (Scheme.homeoOfIso eE.symm).surjective.compactSpace (Scheme.homeoOfIso eE.symm).continuous
  have hsurj := surjective_awnSections_map_of_surjective_of_qcqs p hSp sq.square.f₁₃ hΓ
  exact quasiIso_cSquare_perfectionModule sq Rs (fun d ↦ by
    obtain ⟨b, hb⟩ := hsurj d
    exact ⟨b, 0, by rwa [map_zero, add_zero]⟩)

end AlgebraicGeometry.BigHOver

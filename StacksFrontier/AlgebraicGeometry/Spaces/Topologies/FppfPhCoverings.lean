module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfAffineDomination

/-!
# Fppf coverings of algebraic spaces are ph coverings

Let `S` be a scheme contained in a big fppf site `B`. An fppf covering of an algebraic space
over `S` (Stacks 03ZC) is a ph covering of it (Stacks 0DFG), and so is a syntomic, smooth or
Zariski covering, those being fppf coverings by Stacks 0DFC.

## Main results

* `AlgebraicGeometry.Space.isPHCovering_of_isFppfCovering`: an fppf covering of an algebraic
  space is a ph covering.
* `AlgebraicGeometry.Space.isPHCovering_of_isSyntomicCovering`,
  `AlgebraicGeometry.Space.isPHCovering_of_isSmoothCovering` and
  `AlgebraicGeometry.Space.isPHCovering_of_isZariskiCovering`: a syntomic, smooth or Zariski
  covering of an algebraic space is a ph covering.

## References

* [Stacks Project, Tag 0DFH](https://stacks.math.columbia.edu/tag/0DFH)
* [Stacks Project, Tag 0DFC](https://stacks.math.columbia.edu/tag/0DFC)
* [Stacks Project, Tag 0DBT](https://stacks.math.columbia.edu/tag/0DBT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An fppf covering of an algebraic space over `S` is a ph covering of it. -/
@[stacks 0DFH "fppf coverings"]
theorem isPHCovering_of_isFppfCovering {I : Type v}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (hf : IsFppfCovering B S hS X f) :
    IsPHCovering B S hS X f := by
  classical
  refine ⟨hf.target_isAlgebraicSpace, hf.source_isAlgebraicSpace,
    fun i ↦ isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (hf.locallyOfFinitePresentation i), ?_⟩
  intro U hU a
  set toSch := BigFppfOver.toScheme B S hS
  have : IsAffine (toSch.obj U) := hU
  set Atgt : AlgebraicSpaces B S hS := ⟨F, hf.target_isAlgebraicSpace⟩ with hAtgt
  set Apt : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ with hApt
  set Asrc : I → AlgebraicSpaces B S hS :=
    fun i ↦ ⟨X i, hf.source_isAlgebraicSpace i⟩ with hAsrc
  set aA : Apt ⟶ Atgt := ObjectProperty.homMk a with haA
  set fA : ∀ i, Asrc i ⟶ Atgt := fun i ↦ ObjectProperty.homMk (f i) with hfA
  have hbc : IsFppfCovering B S hS (fun i ↦ pullback a (f i))
      (fun i ↦ pullback.fst a (f i)) :=
    isFppfCovering_fibreProduct B S hS Asrc fA aA hf
  obtain ⟨V, β, hcov⟩ := exists_fppfCovering_scheme_refinement B S hS _ _ hbc
  set v : ∀ i, V i ⟶ U := fun i ↦ yoneda.preimage (β i ≫ pullback.fst a (f i)) with hv
  have hvmap (i : I) : yoneda.map (v i) = β i ≫ pullback.fst a (f i) := by simp [hv]
  have hcov' : IsFppfCovering B S hS (fun i ↦ yoneda.obj (V i))
      (fun i ↦ yoneda.map (v i)) := by
    simpa only [hvmap] using hcov
  have hmem := yoneda_fppfCovering_mem_fppfPrecoverage B S hS V U v hcov'
  have hph : _root_.AlgebraicGeometry.IsPHCovering
      (fun i ↦ toSch.obj (V i)) (fun i ↦ toSch.map (v i)) :=
    _root_.AlgebraicGeometry.IsPHCovering.of_mem_fppfPrecoverage _ _ hmem
  obtain ⟨A, hA, ⟨H⟩⟩ := exists_standardPHCovering_homOver_of_isAffine hph
  have hsmall (j : A.I₀) : B.Contains (A.X j) := by
    let := hA.isAffine j
    let := hA.locallyOfFiniteType j
    exact (Scheme.size_le_of_locallyOfFiniteType (A.f j)).trans_lt U.left.property
  let Q : PreZeroHypercover.{u} U :=
    { I₀ := A.I₀
      X := fun j ↦ Over.mk ((ObjectProperty.homMk (A.f j) : B.obj (hsmall j) ⟶ U.left) ≫ U.hom)
      f := fun j ↦ Over.homMk (ObjectProperty.homMk (A.f j)) }
  refine ⟨Q, hA, ⟨?_⟩⟩
  have hw (j : A.I₀) : H.h₀ j ≫ toSch.map (v (H.s₀ j)) = A.f j := by simpa using H.w₀ j
  have hb (j : A.I₀) : ∃ b : Q.X j ⟶ V (H.s₀ j), toSch.map b = H.h₀ j := by
    refine ⟨Over.homMk (ObjectProperty.homMk (H.h₀ j)) ?_, rfl⟩
    apply ObjectProperty.hom_ext
    show H.h₀ j ≫ (V (H.s₀ j)).hom.hom = A.f j ≫ U.hom.hom
    have hfac : toSch.map (v (H.s₀ j)) ≫ U.hom.hom = (V (H.s₀ j)).hom.hom :=
      congrArg (fun q ↦ q.hom) (v (H.s₀ j)).w
    rw [← hfac, ← Category.assoc, hw j]
  choose b hbmap using hb
  refine ⟨H.s₀, fun j ↦ yoneda.map (b j) ≫ β (H.s₀ j) ≫ pullback.snd a (f (H.s₀ j)),
    fun j ↦ ?_⟩
  have hQv (j : A.I₀) : b j ≫ v (H.s₀ j) = Q.f j := by
    apply Functor.map_injective toSch
    rw [Functor.map_comp, hbmap]
    exact hw j
  show (yoneda.map (b j) ≫ β (H.s₀ j) ≫ pullback.snd a (f (H.s₀ j))) ≫ f (H.s₀ j) =
    yoneda.map (Q.f j) ≫ a
  rw [← hQv j, Functor.map_comp, hvmap]
  simp [pullback.condition]

/-- A syntomic covering of an algebraic space over `S` is a ph covering of it. -/
@[stacks 0DFH "syntomic coverings"]
theorem isPHCovering_of_isSyntomicCovering {I : Type v}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (hf : IsSyntomicCovering B S hS X f) :
    IsPHCovering B S hS X f :=
  isPHCovering_of_isFppfCovering B S hS (isFppfCovering_of_isSyntomicCovering B S hS hf)

/-- A smooth covering of an algebraic space over `S` is a ph covering of it. -/
@[stacks 0DFH "smooth coverings"]
theorem isPHCovering_of_isSmoothCovering {I : Type v}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (hf : IsSmoothCovering B S hS X f) :
    IsPHCovering B S hS X f :=
  isPHCovering_of_isFppfCovering B S hS (isFppfCovering_of_isSmoothCovering B S hS hf)

/-- A Zariski covering of an algebraic space over `S` by algebraic spaces is a ph covering of
it. -/
@[stacks 0DFH "Zariski coverings"]
theorem isPHCovering_of_isZariskiCovering {I : Type v}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (hF : IsAlgebraicSpace B S hS F)
    (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
    (hf : IsZariskiCovering B S hS I X f) :
    IsPHCovering B S hS X f :=
  isPHCovering_of_isFppfCovering B S hS
    (isFppfCovering_of_isZariskiCovering B S hS hF hX hf)

end AlgebraicGeometry.Space

end

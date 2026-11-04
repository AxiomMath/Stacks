module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackCompatibility
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DisjointUnion

/-!
# Fully faithful pullback under an fpqc refinement of families

For two families of schemes over the same base, a morphism of families whose fibres over every
member of the target family form an fpqc covering induces a fully faithful functor on descent
data.

## Main results

* `AlgebraicGeometry.pullbackFunctor_fullyFaithful_of_fpqcRefinement` states full faithfulness
  of the pullback functor under a fibrewise fpqc hypothesis.

## References

* [Stacks Project, Tag 02VZ](https://stacks.math.columbia.edu/tag/02VZ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

private lemma coproductHom_mem_fpqc
    {S : Scheme.{u}} (U V : PreZeroHypercover.{u} S)
    (α : U.HomOver V (𝟙 S))
    (hfpqc : ∀ j : V.I₀,
      Presieve.ofArrows
        (fun i : {i : U.I₀ // α.s₀ i = j} ↦ U.X i)
        (fun i ↦ α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)) ∈
          Scheme.fpqcPrecoverage (V.X j)) :
    Presieve.singleton
      (MorphismOfSchemeFamilies.coproductHom
        { sourceBase := S, targetBase := S,
          sourceFamily := U, targetFamily := V,
          baseHom := 𝟙 S, familyHom := α }) ∈
      Scheme.fpqcPrecoverage (∐ V.X) := by
  let Y := ∐ V.X
  have hinc : Presieve.ofArrows V.X (fun j ↦ Sigma.ι V.X j) ∈
      Scheme.fpqcPrecoverage Y := by
    apply (ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem
      (T := Y) V.X (fun j ↦ Sigma.ι V.X j)).2
    exact Precoverage.mem_coverings_of_isIso (J := Scheme.fpqcPrecoverage)
      (Sigma.desc (fun j ↦ Sigma.ι V.X j))
  have hcomp :
      Presieve.ofArrows
        (fun p : Σ j, {i : U.I₀ // α.s₀ i = j} ↦ U.X p.2.val)
        (fun p ↦
          (α.h₀ p.2.val ≫ eqToHom (congrArg V.X p.2.property)) ≫
            Sigma.ι V.X p.1) ∈ Scheme.fpqcPrecoverage Y :=
    Precoverage.comp_mem_coverings
      (fun j ↦ Sigma.ι V.X j) hinc
      (fun j (i : {i : U.I₀ // α.s₀ i = j}) ↦
        α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)) hfpqc
  let e : (Σ j, {i : U.I₀ // α.s₀ i = j}) → U.I₀ := fun p ↦ p.2.val
  have he : Function.Surjective e := fun i ↦ ⟨⟨α.s₀ i, ⟨i, rfl⟩⟩, rfl⟩
  have hreindex :
      Presieve.ofArrows (fun p : (Σ j, {i : U.I₀ // α.s₀ i = j}) ↦ U.X (e p))
        (fun p ↦ α.h₀ (e p) ≫ Sigma.ι V.X (α.s₀ (e p))) =
      Presieve.ofArrows U.X (fun i ↦ α.h₀ i ≫ Sigma.ι V.X (α.s₀ i)) :=
    Presieve.ofArrows_comp_eq_of_surjective
      (fun i ↦ α.h₀ i ≫ Sigma.ι V.X (α.s₀ i)) he
  have hfamily :
      Presieve.ofArrows U.X (fun i ↦ α.h₀ i ≫ Sigma.ι V.X (α.s₀ i)) ∈
        Scheme.fpqcPrecoverage Y := by
    rw [← hreindex]
    convert hcomp using 2
    funext p
    obtain ⟨_, i, rfl⟩ := p
    simp [e]
  have hsingle :=
    (ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem
      (T := Y) U.X (fun i ↦ α.h₀ i ≫ Sigma.ι V.X (α.s₀ i))).1 hfamily
  simpa [MorphismOfSchemeFamilies.coproductHom, Y] using hsingle

/-- An fpqc refinement of each member of a family induces a fully faithful
pullback functor on descent data. -/
@[stacks 02VZ]
public theorem pullbackFunctor_fullyFaithful_of_fpqcRefinement
    {S : Scheme.{u}} (U V : PreZeroHypercover.{u} S)
    (α : U.HomOver V (𝟙 S))
    (hfpqc : ∀ j : V.I₀,
      Presieve.ofArrows
        (fun i : {i : U.I₀ // α.s₀ i = j} ↦ U.X i)
        (fun i ↦ α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)) ∈
          Scheme.fpqcPrecoverage (V.X j)) :
    Nonempty ((MorphismOfSchemeFamilies.pullbackFunctor
      { sourceBase := S, targetBase := S,
        sourceFamily := U, targetFamily := V,
        baseHom := 𝟙 S, familyHom := α }).functor.FullyFaithful) := by
  let F : MorphismOfSchemeFamilies.{u} :=
    { sourceBase := S, targetBase := S,
      sourceFamily := U, targetFamily := V,
      baseHom := 𝟙 S, familyHom := α }
  let a := Sigma.desc V.f
  let a' := Sigma.desc U.f
  have hcover : Presieve.singleton F.coproductHom ∈ Scheme.fpqcPrecoverage F.targetCoproduct :=
    coproductHom_mem_fpqc U V α hfpqc
  let P := DescentData.pullbackFunctor a a' (𝟙 S) F.coproductHom F.coproductHom_comp
  obtain ⟨hP⟩ := pullbackFunctor_fullyFaithful_of_fpqc P hcover
  let E₁ := DescentData.familyCoproductEquivalence V.f
  let E₂ := DescentData.familyCoproductEquivalence U.f
  have hcomp : (E₁.equivalence.functor ⋙ P.functor).FullyFaithful :=
    E₁.equivalence.fullyFaithfulFunctor.comp hP
  have hcompat := (MorphismOfSchemeFamilies.pullbackCompatibility F).iso
  have hright :
      ((MorphismOfSchemeFamilies.pullbackFunctor F).functor ⋙
        E₂.equivalence.functor).FullyFaithful :=
    Functor.FullyFaithful.ofIso hcomp hcompat
  have : (E₂.equivalence.functor).Faithful := E₂.equivalence.fullyFaithfulFunctor.faithful
  exact ⟨Functor.FullyFaithful.ofCompFaithful hright⟩

end AlgebraicGeometry

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementChow
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver

/-!
# The ph coverings of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A family of morphisms of algebraic
spaces over `S` with common target `X` is a *ph covering* when every member is locally of
finite type and, for every affine scheme-valued point `a : U ⟶ X`, some standard ph covering
of `U` refines the family pulled back along `a`. This is the ph analogue of the five covering
notions of Stacks 03YH, and the condition after base change to an affine is the one of
Stacks 0DBD for schemes.

## Main definitions

* `AlgebraicGeometry.Space.IsPHCovering`: **Stacks 0DFG**.

## Main results

* `AlgebraicGeometry.Space.isPHCovering_of_isIso`: **Stacks 0DFJ**, the isomorphism clause.
* `AlgebraicGeometry.Space.isPHCovering_baseChange`: **Stacks 0DFJ**, the base-change clause.
* `AlgebraicGeometry.Space.isPHCovering_bind_of_chowLemma`: the composition clause, on the
  hypothesis of Chow's lemma. The unconditional form, which carries the tag, is
  `AlgebraicGeometry.Space.isPHCovering_comp` in
  `StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringComposition`.

## Implementation notes

The refining standard ph covering is a `CategoryTheory.PreZeroHypercover` of the site object
`U`, and the refinement datum is a `CategoryTheory.PreZeroHypercover.HomOver` over the point
`a`, which is what makes the composition and base-change arguments for ph coverings the same
manipulations of refinements as for schemes. Its index type is pinned to the universe `u` of
the schemes, matching `AlgebraicGeometry.StandardPHCovering`, while the index type of the
covering family itself lives in its own universe `v`.

Being locally of finite type is the every-étale-chart condition of Stacks 03MJ, so the
property clause of the base-change statement is **Stacks 03XH** and, for an isomorphism, the
invariance of the chart condition under precomposition with an isomorphism together with the
fact that an étale morphism of schemes is locally of finite type.

The composition clause is proved here in the form that carries Chow's lemma (**Stacks 0202**)
as a hypothesis, and in that form is not tagged. It reduces to part (2) of **Stacks 0DBF** —
that standard ph coverings of an affine scheme are closed under refinement by standard ph
coverings of their members — through
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_chowLemma`, whose hypothesis is
the same one. That hypothesis is redundant, Chow's lemma being a theorem of this development,
and it is discharged in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringComposition`, where
`AlgebraicGeometry.Space.isPHCovering_comp` states the clause unconditionally and carries the
tag; the split into two files is only so that this one does not have to import the proof of
Chow's lemma.

The members of the standard ph refinement produced for an affine test scheme are schemes, not
objects of the site, so they have to be put back into the site: each is an affine open of the
source of a proper morphism onto the test scheme, so it is below the site's cutoff by
`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion` and
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`, and the refinement
morphisms are the preimages of the scheme morphisms under the fully faithful inclusion of the
site.

## References

* [Stacks Project, Tag 0DFG](https://stacks.math.columbia.edu/tag/0DFG)
* [Stacks Project, Tag 0DFJ](https://stacks.math.columbia.edu/tag/0DFJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DFG.** A family of morphisms of algebraic spaces over `S` with common target is
a *ph covering* when every member is locally of finite type and every affine scheme-valued
point of the target admits a standard ph covering refining the pullback of the family. -/
@[stacks 0DFG]
structure IsPHCovering {I : Type v} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Xᵢ i ⟶ X) : Prop where
  /-- The target is an algebraic space. -/
  target_isAlgebraicSpace : IsAlgebraicSpace B S hS X
  /-- Every source is an algebraic space. -/
  source_isAlgebraicSpace : ∀ i, IsAlgebraicSpace B S hS (Xᵢ i)
  /-- Every member is locally of finite type. -/
  locallyOfFiniteType : ∀ i, IsLocallyOfFiniteType B S hS (f i)
  /-- Every affine test scheme has a standard ph covering refining the original family after
  base change. -/
  affine_refinement : ∀ (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (a : yoneda.obj U ⟶ X),
    ∃ E : PreZeroHypercover.{u} U,
      StandardPHCovering (E.map (BigFppfOver.toScheme B S hS)).f ∧
      Nonempty ((E.map yoneda).HomOver
        ({ I₀ := I, X := Xᵢ, f := f } : PreZeroHypercover.{v} X) a)

/-- **Stacks 0DFJ**, the isomorphism clause. An isomorphism of algebraic spaces over `S`,
regarded as a family indexed by a point, is a ph covering: the identity of an affine test
scheme is a standard ph covering of it, and it refines the pulled-back family through the
inverse isomorphism. -/
@[stacks 0DFJ "ph_covering_of_isomorphism"]
theorem isPHCovering_of_isIso
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) [IsIso f]
    (hX : IsAlgebraicSpace B S hS X) :
    IsPHCovering B S hS (fun _ : Unit ↦ X') (fun _ ↦ f) := by
  have hX' : IsAlgebraicSpace B S hS X' :=
    isAlgebraicSpace_of_relativelyRepresentable B S hS f
      (Functor.relativelyRepresentable.of_isIso yoneda _) hX
  have hLoc : IsLocallyOfFiniteType B S hS f := by
    simpa using (holdsOnEveryEtaleChart_iso_comp_iff B S hS
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f (𝟙 X)).mpr
      (holdsOnEveryEtaleChart_id_presheaf B S hS
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (by intro _ _ g hg; have : AlgebraicGeometry.Etale g := hg; infer_instance) X)
  refine ⟨hX, fun _ ↦ hX', fun _ ↦ hLoc, ?_⟩
  intro U hU a
  refine ⟨PreZeroHypercover.singleton (𝟙 U), ?_, ?_⟩
  · exact StandardPHCovering.of_presentation
      (f := fun _ : PUnit ↦ 𝟙 ((BigFppfOver.toScheme B S hS).obj U))
      (hX := fun _ ↦ hU) (g := 𝟙 _) (j := fun _ ↦ 𝟙 _) inferInstance inferInstance
      (fun _ ↦ inferInstance) (by simp only [Set.iUnion_const]; exact Set.range_id) (by simp)
  · refine ⟨{ s₀ := fun _ ↦ (), h₀ := fun _ ↦ a ≫ inv f, w₀ := ?_ }⟩
    intro i
    change (a ≫ inv f) ≫ f = yoneda.map (𝟙 U) ≫ a
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    simp

/-- **Stacks 0DFJ**, the base-change clause. The first projections of the fibre products of a
ph covering of an algebraic space over `S` with a morphism `g` into its target form a ph
covering of the source of `g`: a standard ph refinement of the original family over an affine
point `a` of the new base refines the pulled-back family through the universal property of the
fibre product. -/
@[stacks 0DFJ "ph_covering_base_change"]
theorem isPHCovering_baseChange
    {I : Type v} {X X' : AlgebraicSpaces B S hS} (Xᵢ : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xᵢ i ⟶ X) (g : X' ⟶ X)
    (hf : IsPHCovering B S hS (fun i ↦ (Xᵢ i).1) (fun i ↦ (f i).hom)) :
    IsPHCovering B S hS (fun i ↦ (AlgebraicSpaces.fiberProduct B S hS g (f i)).1)
      (fun i ↦ pullback.fst g.hom (f i).hom) := by
  refine ⟨X'.property, fun i ↦ (AlgebraicSpaces.fiberProduct B S hS g (f i)).property,
    fun i ↦ (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g (f i)).flip
      (hf.locallyOfFiniteType i), ?_⟩
  intro U hU a
  obtain ⟨E, hE, ⟨φ⟩⟩ := hf.affine_refinement U (a ≫ g.hom)
  exact ⟨E, hE, ⟨⟨φ.s₀, fun j ↦ pullback.lift ((E.map yoneda).f j ≫ a) (φ.h₀ j)
    (by simpa only [Category.assoc] using (φ.w₀ j).symm),
    fun j ↦ pullback.lift_fst _ _ _⟩⟩⟩


/-- The composition clause of **Stacks 0DFJ**, on the hypothesis of Chow's lemma
(**Stacks 0202**): the composites of a ph covering of an algebraic space over `S` with ph
coverings of its members form a ph covering.

The hypothesis is carried rather than discharged because part (2) of **Stacks 0DBF**, which
this reduces to, is available here only in the conditional form
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_chowLemma`. -/
theorem isPHCovering_bind_of_chowLemma
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (E : PreZeroHypercover.{v} X)
    (hE : IsPHCovering B S hS E.X E.f)
    (F : ∀ i, PreZeroHypercover.{w} (E.X i))
    (hF : ∀ i, IsPHCovering B S hS (F i).X (F i).f)
    (hchow : ∀ (A C : Scheme.{u}) (p : A ⟶ C), IsAffine C → IsProper p →
      HasChowModification p) :
    IsPHCovering B S hS (E.bind F).X (E.bind F).f := by
  classical
  refine ⟨hE.target_isAlgebraicSpace,
    fun ij => (hF ij.1).source_isAlgebraicSpace ij.2, fun ij => ?_, ?_⟩
  · exact isLocallyOfFiniteType_comp B S hS ((hF ij.1).source_isAlgebraicSpace ij.2)
      ((hF ij.1).target_isAlgebraicSpace) hE.target_isAlgebraicSpace
      ((F ij.1).f ij.2) (E.f ij.1)
      ((hF ij.1).locallyOfFiniteType ij.2) (hE.locallyOfFiniteType ij.1)
  · intro U hU a
    let Tf := BigFppfOver.toScheme B S hS
    obtain ⟨A, hA, ⟨φ⟩⟩ := hE.affine_refinement U a
    choose C hC ψ' using fun q : A.I₀ => by
      letI : IsAffine (Tf.obj (A.X q)) := hA.isAffine q
      exact (hF (φ.s₀ q)).affine_refinement (A.X q) (φ.h₀ q)
    let ψ : ∀ q, ((C q).map yoneda).HomOver (F (φ.s₀ q)) (φ.h₀ q) := fun q => (ψ' q).some
    obtain ⟨G, hG, hδ⟩ := exists_standardPHCovering_refinement_bind_of_chowLemma
      (A.map Tf) hA (fun q => (C q).map Tf) hC hchow
    let K : PreZeroHypercover.{u} U := A.bind C
    obtain ⟨δ⟩ := hδ
    have hδ' : G.Hom (K.map Tf) := ⟨δ.s₀, δ.h₀, by
      intro γ
      simpa [K, PreZeroHypercover.bind, PreZeroHypercover.map, Functor.map_comp] using δ.w₀ γ⟩
    obtain ⟨V, p, j, hp, -, hj, -, -⟩ := hG.exists_presentation
    have hGSize : ∀ γ : G.I₀, (G.X γ).size < B.cutoff := by
      intro γ
      let _ : _root_.AlgebraicGeometry.IsOpenImmersion (j γ) := hj γ
      let _ : _root_.AlgebraicGeometry.IsProper p := hp
      exact Scheme.size_lt_of_isOpenImmersion (j γ)
        (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p U.left.property)
    let gBase : ∀ γ : G.I₀,
        B.inclusion.obj (B.obj (hGSize γ)) ⟶ B.inclusion.obj U.left := fun γ => G.f γ
    let gStruct : ∀ γ : G.I₀,
        B.inclusion.obj (B.obj (hGSize γ)) ⟶ B.inclusion.obj (B.obj hS) := fun γ =>
      G.f γ ≫ B.inclusion.map U.hom
    let Gbar : PreZeroHypercover.{u} U :=
      { I₀ := G.I₀
        X := fun γ => Over.mk (B.inclusion.preimage (gStruct γ))
        f := fun γ => Over.homMk (B.inclusion.preimage (gBase γ)) (by
          apply B.inclusion.map_injective
          rw [Functor.map_comp, B.inclusion.map_preimage]
          change gBase γ ≫ B.inclusion.map U.hom =
            B.inclusion.map (B.inclusion.preimage (gStruct γ))
          rw [B.inclusion.map_preimage]) }
    have hGbar_map : Gbar.map Tf = G := by
      ext
      · rfl
      · exact HEq.rfl
      · exact heq_of_eq (funext fun γ => B.inclusion.map_preimage (gBase γ))
    let lift : ∀ γ : Gbar.I₀, (Gbar.X γ).left ⟶ (K.X (hδ'.s₀ γ)).left := fun γ =>
      B.inclusion.preimage
        (show B.inclusion.obj (Gbar.X γ).left ⟶
          B.inclusion.obj (K.X (hδ'.s₀ γ)).left from hδ'.h₀ γ)
    have hKstruct : ∀ γ : Gbar.I₀, B.inclusion.map (K.X (hδ'.s₀ γ)).hom =
        Tf.map (K.f (hδ'.s₀ γ)) ≫ B.inclusion.map U.hom := by
      intro γ
      change B.inclusion.map (K.X (hδ'.s₀ γ)).hom =
        B.inclusion.map (K.f (hδ'.s₀ γ)).left ≫ B.inclusion.map U.hom
      rw [← Functor.map_comp]
      exact (congrArg B.inclusion.map (Over.w (K.f (hδ'.s₀ γ)))).symm
    have δsite : Gbar.Hom K := by
      refine ⟨hδ'.s₀, fun γ => Over.homMk (lift γ) ?_, fun γ => ?_⟩
      · apply B.inclusion.map_injective
        rw [Functor.map_comp, B.inclusion.map_preimage, hKstruct γ,
          show B.inclusion.map (Gbar.X γ).hom = gStruct γ from
            B.inclusion.map_preimage (gStruct γ),
          ← Category.assoc]
        exact congrArg (fun q => q ≫ B.inclusion.map U.hom) (hδ'.w₀ γ)
      · apply Over.OverMorphism.ext
        apply B.inclusion.map_injective
        change B.inclusion.map (lift γ ≫ (K.f (hδ'.s₀ γ)).left) =
          B.inclusion.map (B.inclusion.preimage (gBase γ))
        rw [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
        exact hδ'.w₀ γ
    let ρ : (K.map yoneda).HomOver (E.bind F) a := by
      refine ⟨fun ab => ⟨φ.s₀ ab.1, (ψ ab.1).s₀ ab.2⟩, fun ab => (ψ ab.1).h₀ ab.2, ?_⟩
      intro ab
      change ((ψ ab.1).h₀ ab.2 ≫ (F (φ.s₀ ab.1)).f ((ψ ab.1).s₀ ab.2)) ≫ E.f (φ.s₀ ab.1) =
        (yoneda.map ((C ab.1).f ab.2 ≫ A.f ab.1)) ≫ a
      dsimp [PreZeroHypercover.map] at φ ψ ⊢
      rw [(ψ ab.1).w₀ ab.2, Category.assoc, φ.w₀ ab.1, ← Category.assoc, ← Functor.map_comp]
    have δover : (Gbar.map yoneda).HomOver (K.map yoneda) (𝟙 (yoneda.obj U)) := by
      refine ⟨δsite.s₀, fun γ => yoneda.map (δsite.h₀ γ), ?_⟩
      intro γ
      simpa [PreZeroHypercover.map, ← Functor.map_comp] using
        congrArg yoneda.map (δsite.w₀ γ)
    exact ⟨Gbar, by rw [hGbar_map]; exact hG, ⟨δover.comp ρ (Category.id_comp a)⟩⟩

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBranchCodimension
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NoetherianQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# The dimension function of a universally catenary space, read on a chart

Let `X` be a decent, universally catenary algebraic space carrying a dimension function `δ`,
and let `φ : U ⟶ X` be a surjective étale chart by a locally Noetherian scheme. This file
proves that `δ ∘ φ` is a dimension function on `U`.

That `δ ∘ φ` strictly decreases along specializations is the separation of points of
Stacks 03K5. That it drops by exactly one along an immediate specialization `x ⤳ y` of `U` is
the content: if the drop were two or more, a point strictly between `φ x` and `φ y` in `|X|`
lifts to `U` and gives a strict chain `x' ⤳ x₁ ⤳ y` from a point `x'` with the image of `x`.
Inside the reduced closed subspace of `X` on the closure of `φ x`, the point `x` is generic in
its chart, and the closure of `x` meets the other branches of the chart in a closed set not
containing `x` or `x'`. Restricting the kernel pair of the chart to the trivial relation over
that closed set leaves an étale equivalence relation which glues `x` to `x'`, and
`AlgebraicGeometry.Space.ChartBranch.false_of_branches` refutes the configuration.

## Main results

* `AlgebraicGeometry.Space.exists_dimensionFunction_comp_chart`: `δ ∘ φ` is a dimension function
  on `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- **A maximal point is not in the closure of the complement of its closure**, in a quasi-sober
Noetherian space: every irreducible component through a point outside the closure of a maximal
point `x` misses `x`, and there are finitely many components. -/
theorem notMem_closure_compl_closure_singleton {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {x : X} (hx : ∀ z, z ⤳ x → z = x) :
    x ∉ closure (closure {x})ᶜ := by
  classical
  set D : Set X := ⋃₀ {Z | Z ∈ irreducibleComponents X ∧ x ∉ Z} with hD
  have hfin : {Z | Z ∈ irreducibleComponents X ∧ x ∉ Z}.Finite :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).subset fun _ h ↦ h.1
  have hDcl : IsClosed D :=
    hfin.isClosed_sUnion fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1
  have hsub : (closure {x})ᶜ ⊆ D := by
    intro w hw
    refine ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, ?_⟩,
      mem_irreducibleComponent⟩
    intro hxZ
    obtain ⟨g, hg⟩ := QuasiSober.sober (irreducibleComponent_mem_irreducibleComponents w).1
      (isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents w))
    have hgx : g ⤳ x := by
      rw [specializes_iff_mem_closure, hg.def]
      exact hxZ
    have hgw : w ∈ closure {x} := by
      rw [← hx g hgx, hg.def]
      exact mem_irreducibleComponent
    exact hw hgw
  intro hx'
  obtain ⟨Z, ⟨-, hxZ⟩, hZ⟩ := (closure_minimal hsub hDcl) hx'
  exact hxZ hZ

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

section ReducedChart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- **The reduced closed subspace on a closed set has a chart which is a closed subscheme of the
given chart**: the presentation of the reduced induced closed subscheme of `U` over the closed
set, which maps to the subspace by a surjective étale morphism. -/
theorem exists_reducedChart_isClosedImmersion (T : Set (points B S hS X)) (hT : IsClosed T) :
    ∃ (V : BigFppfOver B S hS) (i : V ⟶ U)
      (k : yoneda.obj V ⟶ (reducedClosedSubspaceOfChart B S hS φ T hT).toFunctor),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) k ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) k ∧
        _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map i) = atlasPointSet B S hS φ T ∧
        k ≫ (reducedClosedSubspaceOfChart B S hS φ T hT).ι = yoneda.map i ≫ φ := by
  have him := isImmersion_arrow_atlasReducedSubscheme B S hS φ T hT
  have hci := isClosedImmersion_arrow_atlasReducedSubscheme B S hS φ T hT
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS _ him
  obtain ⟨k, hk⟩ := exists_isPullback_yoneda_presentation B S hS hs _
    (isInvariantSubscheme_atlasReducedSubscheme B S hS hs he T hT) i e hei
  have hstabs := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have hstabe := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  refine ⟨V, i, k, MorphismProperty.of_isPullback hk.flip hs,
    MorphismProperty.of_isPullback hk.flip he, ?_, ?_, hk.w⟩
  · rw [← hei]
    infer_instance
  have hiso : ∀ {A A' Y : Scheme.{u}} (ε : A ≅ A') (g : A' ⟶ Y),
      Set.range (ε.hom ≫ g).base = Set.range g.base := fun ε g => by
    simp [Set.range_comp]
  have h2 : Set.range ⇑(atlasVanishingIdeal B S hS φ T hT).subschemeι =
      Set.range ⇑(atlasReducedSubscheme B S hS φ T hT).arrow := by
    rw [show (atlasVanishingIdeal B S hS φ T hT).subschemeι =
        (Subobject.underlyingIso (atlasVanishingIdeal B S hS φ T hT).subschemeι).symm.hom ≫
          (atlasReducedSubscheme B S hS φ T hT).arrow from
      (Subobject.underlyingIso_arrow _).symm]
    exact hiso _ _
  show Set.range ((BigFppfOver.toScheme B S hS).map i).base = _
  rw [← hei, hiso e _, ← h2, Scheme.IdealSheafData.range_subschemeι]
  exact coe_support_atlasVanishingIdeal B S hS φ T hT

end ReducedChart

/-! ### No immediate specialization of a chart has a drop of two -/

section Core

open Stacks.Groupoids

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- **An immediate specialization of a chart of a universally catenary space is not the end of
a strict chain of length two from a point with the same image.** Let `φ : U ⟶ X` be a surjective
étale chart by a locally Noetherian scheme of a decent algebraic space `X` all of whose decent
algebraic spaces locally of finite type are catenary. If `x ⤳ y` is an immediate
specialization of `U`, then no point `x'` of `U` with the image of `x` has a strict chain
`x' ⤳ x₁ ⤳ y`. -/
theorem false_of_isImmediateSpecialization_of_chain (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hcat : IsUniversallyCatenary B S hS X)
    (hUN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U))
    {x y : (BigFppfOver.toScheme B S hS).obj U} (hxy : IsImmediateSpecialization x y)
    {x' x₁ : (BigFppfOver.toScheme B S hS).obj U}
    (hx' : pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm x') =
      pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm x))
    (h₁ : x' ⤳ x₁) (h₂ : x₁ ⤳ y) (h₃ : x₁ ≠ x') (h₄ : x₁ ≠ y) : False := by
  classical
  set φpt : (BigFppfOver.toScheme B S hS).obj U → points B S hS X :=
    fun u ↦ pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u) with hφpt
  have hφc : Continuous φpt :=
    (continuous_pointsMap B S hS φ).comp (schemePointsHomeomorph B S hS U).symm.continuous
  have hφet := isEtale_of_presheaf_etale B S hS he
  have hφsep : ∀ {a b}, b ⤳ a → φpt a = φpt b → a = b := fun {a b} h hab ↦
    eq_of_specializes_of_pointsMap_eq_of_isDecentSpace B S hS hX hdec U φ hφet a b hab h
  have hsober := stacksSober_points_of_isDecentSpace B S hS hX hdec
  have : T0Space (points B S hS X) := (stacksSober_iff_t0_and_quasiSober.mp hsober).1
  obtain ⟨hxy, hxy', himm⟩ := hxy
  have hxx' : x' ≠ x := by
    rintro rfl
    rcases himm x₁ h₁ h₂ with h | h
    · exact h₃ h
    · exact h₄ h
  /- The reduced closed subspace on the closure of the image of `x`, and its chart. -/
  set F : Set (points B S hS X) := closure {φpt x} with hF
  have hFc : IsClosed F := isClosed_closure
  obtain ⟨V₀, i, k, hks, hke, hci, hrange, hcomm⟩ :=
    exists_reducedChart_isClosedImmersion B S hS hs he F hFc
  have hTsub := isClosedSubspace_reducedClosedSubspaceOfChart B S hS hs he
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hX F hFc
  have hTdec := isDecentSpace_of_isClosedSubspace B S hS hdec hTsub
  set ι := (BigFppfOver.toScheme B S hS).map i with hι
  have hιemb : Topology.IsClosedEmbedding ι := ι.isClosedEmbedding
  have hlift : ∀ u, φpt u ∈ F → ∃ v, ι v = u := fun u hu ↦ by
    have : u ∈ Set.range ι := by rw [hrange]; exact hu
    exact this
  have hxF : φpt x ∈ F := subset_closure rfl
  have hyF : φpt y ∈ F := specializes_iff_mem_closure.1 (hxy.map hφc)
  have hx'F : φpt x' ∈ F := by
    rw [show φpt x' = φpt x from hx']
    exact hxF
  have hx₁F : φpt x₁ ∈ F := by
    have := h₁.map hφc
    rw [show φpt x' = φpt x from hx'] at this
    exact specializes_iff_mem_closure.1 this
  obtain ⟨xh, hxh⟩ := hlift x hxF
  obtain ⟨yh, hyh⟩ := hlift y hyF
  obtain ⟨xh', hxh'⟩ := hlift x' hx'F
  obtain ⟨xh₁, hxh₁⟩ := hlift x₁ hx₁F
  have hspec : ∀ {a b p q}, ι a = p → ι b = q → p ⤳ q → a ⤳ b := fun {a b p q} ha hb h ↦
    hιemb.isInducing.specializes_iff.1 (by rw [ha, hb]; exact h)
  /- An affine open neighbourhood of `y` in that chart. -/
  have hV₀N : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V₀) :=
    LocallyOfFiniteType.isLocallyNoetherian ι
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (BigFppfOver.toScheme B S hS).obj V₀) (U := ⊤) (x := yh) trivial
  have : IsAffine W := hW
  have hxyh : xh ⤳ yh := hspec hxh hyh hxy
  have hxW : xh ∈ W := hxyh.mem_open W.isOpen hyW
  have hx₁W : xh₁ ∈ W := (hspec hxh₁ hyh h₂).mem_open W.isOpen hyW
  have hx'W : xh' ∈ W := (hspec hxh' hxh₁ h₁).mem_open W.isOpen hx₁W
  /- The chart `W` as an object of the site, and its map to `U`. -/
  set Wo := opensObject B S hS V₀ W with hWo
  set j := opensObjectι B S hS V₀ W with hj
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Wo) := (inferInstance : IsAffine W)
  set m := (BigFppfOver.toScheme B S hS).map (j ≫ i) with hm
  have hm_apply : ∀ w, m w = ι (W.ι w) := fun w ↦ rfl
  have hm_fun : (m : (BigFppfOver.toScheme B S hS).obj Wo → _) = ι ∘ W.ι := funext hm_apply
  have hm_ind : Topology.IsInducing m := by
    rw [hm_fun]
    exact hιemb.isInducing.comp W.ι.isOpenEmbedding.isInducing
  have hm_inj : Function.Injective m := by
    rw [hm_fun]
    exact hιemb.injective.comp W.ι.isOpenEmbedding.injective
  set xt : (BigFppfOver.toScheme B S hS).obj Wo := ⟨xh, hxW⟩
  set yt : (BigFppfOver.toScheme B S hS).obj Wo := ⟨yh, hyW⟩
  set xt' : (BigFppfOver.toScheme B S hS).obj Wo := ⟨xh', hx'W⟩
  set xt₁ : (BigFppfOver.toScheme B S hS).obj Wo := ⟨xh₁, hx₁W⟩
  have hmx : m xt = x := hxh
  have hmy : m yt = y := hyh
  have hmx' : m xt' = x' := hxh'
  have hmx₁ : m xt₁ = x₁ := hxh₁
  have hspecW : ∀ {a b p q}, m a = p → m b = q → p ⤳ q → a ⤳ b := fun {a b p q} ha hb h ↦
    hm_ind.specializes_iff.1 (by rw [ha, hb]; exact h)
  /- The chart `W ⟶ T` of the subspace and its kernel pair. -/
  let Pe := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have _ : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have _ : Pe.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : Pe.IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  have hjet : Pe.presheaf (yoneda.map j) :=
    MorphismProperty.relative_map (show _root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map j) from by
        show _root_.AlgebraicGeometry.Etale W.ι
        infer_instance)
  have hc : Pe.presheaf (yoneda.map j ≫ k) := MorphismProperty.comp_mem Pe.presheaf _ _ hjet hke
  obtain ⟨E, s, t, hE⟩ := exists_kernelPair_of_etale_atlas B S hS (yoneda.map j ≫ k) hc
  have hetS : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map s) :=
    hc.property _ (yoneda.map t) s hE.flip
  have hetT : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map t) :=
    hc.property _ (yoneda.map s) t hE
  have hrel : IsEtaleEquivalenceRelation (Space.relation B S hS s t) := by
    have hequiv := isEquivalenceRelation_of_isPullback B S hS (yoneda.map j ≫ k) t s hE.flip
    have h' : IsEquivalenceRelation (Space.relation B S hS s t).target
        (Space.relation B S hS s t).source := by
      rw [TwistedAffineLine.relation_target_eq, TwistedAffineLine.relation_source_eq]
      exact hequiv
    have hs' : _root_.AlgebraicGeometry.Etale (Space.relation B S hS s t).source.left := by
      rw [TwistedAffineLine.relation_source_eq]; exact hetS
    have ht' : _root_.AlgebraicGeometry.Etale (Space.relation B S hS s t).target.left := by
      rw [TwistedAffineLine.relation_target_eq]; exact hetT
    exact @IsEtaleEquivalenceRelation.mk _ _ _ _ h' hs' ht'
  have hcqc := presheafQuasiCompact_of_affine_etale_chart B S hS hTsub.1 hTdec hks hke hV₀N
    (C := Wo) inferInstance hc
  have hsqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map s) :=
    hcqc.property _ (yoneda.map t) s hE.flip
  have hWN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Wo) :=
    (inferInstance : IsLocallyNoetherian W)
  have hEN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj E) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map s)
  /- The morphism `W ⟶ X`, and its points. -/
  set ψ : yoneda.obj Wo ⟶ X := yoneda.map (j ≫ i) ≫ φ with hψdef
  have hψ : ψ = (yoneda.map j ≫ k) ≫ (reducedClosedSubspaceOfChart B S hS φ F hFc).ι := by
    rw [hψdef, Functor.map_comp, Category.assoc, Category.assoc, hcomm]
  have hψpt : ∀ w, pointsMap B S hS (yoneda.obj Wo) ψ ((pointsEquivScheme B S hS Wo).symm w) =
      φpt (m w) := by
    intro w
    rw [hψdef, pointsMap_comp_apply, ChartBranch.pointsEquivScheme_symm_pointsMap]
  have hψsep : ∀ a b : (BigFppfOver.toScheme B S hS).obj Wo, b ⤳ a →
      pointsMap B S hS (yoneda.obj Wo) ψ ((pointsEquivScheme B S hS Wo).symm a) =
        pointsMap B S hS (yoneda.obj Wo) ψ ((pointsEquivScheme B S hS Wo).symm b) → a = b := by
    intro a b hab h
    rw [hψpt, hψpt] at h
    exact hm_inj (hφsep (hab.map m.continuous) h)
  have hψlft : IsLocallyOfFiniteType B S hS ψ := by
    refine isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS Wo)
      (isAlgebraicSpace_yoneda B S hS U) hX _ _ ?_ (isLocallyOfFiniteType_of_isEtale' B S hS φ hφet)
    rw [isLocallyOfFiniteType_yoneda_map_iff]
    show LocallyOfFiniteType (W.ι ≫ ι)
    infer_instance
  /- The point `x` is generic in `W`. -/
  have hallF : ∀ w, φpt (m w) ∈ F := by
    intro w
    have : m w ∈ Set.range ι := ⟨W.ι w, rfl⟩
    rw [hrange] at this
    exact this
  have hgen : ∀ z, z ⤳ xt → z = xt := by
    intro z hz
    have hz' : m z ⤳ x := hmx ▸ hz.map m.continuous
    have h1 : φpt (m z) ⤳ φpt x := hz'.map hφc
    have h2 : φpt x ⤳ φpt (m z) := specializes_iff_mem_closure.2 (hallF z)
    have heq : φpt x = φpt (m z) := (h2.antisymm h1).eq
    exact hm_inj ((hφsep hz' heq).symm.trans hmx.symm)
  /- The closed set where the closure of `x` meets the other branches, and the subrelation which
  is trivial over it. -/
  set Y : Set ((BigFppfOver.toScheme B S hS).obj Wo) :=
    closure (closure {xt})ᶜ ∩ closure {xt} with hY
  have hYc : IsClosed Y := isClosed_closure.inter isClosed_closure
  set G : ((BigFppfOver.toScheme B S hS).obj Wo).Opens := ⟨Yᶜ, hYc.isOpen_compl⟩ with hG
  have : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Wo) := {}
  have hxG : xt ∈ G := fun h ↦ notMem_closure_compl_closure_singleton hgen h.1
  have hx'G : xt' ∈ G := by
    intro h
    have hxx'' : x ⤳ x' := by
      rw [← hmx, ← hmx']
      exact (specializes_iff_mem_closure.2 h.2).map m.continuous
    exact hxx' (hφsep hxx'' hx')
  obtain ⟨r, hrt, hrs⟩ := OpenSubRelation.exists_identitySection B S hS s t
  have hsub := OpenSubRelation.isEtaleEquivalenceRelation r hrt hrs G
  set E' := OpenSubRelation.subObject s t r hrs G with hE'
  set ιG := OpenSubRelation.subι s t r hrs G with hιG
  have hσqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map (ιG ≫ s)) := by
    rw [Functor.map_comp]
    show QuasiCompact ((OpenSubRelation.opens s t r hrs G).ι ≫ _)
    infer_instance
  have hinv : yoneda.map (ιG ≫ s) ≫ ψ = yoneda.map (ιG ≫ t) ≫ ψ := by
    have hw : ∀ (h : (reducedClosedSubspaceOfChart B S hS φ F hFc).toFunctor ⟶ X),
        yoneda.map s ≫ yoneda.map j ≫ k ≫ h = yoneda.map t ≫ yoneda.map j ≫ k ≫ h :=
      fun h ↦ by simpa only [Category.assoc] using congrArg (· ≫ h) hE.w
    rw [hψ]
    simp only [Functor.map_comp, Category.assoc]
    rw [hw]
  /- The point of the subrelation relating `x` to `x'`. -/
  have hcpt : pointsMap B S hS (yoneda.obj Wo) (yoneda.map j ≫ k)
        ((pointsEquivScheme B S hS Wo).symm xt) =
      pointsMap B S hS (yoneda.obj Wo) (yoneda.map j ≫ k)
        ((pointsEquivScheme B S hS Wo).symm xt') := by
    apply pointsMap_injective_of_mono B S hS (reducedClosedSubspaceOfChart B S hS φ F hFc).ι
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, ← hψ, hψpt, hψpt, hmx, hmx']
    exact hx'.symm
  obtain ⟨w₀, hw₀s, hw₀t⟩ := exists_point_of_isPullback_presheaf B S hS hE _ _ hcpt
  obtain ⟨ε, rfl⟩ : ∃ ε, (pointsEquivScheme B S hS E).symm ε = w₀ :=
    ⟨_, Equiv.symm_apply_apply _ _⟩
  rw [ChartBranch.pointsEquivScheme_symm_pointsMap] at hw₀s hw₀t
  have hσε : (BigFppfOver.toScheme B S hS).map s ε = xt :=
    (pointsEquivScheme B S hS Wo).symm.injective hw₀s
  have hτε : (BigFppfOver.toScheme B S hS).map t ε = xt' :=
    (pointsEquivScheme B S hS Wo).symm.injective hw₀t
  obtain ⟨ε', hε'⟩ := OpenSubRelation.exists_subι_apply_eq r hrs G ε (hτε ▸ hx'G) (hσε ▸ hxG)
  have hε's : (BigFppfOver.toScheme B S hS).map (ιG ≫ s) ε' = xt := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hε', hσε]
  have hε't : (BigFppfOver.toScheme B S hS).map (ιG ≫ t) ε' = xt' := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hε', hτε]
  have hloc : ∀ ε₂ : (BigFppfOver.toScheme B S hS).obj E',
      (BigFppfOver.toScheme B S hS).map (ιG ≫ s) ε₂ ∈ Y ∨
        (BigFppfOver.toScheme B S hS).map (ιG ≫ t) ε₂ ∈ Y →
        ∃ V : Set ((BigFppfOver.toScheme B S hS).obj E'), IsOpen V ∧ ε₂ ∈ V ∧
          ∀ ε₃ ∈ V, (BigFppfOver.toScheme B S hS).map (ιG ≫ s) ε₃ =
            (BigFppfOver.toScheme B S hS).map (ιG ≫ t) ε₃ := by
    intro ε₂ h
    refine OpenSubRelation.exists_isOpen_forall_eq r hrt hrs G ε₂ ?_
    rcases h with h | h
    · exact .inl fun hG' ↦ hG' h
    · exact .inr fun hG' ↦ hG' h
  /- The configuration, read in `W`. -/
  have hxyt : xt ⤳ yt := hspecW hmx hmy hxy
  have hxyt' : xt ≠ yt := fun h ↦ hxy' (by rw [← hmx, ← hmy, h])
  have himmt : ∀ z, xt ⤳ z → z ⤳ yt → z = xt ∨ z = yt := by
    intro z hz₁ hz₂
    have := himm (m z) (hmx ▸ hz₁.map m.continuous) (hmy ▸ hz₂.map m.continuous)
    rcases this with h | h
    · exact .inl (hm_inj (h.trans hmx.symm))
    · exact .inr (hm_inj (h.trans hmy.symm))
  have h₁t : xt' ⤳ xt₁ := hspecW hmx' hmx₁ h₁
  have h₂t : xt₁ ⤳ yt := hspecW hmx₁ hmy h₂
  have h₃t : xt₁ ≠ xt' := fun h ↦ h₃ (by rw [← hmx₁, ← hmx', h])
  have h₄t : xt₁ ≠ yt := fun h ↦ h₄ (by rw [← hmx₁, ← hmy, h])
  exact ChartBranch.false_of_branches B S hS (ιG ≫ s) (ιG ≫ t) hX hcat hσqc ψ hψlft hinv
    hψsep xt yt hxyt hxyt' himmt Y subset_rfl hloc xt' xt₁ ε' hε's hε't h₁t h₂t h₃t h₄t

include hs he in
/-- **The dimension function of a universally catenary space, read on a chart.** Let `X` be a
decent algebraic space all of whose decent algebraic spaces locally of finite type are catenary,
let `δ` be a dimension function on `|X|`, and let `φ : U ⟶ X` be a surjective étale chart by a
locally Noetherian scheme. Then `δ ∘ φ` is a dimension function on `U`.

It decreases strictly along specializations by Stacks 03K5. If it dropped by two or more along
an immediate specialization `x ⤳ y`, a point strictly between the images in `|X|` would lift,
by Stacks 03IL, to a strict chain `x' ⤳ x₁ ⤳ y` with `x'` over the image of `x`, which
`AlgebraicGeometry.Space.false_of_isImmediateSpecialization_of_chain` excludes. -/
theorem exists_dimensionFunction_comp_chart (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hcat : IsUniversallyCatenary B S hS X)
    (δ : DimensionFunction (points B S hS X))
    (hUN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ d : DimensionFunction ((BigFppfOver.toScheme B S hS).obj U), ∀ u,
      d u = δ (pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u)) := by
  classical
  set φpt : (BigFppfOver.toScheme B S hS).obj U → points B S hS X :=
    fun u ↦ pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u) with hφpt
  have hφc : Continuous φpt :=
    (continuous_pointsMap B S hS φ).comp (schemePointsHomeomorph B S hS U).symm.continuous
  have hφet := isEtale_of_presheaf_etale B S hS he
  have hφsep : ∀ {a b}, b ⤳ a → φpt a = φpt b → a = b := fun {a b} h hab ↦
    eq_of_specializes_of_pointsMap_eq_of_isDecentSpace B S hS hX hdec U φ hφet a b hab h
  have hgm := generalizingMap_pointsMap_of_isDecentSpace B S hS X hX hdec U φ he
  have hne : ∀ {a b}, a ⤳ b → a ≠ b → φpt a ≠ φpt b := fun {a b} hab hab' h ↦
    hab' (hφsep hab h.symm).symm
  refine ⟨{ toFun := fun u ↦ δ (φpt u)
            strictAnti_specializes := fun a b hab hab' ↦
              δ.strictAnti_specializes (hab.map hφc) (hne hab hab')
            step_immediate := fun x y hxy ↦ ?_ }, fun _ ↦ rfl⟩
  obtain ⟨h1, h2, h3⟩ := hxy
  have hlt := δ.strictAnti_specializes (h1.map hφc) (hne h1 h2)
  by_contra hstep
  have hnimm : ¬ IsImmediateSpecialization (φpt x) (φpt y) := fun h ↦
    hstep (δ.step_immediate h)
  obtain ⟨b₁, hxb, hby, hbx, hby'⟩ : ∃ b₁, φpt x ⤳ b₁ ∧ b₁ ⤳ φpt y ∧ b₁ ≠ φpt x ∧
      b₁ ≠ φpt y := by
    by_contra hcon
    refine hnimm ⟨h1.map hφc, hne h1 h2, fun z hz₁ hz₂ ↦ ?_⟩
    by_contra hz
    rw [not_or] at hz
    exact hcon ⟨z, hz₁, hz₂, hz.1, hz.2⟩
  have hlift : ∀ (a : points B S hS X) (u), a ⤳ φpt u → ∃ v, φpt v = a ∧ v ⤳ u := by
    intro a u h
    obtain ⟨p, hp, hpφ⟩ := hgm (show a ⤳ pointsMap B S hS (yoneda.obj U) φ
      ((pointsEquivScheme B S hS U).symm u) from h)
    refine ⟨schemePointsHomeomorph B S hS U p, ?_, ?_⟩
    · rw [← hpφ]
      change pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm
        ((pointsEquivScheme B S hS U) p)) = _
      rw [Equiv.symm_apply_apply]
    · have := hp.map (schemePointsHomeomorph B S hS U).continuous
      rwa [show (schemePointsHomeomorph B S hS U) ((pointsEquivScheme B S hS U).symm u) = u from
        (pointsEquivScheme B S hS U).apply_symm_apply u] at this
  obtain ⟨x₁, hx₁φ, hx₁y⟩ := hlift b₁ y hby
  obtain ⟨x', hx'φ, hx'x₁⟩ := hlift (φpt x) x₁ (by rw [hx₁φ]; exact hxb)
  have h₃ : x₁ ≠ x' := fun h ↦ hbx (by rw [← hx₁φ, h, hx'φ])
  have h₄ : x₁ ≠ y := fun h ↦ hby' (by rw [← hx₁φ, h])
  exact false_of_isImmediateSpecialization_of_chain B S hS hs he hX hdec hcat hUN ⟨h1, h2, h3⟩
    hx'φ hx'x₁ hx₁y h₃ h₄

end Core

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.DeterminantHypersurface
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyIrreducibleFamily
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionClassifyingProd

/-!
# The image of the classifying morphism of Tag 0B1S

Let `U` be the locus of the classifying morphism `Ψ` of Tag 0B1S. This file shows that the whole
image of `Ψ` lies in the incidence correspondence `T`, that the closure of this image is the part
of `T` over `X × Y`, and that this part is irreducible, as a set and as a scheme, when `X` and `Y`
are irreducible.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionLocusOver`: the points of the incidence
  correspondence whose first two projections lie in `X` and in `Y`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionVarietyι`: the morphism from the
  correspondence over `X ×_k Y` to the ambient triple product.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSourceToSpec_eq`: the structure morphism
  of the source factors through the base.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_eq_transitionSourcePoint`: every `k`-point
  of the source is one of the explicit points `transitionSourcePoint`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_of_isClosed_singleton`: the
  image of a closed point of the locus lies in the incidence correspondence.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_transitionClassifyingToProd_subset`: the whole
  image of `Ψ` lies in the incidence correspondence.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_closure_range_transitionClassifying`:
  the closure of that image is irreducible.
* `ProjectiveSpaceOfModule.mem_range_transitionClassifyingToProd_of_isClosed_singleton`: every
  closed point of the correspondence over `X × Y` is in the image of `Ψ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.closure_range_transitionClassifyingToProd`: the
  correspondence over `X × Y` is the closure of the image of `Ψ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_transitionLocusOver`: it is
  irreducible.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_prodOfClosedToProdTwo`: the points of
  `X ×_k Y` inside `𝐏(V) ×_k 𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_transitionVarietyι`: the points of the
  correspondence over `X × Y` as a scheme are that same set.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_transitionVariety`: the
  correspondence over `X × Y` is irreducible as a scheme.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- **A `k`-point lands on a closed point.** The image of the point of `Spec k` under a `k`-point
of a scheme locally of finite type over an algebraically closed field `k` is a closed point. -/
public theorem isClosed_singleton_base_of_comp_eq_id {k : Type u} [Field k] [IsAlgClosed k]
    {Z : Scheme.{u}} (gZ : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType gZ]
    (q : Spec (CommRingCat.of k) ⟶ Z) (hq : q ≫ gZ = 𝟙 _) (a : Spec (CommRingCat.of k)) :
    IsClosed ({q.base a} : Set Z) := by
  rw [show a = IsLocalRing.closedPoint k from Subsingleton.elim _ _]
  exact mem_closedPoints_iff.mp (pointEquivClosedPoint gZ ⟨q, hq⟩).property

/-- The image of a `k`-point `τ` of `Z` under a morphism `g` over the base is a closed point. -/
private theorem isClosed_singleton_base_comp_of_comp_eq_id {k : Type u} [Field k] [IsAlgClosed k]
    {Z W : Scheme.{u}} (gZ : Z ⟶ Spec (CommRingCat.of k)) (gW : W ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType gW] (g : Z ⟶ W) (hg : g ≫ gW = gZ) (τ : Spec (CommRingCat.of k) ⟶ Z)
    (hτ : τ ≫ gZ = 𝟙 _) (a : Spec (CommRingCat.of k)) : IsClosed ({g.base (τ.base a)} : Set W) :=
  isClosed_singleton_base_of_comp_eq_id gW (τ ≫ g) (by rw [Category.assoc, hg, hτ]) a

namespace ProjectiveSpaceOfModule

attribute [local instance] isInvertible_tautologicalModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (X Y : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hYc : IsClosed Y)

/-! ### The product of the two closed subvarieties inside `𝐏(V) ×_k 𝐏(V)` -/

/-- **The product of two closed subschemes is a closed subscheme of the product**: the morphism
`X ×_k Y ⟶ 𝐏(V) ×_k 𝐏(V)` is a closed immersion. -/
public instance isClosedImmersion_prodOfClosedToProdTwo :
    IsClosedImmersion (prodOfClosedToProdTwo k V X Y hXc hYc) := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance rfl rfl

/-- **The points of `X ×_k Y` inside `𝐏(V) ×_k 𝐏(V)` are the pairs whose first point lies in `X`
and whose second lies in `Y`.** -/
public theorem range_prodOfClosedToProdTwo :
    Set.range (prodOfClosedToProdTwo k V X Y hXc hYc).base =
      (pullback.fst (projectiveSpaceOfModuleToSpec k V)
            (projectiveSpaceOfModuleToSpec k V)).base ⁻¹' X ∩
        (pullback.snd (projectiveSpaceOfModuleToSpec k V)
            (projectiveSpaceOfModuleToSpec k V)).base ⁻¹' Y := by
  have h := Scheme.Pullback.range_map (closedSubschemeOfToSpec k V X hXc)
    (closedSubschemeOfToSpec k V Y hYc) (projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k V) (closedSubschemeOfι k V X hXc)
    (closedSubschemeOfι k V Y hYc) (𝟙 _) (Category.comp_id _) (Category.comp_id _)
  rwa [range_closedSubschemeOfι, range_closedSubschemeOfι] at h

/-! ### The source and the locus are locally of finite type over the ground field -/

/-- **The structure morphism of the source factors through the base.** It is the projection to
`X × Y`, followed by the first projection, the inclusion of `X` into `𝐏(V)` and the structure
morphism of `𝐏(V)`. -/
public theorem transitionSourceToSpec_eq :
    transitionSourceToSpec k V X Y hXc hYc =
      transitionSourceToBase k V X Y hXc hYc ≫
        pullback.fst (closedSubschemeOfToSpec k V X hXc) (closedSubschemeOfToSpec k V Y hYc) ≫
          closedSubschemeOfι k V X hXc ≫ projectiveSpaceOfModuleToSpec k V :=
  calc transitionSourceToSpec k V X Y hXc hYc
      = (transitionSourceToBase k V X Y hXc hYc ≫
            pullback.fst (closedSubschemeOfToSpec k V X hXc)
                (closedSubschemeOfToSpec k V Y hYc) ≫
              closedSubschemeOfι k V X hXc) ≫ projectiveSpaceOfModuleToSpec k V := rfl
    _ = transitionSourceToBase k V X Y hXc hYc ≫
          (pullback.fst (closedSubschemeOfToSpec k V X hXc)
                (closedSubschemeOfToSpec k V Y hYc) ≫
              closedSubschemeOfι k V X hXc) ≫ projectiveSpaceOfModuleToSpec k V :=
        Category.assoc _ _ _
    _ = _ := congrArg (fun m => transitionSourceToBase k V X Y hXc hYc ≫ m)
        (Category.assoc _ _ _)

variable [FiniteDimensional k V] [Nontrivial V]

/-- The parameter module is nontrivial. -/
private theorem nontrivial_parameterModule : Nontrivial (ParameterModule k V) := by
  refine Module.nontrivial_of_finrank_pos (R := k) ?_
  rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
  exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

/-- **The source is locally of finite type over the ground field.** -/
public instance locallyOfFiniteType_transitionSourceToSpec :
    LocallyOfFiniteType (transitionSourceToSpec k V X Y hXc hYc) := by
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
    have := isProper_projectiveSpaceOfModuleToSpec k V
    infer_instance
  have hfst : LocallyOfFiniteType (pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  rw [transitionSourceToSpec_eq]
  exact MorphismProperty.comp_mem _ _ _ inferInstance
    (MorphismProperty.comp_mem _ _ _ hfst
      (MorphismProperty.comp_mem _ _ _ inferInstance inferInstance))

variable (b : Module.Basis (Fin (Module.finrank k V)) k V)

/-- **The locus of the classifying morphism is locally of finite type over the ground field.** -/
public instance locallyOfFiniteType_transitionClassifyingOpenToSpec :
    LocallyOfFiniteType ((transitionClassifyingOpen k V X Y hXc hYc b).ι ≫
      transitionSourceToSpec k V X Y hXc hYc) :=
  inferInstance

/-- **The locus is a Jacobson space**: its closed points are dense in every closed subset. -/
public instance jacobsonSpace_transitionClassifyingOpen :
    JacobsonSpace (transitionClassifyingOpen k V X Y hXc hYc b).toScheme :=
  LocallyOfFiniteType.jacobsonSpace ((transitionClassifyingOpen k V X Y hXc hYc b).ι ≫
    transitionSourceToSpec k V X Y hXc hYc)

/-! ### Every `k`-point of the source is one of the explicit points -/

omit [FiniteDimensional k V] [Nontrivial V] in
/-- **Every `k`-point of the source is one of the explicit points.** A `k`-point `p` of the source
is `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSourcePoint` at its base component and at
some scalar, three vectors and an endomorphism of `V`. -/
public theorem exists_eq_transitionSourcePoint
    (p : Spec (CommRingCat.of k) ⟶ transitionSource k V X Y hXc hYc) :
    ∃ (c : k) (u u' w : V) (h : V →ₗ[k] V),
      p = transitionSourcePoint k V X Y hXc hYc b
        (p ≫ transitionSourceToBase k V X Y hXc hYc) c u u' w h := by
  classical
  set v : transitionParamIndex k V → k := fun i =>
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      (p.appTop.hom (AffineSpace.coord (prodOfClosed k V X Y hXc hYc) i)) with hv
  have hback : ∀ i : transitionParamIndex k V,
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (v i) =
        p.appTop.hom (AffineSpace.coord (prodOfClosed k V X Y hXc hYc) i) := fun i =>
    congrArg (fun m : Γ(Spec (CommRingCat.of k), ⊤) ⟶ Γ(Spec (CommRingCat.of k), ⊤) => m.hom
      (p.appTop.hom (AffineSpace.coord (prodOfClosed k V X Y hXc hYc) i)))
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
  have hcoord : ∀ (g : Fin (Module.finrank k V) → k) (i : Fin (Module.finrank k V)),
      b.coord i (b.equivFun.symm g) = g i := by
    intro g i
    rw [Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨v ⟨Sum.inl ()⟩,
    b.equivFun.symm fun i => v ⟨Sum.inr (Sum.inl i)⟩,
    b.equivFun.symm fun j => v ⟨Sum.inr (Sum.inr (Sum.inl j))⟩,
    b.equivFun.symm fun i => v ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))⟩,
    b.constr k fun t => b.equivFun.symm fun i =>
      v ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, t))))⟩, ?_⟩
  refine AffineSpace.hom_ext ?_ fun i => ?_
  · rw [transitionSourcePoint, AffineSpace.homOfVector_over]
  · rw [transitionSourcePoint, AffineSpace.homOfVector_appTop_coord, ← hback i]
    congr 1
    obtain ⟨i⟩ := i
    rcases i with _ | i | j | i | ⟨i, t⟩
    · rfl
    · rw [transitionParamCoords_u, hcoord]
    · rw [transitionParamCoords_u', hcoord]
    · rw [transitionParamCoords_w, hcoord]
    · rw [transitionParamCoords_h, Module.Basis.constr_basis, hcoord]

/-! ### The image of a closed point, and of the whole locus -/

section Range

variable [IsAlgClosed k]

/-- **The image of a closed point of the locus lies in the incidence correspondence.** -/
public theorem mem_transitionLocus_of_isClosed_singleton
    (x : (transitionClassifyingOpen k V X Y hXc hYc b).toScheme)
    (hxc : IsClosed ({x} : Set (transitionClassifyingOpen k V X Y hXc hYc b).toScheme)) :
    (transitionClassifyingToProd k V X Y hXc hYc b).base x ∈ transitionLocus k V := by
  set gU := (transitionClassifyingOpen k V X Y hXc hYc b).ι ≫
    transitionSourceToSpec k V X Y hXc hYc with hgU
  set a := IsLocalRing.closedPoint k with ha
  set p := pointOfClosedPoint gU x hxc ≫
    (transitionClassifyingOpen k V X Y hXc hYc b).ι with hp
  have hpspec : p ≫ transitionSourceToSpec k V X Y hXc hYc = 𝟙 _ := by
    rw [hp, Category.assoc]
    exact pointOfClosedPoint_comp gU x hxc
  have hpa : p.base a = (transitionClassifyingOpen k V X Y hXc hYc b).ι.base x := by
    show (transitionClassifyingOpen k V X Y hXc hYc b).ι.base
      ((pointOfClosedPoint gU x hxc).base a) = _
    rw [pointOfClosedPoint_apply gU x hxc a]
  obtain ⟨c, u, u', w, h, hpeq⟩ := exists_eq_transitionSourcePoint k V X Y hXc hYc b p
  set pt := p ≫ transitionSourceToBase k V X Y hXc hYc with hpt
  have hm₁ : p ≫ tsSource k V X Y hXc hYc =
      pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc := by
    rw [hpeq]
    exact transitionSourcePoint_comp_tsSource k V X Y hXc hYc b pt c u u' w h
  have hm₂ : p ≫ tsTarget k V X Y hXc hYc =
      pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc := by
    rw [hpeq]
    exact transitionSourcePoint_comp_tsTarget k V X Y hXc hYc b pt c u u' w h
  have hpt' : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _ := by
    have hassoc : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
          (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc ≫
            projectiveSpaceOfModuleToSpec k V =
        p ≫ transitionSourceToBase k V X Y hXc hYc ≫
          pullback.fst (closedSubschemeOfToSpec k V X hXc)
              (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc ≫
            projectiveSpaceOfModuleToSpec k V := by
      rw [hpt]
      exact Category.assoc _ _ _
    show pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc ≫
          projectiveSpaceOfModuleToSpec k V = 𝟙 _
    rw [hassoc, ← transitionSourceToSpec_eq]
    exact hpspec
  obtain ⟨f, hf, hfeq⟩ := exists_eq_linearFunctionalPoint k V
    ((p ≫ tsSource k V X Y hXc hYc).base a)
    (isClosed_singleton_base_comp_of_comp_eq_id _ _ _ (tsSource_comp_toSpec k V X Y hXc hYc) p
      hpspec a)
  obtain ⟨f', hf', hf'eq⟩ := exists_eq_linearFunctionalPoint k V
    ((p ≫ tsTarget k V X Y hXc hYc).base a)
    (isClosed_singleton_base_comp_of_comp_eq_id _ _ _ (tsTarget_comp_toSpec k V X Y hXc hYc) p
      hpspec a)
  have e₁ : (pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc).base a =
      linearFunctionalPoint k V f hf := by
    rwa [← hm₁]
  have e₂ : (pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc).base a =
      linearFunctionalPoint k V f' hf' := by
    rwa [← hm₂]
  have hx : (transitionClassifyingOpen k V X Y hXc hYc b).ι.base x =
      (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a := by
    rw [← hpa, hpeq]
  obtain ⟨φ, hφ⟩ := (mem_transitionClassifyingOpen_iff k V X Y hXc hYc b _).mp x.2
  have hφG : φ (transitionEnd k V f f' c u u' w h) ≠ 0 :=
    (mem_nonvanishingOpen_transitionSections_point_iff k V X Y hXc hYc b pt hpt' c u u' w h a
      f hf e₁ f' hf' e₂ φ).mp (hx ▸ hφ)
  have hG : transitionEnd k V f f' c u u' w h ≠ 0 := fun h0 => hφG (by rw [h0, map_zero])
  exact mem_transitionLocus_transitionClassifyingToProd pt hpt' c u u' w h a f hf e₁ f' hf' e₂
    x hx (Module.Dual.eval k (V →ₗ[k] V) (transitionEnd k V f f' c u u' w h))
    (eval_ne_zero k V hG) fun _ => rfl

/-- **The whole image of `Ψ` lies in the incidence correspondence.** -/
public theorem range_transitionClassifyingToProd_subset :
    Set.range (transitionClassifyingToProd k V X Y hXc hYc b).base ⊆ transitionLocus k V := by
  rintro _ ⟨z, rfl⟩
  exact Set.subset_of_isClosed_of_closedPoints_subset isClosed_univ
    ((isClosed_transitionLocus k V).preimage
      (transitionClassifyingToProd k V X Y hXc hYc b).base.hom.continuous)
    (fun z _ hz => mem_transitionLocus_of_isClosed_singleton k V X Y hXc hYc b z hz)
    (Set.mem_univ z)

/-- **The closure of the image of `Ψ` is irreducible** when `X` and `Y` are. -/
public theorem isIrreducible_closure_range_transitionClassifying
    (hXirr : IsIrreducible X) (hYirr : IsIrreducible Y) :
    IsIrreducible (closure (Set.range (transitionClassifyingToProd k V X Y hXc hYc b).base)) := by
  have := irreducibleSpace_transitionClassifyingOpen_of_isIrreducible k V X Y hXc hYc b
    hXirr hYirr
  have himg : IsIrreducible (Set.range (transitionClassifyingToProd k V X Y hXc hYc b).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ
      (transitionClassifyingOpen k V X Y hXc hYc b).toScheme).image _
      (transitionClassifyingToProd k V X Y hXc hYc b).base.hom.continuous.continuousOn
  exact himg.closure

/-- **The closure of the image of `Ψ` is contained in the incidence correspondence.** -/
public theorem closure_range_transitionClassifyingToProd_subset :
    closure (Set.range (transitionClassifyingToProd k V X Y hXc hYc b).base) ⊆
      transitionLocus k V :=
  closure_minimal (range_transitionClassifyingToProd_subset k V X Y hXc hYc b)
    (isClosed_transitionLocus k V)

/-! ### Every closed point of the correspondence over `X × Y` is in the image -/

/-- **Every closed point of the correspondence over `X × Y` is in the image of `Ψ`.** A closed
point `t` of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` lying on the incidence correspondence, whose first two
projections lie in `X` and in `Y`, is the image under `Ψ` of a point of the locus. -/
public theorem mem_range_transitionClassifyingToProd_of_isClosed_singleton
    (t : transitionProd k V) (htc : IsClosed ({t} : Set (transitionProd k V)))
    (ht : t ∈ transitionLocus k V) (htX : (tpSource k V).base t ∈ X)
    (htY : (tpTarget k V).base t ∈ Y) :
    t ∈ Set.range (transitionClassifyingToProd k V X Y hXc hYc b).base := by
  have hntP := nontrivial_parameterModule k V
  obtain ⟨a⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨IsLocalRing.closedPoint k⟩
  set τ := pointOfClosedPoint (transitionProdToSpec k V) t htc with hτdef
  have hτspec : τ ≫ transitionProdToSpec k V = 𝟙 _ :=
    pointOfClosedPoint_comp (transitionProdToSpec k V) t htc
  have hτa : τ.base a = t := pointOfClosedPoint_apply (transitionProdToSpec k V) t htc a
  have hc₁ : IsClosed ({(tpSource k V).base t} : Set (projectiveSpaceOfModule k V)) :=
    hτa ▸ isClosed_singleton_base_comp_of_comp_eq_id _ _ _ (tpSource_comp_toSpec k V) τ hτspec a
  have hc₂ : IsClosed ({(tpTarget k V).base t} : Set (projectiveSpaceOfModule k V)) :=
    hτa ▸ isClosed_singleton_base_comp_of_comp_eq_id _ _ _ (tpTarget_comp_toSpec k V) τ hτspec a
  have hc₃ : IsClosed ({(tpPar k V).base t} :
      Set (projectiveSpaceOfModule k (ParameterModule k V))) :=
    hτa ▸ isClosed_singleton_base_comp_of_comp_eq_id _ _ _ (tpPar_comp_toSpec k V) τ hτspec a
  obtain ⟨f, hf, hfeq⟩ := exists_eq_linearFunctionalPoint k V ((tpSource k V).base t) hc₁
  obtain ⟨f', hf', hf'eq⟩ := exists_eq_linearFunctionalPoint k V ((tpTarget k V).base t) hc₂
  obtain ⟨f₃, hf₃, hf₃eq⟩ := exists_eq_linearFunctionalPoint k (ParameterModule k V)
    ((tpPar k V).base t) hc₃
  set g := (Module.evalEquiv k (V →ₗ[k] V)).symm f₃ with hgdef
  have hgval : ∀ ψ : ParameterModule k V, f₃ ψ = ψ g := fun ψ =>
    (Module.apply_evalEquiv_symm_apply k (V →ₗ[k] V) ψ f₃).symm
  have hgne : g ≠ 0 := fun h0 =>
    hf₃ (LinearMap.ext fun ψ => by rw [hgval ψ, h0, map_zero, LinearMap.zero_apply])
  have hgsub : g ∈ transitionSubmodule k V f f' :=
    (mem_transitionLocus_iff_of_linearFunctionalPoint k V t f hf hfeq f' hf' hf'eq f₃ hf₃
      hf₃eq g hgval).mp ht
  obtain ⟨c, u, u', w, heq⟩ := exists_transitionEnd_eq k V hf hf' hgsub
  obtain ⟨x₁, hx₁, hx₁c⟩ := exists_isClosed_closedSubschemeOf k V X hXc
    (linearFunctionalPoint_isClosed k V f hf) (hfeq ▸ htX)
  obtain ⟨y₁, hy₁, hy₁c⟩ := exists_isClosed_closedSubschemeOf k V Y hYc
    (linearFunctionalPoint_isClosed k V f' hf') (hf'eq ▸ htY)
  set pt := prodOfClosedPoint k V X Y hXc hYc x₁ hx₁c y₁ hy₁c with hptdef
  have hpt := prodOfClosedPoint_comp_toSpec k V X Y hXc hYc x₁ hx₁c y₁ hy₁c
  have e₁ := (prodOfClosedPoint_base_fst k V X Y hXc hYc x₁ hx₁c y₁ hy₁c a).trans hx₁
  have e₂ := (prodOfClosedPoint_base_snd k V X Y hXc hYc x₁ hx₁c y₁ hy₁c a).trans hy₁
  have hGne : transitionEnd k V f f' c u u' w g ≠ 0 := by
    rwa [heq]
  have hmem : (transitionSourcePoint k V X Y hXc hYc b pt c u u' w g).base a ∈
      transitionClassifyingOpen k V X Y hXc hYc b :=
    mem_transitionClassifyingOpen_of_transitionEnd_ne_zero pt hpt c u u' w g a f hf e₁
      f' hf' e₂ hGne
  have hrange : Set.range (transitionSourcePoint k V X Y hXc hYc b pt c u u' w g).base ⊆
      Set.range (transitionClassifyingOpen k V X Y hXc hYc b).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a', rfl⟩
    rw [show a' = a from Subsingleton.elim _ _]
    exact hmem
  set σ := IsOpenImmersion.lift (transitionClassifyingOpen k V X Y hXc hYc b).ι
    (transitionSourcePoint k V X Y hXc hYc b pt c u u' w g) hrange with hσdef
  have hσfac : σ ≫ (transitionClassifyingOpen k V X Y hXc hYc b).ι =
      transitionSourcePoint k V X Y hXc hYc b pt c u u' w g :=
    IsOpenImmersion.lift_fac _ _ hrange
  refine ⟨σ.base a, ?_⟩
  have hzx : (transitionClassifyingOpen k V X Y hXc hYc b).ι.base (σ.base a) =
      (transitionSourcePoint k V X Y hXc hYc b pt c u u' w g).base a :=
    show (σ ≫ (transitionClassifyingOpen k V X Y hXc hYc b).ι).base a = _ from by rw [hσfac]
  have hΨspec : (σ ≫ transitionClassifyingToProd k V X Y hXc hYc b) ≫
      transitionProdToSpec k V = 𝟙 _ := by
    rw [Category.assoc, transitionClassifyingToProd_comp_toSpec, ← Category.assoc, hσfac]
    exact transitionSourcePoint_comp_toSpec k V X Y hXc hYc b pt hpt c u u' w g
  have hclΨ : IsClosed ({(transitionClassifyingToProd k V X Y hXc hYc b).base (σ.base a)} :
      Set (transitionProd k V)) :=
    isClosed_singleton_base_of_comp_eq_id (transitionProdToSpec k V)
      (σ ≫ transitionClassifyingToProd k V X Y hXc hYc b) hΨspec a
  have p₁ : (tpSource k V).base
      ((transitionClassifyingToProd k V X Y hXc hYc b).base (σ.base a)) =
      (tpSource k V).base t :=
    (tpSource_base_transitionClassifyingToProd pt c u u' w g a f hf e₁ _ hzx).trans hfeq.symm
  have p₂ : (tpTarget k V).base
      ((transitionClassifyingToProd k V X Y hXc hYc b).base (σ.base a)) =
      (tpTarget k V).base t :=
    (tpTarget_base_transitionClassifyingToProd pt c u u' w g a f' hf' e₂ _ hzx).trans hf'eq.symm
  have p₃ : (tpPar k V).base
      ((transitionClassifyingToProd k V X Y hXc hYc b).base (σ.base a)) =
      (tpPar k V).base t :=
    (tpPar_base_transitionClassifyingToProd pt hpt c u u' w g a f hf e₁ f' hf' e₂ _ hzx f₃ hf₃
      (fun φ => by rw [hgval φ, heq])).trans hf₃eq.symm
  have hclfstΨ : IsClosed ({(tpFst k V).base
                              ((transitionClassifyingToProd k V X Y hXc hYc b).base (σ.base a))} :
      Set (prodTwo k V)) :=
    isClosed_singleton_base_comp_of_comp_eq_id _ _ _ (tpFst_comp_toSpec k V)
      (σ ≫ transitionClassifyingToProd k V X Y hXc hYc b) hΨspec a
  have hclfstt : IsClosed ({(tpFst k V).base t} : Set (prodTwo k V)) :=
    hτa ▸ isClosed_singleton_base_comp_of_comp_eq_id _ _ _ (tpFst_comp_toSpec k V) τ hτspec a
  have hfst : (tpFst k V).base
      ((transitionClassifyingToProd k V X Y hXc hYc b).base (σ.base a)) =
      (tpFst k V).base t :=
    eq_of_isClosed_singleton_of_proj_eq (projectiveSpaceOfModuleToSpec k V)
      (projectiveSpaceOfModuleToSpec k V) hclfstΨ hclfstt p₁ p₂
  exact eq_of_isClosed_singleton_of_proj_eq (prodTwoToSpec k V)
    (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) hclΨ htc hfst p₃

/-! ### The correspondence over `X × Y` is irreducible -/

/-- **The set the correspondence over `X × Y` carries**: the triples of the incidence
correspondence whose first two coordinates lie in `X` and in `Y`. -/
public def transitionLocusOver : Set (transitionProd k V) :=
  transitionLocus k V ∩ (tpSource k V).base ⁻¹' X ∩ (tpTarget k V).base ⁻¹' Y

omit [Nontrivial V] [IsAlgClosed k] in
include hXc hYc in
/-- The set `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionLocusOver` is closed. -/
public theorem isClosed_transitionLocusOver :
    IsClosed (transitionLocusOver k V X Y) :=
  ((isClosed_transitionLocus k V).inter
      (hXc.preimage (tpSource k V).base.hom.continuous)).inter
    (hYc.preimage (tpTarget k V).base.hom.continuous)

/-- **The image of `Ψ` lies in the correspondence over `X × Y`.** -/
public theorem range_transitionClassifyingToProd_subset_transitionLocusOver :
    Set.range (transitionClassifyingToProd k V X Y hXc hYc b).base ⊆
      transitionLocusOver k V X Y := by
  rintro _ ⟨z, rfl⟩
  refine ⟨⟨range_transitionClassifyingToProd_subset k V X Y hXc hYc b ⟨z, rfl⟩, ?_⟩, ?_⟩
  · have h1 : (tpSource k V).base ((transitionClassifyingToProd k V X Y hXc hYc b).base z) =
        ((transitionClassifyingOpen k V X Y hXc hYc b).ι ≫ tsSource k V X Y hXc hYc).base z := by
      rw [← transitionClassifyingToProd_comp_tpSource k V X Y hXc hYc b]
      rfl
    show (tpSource k V).base ((transitionClassifyingToProd k V X Y hXc hYc b).base z) ∈ X
    rw [h1]
    exact (range_closedSubschemeOfι k V X hXc).subset
      ⟨(pullback.fst (closedSubschemeOfToSpec k V X hXc)
          (closedSubschemeOfToSpec k V Y hYc)).base
        ((transitionSourceToBase k V X Y hXc hYc).base
          ((transitionClassifyingOpen k V X Y hXc hYc b).ι.base z)), rfl⟩
  · have h2 : (tpTarget k V).base ((transitionClassifyingToProd k V X Y hXc hYc b).base z) =
        ((transitionClassifyingOpen k V X Y hXc hYc b).ι ≫ tsTarget k V X Y hXc hYc).base z := by
      rw [← transitionClassifyingToProd_comp_tpTarget k V X Y hXc hYc b]
      rfl
    show (tpTarget k V).base ((transitionClassifyingToProd k V X Y hXc hYc b).base z) ∈ Y
    rw [h2]
    exact (range_closedSubschemeOfι k V Y hYc).subset
      ⟨(pullback.snd (closedSubschemeOfToSpec k V X hXc)
          (closedSubschemeOfToSpec k V Y hYc)).base
        ((transitionSourceToBase k V X Y hXc hYc).base
          ((transitionClassifyingOpen k V X Y hXc hYc b).ι.base z)), rfl⟩

/-- **The correspondence over `X × Y` is the closure of the image of `Ψ`.** -/
public theorem closure_range_transitionClassifyingToProd :
    closure (Set.range (transitionClassifyingToProd k V X Y hXc hYc b).base) =
      transitionLocusOver k V X Y := by
  have hntP := nontrivial_parameterModule k V
  have : JacobsonSpace (transitionProd k V) :=
    LocallyOfFiniteType.jacobsonSpace (transitionProdToSpec k V)
  refine Set.Subset.antisymm (closure_minimal
    (range_transitionClassifyingToProd_subset_transitionLocusOver k V X Y hXc hYc b)
    (isClosed_transitionLocusOver k V X Y hXc hYc)) ?_
  refine Set.subset_of_isClosed_of_closedPoints_subset
    (isClosed_transitionLocusOver k V X Y hXc hYc) isClosed_closure fun s hs hsc =>
    subset_closure ?_
  exact mem_range_transitionClassifyingToProd_of_isClosed_singleton k V X Y hXc hYc b s hsc
    hs.1.1 hs.1.2 hs.2

include hXc hYc b in
/-- **The correspondence over `X × Y` is irreducible** when `X` and `Y` are. -/
public theorem isIrreducible_transitionLocusOver (hXirr : IsIrreducible X)
    (hYirr : IsIrreducible Y) :
    IsIrreducible (transitionLocusOver k V X Y) :=
  closure_range_transitionClassifyingToProd k V X Y hXc hYc b ▸
    isIrreducible_closure_range_transitionClassifying k V X Y hXc hYc b hXirr hYirr

/-! ### The correspondence over `X × Y` is irreducible as a scheme -/

/-- **The correspondence over `X × Y` inside the ambient triple product**: its projection to the
incidence correspondence followed by the inclusion of that closed subscheme. -/
public abbrev transitionVarietyι :
    transitionVariety k V (prodOfClosedToProdTwo k V X Y hXc hYc) ⟶ transitionProd k V :=
  transitionVarietyToSubscheme k V (prodOfClosedToProdTwo k V X Y hXc hYc) ≫
    transitionSubschemeι k V

omit [Nontrivial V] [IsAlgClosed k] in
/-- **The points of the correspondence over `X × Y` are exactly
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionLocusOver`.** -/
public theorem range_transitionVarietyι :
    Set.range (transitionVarietyι k V X Y hXc hYc).base = transitionLocusOver k V X Y := by
  have h1 : Set.range (transitionVarietyToSubscheme k V
        (prodOfClosedToProdTwo k V X Y hXc hYc)).base =
      (transitionProj k V).base ⁻¹' Set.range (prodOfClosedToProdTwo k V X Y hXc hYc).base :=
    Scheme.Pullback.range_fst _ _
  have h2 : Set.range (transitionVarietyι k V X Y hXc hYc).base =
      (transitionSubschemeι k V).base ''
        Set.range (transitionVarietyToSubscheme k V
          (prodOfClosedToProdTwo k V X Y hXc hYc)).base := by
    refine Set.ext fun s => ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  have h3 : (transitionProj k V).base ⁻¹'
        Set.range (prodOfClosedToProdTwo k V X Y hXc hYc).base =
      (transitionSubschemeι k V).base ⁻¹' ((tpFst k V).base ⁻¹'
        Set.range (prodOfClosedToProdTwo k V X Y hXc hYc).base) := by
    rw [transitionProj]
    exact Set.preimage_comp
  rw [h2, h1, h3, Set.image_preimage_eq_inter_range, range_transitionSubschemeι,
    range_prodOfClosedToProdTwo, Set.preimage_inter]
  ext s
  simp only [transitionLocusOver, Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨fun h => ⟨⟨h.2, h.1.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.2, h.2⟩, h.1.1⟩⟩

include hXc hYc b in
/-- **The correspondence over `X × Y` is irreducible as a scheme** when `X` and `Y` are. -/
public theorem irreducibleSpace_transitionVariety (hXirr : IsIrreducible X)
    (hYirr : IsIrreducible Y) :
    IrreducibleSpace (transitionVariety k V (prodOfClosedToProdTwo k V X Y hXc hYc)) := by
  have : IrreducibleSpace ↥(transitionLocusOver k V X Y) :=
    isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_transitionLocusOver k V X Y hXc hYc b hXirr hYirr)
  have : IsClosedImmersion (transitionVarietyToSubscheme k V
      (prodOfClosedToProdTwo k V X Y hXc hYc)) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst (transitionProj k V)
      (prodOfClosedToProdTwo k V X Y hXc hYc)))
  exact ((transitionVarietyι k V X Y hXc hYc).isClosedEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_transitionVarietyι k V X Y hXc hYc))).irreducibleSpace_iff.mpr
    inferInstance

end Range

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end

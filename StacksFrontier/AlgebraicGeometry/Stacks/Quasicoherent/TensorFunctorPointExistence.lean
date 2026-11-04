module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineTensorAlgebraFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackEffectiveDescent
public import StacksFrontier.RingTheory.Descent.FaithfullyFlatGenerators
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismConstructionA

/-!
# The point `x_C` of Stacks 0GRQ

Let `g : U ⟶ 𝒳` be an affine morphism from an affine scheme `U = Spec A` to an algebraic stack,
`F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact tensor functor commuting with direct sums and
`C = F(g_{QCoh,*}𝒪_U)` with its ring map `A ⟶ C` (Stacks 0GRK). In the proof of Stacks 0GRQ the
point `x_C : Spec C ⟶ U ⟶ 𝒳` is descended to `Spec R`. This file shows that `Spec C` is an object
of the big fppf site (when `R ⟶ C` is faithfully flat and `Spec R` is one) and constructs `x_C`
as the pullback of the chart point `g(U)` along `Spec C ⟶ Spec A`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.contains_spec_affineTensorAlgebra`: `Spec C` lies in
  the site.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_point_over_affineTensorAlgebra`: the point
  `x_C` over `Spec C`, with its arrow to `g(U)` lying over `Spec C ⟶ Spec A`.

## References

* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For a `C`-linear isomorphism `e : M ≃ C ⊗_A N`, the elements `e⁻¹(1 ⊗ n)` span `M` over `C`
(here indexed through a surjection onto `N`). -/
theorem span_range_symm_one_tmul {A C M N ι : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup M] [Module C M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[C] C ⊗[A] N)
    (j : ι → N) (hj : Function.Surjective j) :
    Submodule.span C (Set.range fun r => e.symm ((1 : C) ⊗ₜ[A] j r)) = ⊤ := by
  refine eq_top_iff.2 fun t _ => ?_
  rw [← e.symm_apply_apply t]
  generalize e t = s
  induction s using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | tmul c n =>
    obtain ⟨r, rfl⟩ := hj n
    rw [show c ⊗ₜ[A] j r = c • ((1 : C) ⊗ₜ[A] j r) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- **The functions on an object of an algebraic stack over an affine scheme form a ring whose
spectrum lies in the site.** -/
theorem contains_spec_fppfStructurePresheaf_obj {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (z : 𝒴.val.val.obj) [IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj z))] :
    B.Contains (Spec (CommRingCat.of ((fppfStructurePresheaf B S hS 𝒴).obj (op z)))) := by
  let X := (BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj z)
  let e := pointRingIso B S hS 𝒴 z X.isoSpec
  calc (Spec (CommRingCat.of ((fppfStructurePresheaf B S hS 𝒴).obj (op z)))).size = X.size :=
        (Scheme.size_congr (Scheme.Spec.mapIso e.op)).trans (Scheme.size_congr X.isoSpec).symm
    _ < B.cutoff := (𝒴.val.val.p.obj z).left.2

section Theta

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

variable {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : IsAffineHom B S hS g)
  {R : Type u} [CommRing R]
  (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Braided] [F.Additive]
  [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
  (hU : IsAffineOver B S hS U)

include hU in
/-- The object `r(g(U))` of `U`, the fibre product `U ×_𝒳 U`, lies over an affine scheme. -/
theorem isAffine_toScheme_affineRightAdjoint_obj :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((schemeStack.{u, w} B S hS U).val.val.p.obj
      ((affineRightAdjoint g hg).obj (g.hom.hom.toFunctor.obj (siteTop.{u, w} U))))) := by
  have hsrc := @isAffine_of_isAffineHom _ _ _
    (isAffineHom_map_affineAdjunction_counit g hg (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)))
    (isAffine_toScheme_p_obj_siteTop g hU)
  exact (congrArg (fun T => IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Functor.congr_obj g.hom.hom.w _)).mp hsrc

include hU in
/-- **`Spec C` is an object of the site** (Stacks 0GRQ, proof): `R ⟶ C` is faithfully flat and
`C ⊗_R C ≅ C ⊗_A Γ(U ×_𝒳 U)` is spanned over `C` by a family indexed by `Γ(U ×_𝒳 U)`, whose
spectrum lies in the site. -/
theorem contains_spec_affineTensorAlgebra (hR : B.Contains (Spec (CommRingCat.of R)))
    (hfl : (algebraMap R (affineTensorAlgebra g hg F)).FaithfullyFlat) :
    B.Contains (Spec (CommRingCat.of (affineTensorAlgebra g hg F))) := by
  have hff := RingHom.faithfullyFlat_algebraMap_iff.1 hfl
  let := (affineTensorRingHom g hg F).toAlgebra
  have := isAffine_toScheme_affineRightAdjoint_obj g hg hU
  let e := selfTensorEquivBaseChange g hg F hU
  let z := (affineRightAdjoint g hg).obj (g.hom.hom.toFunctor.obj (siteTop.{u, w} U))
  let R'm := (quasicoherentGlobalSections.{u, w} U).obj
    (quasicoherentPullbackObj B S hS g (affineQuasicoherentStructureSheaf g hg))
  let R'r := (fppfStructurePresheaf B S hS (schemeStack.{u, w} B S hS U)).obj (op z)
  let ι : R'r → R'm := fun r => r
  let ι' : R'm → R'r := fun r => r
  exact @BigFppfSite.contains_spec_of_span_tensorProduct B R (affineTensorAlgebra g hg F) R'r
    _ _ _ _ hff hR (contains_spec_fppfStructurePresheaf_obj z)
    (fun r => e.symm ((1 : affineTensorAlgebra g hg F) ⊗ₜ[schemeGlobalRing U] ι r))
    (span_range_symm_one_tmul e ι fun r => ⟨ι' r, rfl⟩)

omit [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F] in
/-- **The point `x_C`** (Stacks 0GRQ, proof): a point `y` of `𝒳` over `Spec C`, with an arrow
`y ⟶ g(U)` lying over `Spec C ⟶ Spec A`, the pullback of the chart point. -/
theorem exists_point_over_affineTensorAlgebra
    (hC : B.Contains (Spec (CommRingCat.of (affineTensorAlgebra g hg F)))) :
    ∃ (qC : B.obj hC ⟶ B.obj hS) (y : 𝒳.val.val.obj) (hy : 𝒳.val.val.p.obj y = Over.mk qC)
      (ψ : y ⟶ g.hom.hom.toFunctor.obj (siteTop.{u, w} U)),
      (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ψ) ≫ (chartPointIso g hU).hom =
        (overSpecIso B S hS 𝒳 hy).hom ≫
          Spec.map (CommRingCat.ofHom (affineTensorRingHom g hg F)) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let X := 𝒳.val.val.p.obj (g.hom.hom.toFunctor.obj (siteTop.{u, w} U))
  let f : B.obj hC ⟶ X.left := B.inclusion.preimage
    (Spec.map (CommRingCat.ofHom (affineTensorRingHom g hg F)) ≫ (chartPointIso g hU).inv)
  let k : Over.mk (f ≫ X.hom) ⟶ X := Over.homMk f rfl
  let x₀ : 𝒳.val.val.p.Fiber X := ⟨g.hom.hom.toFunctor.obj (siteTop.{u, w} U), rfl⟩
  let y := Functor.pullbackFiber 𝒳.val.val.p x₀ k
  let ψ : y.1 ⟶ x₀.1 := Functor.IsPreFibered.pullbackMap x₀.2 k
  have : 𝒳.val.val.p.IsHomLift k ψ :=
    (Functor.IsPreFibered.pullbackMap.IsCartesian x₀.2 k).toIsHomLift
  refine ⟨f ≫ X.hom, y.1, y.2, ψ, ?_⟩
  have h :=
    map_map_comp_eqToHom_of_isHomLift 𝒳.val.val.p (BigFppfOver.toScheme B S hS) k ψ y.2 x₀.2
  have hk : (BigFppfOver.toScheme B S hS).map k =
      Spec.map (CommRingCat.ofHom (affineTensorRingHom g hg F)) ≫ (chartPointIso g hU).inv :=
    B.inclusion.map_preimage _
  rw [eqToHom_refl, Category.comp_id, hk] at h
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end Theta

section Chart

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **An affine, smooth and surjective chart** `g : U ⟶ 𝒳` from an affine scheme, for a
quasi-compact algebraic stack with affine (absolute) diagonal: Stacks 04YC gives `g` smooth and
surjective, and `g` is affine because the diagonal is. -/
theorem exists_affine_smooth_surjective_chart
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val)) :
    ∃ (U : BigFppfOver B S hS) (_ : IsAffineOver B S hS U)
      (g : schemeStack.{u, w} B S hS U ⟶ 𝒳),
      IsAffineHom B S hS g ∧ IsSmooth B S hS g ∧ IsSurjective B S hS g := by
  obtain ⟨U, hU, g, hsurj, hfrep, hrel⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 hqc
  have hsm : IsSmooth B S hS g :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) 𝒳.property g.hom hfrep hrel
  exact ⟨U, hU, g, isAffineHom_of_isAffineHom_diagonal_viewOverIntegers B S hS
    (contains_terminalScheme B) hU hΔ g, hsm, hsurj⟩

end Chart

section Uniqueness

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (CommRingCat.of R))}

/-- **Uniqueness in Stacks 0GRQ.** Let `𝒳` be a quasi-compact algebraic stack with affine
(absolute) diagonal and `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a tensor functor. If `F ≅ x₁^*` and `F ≅ x₂^*` as
tensor functors for points `x₁, x₂` over `Spec R` (with structure morphisms `q₁, q₂` to `S`), then
`q₁ = q₂` and there is a unique 2-arrow `a : x₁ ≅ x₂` over the identity of `Spec R` inducing the
isomorphism `x₁^* ≅ F ≅ x₂^*` (Stacks 0GRP and the rigidity of points along a smooth chart). -/
theorem eq_and_existsUnique_iso_of_iso_pointPullback
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Monoidal]
    {q₁ q₂ : B.obj hR ⟶ B.obj hS} {x₁ x₂ : 𝒳.val.val.obj}
    (hx₁ : 𝒳.val.val.p.obj x₁ = Over.mk q₁) (hx₂ : 𝒳.val.val.p.obj x₂ = Over.mk q₂)
    (e₁ : F ≅ pointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁))
    (e₂ : F ≅ pointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂))
    (he₁ : NatTrans.IsMonoidal e₁.hom) (he₂ : NatTrans.IsMonoidal e₂.hom) :
    q₁ = q₂ ∧ ∃ (a : x₁ ≅ x₂) (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫
        (overSpecIso B S hS 𝒳 hx₂).hom = (overSpecIso B S hS 𝒳 hx₁).hom),
      pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁) (overSpecIso B S hS 𝒳 hx₂)
          a ha = e₁.symm ≪≫ e₂ ∧
        ∀ (b : x₁ ≅ x₂) (hb : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map b.hom) ≫
            (overSpecIso B S hS 𝒳 hx₂).hom = (overSpecIso B S hS 𝒳 hx₁).hom),
          pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁)
            (overSpecIso B S hS 𝒳 hx₂) b hb = e₁.symm ≪≫ e₂ → b = a := by
  have : NatTrans.IsMonoidal (e₁.symm ≪≫ e₂).hom :=
    inferInstanceAs (NatTrans.IsMonoidal (e₁.inv ≫ e₂.hom))
  obtain ⟨hq, a, ha, hat⟩ := eq_and_exists_iso_pointPullbackTransportIso_eq B S hS hΔ hx₁ hx₂
    (e₁.symm ≪≫ e₂)
  refine ⟨hq, a, ha, hat, fun b hb hbt => ?_⟩
  obtain ⟨U, -, g, hg, hsm, hsurj⟩ := exists_affine_smooth_surjective_chart hqc hΔ
  exact eq_of_pointPullbackTransportIso_eq_of_isSmooth B S hS U g hg hsm hsurj _ _ b a hb ha
    (hbt.trans hat.symm)

end Uniqueness

end AlgebraicGeometry.Stack.AlgebraicStacks

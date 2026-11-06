module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.ReesPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.MorphismSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.SectionRingBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.SituationBaseChange

/-!
# The degreewise base change of a relative `Proj` situation along a morphism of base schemes

`Stacks.RelativeProj.Situation.gradedBaseChange` is the homomorphism of graded section rings
`𝒜(W) ⟶ 𝒜'(W')` attached to a morphism `g : S' ⟶ S` of base schemes, an identification of the
graded algebra of `s'` with the pullback of that of `s`, and a pair of affine opens
`W' ≤ g⁻¹W`. When the homogeneous pieces are quasi-coherent and the identification is an
isomorphism in each degree, it is a degreewise base change,
`𝒜'ₙ(W') = Γ(S', W') ⊗_{Γ(S, W)} 𝒜ₙ(W)`, and the irrelevant ideal of `𝒜'(W')` is covered by
that of `𝒜(W)`. No hypothesis is placed on `g`.

## Main definitions

* `Stacks.RelativeProj.Situation.pieceLinearEquiv`: the degreewise identification of the two
  algebras, read on sections over an open as a linear equivalence.

## Main results

* `Stacks.RelativeProj.Situation.pullbackSection_smul_appLE`: pulling a section back is
  semilinear over `AlgebraicGeometry.Scheme.Hom.appLE`.
* `Stacks.RelativeProj.Situation.pieceSectionHom_smul`: the same for the degreewise components.
* `Stacks.RelativeProj.Situation.isBaseChange_pieceSectionHom`: **the degreewise base change.**
  Extending the scalars of `𝒜ₙ(W)` along `g.appLE W W'` gives `𝒜'ₙ(W')`.
* `Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange`: **the irrelevant ideal of
  `𝒜'(W')` is covered by that of `𝒜(W)`.**

## Implementation notes

The `Γ(S, W)`-algebra structure on `Γ(S', W')` and the `Γ(S, W)`-module structure on
`𝒜'ₙ(W')` are restriction of scalars along `g.appLE W W' h`, which depends on the inclusion
`W' ≤ g⁻¹W`; that inclusion is not part of the type of an `Algebra` or `Module`, so these cannot
be instances and are instance-implicit hypotheses of
`Stacks.RelativeProj.Situation.isBaseChange_pieceSectionHom`, together with the equation pinning
them down. The statement of `irrelevant_le_gradedBaseChange` mentions none of them.

The homogeneous pieces are named through `Stacks.RelativeProj.Situation.pieceNat`, not as
`s.algebra.piece (n : ℤ)`. The two are the same by `rfl`, but only the first has type
`AlgebraicGeometry.Scheme.Modules`, which is what makes the `Γ(S, W)`-module structure on its
sections and its quasi-coherence available to instance search; with the second spelling the
`Module` instance is not found.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum
open HomogeneousIdeal

universe u

namespace Stacks.RelativeProj.Situation

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **Pulling a section back is semilinear over `appLE`.** -/
public theorem pullbackSection_smul_appLE (M : X.Modules) (W : X.Opens) (W' : Y.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (r : Γ(X, W)) (a : M.val.obj (op W)) :
    Scheme.Modules.pullbackSection g M W W' h
        ((show X.ringCatSheaf.obj.obj (op W) from r) • a) =
      (show Y.ringCatSheaf.obj.obj (op W') from (g.appLE W W' h).hom r) •
        Scheme.Modules.pullbackSection g M W W' h a := by
  rw [← Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink g M W (g ⁻¹ᵁ W) W'
      le_rfl h h,
    ← Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink g M W (g ⁻¹ᵁ W) W'
      le_rfl h h,
    Stacks.Conormal.pullbackSection_smul g M W r a]
  exact Scheme.Modules.map_smul ((Scheme.Modules.pullback g).obj M) (homOfLE h) _ _

/-! ### The degreewise base change -/

section

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)

/-- The degreewise identification of the algebras, read on sections over an open as a linear
equivalence. -/
public noncomputable def pieceLinearEquiv (n : ℕ) (W' : s'.base.Opens)
    (hΦ : IsIso (Φ.app (n : ℤ))) :
    ↥Γ((Scheme.Modules.pullback g).obj (s.pieceNat n), W')
      ≃ₗ[↥Γ(s'.base, W')] ↥Γ(s'.pieceNat n, W') :=
  LinearEquiv.ofLinearMap ((Φ.app (n : ℤ)).val.app (op W')).hom
    ((inv (Φ.app (n : ℤ))).val.app (op W')).hom
    (LinearMap.ext fun y =>
      congrArg (fun k : s'.algebra.piece (n : ℤ) ⟶ s'.algebra.piece (n : ℤ) =>
        k.val.app (op W') y) (IsIso.inv_hom_id (Φ.app (n : ℤ))))
    (LinearMap.ext fun x =>
      congrArg (fun k : (Stacks.Conormal.gradedPullback g s.algebra).piece (n : ℤ) ⟶
          (Stacks.Conormal.gradedPullback g s.algebra).piece (n : ℤ) =>
        k.val.app (op W') x) (IsIso.hom_inv_id (Φ.app (n : ℤ))))

/-- `Stacks.RelativeProj.Situation.pieceLinearEquiv` applied to a section is the component of the
identification of the algebras at that section. -/
@[simp] public theorem pieceLinearEquiv_apply (n : ℕ) (W' : s'.base.Opens)
    (hΦ : IsIso (Φ.app (n : ℤ)))
    (x : ↥Γ((Scheme.Modules.pullback g).obj (s.pieceNat n), W')) :
    pieceLinearEquiv g Φ n W' hΦ x = (Φ.app (n : ℤ)).val.app (op W') x := rfl

/-- **The degreewise base change.** For affine opens `W ⊆ S` and `W' ⊆ g⁻¹W ⊆ S'`, extending the
scalars of `𝒜ₙ(W)` along `g.appLE W W'` gives `𝒜'ₙ(W')`. -/
public theorem isBaseChange_pieceSectionHom (n : ℕ) {W : s.base.Opens} {W' : s'.base.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    (hΦ : IsIso (Φ.app (n : ℤ)))
    [inst : Algebra ↥Γ(s.base, W) ↥Γ(s'.base, W')]
    (halg : ∀ r : ↥Γ(s.base, W),
      algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W') r = (g.appLE W W' h).hom r)
    [Module ↥Γ(s.base, W) ↥Γ(s'.pieceNat n, W')]
    [IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥Γ(s'.pieceNat n, W')]
    (rho : ↥Γ(s.pieceNat n, W) →ₗ[↥Γ(s.base, W)] ↥Γ(s'.pieceNat n, W'))
    (hrho : ∀ a, rho a = pieceSectionHom g Φ n W W' h a) :
    IsBaseChange ↥Γ(s'.base, W') rho := by
  let mP : Module ↥Γ(s.base, W)
      ↥Γ((Scheme.Modules.pullback g).obj (s.pieceNat n), W') :=
    Module.compHom _ (algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W'))
  let tP : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W')
      ↥Γ((Scheme.Modules.pullback g).obj (s.pieceNat n), W') :=
    ⟨fun x y z => by
      rw [Algebra.smul_def x y]
      exact mul_smul (algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W') x) y z⟩
  have hrho0 : ∀ a, (pieceLinearEquiv g Φ n W' hΦ).symm (rho a) =
      Scheme.Modules.pullbackSection g (s.pieceNat n) W W' h a := fun a =>
    (congrArg _ (hrho a)).trans ((pieceLinearEquiv g Φ n W' hΦ).symm_apply_apply _)
  exact IsBaseChange.of_linearEquiv
    (isBaseChange_pullbackSection_of_isAffineOpen g (s.pieceNat n) hW hW' h halg
      (((pieceLinearEquiv g Φ n W' hΦ).symm.restrictScalars ↥Γ(s.base, W)).toLinearMap.comp rho)
      hrho0)
    (LinearEquiv.refl _ _) (pieceLinearEquiv g Φ n W' hΦ).symm rho
    (fun _ => rfl)

/-- The degreewise components are semilinear over `appLE`. -/
public theorem pieceSectionHom_smul (n : ℕ) (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (r : Γ(s.base, W)) (a : s.sectionPieces W n) :
    pieceSectionHom g Φ n W W' h
        ((show s.base.ringCatSheaf.obj.obj (op W) from r) • a) =
      (show s'.base.ringCatSheaf.obj.obj (op W') from (g.appLE W W' h).hom r) •
        pieceSectionHom g Φ n W W' h a := by
  rw [pieceSectionHom_apply, pieceSectionHom_apply,
    pullbackSection_smul_appLE g (s.algebra.piece (n : ℤ)) W W' h r a]
  exact ((Φ.app (n : ℤ)).val.app (op W')).hom.map_smul _ _

/-- **The irrelevant ideal of `𝒜'(W')` is covered by that of `𝒜(W)`.** For affine opens `W` of
`S` and `W' ≤ g⁻¹W` of `S'`, the irrelevant ideal of `𝒜'(W')` is contained in the ideal generated
by the image of the irrelevant ideal of `𝒜(W)` under
`Stacks.RelativeProj.Situation.gradedBaseChange`. -/
public theorem irrelevant_le_gradedBaseChange (W : s.base.affineOpens) (W' : s'.base.affineOpens)
    (h : W'.1 ≤ g ⁻¹ᵁ W.1) (hΦ : ∀ n : ℕ, IsIso (Φ.app (n : ℤ))) :
    (s'.chartGrading W')₊ ≤ ((s.chartGrading W)₊).map (gradedBaseChange g Φ W.1 W'.1 h) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  obtain ⟨a, rfl⟩ : ∃ a, DirectSum.of (s'.sectionPieces W'.1) i a = x := hx
  let aUV : Algebra ↥Γ(s.base, W.1) ↥Γ(s'.base, W'.1) := (g.appLE W.1 W'.1 h).hom.toAlgebra
  let mUV : Module ↥Γ(s.base, W.1) ↥Γ(s'.pieceNat i, W'.1) :=
    Module.compHom _ (g.appLE W.1 W'.1 h).hom
  let tUV : IsScalarTower ↥Γ(s.base, W.1) ↥Γ(s'.base, W'.1) ↥Γ(s'.pieceNat i, W'.1) :=
    ⟨fun x y z => mul_smul ((g.appLE W.1 W'.1 h).hom x) y z⟩
  let rho : ↥Γ(s.pieceNat i, W.1) →ₗ[↥Γ(s.base, W.1)] ↥Γ(s'.pieceNat i, W'.1) :=
    { toFun := fun b => pieceSectionHom g Φ i W.1 W'.1 h b
      map_add' := fun b c => map_add _ _ _
      map_smul' := fun r b => pieceSectionHom_smul g Φ i W.1 W'.1 h r b }
  have hbc : IsBaseChange ↥Γ(s'.base, W'.1) rho :=
    isBaseChange_pieceSectionHom g Φ i (isAffineOpen W) (isAffineOpen W') h (hΦ i)
      (fun _ => rfl) rho (fun _ => rfl)
  refine hbc.inductionOn a (motive := fun b => DirectSum.of (s'.sectionPieces W'.1) i b ∈
      (((s.chartGrading W)₊).map (gradedBaseChange g Φ W.1 W'.1 h)).toAddSubmonoid) ?_ ?_ ?_
  · intro b
    have hm : gradedBaseChange g Φ W.1 W'.1 h (DirectSum.of (s.sectionPieces W.1) i b)
        = DirectSum.of (s'.sectionPieces W'.1) i (pieceSectionHom g Φ i W.1 W'.1 h b) :=
      sectionRingBaseChange_of g Φ W.1 W'.1 h i b
    show DirectSum.of (s'.sectionPieces W'.1) i (pieceSectionHom g Φ i W.1 W'.1 h b) ∈ _
    rw [← hm]
    exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hi ⟨b, rfl⟩)
  · intro r b ih
    rw [s'.of_smul W'.1 i r b]
    exact Ideal.mul_mem_right _ _ ih
  · intro b c hb hc
    exact map_add (DirectSum.of (s'.sectionPieces W'.1) i) b c ▸ add_mem hb hc

end

end Stacks.RelativeProj.Situation

end

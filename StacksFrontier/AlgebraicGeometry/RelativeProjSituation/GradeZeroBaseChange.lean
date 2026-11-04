module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.DegreewiseBaseChange

/-!
# The degree-zero square of a relative `Proj` base change along a morphism of base schemes

A relative `Proj` chart `Proj 𝒜(W)` lies over `Spec` of the degree-zero part `𝒜₀(W)` of its
graded ring of sections. Let `g : S' ⟶ S` be a morphism of base schemes, `W' ≤ g⁻¹W` affine opens,
and `Φ : g^*𝒜 ⟶ 𝒜'` a unital map of graded algebras which is an isomorphism in degree zero. Then
`𝒜'₀(W') = Γ(S', W') ⊗_{Γ(S, W)} 𝒜₀(W)`, and the square of spectra of degree-zero parts over
`Spec Γ(S', W') ⟶ Spec Γ(S, W)` is cartesian. For an inclusion of affine opens of one base this
is `Stacks.RelativeProj.Situation.isPullback_specMap_baseHom`.

## Main results

* `Stacks.RelativeProj.Situation.gradedZeroRingHom_gradeZeroLinearEquiv_baseChange`: in degree
  zero, the base change of graded rings of sections is the base change of sections of `𝒜₀`.
* `Stacks.RelativeProj.Situation.sectionRingBaseChange_baseMap`: the base change of graded rings
  of sections commutes with the structure maps from the base.
* `Stacks.RelativeProj.Situation.baseHom_gradedBaseChange`: the square of rings formed by
  `Γ(S, W) → Γ(S', W')`, `𝒜₀(W) → 𝒜'₀(W')` and the two structure maps commutes.
* `Stacks.RelativeProj.Situation.isPushout_gradeZero_baseChange`:
  `𝒜'₀(W') = Γ(S', W') ⊗_{Γ(S, W)} 𝒜₀(W)` as a pushout of commutative rings.
* `Stacks.RelativeProj.Situation.isPullback_specMap_baseHom_baseChange`: `Spec 𝒜'₀(W')` is the
  base change of `Spec 𝒜₀(W)` along `Spec Γ(S', W') ⟶ Spec Γ(S, W)`.

## Implementation notes

The conclusion of the `Spec` square names only ring maps, so the `Algebra` and `IsScalarTower`
structures relating the degree-zero rings are built by `RingHom.toAlgebra` inside its proof. The
conclusion of the pushout is a statement about those structures, so there they are
instance-implicit hypotheses, pinned down by equations.

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

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)

/-- In degree zero, the base change of graded rings of sections corresponds, under
`Stacks.RelativeProj.Situation.gradeZeroLinearEquiv`, to the base change `pieceSectionHom` of
sections of the degree-zero piece. -/
public theorem gradedZeroRingHom_gradeZeroLinearEquiv_baseChange (W : s.base.Opens)
    (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W) (b : ↥Γ(s.pieceNat 0, W)) :
    (gradedBaseChange g Φ W W' h).gradedZeroRingHom (s.gradeZeroLinearEquiv W b)
      = s'.gradeZeroLinearEquiv W' (pieceSectionHom g Φ 0 W W' h b) := by
  refine Subtype.ext ?_
  show gradedBaseChange g Φ W W' h
      ((s.gradeZeroLinearEquiv W b : ↥(s.sectionRingGrading W 0)) : s.sectionRing W) = _
  rw [coe_gradeZeroLinearEquiv, gradedBaseChange_apply]
  exact (sectionRingBaseChange_of g Φ W W' h 0 b).trans
    (coe_gradeZeroLinearEquiv s' W' (pieceSectionHom g Φ 0 W W' h b)).symm

/-- The base change of graded rings of sections carries the structure map from `Γ(S, W)` to the
structure map from `Γ(S', W')`, composed with `g.appLE W W' h`. -/
public theorem sectionRingBaseChange_baseMap (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (r : Γ(s.base, W)) :
    sectionRingBaseChange g Φ W W' h (s.sectionRingBaseMap W r)
      = s'.sectionRingBaseMap W' ((g.appLE W W' h).hom r) :=
  calc sectionRingBaseChange g Φ W W' h (s.sectionRingBaseMap W r)
      = sectionRingBaseChange g Φ W W' h
          (DirectSum.of (s.sectionPieces W) 0 (r • s.onePiece W)) :=
        congrArg _ ((sectionRingStructure s).baseMap_apply W r)
    _ = DirectSum.of (s'.sectionPieces W') 0
          (pieceSectionHom g Φ 0 W W' h (r • s.onePiece W)) :=
        sectionRingBaseChange_of g Φ W W' h 0 _
    _ = DirectSum.of (s'.sectionPieces W') 0
          ((g.appLE W W' h).hom r • s'.onePiece W') :=
        congrArg (DirectSum.of (s'.sectionPieces W') 0)
          ((pieceSectionHom_smul g Φ 0 W W' h r (s.onePiece W)).trans
            (congrArg (fun z : s'.sectionPieces W' 0 =>
              (show s'.base.ringCatSheaf.obj.obj (op W') from (g.appLE W W' h).hom r) • z)
              (pieceSectionHom_one g Φ W W' h)))
    _ = s'.sectionRingBaseMap W' ((g.appLE W W' h).hom r) :=
        ((sectionRingStructure s').baseMap_apply W' _).symm

/-- **The structure maps to the degree-zero parts commute with the base change**:
`g.appLE W W' h ≫ s'.baseHom W'` equals `s.baseHom W` followed by the degree-zero part of
`gradedBaseChange g Φ W W' h`. -/
public theorem baseHom_gradedBaseChange (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) :
    g.appLE W W' h ≫ s'.baseHom W' =
      s.baseHom W ≫
        CommRingCat.ofHom (gradedBaseChange g Φ W W' h).gradedZeroRingHom := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ Subtype.ext ?_)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, baseHom_apply_coe,
    CommRingCat.ofHom_apply]
  show _ = gradedBaseChange g Φ W W' h ((s.baseHom W) r : s.sectionRing W)
  rw [gradedBaseChange_apply, baseHom_apply_coe]
  exact (sectionRingBaseChange_baseMap g Φ W W' h r).symm

/-- The degree-zero pushout, for any compatible algebra structures. -/
private theorem isPushout_gradeZero_baseChange_aux (W : s.base.Opens) (W' : s'.base.Opens)
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    (hΦ0 : IsIso (Φ.app 0))
    [Algebra ↥Γ(s.base, W) ↥Γ(s'.base, W')]
    (halg : ∀ r : ↥Γ(s.base, W),
      algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W') r = (g.appLE W W' h).hom r)
    [Algebra ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0)]
    (halgAB : ∀ a : ↥(s.sectionRingGrading W 0),
      algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) a
        = (gradedBaseChange g Φ W W' h).gradedZeroRingHom a)
    [Algebra ↥Γ(s.base, W) ↥(s'.sectionRingGrading W' 0)]
    [IsScalarTower ↥Γ(s.base, W) ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0)]
    [IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥(s'.sectionRingGrading W' 0)] :
    Algebra.IsPushout ↥Γ(s.base, W) ↥Γ(s'.base, W')
      ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) := by
  let mUV : Module ↥Γ(s.base, W) ↥Γ(s'.pieceNat 0, W') :=
    Module.compHom _ (g.appLE W W' h).hom
  let tUV : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥Γ(s'.pieceNat 0, W') :=
    ⟨fun x y z => by
      rw [Algebra.smul_def x y, halg x]
      exact mul_smul ((g.appLE W W' h).hom x) y z⟩
  let mP : Module ↥Γ(s.base, W) ↥Γ((Scheme.Modules.pullback g).obj (s.pieceNat 0), W') :=
    Module.compHom _ (g.appLE W W' h).hom
  let tP : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W')
      ↥Γ((Scheme.Modules.pullback g).obj (s.pieceNat 0), W') :=
    ⟨fun x y z => by
      rw [Algebra.smul_def x y, halg x]
      exact mul_smul ((g.appLE W W' h).hom x) y z⟩
  let rho0 : ↥Γ(s.pieceNat 0, W) →ₗ[↥Γ(s.base, W)] ↥Γ(s'.pieceNat 0, W') :=
    { toFun := fun a => pieceSectionHom g Φ 0 W W' h a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => pieceSectionHom_smul g Φ 0 W W' h r a }
  exact isPushout_pullbackSections_of_isAffineOpen g (s.pieceNat 0) hW hW' h halg
    (((pieceLinearEquiv g Φ 0 W' hΦ0).symm.restrictScalars ↥Γ(s.base, W)).toLinearMap.comp rho0)
    (fun a => (pieceLinearEquiv g Φ 0 W' hΦ0).symm_apply_apply _)
    (s.gradeZeroLinearEquiv W).symm
    ((s'.gradeZeroLinearEquiv W').symm ≪≫ₗ (pieceLinearEquiv g Φ 0 W' hΦ0).symm)
    (fun a => by
      obtain ⟨b, rfl⟩ := (s.gradeZeroLinearEquiv W).surjective a
      rw [halgAB, gradedZeroRingHom_gradeZeroLinearEquiv_baseChange, LinearEquiv.trans_apply,
        LinearEquiv.symm_apply_apply]
      exact (congrArg _ ((s'.gradeZeroLinearEquiv W').symm_apply_apply _)).trans
        ((pieceLinearEquiv g Φ 0 W' hΦ0).symm_apply_apply _))


/-- **The degree-zero square of a relative-`Proj` base change.** For affine opens `W' ≤ g⁻¹W` and
`Φ` an isomorphism in degree zero, `Spec 𝒜'₀(W')` is the pullback of `Spec 𝒜₀(W)` along
`Spec Γ(S', W') ⟶ Spec Γ(S, W)`. -/
public theorem isPullback_specMap_baseHom_baseChange (W : s.base.Opens) (W' : s'.base.Opens)
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    (hΦ0 : IsIso (Φ.app 0)) :
    IsPullback (Spec.map (s'.baseHom W'))
      (Spec.map (CommRingCat.ofHom (gradedBaseChange g Φ W W' h).gradedZeroRingHom))
      (Spec.map (g.appLE W W' h)) (Spec.map (s.baseHom W)) := by
  let aUV : Algebra ↥Γ(s.base, W) ↥Γ(s'.base, W') := (g.appLE W W' h).hom.toAlgebra
  have halg : ∀ r : ↥Γ(s.base, W),
      algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W') r = (g.appLE W W' h).hom r := fun _ => rfl
  let aAB : Algebra ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) :=
    ((gradedBaseChange g Φ W W' h).gradedZeroRingHom).toAlgebra
  let aUB : Algebra ↥Γ(s.base, W) ↥(s'.sectionRingGrading W' 0) :=
    (((gradedBaseChange g Φ W W' h).gradedZeroRingHom).comp (s.baseHom W).hom).toAlgebra
  let tAB : IsScalarTower ↥Γ(s.base, W) ↥(s.sectionRingGrading W 0)
      ↥(s'.sectionRingGrading W' 0) := IsScalarTower.of_algebraMap_eq' rfl
  let tB : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥(s'.sectionRingGrading W' 0) :=
    IsScalarTower.of_algebraMap_eq'
      (CommRingCat.hom_ext_iff.1 (baseHom_gradedBaseChange g Φ W W' h)).symm
  have := isPushout_gradeZero_baseChange_aux g Φ W W' hW hW' h hΦ0 halg (fun _ => rfl)
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout _ _ _ _)

/-- **The degree-zero pushout of a relative-`Proj` base change.** For affine opens `W' ≤ g⁻¹W` and
`Φ` an isomorphism in degree zero, `𝒜'₀(W') = Γ(S', W') ⊗_{Γ(S, W)} 𝒜₀(W)`. -/
public theorem isPushout_gradeZero_baseChange (W : s.base.Opens) (W' : s'.base.Opens)
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    (hΦ0 : IsIso (Φ.app 0))
    [Algebra ↥Γ(s.base, W) ↥Γ(s'.base, W')]
    (halg : ∀ r : ↥Γ(s.base, W),
      algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W') r = (g.appLE W W' h).hom r)
    [Algebra ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0)]
    (halgAB : ∀ a : ↥(s.sectionRingGrading W 0),
      algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) a
        = (gradedBaseChange g Φ W W' h).gradedZeroRingHom a)
    [Algebra ↥Γ(s.base, W) ↥(s'.sectionRingGrading W' 0)]
    [IsScalarTower ↥Γ(s.base, W) ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0)]
    [IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥(s'.sectionRingGrading W' 0)] :
    Algebra.IsPushout ↥Γ(s.base, W) ↥Γ(s'.base, W')
      ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) :=
  isPushout_gradeZero_baseChange_aux g Φ W W' hW hW' h hΦ0 halg halgAB

end Stacks.RelativeProj.Situation

end

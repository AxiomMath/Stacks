module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjRepresentsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesAlgebraicSpace

/-!
# Compatibility of `Proj_Z(g^*𝒜) = Z ×_X F` with further base change

In Situation 0849 let `F` be the functor of quadruples of Stacks 084A.  The second assertion of
Stacks 084B identifies `Proj_Z(g^*𝒜)` with `Z ×_X F` for every scheme point `g : Z ⟶ X`, and the
third says that this identification is compatible with further base change: for `h : Z' ⟶ Z`, the
identification over `Z'` is the base change along `h` of the identification over `Z`, through the
canonical isomorphism `Proj_{Z'}(h^*(g^*𝒜)) ≅ Z' ×_Z Proj_Z(g^*𝒜)` of Tag 01O3 and the
identification `(g ∘ h)^*𝒜 ≅ h^*(g^*𝒜)` of the restricted algebras.

`AlgebraicGeometry.Space.GradedAlgebraRestriction.isPullback_projComparison` exhibits
`Proj_{Z'}((g ∘ h)^*𝒜)` as `Z' ×_Z Proj_Z(g^*𝒜)` through the comparison morphism
`AlgebraicGeometry.Space.GradedAlgebraRestriction.projComparison` the two cartesian squares of the
second assertion induce.  This file identifies that comparison morphism with the canonical one:
it is the isomorphism `Proj_{Z'}((g ∘ h)^*𝒜) ≅ Proj_{Z'}(h^*(g^*𝒜))` induced by the restriction
datum, followed by the base-change morphism `Proj_{Z'}(h^*(g^*𝒜)) ⟶ Proj_Z(g^*𝒜)` of Tag 01O3
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.toScheme_map_projComparison`).

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.fibreToF_comp`: the comparison of a fibre of
  `F` with the scheme-level functor of quadruples over a composite.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.toScheme_map_projComparison`: the
  comparison morphism of the third assertion is the canonical one of Tag 01O3.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.isPullback_baseChangeHom_restrictProjIso`:
  the third assertion of Stacks 084B with the canonical morphisms.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The comparison over a composite -/

section Comp

variable {r : GradedAlgebraPoints B S hS X} (ρ : GradedAlgebraRestriction r)

/-- **The comparison of a fibre of `F` with the scheme-level functor of quadruples, over a
composite.** For `h : Z' ⟶ Z`, a scheme point `g` of `X` on `Z` and `τ : W ⟶ Z'`, comparing a
point of the fibre of `F(W)` over `(τ ≫ h)^*g` with the functor of quadruples of `g^*𝒜` over
`τ ≫ h` is comparing it with the functor of quadruples of `(h^*g)^*𝒜` over `τ`, transporting along
the comparison `(h^*g)^*𝒜 ≅ h^*(g^*𝒜)` of the restriction datum, and base changing along `h`. -/
theorem fibreToF_comp {Z Z' W : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (h : Z' ⟶ Z)
    (τ : W ⟶ Z') (f : yoneda.obj W ⟶ X) (hf : yoneda.map (τ ≫ h) ≫ g = f)
    (hf' : yoneda.map τ ≫ yoneda.map h ≫ g = f)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj W)) (A := r.algebra W f))) :
    ρ.fibreToF g (τ ≫ h) f hf q =
      F.baseChangeUp ((BigFppfOver.toScheme B S hS).map h) (r.algebra Z g)
        (F.algebraTransport (unitalHomInverse (ρ.restrict h g (yoneda.map h ≫ g) rfl)
            (ρ.isIso_restrict_app h g _ rfl))
          (isIso_unitalHomInverse_app (ρ.restrict h g (yoneda.map h ≫ g) rfl)
            (ρ.isIso_restrict_app h g _ rfl))
          (ρ.fibreToF (yoneda.map h ≫ g) τ f hf' q)) := by
  set φ := BigFppfOver.toScheme B S hS
  set Ψ := (baseAlgebraMapHom (φ.map τ) (ρ.restrict h g (yoneda.map h ≫ g) rfl)).comp
    (baseAlgebraCompHomOf (r.algebra Z g) (φ.map τ) (φ.map h) (φ.map (τ ≫ h))
      (φ.map_comp τ h).symm) with hΨ
  have hΨiso : ∀ n : ℤ, IsIso (Ψ.app n) := fun n => inferInstance
  set x : F (r.algebra W f) (φ.obj W) := ⟨𝟙 _, q⟩ with hx
  set v := (F.algebraTransportEquiv (ρ.restrict (τ ≫ h) g f hf)
    (ρ.isIso_restrict_app _ g f hf) _).symm x with hv
  have hxv : F.algebraTransport (ρ.restrict τ (yoneda.map h ≫ g) f hf')
      (ρ.isIso_restrict_app _ _ f hf') (F.algebraTransport Ψ hΨiso v) = x := by
    rw [F.algebraTransport_algebraTransport _ _ _ _ (fun n => inferInstance)]
    have hc := ρ.restrict_comp h τ g (yoneda.map h ≫ g) f rfl hf' hf
    refine Eq.trans ?_ ((F.algebraTransportEquiv (ρ.restrict (τ ≫ h) g f hf)
      (ρ.isIso_restrict_app _ g f hf) _).apply_symm_apply x)
    show F.algebraTransport _ _ v = F.algebraTransport _ _ v
    congr 1
    exact hc.symm
  have hR : ρ.fibreToF (yoneda.map h ≫ g) τ f hf' q =
      F.algebraTransport (ρ.restrict h g (yoneda.map h ≫ g) rfl)
        (ρ.isIso_restrict_app h g _ rfl)
        (F.baseChangeUp (φ.map τ) (baseAlgebra (φ.map h) (r.algebra Z g))
          (F.algebraTransport (baseAlgebraCompHomOf (r.algebra Z g) (φ.map τ) (φ.map h)
            (φ.map (τ ≫ h)) (φ.map_comp τ h).symm) (fun n => inferInstance) v)) := by
    have e1 : (F.algebraTransportEquiv (ρ.restrict τ (yoneda.map h ≫ g) f hf')
        (ρ.isIso_restrict_app _ _ f hf') _).symm x = F.algebraTransport Ψ hΨiso v := by
      rw [← hxv]
      exact (F.algebraTransportEquiv _ _ _).symm_apply_apply _
    exact (congrArg (F.baseChangeUp (φ.map τ) (r.algebra Z' (yoneda.map h ≫ g))) e1).trans
      ((congrArg (F.baseChangeUp (φ.map τ) (r.algebra Z' (yoneda.map h ≫ g)))
        (F.algebraTransport_algebraTransport _ _ (fun n => inferInstance)
          (fun n => inferInstance) hΨiso v).symm).trans
        (F.baseChangeUp_algebraTransport (φ.map τ) (ρ.restrict h g (yoneda.map h ≫ g) rfl)
          (ρ.isIso_restrict_app h g _ rfl) _))
  rw [hR]
  have e2 := (F.algebraTransportEquiv (ρ.restrict h g (yoneda.map h ≫ g) rfl)
    (ρ.isIso_restrict_app h g _ rfl) _).symm_apply_apply
    (F.baseChangeUp (φ.map τ) (baseAlgebra (φ.map h) (r.algebra Z g))
      (F.algebraTransport (baseAlgebraCompHomOf (r.algebra Z g) (φ.map τ) (φ.map h)
        (φ.map (τ ≫ h)) (φ.map_comp τ h).symm) (fun n => inferInstance) v))
  refine Eq.trans ?_ (congrArg (F.baseChangeUp (φ.map h) (r.algebra Z g)) e2).symm
  exact (F.baseChangeUp_baseChangeUp (φ.map τ) (φ.map h) (φ.map (τ ≫ h))
    (φ.map_comp τ h).symm v).symm

end Comp

/-! ### The comparison morphism of the third assertion is the canonical one -/

variable {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    (ρ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)

/-- **The identification `Proj_{Z'}((g ∘ h)^*𝒜) ≅ Proj_{Z'}(h^*(g^*𝒜))`** of the relative
homogeneous spectra of the two restrictions of the graded algebra to `Z'`, induced by the
comparison of the restriction datum. -/
def restrictProjIso {Z Z' : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (h : Z' ⟶ Z) :
    (relativeProj (Â Z' (yoneda.map h ≫ g))).scheme ≅
      (relativeProj ((Â Z g).pullback ((BigFppfOver.toScheme B S hS).map h))).scheme :=
  relativeProjCongr (ρ.restrict h g (yoneda.map h ≫ g) rfl) (ρ.isIso_restrict_app h g _ rfl)

/-- The point of the scheme-level functor of quadruples which the representation of Tag 01NZ
attaches to a `W`-point of `Proj_Z(g^*𝒜)`, read on the fibre: it is the comparison of the
corresponding point of `F(W)`. -/
theorem fibreToF_projPoint_val {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (s : T ⟶ projObj Â g (hc Z g)) (W : BigFppfOver B S hS)
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) (w : W ⟶ T) :
    ρ.fibreToF g (w ≫ s ≫ projHom Â g (hc Z g)) _ rfl ((ρ.projPoint g (hc Z g) s).val W hW w) =
      ((relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv
        ((BigFppfOver.toScheme B S hS).map s)).val _ hW ((BigFppfOver.toScheme B S hS).map w) :=
  ρ.fibreToF_fibreOfF g _ _ rfl _ (homEquiv_val_fst _ _ _ _ _)

/-- Equal points `ξ = ξ₂` of the limit have equal comparisons `ρ.fibreToF g t` of their values
at a `W`-point `w`, for any choice of the compatibility proofs. -/
theorem fibreToF_val_eq_of_eq {Z T W : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : W ⟶ Z)
    {ξ ξ₂ : LimPoint ρ T} (hξ : ξ = ξ₂)
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) (w : W ⟶ T)
    (hf : yoneda.map t ≫ g = yoneda.map w ≫ ξ.point)
    (hf₂ : yoneda.map t ≫ g = yoneda.map w ≫ ξ₂.point) :
    ρ.fibreToF g t _ hf (ξ.val W hW w) = ρ.fibreToF g t _ hf₂ (ξ₂.val W hW w) := by
  subst hξ
  rfl

/-- **The comparison morphism of the third assertion of Stacks 084B is the canonical one.** For
`h : Z' ⟶ Z` the morphism `Proj_{Z'}((g ∘ h)^*𝒜) ⟶ Proj_Z(g^*𝒜)` the cartesian squares of the
second assertion induce is the identification `Proj_{Z'}((g ∘ h)^*𝒜) ≅ Proj_{Z'}(h^*(g^*𝒜))` of
the restriction datum followed by the base-change morphism of Tag 01O3. -/
theorem toScheme_map_projComparison {Z Z' : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (h : Z' ⟶ Z) :
    (BigFppfOver.toScheme B S hS).map (ρ.projComparison hc g h) =
      (ρ.restrictProjIso g h).hom ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom (Â Z g)
          ((BigFppfOver.toScheme B S hS).map h) := by
  have hpH : ρ.projComparison hc g h ≫ projHom Â g (hc Z g) =
      projHom Â (yoneda.map h ≫ g) (hc Z' _) ≫ h :=
    (ρ.relativeProjPoints hc).fibreComparison_comp_fibreHom Z g h
  have e' := congrArg (fun α => α.app (op (projObj Â (yoneda.map h ≫ g) (hc Z' _)))
    (𝟙 (projObj Â (yoneda.map h ≫ g) (hc Z' _)))) (ρ.isPullback_projComparison hc g h).2
  have hpt : ρ.projPoint g (hc Z g) (ρ.projComparison hc g h) =
      ρ.projPoint (yoneda.map h ≫ g) (hc Z' _) (𝟙 _) :=
    (ρ.relativeProjFunctorEquiv_projToFunctor hc g (ρ.projComparison hc g h)).symm.trans
      ((congrArg (ρ.relativeProjFunctorEquiv hc _) e').trans
        (ρ.relativeProjFunctorEquiv_projToFunctor hc (yoneda.map h ≫ g) (𝟙 _)))
  apply (relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv.injective
  apply (Scheme.QcExtension.equivQcOpen _ _).injective
  ext V hV
  have hO : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (opensObject B S hS (projObj Â (yoneda.map h ≫ g) (hc Z' _)) V)) :=
    isCompact_iff_compactSpace.mp hV
  set ι := opensObjectι B S hS (projObj Â (yoneda.map h ≫ g) (hc Z' _)) V
  set p' := ρ.projPoint (yoneda.map h ≫ g) (hc Z' _) (𝟙 _)
  have hcomm : ι ≫ ρ.projComparison hc g h ≫ projHom Â g (hc Z g) =
      (ι ≫ projHom Â (yoneda.map h ≫ g) (hc Z' _)) ≫ h := by rw [hpH]; rfl
  show ((relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv
      ((BigFppfOver.toScheme B S hS).map (ρ.projComparison hc g h))).val _ hO
      ((BigFppfOver.toScheme B S hS).map ι) =
    ((relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv
      ((ρ.restrictProjIso g h).hom ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom (Â Z g)
          ((BigFppfOver.toScheme B S hS).map h))).val _ hO
      ((BigFppfOver.toScheme B S hS).map ι)
  have step5 := ρ.fibreToF_projPoint_val hc (yoneda.map h ≫ g) (𝟙 _) _ hO ι
  have step6 := homEquiv_comp_relativeProjCongr_val (A₁ := Â Z' (yoneda.map h ≫ g))
    (A₂ := (Â Z g).pullback ((BigFppfOver.toScheme B S hS).map h))
    (ρ.restrict h g (yoneda.map h ≫ g) rfl)
    (ρ.isIso_restrict_app h g _ rfl) (𝟙 _) _ hO ((BigFppfOver.toScheme B S hS).map ι)
  have step7 := homEquiv_comp_baseChangeHom_val (Â Z g) ((BigFppfOver.toScheme B S hS).map h)
    (ρ.restrictProjIso g h).hom _ hO ((BigFppfOver.toScheme B S hS).map ι)
  refine Eq.trans ?_ step7.symm
  refine (ρ.fibreToF_projPoint_val hc g (ρ.projComparison hc g h) _ hO ι).symm.trans ?_
  refine (ρ.fibreToF_val_eq_of_eq g (ι ≫ ρ.projComparison hc g h ≫ projHom Â g (hc Z g)) hpt
    hO ι rfl (by rw [hpH]; rfl)).trans ?_
  refine (ρ.fibreToF_congr g hcomm (yoneda.map ι ≫ p'.point) (by rw [hpH]; rfl) (by rfl)
    (p'.val _ hO ι)).trans ?_
  refine (ρ.fibreToF_comp g h (ι ≫ projHom Â (yoneda.map h ≫ g) (hc Z' _))
    (yoneda.map ι ≫ p'.point) (by rfl) rfl (p'.val _ hO ι)).trans ?_
  refine congrArg (fun z => F.baseChangeUp ((BigFppfOver.toScheme B S hS).map h)
    (situationAlgebra (Â Z g)) z) ?_
  exact (congrArg (fun z => F.algebraTransport
    (unitalHomInverse (ρ.restrict h g (yoneda.map h ≫ g) rfl) (ρ.isIso_restrict_app h g _ rfl))
    (isIso_unitalHomInverse_app (ρ.restrict h g (yoneda.map h ≫ g) rfl)
      (ρ.isIso_restrict_app h g _ rfl)) z) step5).trans step6.symm

/-- **The third assertion of Stacks 084B, with the canonical morphisms.** For a scheme point
`g : Z ⟶ X` and `h : Z' ⟶ Z`, the square formed by the structure morphisms of
`Proj_{Z'}((g ∘ h)^*𝒜)` and of `Proj_Z(g^*𝒜)`, by `h`, and by the identification
`Proj_{Z'}((g ∘ h)^*𝒜) ≅ Proj_{Z'}(h^*(g^*𝒜))` of the restriction datum followed by the
base-change morphism of Tag 01O3, is cartesian; and that morphism lies over the morphisms to the
functor of quadruples of the second assertion. So the identification
`Proj_{Z'}((g ∘ h)^*𝒜) = Z' ×_X F` is the base change along `h` of
`Proj_Z(g^*𝒜) = Z ×_X F`, through the canonical isomorphism of Tag 01O3. -/
theorem isPullback_baseChangeHom_restrictProjIso {Z Z' : BigFppfOver B S hS}
    (g : yoneda.obj Z ⟶ X) (h : Z' ⟶ Z) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (ρ.projComparison hc g h))
        (relativeProj (Â Z' (yoneda.map h ≫ g))).toBase
        (relativeProj (Â Z g)).toBase ((BigFppfOver.toScheme B S hS).map h) ∧
      (BigFppfOver.toScheme B S hS).map (ρ.projComparison hc g h) =
        (ρ.restrictProjIso g h).hom ≫
          Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom (Â Z g)
            ((BigFppfOver.toScheme B S hS).map h) :=
  ⟨(ρ.relativeProjPoints hc).isPullback_map_fibreComparison Z g h,
    ρ.toScheme_map_projComparison hc g h⟩

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end

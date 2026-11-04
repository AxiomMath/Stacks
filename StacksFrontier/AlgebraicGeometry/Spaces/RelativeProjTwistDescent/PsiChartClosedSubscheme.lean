module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Transpose
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.TwistRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiAdjoint

/-!
# The adjoint form of `ψ` on pulled-back sections, and the ideal of Tag 0801

Let `ι : P ⟶ Proj_Y(A)` be a morphism of schemes and `p = ι ≫ π`.  The adjoint form
`p^*A_n ⟶ ι^*𝒪(n)` of Tag 01NR's `ψ` (`AlgebraicGeometry.Space.pullbackAdjointPsi`)
carries the pullback along `p` of a section `a` of `A_n` to the pullback along `ι` of the
section `ψ(a)` of `𝒪(n)`.  Consequently, for a morphism `j : Z ⟶ P` with `j ≫ ι` a closed
immersion, `a` lies in the graded ideal of Tag 0801 of the closed subscheme `j ≫ ι` exactly when
the adjoint form of `ψ`, applied to the pullback of `a` and restricted to `Z`, vanishes.  This is
the scheme half of the chart dictionary of Stacks 085L, at the scheme of `V ×_X P`.

## Main results

* `AlgebraicGeometry.Space.C1359Bridge.pullbackAdjointPsi_app_pullbackSection`: the adjoint form
  of `ψ` on a pulled-back section.
* `AlgebraicGeometry.Space.C1359Bridge.mem_twistKerGradedIdeal_iff_pullbackAdjointPsi`: membership
  in the ideal of Tag 0801 read through the adjoint form of `ψ`.
* `AlgebraicGeometry.Space.C1359Bridge.mem_twistKerGradedIdeal_chartClosedSubscheme_iff`: the same
  on the scheme of `V ×_X P`.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Space.C1359Bridge

section Generic

variable {Y P : Scheme.{u}} (A : SheafGradedAlgebra Y) (ι : P ⟶ (relativeProj A).scheme)

/-- A section is zero exactly when its image under the component of an isomorphism is. -/
private theorem eq_zero_iff_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (V : X.Opens)
    (x : M.val.obj (op V)) : x = 0 ↔ e.hom.val.app (op V) x = 0 := by
  rw [← map_zero (e.hom.val.app (op V)).hom]
  exact ((ConcreteCategory.bijective_of_isIso (e.hom.app V)).injective.eq_iff).symm

/-- **The adjoint form of `ψ` on a pulled-back section**: for `p = ι ≫ π`, the morphism
`p^*A_n ⟶ ι^*𝒪(n)` carries the pullback along `p` of a section `a` of `A_n` over `W` to the
pullback along `ι` of the section `ψ(a)` of `𝒪(n)` over `π⁻¹(W)`. -/
theorem pullbackAdjointPsi_app_pullbackSection (p : P ⟶ Y) (hp : p = ι ≫ (relativeProj A).toBase)
    (n : ℕ) (W : Y.Opens) (V : P.Opens) (hV : V ≤ ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W))
    (hV' : V ≤ p ⁻¹ᵁ W) (a : Γ(A.piece (n : ℤ), W)) :
    (pullbackAdjointPsi A ι p hp n).val.app (op V)
        (Scheme.Modules.pullbackSection p (A.piece (n : ℤ)) W V hV' a) =
      Scheme.Modules.pullbackSection ι ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))
        ((relativeProj A).toBase ⁻¹ᵁ W) V hV
        (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ n).val.app (op W) a) := by
  subst hp
  have h₁ := Scheme.Modules.pullbackSection_comp ι (relativeProj A).toBase (A.piece (n : ℤ)) W
    ((relativeProj A).toBase ⁻¹ᵁ W) V le_rfl hV hV' a
  have h₂ : ((Scheme.Modules.pullbackComp ι (relativeProj A).toBase).inv.app
      (A.piece (n : ℤ))).val.app (op V)
        (Scheme.Modules.pullbackSection (ι ≫ (relativeProj A).toBase) (A.piece (n : ℤ)) W V hV' a) =
      Scheme.Modules.pullbackSection ι ((Scheme.Modules.pullback (relativeProj A).toBase).obj
          (A.piece (n : ℤ))) ((relativeProj A).toBase ⁻¹ᵁ W) V hV
        (Scheme.Modules.pullbackSection (relativeProj A).toBase (A.piece (n : ℤ)) W
          ((relativeProj A).toBase ⁻¹ᵁ W) le_rfl a) := by
    rw [← h₁]
    change ((Scheme.Modules.pullbackComp ι (relativeProj A).toBase).hom.app (A.piece (n : ℤ)) ≫
      (Scheme.Modules.pullbackComp ι (relativeProj A).toBase).inv.app
        (A.piece (n : ℤ))).val.app (op V) _ = _
    rw [Iso.hom_inv_id_app]
    rfl
  have h₃ := Scheme.Modules.pullbackSection_naturality ι
    (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _
      ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))).symm
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ n)) ((relativeProj A).toBase ⁻¹ᵁ W) V hV
    (Scheme.Modules.pullbackSection (relativeProj A).toBase (A.piece (n : ℤ)) W
      ((relativeProj A).toBase ⁻¹ᵁ W) le_rfl a)
  have h₄ := Scheme.Modules.pullbackSection_homEquiv (relativeProj A).toBase (A.piece (n : ℤ))
    ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))
    (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _
      ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))).symm
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ n)) W ((relativeProj A).toBase ⁻¹ᵁ W)
    le_rfl a
  rw [Equiv.apply_symm_apply] at h₄
  refine (congrArg _ h₂).trans (h₃.trans ?_)
  refine congrArg _ (h₄.trans ?_)
  exact (ConcreteCategory.congr_hom
    (((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ)).val.map_id _) _).trans rfl

/-- **Membership in the ideal of Tag 0801, read through the adjoint form of `ψ`.**  For
`p = ι ≫ π` and `j : Z ⟶ P` with `j ≫ ι` a closed immersion, a section `a` of `A_n` over `W` lies
in the graded ideal of the closed subscheme `j ≫ ι` exactly when the adjoint form of `ψ` applied
to the pullback of `a` along `p` restricts to zero on `Z`. -/
theorem mem_twistKerGradedIdeal_iff_pullbackAdjointPsi {Z : Scheme.{u}} (j : Z ⟶ P)
    [AlgebraicGeometry.IsClosedImmersion (j ≫ ι)]
    [AlgebraicGeometry.QuasiCompact (relativeProj A).toBase] (p : P ⟶ Y)
    (hp : p = ι ≫ (relativeProj A).toBase) (n : ℕ) (W : Y.Opens)
    (hV' : ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W) ≤ p ⁻¹ᵁ W) (a : Γ(A.piece (n : ℤ), W)) :
    a ∈ ((twistKerGradedIdeal A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) (j ≫ ι)).piece
        (n : ℤ)).toSubmodule.obj (op W) ↔
      Scheme.Modules.pullbackSection j
        ((Scheme.Modules.pullback ι).obj ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ)))
        (ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)) (j ⁻¹ᵁ (ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)))
        le_rfl ((pullbackAdjointPsi A ι p hp n).val.app (op (ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)))
          (Scheme.Modules.pullbackSection p (A.piece (n : ℤ)) W _ hV' a)) = 0 := by
  rw [mem_twistKerGradedIdeal_iff,
    pullbackAdjointPsi_app_pullbackSection A ι p hp n W _ le_rfl hV' a,
    eq_zero_iff_of_iso ((Scheme.Modules.pullbackComp j ι).app _),
    Iso.app_hom]
  exact Iff.of_eq (congrArg (· = 0) (Scheme.Modules.pullbackSection_comp j ι
    ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ W)
    (ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)) (j ⁻¹ᵁ (ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)))
    le_rfl le_rfl le_rfl
    (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ n).val.app (op W) a)).symm)

end Generic

section Chart

variable (s : RelativeProjSituation.{u, u}) {Z : AlgebraicSpaces s.site s.base s.containsBase}
  (i : Z ⟶ s.Proj) (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)
  (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- **The ideal of Tag 0801 of the base change of a closed subspace, read through `ψ`.**  At a
scheme point `f : T ⟶ X`, a section `a` of `(f^*𝒜)_n` over `W` lies in the graded ideal of the
closed subscheme `Z ×_X T ⊆ Proj_T(f^*𝒜)` exactly when the adjoint form of `ψ` on the scheme of
`T ×_X P`, applied to the pullback of `a`, restricts to zero on the scheme of `Z ×_X T`. -/
theorem mem_twistKerGradedIdeal_chartClosedSubscheme_iff
    [AlgebraicGeometry.QuasiCompact (relativeProj (s.relativeProjPoints.algebra T f)).toBase]
    (n : ℕ) (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece (n : ℤ), W)) :
    a ∈ ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
        (GluedTwistAlgebra.twistDataOfGradedAlgebra _)
        (RelativeProjSituation.chartClosedSubscheme i hi T f)).piece (n : ℤ)).toSubmodule.obj
          (op W) ↔
      Scheme.Modules.pullbackSection ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.snd
            (s.relativeProjPoints.fibreToSpace T f)))
        ((Scheme.Modules.pullback (s.relativeProjPoints.fibreIso T f).hom).obj
          ((Tag07ZGTwist.twistAlgebra (s.relativeProjPoints.algebra T f)).piece (n : ℤ)))
        ((s.relativeProjPoints.fibreIso T f).hom ⁻¹ᵁ
          ((relativeProj (s.relativeProjPoints.algebra T f)).toBase ⁻¹ᵁ W)) _ le_rfl
        ((pullbackAdjointPsi (s.relativeProjPoints.algebra T f)
          (s.relativeProjPoints.fibreIso T f).hom
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map
              (s.relativeProjPoints.fibreHom T f)) (s.relativeProjPoints.fibreHom_comp T f)
            n).val.app
          (op ((s.relativeProjPoints.fibreIso T f).hom ⁻¹ᵁ
            ((relativeProj (s.relativeProjPoints.algebra T f)).toBase ⁻¹ᵁ W)))
          (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme s.site s.base s.containsBase).map
              (s.relativeProjPoints.fibreHom T f)) _ W _
            (by rw [s.relativeProjPoints.fibreHom_comp T f]; exact le_rfl) a)) = 0 := by
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.snd
            (s.relativeProjPoints.fibreToSpace T f)) ≫ (s.relativeProjPoints.fibreIso T f).hom) :=
    RelativeProjSituation.isClosedImmersion_chartClosedSubscheme i hi T f
  exact mem_twistKerGradedIdeal_iff_pullbackAdjointPsi _ _ _ _
    (s.relativeProjPoints.fibreHom_comp T f) n W _ a

end Chart

end AlgebraicGeometry.Space.C1359Bridge

end

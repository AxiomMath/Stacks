module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffineSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# A sheaf of ideals which is a product on the affine charts

Let `W` be an algebraic space over a scheme `S` and let `𝓟, 𝓘, 𝓘' ⊆ 𝒪_W` be sheaves of ideals on
the small étale site of `W`.  If over every affine étale chart `V` of `W` the ideal `𝓟(V)` is the
product `𝓘(V) 𝓘'(V)` of ideals of `𝒪_W(V)`, then `𝓟` is the product `𝓘 𝓘'` of sheaves of ideals
of `AlgebraicGeometry.Space.Stacks.Sites.idealSmul`.  Both sheaves have local membership and the
affine charts cover every chart, so they agree as soon as they agree on the affine charts, and
there the sheaf-theoretic product contains the product of the ideals of sections.

## Main results

* `AlgebraicGeometry.Space.eq_idealSmul_of_forall_isAffine`: the statement above.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A section lies in a sheaf of submodules if its restrictions to affine étale charts do. -/
private theorem mem_of_forall_isAffine_map_mem {W : AlgebraicSpaces B S hS}
    (M : (SheafOfModules.unit (smallEtaleRingSheaf B S hS W.1 W.2)).Submodule)
    {V : SmallEtale B S hS W.1}
    {x : (SheafOfModules.unit (smallEtaleRingSheaf B S hS W.1 W.2)).val.obj (op V)}
    (h : ∀ (Y : SmallEtale B S hS W.1) (a : Y ⟶ V),
      IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj Y) →
        (SheafOfModules.unit (smallEtaleRingSheaf B S hS W.1 W.2)).val.map a.op x ∈
          M.obj (op Y)) :
    x ∈ M.obj (op V) := by
  obtain ⟨Jw, Yf, a, hYaff, hYcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS W.1 V
  refine M.isSheaf x ((SmallEtale.topology B S hS W.1).superset_covering ?_ hYcov)
  rintro T g ⟨T', k, a', ⟨j⟩, rfl⟩
  change (SheafOfModules.unit (smallEtaleRingSheaf B S hS W.1 W.2)).val.map (k ≫ a j).op x ∈
    M.obj (op T)
  rw [op_comp, PresheafOfModules.map_comp_apply]
  exact M.map_mem k.op (h _ _ (hYaff j))

/-- **A sheaf of ideals which is the product of two sheaves of ideals on every affine chart is
their product.**  If `𝓟(V) = 𝓘(V) 𝓘'(V)` for every affine étale chart `V` of `W`, then
`𝓟 = 𝓘 · 𝓘'`. -/
theorem eq_idealSmul_of_forall_isAffine {W : AlgebraicSpaces B S hS}
    (P I I' : (SheafOfModules.unit (smallEtaleRingSheaf B S hS W.1 W.2)).Submodule)
    (h : ∀ V : SmallEtale B S hS W.1,
      IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
        chartSectionsIdeal B S hS W P V =
          chartSectionsIdeal B S hS W I V * chartSectionsIdeal B S hS W I' V) :
    P = Stacks.Sites.idealSmul (O := structureSheaf B S hS W.1 W.2) I I' := by
  set Q := Stacks.Sites.idealSmul (O := structureSheaf B S hS W.1 W.2) I I' with hQ
  apply le_antisymm
  · -- A section of `𝓟` lies in `𝓘 · 𝓘'` on the affine charts, which cover.
    intro V x hx
    obtain ⟨V⟩ := V
    refine mem_of_forall_isAffine_map_mem Q fun Y a hY => ?_
    have hP := P.map_mem a.op hx
    change _ ∈ chartSectionsIdeal B S hS W P Y at hP
    rw [h Y hY] at hP
    refine Stacks.SheafOfModules.le_sheafifySubmodule _ (op Y) ?_
    refine Submodule.mul_induction_on hP (fun b hb c hc => ?_)
      (fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
    exact Stacks.Sites.smul_mem_presheafIdealSmul (O := structureSheaf B S hS W.1 W.2) I hb hc
  · -- A product of a section of `𝓘` with one of `𝓘'` lies in `𝓟` on the affine charts.
    refine Stacks.SheafOfModules.sheafifySubmodule_le
      (Stacks.Sites.presheafIdealSmul_le (O := structureSheaf B S hS W.1 W.2) I
        fun V b hb c hc => ?_)
    obtain ⟨V⟩ := V
    refine mem_of_forall_isAffine_map_mem P fun Y a hY => ?_
    change ((smallEtaleRingSheaf B S hS W.1 W.2).obj.map a.op).hom
        ((show (smallEtaleRingSheaf B S hS W.1 W.2).obj.obj (op V) from b) *
          (show (smallEtaleRingSheaf B S hS W.1 W.2).obj.obj (op V) from c)) ∈
      chartSectionsIdeal B S hS W P Y
    rw [map_mul, h Y hY]
    exact Ideal.mul_mem_mul (I.map_mem a.op hb) (I'.map_mem a.op hc)

end AlgebraicGeometry.Space

end

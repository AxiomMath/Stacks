module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.StalkHenselian
public import StacksFrontier.CategoryTheory.Sites.LeftAdjointCoveringLift

/-!
# Lifting points of the inverse-image stalk to affine charts

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces `X` and `Y`
and `x̄` a geometric point of `X`.  The functor `F ↦ (g⁻¹F)_x̄` is a left adjoint, so its points
lift along coverings (`CategoryTheory.Sheaf.exists_map_yoneda_map_eq`).  This file records the
two instances of that used in the proof of Stacks 04KL: a point of `(g⁻¹h_P)_x̄` lifts to an
affine open of the chart `P`, and `(g⁻¹h_V)_x̄` is nonempty for some affine étale chart `V` of `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_affineOpen_lift`: a point over a chart lifts to an affine open
  of it.
* `AlgebraicGeometry.Space.exists_affine_invStalk`: some affine chart has a point.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
  (x : GeometricPoint B S hS X.1)

attribute [local instance] smallEtaleTopology_subcanonical

/-- The affine opens of an étale chart, restricted to as charts, cover it. -/
theorem generate_ofArrows_affineOpens_mem_topology (P : SmallEtale B S hS Y.1) :
    Sieve.generate (Presieve.ofArrows
        (fun O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens =>
          chartOpenRestriction B S hS Y.1 P O.1)
        (fun O => chartOpenRestrictionHom B S hS Y.1 P O.1)) ∈
      SmallEtale.topology B S hS Y.1 P := by
  refine smallEtale_sieve_of_pointwise_covering B S hS Y.1 P _ fun z ↦ ?_
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ z)
  refine ⟨chartOpenRestriction B S hS Y.1 P V, chartOpenRestrictionHom B S hS Y.1 P V,
    Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (⟨V, hV⟩ :
      ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens)), ⟨z, hzV⟩, ?_⟩
  have h : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map
      (chartOpenRestrictionHom B S hS Y.1 P V)) = V.ι :=
    chartOpenRestrictionHom_toScheme B S hS Y.1 P V
  rw [h]
  rfl

/-- **A point of the inverse-image stalk over a chart lifts to an affine open of the chart.** -/
theorem exists_affineOpen_lift (P : SmallEtale B S hS Y.1)
    (τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj P)) :
    ∃ (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens)
      (τ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj
        (chartOpenRestriction B S hS Y.1 P O.1))),
      (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
        (chartOpenRestrictionHom B S hS Y.1 P O.1)) τ' = τ :=
  Sheaf.exists_map_yoneda_map_eq (invStalk g x)
    (fun O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens =>
      chartOpenRestriction B S hS Y.1 P O.1)
    (fun O => chartOpenRestrictionHom B S hS Y.1 P O.1)
    (generate_ofArrows_affineOpens_mem_topology P) τ

/-- **Some affine étale chart of `Y` has a point in the inverse-image stalk.** The functor
`F ↦ (g⁻¹F)_x̄` carries the terminal sheaf to a point, which lifts along the covering of the
terminal sheaf by an atlas of `Y`, and then to an affine open of the atlas. -/
theorem exists_affine_invStalk :
    ∃ (V₀ : SmallEtale B S hS Y.1) (_ : IsAffine (chartSch V₀)),
      Nonempty ((invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀)) := by
  obtain ⟨T, a, hsurj, hetale⟩ := Y.2.exists_atlas
  set Va : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk a, hetale⟩
  have hsub : ∀ W : SmallEtale B S hS Y.1,
      Subsingleton ((⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)).obj.obj (op W)) :=
    fun W => @Unique.instSubsingleton _
      (Functor.uniqueTerminalObj (P := Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1)
        (op W)))
  obtain ⟨-, σ, -⟩ := Sheaf.exists_map_yonedaEquiv_symm_eq (invStalk g x)
    (F := ⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (K := PUnit.{u + 1})
    (fun _ => Va)
    (fun _ => (default : (Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op Va)).obj
      (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))) (fun W _ ↦ by
      refine ⟨Sieve.generate (Presieve.singleton (SmallEtale.prodFst B S hS Y.1 W Va)), ?_,
        fun W' i hi ↦ ?_⟩
      · refine smallEtale_sieve_of_pointwise_covering B S hS Y.1 W _ fun z ↦ ?_
        have hs : Surjective ((BigFppfOver.toScheme B S hS).map (W.property.rep.fst' a)) :=
          hsurj.property W.obj.hom _ _ (W.property.rep.isPullback' a).flip
        obtain ⟨z', hz'⟩ := hs.surj z
        exact ⟨SmallEtale.prodObj B S hS Y.1 W Va, SmallEtale.prodFst B S hS Y.1 W Va,
          Sieve.le_generate _ _ _ (Presieve.singleton.mk), z', hz'⟩
      · obtain ⟨_, h, _, ⟨⟩, -⟩ := hi
        exact ⟨PUnit.unit, h ≫ SmallEtale.prodSnd B S hS _ W Va, (hsub W').elim _ _⟩)
    (default : (invStalk g x).obj (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))
  obtain ⟨O, τ', -⟩ := exists_affineOpen_lift g x Va σ
  exact ⟨chartOpenRestriction B S hS Y.1 Va O.1, O.2, ⟨τ'⟩⟩

end AlgebraicGeometry.Space

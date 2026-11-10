module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePureDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteFieldFundamentalGroup

/-!
# Surjectivity along a retraction and normality of the image after a constant field extension

Two facts on étale fundamental groups used in the lattice comparison of Laumon's Fourier family
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)):

* a morphism `p : Y ⟶ X` of connected schemes with a section `s` (`s ≫ p = 𝟙`) induces a
  surjection `π₁(Y, ȳ) → π₁(X, p(ȳ))`
  (`AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_section`): the composite of `s_*`, a
  change of base point and `p_*` is induced by the base change along `s ≫ p = 𝟙`, so it is inner
  conjugate to the identity (Tag 0BND);
* for a connected `X` over a finite field `k`, a finite extension `L` of `k` and a connected
  `Y = X ×_k L`, the image of `π₁(Y, ȳ) → π₁(X, h(ȳ))` is normal
  (`AlgebraicGeometry.normal_range_etaleFundamentalGroupMap_of_isPullback`): it is the stabilizer
  of a point of the fibre of the finite étale cover `Y ⟶ X`, it contains the kernel of
  `π₁(X) → π₁(Spec k)` (which fixes the fibres of covers pulled back from `Spec k`), and that
  kernel contains every commutator, `π₁(Spec k)` being commutative.

## Main results

* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_section`.
* `AlgebraicGeometry.normal_range_etaleFundamentalGroupMap_of_isPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- **A morphism with a section is surjective on étale fundamental groups.** -/
theorem surjective_etaleFundamentalGroupMap_of_section {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (p : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X) (y : GeometricPoint Y) :
    Function.Surjective (etaleFundamentalGroupMap p y) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (x := y) (x' := (y.map p).map s)
  have h₁ := ((isEtaleFundamentalGroupHomInducedBy_map s (y.map p)).comp_baseChange
    (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t)).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_map p y)
  obtain ⟨g, hg⟩ := (isEtaleFundamentalGroupHomInducedBy_id (y.map p)).isInnerConjugate_of_eq h₁
    (by rw [Category.comp_id, hs])
  intro δ
  refine ⟨etaleFundamentalGroupBasePointHom t
    (etaleFundamentalGroupMap s (y.map p) (g⁻¹ * δ * g)), ?_⟩
  refine (hg (g⁻¹ * δ * g)).trans ?_
  rw [MonoidHom.id_apply]
  group

/-- **The image of `π₁(X ×_k L) → π₁(X)` is normal**, for a finite extension `L` of a finite
field `k`. -/
theorem normal_range_etaleFundamentalGroupMap_of_isPullback {k : Type u} [Field k] [Finite k]
    {L : Type u} [Field L] [Algebra k L] [Module.Finite k L] {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Spec (.of k)) (h : Y ⟶ X) (g : Y ⟶ Spec (.of L))
    (hpb : IsPullback h g f (specAlgebraMap k L)) (y : GeometricPoint Y) :
    (etaleFundamentalGroupMap h y).toMonoidHom.range.Normal := by
  let s := specAlgebraMap k L
  have : IsFinite s := (IsFinite.SpecMap_iff _).2 ((RingHom.finite_algebraMap).2 inferInstance)
  have : Etale s := etale_specMap_algebraMap_of_finite_separable k L
  have hs : finiteEtale s := ⟨inferInstance, inferInstance⟩
  have hh : finiteEtale h := MorphismProperty.of_isPullback hpb.flip hs
  have hker : (etaleFundamentalGroupMap f (y.map h)).toMonoidHom.ker ≤
      (etaleFundamentalGroupMap h y).toMonoidHom.range := by
    intro σ hσ
    rw [range_etaleFundamentalGroupMap_eq_stabilizer hh y, MulAction.mem_stabilizer_iff]
    let SL : FiniteEtaleOver (Spec (.of k)) := finiteEtaleOverSource hs
    let c : finiteEtaleOverSource hh ≅ (finiteEtaleBaseChange f).obj SL :=
      MorphismProperty.Over.isoMk (hpb.isoPullback ≪≫ pullbackSymmetry f s) (by
        change (hpb.isoPullback.hom ≫ (pullbackSymmetry f s).hom) ≫ pullback.snd s f = h
        rw [Category.assoc, pullbackSymmetry_hom_comp_snd, IsPullback.isoPullback_hom_fst])
    exact smul_eq_self_of_etaleFundamentalGroupMap_eq_one_of_iso f _ SL c hσ _
  refine ⟨fun a ha b => ?_⟩
  have hc := hker (commutator_mem_ker_etaleFundamentalGroupMap_of_finite k f (y.map h) b a)
  have hmem := Subgroup.mul_mem _ hc ha
  rwa [show b * a * b⁻¹ * a⁻¹ * a = b * a * b⁻¹ by group] at hmem

end AlgebraicGeometry

end

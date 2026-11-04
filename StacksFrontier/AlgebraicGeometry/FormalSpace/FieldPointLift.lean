module

public import StacksFrontier.CategoryTheory.Sites.JointlyLocallySurjective
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChartPoint
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient

/-!
# Lifting a field-valued section along a jointly surjective family, after a finite extension

Let `c i : Yᵢ ⟶ Y` be a family of morphisms of fppf sheaves on the big fppf site of `S` such that
`∐ Yᵢ ⟶ Y` is a surjection of sheaves, and let `y` be a section of `Y` over an object of the site
whose underlying scheme is `Spec k` for a field `k`. Then for some finite extension `l/k` the
restriction of `y` to `Spec l` lifts to one of the `Yᵢ`.

The section lifts locally on an fppf covering of `Spec k`; a member of the covering is a nonempty
scheme locally of finite type over `k`, and the residue field at one of its closed points is a
finite extension of `k` (Stacks 0478).

## Main results

* `exists_finite_extension_lift_of_isLocallySurjective_sigmaDesc`: a section of `Y` over `Spec k`
  lifts to some `Yᵢ` after restriction to `Spec l` for a finite extension `l/k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The object of the big fppf site over `S` given by `Spec l ⟶ Spec k ≅ T₀ ⟶ S` for a field
extension `l/k` and an object `T₀` whose underlying scheme is `Spec k`. -/
abbrev fieldExtensionObject {k : Type u} [Field k] (T₀ : BigFppfOver B S hS)
    (e₀ : (BigFppfOver.toScheme B S hS).obj T₀ = Spec (.of k)) (l : Type u) [Field l]
    [Algebra k l] (hl : B.Contains (Spec (.of l))) : BigFppfOver B S hS :=
  Over.mk ((B.inclusion.preimage (X := B.obj hl) (Y := T₀.left)
    (Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫ eqToHom e₀.symm)) ≫ T₀.hom)

/-- The morphism `Spec l ⟶ T₀` of the site underlying `Spec (k ⟶ l)`. -/
abbrev fieldExtensionMap {k : Type u} [Field k] (T₀ : BigFppfOver B S hS)
    (e₀ : (BigFppfOver.toScheme B S hS).obj T₀ = Spec (.of k)) (l : Type u) [Field l]
    [Algebra k l] (hl : B.Contains (Spec (.of l))) :
    fieldExtensionObject T₀ e₀ l hl ⟶ T₀ :=
  Over.homMk _ rfl

/-- The underlying morphism of schemes of `fieldExtensionMap T₀ e₀ l hl` is
`Spec (k ⟶ l)` followed by the identification `Spec k = T₀`. -/
theorem toScheme_map_fieldExtensionMap {k : Type u} [Field k] (T₀ : BigFppfOver B S hS)
    (e₀ : (BigFppfOver.toScheme B S hS).obj T₀ = Spec (.of k)) (l : Type u) [Field l]
    [Algebra k l] (hl : B.Contains (Spec (.of l))) :
    (BigFppfOver.toScheme B S hS).map (fieldExtensionMap T₀ e₀ l hl) =
      Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫ eqToHom e₀.symm :=
  B.inclusion.map_preimage _

/-- **A section of a jointly surjected sheaf over the spectrum of a field lifts to a member of the
family after a finite extension of the field.** -/
theorem exists_finite_extension_lift_of_isLocallySurjective_sigmaDesc {I : Type (u + 1)}
    {Yi : I → FppfSheaf B S hS} {Y : FppfSheaf B S hS} (c : ∀ i, Yi i ⟶ Y)
    (hc : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc c))
    {k : Type u} [Field k] (T₀ : BigFppfOver B S hS)
    (e₀ : (BigFppfOver.toScheme B S hS).obj T₀ = Spec (.of k)) (y : Y.obj.obj (op T₀)) :
    ∃ (l : Type u) (_ : Field l) (_ : Algebra k l) (_ : Module.Finite k l)
      (hl : B.Contains (Spec (.of l))) (i : I)
      (z : (Yi i).obj.obj (op (fieldExtensionObject T₀ e₀ l hl))),
      (c i).hom.app _ z = Y.obj.map (fieldExtensionMap T₀ e₀ l hl).op y := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨R, hR, hRmem⟩ := Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc c hc y
  obtain ⟨E, hE, hle⟩ := AlgebraicGeometry.Space.exists_covering_refining_sieve B
    ((B.topology.mem_over_iff R).1 hR)
  have hfppf : Presieve.ofArrows (fun j => B.inclusion.obj (E.X j))
      (fun j => B.inclusion.map (E.f j)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj T₀) := by
    have h := B.isFppfCovering_of_isCovering hE
    rw [IsFppfCovering, Precoverage.mem_comap_iff, Presieve.map_ofArrows] at h
    exact h
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hfppf
  obtain ⟨j, t₀, -⟩ := hfppf.1 (cast (congrArg (fun X : Scheme.{u} => (X : Type u)) e₀.symm)
    (IsLocalRing.closedPoint k))
  let X : Scheme.{u} := B.inclusion.obj (E.X j)
  let g : X ⟶ Spec (.of k) := B.inclusion.map (E.f j) ≫ eqToHom e₀
  have : LocallyOfFiniteType (B.inclusion.map (E.f j)) := by
    have := (hfppf.2 j).2; infer_instance
  have : LocallyOfFiniteType g := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  obtain ⟨t, -, ht⟩ := nonempty_inter_closedPoints (X := X) (Z := Set.univ) ⟨t₀, trivial⟩
    isClosed_univ.isLocallyClosed
  have htc : IsClosed ({t} : Set X) := ht
  have hfin := Deformation.Artin.finite_residueField_of_isClosed_of_field g htc
  let algkl : Algebra k (X.residueField t) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation t).hom.toAlgebra
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField t))) =
      X.fromSpecResidueField t ≫ g := SpecMap_algebraMap_residueField g t
  have hl : B.Contains (Spec (.of (X.residueField t))) := B.residueField_spec_contains (E.X j).2 t
  let Vj : BigFppfOver B S hS := Over.mk (E.f j ≫ T₀.hom)
  let fj : Vj ⟶ T₀ := Over.homMk (E.f j) rfl
  obtain ⟨i, w, hw⟩ := hRmem fj ((Sieve.overEquiv_iff _ _).1 (hle _ _ (E.presieve₀_f j)))
  let ρ : B.obj hl ⟶ E.X j := B.inclusion.preimage (X.fromSpecResidueField t)
  have hρ : ρ ≫ E.f j = B.inclusion.preimage (X := B.obj hl) (Y := T₀.left)
      (Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField t))) ≫ eqToHom e₀.symm) := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage, hspec]
    simp [g]
  let m : fieldExtensionObject T₀ e₀ (X.residueField t) hl ⟶ Vj :=
    Over.homMk ρ (by simp [Vj, fieldExtensionObject, ← hρ])
  have hm : m ≫ fj = fieldExtensionMap T₀ e₀ (X.residueField t) hl := by
    ext1; exact hρ
  refine ⟨X.residueField t, inferInstance, algkl, hfin, hl, i, (Yi i).obj.map m.op w, ?_⟩
  rw [NatTrans.naturality_apply, hw, ← hm, op_comp, Functor.map_comp, types_comp_apply]

end AlgebraicGeometry.FormalSpace

end

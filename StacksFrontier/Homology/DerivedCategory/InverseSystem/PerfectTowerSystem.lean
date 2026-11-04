module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower

/-!
# The cohomology inverse system of a perfect tower, as a diagram of `ℤ_[ℓ]`-modules

Let `T = (Kₙ, πₙ, φₙ)` be a tower of perfect complexes over the rings `ℤ/ℓⁿ⁺¹ℤ` in the sense of
[Tag 03V4](https://stacks.math.columbia.edu/tag/03V4) (`Stacks.InverseSystem.PerfectTower`).
Its cohomology modules `Hⁱ(Kₙ)` are `ℤ_[ℓ]`-modules through reduction modulo `ℓⁿ⁺¹` and form an
inverse system; `Stacks.InverseSystem.limitCohomology` is its limit, built as the submodule of
compatible families.  This file packages the system as a functor `ℕᵒᵖ ⥤ ModuleCat ℤ_[ℓ]`, shows
that `Stacks.InverseSystem.limitCohomology` is a limit of it in the categorical sense, and
transports the conclusions of Tag 03V4 — finiteness, finite support and the trace identity — to
the limit of *any* inverse system of `ℤ_[ℓ]`-modules isomorphic to it, compatibly with given
endomorphisms.

## Main definitions

* `Stacks.InverseSystem.levelCohomologySystem`: the functor `n ↦ Hⁱ(Kₙ)`.
* `Stacks.InverseSystem.levelCohomologyEndoSystem`: its endomorphism `n ↦ Hⁱ(πₙ)`.
* `Stacks.InverseSystem.limitCohomologyCone`: the cone with vertex `Hⁱ_∞`, and
  `Stacks.InverseSystem.isLimitLimitCohomologyCone`: it is a limit cone.
* `Stacks.InverseSystem.limitIsoLimitCohomology`: for an inverse system `S` isomorphic to
  `n ↦ Hⁱ(Kₙ)`, the isomorphism `lim S ≅ Hⁱ_∞`.

## Main results

* `Stacks.InverseSystem.limMap_comp_limitIsoLimitCohomology_hom`: that isomorphism intertwines an
  endomorphism of `S` lying over `n ↦ Hⁱ(πₙ)` with `πⁱ_∞`.
* `Stacks.InverseSystem.finite_limit_of_iso`,
  `Stacks.InverseSystem.finite_nontrivial_rational_limit_of_iso` and
  `Stacks.InverseSystem.alternating_trace_rational_limit_of_iso`: Tag 03V4 for `lim S`.

## References

* [Stacks Project, Tag 03V4](https://stacks.math.columbia.edu/tag/03V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe v

namespace Stacks.InverseSystem

variable {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ)

/-- The inverse system `n ↦ Hⁱ(Kₙ)` of a perfect tower, as a functor to `ℤ_[ℓ]`-modules. -/
public def levelCohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ] :=
  Functor.ofOpSequence (X := fun n => ModuleCat.of ℤ_[ℓ] (levelCohomology T i n))
    (fun n => ModuleCat.ofHom (levelCohomologyTransitionₗ T i n))

/-- The object of `levelCohomologySystem` at `n` is `Hⁱ(Kₙ)`. -/
@[simp]
public theorem levelCohomologySystem_obj (n : ℕ) :
    (levelCohomologySystem T i).obj (op n) = ModuleCat.of ℤ_[ℓ] (levelCohomology T i n) :=
  rfl

/-- The map `n + 1 ⟶ n` of `levelCohomologySystem` is the transition map `Hⁱ(Kₙ₊₁) → Hⁱ(Kₙ)`. -/
@[simp]
public theorem levelCohomologySystem_map_succ (n : ℕ) :
    (levelCohomologySystem T i).map (homOfLE (n.le_add_right 1)).op =
      ModuleCat.ofHom (levelCohomologyTransitionₗ T i n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The endomorphism `n ↦ Hⁱ(πₙ)` of the inverse system. -/
public def levelCohomologyEndoSystem : levelCohomologySystem T i ⟶ levelCohomologySystem T i :=
  NatTrans.ofOpSequence (fun n => ModuleCat.ofHom (levelCohomologyEndoₗ T i n)) (fun n => by
    ext x
    simp only [levelCohomologySystem_map_succ]
    exact (levelCohomologyTransitionₗ_endo T i n x).symm)

/-- The component of `levelCohomologyEndoSystem` at `n` is `Hⁱ(πₙ)`. -/
@[simp]
public theorem levelCohomologyEndoSystem_app (n : ℕ) :
    (levelCohomologyEndoSystem T i).app (op n) = ModuleCat.ofHom (levelCohomologyEndoₗ T i n) :=
  rfl

/-- The cone over `n ↦ Hⁱ(Kₙ)` with vertex `Hⁱ_∞` and the projections. -/
public def limitCohomologyCone : Cone (levelCohomologySystem T i) where
  pt := ModuleCat.of ℤ_[ℓ] (limitCohomology T i)
  π := NatTrans.ofOpSequence (fun n => ModuleCat.ofHom (limitCohomologyProjection T i n))
    (fun n => by
      ext a
      simp only [Functor.const_obj_obj, Functor.const_obj_map, levelCohomologySystem_map_succ]
      exact (a.2 n).symm)

/-- The projection of `limitCohomologyCone` at `n` is the projection `Hⁱ_∞ → Hⁱ(Kₙ)`. -/
@[simp]
public theorem limitCohomologyCone_π_app (n : ℕ) :
    (limitCohomologyCone T i).π.app (op n) =
      ModuleCat.ofHom (limitCohomologyProjection T i n) :=
  rfl

/-- `Hⁱ_∞`, the submodule of compatible families, is a limit of `n ↦ Hⁱ(Kₙ)`. -/
public def isLimitLimitCohomologyCone : IsLimit (limitCohomologyCone T i) where
  lift s := ModuleCat.ofHom
    { toFun := fun x => ⟨fun n => (s.π.app (op n)).hom x, fun n => by
        have h := congrArg (fun g => g.hom x) (s.w (homOfLE (n.le_add_right 1)).op)
        rwa [levelCohomologySystem_map_succ] at h⟩
      map_add' := fun x y => Subtype.ext (funext fun n => map_add (s.π.app (op n)).hom x y)
      map_smul' := fun c x => Subtype.ext (funext fun n => map_smul (s.π.app (op n)).hom c x) }
  fac s n := by
    ext x
    rfl
  uniq s m hm := by
    ext x
    exact Subtype.ext (funext fun n => congrArg (fun g => ModuleCat.Hom.hom g x) (hm (op n)))

variable {S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]} (e : S ≅ levelCohomologySystem T i)

/-- For an inverse system `S` of `ℤ_[ℓ]`-modules isomorphic to `n ↦ Hⁱ(Kₙ)`, its limit is
`Hⁱ_∞`. -/
public def limitIsoLimitCohomology : limit S ≅ (limitCohomologyCone T i).pt :=
  HasLimit.isoOfNatIso e ≪≫ limit.isoLimitCone ⟨_, isLimitLimitCohomologyCone T i⟩

/-- Composing `limitIsoLimitCohomology` with the projection `Hⁱ_∞ → Hⁱ(Kₙ)` is the projection
`lim S → S(n)` followed by the component of `e` at `n`. -/
@[reassoc (attr := simp)]
public theorem limitIsoLimitCohomology_hom_π (n : ℕ) :
    (limitIsoLimitCohomology T i e).hom ≫ (limitCohomologyCone T i).π.app (op n) =
      limit.π S (op n) ≫ e.hom.app (op n) := by
  rw [limitIsoLimitCohomology, Iso.trans_hom, Category.assoc, limit.isoLimitCone_hom_π,
    HasLimit.isoOfNatIso_hom_π]

/-- `πⁱ_∞`, as an endomorphism of the vertex of the limit cone. -/
public def limitCohomologyConeEndo : (limitCohomologyCone T i).pt ⟶ (limitCohomologyCone T i).pt :=
  ModuleCat.ofHom (limitCohomologyEndo T i)

/-- The isomorphism `lim S ≅ Hⁱ_∞` carries an endomorphism of `S` lying over `n ↦ Hⁱ(πₙ)` to
`πⁱ_∞`. -/
public theorem limMap_comp_limitIsoLimitCohomology_hom (σ : S ⟶ S)
    (hσ : σ ≫ e.hom = e.hom ≫ levelCohomologyEndoSystem T i) :
    limMap σ ≫ (limitIsoLimitCohomology T i e).hom =
      (limitIsoLimitCohomology T i e).hom ≫ limitCohomologyConeEndo T i := by
  refine (isLimitLimitCohomologyCone T i).hom_ext fun j => ?_
  induction j using Opposite.rec with | op n => ?_
  have hn := congrArg (fun τ => τ.app (op n)) hσ
  simp only [NatTrans.comp_app] at hn
  have hproj : limitCohomologyConeEndo T i ≫
      (limitCohomologyCone T i).π.app (op n) =
      (limitCohomologyCone T i).π.app (op n) ≫ (levelCohomologyEndoSystem T i).app (op n) := by
    ext a
    exact limitCohomologyProjection_limitCohomologyEndo T i n a
  rw [Category.assoc, Category.assoc, hproj, limitIsoLimitCohomology_hom_π, limMap_π_assoc,
    hn, limitIsoLimitCohomology_hom_π_assoc]

/-- The `ℤ_[ℓ]`-linear equivalence `lim S ≃ Hⁱ_∞`. -/
public def limitLinearEquivLimitCohomology :
    (limit S : ModuleCat.{v} ℤ_[ℓ]) ≃ₗ[ℤ_[ℓ]] limitCohomology T i :=
  (limitIsoLimitCohomology T i e).toLinearEquiv

/-- **Tag 03V4, part (2), for `lim S`.**  The limit is a finite `ℤ_[ℓ]`-module. -/
public theorem finite_limit_of_iso (e : S ≅ levelCohomologySystem T i) :
    Module.Finite ℤ_[ℓ] (limit S : ModuleCat.{v} ℤ_[ℓ]) :=
  have := (perfectTower_padicTrace_eq_alternating_trace_limitCohomology T).2.1 i
  Module.Finite.equiv (limitLinearEquivLimitCohomology T i e).symm

/-- The rationalisation `ℚ_[ℓ] ⊗ lim S` is finite-dimensional. -/
public theorem finite_rational_limit_of_iso (e : S ≅ levelCohomologySystem T i) :
    Module.Finite ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (limit S : ModuleCat.{v} ℤ_[ℓ])) :=
  have := finite_limit_of_iso T i e
  inferInstance

/-- **Tag 03V4, part (2), for `lim S`.**  If, in every degree, an inverse system `S i` is
isomorphic to `n ↦ Hⁱ(Kₙ)`, then `ℚ_[ℓ] ⊗ lim S i` vanishes for all but finitely many `i`. -/
public theorem finite_nontrivial_rational_limit_of_iso {S : ℤ → ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]}
    (e : ∀ i, S i ≅ levelCohomologySystem T i) :
    {i : ℤ | Nontrivial (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (limit (S i) : ModuleCat.{v} ℤ_[ℓ]))}.Finite := by
  refine (perfectTower_padicTrace_eq_alternating_trace_limitCohomology T).2.2.1.subset
    fun i hi => ?_
  by_contra h
  have : Subsingleton (limitCohomology T i) := not_nontrivial_iff_subsingleton.mp h
  have : Subsingleton (limit (S i) : ModuleCat.{v} ℤ_[ℓ]) :=
    (limitLinearEquivLimitCohomology T i (e i)).subsingleton
  exact not_nontrivial (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (limit (S i) : ModuleCat.{v} ℤ_[ℓ])) hi

/-- **Tag 03V4, part (3), for `lim S`.**  If, in every degree, an inverse system `S i` with an
endomorphism `σ i` is isomorphic to `n ↦ Hⁱ(Kₙ)` with `n ↦ Hⁱ(πₙ)`, then the alternating sum of
the traces of the endomorphisms induced on `ℚ_[ℓ] ⊗ lim S i` is the ℓ-adic trace `t_∞` of the
tower. -/
public theorem alternating_trace_rational_limit_of_iso {S : ℤ → ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]}
    (σ : ∀ i, S i ⟶ S i) (e : ∀ i, S i ≅ levelCohomologySystem T i)
    (hσ : ∀ i, σ i ≫ (e i).hom = (e i).hom ≫ levelCohomologyEndoSystem T i) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (limit (S i) : ModuleCat.{v} ℤ_[ℓ]))
          (LinearMap.baseChange ℚ_[ℓ] (limMap (σ i)).hom) =
      (padicTrace T : ℚ_[ℓ]) := by
  rw [← alternating_trace_eq_padicTrace T]
  refine finsum_congr fun i => ?_
  congr 1
  let E := limitLinearEquivLimitCohomology T i (e i)
  have hconj : (limMap (σ i)).hom = E.symm.toLinearMap ∘ₗ limitCohomologyEndo T i ∘ₗ
      E.toLinearMap := by
    ext x
    apply E.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply]
    exact congrArg (fun g => g.hom x)
      (limMap_comp_limitIsoLimitCohomology_hom T i (e i) (σ i) (hσ i))
  have hbc : LinearMap.baseChange ℚ_[ℓ] (limMap (σ i)).hom =
      ((LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ E).symm).conj
        (LinearMap.baseChange ℚ_[ℓ] (limitCohomologyEndo T i)) := by
    rw [hconj, LinearEquiv.conj_apply]
    ext x
    simp [LinearEquiv.baseChange]
  rw [hbc, LinearMap.trace_conj']

end Stacks.InverseSystem

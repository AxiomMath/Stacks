module

public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple

/-!
# Quasi-coherent submodules over an affine scheme are compared on global sections

On an affine scheme `X`, a quasi-coherent submodule `A` of an `𝒪_X`-module `M` lies in a
submodule `B` as soon as its global sections do: over a basic open `D(g)` every section of `A` is
`g⁻ⁿ` times the restriction of a global section (Stacks 01P0 for `X` itself), and membership in
`B` is local.

## Main results

* `AlgebraicGeometry.Scheme.Modules.submodule_le_of_obj_top_le`.

## References

* [Stacks Project, Tag 01P0](https://stacks.math.columbia.edu/tag/01P0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsAffine X] {M : X.Modules}

/-- **A quasi-coherent submodule of a module over an affine scheme lies in a submodule as soon as
its global sections do.** -/
theorem submodule_le_of_obj_top_le {A B : M.Submodule}
    [(A.toSheafOfModules : X.Modules).IsQuasicoherent]
    (h : A.obj (op ⊤) ≤ B.obj (op ⊤)) : A ≤ B := by
  refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 ?_)
  rintro ⟨U⟩ x hx
  refine B.isSheaf x fun p hp => ?_
  obtain ⟨g, hD, hpD⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨p, hp⟩ (Set.mem_univ p)
  have hVU : (⊤ : X.Opens) ⊓ X.basicOpen g ≤ U := inf_le_right.trans hD
  let y : Γ((A.toSheafOfModules : X.Modules), (⊤ : X.Opens) ⊓ X.basicOpen g) :=
    ⟨M.val.map (homOfLE hVU).op x, A.map (homOfLE hVU).op hx⟩
  obtain ⟨z, n, hz⟩ := exists_res_eq_pow_smul_of_isCompact (A.toSheafOfModules : X.Modules) g
    (W := ⊤) (by simpa using isQuasiSeparated_univ (α := X)) ⊤ (by simpa using isCompact_univ)
    le_rfl y
  have hu : IsUnit (X.presheaf.map (homOfLE (inf_le_left :
      (⊤ : X.Opens) ⊓ X.basicOpen g ≤ ⊤)).op g) := by
    convert (X.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen g).map
      (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ X.basicOpen g ≤
        X.basicOpen g)).op).hom using 1
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp
      (homOfLE (X.basicOpen_le g)).op
      (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ X.basicOpen g ≤ X.basicOpen g)).op) g
  refine ⟨_, homOfLE hVU, ?_, ⟨Set.mem_univ p, hpD⟩⟩
  refine (Submodule.smul_mem_iff_of_isUnit _ (hu.pow n)).1 ?_
  have hzB' : ((Scheme.Modules.presheaf (A.toSheafOfModules : X.Modules)).map
      (homOfLE (inf_le_left : (⊤ : X.Opens) ⊓ X.basicOpen g ≤ ⊤)).op z).1 ∈
      B.obj (op ((⊤ : X.Opens) ⊓ X.basicOpen g)) := B.map _ (h z.2)
  rwa [congrArg Subtype.val hz] at hzB'

end AlgebraicGeometry.Scheme.Modules

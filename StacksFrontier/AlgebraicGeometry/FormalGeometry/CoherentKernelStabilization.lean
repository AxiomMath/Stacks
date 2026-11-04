module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.SubmoduleAscendingChain
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerSections
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# The kernels of the powers of an endomorphism of a coherent module stabilize

Let `X` be a Noetherian scheme, `ℱ` a coherent `𝒪_X`-module and `g : ℱ ⟶ ℱ` any endomorphism.
The subsheaves `ℱ[gⁿ] = Ker(gⁿ)` grow with `n`, and this file proves that they stop growing: there
is a `c ≥ 1` with `ℱ[g^c] = ℱ[gⁿ]` for every `n ≥ c`, in the strong form that the canonical
inclusion `ℱ[g^c] ⟶ ℱ[gⁿ]` is an isomorphism. That is the predicate
`Stacks.InverseSystems.EndIterate.Stabilizes`.

That predicate is the hypothesis `hstab` carried by every `r = 1` result of this directory —
[Stacks, Tags 0H3D, 0H3E, 0BLD] in
`Topology/Sheaves/Cohomology/InverseSystems/QuotientTowerFormalFunctions.lean`,
`FormalGeometry/PrincipalQuotientTowerSections.lean`,
`FormalGeometry/PrincipalQuotientTowerDerivedCompletion.lean` and
`FormalGeometry/PrincipalQuotientTowerDiagram.lean` — and nothing proved it before. It is an
"exists stabilizing data" hypothesis, so a tag may not acquire it: it has to be discharged, and
`Stacks.Algebraization.stabilizes_mulF_of_isCoherent` below discharges it for the data those
results are about, a coherent module on a Noetherian scheme.

## Main results

* `Stacks.Algebraization.stabilizes_of_isCoherent` — for an arbitrary endomorphism of a coherent
  module on a Noetherian scheme the kernels of the iterates stabilize.
* `Stacks.Algebraization.stabilizes_mulF_of_isCoherent` — the same for multiplication by the
  image of an element of a base ring, which is the shape
  `Stacks.Algebraization.PrincipalQuotientTower.mulF` in which the `r = 1` results consume it.
* `Stacks.Algebraization.isIso_kerIncl_of_kernelSubmodule_eq` — two iterates with the same
  sectionwise kernel have an invertible comparison between their categorical kernels.
* `Stacks.Algebraization.monotone_kernelSubmodule_iterate` — the sectionwise kernels of the
  iterates grow.

## The argument

Nothing is local or affine here: the ascending chain condition for quasi-coherent submodules of a
coherent module on a Noetherian scheme is already available, as
`AlgebraicGeometry.exists_eventually_constant_quasicoherentSubmodules` ([Stacks, Tag 01Y8]), and
it is the only input. Applied to `n ↦ Ker(gⁿ)` it produces a level `n₀` past which the chain is
constant, and `c = max n₀ 1` is the constant the predicate asks for.

Two things have to be supplied. The chain must be *monotone*, which is
`monotone_kernelSubmodule_iterate`: `gⁿ⁺ᵈ = gⁿ ≫ gᵈ`, so a section killed by `gⁿ` is killed by
`gⁿ⁺ᵈ`. And its terms must be *quasi-coherent*, which is `isQuasicoherent_kernelSubmodule_self`:
the sectionwise kernel `Stacks.Algebraization.kernelSubmodule` is carried by
`Stacks.Algebraization.kernelSubmoduleIso` to the categorical kernel, which is quasi-coherent
because quasi-coherent modules on a scheme are closed under kernels.

Equality of two members of the chain is an equality of submodules, while `Stabilizes` asks for
the invertibility of `Stacks.InverseSystems.EndIterate.kerIncl`, a morphism of *categorical*
kernels. `isIso_kerIncl_of_kernelSubmodule_eq` bridges the two: transporting
`kernelSubmoduleIso` along the equality gives an isomorphism of the categorical kernels over
their inclusions into `ℱ`, and `kerIncl` lies over the same pair of inclusions, so the two agree
by cancelling the monomorphism `kernel.ι`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` and the two
presentations carry separately declared category instances, so a composite mixing them is not
type-correct at the transparency `rw` builds its motive at: `𝟙` and `Category.id_comp` are
exactly where that bites. The chain of identifications inside
`isIso_kerIncl_of_kernelSubmodule_eq` is therefore assembled in term mode out of `congrArg`,
`Category.assoc` and `Iso.hom_inv_id_assoc`, with no rewriting.

`Stabilizes` is stated for an arbitrary abelian category, and what is proved here uses the
scheme only through the ascending chain condition, so the endomorphism is arbitrary: nothing
below mentions multiplication by a scalar until the corollary, where
`Stacks.Algebraization.PrincipalQuotientTower.mulF` is such an endomorphism of a coherent module
and the general theorem applies to it unchanged.

## References

* [Stacks Project, Tag 01Y8](https://stacks.math.columbia.edu/tag/01Y8)
* [Stacks Project, Tag 0H3D](https://stacks.math.columbia.edu/tag/0H3D)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.InverseSystems.EndIterate

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-- The sectionwise kernel of a morphism is contained in the sectionwise kernel of any composite
out of it: a section killed by `f` is killed by `f ≫ h`. -/
public lemma kernelSubmodule_le_kernelSubmodule_comp {X : Scheme.{u}} {F G H : X.Modules}
    (f : F ⟶ G) (h : G ⟶ H) :
    kernelSubmodule f ≤ kernelSubmodule (f ≫ h) := by
  intro U x hx
  rw [kernelSubmodule_toSubmodule_obj] at hx
  rw [kernelSubmodule_toSubmodule_obj]
  have hv : ((f ≫ h).val.app U).hom x = (h.val.app U).hom ((f.val.app U).hom x) := rfl
  exact LinearMap.mem_ker.mpr
    (by rw [hv, show (f.val.app U).hom x = 0 from LinearMap.mem_ker.mp hx, map_zero])

/-- **The kernels of the iterates of an endomorphism grow.** -/
public lemma monotone_kernelSubmodule_iterate {X : Scheme.{u}} {F : X.Modules} (g : F ⟶ F) :
    Monotone fun k : ℕ => kernelSubmodule (iterate g k) := by
  intro k l hkl
  obtain ⟨d, rfl⟩ := Nat.le.dest hkl
  have hle := kernelSubmodule_le_kernelSubmodule_comp (iterate g k) (iterate g d)
  rwa [← iterate_add g k d] at hle

/-- **The sectionwise kernel of a morphism of quasi-coherent modules is quasi-coherent**, at an
endomorphism. It is carried by `Stacks.Algebraization.kernelSubmoduleIso` to the categorical
kernel, and quasi-coherent modules on a scheme are closed under kernels. -/
public lemma isQuasicoherent_kernelSubmodule_self {X : Scheme.{u}} {F : X.Modules}
    [F.IsQuasicoherent] (g : F ⟶ F) :
    ((kernelSubmodule g).toSheafOfModules : X.Modules).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (kernelSubmoduleIso g).symm
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel g)

/-- Transporting a submodule's inclusion along an equality of submodules gives that submodule's
inclusion. -/
public lemma eqToHom_toSheafOfModules_comp_ι {X : Scheme.{u}} {F : X.Modules}
    {P Q : F.Submodule} (h : P = Q) :
    eqToHom (congrArg (fun R : F.Submodule => (R.toSheafOfModules : X.Modules)) h) ≫
        (Q.ι : (Q.toSheafOfModules : X.Modules) ⟶ F) = P.ι := by
  subst h
  simp only [eqToHom_refl]
  exact Category.id_comp _

/-- **Two iterates with the same sectionwise kernel have an invertible comparison of categorical
kernels.** The isomorphism obtained by transporting `Stacks.Algebraization.kernelSubmoduleIso`
along the equality lies over the two inclusions into `ℱ`, and so does
`Stacks.InverseSystems.EndIterate.kerIncl`, so they agree by cancelling the monomorphism
`kernel.ι`. -/
public theorem isIso_kerIncl_of_kernelSubmodule_eq {X : Scheme.{u}} {F : X.Modules} (g : F ⟶ F)
    {c n : ℕ} (hcn : c ≤ n)
    (heq : kernelSubmodule (iterate g c) = kernelSubmodule (iterate g n)) :
    IsIso (kerIncl g hcn) := by
  have hco := congrArg (fun R : F.Submodule => (R.toSheafOfModules : X.Modules)) heq
  let e : (kernel (C := X.Modules) (iterate g c)) ≅ kernel (C := X.Modules) (iterate g n) :=
    (kernelSubmoduleIso (iterate g c)).symm ≪≫ eqToIso hco ≪≫ kernelSubmoduleIso (iterate g n)
  have hι : ∀ k, (kernelSubmoduleIso (iterate g k)).inv ≫ (kernelSubmodule (iterate g k)).ι =
      kernel.ι (C := X.Modules) (iterate g k) := fun k => kernelSubmoduleCorestrict_comp_ι _
  have hA : (kernelSubmoduleIso (iterate g n)).hom ≫
      kernel.ι (C := X.Modules) (iterate g n) = (kernelSubmodule (iterate g n)).ι :=
    (congrArg (fun t => (kernelSubmoduleIso (iterate g n)).hom ≫ t) (hι n).symm).trans
      (Iso.hom_inv_id_assoc _ _)
  have he : e.hom = (kernelSubmoduleIso (iterate g c)).inv ≫
      (eqToHom hco ≫ (kernelSubmoduleIso (iterate g n)).hom) := rfl
  have hgoal : e.hom ≫ kernel.ι (C := X.Modules) (iterate g n) =
      kernel.ι (C := X.Modules) (iterate g c) :=
    (congrArg (fun t => t ≫ kernel.ι (C := X.Modules) (iterate g n)) he).trans
      (((Category.assoc _ _ _).trans
        (congrArg (fun t => (kernelSubmoduleIso (iterate g c)).inv ≫ t)
          (Category.assoc _ _ _))).trans
        ((congrArg (fun t => (kernelSubmoduleIso (iterate g c)).inv ≫ eqToHom hco ≫ t) hA).trans
          ((congrArg (fun t => (kernelSubmoduleIso (iterate g c)).inv ≫ t)
            (eqToHom_toSheafOfModules_comp_ι heq)).trans (hι c))))
  have hki : kerIncl g hcn ≫ kernel.ι (C := X.Modules) (iterate g n) =
      kernel.ι (C := X.Modules) (iterate g c) := kernel.lift_ι _ _ _
  have hfin : kerIncl g hcn = e.hom :=
    (cancel_mono (kernel.ι (C := X.Modules) (iterate g n))).1 (hki.trans hgoal.symm)
  rw [hfin]
  infer_instance

/-- **The kernels of the iterates of an endomorphism of a coherent module on a Noetherian scheme
stabilize.** There is a `c ≥ 1` such that for every `n ≥ c` the canonical inclusion
`ℱ[g^c] ⟶ ℱ[gⁿ]` is an isomorphism.

This is the predicate `Stacks.InverseSystems.EndIterate.Stabilizes`, carried as a hypothesis by
every `r = 1` result of this directory and proved nowhere else. The only input is the ascending
chain condition of [Stacks, Tag 01Y8] for quasi-coherent submodules of a coherent module on a
Noetherian scheme, `AlgebraicGeometry.exists_eventually_constant_quasicoherentSubmodules`; the
chain is `n ↦ Ker(gⁿ)`, monotone by `monotone_kernelSubmodule_iterate` and quasi-coherent by
`isQuasicoherent_kernelSubmodule_self`. -/
public theorem stabilizes_of_isCoherent {X : Scheme.{u}} [IsNoetherian X] {F : X.Modules}
    [F.IsCoherent] (g : F ⟶ F) : Stabilizes g := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨n₀, hn₀⟩ := AlgebraicGeometry.exists_eventually_constant_quasicoherentSubmodules X F
    (fun k => kernelSubmodule (iterate g k))
    (fun k => isQuasicoherent_kernelSubmodule_self (iterate g k))
    (monotone_kernelSubmodule_iterate g)
  refine ⟨max n₀ 1, le_max_right _ _, fun n hn => ?_⟩
  exact isIso_kerIncl_of_kernelSubmodule_eq g hn
    ((hn₀ (max n₀ 1) (le_max_left _ _)).trans
      (hn₀ n ((le_max_left n₀ 1).trans hn)).symm)

/-- **The `f`-power torsion of a coherent module on a Noetherian scheme stabilizes.** This is
`stabilizes_of_isCoherent` at `Stacks.Algebraization.PrincipalQuotientTower.mulF`, multiplication
by the image of `f ∈ A` in `Γ(X, 𝒪_X)`, which is the shape in which the `r = 1` results of
[Stacks, Tags 0H3D, 0H3E and 0BLD] carry the hypothesis `hstab`. -/
public theorem stabilizes_mulF_of_isCoherent {X : Scheme.{u}} [IsNoetherian X] {A : Type u}
    [CommRing A]
    (ρ : A →+*
      (structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.toRingedSpace.carrier)))
    (f : A) (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hF : (F : X.Modules).IsCoherent) :
    Stabilizes (PrincipalQuotientTower.mulF X ρ f F) :=
  @stabilizes_of_isCoherent X inferInstance (F : X.Modules) hF
    (PrincipalQuotientTower.mulF X ρ f F)

end Stacks.Algebraization

end

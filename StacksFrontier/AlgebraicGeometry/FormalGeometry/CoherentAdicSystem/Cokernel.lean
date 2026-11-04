module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections

/-!
# Cokernels of coherent adic systems

Let `X` be a scheme, `ℐ` a quasi-coherent ideal sheaf on `X`, and `f : (F_n) ⟶ (G_n)` a morphism
of coherent adic systems along `ℐ`. Forming the cokernel at each level produces an inverse system
`(C_n)` which is again a coherent adic system, and which is the cokernel of `f` in the category
`Coh(X, ℐ)`. This is the half of [Stacks, Tag 087X] which needs no finiteness hypothesis; it is
also the input to the exactness statements of [Stacks, Tag 087Y], because the cokernel formed in
`Coh(X, ℐ)` is computed levelwise and may therefore be analysed one term at a time.

Each of the three clauses of `Stacks.Coherent.IsCoherentAdicSystem` is verified for `(C_n)`
separately.

* Coherence: `C_n` is the cokernel of `F_n ⟶ G_n`, since colimits in a functor category are
  computed levelwise, and coherent modules on a ringed space are closed under cokernels.
* Annihilation by `ℐ ⁿ⁺¹`: the projection `G_n ⟶ C_n` is an epimorphism of quasi-coherent modules,
  hence surjective on the sections over an affine open `U`, so every section of `C_n` over `U` is
  the image of one of `G_n`, which `ℐ(U) ⁿ⁺¹` already kills.
* The transition `C_{n+1} ⟶ C_n` is the quotient by `ℐ ⁿ⁺¹ C_{n+1}`: it kills that subsheaf by the
  same lifting argument, and a morphism `C_{n+1} ⟶ T` killing `ℐ ⁿ⁺¹ C_{n+1}` descends uniquely,
  first along `G_{n+1} ⟶ G_{n+1} / ℐ ⁿ⁺¹ G_{n+1} ≅ G_n` and then along `G_n ⟶ C_n`, the second
  step being available because the composite `F_n ⟶ G_n ⟶ T` vanishes after the epimorphism
  `F_{n+1} ⟶ F_n`.

Finally the inclusion of `Coh(X, ℐ)` into all inverse systems *creates* the cokernel of `f`, which
is what makes the cokernel in `Coh(X, ℐ)` exist, be preserved by the inclusion, and be the
levelwise one.

## Main definitions

* `Stacks.Coherent.coherentAdicCokernel` — the levelwise cokernel, as an object of `Coh(X, ℐ)`,
  with `Stacks.Coherent.coherentAdicCokernelπ` the projection onto it.
* `Stacks.Coherent.cokernelObjIso` — the identification of the value at `n` of the cokernel of a
  morphism of inverse systems with the cokernel of its `n`-th component.
* `Stacks.Coherent.cokernelDesc` — the descent to `C_n` of a morphism out of `C_{n+1}` which
  annihilates `ℐ ⁿ⁺¹`, built from `Stacks.Coherent.cokernelQuotientDesc` and
  `Stacks.Coherent.cokernelDescAux`.
* `Stacks.Coherent.coherentAdicCokernelIsColimit` — the cokernel cofork of
  `coherentAdicCokernelπ`, exhibited as a colimit.

## Main results

* `Stacks.Coherent.isCoherentAdicSystem_cokernel` — **the levelwise cokernel of a morphism of
  coherent adic systems is a coherent adic system**, assembled from
  `Stacks.Coherent.isCoherent_cokernel_obj`,
  `Stacks.Coherent.idealPowerMultiple_cokernel_obj_eq_bot` and
  `Stacks.Coherent.cokernelMapSuccIsColimit`.
* `Stacks.Coherent.coherentAdicCokernel_isCokernel` — the universal property of the cokernel in
  `Coh(X, ℐ)`, in the elementary `∃!` form.
* `Stacks.Coherent.hasCokernels_coherentAdicSystems` — `Coh(X, ℐ)` has all cokernels.
* `Stacks.Coherent.preservesColimitParallelPairι` — **the cokernel in `Coh(X, ℐ)` is the levelwise
  one**: the inclusion into `ℕᵒᵖ ⥤ X.Modules` preserves it.
* `Stacks.Coherent.idealPowerMultiple_ι_comp_eq_zero_of_app_smul` and
  `Stacks.Coherent.app_smul_eq_zero_of_idealPowerMultiple_ι_comp_eq_zero` — the two directions of
  the affine-local criterion for a morphism to annihilate `ℐ ⁿ M`.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the Stacks source's
`F_{n+1}`, which is why the annihilating exponent at `n` is `n + 1`.

Zero morphisms out of a subsheaf are written `(0 : _ ⟶ N)`. The inclusion
`SheafOfModules.Submodule.ι` is typed at `SheafOfModules X.ringCatSheaf`, the other of the two
presentations of the category of `𝒪_X`-modules, and the numeral `0` is not elaborated at that
spelling unless its target is left to be found by unification with the composite.

For the same reason the composites that mix a submodule inclusion with a morphism of `X.Modules`
are manipulated in term mode, with `congrArg` and `Category.assoc`, rather than by `rw`: the
hom types produced by `SheafOfModules.Submodule.ι` and by `CategoryTheory.Functor.map` resolve
`X.ringCatSheaf` through different but definitionally equal spellings of its type, so a rewrite
motive built from one is not type-correct at the transparency `rw` uses, while `Eq.trans` and
`congrArg` need only the definitional equality.
`Stacks.Coherent.map_succ_comp_quotientIso_inv` exists so that the descent lemmas can be stated
and proved without ever reassociating such a composite.

Each transition map of the levelwise cokernel is an epimorphism, so
`CategoryTheory.Limits.CokernelCofork.IsColimit.ofπ'` is used for
`Stacks.Coherent.cokernelMapSuccIsColimit`: only the factorization has to be produced, and
uniqueness is free.

The existence and the preservation of the cokernel in `Coh(X, ℐ)` both come from
`Stacks.Coherent.createsColimitParallelPairι`, which is
`CategoryTheory.Limits.createsColimitFullSubcategoryInclusion'` applied to the levelwise cokernel
cofork. Phrasing it as a created colimit avoids having to know in advance that
`Stacks.Coherent.IsCoherentAdicSystem` is closed under isomorphisms.

The coherence universe is written explicitly as `SheafOfModules.IsCoherent.{u}`, as in
`Stacks.Coherent.IsCoherentAdicSystem` itself, and the coherence predicate is spelled
`_root_.SheafOfModules.IsCoherent` because inside the `Stacks` namespace the unqualified name
resolves to `Stacks.SheafOfModules.IsCoherent`, a different constant.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087Y](https://stacks.math.columbia.edu/tag/087Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### Morphisms annihilating an ideal-power multiple -/

section Annihilation

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules}

/-- A morphism of sheaves of modules annihilates the subsheaf `ℐ ⁿ M` as soon as it annihilates
every section `a • y` with `a` a section of `ℐ ⁿ` and `y` a section of `M` over an affine open. -/
public theorem idealPowerMultiple_ι_comp_eq_zero_of_app_smul (g : M ⟶ N)
    (h : ∀ U : X.affineOpens, ∀ a ∈ I.ideal U ^ n, ∀ y : Γ(M, U), g.app U.1 (a • y) = 0) :
    (idealPowerMultiple I n M).ι ≫ g = (0 : _ ⟶ N) := by
  have hker : idealPowerMultiple I n M ≤ kernelSubmodule g := by
    refine (idealPowerMultiple_le_iff I n M _).2 fun U => ?_
    rw [kernelSubmodule_toSubmodule_obj]
    exact Submodule.smul_le.2 fun a ha y _ => h U a ha y
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  have hx := hker (op V) x.property
  rw [kernelSubmodule_toSubmodule_obj] at hx
  exact hx

/-- Conversely, a morphism annihilating `ℐ ⁿ M` annihilates every section `a • y` over an affine
open: there the sections of `ℐ ⁿ M` are exactly `ℐ(U) ⁿ Γ(M, U)`. -/
public theorem app_smul_eq_zero_of_idealPowerMultiple_ι_comp_eq_zero [M.IsQuasicoherent]
    {g : M ⟶ N} (hg : (idealPowerMultiple I n M).ι ≫ g = (0 : _ ⟶ N))
    (U : X.affineOpens) {a : Γ(X, U)} (ha : a ∈ I.ideal U ^ n) (y : Γ(M, U)) :
    g.app U.1 (a • y) = 0 := by
  have hmem : a • y ∈ (idealPowerMultiple I n M).toSubmodule.obj (op U.1) := by
    rw [idealPowerMultiple_toSubmodule_obj_affine I n M U]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  exact congrArg (fun t : ((idealPowerMultiple I n M).toSheafOfModules ⟶ N) =>
    Scheme.Modules.Hom.app t U.1 ⟨a • y, hmem⟩) hg

/-- Precomposing with an epimorphism of quasi-coherent modules does not change whether a morphism
annihilates `ℐ ⁿ`-multiples. -/
private theorem idealPowerMultiple_ι_comp_epi_comp_eq_zero_iff {P : X.Modules}
    [P.IsQuasicoherent] [M.IsQuasicoherent] (p : P ⟶ M) [Epi p] (h : M ⟶ N) :
    (idealPowerMultiple I n P).ι ≫ p ≫ h = (0 : _ ⟶ N) ↔
      (idealPowerMultiple I n M).ι ≫ h = (0 : _ ⟶ N) := by
  constructor
  · intro H
    refine idealPowerMultiple_ι_comp_eq_zero_of_app_smul I n _ fun U a ha x => ?_
    obtain ⟨y, rfl⟩ := AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen p U.2 x
    exact (congrArg (fun z => Scheme.Modules.Hom.app h U.1 z)
      (Scheme.Modules.Hom.app_smul p a y).symm).trans
      (app_smul_eq_zero_of_idealPowerMultiple_ι_comp_eq_zero I n H U ha y)
  · intro H
    refine idealPowerMultiple_ι_comp_eq_zero_of_app_smul I n _ fun U a ha y => ?_
    exact (congrArg (fun z => Scheme.Modules.Hom.app h U.1 z)
      (Scheme.Modules.Hom.app_smul p a y)).trans
      (app_smul_eq_zero_of_idealPowerMultiple_ι_comp_eq_zero I n H U ha _)

end Annihilation

/-! ### Levelwise cokernels of inverse systems -/

section Levelwise

variable {X : Scheme.{u}} {F G : ℕᵒᵖ ⥤ X.Modules}

/-- The value at an index of the cokernel of a morphism of inverse systems is the cokernel of its
component there: colimits in a functor category are computed levelwise. -/
public def cokernelObjIso (f : F ⟶ G) (n : ℕᵒᵖ) :
    (cokernel f).obj n ≅ cokernel (f.app n) :=
  PreservesCokernel.iso ((evaluation ℕᵒᵖ X.Modules).obj n) f

/-- Under `cokernelObjIso`, the component of the projection onto the cokernel is the projection
onto the cokernel of the component. -/
public theorem app_comp_cokernelObjIso_hom (f : F ⟶ G) (n : ℕᵒᵖ) :
    (cokernel.π f).app n ≫ (cokernelObjIso f n).hom = cokernel.π (f.app n) :=
  PreservesCokernel.π_iso_hom ((evaluation ℕᵒᵖ X.Modules).obj n) f

/-- Every component of the projection onto a levelwise cokernel is an epimorphism. -/
public instance epi_cokernel_π_app (f : F ⟶ G) (n : ℕᵒᵖ) : Epi ((cokernel.π f).app n) := by
  have h : cokernel.π (f.app n) ≫ (cokernelObjIso f n).inv = (cokernel.π f).app n := by
    rw [← app_comp_cokernelObjIso_hom f n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← h]
  infer_instance

end Levelwise

/-! ### The transition maps of a coherent adic system -/

section Transition

variable {X : Scheme.{u}} (I : X.IdealSheafData) {H : ℕᵒᵖ ⥤ X.Modules}

/-- The transition map of a coherent adic system, followed by the inverse of the identification of
its target with a quotient, is the projection onto that quotient. -/
public theorem map_succ_comp_quotientIso_inv (hH : IsCoherentAdicSystem I H) (n : ℕ) :
    H.map (homOfLE (Nat.le_succ n)).op ≫ (hH.quotientIso n).inv =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) (H.obj (op (n + 1)))).ι :=
  (congrArg (fun t => t ≫ (hH.quotientIso n).inv)
      (hH.cokernel_π_comp_quotientIso n)).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => cokernel.π (C := X.Modules)
            (idealPowerMultiple I (n + 1) (H.obj (op (n + 1)))).ι ≫ t)
          (hH.quotientIso n).hom_inv_id).trans
        (Category.comp_id _)))

/-- A transition map of a coherent adic system annihilates the ideal-power multiple it divides
out: it is the projection onto that quotient, followed by an isomorphism. -/
public theorem idealPowerMultiple_ι_comp_map_succ_eq_zero (hH : IsCoherentAdicSystem I H)
    (n : ℕ) :
    (idealPowerMultiple I (n + 1) (H.obj (op (n + 1)))).ι ≫
      H.map (homOfLE (Nat.le_succ n)).op = (0 : _ ⟶ H.obj (op n)) := by
  rw [← hH.cokernel_π_comp_quotientIso n]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (hH.quotientIso n).hom) (cokernel.condition _)).trans zero_comp)

end Transition

/-! ### The levelwise cokernel is a coherent adic system -/

section Cokernel

variable {X : Scheme.{u}} (I : X.IdealSheafData) {F G : CoherentAdicSystems I} (f : F ⟶ G)

/-- Each term of the levelwise cokernel of a morphism of coherent adic systems is coherent:
coherent modules are closed under cokernels and the cokernel is computed levelwise. -/
public theorem isCoherent_cokernel_obj (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} ((cokernel f.hom).obj (op n)) := by
  have hF : _root_.SheafOfModules.IsCoherent.{u} (F.obj.obj (op n)) := F.property.isCoherent n
  have hG : _root_.SheafOfModules.IsCoherent.{u} (G.obj.obj (op n)) := G.property.isCoherent n
  have hser : ObjectProperty.IsWeakSerreClass
      (fun M : X.Modules => _root_.SheafOfModules.IsCoherent.{u} M) :=
    _root_.SheafOfModules.coherentModules_isWeakSerreClass
  exact (show ObjectProperty X.Modules from
      fun M => _root_.SheafOfModules.IsCoherent.{u} M).prop_of_iso
    (cokernelObjIso f.hom (op n)).symm
    (_root_.SheafOfModules.cokernel_isCoherent (f.hom.app (op n)))

/-- Each term of the levelwise cokernel of a morphism of coherent adic systems is quasi-coherent,
being coherent. -/
public theorem isQuasicoherent_cokernel_obj (n : ℕ) :
    ((cokernel f.hom).obj (op n)).IsQuasicoherent :=
  have := isCoherent_cokernel_obj I f n
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    ((cokernel f.hom).obj (op n))).1

/-- The projections onto the levelwise cokernel commute with the transition maps. -/
public theorem cokernel_π_app_comp_map_succ (n : ℕ) :
    (cokernel.π f.hom).app (op (n + 1)) ≫
        (cokernel f.hom).map (homOfLE (Nat.le_succ n)).op =
      G.obj.map (homOfLE (Nat.le_succ n)).op ≫ (cokernel.π f.hom).app (op n) :=
  ((cokernel.π f.hom).naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The `n`-th term of the levelwise cokernel is annihilated by `ℐ ⁿ⁺¹`: over an affine open every
section of it lifts to `G_n`, which `ℐ(U) ⁿ⁺¹` already annihilates. -/
public theorem idealPowerMultiple_cokernel_obj_eq_bot (n : ℕ) :
    idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op n)) = ⊥ := by
  have hG : (G.obj.obj (op n)).IsQuasicoherent := G.property.isQuasicoherent n
  have hC : ((cokernel f.hom).obj (op n)).IsQuasicoherent := isQuasicoherent_cokernel_obj I f n
  refine le_antisymm ((idealPowerMultiple_le_iff _ _ _ _).2 fun U => ?_) bot_le
  refine Submodule.smul_le.2 fun a ha x _ => ?_
  obtain ⟨y, hy⟩ := AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen
    ((cokernel.π f.hom).app (op n)) U.2 x
  subst hy
  have hzero : a • y = 0 :=
    (Submodule.mem_bot _).1
      ((idealPower_smul_sections_eq_bot_of_idealPowerMultiple_eq_bot I (n + 1)
        (G.obj.obj (op n)) (G.property.idealPowerMultiple_eq_bot n) U).le
        (Submodule.smul_mem_smul ha Submodule.mem_top))
  have hax : a • ((cokernel.π f.hom).app (op n)).app U.1 y = 0 :=
    ((Scheme.Modules.Hom.app_smul ((cokernel.π f.hom).app (op n)) a y).symm.trans
      (congrArg (fun z => Scheme.Modules.Hom.app ((cokernel.π f.hom).app (op n)) U.1 z)
        hzero)).trans (map_zero _)
  rw [hax]
  exact Submodule.zero_mem _

/-! ### The universal property of the transition maps of the levelwise cokernel -/

/-- The transition map of the levelwise cokernel annihilates the ideal-power multiple that it must
divide out: over an affine open a section of the cokernel lifts to `G_{n+1}`, where the transition
map of `G` already kills the relevant multiples. -/
public theorem idealPowerMultiple_ι_comp_cokernel_map_eq_zero (n : ℕ) :
    (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫
        (cokernel f.hom).map (homOfLE (Nat.le_succ n)).op =
      (0 : _ ⟶ (cokernel f.hom).obj (op n)) := by
  have hG : (G.obj.obj (op (n + 1))).IsQuasicoherent := G.property.isQuasicoherent (n + 1)
  have hC : ((cokernel f.hom).obj (op (n + 1))).IsQuasicoherent :=
    isQuasicoherent_cokernel_obj I f (n + 1)
  refine (idealPowerMultiple_ι_comp_epi_comp_eq_zero_iff I (n + 1)
    ((cokernel.π f.hom).app (op (n + 1))) _).1 ?_
  exact (congrArg (fun t => (idealPowerMultiple I (n + 1) (G.obj.obj (op (n + 1)))).ι ≫ t)
    (cokernel_π_app_comp_map_succ I f n)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (cokernel.π f.hom).app (op n))
      (idealPowerMultiple_ι_comp_map_succ_eq_zero I G.property n)).trans zero_comp))

variable {T : X.Modules}

/-- A morphism out of the `(n+1)`-st term of the levelwise cokernel which annihilates `ℐ ⁿ⁺¹` pulls
back to a morphism out of `G_{n+1}` which annihilates `ℐ ⁿ⁺¹`. -/
public theorem idealPowerMultiple_ι_comp_cokernel_π_app_comp_eq_zero (n : ℕ)
    (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h =
      (0 : _ ⟶ T)) :
    (idealPowerMultiple I (n + 1) (G.obj.obj (op (n + 1)))).ι ≫
      ((cokernel.π f.hom).app (op (n + 1)) ≫ h) = (0 : _ ⟶ T) := by
  have hG : (G.obj.obj (op (n + 1))).IsQuasicoherent := G.property.isQuasicoherent (n + 1)
  have hC : ((cokernel f.hom).obj (op (n + 1))).IsQuasicoherent :=
    isQuasicoherent_cokernel_obj I f (n + 1)
  exact (idealPowerMultiple_ι_comp_epi_comp_eq_zero_iff I (n + 1)
    ((cokernel.π f.hom).app (op (n + 1))) h).2 hh

/-- The descent of such a morphism through the quotient `G_{n+1} / ℐ ⁿ⁺¹ G_{n+1}`. -/
public def cokernelQuotientDesc (n : ℕ) (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h =
      (0 : _ ⟶ T)) :
    idealPowerQuotient I (n + 1) (G.obj.obj (op (n + 1))) ⟶ T :=
  cokernel.desc _ ((cokernel.π f.hom).app (op (n + 1)) ≫ h)
    (idealPowerMultiple_ι_comp_cokernel_π_app_comp_eq_zero I f n h hh)

/-- The defining property of `cokernelQuotientDesc`. -/
public theorem cokernel_π_comp_cokernelQuotientDesc (n : ℕ)
    (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h =
      (0 : _ ⟶ T)) :
    cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) (G.obj.obj (op (n + 1)))).ι ≫
        cokernelQuotientDesc I f n h hh =
      (cokernel.π f.hom).app (op (n + 1)) ≫ h :=
  cokernel.π_desc _ _ _

/-- The descent to `G_n` of a morphism out of the `(n+1)`-st term of the levelwise cokernel which
annihilates `ℐ ⁿ⁺¹`, obtained from `cokernelQuotientDesc` by identifying `G_n` with the quotient of
`G_{n+1}` by `ℐ ⁿ⁺¹`. -/
public def cokernelDescAux (n : ℕ) (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h =
      (0 : _ ⟶ T)) :
    G.obj.obj (op n) ⟶ T :=
  (G.property.quotientIso n).inv ≫ cokernelQuotientDesc I f n h hh

/-- The descent `cokernelDescAux` undoes the transition map of `G`. -/
public theorem map_succ_comp_cokernelDescAux (n : ℕ)
    (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h =
      (0 : _ ⟶ T)) :
    G.obj.map (homOfLE (Nat.le_succ n)).op ≫ cokernelDescAux I f n h hh =
      (cokernel.π f.hom).app (op (n + 1)) ≫ h :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ cokernelQuotientDesc I f n h hh)
        (map_succ_comp_quotientIso_inv I G.property n)).trans
      (cokernel_π_comp_cokernelQuotientDesc I f n h hh))

/-- The descent `cokernelDescAux` is annihilated by the `n`-th component of `f`, so it descends
further to the `n`-th term of the levelwise cokernel. -/
public theorem app_comp_cokernelDescAux_eq_zero (n : ℕ)
    (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h =
      (0 : _ ⟶ T)) :
    f.hom.app (op n) ≫ cokernelDescAux I f n h hh = 0 := by
  have hepi : Epi (F.obj.map (homOfLE (Nat.le_succ n)).op) := F.property.epi_map_succ n
  refine (cancel_epi (F.obj.map (homOfLE (Nat.le_succ n)).op)).1 ?_
  rw [comp_zero, ← Category.assoc, f.hom.naturality (homOfLE (Nat.le_succ n)).op,
    Category.assoc, map_succ_comp_cokernelDescAux, ← Category.assoc,
    show f.hom.app (op (n + 1)) ≫ (cokernel.π f.hom).app (op (n + 1)) = 0 from
      congrArg (fun t : F.obj ⟶ cokernel f.hom => t.app (op (n + 1)))
        (cokernel.condition f.hom),
    zero_comp]

/-- The descent to the `n`-th term of the levelwise cokernel of a morphism out of its `(n+1)`-st
term which annihilates `ℐ ⁿ⁺¹`. -/
public def cokernelDesc (n : ℕ) (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h =
      (0 : _ ⟶ T)) :
    (cokernel f.hom).obj (op n) ⟶ T :=
  (cokernelObjIso f.hom (op n)).hom ≫
    cokernel.desc (f.hom.app (op n)) (cokernelDescAux I f n h hh)
      (app_comp_cokernelDescAux_eq_zero I f n h hh)

/-- The projection onto the `n`-th term of the levelwise cokernel, followed by `cokernelDesc`, is
the descent to `G_n`. -/
public theorem cokernel_π_app_comp_cokernelDesc (n : ℕ)
    (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h =
      (0 : _ ⟶ T)) :
    (cokernel.π f.hom).app (op n) ≫ cokernelDesc I f n h hh = cokernelDescAux I f n h hh :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ cokernel.desc (f.hom.app (op n)) (cokernelDescAux I f n h hh)
          (app_comp_cokernelDescAux_eq_zero I f n h hh))
        (app_comp_cokernelObjIso_hom f.hom (op n))).trans
      (cokernel.π_desc _ _ _))

/-- The transition map of the levelwise cokernel, followed by `cokernelDesc`, recovers the given
morphism. -/
public theorem map_succ_comp_cokernelDesc (n : ℕ)
    (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple I (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h =
      (0 : _ ⟶ T)) :
    (cokernel f.hom).map (homOfLE (Nat.le_succ n)).op ≫ cokernelDesc I f n h hh = h :=
  (cancel_epi ((cokernel.π f.hom).app (op (n + 1)))).1
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ cokernelDesc I f n h hh)
          (cokernel_π_app_comp_map_succ I f n)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => G.obj.map (homOfLE (Nat.le_succ n)).op ≫ t)
              (cokernel_π_app_comp_cokernelDesc I f n h hh)).trans
            (map_succ_comp_cokernelDescAux I f n h hh)))))

/-- Each transition map of the levelwise cokernel exhibits its target as the quotient of its
source by `ℐ ⁿ⁺¹`. -/
public def cokernelMapSuccIsColimit (n : ℕ) :
    IsColimit (CokernelCofork.ofπ ((cokernel f.hom).map (homOfLE (Nat.le_succ n)).op)
      (idealPowerMultiple_ι_comp_cokernel_map_eq_zero I f n)) :=
  have hepiG : Epi (G.obj.map (homOfLE (Nat.le_succ n)).op) := G.property.epi_map_succ n
  have hcc : Epi ((cokernel.π f.hom).app (op (n + 1)) ≫
      (cokernel f.hom).map (homOfLE (Nat.le_succ n)).op) := by
    rw [cokernel_π_app_comp_map_succ I f n]
    infer_instance
  have hepi : Epi ((cokernel f.hom).map (homOfLE (Nat.le_succ n)).op) :=
    epi_of_epi ((cokernel.π f.hom).app (op (n + 1))) _
  CokernelCofork.IsColimit.ofπ' ((cokernel f.hom).map (homOfLE (Nat.le_succ n)).op)
    (idealPowerMultiple_ι_comp_cokernel_map_eq_zero I f n)
    (fun {_} k hk => ⟨cokernelDesc I f n k hk, map_succ_comp_cokernelDesc I f n k hk⟩)

/-! ### The cokernel in the category of coherent adic systems -/

/-- **The levelwise cokernel of a morphism of coherent adic systems is a coherent adic system.** -/
public theorem isCoherentAdicSystem_cokernel : IsCoherentAdicSystem I (cokernel f.hom) :=
  ⟨isCoherent_cokernel_obj I f, idealPowerMultiple_cokernel_obj_eq_bot I f, fun k =>
    ⟨IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (C := X.Modules)
        (idealPowerMultiple I (k + 1) ((cokernel f.hom).obj (op (k + 1)))).ι)
      (cokernelMapSuccIsColimit I f k),
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel (C := X.Modules)
          (idealPowerMultiple I (k + 1) ((cokernel f.hom).obj (op (k + 1)))).ι)
        (cokernelMapSuccIsColimit I f k) WalkingParallelPair.one⟩⟩

/-- The cokernel of a morphism of coherent adic systems, formed levelwise. -/
public def coherentAdicCokernel : CoherentAdicSystems I :=
  ⟨cokernel f.hom, isCoherentAdicSystem_cokernel I f⟩

/-- The projection onto the cokernel of a morphism of coherent adic systems. -/
public def coherentAdicCokernelπ : G ⟶ coherentAdicCokernel I f :=
  ObjectProperty.homMk (cokernel.π f.hom)

/-- A morphism of coherent adic systems composed with the projection onto its cokernel
vanishes. -/
public theorem comp_coherentAdicCokernelπ : f ≫ coherentAdicCokernelπ I f = 0 :=
  ObjectProperty.hom_ext (IsCoherentAdicSystem I) (cokernel.condition f.hom)

/-- **The universal property of the cokernel of a morphism of coherent adic systems.** -/
public theorem coherentAdicCokernel_isCokernel :
    ∀ (K : CoherentAdicSystems I) (g : G ⟶ K), f.hom ≫ g.hom = 0 →
      ∃! k : coherentAdicCokernel I f ⟶ K,
        (coherentAdicCokernelπ I f).hom ≫ k.hom = g.hom := by
  intro K g hg
  refine ⟨ObjectProperty.homMk (cokernel.desc f.hom g.hom hg), cokernel.π_desc _ _ _, ?_⟩
  intro k hk
  exact ObjectProperty.hom_ext (IsCoherentAdicSystem I)
    ((cancel_epi (cokernel.π f.hom)).1 (hk.trans (cokernel.π_desc _ _ _).symm))

/-- The inclusion of the coherent adic systems into all inverse systems creates the cokernel of a
morphism of coherent adic systems, the levelwise cokernel being one. -/
public instance createsColimitParallelPairι :
    CreatesColimit (parallelPair f 0) (ObjectProperty.ι (IsCoherentAdicSystem I)) :=
  createsColimitFullSubcategoryInclusion' (parallelPair f 0)
    ((isColimitMapCoconeCoforkEquiv' (ObjectProperty.ι (IsCoherentAdicSystem I))
      (comp_coherentAdicCokernelπ I f)).symm (cokernelIsCokernel f.hom))
    (isCoherentAdicSystem_cokernel I f)

/-- The cokernel of a morphism of coherent adic systems exists. -/
public instance hasCokernel_coherentAdicSystems : HasCokernel f :=
  hasColimit_of_created (parallelPair f 0) (ObjectProperty.ι (IsCoherentAdicSystem I))

/-- **The cokernel in `Coh(X, ℐ)` is the levelwise cokernel.** -/
public instance preservesColimitParallelPairι :
    PreservesColimit (parallelPair f 0) (ObjectProperty.ι (IsCoherentAdicSystem I)) :=
  preservesColimit_of_createsColimit_and_hasColimit _ _

/-- The cokernel cofork of `coherentAdicCokernelπ` is a colimit: `coherentAdicCokernel` is the
cokernel of `f` in `Coh(X, ℐ)`. -/
public def coherentAdicCokernelIsColimit :
    IsColimit (CokernelCofork.ofπ (coherentAdicCokernelπ I f) (comp_coherentAdicCokernelπ I f)) :=
  isColimitOfReflects (ObjectProperty.ι (IsCoherentAdicSystem I))
    ((isColimitMapCoconeCoforkEquiv' (ObjectProperty.ι (IsCoherentAdicSystem I))
      (comp_coherentAdicCokernelπ I f)).symm (cokernelIsCokernel f.hom))

end Cokernel

/-- The category of coherent adic systems has all cokernels. -/
public instance hasCokernels_coherentAdicSystems {X : Scheme.{u}} (I : X.IdealSheafData) :
    HasCokernels (CoherentAdicSystems I) where
  has_colimit f := hasCokernel_coherentAdicSystems I f

end Stacks.Coherent

end

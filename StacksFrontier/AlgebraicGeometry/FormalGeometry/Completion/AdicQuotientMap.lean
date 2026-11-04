module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.IdealPowers
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic

/-!
# Ideal-power quotients as a functor of the module and of the ideal

Let `X` be a scheme and let `ℐ, 𝒥 ⊆ 𝒪_X` be quasi-coherent ideal sheaves. A morphism
`f : M ⟶ N` of sheaves of modules carries `𝒥 ⁿ M` into `𝒥 ⁿ N`, so whenever `𝒥 ⁿ ⊆ ℐ ᵐ` it
descends to a map
`M / 𝒥 ⁿ M ⟶ N / ℐ ᵐ N`
on the ideal-power quotients. This file constructs that map, shows that it preserves
epimorphisms, identities, composition and isomorphisms, and gives conditions under which it is an
isomorphism; in particular `M / 𝒥 ⁿ M` is annihilated by `𝒥 ⁿ`.

## Main definitions

* `Stacks.Algebraization.quotientMapOfComap` — the map `M / S ⟶ N / T` induced by a morphism
  `f : M ⟶ N` carrying the submodule `S` of `M` into the submodule `T` of `N`.
* `Stacks.Algebraization.idealPowerQuotientMap` — its ideal-power case
  `M / 𝒥 ⁿ M ⟶ N / ℐ ᵐ N`, available when `𝒥 ⁿ ⊆ ℐ ᵐ`.
* `Stacks.Algebraization.idealPowerQuotientDrop` — the exponent-lowering map
  `M / 𝒥 ᵐ M ⟶ M / 𝒥 ⁿ M` for `n ≤ m`.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_le_of_pow_le` — `𝒥 ⁿ M ⊆ ℐ ᵐ M` when `𝒥 ⁿ ⊆ ℐ ᵐ`.
* `Stacks.Algebraization.epi_cokernel_π_submodule_ι` — a quotient projection is an epimorphism,
  at the `X.Modules` presentation.
* `Stacks.Algebraization.idealPowerQuotientMap_id`, `idealPowerQuotientMap_comp`,
  `epi_idealPowerQuotientMap` and `isIso_idealPowerQuotientMap` — functoriality in the module.
* `Stacks.Algebraization.isQuasicoherent_idealPowerQuotient` and
  `isCoherent_idealPowerQuotient` — the quotient inherits quasi-coherence, and coherence over a
  locally Noetherian scheme.
* `Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot` — the ideal-power quotient
  is annihilated by the same ideal power.
* `Stacks.Algebraization.isIso_idealPowerQuotientMap_cokernel_π` and
  `isIso_idealPowerQuotientMap_of_cokernel_π_comp` — a quotient projection `M ⟶ M / 𝒥 ˢ M`
  becomes an isomorphism after dividing both sides by `ℐ ⁿ`, provided `𝒥 ˢ ⊆ ℐ ⁿ`.
* `Stacks.Algebraization.idealPowerQuotientIsoOfIsIso` and
  `Stacks.Algebraization.doubleIdealPowerQuotientIso` — the two resulting identifications, each
  packaged with its compatibility with the quotient projections.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared category instances. Composites below therefore name the
category with `(C := X.Modules)`, and submodule inclusions and the induced maps between subsheaves
are restated at that presentation (`submoduleMapOfComap`, `epi_cokernel_π_submodule_ι`).

## References

* [Stacks Project, Tag 0EHR](https://stacks.math.columbia.edu/tag/0EHR)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- The projection onto the quotient by a submodule is an epimorphism. -/
public instance epi_cokernel_π_submodule_ι {M : X.Modules} (S : M.Submodule) :
    Epi (cokernel.π (C := X.Modules) S.ι) := by
  change Epi (Cofork.ofπ (cokernel.π (C := X.Modules) S.ι)
    ((cokernel.condition (C := X.Modules) S.ι).trans zero_comp.symm)).π
  exact Cofork.IsColimit.epi (cokernelIsCokernel _)

/-! ### Comparing ideal-power multiples for different ideals -/

/-- A containment `𝒥 ⁿ ⊆ ℐ ᵐ` of ideal sheaves is inherited by the subsheaves they cut out of a
sheaf of modules: `𝒥 ⁿ M ⊆ ℐ ᵐ M`. -/
public theorem idealPowerMultiple_le_of_pow_le {I J : X.IdealSheafData} {m n : ℕ}
    (h : J ^ n ≤ I ^ m) (M : X.Modules) :
    idealPowerMultiple J n M ≤ idealPowerMultiple I m M := by
  refine (idealPowerMultiple_le_iff J n M _).2 fun U ↦ ?_
  refine (Submodule.smul_mono_left ?_).trans ((idealPowerMultiple_le_iff I m M _).1 le_rfl U)
  simpa using h U

/-- A morphism `f : M ⟶ N` carries `𝒥 ⁿ M` into the preimage of `ℐ ᵐ N` as soon as
`𝒥 ⁿ ⊆ ℐ ᵐ`. -/
public theorem idealPowerMultiple_le_sheafSubmoduleComap_of_pow_le {I J : X.IdealSheafData}
    {m n : ℕ} (h : J ^ n ≤ I ^ m) {M N : X.Modules} (f : M ⟶ N) :
    idealPowerMultiple J n M ≤
      AlgebraicGeometry.sheafSubmoduleComap f (idealPowerMultiple I m N) := by
  refine (idealPowerMultiple_le_sheafSubmoduleComap J n f (idealPowerMultiple J n N)
    le_rfl).trans (SheafOfModules.Submodule.le_iff.mpr fun U ↦ ?_)
  exact Submodule.comap_mono
    (SheafOfModules.Submodule.le_iff.mp (idealPowerMultiple_le_of_pow_le h N) U)

/-! ### Quotients are functorial in the module -/

/-- `AlgebraicGeometry.sheafSubmoduleMap`, at the `X.Modules` presentation of the category of
sheaves of modules on `X`. -/
public def submoduleMapOfComap {M N : X.Modules} (f : M ⟶ N) (S : M.Submodule) (T : N.Submodule)
    (h : S ≤ AlgebraicGeometry.sheafSubmoduleComap f T) :
    (S.toSheafOfModules : X.Modules) ⟶ (T.toSheafOfModules : X.Modules) :=
  AlgebraicGeometry.sheafSubmoduleMap f S T h

/-- The restriction of `f` to subsheaves is compatible with the inclusions into the ambient
sheaves. -/
public theorem submoduleMapOfComap_comp_ι {M N : X.Modules} (f : M ⟶ N) (S : M.Submodule)
    (T : N.Submodule) (h : S ≤ AlgebraicGeometry.sheafSubmoduleComap f T) :
    submoduleMapOfComap f S T h ≫ (T.ι : (T.toSheafOfModules : X.Modules) ⟶ N) =
      (S.ι : (S.toSheafOfModules : X.Modules) ⟶ M) ≫ f :=
  AlgebraicGeometry.sheafSubmoduleMap_comp_ι f S T h

/-- The map `M / S ⟶ N / T` on sheaf quotients induced by a morphism `f : M ⟶ N` which carries
the submodule `S` of `M` into the submodule `T` of `N`. -/
public def quotientMapOfComap {M N : X.Modules} {S : M.Submodule} {T : N.Submodule}
    (f : M ⟶ N) (h : S ≤ AlgebraicGeometry.sheafSubmoduleComap f T) :
    cokernel (C := X.Modules) S.ι ⟶ cokernel (C := X.Modules) T.ι :=
  cokernel.desc (C := X.Modules) S.ι (f ≫ cokernel.π (C := X.Modules) T.ι)
    (((Category.assoc (obj := X.Modules) (S.ι : (S.toSheafOfModules : X.Modules) ⟶ M) f
          (cokernel.π (C := X.Modules) T.ι)).symm.trans
        (congrArg (fun k ↦ k ≫ cokernel.π (C := X.Modules) T.ι)
          (submoduleMapOfComap_comp_ι f S T h).symm)).trans
      (((Category.assoc (obj := X.Modules) (submoduleMapOfComap f S T h)
            (T.ι : (T.toSheafOfModules : X.Modules) ⟶ N)
            (cokernel.π (C := X.Modules) T.ι)).trans
          (congrArg (fun k ↦ submoduleMapOfComap f S T h ≫ k)
            (cokernel.condition (C := X.Modules) T.ι))).trans comp_zero))

/-- The induced map on quotients commutes with the quotient projections. -/
@[reassoc]
public theorem quotientMapOfComap_π {M N : X.Modules} {S : M.Submodule} {T : N.Submodule}
    (f : M ⟶ N) (h : S ≤ AlgebraicGeometry.sheafSubmoduleComap f T) :
    cokernel.π (C := X.Modules) S.ι ≫ quotientMapOfComap f h =
      f ≫ cokernel.π (C := X.Modules) T.ι :=
  cokernel.π_desc _ _ _

/-- The map `M / 𝒥 ⁿ M ⟶ N / ℐ ᵐ N` induced by a morphism `f : M ⟶ N` of sheaves of modules,
available whenever `𝒥 ⁿ ⊆ ℐ ᵐ`. -/
public def idealPowerQuotientMap (J I : X.IdealSheafData) (n m : ℕ) (h : J ^ n ≤ I ^ m)
    {M N : X.Modules} (f : M ⟶ N) :
    idealPowerQuotient J n M ⟶ idealPowerQuotient I m N :=
  quotientMapOfComap f (idealPowerMultiple_le_sheafSubmoduleComap_of_pow_le h f)

/-- `idealPowerQuotientMap` commutes with the quotient projections. -/
@[reassoc]
public theorem idealPowerQuotientMap_π (J I : X.IdealSheafData) (n m : ℕ) (h : J ^ n ≤ I ^ m)
    {M N : X.Modules} (f : M ⟶ N) :
    cokernel.π (C := X.Modules) (idealPowerMultiple J n M).ι ≫
        idealPowerQuotientMap J I n m h f =
      f ≫ cokernel.π (C := X.Modules) (idealPowerMultiple I m N).ι :=
  quotientMapOfComap_π f _

/-- A surjection of sheaves of modules induces a surjection of ideal-power quotients. -/
public instance epi_idealPowerQuotientMap (J I : X.IdealSheafData) (n m : ℕ) (h : J ^ n ≤ I ^ m)
    {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Epi (idealPowerQuotientMap J I n m h f) := by
  have hcomp : Epi (cokernel.π (C := X.Modules) (idealPowerMultiple J n M).ι ≫
      idealPowerQuotientMap J I n m h f) := by
    rw [idealPowerQuotientMap_π]
    infer_instance
  exact epi_of_epi (cokernel.π (C := X.Modules) (idealPowerMultiple J n M).ι) _

/-- `idealPowerQuotientMap` sends the identity to the identity. -/
@[simp]
public theorem idealPowerQuotientMap_id (J : X.IdealSheafData) (n : ℕ) (M : X.Modules) :
    idealPowerQuotientMap J J n n le_rfl (𝟙 M) = 𝟙 _ := by
  refine (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple J n M).ι)).1 ?_
  rw [idealPowerQuotientMap_π]
  simp

/-- `idealPowerQuotientMap` is compatible with composition. -/
public theorem idealPowerQuotientMap_comp (J : X.IdealSheafData) (n : ℕ)
    {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    idealPowerQuotientMap J J n n le_rfl (f ≫ g) =
      idealPowerQuotientMap J J n n le_rfl f ≫ idealPowerQuotientMap J J n n le_rfl g := by
  refine (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple J n M).ι)).1 ?_
  rw [idealPowerQuotientMap_π, idealPowerQuotientMap_π_assoc, idealPowerQuotientMap_π,
    Category.assoc]

/-- Lowering the exponent: the map `M / 𝒥 ᵐ M ⟶ M / 𝒥 ⁿ M` for `n ≤ m`.

This is `idealPowerQuotientMap` on the identity of `M`, rather than
`Stacks.Algebraization.quotientMapOfLE`, so that `idealPowerQuotientMap_π` and the functoriality
lemmas above apply to it. -/
public def idealPowerQuotientDrop (J : X.IdealSheafData) {m n : ℕ} (h : n ≤ m) (M : X.Modules) :
    idealPowerQuotient J m M ⟶ idealPowerQuotient J n M :=
  idealPowerQuotientMap J J m n (Scheme.IdealSheafData.pow_le_pow_of_le J h) (𝟙 M)

/-- Lowering the exponent takes the one quotient projection to the other. -/
@[reassoc]
public theorem idealPowerQuotientDrop_π (J : X.IdealSheafData) {m n : ℕ} (h : n ≤ m)
    (M : X.Modules) :
    cokernel.π (C := X.Modules) (idealPowerMultiple J m M).ι ≫ idealPowerQuotientDrop J h M =
      cokernel.π (C := X.Modules) (idealPowerMultiple J n M).ι := by
  rw [idealPowerQuotientDrop, idealPowerQuotientMap_π]
  simp

/-- `idealPowerQuotientMap` sends an isomorphism to an isomorphism. -/
public instance isIso_idealPowerQuotientMap (J : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (e : M ≅ N) :
    IsIso (idealPowerQuotientMap J J n n le_rfl e.hom) :=
  ⟨idealPowerQuotientMap J J n n le_rfl e.inv, by
    rw [← idealPowerQuotientMap_comp, e.hom_inv_id, idealPowerQuotientMap_id], by
    rw [← idealPowerQuotientMap_comp, e.inv_hom_id, idealPowerQuotientMap_id]⟩

/-! ### Coherence of the quotients -/

/-- The ideal-power quotient of a quasi-coherent sheaf of modules is quasi-coherent. -/
public instance isQuasicoherent_idealPowerQuotient (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) [M.IsQuasicoherent] : (idealPowerQuotient I n M).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
    (idealPowerMultiple I n M).ι

/-- The ideal-power quotient of a coherent sheaf of modules on a locally Noetherian scheme is
coherent. -/
public instance isCoherent_idealPowerQuotient [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) [M.IsCoherent] : (idealPowerQuotient I n M).IsCoherent := by
  have : M.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1
  exact Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi
    (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι)

/-! ### When the comparison map is an isomorphism -/

/-- A submodule is contained in the sectionwise kernel of the projection onto the quotient by
it. -/
public theorem submodule_le_kernelSubmodule_cokernel_π {M : X.Modules} (S : M.Submodule) :
    S ≤ kernelSubmodule (cokernel.π (C := X.Modules) S.ι) := by
  refine SheafOfModules.Submodule.le_iff.mpr fun U x hx ↦ ?_
  have key : ((cokernel.π (C := X.Modules) S.ι).val.app U).hom
      (((S.ι : (S.toSheafOfModules : X.Modules) ⟶ M).val.app U).hom ⟨x, hx⟩) = 0 :=
    congrArg (fun t : (S.toSheafOfModules : X.Modules) ⟶ cokernel (C := X.Modules) S.ι ↦
      (t.val.app U).hom ⟨x, hx⟩) (cokernel.condition (C := X.Modules) S.ι)
  have hz : ((cokernel.π (C := X.Modules) S.ι).val.app U).hom x = 0 := key
  show ((cokernel.π (C := X.Modules) S.ι).val.app U).hom x ∈
    (⊥ : (cokernel (C := X.Modules) S.ι).Submodule).toSubmodule.obj U
  rw [hz]
  exact Submodule.zero_mem _

/-- The sections of `M / ℐ ⁿ M` over an affine open `U` are annihilated by `ℐ(U) ⁿ`. -/
public theorem pow_smul_top_idealPowerQuotient_eq_bot (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) :
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(idealPowerQuotient I n M, U.1)) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.2 fun a ha x _ ↦ ?_) bot_le
  obtain ⟨y, hy⟩ : ∃ y, (cokernel.π (C := X.Modules)
      (idealPowerMultiple I n M).ι).app U.1 y = x :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι) U.1 U.2 x
  have hmem : a • y ∈ (idealPowerMultiple I n M).toSubmodule.obj (op U.1) :=
    (idealPowerMultiple_le_iff I n M _).1 le_rfl U
      (Submodule.smul_mem_smul ha (Submodule.mem_top (x := y)))
  have hker := SheafOfModules.Submodule.le_iff.mp
    (submodule_le_kernelSubmodule_cokernel_π (idealPowerMultiple I n M)) (op U.1) hmem
  rw [kernelSubmodule_toSubmodule_obj] at hker
  refine (Submodule.mem_bot _).2 ?_
  calc a • x
      = a • (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι).app U.1 y := by rw [hy]
    _ = (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι).app U.1 (a • y) :=
        (Scheme.Modules.Hom.app_smul _ a y).symm
    _ = 0 := hker

/-- The `ℐ ⁿ`-multiple of the `ℐ ⁿ`-quotient vanishes. -/
public theorem idealPowerMultiple_idealPowerQuotient_eq_bot (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) [M.IsQuasicoherent] :
    idealPowerMultiple I n (idealPowerQuotient I n M) = ⊥ := by
  refine le_antisymm ((idealPowerMultiple_le_iff I n _ ⊥).2 fun U ↦ ?_) bot_le
  rw [pow_smul_top_idealPowerQuotient_eq_bot I n M U]
  exact bot_le

/-- The projection onto the quotient by the zero submodule is an isomorphism. -/
public theorem isIso_cokernel_π_of_eq_bot {M : X.Modules} (S : M.Submodule) (h : S = ⊥) :
    IsIso (cokernel.π (C := X.Modules) S.ι) := by
  subst h
  exact cokernel.π_of_zero ((Category.id_comp _).symm.trans (comp_sheafBot_ι_eq_zero (𝟙 _)))

/-- If `ℐ ⁿ M` vanishes then `M` is already its own `ℐ ⁿ`-quotient. -/
public theorem isIso_cokernel_π_of_idealPowerMultiple_eq_bot (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) (hbot : idealPowerMultiple I n M = ⊥) :
    IsIso (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι) :=
  isIso_cokernel_π_of_eq_bot _ hbot

/-- Dividing the `ℐ ⁿ`-quotient by `ℐ ⁿ` a second time changes nothing. -/
public instance isIso_cokernel_π_idealPowerQuotient (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (cokernel.π (C := X.Modules)
      (idealPowerMultiple I n (idealPowerQuotient I n M)).ι) :=
  isIso_cokernel_π_of_idealPowerMultiple_eq_bot I n _
    (idealPowerMultiple_idealPowerQuotient_eq_bot I n M)

/-- If `𝒥 ˢ ⊆ ℐ ⁿ`, then the quotient projection `M ⟶ M / 𝒥 ˢ M` becomes an isomorphism after
dividing both sides by `ℐ ⁿ`. -/
public theorem isIso_idealPowerQuotientMap_cokernel_π (I J : X.IdealSheafData) (n s : ℕ)
    (h : J ^ s ≤ I ^ n) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (idealPowerQuotientMap I I n n le_rfl
      (cokernel.π (C := X.Modules) (idealPowerMultiple J s M).ι)) := by
  set qJ : M ⟶ idealPowerQuotient J s M :=
    cokernel.π (C := X.Modules) (idealPowerMultiple J s M).ι with hqJ
  set qI : M ⟶ idealPowerQuotient I n M :=
    cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι with hqI
  have hqu : qJ ≫ idealPowerQuotientMap J I s n h (𝟙 M) = qI := by
    rw [hqJ, hqI, idealPowerQuotientMap_π]; simp
  have hcomp : idealPowerQuotientMap I I n n le_rfl qJ ≫
      idealPowerQuotientMap I I n n le_rfl (idealPowerQuotientMap J I s n h (𝟙 M)) =
      idealPowerQuotientMap I I n n le_rfl qI := by
    rw [← idealPowerQuotientMap_comp, hqu]
  have : IsIso (idealPowerQuotientMap I I n n le_rfl qI) := by
    have hbar : idealPowerQuotientMap I I n n le_rfl qI =
        cokernel.π (C := X.Modules)
          (idealPowerMultiple I n (idealPowerQuotient I n M)).ι := by
      refine (cancel_epi qI).1 ?_
      rw [hqI, idealPowerQuotientMap_π]
    rw [hbar]
    infer_instance
  have : Mono (idealPowerQuotientMap I I n n le_rfl qJ) := mono_of_mono_fac hcomp
  exact isIso_of_mono_of_epi _

/-- The previous statement through an abstract presentation of the quotient: if `f : M ⟶ N` is the
quotient projection `M ⟶ M / 𝒥 ˢ M` followed by an isomorphism, and `𝒥 ˢ ⊆ ℐ ⁿ`, then `f`
becomes an isomorphism after dividing both sides by `ℐ ⁿ`. -/
public theorem isIso_idealPowerQuotientMap_of_cokernel_π_comp (I J : X.IdealSheafData) (n s : ℕ)
    (h : J ^ s ≤ I ^ n) {M N : X.Modules} [M.IsQuasicoherent]
    (e : idealPowerQuotient J s M ≅ N) (f : M ⟶ N)
    (hf : cokernel.π (C := X.Modules) (idealPowerMultiple J s M).ι ≫ e.hom = f) :
    IsIso (idealPowerQuotientMap I I n n le_rfl f) := by
  have := isIso_idealPowerQuotientMap_cokernel_π I J n s h M
  rw [← hf, idealPowerQuotientMap_comp]
  infer_instance

/-! ### Two isomorphisms out of a common object

Two invertible maps `α : B ⟶ D` and `β : B ⟶ E` out of a common object give an isomorphism
`D ≅ E`, which carries a factorization through `α` to the corresponding factorization through
`β`. -/

/-- The isomorphism `D ≅ E` determined by two invertible maps out of `B` carries a factorization
`p = d ≫ α` to `d ≫ β`. -/
public theorem comp_isoOfIsIso {C : Type*} [Category C] {A B D E : C} (p : A ⟶ D) (d : A ⟶ B)
    (α : B ⟶ D) [IsIso α] (β : B ⟶ E) [IsIso β] (h : p = d ≫ α) :
    p ≫ ((asIso α).symm ≪≫ asIso β).hom = d ≫ β := by
  rw [h]; simp

/-- The variant in which the target is further identified by an invertible `γ : G ⟶ E`, and the
factorization through `α` is given on a composite `p ≫ q`. -/
public theorem comp_comp_isoOfIsIso {C : Type*} [Category C] {A A' B D E G : C}
    (p : A ⟶ A') (q : A' ⟶ D) (d : A ⟶ B) (α : B ⟶ D) [IsIso α] (β : B ⟶ E) [IsIso β]
    (γ : G ⟶ E) [IsIso γ] (f : A ⟶ G) (h : p ≫ q = d ≫ α) (h' : d ≫ β = f ≫ γ) :
    p ≫ q ≫ ((asIso α).symm ≪≫ asIso β ≪≫ (asIso γ).symm).hom = f := by
  rw [← Category.assoc, h]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
    IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, h', Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-! ### The two packaged reduction isomorphisms -/

/-- Let `M` be quasi-coherent and let
`f : M ⟶ N` have invertible reduction modulo `𝒥 ʳ`. Then the `𝒥 ʳ`-quotient of `M / 𝒥 ʳ⁺¹ M` is
identified with `N / 𝒥 ʳ N`, and under that identification the quotient projection is the map
induced by `f`. -/
public def idealPowerQuotientIsoOfIsIso (J : X.IdealSheafData) (r : ℕ)
    {M N : X.Modules} [M.IsQuasicoherent] (f : M ⟶ N)
    [IsIso (idealPowerQuotientMap J J r r le_rfl f)] :
    {e : idealPowerQuotient J r (idealPowerQuotient J (r + 1) M) ≅ idealPowerQuotient J r N //
      cokernel.π (C := X.Modules)
          (idealPowerMultiple J r (idealPowerQuotient J (r + 1) M)).ι ≫ e.hom =
        idealPowerQuotientMap J J (r + 1) r
          (Scheme.IdealSheafData.pow_le_pow_of_le J (Nat.le_succ r)) f} := by
  have halpha : IsIso (idealPowerQuotientMap J J r r le_rfl
      (cokernel.π (C := X.Modules) (idealPowerMultiple J (r + 1) M).ι)) :=
    isIso_idealPowerQuotientMap_cokernel_π J J r (r + 1)
      (Scheme.IdealSheafData.pow_le_pow_of_le J (Nat.le_succ r)) M
  refine ⟨(asIso (idealPowerQuotientMap J J r r le_rfl
        (cokernel.π (C := X.Modules) (idealPowerMultiple J (r + 1) M).ι))).symm ≪≫
      asIso (idealPowerQuotientMap J J r r le_rfl f), ?_⟩
  refine (comp_isoOfIsIso _ (idealPowerQuotientDrop J (Nat.le_succ r) M) _ _ ?_).trans ?_
  · refine (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple J (r + 1) M).ι)).1 ?_
    rw [idealPowerQuotientDrop_π_assoc, idealPowerQuotientMap_π]
  · refine (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple J (r + 1) M).ι)).1 ?_
    rw [idealPowerQuotientDrop_π_assoc, idealPowerQuotientMap_π, idealPowerQuotientMap_π]

/-- Let `𝒥 ˢ ⊆ ℐ ʳ`, let `M` be quasi-coherent, let `f : M ⟶ N` have invertible reduction
modulo `ℐ ʳ`, and let `ℐ ʳ N = 0`. Then the
`ℐ ʳ`-quotient of `M / 𝒥 ˢ M` is identified with `N`, and under that identification the two
quotient projections `M ⟶ M / 𝒥 ˢ M ⟶ (M / 𝒥 ˢ M) / ℐ ʳ (M / 𝒥 ˢ M)` compose to `f`. -/
public def doubleIdealPowerQuotientIso (I J : X.IdealSheafData) (r s : ℕ) (h : J ^ s ≤ I ^ r)
    {M N : X.Modules} [M.IsQuasicoherent] (f : M ⟶ N)
    [IsIso (idealPowerQuotientMap I I r r le_rfl f)] (hbot : idealPowerMultiple I r N = ⊥) :
    {e : idealPowerQuotient I r (idealPowerQuotient J s M) ≅ N //
      cokernel.π (C := X.Modules) (idealPowerMultiple J s M).ι ≫
        cokernel.π (C := X.Modules)
          (idealPowerMultiple I r (idealPowerQuotient J s M)).ι ≫ e.hom = f} := by
  have halpha : IsIso (idealPowerQuotientMap I I r r le_rfl
      (cokernel.π (C := X.Modules) (idealPowerMultiple J s M).ι)) :=
    isIso_idealPowerQuotientMap_cokernel_π I J r s h M
  have hgamma : IsIso (cokernel.π (C := X.Modules) (idealPowerMultiple I r N).ι) :=
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot I r N hbot
  refine ⟨(asIso (idealPowerQuotientMap I I r r le_rfl
        (cokernel.π (C := X.Modules) (idealPowerMultiple J s M).ι))).symm ≪≫
      asIso (idealPowerQuotientMap I I r r le_rfl f) ≪≫
      (asIso (cokernel.π (C := X.Modules) (idealPowerMultiple I r N).ι)).symm, ?_⟩
  exact comp_comp_isoOfIsIso _ _
    (cokernel.π (C := X.Modules) (idealPowerMultiple I r M).ι) _ _ _ _
    (idealPowerQuotientMap_π I I r r le_rfl _).symm (idealPowerQuotientMap_π I I r r le_rfl f)

end Stacks.Algebraization

end

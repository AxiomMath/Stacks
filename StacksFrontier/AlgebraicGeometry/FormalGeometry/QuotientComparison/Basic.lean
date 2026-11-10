module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The ideal-power quotient and the infinitesimal neighbourhood

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on `X`, `n` a natural number and `F` a sheaf
of modules on `X`. Write `Z = (I ^ n).subscheme` for the closed subscheme cut out by `I ^ n` — the
`n`-th infinitesimal neighbourhood of the subscheme of `I` — and `ι = (I ^ n).subschemeι` for its
closed immersion into `X`. The restriction of `F` to `Z` is `ι^* F`, and pushing it forward again
gives an `𝒪_X`-module `ι_* ι^* F` receiving `F` through the unit of the
pullback–pushforward adjunction.

This file relates that module to the sheaf quotient `F / I ^ n F`. The ideal `I ^ n` annihilates
every pushforward from `Z`, because on an affine open the module structure on `Γ(ι_* M, U)` is the
one restricted along `ι^♯ : Γ(X, U) ⟶ Γ(Z, ι⁻¹U)` and the kernel of that ring map is exactly
`I ^ n (U)`. So the unit kills the subsheaf `I ^ n F` and factors through the quotient, giving the
canonical comparison
`F / I ^ n F ⟶ ι_* ι^* F`
normalized by the equation that the quotient projection composed with it is the unit. Since the
projection is epimorphic that equation determines the comparison uniquely, so a
`QuotientSubschemeComparison` — an isomorphism satisfying it — exists exactly when the canonical
comparison is an isomorphism, and there is at most one.

The comparison is *not* proved to be an isomorphism here; see the implementation notes for what
that needs. What is proved is the statement one gets after restricting back to `Z`: the quotient
projection `F ⟶ F / I ^ n F` becomes an isomorphism under `ι^*`. Equivalently, the inclusion
`I ^ n F ⟶ F` restricts to zero on the `n`-th infinitesimal neighbourhood.

## Main definitions

* `Stacks.Algebraization.quotientSubschemeComparisonMap` — the canonical comparison
  `F / I ^ n F ⟶ ι_* ι^* F`.
* `Stacks.Algebraization.QuotientSubschemeComparison` — the data of an isomorphism
  `F / I ^ n F ≅ ι_* ι^* F` normalized by the adjunction unit.

## Main results

* `Stacks.Algebraization.pushforward_smul_eq_zero` — a section of `Γ(X, U)` in the kernel of
  `f^♯` annihilates `Γ(f_* M, U)`.
* `Stacks.Algebraization.idealPower_smul_pushforward_eq_bot` — `I ^ n` annihilates the sections of
  a pushforward from the `n`-th infinitesimal neighbourhood over every affine open.
* `Stacks.Algebraization.idealPowerMultiple_ι_comp_eq_zero` — consequently every map from `F` to
  such a pushforward kills the subsheaf `I ^ n F`.
* `Stacks.Algebraization.quotientSubschemeComparisonMap_π` — the normalization, and
  `Stacks.Algebraization.quotientSubschemeComparisonMap_unique` — that it pins the map down.
* `Stacks.Algebraization.isIso_pullback_map_cokernel_π` — `ι^*` inverts the quotient projection.
* `Stacks.Algebraization.pullback_map_idealPowerMultiple_ι_eq_zero` — `ι^*` kills the inclusion
  `I ^ n F ⟶ F`.
* `Stacks.Algebraization.QuotientSubschemeComparison.instSubsingleton`,
  `Stacks.Algebraization.QuotientSubschemeComparison.ofIsIso` and
  `Stacks.Algebraization.QuotientSubschemeComparison.isIso` — the comparison data is unique when
  it exists, and exists exactly when `quotientSubschemeComparisonMap` is an isomorphism.

## Implementation notes

The subsheaf `I ^ n F` is `Stacks.Algebraization.idealPowerMultiple`, characterized by the
affine-local universal property `Stacks.Algebraization.idealPowerMultiple_le_iff`, and the
quotient is `Stacks.Algebraization.idealPowerQuotient`, the cokernel of its inclusion. The
annihilation statement is fed to `Stacks.Coherent.idealPowerMultiple_le_kernelSubmodule`, which
turns an affine-local annihilation of the target into containment of `I ^ n F` in the sectionwise
kernel.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` and the two
presentations carry separately declared category instances, so every categorical construction
below names its category explicitly as `(C := X.Modules)`, and the lattice of submodules is
supplied by the local instance.

`isIso_pullback_map_cokernel_π` is an instance of a purely categorical fact, isolated here as
`Stacks.Algebraization.isIso_map_of_unit_fac`: if the unit of an adjunction `L ⊣ R` at `A`
factors as `q ≫ c` through an epimorphism `q : A ⟶ Q`, then `L.map q` is an isomorphism — the
adjunct of `c` is a retraction of `L.map q` by naturality of the hom-equivalence, and a
retraction of an epimorphism is a two-sided inverse. Nothing about closed immersions enters.

What makes the comparison an isomorphism is one statement: that the unit `G ⟶ ι_* ι^* G` is an
isomorphism whenever `I ^ n` annihilates `G`, equivalently that `ι_*` is essentially surjective
onto the `I ^ n`-annihilated modules. Given it at `G = F / I ^ n F`, the comparison is
`unit ≫ ι_*` of the inverse of `ι^*` applied to the projection, hence an isomorphism.

**That statement is proved for a closed immersion of schemes**: it is
`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`, with the
essential image characterized by `Stacks.ClosedImmersion.pushforward_essImage_iff` and full
faithfulness by `Stacks.ClosedImmersion.fullyFaithfulPushforward`, all in
`StacksFrontier/AlgebraicGeometry/ClosedPushforward/Basic.lean`. Consequently the comparison *is*
proved to be an isomorphism — for an arbitrary closed immersion `v` with `v.ker = I ^ n` and an
arbitrary quasi-coherent `F` — as `Stacks.Algebraization.isIso_idealQuotientPushforwardMap` and
`…idealQuotientPushforwardIso` in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFullyFaithful/SectionsComplete.lean`,
whose annihilation input is this file's `pow_smul_top_idealPowerQuotient_eq_bot`. That file is
downstream of this one, which is why the construction here is left unconditional in `F`; the
`QuotientSubschemeComparison` data below is `…QuotientSubschemeComparison.ofIsIso` of it.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe v₁ v₂ u₁ u₂ u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ## A categorical lemma -/

/-- If the unit of an adjunction `L ⊣ R` at `A` factors through an epimorphism `q : A ⟶ Q`, then
`L.map q` is an isomorphism.

The adjunct of the factoring map `c : Q ⟶ R.obj (L.obj A)` is a retraction of `L.map q`, by
naturality of the hom-equivalence on the left; a retraction of an epimorphism is a two-sided
inverse, and `L` preserves epimorphisms because it is a left adjoint. -/
public theorem isIso_map_of_unit_fac {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A Q : C} (q : A ⟶ Q) [Epi q]
    (c : Q ⟶ R.obj (L.obj A)) (hc : q ≫ c = adj.unit.app A) :
    IsIso (L.map q) := by
  have := adj.isLeftAdjoint
  have h1 : L.map q ≫ (adj.homEquiv Q (L.obj A)).symm c = 𝟙 (L.obj A) := by
    apply (adj.homEquiv A (L.obj A)).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, hc,
      Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  refine ⟨(adj.homEquiv Q (L.obj A)).symm c, h1, ?_⟩
  rw [← cancel_epi (L.map q), ← Category.assoc, h1, Category.id_comp, Category.comp_id]

/-! ## The ideal annihilates a pushforward from the subscheme -/

variable {X Z : Scheme.{u}}

/-- A section of `Γ(X, U)` killed by the comorphism of `f : Z ⟶ X` annihilates the sections of any
pushforward along `f` over `U`: the module structure on `Γ(f_* M, U) = Γ(M, f⁻¹U)` is restriction
of scalars along `f^♯` on `U`. -/
public theorem pushforward_smul_eq_zero (f : Z ⟶ X) {M : Z.Modules} {U : X.Opens}
    {a : Γ(X, U)} (ha : f.app U a = 0) (t : Γ((Scheme.Modules.pushforward f).obj M, U)) :
    a • t = 0 := by
  change (f.app U a) • (show Γ(M, f ⁻¹ᵁ U) from t) = 0
  rw [ha, zero_smul]

/-- The `n`-th power of the ideal annihilates, over every affine open, the sections of a
pushforward from the `n`-th infinitesimal neighbourhood: the kernel of the comorphism of
`(I ^ n).subschemeι` on an affine open is precisely `(I ^ n)(U) = I(U) ^ n`. -/
public theorem idealPower_smul_pushforward_eq_bot (I : X.IdealSheafData) (n : ℕ)
    (M : (I ^ n).subscheme.Modules) (U : X.affineOpens) :
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U)
      Γ((Scheme.Modules.pushforward (I ^ n).subschemeι).obj M, U)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro a ha t _
  have hker : a ∈ RingHom.ker ((I ^ n).subschemeι.app U).hom := by
    rw [(I ^ n).ker_subschemeι_app U, Scheme.IdealSheafData.ideal_pow]
    exact ha
  exact (Submodule.mem_bot _).mpr (pushforward_smul_eq_zero _ hker t)

/-- Every morphism from `F` to a pushforward from the `n`-th infinitesimal neighbourhood kills the
subsheaf `I ^ n F`. -/
public theorem idealPowerMultiple_ι_comp_eq_zero (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    {M : (I ^ n).subscheme.Modules}
    (u : F ⟶ (Scheme.Modules.pushforward (I ^ n).subschemeι).obj M) :
    ((idealPowerMultiple I n F).ι :
        ((idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ F) ≫ u =
      (0 : ((idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ _) := by
  have hker : idealPowerMultiple I n F ≤ kernelSubmodule u :=
    Stacks.Coherent.idealPowerMultiple_le_kernelSubmodule I n u
      (idealPower_smul_pushforward_eq_bot I n M)
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  have hx := hker (op V) x.property
  rw [kernelSubmodule_toSubmodule_obj] at hx
  exact hx

/-! ## The canonical comparison -/

/-- The quotient projection `F ⟶ F / I ^ n F` is an epimorphism. -/
public instance epi_cokernel_π_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) :
    Epi (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι) :=
  coequalizer.π_epi

/-- The canonical comparison `F / I ^ n F ⟶ ι_* ι^* F` for `ι` the closed immersion of the `n`-th
infinitesimal neighbourhood of `I`, obtained by factoring the adjunction unit through the
quotient projection. -/
public def quotientSubschemeComparisonMap (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    idealPowerQuotient I n F ⟶ (Scheme.Modules.pushforward (I ^ n).subschemeι).obj
      ((Scheme.Modules.pullback (I ^ n).subschemeι).obj F) :=
  cokernel.desc (C := X.Modules) (idealPowerMultiple I n F).ι
    ((Scheme.Modules.pullbackPushforwardAdjunction (I ^ n).subschemeι).unit.app F)
    (idealPowerMultiple_ι_comp_eq_zero I n F _)

/-- The normalization: the quotient projection composed with the comparison is the adjunction
unit. -/
@[simp]
public theorem quotientSubschemeComparisonMap_π (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι ≫
        quotientSubschemeComparisonMap I n F =
      (Scheme.Modules.pullbackPushforwardAdjunction (I ^ n).subschemeι).unit.app F :=
  cokernel.π_desc _ _ _

/-- The normalization determines the comparison: the quotient projection is epimorphic, so there
is at most one map out of `F / I ^ n F` composing with it to the adjunction unit. -/
public theorem quotientSubschemeComparisonMap_unique (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules)
    (g : idealPowerQuotient I n F ⟶ (Scheme.Modules.pushforward (I ^ n).subschemeι).obj
      ((Scheme.Modules.pullback (I ^ n).subschemeι).obj F))
    (hg : cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι ≫ g =
      (Scheme.Modules.pullbackPushforwardAdjunction (I ^ n).subschemeι).unit.app F) :
    g = quotientSubschemeComparisonMap I n F := by
  rw [← cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι), hg,
    quotientSubschemeComparisonMap_π]

/-! ## Restricting back to the infinitesimal neighbourhood -/

/-- Restriction to the `n`-th infinitesimal neighbourhood inverts the quotient projection
`F ⟶ F / I ^ n F`.

The unit factors through that projection by `quotientSubschemeComparisonMap_π`, which is exactly
the hypothesis of `isIso_map_of_unit_fac`. -/
public instance isIso_pullback_map_cokernel_π (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    IsIso ((Scheme.Modules.pullback (I ^ n).subschemeι).map
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)) :=
  isIso_map_of_unit_fac (Scheme.Modules.pullbackPushforwardAdjunction (I ^ n).subschemeι) _
    (quotientSubschemeComparisonMap I n F) (quotientSubschemeComparisonMap_π I n F)

/-- Restriction to the `n`-th infinitesimal neighbourhood kills the inclusion `I ^ n F ⟶ F`. -/
public theorem pullback_map_idealPowerMultiple_ι_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) :
    (Scheme.Modules.pullback (I ^ n).subschemeι).map
        ((idealPowerMultiple I n F).ι :
          ((idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ F) =
      0 := by
  rw [← cancel_mono ((Scheme.Modules.pullback (I ^ n).subschemeι).map
    (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)), zero_comp]
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg _ (cokernel.condition _)).trans (Functor.map_zero _ _ _))

/-! ## The comparison data -/

/-- The canonical identification of an ideal-power quotient with the pushforward from the
corresponding infinitesimal neighbourhood. The equation with the adjunction unit fixes the
identification uniquely. -/
public structure QuotientSubschemeComparison (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) where
  /-- The identification `F / I ^ n F ≅ ι_* ι^* F`. -/
  iso : idealPowerQuotient I n F ≅ (Scheme.Modules.pushforward (I ^ n).subschemeι).obj
    ((Scheme.Modules.pullback (I ^ n).subschemeι).obj F)
  /-- The identification is normalized by the pullback–pushforward unit. -/
  quotient_unit : cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι ≫ iso.hom =
    (Scheme.Modules.pullbackPushforwardAdjunction (I ^ n).subschemeι).unit.app F

namespace QuotientSubschemeComparison

variable {I : X.IdealSheafData} {n : ℕ} {F : X.Modules}

/-- The normalization pins the identification down, so there is at most one. -/
public instance instSubsingleton : Subsingleton (QuotientSubschemeComparison I n F) := by
  constructor
  rintro ⟨e, he⟩ ⟨e', he'⟩
  obtain rfl : e = e' := Iso.ext <| by
    rw [← cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι), he, he']
  rfl

/-- The identification is the canonical comparison map. -/
public theorem iso_hom_eq (c : QuotientSubschemeComparison I n F) :
    c.iso.hom = quotientSubschemeComparisonMap I n F :=
  quotientSubschemeComparisonMap_unique I n F _ c.quotient_unit

/-- From the comparison data, the canonical comparison map is an isomorphism. -/
public theorem isIso (c : QuotientSubschemeComparison I n F) :
    IsIso (quotientSubschemeComparisonMap I n F) := by
  rw [← c.iso_hom_eq]
  infer_instance

/-- Conversely, if the canonical comparison map is an isomorphism it is the comparison data. -/
public def ofIsIso (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [IsIso (quotientSubschemeComparisonMap I n F)] : QuotientSubschemeComparison I n F where
  iso := asIso (quotientSubschemeComparisonMap I n F)
  quotient_unit := quotientSubschemeComparisonMap_π I n F

/-- The comparison data exists exactly when the canonical comparison map is an isomorphism. -/
public theorem nonempty_iff_isIso (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    Nonempty (QuotientSubschemeComparison I n F) ↔
      IsIso (quotientSubschemeComparisonMap I n F) :=
  ⟨fun ⟨c⟩ => c.isIso, fun h => ⟨@ofIsIso _ I n F h⟩⟩

end QuotientSubschemeComparison

end Stacks.Algebraization

end

module

public import StacksFrontier.RingTheory.Cech.DerivedRingBaseChange
public import StacksFrontier.RingTheory.Cech.RingBaseChange

/-!
# The derived base change of the extended alternating Čech complex of a ring

Let `φ : A → B` be a homomorphism of commutative rings, let `f₁, …, f_r ∈ A` and write
`g_i = φ(f_i)`. The change-of-rings map of complexes of `A`-modules
`Stacks.CechRingBaseChange.complexMap φ f : C^•(f; A) → C^•(g; B)` transposes, across the
extension–restriction adjunction, to a map of complexes of `B`-modules
`B ⊗_A C^•(f; A) → C^•(g; B)`. This file proves that the transpose is an isomorphism: in degree
`p` it is the map `b ⊗ x ↦ b · (change of rings)(x)`, and on the summand of `C^p(f; A)` indexed by
a `p`-element set `s` of indices it is the base-change comparison
`B ⊗_A A_{f_{i_0} \cdots f_{i_{p-1}}} → B_{g_{i_0} \cdots g_{i_{p-1}}}`, which is invertible
because the right-hand side is also a localization of `B` at the image of the localizing set.

Since `C^•(f; A)` is K-flat (`Cech.kFlat_extend_cechComplex`), degreewise extension of scalars
computes the derived tensor product, so the derived base-change map
`C^•(f; A) ⊗^L_A B → C^•(g; B)` of `Stacks.LocalCohomology.derivedBaseChange` is an isomorphism in
`D(B)`. That is condition (c) of [Stacks, Tag 099D] for a pair carrying a chosen finite generating
family; condition (d) is
`Stacks.FunctorialCechFamily.exists_extendedCechObject_iso_over_augmentation`.

In [Stacks, Tag 099D] the complex is attached to a pair `(A, I)` of a ring and a finitely generated
ideal, with no family chosen, and the maps of item (3) are given for every ring map; the statement
here is for a chosen family `f` generating `I`.

## Main definitions

* `Stacks.CechRingBaseChange.modBaseChangeEquiv` — the comparison isomorphism
  `B ⊗_A A_{f|s} ≅ B_{g|s}` at a single subset `s` of indices.
* `Stacks.CechRingBaseChange.termBaseChangeEquiv` — its degreewise assembly
  `B ⊗_A C^p(f; A) ≅ C^p(g; B)`.
* `Stacks.CechRingBaseChange.extendedComplexMap` — `complexMap φ f` read as a map of
  `ℤ`-indexed complexes, the form in which the derived base-change map is taken.

## Main results

* `Stacks.CechRingBaseChange.isIso_transpose_termMap` — the degreewise transpose
  `B ⊗_A C^p(f; A) → C^p(g; B)` is an isomorphism of `B`-modules.
* `Stacks.CechRingBaseChange.isIso_transpose_extendedComplexMap` — the transpose of
  `extendedComplexMap φ f` is an isomorphism of complexes of `B`-modules.
* `Stacks.CechRingBaseChange.isIso_derivedBaseChange_extendedComplexMap` — **condition (c) of
  tag 099D for a pair with a chosen finite generating family**: the induced map
  `C^•(f; A) ⊗^L_A B → C^•(g; B)` is an isomorphism in `D(B)`.

## Implementation notes

The `A`-module structure on `B_{g|s}` used by `Stacks.CechRingBaseChange.modMap` is the one
`ModuleCat.restrictScalars φ` puts on it, namely `Module.compHom`; the one obtained from an
`Algebra A B` instance is definitionally equal but not syntactically so, and typeclass inference
does not identify them. So the comparison maps here are built over an abstract `Algebra A B`,
where `TensorProduct A B` and `LinearMap.liftBaseChange` are available, out of
`Stacks.CechRingBaseChange.modMapAlg` and `Stacks.CechRingBaseChange.termMapAlg`: these are
`modMap` and `termMap` of `algebraMap A B` *as functions*, repackaged as linear maps for the
ambient `A`-module structure of the target. Repackaging rather than redefining is what makes the
final identification of the transpose with `termMap` hold by `rfl`. The passage to `φ` itself is
`φ.toAlgebra`, where the two structures agree definitionally, so
`Stacks.CechRingBaseChange.termExtendScalarsIso` is obtained by `exact`/`change` and not by
rewriting — the pattern of `ModuleCat.ExtendScalars.objSelfIso`.

The per-subset comparison is proved invertible directly, by the universal property of the
localization `B_{g|s}`, rather than specializing the base-change isomorphism
`Stacks.CechBaseChange.termBaseChangeEquiv` of [Stacks, Tag 0G6I] at `M = A`. That isomorphism is
stated for a general `A`-module `M` and so lands in `C^p(g; B ⊗_A A)`; using it would require the
bridge `B ⊗_A A ≅ B` inside each localization and each summand of the direct sum, which is more
work than the two localization arguments it would save.

The transpose of a map of complexes is computed degreewise by
`Stacks.CechRingBaseChange.transpose_mapHomologicalComplex_f`, which holds because the adjunction
`CategoryTheory.Adjunction.mapHomologicalComplex` has the degreewise unit and counit. The degrees
outside the image of `ComplexShape.embeddingUpNat` carry zero objects on both sides, and extension
of scalars preserves zero objects, so the transpose is invertible there for trivial reasons.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 0G6I](https://stacks.math.columbia.edu/tag/0G6I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.CechRingBaseChange

open Stacks.CechBaseChange (gfun)

/-! ### The comparison at a single localization -/

section OverAnAlgebra

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
  (B : Type u) [CommRing B] [Algebra A B]

/-- **Change of rings on a single localization, for the ambient `A`-module structure.** This is
`Stacks.CechRingBaseChange.modMap` of `algebraMap A B`, as an `A`-linear map into `B_{g|s}`
carrying the `A`-module structure that an `Algebra A B` instance gives it, rather than the one
restriction of scalars gives it. -/
def modMapAlg (s : Finset (Fin r)) :
    Cech.cechMod f A s →ₗ[A] Cech.cechMod (gfun f B) B s where
  toFun y := modMap (algebraMap A B) f s y
  map_add' y z := map_add (modMap (algebraMap A B) f s) y z
  map_smul' a y := by
    rw [RingHom.id_apply, ← algebraMap_smul B a
      (show Cech.cechMod (gfun f B) B s from modMap (algebraMap A B) f s y)]
    exact map_smul (modMap (algebraMap A B) f s) a y

/-- `Stacks.CechRingBaseChange.modMapAlg` sends the image of `a ∈ A` in `A_{f|s}` to the image
of `algebraMap A B a` in `B_{g|s}`. -/
@[simp]
theorem modMapAlg_mk (s : Finset (Fin r)) (a : A) :
    modMapAlg f B s (LocalizedModule.mkLinearMap (Cech.cechSub f s) A a)
      = LocalizedModule.mkLinearMap (Cech.cechSub (gfun f B) s) B (algebraMap A B a) :=
  modMap_mkLinearMap (algebraMap A B) f s a

/-- The `B`-linear map `b ↦ b ⊗ (1/1)` from `B` to `B ⊗_A A_{f|s}`. -/
def seedTensor (s : Finset (Fin r)) : B →ₗ[B] TensorProduct A B (Cech.cechMod f A s) where
  toFun b := b ⊗ₜ LocalizedModule.mk (1 : A) 1
  map_add' b b' := TensorProduct.add_tmul b b' _
  map_smul' b b' := (TensorProduct.smul_tmul' b b' _).symm

/-- **The base-change comparison at a single subset `s` of indices**, `B ⊗_A A_{f|s} → B_{g|s}`:
it sends `b ⊗ x` to `b` times the change of rings of `x`. -/
def modBaseChange (s : Finset (Fin r)) :
    TensorProduct A B (Cech.cechMod f A s) →ₗ[B] Cech.cechMod (gfun f B) B s :=
  LinearMap.liftBaseChange B (modMapAlg f B s)

/-- `Stacks.CechRingBaseChange.modBaseChange` sends `b ⊗ y` to `b • modMapAlg f B s y`. -/
@[simp]
theorem modBaseChange_tmul (s : Finset (Fin r)) (b : B) (y : Cech.cechMod f A s) :
    modBaseChange f B s (b ⊗ₜ y) = b • modMapAlg f B s y :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The candidate inverse of `Stacks.CechRingBaseChange.modBaseChange`, obtained from the
universal property of `B_{g|s}`: every element of `Cech.cechSub (gfun f B) s` acts invertibly on
`B ⊗_A A_{f|s}`, so `b ↦ b ⊗ (1/1)` extends to the localization. -/
def modBaseChangeInv (s : Finset (Fin r)) :
    Cech.cechMod (gfun f B) B s →ₗ[B] TensorProduct A B (Cech.cechMod f A s) :=
  LocalizedModule.lift _ (seedTensor f B s)
    (Stacks.CechBaseChange.isUnit_algebraMapS_tensor f A B s)

/-- `Stacks.CechRingBaseChange.modBaseChangeInv` sends the image of `b ∈ B` in `B_{g|s}` to
`b ⊗ (1/1)`. -/
theorem modBaseChangeInv_mk (s : Finset (Fin r)) (b : B) :
    modBaseChangeInv f B s (LocalizedModule.mkLinearMap (Cech.cechSub (gfun f B) s) B b)
      = b ⊗ₜ LocalizedModule.mk (1 : A) 1 := by
  rw [LocalizedModule.mkLinearMap_apply, modBaseChangeInv, LocalizedModule.lift_mk_one]
  rfl

/-- `Stacks.CechRingBaseChange.modBaseChange` sends `b ⊗ (1/1)` to the image of `b` in
`B_{g|s}`. -/
theorem modBaseChange_seedTensor (s : Finset (Fin r)) (b : B) :
    modBaseChange f B s (b ⊗ₜ LocalizedModule.mk (1 : A) 1)
      = LocalizedModule.mkLinearMap (Cech.cechSub (gfun f B) s) B b := by
  have h : (LocalizedModule.mk (1 : A) 1 : Cech.cechMod f A s)
      = LocalizedModule.mkLinearMap (Cech.cechSub f s) A 1 := rfl
  rw [modBaseChange_tmul, h, modMapAlg_mk, map_one, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk, smul_eq_mul, mul_one]

/-- On the image of `A_{f|s}` the candidate inverse is `x ↦ 1 ⊗ x`: both sides are `A`-linear maps
out of a localization of `A` at `Cech.cechSub f s`, and such a map is determined by its values on
the image of `A`. -/
theorem modBaseChangeInv_comp_modMapAlg (s : Finset (Fin r)) :
    ((modBaseChangeInv f B s).restrictScalars A).comp (modMapAlg f B s)
      = TensorProduct.mk A B (Cech.cechMod f A s) 1 := by
  refine IsLocalizedModule.ext (Cech.cechSub f s)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) A)
    (Stacks.CechBaseChange.isUnit_algebraMapR_tensor f A B s) (LinearMap.ext fun a => ?_)
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, modMapAlg_mk,
    TensorProduct.mk_apply]
  rw [modBaseChangeInv_mk, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    LocalizedModule.smul'_mk, smul_eq_mul, mul_one]
  rfl

/-- `Stacks.CechRingBaseChange.modBaseChangeInv` is a left inverse of
`Stacks.CechRingBaseChange.modBaseChange`. -/
theorem modBaseChangeInv_comp_modBaseChange (s : Finset (Fin r)) :
    (modBaseChangeInv f B s).comp (modBaseChange f B s) = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext y
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.comp_apply, LinearMap.id_coe, id_eq]
  rw [modBaseChange_tmul, one_smul]
  exact LinearMap.congr_fun (modBaseChangeInv_comp_modMapAlg f B s) y

/-- `Stacks.CechRingBaseChange.modBaseChangeInv` is a right inverse of
`Stacks.CechRingBaseChange.modBaseChange`. -/
theorem modBaseChange_comp_modBaseChangeInv (s : Finset (Fin r)) :
    (modBaseChange f B s).comp (modBaseChangeInv f B s) = LinearMap.id := by
  refine IsLocalizedModule.ext (Cech.cechSub (gfun f B) s)
    (LocalizedModule.mkLinearMap (Cech.cechSub (gfun f B) s) B)
    (fun x => IsLocalizedModule.map_units
      (LocalizedModule.mkLinearMap (Cech.cechSub (gfun f B) s) B) x)
    (LinearMap.ext fun b => ?_)
  simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
  rw [modBaseChangeInv_mk, modBaseChange_seedTensor]

/-- **The comparison at a single subset is bijective.** -/
theorem modBaseChange_bijective (s : Finset (Fin r)) :
    Function.Bijective (modBaseChange f B s) :=
  ⟨LinearMap.injective_of_comp_eq_id _ _ (modBaseChangeInv_comp_modBaseChange f B s),
    LinearMap.surjective_of_comp_eq_id _ _ (modBaseChange_comp_modBaseChangeInv f B s)⟩

/-- **The base-change isomorphism at a single subset `s` of indices**,
`B ⊗_A A_{f|s} ≅ B_{g|s}`. -/
def modBaseChangeEquiv (s : Finset (Fin r)) :
    TensorProduct A B (Cech.cechMod f A s) ≃ₗ[B] Cech.cechMod (gfun f B) B s :=
  LinearEquiv.ofBijective (modBaseChange f B s) (modBaseChange_bijective f B s)

/-- `Stacks.CechRingBaseChange.modBaseChangeEquiv` applied to `x` is
`Stacks.CechRingBaseChange.modBaseChange` applied to `x`. -/
@[simp]
theorem modBaseChangeEquiv_apply (s : Finset (Fin r))
    (x : TensorProduct A B (Cech.cechMod f A s)) :
    modBaseChangeEquiv f B s x = modBaseChange f B s x := rfl

/-- The inverse of `Stacks.CechRingBaseChange.modBaseChangeEquiv` sends the change of rings of
`y ∈ A_{f|s}` to `1 ⊗ y`. -/
theorem modBaseChangeEquiv_symm_modMapAlg (s : Finset (Fin r)) (y : Cech.cechMod f A s) :
    (modBaseChangeEquiv f B s).symm (modMapAlg f B s y) = (1 : B) ⊗ₜ y := by
  have hone : modBaseChangeEquiv f B s ((1 : B) ⊗ₜ y) = modMapAlg f B s y := by
    rw [modBaseChangeEquiv_apply, modBaseChange_tmul, one_smul]
  rw [← hone, (modBaseChangeEquiv f B s).symm_apply_apply]

/-! ### The comparison on the terms of the complex -/

/-- **Change of rings on the degree-`p` term, for the ambient `A`-module structure.** This is
`Stacks.CechRingBaseChange.termMap` of `algebraMap A B`, repackaged as in
`Stacks.CechRingBaseChange.modMapAlg`. -/
def termMapAlg (p : ℕ) : Cech.cechTerm f A p →ₗ[A] Cech.cechTerm (gfun f B) B p where
  toFun z := termMap (algebraMap A B) f p z
  map_add' z w := map_add (termMap (algebraMap A B) f p) z w
  map_smul' a z := by
    rw [RingHom.id_apply, ← algebraMap_smul B a
      (show Cech.cechTerm (gfun f B) B p from termMap (algebraMap A B) f p z)]
    exact map_smul (termMap (algebraMap A B) f p) a z

/-- `Stacks.CechRingBaseChange.termMapAlg` acts on the summand indexed by `s` as
`Stacks.CechRingBaseChange.modMapAlg`. -/
theorem termMapAlg_lof (p : ℕ) (s : {t : Finset (Fin r) // t.card = p})
    (x : Cech.cechMod f A s.1) :
    termMapAlg f B p (DirectSum.lof A {t : Finset (Fin r) // t.card = p}
        (fun t => Cech.cechMod f A t.1) s x)
      = DirectSum.lof B {t : Finset (Fin r) // t.card = p}
          (fun t => Cech.cechMod (gfun f B) B t.1) s (modMapAlg f B s.1 x) :=
  termMap_lof (algebraMap A B) f p s x

/-- **The degreewise base-change comparison** `B ⊗_A C^p(f; A) → C^p(g; B)`: it sends `b ⊗ z` to
`b` times the change of rings of `z`. -/
def termBaseChange (p : ℕ) :
    TensorProduct A B (Cech.cechTerm f A p) →ₗ[B] Cech.cechTerm (gfun f B) B p :=
  LinearMap.liftBaseChange B (termMapAlg f B p)

/-- `Stacks.CechRingBaseChange.termBaseChange` sends `b ⊗ z` to `b • termMapAlg f B p z`. -/
@[simp]
theorem termBaseChange_tmul (p : ℕ) (b : B) (z : Cech.cechTerm f A p) :
    termBaseChange f B p (b ⊗ₜ z) = b • termMapAlg f B p z :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- `Stacks.CechRingBaseChange.termBaseChange` sends `1 ⊗ x`, for `x` in the summand indexed by
`s`, to the change of rings of `x` in the summand indexed by `s`. -/
theorem termBaseChange_one_tmul_lof (p : ℕ) (s : {t : Finset (Fin r) // t.card = p})
    (x : Cech.cechMod f A s.1) :
    termBaseChange f B p ((1 : B) ⊗ₜ DirectSum.lof A {t : Finset (Fin r) // t.card = p}
        (fun t => Cech.cechMod f A t.1) s x)
      = DirectSum.lof B {t : Finset (Fin r) // t.card = p}
          (fun t => Cech.cechMod (gfun f B) B t.1) s (modMapAlg f B s.1 x) := by
  rw [termBaseChange_tmul, one_smul, termMapAlg_lof]

/-- The degreewise inverse comparison: on the summand indexed by `s` it is the inverse of
`Stacks.CechRingBaseChange.modBaseChangeEquiv` followed by the base change of the inclusion of
that summand. -/
def termBaseChangeInv (p : ℕ) :
    Cech.cechTerm (gfun f B) B p →ₗ[B] TensorProduct A B (Cech.cechTerm f A p) :=
  DirectSum.toModule B {t : Finset (Fin r) // t.card = p} _ (fun s =>
    (LinearMap.baseChange B (DirectSum.lof A {t : Finset (Fin r) // t.card = p}
      (fun t => Cech.cechMod f A t.1) s)).comp (modBaseChangeEquiv f B s.1).symm.toLinearMap)

/-- `Stacks.CechRingBaseChange.termBaseChangeInv` acts on the summand indexed by `s` as the
inverse of `Stacks.CechRingBaseChange.modBaseChangeEquiv` followed by the base change of the
inclusion of that summand. -/
theorem termBaseChangeInv_lof (p : ℕ) (s : {t : Finset (Fin r) // t.card = p})
    (y : Cech.cechMod (gfun f B) B s.1) :
    termBaseChangeInv f B p (DirectSum.lof B {t : Finset (Fin r) // t.card = p}
        (fun t => Cech.cechMod (gfun f B) B t.1) s y)
      = LinearMap.baseChange B (DirectSum.lof A {t : Finset (Fin r) // t.card = p}
          (fun t => Cech.cechMod f A t.1) s) ((modBaseChangeEquiv f B s.1).symm y) := by
  rw [termBaseChangeInv, DirectSum.toModule_lof, LinearMap.comp_apply]
  rfl

/-- `Stacks.CechRingBaseChange.termBaseChangeInv` is a left inverse of
`Stacks.CechRingBaseChange.termBaseChange`. -/
theorem termBaseChangeInv_comp_termBaseChange (p : ℕ) :
    (termBaseChangeInv f B p).comp (termBaseChange f B p) = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro b
  apply DirectSum.linearMap_ext A
  intro s
  apply LinearMap.ext
  intro x
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.comp_apply, LinearMap.id_coe, id_eq]
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul, termBaseChange_one_tmul_lof,
    termBaseChangeInv_lof, modBaseChangeEquiv_symm_modMapAlg, LinearMap.baseChange_tmul,
    ← TensorProduct.tmul_eq_smul_one_tmul]

/-- `Stacks.CechRingBaseChange.termBaseChangeInv` is a right inverse of
`Stacks.CechRingBaseChange.termBaseChange`. -/
theorem termBaseChange_comp_termBaseChangeInv (p : ℕ) :
    (termBaseChange f B p).comp (termBaseChangeInv f B p) = LinearMap.id := by
  refine DirectSum.linearMap_ext B fun s => LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
  obtain ⟨z, rfl⟩ : ∃ z, modBaseChangeEquiv f B s.1 z = y :=
    ⟨(modBaseChangeEquiv f B s.1).symm y, (modBaseChangeEquiv f B s.1).apply_symm_apply y⟩
  rw [termBaseChangeInv_lof, (modBaseChangeEquiv f B s.1).symm_apply_apply]
  induction z with
  | tmul b x =>
      rw [LinearMap.baseChange_tmul, modBaseChangeEquiv_apply, modBaseChange_tmul,
        TensorProduct.tmul_eq_smul_one_tmul, map_smul, termBaseChange_one_tmul_lof, map_smul]
  | add z w hz hw =>
      rw [map_add, map_add, map_add, map_add, hz, hw]

/-- **The degreewise comparison is bijective.** -/
theorem termBaseChange_bijective (p : ℕ) : Function.Bijective (termBaseChange f B p) :=
  ⟨LinearMap.injective_of_comp_eq_id _ _ (termBaseChangeInv_comp_termBaseChange f B p),
    LinearMap.surjective_of_comp_eq_id _ _ (termBaseChange_comp_termBaseChangeInv f B p)⟩

/-- **The degreewise base-change isomorphism** `B ⊗_A C^p(f; A) ≅ C^p(g; B)`. -/
def termBaseChangeEquiv (p : ℕ) :
    TensorProduct A B (Cech.cechTerm f A p) ≃ₗ[B] Cech.cechTerm (gfun f B) B p :=
  LinearEquiv.ofBijective (termBaseChange f B p) (termBaseChange_bijective f B p)

/-- The degreewise base-change isomorphism sends `1 ⊗ z` to the change of rings of `z`. -/
theorem termBaseChangeEquiv_one_tmul (p : ℕ) (z : Cech.cechTerm f A p) :
    termBaseChangeEquiv f B p ((1 : B) ⊗ₜ z) = termMap (algebraMap A B) f p z := by
  show termBaseChange f B p ((1 : B) ⊗ₜ z) = _
  rw [termBaseChange_tmul, one_smul]
  rfl

end OverAnAlgebra

/-! ### The transpose across extension of scalars -/

section Transpose

variable {A B : Type u} [CommRing A] [CommRing B] {r : ℕ}

/-- **The degreewise base-change isomorphism**, in the `ModuleCat` spelling of extension of
scalars: `B ⊗_A C^p(f; A) ≅ C^p(g; B)`. -/
def termExtendScalarsIso (φ : A →+* B) (f : Fin r → A) (p : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj ((Cech.cechComplex f A).X p) ≅
      (Cech.cechComplex (mapFamily φ f) B).X p :=
  let _ := φ.toAlgebra
  (termBaseChangeEquiv f B p).toModuleIso

/-- `Stacks.CechRingBaseChange.termExtendScalarsIso` sends `1 ⊗ z` to the change of rings
`termMap φ f p z`. -/
theorem termExtendScalarsIso_hom_one_tmul (φ : A →+* B) (f : Fin r → A) (p : ℕ)
    (z : Cech.cechTerm f A p) :
    (termExtendScalarsIso φ f p).hom ((1 : B) ⊗ₜ[A,φ] z) = termMap φ f p z := by
  let _ := φ.toAlgebra
  show termBaseChangeEquiv f B p ((1 : B) ⊗ₜ[A] z) = _
  exact termBaseChangeEquiv_one_tmul f B p z

/-- A map `u : X → Y` of an `A`-module to a `B`-module restricted to `A` has an invertible
transpose `B ⊗_A X → Y` as soon as the transpose is realized by an isomorphism, that is, by an
isomorphism `e : B ⊗_A X ≅ Y` with `e (1 ⊗ x) = u x`. -/
theorem isIso_homEquiv_symm (φ : A →+* B) {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
    (u : X ⟶ (ModuleCat.restrictScalars φ).obj Y)
    (e : (ModuleCat.extendScalars.{u, u, u} φ).obj X ≅ Y)
    (h : ∀ x : X, e.hom ((1 : B) ⊗ₜ[A,φ] x) = u x) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).homEquiv X Y).symm u) := by
  have hu : (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).homEquiv X Y e.hom = u :=
    ModuleCat.hom_ext (LinearMap.ext h)
  rw [← hu, Equiv.symm_apply_apply]
  infer_instance

/-- **The degreewise transpose of the change-of-rings map is an isomorphism:** the map
`B ⊗_A C^p(f; A) → C^p(g; B)`, `b ⊗ x ↦ b · (change of rings)(x)`, is invertible. -/
theorem isIso_transpose_termMap (φ : A →+* B) (f : Fin r → A) (p : ℕ) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).homEquiv
        ((Cech.cechComplex f A).X p)
        ((Cech.cechComplex (mapFamily φ f) B).X p)).symm ((complexMap φ f).f p)) :=
  isIso_homEquiv_symm φ _ (termExtendScalarsIso φ f p)
    (termExtendScalarsIso_hom_one_tmul φ f p)

/-- **The change-of-rings map of complexes, read on `ℤ`-indexed complexes.** The extended
alternating Čech complexes are indexed by `ℕ`; `Stacks.LocalCohomology.derivedBaseChange` is
about complexes indexed by `ℤ`, and this is `Stacks.CechRingBaseChange.complexMap` transported
along `ComplexShape.embeddingUpNat`, extension commuting with restriction of scalars. -/
def extendedComplexMap (φ : A →+* B) (f : Fin r → A) :
    (Cech.cechComplex f A).extend ComplexShape.embeddingUpNat ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Cech.cechComplex (mapFamily φ f) B).extend ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap (complexMap φ f) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (ModuleCat.restrictScalars φ)
      (Cech.cechComplex (mapFamily φ f) B) ComplexShape.embeddingUpNat).hom

/-- The transpose of a map of complexes is, in each degree, the transpose of its component: the
degreewise adjunction has the degreewise unit and counit. -/
theorem transpose_mapHomologicalComplex_f (φ : A →+* B)
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ ((ModuleCat.restrictScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) (i : ℤ) :
    ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).homEquiv K L).symm u).f i =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).homEquiv (K.X i) (L.X i)).symm
        (u.f i) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  rfl

/-- A degreewise invertible transpose is invertible. -/
theorem isIso_transpose_of_degreewise (φ : A →+* B)
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ ((ModuleCat.restrictScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L)
    (h : ∀ i : ℤ, IsIso (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).homEquiv
      (K.X i) (L.X i)).symm (u.f i))) :
    IsIso ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).homEquiv K L).symm u) := by
  have : ∀ i : ℤ, IsIso (((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).homEquiv K L).symm u).f i) := fun i => by
    rw [transpose_mapHomologicalComplex_f]
    exact h i
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The transpose `B ⊗_A C^•(f; A) → C^•(g; B)` is an isomorphism of complexes.** In the degrees
coming from the Čech complex it is the degreewise base-change isomorphism, read through the
canonical identifications of the extended complexes with their terms; in the remaining degrees
both complexes are zero, and so is their extension of scalars. -/
theorem isIso_transpose_extendedComplexMap (φ : A →+* B) (f : Fin r → A) :
    IsIso ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv
        ((Cech.cechComplex f A).extend ComplexShape.embeddingUpNat)
        ((Cech.cechComplex (mapFamily φ f) B).extend ComplexShape.embeddingUpNat)).symm
      (extendedComplexMap φ f)) := by
  refine isIso_transpose_of_degreewise φ _ fun i => ?_
  cases hi : ComplexShape.embeddingUpNat.r i with
  | none =>
      have hz : IsZero ((ModuleCat.extendScalars.{u, u, u} φ).obj
          (((Cech.cechComplex f A).extend ComplexShape.embeddingUpNat).X i)) :=
        Functor.map_isZero _ ((Cech.cechComplex f A).isZero_extend_X' _ i hi)
      have hz' : IsZero (((Cech.cechComplex (mapFamily φ f) B).extend
          ComplexShape.embeddingUpNat).X i) :=
        (Cech.cechComplex (mapFamily φ f) B).isZero_extend_X' _ i hi
      exact ⟨⟨(hz.iso hz').inv, hz.eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
  | some n =>
      have hf : ComplexShape.embeddingUpNat.f n = i :=
        ComplexShape.Embedding.f_eq_of_r_eq_some _ hi
      have := isIso_transpose_termMap φ f n
      rw [extendedComplexMap, HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
        (ModuleCat.restrictScalars φ) (Cech.cechComplex (mapFamily φ f) B) (complexMap φ f)
        ComplexShape.embeddingUpNat hf, Adjunction.homEquiv_naturality_left_symm,
        Adjunction.homEquiv_naturality_right_symm]
      infer_instance

/-- **The derived base change of the Čech complex is an isomorphism.** The map
`C^•(f₁, …, f_r; A) ⊗^L_A B → C^•(g₁, …, g_r; B)` induced by the change-of-rings map of item (3)
is an isomorphism in `D(B)`: the Čech complex of a ring is K-flat, so the derived base change is
computed by the degreewise one, which is an isomorphism because each
`B ⊗_A A_{f_{i_0} \cdots f_{i_{p-1}}} → B_{g_{i_0} \cdots g_{i_{p-1}}}` is. -/
@[stacks 099D "condition (c) for a pair with a chosen finite generating family"]
theorem isIso_derivedBaseChange_extendedComplexMap (φ : A →+* B) (f : Fin r → A) :
    IsIso (Stacks.LocalCohomology.derivedBaseChange φ (extendedComplexMap φ f)) := by
  have := isIso_transpose_extendedComplexMap φ f
  exact Stacks.LocalCohomology.isIso_derivedBaseChange_of_kFlat φ (extendedComplexMap φ f)
    (Cech.kFlat_extend_cechComplex f) inferInstance

end Transpose

section AdjointTranspose

open CochainComplex.DerivedExtensionScalars

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The unit `X → B ⊗_A X` of the extension/restriction adjunction. -/
abbrev extendUnit (X : ModuleCat.{u} A) :
    X ⟶ (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj X) :=
  (ModuleCat.extendRestrictScalarsAdj φ).unit.app X

/-- The element `1 ⊗ x` of the scalar extension `B ⊗_A X`. -/
def tensorOne (X : ModuleCat.{u} A) (x : X) : ↑((ModuleCat.extendScalars φ).obj X) :=
  (extendUnit φ X).hom x

/-- The adjoint transpose of a map `X ⟶ B ⊗_A Y`: the `B`-linear map out of the scalar
extension it induces. -/
abbrev adjointHom {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
    (g : X ⟶ (ModuleCat.restrictScalars φ).obj Y) :
    (ModuleCat.extendScalars φ).obj X ⟶ Y :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv X Y).symm g

/-- The adjoint transpose agrees with the original map on the elements `1 ⊗ x`. -/
theorem adjointHom_tensorOne {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
    (g : X ⟶ (ModuleCat.restrictScalars φ).obj Y) (x : X) :
    (adjointHom φ g).hom (tensorOne φ X x) = g.hom x := by
  have h := ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv X Y).apply_symm_apply g
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => (k : X ⟶ (ModuleCat.restrictScalars φ).obj Y).hom x) h

/-- Extension and restriction of scalars on cochain complexes are adjoint. -/
def complexAdj :
    (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) :=
  letI : (ModuleCat.extendScalars φ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  (ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The model of derived extension of scalars that `Stacks.LocalCohomology.derivedBaseChange`
is stated for. -/
abbrev derivedExtension := derivedExtensionScalarsGeneral.{u, u, u} φ

/-- The complex-level adjoint of `u`, read in `D(B)` as a morphism out of the degreewise
extension of scalars. -/
def derivedComplexAdjoint {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :
    (extensionOfScalarsComplexGeneral.{u, u, u} φ).obj K ⟶ DerivedCategory.Q.obj L :=
  DerivedCategory.Q.map (((complexAdj φ).homEquiv K L).symm u)

/-- **The base-change comparison of `D(B)` is computed by the complex-level adjoint.** For a map
`u : K → L` from a complex of `A`-modules to a complex of `B`-modules restricted to `A`, the
morphism `K ⊗^L_A B → L` of `D(B)` is the comparison of the derived functor with degreewise
extension of scalars, followed by the localization of the adjoint `B ⊗_A K → L`.

This is `Stacks.LocalCohomology.derivedBaseChange_eq` with the adjoint named. -/
theorem derivedBaseChange_eq {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :
    Stacks.LocalCohomology.derivedBaseChange φ u =
      (derivedExtension φ).comparison.app K ≫ derivedComplexAdjoint φ u :=
  Stacks.LocalCohomology.derivedBaseChange_eq φ u

/-- **A criterion for condition (c) of [Stacks, Tag 099D].** If the source complex `K` is K-flat
and the adjoint `B ⊗_A K ⟶ L` of a map `u : K ⟶ L` of complexes of `A`-modules is a
quasi-isomorphism, then the base-change comparison `K ⊗^L_A B ⟶ L` is an isomorphism in `D(B)`.

This is `Stacks.LocalCohomology.isIso_derivedBaseChange_of_kFlat` with the hypothesis on the
adjoint stated as a quasi-isomorphism of complexes. -/
theorem isIso_derivedBaseChange_of_kFlat {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : CochainComplex (ModuleCat.{u} B) ℤ} (hK : CochainComplex.KFlat.{u, u} K)
    (u : K ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (hu : QuasiIso (((complexAdj φ).homEquiv K L).symm u)) :
    IsIso (Stacks.LocalCohomology.derivedBaseChange φ u) :=
  have := hu
  Stacks.LocalCohomology.isIso_derivedBaseChange_of_kFlat φ u hK
    (inferInstanceAs (IsIso (DerivedCategory.Q.map (((complexAdj φ).homEquiv K L).symm u))))

end AdjointTranspose

end Stacks.CechRingBaseChange

end

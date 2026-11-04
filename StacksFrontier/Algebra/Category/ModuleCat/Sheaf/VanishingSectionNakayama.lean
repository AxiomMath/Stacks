module

public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization

/-!
# A section that vanishes at a point: the converse of clause 2 of Tag 01CY

Let `(X, O_X)` be a ringed space all of whose stalks are local rings, let `L` be a sheaf of
`O_X`-modules with a global section `s`, and let `F` be another sheaf of `O_X`-modules.
Multiplication by `s`,

`F ≅ F ⊗ O_X --(1 ⊗ s)--> F ⊗ L`,

is bijective on the stalk at every point of the nonvanishing locus `X_s`; that is clause 2 of
[Stacks, Tag 01CY], and in this repository it is
`Stacks.SheafOfModules.bijective_stalkMapL_of_mem_nonvanishingLocus` whiskered by `F`
(`Stacks.SectionProduct.bijective_mapFun_mulRight_of_le_nonvanishingLocus`).

This file proves the **converse at a vanishing point**: if `s` vanishes at `x` — that is, if `x`
is *not* in the nonvanishing locus — then multiplication by `s` cannot be surjective on the
stalk at `x` unless that stalk is zero. This is Nakayama's lemma, and it is the only direction
in which a surjectivity hypothesis gives information about the module rather than about the
section.

## The route

Vanishing of `s` at `x` is *by definition* the statement that the germ of `s` lies in
`𝔪_x L_x` (`Stacks.SheafOfModules.nonvanishingLocus`), so the whole argument is a chase of the
submodule `I • ⊤` through the two structural facts about stalks:

* the stalk of `O_X` as a module over itself is free on the germ of the unit section
  (`Stacks.SheafOfModules.unitStalkLinearEquiv`), and the stalk map of `s : O_X ⟶ L` carries
  that germ to the germ of `s` (`Stacks.SheafOfModules.stalkMapL_unitGerm`) — so the *range* of
  that stalk map lies in `𝔪_x L_x`;
* the stalk of a tensor product is the tensor product of the stalks
  ([Stacks, Tag 01CB], `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`) and that
  identification is natural
  (`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_natural`) — so whiskering by `F`
  keeps the range inside `𝔪_x (F ⊗ L)_x`, because `a ⊗ (r • b) = r • (a ⊗ b)`.

A surjection whose range lies in `𝔪_x` times the target therefore forces the target stalk to
equal `𝔪_x` times itself, and Nakayama
(`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, [Stacks, Tag 00DV]) kills it. The finiteness
Nakayama needs is carried as a hypothesis on the one stalk, not as a finiteness condition on the
sheaf: that is all the argument uses, and a consumer holding a coherent module supplies it from
coherence at the point.

## Main results

* `Stacks.SheafOfModules.map_mem_ideal_smul_top`, `Stacks.SheafOfModules.tmul_mem_smul_top` and
  `Stacks.SheafOfModules.map_mem_smul_top_of_range_le`: the submodule `I • ⊤` is carried into
  `I • ⊤` by a linear map, by tensoring with a fixed element, and by a tensor product of maps
  whose second factor has range in `I • ⊤`.
* `Stacks.SheafOfModules.eq_zero_of_top_le_maximalSmul`: **Nakayama**, in the form a surjectivity
  hypothesis delivers it.
* `Stacks.SheafOfModules.stalkMapL_unitHomEquiv_symm_mem_maximalSmul`: **the stalk map of a
  section vanishing at `x` has its range inside `𝔪_x L_x`.**
* `Stacks.SheafOfModules.stalkMapL_tensorSheafMap_mem_maximalSmul`: **that bound survives
  tensoring**, in either variable.
* `Stacks.SheafOfModules.eq_zero_of_surjective_stalkMapL_of_mem_maximalSmul`: a morphism
  surjective on one stalk whose range there lies in `𝔪_x` times the target kills that stalk.
* `Stacks.SheafOfModules.eq_zero_grpStalk_tensorSheaf_of_notMem_nonvanishingLocus`: **the
  converse of clause 2 of [Stacks, Tag 01CY] at a vanishing point** — if `s` vanishes at `x` and
  multiplication by `s` is surjective on the stalk of `F ⊗ L` at `x`, then that stalk is zero.

## What this is not

It is **not** a statement about the support of a cokernel on a scheme. Surjectivity on one
stalk is equivalent to missing the support of the cokernel there
(`AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel`), and the
twists of a coherent triple spell multiplication by a section as
`Stacks.Algebraization.mulSectionPowScheme`; composing the two with the statements here needs
the identification of `AlgebraicGeometry.stalkLinearMap` with
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL` and of the monoidal product of
`AlgebraicGeometry.Scheme.Modules` with `tensorSheaf`, neither of which is done here.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

/-! ### The submodule `I • ⊤` under linear maps and tensor products -/

section Algebra

variable {R : Type*} [CommRing R] {M N P Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

/-- A linear map carries `I • ⊤` into `I • ⊤`. -/
theorem map_mem_ideal_smul_top (I : Ideal R) (g : M →ₗ[R] N) {m : M}
    (hm : m ∈ I • (⊤ : Submodule R M)) : g m ∈ I • (⊤ : Submodule R N) := by
  have hle : Submodule.map g (I • (⊤ : Submodule R M)) ≤ I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  exact hle (Submodule.mem_map_of_mem hm)

/-- An elementary tensor whose second factor lies in `I • ⊤` lies in `I • ⊤`: this is
`a ⊗ (r • b) = r • (a ⊗ b)`, read through the linear map `b ↦ a ⊗ b`. -/
theorem tmul_mem_smul_top (I : Ideal R) (a : M) {b : N}
    (hb : b ∈ I • (⊤ : Submodule R N)) :
    a ⊗ₜ[R] b ∈ I • (⊤ : Submodule R (M ⊗[R] N)) :=
  map_mem_ideal_smul_top I (TensorProduct.mk R M N a) hb

/-- **A tensor product of linear maps whose second factor has range inside `I • ⊤` has range
inside `I • ⊤`.** Nothing is asked of the first factor. -/
theorem map_mem_smul_top_of_range_le (I : Ideal R) (f : M →ₗ[R] P) (g : N →ₗ[R] Q)
    (hg : ∀ b, g b ∈ I • (⊤ : Submodule R Q)) (z : M ⊗[R] N) :
    TensorProduct.map f g z ∈ I • (⊤ : Submodule R (P ⊗[R] Q)) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul a b => rw [TensorProduct.map_tmul]; exact tmul_mem_smul_top I (f a) (hg b)
  | add y w hy hw => rw [map_add]; exact Submodule.add_mem _ hy hw

/-- **Nakayama's lemma** ([Stacks, Tag 00DV]) in the form a surjectivity hypothesis delivers it:
a finite module over a local ring which is contained in `𝔪` times itself is zero. -/
theorem eq_zero_of_top_le_maximalSmul [IsLocalRing R] [Module.Finite R M]
    (h : (⊤ : Submodule R M) ≤ maximalIdeal R • (⊤ : Submodule R M)) (m : M) : m = 0 := by
  have hbot : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤ Module.Finite.fg_top h
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top])
  exact (Submodule.eq_bot_iff _).mp hbot m Submodule.mem_top

end Algebra

/-! ### The range of the stalk map of a vanishing section -/

section Stalk

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- **A section vanishing at `x` has its germ in `𝔪_x L_x`**: that is what the nonvanishing
locus is defined to exclude. -/
theorem globalGerm_mem_maximalSmul_of_notMem_nonvanishingLocus
    (L : _root_.SheafOfModules.{u} (structureSheafRing X)) (s : L.sections) {x : X.carrier}
    (hx : x ∉ nonvanishingLocus L s) :
    globalGerm L s x ∈ maximalIdeal (ringStalk X x) •
      (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) :=
  not_not.mp hx

/-- **The stalk map of a section vanishing at `x` has its whole range inside `𝔪_x L_x`.** The
stalk of `O_X` as a module over itself is free on the germ of the unit section, which the stalk
map carries to the germ of the section. -/
theorem stalkMapL_unitHomEquiv_symm_mem_maximalSmul
    (L : _root_.SheafOfModules.{u} (structureSheafRing X)) (s : L.sections) {x : X.carrier}
    (hx : x ∉ nonvanishingLocus L s)
    (u : grpStalk X (_root_.SheafOfModules.unit (structureSheafRing X)).val x) :
    stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val L.val
        (L.unitHomEquiv.symm s).val x u
      ∈ maximalIdeal (ringStalk X x) •
        (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) := by
  obtain ⟨r, hr⟩ := (unitStalkLinearEquiv X x).surjective u
  have hru : u = r • unitGerm X x := by
    rw [← hr]
    simp [unitStalkLinearEquiv, LinearMap.toSpanSingleton_apply]
  rw [hru, map_smul, stalkMapL_unitGerm]
  exact Submodule.smul_mem _ r
    (globalGerm_mem_maximalSmul_of_notMem_nonvanishingLocus L s hx)

/-- **A bound on the range of a stalk map by `𝔪_x` times the target survives tensoring.** The
stalk of a tensor product is the tensor product of the stalks ([Stacks, Tag 01CB]) and that
identification is natural, so the statement is
`Stacks.SheafOfModules.map_mem_smul_top_of_range_le` read through two linear equivalences. -/
theorem stalkMapL_tensorSheafMap_mem_maximalSmul
    {F F' G G' : _root_.SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ F') (g : G ⟶ G')
    {x : X.carrier}
    (hg : ∀ u, stalkMapL X G.val G'.val g.val x u ∈
      maximalIdeal (ringStalk X x) • (⊤ : Submodule (ringStalk X x) (grpStalk X G'.val x)))
    (z : grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F)).obj (G))).val x) :
    letI := stalkModule X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G).val x
    letI := stalkModule X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F').obj G').val x
    stalkMapL X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F)).obj (G))).val
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F')).obj (G'))).val
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
        ((φ, g) : (_, _) ⟶ (_, _)))).val x z
      ∈ maximalIdeal (ringStalk X x) •
        (⊤ : Submodule (ringStalk X x)
          (grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F')).obj (G'))).val x)) := by
  let := stalkModule X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G).val x
  let := stalkModule X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F').obj G').val x
  have key := LinearMap.congr_fun (tensorStalkIso_natural X x F G F' G' φ g) z
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe] at key
  have hmem := map_mem_smul_top_of_range_le (maximalIdeal (ringStalk X x))
    (stalkMapL X F.val F'.val φ.val x) (stalkMapL X G.val G'.val g.val x) hg
    ((tensorStalkIso X x F G) z)
  rw [key] at hmem
  have h2 := map_mem_ideal_smul_top (maximalIdeal (ringStalk X x))
    (tensorStalkIso X x F' G').symm.toLinearMap hmem
  rwa [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2

/-- **Nakayama at one stalk.** A morphism of sheaves of modules which is surjective on the stalk
at `x` and whose range there lies inside `𝔪_x` times the target kills that stalk, provided it is
finite over the local ring `O_{X,x}`. -/
theorem eq_zero_of_surjective_stalkMapL_of_mem_maximalSmul
    {M N : _root_.SheafOfModules.{u} (structureSheafRing X)} (φ : M ⟶ N) {x : X.carrier}
    (hfin : Module.Finite (ringStalk X x) (grpStalk X N.val x))
    (hsurj : Function.Surjective (stalkMapL X M.val N.val φ.val x))
    (hrange : ∀ m, stalkMapL X M.val N.val φ.val x m ∈
      maximalIdeal (ringStalk X x) • (⊤ : Submodule (ringStalk X x) (grpStalk X N.val x)))
    (n : grpStalk X N.val x) : n = 0 := by
  have := hfin
  have htop : (⊤ : Submodule (ringStalk X x) (grpStalk X N.val x)) ≤
      maximalIdeal (ringStalk X x) • (⊤ : Submodule (ringStalk X x) (grpStalk X N.val x)) := by
    intro y _
    obtain ⟨m, hm⟩ := hsurj y
    exact hm ▸ hrange m
  exact eq_zero_of_top_le_maximalSmul htop n

/-- **The converse of clause 2 of [Stacks, Tag 01CY] at a vanishing point.** If the global
section `s` of `L` vanishes at `x` and multiplication by `s` is surjective on the stalk of
`F ⊗ L` at `x`, then that stalk is zero.

Clause 2 itself says that at a point of the nonvanishing locus multiplication by `s` is
bijective on stalks, for every `F`; this says that where the section vanishes, surjectivity can
only happen for want of anything to be surjective onto. The hypothesis is surjectivity on the
single stalk at `x`, which is exactly the vanishing there of the cokernel of multiplication by
`s`. -/
theorem eq_zero_grpStalk_tensorSheaf_of_notMem_nonvanishingLocus
    (F L : _root_.SheafOfModules.{u} (structureSheafRing X)) (s : L.sections) {x : X.carrier}
    (hfin : letI := stalkModule X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj L).val x
      Module.Finite (ringStalk X x)
        (grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F)).obj (L))).val x))
    (hx : x ∉ nonvanishingLocus L s)
    (hsurj : Function.Surjective (stalkMapL X
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F)).obj
        ((_root_.SheafOfModules.unit (structureSheafRing X))))).val
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F)).obj (L))).val
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
        (((𝟙 F), (L.unitHomEquiv.symm s)) : (_, _) ⟶ (_, _)))).val x))
    (z : grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F)).obj (L))).val x) :
    z = 0 := by
  let := stalkModule X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj L).val x
  have hrange := stalkMapL_tensorSheafMap_mem_maximalSmul (𝟙 F) (L.unitHomEquiv.symm s)
    (stalkMapL_unitHomEquiv_symm_mem_maximalSmul L s hx)
  exact eq_zero_of_surjective_stalkMapL_of_mem_maximalSmul _ hfin hsurj hrange z

end Stalk

end Stacks.SheafOfModules

end

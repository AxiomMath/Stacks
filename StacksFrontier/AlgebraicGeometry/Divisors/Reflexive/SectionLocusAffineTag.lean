module

public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusColimitSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.OpenImmersionStalkCriterion
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0EBR]: the isomorphism locus has affine inclusion exactly when `s` is nilpotent
on the complement

Let `X` be an integral locally Noetherian normal scheme, let `ℱ` be a rank one coherent reflexive
`𝒪_X`-module, let `s ∈ Γ(X, ℱ)`, and let

`U = {x ∈ X | s : 𝒪_{X, x} → ℱ_x is an isomorphism}`

be the open subscheme of [Stacks, Tag 0EBN].  [Stacks, Tag 0EBR] states that the inclusion
`j : U → X` is affine if and only if for every `x ∈ X \ U` there is an `n > 0` with
`sⁿ ∈ 𝔪_x ℱ^{[n]}_x`.  Both directions are proved here, **with no carried hypothesis.**

## Main results

* `exists_pos_sectionPowStalk_mem_smul_maximalIdeal_of_isAffineHom`:
  **[Stacks, Tag 0EBR], (1) ⇒ (2).**
* `isAffineHom_of_forall_exists_pos_sectionPowStalk_mem_smul_maximalIdeal`:
  **[Stacks, Tag 0EBR], (2) ⇒ (1).**

Both are in the namespace `Stacks.AlgebraicGeometry.SectionLocusAffine`, with the infrastructure
they consume.

## Implementation notes

**Where the two formerly carried hypotheses went.**  An earlier form of these two statements
carried `hcol`, the colimit clause `Γ(U_x, 𝒪_{U_x}) = colim ℱ^{[n]}_x` of [Stacks, Tag 0EBN],
and — in the direction (2) ⇒ (1) — `haff`, the implication from `𝔪_x Γ(U_x, 𝒪_{U_x}) = (1)` off
`U` to affineness of `j`.  Both are now theorems.

* `hcol` is `Stacks.AlgebraicGeometry.ReflexivePowers.nonempty_isStalkColimit_of_isColimit` fed
  with `…nonempty_isColimit_reflexivePowerSystemPushforwardCocone`, the colimit clause of
  [Stacks, Tag 0EBN] proved on sections over the affine opens in
  `SectionLocusColimitSections.lean`.
* `haff` is `AlgebraicGeometry.isAffineHom_of_forall_map_maximalIdeal_eq_top`: a quasi-compact
  open immersion is affine as soon as the maximal ideal generates the unit ideal in the stalk of
  `j_*𝒪_U` at every point off `U`.  That is proved through the relative spectrum of `j_*𝒪_U`, so
  it needs neither the cohomological criterion [Stacks, Tag 0EBE] nor [Stacks, Tag 02KH] outside
  the affine case, which is what the source's own argument for this half uses and what an earlier
  note recorded as the obstruction.

**The `𝒪_{X, x}`-algebra structure is no longer a binder.**  The earlier statements took the
algebra structure on `Γ(U_x, 𝒪_{U_x})` as an instance binder together with a hypothesis `halg`
pinning its `algebraMap` to the restriction map `specRes`.  Neither conclusion mentions that
algebra, so both are now supplied internally: the forward direction installs
`(specRes …).hom.toAlgebra` by a `letI`, and the converse works with
`(j_*𝒪_U)_x` instead, whose `𝒪_{X, x}`-algebra structure is the canonical instance
`AlgebraicGeometry.Scheme.Hom.algebra_stalk_pushforwardStalk`.

**Why the vanishing of `s` is split off.**  The cocone of [Stacks, Tag 0EBN] cannot even be
written down without `[Nonempty U]`, because the trivialization `ℱ^{[n]}|_U ≅ 𝒪_U` it is built
from goes through the rank-one comparison with the tensor powers.  `U` is nonempty exactly when
`s ≠ 0`: a nonzero section of a rank one coherent reflexive module trivializes it at the generic
point (`…nonempty_sectionIsomorphismOpen`, which is where the source's hypotheses `hF` and
`hrank` are spent), and conversely `s = 0` makes the stalk map zero, hence never bijective.  So
`s = 0` is handled separately, and there it is trivial: `U = ∅`, every `sⁿ` is zero, and the
inclusion of an empty open subscheme is affine.

**`hF` and `hrank` are the source's own hypotheses** and are kept.  They are used exactly once,
to make `U` nonempty when `s ≠ 0`; [Stacks, Tag 0EBN] is false without them.

## References

* [Stacks Project, Tag 0EBR](https://stacks.math.columbia.edu/tag/0EBR)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexivePowers
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.SectionLocusAffine

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-! ### Two degenerate facts about a vanishing section -/

/-- **A vanishing section trivializes no stalk**: its stalk map is multiplication by the zero
germ, which is injective only in the zero ring, and the local ring of a scheme is not zero. -/
theorem isEmpty_sectionIsomorphismLocus_of_eval_eq_zero (F : X.Modules) [F.IsCoherent]
    (s : F.sections)
    (hs : s.eval (op (⊤ : X.Opens)) = 0) :
    IsEmpty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme := by
  refine ⟨fun z => ?_⟩
  have hb := (mem_sectionIsomorphismLocus_iff_bijective_stalkMapL F s z.1).mp z.2
  have hcomp : ∀ a, (stalkMapL X.toRingedSpace
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val F.val
        (F.unitHomEquiv.symm s).val z.1)
        (Stacks.SheafOfModules.unitStalkLinearEquiv X.toRingedSpace z.1 a) =
      a • Stacks.SheafOfModules.globalGerm F s z.1 :=
    fun a => Stacks.SheafOfModules.stalkMapL_unitStalkLinearEquiv F s z.1 a
  have hzero : Stacks.SheafOfModules.globalGerm F s z.1 = 0 := by
    refine ((Stacks.SheafOfModules.grpGerm_eval s z.1 ⊤ trivial).symm).trans ?_
    rw [hs]
    exact map_zero _
  have h1 : (stalkMapL X.toRingedSpace
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val F.val
      (F.unitHomEquiv.symm s).val z.1)
      (Stacks.SheafOfModules.unitStalkLinearEquiv X.toRingedSpace z.1 1) =
      (stalkMapL X.toRingedSpace
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val F.val
      (F.unitHomEquiv.symm s).val z.1)
      (Stacks.SheafOfModules.unitStalkLinearEquiv X.toRingedSpace z.1 0) := by
    rw [hcomp, hcomp, hzero, smul_zero, smul_zero]
  exact one_ne_zero
    ((Stacks.SheafOfModules.unitStalkLinearEquiv X.toRingedSpace z.1).injective (hb.1 h1))

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- **A vanishing section has vanishing first power**: the transition `𝒪_X ⟶ ℱ` out of degree `0`
is multiplication by `s`, so it kills the unit section. -/
theorem sectionPowStalk_one_eq_zero (F : X.Modules) (s : F.sections) (x : X)
    (hs : s.eval (op (⊤ : X.Opens)) = 0) : sectionPowStalk X F s x 1 = 0 := by
  show reflexivePowerStalkMap F s x 0 (reflexivePowerUnit F x) = 0
  refine (Stacks.ModuleSkyscraper.stalkMapLinear_germ
    (reflexivePowerTransition F s 0).val x ⊤ trivial (1 : Γ(X, (⊤ : X.Opens)))).trans ?_
  rw [reflexivePowerTransition_zero]
  refine Eq.trans (congrArg _ ((unitHomEquiv_symm_app_unitSection F s ⊤).trans hs)) ?_
  exact map_zero _

/-! ### The colimit input the carriers used to receive from outside -/

/-- **The colimit clause of [Stacks, Tag 0EBN] at a point, with `(j_*𝒪_U)_x` as the colimit.**

This is the form the converse direction of [Stacks, Tag 0EBR] uses: the vertex of the cocone of
[Stacks, Tag 0EBN] is `j_*𝒪_U`, so the identification of its stalk with the colimit of the
`ℱ^{[n]}_x` costs only `AlgebraicGeometry.pushforwardUnitStalkLinearEquiv`, the comparison of the
module stalk with the ring stalk, and no quasi-compactness of `j` and no `Γ(U_x, 𝒪_{U_x})`
enter. -/
theorem nonempty_isStalkColimit_pushforwardStalk (F : X.Modules) [F.IsCoherent]
    (s : F.sections) [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme]
    (hF : ReflexiveModules.IsReflexive F) (x : X) :
    Nonempty (IsStalkColimit F s x
      ↑((AlgebraicGeometry.sectionIsomorphismOpen X F s).ι.pushforwardStalk x)) := by
  obtain ⟨hc⟩ := nonempty_isColimit_reflexivePowerSystemPushforwardCocone F s hF
  refine ⟨isStalkColimitOfIsColimit F s x hc _
    (pushforwardUnitStalkLinearEquiv (AlgebraicGeometry.sectionIsomorphismOpen X F s) x) ?_⟩
  exact (congrArg (pushforwardUnitStalkLinearEquiv
      (AlgebraicGeometry.sectionIsomorphismOpen X F s) x)
    (modulesStalkFunctor_map_cocone_ι_app_zero_unit F s x)).trans
    (pushforwardUnitStalkLinearEquiv_one _ x)

/-! ### Tag 0EBR -/

/-- **[Stacks, Tag 0EBR], (1) ⇒ (2).** With `X`, `ℱ`, `s` and `U` as in [Stacks, Tag 0EBN]:
if the inclusion `j : U → X` is affine, then for every `x ∈ X \ U` there is an `n > 0` with
`sⁿ ∈ 𝔪_x ℱ^{[n]}_x`.

The hypotheses are the source's: `X` integral, locally Noetherian and normal, `ℱ` coherent,
reflexive (`hF`) and of rank one (`hrank`, the fibre rank at the generic point), and `s` a global
section.  The reflexive powers, the multiplication by `s` and the power `sⁿ` are the constructed
ones of `ReflexivePowers.lean`.

If `s = 0` then `s¹ = 0` lies in every submodule and there is nothing to prove.  Otherwise `U`
contains the generic point, so the colimit clause of [Stacks, Tag 0EBN] is available at `x`; the
inverse image `U_x` of `U` under `f_x : Spec 𝒪_{X, x} ⟶ X` is affine because affineness of a
morphism is stable under base change, and it misses the closed point because `f_x` carries the
closed point to `x ∉ U`; so `𝔪_x Γ(U_x, 𝒪_{U_x})` is the unit ideal, and the colimit argument
`exists_pos_powElt_mem_smul` extracts the positive power. -/
@[stacks 0EBR "(1) ⇒ (2)"]
theorem exists_pos_sectionPowStalk_mem_smul_maximalIdeal_of_isAffineHom
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (F : X.Modules) [F.IsCoherent] (hF : ReflexiveModules.IsReflexive F)
    (hrank : Scheme.Modules.fiberRank F (genericPoint X) = 1) (s : F.sections)
    (hj : IsAffineHom (AlgebraicGeometry.sectionIsomorphismOpen X F s).ι)
    (x : X) (hx : x ∉ AlgebraicGeometry.sectionIsomorphismOpen X F s) :
    ∃ n, 0 < n ∧ sectionPowStalk X F s x n ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) •
      (⊤ : Submodule ↑(X.presheaf.stalk x) (reflexivePowerStalk F x n)) := by
  by_cases hs : s.eval (op (⊤ : X.Opens)) = 0
  · refine ⟨1, Nat.one_pos, ?_⟩
    rw [sectionPowStalk_one_eq_zero F s x hs]
    exact Submodule.zero_mem _
  have : Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme :=
    nonempty_sectionIsomorphismOpen X F s hF hrank hs
  have : IsAffineHom (AlgebraicGeometry.sectionIsomorphismOpen X F s).ι := hj
  let : Algebra ↑(X.presheaf.stalk x) ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x) :=
    (specRes (X.presheaf.stalk x) (stalkLocus X F s x)).hom.toAlgebra
  have halg : algebraMap ↑(X.presheaf.stalk x)
      ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x) =
      (specRes (X.presheaf.stalk x) (stalkLocus X F s x)).hom :=
    RingHom.algebraMap_toAlgebra _
  obtain ⟨hc⟩ := nonempty_isColimit_reflexivePowerSystemPushforwardCocone F s hF
  obtain ⟨hcol⟩ := nonempty_isStalkColimit_of_isColimit F s hc x halg
  have hVaff : IsAffineOpen (stalkLocus X F s x) :=
    isAffineOpen_preimage_of_isAffineHom _ _
  have htop := map_maximalIdeal_eq_top (X.presheaf.stalk x) (stalkLocus X F s x) hVaff
    (closedPoint_notMem_preimage (AlgebraicGeometry.sectionIsomorphismOpen X F s) x hx)
  refine exists_pos_powElt_mem_smul _ (reflexivePowerStalkMap F s x) (reflexivePowerUnit F x)
    hcol.toColimit hcol.comp_transition hcol.surjective hcol.eventually_zero ?_
  rw [hcol.map_one, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, halg, htop]
  exact Submodule.mem_top

/-- **[Stacks, Tag 0EBR], (2) ⇒ (1).** With `X`, `ℱ`, `s` and `U` as in [Stacks, Tag 0EBN]:
if for every `x ∈ X \ U` there is an `n > 0` with `sⁿ ∈ 𝔪_x ℱ^{[n]}_x`, then the inclusion
`j : U → X` is affine.

If `s = 0` then `U` is empty (`isEmpty_sectionIsomorphismLocus_of_eval_eq_zero`) and the
inclusion of an empty open subscheme is affine.  Otherwise `U` contains the generic point, the
colimit clause of [Stacks, Tag 0EBN] identifies `(j_*𝒪_U)_x` with `colim ℱ^{[n]}_x`, and
`mem_smul_of_powElt_mem_smul` carries clause (2) over to `1 ∈ 𝔪_x (j_*𝒪_U)_x`, which is
`𝔪_x (j_*𝒪_U)_x = (j_*𝒪_U)_x`, at every point off `U`.  That is exactly the hypothesis of
`AlgebraicGeometry.isAffineHom_of_forall_map_maximalIdeal_eq_top`, the relative-spectrum form of
the second half of the source's proof. -/
@[stacks 0EBR "(2) ⇒ (1)"]
theorem isAffineHom_of_forall_exists_pos_sectionPowStalk_mem_smul_maximalIdeal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (F : X.Modules) [F.IsCoherent] (hF : ReflexiveModules.IsReflexive F)
    (hrank : Scheme.Modules.fiberRank F (genericPoint X) = 1) (s : F.sections)
    (h₂ : ∀ x : X, x ∉ AlgebraicGeometry.sectionIsomorphismOpen X F s →
      ∃ n, 0 < n ∧ sectionPowStalk X F s x n ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) •
          (⊤ : Submodule ↑(X.presheaf.stalk x) (reflexivePowerStalk F x n))) :
    IsAffineHom (AlgebraicGeometry.sectionIsomorphismOpen X F s).ι := by
  by_cases hs : s.eval (op (⊤ : X.Opens)) = 0
  · have : IsEmpty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme :=
      isEmpty_sectionIsomorphismLocus_of_eval_eq_zero F s hs
    exact inferInstance
  have : Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme :=
    nonempty_sectionIsomorphismOpen X F s hF hrank hs
  refine isAffineHom_of_forall_map_maximalIdeal_eq_top _ fun x hx => ?_
  have hxU : x ∉ AlgebraicGeometry.sectionIsomorphismOpen X F s := fun hmem =>
    hx ⟨⟨x, hmem⟩, rfl⟩
  obtain ⟨hcol⟩ := nonempty_isStalkColimit_pushforwardStalk F s hF x
  obtain ⟨n, -, hn⟩ := h₂ x hxU
  have h1 := mem_smul_of_powElt_mem_smul _ (reflexivePowerStalkMap F s x)
    (reflexivePowerUnit F x) hcol.toColimit hcol.comp_transition hn
  rw [hcol.map_one, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at h1
  rw [← AlgebraicGeometry.Scheme.Hom.algebraMap_pushforwardStalk]
  exact Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one

end Stacks.AlgebraicGeometry.SectionLocusAffine

end

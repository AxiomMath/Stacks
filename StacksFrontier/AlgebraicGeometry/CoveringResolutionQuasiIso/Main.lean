module

public import StacksFrontier.AlgebraicGeometry.CoveringResolutionQuasiIso.Basic

/-!
# The augmented Čech complex of a covering is a resolution (Tag 02FU)

The augmentation of the Čech complex of an open covering of a ringed space is a
quasi-isomorphism, which is the last of the nine fields of
  `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`,
and with it `Stacks.CechTotalComplex.CoveringResolution.exists_coveringResolution`.

## Main results

* `exactAt_coveringComplex`: the Čech complex is exact in every positive degree.
* `augShortComplex_exact` and `mono_augZero`: the augmentation is a monomorphism and its
  image is the kernel of the first Čech differential — the sheaf condition for the covering,
  in the two halves the degree-zero quasi-isomorphism needs.
* `quasiIso_augmentationNatTrans`: **the `quasiIso` field**.
* `exists_coveringResolution`: **Tag 02FU**.

## Implementation notes

The route is the source's own: the explicit contracting homotopy, which exists over any open
set contained in a member of the covering, together with the criterion that exactness of a
complex of sheaves of modules is local on a covering family
(`Stacks.SheafOfModules.ComplexLocality`). The homotopy is
`StacksDraft.AlgebraicGeometry.F3.CoveringResolutionQuasiIso.Basic`; this file globalises it.
Three distinct statements are needed from the local picture, and the homotopy supplies all
three: exactness in positive degrees, surjectivity onto the degree-zero cycles, and
injectivity of the augmentation — the last because the homotopy is a *split* retraction in
degree `-1`.

`CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech` is **not** used. It produces an
extra degeneracy on the Čech object of a covering one of whose members is the whole space,
which is a statement about the site and not about sections over `V`; transporting it to the
local situation would mean changing the site to the opens below `V`, and then identifying the
two Čech complexes — strictly more work than the homotopy, which is four lines of
`Fin.succAbove` combinatorics. It is also stated for the alternating *face* complex of a
simplicial object, where the Čech cochain complex is the alternating *coface* complex of a
cosimplicial one.

The split of `QuasiIso` into degree zero and positive degrees follows Mathlib's own proof for
`CategoryTheory.InjectiveResolution.of`: `CochainComplex.quasiIsoAt₀_iff` with
`ShortComplex.quasiIso_iff_of_zeros` in degree zero, where the two halves are exactness and
monicity, and `quasiIsoAt_iff_exactAt` against `CochainComplex.exactAt_succ_single_obj` above
it. The sheafification instances the locality criterion asks for are the statement's own
`Stacks.CechTotalComplex.CoveringResolution.hasSheafify_opens` and
  `Stacks.CechTotalComplex.CoveringResolution.wEqualsLocallyBijective_opens`, at the module
universe `max u v w t`, so the four universes of the tagged statement stay independent and the
statement carries no hypothesis the tag lacks.

## References

* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
* [Stacks Project, Equation 01EE](https://stacks.math.columbia.edu/tag/01EE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open Stacks.CategoryTheory.CechComplex

universe u v w t

namespace Stacks.AlgebraicGeometry.CoveringResolutionQuasiIso

open Stacks.CechTotalComplex.CoveringResolution Stacks.AlgebraicGeometry.CoveringResolution

variable (X : TopCat.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
variable {ι : Type t} (U : ι → Opens X)

variable (F : SheafOfModules.{w} R)

/-- **The Čech complex of a covering is exact in positive degrees.** Exactness is local by
`Stacks.SheafOfModules.ComplexLocality`, and over an open set contained in a member of the
covering the contracting homotopy of `Basic.lean` produces the preimage. -/
theorem exactAt_coveringComplex (hU : ⨆ i, U i = ⊤) (p : ℕ) :
    ((coveringComplex.{u, v, w, t} X R U).obj F).ExactAt (p + 1) := by
  let _ := hasSheafify_opens.{u, max v w t} X
  let _ := wEqualsLocallyBijective_opens.{u, max v w t} X
  refine Stacks.SheafOfModules.ComplexLocality.exactAt_of_coversTop'
    ((coveringComplex.{u, v, w, t} X R U).obj F) (i := p) (k := p + 2)
    ((ComplexShape.up ℕ).prev_eq' rfl) ((ComplexShape.up ℕ).next_eq' rfl)
    ((Opens.coversTop_iff _ U).2 hU) ?_
  intro l W q z hz
  exact exists_preimage_succ.{u, v, w, t} X R U l F (leOfHom q) p z hz

/-- The short complex of the augmentation: the enlargement of `F`, the degree-zero Čech
term, and the degree-one Čech term. -/
noncomputable def augShortComplex : ShortComplex (SheafOfModules.{max u v w t} R) :=
  ShortComplex.mk (augZero.{u, v, w, t} X R U F)
    (((coveringComplex.{u, v, w, t} X R U).obj F).d 0 1) (augZero_comp_d X R U F)

/-- **The augmentation is the kernel of the first Čech differential, in the exactness
form.** -/
theorem augShortComplex_exact (hU : ⨆ i, U i = ⊤) :
    (augShortComplex.{u, v, w, t} X R U F).Exact := by
  let _ := hasSheafify_opens.{u, max v w t} X
  let _ := wEqualsLocallyBijective_opens.{u, max v w t} X
  refine Stacks.SheafOfModules.ComplexLocality.exact_of_isOpenCover U hU
    (augShortComplex.{u, v, w, t} X R U F) ?_
  intro l W hW z hz
  exact exists_preimage_zero.{u, v, w, t} X R U l F hW z hz

/-- **The augmentation is a monomorphism**: it is injective on sections over the open sets
contained in a member of the covering, and those cover `X`. -/
theorem mono_augZero (hU : ⨆ i, U i = ⊤) : Mono (augZero.{u, v, w, t} X R U F) := by
  let _ := hasSheafify_opens.{u, max v w t} X
  let _ := wEqualsLocallyBijective_opens.{u, max v w t} X
  refine (ShortComplex.exact_iff_mono
    (S := ShortComplex.mk (0 : (moduleUniverseLift.{u, v, w, t} X R).obj F ⟶ _)
      (augZero.{u, v, w, t} X R U F) (by simp)) rfl).1 ?_
  refine Stacks.SheafOfModules.ComplexLocality.exact_of_isOpenCover U hU _ ?_
  intro l W hW z hz
  refine ⟨0, ?_⟩
  rw [aug0_injective.{u, v, w, t} X R U l F hW hz, map_zero]

/-- **The `quasiIso` field of `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`**:
  every component of the
natural augmentation is a quasi-isomorphism. -/
theorem quasiIso_augmentationNatTrans (hU : ⨆ i, U i = ⊤) :
    haveI : ∀ q : ℕ, ((coveringComplex.{u, v, w, t} X R U).obj F).HasHomology q :=
      fun q => hasHomology_of_enlarged.{u, v, max w t} X R _ q
    QuasiIso ((augmentationNatTrans.{u, v, w, t} X R U).app F) := by
  let _ := hasSheafify_opens.{u, max v w t} X
  let _ := wEqualsLocallyBijective_opens.{u, max v w t} X
  refine ⟨fun n => ?_⟩
  match n with
  | 0 =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros _ rfl rfl
      (((coveringComplex.{u, v, w, t} X R U).obj F).shape 0 0 (by simp))]
    refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
      ⟨augShortComplex_exact.{u, v, w, t} X R U F hU,
        mono_augZero.{u, v, w, t} X R U F hU⟩
    refine ShortComplex.isoMk
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
        ((moduleUniverseLift.{u, v, w, t} X R).obj F)) (Iso.refl _) (Iso.refl _) ?_
      ((Category.id_comp _).trans (Category.comp_id _).symm)
    exact (Category.comp_id _).trans
      ((augmentationNatTrans_f_zero.{u, v, w, t} X R U F).trans (Category.id_comp _).symm)
  | p + 1 =>
    rw [quasiIsoAt_iff_exactAt]
    · exact exactAt_coveringComplex.{u, v, w, t} X R U F hU p
    · exact CochainComplex.exactAt_succ_single_obj
        ((moduleUniverseLift.{u, v, w, t} X R).obj F) p

/-- **Stacks Project, Tag 02FU.** Every open covering of a ringed space gives a canonical
augmented Čech resolution, functorial in the module sheaf: the complex, its augmentation,
the product coordinates of its terms with Equation 01EE for the differential, the existence
of homology, and the quasi-isomorphism. -/
@[stacks 02FU]
theorem exists_coveringResolution (hU : ⨆ i, U i = ⊤) :
    Nonempty (CoveringResolution.{u, v, w, t} X R U) :=
  ⟨coveringResolutionOfQuasiIso.{u, v, w, t} X R U
    fun G => quasiIso_augmentationNatTrans.{u, v, w, t} X R U G hU⟩

end Stacks.AlgebraicGeometry.CoveringResolutionQuasiIso

module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicStableKernelImage

/-!
# The stable kernel images over an affine chart, as quotients of one module

Let `F` be a Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and
`α : E ⟶ E'` a morphism of coherent `𝓘`-adic systems.  The second stabilization of Stacks 087X
compares the adic quotients of the stable kernel images
`AlgebraicGeometry.Space.stableKernelImage` at two levels, and on a scheme that comparison is
run through the affine presentation of Stacks 087W: every term of `E` is a quotient of one
completed module `M`, and the sections of the stable kernel image at level `k` are the image
under the `k`-th projection of a single submodule `K ⊆ M`, namely the kernel of the completed
map.

**This file produces that presentation over a Noetherian affine étale chart of an algebraic
space, without Stacks 087W.**  The module `M` is
`AlgebraicGeometry.Space.chartCompletedSections` — the `𝓘(V)`-adic completion of the inverse
limit of the tower of sections `n ↦ E_n(V)` — whose projections onto the levels are surjective
with kernel the ideal-power multiple by
`AlgebraicGeometry.Space.surjective_chartCompletedLevel` and
`AlgebraicGeometry.Space.ker_chartCompletedLevel`, and which is a finite module over the
Noetherian completed ring by
`AlgebraicGeometry.Space.moduleFinite_chartCompletedSections`.  The submodule `K` is the kernel
of the map of completed modules induced by `α`, and the two statements about it are the two
halves of Artin–Rees over the base ring: the identification of the sections of the stable kernel
image with `p_k(K)` uses
`Stacks.AdicCompletion.exists_map_comap_pow_smul_restrictScalars_eq`, and the containment
`ker p_k ∩ K ⊆ 𝓘(V) ^ (n + 1) K` for `k` large uses
`Stacks.AdicCompletion.exists_comap_subtype_pow_smul_restrictScalars_le`.

## Main results

* `AlgebraicGeometry.Space.exists_chartStableKernelImagePresentation` — **the presentation**: over
  a Noetherian affine chart there is one module with surjective projections onto the sections of
  the terms of `E`, compatible with the transition maps, and one submodule of it whose images are
  the sections of the stable kernel images, meeting the kernels of the projections inside the
  prescribed power of `𝓘(V)` once the level is large.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: the term at `n` is the Stacks source's
`E_{n + 1}`, which is why the annihilating exponent at level `n` is `n + 1`.

The constant produced by Artin–Rees for the identification of the sections of the stable kernel
image depends on the level `k`, and so does the auxiliary level `l` at which the kernel image is
computed; the conclusion does not mention either, the stabilization
`AlgebraicGeometry.Space.stableKernelImageIso` having already made the kernel image at every
sufficiently large level the same subobject of `E_k`.  The level `l` is taken above both the
global stabilization level of `E_k` and the chart-local Artin–Rees constant.

The Noetherian hypothesis is carried as the pair of explicit arguments `hZ`, `hN` spelling
`AlgebraicGeometry.Space.IsNoetherian`, together with quasi-coherence of `𝓘` in the form
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, exactly as
`AlgebraicGeometry.Space.stableKernelImage` needs them.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 00IN](https://stacks.math.columbia.edu/tag/00IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-- **The affine presentation of the stable kernel images over a Noetherian affine chart.**

There is a module `M` over the ring of the chart — the completion of the inverse limit of the
tower of sections of `E` — with surjective projections `p k : M ⟶ E_k(V)` compatible with the
transition maps of `E`, and a submodule `K ⊆ M` such that the sections of the stable kernel
image at level `k` are `p k '' K`, and such that for every exponent `n` the intersection of `K`
with the kernel of `p k` lies in `𝓘(V) ^ (n + 1) K` once `k` is large. -/
theorem exists_chartStableKernelImagePresentation (α : E ⟶ E')
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V) :
    ∃ (K : Submodule (chartRing B S hS F hF V)
        (chartCompletedSections B S hS F hF 𝓘 E.obj V))
      (p : ∀ k : ℕ, chartCompletedSections B S hS F hF 𝓘 E.obj V →ₗ[chartRing B S hS F hF V]
        (chartSectionsSystem B S hS F hF E.obj V).obj (op k)),
      (∀ k : ℕ, Function.Surjective (p k)) ∧
      (∀ (k l : ℕ) (h : k ≤ l),
          ((chartSectionsSystem B S hS F hF E.obj V).map (homOfLE h).op).hom.comp (p l) = p k) ∧
      (∀ k : ℕ, LinearMap.range
            ((stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α k).val.app (op V)).hom =
          Submodule.map (p k) K) ∧
      (∀ n : ℕ, ∃ c : ℕ, ∀ k : ℕ, n + c ≤ k →
          Submodule.comap K.subtype (LinearMap.ker (p k)) ≤
            chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
              (⊤ : Submodule (chartRing B S hS F hF V) K)) := by
  have hAnoeth : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  have hJfg : (chartSectionIdeal B S hS F hF 𝓘 V).FG := Ideal.fg_of_isNoetherianRing _
  have hcompl : ∀ G : CoherentAdicSystems B S hS F hF 𝓘,
      IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
        (chartSectionsLimit B S hS F hF G.obj V) :=
    fun G => isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 G.property hIcart hV
  have hfin : ∀ G : CoherentAdicSystems B S hS F hF 𝓘, Module.Finite
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V))
      (chartCompletedSections B S hS F hF 𝓘 G.obj V) :=
    fun G => moduleFinite_chartCompletedSections B S hS F hF 𝓘 G.property hIcart hV
  have hMc := hcompl E
  have hNc := hcompl E'
  set eM := Stacks.Coherent.completeModuleEquivAdicCompletion
    (M := chartSectionsLimit B S hS F hF E.obj V) (chartSectionIdeal B S hS F hF 𝓘 V) with heM
  set eN := Stacks.Coherent.completeModuleEquivAdicCompletion
    (M := chartSectionsLimit B S hS F hF E'.obj V) (chartSectionIdeal B S hS F hF 𝓘 V) with heN
  set fA : chartCompletedSections B S hS F hF 𝓘 E.obj V →ₗ[chartRing B S hS F hF V]
      chartCompletedSections B S hS F hF 𝓘 E'.obj V :=
    (eN.toLinearMap.comp (chartSectionsLimitMap B S hS F hF α.hom V).hom).comp
      eM.symm.toLinearMap with hfA
  set f : chartCompletedSections B S hS F hF 𝓘 E.obj V →ₗ[AdicCompletion
      (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)]
      chartCompletedSections B S hS F hF 𝓘 E'.obj V :=
    { toFun := fA
      map_add' := fA.map_add
      map_smul' := fun r x =>
        Stacks.Coherent.completion_linearMap_smul _ hJfg fA r x } with hf
  have hsquare : ∀ l : ℕ,
      (((chartSectionsSystemMap B S hS F hF α.hom V).app (op l)).hom).comp
          (chartCompletedLevel B S hS F hF 𝓘 E.obj hMc l) =
        (chartCompletedLevel B S hS F hF 𝓘 E'.obj hNc l).comp
          (f.restrictScalars (chartRing B S hS F hF V)) := by
    intro l
    refine LinearMap.ext fun x => ?_
    have hw := congrArg
      (fun g : chartSectionsLimit B S hS F hF E.obj V ⟶
          (chartSectionsSystem B S hS F hF E'.obj V).obj (op l) =>
        g.hom (eM.symm x))
      (chartSectionsLimitMap_chartSectionsLevel B S hS F hF α.hom V l)
    change ((chartSectionsSystemMap B S hS F hF α.hom V).app (op l)).hom
        ((chartSectionsLevel B S hS F hF E.obj V l).hom (eM.symm x)) = _
    change _ = (chartSectionsLevel B S hS F hF E'.obj V l).hom
      (eN.symm (eN ((chartSectionsLimitMap B S hS F hF α.hom V).hom (eM.symm x))))
    rw [eN.symm_apply_apply]
    exact hw.symm
  have hproj : ∀ (k l : ℕ) (h : k ≤ l),
      ((chartSectionsSystem B S hS F hF E.obj V).map (homOfLE h).op).hom.comp
          (chartCompletedLevel B S hS F hF 𝓘 E.obj hMc l) =
        chartCompletedLevel B S hS F hF 𝓘 E.obj hMc k := by
    intro k l h
    have hw := limit.w (chartSectionsSystem B S hS F hF E.obj V) (homOfLE h).op
    refine LinearMap.ext fun x => ?_
    exact congrArg
      (fun g : chartSectionsLimit B S hS F hF E.obj V ⟶
          (chartSectionsSystem B S hS F hF E.obj V).obj (op k) => g.hom (eM.symm x)) hw
  refine ⟨(LinearMap.ker f).restrictScalars (chartRing B S hS F hF V),
    fun k => chartCompletedLevel B S hS F hF 𝓘 E.obj hMc k,
    fun k => surjective_chartCompletedLevel B S hS F hF 𝓘 E.property hV.1 hMc k,
    hproj, ?_, ?_⟩
  · intro k
    obtain ⟨c, hc⟩ := Stacks.AdicCompletion.exists_map_comap_pow_smul_restrictScalars_eq
      (P := (chartSectionsSystem B S hS F hF E.obj V).obj (op k))
      (chartSectionIdeal B S hS F hF 𝓘 V) f
    have hkstab : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α k ≤
        max (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α k) (k + c) := le_max_left _ _
    have hkc : k + c ≤
        max (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α k) (k + c) := le_max_right _ _
    set l := max (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α k) (k + c) with hl
    have hkl : k ≤ l :=
      (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α k).trans hkstab
    -- the stable kernel image has the same sections as the kernel image computed at level `l`
    have hbij : Function.Bijective
        ((stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α k l hkstab).hom.val.app (op V)) :=
      bijective_moduleHom_app
        (stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α k l hkstab).hom
        (stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α k l hkstab).inv
        (stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α k l hkstab).hom_inv_id
        (stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α k l hkstab).inv_hom_id V
    have hcomp : ((stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α k).val.app
            (op V)).hom.comp
          ((stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α k l hkstab).hom.val.app
            (op V)).hom =
        ((kernelImageAtIncl B S hS F hF 𝓘 α k l hkl).val.app (op V)).hom :=
      congrArg (fun φ : _ ⟶ E.obj.obj (op k) => (φ.val.app (op V)).hom)
        (stableKernelImageIso_hom_comp B S hS F hF 𝓘 hZ hN hIcart α k l hkstab)
    have hr1 : LinearMap.range
          ((kernelImageAtIncl B S hS F hF 𝓘 α k l hkl).val.app (op V)).hom =
        LinearMap.range
          ((stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α k).val.app (op V)).hom := by
      rw [← hcomp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hbij.2, Submodule.map_top]
    rw [← hr1, range_val_app_kernelImageAtIncl B S hS F hF 𝓘 α k l hkl V hV.1]
    have key := Stacks.AdicCompletion.map_ker_eq_map_comap_ker
      (f.restrictScalars (chartRing B S hS F hF V))
      (chartCompletedLevel B S hS F hF 𝓘 E.obj hMc l)
      (chartCompletedLevel B S hS F hF 𝓘 E'.obj hNc l)
      (((chartSectionsSystemMap B S hS F hF α.hom V).app (op l)).hom)
      (((chartSectionsSystem B S hS F hF E.obj V).map (homOfLE hkl).op).hom)
      (surjective_chartCompletedLevel B S hS F hF 𝓘 E.property hV.1 hMc l) (hsquare l)
    rw [hproj k l hkl,
      ker_chartCompletedLevel B S hS F hF 𝓘 E'.property hIcart hV hNc l] at key
    refine key.trans ?_
    exact hc (k + 1) (l + 1) (by omega) _
      (ker_chartCompletedLevel B S hS F hF 𝓘 E.property hIcart hV hMc k).ge
  · intro n
    obtain ⟨c, hc⟩ := Stacks.AdicCompletion.exists_comap_subtype_pow_smul_restrictScalars_le
      (A := AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V))
      (chartSectionIdeal B S hS F hF 𝓘 V) (LinearMap.ker f)
    refine ⟨c, fun k hk => ?_⟩
    rw [ker_chartCompletedLevel B S hS F hF 𝓘 E.property hIcart hV hMc k]
    exact hc (n + 1) (k + 1) (by omega)

end AlgebraicGeometry.Space

end

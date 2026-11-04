module

public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentInternalHomOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Coherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# Coherence of the small internal Hom on an essentially small ringed site

Let `X` be a ringed site whose underlying category is essentially small, let `ℱ` be an
`𝒪_X`-module of finite presentation in the sense of Stacks 03DL(7) and let `𝒢` be coherent in
the sense of Stacks 03DL(8).  This file proves that `𝓗om_{𝒪_X}(ℱ, 𝒢)`, read at the module universe
of the coefficient rings as `AlgebraicGeometry.RingedSite.internalHomSheafSmall`, is coherent.

## Main results

* `AlgebraicGeometry.RingedSite.isCoherentOnSite_over_internalHomSheafSmall`: over an object
  carrying a finite global presentation of `ℱ`, the restriction of the internal Hom is coherent.
* `AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheafSmall`: the internal Hom out of
  a module of finite presentation into a coherent module is coherent.

## References

* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.RingedSite

section Small

variable (X : RingedSite.{max u w, v, w}) [EssentiallySmall.{w} X.C]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Over an object carrying a finite global presentation of `ℱ`, the restriction of
`𝓗om_{𝒪_X}(ℱ, 𝒢)` is coherent** as soon as `𝒢` is, in the sense of Stacks 03DL(8). -/
theorem isCoherentOnSite_over_internalHomSheafSmall
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hN : SheafOfModules.IsCoherentOnSite N) (W : X.C)
    (hW : SheafOfModules.HasFiniteGlobalPresentation (M.over W)) :
    SheafOfModules.IsCoherentOnSite
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)
      ((internalHomSheafSmall X M N).over W) := by
  classical
  let Rs := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let H := internalHomSheafSmall X M N
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hW
  have : HasFiniteLimits (SheafOfModules.{w} (Rs.over W)) :=
    SheafOfModules.Finite.hasFiniteLimits _
  have : HasFiniteLimits (SheafOfModules.{max u v w} (Rs.over W)) :=
    SheafOfModules.Finite.hasFiniteLimits _
  let L := Stacks.SheafOfModules.moduleULift.{max u v w, w} (Rs.over W)
  have hL : L.FullyFaithful := Stacks.SheafOfModules.moduleULiftFullyFaithful _
  have : PreservesFiniteLimits L := Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  let IH : SheafOfModules.{max u v w} (Rs.over W) :=
    (X.over W).internalHomSheaf
      (SheafOfModules.uliftForPresentation.{max u v w, v, w, w, max u v w} (M.over W))
      (L.obj (N.over W))
  obtain ⟨f', ⟨e'⟩⟩ : ∃ f' : (∏ᶜ fun _ : Fin n => L.obj (N.over W)) ⟶
      ∏ᶜ fun _ : Fin k => L.obj (N.over W), Nonempty (IH ≅ kernel f') :=
    exists_internalHomSheaf_iso_kernel (X.over W) ι hP κ hQ a b hab hb (L.obj (N.over W))
  let eH : L.obj (H.over W) ≅ kernel f' :=
    (SheafOfModules.overFunctor Rs W).mapIso (internalHomSheafSmallIso X M N) ≪≫
      internalHomSheafOverIso X W M N ≪≫
      (internalHomSheafULiftIso (X.over W) (M.over W) (N.over W)).symm ≪≫ e'
  let eP (m : ℕ) : L.obj (∏ᶜ fun _ : Fin m => N.over W) ≅ ∏ᶜ fun _ : Fin m => L.obj (N.over W) :=
    PreservesProduct.iso L _
  let f : (∏ᶜ fun _ : Fin n => N.over W) ⟶ ∏ᶜ fun _ : Fin k => N.over W :=
    hL.preimage ((eP n).hom ≫ f' ≫ (eP k).inv)
  let eK : L.obj (kernel f) ≅ kernel f' :=
    PreservesKernel.iso L f ≪≫ kernel.mapIso _ _ (eP n) (eP k) (by simp [f])
  let eHW : H.over W ≅ kernel f := hL.preimageIso (eH ≪≫ eK.symm)
  have hNW : SheafOfModules.IsCoherentOnSite (R := Rs.over W) (N.over W) :=
    Stacks.SheafOfModules.isCoherentOnSite_over N hN W
  have hprod : ∀ m : ℕ,
      SheafOfModules.IsCoherentOnSite (R := Rs.over W) (∏ᶜ fun _ : Fin m => N.over W) :=
    fun m => Stacks.SheafOfModules.isCoherentOnSite_piFin.{max u w v, v, w}
      (R := Rs.over W) (fun _ : Fin m => N.over W) fun _ => hNW
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso eHW.symm
    (Stacks.SheafOfModules.isCoherentOnSite_kernel (hprod n) (hprod k) f)

/-- **The internal Hom out of a module of finite presentation into a coherent module is
coherent.**  Let `X` be a ringed site, `ℱ` an `𝒪_X`-module of finite presentation in the sense of
Stacks 03DL(7) and `𝒢` an `𝒪_X`-module coherent in the sense of Stacks 03DL(8).  Then
`𝓗om_{𝒪_X}(ℱ, 𝒢)` is coherent in the sense of Stacks 03DL(8). -/
theorem isCoherentOnSite_internalHomSheafSmall
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : M.IsFinitePresentationOnSite) (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite (internalHomSheafSmall X M N) := by
  refine
    (Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite.{max u w, v, w, w}
      X _).2
    ⟨ULift.{v} {W : X.C // SheafOfModules.HasFiniteGlobalPresentation (M.over W)},
      fun W => W.down.1, fun U => ?_, fun W =>
        isCoherentOnSite_over_internalHomSheafSmall X M N hN W.down.1 W.down.2⟩
  obtain ⟨I, V, f, hV, hpres⟩ := hM.locally_hasFiniteGlobalPresentation U
  refine GrothendieckTopology.superset_covering _
    ((Sieve.ofArrows_le_ofObjects V f).trans (Sieve.ofObjects_mono ?_)) hV
  rintro x ⟨i, rfl⟩
  exact ⟨ULift.up ⟨V i, hpres i⟩, rfl⟩

end Small

end AlgebraicGeometry.RingedSite

end

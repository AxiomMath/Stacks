module

public import StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsMap

/-!
# The ideal-power filtration away from the closed subscheme it cuts out

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals on `X` given by its affine-local ideal
data, `M` a sheaf of modules on `X`, and `V ⊆ X` an open disjoint from the closed set `V(I)`.
Over such a `V` the ideal is the unit ideal, so every section of `M` already lies in the
subsheaf `I ^ n • M`: the inclusion `I ^ n • M ⟶ M` restricts to an isomorphism over `V`.

This is the identification under which the two morphism assertions of [Stacks, Tag 01YB] are
stated. That tag compares `colim_n Hom(I ^ n • G, F)` with `Hom_{𝒪_V}(G|_V, F|_V)` for
`V = X \ V(I)`, and the comparison map sends a representative `φ : I ^ n • G ⟶ F` to its
restriction to `V` *read through this isomorphism*; without it the restriction of `φ` is a
morphism out of `(I ^ n • G)|_V` rather than out of `G|_V`.

No tag attribute is placed here. Tag 01YB is the comparison isomorphism itself together with
its restriction and evaluation properties; what is below is the identification its statement
presupposes, and it is to be re-pointed at that tag's covering set when 01YB lands.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support`: on an affine open
  missing the support of `I`, the ideal of `I` is the unit ideal.
* `Stacks.AlgebraicGeometry.IdealPowerHomColimit.mem_idealPowerMultiple_of_disjoint_support`:
  over an open missing the support of `I`, every section of `M` lies in `I ^ n • M`.
* `Stacks.AlgebraicGeometry.IdealPowerHomColimit.isIso_restrict_idealPowerMultiple_ι`: the
  inclusion `I ^ n • M ⟶ M` restricts to an isomorphism over such an open, and
  `isIso_restrict_idealPowerMultiple_ι_idealComplement` is that statement on `idealComplement I`.
* `Stacks.AlgebraicGeometry.IdealPowerHomColimit.isIso_restrict_idealPowerMultipleMap`: the
  transition maps of the filtration likewise restrict to isomorphisms.

## Implementation notes

The ideal data `I : X.IdealSheafData` records an ideal `I.ideal U ⊆ Γ(X, U)` for each affine
open `U`, and `I.support` is the closed set it cuts out. On an affine open `U` disjoint from
that support the zero locus of `I.ideal U` in `Spec Γ(X, U)` is empty, so `I.ideal U = ⊤` by
`PrimeSpectrum.zeroLocus_empty_iff_eq_top`; the translation between the zero locus and the
support goes through `AlgebraicGeometry.IsAffineOpen.fromSpec_image_zeroLocus` and
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_inter`.

`idealPowerMultiple` is a *least* subsheaf rather than an affine-local image, so membership in
it over a general open is established by the sheaf condition on
`PresheafOfModules.Submodule`: a section lies in the subsheaf as soon as it does locally, and
locally — on an affine open refining the given one — the defining lower bound
`idealPowerMultiple_le_iff` applies with `I.ideal U ^ n = ⊤`.

Isomorphy of the restricted inclusion is checked on the underlying presheaves of abelian
groups, where the component at an open is the inclusion of a submodule which the previous
paragraph shows to be everything, and is then reflected back along
`AlgebraicGeometry.Scheme.Modules.toPresheaf`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.LocalCohomology
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- On an affine open disjoint from the support of a quasi-coherent sheaf of ideals, the ideal
is the unit ideal: its zero locus in the spectrum of the sections is empty. -/
public lemma ideal_eq_top_of_disjoint_support (I : X.IdealSheafData) (U : X.affineOpens)
    (hU : Disjoint (U.1 : Set X) (I.support : Set X)) : I.ideal U = ⊤ := by
  apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
  apply (Set.image_eq_empty (f := U.2.fromSpec)).mp
  rw [U.2.fromSpec_image_zeroLocus, ← I.coe_support_inter]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  exact fun h => Set.disjoint_left.mp hU h.2 h.1

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.AlgebraicGeometry.IdealPowerHomColimit

variable {X : Scheme.{u}}

/-- Over an open disjoint from the support of `I`, the subsheaf `I ^ n • M` is all of `M`: every
section of `M` over such an open already lies in it. -/
public lemma mem_idealPowerMultiple_of_disjoint_support (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) (V : X.Opens) (hV : ∀ x ∈ V, x ∉ I.support) (s : Γ(M, V)) :
    s ∈ (idealPowerMultiple I n M).toSubmodule.obj (op V) := by
  apply (idealPowerMultiple I n M).isSheaf s
  intro x hx
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨W, homOfLE hWV, ?_, hxW⟩
  change M.val.map (homOfLE hWV).op s ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W)
  have hg := (idealPowerMultiple_le_iff I n M (idealPowerMultiple I n M)).mp le_rfl ⟨W, hW⟩
  rw [I.ideal_eq_top_of_disjoint_support ⟨W, hW⟩
    (Set.disjoint_left.mpr fun y hy => hV y (hWV hy)), Ideal.top_pow,
    Submodule.top_smul] at hg
  exact hg Submodule.mem_top

/-- The inclusion `I ^ n • M ⟶ M` restricts to an isomorphism over any open disjoint from the
support of `I`. This is the identification under which the morphism assertions of
[Stacks, Tag 01YB] read a morphism out of `I ^ n • G` as one out of `G` over the complement of
`V(I)`. -/
public lemma isIso_restrict_idealPowerMultiple_ι (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) (V : X.Opens) (hV : ∀ x ∈ V, x ∉ I.support) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (idealPowerMultiple I n M).ι) := by
  set q := (Scheme.Modules.restrictFunctor V.ι).map (idealPowerMultiple I n M).ι with hq
  have hpre : IsIso ((Scheme.Modules.toPresheaf V.toScheme).map q) := by
    have happ : ∀ W, IsIso (((Scheme.Modules.toPresheaf V.toScheme).map q).app W) := by
      intro W
      refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨Subtype.val_injective, fun s => ?_⟩
      refine ⟨⟨s, mem_idealPowerMultiple_of_disjoint_support I n M (V.ι ''ᵁ W.unop)
        (fun x hx => ?_) s⟩, rfl⟩
      obtain ⟨y, -, rfl⟩ := hx
      exact hV _ y.2
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso q (Scheme.Modules.toPresheaf V.toScheme)

/-- The inclusion `I ^ n • M ⟶ M` restricts to an isomorphism over `idealComplement I`, the open
complement of the closed subscheme cut out by `I`. -/
public lemma isIso_restrict_idealPowerMultiple_ι_idealComplement (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor (idealComplement I).ι).map
      (idealPowerMultiple I n M).ι) :=
  isIso_restrict_idealPowerMultiple_ι I n M _ fun _ hx => hx

/-- The transition map `I ^ m • M ⟶ I ^ n • M` of the ideal-power filtration restricts to an
isomorphism over any open disjoint from the support of `I`, both sides being all of `M` there. -/
public lemma isIso_restrict_idealPowerMultipleMap (I : X.IdealSheafData) (M : X.Modules)
    {n m : ℕ} (h : n ≤ m) (V : X.Opens) (hV : ∀ x ∈ V, x ∉ I.support) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (idealPowerMultipleMap I M h)) := by
  have hn : IsIso ((Scheme.Modules.restrictFunctor V.ι).map (idealPowerMultiple I n M).ι) :=
    isIso_restrict_idealPowerMultiple_ι I n M V hV
  have hm : IsIso ((Scheme.Modules.restrictFunctor V.ι).map (idealPowerMultiple I m M).ι) :=
    isIso_restrict_idealPowerMultiple_ι I m M V hV
  have hcomp : (Scheme.Modules.restrictFunctor V.ι).map (idealPowerMultipleMap I M h) ≫
      (Scheme.Modules.restrictFunctor V.ι).map (idealPowerMultiple I n M).ι =
      (Scheme.Modules.restrictFunctor V.ι).map (idealPowerMultiple I m M).ι :=
    ((Scheme.Modules.restrictFunctor V.ι).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.restrictFunctor V.ι).map
        (idealPowerMultipleMap_comp_ι I M h))
  exact (isIso_comp_right_iff _ _).mp (hcomp ▸ hm)

/-- The transition maps of the ideal-power filtration restrict to isomorphisms over
`idealComplement I`. -/
public lemma isIso_restrict_idealPowerMultipleMap_idealComplement (I : X.IdealSheafData)
    (M : X.Modules) {n m : ℕ} (h : n ≤ m) :
    IsIso ((Scheme.Modules.restrictFunctor (idealComplement I).ι).map
      (idealPowerMultipleMap I M h)) :=
  isIso_restrict_idealPowerMultipleMap I M h _ fun _ hx => hx

end Stacks.AlgebraicGeometry.IdealPowerHomColimit

end

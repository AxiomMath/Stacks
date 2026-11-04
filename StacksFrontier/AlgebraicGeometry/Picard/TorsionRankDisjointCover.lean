module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Descent
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionZModRank

/-!
# The `ℓ`-torsion of the Picard group over a pairwise disjoint open cover

Let `Y` be a scheme and let `U i` be finitely many pairwise disjoint opens covering it.  An
invertible `𝒪_Y`-module which is trivial on each `U i` is trivial: the trivializing sections glue
with no compatibility condition to check, the overlaps being empty.  Hence
`Pic(Y) → ∏ᵢ Pic(U i)` is injective and

`dim_{F_ℓ} Pic(Y)[ℓ] ≤ ∑ᵢ dim_{F_ℓ} Pic(U i)[ℓ]`.

This is the Picard half of the additivity used to pass from a proper scheme of dimension at most
one to its connected components in the proof of
[Stacks, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6).

The second half of the file records what disposes of the pieces of dimension zero: the Picard
group of a scheme with discrete underlying space vanishes.

## Main results

* `Stacks.Picard.finrank_zmodTorsion_le_sum_of_injOn` and
  `Stacks.Picard.finiteDimensional_zmodTorsion_of_injOn_pi`: for a family of homomorphisms of
  abelian groups which is jointly injective on `ℓ`-torsion, `dim_{F_ℓ} A[ℓ]` is at most the sum
  of the `dim_{F_ℓ} (B i)[ℓ]`, and is finite as soon as they are.
* `Stacks.PicardGroup.nonempty_iso_unit_of_pairwise_disjoint_cover`: **an invertible module
  trivial on each member of a pairwise disjoint open cover is trivial.**
* `Stacks.Picard.injective_schemePullbackClass_pi_of_pairwise_disjoint`: consequently
  `Pic(Y) → ∏ᵢ Pic(U i)` is injective.
* `AlgebraicGeometry.finrank_picardTorsion_le_sum_of_pairwise_disjoint` and
  `AlgebraicGeometry.finiteDimensional_picardTorsion_of_pairwise_disjoint`: **the bound
  `dim_{F_ℓ} Pic(Y)[ℓ] ≤ ∑ᵢ dim_{F_ℓ} Pic(U i)[ℓ]`** and the finite-dimensionality that goes
  with it.
* `Stacks.Picard.subsingleton_ofScheme_of_discreteTopology`: the Picard group of a scheme with
  discrete underlying space is trivial.  This is what disposes of the pieces of dimension zero,
  such a scheme being discrete.

## Implementation notes

The gluing is `Stacks.SheafOfModules.exists_sections_eval_eq_of_pairwise_disjoint` followed by
`Stacks.SheafOfModules.nonempty_iso_unit_of_bijective_smul_on_cover`, exactly as in
`Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology`, which is the special case of the
cover by the points of a discrete space.  The per-piece hypothesis is stated as triviality of the
*pullback* of the module along `(U i).ι`, which is the form
`Stacks.Picard.schemePullbackClass_eq_zero_iff_nonempty_iso_unit` produces; it is converted into
a trivializing section over `U i` by `Stacks.Modules.overIsoUnitOfRestrictIsoUnit` and
`Stacks.SheafOfModules.exists_bijective_smul_of_over_iso_unit`.

## References

* [Stacks Project, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Picard

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-! ### The `F_ℓ`-dimension of the `ℓ`-torsion under a jointly injective family -/

section Algebra

variable {A : Type*} [AddCommGroup A] {ι : Type*} {B : ι → Type*}
  [∀ i, AddCommGroup (B i)]

/-- **The restriction to `n`-torsion of a family of homomorphisms**, assembled into a single
`ZMod n`-linear map into the product of the `n`-torsion subgroups. -/
def zmodTorsionRestrictPi (f : ∀ i, A →+ B i) (n : ℕ) :
    AddSubgroup.torsionBy A (n : ℤ) →ₗ[ZMod n]
      ∀ i, AddSubgroup.torsionBy (B i) (n : ℤ) :=
  LinearMap.pi fun i ↦ zmodTorsionRestrict (f i) n

/-- A family of homomorphisms which is jointly injective on the `n`-torsion restricts to an
injective map into the product of the `n`-torsion subgroups. -/
theorem injective_zmodTorsionRestrictPi (f : ∀ i, A →+ B i) (n : ℕ)
    (hf : Set.InjOn (fun a ↦ fun i ↦ f i a) (zsmulTorsion A (n : ℤ))) :
    Function.Injective (zmodTorsionRestrictPi f n) := by
  intro x y hxy
  refine Subtype.ext (hf (mem_zsmulTorsion_of_mem_torsionBy x.2)
    (mem_zsmulTorsion_of_mem_torsionBy y.2) (funext fun i ↦ ?_))
  exact congrArg Subtype.val (congrFun hxy i)

variable (p : ℕ) [Fact p.Prime]

/-- **Finite-dimensionality of the `ℓ`-torsion descends along a jointly injective finite family
of homomorphisms.** -/
theorem finiteDimensional_zmodTorsion_of_injOn_pi [Finite ι] (f : ∀ i, A →+ B i)
    (hf : Set.InjOn (fun a ↦ fun i ↦ f i a) (zsmulTorsion A (p : ℤ)))
    (hB : ∀ i, FiniteDimensional (ZMod p) (AddSubgroup.torsionBy (B i) (p : ℤ))) :
    FiniteDimensional (ZMod p) (AddSubgroup.torsionBy A (p : ℤ)) := by
  have := hB
  exact FiniteDimensional.of_injective (zmodTorsionRestrictPi f p)
    (injective_zmodTorsionRestrictPi f p hf)

/-- **`dim_{F_ℓ} A[ℓ] ≤ ∑ᵢ dim_{F_ℓ} (B i)[ℓ]` for a jointly injective finite family of
homomorphisms**, the `ℓ`-torsion of each target being finite-dimensional. -/
theorem finrank_zmodTorsion_le_sum_of_injOn [Fintype ι] (f : ∀ i, A →+ B i)
    (hf : Set.InjOn (fun a ↦ fun i ↦ f i a) (zsmulTorsion A (p : ℤ)))
    (hB : ∀ i, FiniteDimensional (ZMod p) (AddSubgroup.torsionBy (B i) (p : ℤ))) :
    Module.finrank (ZMod p) (AddSubgroup.torsionBy A (p : ℤ)) ≤
      ∑ i, Module.finrank (ZMod p) (AddSubgroup.torsionBy (B i) (p : ℤ)) := by
  have := hB
  have h := LinearMap.finrank_le_finrank_of_injective
    (injective_zmodTorsionRestrictPi f p hf)
  rwa [Module.finrank_pi_fintype] at h

end Algebra

end Stacks.Picard

/-! ### Gluing a trivialization over a pairwise disjoint open cover -/

namespace Stacks.PicardGroup

open Stacks.SheafOfModules

/-- **An invertible module which is trivial on each member of a pairwise disjoint open cover is
trivial.**  The transition data on the overlaps is the only obstruction to gluing trivializations,
and a pairwise disjoint cover has no overlaps.

Triviality on `U i` is stated as triviality of the pullback of the module along the inclusion
`U i ⟶ Y`. -/
theorem nonempty_iso_unit_of_pairwise_disjoint_cover {Y : Scheme.{u}} (L : Y.Modules)
    [IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L]
    {ι : Type*} (U : ι → Y.Opens) (hcover : IsOpenCover U)
    (hdisj : Pairwise (Function.onFun Disjoint U))
    (htriv : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L ≅
      SheafOfModules.unit (U i).toScheme.ringCatSheaf)) :
    Nonempty (L ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  classical
  choose a ha using fun i ↦
    exists_bijective_smul_of_over_iso_unit (X := Y.toRingedSpace) L (U i)
      (Stacks.Modules.overIsoUnitOfRestrictIsoUnit L (U i)
        ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app L ≪≫ (htriv i).some))
  obtain ⟨s, hs⟩ := exists_sections_eval_eq_of_pairwise_disjoint (X := Y.toRingedSpace) L U
    hcover hdisj a
  refine nonempty_iso_unit_of_bijective_smul_on_cover (X := Y.toRingedSpace) L s U hcover
    fun i V hV ↦ ?_
  have hev : s.eval (op V) = L.val.map (homOfLE hV).op (s.eval (op (U i))) :=
    (PresheafOfModules.sections_property s (homOfLE hV).op).symm
  rw [hev, hs i]
  exact ha i V hV

end Stacks.PicardGroup

namespace Stacks.Picard

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-! ### Injectivity of `Pic(Y) → ∏ᵢ Pic(U i)` -/

/-- A Picard class is zero once its representative is trivial, given that it is invertible. -/
private theorem eq_zero_of_nonempty_iso_unit_representative {Y : Scheme.{u}} (x : ofScheme Y)
    (h : Stacks.SheafOfModules.IsInvertible Y.presheaf
        (_root_.structureSheafRing Y.toRingedSpace).property
        (picardRepresentative Y.toRingedSpace x).obj →
      Nonempty ((picardRepresentative Y.toRingedSpace x).obj ≅
        SheafOfModules.unit Y.ringCatSheaf)) : x = 0 :=
  (eq_zero_iff_nonempty_iso_unit x).2 (h (picardRepresentative Y.toRingedSpace x).property)

/-- **A Picard class of `Y` which restricts to zero on each member of a pairwise disjoint open
cover is zero.** -/
theorem eq_zero_of_forall_schemePullbackClass_ι_eq_zero {Y : Scheme.{u}} {ι : Type*}
    (U : ι → Y.Opens) (hcover : IsOpenCover U)
    (hdisj : Pairwise (Function.onFun Disjoint U)) (x : ofScheme Y)
    (hx : ∀ i, schemePullbackClass (U i).ι x = 0) : x = 0 := by
  refine eq_zero_of_nonempty_iso_unit_representative x fun _ ↦ ?_
  exact Stacks.PicardGroup.nonempty_iso_unit_of_pairwise_disjoint_cover
    (picardRepresentative Y.toRingedSpace x).obj U hcover hdisj
    fun i ↦ (schemePullbackClass_eq_zero_iff_nonempty_iso_unit (U i).ι x).mp (hx i)

/-- **`Pic(Y) → ∏ᵢ Pic(U i)` is injective for a pairwise disjoint open cover `U` of `Y`.** -/
theorem injective_schemePullbackClass_pi_of_pairwise_disjoint {Y : Scheme.{u}} {ι : Type*}
    (U : ι → Y.Opens) (hcover : IsOpenCover U)
    (hdisj : Pairwise (Function.onFun Disjoint U)) :
    Function.Injective
      (fun x : ofScheme Y ↦ fun i ↦ schemePullbackClassHom (U i).ι x) := by
  intro x y hxy
  have hzero : x - y = 0 :=
    eq_zero_of_forall_schemePullbackClass_ι_eq_zero U hcover hdisj (x - y) fun i ↦ by
      have h : schemePullbackClassHom (U i).ι x = schemePullbackClassHom (U i).ι y :=
        congrFun hxy i
      rw [show schemePullbackClass (U i).ι (x - y) =
        schemePullbackClassHom (U i).ι (x - y) from rfl, map_sub, h, sub_self]
  exact sub_eq_zero.mp hzero

/-! ### The Picard group of a scheme with discrete underlying space -/

/-- **The Picard group of a scheme with discrete underlying space is trivial.**  Every point is
an open set, so an invertible module is trivialized on each point separately and the
trivializations glue over the pairwise disjoint cover by points. -/
theorem subsingleton_ofScheme_of_discreteTopology (Y : Scheme.{u})
    [DiscreteTopology (Y : Type u)] : Subsingleton (ofScheme Y) := by
  refine ⟨fun x y ↦ ?_⟩
  have hzero : ∀ z : ofScheme Y, z = 0 := by
    intro z
    refine eq_zero_of_nonempty_iso_unit_representative z fun _ ↦ ?_
    exact Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology Y
      (picardRepresentative Y.toRingedSpace z).obj
  rw [hzero x, hzero y]

end Stacks.Picard

namespace AlgebraicGeometry

open Stacks.Picard (ofScheme schemePullbackClass schemePullbackClassHom zsmulTorsion)

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-! ### The torsion bound over a pairwise disjoint open cover -/

/-- **Finite-dimensionality of the `ℓ`-torsion of `Pic(Y)` from a pairwise disjoint open
cover.** -/
theorem finiteDimensional_picardTorsion_of_pairwise_disjoint {Y : Scheme.{u}} {ι : Type*}
    [Finite ι] (U : ι → Y.Opens) (hcover : IsOpenCover U)
    (hdisj : Pairwise (Function.onFun Disjoint U)) (ℓ : ℕ) [Fact ℓ.Prime]
    (hfin : ∀ i, FiniteDimensional (ZMod ℓ)
      (AddSubgroup.torsionBy (ofScheme (U i).toScheme) (ℓ : ℤ))) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ)) :=
  Stacks.Picard.finiteDimensional_zmodTorsion_of_injOn_pi ℓ
    (fun i ↦ schemePullbackClassHom (U i).ι)
    (Stacks.Picard.injective_schemePullbackClass_pi_of_pairwise_disjoint U hcover hdisj).injOn
    hfin

/-- **`dim_{F_ℓ} Pic(Y)[ℓ] ≤ ∑ᵢ dim_{F_ℓ} Pic(U i)[ℓ]` for a finite pairwise disjoint open cover
`U` of a scheme `Y`**, the `ℓ`-torsion of each `Pic(U i)` being finite-dimensional. -/
theorem finrank_picardTorsion_le_sum_of_pairwise_disjoint {Y : Scheme.{u}} {ι : Type*}
    [Fintype ι] (U : ι → Y.Opens) (hcover : IsOpenCover U)
    (hdisj : Pairwise (Function.onFun Disjoint U)) (ℓ : ℕ) [Fact ℓ.Prime]
    (hfin : ∀ i, FiniteDimensional (ZMod ℓ)
      (AddSubgroup.torsionBy (ofScheme (U i).toScheme) (ℓ : ℤ))) :
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ)) ≤
      ∑ i, Module.finrank (ZMod ℓ)
        (AddSubgroup.torsionBy (ofScheme (U i).toScheme) (ℓ : ℤ)) :=
  Stacks.Picard.finrank_zmodTorsion_le_sum_of_injOn ℓ
    (fun i ↦ schemePullbackClassHom (U i).ι)
    (Stacks.Picard.injective_schemePullbackClass_pi_of_pairwise_disjoint U hcover hdisj).injOn
    hfin

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MultiplierUnitRatio

/-!
# The agreement hypothesis of Tag 0BD7, with nothing left to assume about the multipliers

`Stacks.InvertiblePullback.forall_mem_generatingLocus_iff_of_isPullMeromorphicFamily` derives
`hagree` for the family `φ^*(g_i) s` of [Stacks, Tag 0BD7] from a relation between the
meromorphic multipliers on an open of the base, with the factor regular and a unit at the image
point. That relation was a hypothesis. This file supplies it, for a flat morphism of integral
schemes and a regular `s`, and so discharges `hagree` outright.

What makes the relation available is that it need only be found where it is used: at a point of
`X` at which both `t_i` and `t_j` generate `ℒ`. There the two sections differ by a unit of
`𝒪_X` on the intersection of their generating loci, and
`Stacks.InvertiblePullback.exists_isUnit_mul_germ_eq_of_isPullMeromorphicFamily` turns that into
a unit of `𝒪_{Y, φ(x)}` relating the germs of the two multipliers. A germ is not a section, so
the last step is the sheaf axiom: two sections of `𝒦_Y` with equal germs at `φ(x)` already agree
on a neighbourhood of it, which is the open the agreement hypothesis asks for.

## Main results

* `Stacks.InvertiblePullback.exists_isUnit_germ_restrictₛₗ_eq_smul_of_germ_eq_mul`: the sheaf
  axiom alone — a germ relation between two meromorphic functions on the base, read on an open.
* `Stacks.InvertiblePullback.exists_isUnit_germ_restrictₛₗ_eq_smul_of_isPullMeromorphicFamily`:
  the relation between the multipliers, on an open of the base, with no hypothesis beyond the
  family itself.
* `Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections_of_isRegular`: the chart
  datum of [Stacks, Tag 0BD7] for the family, with `hagree` gone. What remains assumed of the
  family is `hex` alone.

## Implementation notes

The tag is **withheld**: the family and its existence property `hex` are hypotheses here. A
family satisfying them is exhibited in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/LocalFamilyAgreement.lean`, on arbitrary
opens rather than on preimages, so what that file consumes from here is the germ-to-section step
alone.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Meromorphic Stacks.SheafOfModules

universe u

namespace Stacks.InvertiblePullback

private lemma totalQuotientSheaf_map_map {Y : Scheme.{u}} {U V Z : Y.Opens} (h1 : V ≤ U)
    (h2 : Z ≤ V) (z : Y.totalQuotientSheaf.presheaf.obj (op U)) :
    Y.totalQuotientSheaf.presheaf.map (homOfLE h2).op
        (Y.totalQuotientSheaf.presheaf.map (homOfLE h1).op z)
      = Y.totalQuotientSheaf.presheaf.map (homOfLE (h2.trans h1)).op z := by
  rw [← ConcreteCategory.comp_apply, ← Y.totalQuotientSheaf.presheaf.map_comp,
    show (homOfLE h1).op ≫ (homOfLE h2).op = (homOfLE (h2.trans h1)).op from
      Subsingleton.elim _ _]

/-- **A germ relation between two meromorphic functions on the base, read on an open.** If the
germs of `g₁` and `g₂` at `y` differ by the image of a unit of `𝒪_{Y, y}`, then on some open
neighbourhood of `y` inside both domains they differ by a regular function whose germ at `y` is
that unit.

This is the sheaf-axiom half of the uniqueness sentence of the penultimate paragraph of
[Stacks, Tag 0BD7], separated from the ring theory that produces the unit: nothing about `φ`,
`ℒ` or `s` enters it, and both the family on preimages and the family on arbitrary opens need
exactly this step. -/
theorem exists_isUnit_germ_restrictₛₗ_eq_smul_of_germ_eq_mul {Y : Scheme.{u}} (y : Y)
    {A₁ A₂ : Y.Opens} (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂)
    (g₁ : (totalQuotientSheafAsModule Y).val.obj (op A₁))
    (g₂ : (totalQuotientSheafAsModule Y).val.obj (op A₂))
    (v : Y.presheaf.stalk y) (hv : IsUnit v)
    (hrel : Y.totalQuotientSheaf.presheaf.germ A₁ y hy₁ g₁
      = toTotalQuotientStalk Y y v * Y.totalQuotientSheaf.presheaf.germ A₂ y hy₂ g₂) :
    ∃ (A' : Y.Opens) (hyA : y ∈ A') (h₁ : A' ≤ A₁) (h₂ : A' ≤ A₂) (w : Γ(Y, A')),
      IsUnit (Y.presheaf.germ A' y hyA w) ∧
        (totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE h₁).op g₁
          = HSMul.hSMul (α := (Stacks.Sheaves.Differentials.ringSheaf (J :=
            Opens.grothendieckTopology Y)
              Y.sheaf).obj.obj (op A')) w
              ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE h₂).op g₂) := by
  obtain ⟨B, hxB, w, hw⟩ := Y.presheaf.exists_germ_eq v
  have hkw : Y.totalQuotientSheaf.presheaf.germ B y hxB
        ((Y.toTotalQuotientSheaf.hom.app (op B)).hom w)
      = toTotalQuotientStalk Y y v := by
    rw [← hw]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply B y hxB
      Y.toTotalQuotientSheaf.hom w).symm
  have hCj : A₁ ⊓ A₂ ⊓ B ≤ A₂ := fun _ hz => hz.1.2
  have hCB : A₁ ⊓ A₂ ⊓ B ≤ B := fun _ hz => hz.2
  have hyC : y ∈ A₁ ⊓ A₂ ⊓ B := ⟨⟨hy₁, hy₂⟩, hxB⟩
  have e2 : Y.totalQuotientSheaf.presheaf.germ (A₁ ⊓ A₂ ⊓ B) y hyC
        (Y.totalQuotientSheaf.presheaf.map (homOfLE hCj).op g₂)
      = Y.totalQuotientSheaf.presheaf.germ A₂ y hy₂ g₂ :=
    TopCat.Presheaf.germ_res_apply _ (homOfLE hCj) y hyC _
  have heq : Y.totalQuotientSheaf.presheaf.germ A₁ y hy₁ g₁
      = Y.totalQuotientSheaf.presheaf.germ (A₁ ⊓ A₂ ⊓ B) y hyC
          (Y.totalQuotientSheaf.presheaf.map (homOfLE hCB).op
              ((Y.toTotalQuotientSheaf.hom.app (op B)).hom w) *
            Y.totalQuotientSheaf.presheaf.map (homOfLE hCj).op g₂) := by
    rwa [map_mul (ConcreteCategory.hom (Y.totalQuotientSheaf.presheaf.germ
        (A₁ ⊓ A₂ ⊓ B) y hyC)), TopCat.Presheaf.germ_res_apply _ (homOfLE hCB) y hyC,
      e2, hkw]
  obtain ⟨A', hyA', iU, iV, hres⟩ := Y.totalQuotientSheaf.presheaf.germ_eq y hy₁ hyC
    _ _ heq
  have h₁ : A' ≤ A₁ := iU.le
  have hA'C : A' ≤ A₁ ⊓ A₂ ⊓ B := iV.le
  have h₂ : A' ≤ A₂ := hA'C.trans hCj
  have hA'B : A' ≤ B := hA'C.trans hCB
  rw [show iU = homOfLE h₁ from Subsingleton.elim _ _,
    show iV = homOfLE hA'C from Subsingleton.elim _ _,
    map_mul (ConcreteCategory.hom (Y.totalQuotientSheaf.presheaf.map (homOfLE hA'C).op)),
    totalQuotientSheaf_map_map hCB hA'C,
    totalQuotientSheaf_map_map hCj hA'C g₂] at hres
  have hnat : (Y.toTotalQuotientSheaf.hom.app (op A')).hom
        (Y.presheaf.map (homOfLE hA'B).op w)
      = Y.totalQuotientSheaf.presheaf.map (homOfLE hA'B).op
          ((Y.toTotalQuotientSheaf.hom.app (op B)).hom w) :=
    ConcreteCategory.congr_hom (Y.toTotalQuotientSheaf.hom.naturality (homOfLE hA'B).op) w
  rw [← hnat] at hres
  refine ⟨A', hyA', h₁, h₂, Y.presheaf.map (homOfLE hA'B).op w, ?_, hres⟩
  rwa [Y.presheaf.germ_res_apply (homOfLE hA'B) y hyA' w, hw]

/-- **The uniqueness clause of [Stacks, Tag 0BD7] as a relation between sections.** At a point
over which `t_i` and `t_j` both generate, the two multipliers agree on an open neighbourhood of
its image up to a regular factor which is a unit there. -/
theorem exists_isUnit_germ_restrictₛₗ_eq_smul_of_isPullMeromorphicFamily
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral X] [IsIntegral Y]
    (L : _root_.SheafOfModules.{u} (_root_.structureSheafRing X.toRingedSpace))
    [IsInvertible X.presheaf (_root_.structureSheafRing X.toRingedSpace).property L]
    (s : MeromorphicSection X.sheaf L) {ι : Type*} {A : ι → Y.Opens}
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier)))
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamily f L s g t) :
    ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∃ (A' : Y.Opens) (hxA : f.base x ∈ A') (hi : A' ≤ A i) (hj : A' ≤ A j) (w : Γ(Y, A')),
        IsUnit (Y.presheaf.germ A' (f.base x) hxA w) ∧
          (totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hi).op (g i)
            = HSMul.hSMul (α := (Stacks.Sheaves.Differentials.ringSheaf (J :=
              Opens.grothendieckTopology Y)
                Y.sheaf).obj.obj (op A')) w
                ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hj).op (g j)) := by
  intro i j x hxi hxj
  set W : Opens X.toRingedSpace.carrier :=
    ⟨_, isOpen_inter_generatingLocus L (t i) (t j)⟩
  have hxW : x ∈ W := ⟨hxi, hxj⟩
  have hWi : W ≤ (f ⁻¹ᵁ A i : X.Opens) := fun z hz => generatingLocus_le L (t i) hz.1
  have hWj : W ≤ (f ⁻¹ᵁ A j : X.Opens) := fun z hz => generatingLocus_le L (t j) hz.2
  obtain ⟨c, hcu, hc⟩ := exists_isUnit_smul_restrictₛₗ_of_subset_generatingLocus L (t i) (t j)
    hWi hWj (fun _ hz => hz.1) (fun _ hz => hz.2)
  have hxi' : f.base x ∈ A i := hWi hxW
  have hxj' : f.base x ∈ A j := hWj hxW
  obtain ⟨v, hv, hrel⟩ := exists_isUnit_mul_germ_eq_of_isPullMeromorphicFamily f L s g t hs ht
    i j hxW hWi hWj c hcu hc hxi' hxj'
  exact exists_isUnit_germ_restrictₛₗ_eq_smul_of_germ_eq_mul (f.base x) hxi' hxj' (g i) (g j)
    v hv hrel

/-- **The chart datum of [Stacks, Tag 0BD7] for the family `φ^*(g_i) s`, with `hagree` gone.**
This is the chart datum of the family with its hypothesis on the multipliers discharged: for a
flat morphism of integral schemes and a regular `s`, only `hex` is left to assume. -/
theorem exists_chart_nonempty_generatorSections_of_isRegular
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral X] [IsIntegral Y]
    (L : _root_.SheafOfModules.{u} (_root_.structureSheafRing X.toRingedSpace))
    [IsInvertible X.presheaf (_root_.structureSheafRing X.toRingedSpace).property L]
    [IsLocallyNoetherian Y]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (s : MeromorphicSection X.sheaf L) {ι : Type*} {A : ι → Y.Opens}
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier)))
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamily f L s g t)
    (hex : ∀ z : X.toRingedSpace.carrier, ∃ i, z ∈ generatingLocus L (t i))
    (hirr : ∀ y : Y, IsIrreducible (f.base ⁻¹' {y}))
    (hfiber : ∀ y : Y, Nonempty (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f) :
    ∃ chart : Y → Y.Opens, (∀ y, y ∈ chart y) ∧
      ∀ y, Nonempty (GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ chart y)) :=
  exists_chart_nonempty_generatorSections_of_isPullMeromorphicFamily f L s g t hL ht hex hirr
    (exists_isUnit_germ_restrictₛₗ_eq_smul_of_isPullMeromorphicFamily f L s g t hs ht)
    hfiber hfinite

end Stacks.InvertiblePullback

end

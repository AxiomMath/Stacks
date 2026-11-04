module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient

/-!
# Sections of the sheaf of total quotient rings are locally fractions

The sheaf of total quotient rings is the *sheafification* of the presheaf which localizes each
ring of sections at the sections whose germs are everywhere nonzerodivisors. Consequently a
section of that sheaf over an open set is **not** in general a single fraction; it is only
locally one. This file records exactly that: around each point of `U`, every section `t` over
`U` has an open neighbourhood `V ⊆ U` and sections `a`, `b` of the structure sheaf over
`V` with `b` a nonzerodivisor, becoming a unit in the total quotient sheaf, such that
`t|_V * b = a` there — that is, `t|_V = a / b`.

## Main results

* `AlgebraicGeometry.mem_nonZeroDivisors_of_mem_submonoidPresheafOfStalk`: for a *sheaf* of
  rings, a section whose germ at every point of an open set is a nonzerodivisor is itself a
  nonzerodivisor in the ring of sections over that open set.
* `AlgebraicGeometry.exists_nhds_mul_toTotalQuotientSheaf_eq`: the denominator form of the
  local description, with the denominator exhibited in the denominator submonoid of the total
  quotient presheaf.
* `AlgebraicGeometry.exists_nhds_isFraction_totalQuotientSheaf`: the same with the denominator
  recorded as a nonzerodivisor which becomes a unit after passing to the total quotient sheaf.
* `AlgebraicGeometry.exists_openCover_isFraction_totalQuotientSheaf`: the open-cover form, an
  open cover of `U` on each member of which the section is a fraction.
* `AlgebraicGeometry.Scheme.exists_isAffineOpen_nhds_isFraction_totalQuotientSheaf`: for a
  scheme the neighbourhood may in addition be taken affine.

## Implementation notes

The proof is in three independent steps, none of which needs any hypothesis on the space, the
sheaf, or the open set.

Sheafification is locally surjective: `CategoryTheory.Presheaf.imageSieve_mem` applied to
`CategoryTheory.toSheafify` produces a covering sieve of opens on which `t` is in the image of
the total quotient presheaf, and membership in `Opens.grothendieckTopology` is literally the
statement that those opens cover `U`.

Over each such open the total quotient presheaf is a localization of the sections of the
structure sheaf at the denominator submonoid — by construction, not by a comparison theorem —
so `IsLocalization.surj` and `IsLocalization.map_units` supply the numerator, the denominator
and the unit.

That a denominator is a nonzerodivisor is a separate, purely sheaf-theoretic point: if
`b * s = 0` then every germ of `s` vanishes, hence `s = 0` by `TopCat.Presheaf.section_ext`.
No affineness is used, so `b` is a nonzerodivisor over an arbitrary open set, not merely over
an affine one.

Shrinking the neighbourhood is harmless, by `AlgebraicGeometry.mul_toTotalQuotientSheaf_eq_of_le`
together with the restriction-stability built into `TopCat.Presheaf.SubmonoidPresheaf`; this is
what allows the neighbourhood to be taken affine on a scheme.

## References

* [Stacks Project, Tag 01X2](https://stacks.math.columbia.edu/tag/01X2)
* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}}

/-- For a sheaf of commutative rings, a section over an open set whose germ at every point of
that open set is a nonzerodivisor is itself a nonzerodivisor in the ring of sections. This is
the inclusion of the denominator submonoid of the total quotient presheaf into the
nonzerodivisors, and it needs no hypothesis on the open set. -/
theorem mem_nonZeroDivisors_of_mem_submonoidPresheafOfStalk
    (O : TopCat.Sheaf CommRingCat.{u} X) {U : Opens X} {b : O.presheaf.obj (op U)}
    (hb : b ∈ (O.presheaf.submonoidPresheafOfStalk
      fun y => (O.presheaf.stalk y)⁰).obj (op U)) :
    b ∈ (O.presheaf.obj (op U))⁰ := by
  simp only [TopCat.Presheaf.submonoidPresheafOfStalk_obj, Submonoid.mem_iInf,
    Submonoid.mem_comap] at hb
  refine mem_nonZeroDivisors_iff_right.mpr fun s hs => ?_
  refine TopCat.Presheaf.section_ext O U s 0 fun y hy => ?_
  have h1 : (O.presheaf.germ U y hy).hom s * (O.presheaf.germ U y hy).hom b = 0 := by
    rw [← map_mul, hs, map_zero]
  simpa only [map_zero] using mem_nonZeroDivisors_iff_right.mp (hb ⟨y, hy⟩) _ h1

/-- Every section of the total quotient presheaf over an open set is a fraction: it has a
numerator and a denominator taken from the denominator submonoid. -/
theorem exists_mul_toTotalQuotientPresheaf_eq (F : TopCat.Presheaf CommRingCat.{u} X)
    (U : Opens X) (z : F.totalQuotientPresheaf.obj (op U)) :
    ∃ a b : F.obj (op U),
      b ∈ (F.submonoidPresheafOfStalk fun y => (F.stalk y)⁰).obj (op U) ∧
      z * F.toTotalQuotientPresheaf.app (op U) b = F.toTotalQuotientPresheaf.app (op U) a := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
    (M := (F.submonoidPresheafOfStalk fun y => (F.stalk y)⁰).obj (op U))
    (S := (F.submonoidPresheafOfStalk fun y => (F.stalk y)⁰).localizationPresheaf.obj (op U)) z
  exact ⟨a, b, b.2, hab⟩

/-- A denominator becomes a unit in the total quotient presheaf. -/
theorem isUnit_toTotalQuotientPresheaf_app (F : TopCat.Presheaf CommRingCat.{u} X)
    {U : Opens X} {b : F.obj (op U)}
    (hb : b ∈ (F.submonoidPresheafOfStalk fun y => (F.stalk y)⁰).obj (op U)) :
    IsUnit (F.toTotalQuotientPresheaf.app (op U) b) :=
  IsLocalization.map_units
    (S := (F.submonoidPresheafOfStalk fun y => (F.stalk y)⁰).localizationPresheaf.obj (op U))
    ⟨b, hb⟩

/-- The structure morphism to the total quotient sheaf is the objectwise localization map
followed by the sheafification unit, read on an individual section. -/
theorem toTotalQuotientSheaf_app_apply (O : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)
    (y : O.presheaf.obj (op U)) :
    (toTotalQuotientSheaf O).hom.app (op U) y =
      (toSheafify (Opens.grothendieckTopology X) O.presheaf.totalQuotientPresheaf).app (op U)
        (O.presheaf.toTotalQuotientPresheaf.app (op U) y) :=
  rfl

/-- The scheme-level reading of `AlgebraicGeometry.toTotalQuotientSheaf_app_apply`. -/
theorem Scheme.toTotalQuotientSheaf_app_apply (Y : Scheme.{u}) (U : Y.Opens) (y : Γ(Y, U)) :
    Y.toTotalQuotientSheaf.hom.app (op U) y =
      (toSheafify (Opens.grothendieckTopology Y) Y.presheaf.totalQuotientPresheaf).app (op U)
        (Y.presheaf.toTotalQuotientPresheaf.app (op U) y) :=
  rfl

/-- A denominator becomes a unit in the total quotient sheaf. -/
private theorem isUnit_toTotalQuotientSheaf_app (O : TopCat.Sheaf CommRingCat.{u} X)
    {V : Opens X} {b : O.presheaf.obj (op V)}
    (hb : b ∈ (O.presheaf.submonoidPresheafOfStalk fun y => (O.presheaf.stalk y)⁰).obj (op V)) :
    IsUnit ((toTotalQuotientSheaf O).hom.app (op V) b) := by
  rw [toTotalQuotientSheaf_app_apply]
  exact (isUnit_toTotalQuotientPresheaf_app O.presheaf hb).map
    ((toSheafify (Opens.grothendieckTopology X) O.presheaf.totalQuotientPresheaf).app (op V)).hom

/-- A fraction description of a section of the total quotient sheaf restricts to any smaller
open set. -/
theorem mul_toTotalQuotientSheaf_eq_of_le (O : TopCat.Sheaf CommRingCat.{u} X)
    {V W : Opens X} (hWV : W ≤ V) {t : (totalQuotientSheaf O).presheaf.obj (op V)}
    {a b : O.presheaf.obj (op V)}
    (h : t * (toTotalQuotientSheaf O).hom.app (op V) b =
      (toTotalQuotientSheaf O).hom.app (op V) a) :
    (totalQuotientSheaf O).presheaf.map (homOfLE hWV).op t *
        (toTotalQuotientSheaf O).hom.app (op W) (O.presheaf.map (homOfLE hWV).op b) =
      (toTotalQuotientSheaf O).hom.app (op W) (O.presheaf.map (homOfLE hWV).op a) := by
  have hnat : ∀ y : O.presheaf.obj (op V),
      (toTotalQuotientSheaf O).hom.app (op W) (O.presheaf.map (homOfLE hWV).op y) =
        (totalQuotientSheaf O).presheaf.map (homOfLE hWV).op
          ((toTotalQuotientSheaf O).hom.app (op V) y) :=
    fun y => NatTrans.naturality_apply (toTotalQuotientSheaf O).hom (homOfLE hWV).op y
  rw [hnat, hnat, ← map_mul, h]

/-- **Sections of the total quotient sheaf are locally fractions.** Around every point of `U`
there is an open neighbourhood `V ⊆ U` and sections `a`, `b` over `V`, with `b` a denominator,
such that `t|_V * b = a` in the total quotient sheaf over `V`.

The sheaf of total quotient rings is a sheafification, so `t` itself need not be a fraction
over `U`; this local statement is the correct replacement. -/
theorem exists_nhds_mul_toTotalQuotientSheaf_eq (O : TopCat.Sheaf CommRingCat.{u} X)
    {U : Opens X} (t : (totalQuotientSheaf O).presheaf.obj (op U)) {x : X} (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∃ a b : O.presheaf.obj (op V),
        b ∈ (O.presheaf.submonoidPresheafOfStalk
          fun y => (O.presheaf.stalk y)⁰).obj (op V) ∧
        (totalQuotientSheaf O).presheaf.map (homOfLE hVU).op t *
            (toTotalQuotientSheaf O).hom.app (op V) b =
          (toTotalQuotientSheaf O).hom.app (op V) a := by
  obtain ⟨V, hVU, hxV, z, hz⟩ : ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∃ z : O.presheaf.totalQuotientPresheaf.obj (op V),
        (toSheafify (Opens.grothendieckTopology X)
            O.presheaf.totalQuotientPresheaf).app (op V) z =
          (totalQuotientSheaf O).presheaf.map (homOfLE hVU).op t := by
    have hls := CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        O.presheaf.totalQuotientPresheaf) (U := op U) t
    rw [Opens.mem_grothendieckTopology] at hls
    obtain ⟨W, f, ⟨z, hzw⟩, hxW⟩ := hls x hx
    exact ⟨W, f.le, hxW, z, by rw [hzw]; congr 1⟩
  obtain ⟨a, b, hb, hab⟩ := exists_mul_toTotalQuotientPresheaf_eq O.presheaf V z
  refine ⟨V, hVU, hxV, a, b, hb, ?_⟩
  rw [toTotalQuotientSheaf_app_apply, toTotalQuotientSheaf_app_apply, ← hz, ← map_mul, hab]

/-- **Sections of the total quotient sheaf are locally fractions `a / b` with `b` a
nonzerodivisor.** Around every point of `U` there is an open neighbourhood `V ⊆ U` and sections
`a`, `b` over `V` with `b` a nonzerodivisor whose image in the total quotient sheaf is a unit,
such that `t|_V * b = a`; equivalently `t|_V = a / b`. -/
theorem exists_nhds_isFraction_totalQuotientSheaf (O : TopCat.Sheaf CommRingCat.{u} X)
    {U : Opens X} (t : (totalQuotientSheaf O).presheaf.obj (op U)) {x : X} (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∃ a b : O.presheaf.obj (op V), b ∈ (O.presheaf.obj (op V))⁰ ∧
        IsUnit ((toTotalQuotientSheaf O).hom.app (op V) b) ∧
        (totalQuotientSheaf O).presheaf.map (homOfLE hVU).op t *
            (toTotalQuotientSheaf O).hom.app (op V) b =
          (toTotalQuotientSheaf O).hom.app (op V) a := by
  obtain ⟨V, hVU, hxV, a, b, hb, hab⟩ :=
    exists_nhds_mul_toTotalQuotientSheaf_eq O t hx
  refine ⟨V, hVU, hxV, a, b, mem_nonZeroDivisors_of_mem_submonoidPresheafOfStalk O hb, ?_, hab⟩
  exact isUnit_toTotalQuotientSheaf_app O hb

/-- **The open-cover form.** A section of the total quotient sheaf over `U` is a fraction `a / b`
with `b` a nonzerodivisor on each member of an open cover of `U` by open subsets of `U`. -/
theorem exists_openCover_isFraction_totalQuotientSheaf (O : TopCat.Sheaf CommRingCat.{u} X)
    {U : Opens X} (t : (totalQuotientSheaf O).presheaf.obj (op U)) :
    ∃ (V : U → Opens X) (hVU : ∀ i, V i ≤ U)
      (a : ∀ i, O.presheaf.obj (op (V i))) (b : ∀ i, O.presheaf.obj (op (V i))),
      U ≤ ⨆ i, V i ∧ (∀ i, b i ∈ (O.presheaf.obj (op (V i)))⁰) ∧
        (∀ i, IsUnit ((toTotalQuotientSheaf O).hom.app (op (V i)) (b i))) ∧
        ∀ i, (totalQuotientSheaf O).presheaf.map (homOfLE (hVU i)).op t *
              (toTotalQuotientSheaf O).hom.app (op (V i)) (b i) =
            (toTotalQuotientSheaf O).hom.app (op (V i)) (a i) := by
  choose V hVU hxV a b hb hu heq using
    fun i : U => exists_nhds_isFraction_totalQuotientSheaf O t i.2
  refine ⟨V, hVU, a, b, fun x hxU => ?_, hb, hu, heq⟩
  exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hxV ⟨x, hxU⟩⟩

/-- **Sections of the sheaf of total quotient rings of a scheme are locally fractions, on affine
opens.** Around every point of `U` there is an *affine* open neighbourhood `V ⊆ U` and sections
`a`, `b ∈ Γ(X, V)` with `b` a nonzerodivisor becoming a unit, such that `t|_V * b = a`. -/
theorem Scheme.exists_isAffineOpen_nhds_isFraction_totalQuotientSheaf (Y : Scheme.{u})
    {U : Y.Opens} (t : Y.totalQuotientSheaf.presheaf.obj (op U)) {x : Y} (hx : x ∈ U) :
    ∃ (V : Y.Opens) (hVU : V ≤ U), IsAffineOpen V ∧ x ∈ V ∧
      ∃ a b : Γ(Y, V), b ∈ (Γ(Y, V))⁰ ∧
        IsUnit (Y.toTotalQuotientSheaf.hom.app (op V) b) ∧
        Y.totalQuotientSheaf.presheaf.map (homOfLE hVU).op t *
            Y.toTotalQuotientSheaf.hom.app (op V) b =
          Y.toTotalQuotientSheaf.hom.app (op V) a := by
  obtain ⟨V, hVU, hxV, a, b, hb, hab⟩ :=
    exists_nhds_mul_toTotalQuotientSheaf_eq Y.sheaf t hx
  obtain ⟨W, hWaff, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  refine ⟨W, le_trans hWV hVU, hWaff, hxW, Y.presheaf.map (homOfLE hWV).op a,
    Y.presheaf.map (homOfLE hWV).op b, ?_, ?_, ?_⟩
  · exact mem_nonZeroDivisors_of_mem_submonoidPresheafOfStalk Y.sheaf
      ((Y.presheaf.submonoidPresheafOfStalk
        fun y => (Y.presheaf.stalk y)⁰).map (homOfLE hWV).op hb)
  · exact isUnit_toTotalQuotientSheaf_app Y.sheaf
      ((Y.presheaf.submonoidPresheafOfStalk
        fun y => (Y.presheaf.stalk y)⁰).map (homOfLE hWV).op hb)
  · have h := mul_toTotalQuotientSheaf_eq_of_le Y.sheaf hWV hab
    rw [show (homOfLE (le_trans hWV hVU) : W ⟶ U).op =
        (homOfLE hVU : V ⟶ U).op ≫ (homOfLE hWV : W ⟶ V).op from rfl,
      Y.totalQuotientSheaf.presheaf.map_comp, ConcreteCategory.comp_apply]
    exact h

end AlgebraicGeometry

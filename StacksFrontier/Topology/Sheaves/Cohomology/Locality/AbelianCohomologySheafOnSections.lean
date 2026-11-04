module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge
public import StacksFrontier.CategoryTheory.Sites.SmallSiteSheafification

/-!
# Cohomology sheaves of a complex of abelian sheaves are locally computed by sections

Let `K` be a cochain complex of abelian sheaves on a topological space `Y`.  For an open
`U ⊆ Y` there is a canonical comparison

  `Hⁿ(Γ(U, K)) ⟶ Γ(U, Hⁿ(K))`

(`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology`, available because `Γ(U, -)` is
left exact).  This file proves that its kernel consists exactly of the classes that vanish on
the members of some open cover of `U`: a class of `Hⁿ(Γ(U, K))` induces the zero section of the
cohomology sheaf `Hⁿ(K)` if and only if every point of `U` has a neighbourhood `V ⊆ U` on which
the class restricts to zero in `Hⁿ(Γ(V, K))`.

This is the local half of the description of cohomology sheaves used in the proof of
[Stacks, Tag 01E4]: the cohomology sheaf of a complex is the sheaf *associated* to the presheaf
`U ↦ Hⁿ(Γ(U, K))`, and the only consequence of that description needed by a consumer that wants
a vanishing criterion is the identification of the kernel of the associated-sheaf map.  Unlike
`Stacks.Cohomology.HigherDirectImagePresheaf.higherDirectImage_iso_sheafify_preimageCohomology`,
which is pinned to module-valued sheaves at the universe of the space, everything here is for
abelian sheaves at any coefficient universe containing that of the space.  No `@[stacks 01E4]`
tag is placed: the statements below are weaker than, and not a restatement of, any clause of
that tag.

The argument is the one Tag 01E3 runs for sheaves of modules.  Pick an open `U` and a class
`ζ ∈ Hⁿ(Γ(U, K))`.  Left exactness of `Γ(U, -)` makes `Γ(U, Zⁿ K) ⟶ Zⁿ(Γ(U, K))` an
isomorphism, so `ζ` is the class of a section `z ∈ Γ(U, Zⁿ K)`, and `ζ` dies in `Γ(U, Hⁿ K)`
precisely when `Γ(U, π)(z) = 0` for the projection `π : Zⁿ K ⟶ Hⁿ K`.  Now `π` exhibits `Hⁿ K`
as a cokernel, so `Kⁿ⁻¹ ⟶ Zⁿ K ⟶ Hⁿ K` is an exact sequence of sheaves; `Γ(U, -)` is left
exact, so `z` with `Γ(U, π)(z) = 0` is a section of `ker π`, and the epimorphism
`Kⁿ⁻¹ ⟶ ker π` is locally surjective, which produces the cover and the local primitives.
Conversely a section of `Hⁿ K` that vanishes on a cover vanishes, because `Hⁿ K` is a sheaf.

## Main definitions

* `Stacks.Cohomology.AbelianHigherDirectImage.secAb`, `resAb`: sections of an abelian sheaf on
  a topological space over an open subset, and their restriction maps.

## Main results

* `Stacks.Cohomology.AbelianHigherDirectImage.homologyToMapHomology_eq_zero_iff`: the local
  vanishing criterion for the comparison `Hⁿ(Γ(U, K)) ⟶ Γ(U, Hⁿ K)`.
* `Stacks.Cohomology.AbelianHigherDirectImage.map_homologyπ_eq_zero_iff`: the same criterion at
  the level of cycles — a section of `Zⁿ K` induces the zero section of `Hⁿ K` exactly when it
  is locally a boundary.
* `Stacks.Cohomology.AbelianHigherDirectImage.eq_of_locally_eq`: a section of an abelian sheaf
  that vanishes locally vanishes.
* `Stacks.Cohomology.AbelianHigherDirectImage.isLocallySurjective_of_epi`: an epimorphism of
  abelian sheaves on a topological space is locally surjective.
* `Stacks.Cohomology.AbelianHigherDirectImage.homologyMap_comp_homologyToMapHomology`: the
  comparison `Hⁿ(Q C) ⟶ Q(Hⁿ C)` is natural in the functor `Q`, which is what turns the
  criterion into a statement about restriction maps.

## References

* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.RightDerivedCoEdge

universe u v w u₂

namespace Stacks.Cohomology.AbelianHigherDirectImage

section Functoriality

variable {B : Type u₂} [Category.{v} B] [Abelian B] {D : Type w} [Category.{u} D] [Abelian D]
  {Q Q' : B ⥤ D} [Q.Additive] [Q'.Additive] (β : Q ⟶ Q')

/-- **The comparison of cycles is natural in the functor.**  Both ways around the square are the
unique cycle of `Q' C` whose inclusion is `β` composed with `Q` applied to the inclusion of the
cycles of `C`. -/
lemma mapCycles_comp_cyclesMap (C : CochainComplex B ℕ) (n : ℕ) :
    mapCycles Q C n ≫ HomologicalComplex.cyclesMap
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app C) n =
      β.app (C.cycles n) ≫ mapCycles Q' C n := by
  rw [← cancel_mono (((Q'.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).iCycles n),
    Category.assoc, Category.assoc, HomologicalComplex.cyclesMap_i, mapCycles_i_assoc,
    mapCycles_i, show ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app C).f n =
      β.app (C.X n) from rfl]
  exact β.naturality (C.iCycles n)

/-- The class in `Hⁿ (Q' C)` of the image under `β` of a cycle of `Q C` is the image under the
homology map of `β` of its class in `Hⁿ (Q C)`. -/
private lemma mapCycles_homologyπ_homologyMap_aux (C : CochainComplex B ℕ) (n : ℕ) :
    mapCycles Q C n ≫ ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app C) n =
    β.app (C.cycles n) ≫ mapCycles Q' C n ≫
      ((Q'.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n := by
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    mapCycles_comp_cyclesMap, Category.assoc]

/-- **The comparison `Hⁿ (Q C) ⟶ Q (Hⁿ C)` is natural in the left exact functor `Q`.**  Both
composites are characterised on cycles, where they become the naturality square of `β` at the
projection `Zⁿ C ⟶ Hⁿ C`. -/
lemma homologyMap_comp_homologyToMapHomology [PreservesFiniteLimits Q]
    [PreservesFiniteLimits Q'] (C : CochainComplex B ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app C) n ≫
        homologyToMapHomology Q' C n =
      homologyToMapHomology Q C n ≫ β.app (C.homology n) := by
  rw [← cancel_epi (mapCycles Q C n ≫
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n), Category.assoc,
    Category.assoc, reassoc_of% mapCycles_homologyπ_homologyMap_aux β C n,
    mapCycles_comp_homologyπ_comp_homologyToMapHomology,
    mapCycles_comp_homologyπ_comp_homologyToMapHomology_assoc]
  exact (β.naturality (C.homologyπ n)).symm

/-- The class in `Hⁿ (Q' C)` of the image under `β` of a cycle of `Q C` is the image under the
homology map of `β` of its class in `Hⁿ (Q C)`. -/
lemma mapCycles_comp_homologyπ_comp_homologyMap (C : CochainComplex B ℕ) (n : ℕ) :
    mapCycles Q C n ≫ ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app C) n =
    β.app (C.cycles n) ≫ mapCycles Q' C n ≫
      ((Q'.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n :=
  mapCycles_homologyπ_homologyMap_aux β C n

end Functoriality

/-- An isomorphism of abelian groups sends only `0` to `0`. -/
lemma eq_zero_iff_of_isIso {A A' : AddCommGrpCat.{w}} (g : A ⟶ A') [IsIso g] (x : ToType A) :
    g x = 0 ↔ x = 0 := by
  have hm : Function.Injective (ConcreteCategory.hom g) := by
    rw [← AddCommGrpCat.mono_iff_injective]
    infer_instance
  exact ⟨fun h ↦ hm (h.trans (map_zero (ConcreteCategory.hom g)).symm),
    fun h ↦ by rw [h, map_zero]⟩

section Boundaries

variable {B : Type u₂} [Category.{v} B] [Abelian B]

/-- **A cycle has vanishing homology class in the complex of sections exactly when it is a
boundary there.**  For a left exact functor `Q` into abelian groups the comparison
`Q (Zⁿ C) ⟶ Zⁿ (Q C)` is an isomorphism, and `Hⁿ (Q C)` is the cokernel of the boundaries
inside `Zⁿ (Q C)`; reading the cokernel of abelian groups as a quotient gives the statement. -/
lemma homologyπ_mapCycles_eq_zero_iff (Q : B ⥤ AddCommGrpCat.{w}) [Q.Additive]
    [PreservesFiniteLimits Q] (C : CochainComplex B ℕ) (n : ℕ) (z : Q.obj (C.cycles n)) :
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n
        (mapCycles Q C n z) = 0 ↔
      ∃ t : Q.obj (C.X ((ComplexShape.up ℕ).prev n)),
        Q.map (C.toCycles ((ComplexShape.up ℕ).prev n) n) t = z := by
  set i := (ComplexShape.up ℕ).prev n with hi
  set QC := (Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C with hQC
  set T : ShortComplex AddCommGrpCat.{w} :=
    ShortComplex.mk (QC.toCycles i n) (QC.homologyπ n) (QC.toCycles_comp_homologyπ i n) with hT
  have hTex : T.Exact := T.exact_of_g_is_cokernel (QC.homologyIsCokernel i n hi.symm)
  have hcomp : Q.map (C.toCycles i n) ≫ mapCycles Q C n = QC.toCycles i n := by
    rw [← toCycles_comp_mapCyclesIso_inv Q C i n, Category.assoc,
      ← mapCyclesIso_hom Q C n, Iso.inv_hom_id, Category.comp_id]
  have hkey : ∀ t : Q.obj (C.X i), mapCycles Q C n (Q.map (C.toCycles i n) t) =
      QC.toCycles i n t := fun t ↦ by
    rw [← ConcreteCategory.comp_apply, hcomp]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := T.ab_exact_iff.mp hTex (mapCycles Q C n z) h
    have hmono : Function.Injective (mapCycles Q C n) := by
      rw [← AddCommGrpCat.mono_iff_injective]
      infer_instance
    exact ⟨t, hmono (by rwa [hkey t])⟩
  · rintro ⟨t, ht⟩
    rw [← ht, hkey t, ← ConcreteCategory.comp_apply, QC.toCycles_comp_homologyπ i n]
    simp

end Boundaries

section Space

/-- On an essentially small site, the maps inverted by sheafification of abelian presheaves are
exactly the locally bijective ones. -/
private theorem siteW {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{w} C] : J.WEqualsLocallyBijective AddCommGrpCat.{w} := by
  let : ((equivSmallModel.{w} C).inverse.inducedTopology J).WEqualsLocallyBijective
      AddCommGrpCat.{w} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _, w} J

variable {Y : Type u} [TopologicalSpace Y]

/-- **The maps of abelian presheaves on a topological space inverted by sheafification are the
locally bijective ones**, in any coefficient universe containing that of the space: the site
`Opens Y` is `u`-small, hence essentially small there. -/
theorem abelianSheafWEqualsLocallyBijective :
    (Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
  siteW _

/-- Sections of an abelian sheaf on `Y` over an open subset. -/
abbrev secAb (U : Opens Y) :
    Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{w}).obj (op U)

/-- Restriction of sections of abelian sheaves along an inclusion of open subsets. -/
abbrev resAb {U V : Opens Y} (h : V ≤ U) : secAb.{u, w} U ⟶ secAb.{u, w} V :=
  (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{w}).map (homOfLE h).op

/-- Taking sections of an abelian sheaf over an open subset is additive. -/
instance secAb_additive (U : Opens Y) : (secAb.{u, w} U).Additive := by
  change (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _).Additive
  infer_instance

/-- Taking sections of an abelian sheaf over an open subset is left exact: it is the inclusion
of sheaves into presheaves, which preserves limits because limits of sheaves are computed in
presheaves, followed by evaluation, which preserves limits because limits of presheaves are
computed pointwise. -/
instance secAb_preservesFiniteLimits (U : Opens Y) :
    PreservesFiniteLimits (secAb.{u, w} U) := by
  change PreservesFiniteLimits (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _)
  infer_instance

/-- Restriction of sections commutes with a map of abelian sheaves, read on elements. -/
lemma resAb_naturality_apply {U V : Opens Y} (h : V ≤ U)
    {A A' : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w}} (φ : A ⟶ A')
    (a : (secAb.{u, w} U).obj A) :
    (resAb.{u, w} h).app A' ((secAb.{u, w} U).map φ a) =
      (secAb.{u, w} V).map φ ((resAb.{u, w} h).app A a) := by
  rw [← ConcreteCategory.comp_apply, (resAb.{u, w} h).naturality φ,
    ConcreteCategory.comp_apply]

variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max u v}]

omit [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max u v}] in
/-- **Two sections of an abelian sheaf that agree locally agree.**  Forgetting the group
structure turns the sheaf into a sheaf of types, hence a separated presheaf, and the sieve on
which the two sections agree is covering. -/
theorem eq_of_locally_eq
    {H : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{max u v}} {U : Opens Y}
    (s t : (secAb.{u, max u v} U).obj H)
    (h : ∀ y ∈ U, ∃ (V : Opens Y) (hV : V ≤ U), y ∈ V ∧
      (resAb.{u, max u v} hV).app H s = (resAb.{u, max u v} hV).app H t) :
    s = t := by
  have hsep : Presieve.IsSeparated (Opens.grothendieckTopology Y)
      (H.obj ⋙ forget AddCommGrpCat.{max u v}) := by
    apply Presieve.IsSheaf.isSeparated
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose _ (forget AddCommGrpCat.{max u v})).obj H).property
  have hmem : Presheaf.equalizerSieve (F := H.obj) (X := op U) s t
      ∈ Opens.grothendieckTopology Y U := by
    intro y hy
    obtain ⟨V, hV, hyV, hst⟩ := h y hy
    exact ⟨V, homOfLE hV, hst, hyV⟩
  exact (hsep _ hmem).ext (fun _ _ hf => hf)

/-- **An epimorphism of abelian sheaves on a topological space is locally surjective.**  The
sheaf category is abelian, hence balanced, and the maps inverted by sheafification are the
locally bijective ones. -/
theorem isLocallySurjective_of_epi
    {G H : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{max u v}} (φ : G ⟶ H) [Epi φ] :
    Sheaf.IsLocallySurjective φ := by
  have := abelianSheafWEqualsLocallyBijective.{u, v} (Y := Y)
  exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v} φ).mpr inferInstance

/-- **A section of the cycles of a complex of abelian sheaves induces the zero section of the
cohomology sheaf exactly when it is locally a boundary.**  The projection `Zⁿ K ⟶ Hⁿ K` makes
`Hⁿ K` a cokernel, so `Kⁿ⁻¹ ⟶ Zⁿ K ⟶ Hⁿ K` is exact; taking sections is left exact, so a
section killed by the projection is a section of the kernel of the projection, and the
epimorphism from `Kⁿ⁻¹` onto that kernel is locally surjective.  Conversely a section of the
sheaf `Hⁿ K` vanishing on a cover vanishes. -/
theorem map_homologyπ_eq_zero_iff
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{max u v}) ℕ)
    (n : ℕ) (U : Opens Y) (z : (secAb.{u, max u v} U).obj (K.cycles n)) :
    (secAb.{u, max u v} U).map (K.homologyπ n) z = 0 ↔
      ∀ y ∈ U, ∃ (V : Opens Y) (hV : V ≤ U), y ∈ V ∧
        ∃ t : (secAb.{u, max u v} V).obj (K.X ((ComplexShape.up ℕ).prev n)),
          (secAb.{u, max u v} V).map (K.toCycles ((ComplexShape.up ℕ).prev n) n) t =
            (resAb.{u, max u v} hV).app (K.cycles n) z := by
  set i := (ComplexShape.up ℕ).prev n with hi
  set S : ShortComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{max u v}) :=
    ShortComplex.mk (K.toCycles i n) (K.homologyπ n) (K.toCycles_comp_homologyπ i n) with hS
  constructor
  · intro hz y hy
    have hSex : S.Exact := S.exact_of_g_is_cokernel (K.homologyIsCokernel i n hi.symm)
    have hS2ex : (ShortComplex.mk S.iCycles S.g S.iCycles_g).Exact :=
      ShortComplex.exact_of_f_is_kernel _ S.cyclesIsKernel
    have hmap := hS2ex.map_of_mono_of_preservesKernel (secAb.{u, max u v} U)
      inferInstance inferInstance
    obtain ⟨z₀, hz₀⟩ := (ShortComplex.ab_exact_iff _).mp hmap z hz
    have hz₀' : (secAb.{u, max u v} U).map S.iCycles z₀ = z := hz₀
    have hepi : Epi S.toCycles := hSex.epi_toCycles
    have hpls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) S.toCycles.hom :=
      isLocallySurjective_of_epi.{u, v} _
    have hmem : Presheaf.imageSieve S.toCycles.hom z₀ ∈ Opens.grothendieckTopology Y U :=
      Presheaf.imageSieve_mem _ S.toCycles.hom (U := op U) z₀
    obtain ⟨V, g, hg, hyV⟩ := hmem y hy
    have happ := Presheaf.app_localPreimage S.toCycles.hom z₀ g hg
    refine ⟨V, leOfHom g, hyV, Presheaf.localPreimage S.toCycles.hom z₀ g hg, ?_⟩
    have hgeq : g = homOfLE (leOfHom g) := Subsingleton.elim _ _
    have h1 : (secAb.{u, max u v} V).map S.toCycles
        (Presheaf.localPreimage S.toCycles.hom z₀ g hg) =
        (resAb.{u, max u v} (leOfHom g)).app S.cycles z₀ := by
      rw [show (secAb.{u, max u v} V).map S.toCycles = S.toCycles.hom.app (op V) from rfl, happ,
        hgeq]
      rfl
    have h2 : (secAb.{u, max u v} V).map S.f
        (Presheaf.localPreimage S.toCycles.hom z₀ g hg) =
        (resAb.{u, max u v} (leOfHom g)).app (K.cycles n) z := by
      rw [show S.f = S.toCycles ≫ S.iCycles from S.toCycles_i.symm, Functor.map_comp,
        ConcreteCategory.comp_apply, h1, ← resAb_naturality_apply, hz₀']
    exact h2
  · intro h
    refine eq_of_locally_eq.{u, v} _ 0 (fun y hy ↦ ?_)
    obtain ⟨V, hV, hyV, t, ht⟩ := h y hy
    refine ⟨V, hV, hyV, ?_⟩
    rw [resAb_naturality_apply, ← ht, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      K.toCycles_comp_homologyπ i n]
    simp

/-- **A cohomology class of the complex of sections induces the zero section of the cohomology
sheaf exactly when it vanishes on the members of an open cover.**  This is the local half of the
description of `Hⁿ K` as the sheaf associated to the presheaf `U ↦ Hⁿ(Γ(U, K))`: the kernel of
the comparison `Hⁿ(Γ(U, K)) ⟶ Γ(U, Hⁿ K)` is exactly the subgroup of locally vanishing
classes. -/
theorem homologyToMapHomology_eq_zero_iff
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{max u v}) ℕ)
    (n : ℕ) (U : Opens Y)
    (ζ : (((secAb.{u, max u v} U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n) :
    homologyToMapHomology (secAb.{u, max u v} U) K n ζ = 0 ↔
      ∀ y ∈ U, ∃ (V : Opens Y) (hV : V ≤ U), y ∈ V ∧
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (resAb.{u, max u v} hV)
            (ComplexShape.up ℕ)).app K) n ζ = 0 := by
  set i := (ComplexShape.up ℕ).prev n
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective
    ((((secAb.{u, max u v} U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ
      n)).mp inferInstance ζ
  set z := (mapCyclesIso (secAb.{u, max u v} U) K n).inv c with hzdef
  have hzc : mapCycles (secAb.{u, max u v} U) K n z = c := by
    rw [hzdef, ← ConcreteCategory.comp_apply, ← mapCyclesIso_hom (secAb.{u, max u v} U) K n,
      Iso.inv_hom_id]
    simp
  have hL : homologyToMapHomology (secAb.{u, max u v} U) K n ζ =
      (secAb.{u, max u v} U).map (K.homologyπ n) z := by
    rw [← hc, ← hzc, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      mapCycles_comp_homologyπ_comp_homologyToMapHomology]
  have hR : ∀ (V : Opens Y) (hV : V ≤ U),
      (HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
          (resAb.{u, max u v} hV) (ComplexShape.up ℕ)).app K) n ζ = 0) ↔
        ∃ t : (secAb.{u, max u v} V).obj (K.X i),
          (secAb.{u, max u v} V).map (K.toCycles i n) t =
            (resAb.{u, max u v} hV).app (K.cycles n) z := by
    intro V hV
    rw [← homologyπ_mapCycles_eq_zero_iff (secAb.{u, max u v} V) K n
      ((resAb.{u, max u v} hV).app (K.cycles n) z)]
    congr! 1
    have happ := ConcreteCategory.congr_hom
      (mapCycles_comp_homologyπ_comp_homologyMap (resAb.{u, max u v} hV) K n) z
    simp only [ConcreteCategory.comp_apply] at happ
    rwa [hzc, hc] at happ
  rw [hL, map_homologyπ_eq_zero_iff]
  exact forall₂_congr fun y _ ↦ exists₂_congr fun V hV ↦ and_congr_right' (hR V hV).symm

end Space

end Stacks.Cohomology.AbelianHigherDirectImage

end

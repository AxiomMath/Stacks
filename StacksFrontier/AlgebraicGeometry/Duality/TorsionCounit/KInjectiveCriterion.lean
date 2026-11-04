module

public import StacksFrontier.RingTheory.Dualizing.CompareTorsionFunctors
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison

/-!
# A concrete criterion for the derived torsion counit to be invertible

Let `I` be a finitely generated ideal of a commutative ring `A`. Derived `I`-power torsion
`RΓ_I` is the total right derived functor of the torsion-submodule functor `Γ_I`, and
`Dualizing.derivedPowerTorsionCounit` is the canonical map `RΓ_I → id` normalized by the
degreewise torsion-submodule inclusion. Stacks Tag 0955 part (1) asserts that this counit is
invertible at every object of `D(A)` whose cohomology modules are `I`-power torsion, provided
`A` is Noetherian.

That assertion is about a functor produced by an abstract derived-functor construction. This
file turns it into a statement about complexes: the unit of the derived functor is invertible on
K-injective complexes, so for a K-injective `J` the counit at `Q(J)` is, up to invertible
factors, the image under `Q` of the degreewise inclusion `Γ_I(J) ⟶ J` of the termwise
`I`-power-torsion subcomplex. Hence the counit at `Q(J)` is invertible exactly when that
degreewise inclusion is a quasi-isomorphism — a statement entirely about modules and
differentials.

Two consequences are recorded. First, if a K-injective representative can be chosen with all of
its terms `I`-power torsion, the counit is invertible there; this is the mechanism by which the
Noetherian hypothesis will enter, through the injectivity of `J[I^∞]` for injective `J`
(Stacks Tag 08XW). Second, at an object with `I`-power-torsion cohomology the counit is
invertible exactly when the comparison `RΓ_I ⟶ RΓ_Z` of Stacks Tag 0A6U is, so part (1) of
Tag 0955 and the restriction of part (3) to `D_{I^∞-torsion}(A)` are the same statement.

## Main definitions

* `Dualizing.TorsionCounit.powerTorsionSubcomplexι` — the degreewise inclusion of the termwise
  `I`-power-torsion subcomplex of a complex of `A`-modules.

## Main results

* `Dualizing.TorsionCounit.isIso_derivedPowerTorsionUnit_app_of_isKInjective` — the unit of the
  total right derived functor `RΓ_I` is invertible at a K-injective complex.
* `Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_Q_iff_quasiIso` — for a
  K-injective `J`, the counit at `Q(J)` is invertible if and only if the degreewise torsion
  inclusion `Γ_I(J) ⟶ J` is a quasi-isomorphism.
* `Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_of_isIPowerTorsion_kInjective` —
  the counit is invertible at any object represented by a K-injective complex whose terms are
  all `I`-power torsion.
* `Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_iff_isIso_compareTorsionFunctors`
  — at an object with `I`-power-torsion cohomology, the counit of Tag 0A6L is invertible exactly
  when the comparison of Tag 0A6U is.

## Implementation notes

Carrying no `@[stacks]` attribute is deliberate: nothing here is a part of Tag 0955, whose
covering set is the three enumerated assertions of the source, and none of those is proved here.

The universe convention is the one forced by `Dualizing.derivedPowerTorsion`: the ring lives in
`Type u` and the modules in `Type (max u v)`, as the available construction of enough injectives
requires.

## References

* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0A6L](https://stacks.math.columbia.edu/tag/0A6L)
* [Stacks Project, Tag 0A6U](https://stacks.math.columbia.edu/tag/0A6U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Dualizing.TorsionCounit

attribute [local instance] HasDerivedCategory.standard

/-- Two morphisms with the same composite after invertible prefixes are invertible together. -/
private lemma isIso_iff_of_comp_eq {C : Type*} [Category C] {W X Y Z : C}
    {a : W ⟶ X} {c : X ⟶ Z} {b : W ⟶ Y} {d : Y ⟶ Z}
    (h : a ≫ c = b ≫ d) (ha : IsIso a) (hb : IsIso b) : IsIso c ↔ IsIso d := by
  rw [← isIso_comp_left_iff a c, h, isIso_comp_left_iff]

/-- Across a commuting square whose two other edges are invertible, the remaining two edges are
invertible together. -/
private lemma isIso_iff_of_naturality {C : Type*} [Category C] {W X Y Z : C}
    {p : W ⟶ X} {y : X ⟶ Z} {x : W ⟶ Y} {q : Y ⟶ Z}
    (h : p ≫ y = x ≫ q) (hx : IsIso x) (hy : IsIso y) : IsIso p ↔ IsIso q := by
  rw [← isIso_comp_right_iff p y, h, isIso_comp_left_iff]

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The degreewise inclusion of the termwise `I`-power-torsion subcomplex of a complex of
`A`-modules, as a natural transformation of functors on cochain complexes. -/
def powerTorsionSubcomplexι :
    let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    (powerTorsionFunctor.{u, v} A I).mapHomologicalComplex (.up ℤ) ⋙
      P.ι.mapHomologicalComplex (.up ℤ) ⟶ 𝟭 _ where
  app K :=
    { f := fun n ↦ (powerTorsionCounit.{u, v} A I).app (K.X n)
      comm' := fun _ _ _ ↦ by ext x; rfl }
  naturality K L f := by ext n x; rfl

/-- On the homotopy category, the canonical degreewise torsion inclusion is the image of
`Dualizing.TorsionCounit.powerTorsionSubcomplexι`. -/
theorem powerTorsionHomotopyInclusion_app_quotient_obj
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (powerTorsionHomotopyInclusion.{u, v} A I).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj J) =
      (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map
        ((powerTorsionSubcomplexι.{u, v} A I).app J) :=
  rfl

variable (hI : I.FG)

/-- Local cohomology `RΓ_I` is a right derived functor of the degreewise torsion functor, with
`Dualizing.derivedPowerTorsionUnit` as its unit. -/
theorem isRightDerivedFunctor_derivedPowerTorsion :
    (derivedPowerTorsion.{u, v} A I hI).IsRightDerivedFunctor
      (derivedPowerTorsionUnit.{u, v} A I hI)
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) := by
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
  let : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
  let : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  let H := (powerTorsionFunctor.{u, v} A I).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh (C := P.FullSubcategory)
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)
  let : H.HasPointwiseRightDerivedFunctor W :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
        max u v, max (u + 1) (v + 1), max (u + 1) (v + 1),
        max (u + 1) (v + 1), max (u + 1) (v + 1), max (u + 1) (v + 1)} H
      (fun K ↦ by
        obtain ⟨L, q, hq, hL⟩ := CochainComplex.exists_quasiIso_isKInjective K
        exact ⟨L, q, hL, hq⟩)).1
  show (H.totalRightDerived DerivedCategory.Qh W).IsRightDerivedFunctor
    (H.totalRightDerivedUnit DerivedCategory.Qh W) W
  infer_instance

/-- The unit of the total right derived functor `RΓ_I` is invertible at every K-injective
complex: a right derived functor is computed by a K-injective resolution. -/
theorem isIso_derivedPowerTorsionUnit_app_of_isKInjective
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ) (hJ : J.IsKInjective) :
    IsIso ((derivedPowerTorsionUnit.{u, v} A I hI).app
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj J)) := by
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
  let : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
  let : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  let H := (powerTorsionFunctor.{u, v} A I).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh (C := P.FullSubcategory)
  let : (derivedPowerTorsion.{u, v} A I hI).IsRightDerivedFunctor
      (derivedPowerTorsionUnit.{u, v} A I hI)
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) :=
    isRightDerivedFunctor_derivedPowerTorsion.{u, v} A I hI
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      max u v, max (u + 1) (v + 1), max (u + 1) (v + 1),
      max (u + 1) (v + 1), max (u + 1) (v + 1), max (u + 1) (v + 1)} H
    (fun K ↦ by
      obtain ⟨L, q, hq, hL⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨L, q, hL, hq⟩)).2 DerivedCategory.Qh _
    (derivedPowerTorsionUnit.{u, v} A I hI) J hJ

/-- Invertibility of the derived torsion counit depends only on the isomorphism class of the
object, since the counit is a natural transformation. -/
theorem isIso_derivedPowerTorsionCounit_app_of_iso
    {X Y : DerivedCategory (ModuleCat.{max u v} A)} (e : X ≅ Y)
    (h : IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app X)) :
    IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app Y) :=
  (NatTrans.isIso_app_iff_of_iso _ e).mp h

/-- **The criterion.** For a K-injective complex `J`, the derived torsion counit at `Q(J)` is
invertible if and only if the degreewise inclusion `Γ_I(J) ⟶ J` of the termwise
`I`-power-torsion subcomplex is a quasi-isomorphism. -/
theorem isIso_derivedPowerTorsionCounit_app_Q_iff_quasiIso
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ) (hJ : J.IsKInjective) :
    IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app (DerivedCategory.Q.obj J)) ↔
      QuasiIso ((powerTorsionSubcomplexι.{u, v} A I).app J) := by
  set Khot := (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj J
    with hKhot
  -- the canonicity equation of the counit at the homotopy class of `J`
  have hcan := derivedPowerTorsionCounit_isCanonical.{u, v} A I hI Khot
  rw [powerTorsionHomotopyInclusion_app_quotient_obj.{u, v} A I J] at hcan
  have hunit : IsIso ((derivedPowerTorsionUnit.{u, v} A I hI).app Khot) :=
    isIso_derivedPowerTorsionUnit_app_of_isKInjective.{u, v} A I hI J hJ
  -- the counit at `Qh(J)` is invertible exactly when the image of the inclusion is
  have key : IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app
        (DerivedCategory.Qh.obj Khot)) ↔
      IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map
          ((powerTorsionSubcomplexι.{u, v} A I).app J))) :=
    isIso_iff_of_comp_eq hcan
      (Functor.mapIso _ (asIso ((derivedPowerTorsionUnit.{u, v} A I hI).app Khot))).isIso_hom
      (NatIso.hom_app_isIso _ _)
  -- transport from `Qh(J)` to `Q(J)` along the canonical isomorphism
  have hQ : IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app (DerivedCategory.Q.obj J)) ↔
      IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app
        (DerivedCategory.Qh.obj Khot)) :=
    ⟨fun h ↦ isIso_derivedPowerTorsionCounit_app_of_iso.{u, v} A I hI
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app J).symm h,
      fun h ↦ isIso_derivedPowerTorsionCounit_app_of_iso.{u, v} A I hI
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app J) h⟩
  -- and the image of the inclusion under `Qh ∘ quotient` is invertible exactly when under `Q`
  have hmap : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map
          ((powerTorsionSubcomplexι.{u, v} A I).app J))) ↔
      IsIso (DerivedCategory.Q.map ((powerTorsionSubcomplexι.{u, v} A I).app J)) := by
    have hn := (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).hom.naturality
      ((powerTorsionSubcomplexι.{u, v} A I).app J)
    exact isIso_iff_of_naturality hn (NatIso.hom_app_isIso _ _) (NatIso.hom_app_isIso _ _)
  rw [hQ, key, hmap, DerivedCategory.isIso_Q_map_iff_quasiIso]

/-- The underived torsion counit `Γ_I(M) ⟶ M` is invertible at an `I`-power-torsion module:
there the torsion submodule is everything. -/
theorem isIso_powerTorsionCounit_app_of_isIPowerTorsion (M : ModuleCat.{max u v} A)
    (hM : IsIPowerTorsion A M I) : IsIso ((powerTorsionCounit.{u, v} A I).app M) := by
  have hmem : ∀ m : M, m ∈ Ideal.primaryComponent M I := by
    intro m
    obtain ⟨n, -, hn⟩ := hM m
    rw [Ideal.primaryComponent_mem]
    exact ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr fun a ↦ hn a.1 a.2⟩
  refine ⟨⟨ModuleCat.ofHom ((LinearMap.id (R := A) (M := M)).codRestrict _ hmem), ?_, ?_⟩⟩
  · ext x
    rfl
  · ext x
    rfl

/-- **The counit is invertible on a torsion K-injective complex.** If a K-injective complex has
all of its terms `I`-power torsion, the derived torsion counit is invertible at the object it
represents: the degreewise torsion inclusion is then the identity. -/
theorem isIso_derivedPowerTorsionCounit_app_Q_of_forall_isIPowerTorsion
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ) (hJ : J.IsKInjective)
    (hterm : ∀ n : ℤ, IsIPowerTorsion A (J.X n) I) :
    IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app (DerivedCategory.Q.obj J)) := by
  rw [isIso_derivedPowerTorsionCounit_app_Q_iff_quasiIso.{u, v} A I hI J hJ]
  have hcomp : ∀ n : ℤ, IsIso (((powerTorsionSubcomplexι.{u, v} A I).app J).f n) := fun n ↦
    isIso_powerTorsionCounit_app_of_isIPowerTorsion.{u, v} A I (J.X n) (hterm n)
  have : IsIso ((powerTorsionSubcomplexι.{u, v} A I).app J) :=
    HomologicalComplex.Hom.isIso_of_components _
  infer_instance

/-- **Stacks 0955, part (1), at an object with a torsion K-injective representative.** If `K` is
represented by a K-injective complex all of whose terms are `I`-power torsion, then the counit
`RΓ_I(K) ⟶ K` is an isomorphism. -/
theorem isIso_derivedPowerTorsionCounit_app_of_isIPowerTorsion_kInjective
    {K : DerivedCategory (ModuleCat.{max u v} A)}
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ) (hJ : J.IsKInjective)
    (hterm : ∀ n : ℤ, IsIPowerTorsion A (J.X n) I) (e : DerivedCategory.Q.obj J ≅ K) :
    IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app K) :=
  isIso_derivedPowerTorsionCounit_app_of_iso.{u, v} A I hI e
    (isIso_derivedPowerTorsionCounit_app_Q_of_forall_isIPowerTorsion.{u, v} A I hI J hJ hterm)

/-- **Part (1) of Stacks Tag 0955 is the restriction of part (3) to `D_{I^∞-torsion}(A)`.** At an
object whose cohomology modules are `I`-power torsion, the counit `RΓ_I ⟶ id` of Tag 0A6L is
invertible exactly when the comparison `RΓ_I ⟶ RΓ_Z` of Tag 0A6U is. Indeed the comparison
factors the counit through the counit of `RΓ_Z`, which is invertible on the subcategory because
`RΓ_Z` is a coreflection onto it. -/
theorem isIso_derivedPowerTorsionCounit_app_iff_isIso_compareTorsionFunctors
    (K : PowerTorsionDerivedCategory.{u, max u v} A I hI) :
    IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app K.obj) ↔
      IsIso ((compareTorsionFunctors.{u, v} A I hI).app K.obj) := by
  have hcounitZ : IsIso ((localCohomologyAdjunction.{u, max u v} A I hI).counit.app K.obj) :=
    isIso_localCohomologyAdjunction_counit.{u, max u v} A I hI K
  have hsq := isIso_iff_of_naturality
    (compareTorsionFunctors_app_counit.{u, v} A I hI K.obj)
    (NatIso.hom_app_isIso _ _) hcounitZ
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := hsq.mpr h
    exact isIso_of_fully_faithful (derivedPowerTorsionProperty A I hI).ι
      ((compareTorsionFunctors.{u, v} A I hI).app K.obj)
  · have := h
    exact hsq.mp inferInstance

end Dualizing.TorsionCounit

end

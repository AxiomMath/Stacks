module

public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsionCounit
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison
public import StacksFrontier.RingTheory.Dualizing.Ext
public import StacksFrontier.Algebra.Module.IPowerTorsion

/-!
# Dividing a module by its ideal-power torsion

Let `I` be a finitely generated ideal of a commutative ring `A`, let `M` be an `A`-module and
let `Z = V(I)`. The two local cohomology theories of [Stacks, Tag 0AW0] are assembled here as
functors: `H^p_I` is the `p`-th cohomology of derived `I`-power torsion `RΓ_I`, and `H^p_Z` is
the `p`-th cohomology of local cohomology `RΓ_Z` with support in `Z`. Each comes with its
canonical map to `M` in degree zero, the counit of the adjunction defining it.

Write `N = M[I^∞]` and `M' = M/N`. What is proved here is part (2) of the source for the two
statements that do not need the long exact sequence:

* `H^p_Z(N) = 0` for `p ≠ 0`. The mechanism is that `N` placed in degree zero already has
  `I`-power-torsion cohomology, so it lies in the subcategory `D_{I^∞-torsion}(A)`, and the
  counit of a coreflection onto a full subcategory is invertible at the objects of that
  subcategory. Hence `RΓ_Z(N) ≅ N` in `D(A)`, and a module placed in degree zero has no
  cohomology away from degree zero.
* `H^0_Z(M') = 0`. Here `H^0_Z(M')` is `I`-power torsion, being the degree-zero cohomology of an
  object of `D_{I^∞-torsion}(A)`, and it injects into `M'` by Stacks 0DWR. But `M'` is
  `I`-power-torsion free by Stacks 05EB, and an element killed by `I^n` in a module killed by no
  element of `I` is zero, by induction on `n`.

## Main definitions

* `Stacks.Duality.idealLocalCohomology` — the functor `H^p_I`.
* `Stacks.Duality.supportLocalCohomology` — the functor `H^p_Z`.
* `Stacks.Duality.idealLocalCohomologyToModule`,
  `Stacks.Duality.supportLocalCohomologyToModule` — their canonical maps to `M` in degree
  zero.

## Main results

* `Stacks.Duality.supportLocalCohomology_torsion_higher` — part (2) of the source's higher
  vanishing: `H^p_Z` kills the `I`-power-torsion submodule for `p > 0`.
* `Stacks.Duality.supportLocalCohomology_quotient_zero` — part (2) in degree zero: `H^0_Z`
  kills the quotient by the `I`-power-torsion submodule.

## Implementation notes

The constructions are the library's: `Dualizing.derivedPowerTorsion` for `RΓ_I`,
`Dualizing.localCohomologyFunctor` for `RΓ_Z`, and `Dualizing.powerTorsionComparison` for the
comparison of [Stacks, Tag 0A6N]. The object `(supportLocalCohomology A I hI p).obj M` is the
library's `Stacks.LocalCohomology.localCohomologyModule A I hI M p` and
`supportLocalCohomologyToModule` is its `Stacks.LocalCohomology.localCohomologyZeroToModule`;
what is new here is only the functor packaging, which the source's
`H^p(M) = H^p(M')` statements need in order to speak of the map induced by `M ⟶ M'`.

The `I`-power-torsion submodule `M[I^∞]` is Mathlib's `Ideal.primaryComponent M I`; that it is
itself `I`-power torsion is read off the library's `Dualizing.powerTorsionFunctor`, which has it
as the defining property of its values, rather than re-proved.

## References

* [Stacks Project, Tag 0AW0](https://stacks.math.columbia.edu/tag/0AW0)
* [Stacks Project, Tag 05EB](https://stacks.math.columbia.edu/tag/05EB)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.Duality

/-- The `p`-th local cohomology functor for ideal-power torsion. -/
noncomputable def idealLocalCohomology
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (p : ℤ) :
    ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
  DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
    Dualizing.derivedPowerTorsion.{u, v} A I hI ⋙
    Dualizing.powerTorsionComparison A I hI ⋙
    (Dualizing.derivedPowerTorsionProperty A I hI).ι ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p

/-- The `p`-th local cohomology functor with support in `V(I)`. -/
noncomputable def supportLocalCohomology
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (p : ℤ) :
    ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
  DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
    Dualizing.localCohomologyFunctor A I hI ⋙
    (Dualizing.derivedPowerTorsionProperty A I hI).ι ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p

/-- The canonical map from zeroth ideal local cohomology into the original module. -/
noncomputable def idealLocalCohomologyToModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) :
    (idealLocalCohomology.{u, v} A I hI 0).obj M ⟶ M :=
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
      (((Dualizing.powerTorsionComparisonCompInclusionIso A I hI).hom.app
        ((Dualizing.derivedPowerTorsion.{u, v} A I hI).obj X)) ≫
        (Dualizing.derivedPowerTorsionCounit.{u, v} A I hI).app X) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max u v} A) 0).hom.app M

/-- The canonical map from zeroth local cohomology supported on `V(I)` into the module. -/
noncomputable def supportLocalCohomologyToModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) :
    (supportLocalCohomology.{u, v} A I hI 0).obj M ⟶ M :=
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
      ((Dualizing.localCohomologyAdjunction A I hI).counit.app X) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max u v} A) 0).hom.app M

/-! ### Higher vanishing on the torsion submodule -/

/-- Local cohomology with support in `V(I)` of an `I`-power-torsion module is concentrated in
degree zero: such a module already lies in `D_{I^∞-torsion}(A)`, where the counit of the
defining adjunction is invertible. -/
theorem supportLocalCohomology_isZero_of_isIPowerTorsion
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (N : ModuleCat.{max u v} A) (hN : IsIPowerTorsion A N I) (p : ℤ) (hp : p ≠ 0) :
    IsZero ((supportLocalCohomology.{u, v} A I hI p).obj N) := by
  set P := Dualizing.derivedPowerTorsionProperty A I hI with hP
  set X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N with hX
  have hprop : P X :=
    Dualizing.PowerTorsionBaseChange.derivedPowerTorsionProperty_singleFunctor I hI N hN
  have hiso : IsIso ((Dualizing.localCohomologyAdjunction A I hI).counit.app X) :=
    Dualizing.isIso_localCohomologyAdjunction_counit A I hI ⟨X, hprop⟩
  have e : P.ι.obj ((Dualizing.localCohomologyFunctor A I hI).obj X) ≅ X :=
    @asIso _ _ _ _ ((Dualizing.localCohomologyAdjunction A I hI).counit.app X) hiso
  change IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p).obj
    (P.ι.obj ((Dualizing.localCohomologyFunctor A I hI).obj X)))
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p).mapIso e)
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) p).app
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj N))
  exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 N p hp

/-- **Stacks 0AW0, part (2).** Higher local cohomology with support in `V(I)` of torsion
vanishes: `H^p_Z(M[I^∞]) = 0` for `p > 0`. -/
-- `Stacks.Duality.isZero_supportLocalCohomology_primaryComponent` in
-- `StacksFrontier/RingTheory/Dualizing/TorsionQuotient.lean` is an alias of this theorem. Six of
-- the tag's eight registrations live in that file, and the other two are this theorem and
-- `supportLocalCohomology_quotient_zero` below; the conjunction of all eight is
-- `Stacks.Duality.localCohomology_divide_by_torsion`, also in that file.
@[stacks 0AW0 "part (2), higher cohomology of the torsion submodule"]
theorem supportLocalCohomology_torsion_higher
    (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A)
    (p : ℤ) (hp : 0 < p) :
    IsZero ((supportLocalCohomology.{u, v} A I hI p).obj
      (ModuleCat.of A (Ideal.primaryComponent M I))) :=
  supportLocalCohomology_isZero_of_isIPowerTorsion.{u, v} A I hI _
    ((Dualizing.powerTorsionFunctor.{u, v} A I).obj M).property p hp.ne'

/-! ### Degree zero is the torsion submodule -/

/-- Every element of `H^0_Z(M)` is sent by the canonical map to `M` to an element killed by a
power of `I`, because `H^0_Z(M)` is the degree-zero cohomology of an object of
`D_{I^∞-torsion}(A)`. -/
private theorem exists_pow_smul_supportLocalCohomologyToModule_eq_zero
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A)
    (x : (supportLocalCohomology.{u, v} A I hI 0).obj M) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, a • (supportLocalCohomologyToModule.{u, v} A I hI M).hom x = 0 := by
  obtain ⟨n, -, hn⟩ := (((Dualizing.localCohomologyFunctor A I hI).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)).property 0) x
  exact ⟨n, fun a ha =>
    (map_smul (supportLocalCohomologyToModule.{u, v} A I hI M).hom a x).symm.trans
      ((congrArg _ (hn a ha)).trans (map_zero _))⟩

/-- The canonical map `H^0_Z(M) ⟶ M` lands in the `I`-power-torsion submodule, because
`H^0_Z(M)` is the degree-zero cohomology of an object of `D_{I^∞-torsion}(A)`. -/
theorem supportLocalCohomologyToModule_mem_primaryComponent
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A)
    (x : (supportLocalCohomology.{u, v} A I hI 0).obj M) :
    (supportLocalCohomologyToModule.{u, v} A I hI M).hom x ∈
      Ideal.primaryComponent M I := by
  obtain ⟨n, hn⟩ := exists_pow_smul_supportLocalCohomologyToModule_eq_zero A I hI M x
  rw [Ideal.primaryComponent_mem]
  exact ⟨n, Submodule.mem_torsionBySet_iff _ _ |>.2 fun a => hn a a.2⟩

/-- The canonical map `H^0_Z(M) ⟶ M[I^∞]`, the corestriction of the map to `M` along the
inclusion of the torsion submodule. -/
noncomputable def supportLocalCohomologyToTorsion
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A) :
    (supportLocalCohomology.{u, v} A I hI 0).obj M ⟶
      ModuleCat.of A (Ideal.primaryComponent M I) :=
  ModuleCat.ofHom
    (LinearMap.codRestrict _ (supportLocalCohomologyToModule.{u, v} A I hI M).hom
      (supportLocalCohomologyToModule_mem_primaryComponent.{u, v} A I hI M))

/-- The map `H^0_Z(M) ⟶ M[I^∞]` followed by the inclusion `M[I^∞] ⟶ M` is the canonical map
`H^0_Z(M) ⟶ M`. -/
@[simp] theorem supportLocalCohomologyToTorsion_comp_subtype
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A) :
    supportLocalCohomologyToTorsion.{u, v} A I hI M ≫
        ModuleCat.ofHom (Submodule.subtype (Ideal.primaryComponent M I)) =
      supportLocalCohomologyToModule.{u, v} A I hI M := rfl

/-- Zeroth local cohomology supported on `V(I)` is the same torsion submodule, including
its canonical inclusion into the original module. -/
-- No `@[stacks 0AW0]` attribute here: this is one half of the source's `H^0_I(M) = H^0_Z(M)`,
-- and the equality itself is
-- `Stacks.Duality.idealLocalCohomology_zero_iso_supportLocalCohomology_zero` in
-- `StacksFrontier/RingTheory/Dualizing/TorsionQuotient.lean`, which carries the attribute.
theorem supportLocalCohomology_zero_iso_torsion
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) :
    ∃ e : (supportLocalCohomology.{u, v} A I hI 0).obj M ≅
        ModuleCat.of A (Ideal.primaryComponent M I),
      e.hom ≫ ModuleCat.ofHom (Submodule.subtype (Ideal.primaryComponent M I)) =
        supportLocalCohomologyToModule.{u, v} A I hI M := by
  set N : ModuleCat.{max u v} A := ModuleCat.of A (Ideal.primaryComponent M I) with hN
  set incl : N ⟶ M := ModuleCat.ofHom (Submodule.subtype (Ideal.primaryComponent M I))
    with hincl
  have hinj : Function.Injective
      (supportLocalCohomologyToModule.{u, v} A I hI M).hom :=
    Stacks.LocalCohomology.localCohomologyZeroToModule_injective A I hI M
  -- the torsion submodule, placed in degree zero, lies in `D_{I^∞-torsion}(A)`
  have hprop : Dualizing.derivedPowerTorsionProperty A I hI
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) :=
    Dualizing.PowerTorsionBaseChange.derivedPowerTorsionProperty_singleFunctor I hI N
      ((Dualizing.powerTorsionFunctor.{u, v} A I).obj M).property
  -- so the inclusion `N ⟶ M` lifts through the counit
  obtain ⟨g, hg⟩ := (Stacks.LocalCohomology.bijective_comp_localCohomologyCounit I hI
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N)
    hprop).surjective ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map incl)
  dsimp only at hg
  set ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} A) 0
    with hε
  have hnat : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map incl) ≫
          ε.hom.app M = ε.hom.app N ≫ incl := ε.hom.naturality incl
  have step := ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map_comp g
      ((Dualizing.localCohomologyAdjunction A I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M))).symm.trans
    (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map hg)
  -- the lift is compatible with the canonical maps down to `M`
  have hαcompat :
      (((ε.app N)).inv ≫ (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map g) ≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
            ((Dualizing.localCohomologyAdjunction A I hI).counit.app
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) ≫
          ε.hom.app M) = incl :=
    calc (((ε.app N)).inv ≫ (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map g) ≫
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
              ((Dualizing.localCohomologyAdjunction A I hI).counit.app
                ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) ≫
            ε.hom.app M)
        = (ε.app N).inv ≫
            (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map g ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
                ((Dualizing.localCohomologyAdjunction A I hI).counit.app
                  ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M))) ≫
              ε.hom.app M) := by simp only [Category.assoc]
      _ = (ε.app N).inv ≫
            ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map incl) ≫
              ε.hom.app M) :=
          congrArg (fun t => (ε.app N).inv ≫ (t ≫ ε.hom.app M)) step
      _ = (ε.app N).inv ≫ (ε.hom.app N ≫ incl) := congrArg (fun t => (ε.app N).inv ≫ t) hnat
      _ = incl := by rw [← Category.assoc, Iso.app_inv, Iso.inv_hom_id_app, Category.id_comp]
  -- the lift, read as a map of modules
  have hα : ∃ α : N ⟶ (supportLocalCohomology.{u, v} A I hI 0).obj M,
      α ≫ supportLocalCohomologyToModule.{u, v} A I hI M = incl :=
    ⟨(ε.app N).inv ≫ (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map g,
      hαcompat⟩
  obtain ⟨α, hαc⟩ := hα
  have hcomp : ∀ z, incl.hom ((supportLocalCohomologyToTorsion.{u, v} A I hI M).hom z)
      = (supportLocalCohomologyToModule.{u, v} A I hI M).hom z := by
    intro z
    rw [hincl]
    rfl
  refine ⟨⟨supportLocalCohomologyToTorsion.{u, v} A I hI M, α, ?_, ?_⟩, rfl⟩
  · refine ModuleCat.hom_ext (LinearMap.ext fun x => hinj ?_)
    have h1 := congrArg (fun k : N ⟶ M => k.hom
      ((supportLocalCohomologyToTorsion.{u, v} A I hI M).hom x)) hαc
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
    exact h1.trans (hcomp x)
  · refine ModuleCat.hom_ext (LinearMap.ext fun y => Subtype.ext ?_)
    change (supportLocalCohomologyToModule.{u, v} A I hI M).hom (α.hom y) = (y : M)
    have h1 := congrArg (fun k : N ⟶ M => k.hom y) hαc
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
    rw [h1, hincl]
    rfl

/-! ### Degree-zero vanishing on the quotient -/

/-- **In a module with no `I`-torsion there is no `I`-power torsion either.** If no nonzero
element of `N` is killed by all of `I`, then an element killed by `I^n` is zero. -/
theorem eq_zero_of_pow_smul_eq_zero {A : Type u} [CommRing A]
    (I : Ideal A) (N : Type*) [AddCommGroup N] [Module A N]
    (hN : Submodule.torsionBySet A N (I : Set A) = ⊥) :
    ∀ (n : ℕ) (y : N), (∀ a ∈ I ^ n, a • y = 0) → y = 0 := by
  intro n
  induction n with
  | zero => intro y hy; simpa using hy 1 (by simp)
  | succ k ih =>
      intro y hy
      have hyI : ∀ b ∈ I, b • y = 0 := by
        intro b hb
        refine ih (b • y) ?_
        intro a ha
        rw [smul_smul]
        exact hy (a * b) (by rw [pow_succ]; exact Ideal.mul_mem_mul ha hb)
      have hmem : y ∈ Submodule.torsionBySet A N (I : Set A) := by
        rw [Submodule.mem_torsionBySet_iff]
        intro a
        exact hyI a.1 a.2
      rw [hN] at hmem
      simpa using hmem

/-- **Stacks 0AW0, part (2).** Quotienting by `I`-power torsion kills zeroth local cohomology
with support in `V(I)`: `H^0_Z(M/M[I^∞]) = 0`. -/
@[stacks 0AW0 "part (2), degree zero"]
theorem supportLocalCohomology_quotient_zero
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) :
    IsZero ((supportLocalCohomology.{u, v} A I hI 0).obj
      (ModuleCat.of A (M ⧸ Ideal.primaryComponent M I))) := by
  set M' : ModuleCat.{max u v} A := ModuleCat.of A (M ⧸ Ideal.primaryComponent M I) with hM'
  have hfree : Submodule.torsionBySet A (M ⧸ Ideal.primaryComponent M I) (I : Set A) = ⊥ :=
    torsionBySet_quotient_primaryComponent_eq_bot I hI _
  have hinj : Function.Injective
      (supportLocalCohomologyToModule.{u, v} A I hI M').hom :=
    Stacks.LocalCohomology.localCohomologyZeroToModule_injective A I hI M'
  rw [ModuleCat.isZero_iff_subsingleton, subsingleton_iff_forall_eq 0]
  intro x
  obtain ⟨n, hn⟩ := exists_pow_smul_supportLocalCohomologyToModule_eq_zero A I hI M' x
  refine hinj ?_
  rw [map_zero]
  exact eq_zero_of_pow_smul_eq_zero I (M ⧸ Ideal.primaryComponent M I) hfree n _ hn

end Stacks.Duality

end

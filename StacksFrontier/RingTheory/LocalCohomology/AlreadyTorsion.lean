module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.Shrink
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.SmallLocalization
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange.DerivedLoc
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.FiniteCohomologicalDimension
public import StacksFrontier.RingTheory.LocalCohomology.FreeUniverse.Augmentation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationReduction

/-!
# Local cohomology of a module that is already torsion

Let `I` and `J` be finitely generated ideals of a commutative ring `A` and let `M` be an
`I`-power-torsion `A`-module. Then imposing support in `V(I)` on top of support in `V(J)` changes
nothing: the canonical comparison
`RΓ_{V(I) ∩ V(J)}(M) ⟶ RΓ_{V(J)}(M)` is an isomorphism in `D(A)`, hence an isomorphism on every
cohomology module. This is Stacks 0DWS.

The reason is that `RΓ_{V(J)}(M)` is itself `I`-power torsion, so it lies in the subcategory onto
which `RΓ_{V(I) ∩ V(J)}` coreflects and the two coreflections of `M` agree. That is the content
proved here, and it is proved from the *construction* of local cohomology rather than from its
universal property: `RΓ_{V(J)}` is built by iterating the fibre of the localization unit at the
generators of `J`, and localizing away from a generator of `I` kills `M`, hence kills every stage
of that tower.

## Main results

* `Stacks.LocalCohomology.derivedPowerTorsionProperty_localCohomologyFunctor_of_isIPowerTorsion`
  — the local cohomology of an `I`-power-torsion module with support in any finitely generated
  ideal is again `I`-power torsion.
* `Stacks.LocalCohomology.isIso_localCohomologyComparison_of_isIPowerTorsion` — Stacks 0DWS in
  `D(A)`.
* `Stacks.LocalCohomology.isIso_homology_localCohomologyComparison_of_isIPowerTorsion` — Stacks
  0DWS degreewise.

## Implementation notes

The ring universe and the module universe are independent, so the localization functors used here
must preserve the module universe. The localization `M[S⁻¹]` of a module in `Type v` at a monoid
in `Type u` lives in `Type (max u v)`, and is brought back to `Type v` by `Shrink`. This is the
same construction that `Dualizing.localCohomologyRightAdjoint` is built from, and it is reused
here, together with the power-torsion criterion
`Dualizing.derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory`.

The strengthened coreflection statement `exists_coreflection_preserving` adds to
`Stacks.LocalCohomology.exists_coreflection_transport` the one clause the universal property does
not give: a localization that kills the input kills the coreflection. Everything else is formal.

## References

* [Stacks Project, Tag 0DWS](https://stacks.math.columbia.edu/tag/0DWS)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

open Dualizing.Coreflection (derivedUnit derivedUnit_obj_isIso derivedUnit_map_isIso)

/-! ### Universe-preserving localization of modules

The localization functors are `Dualizing.smallLocalization`, `Dualizing.smallLocalizationFunctor`
and its unit `Dualizing.smallLocalizationUnit`, all of
`StacksFrontier/RingTheory/Dualizing/TorsionComplete/SmallLocalization.lean`, which also carries
the exactness and smallness instances they need. -/

/-! ### A strengthened coreflection -/

section Coreflection

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The coreflection along a finite family of idempotent localizations, with its vanishing
clause.** This is `Stacks.LocalCohomology.exists_coreflection_transport` for the identity functor,
together with one extra conclusion: any member of the family that kills the input object also
kills the coreflection. The coreflection is built by iterating fibres of the units, and the
third object of each fibre triangle is in the image of a localization, so the extra conclusion
propagates along the tower. -/
private lemma exists_coreflection_preserving
    {ι : Type*} (F : ι → C ⥤ C) [∀ i, (F i).Additive] [∀ i, (F i).CommShift ℤ]
    [∀ i, (F i).IsTriangulated]
    (η : ∀ i, 𝟭 C ⟶ F i) (hη : ∀ i X, IsIso ((η i).app ((F i).obj X)))
    (hFη : ∀ i X, IsIso ((F i).map ((η i).app X)))
    (hpres : ∀ i j X, IsZero ((F j).obj X) → IsZero ((F j).obj ((F i).obj X)))
    (s : Finset ι) (X : C) :
    ∃ (Y : C) (c : Y ⟶ X),
      (∀ i ∈ s, IsZero ((F i).obj Y)) ∧
      (∀ W, (∀ i ∈ s, IsZero ((F i).obj W)) →
        Function.Bijective (fun g : W ⟶ Y => g ≫ c)) ∧
      (∀ j : ι, IsZero ((F j).obj X) → IsZero ((F j).obj Y)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨X, 𝟙 X, by simp, ?_, fun _ hj => hj⟩
      intro W _
      exact ⟨fun _ _ h => by simpa only [Category.comp_id] using h,
        fun g => ⟨g, Category.comp_id g⟩⟩
  | @insert i s hi ih =>
      obtain ⟨U, b, hU, hb, hkeep⟩ := ih
      obtain ⟨T, hT, h₂, h₃, hFT⟩ := exists_fiber_triangle (F i) (η i) (hFη i) U
      let e : T.obj₂ ≅ U := eqToIso h₂
      have hfib : ∀ j : ι, IsZero ((F j).obj U) → IsZero ((F j).obj T.obj₁) := fun j hj =>
        Triangle.isZero₁_of_isZero₂₃ _ ((F j).map_distinguished _ hT)
          (hj.of_iso ((F j).mapIso e)) ((hpres i j U hj).of_iso ((F j).mapIso (eqToIso h₃)))
      refine ⟨T.obj₁, T.mor₁ ≫ e.hom ≫ b, ?_, ?_, fun j hj => hfib j (hkeep j hj)⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hFT
        · exact hfib j (hU j hj)
      · intro W hW
        have k₁ := bijective_of_fiber (F i) (η i) (hη i) T hT U (eqToIso h₃) W
          (hW i (Finset.mem_insert_self _ _))
        have k₂ : Function.Bijective (fun g : W ⟶ T.obj₂ => g ≫ e.hom) :=
          ⟨fun _ _ h => (cancel_mono e.hom).1 h, fun g => ⟨g ≫ e.inv, by simp⟩⟩
        have k₃ := hb W (fun j hj => hW j (Finset.mem_insert_of_mem hj))
        simpa only [Function.comp_def, Category.assoc] using k₃.comp (k₂.comp k₁)

end Coreflection

/-! ### Local cohomology of a torsion module -/

section Main

variable (A : Type u) [CommRing A]

/-- A module placed in degree zero has `I`-power-torsion cohomology as soon as it is itself
`I`-power torsion. -/
private lemma derivedPowerTorsion_singleFunctor
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{v} A) (hM : IsIPowerTorsion A M I) :
    Dualizing.derivedPowerTorsionProperty A I hI
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) := by
  intro j
  rcases eq_or_ne j 0 with rfl | hj
  · exact Dualizing.PowerTorsionBaseChange.isIPowerTorsion_of_moduleIso _ _
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app M) hM
  · refine Dualizing.PowerTorsionBaseChange.isIPowerTorsion_of_isZero I _ (IsZero.of_iso ?_
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) j).app
        ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).obj M)))
    exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M j hj

/-- **The local cohomology of a torsion module stays torsion.** If `M` is `I`-power torsion and
`J` is any finitely generated ideal, then `RΓ_{V(J)}(M)` has `I`-power-torsion cohomology.

This is read off the construction of `RΓ_{V(J)}` as the iterated fibre of the localization units
at a generating set of `J`: localizing away from a generator of `I` kills `M`, hence kills every
stage of that tower, and the resulting object is identified with `RΓ_{V(J)}(M)` by uniqueness of
the coreflection. -/
theorem derivedPowerTorsionProperty_localCohomologyFunctor_of_isIPowerTorsion
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{v} A)
    (hM : IsIPowerTorsion A M I) :
    Dualizing.derivedPowerTorsionProperty A I hI
      ((Dualizing.derivedPowerTorsionProperty A J hJ).ι.obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M))) := by
  classical
  obtain ⟨sI, hsI⟩ := id hI
  obtain ⟨sJ, hsJ⟩ := id hJ
  set M0 := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  set F : A → DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
    fun f => (Dualizing.smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory
  set η : ∀ f, 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F f := fun f =>
    derivedUnit (Dualizing.smallLocalizationFunctor (Submonoid.powers f))
      (Dualizing.smallLocalizationUnit (Submonoid.powers f))
  have hη (f : A) (X : DerivedCategory (ModuleCat.{v} A)) : IsIso ((η f).app ((F f).obj X)) :=
    derivedUnit_obj_isIso _ _
      (Dualizing.isIso_smallLocalizationUnit_app_obj (Submonoid.powers f)) X
  have hFη (f : A) (X : DerivedCategory (ModuleCat.{v} A)) : IsIso ((F f).map ((η f).app X)) :=
    derivedUnit_map_isIso _ _
      (Dualizing.isIso_smallLocalizationFunctor_map_smallLocalizationUnit_app
        (Submonoid.powers f)) X
  have hpres (f g : A) (X : DerivedCategory (ModuleCat.{v} A))
      (h : IsZero ((F g).obj X)) : IsZero ((F g).obj ((F f).obj X)) :=
    Dualizing.isZero_mapDerivedCategory_smallLocalization_comp
      (Submonoid.powers g) (Submonoid.powers f) X h
  obtain ⟨Y, c, hYvan, hYuniv, hYkeep⟩ :=
    exists_coreflection_preserving F η hη hFη hpres sJ M0
  have hiffI := Dualizing.derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory I hI sI hsI
  have hiffJ := Dualizing.derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory J hJ sJ hsJ
  -- `Y` is a coreflection of `M0` into the `J`-power-torsion objects
  have hYJ : Dualizing.derivedPowerTorsionProperty A J hJ Y := (hiffJ Y).mpr hYvan
  -- and it is `I`-power torsion, because `M0` is
  have hYI : Dualizing.derivedPowerTorsionProperty A I hI Y := (hiffI Y).mpr fun f hf =>
    hYkeep f (((hiffI M0).mp (derivedPowerTorsion_singleFunctor A I hI M hM)) f hf)
  -- identify `Y` with `RΓ_{V(J)}(M)`
  obtain ⟨e⟩ := nonempty_iso_of_coreflection
    (Dualizing.derivedPowerTorsionProperty A J hJ) hYJ
    ((Dualizing.localCohomologyFunctor A J hJ).obj M0).property c
    ((Dualizing.localCohomologyAdjunction A J hJ).counit.app M0)
    (fun W hW => hYuniv W ((hiffJ W).mp hW))
    (fun W hW => bijective_comp_localCohomologyCounitShrink J hJ M0 W hW)
  intro i
  exact Dualizing.PowerTorsionBaseChange.isIPowerTorsion_of_moduleIso _ _
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).mapIso e) (hYI i)

/-- Power torsion for two finitely generated ideals is power torsion for their sum, because the
support is contained in `V(I) ∩ V(J) = V(I ⊔ J)`. -/
private lemma isIPowerTorsion_sup {N : Type*} [AddCommGroup N] [Module A N]
    {I J : Ideal A} (hI : I.FG) (hJ : J.FG)
    (h₁ : IsIPowerTorsion A N I) (h₂ : IsIPowerTorsion A N J) :
    IsIPowerTorsion A N (I ⊔ J) := by
  refine isIPowerTorsion_of_support_subset (Submodule.FG.sup hI hJ) ?_
  rw [PrimeSpectrum.zeroLocus_sup]
  exact Set.subset_inter (support_subset_zeroLocus_of_isIPowerTorsion h₁)
    (support_subset_zeroLocus_of_isIPowerTorsion h₂)

/-- Two morphisms over a common target, each universal for endomorphisms of its source, are
isomorphic by the unique morphisms over that target. -/
private lemma isIso_of_comp_right {D : Type*} [Category D] {X Y Z : D}
    (a : X ⟶ Z) (b : Y ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : f ≫ b = a) (hg : g ≫ a = b)
    (hX : Function.Injective (fun h : X ⟶ X => h ≫ a))
    (hY : Function.Injective (fun h : Y ⟶ Y => h ≫ b)) : IsIso f := by
  refine ⟨g, ?_, ?_⟩
  · exact hX (by simp only [Category.assoc, hg, hf, Category.id_comp])
  · exact hY (by simp only [Category.assoc, hf, hg, Category.id_comp])

/-- **Stacks 0DWS.** Let `I` and `J` be finitely generated ideals of a commutative ring `A` and
let `M` be an `I`-power-torsion `A`-module. Then the canonical comparison
`RΓ_{V(I) ∩ V(J)}(M) ⟶ RΓ_{V(J)}(M)` is an isomorphism of `D(A)`.

`RΓ_{V(J)}(M)` is `J`-power torsion by construction and `I`-power torsion by
`derivedPowerTorsionProperty_localCohomologyFunctor_of_isIPowerTorsion`, hence `I ⊔ J`-power
torsion; so the counit `RΓ_{V(J)}(M) ⟶ M` factors through the counit
`RΓ_{V(I) ∩ V(J)}(M) ⟶ M`, and the two factorizations are mutually inverse. -/
theorem isIso_localCohomologyComparison_of_isIPowerTorsion
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{v} A)
    (hM : IsIPowerTorsion A M I) :
    IsIso (Stacks.Algebraization.localCohomologyComparison A (I ⊔ J) J
      (Submodule.FG.sup hI hJ) hJ le_sup_right
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)) := by
  set hK := Submodule.FG.sup hI hJ
  set M0 := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  set YJ := (Dualizing.derivedPowerTorsionProperty A J hJ).ι.obj
    ((Dualizing.localCohomologyFunctor A J hJ).obj M0)
  have hinj (K : Ideal A) (hK : K.FG) :=
    (bijective_comp_localCohomologyCounitShrink K hK M0 _
      ((Dualizing.localCohomologyFunctor A K hK).obj M0).property).injective
  -- `RΓ_{V(J)}(M)` is `I ⊔ J`-power torsion
  have hYJ : Dualizing.derivedPowerTorsionProperty A (I ⊔ J) hK YJ := fun i =>
    isIPowerTorsion_sup A hI hJ
      (derivedPowerTorsionProperty_localCohomologyFunctor_of_isIPowerTorsion A I J hI hJ M hM i)
      (((Dualizing.localCohomologyFunctor A J hJ).obj M0).property i)
  -- hence the `J`-counit factors through the `I ⊔ J`-counit
  obtain ⟨g, hg⟩ := (bijective_comp_localCohomologyCounitShrink (I ⊔ J) hK M0 YJ hYJ).surjective
    ((Dualizing.localCohomologyAdjunction A J hJ).counit.app M0)
  exact isIso_of_comp_right
    ((Dualizing.localCohomologyAdjunction A (I ⊔ J) hK).counit.app M0)
    ((Dualizing.localCohomologyAdjunction A J hJ).counit.app M0) _ g
    (Stacks.Algebraization.localCohomologyComparison_comp_counit (I ⊔ J) J hK hJ le_sup_right
      M0) hg
    (hinj (I ⊔ J) hK) (hinj J hJ)

/-- **Stacks 0DWS.** For an `I`-power-torsion module `M`, the canonical map
`H^i_{V(I) ∩ V(J)}(M) ⟶ H^i_{V(J)}(M)` is an isomorphism in every degree. -/
@[stacks 0DWS]
theorem isIso_homology_localCohomologyComparison_of_isIPowerTorsion
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{v} A)
    (hM : IsIPowerTorsion A M I) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (Stacks.Algebraization.localCohomologyComparison A (I ⊔ J) J
        (Submodule.FG.sup hI hJ) hJ le_sup_right
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M))) := by
  have := isIso_localCohomologyComparison_of_isIPowerTorsion A I J hI hJ M hM
  infer_instance

end Main

end Stacks.LocalCohomology

end

module

public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.UniformProInverse
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDualProZero
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulTopQuotientTower
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismFromEventualInverses
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# The dual Koszul tower is pro-isomorphic to the quotient tower in `D(𝒪_Y)`

Let `Y` be a quasi-compact locally Noetherian scheme, let `f_1, …, f_r` be global sections of
`𝒪_Y` and let `ℱ` be a coherent `𝒪_Y`-module. The comparison of towers
`Stacks.Algebraization.koszulDualToTopQuotient` goes from the dual Koszul tower
`n ↦ K(𝒪_Y, f_1^{n+1}, …, f_r^{n+1}) ⊗ ℱ` to the quotient tower
`n ↦ ℱ / (f_1^{n+1}, …, f_r^{n+1})ℱ` placed in the top degree `r`. This file shows that **it is an
isomorphism of pro-objects of `D(𝒪_Y)`**.

[Stacks, Tag 0G3D] is what does the work: a morphism of towers of the derived category whose
cohomology lies in a bounded interval and which is a pro-isomorphism on every cohomology object is
a pro-isomorphism. Its hypothesis is checked degree by degree:

* in the top degree `r` the comparison is an isomorphism at **every** level, with no refinement of
  the index, by `Stacks.Algebraization.isIso_homologyMap_koszulTopSingleComparison`;
* below the top degree the cohomology of the Koszul side is **pro-zero**, which is the Artin–Rees
  input `Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_coherent`, and the
  cohomology of the single-complex side vanishes outright, so the zero map is a pro-inverse;
* above the top degree both sides vanish.

0G3D hands back a *per-level* existence statement, and `InverseSequence.ProIso` wants a single
index sequence with maps in both directions. The passage between the two is
`InverseSequence.ProIso.proIsoOfExistsProInverse`, which builds the index sequence by recursion —
the Artin–Rees bound being existential rather than explicit.

## Main results

* `Stacks.Algebraization.proIso_koszulDualTower_koszulTopQuotientSystem` — **the two towers are
  isomorphic as pro-objects of `D(𝒪_Y)`.**
* `Stacks.Algebraization.hasEventualInverses_koszulDualToTopQuotientDerived` — the same fact with
  the **transformation kept**: 0G3D's per-level pro-inverse of
  `Stacks.Algebraization.koszulDualToTopQuotientDerived` is
  `NoetherianAdicCompletion.HasEventualInverses` of it, and the pro-isomorphism is read off that.
* `Stacks.Algebraization.koszulTopQuotientToAdicQuotient` and
  `Stacks.Algebraization.hasEventualInverses_koszulTopQuotientToAdicQuotient` — the comparison of
  the two quotient towers as a genuine natural transformation with eventual inverses, in place of
  the interleaving of
  `Stacks.Algebraization.proIso_koszulTopQuotientSystem_adicQuotientSystem`.
* `Stacks.Algebraization.submoduleQuotientSystemHom` and
  `Stacks.Algebraization.hasEventualInverses_submoduleQuotientSystemHom` — those two statements
  for an arbitrary pair of interleaved antitone families of subsheaves of one sheaf of modules.

An `InverseSequence.ProIso` carries a zig-zag `X_{α m} ⟶ Y_m` at a reindexing and no component
`X_m ⟶ Y_m` at all, so it cannot be fed to
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses`, which is
what carries the *projections* of a derived-limit presentation along a comparison of towers. The
eventual-inverse forms above exist for that consumer; see
`Completion/KoszulAdicCompletionLimit.lean` for their composite.

## Implementation notes

Quasi-compactness of `Y` enters only through the Artin–Rees input, where the levels contributed by
the finitely many members of an affine cover are maximised; see
`Stacks.KoszulProZero.exists_koszulPowerComplexOnDown_homologyMap_eq_zero_of_coherent`.

The derived category is taken with the local instance of
`Completion/AdicQuotientDerivedLimit.lean`, which is `CategoryTheory.HasDerivedCategory.standard`
at `Y.Modules`; that is the instance the tag's part (4) is stated with.

The cohomology of an object of the derived category coming from a complex is the cohomology of
that complex, `DerivedCategory.homologyFunctorFactors`; the two bridge lemmas below move the
vanishing and the invertibility across that isomorphism, because 0G3D's hypothesis is phrased with
the derived-category functor while the Koszul inputs are phrased with
`HomologicalComplex.homologyMap`.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0G3D](https://stacks.math.columbia.edu/tag/0G3D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] modulesEnoughInjectives modulesHasDerivedCategory

/-! ### Reading cohomology in the derived category -/

section Bridge

variable {Y : Scheme.{u}} {K L : CochainComplex Y.Modules ℤ}

/-- A map of complexes which vanishes on cohomology in a degree induces the zero map on the
cohomology of the derived category in that degree. This is
`DerivedCategory.homologyFunctor_map_Q_map_eq_zero`, which holds in any abelian category with a
chosen derived category, read at the modules on a scheme. -/
theorem homologyFunctor_map_Q_map_eq_zero (φ : K ⟶ L) (i : ℤ)
    (h : (HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℤ) i).map φ = 0) :
    (DerivedCategory.homologyFunctor Y.Modules i).map (DerivedCategory.Q.map φ) = 0 :=
  DerivedCategory.homologyFunctor_map_Q_map_eq_zero φ i h

/-- A map of complexes which is invertible on cohomology in a degree induces an isomorphism on the
cohomology of the derived category in that degree. -/
theorem isIso_homologyFunctor_map_Q_map (φ : K ⟶ L) (i : ℤ)
    [IsIso ((HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℤ) i).map φ)] :
    IsIso ((DerivedCategory.homologyFunctor Y.Modules i).map (DerivedCategory.Q.map φ)) := by
  have hnat := (DerivedCategory.homologyFunctorFactors Y.Modules i).hom.naturality φ
  have hfac : (DerivedCategory.homologyFunctor Y.Modules i).map (DerivedCategory.Q.map φ) =
      ((DerivedCategory.homologyFunctorFactors Y.Modules i).hom.app K ≫
          (HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℤ) i).map φ) ≫
        ((DerivedCategory.homologyFunctorFactors Y.Modules i).app L).inv :=
    (Iso.eq_comp_inv ((DerivedCategory.homologyFunctorFactors Y.Modules i).app L)).2 hnat
  rw [hfac]
  infer_instance

/-- An object of the derived category coming from a complex with no cohomology in a degree has no
cohomology there. -/
theorem isZero_homologyFunctor_obj_Q_obj (i : ℤ)
    (h : IsZero ((HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℤ) i).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj (DerivedCategory.Q.obj K)) :=
  ((DerivedCategory.homologyFunctorFactors Y.Modules i).app K).isZero_iff.2 h

end Bridge

/-! ### Quotient towers of a sheaf of modules, as a transformation with eventual inverses -/

section QuotientTowers

variable {X : Scheme.{u}}

/-- **The levelwise comparison of two quotient towers of one sheaf of modules.** If `N n ≤ N' n`
at every level then the quotient maps `ℱ/N n ⟶ ℱ/N' n` form a genuine natural transformation of
towers. Both squares are composites of quotient maps of the same sheaf, so they agree by
`Stacks.Algebraization.quotientMapOfLE_comp`.

`Stacks.Algebraization.quotientInterleaving` produces instead a zig-zag at a reindexing, which
is what `InverseSequence.ProIso` records; a transformation is what
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses` needs, and
it carries the projections of a derived-limit presentation across. -/
def submoduleQuotientSystemHom (M : X.Modules) (N N' : ℕ → M.Submodule)
    (hN : ∀ m n : ℕ, n ≤ m → N m ≤ N n) (hN' : ∀ m n : ℕ, n ≤ m → N' m ≤ N' n)
    (h : ∀ n : ℕ, N n ≤ N' n) :
    submoduleQuotientSystem M N hN ⟶ submoduleQuotientSystem M N' hN' where
  app n := quotientMapOfLE (h n.unop)
  naturality _ _ g :=
    (quotientMapOfLE_comp (hN _ _ (leOfHom g.unop)) (h _)
        ((hN _ _ (leOfHom g.unop)).trans (h _))).trans
      (quotientMapOfLE_comp (h _) (hN' _ _ (leOfHom g.unop))
        ((hN _ _ (leOfHom g.unop)).trans (h _))).symm

/-- **The comparison of two quotient towers has eventual inverses as soon as the two families of
subsheaves interleave.** The inverse at level `n` is the quotient map `ℱ/N' m ⟶ ℱ/N n` provided
by the containment `N' m ≤ N n`, and both composition identities are instances of
`Stacks.Algebraization.quotientMapOfLE_comp` again.

This is the eventual-inverse form of the interleaving behind
`Stacks.Algebraization.proIso_globalSpanQuotientSystem_adicQuotientSystem`: it keeps the
transformation that an `InverseSequence.ProIso` discards. -/
theorem hasEventualInverses_submoduleQuotientSystemHom (M : X.Modules) (N N' : ℕ → M.Submodule)
    (hN : ∀ m n : ℕ, n ≤ m → N m ≤ N n) (hN' : ∀ m n : ℕ, n ≤ m → N' m ≤ N' n)
    (h : ∀ n : ℕ, N n ≤ N' n) (hinv : ∀ n : ℕ, ∃ m : ℕ, ∃ _ : n ≤ m, N' m ≤ N n) :
    NoetherianAdicCompletion.HasEventualInverses
      (submoduleQuotientSystemHom M N N' hN hN' h) := by
  intro n
  obtain ⟨m, hnm, hle⟩ := hinv n
  exact ⟨m, hnm, quotientMapOfLE hle,
    quotientMapOfLE_comp (h m) hle (hN m n hnm),
    quotientMapOfLE_comp hle (h n) (hN' m n hnm)⟩

/-- **The eventual inverses of the hom of a natural isomorphism of towers**: the inverse
component serves at the same level, both composites being the identity, which is the transition
map along `n ≤ n`. -/
theorem hasEventualInverses_hom_of_natIso {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G) :
    NoetherianAdicCompletion.HasEventualInverses e.hom :=
  fun n => ⟨n, le_rfl, e.inv.app (op n), by simp, by simp⟩

end QuotientTowers

section KoszulAdicQuotient

variable (Y : Scheme.{u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections
    ((Stacks.SheafOfModules.opensRingedSite Y.sheaf).O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : Y.Modules)

/-- **The comparison `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ ⟶ ℱ/ℐⁿℱ` of the two quotient towers**, as a
genuine natural transformation.

The containment `(f_1^{n+1}, …, f_r^{n+1})ℱ ⊆ ℐ^{n+1}ℱ ⊆ ℐⁿℱ` holds at every level because each
generator is a section of `ℐ`, so the quotient maps are defined levelwise and need no
reindexing. `Stacks.Algebraization.proIso_koszulTopQuotientSystem_adicQuotientSystem` records
the same comparison as an interleaving, which forgets the transformation.

Nothing Noetherian, coherent or compact is used: the containment holds on every affine open with
the same exponents. -/
def koszulTopQuotientToAdicQuotient (I : Y.IdealSheafData)
    (hgen : ∀ U : Y.affineOpens, I.ideal U =
      Ideal.span (Set.range fun i => globalRes U (koszulGlobalGenerator Y f i))) :
    koszulTopQuotientSystem Y f ℱ ⟶ adicQuotientSystem I ℱ :=
  submoduleQuotientSystemHom ℱ (fun n => globalSpanMultiple (koszulGlobalGenerator Y f) (n + 1) ℱ)
    (fun n => idealPowerMultiple I n ℱ)
    (fun _ _ h => globalSpanMultiple_antitone (koszulGlobalGenerator Y f) ℱ
      (Nat.add_le_add_right h 1))
    (fun _ _ h => idealPowerMultiple_antitone I ℱ h)
    (fun n => (globalSpanMultiple_le_idealPowerMultiple (koszulGlobalGenerator Y f) I
      (fun U i => (hgen U).symm ▸ Ideal.subset_span ⟨i, rfl⟩) (n + 1) ℱ).trans
      (idealPowerMultiple_antitone I ℱ (Nat.le_succ n)))

/-- **The comparison of the two quotient towers has eventual inverses.** At level `n` the
pigeonhole containment `ℐ^{r(n+1)+1}ℱ ⊆ (f_1^{n+1}, …, f_r^{n+1})ℱ` of
`Stacks.Algebraization.idealPowerMultiple_le_globalSpanMultiple` supplies the backward quotient
map, and both composites are transition maps of the two towers.

The level is explicit — `max n (r·(n+1)+1)` — and no hypothesis beyond the generation of `ℐ` by
`f_1, …, f_r` on every affine open enters. -/
theorem hasEventualInverses_koszulTopQuotientToAdicQuotient (I : Y.IdealSheafData)
    (hgen : ∀ U : Y.affineOpens, I.ideal U =
      Ideal.span (Set.range fun i => globalRes U (koszulGlobalGenerator Y f i))) :
    NoetherianAdicCompletion.HasEventualInverses
      (koszulTopQuotientToAdicQuotient Y f ℱ I hgen) :=
  hasEventualInverses_submoduleQuotientSystemHom ℱ _ _ _ _ _ fun n =>
    ⟨max n (r * (n + 1) + 1), le_max_left _ _,
      (idealPowerMultiple_antitone I ℱ (le_max_right n (r * (n + 1) + 1))).trans
        (idealPowerMultiple_le_globalSpanMultiple (koszulGlobalGenerator Y f) I hgen
          (n + 1) (r * (n + 1) + 1) le_rfl ℱ)⟩

end KoszulAdicQuotient

/-! ### The pro-isomorphism -/

section ProIso

open scoped IsMulCommutative


variable (Y : Scheme.{u}) [IsLocallyNoetherian Y] [CompactSpace Y] {r : ℕ}
  (f : Fin r → Presheaf.globalSections
    ((Stacks.SheafOfModules.opensRingedSite Y.sheaf).O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : Y.Modules) [ℱ.IsCoherent]

/-- The dual Koszul tower, read in the derived category. -/
def koszulDualDerivedTower : ℕᵒᵖ ⥤ DerivedCategory Y.Modules :=
  koszulDualTowerOn Y f ℱ ⋙ DerivedCategory.Q

/-- The quotient tower placed in the top degree, read in the derived category. -/
def koszulTopQuotientDerivedTower : ℕᵒᵖ ⥤ DerivedCategory Y.Modules :=
  (koszulTopQuotientSystem Y f ℱ ⋙
    HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) ((r : ℤ) - 1 + 1)) ⋙
      DerivedCategory.Q

/-- The comparison of the two towers, read in the derived category. -/
def koszulDualToTopQuotientDerived :
    koszulDualDerivedTower Y f ℱ ⟶ koszulTopQuotientDerivedTower Y f ℱ :=
  Functor.whiskerRight (koszulDualToTopQuotient Y f ℱ) DerivedCategory.Q

omit [IsLocallyNoetherian Y] [CompactSpace Y] [ℱ.IsCoherent] in
/-- At level `n`, the derived comparison is the image under `DerivedCategory.Q` of
`koszulTopSingleComparison`. -/
theorem koszulDualToTopQuotientDerived_app (n : ℕ) :
    (koszulDualToTopQuotientDerived Y f ℱ).app (op n) =
      DerivedCategory.Q.map (koszulTopSingleComparison Y f ℱ n) :=
  rfl

omit [IsLocallyNoetherian Y] [CompactSpace Y] [ℱ.IsCoherent] in
/-- The Koszul side has no cohomology outside the degrees `0, …, r`. -/
theorem isZero_homology_koszulDualDerivedTower (i : ℤ) (hi : i < 0 ∨ (r : ℤ) < i) (n : ℕᵒᵖ) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((koszulDualDerivedTower Y f ℱ).obj n)) := by
  refine isZero_homologyFunctor_obj_Q_obj i ?_
  rcases hi with hi | hi
  · exact RingedSite.isZero_homology_koszulPowerComplexOn_of_neg
      (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f n.unop ℱ hi
  · exact RingedSite.isZero_homology_koszulPowerComplexOn_of_gt
      (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f n.unop ℱ hi

omit [IsLocallyNoetherian Y] [CompactSpace Y] [ℱ.IsCoherent] in
/-- The single-complex side has no cohomology outside the top degree. -/
theorem isZero_homology_koszulTopQuotientDerivedTower (i : ℤ) (hi : i ≠ (r : ℤ) - 1 + 1)
    (n : ℕᵒᵖ) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((koszulTopQuotientDerivedTower Y f ℱ).obj n)) :=
  isZero_homologyFunctor_obj_Q_obj i
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) ((r : ℤ) - 1 + 1)
      ((koszulTopQuotientSystem Y f ℱ).obj n) i hi)

/-- **The comparison is a pro-isomorphism on cohomology in every degree**, which is the hypothesis
of [Stacks, Tag 0G3D]. In the top degree it is an isomorphism at every level; below it the Koszul
cohomology is pro-zero and the other side vanishes; above it both sides vanish. -/
theorem hasProInverse_homology_koszulDualToTopQuotientDerived (i : ℤ) (j : ℕᵒᵖ) :
    ∃ (k : ℕᵒᵖ) (g : k ⟶ j)
      (s : (DerivedCategory.homologyFunctor Y.Modules i).obj
          ((koszulTopQuotientDerivedTower Y f ℱ).obj k) ⟶
        (DerivedCategory.homologyFunctor Y.Modules i).obj
          ((koszulDualDerivedTower Y f ℱ).obj j)),
      (DerivedCategory.homologyFunctor Y.Modules i).map
            ((koszulDualToTopQuotientDerived Y f ℱ).app k) ≫ s =
          (DerivedCategory.homologyFunctor Y.Modules i).map
            ((koszulDualDerivedTower Y f ℱ).map g) ∧
        s ≫ (DerivedCategory.homologyFunctor Y.Modules i).map
              ((koszulDualToTopQuotientDerived Y f ℱ).app j) =
            (DerivedCategory.homologyFunctor Y.Modules i).map
              ((koszulTopQuotientDerivedTower Y f ℱ).map g) := by
  rcases lt_trichotomy i ((r : ℤ) - 1 + 1) with hi | hi | hi
  · -- below the top degree: the Koszul cohomology is pro-zero, the other side vanishes
    obtain ⟨m, hnm, hzero⟩ :=
      Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_coherent Y f ℱ
        j.unop i (by omega)
    refine ⟨op m, (homOfLE hnm).op, 0, ?_, ?_⟩
    · rw [comp_zero]
      exact (homologyFunctor_map_Q_map_eq_zero
        ((koszulDualTowerOn Y f ℱ).map (homOfLE hnm).op) i hzero).symm
    · rw [zero_comp]
      exact ((isZero_homology_koszulTopQuotientDerivedTower Y f ℱ i (by omega) (op m)).eq_of_src
        _ _).symm
  · -- the top degree: the comparison is an isomorphism at every level
    subst hi
    have : IsIso ((DerivedCategory.homologyFunctor Y.Modules ((r : ℤ) - 1 + 1)).map
        ((koszulDualToTopQuotientDerived Y f ℱ).app j)) := by
      have : IsIso ((HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℤ)
          ((r : ℤ) - 1 + 1)).map (koszulTopSingleComparison Y f ℱ j.unop)) :=
        isIso_homologyMap_koszulTopSingleComparison Y f ℱ j.unop
      rw [show j = op j.unop from rfl, koszulDualToTopQuotientDerived_app]
      exact isIso_homologyFunctor_map_Q_map (koszulTopSingleComparison Y f ℱ j.unop) _
    refine ⟨j, 𝟙 j, inv ((DerivedCategory.homologyFunctor Y.Modules ((r : ℤ) - 1 + 1)).map
      ((koszulDualToTopQuotientDerived Y f ℱ).app j)), ?_, ?_⟩
    · simp
    · simp
  · -- above the top degree: both sides vanish
    refine ⟨j, 𝟙 j, 0, ?_, ?_⟩ <;> simp only [comp_zero, zero_comp]
    · exact ((isZero_homology_koszulDualDerivedTower Y f ℱ i (Or.inr (by omega)) j).eq_of_src
        _ _).symm
    · exact ((isZero_homology_koszulTopQuotientDerivedTower Y f ℱ i (by omega) j).eq_of_src
        _ _).symm

/-- **The comparison of the dual Koszul tower with the quotient tower in the top degree has
eventual inverses.**

[Stacks, Tag 0G3D] turns the degreewise pro-invertibility into a per-level pro-inverse of the
comparison itself, and that per-level statement *is*
`NoetherianAdicCompletion.HasEventualInverses` of the genuine natural transformation
`Stacks.Algebraization.koszulDualToTopQuotientDerived`.

This is the form that keeps the transformation. `InverseSequence.ProIso` records only a zig-zag
at a reindexing, so it cannot be fed to
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses`, which is
what carries the projections of a derived-limit presentation along a comparison of towers. -/
theorem hasEventualInverses_koszulDualToTopQuotientDerived :
    NoetherianAdicCompletion.HasEventualInverses (koszulDualToTopQuotientDerived Y f ℱ) := by
  intro n
  obtain ⟨k, g, s, hs₁, hs₂⟩ :=
    DerivedCategory.exists_proInverse_of_proInverse_homology
      (koszulDualToTopQuotientDerived Y f ℱ) 0 (r : ℤ)
      (fun i hi => isZero_homology_koszulDualDerivedTower Y f ℱ i (by omega))
      (fun i hi => isZero_homology_koszulTopQuotientDerivedTower Y f ℱ i (by omega))
      (hasProInverse_homology_koszulDualToTopQuotientDerived Y f ℱ) (op n)
  have h : n ≤ k.unop := leOfHom g.unop
  have hg : g = (homOfLE h).op := Subsingleton.elim _ _
  exact ⟨k.unop, h, s, by rw [← hg]; exact hs₁, by rw [← hg]; exact hs₂⟩

/-- **The dual Koszul tower and the quotient tower placed in the top degree are isomorphic as
pro-objects of `D(𝒪_Y)`.**

[Stacks, Tag 0G3D] turns the degreewise pro-invertibility into a per-level pro-inverse of the
comparison itself, and `InverseSequence.ProIso.proIsoOfExistsProInverse` builds from that the
index sequence an `InverseSequence.ProIso` asks for. The per-level statement is
`Stacks.Algebraization.hasEventualInverses_koszulDualToTopQuotientDerived`. -/
def proIso_koszulDualTower_koszulTopQuotientSystem :
    InverseSequence.ProIso (koszulDualDerivedTower Y f ℱ)
      (koszulTopQuotientDerivedTower Y f ℱ) :=
  InverseSequence.ProIso.proIsoOfExistsProInverse
    (koszulDualToTopQuotientDerived Y f ℱ)
    (hasEventualInverses_koszulDualToTopQuotientDerived Y f ℱ)

/-! ### The quotient tower by the powers of the generators and the adic quotient tower -/

/-- The index sequence `k ↦ (r + 2)^{k+1}` used to interleave the quotient tower by the powers of
the generators with the adic quotient tower. One step multiplies the exponent by `r + 2`, which
outruns the pigeonhole bound `r·n + 1`; the shift by one in the exponent absorbs the shift by one
that the Koszul indexing carries. -/
theorem strictMono_koszulAdicIdx : StrictMono (fun k : ℕ => (r + 2) ^ (k + 1)) :=
  strictMono_nat_of_lt_succ fun k => Nat.pow_lt_pow_succ (by omega)

/-- One step of the index sequence outruns the pigeonhole bound at the shifted exponent. -/
theorem koszulAdicIdx_bound (k : ℕ) :
    r * ((r + 2) ^ (2 * k + 1) + 1) + 1 ≤ (r + 2) ^ (2 * k + 2) := by
  have h1 : r + 2 ≤ (r + 2) ^ (2 * k + 1) := by
    calc r + 2 = (r + 2) ^ 1 := (pow_one _).symm
      _ ≤ (r + 2) ^ (2 * k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (r + 2) ^ (2 * k + 2) = (r + 2) ^ (2 * k + 1) * (r + 2) := by rw [pow_succ]
  rw [h2]
  nlinarith [h1]

/-- **The quotient tower by the powers of the generators is pro-isomorphic to the adic quotient
tower.**

This is `Stacks.Algebraization.proIso_globalSpanQuotientSystem_adicQuotientSystem` at the shifted
indexing that the Koszul levels carry: level `n` of the Koszul tower quotients by the `(n+1)`-st
powers of the generators. Nothing Noetherian, coherent or compact is used — both containments hold
on every affine open with the same exponents. -/
def proIso_koszulTopQuotientSystem_adicQuotientSystem (I : Y.IdealSheafData)
    (hgen : ∀ U : Y.affineOpens, I.ideal U =
      Ideal.span (Set.range fun i => globalRes U (koszulGlobalGenerator Y f i))) :
    InverseSequence.ProIso (koszulTopQuotientSystem Y f ℱ) (adicQuotientSystem I ℱ) := by
  have hmem : ∀ (U : Y.affineOpens) (i : Fin r),
      globalRes U (koszulGlobalGenerator Y f i) ∈ I.ideal U := by
    intro U i
    rw [hgen U]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine InverseSequence.ProIso.Interleaving.proIso ?_
  rw [adicQuotientSystem_eq_submoduleQuotientSystem]
  refine quotientInterleaving ℱ
    (fun n => globalSpanMultiple (koszulGlobalGenerator Y f) (n + 1) ℱ)
    (fun n => idealPowerMultiple I n ℱ)
    (fun _ _ h => globalSpanMultiple_antitone (koszulGlobalGenerator Y f) ℱ
      (Nat.add_le_add_right h 1))
    (fun _ _ h => idealPowerMultiple_antitone I ℱ h)
    (fun k => (r + 2) ^ (k + 1)) strictMono_koszulAdicIdx (fun i => ?_) (fun i => ?_)
  · refine le_trans (globalSpanMultiple_le_idealPowerMultiple (koszulGlobalGenerator Y f) I hmem
      ((r + 2) ^ (2 * i + 2 + 1) + 1) ℱ) ?_
    exact idealPowerMultiple_antitone I ℱ
      (le_trans (le_of_lt (strictMono_koszulAdicIdx (show 2 * i + 1 < 2 * i + 2 by omega)))
        (Nat.le_succ _))
  · refine le_trans ?_ (idealPowerMultiple_le_globalSpanMultiple (koszulGlobalGenerator Y f) I
      hgen ((r + 2) ^ (2 * i + 1) + 1) (r * ((r + 2) ^ (2 * i + 1) + 1) + 1) le_rfl ℱ)
    exact idealPowerMultiple_antitone I ℱ (koszulAdicIdx_bound i)

end ProIso

end Stacks.Algebraization

end

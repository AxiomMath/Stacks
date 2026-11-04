module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapOpenClosedGlue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaOpenClosedDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapOpenClosedConstantComplex

/-!
# The canonical Frobenius on `RΓ(Y_k̄, N_Y)` is the pullback by `π̄`

Let `Y` be a scheme over a finite field `k` with `q = p ^ f` elements, `k̄` an extension field,
`π̄ = π_Y × id` the base change of the geometric Frobenius and `f : Y_k̄ ⟶ Spec k̄` the structure
morphism. For a constant complex `N_Y`, the cohomology `RΓ(Y_k̄, N_Y|_{Y_k̄})` carries two
endomorphisms.

* The canonical `π_Y^*` of the trace formula
  (`Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo`) is built from the Frobenius descent
  isomorphism of [Stacks, Tag 03SR].
* The pullback `π̄^*` (`Stacks.EtaleCohomology.selfMapCohomologyEndo`) acts on
  `RΓ(Spec k̄, Rf_*(f^{-1} N_{k̄}))`. Its trace Weil's formula computes.

They agree under `N_Y|_{Y_k̄} ≅ N_{Y_k̄} ≅ f^{-1} N_{k̄}`, so they have the same trace. Both twists
`N|_{Y_k̄} ⟶ π̄_* N|_{Y_k̄}` are maps out of a constant sheaf, and both send the constant section
to a restriction of the constant section.

For a proper `Y`, compactified by itself, the canonical `π_Y^*` on `RΓ_c(Y_k̄, N_Y)` is the first
endomorphism. So the Lefschetz number of the trace formula with constant coefficients is the
trace of the pullback `π̄^*` on `RΓ(Y_k̄, N)`.

## Main results

* `frobeniusBaseChangeTwist_constant_comp_map_eq`: the two twists agree.
* `perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_constant_eq_selfMap`: the canonical
  Frobenius and the pullback by `π̄` have the same trace on `RΓ(Y_k̄, N_Y|_{Y_k̄})`.
* `canonicalCompactSupportLefschetzNumber_ofProper_constant_eq_selfMap`: for `Y` proper, the
  Lefschetz number with constant coefficients is the trace of the pullback by `π̄`.

## References

* [Stacks Project, Tag 03UJ](https://stacks.math.columbia.edu/tag/03UJ)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03SR](https://stacks.math.columbia.edu/tag/03SR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Sheaf

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ) {k : Type u} [Field k]
  [Fintype k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The Frobenius base change twist of a constant sheaf is the self-map twist of `π̄`**, once
both are transported to the constant sheaf `M_{Y_k̄}`. -/
theorem transportedConstantTwist_frobeniusBaseChangeTwist :
    transportedConstantTwist.{u, r} Λ M (fieldBaseChangeProj Y kbar)
        (geometricFrobeniusBaseChange Y kbar p q hcard)
        ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app
          (etaleModuleConstantSheaf Λ M Y.left)) =
      transportedConstantTwist.{u, r} Λ M (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChange Y kbar p q hcard)
        ((selfMapTwist.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange Y kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).app
            (etaleModuleConstantSheaf Λ M (Spec (.of kbar)))) := by
  obtain ⟨ρ₁, h₁⟩ := exists_pulledBackConstantSection_comp_frobeniusBaseChangeTwist Λ M Y kbar p q
    hcard
  obtain ⟨ρ₂, h₂⟩ := exists_pulledBackConstantSection_comp_selfMapTwist Λ M
    (pullback.snd Y.hom (specAlgebraMap k kbar)) (geometricFrobeniusBaseChange Y kbar p q hcard)
    (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)
  apply constantSheaf_hom_ext
  rw [constantSheafSection_comp_transportedConstantTwist Λ M _ _ _ ρ₁ h₁,
    constantSheafSection_comp_transportedConstantTwist Λ M _ _ _ ρ₂ h₂]

/-- **The Frobenius base change twist of a constant sheaf is the self-map twist of `π̄`**, through
the identification `M_Y|_{Y_k̄} ≅ f^{-1} M_{k̄}`. -/
theorem frobeniusBaseChangeTwist_constant_comp_map_eq :
    (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app (etaleModuleConstantSheaf Λ M Y.left) ≫
      (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
        (fieldBaseChangeConstantIso Λ M Y kbar).hom =
    (fieldBaseChangeConstantIso Λ M Y kbar).hom ≫
      (selfMapTwist.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChange Y kbar p q hcard)
        (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).app
          (etaleModuleConstantSheaf Λ M (Spec (.of kbar))) := by
  have T := transportedConstantTwist_frobeniusBaseChangeTwist Λ M Y kbar p q hcard
  simp only [transportedConstantTwist] at T
  rw [← cancel_epi
    ((etaleModuleInverseImageConstantIso.{u, r} Λ (fieldBaseChangeProj Y kbar)).app M).inv]
  simp only [fieldBaseChangeConstantIso, Iso.trans_hom, Iso.symm_hom, Functor.map_comp]
  calc _ = (((etaleModuleInverseImageConstantIso.{u, r} Λ (fieldBaseChangeProj Y kbar)).app M).inv ≫
        (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app
          (etaleModuleConstantSheaf Λ M Y.left) ≫
        (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          ((etaleModuleInverseImageConstantIso.{u, r} Λ (fieldBaseChangeProj Y kbar)).app M).hom) ≫
        (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          ((etaleModuleInverseImageConstantIso.{u, r} Λ
            (pullback.snd Y.hom (specAlgebraMap k kbar))).app M).inv := by
        simp only [Category.assoc]
    _ = _ := by
        rw [T]
        simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id_assoc]

end Sheaf

section Complex

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q) (N : CochainComplex.Plus (ModuleCat.{u + 1} Λ))

/-- The constant complex `N_Y` on `Y_étale`. -/
abbrev etaleModuleConstantComplexOver :
    CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left) :=
  (constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapCochainComplexPlus.obj N

/-- **`N_Y|_{Y_k̄} ≅ f^{-1} N_{k̄}`**, degreewise the identification of the two pulled back
constant sheaves. -/
def fieldBaseChangeConstantComplexIso :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        (etaleModuleConstantComplexOver Λ Y N) ≅
      (etaleModuleInverseImage.{u, 0} Λ
        (pullback.snd Y.hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
        (etaleModuleConstantComplex Λ kbar N) :=
  ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents
    (fun n => fieldBaseChangeConstantIso Λ (N.obj.X n) Y kbar)
    (fun i j _ => by
      have h₁ := (etaleModuleInverseImageConstantIso.{u, 0} Λ
        (fieldBaseChangeProj Y kbar)).hom.naturality (N.obj.d i j)
      have h₂ := (etaleModuleInverseImageConstantIso.{u, 0} Λ
        (pullback.snd Y.hom (specAlgebraMap k kbar))).inv.naturality (N.obj.d i j)
      dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
      show ((etaleModuleInverseImageConstantIso.{u, 0} Λ (fieldBaseChangeProj Y kbar)).hom.app
            (N.obj.X i) ≫ (etaleModuleInverseImageConstantIso.{u, 0} Λ
              (pullback.snd Y.hom (specAlgebraMap k kbar))).inv.app (N.obj.X i)) ≫
          (etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
            ((constantSheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
              (N.obj.d i j)) =
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).map
            ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map (N.obj.d i j)) ≫
          (etaleModuleInverseImageConstantIso.{u, 0} Λ (fieldBaseChangeProj Y kbar)).hom.app
            (N.obj.X j) ≫ (etaleModuleInverseImageConstantIso.{u, 0} Λ
              (pullback.snd Y.hom (specAlgebraMap k kbar))).inv.app (N.obj.X j)
      rw [← Category.assoc, h₁, Category.assoc, Category.assoc, h₂]))

/-- Perfectness of `RΓ(Y_k̄, N_Y|_{Y_k̄})` is perfectness of `RΓ(Spec k̄, Rf_*(f^{-1} N_{k̄}))`. -/
theorem isPerfect_selfMapCohomology_constant_of_frobeniusRestriction
    (h₁ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar (etaleModuleConstantComplexOver Λ Y N)))))) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (selfMapCohomology.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex Λ kbar N))) :=
  StacksDraft.Perfect.isPerfect_of_iso.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
        (DerivedCategory.Plus.Q.mapIso (fieldBaseChangeConstantComplexIso Λ Y kbar N).symm)))) h₁

/-- **The canonical Frobenius and the pullback by `π̄` have the same trace on
`RΓ(Y_k̄, N_Y|_{Y_k̄})`.** -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_constant_eq_selfMap
    (h₁ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar (etaleModuleConstantComplexOver Λ Y N))))))
    (h₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (selfMapCohomology.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex Λ kbar N)))) :
    perfectDerivedTrace Λ ⟨_, h₁⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
          (etaleModuleConstantComplexOver Λ Y N))) =
      perfectDerivedTrace Λ ⟨_, h₂⟩ (DerivedCategory.Plus.ι.map
        (selfMapCohomologyEndo.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange Y kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)
          (etaleModuleConstantComplex Λ kbar N))) := by
  rw [frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
  refine Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_iso
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (fieldBaseChangeConstantComplexIso Λ Y kbar N) _ _ ?_ h₁ h₂
  ext n : 2
  exact frobeniusBaseChangeTwist_constant_comp_map_eq Λ (N.obj.X n) Y kbar p q hcard

end Complex

section Proper

variable (Λ : Type) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f] (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  (N : CochainComplex.Plus (ModuleCat.{u + 1} Λ))

/-- Perfectness of `RΓ_c(X_k̄, N_X)` for `X` proper, compactified by itself, is perfectness of
`RΓ(Spec k̄, Rf_*(f^{-1} N_{k̄}))`. -/
theorem isPerfect_selfMapCohomology_constant_of_ofProper
    (hX : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f (CompactificationOf.ofProper f) kbar
        (etaleModuleConstantComplexOver Λ (Over.mk f) N)))) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (selfMapCohomology.{u, 0} Λ (pullback.snd f (specAlgebraMap k kbar))
        (etaleModuleConstantComplex Λ kbar N))) :=
  isPerfect_selfMapCohomology_constant_of_frobeniusRestriction Λ (Over.mk f) kbar N
    (StacksDraft.Perfect.isPerfect_of_iso.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.mapIso
      (frobeniusRestrictionCohomologyIso Λ (Over.mk f) kbar
        (etaleModuleExtensionByZeroIdMapCochainComplexPlusIso Λ X
          (etaleModuleConstantComplexOver Λ (Over.mk f) N)).symm)) hX)

/-- **The Lefschetz number of the trace formula with constant coefficients on a proper scheme is
the trace of the pullback by `π̄`.** For `X` proper over `k`, compactified by itself, and a
constant complex `N_X`,

`Tr(π_X^* | RΓ_c(X_k̄, N_X)) = Tr(π̄^* | RΓ(X_k̄, f^{-1} N_{k̄}))`,

where on the right `π̄ = π_X × id` acts by pullback. -/
theorem canonicalCompactSupportLefschetzNumber_ofProper_constant_eq_selfMap
    (hX : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f (CompactificationOf.ofProper f) kbar
        (etaleModuleConstantComplexOver Λ (Over.mk f) N))))
    (h₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (selfMapCohomology.{u, 0} Λ (pullback.snd f (specAlgebraMap k kbar))
        (etaleModuleConstantComplex Λ kbar N)))) :
    canonicalCompactSupportLefschetzNumber.{u, 0} Λ f (CompactificationOf.ofProper f) kbar p q
        hcard (etaleModuleConstantComplexOver Λ (Over.mk f) N) hX =
      perfectDerivedTrace Λ ⟨_, h₂⟩ (DerivedCategory.Plus.ι.map
        (selfMapCohomologyEndo.{u, 0} Λ (pullback.snd f (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard)
          (etaleModuleConstantComplex Λ kbar N))) := by
  have e := etaleModuleExtensionByZeroIdMapCochainComplexPlusIso Λ X
    (etaleModuleConstantComplexOver Λ (Over.mk f) N)
  have h₁ := StacksDraft.Perfect.isPerfect_of_iso.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.mapIso
    (frobeniusRestrictionCohomologyIso Λ (Over.mk f) kbar e.symm)) hX
  refine (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ (Over.mk f) kbar p q
    hcard e hX h₁).trans ?_
  exact perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_constant_eq_selfMap Λ (Over.mk f)
    kbar p q hcard N h₁ h₂

end Proper

end Stacks.EtaleCohomology

end

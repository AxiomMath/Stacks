module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.AffineCech
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoveringsLargeCoefficients
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.AcyclicCorners
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.ModuleSectionsVanishingUnivLE

/-!
# `𝒪^{perf}` has no higher fppf cohomology on affine objects

Let `p` be a prime, `S` a scheme over `𝔽_p` and `(Sch/S)_h` a big h site over `S`. On its
underlying category with the fppf topology, regard `𝒪^{perf} = colim_F 𝒪` as a module over
itself. This file proves that its higher cohomology over every object with affine underlying
scheme vanishes, both as an abelian sheaf and as a sheaf of modules, and that consequently the
sections functor over such an object carries an injective resolution of `𝒪^{perf}` to a
quasi-isomorphism. This is the vanishing `H^i_{fppf}(X, 𝒪^{perf}) = 0` for affine `X` and `i > 0`
used in the proof of Stacks 0EWT.

## Main definitions

* `AlgebraicGeometry.BigHOver.perfectionRing`: the fppf sheaf of rings `𝒪^{perf}`.
* `AlgebraicGeometry.BigHOver.perfectionModule`: `𝒪^{perf}` as a module over itself, with its
  sections in the module universe of the site.

## Main results

* `AlgebraicGeometry.BigHOver.isZero_rightDerived_sheafSections_perfectionModule`: the higher
  cohomology of the underlying abelian sheaf over an affine object vanishes; this is the
  Čech-vanishing criterion of Stacks 03F9 for the standard fppf coverings.
* `AlgebraicGeometry.BigHOver.isZero_rightDerived_sections_perfectionModule`: the same for the
  module-valued sections functor (Stacks 03FD).
* `AlgebraicGeometry.BigHOver.quasiIso_sections_map_ι'_perfectionModule`: sections over an affine
  object carry an injective resolution of `𝒪^{perf}` to a quasi-isomorphism.

## References

* [Stacks Project, Tag 0EWT](https://stacks.math.columbia.edu/tag/0EWT)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigHOver

-- The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is stated at a module
-- universe that is a `max` of four universes, against which `Abelian (SheafOfModules.{u + 1} _)`
-- leaves a stuck universe constraint; the instance used here is Mathlib's.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fppf sheaf of rings `𝒪^{perf} = colim_F 𝒪`**, as a sheaf of rings for the fppf topology:
the fppf sheaf underlying the h sheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)`, which is the colimit of the Frobenius
system by `AlgebraicGeometry.BigHOver.isColimitPerfectionCocone`. -/
abbrev perfectionRing : Sheaf (fppfTopology B S hS) RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (awnRingSheafFppf B S hS)

/-- **`𝒪^{perf}` as a module over itself**, with its sections raised to the module universe
`u + 1` of the big site. -/
abbrev perfectionModule [HasSheafify (fppfTopology B S hS) AddCommGrpCat.{u + 1}]
    [(fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    SheafOfModules.{u + 1} (perfectionRing B S hS) :=
  Stacks.SheafOfModules.uliftUnit.{u + 1} (perfectionRing B S hS)

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)
  [HasSheafify (fppfTopology B S hS) AddCommGrpCat.{u + 1}]
  [(fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]

include hSp in
/-- **The higher fppf cohomology of `𝒪^{perf}` over an affine object vanishes**, for the underlying
abelian sheaf. This is the Čech-vanishing criterion of Stacks 03F9 for the collection of objects
with affine underlying scheme and their standard fppf coverings, which are cofinal (Stacks 03XA),
have affine iterated fibre products, and have vanishing positive degree Čech cohomology. -/
theorem isZero_rightDerived_sheafSections_perfectionModule (U : BigHOver B S hS)
    (hU : IsAffine ((BigHOver.toScheme B S hS).obj U)) (n : ℕ) (hn : 0 < n) :
    IsZero ((((sheafSections (fppfTopology B S hS) AddCommGrpCat.{u + 1}).obj (op U)).rightDerived
      n).obj ((SheafOfModules.toSheaf _).obj (perfectionModule B S hS))) := by
  refine Stacks.CechSite.isZero_rightDerived_sheafSections_of_cechCohomology_isZero.{0, u, u, u + 1}
    (fppfTopology B S hS) {V | IsAffine ((BigHOver.toScheme B S hS).obj V)}
    (fun V ↦ {E | IsStandardFppf B S hS E.1})
    (fun _ _ _ _ ↦ inferInstance) (fun E hE ↦ ?_) (fun V hV R hR ↦ ?_)
    ((SheafOfModules.toSheaf _).obj (perfectionModule B S hS)) (fun E hE q hq ↦ ?_) U hU n hn
  · obtain ⟨hU', hX⟩ := IsStandardFppf.isAffine hE
    exact ⟨hU', hX, fun q i ↦ isAffine_toScheme_piObj hU' E.1 hX q i⟩
  · obtain ⟨E, hE, hER⟩ := exists_isStandardFppf_sieve₀_le hV hR
    exact ⟨⟨E, hE.sieve₀_mem_fppfTopology⟩, hE, hER⟩
  · exact isZero_cechCohomology_awn p hSp hE q hq

variable [EnoughInjectives (SheafOfModules.{u + 1} (perfectionRing B S hS))]

include hSp in
/-- **The higher fppf cohomology of `𝒪^{perf}` over an affine object vanishes**, for the sections
functor on sheaves of `𝒪^{perf}`-modules. The higher sections of a sheaf of modules are those of
its underlying abelian sheaf (Stacks 03FD). -/
theorem isZero_rightDerived_sections_perfectionModule (U : BigHOver B S hS)
    (hU : IsAffine ((BigHOver.toScheme B S hS).obj U)) (n : ℕ) (hn : 0 < n) :
    IsZero (((Stacks.MayerVietoris.CanonicalMapOfComplexes.sections.{u + 1, u + 1}
      (perfectionRing B S hS) U).rightDerived n).obj (perfectionModule B S hS)) :=
  (isZero_rightDerived_sheafSections_perfectionModule B S hS p hSp U hU n hn).of_iso
    ((Stacks.Cohomology.ObjectSections.rightDerivedSectionsIsoUnivLE.{0, u, u, u + 1}
      (fppfTopology B S hS) (perfectionRing B S hS) U n).app (perfectionModule B S hS))

include hSp in
/-- **Sections over an affine object carry an injective resolution of `𝒪^{perf}` to a
quasi-isomorphism**, the higher cohomology of `𝒪^{perf}` over the object vanishing. -/
theorem quasiIso_sections_map_ι'_perfectionModule (U : BigHOver B S hS)
    (hU : IsAffine ((BigHOver.toScheme B S hS).obj U))
    (Rs : InjectiveResolution (perfectionModule B S hS)) :
    QuasiIso ((Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex.{u + 1, u + 1}
      (perfectionRing B S hS) U).map Rs.ι') :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.quasiIso_sections_map_ι' U Rs
    (isZero_rightDerived_sections_perfectionModule B S hS p hSp U hU)


end AlgebraicGeometry.BigHOver

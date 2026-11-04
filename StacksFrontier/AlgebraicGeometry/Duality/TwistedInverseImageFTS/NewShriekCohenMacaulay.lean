module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekFibreDimension
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartConsequences
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCoherent
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.RelativeSerreVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Witnesses
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Composition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `f_new^! 𝒪_Y` for flat quasi-finite and for Cohen–Macaulay morphisms

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a morphism of schemes of finite type over
`S`, not necessarily separated. With `f^!` replaced by `f_new^!` ([Stacks, Tag 0BV9]):

* [Stacks, Tag 0BV7]: if `f` is flat and quasi-finite, then `f_new^! 𝒪_Y = ω_{X/Y}[0]` for a
  coherent `𝒪_X`-module `ω_{X/Y}` flat over `Y`;
* [Stacks, Tag 0BV8]: if `f` is Cohen–Macaulay, then `f_new^! 𝒪_Y = ω_{X/Y}[d]` for a coherent
  `𝒪_X`-module `ω_{X/Y}` flat over `Y`, where `d` is the locally constant relative dimension of
  `X` over `Y`.

The proof is the source's: every statement is local on `X`, and on an affine open `V ⊆ X` the
restriction of `f_new^! 𝒪_Y` is `(V → Y)^! 𝒪_Y`
(`Stacks.Duality.NormalizedOnOpens.newShriekHomologyRestrictIso`), where the library's
[Stacks, Tag 0AU1], [Stacks, Tag 0BV7] and [Stacks, Tag 0BV8] for the morphism `V → Y` of
`FTS_Y` apply. The module `ω_{X/Y}` is a cohomology sheaf of `f_new^! 𝒪_Y` (for 0BV8, the direct
sum of the finitely many cohomology sheaves in degrees `-d`), so it is global from the start and
no glueing is needed.

## Main results

* `Stacks.Duality.NormalizedOnOpens.isCoherent_homology_newShriek`: the cohomology sheaves of
  `f_new^! 𝒪_Y` are coherent.
* `Stacks.Duality.NormalizedOnOpens.exists_isCoherent_isFlatOver_iso_single_newShriek`:
  [Stacks, Tag 0BV7] for `f_new^!`.
* `Stacks.Duality.NormalizedOnOpens.exists_isCoherent_isFlatOver_iso_shift_newShriek`:
  [Stacks, Tag 0BV8] for `f_new^!`.

## References

* [Stacks Project, Tag 0BV9](https://stacks.math.columbia.edu/tag/0BV9)
* [Stacks Project, Tag 0BV7](https://stacks.math.columbia.edu/tag/0BV7)
* [Stacks Project, Tag 0BV8](https://stacks.math.columbia.edu/tag/0BV8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
  (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)

/-! ### Preliminaries on `f` -/

include hp hpe in
/-- A morphism between schemes of finite type over a Noetherian base is locally of finite
type. -/
theorem locallyOfFiniteType_of_isFiniteTypeOverNoetherian : LocallyOfFiniteType f := by
  have : LocallyOfFiniteType (f ≫ q) := hpe ▸ hp.locallyOfFiniteType
  exact locallyOfFiniteType_of_comp f q

include hp hpe in
/-- The fibres of a morphism between schemes of finite type over a Noetherian base are locally
Noetherian. -/
theorem isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian (y : Y) :
    IsLocallyNoetherian (f.fiber y) := by
  have := locallyOfFiniteType_of_isFiniteTypeOverNoetherian (hp := hp) hpe
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField y)))
  exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)

/-- The fibres of an open immersion are locally Noetherian. -/
theorem isLocallyNoetherian_fiber_of_isOpenImmersion {V Z : Scheme.{u}} (ι : V ⟶ Z)
    [IsOpenImmersion ι] (z : Z) : IsLocallyNoetherian (ι.fiber z) := by
  have : LocallyOfFiniteType (ι.fiberToSpecResidueField z) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd ι (Z.fromSpecResidueField z)))
  exact LocallyOfFiniteType.isLocallyNoetherian (ι.fiberToSpecResidueField z)

/-! ### Coherence of the cohomology sheaves -/

include hpe hωS in
/-- **The cohomology sheaves of `f_new^! 𝒪_Y` are coherent.** On an affine open `V ⊆ X` they are
those of `(V → Y)^! 𝒪_Y`, which are coherent by [Stacks, Tag 0AU1]. -/
theorem isCoherent_homology_newShriek (i : ℤ) :
    ((@DerivedCategory.homologyFunctor X.Modules _ _ (PerfectApproximation.standardModel X)
      i).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y)).IsCoherent := by
  have := hq.source_noetherian
  refine AlgebraicGeometry.Modules.isCoherent_of_restrict _ (fun V : X.affineOpens => V.1)
    (AlgebraicGeometry.iSup_affineOpens_eq_top X) fun V => ?_
  have hsh := hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2
  have hE : DerivedCategoryB.derivedCategoryBPlus
      (fun M : Y.Modules ↦ _root_.SheafOfModules.IsCoherent M)
      (DerivedPushforward.derivedStructureSheaf Y).obj :=
    DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre Y)
      (SheafOfModules.unit Y.ringCatSheaf)
      (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit (X := Y))
  exact Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
    (newShriekHomologyRestrictIso c 𝒦X 𝒦Y hpe hωS V.1 hsh i).symm
    ((derivedCategoryBPlus_upperShriek (ftsHomSelf hsh) (c _ hsh) _ hE).2 i)

include hp hq hpe in
/-- A morphism between schemes of finite type over a Noetherian base is locally of finite
presentation, its target being locally Noetherian. -/
@[sga "1 IX 4.10" "Noetherian base",
  sga "1 IX 4.7" "partial",
  sga "3 V 6.1" "special case",
  sga "3 VIA 2.5.4" "partial",
  sga "3 VIB 10.8" "special case",
  sga "3 X 3.5" "special case",
  sga "3 X 3.7" "partial"]
theorem locallyOfFinitePresentation_of_isFiniteTypeOverNoetherian :
    LocallyOfFinitePresentation f := by
  have := locallyOfFiniteType_of_isFiniteTypeOverNoetherian (hp := hp) hpe
  have := hq.source_noetherian
  infer_instance

/-- A sheaf of abelian groups vanishes exactly when it has no nonzero element. -/
theorem isZero_iff_not_nontrivial (A : Ab.{u}) : IsZero A ↔ ¬ Nontrivial A := by
  rw [AddCommGrpCat.isZero_iff_subsingleton, not_nontrivial_iff_subsingleton]

/-! ### Tag 0BV7 for `f_new^!` -/

include hpe hωS in
/-- **[Stacks, Tag 0BV7] for `f_new^!`.** Let `f : X ⟶ Y` be a flat, locally quasi-finite
morphism of schemes of finite type over the base of [Stacks, Tag 0AU4], not necessarily
separated. Then `f_new^! 𝒪_Y = ω_{X/Y}[0]` for some coherent `𝒪_X`-module `ω_{X/Y}` flat over
`Y`. -/
theorem exists_isCoherent_isFlatOver_iso_single_newShriek [Flat f] [LocallyQuasiFinite f] :
    letI := PerfectApproximation.standardModel X
    ∃ ω : X.Modules, ω.IsCoherent ∧ IsFlatOver f.toLRSHom.toShHom ω ∧
      Nonempty ((newShriekStructureSheaf c f 𝒦X 𝒦Y : DerivedCategory X.Modules) ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj ω) := by
  have := hq.source_noetherian
  let := PerfectApproximation.standardModel X
  let K : DerivedCategory X.Modules := newShriekStructureSheaf c f 𝒦X 𝒦Y
  -- `f_new^! 𝒪_Y` is concentrated in degree `0`, by the flat bound with fibres of dimension `0`.
  have hzero : ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K) :=
    fun i hi => AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun x => by
      have hd : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
          ((0 : ℕ) : WithBot ℕ∞) :=
        le_antisymm ((topologicalKrullDimAt_le_topologicalKrullDim _).trans
          (topologicalKrullDim_fiber_le_zero_of_locallyQuasiFinite f _))
          (by simpa using topologicalKrullDimAt_nonneg (f.asFiber x))
      refine (isZero_iff_not_nontrivial _).2 fun hnt => hi ?_
      have := fibreDim_bounds_of_nontrivial_stalk_homology_newShriek_of_flat c 𝒦X 𝒦Y hpe hωS
        x 0 hd i hnt
      omega
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero K 0 hzero
  let ω := (DerivedCategory.homologyFunctor X.Modules 0).obj K
  refine ⟨ω, isCoherent_homology_newShriek c 𝒦X 𝒦Y hpe hωS 0, fun x => ?_, ⟨e⟩⟩
  -- flatness, read on an affine open through `x` from Tag 0BV7 for `V → Y`.
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  have hsh := hp.isShriekable_ι_comp_of_isAffineOpen hq hpe hV
  have : Flat (ftsHomSelf hsh).left := inferInstanceAs (Flat (V.ι ≫ f))
  have : LocallyQuasiFinite (ftsHomSelf hsh).left :=
    inferInstanceAs (LocallyQuasiFinite (V.ι ≫ f))
  obtain ⟨ωV, -, hflV, ⟨eV⟩⟩ := exists_isCoherent_isFlatOver_iso_single (ftsHomSelf hsh) (c _ hsh)
  let W := (ftsOf (V.ι ≫ f) hsh.separatedFiniteType).left
  let eω : (Scheme.Modules.pullback V.ι).obj ω ≅ ωV :=
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app ω).symm ≪≫
      newShriekHomologyRestrictIso c 𝒦X 𝒦Y hpe hωS V hsh 0 ≪≫
      (DerivedCategory.homologyFunctor W.Modules 0).mapIso eV ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso W.Modules 0).app ωV
  exact (isFlatOverAt_pullback_ι_iff f V ω ⟨x, hxV⟩).1
    ((flatOverAt_iff_of_iso (V.ι ≫ f) eω ⟨x, hxV⟩).2 (hflV ⟨x, hxV⟩))

/-! ### Tag 0BV8 for `f_new^!` -/

/-- The restriction of a Cohen–Macaulay morphism to an open of the source is Cohen–Macaulay. -/
private theorem isCohenMacaulay_ftsHomSelf_left
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian
      (hp := hp) hpe)) {V : X.Opens} (hsh : IsShriekable (V.ι ≫ f)) :
    (ftsHomSelf hsh).left.IsCohenMacaulay (isLocallyNoetherian_fiber_left (ftsHomSelf hsh)) :=
  isCohenMacaulay_comp V.ι f (isLocallyNoetherian_fiber_of_isOpenImmersion V.ι)
    (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian (hp := hp) hpe)
    (isLocallyNoetherian_fiber_left (ftsHomSelf hsh))
    (Scheme.Hom.isCohenMacaulay_of_isOpenImmersion V.ι _) hCM

include hpe hωS in
/-- **The cohomology of `f_new^! 𝒪_Y` for a Cohen–Macaulay `f` sits in degree minus the
relative dimension**: at a point `x` where the relative dimension of `X` over `Y` is `d`, the
stalk of `H^i(f_new^! 𝒪_Y)` vanishes for `i ≠ -d`. On an affine open through `x` this is the
known computation for the morphism `V → Y` of `FTS_Y`. -/
theorem isZero_stalk_homology_newShriek_of_isCohenMacaulay
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian
      (hp := hp) hpe))
    (hfib : ∀ y : Y, IsCohenMacaulay (f.fiber y)) [Flat f] [LocallyOfFinitePresentation f]
    (x : X) (i : ℤ) (hi : i ≠ -(relativeDimensionFunction f hfib x : ℤ)) :
    IsZero (((@DerivedCategory.homologyFunctor X.Modules _ _
      (PerfectApproximation.standardModel X) i).obj
        (newShriekStructureSheaf c f 𝒦X 𝒦Y)).presheaf.stalk x) := by
  have := hq.source_noetherian
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  have hsh := hp.isShriekable_ι_comp_of_isAffineOpen hq hpe hV
  let g := ftsHomSelf hsh
  have : Flat g.left := inferInstanceAs (Flat (V.ι ≫ f))
  have := locallyOfFinitePresentation_left g
  have hCMg := isCohenMacaulay_ftsHomSelf_left (hp := hp) hpe hCM hsh
  have hfibg := ((isCohenMacaulay_iff_flat_and_fibers g.left
    (isLocallyNoetherian_fiber_left g)).mp hCMg).2
  have hrd : relativeDimensionFunction g.left hfibg ⟨x, hxV⟩ =
      relativeDimensionFunction f hfib x := by
    exact_mod_cast (relativeDimensionFunction_apply g.left hfibg ⟨x, hxV⟩).symm.trans
      ((fiberDimensionAt_comp_openImmersion V.ι f ⟨x, hxV⟩).trans
        (relativeDimensionFunction_apply f hfib x))
  have hz := isZero_restrict_homology_relativeDimensionOpen
    (upperShriekStructureSheafCharts g (c _ hsh)) hCMg hfibg
    (relativeDimensionFunction f hfib x) i hi
  have hx' : (⟨x, hxV⟩ : V.toScheme) ∈
      relativeDimensionOpen g.left hfibg (relativeDimensionFunction f hfib x) :=
    (mem_relativeDimensionOpen g.left hfibg _ _).2 hrd
  exact (isZero_iff_not_nontrivial _).2 fun hnt => (isZero_iff_not_nontrivial _).1
    (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict
      _ _ _ hx' hz)
    ((nontrivial_stalk_homology_newShriek_iff c 𝒦X 𝒦Y hpe hωS V hsh i ⟨x, hxV⟩).1 hnt)

include hpe hωS in
/-- **On the locus where the relative dimension of a Cohen–Macaulay `f` is `d`, the cohomology of
`f_new^! 𝒪_Y` sits in degree `-d`.** -/
theorem isZero_restrict_homology_newShriek_of_isCohenMacaulay
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian
      (hp := hp) hpe))
    (hfib : ∀ y : Y, IsCohenMacaulay (f.fiber y)) [Flat f] [LocallyOfFinitePresentation f]
    (d : ℕ) (i : ℤ) (hi : i ≠ -(d : ℤ)) :
    IsZero ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f hfib d).ι).obj
      ((@DerivedCategory.homologyFunctor X.Modules _ _ (PerfectApproximation.standardModel X)
        i).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y))) :=
  AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y =>
    (isZero_stalk_homology_newShriek_of_isCohenMacaulay c 𝒦X 𝒦Y hpe hωS hCM hfib
      ((relativeDimensionOpen f hfib d).ι y) i
        (by rwa [show relativeDimensionFunction f hfib ((relativeDimensionOpen f hfib d).ι y) = d
          from (mem_relativeDimensionOpen f hfib d _).1 y.2])
      ).of_iso ((Scheme.Modules.restrictStalkNatIso (relativeDimensionOpen f hfib d).ι y).app _)

include hpe hωS in
/-- **The cohomology sheaves of `f_new^! 𝒪_Y` for a Cohen–Macaulay `f` are flat over `Y`.** On an
affine open `V ⊆ X` they are those of `(V → Y)^! 𝒪_Y`, which are flat over `Y` by
[Stacks, Tag 0BV8]. -/
theorem isFlatOver_homology_newShriek_of_isCohenMacaulay
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian
      (hp := hp) hpe)) [Flat f] (i : ℤ) :
    IsFlatOver f.toLRSHom.toShHom ((@DerivedCategory.homologyFunctor X.Modules _ _
      (PerfectApproximation.standardModel X) i).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y)) := by
  intro x
  have := hq.source_noetherian
  let := PerfectApproximation.standardModel X
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  have hsh := hp.isShriekable_ι_comp_of_isAffineOpen hq hpe hV
  let g := ftsHomSelf hsh
  have : Flat g.left := inferInstanceAs (Flat (V.ι ≫ f))
  have hCMg := isCohenMacaulay_ftsHomSelf_left (hp := hp) hpe hCM hsh
  let eG : (Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules i).obj
      (newShriekStructureSheaf c f 𝒦X 𝒦Y)) ≅
      (DerivedCategory.homologyFunctor (ftsOf (V.ι ≫ f) hsh.separatedFiniteType).left.Modules
        i).obj (relativeDualizingComplexObj g (c _ hsh)) :=
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫
      newShriekHomologyRestrictIso c 𝒦X 𝒦Y hpe hωS V hsh i
  exact (isFlatOverAt_pullback_ι_iff f V _ ⟨x, hxV⟩).1
    ((flatOverAt_iff_of_iso (V.ι ≫ f) eG ⟨x, hxV⟩).2
      (isFlatOver_homology_of_isCohenMacaulay (upperShriekStructureSheafCharts g (c _ hsh)) hCMg
        i ⟨x, hxV⟩))

/-- In a preadditive category, if every summand of a finite biproduct except the `j₀`-th is zero,
then the projection onto the `j₀`-th summand is an isomorphism. -/
theorem isIso_biproduct_π_of_isZero {C : Type*} [Category C] [Preadditive C] {J : Type*}
    (F : J → C) [HasBiproduct F] (j₀ : J)
    (hz : ∀ j, j ≠ j₀ → IsZero (F j)) : IsIso (biproduct.π F j₀) := by
  classical
  refine ⟨⟨biproduct.ι F j₀, biproduct.hom_ext' _ _ fun j => ?_, biproduct.ι_π_self _ _⟩⟩
  rcases eq_or_ne j j₀ with rfl | hj
  · simp
  · exact (hz j hj).eq_of_src _ _

/-- A finite direct sum of coherent sheaves of modules on a scheme is coherent. -/
theorem isCoherent_biproduct {X : Scheme.{u}} {n : ℕ} (F : Fin n → X.Modules)
    (hF : ∀ k, (F k).IsCoherent) : (⨁ F).IsCoherent :=
  AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
    ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_of_iso
      (Limits.biproduct.isoCoproduct F).symm
      (Stacks.SheafOfModules.isCoherent_sigma _ fun k =>
        AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent (hF k)))

/-- A complex whose cohomology is concentrated in degree `-n` is its cohomology object in degree
`-n`, placed in degree `-n`. -/
theorem nonempty_iso_shift_singleFunctor_homology_of_isZero {C : Type u} [Category C]
    [Abelian C] [HasDerivedCategory C] (E : DerivedCategory C) (n : ℤ)
    (hE : ∀ i : ℤ, i ≠ -n → IsZero ((DerivedCategory.homologyFunctor C i).obj E)) :
    Nonempty (E ≅ ((DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C (-n)).obj E))⟦n⟧) := by
  let L := E⟦-n⟧
  have hzL : ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C i).obj L) := fun i hi =>
    (hE (i + -n) (by omega)).of_iso (Dualizing.homologyShiftObjIso E i (-n))
  obtain ⟨eL⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero L 0 hzL
  let eM : (DerivedCategory.homologyFunctor C 0).obj L ≅
      (DerivedCategory.homologyFunctor C (-n)).obj E :=
    Dualizing.homologyShiftObjIso E 0 (-n) ≪≫
      eqToIso (congrArg (fun m => (DerivedCategory.homologyFunctor C m).obj E) (zero_add _))
  exact ⟨((shiftFunctorCompIsoId _ (-n) n (by omega)).app E).symm ≪≫
    (shiftFunctor _ n).mapIso (eL ≪≫ (DerivedCategory.singleFunctor C 0).mapIso eM)⟩

include hpe hωS in
/-- **[Stacks, Tag 0BV8] for `f_new^!`.** Let `f : X ⟶ Y` be a Cohen–Macaulay morphism of
schemes of finite type over the base of [Stacks, Tag 0AU4], not necessarily separated. Then
`f_new^! 𝒪_Y = ω_{X/Y}[d]` for some coherent `𝒪_X`-module `ω_{X/Y}` flat over `Y`, where `d` is
the locally constant relative dimension of `X` over `Y`: on the open and closed locus where the
relative dimension is `d`, `f_new^! 𝒪_Y` is `ω_{X/Y}` placed in degree `-d`. -/
theorem exists_isCoherent_isFlatOver_iso_shift_newShriek
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian
      (hp := hp) hpe)) :
    letI h := (isCohenMacaulay_iff_flat_and_fibers f
      (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian (hp := hp) hpe)).mp hCM
    letI : Flat f := h.1
    letI := locallyOfFinitePresentation_of_isFiniteTypeOverNoetherian (hp := hp) (hq := hq) hpe
    letI := PerfectApproximation.standardModel X
    ∃ ω : X.Modules, ω.IsCoherent ∧ IsFlatOver f.toLRSHom.toShHom ω ∧
      ∀ d : ℕ,
        letI := PerfectApproximation.standardModel (relativeDimensionOpen f h.2 d).toScheme
        Nonempty ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f h.2 d).ι
            ).mapDerivedCategory.obj
              (newShriekStructureSheaf c f 𝒦X 𝒦Y : DerivedCategory X.Modules) ≅
          ((DerivedCategory.singleFunctor _ 0).obj
            ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f h.2 d).ι).obj ω))⟦
              (d : ℤ)⟧) := by
  let h := (isCohenMacaulay_iff_flat_and_fibers f
    (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian (hp := hp) hpe)).mp hCM
  let : Flat f := h.1
  let := locallyOfFinitePresentation_of_isFiniteTypeOverNoetherian (hp := hp) (hq := hq) hpe
  let := PerfectApproximation.standardModel X
  have := hp.source_noetherian
  have := hq.source_noetherian
  let K : DerivedCategory X.Modules := newShriekStructureSheaf c f 𝒦X 𝒦Y
  let rd := relativeDimensionFunction f h.2
  obtain ⟨N, hN⟩ := rd.range_finite.bddAbove
  let G : ℕ → X.Modules := fun k => (DerivedCategory.homologyFunctor X.Modules (-(k : ℤ))).obj K
  let G' : Fin (N + 1) → X.Modules := fun k => G k
  let ω : X.Modules := ⨁ G'
  let Ud := fun d : ℕ => relativeDimensionOpen f h.2 d
  have hzU := isZero_restrict_homology_newShriek_of_isCohenMacaulay c 𝒦X 𝒦Y hpe hωS hCM h.2
  have hres : ∀ d : ℕ, Nonempty ((Scheme.Modules.restrictFunctor (Ud d).ι).obj ω ≅
      (Scheme.Modules.restrictFunctor (Ud d).ι).obj (G d)) := by
    intro d
    let R := Scheme.Modules.restrictFunctor (Ud d).ι
    by_cases hd : d ≤ N
    · let k₀ : Fin (N + 1) := ⟨d, Nat.lt_succ_of_le hd⟩
      have := isIso_biproduct_π_of_isZero (fun k : Fin (N + 1) => R.obj (G k)) k₀ fun k hk =>
        hzU d _ fun he => hk (Fin.ext (by simp only [k₀]; omega))
      exact ⟨R.mapBiproduct _ ≪≫ asIso (biproduct.π (fun k : Fin (N + 1) => R.obj (G k)) k₀)⟩
    · have hempty : ∀ M : (Ud d).toScheme.Modules, IsZero M := fun M =>
        AlgebraicGeometry.isZero_of_forall_isZero_stalk M fun y =>
          absurd ((mem_relativeDimensionOpen f h.2 d _).1 y.2 ▸ hN ⟨_, rfl⟩) hd
      exact ⟨(hempty _).iso (hempty _)⟩
  refine ⟨ω, isCoherent_biproduct G' fun k => isCoherent_homology_newShriek c 𝒦X 𝒦Y hpe hωS _,
    fun x => ?_, fun d => ?_⟩
  · let d := rd x
    have hx : x ∈ Ud d := (mem_relativeDimensionOpen f h.2 d x).2 rfl
    let e : (Scheme.Modules.pullback (Ud d).ι).obj ω ≅
        (Scheme.Modules.pullback (Ud d).ι).obj (G d) :=
      (Scheme.Modules.restrictFunctorIsoPullback (Ud d).ι).symm.app _ ≪≫ (hres d).some ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback (Ud d).ι).app _
    exact (isFlatOverAt_pullback_ι_iff f (Ud d) ω ⟨x, hx⟩).1
      ((flatOverAt_iff_of_iso ((Ud d).ι ≫ f) e ⟨x, hx⟩).2
        ((isFlatOverAt_pullback_ι_iff f (Ud d) (G d) ⟨x, hx⟩).2
          (isFlatOver_homology_newShriek_of_isCohenMacaulay c 𝒦X 𝒦Y hpe hωS hCM _ x)))
  · let := PerfectApproximation.standardModel (Ud d).toScheme
    let R := Scheme.Modules.restrictFunctor (Ud d).ι
    let eH := fun i : ℤ => (R.mapDerivedCategoryHomologyIso i).app K
    obtain ⟨e⟩ := nonempty_iso_shift_singleFunctor_homology_of_isZero (R.mapDerivedCategory.obj K)
      d fun i hi => (hzU d i hi).of_iso (eH i)
    exact ⟨e ≪≫ (shiftFunctor _ (d : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (eH (-(d : ℤ)) ≪≫ (hres d).some.symm))⟩

end NormalizedOnOpens

end Stacks.Duality

end

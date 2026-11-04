module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModelTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.CohenMacaulayDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectOfDerivedFibreWindow
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenBetti
public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.RelativelyPerfect
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GorensteinDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic

/-!
# The relative dualizing sheaf of a family of Gorenstein curves

Let `S` be a quasi-compact and quasi-separated scheme and `f : X ⟶ S` a proper, flat morphism of
finite presentation, with relative dualizing complex `ω_{X/S}^• = a(𝒪_S)` (Stacks 0E2Z). For a
cartesian square presenting `C` as `X ×_S Spec k` over a field, the derived restriction
`Lh^*ω_{X/S}^•` is the dualizing complex `ω_C^•` of `C` over `k` (Stacks 0E4P). When the fibres of
`f` are Gorenstein and equidimensional of dimension one, the derived fibres of `ω_{X/S}^•` are
one-dimensional and concentrated in degree `-1`, so `ω_{X/S}^•` is perfect (Stacks 068V on affine
charts) and, by Stacks 0BDK, it is `ω_{X/S}[1]` for a finite locally free module `ω_{X/S}` of rank
one. The top-degree base change then identifies the pullback of `ω_{X/S}` to every such `C` with
the dualizing sheaf `ω_C` of Stacks 0BS2. These are the assertions of Stacks 0E6P and 0E6R for the
families of curves whose total space is a scheme, with the relative dualizing sheaf of
Stacks 0E6Q, proved by the route the source suggests ("deduce this directly from the discussion
above of what happens after base change to a field").

## Main definitions

* `Stacks.Duality.CurveFibres.properFlatDualizingSheaf`: `ω_{X/S} = H^{-1}(ω_{X/S}^•)`.
* `Stacks.Duality.CurveFibres.HasGorensteinCurveFibres`: every fibre, presented over its residue
  field, is Gorenstein and equidimensional of dimension one.

## Main results

* `Stacks.Duality.CurveFibres.nonempty_relativeDualizingComplex_baseChange_iso`: Stacks 0E4P at
  `Spec k ⟶ S`.
* `Stacks.Duality.CurveFibres.derivedFiberBetti_relativeDualizingComplex`: the derived fibres of
  `ω_{X/S}^•`.
* `Stacks.Duality.CurveFibres.isPerfect_relativeDualizingComplex`: `ω_{X/S}^•` is perfect.
* `Stacks.Duality.CurveFibres.isFiniteLocallyFreeOfRank_properFlatDualizingSheaf` and
  `Stacks.Duality.CurveFibres.isZero_homology_relativeDualizingComplex`: `ω_{X/S}^• = ω_{X/S}[1]`
  with `ω_{X/S}` invertible (Stacks 0E6P, 0E6R).
* `Stacks.Duality.CurveFibres.nonempty_pullback_properFlatDualizingSheaf_iso_of_isPullback`: the
  pullback of `ω_{X/S}` to a fibre over a field is its dualizing sheaf.

## Implementation notes

Not registered: Stacks 0E6P, 0E6Q and 0E6R are stated for families of curves whose total space is
an algebraic space; these are their contents for scheme families.
The relative dualizing complex and the derived-fibre machinery of Stacks 0BDK are stated at the
standard model `CategoryTheory.HasDerivedCategory.standard`; the statements here name that model
explicitly, and cross to the locally small model of `Stacks.Duality.dualizingComplexOverField`
through `Stacks.Duality.StandardModel.relativeDualizingComplexModelIso` and
`StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso`.

## References

* [Stacks Project, Tag 0E4P](https://stacks.math.columbia.edu/tag/0E4P)
* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.CurveFibres

variable {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

section FibreInstances

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)

/-- The fibre `X_s ⟶ Spec κ(s)` of a proper morphism is proper, as a base change of `f`. -/
instance isProper_fiberToSpecResidueField [IsProper f] : IsProper (f.fiberToSpecResidueField s) :=
  MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _) inferInstance

/-- The fibre `X_s ⟶ Spec κ(s)` of a flat morphism is flat, as a base change of `f`. -/
instance flat_fiberToSpecResidueField [Flat f] : Flat (f.fiberToSpecResidueField s) :=
  inferInstanceAs (Flat (pullback.snd _ _))

/-- The fibre `X_s ⟶ Spec κ(s)` of a morphism locally of finite presentation is locally of finite
presentation, as a base change of `f`. -/
instance locallyOfFinitePresentation_fiberToSpecResidueField [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (f.fiberToSpecResidueField s) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (IsPullback.of_hasPullback _ _) inferInstance

/-- The structure morphism `X_s ⟶ Spec κ(s)` of the fibre, with `κ(s)` read as
`CommRingCat.of κ(s)`: the spelling of the base of `Stacks.Duality.dualizingSheafOverField`. -/
def fiberToSpecOf : f.fiber s ⟶ Spec (.of (S.residueField s)) :=
  f.fiberToSpecResidueField s

/-- `fiberToSpecOf f s` is proper when `f` is. -/
instance isProper_fiberToSpecOf [IsProper f] : IsProper (fiberToSpecOf f s) :=
  isProper_fiberToSpecResidueField f s

/-- `fiberToSpecOf f s` is flat when `f` is. -/
instance flat_fiberToSpecOf [Flat f] : Flat (fiberToSpecOf f s) :=
  flat_fiberToSpecResidueField f s

/-- `fiberToSpecOf f s` is locally of finite presentation when `f` is. -/
instance locallyOfFinitePresentation_fiberToSpecOf [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (fiberToSpecOf f s) :=
  locallyOfFinitePresentation_fiberToSpecResidueField f s

/-- The fibre `X_s` of a proper morphism is quasi-compact. -/
instance compactSpace_fiber [IsProper f] : CompactSpace (f.fiber s) :=
  QuasiCompact.compactSpace_of_compactSpace (f.fiberToSpecResidueField s)

/-- The fibre `X_s` of a proper morphism is quasi-separated. -/
instance quasiSeparatedSpace_fiber [IsProper f] : QuasiSeparatedSpace (f.fiber s) :=
  quasiSeparatedSpace_of_quasiSeparated (f.fiberToSpecResidueField s)

end FibreInstances

/-- **The relative dualizing complex after base change to a field** (Stacks 0E4P at
`Spec k ⟶ S`). For a cartesian square presenting `C` as `X ×_S Spec k`, the relative dualizing
complex `a_C(𝒪_{Spec k})` of `C ⟶ Spec k` is the derived pullback `Lh^*ω_{X/S}^•` of the relative
dualizing complex of `f` along `h : C ⟶ X`. -/
theorem nonempty_relativeDualizingComplex_baseChange_iso {k : Type u} [Field k] {C : Scheme.{u}}
    {h : C ⟶ X} {g : C ⟶ Spec (.of k)} {c : Spec (.of k) ⟶ S} (hpb : IsPullback h g f c)
    [IsProper g] [CompactSpace C] [QuasiSeparatedSpace C] :
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    Nonempty ((StandardModel.relativeDualizingComplex g).obj ≅
      Scheme.Hom.DiagonalOpen.baseChangeComplex h
        (StandardModel.relativeDualizingComplex f).obj) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  have : QuasiSeparatedSpace (pullback f f : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst f f)
  obtain ⟨φ, -, -⟩ := Scheme.Hom.existsUnique_relativeDualizingComplex_iso_baseChange f
    (isRelativeDualizingComplex_relativeDualizingComplex f) hpb
    (Scheme.Hom.DiagonalOpen.ofIsSeparated _) (Scheme.Hom.pullbackMapOfIsPullback hpb)
    (by simp [Scheme.Hom.DiagonalOpen.ofIsSeparated])
  exact ⟨φ⟩

/-- **The relative dualizing complex restricted to a fibre** (Stacks 0E4P at `Spec κ(s) ⟶ S`).
The relative dualizing complex `a_{X_s}(𝒪_{κ(s)})` of the fibre `X_s ⟶ Spec κ(s)` is the derived
restriction `Lh^*ω_{X/S}^•` of the relative dualizing complex of `f` along `h : X_s ⟶ X`. -/
theorem nonempty_relativeDualizingComplex_fiber_iso (s : S) :
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    Nonempty ((StandardModel.relativeDualizingComplex (f.fiberToSpecResidueField s)).obj ≅
      Scheme.Hom.DiagonalOpen.baseChangeComplex (f.fiberι s)
        (StandardModel.relativeDualizingComplex f).obj) := by
  exact nonempty_relativeDualizingComplex_baseChange_iso f
    (g := fiberToSpecOf f s) (IsPullback.of_hasPullback _ _)

/-! ### Over a field: the relative dualizing complex of a Cohen–Macaulay curve -/

section OverField

variable {k : Type u} [Field k] {C : Scheme.{u}} (g : C ⟶ Spec (CommRingCat.of k)) [IsProper g]
  [CompactSpace C] [QuasiSeparatedSpace C]

/-- The relative dualizing complex `a(𝒪_{Spec k})` of a proper scheme over a field, read at the
locally small model, is the dualizing complex `ω_C^•` of Stacks 0BS2: the comparison of the two
models carries `a(𝒪_{Spec k})` at the standard model to `a(𝒪_{Spec k})` at the locally small
model, which is `Stacks.Duality.dualizingComplexOverField` by definition. -/
def relativeDualizingComplexModelIsoOverField :
    (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard C.Modules)
        (Scheme.Modules.hasDerivedCategory C)).functor.obj
        (StandardModel.relativeDualizingComplex g).obj ≅
      (dualizingComplexOverField g).obj :=
  (ObjectProperty.ι _).mapIso (StandardModel.relativeDualizingComplexModelIso g)

/-- **The cohomology sheaves of `a(𝒪_{Spec k})` at the standard model** are those of the
dualizing complex `ω_C^•` of Stacks 0BS2. -/
def homologyRelativeDualizingComplexIsoOverField (n : ℤ) :
    (@DerivedCategory.homologyFunctor C.Modules _ _ (HasDerivedCategory.standard C.Modules) n).obj
        (StandardModel.relativeDualizingComplex g).obj ≅
      (DerivedCategory.homologyFunctor C.Modules n).obj (dualizingComplexOverField g).obj :=
  ((StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso
      (HasDerivedCategory.standard C.Modules) (Scheme.Modules.hasDerivedCategory C) n).app
        (StandardModel.relativeDualizingComplex g).obj).symm ≪≫
    (DerivedCategory.homologyFunctor C.Modules n).mapIso
      (relativeDualizingComplexModelIsoOverField g)

/-- For a proper Cohen–Macaulay scheme `C` over a field, equidimensional of dimension one, the
relative dualizing complex `a(𝒪_{Spec k})` has no cohomology outside degree `-1`
(Stacks 0BS2, 0AWN). -/
theorem isZero_homology_relativeDualizingComplex_of_isCohenMacaulay
    (hcm : AlgebraicGeometry.IsCohenMacaulay C) (hequi : TopologicalSpace.Equidimensional C)
    (hdim : topologicalKrullDim C = 1) (n : ℤ) (hn : n ≠ -1) :
    IsZero ((@DerivedCategory.homologyFunctor C.Modules _ _
      (HasDerivedCategory.standard C.Modules) n).obj
        (StandardModel.relativeDualizingComplex g).obj) :=
  (isZero_homology_dualizingComplexOverField_of_isCohenMacaulay g hcm hequi hdim n hn).of_iso
    (homologyRelativeDualizingComplexIsoOverField g n)

/-- The relative dualizing complex of a proper scheme over a field which is Gorenstein and
equidimensional of dimension one is its dualizing sheaf placed in degree `-1`, a finite locally
free module of rank one (Stacks 0BS6): its open subscheme of Stacks 0BDK in degree `-1` and rank
`1` is everything. -/
theorem top_le_singleDegreeRankOpen_relativeDualizingComplex_of_isGorenstein
    (hG : AlgebraicGeometry.IsGorenstein C) (hequi : TopologicalSpace.Equidimensional C)
    (hdim : topologicalKrullDim C = 1) :
    ⊤ ≤ Scheme.Modules.singleDegreeRankOpen (StandardModel.relativeDualizingComplex g).obj (-1) 1 :=
  Scheme.Modules.le_singleDegreeRankOpen _ _ _
    ⟨fun j hj => Functor.map_isZero _ (isZero_homology_relativeDualizingComplex_of_isCohenMacaulay
        g (AlgebraicGeometry.isCohenMacaulay_of_isGorenstein C) hequi hdim j hj),
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ 1).1
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ 1).2
          ((isInvertible_dualizingSheafOverField_of_isGorenstein g hG hequi hdim).2.of_iso
            (homologyRelativeDualizingComplexIsoOverField g (-1)).symm)).restrict _)⟩

end OverField

/-! ### The relative dualizing sheaf of a family with Gorenstein one-dimensional fibres -/

section Family

variable {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

/-- The fibres of `f` are Gorenstein and equidimensional of dimension one: the families of curves
of Stacks 0E6R (Gorenstein fibres equidimensional of dimension `1`, Stacks 0E6M). The fibre over
`s` is read on any scheme `C` presenting it by a cartesian square over `Spec κ(s) ⟶ S`. -/
def HasGorensteinCurveFibres : Prop :=
  ∀ s : S, ∃ (C : Scheme.{u}) (h : C ⟶ X) (g : C ⟶ Spec (.of (S.residueField s))),
    IsPullback h g f (S.fromSpecResidueField s) ∧ AlgebraicGeometry.IsGorenstein C ∧
      TopologicalSpace.Equidimensional C ∧ topologicalKrullDim C = 1

/-- The relative dualizing complex `ω_{X/S}^• = a(𝒪_S)` of a proper flat morphism of finite
presentation is pseudo-coherent: it is `S`-perfect (Stacks 0E4L). -/
theorem isPseudoCoherent_relativeDualizingComplex :
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    @RingedSpace.IsPseudoCoherent X.toRingedSpace (HasDerivedCategory.standard _)
      (StandardModel.relativeDualizingComplex f).obj :=
  (StandardModel.isPerfectRelativeTo_relativeDualizingComplex f).1

/-- **The derived fibres of `ω_{X/S}^•`** for a family with Gorenstein fibres equidimensional of
dimension one: at every point of `X` the derived fibre is one-dimensional in degree `-1` and zero
in every other degree. The derived fibre at `x` is the derived fibre at `x` of the restriction
`Lh^*ω_{X/S}^•` to the fibre through `x` (Stacks 0BDI), which is `ω_{X_s}^• = ω_{X_s}[1]`
(Stacks 0E4P, 0BS2) with `ω_{X_s}` invertible (Stacks 0BS6). -/
theorem derivedFiberBetti_relativeDualizingComplex (hG : HasGorensteinCurveFibres f) (j : ℤ)
    (x : X) :
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    DerivedFibreBetti.derivedFiberBetti X (StandardModel.relativeDualizingComplex f).obj
      (isPseudoCoherent_relativeDualizingComplex f) j x = if j = -1 then 1 else 0 := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨C, h, g, hpb, hGs, hequi, hdim⟩ := hG (f.base x)
  have : IsProper g := MorphismProperty.of_isPullback (P := @IsProper) hpb inferInstance
  have : Flat g := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have : LocallyOfFinitePresentation g :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated g
  let y : C := hpb.isoPullback.inv.base (f.asFiber x)
  have hy : h.base y = x := by
    show (hpb.isoPullback.inv ≫ h).base (f.asFiber x) = x
    rw [hpb.isoPullback_inv_fst]
    exact f.fiberι_asFiber x
  obtain ⟨e⟩ := nonempty_relativeDualizingComplex_baseChange_iso f hpb
  have hpcF := isPseudoCoherent_relativeDualizingComplex g
  have hmem : y ∈ Scheme.Modules.singleDegreeRankOpen
      (StandardModel.relativeDualizingComplex g).obj (-1) 1 :=
    top_le_singleDegreeRankOpen_relativeDualizingComplex_of_isGorenstein g hGs hequi hdim trivial
  have hF : DerivedFibreBetti.derivedFiberBetti C
      (StandardModel.relativeDualizingComplex g).obj hpcF j y = if j = -1 then 1 else 0 := by
    split_ifs with hj
    · subst hj
      exact Scheme.Modules.derivedFiberBetti_eq_rank_of_mem_singleDegreeRankOpen _ hpcF _ _ hmem
    · exact Scheme.Modules.derivedFiberBetti_eq_zero_of_mem_singleDegreeRankOpen _ hpcF _ _ j hj
        hmem
  have hpc := isPseudoCoherent_relativeDualizingComplex f
  have hbc := congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback h
    (StandardModel.relativeDualizingComplex f).obj hpc j) y
  have hiso := congrFun (FibreBetti.derivedFiberBetti_eq_of_iso C hpcF
    (DerivedFibreBetti.isPseudoCoherent_derivedPullback h _ hpc) e j) y
  rw [← hF, hiso, hbc]
  simp only [Function.comp_apply, hy]

/-- **`ω_{X/S}^•` is perfect** for a family with Gorenstein fibres equidimensional of dimension
one: it is pseudo-coherent and its derived fibres are concentrated in degree `-1`. -/
theorem isPerfect_relativeDualizingComplex (hG : HasGorensteinCurveFibres f) :
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    @RingedSpace.IsPerfect X.toRingedSpace (HasDerivedCategory.standard _)
      (StandardModel.relativeDualizingComplex f).obj := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact Scheme.Modules.isPerfect_of_isPseudoCoherent_of_finrank_derivedFibre _
    (isPseudoCoherent_relativeDualizingComplex f) (-1) (-1) fun x j hj =>
      (derivedFiberBetti_relativeDualizingComplex f hG j x).trans (if_neg (by omega))

/-- **`ω_{X/S}^•` is a finite locally free module of rank one placed in degree `-1`
everywhere** (Stacks 0E6P, 0E6R): the open subscheme of Stacks 0BDK on which it is so is all of
`X`, by the pointwise description of that open for a perfect object. -/
theorem singleDegreeRankOpen_relativeDualizingComplex_eq_top (hG : HasGorensteinCurveFibres f) :
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    Scheme.Modules.singleDegreeRankOpen (StandardModel.relativeDualizingComplex f).obj (-1) 1 =
      ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact eq_top_iff.2 fun x _ => (Scheme.Modules.mem_singleDegreeRankOpen_iff _ (-1) 1
    (isPerfect_relativeDualizingComplex f hG) x).2 fun j =>
      derivedFiberBetti_relativeDualizingComplex f hG j x

/-- **The relative dualizing sheaf** `ω_{X/S} = H^{-1}(ω_{X/S}^•)` of a proper flat morphism of
finite presentation over a quasi-compact quasi-separated base (Stacks 0E6Q): the degree `-1`
cohomology sheaf of the relative dualizing complex `ω_{X/S}^• = a(𝒪_S)` of Stacks 0E2Z. -/
def properFlatDualizingSheaf : X.Modules :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) (-1)).obj
    (StandardModel.relativeDualizingComplex f).obj

/-- **`ω_{X/S}^•` has a single nonzero cohomology sheaf, in degree `-1`, finite locally free of
rank one, on all of `X`** (Stacks 0E6P, 0E6R): the open of Stacks 0BDK on which this holds is
`⊤`. -/
theorem isSingleDegreeRank_top_relativeDualizingComplex (hG : HasGorensteinCurveFibres f) :
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    Scheme.Modules.IsSingleDegreeRank (StandardModel.relativeDualizingComplex f).obj (-1) 1 ⊤ :=
  Scheme.Modules.IsSingleDegreeRank.mono _ _ _
    (Scheme.Modules.isSingleDegreeRank_singleDegreeRankOpen _ _ _)
    (singleDegreeRankOpen_relativeDualizingComplex_eq_top f hG).ge

/-- **The relative dualizing sheaf is invertible** (Stacks 0E6R): for a family with Gorenstein
fibres equidimensional of dimension one, `ω_{X/S}` is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_properFlatDualizingSheaf (hG : HasGorensteinCurveFibres f) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (properFlatDualizingSheaf f) 1 :=
  have := Stacks.RelativeAmpleAffineBase.isIso_ι_top X
  (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ 1).1
    (Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_isIso (⊤ : X.Opens).ι
      ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ 1).2
        (isSingleDegreeRank_top_relativeDualizingComplex f hG).2))

/-- **`ω_{X/S}^• = ω_{X/S}[1]`** (Stacks 0E6P): for a family with Gorenstein fibres
equidimensional of dimension one, `ω_{X/S}^•` has no cohomology outside degree `-1`. -/
theorem isZero_homology_relativeDualizingComplex (hG : HasGorensteinCurveFibres f) (j : ℤ)
    (hj : j ≠ -1) :
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    IsZero ((@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) j).obj
      (StandardModel.relativeDualizingComplex f).obj) :=
  have := Stacks.RelativeAmpleAffineBase.isIso_ι_top X
  Scheme.Modules.isZero_of_isZero_restrict_isIso (⊤ : X.Opens).ι
    ((isSingleDegreeRank_top_relativeDualizingComplex f hG).1 j hj)

/-- The pullback of `ω_{X/S}` along `h : C ⟶ X` is the dualizing sheaf of `C` over `k`, given the
base change identification of the relative dualizing complexes. -/
private theorem nonempty_pullback_properFlatDualizingSheaf_iso_of_iso
    (hG : HasGorensteinCurveFibres f) {k : Type u} [Field k] {C : Scheme.{u}} (h : C ⟶ X)
    (g : C ⟶ Spec (.of k)) [IsProper g] [CompactSpace C] [QuasiSeparatedSpace C]
    (e : (StandardModel.relativeDualizingComplex g).obj ≅
      have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      Scheme.Hom.DiagonalOpen.baseChangeComplex h
        (StandardModel.relativeDualizingComplex f).obj) :
    Nonempty ((RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom).obj
        (properFlatDualizingSheaf f) ≅ dualizingSheafOverField g) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hLE : @DerivedCategory.IsLE X.Modules _ _ (HasDerivedCategory.standard _)
      (StandardModel.relativeDualizingComplex f).obj (-1) :=
    (@DerivedCategory.isLE_iff X.Modules _ _ (HasDerivedCategory.standard _) _ (-1)).2 fun j hj =>
      isZero_homology_relativeDualizingComplex f hG j (by omega)
  exact ⟨(Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
      h.toLRSHom.toShHom (StandardModel.relativeDualizingComplex f).obj (-1) hLE).symm ≪≫
    (@DerivedCategory.homologyFunctor C.Modules _ _ (HasDerivedCategory.standard _)
      (-1)).mapIso e.symm ≪≫ homologyRelativeDualizingComplexIsoOverField g (-1)⟩

/-- **The relative dualizing sheaf restricts to the dualizing sheaf of every fibre**
(Stacks 0E6P, 0E6R: formation of `ω_{X/S}` commutes with base change, here to `Spec κ(s)`).
`ω_{X/S}^•` lies in `D^{≤ -1}`, so the degree `-1` cohomology of its derived restriction to the
fibre `h : X_s ⟶ X` is `h^*ω_{X/S}` (the top-degree base change), and `Lh^*ω_{X/S}^•` is
`ω_{X_s}^•` (Stacks 0E4P), whose degree `-1` cohomology is `ω_{X_s}` (Stacks 0BS2). -/
theorem nonempty_pullback_properFlatDualizingSheaf_iso (hG : HasGorensteinCurveFibres f) (s : S) :
    Nonempty ((RingedSpaceModuleAdjunction.modulePullback (f.fiberι s).toLRSHom.toShHom).obj
        (properFlatDualizingSheaf f) ≅
      dualizingSheafOverField (fiberToSpecOf f s)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨e⟩ := nonempty_relativeDualizingComplex_fiber_iso f s
  exact nonempty_pullback_properFlatDualizingSheaf_iso_of_iso f hG _ (fiberToSpecOf f s) e

/-- **The relative dualizing sheaf after base change to a field** (Stacks 0E6P, 0E6R: formation
of `ω_{X/S}` commutes with base change). For a cartesian square presenting `C` as
`X ×_S Spec k`, with `C` Gorenstein and equidimensional of dimension one, the pullback of
`ω_{X/S}` to `C` is the dualizing sheaf `ω_C` of Stacks 0BS2. -/
theorem nonempty_pullback_properFlatDualizingSheaf_iso_of_isPullback
    (hG : HasGorensteinCurveFibres f) {k : Type u} [Field k] {C : Scheme.{u}} {h : C ⟶ X}
    {g : C ⟶ Spec (.of k)} {c : Spec (.of k) ⟶ S} (hpb : IsPullback h g f c) [IsProper g]
    (hC : AlgebraicGeometry.IsGorenstein C ∧ TopologicalSpace.Equidimensional C ∧
      topologicalKrullDim C = 1) :
    Nonempty ((RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom).obj
        (properFlatDualizingSheaf f) ≅ dualizingSheafOverField g) := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated g
  obtain ⟨e⟩ := nonempty_relativeDualizingComplex_baseChange_iso f hpb
  exact nonempty_pullback_properFlatDualizingSheaf_iso_of_iso f hG h g e

end Family

end Stacks.Duality.CurveFibres

end

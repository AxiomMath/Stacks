module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDirectSums
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckAxioms.CountableCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.HomologyAlongTruncationColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatLocallyFree

/-!
# The derived pullback of algebraic spaces preserves `D_QCoh`: the ingredients

Let `f : X ⟶ Y` be a morphism of algebraic spaces.  Stacks 08F4 asserts that the derived
pullback `Lf^*` sends `D_QCoh(𝒪_Y)` into `D_QCoh(𝒪_X)`.

## Main results

* `isQuasicoherentOnSite_homology_smallEtaleDerivedModulePullback_singleFunctor`: `Lf^*` of a
  quasi-coherent module has quasi-coherent cohomology.
* `derivedCategoryB_smallEtaleDerivedModulePullback_obj_of_isLE`: the same for an object bounded
  above with quasi-coherent cohomology.
* `derivedCategoryB_smallEtaleDerivedModulePullback_obj_Q_truncLE`: the case of a truncation
  `τ_{≤ n} K`.
* `isQuasicoherentOnSite_colimit_nat`: a sequential colimit of quasi-coherent modules is
  quasi-coherent.

Stacks 08F4 itself is assembled from these in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedPullback.lean`.

## Implementation notes

The source reduces to the case of schemes on the small étale site, where it uses the
description of `D_QCoh` of an affine scheme by complexes of modules (Stacks 08DW); that
description is not available here for the small étale site, so the proof is intrinsic.

*A quasi-coherent module.*  Quasi-coherence is étale local, and the charts of `X` carrying an
affine chart diagram over `f` cover `X`; on such a chart `Lf^*M` restricts to `Lk^*(b^*M)` with
`b^*M` globally presented on an affine chart space (Stacks 03LV, 0D6D).  A presentation gives a
short exact sequence `0 ⟶ K ⟶ G ⟶ N ⟶ 0` with `G` free, `Lk^*G = k^*G` in degree `0`, so the
long exact cohomology sequence identifies `H^{-n}(Lk^*N)` with a kernel or a cokernel of maps of
quasi-coherent modules involving `H^{-n+1}(Lk^*K)`; induction on `n`.

*Bounded objects* follow by dévissage, since `D_QCoh` is a triangulated subcategory and `Lf^*`
is triangulated; *bounded above objects* because `Lf^*` is right t-exact, so
`Hʲ(Lf^*E) = Hʲ(Lf^*τ_{≥ j}E)`; and *arbitrary objects* because `Hʲ(Lf^*E)` is a sequential
colimit of the `Hʲ(Lf^*τ_{≤ n}E)`
(`Stacks.Cohomology.DerivedPullbackOfToposHom.prop_homology_derivedPullback_of_truncLE`) and
quasi-coherence is closed under sequential colimits.

## References

* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
* [Stacks Project, Tag 08F2](https://stacks.math.columbia.edu/tag/08F2)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] isGrothendieckAbelian_ringedToposStructureRingSheaf
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-! ### Cohomology sheaves along a distinguished triangle -/

section Triangle

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] (P : ObjectProperty C)

/-- If the middle vertex of a distinguished triangle has no cohomology in degree `j`, the
cohomology of its third vertex in degree `j` is the kernel of the map in degree `j + 1` between
the first two, so it lies in any class closed under kernels containing those. -/
private theorem prop_homology_obj₃_of_isZero_obj₂ [P.IsClosedUnderKernels]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (j k : ℤ) (hk : j + 1 = k)
    (h₂ : IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₂))
    (h₁ : P ((DerivedCategory.homologyFunctor C k).obj T.obj₁))
    (h₂' : P ((DerivedCategory.homologyFunctor C k).obj T.obj₂)) :
    P ((DerivedCategory.homologyFunctor C j).obj T.obj₃) := by
  have hmono : Mono (DerivedCategory.HomologySequence.δ T j k hk) :=
    (DerivedCategory.HomologySequence.exact₃ T hT j k hk).mono_g (h₂.eq_of_src _ _)
  exact P.prop_of_isLimit_kernelFork
    ((DerivedCategory.HomologySequence.exact₁ T hT j k hk).fIsKernel) h₁ h₂'

/-- If the first vertex of a distinguished triangle has no cohomology in degree `j + 1`, the
cohomology of its third vertex in degree `j` is the cokernel of the map in degree `j` between
the first two, and that map may be precomposed with any map surjective on `Hʲ`. -/
private theorem prop_homology_obj₃_of_isZero_obj₁ [P.IsClosedUnderCokernels]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (j k : ℤ) (hk : j + 1 = k)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C k).obj T.obj₁)) {B' : DerivedCategory C}
    (φ : B' ⟶ T.obj₁) (hφ : Epi ((DerivedCategory.homologyFunctor C j).map φ))
    (hB' : P ((DerivedCategory.homologyFunctor C j).obj B'))
    (h₂ : P ((DerivedCategory.homologyFunctor C j).obj T.obj₂)) :
    P ((DerivedCategory.homologyFunctor C j).obj T.obj₃) := by
  have hepi : Epi ((DerivedCategory.homologyFunctor C j).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT j k hk).2 (h₁.eq_of_tgt _ _)
  exact P.prop_of_isColimit_cokernelCofork
    (isCokernelEpiComp (DerivedCategory.HomologySequence.exact₂ T hT j).gIsCokernel
      ((DerivedCategory.homologyFunctor C j).map φ) rfl) hB' h₂

/-- An object of the derived category concentrated in degree `0` has no cohomology elsewhere. -/
private theorem isZero_homology_of_ne_zero (Z : DerivedCategory C) [Z.IsGE 0] [Z.IsLE 0]
    (j : ℤ) (hj : j ≠ 0) : IsZero ((DerivedCategory.homologyFunctor C j).obj Z) := by
  rcases lt_or_gt_of_ne hj with hj | hj
  · exact DerivedCategory.isZero_of_isGE Z 0 j hj
  · exact DerivedCategory.isZero_of_isLE Z 0 j hj

/-- The cohomology of an object placed in degree `0` lies in a class containing the object and
zero, closed under isomorphisms. -/
private theorem prop_homology_singleFunctor [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (X : C) (hX : P X) (j : ℤ) :
    P ((DerivedCategory.homologyFunctor C j).obj ((DerivedCategory.singleFunctor C 0).obj X)) := by
  by_cases hj : j = 0
  · subst hj
    exact P.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app X).symm hX
  · exact P.prop_of_isZero (isZero_homology_of_ne_zero _ j hj)

end Triangle


/-! ### Modules placed in degree zero -/

section Module

variable (B S hS) in
/-- Quasi-coherence of `𝒪_X`-modules, in the spelling of the derived pullback. -/
private abbrev qcoh (X : AlgebraicSpaces B S hS) :
    ObjectProperty (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (ringedToposStructureRingSheaf B S hS X)

open ZeroObject in
private instance (X : AlgebraicSpaces B S hS) : (qcoh B S hS X).ContainsZero :=
  ⟨⟨0, isZero_zero _, SheafOfModules.IsQuasicoherentOnSite.of_isZero (isZero_zero _)⟩⟩

private instance (X : AlgebraicSpaces B S hS) : (qcoh B S hS X).IsClosedUnderKernels :=
  isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS X.1 X.2

private instance (X : AlgebraicSpaces B S hS) : (qcoh B S hS X).IsClosedUnderCokernels :=
  isClosedUnderCokernels_quasicoherentSheaves B S hS X.1 X.2

/-- `Lf^*` of a flat quasi-coherent module placed in degree `0` has quasi-coherent cohomology,
vanishing outside degree `0`. -/
private theorem qcoh_homology_singleFunctor_of_isFlat (f : X ⟶ Y)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (hG : qcoh B S hS Y G)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) G) (j : ℤ) :
    qcoh B S hS X ((DerivedCategory.homologyFunctor _ j).obj
      ((smallEtaleDerivedModulePullback B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_obj_singleFunctor_iso f G 0 hflat
  refine (qcoh B S hS X).prop_of_iso ((DerivedCategory.homologyFunctor _ j).mapIso e).symm ?_
  refine prop_homology_singleFunctor _ _ ?_ j
  exact (qcoh B S hS X).prop_of_iso ((pullbackModulesIsoModulePullback B S hS f).app G).symm
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hG)

/-- `Lf^*` of a flat module placed in degree `0` has no cohomology in degree `j ≠ 0`. -/
private theorem isZero_homology_singleFunctor_of_isFlat (f : X ⟶ Y)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) G) (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ j).obj
      ((smallEtaleDerivedModulePullback B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_obj_singleFunctor_iso f G 0 hflat
  exact IsZero.of_iso (isZero_homology_of_ne_zero _ j hj)
    ((DerivedCategory.homologyFunctor _ j).mapIso e)


/-- A free `𝒪_Y`-module is flat and quasi-coherent. -/
private theorem isFlat_free_smallEtale (I : Type u) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O)
      (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS Y) I) :=
  Stacks.SheafOfModules.isFlat_free_of_anyIndex (Y := smallEtaleRingedSite B S hS Y.1 Y.2) I

private theorem qcoh_free (I : Type u) :
    qcoh B S hS Y (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS Y) I) :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ (isCartesianOnAffineCharts_free I)

/-- The short exact sequence `0 ⟶ ker π ⟶ G ⟶ N ⟶ 0` of an epimorphism `π`. -/
private theorem shortExact_kernel {Y : AlgebraicSpaces B S hS}
    {G N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (π : G ⟶ N) [Epi π] :
    (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel (ShortComplex.mk (kernel.ι π) π (kernel.condition π))
      (kernelIsKernel π)) inferInstance inferInstance

/-- `Lf^*` of a module placed in degree `0` has no cohomology in positive degrees. -/
private theorem isZero_homology_singleFunctor_of_pos (f : X ⟶ Y)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (j : ℤ) (hj : 0 < j) :
    IsZero ((DerivedCategory.homologyFunctor _ j).obj
      ((smallEtaleDerivedModulePullback B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  have := isLE_smallEtaleDerivedModulePullback_obj f ((DerivedCategory.singleFunctor _ 0).obj G) 0
    inferInstance
  exact DerivedCategory.isZero_of_isLE _ 0 j hj

/-- **The dimension shift.**  Let `N` be an `𝒪_Y`-module with a global presentation.  If the
derived pullback of every quasi-coherent module has quasi-coherent cohomology in degrees
`> -n`, then `H^{-n}(Lk^* N)` is quasi-coherent: the presentation gives a short exact sequence
`0 ⟶ K ⟶ G ⟶ N ⟶ 0` with `G` free, `Lk^* G = k^* G` sits in degree `0`, and the long exact
cohomology sequence identifies `H^{-n}(Lk^* N)` with a kernel or a cokernel of maps between
quasi-coherent modules. -/
private theorem qcoh_homology_singleFunctor_of_presentation (n : ℕ)
    (ih : ∀ m < n, ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
      (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)), qcoh B S hS Y M →
      qcoh B S hS X ((DerivedCategory.homologyFunctor _ (-(m : ℤ))).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))
    (k : X ⟶ Y) (N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hN : qcoh B S hS Y N) (P : N.Presentation) :
    qcoh B S hS X ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).obj
      ((smallEtaleDerivedModulePullback B S hS k).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))) := by
  let π := P.generators.π
  have hK : qcoh B S hS Y (kernel π) := (qcoh B S hS Y).prop_kernel π (qcoh_free _) hN
  have hS₁ := shortExact_kernel π
  let T := (smallEtaleDerivedModulePullback B S hS k).mapTriangle.obj hS₁.singleTriangle
  have hT : T ∈ distTriang _ :=
    (smallEtaleDerivedModulePullback B S hS k).map_distinguished _ hS₁.singleTriangle_distinguished
  rcases n with _ | m
  · let ρ := P.relations.π
    have hS₂ := shortExact_kernel ρ
    let T₂ := (smallEtaleDerivedModulePullback B S hS k).mapTriangle.obj hS₂.singleTriangle
    have hT₂ : T₂ ∈ distTriang _ :=
      (smallEtaleDerivedModulePullback B S hS k).map_distinguished _
        hS₂.singleTriangle_distinguished
    have hepi := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T₂ hT₂ 0 1 rfl).2
      ((isZero_homology_singleFunctor_of_pos k _ 1 one_pos).eq_of_tgt _ _)
    simp only [Nat.cast_zero, neg_zero]
    exact prop_homology_obj₃_of_isZero_obj₁ (qcoh B S hS X) T hT 0 1 rfl
      (isZero_homology_singleFunctor_of_pos k _ 1 one_pos) T₂.mor₂ hepi
      (qcoh_homology_singleFunctor_of_isFlat k _ (qcoh_free _) (isFlat_free_smallEtale _) 0)
      (qcoh_homology_singleFunctor_of_isFlat k _ (qcoh_free _) (isFlat_free_smallEtale _) 0)
  · exact prop_homology_obj₃_of_isZero_obj₂ (qcoh B S hS X) T hT (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ))
      (by push_cast; ring)
      (isZero_homology_singleFunctor_of_isFlat k _ (isFlat_free_smallEtale _) _ (by omega))
      (ih m (by omega) k _ hK)
      (qcoh_homology_singleFunctor_of_isFlat k _ (qcoh_free _) (isFlat_free_smallEtale _) _)

/-- On the chart space of a chart `W` of `X` carrying an affine chart diagram `q` over `f`, with
`V` the affine chart of `Y`, the étale restriction of `Hʲ(Lf^* M)` to `W` is `Hʲ(Lk^*(b^*M))`,
for `k` the chart map and `b` the structure morphism of `V`: étale restriction is the derived
pullback (Stacks 03LV), and the two composites around the square agree (Stacks 0D6D). -/
private def etaleModulePullbackHomologyIso (f : X ⟶ Y) (W : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1) (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ f.hom)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (j : ℤ) :
    (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).obj
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) j).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) ≅
      (DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X W))) j).obj
        ((smallEtaleDerivedModulePullback B S hS (chartSpaceMapOver B S hS q)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((modulePullback B S hS (chartToSpace B S hS Y V)).obj M))) :=
  let e := chartToSpace B S hS X W
  let he := isEtale_chartToSpace B S hS X W
  let b := chartToSpace B S hS Y V
  let hb := isEtale_chartToSpace B S hS Y V
  let k := chartSpaceMapOver B S hS q
  have hfac : e ≫ f = k ≫ b := (chartSpaceMapOver_comp_chartToSpace B S hS f q hq).symm
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X W))) j
  ((Functor.mapDerivedCategoryHomologyIso (etaleModulePullback.{u, u} B S hS e he) j).app _).symm ≪≫
    H.mapIso (((smallEtaleDerivedModulePullbackIsoEtale B S hS e he).app _).symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS e f).app _ ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS hfac).app _ ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B S hS k b).app _).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS k).mapIso
        ((smallEtaleDerivedModulePullbackIsoEtale B S hS b hb).app _ ≪≫
          ((etaleModulePullback.{u, u} B S hS b hb).mapDerivedCategorySingleFunctor 0).app M ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            ((modulePullbackIsoEtaleModulePullback B S hS b hb).app M).symm))

/-- **The derived pullback of a quasi-coherent module has quasi-coherent cohomology**: for every
morphism `f : X ⟶ Y` of algebraic spaces, every quasi-coherent `𝒪_Y`-module `M` and every `n`,
`H^{-n}(Lf^* M)` is quasi-coherent.

By induction on `n`.  Quasi-coherence is étale local on `X`, and the charts of `X` carrying an
affine chart diagram over `f` cover it; on such a chart the restriction of `H^{-n}(Lf^* M)` is
`H^{-n}(Lk^*(b^* M))` with `b^* M` globally presented on an affine chart space, which the
dimension shift handles from the inductive hypothesis. -/
theorem isQuasicoherentOnSite_homology_neg_smallEtaleDerivedModulePullback_singleFunctor (n : ℕ) :
    ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
      (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
      M.IsQuasicoherentOnSite →
      ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))).IsQuasicoherentOnSite := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y f M hM
  refine isQuasicoherentOnSite_of_coversTop_etaleModulePullback B S hS X
    (affineChartDiagramCharts B S hS f) (coversTop_affineChartDiagramCharts B S hS f) _
    fun i => ?_
  obtain ⟨-, V, q, hq, hVaff⟩ := i.2
  obtain ⟨P⟩ := nonempty_presentation_modulePullback_chartToSpace_of_isAffine B S hS Y M hM V hVaff
  exact (qcoh B S hS _).prop_of_iso
    (etaleModulePullbackHomologyIso f i.1 V q hq M (-(n : ℤ))).symm
    (qcoh_homology_singleFunctor_of_presentation n (fun m hm => ih m hm)
      (chartSpaceMapOver B S hS q) _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hM) P)

/-- **`Lf^*` of a quasi-coherent module has quasi-coherent cohomology in every degree.** -/
theorem isQuasicoherentOnSite_homology_smallEtaleDerivedModulePullback_singleFunctor
    (f : X ⟶ Y) (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hM : M.IsQuasicoherentOnSite) (j : ℤ) :
    ((DerivedCategory.homologyFunctor _ j).obj
      ((smallEtaleDerivedModulePullback B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))).IsQuasicoherentOnSite := by
  rcases le_or_gt j 0 with hj | hj
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨j.natAbs, by omega⟩
    exact isQuasicoherentOnSite_homology_neg_smallEtaleDerivedModulePullback_singleFunctor n f M hM
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (isZero_homology_singleFunctor_of_pos f M j hj)

end Module

/-! ### Bounded objects -/

section Bounded

variable (B S hS) in
/-- Having quasi-coherent cohomology, for an object of `D(𝒪_X)` in the spelling of the derived
pullback. -/
private abbrev qcohD (X : AlgebraicSpaces B S hS) :
    ObjectProperty
      (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

/-- **`Lf^*` of a bounded object with quasi-coherent cohomology has quasi-coherent cohomology**,
by dévissage along the truncation triangles: the objects whose derived pullback lies in
`D_QCoh(𝒪_X)` form a triangulated subcategory, which contains every quasi-coherent module placed
in a single degree. -/
private theorem qcohD_smallEtaleDerivedModulePullback_of_bounded (f : X ⟶ Y) (a : ℤ) (n : ℕ)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hGE : E.IsGE a) (hLE : E.IsLE (a + (n : ℤ))) (hE : qcohD B S hS Y E) :
    qcohD B S hS X ((smallEtaleDerivedModulePullback B S hS f).obj E) := by
  have : (qcohD B S hS X).IsTriangulated :=
    isTriangulated_quasicoherentDerivedCategory B S hS X.1 X.2
  have : (qcohD B S hS X).IsClosedUnderIsomorphisms :=
    derivedCategoryB_isQuasicoherentOnSite_isClosedUnderIsomorphisms B S hS X.1 X.2
  exact ((qcohD B S hS X).inverseImage
    (smallEtaleDerivedModulePullback B S hS f)).prop_of_isGE_of_isLE a n E hGE hLE fun q _ _ =>
      isQuasicoherentOnSite_homology_smallEtaleDerivedModulePullback_singleFunctor f _ (hE q)

/-- **`Lf^*` of an object bounded above with quasi-coherent cohomology has quasi-coherent
cohomology.**  `Lf^*` is right t-exact, so `Hʲ(Lf^* E) = Hʲ(Lf^* τ_{≥ j} E)`, and `τ_{≥ j} E` is
bounded. -/
theorem derivedCategoryB_smallEtaleDerivedModulePullback_obj_of_isLE (f : X ⟶ Y) (b : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hLE : E.IsLE b)
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
      ((smallEtaleDerivedModulePullback B S hS f).obj E) := by
  intro j
  let L := smallEtaleDerivedModulePullback B S hS f
  let T := L.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLTGE j).obj E)
  have hT : T ∈ distTriang _ :=
    L.map_distinguished _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished j E)
  have hT₁ : T.obj₁.IsLE (j - 1) := isLE_smallEtaleDerivedModulePullback_obj f _ (j - 1)
    (DerivedCategory.TStructure.t.isLE_truncLT_obj E j (j - 1) (by omega))
  have hiso := DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ T hT j (j - 1) hT₁ (by omega)
  have hGE : ((DerivedCategory.TStructure.t.truncGE j).obj E).IsGE j := inferInstance
  have hLE' : ((DerivedCategory.TStructure.t.truncGE j).obj E).IsLE (j + ((b - j).toNat : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_of_le _ b _ (by omega)
  have hbd := qcohD_smallEtaleDerivedModulePullback_of_bounded f j (b - j).toNat _ hGE hLE'
    (DerivedCategoryB.derivedCategoryB_truncGE_obj _
      (@WeakSerre.isWeakSerre_of_isWeakSerreClass _ _ _ _
        (quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS Y.1 Y.2)) j E hE)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (asIso ((DerivedCategory.homologyFunctor _ j).map T.mor₂)).symm (hbd j : _)

end Bounded

/-! ### Unbounded objects -/

section Unbounded

/-- A colimit of a sequence of quasi-coherent `𝒪_X`-modules is quasi-coherent: it is the
cokernel of `1 - f` on the direct sum (Stacks 093W), and quasi-coherence is closed under direct
sums and cokernels. -/
theorem isQuasicoherentOnSite_colimit_nat
    (F : ℕ ⥤ SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) [HasColimit F]
    (hF : ∀ n, (F.obj n).IsQuasicoherentOnSite) : (colimit F).IsQuasicoherentOnSite := by
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize
    (smallEtaleRingedTopos B S hS X).O
  have : HasColimitsOfShape (Discrete ℕ)
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
    Stacks.CountableCoproducts.hasColimitsOfShape_discrete_of_hasColimitsOfShape_nat
  have hsigma : qcoh B S hS X (∐ F.obj) :=
    isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX.{0, u, u} B S hS X.1 X.2
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2) _
      (coproductIsCoproduct F.obj) hF
  have := Stacks.CountableCoproducts.epi_piMap F
  exact (qcoh B S hS X).prop_of_isColimit_cokernelCofork
    (Stacks.CountableCoproducts.exact_oneSubShift_piMap F).gIsCokernel hsigma hsigma

/-- The cohomology of the truncation `τ_{≤ n} K` of a complex with quasi-coherent cohomology is
quasi-coherent. -/
theorem derivedCategoryB_Q_obj_truncLE
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      (DerivedCategory.Q.obj K))
    (n : ℤ) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      (DerivedCategory.Q.obj (K.truncLE n)) := by
  intro q
  by_cases hq : q ≤ n
  · have := K.quasiIsoAt_ιTruncLE n q hq
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (((DerivedCategory.homologyFunctorFactors _ q).app K) ≪≫
        (asIso (HomologicalComplex.homologyMap (K.ιTruncLE n) q)).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors _ q).app (K.truncLE n)).symm) (hK q)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj (K.truncLE n)) n q (by omega))

/-- `Lf^*` of the truncation `τ_{≤ n} K` of a complex with quasi-coherent cohomology has
quasi-coherent cohomology. -/
theorem derivedCategoryB_smallEtaleDerivedModulePullback_obj_Q_truncLE (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      (DerivedCategory.Q.obj K))
    (n : ℤ) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
      ((smallEtaleDerivedModulePullback B S hS f).obj (DerivedCategory.Q.obj (K.truncLE n))) :=
  derivedCategoryB_smallEtaleDerivedModulePullback_obj_of_isLE f n _ inferInstance
    (derivedCategoryB_Q_obj_truncLE K hK n)

end Unbounded

end AlgebraicGeometry.Space

end

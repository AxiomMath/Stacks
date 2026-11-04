module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOnBoundedResolutions
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreTotalComplexGeneralCoefficients
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleFreeSimplicial
import StacksCore.Tactic.StacksAttribute

/-!
# `Lπ_!` of a simplicial module is its alternating-face-map complex

Let `(C, J)` be a small site, let `O` be a sheaf of rings on it, let `π : Δ × C ⥤ C` be the
projection of Stacks 09D0 and let `Δ × C` carry the topology `K` it inherits from `(C, J)` along
`π`. A sheaf of `π^{-1}O`-modules `ℱ` on `Δ × C` *is* a simplicial sheaf of `O`-modules `ℱ_•` on
`C` (`Stacks.SimplicialModules.simplicialModuleEquivalence`), and the untagged paragraph of
Cohomology on Sites, Section 09D0 asserts that the derived lower shriek of Remark 09CY,

`Lπ_! : D(π^{-1}O) ⥤ D(O)`,

carries `ℱ` to the *associated chain complex* `s(ℱ_•)` of Simplicial, Section 14.23 — that is, to
the alternating-face-map complex of the simplicial sheaf of `O`-modules `ℱ_•`.

This file proves that, in the form

`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplexModules`.

## Why the abelian case does not give this

`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplex` is the same statement for
an abelian sheaf on `Δ × C`, and it does **not** imply this one: derived lower shriek provably
does not commute with forgetting the module structure
(`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`), so an isomorphism in `D(Ab(C))` says
nothing about `D(O)`. Everything below is therefore run again at module coefficients; what is
reused unchanged is the half of the argument that lives over `Δ` and is already stated at
arbitrary abelian coefficients, namely
`Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution` and the acyclicity of the
free simplicial objects.

## How the theorem is assembled

The proof is the one the source gives — Lemmas 21.40.2 and 21.39.7 — in five steps, each the
module-coefficient form of a step of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/DerivedProjectionMooreComplex.lean`:

1. Stacks 06XX at stage `0` produces a complex `R` with `R.IsStrictlyLE 0` whose terms are direct
   sums of the `j_{W!}(π^{-1}O)_W`, together with a quasi-isomorphism `ε : R ⟶ ℱ[0]`.
2. `StacksDraft.UnboundedLeftDerivedFunctor.leftDerivedObjIsoOfBoundedProp`, fed with the
   acyclicity of `π_!` on modules
   (`Stacks.Cohomology.DerivedLowerShriek.lowerShriekAcyclic_of_preservesCoveringPullbacks`,
   which is Lemma 21.40.2), computes `Lπ_!(R) = π_!(R)` degreewise.
3. `ε` is inverted by `DerivedCategory.Q`, so `Lπ_!(ℱ[0]) ≅ Lπ_!(R)`.
4. `Stacks.SimplicialModules.moduleLowerShriekIsoColim` rewrites `π_!` as
   `fibrewiseMod ⋙ colim`, degreewise.
5. `Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution`, at the site `Δ` with the
   tautological cosimplicial object `𝟭 Δ` and coefficients `Mod(O)`, identifies
   `colim (fibrewiseMod R)` with the extended Moore complex of `ℱ_•`. Its hypothesis `haug` is
   `Stacks.SimplicialModules.quasiIso_mooreCochainAugmentation_fibrewiseMod`.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 06XX](https://stacks.math.columbia.edu/tag/06XX)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.SimplicialModules

open Stacks.Cohomology.DerivedLowerShriek

universe w

attribute [local instance] HasDerivedCategory.standard

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  (O : Sheaf J RingCat.{w})
  [HasSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{w} (Sheaf (projectionTopology C J) AddCommGrpCat.{w})]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (idRingMap (projectionTopology C J) J (projection C) O)).IsRightAdjoint]
  [∀ V : SimplexCategory × C, (SheafOfModules.pushforward.{w} (F := Over.forget V)
    (𝟙 ((projectionRing C J O).over V) :
      (projectionRing C J O).over V ⟶ (projectionRing C J O).over V)).IsRightAdjoint]
  [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 (O.over U) : O.over U ⟶ O.over U)).IsRightAdjoint]
  [EnoughInjectives (SheafOfModules.{w} (projectionRing C J O))]
  [EnoughInjectives (SheafOfModules.{w} O)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} O)]
  [HasColimitsOfShape SimplexCategoryᵒᵖ (SheafOfModules.{w} O)]

/-- Steps 1-4 of the assembly: a bounded above `X` has a resolution `ε : R ⟶ X` by sums of
`j_{W!}(π^{-1}O)_W` such that `Lπ_!(X)` is the degreewise colimit of `R`. -/
private theorem exists_resolution_derivedProjectionLowerShriek_iso_colim (O' : Sheaf J RingCat.{w})
    [(SheafOfModules.pushforward.{w} (F := projection C)
      (idRingMap (projectionTopology C J) J (projection C) O')).IsRightAdjoint]
    [∀ V : SimplexCategory × C, (SheafOfModules.pushforward.{w} (F := Over.forget V)
      (𝟙 ((projectionRing C J O').over V) :
        (projectionRing C J O').over V ⟶ (projectionRing C J O').over V)).IsRightAdjoint]
    [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
      (𝟙 (O'.over U) : O'.over U ⟶ O'.over U)).IsRightAdjoint]
    [EnoughInjectives (SheafOfModules.{w} (projectionRing C J O'))]
    [EnoughInjectives (SheafOfModules.{w} O')]
    [HasColimitsOfShape SimplexCategoryᵒᵖ (SheafOfModules.{w} O')]
    (X : CochainComplex (SheafOfModules.{w} (projectionRing C J O')) ℤ) [X.IsStrictlyLE 0] :
    ∃ (R : CochainComplex (SheafOfModules.{w} (projectionRing C J O')) ℤ) (ε : R ⟶ X),
      R.IsStrictlyLE 0 ∧ QuasiIso ε ∧
        (∀ p, IsSumOfExtensionByZeroUnits (projectionRing C J O') (R.X p)) ∧
        Nonempty ((derivedProjectionLowerShriek C J O').obj (DerivedCategory.Q.obj X) ≅
          DerivedCategory.Q.obj
            (((colim : (SimplexCategoryᵒᵖ ⥤ SheafOfModules.{w} O') ⥤
                SheafOfModules.{w} O').mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((fibrewiseMod C J O').mapHomologicalComplex (ComplexShape.up ℤ)).obj R))) := by
  have hnatA := hasExactColimitsOfShape_nat.{w} (projectionRing C J O')
  have hnatB := hasExactColimitsOfShape_nat.{w} O'
  -- Step 1: the resolution of Stacks 06XX, read off at stage `0`.
  obtain ⟨R, f, g, hqis, hLE, hprops, -, -⟩ :=
    StacksDraft.UnboundedLeftDerivedFunctor.exists_sequence_quasiIso_truncLE
      (IsSumOfExtensionByZeroUnits (projectionRing C J O'))
      (fun _ _ => isSumOfExtensionByZeroUnits_biprod (projectionRing C J O'))
      (fun Y => exists_epi_isSumOfExtensionByZeroUnits (projectionRing C J O') Y) X
  have hXLE : CochainComplex.IsStrictlyLE X ((0 : ℕ) : ℤ) := by
    rw [Nat.cast_zero]; infer_instance
  have := hqis 0
  -- Step 2: `Lπ_!` computed on the resolution.
  have step2 :=
    StacksDraft.UnboundedLeftDerivedFunctor.leftDerivedObjIsoOfBoundedProp
      (lowerShriekModules (projectionTopology C J) J (projection C) O')
      (IsSumOfExtensionByZeroUnits (projectionRing C J O'))
      (fun _ _ => isSumOfExtensionByZeroUnits_biprod (projectionRing C J O'))
      (fun Y => exists_epi_isSumOfExtensionByZeroUnits (projectionRing C J O') Y)
      (lowerShriekAcyclic_of_preservesCoveringPullbacks (projectionTopology C J) J O'
        (projection C))
      (derivedLowerShriek (projectionTopology C J) J (projection C) O')
      (derivedLowerShriekComparison (projectionTopology C J) J (projection C) O')
      (R 0) (fun i => hprops 0 i)
  -- Step 3: `ε` moves `Lπ_!` across.
  have step3 :
      (derivedLowerShriek (projectionTopology C J) J (projection C) O').obj
          (DerivedCategory.Q.obj X) ≅
        (derivedLowerShriek (projectionTopology C J) J (projection C) O').obj
          (DerivedCategory.Q.obj (R 0)) :=
    (derivedLowerShriek (projectionTopology C J) J (projection C) O').mapIso
      (CochainComplex.derivedIsoOfQuasiIso (f 0 ≫ CochainComplex.ιTruncLE X ((0 : ℕ) : ℤ))
        inferInstance).symm
  -- Step 4: `π_!` is the colimit over `Δᵒᵖ`, degreewise.
  have step4 :
      DerivedCategory.Q.obj
          (((lowerShriekModules (projectionTopology C J) J
            (projection C) O').mapHomologicalComplex (ComplexShape.up ℤ)).obj (R 0)) ≅
        DerivedCategory.Q.obj
          (((colim : (SimplexCategoryᵒᵖ ⥤ SheafOfModules.{w} O') ⥤
                SheafOfModules.{w} O').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((fibrewiseMod C J O').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (R 0))) :=
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (moduleLowerShriekIsoColim C J O')
        (ComplexShape.up ℤ)).app (R 0))
  refine ⟨R 0, f 0 ≫ CochainComplex.ιTruncLE X ((0 : ℕ) : ℤ), ?_, inferInstance,
    fun p => hprops 0 p, ⟨step3 ≪≫ step2 ≪≫ step4⟩⟩
  simpa using hLE 0

/-- Complexes concentrated in non-positive degrees stay so under a functor preserving zero
objects. -/
private theorem isStrictlyLE_mapHomologicalComplex_obj_of_preservesZero
    {A B : Type*} [Category* A] [Category* B] [HasZeroMorphisms A] [HasZeroMorphisms B]
    (G : A ⥤ B) [G.PreservesZeroMorphisms] (X : CochainComplex A ℤ) [X.IsStrictlyLE 0] :
    CochainComplex.IsStrictlyLE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero G (CochainComplex.isZero_of_isStrictlyLE X 0 i hi)

omit [IsGrothendieckAbelian.{w} (SheafOfModules.{w} O)] in
/-- **The module-coefficient Stacks 09D0, in the form the assembly produces it.** The existence
of the isomorphism of
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplexModules`; the resolution of
Stacks 06XX is chosen inside the proof. -/
theorem nonempty_derivedProjectionLowerShriekIsoMooreComplexModules
    (F : SheafOfModules.{w} (projectionRing C J O)) :
    Nonempty
      ((derivedProjectionLowerShriek C J O).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (SheafOfModules.{w} (projectionRing C J O))
              (ComplexShape.up ℤ) 0).obj F)) ≅
        DerivedCategory.Q.obj
          ((Stacks.ChaoticSite.GeneralValued.mooreCochainComplex (𝟭 SimplexCategory)
            (SheafOfModules.{w} O)).obj ((fibrewiseMod C J O).obj F))) := by
  obtain ⟨R, ε, hRLE, hε, hprops, ⟨e⟩⟩ := exists_resolution_derivedProjectionLowerShriek_iso_colim
    C J O ((HomologicalComplex.single (SheafOfModules.{w} (projectionRing C J O))
      (ComplexShape.up ℤ) 0).obj F)
  -- Step 5: the two filtrations of the Moore double complex over `Δ`.
  have := isStrictlyLE_mapHomologicalComplex_obj_of_preservesZero (fibrewiseMod C J O) R
  have : QuasiIso (((fibrewiseMod C J O).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ε ≫
      ((HomologicalComplex.singleMapHomologicalComplex (fibrewiseMod C J O)
        (ComplexShape.up ℤ) 0).app F).hom) := by
    have := HomologicalComplex.quasiIso_map_of_preservesHomology ε (fibrewiseMod C J O)
    infer_instance
  exact ⟨e ≪≫ (Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution
      (𝟭 SimplexCategory) ((fibrewiseMod C J O).obj F)
      (((fibrewiseMod C J O).mapHomologicalComplex (ComplexShape.up ℤ)).obj R)
      (((fibrewiseMod C J O).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
        ((HomologicalComplex.singleMapHomologicalComplex (fibrewiseMod C J O)
          (ComplexShape.up ℤ) 0).app F).hom)
      (fun p => quasiIso_mooreCochainAugmentation_fibrewiseMod C J O (R.X p) (hprops p))).symm⟩

/-- **Stacks 09D0 at module coefficients.** Let `(C, J)` be a small site, let `O` be a sheaf of
rings on it and let `Δ × C` carry the topology inherited from `(C, J)` along the projection
`π : Δ × C ⥤ C`. For every sheaf of `π^{-1}O`-modules `ℱ` on `Δ × C`, the derived lower shriek of
Remark 09CY carries `ℱ` to the associated chain complex of the simplicial sheaf of `O`-modules
`ℱ_•` that `ℱ` is:

`Lπ_!(ℱ[0]) ≅ s(ℱ_•)` in `D(O)`,

where `s(ℱ_•)` is the alternating-face-map complex of `ℱ_• = fibrewiseMod ℱ`, read as a cochain
complex over `ℤ` in non-positive degrees.

This is the source's own argument, run at module coefficients: a resolution of `ℱ` by direct sums
of the `j_{W!}(π^{-1}O)_W` (Stacks 06XX) computes `Lπ_!` because `π_!` is acyclic on those
(`Stacks.Cohomology.DerivedLowerShriek.lowerShriekAcyclic_of_preservesCoveringPullbacks`, which
is Lemma 21.40.2), and the degreewise colimit over `Δᵒᵖ` of such a resolution is the Moore
complex (`Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution`, which is Lemma
21.39.7). -/
@[stacks 09D0 "the MODULE-coefficient representation: for a simplicial sheaf of O-modules ℱ_•, \
  equivalently a sheaf of π^{-1}O-modules on Δ × C, Lπ_!(ℱ_•) is represented by the associated \
  chain complex s(ℱ_•) in D(O). This is the form in which the untagged paragraph of Section \
  09D0 is used by Tag 09DH, whose triangle lives in D(ℬ); the abelian registration beside it, \
  derivedProjectionLowerShriekIsoMooreComplex, cannot reach it because derived lower shriek \
  does not commute with forgetting the module structure"]
def derivedProjectionLowerShriekIsoMooreComplexModules
    (F : SheafOfModules.{w} (projectionRing C J O)) :
    (derivedProjectionLowerShriek C J O).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (SheafOfModules.{w} (projectionRing C J O))
            (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        ((Stacks.ChaoticSite.GeneralValued.mooreCochainComplex (𝟭 SimplexCategory)
          (SheafOfModules.{w} O)).obj ((fibrewiseMod C J O).obj F)) :=
  (nonempty_derivedProjectionLowerShriekIsoMooreComplexModules C J O F).some

/-! ### The same computation for a bounded above complex of simplicial modules

The conclusion of [Stacks, Tag 09D2] is about an object of `D(A_•)`, not about a simplicial
module placed in degree zero, so a proof of it needs `Lπ_!` of a *complex*. The five steps above
compute `Lπ_!` of whatever bounded above object the resolution of Stacks 06XX is taken at; only
the last of them specialises to a single module, by rewriting the total complex of the Moore
double complex of `ℱ[0]` as the extended Moore complex of `ℱ_•`. Dropping that rewriting leaves
the computation valid for an arbitrary complex bounded above by `0`, with the total complex of
the Moore double complex as the answer. -/

omit [IsGrothendieckAbelian.{w} (SheafOfModules.{w} O)] in
/-- **The module-coefficient Stacks 09D0 for a bounded above complex, in the form the assembly
produces it.** The existence of the isomorphism of
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreBicomplexTotalModules`; the
resolution of Stacks 06XX is chosen inside the proof. -/
theorem nonempty_derivedProjectionLowerShriekIsoMooreBicomplexTotalModules
    (X : CochainComplex (SheafOfModules.{w} (projectionRing C J O)) ℤ) [X.IsStrictlyLE 0] :
    Nonempty
      ((derivedProjectionLowerShriek C J O).obj (DerivedCategory.Q.obj X) ≅
        DerivedCategory.Q.obj
          ((Stacks.ChaoticSite.GeneralValued.mooreBicomplex (𝟭 SimplexCategory)
            (((fibrewiseMod C J O).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).total
              (ComplexShape.up ℤ))) := by
  obtain ⟨R, ε, hRLE, hε, hprops, ⟨e⟩⟩ :=
    exists_resolution_derivedProjectionLowerShriek_iso_colim C J O X
  -- Step 5: the two filtrations of the Moore double complex over `Δ`.
  have := isStrictlyLE_mapHomologicalComplex_obj_of_preservesZero (fibrewiseMod C J O) R
  have := isStrictlyLE_mapHomologicalComplex_obj_of_preservesZero (fibrewiseMod C J O) X
  have := HomologicalComplex.quasiIso_map_of_preservesHomology ε (fibrewiseMod C J O)
  exact ⟨e ≪≫ (Stacks.ChaoticSite.GeneralValued.mooreBicomplexTotalQIsoColimOfResolution
    (𝟭 SimplexCategory)
    (((fibrewiseMod C J O).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)
    (((fibrewiseMod C J O).mapHomologicalComplex (ComplexShape.up ℤ)).obj R)
    (((fibrewiseMod C J O).mapHomologicalComplex (ComplexShape.up ℤ)).map ε)
    (fun p => quasiIso_mooreCochainAugmentation_fibrewiseMod C J O (R.X p) (hprops p))).symm⟩


/-- **Stacks 09D0 at module coefficients, for a bounded above complex.** Let `(C, J)` be a small
site, let `O` be a sheaf of rings on it and let `Δ × C` carry the topology inherited from `(C, J)`
along the projection `π : Δ × C ⥤ C`. For every complex `X^•` of sheaves of `π^{-1}O`-modules on
`Δ × C` which vanishes in positive degrees, the derived lower shriek of Remark 09CY is the total
complex of the Moore double complex of the simplicial sheaf of `O`-modules that `X^•` is:

`Lπ_!(X^•) ≅ Tot(Z_{X^•})` in `D(O)`,  where  `Z^{p,q} = (X^p_•)^q`.

For `X^• = ℱ[0]` the total complex is the alternating-face-map complex `s(ℱ_•)` and this is
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplexModules`. The proof is the
same five steps; what is dropped is the last rewriting, which is the only one specific to a
single module.

This is the shape in which the conclusion of [Stacks, Tag 09D2] consumes Section 09D0: that
lemma compares `Lπ_!` of an object of `D(A_•)` with `Lπ_!` of its derived base change, and after
the source's reduction to bounded above complexes both are complexes rather than single modules.
It is a strengthening of the registered statement, not a new tag, so it carries none. -/
def derivedProjectionLowerShriekIsoMooreBicomplexTotalModules
    (X : CochainComplex (SheafOfModules.{w} (projectionRing C J O)) ℤ) [X.IsStrictlyLE 0] :
    (derivedProjectionLowerShriek C J O).obj (DerivedCategory.Q.obj X) ≅
      DerivedCategory.Q.obj
        ((Stacks.ChaoticSite.GeneralValued.mooreBicomplex (𝟭 SimplexCategory)
          (((fibrewiseMod C J O).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).total
            (ComplexShape.up ℤ)) :=
  (nonempty_derivedProjectionLowerShriekIsoMooreBicomplexTotalModules C J O X).some

end Stacks.SimplicialModules

end

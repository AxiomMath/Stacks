module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackFlatPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties

/-!
# Tag 0GM7, clause (1): pullback of a derived internal hom out of a perfect object

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `K ∈ D(𝒪_Y)` perfect.  Then the
canonical map of Tag 08I3,

`Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)`,

is an isomorphism for every `M ∈ D(𝒪_Y)`.  The question is local on `Y`, and on the members of
an open covering `K` is represented by a strictly perfect complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.Cohomology.HigherDirectImage

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (h : X ⟶ Y)

/-- **Tag 0GM7, clause (1), given its strictly perfect case.**  For a morphism of ringed spaces
`h : X ⟶ Y`, a perfect `K ∈ D(𝒪_Y)` and an arbitrary `M ∈ D(𝒪_Y)`, the canonical map
`Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)` is an isomorphism, as soon as it is one at every strictly
perfect complex along every morphism of ringed spaces. -/
theorem isIso_derivedPullbackSheafHomMap_of_isPerfect_of_strictlyPerfect
    (hsp : StrictlyPerfectInvertibility.{u})
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hK : AlgebraicGeometry.RingedSpace.IsPerfect (X := Y) K)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    IsIso (derivedPullbackSheafHomMap h K M) := by
  obtain ⟨E, ⟨I, U, hU, hloc⟩, ⟨eE⟩⟩ := hK
  -- `DerivedCategory.isIso_iff` is applied as a term rather than rewritten with: the goal names
  -- the module category of `Y` at the canonical spelling
  -- `Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf` and the derived internal hom names it at
  -- the structure-sheaf spelling, and the two carry different `Abelian` instances, so the goal
  -- is not type-correct at the `implicit` transparency `rw` matches patterns at.
  refine (DerivedCategory.isIso_iff _ _).2 fun n => ?_
  refine (isIso_map_derivedPullbackSheafHomMap_iff_of_iso h _ eE M).1 ?_
  refine isIso_homologyMap_derivedPullbackSheafHomMap_of_local h n _ M fun x => ?_
  have hx : h.hom.base x ∈ iSup U := hU ▸ TopologicalSpace.Opens.mem_top _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨P, hP, f, hf⟩ := hloc i
  let P' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      (restrictToOpen Y (U i))) ℤ := P
  have hP' : StrictlyPerfect.IsStrictlyPerfect P' := hP
  let f' : P' ⟶ AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex E (U i) := f
  have hf' : QuasiIso f' := hf
  have e : (derivedPullbackFunctor (openSubspaceInclusion Y (U i))).obj (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj P' :=
    derivedPullbackOpenSubspaceQIso Y (U i) E ≪≫ (@asIso _ _ _ _ (DerivedCategory.Q.map f')
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ f').2 hf')).symm
  refine ⟨U i, hi, ?_⟩
  refine (isIso_map_derivedPullbackSheafHomMap_iff_of_iso (restrictedMorphism h (U i)) _
    e.symm _).1 ?_
  -- `Functor.map_isIso` is applied with its `IsIso` argument supplied as a term rather than left
  -- to instance search: the goal names the derived category of the restriction of `X` at the
  -- canonical `Stacks.SheafOfModules.Tensor.ringSheaf` spelling of its sheaf of rings, while
  -- `hsp` states invertibility at the spelling the derived internal hom carries, and the two are
  -- identified only at default transparency.
  exact @Functor.map_isIso _ _ _ _ _ _ (DerivedCategory.homologyFunctor _ n) _
    (hsp (restrictedMorphism h (U i)) P' hP'
      ((derivedPullbackFunctor (openSubspaceInclusion Y (U i))).obj M))

end Stacks.Cohomology.DerivedInternalHomPullback

end

module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericFreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# The derived stalk of a perfect complex is pseudo-coherent

Let `X` be a Noetherian scheme, `x` a point of `X` and `K` a perfect object of the derived
category of `𝒪_X`-modules. Then the derived stalk of `K` at `x`, the image of `K` under the
functor induced on derived categories by the exact functor
`AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x`, is a pseudo-coherent object of
the derived category of modules over the stalk of the sheaf of rings at `x`.

## Main results

* `Stacks.AlgebraicGeometry.DerivedStalk.module_finite_stalkFunctor_obj_of_isCoherent`: the stalk
  at `x` of a coherent sheaf of `𝒪_X`-modules is a finite module over the stalk of the sheaf of
  rings at `x`.
* `Stacks.AlgebraicGeometry.DerivedStalk.isPseudoCoherent_derivedStalk_of_isPerfect`: the derived
  stalk at `x` of a perfect object of `D(𝒪_X)` is pseudo-coherent.

## Implementation notes

Over a Noetherian ring, pseudo-coherence of an object of the derived category of modules is
cohomological: it says that the cohomology vanishes in all sufficiently large degrees and that
every cohomology module is finite. That is [Stacks, Tag 066E], in the library
`StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology`. Both halves are
therefore checked on the cohomology of the derived stalk, and the stalk functor is exact, so
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` identifies that cohomology with the stalk
of the cohomology of `K`. The two inputs then come from [Stacks, Tag 0FXU]: `K` has bounded
cohomology, and every cohomology sheaf of `K` is coherent.

The stalk at `x` of a coherent sheaf of modules is a finite module over the stalk ring because a
coherent sheaf is of finite type, and the germs of a finite family of local generators span the
stalk — `SheafOfModules.finite_stalk`. That statement is over the `CommRingCat`-valued stalk
`𝒪_{X,x}`, while the stalk functor on sheaves of modules takes its values in modules over the
`RingCat`-valued stalk; the two are two filtered colimits in two different categories, and
finiteness is carried from one to the other along the comparison ring isomorphism
`SemilinearStalk.commStalkRingEquiv`, which matches the two scalar actions.

Noetherianness of the `RingCat`-valued stalk is taken as a typeclass hypothesis rather than
synthesized: the instance available in the library is keyed on another spelling of the structure
sheaf, and importing it here changes which `Ring` structure instance search puts on the stalk,
which breaks the module instances the stalk functor produces.

## References

* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open StacksDraft.PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.DerivedStalk

/-- The stalk at `x` of a coherent sheaf of `𝒪_X`-modules is a finite module over the
`RingCat`-valued stalk of the sheaf of rings at `x`, the ring the stalk functor on sheaves of
modules takes its values over. -/
theorem module_finite_stalkFunctor_obj_of_isCoherent (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (hF : F.IsCoherent) (x : X) :
    Module.Finite (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x))
      ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj F) := by
  have : F.IsFiniteType := hF.isFiniteType
  let _ : Module (ToType (X.presheaf.stalk x))
      ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj F) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  exact IrreducibleDevissage.module_finite_of_ringEquiv
    (SemilinearStalk.commStalkRingEquiv X.presheaf x)
    (fun a m => SemilinearStalk.comm_smul_eq X.presheaf x F.val a m)
    (SheafOfModules.finite_stalk X.sheaf F x)

/-- **The derived stalk of a perfect complex on a Noetherian scheme is pseudo-coherent.** For `K`
a perfect object of the derived category of `𝒪_X`-modules, the derived stalk of `K` at `x` is a
pseudo-coherent object of the derived category of modules over the stalk ring at `x`. -/
theorem isPseudoCoherent_derivedStalk_of_isPerfect (X : Scheme.{u}) [IsNoetherian X] (x : X)
    [IsNoetherianRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x))]
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) :
    IsPseudoCoherent
      ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj K) := by
  have hbc := PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK
  have hiso : ∀ n : ℤ,
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (ToType (TopCat.Presheaf.stalk X.ringCatSheaf.obj x))) n).obj
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj K) ≅
      (SheafOfModules.stalkFunctor X.ringCatSheaf x).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).obj K) :=
    fun n => ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategoryHomologyIso n).app K
  refine (pseudoCoherent_iff_boundedAbove_finite_homology
    ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj K) 0
    (ToType (TopCat.Presheaf.stalk X.ringCatSheaf.obj x))).2.1.2 ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := hbc.1.2
    exact ⟨b, fun i hi =>
      (Functor.map_isZero (SheafOfModules.stalkFunctor X.ringCatSheaf x) (hb i hi)).of_iso
        (hiso i)⟩
  · intro i
    have hcoh : ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
        K).IsCoherent := hbc.2 i
    have := module_finite_stalkFunctor_obj_of_isCoherent X _ hcoh x
    exact Module.Finite.equiv (hiso i).symm.toLinearEquiv

end Stacks.AlgebraicGeometry.DerivedStalk

end

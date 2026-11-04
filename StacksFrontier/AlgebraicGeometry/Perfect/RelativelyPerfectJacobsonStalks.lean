module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectThickening

/-!
# The derived fibre of a stalk of an object whose restriction to a closed fibre is bounded

Consider a cartesian square of schemes with `i : X ⟶ X'`, `f : X ⟶ Y`, `f' : X' ⟶ Y'` and
`j : Y ⟶ Y'`, in which `j` is a closed immersion and `f'` is flat. Let `E'` be an object of
`D(𝒪_{X'})` and `x` a point of `X`. If the stalk at `x` of the derived restriction `Li^*E'`, read
over `𝒪_{Y, f x}`, has Tor amplitude in `[a, b]`, then the derived base change along
`𝒪_{Y', j (f x)} ⟶ 𝒪_{Y, f x}` of the stalk of `E'` at `i x`, read over `𝒪_{Y', j (f x)}`, has Tor
amplitude in `[a, b]` over `𝒪_{Y, f x}`.

## Main results

* `Stacks.Thickenings.hasTorAmplitudeCanonical_derivedExtensionScalars_restrictScalars`: the
  ring-level statement, for a pushout square of rings whose upper leg is flat.
* `Stacks.Thickenings.hasTorAmplitudeCanonical_derivedFibre_derivedStalk_of_isPullback`: the
  statement above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open StrictlyPerfect

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Thickenings

/-- A flat `R`-algebra `A` is Tor independent from every `R`-algebra `B`. -/
private alias torIndependent_of_flat_left' := torIndependent_of_flat_left

/-- **Tor amplitude of a derived base change, from that of the base change of the algebra.** Let
`A'` be a flat `R'`-algebra, `R` an `R'`-algebra and `A = A' ⊗_{R'} R`, presented as a pushout
square. If the derived extension of scalars of `K' ∈ D(A')` to `A`, read over `R`, has Tor
amplitude in `[a, b]`, then so has the derived extension of scalars along `R' → R` of `K'` read
over `R'`.

The two are isomorphic by Stacks 065Z, the comparison being invertible because `A'` is flat over
`R'`, hence Tor independent from `R` (Stacks 0661). -/
public theorem hasTorAmplitudeCanonical_derivedExtensionScalars_restrictScalars
    {R' A' R A : Type u} [CommRing R'] [CommRing A'] [CommRing R] [CommRing A]
    [Algebra R' A'] [Algebra R' R] [Algebra R' A] [Algebra A' A] [Algebra R A]
    [IsScalarTower R' A' A] [IsScalarTower R' R A] [Algebra.IsPushout R' A' R A]
    [Module.Flat R' A']
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (K : DerivedCategory (ModuleCat.{u} A))
    (eK : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A' A)).functor.obj K' ≅ K)
    (a b : ℤ)
    (hK : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) a b) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R' R)).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K')) a b := by
  let Dbase := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R' R)
  let Dtop := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A' A)
  let sq : (algebraMap A' A).comp (algebraMap R' A') =
      (algebraMap R A).comp (algebraMap R' R) :=
    (IsScalarTower.algebraMap_eq R' A' A).symm.trans (IsScalarTower.algebraMap_eq R' R A)
  let cmp :=
    @RingTheory.TorIndependence.derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1,
      u + 1}
    R' A' R A _ _ _ _ _ _ _ _
    (algebraMap R' A') (algebraMap R' R) (algebraMap A' A) (algebraMap R A)
    sq Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
    Dbase.isLeftDerived Dtop.isLeftDerived
  have hcmp : IsIso cmp.2.1 :=
    @RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u,
      u, u + 1, u + 1, u + 1, u + 1}
    R' A' R A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    torIndependent_of_flat_left' Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
    Dbase.isLeftDerived Dtop.isLeftDerived
  have hcmpK : IsIso (cmp.2.1.app K') := by
    have : IsIso cmp.2.1 := hcmp
    infer_instance
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    (asIso (cmp.2.1.app K') ≪≫
      (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.mapIso eK).symm a b hK

/-- **The derived fibre of a stalk, bounded from the closed fibre.** Consider a cartesian diagram
of schemes with `i : X ⟶ X'`, `f : X ⟶ Y`, `f' : X' ⟶ Y'` and `j : Y ⟶ Y'`, with `j` a closed
immersion and `f'` flat. Let `E'` be an object of `D(𝒪_{X'})` and let `x` be a point of `X`. If
the stalk of `Li^*E'` at `x`, read over the local ring `𝒪_{Y, f x}`, has Tor amplitude in
`[a, b]`, then the derived extension of scalars along `𝒪_{Y', j (f x)} ⟶ 𝒪_{Y, f x}` of the stalk
of `E'` at `i x`, read over `𝒪_{Y', j (f x)}`, has Tor amplitude in `[a, b]` over `𝒪_{Y, f x}`.

The four local rings form a pushout square because `j` is a closed immersion, `𝒪_{X', i x}` is
flat over `𝒪_{Y', j (f x)}` because `f'` is flat, and the stalk of a derived pullback is the
derived extension of scalars along the stalk map. -/
public theorem hasTorAmplitudeCanonical_derivedFibre_derivedStalk_of_isPullback
    {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    (hpb : IsPullback i f f' j) [IsClosedImmersion j] [Flat f']
    (x : X) (hpt : j.base (f.base x) = f'.base (i.base x))
    (E' : DerivedCategory X'.Modules) (a b : ℤ)
    (hE : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical (Y.presheaf.stalk (f.base x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.obj
        ((AlgebraicGeometry.derivedStalkFunctor x).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            i.toLRSHom.toShHom).obj E'))) a b) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical (Y.presheaf.stalk (f.base x))
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (j.stalkMap (f.base x)).hom).functor.obj
        ((ModuleCat.restrictScalars
            ((Y'.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫
              f'.stalkMap (i.base x)).hom).mapDerivedCategory.obj
          ((AlgebraicGeometry.derivedStalkFunctor (i.base x)).obj E'))) a b := by
  let : Algebra (Y'.presheaf.stalk (j.base (f.base x))) (Y.presheaf.stalk (f.base x)) :=
    (j.stalkMap (f.base x)).hom.toAlgebra
  let : Algebra (Y'.presheaf.stalk (j.base (f.base x))) (X'.presheaf.stalk (i.base x)) :=
    ((Y'.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫
      f'.stalkMap (i.base x)).hom.toAlgebra
  let : Algebra (Y'.presheaf.stalk (j.base (f.base x))) (X.presheaf.stalk x) :=
    ((Y'.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f'.stalkMap (i.base x) ≫
      i.stalkMap x).hom.toAlgebra
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (X'.presheaf.stalk (i.base x)) (X.presheaf.stalk x) :=
    (i.stalkMap x).hom.toAlgebra
  have htower₁ : IsScalarTower (Y'.presheaf.stalk (j.base (f.base x)))
      (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        ← Stacks.Cohomology.StalkPushout.stalkMap_comm_of_isPullback hpb x hpt])
  have htower₂ : IsScalarTower (Y'.presheaf.stalk (j.base (f.base x)))
      (X'.presheaf.stalk (i.base x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Category.assoc])
  have hpush : Algebra.IsPushout (Y'.presheaf.stalk (j.base (f.base x)))
      (X'.presheaf.stalk (i.base x)) (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (Stacks.Cohomology.StalkPushout.isPushout_stalk_of_isPullback hpb x hpt
      (RingHom.algebraMap_toAlgebra _) (RingHom.algebraMap_toAlgebra _)
      (RingHom.algebraMap_toAlgebra _)).symm
  have hflat : Module.Flat (Y'.presheaf.stalk (j.base (f.base x)))
      (X'.presheaf.stalk (i.base x)) := by
    have hcong : Function.Bijective
        (Y'.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom :=
      (ConcreteCategory.isIso_iff_bijective
        (Y'.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom).mp inferInstance
    have : ((Y'.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫
        f'.stalkMap (i.base x)).hom.Flat :=
      RingHom.Flat.comp (RingHom.Flat.of_bijective hcong)
        (AlgebraicGeometry.Flat.stalkMap f' (i.base x))
    exact this
  have halg : algebraMap (X'.presheaf.stalk (i.base x)) (X.presheaf.stalk x) =
      (i.stalkMap x).hom := RingHom.algebraMap_toAlgebra _
  exact hasTorAmplitudeCanonical_derivedExtensionScalars_restrictScalars
    ((AlgebraicGeometry.derivedStalkFunctor (i.base x)).obj E') _
    ((eqToIso (congrArg (fun φ : X'.presheaf.stalk (i.base x) →+* X.presheaf.stalk x =>
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        φ).functor.obj ((AlgebraicGeometry.derivedStalkFunctor (i.base x)).obj E'))
      halg)).trans ((AlgebraicGeometry.derivedPullbackStalkIso i x).app E').symm) a b hE

end Stacks.Thickenings

end

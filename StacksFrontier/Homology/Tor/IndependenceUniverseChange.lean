module

public import StacksFrontier.Homology.Tor.Independence

/-!
# Tor independence across a change of universe

`RingTheory.TorIndependence.TorIndependent` is stated for rings in three independent universes,
but it is *defined* by lifting all three into their maximum, so two presentations of the same
three rings in different universes are not literally the same statement.  Stacks 0FXF,
`RingTheory.TorIndependence.torIndependent_tensorProduct_of_flat`, moves Tor independence
*upward*: along the flat map `R → ULift R` it turns Tor independence over `R` into Tor
independence over `ULift R`.  This file provides the opposite direction, which no flat base
change gives: Tor independence of three rings in a larger universe descends to Tor independence
of three isomorphic rings in a smaller one.

The need for it is the comparison of conditions (1) and (4) of Stacks 08IQ.  The ordinary local
rings of a scheme live in the universe `u` of the scheme, while the étale local rings of an
algebraic space at a geometric point live in `u + 1`, the universe of the category of étale
neighbourhoods they are a colimit over; `AlgebraicGeometry.Space.chartStrictHenselizationEquiv`
is a ring isomorphism between the two, and transporting Tor independence along it is a change of
universe.

## Main results

* `RingTheory.TorIndependence.torIndependent_congr_universe`: Tor independence transports along
  ring isomorphisms of the base and of the two algebras which may raise the universe.

## Implementation notes

The comparison is the one the universe-equal reformulations of Tor independence are proved by:
raising a module along `ModuleCat.uliftFunctor` and restricting scalars along `ULift.ringEquiv`
is additive, fully faithful, exact and projective-preserving, so it carries a projective
resolution to a projective resolution, and it commutes with the tensor product by
`TensorProduct.AlgebraTensorModule.uliftEquiv`.  Hence it carries `Tor` to `Tor`, and a fully
faithful additive functor reflects zero objects.

The ring isomorphisms are allowed to raise the universe by stating the larger side over
`Type (max u v)`; at `v := u + 1` that is `Type (u + 1)`, which is the case the comparison of
Stacks 08IQ needs.

## References

* [Stacks Project, Tag 0660](https://stacks.math.columbia.edu/tag/0660)
* [Stacks Project, Tag 0FXF](https://stacks.math.columbia.edu/tag/0FXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open scoped TensorProduct

namespace RingTheory.TorIndependence

universe uR uA

attribute [local instance] ULift.algebra'
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Raising a module to a larger universe and reading it over the lifted ring. -/
private def raiseModules (R : Type uR) [CommRing R] :
    ModuleCat.{uR} R ⥤ ModuleCat.{max uR uA} (ULift.{uA} R) :=
  ModuleCat.uliftFunctor.{uA} R ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom

private instance {R : Type uR} [CommRing R] : (raiseModules.{uR, uA} R).Additive := by
  unfold raiseModules
  infer_instance

private instance {R : Type uR} [CommRing R] : (raiseModules.{uR, uA} R).Full := by
  unfold raiseModules
  infer_instance

private instance {R : Type uR} [CommRing R] : (raiseModules.{uR, uA} R).Faithful := by
  unfold raiseModules
  infer_instance

private instance {R : Type uR} [CommRing R] :
    (raiseModules.{uR, uA} R).PreservesProjectiveObjects := by
  unfold raiseModules
  infer_instance

private instance {R : Type uR} [CommRing R] :
    PreservesFiniteLimits (raiseModules.{uR, uA} R) := by
  unfold raiseModules
  apply comp_preservesFiniteLimits

private instance {R : Type uR} [CommRing R] :
    PreservesFiniteColimits (raiseModules.{uR, uA} R) := by
  unfold raiseModules
  apply comp_preservesFiniteColimits

/-- Raising modules commutes with the tensor product. -/
private def uliftTensorIso {R : Type uR} [CommRing R] (M N : ModuleCat.{uR} R) :
    (raiseModules.{uR, uA} R).obj M ⊗ (raiseModules.{uR, uA} R).obj N ≅
      (raiseModules.{uR, uA} R).obj (M ⊗ N) :=
  LinearEquiv.toModuleIso
    (TensorProduct.AlgebraTensorModule.uliftEquiv R (ULift.{uA} R) M N).symm

/-- The tensor comparison for raised modules is natural in the second module. -/
private def uliftTensorNatIso {R : Type uR} [CommRing R] (M : ModuleCat.{uR} R) :
    raiseModules.{uR, uA} R ⋙ tensorLeft ((raiseModules.{uR, uA} R).obj M) ≅
      tensorLeft M ⋙ raiseModules.{uR, uA} R :=
  NatIso.ofComponents (uliftTensorIso M) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

/-- Raising modules carries `Tor` to `Tor`: it takes a projective resolution to a projective
resolution and commutes with the tensor product. -/
private def torUliftIso {R : Type uR} [CommRing R] (M N : ModuleCat.{uR} R) (i : ℕ) :
    ((Tor (ModuleCat.{max uR uA} (ULift.{uA} R)) i).obj
      ((raiseModules.{uR, uA} R).obj M)).obj ((raiseModules.{uR, uA} R).obj N) ≅
      (raiseModules.{uR, uA} R).obj (((Tor (ModuleCat.{uR} R) i).obj M).obj N) := by
  let F := raiseModules.{uR, uA} R
  let P := projectiveResolution N
  let K := ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  exact ((F.mapProjectiveResolution P).isoLeftDerivedObj (tensorLeft (F.obj M)) i) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat (ULift.{uA} R))
      (ComplexShape.down ℕ) i).mapIso
      ((NatIso.mapHomologicalComplex (uliftTensorNatIso M) (ComplexShape.down ℕ)).app
        P.complex) ≪≫
    ((K.sc i).mapHomologyIso F) ≪≫
    F.mapIso (P.isoLeftDerivedObj (tensorLeft M) i).symm

/-- Vanishing of `Tor` is unchanged by raising the universe and transporting along a ring
isomorphism onto the lifted ring. -/
private theorem isZero_tor_changeUniverse {R : Type uR} [CommRing R]
    (M N : ModuleCat.{uR} R) (T : Type (max uR uA)) [CommRing T]
    (P Q : ModuleCat.{max uR uA} T) (e : T ≃+* ULift.{uA} R)
    (eM : P ≅ (ModuleCat.restrictScalars e.toRingHom).obj ((raiseModules.{uR, uA} R).obj M))
    (eN : Q ≅ (ModuleCat.restrictScalars e.toRingHom).obj ((raiseModules.{uR, uA} R).obj N))
    (i : ℕ) :
    IsZero (((Tor (ModuleCat T) i).obj P).obj Q) ↔
      IsZero (((Tor (ModuleCat R) i).obj M).obj N) := by
  let F := raiseModules.{uR, uA} R
  let G := ModuleCat.restrictScalars e.toRingHom
  let et : ((Tor (ModuleCat T) i).obj P).obj Q ≅
      G.obj (((Tor (ModuleCat (ULift.{uA} R)) i).obj (F.obj M)).obj (F.obj N)) :=
    (((Tor (ModuleCat T) i).mapIso eM).app Q) ≪≫
      ((Tor (ModuleCat T) i).obj _).mapIso eN ≪≫
      torRestrictIso e (F.obj M) (F.obj N) i
  constructor
  · intro h
    have hG := et.isZero_iff.mp h
    have hu : IsZero (((Tor (ModuleCat (ULift.{uA} R)) i).obj
        (F.obj M)).obj (F.obj N)) := IsZero.of_full_of_faithful_of_isZero G _ hG
    have hF := (torUliftIso M N i).isZero_iff.mp hu
    exact IsZero.of_full_of_faithful_of_isZero F _ hF
  · intro h
    apply et.isZero_iff.mpr
    apply G.map_isZero
    apply (torUliftIso M N i).isZero_iff.mpr
    exact F.map_isZero h

/-- An algebra over `R'` matched with an algebra over `R` by compatible ring isomorphisms is
isomorphic to the raised module, read over `R'`. -/
private def moduleIsoRaise {R A : Type uR} {R' A' : Type (max uR uA)}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R' A']
    (eR : R ≃+* R') (eA : A ≃+* A')
    (hA : ∀ r, eA (algebraMap R A r) = algebraMap R' A' (eR r)) :
    ModuleCat.of R' A' ≅
      (ModuleCat.restrictScalars (eR.symm.trans ULift.ringEquiv.symm).toRingHom).obj
        ((raiseModules.{uR, uA} R).obj (ModuleCat.of R A)) :=
  LinearEquiv.toModuleIso (show A' ≃ₗ[R'] ((ModuleCat.restrictScalars
      (eR.symm.trans ULift.ringEquiv.symm).toRingHom).obj
        ((raiseModules.{uR, uA} R).obj (ModuleCat.of R A))) from
    { toFun := fun a => ULift.up (eA.symm a)
      invFun := fun a => eA a.down
      left_inv := fun a => by simp
      right_inv := fun a => by refine ULift.ext ?_; simp
      map_add' := fun a a' => ULift.ext (map_add eA.symm a a')
      map_smul' := fun r' a => by
        refine ULift.ext ?_
        change eA.symm (r' • a) = eR.symm r' • eA.symm a
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        refine congrArg (· * eA.symm a) ?_
        refine eA.injective ?_
        rw [eA.apply_symm_apply, hA, eR.apply_symm_apply] })

/-- **Tor independence descends along a universe-raising isomorphism.**  Let `R`, `A`, `B` be a
ring and two algebras over it in one universe and let `R'`, `A'`, `B'` be the same data in a
possibly larger one, matched by ring isomorphisms compatible with the two structure maps.  Then
`A'` and `B'` are Tor independent over `R'` exactly when `A` and `B` are Tor independent
over `R`.

Stacks 0FXF gives the direction that raises the universe, as a flat base change along
`R → ULift R`; the direction that lowers it is not a base change, and is the comparison
`RingTheory.TorIndependence.isZero_tor_changeUniverse` of the two `Tor` functors. -/
theorem torIndependent_congr_universe {R A B : Type uR} {R' A' B' : Type (max uR uA)}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']
    (eR : R ≃+* R') (eA : A ≃+* A') (eB : B ≃+* B')
    (hA : ∀ r, eA (algebraMap R A r) = algebraMap R' A' (eR r))
    (hB : ∀ r, eB (algebraMap R B r) = algebraMap R' B' (eR r)) :
    TorIndependent R' A' B' ↔ TorIndependent R A B := by
  rw [torIndependent_iff_isZero_tor, torIndependent_iff_isZero_tor]
  exact forall_congr' fun i => imp_congr_right fun _ =>
    isZero_tor_changeUniverse (ModuleCat.of R A) (ModuleCat.of R B) R'
      (ModuleCat.of R' A') (ModuleCat.of R' B') (eR.symm.trans ULift.ringEquiv.symm)
      (moduleIsoRaise eR eA hA) (moduleIsoRaise eR eB hB) i

end RingTheory.TorIndependence

end

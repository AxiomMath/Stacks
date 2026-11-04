module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesHomEq
public import StacksFrontier.Homology.TorAmplitude.FlatSquareDescent
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange
import all StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMap

/-!
# Relative Tor amplitude across the geometric stalks of a cartesian square

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over a scheme `S` with `g` flat, and let `x̄'` be a
geometric point of `X'`, with images `x̄` in `X`, `ȳ'` in `Y'` and `ȳ` in `Y`.  The geometric
stalks of the four structure sheaves form a commutative square of rings

```
𝒪_{X,x̄} ---c---> 𝒪_{X',x̄'}
   ^                 ^
   σ                 e
   |                 |
𝒪_{Y,ȳ} ---b---> 𝒪_{Y',ȳ'}
```

whose arrows are the fibres of the structure maps (`AlgebraicGeometry.Space.stalkStructureMap`
and `AlgebraicGeometry.Space.geometricBaseStalkMap`).  This file proves that for a complex `K` of
`𝒪_{X,x̄}`-modules, `K` has Tor amplitude in `[a, b]` over `𝒪_{Y,ȳ}` if and only if
`K ⊗_{𝒪_{X,x̄}} 𝒪_{X',x̄'}` has Tor amplitude in `[a, b]` over `𝒪_{Y',ȳ'}`, which is the content
of Stacks 0DL2 at a geometric point.

## Main results

* `AlgebraicGeometry.Space.stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap`: the fibre
  of the structure map is the homomorphism along which Stacks 05V5 extends scalars.
* `AlgebraicGeometry.Space.flat_stalkStructureMap` and
  `AlgebraicGeometry.Space.faithfullyFlat_stalkStructureMap`: for a flat morphism the fibre of
  the structure map is flat, and, being local, faithfully flat.
* `AlgebraicGeometry.Space.cartesian_geometricStalk_tensor_flat`: `𝒪_{X',x̄'}` is flat over
  `𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}`, the cartesian input of Stacks 0DKD transported from the étale
  local rings to the geometric stalks.
* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_geometricStalk_baseChange`: the bound passes
  from `K` to `K ⊗ 𝒪_{X',x̄'}` (Stacks 0DKD (1) at a geometric point, for flat `g`).
* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_geometricStalk_of_baseChange`: the bound
  descends from `K ⊗ 𝒪_{X',x̄'}` to `K`.

## Implementation notes

The étale local rings of Stacks 04KG live one universe above the module categories that the
stalks of sheaves of modules on the small étale site take values in, so everything is stated at
the geometric stalk rings `AlgebraicGeometry.Space.geometricStalkRing`, which are in the universe
of the modules.  The geometric facts proved at the étale local rings are carried over along the
comparisons `AlgebraicGeometry.Space.pointStalkRingEquiv` of Stacks 05VQ; the two compatibilities
used for that are the private lemmas of `GeometricStalkCohomologyMap`, reached by `import all`.

The forward direction is the Tor-independent flat base change of
`AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_torIndependent_flatBaseChange`
(Stacks 0661 and 066L), applied to a K-flat resolution; `g` being flat, the two corners over
`𝒪_{Y,ȳ}` are Tor independent and `c` is flat, so the resolution can be removed on both sides.
The descent direction is
`StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_of_flatSquare`: `b` is flat
and `c` is flat and local, hence faithfully flat.

## References

* [Stacks Project, Tag 0DL2](https://stacks.math.columbia.edu/tag/0DL2)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Space

universe u

section StructureMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- The fibre at `x̄` of the structure map of `f` is the homomorphism of stalk rings along which
Stacks 05V5 computes the stalk of a pullback of modules: both are the canonical homomorphism of
étale local rings of Stacks 04NG after transport along the comparisons of Stacks 05VQ. -/
theorem stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap :
    (stalkStructureMap B S hS f x).hom = smallEtaleStalkPullbackRingMap B S hS f x := by
  refine RingHom.ext fun z => (pointStalkRingEquiv B S hS X x).injective ?_
  obtain ⟨w, rfl⟩ := (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm.surjective z
  exact RingHom.congr_fun ((stalkStructureMapAsEtaleLocalRingMap_eq B S hS f x).trans
    (smallEtaleStalkPullbackEtaleLocalRingMap_eq B S hS f x).symm) w

/-- The fibre of the structure map of a flat morphism of algebraic spaces at a geometric point is
flat. -/
theorem flat_stalkStructureMap (hf : IsFlat B S hS f.hom) :
    (stalkStructureMap B S hS f x).hom.Flat := by
  rw [stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap]
  exact flat_smallEtaleStalkPullbackRingMap B S hS f hf x

/-- The homomorphism of stalk rings of Stacks 05V5 for the morphism of ringed topoi that the
derived pullback derives is the one for the morphism of small étale ringed topoi of Stacks 03G8:
the two readings of the morphism as a four-field datum agree. -/
theorem stalkRingMap_toModulesHom_eq :
    Stacks.Sheaves.StalkPullback.stalkRingMap (smallEtaleRingedToposHom B S hS f).toModulesHom
      (etaleSitePoint B S hS X.1 x X.2)
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
      (smallEtaleInverseImageFiberIso B S hS f x) =
    smallEtaleStalkPullbackRingMap B S hS f x := by
  unfold smallEtaleStalkPullbackRingMap smallEtaleRingedToposModulesHom
  congr 1
  exact (RingedToposHom.toRingedToposModulesHom_eq_toModulesHom
    (smallEtaleRingedToposHom B S hS f)).symm

end StructureMap

/-- Flatness of a ring over a tensor product, through a homomorphism restricting to two given
maps on the factors, transports along isomorphisms of the four rings compatible with all the
maps. -/
theorem exists_flat_tensorLift_of_ringEquiv
    {R A B C R' A' B' C' : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [CommRing R'] [CommRing A'] [CommRing B'] [CommRing C']
    (σ : R →+* A) (b : R →+* B) (c : A →+* C) (e : B →+* C)
    (σ' : R' →+* A') (b' : R' →+* B') (c' : A' →+* C') (e' : B' →+* C')
    (eR : R ≃+* R') (eA : A ≃+* A') (eB : B ≃+* B') (eC : C ≃+* C')
    (hσ : ∀ r, eA (σ r) = σ' (eR r)) (hb : ∀ r, eB (b r) = b' (eR r))
    (hc : ∀ a, eC (c a) = c' (eA a)) (he : ∀ y, eC (e y) = e' (eB y))
    (h : letI := σ'.toAlgebra; letI := b'.toAlgebra;
      ∃ φ' : A' ⊗[R'] B' →+* C', φ'.comp Algebra.TensorProduct.includeLeftRingHom = c' ∧
        φ'.comp Algebra.TensorProduct.includeRight.toRingHom = e' ∧ φ'.Flat) :
    letI := σ.toAlgebra; letI := b.toAlgebra;
    ∃ φ : A ⊗[R] B →+* C, φ.comp Algebra.TensorProduct.includeLeftRingHom = c ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom = e ∧ φ.Flat := by
  let := σ.toAlgebra
  let := b.toAlgebra
  let := σ'.toAlgebra
  let := b'.toAlgebra
  obtain ⟨φ', hl, hr, hflat⟩ := h
  let τ : A ⊗[R] B ≃+* A' ⊗[R'] B' := tensorRingCongr eR eA eB hσ hb
  refine ⟨eC.symm.toRingHom.comp (φ'.comp τ.toRingHom), ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    change eC.symm (φ' (eA a ⊗ₜ[R'] eB 1)) = c a
    rw [map_one, RingEquiv.symm_apply_eq]
    exact (RingHom.congr_fun hl (eA a)).trans (hc a).symm
  · refine RingHom.ext fun y => ?_
    change eC.symm (φ' (eA 1 ⊗ₜ[R'] eB y)) = e y
    rw [map_one, RingEquiv.symm_apply_eq]
    exact (RingHom.congr_fun hr (eB y)).trans (he y).symm
  · exact RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective τ.bijective) hflat)
      (RingHom.Flat.of_bijective eC.symm.bijective)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X' X Y' Y : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y)

/-- The cartesian input of Stacks 0DKD read at the geometric stalk rings: for a cartesian square
of algebraic spaces and a geometric point `x̄'` of the upper-left corner, the stalk
`𝒪_{X',x̄'}` is flat over `𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}` through a homomorphism restricting to
the two fibre maps of the structure maps. -/
theorem cartesian_geometricStalk_tensor_flat (hpb : IsPullback g' f' f g)
    (x' : GeometricPoint B S hS X'.1) :
    letI := (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom.toAlgebra
    letI := (geometricBaseStalkMap B S hS f g f' g' hpb.w x').hom.toAlgebra
    ∃ φ : (geometricStalkRing B S hS (geometricPointMap g'.hom x')) ⊗[
        geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x'))]
        (geometricStalkRing B S hS (geometricPointMap f'.hom x')) →+*
        geometricStalkRing B S hS x',
      φ.comp Algebra.TensorProduct.includeLeftRingHom = (stalkStructureMap B S hS g' x').hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        (stalkStructureMap B S hS f' x').hom ∧ φ.Flat := by
  have h : geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
    geometricPointMap_square B S hS f g f' g' hpb.w x'
  refine exists_flat_tensorLift_of_ringEquiv _ _ _ _
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x'))
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫
      CommRingCat.ofHom (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom)
    (etaleLocalRingMap X'.2 g'.hom x') (etaleLocalRingMap X'.2 f'.hom x')
    (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom (geometricPointMap g'.hom x')))
    (pointStalkRingEquiv B S hS X (geometricPointMap g'.hom x'))
    (pointStalkRingEquiv B S hS Y' (geometricPointMap f'.hom x'))
    (pointStalkRingEquiv B S hS X' x')
    (fun r => pointStalkRingEquiv_stalkStructureMap B S hS f _ r) (fun r => ?_)
    (fun r => pointStalkRingEquiv_stalkStructureMap B S hS g' x' r)
    (fun r => pointStalkRingEquiv_stalkStructureMap B S hS f' x' r)
    (cartesian_etaleStalk_tensor_flat B S hS g' f' f g hpb x')
  exact (pointStalkRingEquiv_stalkStructureMap B S hS g _ _).trans
    (congrArg (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))
      (pointStalkRingEquiv_eqToHom B S hS h r))

open StacksDraft.TorAmplitude in
/-- The base stalk map of a commutative square is flat when the lower edge is. -/
theorem flat_geometricBaseStalkMap (w : g' ≫ f = f' ≫ g) (hg : IsFlat B S hS g.hom)
    (x' : GeometricPoint B S hS X'.1) :
    (geometricBaseStalkMap B S hS f g f' g' w x').hom.Flat := by
  rw [geometricBaseStalkMap, CommRingCat.hom_comp]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (eqToIso (congrArg (fun z : GeometricPoint B S hS Y.1 =>
        geometricStalkRing B S hS (X := Y) z)
        (geometricPointMap_square B S hS f g f' g' w x'))).commRingCatIsoToRingEquiv.bijective)
    (flat_stalkStructureMap B S hS g _ hg)

/-- The fibre of the structure map of a flat morphism of algebraic spaces at a geometric point is
faithfully flat: it is flat, and a local homomorphism of local rings. -/
theorem faithfullyFlat_stalkStructureMap {Z W : AlgebraicSpaces B S hS} (h : Z ⟶ W)
    (hh : IsFlat B S hS h.hom) (z : GeometricPoint B S hS Z.1) :
    (stalkStructureMap B S hS h z).hom.FaithfullyFlat := by
  let := (stalkStructureMap B S hS h z).hom.toAlgebra
  have : Module.Flat (geometricStalkRing B S hS (geometricPointMap h.hom z))
      (geometricStalkRing B S hS z) := flat_stalkStructureMap B S hS h z hh
  have : IsLocalHom (algebraMap (geometricStalkRing B S hS (geometricPointMap h.hom z))
      (geometricStalkRing B S hS z)) := isLocalHom_stalkStructureMap B S hS h z
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

section TorAmplitude

-- The standard model is forced: `HasTorAmplitudeCanonical` is stated only for it.
attribute [local instance 10000] HasDerivedCategory.standard

open StacksDraft.TorAmplitude in
/-- **Stacks 0DL2, descent half, at a geometric point.**  For a cartesian square of algebraic
spaces whose lower edge `g` is flat and a geometric point `x̄'` of the upper-left corner, a complex
`K` of `𝒪_{X,x̄}`-modules has Tor amplitude in `[a, b]` over `𝒪_{Y,ȳ}` as soon as
`K ⊗_{𝒪_{X,x̄}} 𝒪_{X',x̄'}` has Tor amplitude in `[a, b]` over `𝒪_{Y',ȳ'}`. -/
theorem hasTorAmplitudeCanonical_geometricStalk_of_baseChange (hpb : IsPullback g' f' f g)
    (hg : IsFlat B S hS g.hom) (x' : GeometricPoint B S hS X'.1)
    (K : CochainComplex
      (ModuleCat.{u} (geometricStalkRing B S hS (geometricPointMap g'.hom x'))) ℤ) (a b : ℤ)
    (h : HasTorAmplitudeCanonical (geometricStalkRing B S hS (geometricPointMap f'.hom x'))
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars
          (stalkStructureMap B S hS f' x').hom).obj
        ((CochainComplex.extendScalars (stalkStructureMap B S hS g' x').hom).obj K))) a b) :
    HasTorAmplitudeCanonical
      (geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars
        (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom).obj K)) a b :=
  hasTorAmplitudeCanonical_restrictScalars_of_flatSquare
    (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom
    (stalkStructureMap B S hS f' x').hom (geometricBaseStalkMap B S hS f g f' g' hpb.w x').hom
    (stalkStructureMap B S hS g' x').hom
    (stalkStructureMap_square B S hS f g f' g' hpb.w x').symm
    (flat_geometricBaseStalkMap B S hS g' f' f g hpb.w hg x')
    (faithfullyFlat_stalkStructureMap B S hS g'
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb.flip hg) x') K a b h

open StacksDraft.TorAmplitude AlgebraicGeometry.BaseChangeTorAmplitude in
/-- **Stacks 0DKD (1) at a geometric point, for a flat lower edge.**  For a cartesian square of
algebraic spaces whose lower edge `g` is flat and a geometric point `x̄'` of the upper-left
corner, if a complex `K` of `𝒪_{X,x̄}`-modules has Tor amplitude in `[a, b]` over `𝒪_{Y,ȳ}`, then
`K ⊗_{𝒪_{X,x̄}} 𝒪_{X',x̄'}` has Tor amplitude in `[a, b]` over `𝒪_{Y',ȳ'}`. -/
theorem hasTorAmplitudeCanonical_geometricStalk_baseChange (hpb : IsPullback g' f' f g)
    (hg : IsFlat B S hS g.hom) (x' : GeometricPoint B S hS X'.1)
    (K : CochainComplex
      (ModuleCat.{u} (geometricStalkRing B S hS (geometricPointMap g'.hom x'))) ℤ) (a b : ℤ)
    (h : HasTorAmplitudeCanonical
      (geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars
        (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom).obj K)) a b) :
    HasTorAmplitudeCanonical (geometricStalkRing B S hS (geometricPointMap f'.hom x'))
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars
          (stalkStructureMap B S hS f' x').hom).obj
        ((CochainComplex.extendScalars (stalkStructureMap B S hS g' x').hom).obj K))) a b := by
  have hc : (stalkStructureMap B S hS g' x').hom.Flat := flat_stalkStructureMap B S hS g' x'
    ((isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb.flip hg)
  let := (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom.toAlgebra
  let := (geometricBaseStalkMap B S hS f g f' g' hpb.w x').hom.toAlgebra
  have : Module.Flat
      (geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      (geometricStalkRing B S hS (geometricPointMap f'.hom x')) :=
    flat_geometricBaseStalkMap B S hS g' f' f g hpb.w hg x'
  obtain ⟨φ, hl, hr, hflat⟩ := cartesian_geometricStalk_tensor_flat B S hS g' f' f g hpb x'
  let : Algebra (geometricStalkRing B S hS (geometricPointMap f'.hom x'))
      ((geometricStalkRing B S hS (geometricPointMap g'.hom x')) ⊗[
        geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x'))]
        (geometricStalkRing B S hS (geometricPointMap f'.hom x'))) :=
    Algebra.TensorProduct.rightAlgebra
  have := Algebra.TensorProduct.right_isScalarTower
    (R := geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x')))
    (A := geometricStalkRing B S hS (geometricPointMap g'.hom x'))
    (B := geometricStalkRing B S hS (geometricPointMap f'.hom x'))
  have := TensorProduct.isPushout
    (R := geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x')))
    (S := geometricStalkRing B S hS (geometricPointMap g'.hom x'))
    (T := geometricStalkRing B S hS (geometricPointMap f'.hom x'))
  let := φ.toAlgebra
  let := (stalkStructureMap B S hS g' x').hom.toAlgebra
  let := (stalkStructureMap B S hS f' x').hom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' hl.symm
  have := IsScalarTower.of_algebraMap_eq' hr.symm
  have : Module.Flat ((geometricStalkRing B S hS (geometricPointMap g'.hom x')) ⊗[
        geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x'))]
        (geometricStalkRing B S hS (geometricPointMap f'.hom x')))
      (geometricStalkRing B S hS x') := hflat
  have htor := Dualizing.torIndependent_of_flat_right
    (R := geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x')))
    (A := geometricStalkRing B S hS (geometricPointMap g'.hom x'))
    (B := geometricStalkRing B S hS (geometricPointMap f'.hom x'))
  obtain ⟨P, p, hP, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} K
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have hP' := AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (((ModuleCat.restrictScalars
          (stalkStructureMap B S hS f
            (geometricPointMap g'.hom x')).hom).mapDerivedCategoryFactors.app
            K).symm ≪≫
        (ModuleCat.restrictScalars
          (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom).mapDerivedCategory.mapIso
          (asIso (DerivedCategory.Q.map p)).symm) a b h
  have h₁ := hasTorAmplitudeCanonical_torIndependent_flatBaseChange
    (T := (geometricStalkRing B S hS (geometricPointMap g'.hom x')) ⊗[
        geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x'))]
        (geometricStalkRing B S hS (geometricPointMap f'.hom x')))
    (C := geometricStalkRing B S hS x') htor P hP a b hP'
  have : Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (stalkStructureMap B S hS g' x').hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hc
  refine AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ?_ a b h₁
  exact ((ModuleCat.restrictScalars
      (stalkStructureMap B S hS f' x').hom).mapDerivedCategoryFactors.app
      _).symm ≪≫
    (ModuleCat.restrictScalars (stalkStructureMap B S hS f' x').hom).mapDerivedCategory.mapIso
      (((ModuleCat.extendScalars (stalkStructureMap B S hS g' x').hom).mapDerivedCategoryFactors.app
          P).symm ≪≫
        (ModuleCat.extendScalars (stalkStructureMap B S hS g' x').hom).mapDerivedCategory.mapIso
          (asIso (DerivedCategory.Q.map p)) ≪≫
        (ModuleCat.extendScalars
          (stalkStructureMap B S hS g' x').hom).mapDerivedCategoryFactors.app K) ≪≫
    (ModuleCat.restrictScalars (stalkStructureMap B S hS f' x').hom).mapDerivedCategoryFactors.app _

end TorAmplitude

end AlgebraicGeometry.Space

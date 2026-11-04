module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ClosureRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.NoetherNormalization
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
public import StacksFrontier.RingTheory.CohenMacaulay.Locus
public import StacksFrontier.RingTheory.KrullDimension.Defs
public import StacksFrontier.RingTheory.RelativeDimension.QuasiFinite
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop

/-!
# Cohen–Macaulay morphisms and quasi-finite maps to affine space

Let `f : X ⟶ S` be flat and locally of finite presentation, let `x` be a point of `X` with
image `s`, and let `d` be the dimension of the fibre `X_s` at `x`. Then `f` is Cohen–Macaulay
at `x` if and only if some open neighbourhood of `x` admits a locally quasi-finite
`S`-morphism to affine `d`-space over `S` which is flat at `x`, if and only if some open
neighbourhood admits a locally quasi-finite flat such morphism, if and only if every
`S`-morphism to affine `d`-space from an open neighbourhood of `x` which is quasi-finite at
`x` is flat at `x`.

## Main results

* `AlgebraicGeometry.exists_nat_topologicalKrullDimAt_fiber`: the dimension of the fibre of a
  morphism locally of finite presentation at a point of the source is a natural number.
* `AlgebraicGeometry.isCohenMacaulayAt_tfae`: the four equivalent characterizations of
  Cohen–Macaulayness at a point.

## Implementation notes

The dimension of a scheme at a point takes values in `WithBot ℕ∞`; local finite presentation
forces the fibre dimension to be the cast of a natural number `n`, which is supplied as a
hypothesis to the equivalence so that affine `n`-space over `S` can be formed. Being locally
quasi-finite is expressed by local finite type together with the fibre-isolation condition
`AlgebraicGeometry.LocallyQuasiFinite`, and quasi-finiteness at a point by
`AlgebraicGeometry.quasiFiniteAt`. The locally Noetherian fibres demanded by
`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulayAt` are not a hypothesis of the equivalence: they
are supplied from local finite presentation by
`AlgebraicGeometry.isLocallyNoetherian_fiber_of_locallyOfFinitePresentation`.

## References

* [Stacks Project, Tag 0BUU](https://stacks.math.columbia.edu/tag/0BUU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A Noetherian local ring is a maximal Cohen–Macaulay module over itself exactly when it is
a Cohen–Macaulay local ring. -/
private theorem maxCM_self_iff_CohenMacaulayLocalRing (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    Module.IsMaximalCohenMacaulay A A ↔ IsCohenMacaulayLocalRing A := by
  have hI : IsLocalRing.maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ := by
    simpa [smul_eq_mul, Ideal.mul_top] using
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  constructor
  · intro h
    have hdepth : Module.depthSup A (IsLocalRing.maximalIdeal A) A = ringKrullDim A := by
      change (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) =
        ringKrullDim A at h
      rw [Module.depth, ite_eq_right hI, ← Module.depthSup_eq_iSup] at h
      exact h
    change IsCohenMacaulayModule A A
    change Module.depthSup A (IsLocalRing.maximalIdeal A) A =
      (Module.supportDim A A : WithBot ℕ∞)
    rw [Module.supportDim_self_eq_ringKrullDim]
    exact hdepth
  · intro h
    change Module.depthSup A (IsLocalRing.maximalIdeal A) A =
      (Module.supportDim A A : WithBot ℕ∞) at h
    rw [Module.supportDim_self_eq_ringKrullDim] at h
    change (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) = ringKrullDim A
    rw [Module.depth, ite_eq_right hI, ← Module.depthSup_eq_iSup]
    exact h

/-- The morphism of affine schemes induced by the structure map of an algebra. -/
@[ega "IV 1.9.2"]
private noncomputable abbrev affineSpecMap (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- The prime ideal of `A` corresponding to a point of `Spec A`. -/
private noncomputable abbrev specPointPrime {A : Type u} [CommRing A]
    (q : Spec (.of A)) : PrimeSpectrum A :=
  OrderDual.ofDual (specOrderIsoPrimeSpectrum (.of A) q)

/-- A morphism of affine schemes is flat at a point exactly when the localization of the target
ring at the corresponding prime is flat over the source ring. -/
private theorem flatAt_specMap_iff {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (q : PrimeSpectrum A) :
    AlgebraicGeometry.IsFlatAt (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom q ↔
      (letI : Algebra P A := φ.toAlgebra
       let p : PrimeSpectrum P := q.comap φ
       letI : p.asIdeal.IsPrime := p.isPrime
       letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
       letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
         (Localization.localRingHom p.asIdeal q.asIdeal φ rfl).toAlgebra
       letI : IsScalarTower P (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
         .of_algebraMap_eq fun a =>
           (Localization.localRingHom_to_map p.asIdeal q.asIdeal φ rfl a).symm
       Module.Flat P (Localization.AtPrime q.asIdeal)) := by
  let : Algebra P A := φ.toAlgebra
  let p : PrimeSpectrum P := q.comap φ
  let : p.asIdeal.IsPrime := p.isPrime
  let : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom p.asIdeal q.asIdeal φ rfl).toAlgebra
  have htower : IsScalarTower P (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    .of_algebraMap_eq fun a =>
      (Localization.localRingHom_to_map p.asIdeal q.asIdeal φ rfl a).symm
  have h := RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom φ) q)
  change AlgebraicGeometry.IsFlatAt (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom q ↔
      (Localization.localRingHom p.asIdeal q.asIdeal φ rfl).Flat at h
  have h' : (Localization.localRingHom p.asIdeal q.asIdeal φ rfl).Flat ↔
      Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) := Iff.rfl
  have h'' : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) ↔
      Module.Flat P (Localization.AtPrime q.asIdeal) :=
    Module.flat_iff_of_isLocalization (S := Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
  simpa using h.trans (h'.trans h'')

/-- Flatness at a point is unchanged by composing with isomorphisms on either side. -/
private theorem flatAt_comp_iso_iff {X Y X' Y' : Scheme.{u}}
    (g : X' ⟶ Y') (eX : X ≅ X') (eY : Y' ≅ Y) (x : X) :
    AlgebraicGeometry.IsFlatAt (eX.hom ≫ g ≫ eY.hom).toLRSHom.toShHom x ↔
      AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom (eX.hom x) := by
  let y := g (eX.hom x)
  let α₀ := eY.hom.stalkMap y
  let β₀ := eX.hom.stalkMap x
  have hα : IsIso α₀ :=
    ((isIso_iff_isIso_stalkMap eY.hom).mp (inferInstance : IsIso eY.hom)).2 y
  have hβ : IsIso β₀ :=
    ((isIso_iff_isIso_stalkMap eX.hom).mp (inferInstance : IsIso eX.hom)).2 x
  let α : Y.presheaf.stalk (eY.hom y) ≅ Y'.presheaf.stalk y := asIso α₀
  let β : X'.presheaf.stalk (eX.hom x) ≅ X.presheaf.stalk x := asIso β₀
  have hstalk : (eX.hom ≫ g ≫ eY.hom).stalkMap x =
      α.hom ≫ g.stalkMap (eX.hom x) ≫ β.hom := by
    simp [Scheme.Hom.stalkMap_comp, α, β, y, Category.assoc]
    rfl
  have hsquare : α.inv ≫ (eX.hom ≫ g ≫ eY.hom).stalkMap x =
      g.stalkMap (eX.hom x) ≫ β.hom := by
    rw [hstalk]
    simp
  have harrow : Arrow.mk (g.stalkMap (eX.hom x)) ≅
      Arrow.mk ((eX.hom ≫ g ≫ eY.hom).stalkMap x) :=
    Arrow.isoMk α.symm β hsquare
  change ((eX.hom ≫ g ≫ eY.hom).stalkMap x).hom.Flat ↔
    (g.stalkMap (eX.hom x)).hom.Flat
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff harrow).symm

/-- The stalk map of `f` and that of `f ≫ j`, for an open immersion `j`, are isomorphic arrows. -/
private theorem nonempty_arrow_stalkMap_postcomp_openImmersion {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion j] (x : X) :
    Nonempty (Arrow.mk (f.stalkMap x) ≅ Arrow.mk ((f ≫ j).stalkMap x)) := by
  have : IsIso (j.stalkMap (f x)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 (f x)
  exact ⟨Arrow.isoMk (asIso (j.stalkMap (f x))).symm (Iso.refl _)
    (by simp only [Arrow.mk_hom, Scheme.Hom.stalkMap_comp]; simp)⟩

/-- Flatness at a point is unchanged by composing with an open immersion on the target. -/
private theorem flatAt_postcomp_openImmersion_iff {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion j] (x : X) :
    AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x ↔
      AlgebraicGeometry.IsFlatAt (f ≫ j).toLRSHom.toShHom x :=
  (nonempty_arrow_stalkMap_postcomp_openImmersion f j x).elim
    RingHom.Flat.respectsIso.arrow_mk_iso_iff

/-- Flatness of a morphism at a point can be read off from any affine chart presenting it as the
morphism of spectra attached to a ring homomorphism. -/
private theorem flatAt_chartSpecMap_iff {X Y : Scheme.{u}} {P A : Type u}
    [CommRing P] [CommRing A] (f : X ⟶ Y) (φ : P →+* A)
    (eX : X ≅ Spec (.of A)) (eY : Spec (.of P) ≅ Y)
    (h : eX.hom ≫ Spec.map (CommRingCat.ofHom φ) = f ≫ eY.symm.hom)
    (x : X) :
    AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x ↔
      AlgebraicGeometry.IsFlatAt (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom (eX.hom x) := by
  have hcomp : f = eX.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ eY.hom := by
    calc
      f = (f ≫ eY.symm.hom) ≫ eY.hom := by simp
      _ = (eX.hom ≫ Spec.map (CommRingCat.ofHom φ)) ≫ eY.hom :=
        (congrArg (fun k => k ≫ eY.hom) h).symm
      _ = eX.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ eY.hom := by
        simp [Category.assoc]
  rw [hcomp]
  exact flatAt_comp_iso_iff (Spec.map (CommRingCat.ofHom φ)) eX eY x

section FiberFlatness

open IsLocalRing Algebra.TensorProduct TensorProduct

section FiberLocalization

variable {R X : Type*} [CommRing R] [CommRing X] [Algebra R X] (p : Ideal R) [p.IsPrime]
  (r : Ideal X) [r.IsPrime] [r.LiesOver p] (J : Ideal (Localization.AtPrime r))

end FiberLocalization

section Core

open Localization.AtPrime

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {σ : Type*} [Finite σ]
  [Algebra (MvPolynomial σ R) T] [IsScalarTower R (MvPolynomial σ R) T]

end Core

/-- Identify Cohen–Macaulayness in the quotient and tensor-product models of a fibre. -/
private theorem isMaximalCohenMacaulay_fiber_localization_iff
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] (Q : Ideal ((q.under R).Fiber S)) [Q.IsPrime]
    (hQ : Q.comap (includeRight : S →ₐ[R] (q.under R).Fiber S).toRingHom = q) :
    Module.IsMaximalCohenMacaulay
        (Localization.AtPrime (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))))
        (Localization.AtPrime (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S))))) ↔
      Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q) := by
  let J := (q.under R).map (algebraMap R (Localization.AtPrime q))
  let : Algebra ((q.under R).Fiber S) (Localization.AtPrime q ⧸ J) :=
    (fiberToQuotient (q.under R) q J rfl).toRingHom.toAlgebra
  have : IsLocalization.AtPrime (Localization.AtPrime q ⧸ J) Q :=
    isLocalization_fiberToQuotient (q.under R) q J rfl Q hQ
  have : IsLocalRing (Localization.AtPrime q ⧸ J) :=
    IsLocalization.AtPrime.isLocalRing _ Q
  exact (Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv
    (fiberRingEquiv R q (Localization.AtPrime q))).symm.trans
      (Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv
        (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime q ⧸ J)
          (Localization.AtPrime Q)).toRingEquiv)

end FiberFlatness

/-- For a finite type algebra `R → A` and a point `q` of `Spec A`, the fibre ring at `q` is a
maximal Cohen–Macaulay module over itself exactly when the stalk of the scheme-theoretic fibre is
Cohen–Macaulay, and the relative dimension at `q` agrees with the local dimension of that
fibre. -/
private theorem maxCM_fiberChart_iff_CohenMacaulayLocalRing
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (q : Spec (.of A))
    [IsNoetherianRing
      (((affineSpecMap R A).fiber ((affineSpecMap R A) q)).presheaf.stalk
        ((affineSpecMap R A).asFiber q))] :
    (Module.IsMaximalCohenMacaulay
        (Localization.AtPrime ((specPointPrime q).asIdeal.map (Ideal.Quotient.mk
          (((specPointPrime q).asIdeal.under R).map (algebraMap R A)))))
        (Localization.AtPrime ((specPointPrime q).asIdeal.map (Ideal.Quotient.mk
          (((specPointPrime q).asIdeal.under R).map (algebraMap R A))))) ↔
      IsCohenMacaulayLocalRing
        (((affineSpecMap R A).fiber ((affineSpecMap R A) q)).presheaf.stalk
            ((affineSpecMap R A).asFiber q))) ∧
    Algebra.relativeDimensionAt R (specPointPrime q).asIdeal =
      topologicalKrullDimAt ((affineSpecMap R A).fiber ((affineSpecMap R A) q))
        ((affineSpecMap R A).asFiber q) := by
  classical
  let f := affineSpecMap R A
  let q' : PrimeSpectrum A := specPointPrime q
  let p : PrimeSpectrum R := specPointPrime (f q)
  let : p.asIdeal.IsPrime := p.isPrime
  have hpS : (p : Spec (.of R)) = f q := by rfl
  let hres := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p
  let eleft : f.fiber p ≅ Spec (.of (p.asIdeal.Fiber A)) :=
    pullbackSymmetry _ _ ≪≫
      pullback.congrHom hres.symm (by
        change Spec.map (CommRingCat.ofHom (algebraMap R A)) = _
        rfl) ≪≫
      asIso (Limits.pullback.map _ _ _ _
        (Spec.map <| (Scheme.Spec.residueFieldIso (.of R) _).inv) (𝟙 _) (𝟙 _)
        (by simp) (by simp)) ≪≫
      pullbackSpecIso R p.asIdeal.ResidueField A
  let qF : f.fiber p := hpS.symm ▸ f.asFiber q
  let hqF : qF = f.asFiber q := by rfl
  let Qspec : Spec (.of (p.asIdeal.Fiber A)) := eleft.hom qF
  let Q' : PrimeSpectrum (p.asIdeal.Fiber A) := specPointPrime Qspec
  let Q : Ideal (p.asIdeal.Fiber A) := Q'.asIdeal
  have hproj : eleft.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom) =
      f.fiberι p := by
    dsimp [eleft, Iso.trans]
    simp only [Category.assoc, pullbackSpecIso_hom_snd,
      Limits.pullback.congrHom_hom, Limits.pullback.map, Limits.pullback.lift_snd]
    simp only [Limits.pullback.lift_snd, Category.comp_id]
    change (Limits.pullbackSymmetry f ((Spec (.of R)).fromSpecResidueField p)).hom ≫
      Limits.pullback.snd ((Spec (.of R)).fromSpecResidueField p) f =
        Limits.pullback.fst f ((Spec (.of R)).fromSpecResidueField p)
    exact Limits.pullbackSymmetry_hom_comp_snd f _
  have hQpoint : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom Q' = q' := by
    have hpoint : (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom)
        Qspec) = q := by
      change ((eleft.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom))
          qF) = q
      rw [hproj, hqF]
      exact Scheme.Hom.fiberι_asFiber f q
    have h'' := congrArg specPointPrime hpoint
    change PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom Q' = q' at h''
    exact h''
  have hQ : Q.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom = q'.asIdeal := by
    simpa [Q] using congrArg PrimeSpectrum.asIdeal hQpoint
  have : Q.IsPrime := Q'.isPrime
  have hCMiso : Module.IsMaximalCohenMacaulay
      ((f.fiber p).presheaf.stalk qF)
      ((f.fiber p).presheaf.stalk qF) ↔
      Module.IsMaximalCohenMacaulay (Localization.AtPrime Q)
          (Localization.AtPrime Q) := by
    let : IsIso eleft.hom := by infer_instance
    let : IsIso (eleft.hom.stalkMap qF) := by infer_instance
    let ρ := ((asIso (eleft.hom.stalkMap qF)).commRingCatIsoToRingEquiv).symm.trans
      (Spec.stalkIso (.of (p.asIdeal.Fiber A)) (eleft.hom qF)).commRingCatIsoToRingEquiv
    let : IsNoetherianRing ((f.fiber p).presheaf.stalk qF) := by
      cases hpS
      exact (inferInstance : IsNoetherianRing
        (((affineSpecMap R A).fiber ((affineSpecMap R A) q)).presheaf.stalk
          ((affineSpecMap R A).asFiber q)))
    let : IsNoetherianRing (Localization.AtPrime Q) :=
      isNoetherianRing_of_ringEquiv _ ρ
    exact Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv ρ
  let : IsNoetherianRing ((f.fiber p).presheaf.stalk qF) := by
    cases hpS
    exact (inferInstance : IsNoetherianRing
      (((affineSpecMap R A).fiber ((affineSpecMap R A) q)).presheaf.stalk
        ((affineSpecMap R A).asFiber q)))
  let : IsLocalRing ((f.fiber p).presheaf.stalk qF) := by infer_instance
  have hCMfiber := @isMaximalCohenMacaulay_fiber_localization_iff
    R A _ _ _ q'.asIdeal q'.isPrime Q Q'.isPrime hQ
  have hCMfinal := (hCMfiber.trans hCMiso.symm).trans
    (maxCM_self_iff_CohenMacaulayLocalRing
      ((f.fiber p).presheaf.stalk qF))
  have hcmTransport :
      IsCohenMacaulayLocalRing ((f.fiber p).presheaf.stalk qF) ↔
        IsCohenMacaulayLocalRing ((f.fiber (f q)).presheaf.stalk (f.asFiber q)) := by
    cases hpS
    rfl
  constructor
  · simpa [f, q', specPointPrime] using hCMfinal.trans hcmTransport
  · let : IsIso eleft.hom := by infer_instance
    have hdimRel : Algebra.relativeDimensionAt R q'.asIdeal =
        TopologicalSpace.localKrullDim (PrimeSpectrum (p.asIdeal.Fiber A)) Q' := by
      have hp : q'.asIdeal.under R = p.asIdeal := by
        change (q'.comap (algebraMap R A)).asIdeal = p.asIdeal
        rfl
      exact Algebra.relativeDimensionAt_eq_localKrullDim q'.asIdeal p.asIdeal hp Q hQ
    have hdimHome := topologicalKrullDimAt_eq_of_homeomorph
      eleft.hom.homeomorph qF
    have hdimSpace : topologicalKrullDimAt (f.fiber p) qF =
        TopologicalSpace.localKrullDim (PrimeSpectrum (p.asIdeal.Fiber A)) Q' := by
      calc
        _ = topologicalKrullDimAt (Spec (.of (p.asIdeal.Fiber A))) Qspec := hdimHome
        _ = TopologicalSpace.localKrullDim (PrimeSpectrum (p.asIdeal.Fiber A)) Q' := by
          rw [TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
          rfl
    have hdimTransport : topologicalKrullDimAt (f.fiber p) qF =
        topologicalKrullDimAt (f.fiber (f q)) (f.asFiber q) := by
      cases hpS
      rfl
    simpa [f, q', specPointPrime] using hdimRel.trans (hdimSpace.symm.trans hdimTransport)

/-- Let `R → A` be flat of finite presentation and let `R[σ] → A` be quasi-finite, with the local
dimension of the fibre of `Spec A → Spec R` at `q` equal to the number of variables. Then
`Spec A → Spec R[σ]` is flat at `q` exactly when that fibre is Cohen–Macaulay at `q`. -/
private theorem affineFlatAt_iff_fiberCohenMacaulay_of_dim
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A] [Algebra.FiniteType R A]
    {σ : Type u} [Finite σ] (φ : MvPolynomial σ R →ₐ[R] A)
    (q : Spec (.of A))
    (hqf : (letI : Algebra (MvPolynomial σ R) A := φ.toRingHom.toAlgebra
      Algebra.QuasiFinite (MvPolynomial σ R) A))
    (hdim : topologicalKrullDimAt
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
        ((Spec.map (CommRingCat.ofHom (algebraMap R A))) q))
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))).asFiber q) = Nat.card σ)
    [IsNoetherianRing (((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))) q)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (algebraMap R A))).asFiber q))] :
    AlgebraicGeometry.IsFlatAt (Spec.map (CommRingCat.ofHom φ.toRingHom)).toLRSHom.toShHom q ↔
      IsCohenMacaulayLocalRing
        (((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
          ((Spec.map (CommRingCat.ofHom (algebraMap R A))) q)).presheaf.stalk
            ((Spec.map (CommRingCat.ofHom (algebraMap R A))).asFiber q)) := by
  let : Algebra (MvPolynomial σ R) A := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) A :=
    .of_algebraMap_eq' (by
      ext r
      exact (φ.commutes r).symm)
  let : Algebra.QuasiFinite (MvPolynomial σ R) A := hqf
  let q' := specPointPrime q
  let : q'.asIdeal.IsPrime := q'.isPrime
  have hcore := flat_localization_iff (R := R) (T := A) (σ := σ) q'.asIdeal
  have hchart := maxCM_fiberChart_iff_CohenMacaulayLocalRing
    (R := R) (A := A) q
  have hdim' : Algebra.relativeDimensionAt R q'.asIdeal = Nat.card σ := by
    calc
      Algebra.relativeDimensionAt R q'.asIdeal =
          topologicalKrullDimAt
            ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
              ((Spec.map (CommRingCat.ofHom (algebraMap R A))) q))
            ((Spec.map (CommRingCat.ofHom (algebraMap R A))).asFiber q) := by
              simpa [specPointPrime, affineSpecMap] using hchart.2
      _ = Nat.card σ := hdim
  let I := q'.asIdeal.map (Ideal.Quotient.mk
    ((q'.asIdeal.under R).map (algebraMap R A)))
  have hCM :
      Module.IsMaximalCohenMacaulay (Localization.AtPrime I) (Localization.AtPrime I) ↔
        IsCohenMacaulayLocalRing
          (((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
            ((Spec.map (CommRingCat.ofHom (algebraMap R A))) q)).presheaf.stalk
              ((Spec.map (CommRingCat.ofHom (algebraMap R A))).asFiber q)) := by
    simpa [I, affineSpecMap] using hchart.1
  have hpair :
      (Module.IsMaximalCohenMacaulay (Localization.AtPrime I) (Localization.AtPrime I) ∧
        Algebra.relativeDimensionAt R q'.asIdeal = Nat.card σ) ↔
        IsCohenMacaulayLocalRing
          (((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
            ((Spec.map (CommRingCat.ofHom (algebraMap R A))) q)).presheaf.stalk
              ((Spec.map (CommRingCat.ofHom (algebraMap R A))).asFiber q)) := by
    rw [hCM, hdim']
    simp
  exact (flatAt_specMap_iff φ.toRingHom q').trans (hcore.trans hpair)

/-- A locally quasi-finite morphism from an affine open to affine space over an affine open of the
target is induced by a quasi-finite polynomial algebra homomorphism over the base. -/
private theorem affineFactorizationAlgHom {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (n : ℕ) (π : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme)
    (hfactor : π ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom ≫ V.1.ι =
      U.1.ι ≫ f)
    (hLQF : LocallyQuasiFinite π) :
    ∃ θ : MvPolynomial (ULift.{u} (Fin n)) Γ(S, V.1) →+* Γ(X, U.1),
      (U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ) =
        π ≫ AffineSpace.map (ULift.{u} (Fin n)) V.2.isoSpec.hom ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin n)) Γ(S, V.1)).hom) ∧
      θ.comp (MvPolynomial.C : Γ(S, V.1) →+* _) = (f.appLE V.1 U.1 hUV).hom ∧
      θ.QuasiFinite := by
  classical
  let R := Γ(S, V.1)
  let A := Γ(X, U.1)
  have hUaff : IsAffineOpen U.1 := U.2
  have hVaff : IsAffineOpen V.1 := V.2
  let targetIso : Spec (.of (MvPolynomial (ULift.{u} (Fin n)) R)) ≅
      AffineSpace (ULift.{u} (Fin n)) V.1.toScheme := by
    let mapIso : AffineSpace (ULift.{u} (Fin n)) (Spec R) ≅
        AffineSpace (ULift.{u} (Fin n)) V.1.toScheme := {
      hom := AffineSpace.map (ULift.{u} (Fin n)) hVaff.isoSpec.inv
      inv := AffineSpace.map (ULift.{u} (Fin n)) hVaff.isoSpec.hom
      hom_inv_id := by
        rw [← AffineSpace.map_comp, hVaff.isoSpec.inv_hom_id]
        exact AffineSpace.map_id (S := Spec R)
      inv_hom_id := by
        rw [← AffineSpace.map_comp, hVaff.isoSpec.hom_inv_id]
        exact AffineSpace.map_id (S := V.1.toScheme)
    }
    exact (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).symm ≪≫ mapIso
  let m : Spec (.of A) ⟶ Spec (.of (MvPolynomial (ULift.{u} (Fin n)) R)) :=
    hUaff.isoSpec.inv ≫ π ≫ targetIso.inv
  let θ₀ : MvPolynomial (ULift.{u} (Fin n)) R →+* A := (Spec.preimage m).hom
  have hm : Spec.map (CommRingCat.ofHom θ₀) = m := Spec.map_preimage m
  have hsource : hUaff.isoSpec.hom ≫ m = π ≫ targetIso.inv := by
    dsimp only [m]
    simp
  let ρ := f.appLE V.1 U.1 hUV
  have htarget : targetIso.hom ≫
      (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom ≫ V.1.ι =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* _)) ≫ V.2.fromSpec := by
    change (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv ≫
        (AffineSpace.map (ULift.{u} (Fin n)) hVaff.isoSpec.inv ≫
          (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme)) ≫ V.1.ι = _
    simp only [Category.assoc, AffineSpace.map_over_assoc,
      AffineSpace.SpecIso_inv_over_assoc, hVaff.isoSpec_inv_ι]
  have hmaps : m ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R)) = Spec.map ρ := by
    have : IsOpenImmersion hVaff.fromSpec := hVaff.isOpenImmersion_fromSpec
    have hafter :
        (m ≫ Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R))) ≫ hVaff.fromSpec =
          Spec.map ρ ≫ hVaff.fromSpec := by
      calc
        (m ≫ Spec.map (CommRingCat.ofHom
            (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R))) ≫ hVaff.fromSpec =
          hUaff.isoSpec.inv ≫ π ≫
            (targetIso.inv ≫ Spec.map (CommRingCat.ofHom
              (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R)) ≫ hVaff.fromSpec) := by
                dsimp only [m]
                simp [Category.assoc]
        _ = hUaff.isoSpec.inv ≫ π ≫
            ((AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom ≫ V.1.ι) := by
          rw [show targetIso.inv ≫ Spec.map (CommRingCat.ofHom
            (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R)) ≫ hVaff.fromSpec =
              (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom ≫ V.1.ι from by
            calc
              _ = targetIso.inv ≫ (targetIso.hom ≫
                  (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom ≫ V.1.ι) := by
                    rw [← htarget]
              _ = _ := by simp]
        _ = hUaff.isoSpec.inv ≫ (π ≫
              (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom ≫ V.1.ι) := by
              simp
        _ = hUaff.isoSpec.inv ≫ (U.1.ι ≫ f) := by rw [hfactor]
        _ = hUaff.fromSpec ≫ f := by
              change (hUaff.isoSpec.inv ≫ U.1.ι) ≫ f = hUaff.fromSpec ≫ f
              rw [hUaff.isoSpec_inv_ι]
        _ = Spec.map ρ ≫ hVaff.fromSpec :=
              (IsAffineOpen.SpecMap_appLE_fromSpec f hVaff hUaff hUV).symm
    exact (cancel_mono hVaff.fromSpec).mp hafter
    
  have hbase : θ₀.comp (MvPolynomial.C : R →+* _) = ρ.hom := by
    have hCat : CommRingCat.ofHom (θ₀.comp (MvPolynomial.C : R →+* _)) = ρ := by
      apply Spec.map_injective
      calc
        Spec.map (CommRingCat.ofHom (θ₀.comp
            (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R))) =
            Spec.map (CommRingCat.ofHom θ₀) ≫ Spec.map (CommRingCat.ofHom
              (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R)) := by simp
        _ = m ≫ Spec.map (CommRingCat.ofHom
            (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R)) := by rw [hm]
        _ = Spec.map ρ := hmaps
    exact congrArg CommRingCat.Hom.hom hCat
  have hqf : θ₀.QuasiFinite := by
    have hmQF : LocallyQuasiFinite m := by
      let : LocallyQuasiFinite (U.2.isoSpec.inv) := inferInstance
      let : LocallyQuasiFinite π := hLQF
      let : LocallyQuasiFinite targetIso.inv := inferInstance
      dsimp [m]
      infer_instance
    have hSpecQF : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom θ₀)) := by
      simpa [hm] using hmQF
    exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp hSpecQF
  refine ⟨θ₀, ?_, hbase, hqf⟩
  calc
    hUaff.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ₀) =
        hUaff.isoSpec.hom ≫ m := by rw [hm]
    _ = π ≫ targetIso.inv := hsource
    _ = π ≫ AffineSpace.map (ULift.{u} (Fin n)) V.2.isoSpec.hom ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).hom := rfl

/-- Flatness at a point is unchanged by composing with an open immersion on the source. -/
private theorem flatAt_precomp_openImmersion_iff {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (f : Y ⟶ Z) (x : X) :
    AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom (j x) ↔
      AlgebraicGeometry.IsFlatAt (j ≫ f).toLRSHom.toShHom x := by
  let β₀ := j.stalkMap x
  have hβ : IsIso β₀ :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion j)).2 x
  let β : Y.presheaf.stalk (j x) ≅ X.presheaf.stalk x := asIso β₀
  have hstalk : (j ≫ f).stalkMap x = f.stalkMap (j x) ≫ j.stalkMap x := by
    simp [Scheme.Hom.stalkMap_comp]
  have hsquare : f.stalkMap (j x) ≫ β.hom = (j ≫ f).stalkMap x := by
    exact hstalk.symm
  have harrow : Arrow.mk (f.stalkMap (j x)) ≅ Arrow.mk ((j ≫ f).stalkMap x) :=
    Arrow.isoMk (Iso.refl _) β hsquare.symm
  change (f.stalkMap (j x)).hom.Flat ↔ ((j ≫ f).stalkMap x).hom.Flat
  exact RingHom.Flat.respectsIso.arrow_mk_iso_iff harrow

/-- Flatness of a morphism at a point of an affine chart of the source is flatness of the induced
morphism of spectra at the corresponding prime. -/
private theorem flatAt_fromSpec_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1)
    (q : Spec Γ(X, U.1)) :
    AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom (U.2.fromSpec q) ↔
      AlgebraicGeometry.IsFlatAt (Spec.map (f.appLE V.1 U.1 e)).toLRSHom.toShHom q := by
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  rw [flatAt_precomp_openImmersion_iff U.2.fromSpec f q,
    ← IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 e,
    ← flatAt_postcomp_openImmersion_iff]

/-- The flat locus of a morphism locally of finite presentation is open. -/
private theorem isOpen_flatAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] :
    IsOpen {x : X | AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V₀).isOpen
  let V : S.affineOpens := ⟨V₀, hV₀⟩
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  let θ := (f.appLE V₀ U₀ hUV).hom
  let : Algebra Γ(S, V₀) Γ(X, U₀) := θ.toAlgebra
  let : Algebra.FinitePresentation Γ(S, V₀) Γ(X, U₀) :=
    f.finitePresentation_appLE hV₀ hU₀ hUV
  let P := {q : PrimeSpectrum Γ(X, U₀) |
    Module.Flat Γ(S, V₀) (Localization.AtPrime q.asIdeal)}
  have hP : IsOpen P := by
    convert Module.isOpen_setOf_flat_localizedModule_atPrime
      (R := Γ(S, V₀)) (S := Γ(X, U₀)) (M := Γ(X, U₀)) using 1
  have hiff (q : PrimeSpectrum Γ(X, U₀)) :
      AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom (U.2.fromSpec q) ↔ q ∈ P :=
    (flatAt_fromSpec_iff f V U hUV q).trans (flatAt_specMap_iff θ q)
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  refine ⟨U.2.fromSpec '' P, ?_, U.2.fromSpec.isOpenEmbedding.isOpenMap _ hP, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (hiff q).mpr hq
  · refine ⟨U.2.primeIdealOf ⟨x, hxU⟩, ?_, U.2.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
    apply (hiff _).mp
    rw [U.2.fromSpec_primeIdealOf]
    exact hx

/-- A morphism locally of finite type whose composition with an open immersion is locally
quasi-finite is itself locally quasi-finite. -/
private theorem locallyQuasiFinite_of_postcomp_openImmersion {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion j]
    [LocallyOfFiniteType f] [LocallyQuasiFinite (f ≫ j)] :
    LocallyQuasiFinite f := by
  have hall : ∀ x, AlgebraicGeometry.quasiFiniteAt f x := fun x =>
    ⟨finiteTypeAt_of_locallyOfFiniteType f x,
      (nonempty_arrow_stalkMap_postcomp_openImmersion f j x).elim
        RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff |>.mpr
          ((AlgebraicGeometry.forall_quasiFiniteAt_iff (f ≫ j)).mpr
            ⟨inferInstance, inferInstance⟩ x).2⟩
  exact ((AlgebraicGeometry.forall_quasiFiniteAt_iff f).mp hall).2

/-- Cohen–Macaulayness of the fibre local ring transports along an equality of morphisms. -/
private theorem fiberCM_congr {X S : Scheme.{u}} (f g : X ⟶ S) (h : f = g) (x : X)
    [IsLocallyNoetherian (f.fiber (f x))] [IsLocallyNoetherian (g.fiber (g x))] :
    IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ↔
      IsCohenMacaulayLocalRing ((g.fiber (g x)).presheaf.stalk (g.asFiber x)) := by
  subst g
  rfl

/-- Cohen–Macaulayness of the fibre local ring transports along an equality of points. -/
private theorem fiberCM_congr_point {X S : Scheme.{u}} (f : X ⟶ S) (x y : X) (h : x = y)
    [IsLocallyNoetherian (f.fiber (f x))] [IsLocallyNoetherian (f.fiber (f y))] :
    IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ↔
      IsCohenMacaulayLocalRing ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) := by
  subst y
  rfl

/-- Affine space over an open subscheme is an open subscheme of affine space over the ambient
scheme. -/
private theorem affineSpace_map_isOpenImmersion (σ : Type u) {V S : Scheme.{u}}
    (j : V ⟶ S) [IsOpenImmersion j] : IsOpenImmersion (AffineSpace.map σ j) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (AffineSpace.isPullback_map (n := σ) j).flip inferInstance

/-- Cohen–Macaulayness of the fibre local ring at a point of an affine chart of the source agrees
with the same condition for the induced morphism of spectra. -/
private theorem fiberCM_iff_fromSpec {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (V : S.affineOpens) (U : X.affineOpens)
    (e : U.1 ≤ f ⁻¹ᵁ V.1) (q : Spec Γ(X, U.1))
    [IsLocallyNoetherian (f.fiber (f (U.2.fromSpec q)))]
    [IsLocallyNoetherian ((Spec.map (f.appLE V.1 U.1 e)).fiber
      (Spec.map (f.appLE V.1 U.1 e) q))] :
    IsCohenMacaulayLocalRing ((f.fiber (f (U.2.fromSpec q))).presheaf.stalk
      (f.asFiber (U.2.fromSpec q))) ↔
    IsCohenMacaulayLocalRing (((Spec.map (f.appLE V.1 U.1 e)).fiber
      (Spec.map (f.appLE V.1 U.1 e) q)).presheaf.stalk
      ((Spec.map (f.appLE V.1 U.1 e)).asFiber q)) := by
  let m := Spec.map (f.appLE V.1 U.1 e)
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  let : LocallyOfFiniteType m :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (f.finiteType_appLE V.2 U.2 e)
  let (s : S) : IsLocallyNoetherian ((U.2.fromSpec ≫ f).fiber s) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType _ s
  let (s : S) : IsLocallyNoetherian ((m ≫ V.2.fromSpec).fiber s) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType _ s
  let : IsNoetherianRing (((U.2.fromSpec ≫ f).fiber (f (U.2.fromSpec q))).presheaf.stalk
      ((U.2.fromSpec ≫ f).asFiber q)) := noetherianStalk_of_locallyNoetherian _ inferInstance
  let : IsLocalRing (((U.2.fromSpec ≫ f).fiber (f (U.2.fromSpec q))).presheaf.stalk
      ((U.2.fromSpec ≫ f).asFiber q)) := LocallyRingedSpace.isLocalRing _ _
  let : IsNoetherianRing (((m ≫ V.2.fromSpec).fiber (V.2.fromSpec (m q))).presheaf.stalk
      ((m ≫ V.2.fromSpec).asFiber q)) := noetherianStalk_of_locallyNoetherian _ inferInstance
  let : IsLocalRing (((m ≫ V.2.fromSpec).fiber (V.2.fromSpec (m q))).presheaf.stalk
      ((m ≫ V.2.fromSpec).asFiber q)) := LocallyRingedSpace.isLocalRing _ _
  have hsource := localFiberCM_iff_sourceOpenImmersion U.2.fromSpec f q
    inferInstance inferInstance
  have htarget := localFiberCM_iff_openTarget V.2.fromSpec m (m q) q
    inferInstance inferInstance
  have hcomp : m ≫ V.2.fromSpec = U.2.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 e
  exact hsource.trans ((fiberCM_congr (U.2.fromSpec ≫ f) (m ≫ V.2.fromSpec)
    hcomp.symm q).trans htarget.symm)

/-- For a flat morphism locally of finite presentation, a quasi-finite factorization through
affine space of the fibre dimension over an affine chart is flat at the point exactly when the
fibre is Cohen–Macaulay there. -/
private theorem flatAt_affineFactorization_iff_fiberCM
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (x : X) (n : ℕ)
    (hn : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (n : WithBot ℕ∞))
    (V : S.affineOpens) (U : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (hx : x ∈ U.1)
    (π : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme)
    (_hfactor : π ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom ≫ V.1.ι =
      U.1.ι ≫ f)
    (θ : MvPolynomial (ULift.{u} (Fin n)) Γ(S, V.1) →+* Γ(X, U.1))
    (hθ : U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ) =
      π ≫ AffineSpace.map (ULift.{u} (Fin n)) V.2.isoSpec.hom ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin n)) Γ(S, V.1)).hom)
    (hbase : θ.comp (MvPolynomial.C : Γ(S, V.1) →+* _) =
      (f.appLE V.1 U.1 hUV).hom)
    (hθqf : θ.QuasiFinite) [IsLocallyNoetherian (f.fiber (f x))] :
    AlgebraicGeometry.IsFlatAt π.toLRSHom.toShHom ⟨x, hx⟩ ↔
      IsCohenMacaulayLocalRing
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  classical
  let R := Γ(S, V.1)
  let A := Γ(X, U.1)
  let σ := ULift.{u} (Fin n)
  let ρ := f.appLE V.1 U.1 hUV
  let q : Spec (.of A) := U.2.isoSpec.hom ⟨x, hx⟩
  let : Algebra R A := ρ.hom.toAlgebra
  let φ : MvPolynomial σ R →ₐ[R] A := {
    toRingHom := θ
    commutes' := fun r => by
      have hb := congrArg (fun ψ : R →+* A => ψ r) hbase
      exact hb
  }
  let : Algebra.FinitePresentation R A := by
    exact f.finitePresentation_appLE V.2 U.2 hUV
  let : Algebra.FiniteType R A := by
    infer_instance
  let : Module.Flat R A := f.flat_appLE V.2 U.2 hUV
  let : Algebra (MvPolynomial σ R) A := φ.toRingHom.toAlgebra
  have hθQF : Algebra.QuasiFinite (MvPolynomial σ R) A :=
    RingHom.quasiFinite_algebraMap.mp hθqf
  have hdim : topologicalKrullDimAt
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
        ((Spec.map (CommRingCat.ofHom (algebraMap R A))) q))
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))).asFiber q) = Nat.card σ := by
    have hchart := fiberDimensionAt_eq_relativeDimensionAt_chart f V U hUV x hx
    have hcard : Nat.card σ = n := by simp [σ]
    have hspec := fiberDimensionAt_specMap (R := R) (B := A) (specPointPrime q)
    exact hspec.trans (hchart.symm.trans (hn.trans (by rw [hcard])))
  let : Algebra (MvPolynomial σ R) A := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) A := .of_algebraMap_eq' (by
    ext r
    exact (φ.commutes r).symm)
  let : Algebra.QuasiFinite (MvPolynomial σ R) A := hθQF
  let : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
    exact RingHom.FiniteType.of_finitePresentation (f.finitePresentation_appLE V.2 U.2 hUV)
  let (s : Spec (.of R)) : IsLocallyNoetherian
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber s) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType _ s
  have hcriterion := affineFlatAt_iff_fiberCohenMacaulay_of_dim φ q hθQF hdim
  have hflatChart : AlgebraicGeometry.IsFlatAt
      (Spec.map (CommRingCat.ofHom θ)).toLRSHom.toShHom q ↔
      IsCohenMacaulayLocalRing
        (((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
          ((Spec.map (CommRingCat.ofHom (algebraMap R A))) q)).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom (algebraMap R A))).asFiber q)) := by
    simpa [φ, q, R, A, σ] using hcriterion
  let mapIso : AffineSpace σ (Spec R) ≅ AffineSpace σ V.1.toScheme := {
    hom := AffineSpace.map σ V.2.isoSpec.inv
    inv := AffineSpace.map σ V.2.isoSpec.hom
    hom_inv_id := by rw [← AffineSpace.map_comp, V.2.isoSpec.inv_hom_id, AffineSpace.map_id]
    inv_hom_id := by rw [← AffineSpace.map_comp, V.2.isoSpec.hom_inv_id, AffineSpace.map_id]
  }
  let targetIso : Spec (.of (MvPolynomial σ R)) ≅ AffineSpace σ V.1.toScheme :=
    (AffineSpace.SpecIso σ R).symm ≪≫ mapIso
  have hchartMap : U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ) =
      π ≫ targetIso.inv := by
    simpa [targetIso, mapIso, R, σ, Category.assoc] using hθ
  have hflatπ : AlgebraicGeometry.IsFlatAt π.toLRSHom.toShHom ⟨x, hx⟩ ↔
      AlgebraicGeometry.IsFlatAt (Spec.map (CommRingCat.ofHom θ)).toLRSHom.toShHom q := by
    have := flatAt_chartSpecMap_iff π θ U.2.isoSpec targetIso hchartMap ⟨x, hx⟩
    simpa [q] using this
  have hqx : U.2.fromSpec q = x := U.2.fromSpec_primeIdealOf ⟨x, hx⟩
  let : IsLocallyNoetherian (f.fiber (f (U.2.fromSpec q))) := by rw [hqx]; infer_instance
  have hsourceCM := fiberCM_iff_fromSpec f V U hUV q
  have hfiberCM : IsCohenMacaulayLocalRing
      (((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber
        ((Spec.map (CommRingCat.ofHom (algebraMap R A))) q)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (algebraMap R A))).asFiber q)) ↔
      IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
    have hpoint := fiberCM_congr_point f (U.2.fromSpec q) x hqx
    exact hsourceCM.symm.trans hpoint
  exact hflatπ.trans (hflatChart.trans hfiberCM)

/-- For a flat morphism locally of finite presentation which factors through affine space of the
fibre dimension by a morphism quasi-finite at `x`, that morphism is flat at `x` exactly when the
fibre of the morphism is Cohen–Macaulay at `x`. -/
private theorem flatAt_affineSpace_iff_fiberCM
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (x : X) (n : ℕ)
    (hn : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (n : WithBot ℕ∞))
    (g : X ⟶ AffineSpace (ULift.{u} (Fin n)) S)
    (hg : g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f)
    (hq : g.QuasiFiniteAt x) [IsLocallyNoetherian (f.fiber (f x))] :
    AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom x ↔
      IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  classical
  let : LocallyOfFiniteType (g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S)) := by
    rw [hg]
    infer_instance
  let : LocallyOfFiniteType g :=
    locallyOfFiniteType_of_comp g (AffineSpace (ULift.{u} (Fin n)) S ↘ S)
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let V : S.affineOpens := ⟨V₀, hV₀⟩
  have hxQ : x ∈ g.quasiFiniteLocus := (Scheme.Hom.mem_quasiFiniteLocus).mpr hq
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (f ⁻¹ᵁ V₀ ⊓ g.quasiFiniteLocus) from ⟨hxV, hxQ⟩)
      (f ⁻¹ᵁ V₀ ⊓ g.quasiFiniteLocus).isOpen
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  have hUV : U.1 ≤ f ⁻¹ᵁ V.1 := hU.trans inf_le_left
  have hUQ : U.1 ≤ g.quasiFiniteLocus := hU.trans inf_le_right
  let j := AffineSpace.map (ULift.{u} (Fin n)) V.1.ι
  let : IsOpenImmersion j := affineSpace_map_isOpenImmersion _ _
  let b := f.resLE V.1 U.1 hUV
  have hb : b ≫ V.1.ι = U.1.ι ≫ f := by simp [b]
  let H := AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) V.1.ι
  have hw : (U.1.ι ≫ g) ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = b ≫ V.1.ι := by
    rw [Category.assoc, hg, hb]
  let π := H.lift (U.1.ι ≫ g) b hw
  have hπj : π ≫ j = U.1.ι ≫ g := H.lift_fst _ _ _
  have hπb : π ≫ (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) = b :=
    H.lift_snd _ _ _
  have hfac : π ≫ (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) ≫ V.1.ι =
      U.1.ι ≫ f := by rw [← Category.assoc, hπb, hb]
  let : LocallyOfFiniteType (π ≫ j) := by rw [hπj]; infer_instance
  let : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π j
  let : LocallyQuasiFinite (π ≫ j) := by
    rw [hπj]
    refine ((AlgebraicGeometry.forall_quasiFiniteAt_iff _).mp ?_).2
    intro y
    refine ⟨finiteTypeAt_of_locallyOfFiniteType _ _, ?_⟩
    rw [Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]
    exact (Scheme.Hom.mem_quasiFiniteLocus).mp (hUQ y.2)
  let : LocallyQuasiFinite π := locallyQuasiFinite_of_postcomp_openImmersion π j
  obtain ⟨θ, hθ, hbase, hθqf⟩ :=
    affineFactorizationAlgHom f V U hUV n π hfac inferInstance
  have hcrit := flatAt_affineFactorization_iff_fiberCM f x n hn V U hUV hxU
    π hfac θ hθ hbase hθqf
  have hflat : AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom x ↔
      AlgebraicGeometry.IsFlatAt π.toLRSHom.toShHom ⟨x, hxU⟩ := by
    have h1 := flatAt_precomp_openImmersion_iff U.1.ι g ⟨x, hxU⟩
    have h2 : AlgebraicGeometry.IsFlatAt (U.1.ι ≫ g).toLRSHom.toShHom ⟨x, hxU⟩ ↔
        AlgebraicGeometry.IsFlatAt (π ≫ j).toLRSHom.toShHom ⟨x, hxU⟩ := by rw [hπj]
    exact h1.trans (h2.trans (flatAt_postcomp_openImmersion_iff π j ⟨x, hxU⟩).symm)
  exact hflat.trans hcrit

attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver

/-- The local dimension of a fibre of a locally finitely presented morphism is finite. -/
@[stacks 0BUU "finiteness of the fibre dimension"]
public theorem exists_nat_topologicalKrullDimAt_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) :
    ∃ n : ℕ,
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (n : WithBot ℕ∞) := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  exact Stacks.RelativeAssassin.exists_nat_eq_topologicalKrullDimAt
    (f.fiber (f x)) (S.residueField (f x)) (f.fiberToSpecResidueField (f x)) (f.asFiber x)

/-- Let `f : X ⟶ S` be flat and locally of finite presentation and let `n` be the dimension of
the fibre of `f` through `x` at `x`. Then `f` is Cohen–Macaulay at `x` if and only if some open
neighbourhood of `x` carries a locally quasi-finite `S`-morphism to affine `n`-space over `S`
that is flat at `x`, if and only if some open neighbourhood carries a locally quasi-finite flat
such morphism, if and only if every `S`-morphism to affine `n`-space from an open neighbourhood
of `x` that is quasi-finite at `x` is flat at `x`. -/
@[stacks 0BUU "the four equivalent conditions",
  ega "IV 15.4.3" "F = O_X, f flat",
  sga "4 XVIII 2.4"]
public theorem isCohenMacaulayAt_tfae {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] (x : X) (n : ℕ)
    (hn : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (n : WithBot ℕ∞)) :
    List.TFAE [
      Scheme.Hom.IsCohenMacaulayAt f
        (fun s => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f s) x,
      ∃ (U : X.Opens) (hx : x ∈ U.1)
          (g : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        (g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U.ι ≫ f) ∧
        (LocallyOfFiniteType g ∧ LocallyQuasiFinite g) ∧
        AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom ⟨x, hx⟩,
      ∃ (U : X.Opens) (_hx : x ∈ U.1)
          (g : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        (g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U.ι ≫ f) ∧
        (LocallyOfFiniteType g ∧ LocallyQuasiFinite g) ∧ Flat g,
      ∀ (U : X.Opens) (hx : x ∈ U.1)
          (g : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        (g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U.ι ≫ f) →
        (AlgebraicGeometry.quasiFiniteAt g ⟨x, hx⟩ →
          AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom ⟨x, hx⟩)] := by
  classical
  -- Every fibre of a morphism locally of finite presentation is locally of finite type over
  -- the residue field of its base point, hence locally Noetherian; this discharges the
  -- witness that `Scheme.Hom.IsCohenMacaulayAt` asks for.
  have hf : ∀ s : S, IsLocallyNoetherian (f.fiber s) := fun s =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f s
  let (s : S) : IsLocallyNoetherian (f.fiber s) := hf s
  have hcriterion (U : X.Opens) (hx : x ∈ U.1)
      (g : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S)
      (hg : g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U.ι ≫ f)
      (hq : g.QuasiFiniteAt ⟨x, hx⟩) :
      AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom ⟨x, hx⟩ ↔
        IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
    let fU := U.ι ≫ f
    let xU : U.toScheme := ⟨x, hx⟩
    let (s : S) : IsLocallyNoetherian (fU.fiber s) :=
      isLocallyNoetherian_fiber_of_locallyOfFiniteType fU s
    have hdim : topologicalKrullDimAt (fU.fiber (fU xU)) (fU.asFiber xU) =
        (n : WithBot ℕ∞) := (fiberDimensionAt_comp_openImmersion U.ι f xU).trans hn
    let : IsNoetherianRing ((fU.fiber (f (U.ι xU))).presheaf.stalk (fU.asFiber xU)) :=
      noetherianStalk_of_locallyNoetherian _ inferInstance
    let : IsLocalRing ((fU.fiber (f (U.ι xU))).presheaf.stalk (fU.asFiber xU)) :=
      LocallyRingedSpace.isLocalRing _ _
    have hcm := localFiberCM_iff_sourceOpenImmersion U.ι f xU (hf _) inferInstance
    exact (flatAt_affineSpace_iff_fiberCM fU xU n hdim g hg hq).trans hcm.symm
  let buildMap : ∀ (V : S.affineOpens) (_ : f x ∈ V.1),
      ∃ (U : X.affineOpens) (hxU : x ∈ U.1)
        (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
        (π : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme),
        (π ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom ≫ V.1.ι =
          U.1.ι ≫ f) ∧
        ((LocallyOfFiniteType π ∧ QuasiCompact π) ∧ LocallyQuasiFinite π) ∧
        ∃ θ : MvPolynomial (ULift.{u} (Fin n)) Γ(S, V.1) →+* Γ(X, U.1),
          (U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ) =
            π ≫ AffineSpace.map (ULift.{u} (Fin n)) V.2.isoSpec.hom ≫
              (AffineSpace.SpecIso (ULift.{u} (Fin n)) Γ(S, V.1)).hom) ∧
          θ.comp (MvPolynomial.C : Γ(S, V.1) →+* _) =
            (f.appLE V.1 U.1 hUV).hom ∧ θ.QuasiFinite := by
    intro V hxV
    obtain ⟨U, hxU, hUV, π, hfac, hprops⟩ :=
      AlgebraicGeometry.exists_affineOpen_quasiFinite_affineSpace_factorization f x V hxV n hn
    exact ⟨U, hxU, hUV, π, hfac, hprops,
      affineFactorizationAlgHom f V U hUV n π hfac hprops.2⟩
  let chooseBase : ∃ (V : S.affineOpens), f x ∈ V.1 := by
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f x)) isOpen_univ
    exact ⟨⟨V₀, hV₀⟩, hxV⟩
  let construct : ∃ (U : X.Opens) (hx : x ∈ U.1)
      (g : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      (g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U.ι ≫ f) ∧
      (LocallyOfFiniteType g ∧ LocallyQuasiFinite g) ∧
      (AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom ⟨x, hx⟩ ↔
        IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) := by
    obtain ⟨V, hxV⟩ := chooseBase
    obtain ⟨U, hxU, hUV, π, hfac, hprops, θ, hθ, hbase, hθqf⟩ := buildMap V hxV
    let j : AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ⟶
        AffineSpace (ULift.{u} (Fin n)) S :=
      AffineSpace.map (ULift.{u} (Fin n)) V.1.ι
    let : IsOpenImmersion j := affineSpace_map_isOpenImmersion _ _
    let g : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S := π ≫ j
    have hfacS : g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U.1.ι ≫ f := by
      calc
        g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) =
            π ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom ≫ V.1.ι := by
              dsimp [g, j]
              rw [Category.assoc, AffineSpace.map_over]
              rfl
        _ = U.1.ι ≫ f := hfac
    let : LocallyOfFiniteType π := hprops.1.1
    let : LocallyQuasiFinite π := hprops.2
    have hLFT : LocallyOfFiniteType g := by dsimp [g, j]; infer_instance
    have hLQF : LocallyQuasiFinite g := by dsimp [g, j]; infer_instance
    exact ⟨U.1, hxU, g, hfacS, ⟨hLFT, hLQF⟩,
      (flatAt_postcomp_openImmersion_iff π j ⟨x, hxU⟩).symm.trans
        (flatAt_affineFactorization_iff_fiberCM f x n hn V U hUV hxU
          π hfac θ hθ hbase hθqf)⟩
  tfae_have 1 → 2 := by
    intro hCM
    obtain ⟨U, hx, g, hfac, hprops, hiff⟩ := construct
    exact ⟨U, hx, g, hfac, hprops, hiff.mpr hCM.2⟩
  tfae_have 2 → 3 := by
    rintro ⟨U, hxU, g, hfac, hprops, hflat⟩
    -- The flat locus is open by 0399; restrict the given neighbourhood to it.
    let : LocallyOfFinitePresentation g := by
      have hcomp : LocallyOfFinitePresentation (g ≫
          (AffineSpace (ULift.{u} (Fin n)) S ↘ S)) := by
        rw [hfac]
        infer_instance
      have : LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin n)) S ↘ S) := inferInstance
      exact AlgebraicGeometry.locallyOfFinitePresentation_of_comp g
        (AffineSpace (ULift.{u} (Fin n)) S ↘ S)
    let : LocallyOfFiniteType g := hprops.1
    let : LocallyQuasiFinite g := hprops.2
    let W : U.toScheme.Opens := ⟨{y | AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom y},
      isOpen_flatAt g⟩
    have hxW : (⟨x, hxU⟩ : U.toScheme) ∈ W := hflat
    let k : W.toScheme ⟶ X := W.ι ≫ U.ι
    let U' : X.Opens := k.opensRange
    have hrange : Set.range U'.ι = Set.range k := by exact U'.range_ι
    let e := IsOpenImmersion.isoOfRangeEq U'.ι k hrange
    have he : e.hom ≫ k = U'.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hxU' : x ∈ U' := ⟨⟨⟨x, hxU⟩, hxW⟩, rfl⟩
    let g' := e.hom ≫ W.ι ≫ g
    have hflat' : Flat (W.ι ≫ g) := by
      apply (Flat.iff_flat_stalkMap _).mpr
      intro z
      exact (flatAt_precomp_openImmersion_iff W.ι g z).mp z.2
    let := hflat'
    have hfactor : g' ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U'.ι ≫ f := by
      dsimp [g']
      rw [Category.assoc, Category.assoc, hfac, ← Category.assoc W.ι U.ι,
        ← Category.assoc, he]
    exact ⟨U', hxU', g', hfactor, ⟨by dsimp [g']; infer_instance,
      by dsimp [g']; infer_instance⟩, by dsimp [g']; infer_instance⟩
  tfae_have 3 → 2 := by
    rintro ⟨U, hxU, g, hfac, hprops, hflat⟩
    exact ⟨U, hxU, g, hfac, hprops, (Flat.iff_flat_stalkMap g).mp hflat _⟩
  tfae_have 2 → 1 := by
    rintro ⟨U, hxU, g, hfac, hprops, hflat⟩
    have hq := (AlgebraicGeometry.forall_quasiFiniteAt_iff g).mpr hprops ⟨x, hxU⟩
    exact ⟨(Flat.iff_flat_stalkMap f).mp inferInstance x,
      (hcriterion U hxU g hfac hq.2).mp hflat⟩
  tfae_have 1 → 4 := by
    intro hCM U hxU g hfac hqf
    exact (hcriterion U hxU g hfac hqf.2).mpr hCM.2
  tfae_have 4 → 1 := by
    intro h4
    obtain ⟨U, hx, g, hfac, hprops, hiff⟩ := construct
    exact ⟨(Flat.iff_flat_stalkMap f).mp inferInstance x,
      hiff.mp (h4 U hx g hfac
        (((AlgebraicGeometry.forall_quasiFiniteAt_iff g).mpr hprops) ⟨x, hx⟩))⟩
  tfae_finish

end AlgebraicGeometry

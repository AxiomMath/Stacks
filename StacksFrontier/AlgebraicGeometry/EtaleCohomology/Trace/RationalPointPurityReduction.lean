module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConclusionsPow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafRestrictionIsogeny

/-!
# The reduction of purity to a scheme with a rational point

In the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Deligne, Weil II), purity
of `Hⁱ(X_k̄, ℱ_ρ)` for `X` geometrically connected, proper and smooth of pure relative dimension
over a finite field `k` is reduced to the case where `X` has a `k`-rational point
(`Stacks.EtaleCohomology.LAdicSheaf.RationalPointPurityReductionInput`). Let `x₀` be a closed point
of `X` and `k' = κ(x₀)`, an extension of `k` of degree `m + 1`; then `X' = X ×_k k'` has the
`k'`-rational point given by `x₀`, and it is again geometrically connected, proper and smooth of
relative dimension `d` over `k'`. For `ρ` on `π₁(X, x̄)` with `x̄` the image of `x̄'`:

* the restriction `ρ'` of `ρ` to `π₁(X', x̄')` satisfies the conclusions of Deligne's conjecture,
  the geometric Frobenius elements of `X'` mapping to conjugates of powers of those of `X`
  (`Stacks.EtaleCohomology.HasDeligneConclusions.comp_of_conj_pow`,
  `AlgebraicGeometry.exists_etaleFundamentalGroupMap_geometricFrobeniusFamily_eq_conj_pow`);
* `ℱ_{ρ'}` is isogenous to the inverse image of `ℱ_ρ`
  (`Stacks.EtaleCohomology.exists_inverseImage_representationSheaf_isogeny`), the Frobenius
  characteristic polynomials on `Hⁱ_c` do not depend on the compactification (Tag 0F7I), and
  `Hⁱ_c(X'_{k̄}, g⁻¹ℱ_ρ) ≅ Hⁱ_c(X_{k̄}, ℱ_ρ)` carries `π_{X'}^*` to `(π_X^*) ^ (m + 1)`
  (`Stacks.EtaleCohomology.LAdicSheaf.fieldExtensionCohomologyIso_comm`);
* purity of weight `i` of `(π_X^*) ^ (m + 1)` against `q ^ (m + 1)` is purity of weight `i` of
  `π_X^*` against `q` (`Stacks.EtaleCohomology.IsCharpolyPureOfWeight.of_pow`).

## Main results

* `LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_fieldExtension`: the
  Frobenius of `X ×_k k'` on `Hⁱ_c` has the characteristic polynomial of `(π_X^*) ^ (m + 1)`.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalPointPurityReductionInput`: the reduction holds.

## Implementation notes

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

/-- The class of morphisms of étale sheaves of `Λ`-modules on `S` inverted by sheafification is
compatible with the monoidal structure. -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

/-! ### The scheme `X ×_k k'` -/

section Scheme

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k']

/-- **Every geometric point of `X` lifts to `X ×_k k'`**: the field `Ω` of the point is an
algebraically closed extension of `k`, into which `k'` embeds over `k`. -/
theorem exists_geometricPoint_map_fieldExtensionProj (x : GeometricPoint X.1) :
    ∃ x' : GeometricPoint (fieldExtensionScheme B X f k').1,
      x'.map (fieldExtensionProj B X f k').hom = x := by
  let φ : k →+* x.residueField := (Spec.preimage (x.hom ≫ f)).hom
  let : Algebra k x.residueField := φ.toAlgebra
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  let σ : k' →ₐ[k] x.residueField := IsAlgClosed.lift
  have h : x.hom ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ specAlgebraMap k k' := by
    rw [← Spec.map_preimage (x.hom ≫ f), specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => (σ.commutes a).symm)
  refine ⟨⟨x.residueField, pullback.lift x.hom (Spec.map (CommRingCat.ofHom σ.toRingHom)) h⟩, ?_⟩
  cases x
  simp only [GeometricPoint.map]
  congr 1
  exact pullback.lift_fst _ _ _

/-- **A `k'`-point of `X` gives a `k'`-rational point of `X ×_k k'`.** -/
theorem exists_section_fieldExtensionScheme (a : Spec (.of k') ⟶ X.1)
    (ha : a ≫ f = specAlgebraMap k k') :
    ∃ s : Spec (.of k') ⟶ (fieldExtensionScheme B X f k').1,
      s ≫ pullback.snd f (specAlgebraMap k k') = 𝟙 _ :=
  ⟨pullback.lift a (𝟙 _) (by rw [ha, Category.id_comp]), pullback.lift_snd _ _ _⟩

/-- The projection `X ×_k k' ⟶ X` is a closed map, being finite. -/
theorem isClosedMap_fieldExtensionProj :
    IsClosedMap (fieldExtensionProj B X f k').hom := by
  have : IsFinite (specAlgebraMap k k') :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  exact Scheme.Hom.isClosedMap (pullback.fst f (specAlgebraMap k k'))

/-- **The conclusions of Deligne's conjecture restrict along a morphism of schemes over finite
fields which is a closed map**: the geometric Frobenius elements of `X'` map to conjugates of
powers of those of `X`
(`AlgebraicGeometry.exists_etaleFundamentalGroupMap_geometricFrobeniusFamily_eq_conj_pow`). -/
theorem HasDeligneConclusions.comp_etaleFundamentalGroupMap {k k' : Type u} [Field k] [Finite k]
    [Field k'] [Finite k'] {X₀ X' : Scheme.{u}} [ConnectedSpace X₀] [ConnectedSpace X']
    (f₀ : X₀ ⟶ Spec (.of k)) [LocallyOfFiniteType f₀] (f' : X' ⟶ Spec (.of k'))
    [LocallyOfFiniteType f'] (g : X' ⟶ X₀) (hg : IsClosedMap g) (x' : GeometricPoint X')
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    {ρ : EtaleFundamentalGroup X₀ (x'.map g) →* GL (Fin r) K} {p : ℕ} {ι : K →+* ℂ}
    (h : HasDeligneConclusions (geometricFrobeniusFamily f₀ (x'.map g)) p ι ρ) :
    HasDeligneConclusions (geometricFrobeniusFamily f' x') p ι
      (ρ.comp (etaleFundamentalGroupMap g x').toMonoidHom) := by
  have hcl : ∀ y' : closedPoints X', g y'.1 ∈ closedPoints X₀ := fun y' => by
    have h' := hg _ y'.2
    rwa [Set.image_singleton] at h'
  refine HasDeligneConclusions.comp_of_conj_pow (Fr := geometricFrobeniusFamily f₀ (x'.map g))
    (Fr' := geometricFrobeniusFamily f' x') (etaleFundamentalGroupMap g x').toMonoidHom
    (etaleFundamentalGroupMap g x').continuous (fun y' => ⟨g y'.1, hcl y'⟩)
    (fun y' => residueFieldMapDegree g y') (fun y' => ?_) (fun y' => ?_) h
  · have := finite_residueField f' y'.1 y'.2
    have := finite_residueField f₀ _ (hcl y')
    exact residueFieldMapDegree_ne_zero g y'
  · exact exists_etaleFundamentalGroupMap_geometricFrobeniusFamily_eq_conj_pow g x' y' (hcl y')
      f₀ f'

end Scheme

/-! ### The Frobenius of `X ×_k k'` on cohomology -/

section Cohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]
  [IsNoetherian X.1] [IsNoetherian (fieldExtensionScheme B X f k').1]
  (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
  (hcard : Fintype.card k = p ^ q) (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * (m + 1)))

/-- **The Frobenius of `X' = X ×_k k'` on `Hⁱ_c(X'_{k̄}, g⁻¹F ⊗ ℚ_ℓ)` has the characteristic
polynomial of `(π_X^*) ^ (m + 1)` on `Hⁱ_c(X_{k̄}, F ⊗ ℚ_ℓ)`**, for `k'` with `q ^ (m + 1)`
elements: the identification
`Stacks.EtaleCohomology.LAdicSheaf.rationalFieldExtensionCohomologyIso` conjugates the two
(`Stacks.EtaleCohomology.LAdicSheaf.fieldExtensionCohomologyIso_comm`). -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_fieldExtension
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
        (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p
        (q * (m + 1)) hcard' (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F)
        i).hom.charpoly =
      ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom ^
        (m + 1)).charpoly := by
  have h := congrArg (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.fieldExtensionCohomologyIso_comm B X ℓ f j k' kbar F i p q hcard m hcard')
  have hmp := ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).mapEnd
    (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i)).map_pow
    (End.of (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i)) (m + 1)
  rw [Functor.map_comp, Functor.map_comp] at h
  rw [show (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      ((End.of (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i)) ^
        (m + 1)) = _ from hmp] at h
  have hl := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_comp] at hl
  have hp : ((End.of (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
      hcard F i)) ^ (m + 1)).hom =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom ^
        (m + 1) :=
    map_pow (ModuleCat.endRingEquiv _) (End.of _) (m + 1)
  set e := LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar F i
  have hconj : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
      (compactificationFieldBaseChange f j k') kbar p (q * (m + 1)) hcard'
      (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i).hom =
      e.toLinearEquiv.conj ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j
        kbar p q hcard F i).hom ^ (m + 1)) := by
    rw [← hp]
    refine LinearMap.ext fun v => ?_
    have hv := LinearMap.congr_fun hl (e.inv.hom v)
    simp only [LinearMap.coe_comp] at hv
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    have hi : e.hom.hom (e.inv.hom v) = v := Iso.inv_hom_id_apply e v
    exact (hv.trans (congrArg (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
      (compactificationFieldBaseChange f j k') kbar p (q * (m + 1)) hcard'
      (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i).hom hi)).symm
  rw [hconj, LinearEquiv.charpoly_conj]

end Cohomology

/-! ### The reduction -/

section Reduction

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The Frobenius characteristic polynomial of `ℱ_{ρ'}` on `X ×_k k'`**, for `ρ'` the restriction
of `ρ` to `π₁(X ×_k k')`: that of `(π_X^*) ^ (m + 1)` on `Hⁱ(X_k̄, ℱ_ρ)`, through the isogeny
`g⁻¹ℱ_ρ ∼ ℱ_{ρ'}`, the independence of the compactification (Tag 0F7I) and the identification of
`Hⁱ_c(X'_{k̄}, g⁻¹ℱ_ρ)` with `Hⁱ_c(X_{k̄}, ℱ_ρ)`. -/
theorem LAdicSheaf.charpoly_representationSheaf_fieldExtension {k : Type u} [Field k] [Fintype k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1]
    (f : X.1 ⟶ Spec (.of k)) [QuasiCompact f] [IsProper f] (k' : Type u) [Field k'] [Fintype k']
    [Algebra k k'] [Module.Finite k k'] [CharP k' p] [Algebra k' kbar] [IsScalarTower k k' kbar]
    [IsAlgClosure k' kbar]
    (hℓ : ℓ ≠ p) (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * (m + 1)))
    [IsNoetherian (fieldExtensionScheme B X f k').1]
    [ConnectedSpace (fieldExtensionScheme B X f k').1]
    (x' : GeometricPoint (fieldExtensionScheme B X f k').1) {r : ℕ}
    (ρ : EtaleFundamentalGroup X.1 (x'.map (fieldExtensionProj B X f k').hom) →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar
      (LAdicSheaf.representationSheaf B X (x'.map (fieldExtensionProj B X f k').hom) ρ hρ) i)]
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
      (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar
      (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x'
        (ρ.comp (etaleFundamentalGroupMap (fieldExtensionProj B X f k').hom x').toMonoidHom)
        (hρ.comp (etaleFundamentalGroupMap (fieldExtensionProj B X f k').hom x').continuous)) i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k'))
        (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar p (q * (m + 1))
        hcard' (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x'
          (ρ.comp (etaleFundamentalGroupMap (fieldExtensionProj B X f k').hom x').toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap (fieldExtensionProj B X f k').hom x').continuous))
        i).hom.charpoly =
      ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard
        (LAdicSheaf.representationSheaf B X (x'.map (fieldExtensionProj B X f k').hom) ρ hρ)
          i).hom ^ (m + 1)).charpoly := by
  obtain ⟨φ, ψ, N, h₁, h₂⟩ := exists_inverseImage_representationSheaf_isogeny B
    (fieldExtensionProj B X f k') x' ρ hρ
  have hfd := fun j => LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology
    B ℓ kbar p (q * (m + 1)) hcard' hℓ (fieldExtensionScheme B X f k')
    (pullback.snd f (specAlgebraMap k k')) j
    (LAdicSheaf.inverseImage (ℓ := ℓ) (fieldExtensionProj B X f k')
      (LAdicSheaf.representationSheaf B X (x'.map (fieldExtensionProj B X f k').hom) ρ hρ)) i
  have := hfd (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k')))
  have := hfd (compactificationFieldBaseChange f (CompactificationOf.ofProper f) k')
  rw [LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny B
    (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
    (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar p (q * (m + 1))
    hcard' φ ψ N h₁ h₂ i,
    LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactifications
    B ℓ kbar p (q * (m + 1)) hcard' hℓ (fieldExtensionScheme B X f k')
    (pullback.snd f (specAlgebraMap k k'))
    (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k')))
    (compactificationFieldBaseChange f (CompactificationOf.ofProper f) k')]
  exact LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_fieldExtension B X ℓ
    f (CompactificationOf.ofProper f) k' kbar _ i p q hcard m hcard'

/-- **Purity on `X` from purity on `X ×_k k'`, for a finite extension `k'` of degree `m + 1` over
which `X` has a point.** -/
theorem LAdicSheaf.representationPurityAt_of_fieldExtension
    (hrat : LAdicSheaf.GeometricRationalPurity B ℓ) {k : Type u} [Field k] [Fintype k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar] (p q : ℕ)
    [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) (hℓ : ℓ ≠ p) (X : B.Scheme)
    [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k)) [QuasiCompact f] [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (k' : Type u) [Field k'] [Finite k']
    [Algebra k k'] [Module.Finite k k'] (m : ℕ) (hm : Module.finrank k k' = m + 1)
    (a : Spec (.of k') ⟶ X.1) (ha : a ≫ f = specAlgebraMap k k') :
    LAdicSheaf.RepresentationPurityAt B ℓ X f kbar p q hcard := by
  have := Fintype.ofFinite k'
  intro x r ρ hρ hD i _ ι
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have hcard' : Fintype.card k' = p ^ (q * (m + 1)) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k'), hcard, hm, pow_mul]
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  let σ : k' →ₐ[k] kbar := IsAlgClosed.lift
  let : Algebra k' kbar := σ.toRingHom.toAlgebra
  have : IsScalarTower k k' kbar := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic k' kbar := Algebra.IsAlgebraic.tower_top (K := k) k'
  have : IsAlgClosure k' kbar := ⟨inferInstance, inferInstance⟩
  have : IsNoetherian (fieldExtensionScheme B X f k').1 :=
    isNoetherian_fieldExtensionScheme B X f k'
  have : SmoothOfRelativeDimension d (pullback.snd f (specAlgebraMap k k')) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback f (specAlgebraMap k k')) ‹_›
  have hconn' : ConnectedSpace
      (fieldBaseChange (Over.mk (pullback.snd f (specAlgebraMap k k'))) kbar) :=
    Function.Surjective.connectedSpace
      (Scheme.Hom.surjective (fieldBaseChangeExtensionIso (Over.mk f) k' kbar).inv)
      (Scheme.Hom.continuous _)
  have : Surjective (specAlgebraMap k' kbar) :=
    ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : ConnectedSpace (fieldExtensionScheme B X f k').1 :=
    Function.Surjective.connectedSpace
      (Scheme.Hom.surjective (fieldBaseChangeProj (Over.mk (pullback.snd f (specAlgebraMap k k')))
        kbar)) (Scheme.Hom.continuous _)
  obtain ⟨x', rfl⟩ := exists_geometricPoint_map_fieldExtensionProj B X f k' x
  let φ₀ := (etaleFundamentalGroupMap (fieldExtensionProj B X f k').hom x').toMonoidHom
  have hφ₀ : Continuous φ₀ :=
    (etaleFundamentalGroupMap (fieldExtensionProj B X f k').hom x').continuous
  have hD' : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions
      (geometricFrobeniusFamily (pullback.snd f (specAlgebraMap k k')) x') p ι (ρ.comp φ₀) :=
    fun ι => HasDeligneConclusions.comp_etaleFundamentalGroupMap f
      (pullback.snd f (specAlgebraMap k k')) (fieldExtensionProj B X f k').hom
      (isClosedMap_fieldExtensionProj B X f k') x' (hD ι)
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
      (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar
      (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x' (ρ.comp φ₀)
        (hρ.comp hφ₀)) i) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p
      (q * (m + 1)) hcard' hℓ _ _ _ _ i
  have hpure := hrat k' kbar p (q * (m + 1)) hcard' hℓ (fieldExtensionScheme B X f k')
    (pullback.snd f (specAlgebraMap k k')) d (exists_section_fieldExtensionScheme B X f k' a ha)
    x' (ρ.comp φ₀) (hρ.comp hφ₀) hD' i ι
  have hc := LAdicSheaf.charpoly_representationSheaf_fieldExtension B ℓ kbar p q hcard X f k' hℓ m
    hcard' x' ρ hρ i
  have hpow : IsCharpolyPureOfWeight ((p ^ q) ^ (m + 1)) ι i
      ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard
        (LAdicSheaf.representationSheaf B X (x'.map (fieldExtensionProj B X f k').hom) ρ hρ)
          i).hom ^ (m + 1)) := by
    intro z hz
    rw [← hc] at hz
    rw [← pow_mul]
    exact hpure z hz
  exact hpow.of_pow (Nat.succ_ne_zero m)

/-- **[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): the reduction of purity to a scheme
with a rational point.**  Purity for `X` geometrically connected, proper and smooth of relative
dimension `d` over a finite field `k` with a `k`-rational point implies it without the rational
point: for a closed point `x₀` of `X`, with residue field `k' = κ(x₀)` finite of degree `m + 1`
over `k`, the scheme `X ×_k k'` has the `k'`-rational point given by `x₀`
(`Stacks.EtaleCohomology.LAdicSheaf.representationPurityAt_of_fieldExtension`). -/
theorem LAdicSheaf.rationalPointPurityReductionInput :
    LAdicSheaf.RationalPointPurityReductionInput B ℓ := by
  intro hrat k _ _ kbar _ _ _ p q _ _ hcard hℓ X _ _ f _ _ _ _ d _ _
  have : Nonempty X.1 := ConnectedSpace.toNonempty
  obtain ⟨x₀, -, hx₀⟩ := IsClosed.exists_closed_singleton (X := X.1) isClosed_univ Set.univ_nonempty
  have := finite_residueField f x₀ hx₀
  let : Fintype (X.1.residueField x₀) := Fintype.ofFinite _
  let : Algebra k (X.1.residueField x₀) := (fieldToResidue f x₀).hom.toAlgebra
  have : Module.Finite k (X.1.residueField x₀) := Module.Finite.of_finite
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Module.finrank_pos (R := k) (M := X.1.residueField x₀)).ne'
  have ha := (fromSpecResidueField_comp_eq_iff f (X.1.residueField x₀) x₀ (𝟙 _)).2
    (by rw [Category.comp_id]; rfl)
  exact LAdicSheaf.representationPurityAt_of_fieldExtension B ℓ hrat kbar p q hcard hℓ X f d
    (X.1.residueField x₀) m hm _ ha

end Reduction

end Stacks.EtaleCohomology

end

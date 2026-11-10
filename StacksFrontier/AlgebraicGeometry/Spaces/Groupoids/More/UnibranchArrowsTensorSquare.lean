module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleLocalRingChartHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.UnibranchArrowsMinimalPrimePairs
public import StacksFrontier.RingTheory.Branches.WeaklyEtaleTensorProduct

/-!
# Tag 06DU at the étale local rings of the identity arrow of a groupoid

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces, let `z` be a geometric point of `U`, and
write `A = 𝒪_{R, e(z)}` for the étale local ring of the arrow space at the identity arrow at `z`
and `C = 𝒪_{R ×_{s, U, t} R, (e(z), e(z))}` for the étale local ring of the space of composable
pairs at the pair of identity arrows.  When the étale local rings of `U` are algebraically closed
fields — as for the spectrum of an algebraically closed field — this file proves the conclusion
of [Stacks Project, Tag 06DU] for `A` and `C`: contracting a minimal prime of `C` along the two
projections is a bijection onto the pairs of minimal primes of `A`, and each minimal prime of `C`
is the smallest prime containing the images of its two contractions.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.minimalPrimesSplitAtIdentityArrow_of_isAlgClosed`:
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.MinimalPrimesSplitAtIdentityArrow` holds as soon
  as the étale local rings of the object space are algebraically closed fields.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.minimalPrimesSplitAtIdentityArrow_restriction`:
  it holds at the tautological geometric point of the restriction of a groupoid over a field
  along an algebraically closed extension field.

## Implementation notes

The square

```
R ×_{s, U, t} R --pr₂--> R
      |pr₁               |t
      v                  v
      R  -------s------> U
```

is cartesian, so by `AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_weaklyEtale` the
homomorphism `A ⊗_K A → C` induced by the two projections is weakly étale, where `K` is the étale
local ring of `U` at `z` and the two factors are `K`-algebras through `s` and `t`.  The identity
section `e` of `s` and of `t` supplies the two residue maps `A → K`, and their kernels are the
maximal ideal because `e^#` is a local homomorphism to a field.  Both `A` and `C` are strictly
henselian (`AlgebraicGeometry.Space.strictlyHenselianLocalRing_etaleLocalRing`), so
`minimalPrimes_bijOn_of_weaklyEtale_tensorProduct` applies.

The three geometric points `pr₁(e(z), e(z))`, `pr₂(e(z), e(z))` and `e(z)` of `R` are equal but
not definitionally so; the two factors of the tensor product are taken at the first two, as the
cartesian square produces them, and the result is transported to the third along
`AlgebraicGeometry.Space.etaleLocalRingCongr`.

## References

* [Stacks Project, Tag 06DU](https://stacks.math.columbia.edu/tag/06DU)
* [Stacks Project, Tag 06E4](https://stacks.math.columbia.edu/tag/06E4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

universe u

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_unibranchArrowsTensorSquare
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : AlgebraicGeometry.Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-- Contracting along a ring isomorphism carries minimal primes to minimal primes. -/
private theorem mapsTo_comap_minimalPrimes_ringEquiv {A A' : Type*} [CommRing A] [CommRing A']
    (e : A ≃+* A') :
    Set.MapsTo (Ideal.comap e.toRingHom) (minimalPrimes A') (minimalPrimes A) := by
  intro J hJ
  have h := Ideal.minimalPrimes_comap_of_surjective (f := e.toRingHom) e.surjective hJ
  have hbot : (⊥ : Ideal A').comap e.toRingHom = ⊥ :=
    (RingHom.ker_eq_bot_iff_eq_zero _).mpr fun x hx => by
      simpa using congrArg e.symm hx
  rwa [hbot] at h

/-- Contracting along a ring isomorphism is a bijection of minimal primes. -/
theorem bijOn_comap_minimalPrimes_ringEquiv {A A' : Type*} [CommRing A] [CommRing A']
    (e : A ≃+* A') :
    Set.BijOn (Ideal.comap e.toRingHom) (minimalPrimes A') (minimalPrimes A) := by
  refine ⟨mapsTo_comap_minimalPrimes_ringEquiv e,
    (Ideal.comap_injective_of_surjective _ e.surjective).injOn, fun J hJ => ?_⟩
  refine ⟨J.comap e.symm.toRingHom, mapsTo_comap_minimalPrimes_ringEquiv e.symm hJ, ?_⟩
  rw [Ideal.comap_comap]
  convert Ideal.comap_id J using 2
  ext x
  simp

/-- The contraction of an ideal along a homomorphism composed with a ring isomorphism generates
the same ideal as the contraction along the homomorphism itself. -/
theorem map_comap_comp_ringEquiv {A A' P : Type*} [CommRing A] [CommRing A'] [CommRing P]
    (f : A' →+* P) (e : A ≃+* A') (q : Ideal P) :
    (q.comap (f.comp e.toRingHom)).map (f.comp e.toRingHom) = (q.comap f).map f := by
  rw [← Ideal.comap_comap, ← Ideal.map_map,
    Ideal.map_comap_of_surjective e.toRingHom e.surjective]

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The kernel of a local homomorphism to a field is the maximal ideal. -/
private theorem ker_eq_maximalIdeal_of_isLocalHom {A K : Type*} [CommRing A] [IsLocalRing A]
    [CommRing K] (hK : IsField K) (f : A →+* K) [IsLocalHom f] :
    RingHom.ker f = maximalIdeal A := by
  let := hK.toField
  ext a
  rw [RingHom.mem_ker, mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff f a,
    isUnit_iff_ne_zero, not_not]

/-- An `eqToHom` between étale local rings is the transport along the equality of geometric
points. -/
private theorem eqToHom_etaleLocalRing_apply {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {a b : Space.GeometricPoint C S hS F} (h : a = b) (c : Space.etaleLocalRing C S hS F a) :
    (eqToHom (congrArg (Space.etaleLocalRing C S hS F) h)).hom c =
      Space.etaleLocalRingCongr h c := by
  subst h
  rfl

/-- **Tag 06DU at the étale local rings of an identity arrow.** Let `G` be a groupoid in
algebraic spaces whose étale local rings of the object space are algebraically closed fields, and
let `z` be a geometric point of the object space.  Then contracting a minimal prime of the étale
local ring of the space of composable pairs at the pair of identity arrows along the two
projections is a bijection onto the pairs of minimal primes of the étale local ring of the arrow
space at the identity arrow, and each minimal prime is the smallest prime containing the images
of its two contractions. -/
theorem minimalPrimesSplitAtIdentityArrow_of_isAlgClosed (G : GroupoidInAlgebraicSpaces C S hS B)
    (z : Space.GeometricPoint C S hS G.objects.obj)
    (hK : ∀ w : Space.GeometricPoint C S hS G.objects.obj,
      ∃ hw : IsField (Space.etaleLocalRing C S hS G.objects.obj w),
        letI := hw.toField
        IsAlgClosed (Space.etaleLocalRing C S hS G.objects.obj w)) :
    MinimalPrimesSplitAtIdentityArrow G z := by
  have hpb := AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target
  let x' := identityPairPoint G z
  let y₁ := Space.geometricPointMap (pullback.fst G.source.hom G.target.hom) x'
  let y₂ := Space.geometricPointMap (pullback.snd G.source.hom G.target.hom) x'
  let w₀ := Space.geometricPointMap G.source.hom y₁
  let w₂ := Space.geometricPointMap G.target.hom y₂
  have h : w₀ = w₂ := congrArg
    (fun k : AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.objects =>
      Space.geometricPointMap k.hom x') hpb.w
  have hfst : y₁ = identityArrowPoint G z := geometricPointMap_fst_identityPairPoint G z
  have hsnd : y₂ = identityArrowPoint G z := geometricPointMap_snd_identityPairPoint G z
  have hy₁ : Space.geometricPointMap (identityArrow G).hom w₀ = y₁ := by
    change Space.geometricPointMap (identityArrow G).hom (Space.geometricPointMap G.source.hom y₁)
      = y₁
    rw [hfst, geometricPointMap_source_identityArrowPoint]
  have hy₂ : Space.geometricPointMap (identityArrow G).hom w₂ = y₂ := by
    change Space.geometricPointMap (identityArrow G).hom (Space.geometricPointMap G.target.hom y₂)
      = y₂
    rw [hsnd, geometricPointMap_target_identityArrowPoint]
  -- the base field and the two factors
  obtain ⟨hw₀, halg⟩ := hK w₀
  let : Field (Space.etaleLocalRing C S hS G.objects.obj w₀) := hw₀.toField
  let : Algebra (Space.etaleLocalRing C S hS G.objects.obj w₀)
      (Space.etaleLocalRing C S hS G.arrows.obj y₁) :=
    (Space.etaleLocalRingMap G.arrows.property G.source.hom y₁).toAlgebra
  let : Algebra (Space.etaleLocalRing C S hS G.objects.obj w₀)
      (Space.etaleLocalRing C S hS G.arrows.obj y₂) :=
    ((eqToHom (congrArg (Space.etaleLocalRing C S hS G.objects.obj) h) ≫
      CommRingCat.ofHom (Space.etaleLocalRingMap G.arrows.property G.target.hom y₂)).hom).toAlgebra
  obtain ⟨φ, hφl, hφr, hφw⟩ : ∃ φ : Space.etaleLocalRing C S hS G.arrows.obj y₁ ⊗[
        Space.etaleLocalRing C S hS G.objects.obj w₀] Space.etaleLocalRing C S hS G.arrows.obj y₂
        →+* Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom) x',
      φ.comp (Algebra.TensorProduct.includeLeft :
          Space.etaleLocalRing C S hS G.arrows.obj y₁ →ₐ[
            Space.etaleLocalRing C S hS G.objects.obj w₀] _).toRingHom =
          Space.etaleLocalRingMap (isAlgebraicSpace_composablePairs G)
            (pullback.fst G.source.hom G.target.hom) x' ∧
        φ.comp (Algebra.TensorProduct.includeRight :
          Space.etaleLocalRing C S hS G.arrows.obj y₂ →ₐ[
            Space.etaleLocalRing C S hS G.objects.obj w₀] _).toRingHom =
          Space.etaleLocalRingMap (isAlgebraicSpace_composablePairs G)
            (pullback.snd G.source.hom G.target.hom) x' ∧
        @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra :=
    Space.cartesian_etaleStalk_tensor_weaklyEtale C S hS _ _ G.source G.target hpb x'
  have := Space.strictlyHenselianLocalRing_etaleLocalRing C S hS G.arrows.obj
    G.arrows.property y₁
  have := Space.strictlyHenselianLocalRing_etaleLocalRing C S hS G.arrows.obj
    G.arrows.property y₂
  have := Space.strictlyHenselianLocalRing_etaleLocalRing C S hS
    (pullback G.source.hom G.target.hom) (isAlgebraicSpace_composablePairs G) x'
  -- the two residue maps, carried by the identity section
  let resA : Space.etaleLocalRing C S hS G.arrows.obj y₁ →ₐ[
      Space.etaleLocalRing C S hS G.objects.obj w₀] Space.etaleLocalRing C S hS G.objects.obj w₀ :=
    { (Space.etaleLocalRingMap G.objects.property (identityArrow G).hom w₀).comp
        (Space.etaleLocalRingCongr hy₁).symm.toRingHom with
      commutes' := fun c =>
        Space.comp_etaleLocalRingMap_apply_of_section G.objects.property G.arrows.property
          (identityArrow G).hom G.source.hom (identityArrow_hom_comp_source G) w₀ y₁ hy₁ rfl c }
  let resB : Space.etaleLocalRing C S hS G.arrows.obj y₂ →ₐ[
      Space.etaleLocalRing C S hS G.objects.obj w₀] Space.etaleLocalRing C S hS G.objects.obj w₀ :=
    { (Space.etaleLocalRingCongr h).symm.toRingHom.comp
        ((Space.etaleLocalRingMap G.objects.property (identityArrow G).hom w₂).comp
          (Space.etaleLocalRingCongr hy₂).symm.toRingHom) with
      commutes' := fun c => by
        have key := Space.comp_etaleLocalRingMap_apply_of_section G.objects.property
          G.arrows.property (identityArrow G).hom G.target.hom (identityArrow_hom_comp_target G)
          w₂ y₂ hy₂ rfl
          ((eqToHom (congrArg (Space.etaleLocalRing C S hS G.objects.obj) h)).hom c)
        refine (congrArg (Space.etaleLocalRingCongr h).symm key).trans ?_
        rw [eqToHom_etaleLocalRing_apply h, RingEquiv.symm_apply_apply]
        rfl }
  have hlocA : IsLocalHom resA.toRingHom := by
    have := Space.isLocalHom_etaleLocalRingMap C S hS G.objects.property G.arrows.property
      (identityArrow G).hom w₀
    have := Space.isLocalHom_ringEquiv (Space.etaleLocalRingCongr hy₁).symm
    exact RingHom.isLocalHom_comp _ _
  have hlocB : IsLocalHom resB.toRingHom := by
    have := Space.isLocalHom_etaleLocalRingMap C S hS G.objects.property G.arrows.property
      (identityArrow G).hom w₂
    have := Space.isLocalHom_ringEquiv (Space.etaleLocalRingCongr hy₂).symm
    have := Space.isLocalHom_ringEquiv (Space.etaleLocalRingCongr h).symm
    exact RingHom.isLocalHom_comp _ _
  -- the two restrictions of `φ` are the two projections, which are local
  have hA : IsLocalHom (φ.comp (Algebra.TensorProduct.includeLeft :
      Space.etaleLocalRing C S hS G.arrows.obj y₁ →ₐ[
        Space.etaleLocalRing C S hS G.objects.obj w₀] _).toRingHom) := by
    rw [hφl]
    exact Space.isLocalHom_etaleLocalRingMap C S hS (isAlgebraicSpace_composablePairs G)
      G.arrows.property _ x'
  have hB : IsLocalHom (φ.comp (Algebra.TensorProduct.includeRight :
      Space.etaleLocalRing C S hS G.arrows.obj y₂ →ₐ[
        Space.etaleLocalRing C S hS G.objects.obj w₀] _).toRingHom) := by
    rw [hφr]
    exact Space.isLocalHom_etaleLocalRingMap C S hS (isAlgebraicSpace_composablePairs G)
      G.arrows.property _ x'
  obtain ⟨hbij, hsmall⟩ := minimalPrimes_bijOn_of_weaklyEtale_tensorProduct
    (Space.etaleLocalRing C S hS G.objects.obj w₀)
    (Space.etaleLocalRing C S hS G.arrows.obj y₁) (Space.etaleLocalRing C S hS G.arrows.obj y₂)
    resA resB (ker_eq_maximalIdeal_of_isLocalHom hw₀ resA.toRingHom)
    (ker_eq_maximalIdeal_of_isLocalHom hw₀ resB.toRingHom) _ φ hφw hA hB
  rw [hφl, hφr] at hbij hsmall
  -- transport to the identity arrow
  have hL : identityPairLeft G z =
      (Space.etaleLocalRingMap (isAlgebraicSpace_composablePairs G)
        (pullback.fst G.source.hom G.target.hom) x').comp
        (Space.etaleLocalRingCongr hfst).symm.toRingHom := rfl
  have hR : identityPairRight G z =
      (Space.etaleLocalRingMap (isAlgebraicSpace_composablePairs G)
        (pullback.snd G.source.hom G.target.hom) x').comp
        (Space.etaleLocalRingCongr hsnd).symm.toRingHom := rfl
  refine ⟨?_, fun q hq P hP hPl hPr => ?_⟩
  · rw [hL, hR]
    have := ((bijOn_comap_minimalPrimes_ringEquiv (Space.etaleLocalRingCongr hfst).symm).prodMap
      (bijOn_comap_minimalPrimes_ringEquiv (Space.etaleLocalRingCongr hsnd).symm)).comp hbij
    simpa only [Function.comp_def, Prod.map, Ideal.comap_comap] using this
  · rw [hL, map_comap_comp_ringEquiv] at hPl
    rw [hR, map_comap_comp_ringEquiv] at hPr
    exact hsmall q hq P hP hPl hPr

section Restriction

variable (C) (hS) {k : Type u} [Field k] (hk : C.Contains (Spec (.of k)))
  (structureMap : Spec (.of k) ⟶ S) (G : GroupoidInAlgebraicSpaces C S hS B)
  (hU : G.objects = Space.fieldSpace C hS hk structureMap)

/-- **Tag 06DU at the identity arrows of an algebraically closed restriction.** Let `G` be a
groupoid in algebraic spaces whose object space is the spectrum of a field `k`, and let `k'` be an
algebraically closed extension of `k` whose spectrum lies in the site.  For the restriction of `G`
along `k → k'`, the étale local rings of the arrow space at the identity arrow at the tautological
geometric point and of its space of composable pairs at the pair of identity arrows satisfy
[Stacks Project, Tag 06DU]. -/
theorem minimalPrimesSplitAtIdentityArrow_restriction {k' : Type u} [Field k']
    (alg' : IsAlgClosed k') (hk' : C.Contains (Spec (.of k'))) (i : k →+* k') :
    MinimalPrimesSplitAtIdentityArrow (extensionRestriction C hS hk structureMap G hU hk' i)
      (extensionTautologicalGeometricPoint C hS hk structureMap G hU alg' hk' i) := by
  exact minimalPrimesSplitAtIdentityArrow_of_isAlgClosed _ _ fun w =>
    ⟨Space.isField_etaleLocalRing_fieldSpace C hS hk'
        (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) w,
      Space.isAlgClosed_etaleLocalRing_fieldSpace C hS hk'
        (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) w⟩

end Restriction

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end

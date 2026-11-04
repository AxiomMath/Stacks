module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.DenseFibreShrinking
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreDimensionSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.FiniteGenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusFibre
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedReduction
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen
public import StacksFrontier.RingTheory.DedekindDomain.IntegralClosureFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The first reduction step of the reduced fibre theorem

Let `A` be a Dedekind Nagata domain with fraction field `K` and let `f : X ⟶ Spec A` be flat,
locally of finite type and quasi-compact. The reduced fibre theorem produces a finite extension
`L/K` over which the normalized base change of `X` is smooth at all generic points of all
fibres, and its proof begins by arranging this at the generic fibre alone.

That first step is carried out here. The generic fibre `X_K` is a quasi-compact scheme locally
of finite type over the field `K`, so it has finitely many irreducible components, and therefore
a finite purely inseparable extension `L/K` makes the reduction of `X_L` geometrically reduced
over `L`. A reduced scheme of finite type over a field is geometrically reduced exactly when it
has a dense open subscheme smooth over that field, so the reduction of `X_L` — which is the
generic fibre of the base change of `X` to the integral closure `B` of `A` in `L` — carries a
dense open smooth over `L`.

The arithmetic of the resulting base `B` is also recorded: `B` is module-finite over `A`, is
again a Dedekind domain and is again Nagata, so that `Spec B` may replace `Spec A` in the next
step of the proof. Note that `L/K` is purely inseparable, so the Dedekind property of `B` is not
the one coming from a separable extension; it is deduced from the Nagata hypothesis instead.

## Main results

* `AlgebraicGeometry.finite_irreducibleComponents_of_quasiCompact_over_field`: a quasi-compact
  scheme locally of finite type over a field has finitely many irreducible components.
* `AlgebraicGeometry.finite_irreducibleComponents_isCompact_of_locallyOfFiniteType`: every
  quasi-compact open of a scheme locally of finite type over a Noetherian ring has finitely many
  irreducible components.
* `AlgebraicGeometry.ker_eq_nilradical_of_surjective`: a surjective closed immersion with reduced
  source presents the reduction of its target.
* `AlgebraicGeometry.exists_finite_purelyInseparable_extension_dense_open_smooth_reduction`: for
  a scheme locally of finite type over a field with finitely many irreducible components, a
  finite purely inseparable extension of the field makes the reduction of the base change carry
  a dense open subscheme smooth over the extension.
* `AlgebraicGeometry.exists_finite_extension_dense_open_smooth_reduction_genericFibre`: the same
  conclusion for the generic fibre of a quasi-compact morphism locally of finite type to the
  spectrum of a domain, stated on the base change of the whole scheme along the extension.
* `AlgebraicGeometry.isDedekindDomain_integralClosure_of_isNagataRing`: the integral closure of a
  Dedekind Nagata domain in a finite extension of its fraction field is a Dedekind domain, with
  no separability hypothesis on the extension.
* `AlgebraicGeometry.isOpenMap_of_isPullback_integralClosure_of_isNagataRing`: every base change
  of the spectrum of such an integral closure is an open map.
* `AlgebraicGeometry.isFinite_normalization_pullback_integralClosure`: the normalization of the
  base change of a scheme locally of finite type along such an integral closure is finite.
* `AlgebraicGeometry.exists_dense_open_smooth_normalization`: the normalization of a reduced
  scheme over a field with a dense open smooth over the field again has such a dense open.
* `AlgebraicGeometry.finite_setOf_notMem_smoothLocus_mem_genericPoints_fiber`: a dense open of
  the generic fibre smooth over the residue field of the generic point of the base leaves only
  finitely many points outside the smooth locus that are generic points of their own fibre.

## Implementation notes

The reduction of a scheme is `X.nilradical.subscheme`, and that construction does not transport
along an isomorphism of schemes without a dependent rewrite. The statements below therefore name
the reduction by its universal characterisation: a surjective closed immersion `ρ` with reduced
source whose kernel ideal sheaf is the nilradical. That pins `ρ` down up to unique isomorphism
by `AlgebraicGeometry.ker_eq_nilradical_of_surjective`, while composing with an isomorphism of
the target stays inside the same shape.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 04KT](https://stacks.math.columbia.edu/tag/04KT)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 035S](https://stacks.math.columbia.edu/tag/035S)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry

/-! ### Finitely many irreducible components -/

/-- **A quasi-compact scheme locally of finite type over a field has finitely many irreducible
components.** Such a scheme is locally Noetherian and compact, hence a Noetherian space. -/
@[ega "II 6.5.1" "special case", ega "II 7.4.1" "partial", ega "IV 4.4.1" "partial"]
theorem finite_irreducibleComponents_of_quasiCompact_over_field (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] :
    (irreducibleComponents X).Finite := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := IsNoetherian.mk
  exact NoetherianSpace.finite_irreducibleComponents

/-- **Every quasi-compact open of a scheme locally of finite type over a Noetherian ring has
finitely many irreducible components.** The scheme is locally Noetherian, and a quasi-compact
open of a locally Noetherian scheme is a Noetherian space. -/
@[ega "I 7.3.3" "special case", ega "II 6.5.1" "special case", ega "IV 2.3.6" "special case"]
theorem finite_irreducibleComponents_isCompact_of_locallyOfFiniteType {R : Type u} [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  finite_irreducibleComponents_of_isCompact X

/-! ### Presentations of the reduction -/

/-- **A surjective closed immersion with reduced source presents the reduction of its target**,
that is, its kernel ideal sheaf is the nilradical. -/
theorem ker_eq_nilradical_of_surjective {Z W : Scheme.{u}} (ρ : Z ⟶ W) [IsClosedImmersion ρ]
    [Surjective ρ] [IsReduced Z] : ρ.ker = W.nilradical := by
  refine ker_eq_nilradical_of_support_eq_top ρ ?_
  ext1
  rw [Scheme.Hom.support_ker, ρ.surjective.range_eq, closure_univ,
    TopologicalSpace.Closeds.coe_top]

/-- A dense open smooth over the base, carried along an isomorphism of the base change which
rewrites an iterated base change `(X ×_S T) ×_T R` as the single base change `X ×_S R`. -/
private theorem dense_open_smooth_of_pullbackLeftPullbackSndIso {X S T R : Scheme.{u}}
    (f : X ⟶ S) (ι : T ⟶ S) (g : R ⟶ T) (j : R ⟶ S) (hj : g ≫ ι = j)
    (h : ∃ (Z : Scheme.{u}) (ρ : Z ⟶ (pullback (pullback.snd f ι) g : Scheme.{u})),
      IsClosedImmersion ρ ∧ Surjective ρ ∧ IsReduced Z ∧
        ∃ U : Z.Opens, Dense (U : Set Z) ∧
          Smooth (U.ι ≫ ρ ≫ pullback.snd (pullback.snd f ι) g)) :
    ∃ (Z : Scheme.{u}) (ρ : Z ⟶ (pullback f j : Scheme.{u})),
      IsClosedImmersion ρ ∧ Surjective ρ ∧ IsReduced Z ∧
        ρ.ker = (pullback f j : Scheme.{u}).nilradical ∧
        ∃ U : Z.Opens, Dense (U : Set Z) ∧ Smooth (U.ι ≫ ρ ≫ pullback.snd f j) := by
  subst hj
  obtain ⟨Z, ρ, hci, hsurj, hred, U, hU, hsm⟩ := h
  refine ⟨Z, ρ ≫ (pullbackLeftPullbackSndIso f ι g).hom, inferInstance, inferInstance, hred,
    ker_eq_nilradical_of_surjective _, U, hU, ?_⟩
  rw [show U.ι ≫ (ρ ≫ (pullbackLeftPullbackSndIso f ι g).hom) ≫ pullback.snd f (g ≫ ι) =
      U.ι ≫ ρ ≫ pullback.snd (pullback.snd f ι) g by simp]
  exact hsm

/-! ### The reduction step -/

/-- **A finite purely inseparable extension of the ground field makes the reduction of the base
change carry a dense open smooth over the extension.** For `X` locally of finite type over a
field `k` with finitely many irreducible components there is a finite purely inseparable
extension `k'/k` such that the reduction of `X ×_k k'` is geometrically reduced over `k'`
(`exists_finite_purelyInseparable_extension_geometricallyReduced_reduction`), and a reduced
scheme locally of finite type over a field is geometrically reduced exactly when it has a dense
open subscheme smooth over that field.

The reduction is presented as a surjective closed immersion `ρ` with reduced source, rather than
as the specific `Scheme.IdealSheafData.subscheme` named in the geometrically reduced statement,
so that composing with an isomorphism of the target stays inside the same shape. -/
@[ega "IV 17.15.13" "more general", sga "4½ Th_finitude 2.7" "special case"]
theorem exists_finite_purelyInseparable_extension_dense_open_smooth_reduction
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hX : (irreducibleComponents X).Finite) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : IsPurelyInseparable k k'),
      let g : Spec (.of k') ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
      ∃ (Z : Scheme.{u}) (ρ : Z ⟶ (pullback f g : Scheme.{u})),
        IsClosedImmersion ρ ∧ Surjective ρ ∧ IsReduced Z ∧
          ρ.ker = (pullback f g : Scheme.{u}).nilradical ∧
          ∃ U : Z.Opens, Dense (U : Set Z) ∧ Smooth (U.ι ≫ ρ ≫ pullback.snd f g) := by
  obtain ⟨k', _, _, hfin, hpi, hgeo⟩ :=
    exists_finite_purelyInseparable_extension_geometricallyReduced_reduction k f hX
  refine ⟨k', inferInstance, inferInstance, hfin, hpi, ?_⟩
  intro g
  set I := Scheme.IdealSheafData.vanishingIdeal (X := (pullback f g : Scheme.{u}))
    (⊤ : Closeds (pullback f g : Scheme.{u})) with hI
  have hIn : I = (pullback f g : Scheme.{u}).nilradical := by simp [hI]
  have hsurj : Surjective I.subschemeι := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, hIn]
    simp
  refine ⟨I.subscheme, I.subschemeι, inferInstance, hsurj, inferInstance,
    ker_eq_nilradical_of_surjective _, ?_⟩
  exact (geometricallyReduced_iff_exists_dense_open_smooth _).mp hgeo

/-- **The generic fibre of a quasi-compact morphism locally of finite type acquires a dense open
smooth over the base after a finite purely inseparable extension of the fraction field.** Let
`A` be a domain with fraction field `K` and let `f : X ⟶ Spec A` be locally of finite type and
quasi-compact. There is a finite purely inseparable extension `L/K` such that the reduction of
`X ×_{Spec A} Spec L` has a dense open subscheme smooth over `Spec L`.

Here `X ×_{Spec A} Spec L` is the generic fibre of the base change of `X` to the integral closure
of `A` in `L`, and the reduction is presented as a surjective closed immersion `ρ` with reduced
source and kernel the nilradical. -/
@[ega "IV 17.15.13" "more general"]
theorem exists_finite_extension_dense_open_smooth_reduction_genericFibre {A : Type u}
    [CommRing A] [IsDomain A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsPurelyInseparable K L) (_ : Algebra A L) (_ : IsScalarTower A K L),
      let j : Spec (.of L) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A L))
      ∃ (Z : Scheme.{u}) (ρ : Z ⟶ (pullback f j : Scheme.{u})),
        IsClosedImmersion ρ ∧ Surjective ρ ∧ IsReduced Z ∧
          ρ.ker = (pullback f j : Scheme.{u}).nilradical ∧
          ∃ U : Z.Opens, Dense (U : Set Z) ∧ Smooth (U.ι ≫ ρ ≫ pullback.snd f j) := by
  obtain ⟨L, _, _, hfin, hpi, hZ⟩ :=
    exists_finite_purelyInseparable_extension_dense_open_smooth_reduction K
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      (finite_irreducibleComponents_of_quasiCompact_over_field K
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A K)))))
  obtain ⟨Z, ρ, hci, hsurj, hred, -, hU⟩ := hZ
  let _ : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨L, inferInstance, inferInstance, hfin, hpi, inferInstance, inferInstance, ?_⟩
  refine dense_open_smooth_of_pullbackLeftPullbackSndIso f
    (Spec.map (CommRingCat.ofHom (algebraMap A K)))
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) _ ?_ ⟨Z, ρ, hci, hsurj, hred, hU⟩
  rw [← Spec.map_comp]
  rfl

/-! ### The new base -/

/-- **The integral closure of a Dedekind Nagata domain in a finite extension of its fraction
field is a Dedekind domain.** No separability is assumed: module-finiteness of the closure comes
from the Nagata hypothesis, and the closure is then a Noetherian, integrally closed domain of
dimension at most one. -/
@[ega "IV 9.5.7" "B", sga "5 VI 1.4.7" "A is a Dedekind ring"]
theorem isDedekindDomain_integralClosure_of_isNagataRing {A : Type u} [CommRing A]
    [IsDedekindDomain A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type w)
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hA : IsNagataRing A) : IsDedekindDomain (integralClosure A L) := by
  have : Module.Finite A (integralClosure A L) :=
    module_finite_integralClosure_of_isNagataRing K L hA
  have : IsNoetherianRing (integralClosure A L) :=
    IsNoetherianRing.of_finite A (integralClosure A L)
  have : Ring.DimensionLEOne (integralClosure A L) := Ring.DimensionLEOne.of_isIntegral A _
  have : IsIntegrallyClosed (integralClosure A L) :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure A L) L
  exact { toIsDomain := inferInstance
          toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance }

/-- **Every base change of the spectrum of the integral closure of a Dedekind Nagata domain in a
finite extension of its fraction field is an open map.** The closure is module-finite over the
base by the Nagata hypothesis, and flat because the base is Dedekind, so its spectrum is
universally open over the base. -/
theorem isOpenMap_of_isPullback_integralClosure_of_isNagataRing {A : Type u} [CommRing A]
    [IsDedekindDomain A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type u)
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hA : IsNagataRing A) {Y W : Scheme.{u}} {c : W ⟶ Y}
    {d : W ⟶ Spec (.of (integralClosure A L))} {q : Y ⟶ Spec (.of A)}
    (hsq : IsPullback c d q
      (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))))) :
    IsOpenMap c.base :=
  have := module_finite_integralClosure_of_isNagataRing (A := A) K L hA
  IsIntegralClosure.isOpenMap_of_isPullback A K L hsq

/-- **The normalization of the base change of a scheme locally of finite type along the integral
closure of a Dedekind Nagata domain in a finite extension of its fraction field is finite.** The
base change is a Nagata scheme, and the normalization morphism of a Nagata scheme is finite. -/
theorem isFinite_normalization_pullback_integralClosure {A : Type u} [CommRing A]
    [IsDedekindDomain A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type u)
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hA : IsNagataRing A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    letI : IsDedekindDomain (integralClosure A L) :=
      isDedekindDomain_integralClosure_of_isNagataRing K L hA
    IsFinite ((pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))))).normalization
      (finite_irreducibleComponents_isCompact_of_locallyOfFiniteType
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L)))))))
  := by
  have : IsDedekindDomain (integralClosure A L) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L hA
  exact Scheme.isFinite_normalization (isNagataScheme_pullback_integralClosure K L hA f) _

/-! ### Passing the dense smooth open to the normalization -/

/-- **A dense smooth open of a reduced scheme over a field is inherited by its normalization.**
Let `Z` be a reduced scheme locally of finite type over a field `k` with a dense open subscheme
`U` smooth over `k`. Then the normalization of `Z` also has a dense open subscheme smooth
over `k`, namely the inverse image of `U`.

A smooth scheme over a field is normal, so the normalization is an isomorphism over `U`; and the
normalization is birational, so it carries the generic points of the irreducible components of
the normalization onto those of `Z`, which a dense open of a locally Noetherian scheme contains.
This is the step of the reduced fibre theorem that replaces the base change of `X` by its
normalization. -/
theorem exists_dense_open_smooth_normalization {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [IsReduced Z] [LocallyOfFiniteType p]
    (hZ : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite)
    (U : Z.Opens) (hU : Dense (U : Set Z)) (hsmooth : Smooth (U.ι ≫ p)) :
    ∃ V : (Z.normalizationScheme hZ).Opens, Dense (V : Set (Z.normalizationScheme hZ)) ∧
      Smooth (V.ι ≫ Z.normalization hZ ≫ p) := by
  have _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have _ : IsNormal (Spec (CommRingCat.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have hUnormal : IsNormal U.toScheme := isNormal_of_smooth (U.ι ≫ p)
  have hiso : IsIso (Z.normalization hZ ∣_ U) :=
    Z.isIso_normalization_restrict_of_isNormal hZ U hUnormal
  refine ⟨Z.normalization hZ ⁻¹ᵁ U, ?_, ?_⟩
  · refine (dense_iff_closure_eq.mpr
      (genericPoints.closure (α := Z.normalizationScheme hZ))).mono fun η hη ↦ ?_
    exact scheme_genericPoints_mem_dense_open Z U.isOpen hU
      ((Z.isBirational_normalization hZ).bijOn.mapsTo hη)
  · rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hsmooth

/-! ### The finitely many points where smoothness fails -/

/-- **A dense smooth open in the generic fibre leaves only finitely many bad generic points.**
Let `A` be a Dedekind domain and let `g : Y ⟶ Spec A` be flat, quasi-compact and locally of
finite type. If the generic fibre of `g` has a dense open subscheme smooth over the residue field
of the generic point of `Spec A`, then only finitely many points of `Y` are outside the smooth
locus of `g` and at the same time generic points of their own fibre.

This is the finite family of points at which the elimination of ramification has to be carried
out in the proof of the reduced fibre theorem. -/
theorem finite_setOf_notMem_smoothLocus_mem_genericPoints_fiber {A : Type u} [CommRing A]
    [IsDedekindDomain A] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [LocallyOfFiniteType g]
    [QuasiCompact g] [Flat g]
    (U : (g.fiber (genericPoint (Spec (.of A)))).Opens)
    (hU : Dense (U : Set (g.fiber (genericPoint (Spec (.of A))))))
    (hsmooth : Smooth (U.ι ≫ g.fiberToSpecResidueField (genericPoint (Spec (.of A))))) :
    letI : LocallyOfFinitePresentation g := inferInstance
    {y : Y | y ∉ g.smoothLocus ∧ g.asFiber y ∈ genericPoints (g.fiber (g y))}.Finite := by
  have _ : LocallyOfFinitePresentation g := inferInstance
  have hdense := dense_preimage_smoothLocus_fiber_of_dense_open_smooth g
    (genericPoint (Spec (.of A))) U hU hsmooth
  refine finite_setOf_mem_genericPoints_fiber g (Z := ((g.smoothLocus : Set Y)ᶜ))
    g.smoothLocus.2.isClosed_compl ?_
  rw [Set.preimage_compl]
  exact (isNowhereDense_compl_iff
    (g.smoothLocus.2.preimage (g.fiberι (genericPoint (Spec (.of A)))).continuous)).mpr hdense

end AlgebraicGeometry

end

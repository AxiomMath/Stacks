module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.GenericFibrePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreBadPoints
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreGenericFibrePoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSmoothBadPoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSmoothLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# One finite extension making the normalized base change smooth at every generic point

Let `R` be a Nagata Dedekind domain with fraction field `K` and let `g : Y ⟶ Spec R` be flat,
quasi-compact and locally of finite type with `Y` **normal**, whose generic fibre carries a dense
open subscheme smooth over `K`.  **Then there is a finite extension `K₁ / K` such that, with `B`
the integral closure of `R` in `K₁`, the normalization of `Y ×_{Spec R} Spec B` is smooth over
`Spec B` at every generic point of every one of its fibres.**

This is the whole of the last paragraph of the proof of the reduced fibre theorem, for a scheme
already in the shape its first paragraph produces.  It is *not* Tag 09IL: the normality of `Y`
and the dense smooth open in the generic fibre are hypotheses here, and the theorem's `X` is
arbitrary.  Supplying them is the first paragraph, which is
`AlgebraicGeometry.exists_finite_extension_dense_open_smooth_genericFibre_normalization`; the
two extensions are then composed by
`AlgebraicGeometry.exists_normalizationScheme_iso_normalization_pullback_tower`.

The extension is the one of
`AlgebraicGeometry.exists_finite_extension_forall_isSolution_stalk_of_dense_open_smooth`, a
simultaneous solution at every bad point of `Y`.  A point `y` of the normalized base change is
then treated by a case split on its image `w` in `Y ×_{Spec R} Spec B`:

* if `w` lies in the smooth locus of `Y_B ⟶ Spec B` then
  `AlgebraicGeometry.Scheme.smoothAt_normalization_comp_of_mem_preimage_smoothLocus` applies, the
  normalization being an isomorphism over a smooth hence normal open;
* otherwise the point `x = pr₁ w` of `Y` is outside the smooth locus of `g`, the smooth locus of
  a base change being the preimage of the smooth locus
  (`AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_preimage_of_isPullback`), it is a generic point
  of its own fibre of `g` by going down
  (`AlgebraicGeometry.mem_genericPoints_asFiber_normalization_pullbackFst`, fed through
  `AlgebraicGeometry.mem_genericPoints_asFiber_comp_of_isIntegralHom` because `Spec B ⟶ Spec R`
  is integral), and its fibre is not the generic one because a generic point of the generic
  fibre would lie in the dense smooth open.  So `K₁` is a solution at `x`, and
  `AlgebraicGeometry.smoothAt_normalization_pullback_of_isSolutionForStalk` applies.

## Main results

* `AlgebraicGeometry.mem_smoothLocus_of_mem_genericPoints_fiber_of_dense_open_smooth`: a generic
  point of a fibre carrying a dense smooth open lies in the smooth locus.
* `AlgebraicGeometry.universallyOpen_specMap_algebraMap_integralClosure`: the spectrum of the
  integral closure is universally open over the base, which is what
  `AlgebraicGeometry.exists_normalizationScheme_iso_normalization_pullback_tower` asks of the
  second extension.
* `AlgebraicGeometry.smoothAt_normalization_pullback_of_forall_isSolutionForStalk`: any finite
  extension which is a solution at every bad point makes the normalized base change smooth at
  every generic point of every fibre.
* `AlgebraicGeometry.exists_finiteExtension_smoothAt_normalization_pullback_of_dense_open_smooth`:
  the finite extension and the smoothness.

## Implementation notes

The finiteness-of-irreducible-components witness `hW` is universally quantified in the
conclusion rather than fixed: it is a proposition, so every choice names the same normalization,
and leaving it free lets a consumer use whichever witness its own statement already carries.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4)
* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A generic point of a fibre carrying a dense smooth open lies in the smooth locus.**  A
dense open of a fibre smooth over the residue field makes the trace of the smooth locus on that
fibre a dense open of it, and a dense open of a locally Noetherian scheme contains every generic
point. -/
theorem mem_smoothLocus_of_mem_genericPoints_fiber_of_dense_open_smooth {S Y : Scheme.{u}}
    (g : Y ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType g] [Flat g] (s : S)
    (U : (g.fiber s).Opens) (hU : Dense (U : Set (g.fiber s)))
    (hsmooth : Smooth (U.ι ≫ g.fiberToSpecResidueField s)) {x : Y} (hx : g.base x = s)
    (hgen : g.asFiber x ∈ genericPoints ↥(g.fiber (g.base x))) :
    letI : LocallyOfFinitePresentation g := inferInstance
    x ∈ g.smoothLocus := by
  subst hx
  have _ : LocallyOfFinitePresentation g := inferInstance
  have _ : IsLocallyNoetherian (g.fiber (g.base x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (g.fiberToSpecResidueField (g.base x))
  have hdense := dense_preimage_smoothLocus_fiber_of_dense_open_smooth g (g.base x) U hU hsmooth
  have hmem := scheme_genericPoints_mem_dense_open (g.fiber (g.base x))
    (g.fiberι (g.base x) ⁻¹ᵁ g.smoothLocus).isOpen hdense hgen
  have hmem' : g.fiberι (g.base x) (g.asFiber x) ∈ g.smoothLocus := hmem
  rwa [g.fiberι_asFiber] at hmem'


variable {R : Type u} [CommRing R] [IsDedekindDomain R] (K : Type u) [Field K] [Algebra R K]
  [IsFractionRing R K] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R)) [Flat g] [LocallyOfFiniteType g]
  [QuasiCompact g] [IsNormal Y]


/-- **`Spec` of the integral closure is universally open over the base.**  For `R` a Nagata
Dedekind domain with fraction field `K` and `K₁ / K` finite, the morphism
`Spec (integralClosure R K₁) ⟶ Spec R` is flat — a torsion-free module over a Dedekind domain is
flat — and locally of finite presentation — the closure is a finite `R`-module by the Nagata
hypothesis and `R` is Noetherian — hence universally open.

This is the hypothesis of
`AlgebraicGeometry.exists_normalizationScheme_iso_normalization_pullback_tower` for the second
of the two finite extensions of the reduced fibre theorem. -/
@[ega "IV 15.5.5" "special case"]
theorem universallyOpen_specMap_algebraMap_integralClosure {R : Type u} [CommRing R]
    [IsDedekindDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] (K₁ : Type u)
    [Field K₁] [Algebra K K₁] [Algebra R K₁] [IsScalarTower R K K₁] [FiniteDimensional K K₁]
    (hR : IsNagataRing R) :
    UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))) :=
  have := module_finite_integralClosure_of_isNagataRing (A := R) K K₁ hR
  IsIntegralClosure.universallyOpen_specMap_algebraMap R K K₁

/-- **A simultaneous solution at the bad points makes the normalized base change smooth at
every generic point of every fibre.**  Let `R` be a Nagata Dedekind domain with fraction field
`K` and let `g : Y ⟶ Spec R` be flat, quasi-compact and locally of finite type with `Y` normal,
whose generic fibre carries a dense open subscheme smooth over `K`.  Let `K₁ / K` be a finite
extension which is a solution for the extension of discrete valuation rings `R_x → 𝒪_{Y, x}` at
every point `x` outside the smooth locus of `g` which is a generic point of its own fibre, that
fibre not the generic one.  Then, with `B` the integral closure of `R` in `K₁`, the
normalization of `Y ×_{Spec R} Spec B` is smooth over `Spec B` at every generic point of every
one of its fibres. -/
theorem smoothAt_normalization_pullback_of_forall_isSolutionForStalk
    (hR : IsNagataRing R)
    (U : (g.fiber (genericPoint (Spec (.of R)))).Opens)
    (hU : Dense (U : Set (g.fiber (genericPoint (Spec (.of R))))))
    (hsmooth : Smooth (U.ι ≫ g.fiberToSpecResidueField (genericPoint (Spec (.of R)))))
    (K₁ : Type u) [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁] [Algebra R K₁]
    [IsScalarTower R K K₁]
    (hsol : letI : LocallyOfFinitePresentation g := inferInstance
      ∀ x : Y, x ∉ g.smoothLocus → ∀ (hs : (g.base x).asIdeal ≠ ⊥)
        (hg : g.asFiber x ∈ genericPoints (g.fiber (g.base x))),
        IsSolutionForStalk K g x hs hg K₁) :
    ∀ hW : ∀ V : (pullback g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).Opens,
      IsCompact (V : Set (pullback g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u})) →
      (irreducibleComponents V).Finite,
    ∀ y : (pullback g (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).normalizationScheme hW,
    (Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).asFiber y ∈
      genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map
        (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))).fiber
          ((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
            (algebraMap R ↥(integralClosure R K₁))))).base y)) →
    InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd g
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))) y := by
  intro hW y hygen
  have : Module.Finite R ↥(integralClosure R K₁) :=
    module_finite_integralClosure_of_isNagataRing K K₁ hR
  have : IsDedekindDomain ↥(integralClosure R K₁) :=
    isDedekindDomain_integralClosure_of_isNagataRing K K₁ hR
  have : IsNormal (Spec (.of ↥(integralClosure R K₁))) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed _)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
    exact RingHom.flat_algebraMap_iff.mpr (integralClosure.flat R K K₁)
  have : IsIntegralHom
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))) := by
    rw [IsIntegralHom.SpecMap_iff, CommRingCat.hom_ofHom]
    exact fun z ↦ Algebra.IsIntegral.isIntegral z
  obtain ⟨hnorm, hflat, hlft, hqc⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback K K₁ hR g
  have := hnorm
  have := hflat
  have := hlft
  have := hqc
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hNor : IsLocallyNoetherian ((pullback g (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).normalizationScheme hW) :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.normalization _ hW ≫ pullback.snd g
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))))
  by_cases hsm : (Scheme.normalization _ hW).base y ∈
      (pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).smoothLocus
  · exact Scheme.smoothAt_normalization_comp_of_mem_preimage_smoothLocus hW
      (pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))) y hsm
  · -- the point of `Y` below `y` is bad
    have hloc := Scheme.Hom.smoothLocus_eq_preimage_of_isPullback
      (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))) (Or.inl ‹Flat g›)
    rw [hloc] at hsm
    -- the generic-point condition, transported down to `Y`
    have hy1 := mem_genericPoints_asFiber_comp_of_isIntegralHom
      (Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))) hygen
    have hcomp : (Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁))))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))) =
        (Scheme.normalization _ hW ≫ pullback.fst g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁))))) ≫ g := by
      rw [Category.assoc, Category.assoc, ← pullback.condition]
    rw [hcomp] at hy1
    have hgx := mem_genericPoints_asFiber_normalization_pullbackFst g
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))) hW hNor hy1
    -- the fibre through it is not the generic one
    have hsx : (g.base ((pullback.fst g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).base
          ((Scheme.normalization _ hW).base y))).asIdeal ≠ ⊥ := by
      intro h0
      refine hsm (mem_smoothLocus_of_mem_genericPoints_fiber_of_dense_open_smooth g
        (genericPoint (Spec (.of R))) U hU hsmooth ?_ hgx)
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext h0
    have hyne : ((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).base y).asIdeal ≠ ⊥ := by
      intro h0
      refine hsx ?_
      have hb := congrArg (fun k : _ ⟶ Spec (.of R) ↦ k.base y) hcomp
      simp only [Scheme.Hom.comp_base] at hb
      have h1 : (g.base ((pullback.fst g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁))))).base
            ((Scheme.normalization _ hW).base y))).asIdeal =
          (((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
            (algebraMap R ↥(integralClosure R K₁))))).base y).asIdeal).comap
              (algebraMap R ↥(integralClosure R K₁)) := congrArg PrimeSpectrum.asIdeal hb.symm
      rw [h1, h0, ← RingHom.ker_eq_comap_bot]
      have hinjK : Function.Injective (algebraMap R K₁) := by
        rw [IsScalarTower.algebraMap_eq R K K₁]
        exact (algebraMap K K₁).injective.comp (IsFractionRing.injective R K)
      exact (RingHom.injective_iff_ker_eq_bot _).mp fun a b hab ↦ hinjK
        (by simpa only [Subalgebra.coe_algebraMap] using congrArg Subtype.val hab)
    exact smoothAt_normalization_pullback_of_isSolutionForStalk K g K₁ hR hW y hyne hygen
      hsx hgx (hsol _ hsm hsx hgx)


/-- **One finite extension makes the normalized base change smooth at every generic point of
every fibre.**  Let `R` be a Nagata Dedekind domain with fraction field `K` and let
`g : Y ⟶ Spec R` be flat, quasi-compact and locally of finite type with `Y` normal, whose
generic fibre carries a dense open subscheme smooth over `K`.  Then there is a finite extension
`K₁ / K` such that, with `B` the integral closure of `R` in `K₁`, the normalization of
`Y ×_{Spec R} Spec B` is smooth over `Spec B` at every generic point of every one of its
fibres. -/
theorem exists_finiteExtension_smoothAt_normalization_pullback_of_dense_open_smooth
    (hR : IsNagataRing R)
    (U : (g.fiber (genericPoint (Spec (.of R)))).Opens)
    (hU : Dense (U : Set (g.fiber (genericPoint (Spec (.of R))))))
    (hsmooth : Smooth (U.ι ≫ g.fiberToSpecResidueField (genericPoint (Spec (.of R))))) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : FiniteDimensional K K₁)
      (_ : Algebra R K₁) (_ : IsScalarTower R K K₁),
      ∀ hW : ∀ V : (pullback g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).Opens,
        IsCompact (V : Set (pullback g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u})) →
        (irreducibleComponents V).Finite,
      ∀ y : (pullback g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).normalizationScheme hW,
      (Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁))))).asFiber y ∈
        genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map
          (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))).fiber
            ((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
              (algebraMap R ↥(integralClosure R K₁))))).base y)) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd g
        (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))) y := by
  obtain ⟨K₁, hfield, halg, hfin, hsol⟩ :=
    exists_finite_extension_forall_isSolution_stalk_of_dense_open_smooth K g U hU hsmooth
  let := hfield
  let := halg
  have := hfin
  let : Algebra R K₁ := ((algebraMap K K₁).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K K₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact ⟨K₁, hfield, halg, hfin, inferInstance, inferInstance,
    smoothAt_normalization_pullback_of_forall_isSolutionForStalk K g hR U hU hsmooth K₁ hsol⟩

end AlgebraicGeometry

end

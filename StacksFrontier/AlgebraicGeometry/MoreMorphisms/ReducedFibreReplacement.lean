module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreNormalizationFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreNormalizedGenericFibre
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Replacing the base by an integral closure and the scheme by its normalized base change

Let `A` be a Nagata Dedekind domain with fraction field `K` and let `f : X ⟶ Spec A` be flat,
quasi-compact and locally of finite type.  The reduced fibre theorem begins by replacing `A` by
the integral closure `B₀` of `A` in a finite extension `L₀/K` and `X` by the normalization `Y₀`
of `X ×_{Spec A} Spec B₀`, chosen so that the *generic* fibre of `Y₀ ⟶ Spec B₀` already carries a
dense open subscheme smooth over the residue field there.

**That replacement is carried out here.**  The extension is the one of the first paragraph of the
proof (`AlgebraicGeometry.exists_finite_extension_dense_open_smooth_reduction_genericFibre`); the
new base `B₀` is again a Nagata Dedekind domain with fraction field `L₀`, and the new scheme `Y₀`
is normal and again flat, quasi-compact and locally of finite type over `Spec B₀`.  The
conclusion is stated as the dense smooth open of the generic fibre of `Y₀ ⟶ Spec B₀`, which is
exactly the hypothesis under which
`AlgebraicGeometry.exists_finite_extension_forall_isSolution_stalk_of_dense_open_smooth`
continues the proof.

## Main results

* `AlgebraicGeometry.isDedekindDomain_isNagataRing_isFractionRing_integralClosure`: the integral
  closure of a Nagata Dedekind domain in a finite extension of its fraction field is a Nagata
  Dedekind domain with that extension as its fraction field, module-finite and flat over the
  original.
* `AlgebraicGeometry.flat_locallyOfFiniteType_quasiCompact_normalization_pullback`: the
  normalized base change along such an integral closure is normal and again flat, quasi-compact
  and locally of finite type over the new base.
* `AlgebraicGeometry.exists_finite_extension_dense_open_smooth_genericFibre_normalization`: the
  extension can be chosen so that the generic fibre of the normalized base change carries a
  dense open subscheme smooth over the residue field of the generic point of the new base.

## Implementation notes

The arithmetic conclusions about `B₀` are not repeated in the existential statement of
`AlgebraicGeometry.exists_finite_extension_dense_open_smooth_genericFibre_normalization`: they
are *derived* from the Nagata hypothesis by the lemmas above, so a consumer introduces exactly
the same instances from `hA` and the witnesses it is handed.  Only the extension itself and the
dense smooth open are genuinely existential.

The dense smooth open of the first paragraph lives on the reduction of `X ×_{Spec A} Spec L₀`,
while `AlgebraicGeometry.exists_dense_open_smooth_fiber_genericPoint_normalization_pullback`
wants it on the reduction of `(X ×_{Spec A} Spec B₀) ×_{Spec B₀} Spec L₀`.  The two base changes
agree by `CategoryTheory.Limits.pullbackLeftPullbackSndIso`, and the transport is
`AlgebraicGeometry.exists_reduction_dense_open_smooth_pullbackLeftPullbackSndIso`, which keeps
the characterisation of the reduction as a surjective closed immersion with reduced source: the
kernel ideal sheaf is then recovered by
`AlgebraicGeometry.ker_eq_nilradical_of_surjective` rather than transported.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 032T](https://stacks.math.columbia.edu/tag/032T)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry

/-! ### The new base -/

/-- **The integral closure of a Nagata Dedekind domain in a finite extension of its fraction
field is a Nagata Dedekind domain with that extension as fraction field.**  It is moreover
module-finite and flat over the original domain, so that `Spec` of it is a finite flat cover of
`Spec A`.

Module-finiteness is the Japanese property contained in the Nagata hypothesis, the Dedekind and
Nagata conclusions are `AlgebraicGeometry.isDedekindDomain_integralClosure_of_isNagataRing` and
`isNagataRing_integralClosure`, flatness holds because a torsion-free module over a Dedekind
domain is flat, and the fraction field is `L` because the closure is integral with `L`
algebraic over `A`. -/
@[ega "IV 9.5.7" "B", sga "5 VI 1.4.7" "partial"]
theorem isDedekindDomain_isNagataRing_isFractionRing_integralClosure {A : Type u} [CommRing A]
    [IsDedekindDomain A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type w)
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hA : IsNagataRing A) :
    Module.Finite A ↥(integralClosure A L) ∧ Module.Flat A ↥(integralClosure A L) ∧
      IsDedekindDomain ↥(integralClosure A L) ∧ IsNagataRing ↥(integralClosure A L) ∧
      IsFractionRing ↥(integralClosure A L) L :=
  ⟨module_finite_integralClosure_of_isNagataRing K L hA, integralClosure.flat A K L,
    isDedekindDomain_integralClosure_of_isNagataRing K L hA, isNagataRing_integralClosure K L hA,
    integralClosure.isFractionRing_of_finite_extension K L⟩

/-! ### The new scheme -/

/-- **The normalized base change along a finite integral closure of a Dedekind base is normal
and again flat, quasi-compact and locally of finite type.**  Let `A` be a Nagata Dedekind domain
with fraction field `K`, let `L/K` be finite, let `B` be the integral closure of `A` in `L` and
let `f : X ⟶ Spec A` be flat, quasi-compact and locally of finite type.  Then the normalization
`Y` of `X ×_{Spec A} Spec B` is a normal scheme and `Y ⟶ Spec B` is flat, quasi-compact and
locally of finite type.

Normality is the defining property of the normalization; flatness is
`AlgebraicGeometry.flat_normalization_pullback_snd_of_isDedekindDomain`, which uses that the new
base is again Dedekind; and the two finiteness conditions hold because the normalization
morphism is *finite* over a Nagata base
(`AlgebraicGeometry.isFinite_normalization_pullback_integralClosure`), while the projection
inherits them from `f`. -/
theorem flat_locallyOfFiniteType_quasiCompact_normalization_pullback {A : Type u} [CommRing A]
    [IsDedekindDomain A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type u)
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hA : IsNagataRing A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    letI : IsDedekindDomain ↥(integralClosure A L) :=
      isDedekindDomain_integralClosure_of_isNagataRing K L hA
    letI hW := finite_irreducibleComponents_isCompact_of_locallyOfFiniteType
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L)))))
    IsNormal ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))
          : Scheme.{u}).normalizationScheme hW) ∧
      Flat ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))
          : Scheme.{u}).normalization hW ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))) ∧
      LocallyOfFiniteType ((pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))
            : Scheme.{u}).normalization hW ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))) ∧
      QuasiCompact ((pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))
            : Scheme.{u}).normalization hW ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))) := by
  let : IsDedekindDomain ↥(integralClosure A L) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L hA
  have hfin := isFinite_normalization_pullback_integralClosure K L hA f
  refine ⟨Scheme.isNormal_normalizationScheme _ _,
    flat_normalization_pullback_snd_of_isDedekindDomain f _ _, ?_, ?_⟩ <;> infer_instance

/-! ### The dense smooth open of the generic fibre -/

/-- **A presentation of the reduction of an iterated base change, read on the single base
change.**  A surjective closed immersion with reduced source presenting the reduction of
`X ×_S R` carries over, along `CategoryTheory.Limits.pullbackLeftPullbackSndIso`, to one
presenting the reduction of `(X ×_S T) ×_T R`, together with a dense open smooth over `R`. -/
theorem exists_reduction_dense_open_smooth_pullbackLeftPullbackSndIso {X S T R : Scheme.{u}}
    (f : X ⟶ S) (ι : T ⟶ S) (g : R ⟶ T) (j : R ⟶ S) (hj : g ≫ ι = j)
    {Z : Scheme.{u}} (ρ : Z ⟶ (pullback f j : Scheme.{u})) [IsClosedImmersion ρ]
    (hsurj : Surjective ρ) [IsReduced Z]
    (U : Z.Opens) (hU : Dense (U : Set Z)) (hsm : Smooth (U.ι ≫ ρ ≫ pullback.snd f j)) :
    ∃ (Z' : Scheme.{u}) (ρ' : Z' ⟶ (pullback (pullback.snd f ι) g : Scheme.{u})),
      IsClosedImmersion ρ' ∧
        ρ'.ker = (pullback (pullback.snd f ι) g : Scheme.{u}).nilradical ∧
        ∃ U' : Z'.Opens, Dense (U' : Set Z') ∧
          Smooth (U'.ι ≫ ρ' ≫ pullback.snd (pullback.snd f ι) g) := by
  subst hj
  have _ := hsurj
  refine ⟨Z, ρ ≫ (pullbackLeftPullbackSndIso f ι g).inv, inferInstance,
    ker_eq_nilradical_of_surjective _, U, hU, ?_⟩
  rw [show U.ι ≫ (ρ ≫ (pullbackLeftPullbackSndIso f ι g).inv) ≫
      pullback.snd (pullback.snd f ι) g = U.ι ≫ ρ ≫ pullback.snd f (g ≫ ι) by simp]
  exact hsm

/-- **The first reduction of the reduced fibre theorem.**  Let `A` be a Nagata Dedekind domain
with fraction field `K` and let `f : X ⟶ Spec A` be flat, quasi-compact and locally of finite
type.  There is a finite extension `L₀/K` such that the generic fibre of the normalized base
change of `X` to the integral closure `B₀` of `A` in `L₀` carries a dense open subscheme smooth
over the residue field of the generic point of `Spec B₀`.

The extension is the finite purely inseparable one of the first paragraph of the proof, which
makes the reduction of `X ×_{Spec A} Spec L₀` carry a dense open smooth over `L₀`
(`AlgebraicGeometry.exists_finite_extension_dense_open_smooth_reduction_genericFibre`).  That
scheme is `(X ×_{Spec A} Spec B₀) ×_{Spec B₀} Spec L₀`, and the dense smooth open on its
reduction becomes one on the generic fibre of the normalized base change by
`AlgebraicGeometry.exists_dense_open_smooth_fiber_genericPoint_normalization_pullback`, whose
mathematical content is that normalization commutes with base change to the fraction field of
the base.

Together with
`AlgebraicGeometry.flat_locallyOfFiniteType_quasiCompact_normalization_pullback` and
`AlgebraicGeometry.isDedekindDomain_isNagataRing_isFractionRing_integralClosure` this is the
source's "replace `A` by `B` and `X` by `Y`": the replacement satisfies every hypothesis of the
theorem, is normal, and has a dense smooth open in its generic fibre. -/
theorem exists_finite_extension_dense_open_smooth_genericFibre_normalization {A : Type u}
    [CommRing A] [IsDedekindDomain A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (hA : IsNagataRing A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (L₀ : Type u) (_ : Field L₀) (_ : Algebra K L₀) (_ : FiniteDimensional K L₀)
      (_ : Algebra A L₀) (_ : IsScalarTower A K L₀),
      letI : IsDedekindDomain ↥(integralClosure A L₀) :=
        isDedekindDomain_integralClosure_of_isNagataRing K L₀ hA
      letI hW := finite_irreducibleComponents_isCompact_of_locallyOfFiniteType
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀)))))
      let g := (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₀)))) : Scheme.{u}).normalization hW ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀))))
      ∃ V : (g.fiber (genericPoint (Spec (.of ↥(integralClosure A L₀))))).Opens,
        Dense (V : Set (g.fiber (genericPoint (Spec (.of ↥(integralClosure A L₀)))))) ∧
          Smooth (V.ι ≫ g.fiberToSpecResidueField
            (genericPoint (Spec (.of ↥(integralClosure A L₀))))) := by
  obtain ⟨L₀, _, _, hLfin, -, _, _, hred⟩ :=
    exists_finite_extension_dense_open_smooth_reduction_genericFibre K f
  obtain ⟨Z, ρ, hci, hsurj, hZred, -, U, hU, hsm⟩ := hred
  refine ⟨L₀, inferInstance, inferInstance, hLfin, inferInstance, inferInstance, ?_⟩
  let : IsDedekindDomain ↥(integralClosure A L₀) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L₀ hA
  have : IsFractionRing ↥(integralClosure A L₀) L₀ :=
    integralClosure.isFractionRing_of_finite_extension K L₀
  have _ := hci
  have _ := hZred
  obtain ⟨Z', ρ', hci', hker', U', hU', hsm'⟩ :=
    exists_reduction_dense_open_smooth_pullbackLeftPullbackSndIso f
      (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀))))
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(integralClosure A L₀) L₀)))
      (Spec.map (CommRingCat.ofHom (algebraMap A L₀)))
      (by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq A ↥(integralClosure A L₀) L₀])
      ρ hsurj U hU hsm
  have _ := hci'
  exact exists_dense_open_smooth_fiber_genericPoint_normalization_pullback L₀ f _ _ ρ' hker'
    U' hU' hsm'

end AlgebraicGeometry

end

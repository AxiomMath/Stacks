module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FractionFieldFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReductionNormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FractionFieldBaseChange

/-!
# The generic fibre of a normalized base change

Let `g : Spec B ⟶ Spec A` with `B` a domain with fraction field `L`, let `f : X ⟶ Spec A`, write
`W = X ×_{Spec A} Spec B` and let `Y = W^ν` be its normalization, with structure morphism
`r = ν ≫ pr₂ : Y ⟶ Spec B`.  **The base change of `r` to `Spec L` is the normalization of
`W ×_{Spec B} Spec L`.**  Consequently a dense open subscheme of the reduction of
`W ×_{Spec B} Spec L` which is smooth over `L` produces a dense open subscheme of the *generic
fibre* of `r` which is smooth over the residue field at the generic point of `Spec B`.

## Main results

* `AlgebraicGeometry.isPullback_normalizationSchemeMap_normalization_comp_pullbackSnd`: the
  normalization of `W ×_{Spec B} Spec L` is the base change of `Y ⟶ Spec B` to `Spec L`.
* `AlgebraicGeometry.exists_dense_open_smooth_fiber_genericPoint_normalization_pullback`: a dense
  smooth open on a presentation of the reduction of `W ×_{Spec B} Spec L` gives one on the
  generic fibre of `Y ⟶ Spec B`.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 0307](https://stacks.math.columbia.edu/tag/0307)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] [IsDomain B] (L : Type u) [Field L]
  [Algebra B L] [IsFractionRing B L] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (g : Spec (.of B) ⟶ Spec (.of A))

omit [IsDomain B] in
/-- **The normalization of `W ×_{Spec B} Spec L` is the base change of `Y ⟶ Spec B` to
`Spec L`.** With `W = X ×_{Spec A} Spec B` and `Y = W^ν`, the square whose vertical arrows are
the two structure morphisms to `Spec B` and `Spec L` and whose horizontal arrows are the
comparison of normalizations and `Spec L ⟶ Spec B` is cartesian. -/
theorem isPullback_normalizationSchemeMap_normalization_comp_pullbackSnd
    (hW : ∀ U : (pullback f g : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f g : Scheme.{u})) → (irreducibleComponents U).Finite) :
    letI := flat_specMap_algebraMap_fractionRing (B := B) L
    IsPullback
      (normalizationSchemeMap
        (pullback.fst (pullback.snd f g) (Spec.map (CommRingCat.ofHom (algebraMap B L))))
        (finite_irreducibleComponents_pullbackFst_fractionRing L (pullback.snd f g) hW) hW)
      ((pullback (pullback.snd f g)
          (Spec.map (CommRingCat.ofHom (algebraMap B L)))).normalization
            (finite_irreducibleComponents_pullbackFst_fractionRing L (pullback.snd f g) hW) ≫
        pullback.snd (pullback.snd f g) (Spec.map (CommRingCat.ofHom (algebraMap B L))))
      ((pullback f g : Scheme.{u}).normalization hW ≫ pullback.snd f g)
      (Spec.map (CommRingCat.ofHom (algebraMap B L))) :=
  let := flat_specMap_algebraMap_fractionRing (B := B) L
  (isPullback_normalizationSchemeMap_specMap_fractionRing L (pullback.snd f g) hW).paste_vert
    (IsPullback.of_hasPullback _ _)

/-- **A dense smooth open on the generic fibre of a normalized base change.** With
`W = X ×_{Spec A} Spec B` and `Y = W^ν`, suppose some closed immersion `ρ` presents the reduction
of `W ×_{Spec B} Spec L` and carries a dense open subscheme smooth over `L`.  Then the fibre of
`Y ⟶ Spec B` over the generic point of `Spec B` has a dense open subscheme smooth over the
residue field there. -/
theorem exists_dense_open_smooth_fiber_genericPoint_normalization_pullback
    [LocallyOfFiniteType (pullback.snd f g)]
    (hW : ∀ U : (pullback f g : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f g : Scheme.{u})) → (irreducibleComponents U).Finite)
    {Z : Scheme.{u}}
    (ρ : Z ⟶ (pullback (pullback.snd f g)
      (Spec.map (CommRingCat.ofHom (algebraMap B L))) : Scheme.{u}))
    [IsClosedImmersion ρ]
    (hρ : ρ.ker = (pullback (pullback.snd f g)
      (Spec.map (CommRingCat.ofHom (algebraMap B L))) : Scheme.{u}).nilradical)
    (U : Z.Opens) (hU : Dense (U : Set Z))
    (hsm : Smooth (U.ι ≫ ρ ≫ pullback.snd (pullback.snd f g)
      (Spec.map (CommRingCat.ofHom (algebraMap B L))))) :
    ∃ V : (((pullback f g : Scheme.{u}).normalization hW ≫ pullback.snd f g).fiber
        (genericPoint (Spec (.of B)))).Opens,
      Dense (V : Set (((pullback f g : Scheme.{u}).normalization hW ≫
          pullback.snd f g).fiber (genericPoint (Spec (.of B))))) ∧
        Smooth (V.ι ≫ ((pullback f g : Scheme.{u}).normalization hW ≫
          pullback.snd f g).fiberToSpecResidueField (genericPoint (Spec (.of B)))) := by
  obtain ⟨V₁, hV₁, hsmV₁⟩ := exists_dense_open_smooth_normalization_of_ker_eq_nilradical
    (pullback.snd (pullback.snd f g) (Spec.map (CommRingCat.ofHom (algebraMap B L))))
    (finite_irreducibleComponents_pullbackFst_fractionRing L (pullback.snd f g) hW) ρ hρ U hU hsm
  refine exists_dense_open_smooth_fiber_genericPoint_of_isPullback L
    ((pullback f g : Scheme.{u}).normalization hW ≫ pullback.snd f g)
    (isPullback_normalizationSchemeMap_normalization_comp_pullbackSnd L f g hW) V₁ hV₁ ?_
  rwa [← Category.assoc]

end AlgebraicGeometry

end

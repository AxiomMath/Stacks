module

public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.RelativeDifferentialsStalk
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion
public import StacksFrontier.RingTheory.NodalChart.Differentials

/-!
# The standard nodal chart is at-worst-nodal of relative dimension one

For a commutative ring `R` and an element `h : R` the nodal chart `Spec R[x, y]/(xy - h)` is
at-worst-nodal of relative dimension one over `Spec R`, with no hypothesis on `R` or `h`.

Both halves of the definition (Tag 0C5A) are checked directly. Syntomicity of relative dimension
one is the ring-theoretic statement that `R → R[x, y]/(xy - h)` is a relative global complete
intersection presented by two variables and one relation, whose fibres therefore have dimension
`2 - 1 = 1`. For the singular subscheme, the first Fitting ideal of `Ω_{A/R}` is the ideal
`(x, y)` of the two coordinates, so `Sing(f) ⊆ Spec A` is cut out by `(x, y)`; killing the two
coordinates leaves `R/(h)`, so `Sing(f) ⟶ Spec R` is a closed immersion and in particular
unramified.

## Main results

* `Stacks.syntomicOfRelativeDimension_one_specMap_nodalChartRing` — the nodal chart is syntomic
  of relative dimension one over the base.
* `Stacks.isAtWorstNodalOfRelativeDimensionOne_specMap_nodalChartRing` — the nodal chart is
  at-worst-nodal of relative dimension one over the base.

## Implementation notes

The global sections of `Spec R[x, y]/(xy - h)` are isomorphic to `R[x, y]/(xy - h)` but not equal
to it, and the Fitting ideal sheaf is computed from the sections, so the ring-theoretic input is
applied over the section ring `Γ(Spec R, ⊤)` rather than over `R`: the nodal chart ring is
transported along a ring isomorphism of the base by `Stacks.nodalChartRingCongr`, and
`Stacks.nodalSectionsAlgEquiv` is the resulting identification of `Γ(Spec A, ⊤)` with the nodal
chart ring over `Γ(Spec R, ⊤)`. That both square with the structure morphism is the naturality of
`AlgebraicGeometry.Scheme.ΓSpecIso`.

Unramifiedness of the singular subscheme is obtained without identifying that subscheme: it is a
closed subscheme of an affine scheme, hence affine, and the composite to the base is surjective on
global sections because the ideal cutting it out contains the two coordinates, so the composite is
a closed immersion by `AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine` and a closed
immersion is unramified.

## References

* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u

namespace Stacks

variable {R : Type u} [CommRing R]

/-! ### Transport of the nodal chart ring along a ring isomorphism of the base -/

/-- **The nodal chart ring transported along a ring isomorphism of the base.** A ring isomorphism
`e : R ≃+* R'` carrying `h` to `h'` induces an isomorphism `R[x, y]/(xy - h) ≃ R'[x, y]/(xy - h')`
fixing the two coordinates. -/
public def nodalChartRingCongr {R R' : Type u} [CommRing R] [CommRing R'] (e : R ≃+* R')
    {h : R} {h' : R'} (hh : e h = h') :
    nodalChartRing R h ≃+* nodalChartRing R' h' :=
  Ideal.quotientEquiv _ _ (MvPolynomial.mapEquiv (Fin 2) e) <| by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [nodalEquation_def, ← hh]

/-- The transport of the nodal chart ring fixes the two coordinates. -/
@[simp] public theorem nodalChartRingCongr_nodalGen {R R' : Type u} [CommRing R] [CommRing R']
    (e : R ≃+* R') {h : R} {h' : R'} (hh : e h = h') (i : Fin 2) :
    nodalChartRingCongr e hh (nodalGen R h i) = nodalGen R' h' i := by
  simp [nodalChartRingCongr, nodalGen, Ideal.quotientEquiv_apply]

/-- The transport of the nodal chart ring acts on the base through the given isomorphism. -/
@[simp] public theorem nodalChartRingCongr_algebraMap {R R' : Type u} [CommRing R] [CommRing R']
    (e : R ≃+* R') {h : R} {h' : R'} (hh : e h = h') (r : R) :
    nodalChartRingCongr e hh (algebraMap R (nodalChartRing R h) r) =
      algebraMap R' (nodalChartRing R' h') (e r) := by
  simp [nodalChartRingCongr, algebraMap_nodalChartRing_eq, Ideal.quotientEquiv_apply]

/-! ### The nodal chart as a scheme over its base -/

/-- The ring isomorphism between the global sections of `Spec R` and `R`. -/
public def specSectionsRingEquiv (R : Type u) [CommRing R] :
    Γ(Spec (CommRingCat.of R), ⊤) ≃+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv

/-- The structure morphism of the nodal chart acts on global sections through the structure map of
the nodal chart ring. -/
public theorem specSectionsRingEquiv_appTop (h : R)
    (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    specSectionsRingEquiv (nodalChartRing R h)
        ((Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))).appTop r) =
      algebraMap R (nodalChartRing R h) (specSectionsRingEquiv R r) :=
  congrFun (congrArg (fun φ : Γ(Spec (CommRingCat.of R), ⊤) ⟶
      CommRingCat.of (nodalChartRing R h) =>
    (CommRingCat.Hom.hom φ : Γ(Spec (CommRingCat.of R), ⊤) → nodalChartRing R h))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (algebraMap R (nodalChartRing R h))))) r

/-- **The global sections of the nodal chart form a nodal chart ring over the global sections of
the base.** -/
public def nodalSectionsAlgEquiv (h : R) :
    letI := Stacks.Smooth.algebraAppLE
      (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))) (V := ⊤) (W := ⊤) le_top
    nodalChartRing Γ(Spec (CommRingCat.of R), ⊤) ((specSectionsRingEquiv R).symm h) ≃ₐ[
        Γ(Spec (CommRingCat.of R), ⊤)] Γ(Spec (CommRingCat.of (nodalChartRing R h)), ⊤) :=
  letI := Stacks.Smooth.algebraAppLE
    (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))) (V := ⊤) (W := ⊤) le_top
  { (nodalChartRingCongr (specSectionsRingEquiv R)
      ((specSectionsRingEquiv R).apply_symm_apply h)).trans
      (specSectionsRingEquiv (nodalChartRing R h)).symm with
    commutes' := fun r => by
      change (specSectionsRingEquiv (nodalChartRing R h)).symm
          (nodalChartRingCongr (specSectionsRingEquiv R)
            ((specSectionsRingEquiv R).apply_symm_apply h)
            (algebraMap Γ(Spec (CommRingCat.of R), ⊤)
              (nodalChartRing Γ(Spec (CommRingCat.of R), ⊤)
                ((specSectionsRingEquiv R).symm h)) r)) = _
      rw [nodalChartRingCongr_algebraMap (specSectionsRingEquiv R)
          ((specSectionsRingEquiv R).apply_symm_apply h) r,
        ← specSectionsRingEquiv_appTop h r, RingEquiv.symm_apply_apply]
      rfl }

/-! ### Syntomicity of relative dimension one -/

/-- A ring map that is the structure map of an algebra is syntomic exactly when the algebra is. -/
public theorem RingHom.syntomic_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] : (algebraMap R S).Syntomic ↔ Algebra.Syntomic R S := by
  rw [_root_.RingHom.Syntomic, toAlgebra_algebraMap]

/-- **The nodal chart is syntomic over its base.** -/
public theorem syntomic_specMap_nodalChartRing (h : R) :
    Syntomic (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))) :=
  HasRingHomProperty.Spec_iff.2
    (Stacks.RingHom.syntomic_algebraMap.2 (syntomic_nodalChartRing h))

/-- **The nodal chart is syntomic of relative dimension one over its base**: two variables subject
to one relation. -/
public theorem syntomicOfRelativeDimension_one_specMap_nodalChartRing (h : R) :
    SyntomicOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))) := by
  refine ⟨syntomic_specMap_nodalChartRing h, fun x => ?_⟩
  have := nodalPresentation_isRelativeGlobalCompleteIntersection h
  simpa using fiberDimensionAt_eq_card_sub_card (nodalPresentation R h) x

/-! ### The singular subscheme -/

/-- **The relative singular subscheme of the nodal chart is cut out by the two coordinates.** -/
public theorem ideal_relativeSingularIdeal_specMap_nodalChartRing (h : R) :
    (relativeSingularIdeal
          (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h))))).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span
        {nodalSectionsAlgEquiv h
            (nodalGen Γ(Spec (CommRingCat.of R), ⊤) ((specSectionsRingEquiv R).symm h) 0),
          nodalSectionsAlgEquiv h
            (nodalGen Γ(Spec (CommRingCat.of R), ⊤) ((specSectionsRingEquiv R).symm h) 1)} := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))
  have : LocallyOfFinitePresentation f :=
    locallyOfFinitePresentation (syntomic_specMap_nodalChartRing h)
  have : LocallyOfFiniteType f := inferInstance
  let _ := Stacks.Smooth.algebraAppLE f (V := ⊤) (W := ⊤) le_top
  have : Module.Finite Γ(Spec (CommRingCat.of (nodalChartRing R h)), ⊤)
      Γ(Scheme.Hom.relativeDifferentials f, ⊤) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections _ (isAffineOpen_top _)
  have := moduleFinite_kaehlerDifferential_appLE f (isAffineOpen_top _) (isAffineOpen_top _)
    (le_top (a := (⊤ : (Spec (CommRingCat.of (nodalChartRing R h))).Opens)))
  rw [relativeSingularIdeal,
    fittingIdeal_ideal (Scheme.Hom.relativeDifferentials f) 1 ⟨⊤, isAffineOpen_top _⟩,
    show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
    fittingIdeal_eq_of_linearEquiv
      (sectionsRelativeDifferentialsEquiv f (isAffineOpen_top _) (isAffineOpen_top _) le_top) 1]
  exact fittingIdeal_kaehlerDifferential_nodalChartRing _ (nodalSectionsAlgEquiv h)

/-- **The relative singular subscheme of the nodal chart is unramified over the base.** It is a
closed subscheme of an affine scheme, and killing the two coordinates leaves a quotient of the
base, so the composite is a closed immersion. -/
public theorem unramified_subschemeι_comp_specMap_nodalChartRing (h : R) :
    Unramified
      ((relativeSingularIdeal
            (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h))))).subschemeι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))) := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))
  set J := relativeSingularIdeal f
  let _ := Stacks.Smooth.algebraAppLE f (V := ⊤) (W := ⊤) le_top
  have hmk : Function.Surjective
      ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top _⟩)).comp f.appTop.hom) := by
    rw [ideal_relativeSingularIdeal_specMap_nodalChartRing h]
    exact surjective_quotient_span_nodalGen _ (nodalSectionsAlgEquiv h)
  have hsurj : Function.Surjective (J.subschemeι ≫ f).appTop := by
    intro z
    obtain ⟨w, hw⟩ := J.subschemeι_app_surjective ⟨⊤, isAffineOpen_top _⟩ z
    obtain ⟨r, hr⟩ := hmk (Ideal.Quotient.mk _ w)
    refine ⟨r, ?_⟩
    have hzero : (J.subschemeι.app (⟨⊤, isAffineOpen_top _⟩ :
        (Spec (CommRingCat.of (nodalChartRing R h))).affineOpens)).hom
        (f.appTop.hom r - w) = 0 := by
      rw [← RingHom.mem_ker, J.ker_subschemeι_app]
      exact Ideal.Quotient.eq.1 hr
    rw [map_sub, sub_eq_zero] at hzero
    rw [Scheme.Hom.comp_appTop]
    exact hzero.trans hw
  have : IsAffine J.subscheme :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (f := J.subschemeι)).1
  have : IsClosedImmersion (J.subschemeι ≫ f) :=
    IsClosedImmersion.of_surjective_of_isAffine _ hsurj
  infer_instance

/-- **The nodal chart `Spec R[x, y]/(xy - h)` is at-worst-nodal of relative dimension one over
`Spec R`**, for every commutative ring `R` and every `h : R`. -/
public theorem isAtWorstNodalOfRelativeDimensionOne_specMap_nodalChartRing (h : R) :
    IsAtWorstNodalOfRelativeDimensionOne
      (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))) :=
  ⟨syntomicOfRelativeDimension_one_specMap_nodalChartRing h,
    unramified_subschemeι_comp_specMap_nodalChartRing h⟩

end Stacks

end

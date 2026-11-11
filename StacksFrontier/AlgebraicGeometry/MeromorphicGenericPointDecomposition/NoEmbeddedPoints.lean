module

public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.ModuleValued
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Criteria
public import StacksFrontier.AlgebraicGeometry.RationalFunctions.Meromorphic
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian

/-!
# Meromorphic functions on a locally Noetherian scheme without embedded points

[Stacks, Tag 0EMH]: let `X` be a locally Noetherian scheme having no embedded points, and `X⁰` the
set of generic points of its irreducible components. Then
`𝒦_X = ⊕_{η ∈ X⁰} j_{η,*} 𝒪_{X,η} = ∏_{η ∈ X⁰} j_{η,*} 𝒪_{X,η}`, where `j_η : Spec 𝒪_{X,η} → X` is
the canonical morphism, and moreover

1. `𝒦_X` is a quasi-coherent sheaf of `𝒪_X`-algebras,
2. for every quasi-coherent `𝒪_X`-module `F` the sheaf
   `𝒦_X(F) = ⊕_{η ∈ X⁰} j_{η,*} F_η = ∏_{η ∈ X⁰} j_{η,*} F_η` of meromorphic sections of `F` is
   quasi-coherent, and
3. the ring of rational functions of `X` is the ring of meromorphic functions on `X`:
   `R(X) = Γ(X, 𝒦_X)`.

The identifications of the source are the canonical maps, and this file states them as such:
the canonical map of sheaves of rings `𝒦_X ⟶ ∏_η j_{η,*} 𝒪_{X,η}` is an isomorphism and is a map
of `𝒪_X`-algebras; the canonical map of `𝒪_X`-modules `𝒦_X ⟶ ∏_η j_{η,*} 𝒪_{X,η}` and the
canonical map from the direct sum to the product are isomorphisms; for `F` quasi-coherent the
canonical comparison `𝒦_X(F) ⟶ ∏_η j_{η,*} j_η^* F` and the canonical map from the direct sum to
the product are isomorphisms; and the ring isomorphism `R(X) ≅ Γ(X, 𝒦_X)` sends the rational
function of a section `s` over a dense open `U` to the meromorphic function whose restriction to
`U` is the image of `s`.

The source proves the lemma as the special case of [Stacks, Tag 0EMF] in which the weakly
associated points are the associated points ([Stacks, Tag 05AR]); this is the proof here.

## Main results

* `AlgebraicGeometry.genericPointDecomposition_of_hasNoEmbeddedPoints`: the whole of
  [Stacks, Tag 0EMH].
* `AlgebraicGeometry.exists_commRing_rationalFunctions_ringEquiv_totalQuotientSheaf_top_compat`:
  part (6) of [Stacks, Tag 0EMF] with the ring isomorphism `R(X) ≅ Γ(X, 𝒦_X)` compatible with the
  maps from the sections over dense opens.

## Implementation notes

The ring structure on `R(X)` is not constructed in
`StacksFrontier.AlgebraicGeometry.RationalFunctions.Basic`, so clause (3) asserts the existence of a
commutative ring structure on `R(X)` for which every section over a dense open is a ring
homomorphism to `R(X)` (the characterization of [Stacks, Tag 01RU]), together with a ring
isomorphism to `Γ(X, 𝒦_X)` compatible with those maps. Since every rational function is the
rational function of a section over a dense open, that compatibility determines the
isomorphism.

## References

* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.GenericPointDecomposition
  (genericPointStalkModuleOf meromorphicSections)
open Stacks.AlgebraicGeometry.MeromorphicQuasicoherent
  (meromorphicFunctions_isQuasicoherent_of_noEmbeddedPoints)

universe u

noncomputable section

namespace AlgebraicGeometry

/-- **Part (6) of [Stacks, Tag 0EMF], with a compatible isomorphism.** For a scheme whose weakly
associated points are generic points of irreducible components and whose quasi-compact opens
have finitely many irreducible components, there is a commutative ring structure on the rational
functions for which every section over a dense open is a ring homomorphism, and a ring
isomorphism from the rational functions to the global meromorphic functions sending the rational
function of a section `s` over a dense open `U` to the global meromorphic function whose
restriction to `U` is the image of `s`. -/
theorem exists_commRing_rationalFunctions_ringEquiv_totalQuotientSheaf_top_compat
    (X : Scheme.{u})
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    ∃ _ : CommRing X.rationalFunctions,
      (∀ (U : X.Opens) (hU : Dense (U : Set X)),
          ∃ ψ : Γ(X, U) →+* X.rationalFunctions,
            ∀ s, ψ s = X.rationalFunctionOfSection U hU s) ∧
        ∃ e : X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤),
          ∀ (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(X, U)),
            resTotalQuotientSheaf (e (X.rationalFunctionOfSection U hU s)) U =
              (X.toTotalQuotientSheaf.hom.app (op U)).hom s := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_totalQuotientSheaf_top hass hfinite X.rationalFunctions
    (fun P hP f => X.rationalFunctionOfSection P hP f)
    (fun P Q hP hQ hQP f => X.rationalFunctionOfSection_res hP hQ hQP f)
    (fun r => X.exists_rationalFunctionOfSection_eq r)
    (fun P hP f f' h => X.exists_dense_res_eq_of_rationalFunctionOfSection_eq hP f f' h)
  let _ : CommRing X.rationalFunctions := Equiv.commRing e.symm
  let hring : X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤) :=
    e.symm.ringEquiv
  -- The global meromorphic function attached to a section over a dense open.
  have hcompat : ∀ (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(X, U)),
      resTotalQuotientSheaf (hring (X.rationalFunctionOfSection U hU s)) U =
        (X.toTotalQuotientSheaf.hom.app (op U)).hom s := by
    intro U hU s
    obtain ⟨t, ht⟩ := (bijective_totalQuotientSheaf_presheaf_map_of_genericPoints_mem hass hfinite
      (mem_of_dense_of_mem_genericPoints hfinite hU)).2
      ((X.toTotalQuotientSheaf.hom.app (op U)).hom s)
    have het : e t = X.rationalFunctionOfSection U hU s := he t U hU s ht.symm
    have hts : hring (X.rationalFunctionOfSection U hU s) = t := by
      change e.symm (X.rationalFunctionOfSection U hU s) = t
      rw [← het, Equiv.symm_apply_apply]
    rw [hts]
    exact ht
  refine ⟨inferInstance, fun U hU => ?_, hring, hcompat⟩
  have hbij := bijective_totalQuotientSheaf_presheaf_map_of_genericPoints_mem hass hfinite
    (mem_of_dense_of_mem_genericPoints hfinite hU)
  let ρ : X.totalQuotientSheaf.presheaf.obj (op ⊤) ≃+*
      X.totalQuotientSheaf.presheaf.obj (op U) :=
    RingEquiv.ofBijective
      (X.totalQuotientSheaf.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom hbij
  refine ⟨(hring.symm.toRingHom.comp ρ.symm.toRingHom).comp
    (X.toTotalQuotientSheaf.hom.app (op U)).hom, fun s => ?_⟩
  change hring.symm (ρ.symm ((X.toTotalQuotientSheaf.hom.app (op U)).hom s)) = _
  rw [RingEquiv.symm_apply_eq, RingEquiv.symm_apply_eq]
  exact (hcompat U hU s).symm

/-- The canonical map of sheaves of rings from the sheaf of meromorphic functions to the product
of the pushforwards `j_{η,*} 𝒪_{X,η}` is a map of `𝒪_X`-algebras: composed with the canonical map
`𝒪_X ⟶ 𝒦_X` it is the product of the canonical maps `𝒪_X ⟶ j_{η,*} 𝒪_{X,η}`. -/
theorem toTotalQuotientSheaf_comp_toGenericPointStalkProduct (X : Scheme.{u}) :
    X.toTotalQuotientSheaf ≫ toGenericPointStalkProduct X =
      Pi.lift fun η : genericPoints X ↦ toStalkSpecPushforwardStructure X η.1 := by
  refine Pi.hom_ext _ _ fun η ↦ ?_
  rw [Category.assoc, toGenericPointStalkProduct, Pi.lift_comp_π, Pi.lift_comp_π,
    toTotalQuotientSheaf_comp_toStalkSpecPushforwardSheaf]

open scoped Classical in
/-- **Stacks Project, Tag 0EMH.** Let `X` be a locally Noetherian scheme having no embedded
points, and let `η` range over the generic points of the irreducible components of `X`, with
`j_η : Spec 𝒪_{X,η} ⟶ X` the canonical morphism. Then:

* `𝒦_X = ∏_η j_{η,*} 𝒪_{X,η}` as sheaves of `𝒪_X`-algebras: the canonical map of sheaves of
  rings `toGenericPointStalkProduct X` is an isomorphism, and it is compatible with the maps from
  `𝒪_X`;
* `𝒦_X = ∏_η j_{η,*} 𝒪_{X,η} = ⊕_η j_{η,*} 𝒪_{X,η}` as `𝒪_X`-modules: the canonical map
  `toGenericPointStalkModulePi X` and the canonical map from the direct sum to the product are
  isomorphisms;
* (1) `𝒦_X` is quasi-coherent;
* (2) for every quasi-coherent `𝒪_X`-module `F`, `𝒦_X(F) = ∏_η j_{η,*} F_η = ⊕_η j_{η,*} F_η`
  through the canonical comparison `genericPointComparisonPi F` and the canonical map from the
  direct sum to the product, and `𝒦_X(F)` is quasi-coherent;
* (3) `R(X) = Γ(X, 𝒦_X)`: there is a commutative ring structure on the rational functions for
  which each section over a dense open is a ring homomorphism, and a ring isomorphism to the
  global meromorphic functions sending the rational function of a section `s` over a dense open
  `U` to the meromorphic function restricting on `U` to the image of `s`. -/
@[stacks 0EMH "canonical decompositions of K_X and K_X(F), (1), (2) and (3)"]
theorem genericPointDecomposition_of_hasNoEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X) :
    (IsIso (toGenericPointStalkProduct X) ∧
      X.toTotalQuotientSheaf ≫ toGenericPointStalkProduct X =
        Pi.lift fun η : genericPoints X ↦ toStalkSpecPushforwardStructure X η.1) ∧
    (IsIso (toGenericPointStalkModulePi X) ∧
      IsIso (sigmaPiComparison fun η : genericPoints X ↦ genericPointStalkModule X η)) ∧
    (meromorphicFunctions X).IsQuasicoherent ∧
    (∀ (F : X.Modules) [F.IsQuasicoherent],
      IsIso (genericPointComparisonPi F) ∧
        IsIso (sigmaPiComparison fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) ∧
        (meromorphicSections X F).IsQuasicoherent) ∧
    ∃ _ : CommRing X.rationalFunctions,
      (∀ (U : X.Opens) (hU : Dense (U : Set X)),
          ∃ ψ : Γ(X, U) →+* X.rationalFunctions,
            ∀ s, ψ s = X.rationalFunctionOfSection U hU s) ∧
        ∃ e : X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤),
          ∀ (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(X, U)),
            resTotalQuotientSheaf (e (X.rationalFunctionOfSection U hU s)) U =
              (X.toTotalQuotientSheaf.hom.app (op U)).hom s := by
  have hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X :=
    (schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX).le
  have hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite :=
    finite_irreducibleComponents_of_isCompact X
  refine ⟨⟨isIso_toGenericPointStalkProduct hass hfinite,
      toTotalQuotientSheaf_comp_toGenericPointStalkProduct X⟩,
    ⟨isIso_toGenericPointStalkModulePi hass hfinite, ?_⟩,
    meromorphicFunctions_isQuasicoherent_of_noEmbeddedPoints X hX,
    fun F _ ↦ ⟨isIso_genericPointComparisonPi hass hfinite F, ?_,
      meromorphicSections_isQuasicoherent_of_genericHypotheses hass hfinite F⟩,
    exists_commRing_rationalFunctions_ringEquiv_totalQuotientSheaf_top_compat X hass hfinite⟩
  · exact isIso_sigmaPiComparison_of_locallyFinite _ (fun V : X.affineOpens ↦ (V : X.Opens))
      (IsOpenCover.mk (iSup_affineOpens_eq_top X))
      (fun V η ↦ (η : X) ∈ (V : X.Opens))
      (fun V ↦ finite_genericPoints_mem_of_isCompact X _ V.2.isCompact hfinite)
      (fun _ η hη ↦ isZero_restrict_genericPointStalkModule η hη)
  · exact isIso_sigmaPiComparison_of_locallyFinite _ (fun V : X.affineOpens ↦ (V : X.Opens))
      (IsOpenCover.mk (iSup_affineOpens_eq_top X))
      (fun V η ↦ (η : X) ∈ (V : X.Opens))
      (fun V ↦ finite_genericPoints_mem_of_isCompact X _ V.2.isCompact hfinite)
      (fun _ η hη ↦ isZero_restrict_genericPointStalkModuleOf F η hη)

end AlgebraicGeometry

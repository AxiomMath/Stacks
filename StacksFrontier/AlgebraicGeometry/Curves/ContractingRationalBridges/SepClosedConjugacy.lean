module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.ComponentDegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ConjugateComponentDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.UnionBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional

/-!
# Components with the same image over a separably closed extension have the same degree

Let `X` be a proper one-dimensional equidimensional curve over a field `k` with at worst nodal
singularities, and let `Ω/k` be an extension with `Ω` separably closed. For a closed subset `T` of
a base change of `X`, write `P T` for the reduced induced closed subscheme structure
`Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure T)` and

`δ(T) = dim Γ(T ∩ X', 𝒪)`

for the degree over the ground field of its scheme-theoretic intersection with the closure of its
complement, cut out by `P T ⊔ complementaryCurveIdeal (P T)`. This file proves that two
irreducible components of `X_Ω` with the same image in `X` have the same `δ`.

## Main results

* `Stacks.Curves.finrank_sup_complementaryCurveIdeal_eq_of_image_eq`: over a separably closed
  extension `Ω/k`, two irreducible components of `X_Ω` whose images in `X` agree have the same
  complementary degree over `Ω`.
* `Stacks.Curves.componentIdealSheafData_eq_vanishingIdeal_closure`: the reduced induced structure
  on an irreducible component is the vanishing ideal of its topological closure, which identifies
  the two spellings of `P` used by the files feeding this one.

## Why the proof goes through the separable closure

`Ω/k` is an arbitrary extension of a separably closed field: it need not be algebraic, and
`Normal k Ω` is false in general — for `k = ℚ` and `Ω` a separable closure of `ℚ(t)` the group
`Ω ≃ₐ[ℚ] Ω` does not act transitively on anything relevant. So the conjugacy of the two components,
which is what forces their degrees to agree, cannot be run over `Ω`.

It is run over `E = separableClosure k Ω` instead. Since `Ω` is separably closed, `E` is a
separable closure of `k` (`separableClosure.isSepClosure`), hence normal and separably closed, and
`E` is separably closed *in* `Ω` (`separableClosure.separableClosure_eq_bot`). The first fact makes
the Galois argument available at `E`, the second makes the comparison `X_Ω ⟶ X_E` a bijection on
irreducible components (`AlgebraicGeometry.bijOn_image_baseChangeComparison`, Tag 038H for a base
separably closed in the extension). Nothing about `Ω` beyond separable closedness is used, and no
algebraicity.

The three steps are:

* the two components `T`, `T'` of `X_E` lying over one component of `X` are conjugate, so their
  *relative* complementary degrees over the global functions of the component agree
  (`AlgebraicGeometry.finrank_intersectionWithComplementaryCurve_eq_of_baseChangeMap_eq`,
  Tag 04KY);
* over the separably closed `E` the relative degree *is* the absolute one, because a component of a
  nodal curve is geometrically reduced and therefore has `h⁰ = 1`
  (`Stacks.Curves.finrank_structureSheafCohomology_zero_vanishingIdeal_component_eq_one`), so the
  tower formula `AlgebraicGeometry.finrank_structureSheafCohomology_zero_intersection_eq_mul` has a
  unit factor;
* the absolute degree is unchanged by the further extension `Ω/E`
  (`AlgebraicGeometry.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_comap`),
  whose reducedness hypothesis is geometric reducedness of the component downstairs.

## Implementation notes

The base change `X_E` inherits what the degree computation needs from `X`: its dimension by
[Stacks, Tag 0BY9] (`AlgebraicGeometry.topologicalKrullDim_baseChange`), its nodality by
`Stacks.Curves.hasAtWorstNodalSingularities_baseChange`, and its equidimensionality from the
constancy of the local dimension, part (1) of [Stacks, Tag 02FY] in the form
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_isPullback_of_subsingleton`. All three hold for an
arbitrary extension, so none of them is what forces the detour through `E`: that is the conjugacy
step alone, which needs a group acting transitively on the components over a fixed component of
`X` and has only the trivial group available at `Ω`.

The two spellings of the reduced structure on a component — `vanishingIdeal (Closeds.closure T)`,
used by the degree files, and `Stacks.AffineNoProperComponent.componentIdealSheafData`, used by the
conjugacy files — agree, and `Stacks.Curves.componentIdealSheafData_eq_vanishingIdeal_closure`
records that. The conjugacy input is taken in its automorphism form
(`AlgebraicGeometry.exists_algEquiv_image_eq_of_irreducibleComponentsBaseChangeMap_eq` followed by
`AlgebraicGeometry.finrank_intersectionWithComplementaryCurve_vanishingIdeal_eq_of_image_eq`)
rather than in its packaged form, so that no ideal sheaf has to be rewritten underneath an algebra
instance.

## References

* [Stacks Project, Tag 0E65](https://stacks.math.columbia.edu/tag/0E65)
* [Stacks Project, Tag 04KY](https://stacks.math.columbia.edu/tag/04KY)
* [Stacks Project, Tag 038H](https://stacks.math.columbia.edu/tag/038H)
* [Stacks Project, Tag 0G33](https://stacks.math.columbia.edu/tag/0G33)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Curves

/-- **The reduced induced structure on an irreducible component is the vanishing ideal of its
closure.** An irreducible component is closed, so repackaging it as an element of
`TopologicalSpace.Closeds` and taking its closure give the same closed set; this identifies the
spelling `Stacks.AffineNoProperComponent.componentIdealSheafData` used by the conjugacy files with
the spelling `vanishingIdeal (Closeds.closure _)` used by the degree files. -/
theorem componentIdealSheafData_eq_vanishingIdeal_closure {X : Scheme.{u}}
    (Z : irreducibleComponents X) :
    Stacks.AffineNoProperComponent.componentIdealSheafData Z =
      vanishingIdeal (Closeds.closure Z.1) :=
  congrArg vanishingIdeal
    (Closeds.ext ((isClosed_of_mem_irreducibleComponents Z.1 Z.2).closure_eq).symm)

/-- The base change along a field extension of a scheme locally of finite type, equidimensional of
dimension one, is again equidimensional: the local dimension of the base change at a point is the
local dimension of the original scheme at its image, by part (1) of [Stacks, Tag 02FY], and on an
equidimensional scheme that is constant. -/
public theorem equidimensional_pullback_spec_algebraMap (k E : Type u) [Field k] [Field E]
    [Algebra k E] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1) :
    Equidimensional (pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))) := by
  have hone : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hX_dimension]; simp
  refine equidimensional_of_topologicalKrullDimAt_eq E _
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) (d := 1) fun x => ?_
  rw [← topologicalKrullDimAt_eq_of_isPullback_of_subsingleton
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) x]
  exact topologicalKrullDimAt_eq_of_equidimensional k X f hX_equidimensional hone _

/-- The base change `X_E` of a proper equidimensional nodal curve over `k` is proper, Noetherian,
one-dimensional, equidimensional and nodal over `E`. -/
private theorem isProper_isNoetherian_and_baseChange_spec_algebraMap
    (k E : Type u) [Field k] [Field E] [Algebra k E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X) :
    letI : (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))).Over (Spec (.of E)) :=
      ⟨pullback.snd _ _⟩
    IsProper ((pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))) ↘ Spec (.of E)) ∧
      AlgebraicGeometry.IsNoetherian (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))) ∧
      topologicalKrullDim (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))) = 1 ∧
      Equidimensional (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))) ∧
      HasAtWorstNodalSingularities E (pullback (C := Scheme.{u})
        (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k E)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show IsProper (pullback.snd (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    infer_instance
  · have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    have := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    exact ⟨⟩
  · exact (topologicalKrullDim_baseChange k E
      (pullback.fst (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k E))))
      (pullback.snd (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k E))))
      (X ↘ Spec (.of k)) (IsPullback.of_hasPullback _ _)).trans hX_dimension
  · exact equidimensional_pullback_spec_algebraMap k E (X ↘ Spec (.of k)) hX_equidimensional
      hX_dimension
  · exact hasAtWorstNodalSingularities_baseChange k E X hX_equidimensional hX_dimension hX_nodal

/-- Over a separably closed field, the complementary degree of an irreducible component of a proper
equidimensional one-dimensional nodal curve is its relative degree over the global functions of the
component, as `h⁰` of the component is one. -/
private theorem finrank_sup_complementaryCurveIdeal_eq_finrank_intersection
    {E : Type u} [Field E] [IsSepClosed E] {Y : Scheme.{u}} [Y.Over (Spec (.of E))]
    [IsProper (Y ↘ Spec (.of E))] [AlgebraicGeometry.IsNoetherian Y]
    (hY_equidimensional : Equidimensional Y) (hY_dimension : topologicalKrullDim Y = 1)
    (hY_nodal : HasAtWorstNodalSingularities E Y) {T : Set Y} (hT : T ∈ irreducibleComponents Y) :
    letI : Algebra Γ((vanishingIdeal (Closeds.closure T)).subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal
          (vanishingIdeal (Closeds.closure T))).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion (le_sup_left :
        vanishingIdeal (Closeds.closure T) ≤
          intersectionWithComplementaryCurveIdeal
            (vanishingIdeal (Closeds.closure T)))).appTop.hom.toAlgebra
    Module.finrank E (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure T) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure T))).subschemeι ≫
            (Y ↘ Spec (.of E))) 0) =
      Module.finrank Γ((vanishingIdeal (Closeds.closure T)).subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal
          (vanishingIdeal (Closeds.closure T))).subscheme, ⊤) := by
  have : IsIntegral (vanishingIdeal (Closeds.closure T)).subscheme := by
    rw [← componentIdealSheafData_eq_vanishingIdeal_closure (⟨T, hT⟩ : irreducibleComponents _)]
    exact Stacks.AffineNoProperComponent.isIntegral_componentIdealSheafData _
  have htower := finrank_structureSheafCohomology_zero_intersection_eq_mul
    (Y ↘ Spec (.of E)) (vanishingIdeal (Closeds.closure T))
  rw [finrank_structureSheafCohomology_zero_vanishingIdeal_component_eq_one hY_equidimensional
    hY_dimension hY_nodal hT, one_mul] at htower
  exact htower

/-- **Over a normal separably closed extension, two irreducible components of the base change with
the same image downstairs have the same complementary degree.** Normality makes the two components
conjugate, so their relative complementary degrees agree (Tag 04KY); separable closedness makes
`h⁰` of a component of the base change equal to one, so the tower formula turns the relative degree
into the absolute one. -/
private theorem finrank_sup_complementaryCurveIdeal_eq_of_image_eq_of_normal
    (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosed E] [Normal k E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (T T' : Set (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))))
    (hT : T ∈ irreducibleComponents (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))))
    (hT' : T' ∈ irreducibleComponents (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))))
    (himg : (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k E)))).base '' T =
        (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k E)))).base '' T') :
    Module.finrank E (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure T) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure T))).subschemeι ≫
          pullback.snd (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k E)))) 0)
      = Module.finrank E (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure T') ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure T'))).subschemeι ≫
          pullback.snd (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k E)))) 0) := by
  let : (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))).Over (Spec (.of E)) :=
    ⟨pullback.snd _ _⟩
  obtain ⟨hproper, hnoeth, hXEdim, hXEeq, hXEnodal⟩ :=
    isProper_isNoetherian_and_baseChange_spec_algebraMap k E X hX_equidimensional hX_dimension
      hX_nodal
  -- The relative complementary degree of each of the two components.
  have htower := finrank_sup_complementaryCurveIdeal_eq_finrank_intersection hXEeq hXEdim
    hXEnodal hT
  have htower' := finrank_sup_complementaryCurveIdeal_eq_finrank_intersection hXEeq hXEdim
    hXEnodal hT'
  -- The two components are conjugate, so their relative degrees agree.
  obtain ⟨σ, hσ⟩ := exists_algEquiv_image_eq_of_irreducibleComponentsBaseChangeMap_eq k E
    (Over.mk (X ↘ Spec (.of k))) ⟨T, hT⟩ ⟨T', hT'⟩ (Subtype.ext himg)
  have := isIso_galoisBaseChangeMap k E X (X ↘ Spec (.of k)) σ
  have himage : (galoisBaseChangeMap k E X (X ↘ Spec (.of k)) σ).base ''
      ((Closeds.closure T : Closeds (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k E))))) : Set _)
      = ((Closeds.closure T' : Closeds (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k E))))) : Set _) := by
    show (galoisBaseChangeMap k E X (X ↘ Spec (.of k)) σ).base '' closure T = closure T'
    rw [(isClosed_of_mem_irreducibleComponents T hT).closure_eq,
      (isClosed_of_mem_irreducibleComponents T' hT').closure_eq]
    exact hσ
  have hrel := finrank_intersectionWithComplementaryCurve_vanishingIdeal_eq_of_image_eq
    (galoisBaseChangeMap k E X (X ↘ Spec (.of k)) σ) (Closeds.closure T) (Closeds.closure T')
    himage
  exact htower.trans (hrel.trans htower'.symm)

/-- **The complementary degree of a component is unchanged by the comparison with a base change
over an intermediate field in which it is separably closed.** For a tower `k ⊆ E ⊆ Ω` with `E`
separably closed in `Ω`, the comparison `b : X_Ω ⟶ X_E` carries an irreducible
component `V` of `X_Ω` onto an irreducible component of `X_E` with `b ⁻¹' (b '' V) = V`, and the
degree of the intersection of `V` with the closure of its complement, taken over `Ω`, equals that
of its image, taken over `E`. -/
private theorem finrank_sup_complementaryCurveIdeal_image_baseChangeComparison
    (k E Ω : Type u) [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra E Ω] [Algebra k Ω] [IsScalarTower k E Ω]
    (hsc : separableClosure E Ω = ⊥)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (V : Set (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
    (hV : V ∈ irreducibleComponents (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))) :
    Module.finrank Ω (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure V) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure V))).subschemeι ≫
          pullback.snd (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) 0)
      = Module.finrank E (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure
              ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V)) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure
              ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V)))).subschemeι ≫
          pullback.snd (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k E)))) 0) := by
  let : (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))).Over (Spec (.of E)) :=
    ⟨pullback.snd _ _⟩
  obtain ⟨hproper, hnoeth, hXEdim, hXEeq, hXEnodal⟩ :=
    isProper_isNoetherian_and_baseChange_spec_algebraMap k E X hX_equidimensional hX_dimension
      hX_nodal
  -- The comparison map is a base change of `Spec Ω ⟶ Spec E`, which is geometrically irreducible.
  have hgi : GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap E Ω))) :=
    (separableClosure.eq_bot_iff_geometricallyIrreducible E Ω).mp hsc
  have hpb := isPullback_baseChangeComparison k E Ω X (X ↘ Spec (.of k))
  have : GeometricallyIrreducible (baseChangeComparison k E Ω X (X ↘ Spec (.of k))) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIrreducible) hpb.flip hgi
  have : UniversallyOpen (baseChangeComparison k E Ω X (X ↘ Spec (.of k))) :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) hpb.flip inferInstance
  have hTE : (baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V ∈
      irreducibleComponents (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))) :=
    (bijOn_image_baseChangeComparison k E Ω hsc X (X ↘ Spec (.of k))).mapsTo hV
  have hpre : (baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base ⁻¹'
      ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V) = V :=
    congrArg Subtype.val ((Scheme.Hom.irreducibleComponentsEquiv
      (baseChangeComparison k E Ω X (X ↘ Spec (.of k)))
      (baseChangeComparison k E Ω X (X ↘ Spec (.of k))).isOpenMap).symm_apply_apply ⟨V, hV⟩)
  -- The inverse image of the component downstairs stays reduced, it being geometrically reduced.
  have hgr : GeometricallyReduced ((vanishingIdeal (Closeds.closure
      ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V))).subschemeι ≫
      pullback.snd (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k E)))) :=
    geometricallyReduced_vanishingIdeal_component hXEeq hXEdim hXEnodal hTE
  have hsqcomap : IsPullback
      ((vanishingIdeal (Closeds.closure
          ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V))).comap
        (baseChangeComparison k E Ω X (X ↘ Spec (.of k)))).subschemeι
      (Scheme.IdealSheafData.subschemeMap _ _ (baseChangeComparison k E Ω X (X ↘ Spec (.of k)))
        ((vanishingIdeal (Closeds.closure
          ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V))).le_map_comap
          (baseChangeComparison k E Ω X (X ↘ Spec (.of k)))))
      (baseChangeComparison k E Ω X (X ↘ Spec (.of k)))
      (vanishingIdeal (Closeds.closure
        ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V))).subschemeι :=
    IsPullback.of_iso_pullback ⟨(Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm⟩
      ((vanishingIdeal (Closeds.closure
        ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V))).comapIso
        (baseChangeComparison k E Ω X (X ↘ Spec (.of k))))
      (Scheme.IdealSheafData.comapIso_hom_fst _ _)
      (Scheme.IdealSheafData.comapIso_hom_snd _ _)
  have hred : IsReduced ((vanishingIdeal (Closeds.closure
      ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V))).comap
      (baseChangeComparison k E Ω X (X ↘ Spec (.of k)))).subscheme :=
    hgr.geometrically_isReduced (Spec.map (CommRingCat.ofHom (algebraMap E Ω))) _ _
      (hsqcomap.flip.paste_vert hpb)
  have hmain := finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_comap E Ω
    (pullback.snd (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    (baseChangeComparison k E Ω X (X ↘ Spec (.of k)))
    (pullback.snd (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
    hpb ((baseChangeComparison k E Ω X (X ↘ Spec (.of k))).base '' V)
    (isClosed_of_mem_irreducibleComponents _ hTE) hred
  rw [hpre] at hmain
  exact hmain

/-- **Over a separably closed extension of the ground field, two irreducible components of the
base change of a nodal curve with the same image downstairs have the same complementary degree.**
Let `X` be a proper one-dimensional equidimensional curve over a field `k` with at worst nodal
singularities, let `Ω/k` be *any* extension with `Ω` separably closed, and let `Z`, `W` be
irreducible components of `X_Ω` whose images in `X` agree. Writing `P T` for the reduced induced
structure `vanishingIdeal (Closeds.closure T)` on a closed subset `T` of `X_Ω` and `X'_T` for the
scheme-theoretic closure of the complement of `T`, cut out by `complementaryCurveIdeal (P T)`, the
degrees over `Ω` of `T ∩ X'_T` agree for `T = Z` and `T = W`.

This is the symmetry input of [Stacks, Tag 0E65]: the counting available over `k` pins only the
sum of the complementary degrees of the components of a base-changed rational bridge, and it is
their equality that forces each of them to be two.

Nothing is assumed about `Ω` beyond separable closedness — in particular neither algebraicity nor
normality over `k`, both of which fail for a general separably closed extension. The proof runs the
conjugacy argument over `E = separableClosure k Ω`, which is a separable closure of `k` and
therefore normal over `k`, and transports the answer along `X_Ω ⟶ X_E`; see the module
documentation. -/
theorem finrank_sup_complementaryCurveIdeal_eq_of_image_eq
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (Z W : Set (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
    (hZ : Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
    (hW : W ∈ irreducibleComponents (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
    (himg : (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).base '' Z =
        (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).base '' W) :
    Module.finrank Ω (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure Z) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z))).subschemeι ≫
          pullback.snd (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) 0)
      = Module.finrank Ω (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure W) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure W))).subschemeι ≫
          pullback.snd (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) 0) := by
  have : IsSepClosed ↥(separableClosure k Ω) :=
    IsSepClosure.sep_closed (k := k) (K := ↥(separableClosure k Ω))
  -- The image of each of the two components in `X` is computed through `X_E`.
  have hcomp : ∀ U : Set (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))),
      (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom
            (algebraMap k ↥(separableClosure k Ω))))).base ''
        ((baseChangeComparison k ↥(separableClosure k Ω) Ω X (X ↘ Spec (.of k))).base '' U)
      = (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).base '' U := by
    intro U
    rw [← Set.image_comp]
    exact congrArg (· '' U) (congrArg (fun g : _ ⟶ X => (g.base : _ → X))
      (baseChangeComparison_comp_fst k ↥(separableClosure k Ω) Ω X (X ↘ Spec (.of k))))
  have hbij := bijOn_image_baseChangeComparison k ↥(separableClosure k Ω) Ω
    (separableClosure.separableClosure_eq_bot k Ω) X (X ↘ Spec (.of k))
  refine (finrank_sup_complementaryCurveIdeal_image_baseChangeComparison k
      ↥(separableClosure k Ω) Ω (separableClosure.separableClosure_eq_bot k Ω) X
      hX_equidimensional hX_dimension hX_nodal Z hZ).trans
    (Eq.trans ?_ (finrank_sup_complementaryCurveIdeal_image_baseChangeComparison k
      ↥(separableClosure k Ω) Ω (separableClosure.separableClosure_eq_bot k Ω) X
      hX_equidimensional hX_dimension hX_nodal W hW).symm)
  exact finrank_sup_complementaryCurveIdeal_eq_of_image_eq_of_normal k
    ↥(separableClosure k Ω) X hX_equidimensional hX_dimension hX_nodal _ _
    (hbij.mapsTo hZ) (hbij.mapsTo hW) (by rw [hcomp, hcomp, himg])

end Stacks.Curves

end

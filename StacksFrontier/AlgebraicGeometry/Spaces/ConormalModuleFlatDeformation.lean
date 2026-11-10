module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImageUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatDeformationCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact

/-!
# Flat deformations of first-order thickenings of algebraic spaces (Stacks 06BH)

Let `S` be a scheme contained in a big fppf site `B` and let
```
X --⊆--→ X'
|        |
f        g
↓        ↓
Y --⊆--→ Y'
```
be a morphism `(f, g) : (X ⊆ X') → (Y ⊆ Y')` of first-order thickenings of algebraic spaces over
`S`, with `f` flat.  [Stacks Project, Tag 06BH] asserts that the following are equivalent:

1. `g` is flat and `X = Y ×_{Y'} X'`;
2. the canonical map `f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 04CP] is an isomorphism.

This file proves the equivalence,
`AlgebraicGeometry.Space.isFlat_and_isPullback_iff_isIso_conormalMap`.
Here `X` and `Y` are arbitrary closed subspaces which are first-order thickenings, the morphism of
thickenings is a pair of morphisms with commuting square of inclusions, flatness is
`AlgebraicGeometry.Space.IsFlat` of [Stacks Project, Tag 03ML] for both `f` and `g`, and
`X = Y ×_{Y'} X'` is `CategoryTheory.IsPullback` of the square.

## The proof

Write `P = g⁻¹(Y) ⊆ X'` (Stacks 083Q), `φ : g^*𝓘_Y ⟶ 𝓘_X` for the map of defining ideal sheaves
of Stacks 04CP and `i : X ⟶ X'` for the inclusion.  The conormal map is `i^*φ` up to an
isomorphism.

*(1) ⟹ (2).*  A cartesian square is the fibre product square of `P`, so `X = P`.  Flatness of
`g` makes `g^*` left exact
(`AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom`),
so `φ`, which followed by `𝓘_P ⊆ 𝒪_{X'}` is `g^*(𝓘_Y ⊆ 𝒪_{Y'})` followed by an isomorphism, is a
monomorphism; it is an epimorphism by the surjectivity clause of Stacks 04CQ, hence an
isomorphism, and so is `i^*φ`.

*(2) ⟹ (1), cartesianness.*  If `i^*φ` is an isomorphism then so is `i_*i^*φ`, and the unit
`g^*𝓘_Y ⟶ i_*i^*g^*𝓘_Y` is an epimorphism (Stacks 04CJ); the unit at `𝓘_X` is an isomorphism
because `X ⊆ X'` is first order.  By naturality `φ` is an epimorphism.  Both `φ` and the map
`g^*𝓘_Y ⟶ 𝓘_P` of the fibre product square become `g^*(𝓘_Y ⊆ 𝒪_{Y'})` followed by the same
isomorphism after the inclusions into `𝒪_{X'}`, so every section of `𝓘_X` lies locally, hence
globally, in `𝓘_P`; that is `P ⊆ X`, while `X ⊆ P` by commutativity of the square.  So `X = P`,
which is cartesianness.

*(2) ⟹ (1), flatness.*  Now `𝓘_P` annihilates `g^*𝓘_Y` because `𝓘_Y² = 0`, so the unit at
`g^*𝓘_Y` is an isomorphism as well (Stacks 08KS) and the same naturality square makes `φ` a
monomorphism, hence `g^*(𝓘_Y ⊆ 𝒪_{Y'})` a monomorphism.  Read on an affine chart diagram
`Γ(V) ⟶ Γ(U)` over `g`, with `J = 𝓘_Y(V)`, this is injectivity of `J ⊗_{Γ(V)} Γ(U) ⟶ Γ(U)`; the
flatness of `f` on the induced chart diagram of the closed subspaces is flatness of
`Γ(V)/J ⟶ Γ(U)/JΓ(U)`; and the local flatness criterion for the nilpotent ideal `J` gives
flatness of `Γ(V) ⟶ Γ(U)`.  Flatness on affine chart diagrams is flatness of `g`.  The chart-level
statements are in `StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatDeformationCharts`.

The source proves the lemma by reducing to its scheme analogue, Stacks 063Y, on étale charts.
The argument above uses the same commutative algebra, read on chart sections of modules on the
small étale site rather than on schemes.

## Main results

* `AlgebraicGeometry.Space.isFlat_and_isPullback_iff_isIso_conormalMap`: **[Stacks Project,
  Tag 06BH]**.
* `AlgebraicGeometry.Space.eq_preimageSubspace_of_isPullback`: a cartesian square of closed
  subspaces is the fibre product square of the inverse image.
* `AlgebraicGeometry.Space.epi_idealSheafMap_of_isIso_conormalMap` and
  `AlgebraicGeometry.Space.definingIdealSheaf_le_preimage_of_epi_idealSheafMap`: the two steps
  of cartesianness in (2) ⟹ (1).
* `AlgebraicGeometry.Space.mono_idealSheafMap_of_isIso_conormalMap_preimage`: injectivity of the
  map of ideal sheaves in (2) ⟹ (1).
* `AlgebraicGeometry.Space.mono_modulePullback_map_ι_of_isFlat`: its consequence for a flat `g`.

## Implementation notes

**Relation to `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderThickening.lean`.**
That file registers the implication (1) ⟹ (2) on the fibre product configuration, with flatness
of `g` taken for its morphism of small étale ringed topoi.  The statement here carries the
source's hypotheses and both directions: the closed subspace `X` is arbitrary, the cartesianness
of the square is part of condition (1), and both flatness conditions are the chartwise one of
Stacks 03ML.

**The abelian structure and the instance arguments are pinned.**  As recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeFlat.lean`, a search for
`Abelian (Modules.{u, u} …)` can abort on a stuck universe constraint in this part of the
development; the proofs below therefore supply the abelian structure and the `Epi`, `Mono` and
`IsIso` instances of composites explicitly.

## References

* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y') (X : ClosedSubspaces B S hS X'.1)
    (Y : ClosedSubspaces B S hS Y'.1)
    (f : (⟨X.1.toFunctor, X.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X' X ≫ g = f ≫ subspaceInclusion B S hS Y' Y)

/-- **Invertibility of the conormal map is invertibility of the inverse image of the map of ideal
sheaves.**  The conormal map of Stacks 04CP is the comparison isomorphism
`AlgebraicGeometry.Space.conormalPullbackComparison` followed by `i^*φ`, for `φ` the map of
defining ideal sheaves (`AlgebraicGeometry.Space.conormalMap_eq`). -/
theorem isIso_modulePullback_map_idealSheafMap_of_isIso_conormalMap
    (h : IsIso (conormalMap B S hS X Y g f hsq)) :
    IsIso ((modulePullback B S hS (subspaceInclusion B S hS X' X)).map
      (idealSheafMap B S hS X Y g f hsq)) := by
  rw [conormalMap_eq B S hS X Y g f hsq] at h
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (conormalPullbackComparison B S hS X Y g f hsq)
    ((modulePullback B S hS (subspaceInclusion B S hS X' X)).map
      (idealSheafMap B S hS X Y g f hsq))
    (isIso_conormalPullbackComparison B S hS X Y g f hsq) h

/-- **If the conormal map is invertible, the map of defining ideal sheaves is an epimorphism**,
for `X ⊆ X'` a first-order thickening.  By naturality of the unit of `i^* ⊣ i_*`, `φ` followed by
the unit at `𝓘_X` is the unit at `g^*𝓘_Y`, an epimorphism (Stacks 04CJ), followed by `i_*i^*φ`,
an isomorphism; and the unit at `𝓘_X` is an isomorphism because `𝓘_X² = 0`. -/
theorem epi_idealSheafMap_of_isIso_conormalMap
    (hX : IsFirstOrderThickening B S hS X' X.1)
    (h : IsIso (conormalMap B S hS X Y g f hsq)) :
    Epi (idealSheafMap B S hS X Y g f hsq) := by
  let : Abelian (Modules.{u, u} B S hS X'.1 X'.2) :=
    @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS X'.1 X'.2)
      (smallEtaleRingedSite_wEqualsLocallyBijective B S hS X'.1 X'.2)
  let i := subspaceInclusion B S hS X' X
  have hi : IsClosedImmersion B S hS i.hom := X.2.2
  let adj := modulePullbackAdjunction B S hS i
  have hmap := isIso_modulePullback_map_idealSheafMap_of_isIso_conormalMap B S hS g X Y f hsq h
  have hunitN : Epi (adj.unit.app ((modulePullback B S hS g).obj
      (definingIdealSheaf B S hS Y' Y).toSheafOfModules)) :=
    epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS i hi
      (fun M hM => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi M hM) _
  have hnat := adj.unit.naturality (idealSheafMap B S hS X Y g f hsq)
  have hR : IsIso ((modulePushforward B S hS i).map
      ((modulePullback B S hS i).map (idealSheafMap B S hS X Y g f hsq))) := inferInstance
  have hcomp : Epi (idealSheafMap B S hS X Y g f hsq ≫
      adj.unit.app (definingIdealSheaf B S hS X' X).toSheafOfModules) := by
    have : idealSheafMap B S hS X Y g f hsq ≫
        adj.unit.app (definingIdealSheaf B S hS X' X).toSheafOfModules =
        adj.unit.app _ ≫ (modulePushforward B S hS i).map
          ((modulePullback B S hS i).map (idealSheafMap B S hS X Y g f hsq)) := hnat
    rw [this]
    exact @epi_comp _ _ _ _ _ _ hunitN _ (@IsIso.epi_of_iso _ _ _ _ _ hR)
  have hunitX : IsIso (adj.unit.app (definingIdealSheaf B S hS X' X).toSheafOfModules) :=
    isIso_unit_definingIdealSheaf_of_isFirstOrderThickening B S hS X hX
  exact (@epi_comp_iff_of_isIso _ _ _ _ _ _ _ hunitX).1 hcomp

/-- **An epimorphic map of defining ideal sheaves forces `𝓘_X ⊆ 𝓘_{g⁻¹(Y)}`.**  Both `φ` and the
map `g^*𝓘_Y ⟶ 𝓘_{g⁻¹(Y)}` of the fibre product square are, after the inclusions into `𝒪_{X'}`, the
inverse image of `𝓘_Y ⊆ 𝒪_{Y'}` followed by the comparison of structure sheaves
(`AlgebraicGeometry.Space.idealSheafMap_comp_ι`).  So a section of `𝓘_X`, which is locally a
value of `φ`, is locally in `𝓘_{g⁻¹(Y)}`, and the latter has local membership. -/
theorem definingIdealSheaf_le_preimage_of_epi_idealSheafMap
    (he : Epi (idealSheafMap B S hS X Y g f hsq)) :
    definingIdealSheaf B S hS X' X ≤
      definingIdealSheaf B S hS X' (preimageSubspace B S hS g Y) := by
  have h1 := idealSheafMap_comp_ι B S hS X Y g f hsq
  have h2 := idealSheafMap_comp_ι B S hS (preimageSubspace B S hS g Y) Y g
    (preimageProjection B S hS g Y) (conormalEtaleRestrictionSquare B S hS g Y)
  have h12 := h1.trans h2.symm
  intro U a ha
  refine (definingIdealSheaf B S hS X' (preimageSubspace B S hS g Y)).isSheaf a ?_
  refine GrothendieckTopology.superset_covering _ ?_
    (Stacks.SheafOfModules.EpiMono.imageSieve_mem_of_epi
      (idealSheafMap B S hS X Y g f hsq) (V := U.unop) (⟨a, ha⟩ : _))
  intro W k ⟨t, ht⟩
  have e := congrArg (fun m => m.val.app (op W) t) h12
  simp only at e
  have h3 := congrArg Subtype.val ht
  have h4 : (SheafOfModules.unit (structureRingSheaf B S hS X')).val.map k.op a =
      ((idealSheafMap B S hS (preimageSubspace B S hS g Y) Y g
        (preimageProjection B S hS g Y) (conormalEtaleRestrictionSquare B S hS g Y)).val.app
          (op W) t).1 :=
    h3.symm.trans e
  change (SheafOfModules.unit (structureRingSheaf B S hS X')).val.map k.op a ∈
    definingIdealAt B S hS X' (preimageSubspace B S hS g Y) (op W)
  rw [h4]
  exact ((idealSheafMap B S hS (preimageSubspace B S hS g Y) Y g
    (preimageProjection B S hS g Y) (conormalEtaleRestrictionSquare B S hS g Y)).val.app
      (op W) t).2

include hsq in
/-- A closed subspace `X ⊆ X'` mapping into `Y` along `g` lies in `g⁻¹(Y)`. -/
theorem le_preimageSubspace_of_comm : X.1 ≤ (preimageSubspace B S hS g Y).1 := by
  intro T x hx
  have e := congrArg (fun m => m.hom.app T ⟨x, hx⟩) hsq
  change g.hom.app T x ∈ Y.1.obj T
  have e' : g.hom.app T x = (Y.1.ι.app T (f.hom.app T ⟨x, hx⟩)) := e
  rw [e']
  exact (f.hom.app T ⟨x, hx⟩).2

/-- **A cartesian square of closed subspaces is the fibre product square of the inverse image.**
If the square of inclusions over `g` is cartesian, then `X = g⁻¹(Y)`: the range of a leg of a
cartesian square of presheaves is the inverse image of the range of the opposite leg
(`CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback`). -/
theorem eq_preimageSubspace_of_isPullback
    (h : IsPullback (subspaceInclusion B S hS X' X) f g (subspaceInclusion B S hS Y' Y)) :
    X = preimageSubspace B S hS g Y := by
  have hp := AlgebraicSpaces.isPullback_hom B S hS h
  have hr := Subfunctor.range_eq_preimage_of_isPullback hp
  refine Subtype.ext ?_
  change X.1 = Y.1.preimage g.hom
  have e1 : Subfunctor.range (subspaceInclusion B S hS X' X).hom = X.1 := Subfunctor.range_ι X.1
  have e2 : Subfunctor.range (subspaceInclusion B S hS Y' Y).hom = Y.1 := Subfunctor.range_ι Y.1
  rw [← e1, hr, e2]

/-- **At the fibre product square, invertibility of the conormal map makes the map of ideal
sheaves a monomorphism**, for first-order thickenings `Y ⊆ Y'` and `g⁻¹(Y) ⊆ X'`.  The defining
ideal of `g⁻¹(Y)` annihilates `g^*𝓘_Y`
(`AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePullback_definingIdealSheaf`), so the unit
of `i^* ⊣ i_*` at `g^*𝓘_Y` is an isomorphism (Stacks 08KS), as is the unit at `𝓘_{g⁻¹(Y)}`; by
naturality `φ` followed by an isomorphism is an isomorphism followed by `i_*i^*φ`, which is an
isomorphism. -/
theorem mono_idealSheafMap_of_isIso_conormalMap_preimage
    (hY : IsFirstOrderThickening B S hS Y' Y.1)
    (hX : IsFirstOrderThickening B S hS X' (preimageSubspace B S hS g Y).1)
    (h : IsIso (conormalMap B S hS (preimageSubspace B S hS g Y) Y g
      (preimageProjection B S hS g Y) (conormalEtaleRestrictionSquare B S hS g Y))) :
    Mono (idealSheafMap B S hS (preimageSubspace B S hS g Y) Y g
      (preimageProjection B S hS g Y) (conormalEtaleRestrictionSquare B S hS g Y)) := by
  let P := preimageSubspace B S hS g Y
  let i := subspaceInclusion B S hS X' P
  have hi : IsClosedImmersion B S hS i.hom := P.2.2
  let adj := modulePullbackAdjunction B S hS i
  let ψ := idealSheafMap B S hS P Y g (preimageProjection B S hS g Y)
    (conormalEtaleRestrictionSquare B S hS g Y)
  have hmap : IsIso ((modulePullback B S hS i).map ψ) :=
    isIso_modulePullback_map_idealSheafMap_of_isIso_conormalMap B S hS g P Y _ _ h
  have hR : IsIso ((modulePushforward B S hS i).map ((modulePullback B S hS i).map ψ)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ hmap
  have hunitN : IsIso (adj.unit.app ((modulePullback B S hS g).obj
      (definingIdealSheaf B S hS Y' Y).toSheafOfModules)) :=
    (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i hi _).1
      (essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi _
        (annihilatedByKerIdeal_modulePullback_definingIdealSheaf B S hS g Y hY))
  have hunitX : IsIso (adj.unit.app (definingIdealSheaf B S hS X' P).toSheafOfModules) :=
    isIso_unit_definingIdealSheaf_of_isFirstOrderThickening B S hS P hX
  have hnat : ψ ≫ adj.unit.app (definingIdealSheaf B S hS X' P).toSheafOfModules =
      adj.unit.app _ ≫ (modulePushforward B S hS i).map ((modulePullback B S hS i).map ψ) :=
    adj.unit.naturality ψ
  have hcomp : Mono (ψ ≫ adj.unit.app (definingIdealSheaf B S hS X' P).toSheafOfModules) := by
    rw [hnat]
    exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hunitN) _
      (@IsIso.mono_of_iso _ _ _ _ _ hR)
  exact @mono_of_mono _ _ _ _ _ _ _ hcomp

/-- **For a flat `g` the inverse image of the inclusion `𝓘_Y ⊆ 𝒪_{Y'}` is a monomorphism**:
flatness in the sense of Stacks 03ML makes `g^*` left exact
(`AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom`). -/
theorem mono_modulePullback_map_ι_of_isFlat (hg : IsFlat B S hS g.hom) :
    Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS Y' Y).ι) := by
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS g hg
  have hmi : Mono (definingIdealSheaf B S hS Y' Y).ι :=
    (definingIdealShortComplex_shortExact B S hS Y' Y).mono_f
  have hpm : (modulePullback B S hS g).PreservesMonomorphisms :=
    ⟨fun f _ => preserves_mono_of_preservesLimit _ f⟩
  exact @Functor.map_mono _ _ _ _ (modulePullback B S hS g) hpm _ _
    (definingIdealSheaf B S hS Y' Y).ι hmi

/-- At the fibre product square of `g⁻¹(Y)`, a morphism completing the square of inclusions is
the projection: the inclusion of `Y` is a monomorphism. -/
theorem eq_preimageProjection_of_comm
    (f : (⟨(preimageSubspace B S hS g Y).1.toFunctor, (preimageSubspace B S hS g Y).2.1⟩ :
      AlgebraicSpaces B S hS) ⟶ (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X' (preimageSubspace B S hS g Y) ≫ g =
      f ≫ subspaceInclusion B S hS Y' Y) :
    f = preimageProjection B S hS g Y := by
  refine ObjectProperty.hom_ext _ ((cancel_mono Y.1.ι).1 ?_)
  exact (congrArg (fun m => m.hom) hsq).symm.trans
    (congrArg (fun m => m.hom) (conormalEtaleRestrictionSquare B S hS g Y))

/-- The map `g^*𝓘_Y ⟶ 𝓘_{g⁻¹(Y)}` of the fibre product square is a monomorphism iff the inverse
image of the inclusion `𝓘_Y ⊆ 𝒪_{Y'}` is: after the inclusion into `𝒪_{X'}` the former is the
latter followed by the isomorphism of structure sheaves. -/
private theorem mono_idealSheafMap_preimage_iff :
    Mono (idealSheafMap B S hS (preimageSubspace B S hS g Y) Y g
      (preimageProjection B S hS g Y) (conormalEtaleRestrictionSquare B S hS g Y)) ↔
    Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS Y' Y).ι) := by
  have h1 := idealSheafMap_comp_ι B S hS (preimageSubspace B S hS g Y) Y g
    (preimageProjection B S hS g Y) (conormalEtaleRestrictionSquare B S hS g Y)
  have hmi : Mono (definingIdealSheaf B S hS X' (preimageSubspace B S hS g Y)).ι :=
    (definingIdealShortComplex_shortExact B S hS X' (preimageSubspace B S hS g Y)).mono_f
  constructor
  · intro hmono
    have h3 : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS Y' Y).ι ≫
        structureSheafMap B S hS g) := by
      rw [← h1]
      exact @mono_comp _ _ _ _ _ _ hmono _ hmi
    exact @mono_of_mono _ _ _ _ _ _ _ h3
  · intro hmono
    have h3 : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS Y' Y).ι ≫
        structureSheafMap B S hS g) :=
      @mono_comp _ _ _ _ _ _ hmono _
        (@IsIso.mono_of_iso _ _ _ _ _ (isIso_structureSheafMap B S hS g))
    rw [← h1] at h3
    exact @mono_of_mono _ _ _ _ _ _ _ h3

/-- **[Stacks Project, Tag 06BH].**  Let `(f, f') : (X ⊆ X') → (Y ⊆ Y')` be a morphism of
first-order thickenings of algebraic spaces over `S` — `X ⊆ X'` and `Y ⊆ Y'` first-order
thickenings, `f' = g : X' ⟶ Y'` and `f : X ⟶ Y` with commuting square of inclusions — and let
`f` be flat.  Then the following are equivalent:

1. `f'` is flat and `X = Y ×_{Y'} X'`;
2. the canonical map `f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 04CP] is an
   isomorphism.

Both flatness conditions are `AlgebraicGeometry.Space.IsFlat` of [Stacks Project, Tag 03ML],
`X = Y ×_{Y'} X'` is cartesianness of the square of inclusions, and the canonical map is
`AlgebraicGeometry.Space.conormalMap`.  The first-order thickening hypotheses are used only in
(2) ⟹ (1), and so is the flatness of `f`. -/
@[stacks 06BH]
theorem isFlat_and_isPullback_iff_isIso_conormalMap
    (hX : IsFirstOrderThickening B S hS X' X.1) (hY : IsFirstOrderThickening B S hS Y' Y.1)
    (hf : IsFlat B S hS f.hom) :
    (IsFlat B S hS g.hom ∧
        IsPullback (subspaceInclusion B S hS X' X) f g (subspaceInclusion B S hS Y' Y)) ↔
      IsIso (conormalMap B S hS X Y g f hsq) := by
  refine ⟨fun ⟨hg, hpb⟩ => ?_, fun hiso => ?_⟩
  · obtain rfl := eq_preimageSubspace_of_isPullback B S hS g X Y f hpb
    obtain rfl := eq_preimageProjection_of_comm B S hS g Y f hsq
    refine isIso_conormalMap_of_isIso_idealSheafMap B S hS _ Y g _ hsq ?_
    have hbal : Balanced (Modules.{u, u} B S hS X'.1 X'.2) := by
      let habelian : Abelian (Modules.{u, u} B S hS X'.1 X'.2) :=
        @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS X'.1 X'.2)
          (smallEtaleRingedSite_wEqualsLocallyBijective B S hS X'.1 X'.2)
      exact Stacks.SheafOfModules.ImageSubsheaf.balanced_of_abelian
    exact @isIso_of_mono_of_epi _ _ hbal _ _ _
      ((mono_idealSheafMap_preimage_iff B S hS g Y).2
        (mono_modulePullback_map_ι_of_isFlat B S hS g Y hg)) (epi_idealSheafMap B S hS g Y)
  · have hle := definingIdealSheaf_le_preimage_of_epi_idealSheafMap B S hS g X Y f hsq
      (epi_idealSheafMap_of_isIso_conormalMap B S hS g X Y f hsq hX hiso)
    obtain rfl : X = preimageSubspace B S hS g Y :=
      Subtype.ext (le_antisymm (le_preimageSubspace_of_comm B S hS g X Y f hsq)
        (le_of_definingIdealSheaf_le B S hS X' (preimageSubspace B S hS g Y) X hle))
    obtain rfl := eq_preimageProjection_of_comm B S hS g Y f hsq
    refine ⟨?_, (isPullback_preimageProjection B S hS g Y).flip⟩
    have hmono := (mono_idealSheafMap_preimage_iff B S hS g Y).1
      (mono_idealSheafMap_of_isIso_conormalMap_preimage B S hS g Y hY hX hiso)
    exact isFlat_of_flat_chartDiagramRestrict B S hS g fun d hU hV =>
      flat_chartDiagramRestrict_of_mono B S hS g Y hY hf hmono d hU hV

end AlgebraicGeometry.Space

end

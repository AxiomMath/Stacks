module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechCharts

/-!
# The degreewise base change of the Čech complex of a cover

Let

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine, and let `F` be a quasi-coherent
`𝒪_X`-module. For every open `U` of `X` the unit of `p^* ⊣ p_*`, read on sections, is a
`Γ(S, ⊤)`-linear map `Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)`; extending its scalars to `Γ(T, ⊤)` gives the
canonical comparison

  `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)`.

This file proves the two facts about that comparison which make the Čech complexes of a cover
and of its preimage comparable: it is an isomorphism when `U` is affine, and it commutes with
restriction along an inclusion of opens. The Čech differential of a cover is an alternating sum
of restrictions, so the second fact is what turns the family of degreewise comparisons into a
map of Čech complexes.

Affineness of `U` is the only hypothesis of the isomorphism statement: **no flatness is used.**
That matches the source, where the degreewise identification of Čech complexes is affine base
change ([Stacks, Tag 02KG]), and flatness of `q` enters only when passing from the complexes to
their cohomology.

Both facts are then specialised to the standard charts of projective space, where the opens in
question are the finite intersections of charts: they are affine, and the charts of `ℙⁿ_B` are
*equal* to the preimages of the charts of `ℙⁿ_A`.

## Main definitions

* `Stacks.AlgebraicGeometry.SectionsBaseChange.baseResHom`: restriction of sections of `F`,
  as a `Γ(S, ⊤)`-linear map.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackBaseResHom`: restriction of sections of
  `p^* F` along the preimage of an inclusion, as a `Γ(T, ⊤)`-linear map.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.sectionsBaseChangeHom`: the unit of `p^* ⊣ p_*`
  on sections over one open, as a `Γ(S, ⊤)`-linear map.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.sectionsBaseChangeMap`: its base change,
  `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)`.

## Main results

* `Stacks.AlgebraicGeometry.SectionsBaseChange.sectionsBaseChangeMap_tmul`: the normalisation,
  `b ⊗ a ↦ b • (pullback of a)`.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_sectionsBaseChangeMap_of_isAffineOpen`:
  **the comparison is bijective over an affine open**, with no flatness hypothesis.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.sectionsBaseChangeMap_comm_res`: **the comparison
  commutes with restriction**.
* `Stacks.ProjectiveCohomology.bijective_sectionsBaseChangeMap_iInf_chart`: the isomorphism over
  a finite intersection of standard charts of projective space. The restriction compatibility
  needs no projective-space form: `Stacks.ProjectiveCohomology.preimage_iInf_chart` already
  identifies the preimage of such an intersection with the corresponding intersection of charts
  downstairs, so the general statement applies verbatim.

## Implementation notes

The scalar structures over `Γ(S, ⊤)` and `Γ(T, ⊤)` are restrictions of scalars along the
structure morphisms and are not instances, so they are introduced by `letI` in the statements,
in the shape used throughout
`StacksFrontier/AlgebraicGeometry/PullbackSections/Qcqs.lean`.

The bijectivity proof is the composite of two isomorphisms. Over a pair of affine opens
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` identifies `Γ(p^* F, p⁻¹U)` with
`Γ(Y, p⁻¹U) ⊗_{Γ(X, U)} Γ(F, U)`, and `Algebra.IsPushout.cancelBaseChange` rewrites that as
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U)`, the pushout being
`Stacks.AlgebraicGeometry.SectionsBaseChange.algebraIsPushout_sections` fed by the affine case of
Mathlib's `pushoutSection`. One sequencing point is worth recording: the semilinearity field of
the `Γ(X, U)`-linear unit must be supplied by a previously stated equation whose right-hand side
uses the *native* `Γ(Y, p⁻¹U)`-action, because the `Module.compHom` action that the field's own
statement displays is not syntactically of that form and no rewrite applies to it.

The restriction compatibility is an application of
`Stacks.FlatSectionsDescent.liftBaseChange_lTensor`, whose hypothesis is exactly
`Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections_naturality`, naturality of the
unit in the open.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.FlatSectionsDescent
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.SectionsBaseChange

variable {S T X Y : Scheme.{u}}

/-! ### Restriction maps over the base rings -/

/-- Restriction of sections of `F` along an inclusion of opens, as a `Γ(S, ⊤)`-linear map for
the scalar structures restricted along `iX`. -/
public def baseResHom (iX : X ⟶ S) (F : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    letI := baseModule iX F U
    letI := baseModule iX F V
    Γ(F, U) →ₗ[Γ(S, ⊤)] Γ(F, V) :=
  letI := baseModule iX F U
  letI := baseModule iX F V
  { toFun := (F.presheaf.map (homOfLE h).op).hom
    map_add' := (F.presheaf.map (homOfLE h).op).hom.map_add
    map_smul' := fun a x =>
      map_smul_of_smul_eq _ (fun _ _ => rfl) _ (fun _ _ => rfl)
        (X.presheaf.map (homOfLE h).op).hom
        (fun a => (congrArg (fun m : Γ(S, ⊤) ⟶ Γ(X, V) => m.hom a)
          (Scheme.Hom.appLE_map iX (le_preimage_top iX U) (homOfLE h).op)).symm)
        _ (fun r y => Scheme.Modules.map_smul F (homOfLE h) r y) a x }

/-- Restriction of sections of `p^* F` along the preimage of an inclusion of opens, as a
`Γ(T, ⊤)`-linear map for the scalar structures restricted along `k`. -/
public def pullbackBaseResHom (k : Y ⟶ T) (p : Y ⟶ X) (F : X.Modules) {U V : X.Opens}
    (h : V ≤ U) :
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ V)
    Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) →ₗ[Γ(T, ⊤)]
      Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ V) :=
  letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ V)
  { toFun := (((Scheme.Modules.pullback p).obj F).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono p h)).op).hom
    map_add' := (((Scheme.Modules.pullback p).obj F).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono p h)).op).hom.map_add
    map_smul' := fun b y =>
      map_smul_of_smul_eq _ (fun _ _ => rfl) _ (fun _ _ => rfl)
        (Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono p h)).op).hom
        (fun b => (congrArg (fun m : Γ(T, ⊤) ⟶ Γ(Y, p ⁻¹ᵁ V) => m.hom b)
          (Scheme.Hom.appLE_map k (le_preimage_top k _)
            (homOfLE (Scheme.Hom.preimage_mono p h)).op)).symm)
        _ (fun r z => Scheme.Modules.map_smul ((Scheme.Modules.pullback p).obj F)
          (homOfLE (Scheme.Hom.preimage_mono p h)) r z) b y }

/-! ### The degreewise comparison -/

/-- The unit of `p^* ⊣ p_*` read on the sections over one open, as a `Γ(S, ⊤)`-linear map. -/
public def sectionsBaseChangeHom (iX : X ⟶ S) (p : Y ⟶ X) (F : X.Modules) (U : X.Opens) :
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Γ(F, U) →ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
  letI := baseModule iX F U
  letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  { toFun := pullbackUnitSections p F U
    map_add' := (pullbackUnitSections p F U).map_add
    map_smul' := fun a x =>
      map_smul_of_smul_eq _ (fun _ _ => rfl) _ (fun _ _ => rfl)
        (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom (appLE_comp_base iX p U)
        (pullbackUnitSections p F U)
        (fun r y => by
          rw [Scheme.Hom.appLE_preimage_self]
          exact pullbackUnitSections_smul p F U r y) a x }

variable {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}

/-- **The canonical degreewise base-change comparison.** Over an open `U` of `X` it is the
`Γ(T, ⊤)`-linear map `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)` sending `b ⊗ a` to `b`
times the pullback of `a`. -/
public def sectionsBaseChangeMap (H : IsPullback p k iX q) (F : X.Modules) (U : X.Opens) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U) →ₗ[Γ(T, ⊤)]
      Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
  letI := baseAlgebra q
  letI := baseModule iX F U
  letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  (sectionsBaseChangeHom iX p F U).liftBaseChange Γ(T, ⊤)

/-- **The normalisation.** The comparison sends `b ⊗ a` to `b` times the pullback of `a`. -/
public theorem sectionsBaseChangeMap_tmul (H : IsPullback p k iX q) (F : X.Modules)
    (U : X.Opens) (b : Γ(T, ⊤)) (a : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    sectionsBaseChangeMap H F U (b ⊗ₜ[Γ(S, ⊤)] a) = b • pullbackUnitSections p F U a := by
  rfl

/-- **The degreewise comparison is an isomorphism over an affine open.** For a cartesian square
with affine base, a quasi-coherent `F` and an affine open `U` of `X`, the canonical map
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)` is bijective.

No flatness is assumed: this is affine base change, [Stacks, Tag 02KG]. -/
public theorem bijective_sectionsBaseChangeMap_of_isAffineOpen (H : IsPullback p k iX q)
    [IsAffine S] [IsAffine T] (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Bijective (sectionsBaseChangeMap H F U) := by
  have hpaff : IsAffineHom p := MorphismProperty.of_isPullback H.flip inferInstance
  let algAB := baseAlgebra q
  let modAF := baseModule iX F U
  let modAG := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  let modBG := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  let towerG := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU.preimage p
  let algAX : Algebra Γ(S, ⊤) Γ(X, U) :=
    (iX.appLE ⊤ U (le_preimage_top iX U)).hom.toAlgebra
  let algAY : Algebra Γ(S, ⊤) Γ(Y, p ⁻¹ᵁ U) :=
    ((p ≫ iX).appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top (p ≫ iX) _)).hom.toAlgebra
  let algBY : Algebra Γ(T, ⊤) Γ(Y, p ⁻¹ᵁ U) :=
    (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom.toAlgebra
  let algXY : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
    (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have towerAXY : IsScalarTower Γ(S, ⊤) Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
    isScalarTower_of_smul_eq (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom (fun _ _ => rfl) _
      (fun _ _ => rfl) (appLE_comp_base iX p U)
  have towerATY : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, p ⁻¹ᵁ U) :=
    isScalarTower_of_smul_eq (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom (fun _ _ => rfl) _
      (fun _ _ => rfl) (sectionsSquare_comm H (p ⁻¹ᵁ U))
  have towerAXF : IsScalarTower Γ(S, ⊤) Γ(X, U) Γ(F, U) :=
    isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
      (iX.appLE ⊤ U (le_preimage_top iX U)).hom (fun _ _ => rfl) (fun _ => rfl)
  have hUST : (⊤ : T.Opens) ≤ q ⁻¹ᵁ (⊤ : S.Opens) := le_preimage_top q ⊤
  have hpo : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
    algebraIsPushout_sections H U (p ⁻¹ᵁ U) hUST (le_preimage_top iX U) (by simp)
      (isIso_pushoutSection_of_isAffineOpen H hUST (le_preimage_top iX U) (by simp)
        (isAffineOpen_top S) (isAffineOpen_top T) hU)
      le_rfl (le_preimage_top k _) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  let modXG : Module Γ(X, U) Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
    Module.compHom _ (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom
  have towerXYG : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U)
      Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
    isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
      (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom (fun _ _ => rfl) (fun _ => rfl)
  have hunitsmul : ∀ (r : Γ(X, U)) (a : Γ(F, U)),
      pullbackUnitSections p F U (r • a) =
        (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom r • pullbackUnitSections p F U a := by
    intro r a
    rw [Scheme.Hom.appLE_preimage_self]
    exact pullbackUnitSections_smul p F U r a
  let rhoU : Γ(F, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
    { toFun := pullbackUnitSections p F U
      map_add' := (pullbackUnitSections p F U).map_add
      map_smul' := hunitsmul }
  have hbc : IsBaseChange Γ(Y, p ⁻¹ᵁ U) rhoU :=
    AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso
      (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom rfl
      (affinePullbackSectionsBaseChangeIso p F hU hV le_rfl) rhoU (fun m => by
        rw [affinePullbackSectionsBaseChangeIso_one_tmul]
        exact pullbackSection_eq_pullbackUnitSections p F U m)
  let can := Algebra.IsPushout.cancelBaseChange Γ(S, ⊤) Γ(T, ⊤) Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Γ(F, U)
  let g : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U) ≃+
      Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
    (can.symm.toAddEquiv).trans hbc.equiv.toAddEquiv
  refine bijective_liftBaseChange_of_tmul (sectionsBaseChangeHom iX p F U)
    g.toAddMonoidHom g.bijective ?_
  intro b m
  show hbc.equiv (can.symm (b ⊗ₜ[Γ(S, ⊤)] m)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, hbc.equiv_tmul]
  rfl

/-- **The degreewise comparisons commute with restriction.** Comparing over `V` after
`id ⊗ res` is restricting after comparing over `U`.

The Čech differential of a covering family is an alternating sum of restriction maps, so this is
the compatibility that makes the family of degreewise comparisons a map of Čech complexes. -/
public theorem sectionsBaseChangeMap_comm_res (H : IsPullback p k iX q) (F : X.Modules)
    {U V : X.Opens} (h : V ≤ U) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule iX F V
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ V)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ V)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ V)
    ∀ z : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U),
      sectionsBaseChangeMap H F V (LinearMap.lTensor Γ(T, ⊤) (baseResHom iX F h) z) =
        pullbackBaseResHom k p F h (sectionsBaseChangeMap H F U z) := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule iX F V
  let := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  let := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ V)
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ V)
  let := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  let := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ V)
  exact fun z => liftBaseChange_lTensor (sectionsBaseChangeHom iX p F U)
    (sectionsBaseChangeHom iX p F V) (baseResHom iX F h) (pullbackBaseResHom k p F h)
    (fun a => pullbackUnitSections_naturality p F h a) z

end Stacks.AlgebraicGeometry.SectionsBaseChange

namespace Stacks.ProjectiveCohomology

open Stacks.AlgebraicGeometry.SectionsBaseChange

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) {A B : CommRingCat.{u}} (φ : A ⟶ B)

/-- **The degreewise base change over an intersection of standard charts of projective space.**
For a ring map `A ⟶ B` and a quasi-coherent module `F` on `ℙⁿ_A`, the canonical map

  `Γ(Spec B, ⊤) ⊗_{Γ(Spec A, ⊤)} Γ(F, ⋂ Uᵢ) ⟶ Γ(g^* F, ⋂ (Uᵢ)_B)`

is bijective, where the `Uᵢ` are standard charts of `ℙⁿ_A`. The intersection is affine by
`Stacks.ProjectiveCohomology.isAffineOpen_iInf_chart`, which is the only hypothesis the general
statement needs; in particular no flatness of `A ⟶ B` is used here.

This is the degreewise input to the comparison of Čech complexes for the standard cover. -/
public theorem bijective_sectionsBaseChangeMap_iInf_chart
    (F : (projectiveSpaceOverRing n A).Modules) [F.IsQuasicoherent]
    {r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) :
    letI H := isPullback_projectiveSpaceOverMap n (Spec.map φ)
    letI := baseAlgebra (Spec.map φ)
    letI := baseModule (pullback.fst (terminal.from (Spec A))
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) F (⨅ j, chart n A (s j))
    letI := baseModule (projectiveSpaceOverRingMap n φ ≫ pullback.fst (terminal.from (Spec A))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n φ)).obj F)
      (projectiveSpaceOverRingMap n φ ⁻¹ᵁ ⨅ j, chart n A (s j))
    letI := baseModule (pullback.fst (terminal.from (Spec B))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n φ)).obj F)
      (projectiveSpaceOverRingMap n φ ⁻¹ᵁ ⨅ j, chart n A (s j))
    letI := baseTower H ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n φ)).obj F)
      (projectiveSpaceOverRingMap n φ ⁻¹ᵁ ⨅ j, chart n A (s j))
    Function.Bijective (sectionsBaseChangeMap H F (⨅ j, chart n A (s j))) :=
  bijective_sectionsBaseChangeMap_of_isAffineOpen _ F (isAffineOpen_iInf_chart n A s)

end Stacks.ProjectiveCohomology

end

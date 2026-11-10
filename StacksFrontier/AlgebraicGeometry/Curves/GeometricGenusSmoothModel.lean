module

public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GeometricGenusModel
public import StacksFrontier.AlgebraicGeometry.Curves.ModelGlobalSections
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModelUniqueness
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothModelPurelyInseparable
public import StacksFrontier.AlgebraicGeometry.FunctionField.GenericPointBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.FieldTheory.CommonExtensionTensor

/-!
# The geometric genus of a geometrically irreducible curve

Let `k` be a field and let `X` be a geometrically irreducible curve over `k`. [Stacks, Tag 0BYF]
defines the *geometric genus* of `X` to be the genus of a smooth projective model of `X` possibly
defined over an extension field of `k`, as in [Stacks, Tag 0BY4]: for a field extension `K/k`,
let `Y_K` be a nonsingular projective model of `(X_K)_red`; when `Y_K` is smooth over `K`, the
geometric genus of `X` is the genus of `Y_K`. The source adds that this is well defined by
Tags 0BY4 and 0BY9. This file makes the definition and proves that it is well defined.

## Main definitions

* `AlgebraicGeometry.SmoothModelOverExtension`: a smooth projective model of `X` over an extension
  field, as in Tag 0BY4 — a field extension `K/k` together with a nonsingular projective model of
  `(X_K)_red` which is smooth over `K`.
* `AlgebraicGeometry.geometricGenusOfCurve`: **[Stacks, Tag 0BYF]**, the genus of such a model.

## Main results

* `AlgebraicGeometry.genus_eq_genus_of_smooth_model`: two smooth projective models of `X`, over
  any two extension fields `K` and `K'` of `k`, have the same genus. This is the well-definedness
  the source asserts.
* `AlgebraicGeometry.geometricGenusOfCurve_eq_genus`: the geometric genus is the genus of *every*
  smooth projective model of `X` over *every* extension field of `k`.
* `AlgebraicGeometry.nonempty_smoothModelOverExtension_of_isProper`: for proper `X` a smooth
  model exists, over a finite purely inseparable extension (Tag 0BY4 (2)).
* `AlgebraicGeometry.geometricGenusOfModel_eq_geometricGenusOfCurve`: the genus read off a smooth
  model by `AlgebraicGeometry.geometricGenusOfModel` is the geometric genus.

## The proof of well-definedness

Given smooth models `M` over `K` and `M'` over `K'`, choose a field `Ω` containing both `K` and
`K'` over `k` (a quotient of `K ⊗_k K'` by a maximal ideal). The source's argument is Tag 0BY4 (4):
`Y_Ω = (Y_K)_Ω = (Y_{K'})_Ω`. It is carried out as follows.

* The base change `M_Ω` is a smooth, hence regular, proper curve over `Ω`
  (`AlgebraicGeometry.isCurve_pullback_snd`), and by Tag 0BY9 it has the genus of `M`.
* The function field of `M_Ω` is `Ω`-isomorphic to the residue field at the generic point of
  `X_Ω`. Indeed `M` and `(X_K)_red` are integral and geometrically irreducible over `K` with
  `K`-isomorphic function fields, so the residue fields at the generic points of `M_Ω` and of
  `((X_K)_red)_Ω` are `Ω`-isomorphic
  (`AlgebraicGeometry.exists_residueField_genericPoint_ringEquiv`); the closed immersion
  `((X_K)_red)_Ω ⟶ (X_K)_Ω`, a homeomorphism, and the identification `(X_K)_Ω = X_Ω` do not change
  that residue field.
* So `M_Ω` and `M'_Ω` are regular proper curves over `Ω` with `Ω`-isomorphic function fields,
  hence isomorphic over `Ω` by the uniqueness of the nonsingular projective model
  ([Stacks, Tag 0BY1], `AlgebraicGeometry.genus_eq_of_functionFieldEquiv`), and have equal genus.

## Implementation notes

That `(X_K)_red` is a curve over `K` is proved here for every extension `K/k`
(`AlgebraicGeometry.isCurve_reducedBaseChangeStructureMap_of_isCurve`), so the model of Tag 0BY4
needs no further hypothesis. The value of `AlgebraicGeometry.geometricGenusOfCurve` when no smooth
model exists is `0`; by Tag 0BY4 (2) a smooth model always exists, and for proper `X` this file
proves it.

## References

* [Stacks Project, Tag 0BYF](https://stacks.math.columbia.edu/tag/0BYF)
* [Stacks Project, Tag 0BY4](https://stacks.math.columbia.edu/tag/0BY4)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The reduction `(X_K)_red` of the base change of a geometrically irreducible curve along a
field extension `K/k` is a curve over `K`: it is separated and of finite type, reduced, irreducible
because `X` is geometrically irreducible, and of dimension one because the reduction is a
homeomorphism and extension of the ground field preserves dimension. -/
instance isCurve_reducedBaseChangeStructureMap_of_isCurve (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsCurve k sX]
    [GeometricallyIrreducible sX] :
    IsCurve K (reducedBaseChangeStructureMap k K sX) := by
  have : IrreducibleSpace (reducedBaseChange k K sX) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (reducedBaseChangeStructureMap k K sX)
  have : IsIntegral (reducedBaseChange k K sX) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have hhomeo : IsHomeomorph
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι :=
    (inferInstance : UniversalHomeomorphism
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι)
      |>.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  have hdim : topologicalKrullDim (reducedBaseChange k K sX) = 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ hhomeo,
      topologicalKrullDim_baseChange k K
        (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) sX
        (IsPullback.of_hasPullback _ _)]
    exact IsCurve.topologicalKrullDim_eq_one (k := k) (f := sX)
  exact { topologicalKrullDim_eq_one := hdim }

/-- The structure morphism of a nonsingular projective model is a curve. -/
instance NonsingularProjectiveModel.instIsCurveStructureMap {F : Type u} [Field F]
    {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of F)} [IsCurve F sZ]
    (M : NonsingularProjectiveModel F Z sZ) :
    IsCurve F M.structureMap :=
  M.isCurve

/-- A nonsingular projective model of a geometrically irreducible curve is geometrically
irreducible. -/
instance NonsingularProjectiveModel.instGeometricallyIrreducibleStructureMap {F : Type u}
    [Field F] {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of F)} [IsCurve F sZ] [GeometricallyIrreducible sZ]
    (M : NonsingularProjectiveModel F Z sZ) : GeometricallyIrreducible M.structureMap :=
  M.geometricallyIrreducible_structureMap F

/-- The `F`-algebra structure on the function field of a curve over `F`, read in the residue field
at the generic point: it is evaluation of the pulled back global function. -/
theorem genericResidueEquiv_algebraMap {F : Type u} [Field F] {T : Scheme.{u}}
    (t : T ⟶ Spec (.of F)) [IsCurve F t] (a : F) :
    letI := functionFieldAlgebra F t
    genericResidueEquiv T (algebraMap F T.functionField a) =
      T.Γevaluation (genericPoint T) (t.appTop ((Scheme.ΓSpecIso (.of F)).inv a)) :=
  rfl

section BaseChange

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω]
  [Algebra k Ω] [IsScalarTower k K Ω] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsCurve k sX] [GeometricallyIrreducible sX]

/-- A dominant morphism over `S` between irreducible schemes which is surjective on stalks induces
a residue field isomorphism at the generic points, compatible with the global functions of `S`. -/
private theorem exists_residueField_ringEquiv_genericPoint {T T' S : Scheme.{u}}
    [IrreducibleSpace T] [IrreducibleSpace T'] (t : T ⟶ S) (t' : T' ⟶ S) (h : T ⟶ T')
    (hh : h ≫ t' = t) [IsDominant h] [SurjectiveOnStalks h] :
    ∃ Φ : T'.residueField (genericPoint T') ≃+* T.residueField (genericPoint T),
      ∀ a : Γ(S, ⊤), Φ (T'.Γevaluation _ (t'.appTop a)) = T.Γevaluation _ (t.appTop a) :=
  exists_residueField_ringEquiv_of_surjective_stalkMap t t' h hh _ _
    (map_genericPoint_of_isDominant h) (h.stalkMap_surjective _)

omit [IsCurve k sX] in
/-- For a tower `k → K → Ω`, the residue field at the generic point of `((X_K)_red)_Ω` is that of
`X_Ω`, compatibly with `Ω`: the closed immersion `((X_K)_red)_Ω ⟶ (X_K)_Ω` is a homeomorphism
which is surjective on local rings, and `(X_K)_Ω = X_Ω`. -/
theorem exists_residueField_ringEquiv_reducedBaseChange_baseChange :
    ∃ Φ : (pullback (reducedBaseChangeStructureMap k K sX)
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u}).residueField
          (genericPoint _) ≃+*
        (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) : Scheme.{u}).residueField
          (genericPoint _),
      ∀ ω : Ω, Φ (Scheme.Γevaluation _ _
          ((pullback.snd (reducedBaseChangeStructureMap k K sX)
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).appTop
              ((Scheme.ΓSpecIso (.of Ω)).inv ω))) =
        Scheme.Γevaluation _ _
          ((pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).appTop
            ((Scheme.ΓSpecIso (.of Ω)).inv ω)) := by
  set gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  set gΩK := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  set gΩ := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  have htower : gΩK ≫ gK = gΩ := by
    simp only [gK, gΩK, gΩ, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  -- the reduction step
  let ι := (pullback sX gK).reductionι
  let h₂ : (pullback (ι ≫ pullback.snd sX gK) gΩK : Scheme.{u}) ⟶
      pullback (pullback.snd sX gK) gΩK :=
    (pullbackRightPullbackFstIso (pullback.snd sX gK) gΩK ι).inv ≫ pullback.snd _ _
  have hh₂ : h₂ ≫ pullback.snd (pullback.snd sX gK) gΩK = pullback.snd _ _ := by
    simp [h₂]
  have : Surjective ι := ⟨Scheme.surjective_reductionι _⟩
  obtain ⟨Φ₂, hΦ₂⟩ := exists_residueField_ringEquiv_genericPoint _ _ h₂ hh₂
  -- the comparison of the two base changes of `X`
  let h₃ : (pullback (pullback.snd sX gK) gΩK : Scheme.{u}) ⟶ pullback sX gΩ :=
    (pullbackLeftPullbackSndIso sX gK gΩK).hom ≫ (pullback.congrHom rfl htower).hom
  have hh₃ : h₃ ≫ pullback.snd sX gΩ = pullback.snd _ _ := by
    simp only [h₃, pullback.congrHom, pullback.map, Category.assoc, Category.comp_id, asIso_hom,
      pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd]
  obtain ⟨Φ₃, hΦ₃⟩ := exists_residueField_ringEquiv_genericPoint _ _ h₃ hh₃
  refine ⟨Φ₂.symm.trans Φ₃.symm, fun ω => ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq, ← hΦ₂, RingEquiv.symm_apply_eq, ← hΦ₃]

omit [IsCurve k sX] in
/-- For a tower `k → K → Ω` and a nonsingular projective model `M` of `(X_K)_red`, the residue
field at the generic point of `M_Ω` is that of `X_Ω`, compatibly with `Ω`: `M` and `(X_K)_red`
have `K`-isomorphic function fields. -/
theorem exists_residueField_ringEquiv_model_baseChange
    [IsCurve K (reducedBaseChangeStructureMap k K sX)]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX)) :
    ∃ Φ : (pullback M.structureMap
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u}).residueField
          (genericPoint _) ≃+*
        (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) : Scheme.{u}).residueField
          (genericPoint _),
      ∀ ω : Ω, Φ (Scheme.Γevaluation _ _
          ((pullback.snd M.structureMap
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).appTop
              ((Scheme.ΓSpecIso (.of Ω)).inv ω))) =
        Scheme.Γevaluation _ _
          ((pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).appTop
            ((Scheme.ΓSpecIso (.of Ω)).inv ω)) := by
  let := functionFieldAlgebra K M.structureMap
  let := functionFieldAlgebra K (reducedBaseChangeStructureMap k K sX)
  obtain ⟨Φ₁, hΦ₁⟩ := exists_residueField_genericPoint_ringEquiv K Ω M.structureMap
    (reducedBaseChangeStructureMap k K sX) M.functionFieldEquiv.symm
  obtain ⟨Φ₂, hΦ₂⟩ := exists_residueField_ringEquiv_reducedBaseChange_baseChange k K Ω sX
  exact ⟨Φ₁.trans Φ₂, fun ω => by rw [RingEquiv.trans_apply, hΦ₁, hΦ₂]⟩

omit [IsCurve k sX] in
/-- **Two smooth models over a common extension have the same genus.** Let `k → K → Ω` and
`k → K' → Ω` be towers of fields, `M` a smooth nonsingular projective model of `(X_K)_red` and
`M'` one of `(X_{K'})_red`. Then `M` and `M'` have the same genus: their base changes to `Ω` are
regular proper curves over `Ω` with `Ω`-isomorphic function fields, hence isomorphic, and the
genus does not change under extension of the ground field (Tag 0BY9). -/
theorem genus_eq_genus_of_smooth_baseChange [IsCurve K (reducedBaseChangeStructureMap k K sX)]
    (K' : Type u) [Field K'] [Algebra k K'] [Algebra K' Ω] [IsScalarTower k K' Ω]
    [IsCurve K' (reducedBaseChangeStructureMap k K' sX)]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX))
    (M' : NonsingularProjectiveModel K' (reducedBaseChange k K' sX)
      (reducedBaseChangeStructureMap k K' sX))
    [Smooth M.structureMap] [Smooth M'.structureMap] :
    genus M.structureMap = genus M'.structureMap := by
  have := M.isProper_structureMap
  have := M'.isProper_structureMap
  obtain ⟨Φ, hΦ⟩ := exists_residueField_ringEquiv_model_baseChange k K Ω sX M
  obtain ⟨Φ', hΦ'⟩ := exists_residueField_ringEquiv_model_baseChange k K' Ω sX M'
  set t := pullback.snd M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  set t' := pullback.snd M'.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K' Ω)))
  have : IsCurve Ω t := isCurve_pullback_snd K Ω M.structureMap
  have : IsCurve Ω t' := isCurve_pullback_snd K' Ω M'.structureMap
  let := functionFieldAlgebra Ω t
  let := functionFieldAlgebra Ω t'
  let e : (pullback M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).functionField
      ≃ₐ[Ω] (pullback M'.structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap K' Ω)))).functionField :=
    AlgEquiv.ofRingEquiv (f := (genericResidueEquiv _).trans
      ((Φ.trans Φ'.symm).trans (genericResidueEquiv _).symm)) fun ω => by
      rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.trans_apply,
        RingEquiv.symm_apply_eq, genericResidueEquiv_algebraMap, genericResidueEquiv_algebraMap,
        hΦ, RingEquiv.symm_apply_eq, hΦ']
  rw [← genus_baseChange K Ω (pullback.fst _ _) t M.structureMap (IsPullback.of_hasPullback _ _),
    ← genus_baseChange K' Ω (pullback.fst _ _) t' M'.structureMap (IsPullback.of_hasPullback _ _)]
  exact genus_eq_of_functionFieldEquiv Ω t t' (isRegular_of_smooth_over_field t)
    (isRegular_of_smooth_over_field t') e

end BaseChange

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsCurve k sX]
  [GeometricallyIrreducible sX]

/-- **Stacks Project, Tag 0BYF, well-definedness.** Two smooth projective models of a
geometrically irreducible curve `X` over `k`, possibly defined over different extension fields
`K` and `K'` of `k` as in Tag 0BY4, have the same genus. -/
theorem genus_eq_genus_of_smooth_model (K K' : Type u) [Field K] [Field K'] [Algebra k K]
    [Algebra k K']
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX))
    (M' : NonsingularProjectiveModel K' (reducedBaseChange k K' sX)
      (reducedBaseChangeStructureMap k K' sX))
    (hM : Smooth M.structureMap) (hM' : Smooth M'.structureMap) :
    genus M.structureMap = genus M'.structureMap := by
  obtain ⟨Ω, _, _, _, _, _, _⟩ := exists_field_isScalarTower_isScalarTower k K K'
  exact genus_eq_genus_of_smooth_baseChange k K Ω sX K' M M'

/-- A smooth projective model of a geometrically irreducible curve `X` over `k`, possibly defined
over an extension field of `k`, as in [Stacks, Tag 0BY4]: a field extension `K/k` together with a
nonsingular projective model `Y_K` of `(X_K)_red` which is smooth over `K`. -/
structure SmoothModelOverExtension where
  /-- The extension field over which the model is defined. -/
  K : Type u
  /-- The field structure of the extension. -/
  [field : Field K]
  /-- The extension `K/k`. -/
  [algebra : Algebra k K]
  /-- The nonsingular projective model `Y_K` of `(X_K)_red`. -/
  model : NonsingularProjectiveModel K (reducedBaseChange k K sX)
    (reducedBaseChangeStructureMap k K sX)
  /-- The model is smooth over `K`. -/
  smooth : Smooth model.structureMap

attribute [instance] SmoothModelOverExtension.field SmoothModelOverExtension.algebra

open Classical in
/-- **Stacks Project, Tag 0BYF.** The *geometric genus* of a geometrically irreducible curve `X`
over a field `k`: the genus of a smooth projective model of `X` possibly defined over an
extension field of `k`, as in Tag 0BY4 — for an extension `K/k` such that the nonsingular
projective model `Y_K` of `(X_K)_red` is smooth over `K`, the genus `dim_K H¹(Y_K, 𝒪_{Y_K})`.

It does not depend on the choice of `K` or of the model, by
`AlgebraicGeometry.geometricGenusOfCurve_eq_genus`. Such a model exists by Tag 0BY4 (2)
(`AlgebraicGeometry.nonempty_smoothModelOverExtension_of_isProper` for proper `X`); the value
`0` is a junk value for the case where none is supplied. -/
@[stacks 0BYF]
def geometricGenusOfCurve : ℕ :=
  if h : Nonempty (SmoothModelOverExtension k sX) then genus h.some.model.structureMap else 0

/-- **Stacks Project, Tag 0BYF, well-definedness.** The geometric genus of `X` is the genus of
every smooth projective model of `X` over every extension field of `k`. -/
@[stacks 0BYF "the definition is independent of the extension field and of the smooth model"]
theorem geometricGenusOfCurve_eq_genus (N : SmoothModelOverExtension k sX) :
    geometricGenusOfCurve k sX = genus N.model.structureMap := by
  have h : Nonempty (SmoothModelOverExtension k sX) := ⟨N⟩
  rw [geometricGenusOfCurve, dite_eq_left h]
  exact genus_eq_genus_of_smooth_model k sX _ _ _ _ h.some.smooth N.smooth

/-- The geometric genus of `X` is the genus of every smooth nonsingular projective model of
`(X_K)_red`, for every extension field `K` of `k`. -/
theorem geometricGenusOfCurve_eq_genus_of_smooth (K : Type u) [Field K] [Algebra k K]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX)) (hM : Smooth M.structureMap) :
    geometricGenusOfCurve k sX = genus M.structureMap :=
  geometricGenusOfCurve_eq_genus k sX ⟨K, M, hM⟩

/-- The genus read off a smooth nonsingular projective model by
`AlgebraicGeometry.geometricGenusOfModel` is the geometric genus. -/
theorem geometricGenusOfModel_eq_geometricGenusOfCurve (K : Type u) [Field K] [Algebra k K]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX)) (hM : Smooth M.structureMap) :
    geometricGenusOfModel k K sX M = geometricGenusOfCurve k sX :=
  (geometricGenusOfCurve_eq_genus_of_smooth k sX K M hM).symm

/-- **Stacks Project, Tag 0BY4 (2), as used by Tag 0BYF.** A proper geometrically irreducible
curve over `k` has a smooth projective model over a finite purely inseparable extension of `k`, so
its geometric genus is the genus of an actual model. -/
theorem nonempty_smoothModelOverExtension_of_isProper [IsProper sX] :
    Nonempty (SmoothModelOverExtension k sX) := by
  obtain ⟨K, _, _, _, _, M, hM⟩ :=
    exists_isPurelyInseparable_smooth_nonsingularProjectiveModel k sX
  exact ⟨⟨K, M, hM⟩⟩

end AlgebraicGeometry

end

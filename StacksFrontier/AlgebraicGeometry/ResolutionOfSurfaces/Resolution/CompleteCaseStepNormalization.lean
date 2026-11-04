module

public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.ResidueField
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of a resolution in a finite extension of its function field

Let `B → A` be an injective map of domains and `g : Y ⟶ Spec B` a birational morphism from an
integral scheme. Write `K` for the function field of `Spec A`. The function field of `Y` is that
of `Spec B`, so `Spec K` maps to `Y` over `Spec B`, and hence to the fibre product
`Y ×_{Spec B} Spec A`. The inductive step of the proof of [Stacks, Tag 0BGN] considers the
normalization `X` of `Y ×_{Spec B} Spec A` in `Spec K` — the normalization of the fibre product,
with its components not dominating `Spec A` discarded — together with its morphisms to `Spec A`
and to `Y`.

This file constructs `X` and proves the global facts the source uses: `X` is a normal integral
scheme, and when `A` is a Noetherian complete local ring, `A` is finite over `B` and `g` is
proper and of finite type, `X ⟶ Y ×_{Spec B} Spec A` is finite, `X ⟶ Spec A` is a
modification and `X ⟶ Y` is finite.

## Main definitions

* `AlgebraicGeometry.CompleteCaseStep.genericPointToResolution`: the morphism `Spec K ⟶ Y`.
* `AlgebraicGeometry.CompleteCaseStep.liftToFibreProduct`: the morphism
  `Spec K ⟶ Y ×_{Spec B} Spec A`.
* `AlgebraicGeometry.CompleteCaseStep.toBase`: the morphism `X ⟶ Spec A`.
* `AlgebraicGeometry.CompleteCaseStep.toResolution`: the morphism `X ⟶ Y`.

## Main results

* `AlgebraicGeometry.isNormal_normalization_of_isField`: the normalization of a scheme in the
  spectrum of a field is normal.
* `AlgebraicGeometry.isBirational_of_surjective_functionFieldMap`: a dominant morphism of integral
  schemes inducing a surjection of function fields is birational.
* `AlgebraicGeometry.CompleteCaseStep.isNormal_normalization`: `X` is normal.
* `AlgebraicGeometry.CompleteCaseStep.isFinite_fromNormalization`: `X` is finite over the fibre
  product.
* `AlgebraicGeometry.CompleteCaseStep.isModification_toBase`: `X ⟶ Spec A` is a modification.
* `AlgebraicGeometry.CompleteCaseStep.isFinite_toResolution`: `X ⟶ Y` is finite.

## Implementation notes

The field `K` is the function field of `Spec A` rather than an abstract fraction field of `A`,
and `Spec K ⟶ Spec A` is `Scheme.fromSpecStalk` at the generic point; then every compatibility
needed is an instance of `AlgebraicGeometry.functionFieldMap_fromSpecStalk`. The morphism
`Spec K ⟶ Y` is `Spec K ⟶ Spec L ⟶ Y` for `L` the function field of `Y`, through the inverse of
the isomorphism of function fields induced by `g`.

The composition rule `AlgebraicGeometry.functionFieldMap_comp` is proved where it is needed here
and in `CompleteCaseStepDegree.lean`, from `AlgebraicGeometry.functionFieldMap_fromSpecStalk`,
rather than imported from `StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain`.
That module brings in `AlgebraicGeometry.IsProjectiveVariety` and its instance
`IsProjectiveVariety k f → IsProperVariety k f`, which solves `Field k` while `k` is still
unknown. Reached from `IsVariety.toIsIntegral`, whose field is not determined by the scheme,
it makes every `IsIntegral X` search that should fail enumerate all field instances, and the
resolution-of-surfaces modules above this one then time out on searches such as
`IsIso (f.stalkMap x)` for an open immersion `f`, or `Nontrivial X`.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
* [Stacks Project, Tag 0AVK](https://stacks.math.columbia.edu/tag/0AVK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Normalization in the spectrum of a field -/

/-- A morphism out of the spectrum of a field is quasi-compact: its source has a single point,
so every subset of it is compact. -/
theorem quasiCompact_of_isField {Z : Scheme.{u}} {F : CommRingCat.{u}} (hF : IsField F)
    (f : Spec F ⟶ Z) : QuasiCompact f := by
  let := hF.toField
  have : Finite (Spec F) := inferInstanceAs (Finite (PrimeSpectrum F))
  exact ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩

/-- Every section of the structure sheaf of the spectrum of a field, over any open, is zero or a
unit: the open is empty, or it is everything and the sections are the field. -/
private theorem eq_zero_or_isUnit_of_isField {F : CommRingCat.{u}} (hF : IsField F)
    (V : (Spec F).Opens) (x : Γ(Spec F, V)) : x = 0 ∨ IsUnit x := by
  let := hF.toField
  have : Subsingleton (Spec F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  rcases eq_or_ne V ⊥ with rfl | hV
  · exact Or.inl (Subsingleton.elim _ _)
  · obtain ⟨z, hz⟩ : (V : Set (Spec F)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun h ↦ hV (Opens.coe_eq_empty.mp h)
    obtain rfl : V = ⊤ := Opens.ext (Set.eq_univ_of_forall fun y ↦ Subsingleton.elim y z ▸ hz)
    let e := (Scheme.ΓSpecIso F).commRingCatIsoToRingEquiv
    rcases eq_or_ne (e x) 0 with h | h
    · exact Or.inl (e.injective (by rw [h, map_zero]))
    · refine Or.inr ?_
      have hu : IsUnit (e.symm (e x)) := (isUnit_iff_ne_zero.mpr h).map e.symm.toRingHom
      rwa [e.symm_apply_apply] at hu

/-- **The normalization of a scheme in the spectrum of a field is normal.** Over an affine open
`U` of the target it is the spectrum of the integral closure of `Γ(Z, U)` in a ring all of whose
elements are zero or units, and such an integral closure is a normal ring. -/
theorem isNormal_normalization_of_isField {Z : Scheme.{u}} {F : CommRingCat.{u}} (hF : IsField F)
    (f : Spec F ⟶ Z) [QuasiCompact f] [QuasiSeparated f] : IsNormal f.normalization := by
  have h : IsNormal f.normalization ↔
      ∃ (I : Type u) (U : I → f.normalization.Opens),
        IsOpenCover U ∧ ∀ i, IsNormal (U i).toScheme :=
    (isNormal_tfae _).out 1 4
  refine h.mpr ⟨Z.affineOpens, fun U ↦ f.fromNormalization ⁻¹ᵁ U.1, IsOpenCover.mk ?_, fun U ↦ ?_⟩
  · refine top_unique fun z _ ↦ ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f.fromNormalization z)) isOpen_univ
    exact Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩
  · let : Algebra Γ(Z, U.1) Γ(Spec F, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    have := isNormal_spec_of_isNormalRing
      (isNormalRing_integralClosure_of_isUnit_or_eq_zero Γ(Z, U.1) Γ(Spec F, f ⁻¹ᵁ U.1)
        fun x ↦ eq_zero_or_isUnit_of_isField hF _ x)
    exact isNormal_of_iso (relativeNormalizationPreimageIso f U.1 U.2)

/-- The extension of function fields of a dominant morphism of integral schemes is bijective iff
the stalk map at the generic point is an isomorphism. -/
private theorem bijective_functionFieldMap_iff_isIso_stalkMap {X Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Z] (f : X ⟶ Z) [IsDominant f] :
    Function.Bijective (functionFieldMap f) ↔ IsIso (f.stalkMap (genericPoint X)) :=
  (ConcreteCategory.isIso_iff_bijective _).symm.trans
    (isIso_comp_left_iff
      (Z.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom _)

/-- The extension of function fields induced by the canonical morphism from the spectrum of the
function field of an integral scheme is bijective: it is the stalk map at the closed point, which
is an isomorphism. -/
@[ega "I 2.4.2" "special case"]
theorem bijective_functionFieldMap_fromSpecStalk_genericPoint (Z : Scheme.{u}) [IsIntegral Z] :
    letI := isDominant_fromSpecStalk_genericPoint Z
    Function.Bijective (functionFieldMap (Z.fromSpecStalk (genericPoint Z))) := by
  let := isDominant_fromSpecStalk_genericPoint Z
  have hc : genericPoint (Spec Z.functionField) =
      (closedPoint Z.functionField : Spec Z.functionField) :=
    Subsingleton.elim (α := PrimeSpectrum Z.functionField) _ _
  rw [bijective_functionFieldMap_iff_isIso_stalkMap, hc]
  exact isIso_stalkMap_fromSpecStalk_closedPoint Z (genericPoint Z)

/-- **A dominant morphism of integral schemes is birational as soon as it induces a surjection of
function fields.** -/
theorem isBirational_of_surjective_functionFieldMap {X Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Z] (f : X ⟶ Z) [IsDominant f] (hf : Function.Surjective (functionFieldMap f)) :
    IsBirational f := by
  refine isBirational_of_bijOn_of_isIso_stalkMap f ?_ fun x hx => ?_
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    exact Set.bijOn_singleton.mpr (map_genericPoint_of_isDominant f)
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact (bijective_functionFieldMap_iff_isIso_stalkMap f).mp ⟨(functionFieldMap f).injective, hf⟩

namespace CompleteCaseStep

variable (B A : Type u) [CommRing B] [CommRing A] [IsDomain B] [IsDomain A] [Algebra B A]
  [FaithfulSMul B A] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ Spec (.of B))

/-- The morphism `Spec A ⟶ Spec B` induced by `B → A`. -/
abbrev baseMap : Spec (.of A) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (algebraMap B A))

/-- `Spec A ⟶ Spec B` is dominant, `B → A` being injective. -/
instance isDominant_baseMap : IsDominant (baseMap B A) := by
  constructor
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap B A)).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)]
  exact bot_le

/-- The function field of `Spec A`, the field `K` of the source. -/
abbrev fieldK : CommRingCat.{u} := (Spec (.of A)).functionField

/-- The morphism `Spec K ⟶ Spec A` from the spectrum of the function field. -/
abbrev genericPointToBase : Spec (fieldK A) ⟶ Spec (.of A) :=
  (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))

variable {B A g}

/-- The extension of function fields induced by a birational morphism `g : Y ⟶ Spec B` is an
isomorphism. -/
theorem isIso_functionFieldMap (hg : IsBirational g) :
    letI := hg.isDominant
    IsIso g.functionFieldMap := by
  let := hg.isDominant
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(functionFieldMap g).injective, hg.surjective_functionFieldMap⟩

variable (B A) in
/-- **The morphism `Spec K ⟶ Y`**: through the function field of `Y`, which is identified with
that of `Spec B` by `g`, and the extension of function fields induced by `Spec A ⟶ Spec B`. -/
def genericPointToResolution (hg : IsBirational g) : Spec (fieldK A) ⟶ Y :=
  letI := hg.isDominant
  letI := isIso_functionFieldMap hg
  Spec.map (inv g.functionFieldMap ≫ (baseMap B A).functionFieldMap) ≫
    Y.fromSpecStalk (genericPoint Y)

/-- The extension of function fields of a dominant morphism is compatible with the canonical
morphisms from the spectra of the function fields. -/
private theorem SpecMap_functionFieldMap_fromSpecStalk {X Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Z] (f : X ⟶ Z) [IsDominant f] :
    Spec.map f.functionFieldMap ≫ Z.fromSpecStalk (genericPoint Z) =
      X.fromSpecStalk (genericPoint X) ≫ f :=
  functionFieldMap_fromSpecStalk f

/-- `Spec K ⟶ Y ⟶ Spec B` is `Spec K ⟶ Spec A ⟶ Spec B`. -/
theorem genericPointToResolution_comp (hg : IsBirational g) :
    genericPointToResolution B A hg ≫ g = genericPointToBase A ≫ baseMap B A := by
  let := hg.isDominant
  let := isIso_functionFieldMap hg
  rw [genericPointToResolution, Category.assoc, ← SpecMap_functionFieldMap_fromSpecStalk g,
    Spec.map_comp, Category.assoc, ← Category.assoc (Spec.map (inv g.functionFieldMap)),
    ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp,
    SpecMap_functionFieldMap_fromSpecStalk]

variable (B A) in
/-- **The morphism `Spec K ⟶ Y ×_{Spec B} Spec A`.** -/
def liftToFibreProduct (hg : IsBirational g) : Spec (fieldK A) ⟶ pullback g (baseMap B A) :=
  pullback.lift (genericPointToResolution B A hg) (genericPointToBase A)
    (genericPointToResolution_comp hg)

/-- `Spec K ⟶ Y ×_{Spec B} Spec A` is quasi-compact, its source having one point. -/
instance quasiCompact_liftToFibreProduct (hg : IsBirational g) :
    QuasiCompact (liftToFibreProduct B A hg) :=
  quasiCompact_of_isField (Field.toIsField _) _

/-- `Spec K ⟶ Y ×_{Spec B} Spec A` is quasi-separated, its source being affine. -/
instance quasiSeparated_liftToFibreProduct (hg : IsBirational g) :
    QuasiSeparated (liftToFibreProduct B A hg) :=
  QuasiSeparated.of_quasiSeparatedSpace _

variable (B A) in
/-- **The morphism `X ⟶ Spec A`** from the normalization `X` of `Y ×_{Spec B} Spec A` in
`Spec K`. -/
def toBase (hg : IsBirational g) : (liftToFibreProduct B A hg).normalization ⟶ Spec (.of A) :=
  (liftToFibreProduct B A hg).fromNormalization ≫ pullback.snd g (baseMap B A)

variable (B A) in
/-- **The morphism `X ⟶ Y`** from the normalization `X` of `Y ×_{Spec B} Spec A` in
`Spec K`. -/
def toResolution (hg : IsBirational g) : (liftToFibreProduct B A hg).normalization ⟶ Y :=
  (liftToFibreProduct B A hg).fromNormalization ≫ pullback.fst g (baseMap B A)

/-- The two morphisms out of `X` lie over `Spec B` compatibly. -/
theorem toResolution_comp (hg : IsBirational g) :
    toResolution B A hg ≫ g = toBase B A hg ≫ baseMap B A := by
  rw [toResolution, toBase, Category.assoc, Category.assoc, pullback.condition]

/-- **`X` is normal.** -/
theorem isNormal_normalization (hg : IsBirational g) :
    IsNormal (liftToFibreProduct B A hg).normalization :=
  isNormal_normalization_of_isField (Field.toIsField _) _

/-- `Spec K ⟶ X ⟶ Spec A` is `Spec K ⟶ Spec A`. -/
theorem toNormalization_toBase (hg : IsBirational g) :
    (liftToFibreProduct B A hg).toNormalization ≫ toBase B A hg = genericPointToBase A := by
  rw [toBase, ← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, liftToFibreProduct,
    pullback.lift_snd]

/-- `Spec K ⟶ Y ×_{Spec B} Spec A ⟶ Spec A` is `Spec K ⟶ Spec A`. -/
theorem liftToFibreProduct_snd (hg : IsBirational g) :
    liftToFibreProduct B A hg ≫ pullback.snd g (baseMap B A) = genericPointToBase A :=
  pullback.lift_snd _ _ _

/-- **`X ⟶ Spec A` is birational.** The composite `Spec K ⟶ X ⟶ Spec A` induces an isomorphism of
function fields, so `X ⟶ Spec A` induces a surjection of function fields. -/
theorem isBirational_toBase (hg : IsBirational g) : IsBirational (toBase B A hg) := by
  let := isDominant_fromSpecStalk_genericPoint (Spec (.of A))
  let j := (liftToFibreProduct B A hg).toNormalization
  have hj : j ≫ toBase B A hg = genericPointToBase A := toNormalization_toBase hg
  have : IsDominant (j ≫ toBase B A hg) := by
    rw [hj]
    infer_instance
  have : IsDominant (toBase B A hg) := IsDominant.of_comp j _
  refine isBirational_of_surjective_functionFieldMap _ fun w => ?_
  have hcomp : functionFieldMap (j ≫ toBase B A hg) =
      (functionFieldMap j).comp (functionFieldMap (toBase B A hg)) := by
    suffices h : CommRingCat.ofHom (functionFieldMap (j ≫ toBase B A hg)) =
        CommRingCat.ofHom ((functionFieldMap j).comp (functionFieldMap (toBase B A hg))) from
      congrArg CommRingCat.Hom.hom h
    apply Spec.map_injective
    apply (cancel_mono ((Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))))).mp
    rw [functionFieldMap_fromSpecStalk (j ≫ toBase B A hg)]
    have h1 := functionFieldMap_fromSpecStalk j
    have h2 := functionFieldMap_fromSpecStalk (toBase B A hg)
    have hof : CommRingCat.ofHom ((functionFieldMap j).comp (functionFieldMap (toBase B A hg))) =
        CommRingCat.ofHom (functionFieldMap (toBase B A hg)) ≫
          CommRingCat.ofHom (functionFieldMap j) := rfl
    rw [hof, Spec.map_comp, Category.assoc, h2,
      ← Category.assoc (Spec.map (CommRingCat.ofHom (functionFieldMap j))), h1]
    exact (Category.assoc _ _ _).symm
  have hbij : Function.Bijective (functionFieldMap (j ≫ toBase B A hg)) := by
    rw! (castMode := .all) [hj]
    exact bijective_functionFieldMap_fromSpecStalk_genericPoint (Spec (.of A))
  obtain ⟨a, ha⟩ := hbij.2 (functionFieldMap j w)
  rw [hcomp, RingHom.comp_apply] at ha
  exact ⟨a, (functionFieldMap j).injective ha⟩

variable [IsNoetherianRing A] [IsLocalRing A] [IsPrecomplete (maximalIdeal A) A]
  [Module.Finite B A] [LocallyOfFiniteType g]

omit [Module.Finite B A] in
/-- **`X` is finite over `Y ×_{Spec B} Spec A`** ([Stacks, Tag 0AVK]): the fibre product is of
finite type over the Nagata ring `A`, and `Spec K ⟶ Y ×_{Spec B} Spec A` is surjective on residue
fields, its composite with the projection to `Spec A` being. -/
theorem isFinite_fromNormalization (hg : IsBirational g) :
    IsFinite (liftToFibreProduct B A hg).fromNormalization := by
  have hA : IsNagataScheme (Spec (.of A)) :=
    isNagataScheme_spec_of_isNagataRing _ IsNagataRing.of_isPrecomplete_maximalIdeal
  have hP : IsNagataScheme (pullback g (baseMap B A)) :=
    isNagataScheme_of_locallyOfFiniteType (pullback.snd g (baseMap B A)) hA
  have : Finite (Spec (fieldK A)) := inferInstanceAs (Finite (PrimeSpectrum (fieldK A)))
  refine AlgebraicGeometry.isFinite_fromNormalization (liftToFibreProduct B A hg) hP
    (fun U _ => have : Finite U := Subtype.finite
      NoetherianSpace.finite_irreducibleComponents) fun x => ?_
  let φ := liftToFibreProduct B A hg
  let := (φ.residueFieldMap x.1).hom.toAlgebra
  have hsurj : Function.Surjective (φ.residueFieldMap x.1).hom := by
    have h := surjective_residueFieldMap_of_surjectiveOnStalks (genericPointToBase A) x.1
    rw [Scheme.Hom.residueFieldMap_congr (liftToFibreProduct_snd hg).symm,
      Scheme.residueFieldMap_comp] at h
    exact fun z ↦ ⟨_, (h z).choose_spec⟩
  have : Algebra.EssFiniteType (pullback g (baseMap B A) |>.residueField (φ x.1))
      ((Spec (fieldK A)).residueField x.1) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
  exact IntermediateField.fg_top _ _

omit [Module.Finite B A] [LocallyOfFiniteType g] in
/-- **`X ⟶ Spec A` is a modification**: it is birational, `X` is integral, and it is proper, as
the composite of the finite morphism to the fibre product and the base change of the proper
morphism `g`. -/
theorem isModification_toBase [IsProper g] (hg : IsBirational g) :
    IsModification (toBase B A hg) := by
  have : IsFinite (liftToFibreProduct B A hg).fromNormalization := isFinite_fromNormalization hg
  refine ⟨isBirational_toBase hg, ?_, inferInstance⟩
  rw [toBase]
  infer_instance

/-- **`X ⟶ Y` is finite**: it is the composite of the finite morphism to the fibre product and the
base change of the finite morphism `Spec A ⟶ Spec B`. -/
theorem isFinite_toResolution (hg : IsBirational g) : IsFinite (toResolution B A hg) := by
  have : IsFinite (liftToFibreProduct B A hg).fromNormalization := isFinite_fromNormalization hg
  have : IsFinite (baseMap B A) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  rw [toResolution]
  infer_instance

end CompleteCaseStep

end AlgebraicGeometry

end

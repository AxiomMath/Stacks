module

public import StacksFrontier.AlgebraicGeometry.Models.ModelHomUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessLocal
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.FibreCohomology
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.SpecialFibreTransport
public import StacksFrontier.AlgebraicGeometry.SpecResidueFieldClosedPoint
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# The step of Stacks 0E97 through Stacks 0E89, over any discrete valuation ring

Let `R` be a discrete valuation ring with residue field `κ` and closed point `s`, let `W`, `X`,
`X'` be proper models of `V` over `R` and `c : W ⟶ X`, `c' : W ⟶ X'` morphisms of models. If the
special fibres `Xₛ`, `X'ₛ` are identified over `κ` compatibly with `cₛ`, `c'ₛ`, and
`𝒪_{Xₛ} = cₛ,* 𝒪_{Wₛ}`, `R¹cₛ,* 𝒪_{Wₛ} = 0`, then `X ≅ X'` by a unique isomorphism of models.
`Stacks.Models.existsUnique_isModelHom_iso_of_specialFibre_of_isAdicComplete_holds` does this
for `R` complete; here the completeness hypothesis is removed, as the proof of
[Stacks, Tag 0E89] does, by passing to the completion `R^` of `R`:

* the special fibres of the base changes to `R^` are those over `R`, since `κ(R) = κ(R^)`
  (`Stacks.Models.SpecialFibreDescent.baseChangeFibreIso`), so all the special-fibre hypotheses
  transport (`Stacks.Models.SpecialFibreDescent.exists_specialFibre_data_baseChange`); here the
  properties `𝒪 = f_*𝒪` and `R¹f_*𝒪 = 0` are invariant under isomorphisms of arrows
  (`Stacks.Models.SpecialFibreDescent.isIso_unitToPushforwardUnit_of_arrowIso`,
  `Stacks.Models.SpecialFibreDescent.isZero_rightDerived_one_unit_of_arrowIso`);
* the complete case gives `ψ : X_{R^} ≅ X'_{R^}` with `c_{R^} ≫ ψ = c'_{R^}`;
* `c` is scheme-theoretically dominant
  (`Stacks.Models.SpecialFibreDescent.isSchemeTheoreticallyDominant_of_specialMap`, from
  `AlgebraicGeometry.isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing`, which asks
  for fibres of `cₛ` of dimension at most one; this is where the hypothesis `dim Wₛ ≤ 1` enters),
  so `ψ` descends along the faithfully flat `Spec R^ ⟶ Spec R`
  (`AlgebraicGeometry.exists_iso_desc_of_isSchemeTheoreticallyDominant`).

## Main results

* `Stacks.Models.existsUnique_isModelHom_iso_of_specialFibre`: the statement above.

Everything here is a step of the proof of [Stacks, Tag 0E97]; nothing is registered.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Models.SpecialFibreDescent

section ArrowIso

variable {A B A' B' : Scheme.{u}} {f : A ⟶ B} {f' : A' ⟶ B'} (α : A ≅ A') (β : B ≅ B')

/-- **`𝒪 = f_*𝒪` is invariant under isomorphisms of arrows.** If `f : A ⟶ B` and `f' : A' ⟶ B'`
are related by isomorphisms `α : A ≅ A'`, `β : B ≅ B'` with `α ≫ f' = f ≫ β`, and
`𝒪_B ⟶ f_*𝒪_A` is an isomorphism, so is `𝒪_{B'} ⟶ f'_*𝒪_{A'}`. -/
theorem isIso_unitToPushforwardUnit_of_arrowIso (w : α.hom ≫ f' = f ≫ β.hom)
    (h : IsIso (C := B.Modules) (Scheme.Modules.unitToPushforwardUnit f)) :
    IsIso (C := B'.Modules) (Scheme.Modules.unitToPushforwardUnit f') := by
  have hf' : f' = α.inv ≫ f ≫ β.hom := by rw [← w, Iso.inv_hom_id_assoc]
  subst hf'
  have := SpecialFibreIso.isIso_unitToPushforwardUnit_of_isIso α.inv
  have := SpecialFibreIso.isIso_unitToPushforwardUnit_of_isIso β.hom
  rw [← Scheme.Modules.unitToPushforwardUnit_comp, ← Scheme.Modules.unitToPushforwardUnit_comp]
  infer_instance

/-- **`R¹f_*𝒪 = 0` is invariant under isomorphisms of arrows.** If `f : A ⟶ B` and `f' : A' ⟶ B'`
are related by isomorphisms `α : A ≅ A'`, `β : B ≅ B'` with `α ≫ f' = f ≫ β`, and
`R¹f_*𝒪_A = 0`, then `R¹f'_*𝒪_{A'} = 0`: `f' = α⁻¹ ≫ f ≫ β`, and neither a precomposition nor a
postcomposition with an isomorphism changes the vanishing. -/
theorem isZero_rightDerived_one_unit_of_arrowIso (w : α.hom ≫ f' = f ≫ β.hom)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit A.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward f').rightDerived 1).obj
      (SheafOfModules.unit A'.ringCatSheaf)) := by
  have hf' : f' = α.inv ≫ f ≫ β.hom := by rw [← w, Iso.inv_hom_id_assoc]
  subst hf'
  exact SpecialFibreIso.isZero_rightDerived_unit_iso_comp α.inv (f ≫ β.hom) 1
    (Stacks.BaseAdicFiltration.isZero_rightDerived_one_comp_of_isZero f β.hom _ h)

end ArrowIso

section ClosedPoint

/-- **The closed point of `Spec B`, through the residue field of the scheme.** Under the
identification of the residue field of `Spec B` at its closed point with that of `B`, the
canonical morphism from the spectrum of the residue field of `Spec B` at its closed point is
`Spec` of the residue map of `B`. -/
theorem specMap_residueFieldAtClosedPointEquiv_comp_fromSpecResidueField
    (B : CommRingCat.{u}) [IsLocalRing B] :
    Spec.map (CommRingCat.ofHom (residueFieldAtClosedPointEquiv (R := B)).toRingHom) ≫
      (Spec B).fromSpecResidueField (IsLocalRing.closedPoint B : Spec B) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) := by
  let cp : Spec B := IsLocalRing.closedPoint B
  let _ : IsLocalRing ((Spec B).presheaf.stalk cp) :=
    (Spec.stalkIso B cp).commRingCatIsoToRingEquiv.symm.isLocalRing
  simp only [Scheme.fromSpecResidueField]
  rw [← Spec_stalkClosedPointIso, ← Spec.map_comp, ← Spec.map_comp]
  apply Spec.map_inj.mpr
  apply CommRingCat.hom_ext
  ext a
  show IsLocalRing.ResidueField.map (stalkClosedPointIso B).hom.hom
    (IsLocalRing.residue _ ((stalkClosedPointIso B).inv.hom a)) =
      IsLocalRing.residue B a
  rw [IsLocalRing.ResidueField.map_residue]
  simp

end ClosedPoint

section Completion

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The morphism `Spec R^ ⟶ Spec R` from the spectrum of the completion of `R` along its maximal
ideal. -/
abbrev completionMap : Spec (.of (AdicCompletion (maximalIdeal R) R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (AdicCompletion (maximalIdeal R) R)))

/-- The completion of a Noetherian ring is flat over it. -/
instance flat_completionMap : Flat (completionMap R) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The completion of a Noetherian local ring is faithfully flat over it, so `Spec R^ ⟶ Spec R`
is surjective. -/
instance surjective_completionMap : Surjective (completionMap R) := by
  have : Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr this)).2

/-- The isomorphism `Spec κ(R^) ⟶ Spec κ(R)` of the closed points of `Spec R^` and `Spec R`. -/
abbrev residueFieldCompletionMap :
    Spec (.of (ResidueField (AdicCompletion (maximalIdeal R) R))) ⟶
      Spec (.of (ResidueField R)) :=
  Spec.map (CommRingCat.ofHom
    (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))))

/-- The residue fields of `R` and `R^` agree. -/
instance isIso_residueFieldCompletionMap : IsIso (residueFieldCompletionMap R) := by
  let e := RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective R)
  have : CommRingCat.ofHom
      (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) =
      e.toCommRingCatIso.hom := rfl
  rw [residueFieldCompletionMap, this]
  infer_instance

/-- The closed point of `Spec R^` lies over the closed point of `Spec R`, through the
identification of the residue fields. -/
theorem closedPoint_comp_completionMap :
    ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal R) R) ≫
      completionMap R =
    residueFieldCompletionMap R ≫ ContractionUniquenessComplete.closedPoint R := by
  rw [ContractionUniquenessComplete.closedPoint, ContractionUniquenessComplete.closedPoint,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1

end Completion

section BaseChangeFibre

variable {S T P Q X : Scheme.{u}} (f : X ⟶ S) (π : T ⟶ S) (t : P ⟶ T) (s : Q ⟶ S)
  (j : P ⟶ Q) [IsIso j] (h : t ≫ π = j ≫ s)

/-- The base change of `c : X ⟶ Y` along `π` lies over `T`. -/
theorem pullbackMap_snd {Y : Scheme.{u}} (g : Y ⟶ S) (c : X ⟶ Y) (w₁ : f ≫ 𝟙 S = c ≫ g)
    (w₂ : π ≫ 𝟙 S = 𝟙 T ≫ π) :
    pullback.map f π g π c (𝟙 T) (𝟙 S) w₁ w₂ ≫ pullback.snd g π = pullback.snd f π :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- **The fibre of a base change is a fibre of the original morphism.** For `f : X ⟶ S`,
`π : T ⟶ S` and points `t : P ⟶ T`, `s : Q ⟶ S` identified by an isomorphism `j : P ≅ Q` with
`t ≫ π = j ≫ s`, the fibre of `X_T ⟶ T` over `t` is the fibre of `f` over `s`. -/
def baseChangeFibreIso : pullback (pullback.snd f π) t ≅ pullback f s :=
  pullbackLeftPullbackSndIso f π t ≪≫
    asIso (pullback.map f (t ≫ π) f s (𝟙 _) j (𝟙 _) (by simp) (by simp [h]))

/-- The identification of fibres commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem baseChangeFibreIso_hom_fst :
    (baseChangeFibreIso f π t s j h).hom ≫ pullback.fst f s =
      pullback.fst _ _ ≫ pullback.fst f π := by
  rw [baseChangeFibreIso, Iso.trans_hom, asIso_hom, Category.assoc, pullback.lift_fst,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

/-- The identification of fibres lies over `j`. -/
@[reassoc (attr := simp)]
theorem baseChangeFibreIso_hom_snd :
    (baseChangeFibreIso f π t s j h).hom ≫ pullback.snd f s = pullback.snd _ _ ≫ j := by
  rw [baseChangeFibreIso, Iso.trans_hom, asIso_hom, Category.assoc, pullback.lift_snd,
    pullbackLeftPullbackSndIso_hom_snd_assoc]

/-- **The identification of fibres is natural**: it carries the fibre over `t` of the base
change of `c : X ⟶ Y` to the fibre of `c` over `s`. -/
theorem baseChangeFibreIso_naturality {Y : Scheme.{u}} (g : Y ⟶ S) (c : X ⟶ Y)
    (hc : c ≫ g = f) :
    pullback.map (pullback.snd f π) t (pullback.snd g π) t
        (pullback.map f π g π c (𝟙 T) (𝟙 S) (by simp [hc]) (by simp)) (𝟙 P) (𝟙 T)
        (by rw [Category.comp_id, pullbackMap_snd]) (by simp) ≫
          (baseChangeFibreIso g π t s j h).hom =
      (baseChangeFibreIso f π t s j h).hom ≫
        pullback.map f s g s c (𝟙 Q) (𝟙 S) (by simp [hc]) (by simp) := by
  apply pullback.hom_ext <;>
    simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

include h in
/-- **Special-fibre data descend along a base change with the same closed point.** Let
`c : W ⟶ X`, `c' : W ⟶ X'` be morphisms over `S`, `π : T ⟶ S`, and `t : P ⟶ T`, `s : Q ⟶ S`
points identified by an isomorphism `j` with `t ≫ π = j ≫ s`. An identification `φ` of the
fibres of `X`, `X'` over `s` compatible with `c`, `c'`, together with `𝒪 = c_*𝒪` and `R¹c_*𝒪 = 0`
on fibres over `s`, gives the same data for the base changes to `T` on fibres over `t`. -/
theorem exists_specialFibre_data_baseChange {Y Y' : Scheme.{u}} (g : Y ⟶ S) (g' : Y' ⟶ S)
    (c : X ⟶ Y) (hc : c ≫ g = f) (c' : X ⟶ Y') (hc' : c' ≫ g' = f)
    (φ : pullback g s ≅ pullback g' s) (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : pullback.map f s g s c (𝟙 Q) (𝟙 S) (by simp [hc]) (by simp) ≫ φ.hom =
      pullback.map f s g' s c' (𝟙 Q) (𝟙 S) (by simp [hc']) (by simp))
    (h0 : IsIso (C := (pullback g s).Modules) (Scheme.Modules.unitToPushforwardUnit
      (pullback.map f s g s c (𝟙 Q) (𝟙 S) (by simp [hc]) (by simp))))
    (hR : IsZero (((Scheme.Modules.pushforward
        (pullback.map f s g s c (𝟙 Q) (𝟙 S) (by simp [hc]) (by simp))).rightDerived 1).obj
      (SheafOfModules.unit (pullback f s).ringCatSheaf))) :
    ∃ φT : pullback (pullback.snd g π) t ≅ pullback (pullback.snd g' π) t,
      φT.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      pullback.map (pullback.snd f π) t (pullback.snd g π) t
          (pullback.map f π g π c (𝟙 T) (𝟙 S) (by simp [hc]) (by simp)) (𝟙 P) (𝟙 T)
          (by rw [Category.comp_id, pullbackMap_snd]) (by simp) ≫ φT.hom =
        pullback.map (pullback.snd f π) t (pullback.snd g' π) t
          (pullback.map f π g' π c' (𝟙 T) (𝟙 S) (by simp [hc']) (by simp)) (𝟙 P) (𝟙 T)
          (by rw [Category.comp_id, pullbackMap_snd]) (by simp) ∧
      IsIso (C := (pullback (pullback.snd g π) t).Modules) (Scheme.Modules.unitToPushforwardUnit
        (pullback.map (pullback.snd f π) t (pullback.snd g π) t
          (pullback.map f π g π c (𝟙 T) (𝟙 S) (by simp [hc]) (by simp)) (𝟙 P) (𝟙 T)
          (by rw [Category.comp_id, pullbackMap_snd]) (by simp))) ∧
      IsZero (((Scheme.Modules.pushforward
        (pullback.map (pullback.snd f π) t (pullback.snd g π) t
          (pullback.map f π g π c (𝟙 T) (𝟙 S) (by simp [hc]) (by simp)) (𝟙 P) (𝟙 T)
          (by rw [Category.comp_id, pullbackMap_snd]) (by simp))).rightDerived 1).obj
        (SheafOfModules.unit (pullback (pullback.snd f π) t).ringCatSheaf)) := by
  have nat := baseChangeFibreIso_naturality f π t s j h g c hc
  have nat' := baseChangeFibreIso_naturality f π t s j h g' c' hc'
  have w : (baseChangeFibreIso f π t s j h).symm.hom ≫
        pullback.map (pullback.snd f π) t (pullback.snd g π) t
          (pullback.map f π g π c (𝟙 T) (𝟙 S) (by simp [hc]) (by simp)) (𝟙 P) (𝟙 T)
          (by rw [Category.comp_id, pullbackMap_snd]) (by simp) =
      pullback.map f s g s c (𝟙 Q) (𝟙 S) (by simp [hc]) (by simp) ≫
        (baseChangeFibreIso g π t s j h).symm.hom := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← reassoc_of% nat, Iso.hom_inv_id]
    exact (Category.comp_id _).symm
  refine ⟨baseChangeFibreIso g π t s j h ≪≫ φ ≪≫ (baseChangeFibreIso g' π t s j h).symm,
    ?_, ?_, isIso_unitToPushforwardUnit_of_arrowIso _ _ w h0,
    isZero_rightDerived_one_unit_of_arrowIso _ _ w hR⟩
  · rw [← cancel_mono j, Category.assoc, ← baseChangeFibreIso_hom_snd g' π t s j h,
      ← baseChangeFibreIso_hom_snd g π t s j h]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, hφ]
  · rw [← cancel_mono (baseChangeFibreIso g' π t s j h).hom, nat']
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% nat, hφc]

end BaseChangeFibre

section FiberForm

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] {W X : Scheme.{u}}
  (pW : W ⟶ Spec (.of Λ)) (p : X ⟶ Spec (.of Λ)) (c : W ⟶ X) (hc : c ≫ p = pW)

/-- The identification of `Spec κ(Λ)` with the spectrum of the residue field of the scheme
`Spec Λ` at its closed point. -/
abbrev closedPointResidueFieldMap :
    Spec (.of (ResidueField Λ)) ⟶ Spec ((Spec (.of Λ)).residueField (closedPoint Λ)) :=
  Spec.map (CommRingCat.ofHom (residueFieldAtClosedPointEquiv (R := .of Λ)).toRingHom)

/-- The identification of the two residue fields at the closed point is an isomorphism. -/
instance isIso_closedPointResidueFieldMap : IsIso (closedPointResidueFieldMap (Λ := Λ)) :=
  inferInstanceAs
    (IsIso (Spec.map (residueFieldAtClosedPointEquiv (R := .of Λ)).toCommRingCatIso.hom))

/-- The closed point `Spec κ(Λ) ⟶ Spec Λ` factors through the canonical morphism from the
spectrum of the residue field of the scheme `Spec Λ`. -/
theorem closedPointResidueFieldMap_comp_fromSpecResidueField :
    closedPointResidueFieldMap (Λ := Λ) ≫ (Spec (.of Λ)).fromSpecResidueField (closedPoint Λ) =
      ContractionUniquenessComplete.closedPoint Λ :=
  specMap_residueFieldAtClosedPointEquiv_comp_fromSpecResidueField (.of Λ)

/-- The special fibre `pullback p s` of `p`, along `s : Spec κ(Λ) ⟶ Spec Λ`, maps isomorphically
onto the scheme-theoretic fibre `p.fiber` at the closed point. -/
abbrev specialFibreToFiber :
    pullback p (ContractionUniquenessComplete.closedPoint Λ) ⟶ p.fiber (closedPoint Λ) :=
  pullback.map p _ p _ (𝟙 _) closedPointResidueFieldMap (𝟙 _) (by simp)
    (by rw [Category.comp_id, closedPointResidueFieldMap_comp_fromSpecResidueField])

/-- The comparison of the special fibre with the scheme-theoretic fibre is an isomorphism. -/
instance isIso_specialFibreToFiber : IsIso (specialFibreToFiber p) :=
  pullback.map_isIso _ _ _ _ _ _ _ _ _

/-- The base change of `c` along the special fibre of `p` maps isomorphically onto its base
change along the scheme-theoretic fibre of `p` at the closed point. -/
abbrev specialFibrePullbackToFiberPullback :
    pullback c (pullback.fst p (ContractionUniquenessComplete.closedPoint Λ)) ⟶
      pullback c (p.fiberι (closedPoint Λ)) :=
  pullback.map c _ c _ (𝟙 _) (specialFibreToFiber p) (𝟙 _) (by simp)
    (by rw [Category.comp_id]; exact ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm)

/-- The comparison of the two base changes of `c` is an isomorphism. -/
instance isIso_specialFibrePullbackToFiberPullback :
    IsIso (specialFibrePullbackToFiberPullback p c) :=
  pullback.map_isIso _ _ _ _ _ _ _ _ _

/-- The special-fibre map `cₛ` is isomorphic, as an arrow, to the base change of `c` along the
scheme-theoretic fibre of `p` at the closed point. -/
private theorem exists_arrowIso_specialMap_fiber :
    ∃ (α : pullback pW (ContractionUniquenessComplete.closedPoint Λ) ≅
        pullback c (p.fiberι (closedPoint Λ)))
      (β : pullback p (ContractionUniquenessComplete.closedPoint Λ) ≅ p.fiber (closedPoint Λ)),
      α.hom ≫ pullback.snd c (p.fiberι (closedPoint Λ)) =
        ContractionUniquenessComplete.specialMap pW p c hc ≫ β.hom := by
  have sq := SpecialFibreIso.isPullback_pullbackMap pW p c hc
    (ContractionUniquenessComplete.closedPoint Λ) (by simp [hc]) (by simp)
  refine ⟨sq.isoPullback ≪≫ asIso (specialFibrePullbackToFiberPullback p c),
    asIso (specialFibreToFiber p), ?_⟩
  rw [Iso.trans_hom, asIso_hom, asIso_hom, Category.assoc, specialFibrePullbackToFiberPullback,
    pullback.lift_snd, ← Category.assoc, sq.isoPullback_hom_snd]

/-- `𝒪 = c_*𝒪` on special fibres in the spelling of `specialMap` gives it in the spelling of the
scheme-theoretic fibre at the closed point. -/
theorem isIso_unitToPushforwardUnit_fiber_of_specialMap
    (h0 : IsIso (C := (pullback p (ContractionUniquenessComplete.closedPoint Λ)).Modules)
      (Scheme.Modules.unitToPushforwardUnit
        (ContractionUniquenessComplete.specialMap pW p c hc))) :
    IsIso (Scheme.Modules.unitToPushforwardUnit
      (pullback.snd c (p.fiberι (closedPoint Λ)))) := by
  obtain ⟨α, β, w⟩ := exists_arrowIso_specialMap_fiber pW p c hc
  exact isIso_unitToPushforwardUnit_of_arrowIso α β w h0

/-- `R¹c_*𝒪 = 0` on special fibres in the spelling of `specialMap` gives it in the spelling of
the scheme-theoretic fibre at the closed point. -/
theorem isZero_firstDirectImage_fiber_of_specialMap
    (hR : IsZero (((Scheme.Modules.pushforward
        (ContractionUniquenessComplete.specialMap pW p c hc)).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback pW (ContractionUniquenessComplete.closedPoint Λ)).ringCatSheaf))) :
    IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf
      (pullback.snd c (p.fiberι (closedPoint Λ)))) := by
  obtain ⟨α, β, w⟩ := exists_arrowIso_specialMap_fiber pW p c hc
  exact (SpecialFibreIso.isZero_firstDirectImageStructureSheaf_iff _).2
    (isZero_rightDerived_one_unit_of_arrowIso α β w hR)

end FiberForm

section Dominance

/-- **The contraction is scheme-theoretically dominant, from its special fibre.** Let `Λ` be a
Noetherian local ring, `pW : W ⟶ Spec Λ` proper and flat with special fibre of dimension at most
one, `p : X ⟶ Spec Λ` proper and `c : W ⟶ X` over `Spec Λ`. If `𝒪 = c_*𝒪` and `R¹c_*𝒪 = 0` on
special fibres, then `c` is scheme-theoretically dominant
(`AlgebraicGeometry.isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing`). -/
theorem isSchemeTheoreticallyDominant_of_specialMap {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
    [IsNoetherianRing Λ] {W X : Scheme.{u}} (pW : W ⟶ Spec (.of Λ)) (p : X ⟶ Spec (.of Λ))
    [IsProper pW] [Flat pW] [IsProper p] (c : W ⟶ X) (hc : c ≫ p = pW)
    (hdim : topologicalKrullDim
      (pullback pW (ContractionUniquenessComplete.closedPoint Λ) : Scheme.{u}) ≤ 1)
    (h0 : IsIso (C := (pullback p (ContractionUniquenessComplete.closedPoint Λ)).Modules)
      (Scheme.Modules.unitToPushforwardUnit
        (ContractionUniquenessComplete.specialMap pW p c hc)))
    (hR : IsZero (((Scheme.Modules.pushforward
        (ContractionUniquenessComplete.specialMap pW p c hc)).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback pW (ContractionUniquenessComplete.closedPoint Λ)).ringCatSheaf))) :
    IsSchemeTheoreticallyDominant c := by
  have : IsProper (c ≫ p) := by rw [hc]; infer_instance
  have : IsProper c := IsProper.of_comp c p
  have : Flat (c ≫ p) := by rw [hc]; infer_instance
  refine isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing c p
    (fun x _ => Flat.stalkMap (c ≫ p) x) (fun y => ?_)
    (isZero_firstDirectImage_fiber_of_specialMap pW p c hc hR)
    (isIso_unitToPushforwardUnit_fiber_of_specialMap pW p c hc h0)
  refine ((Scheme.Hom.fiberι _ y).isEmbedding.isInducing.topologicalKrullDim_le).trans ?_
  let m := pullback.map pW (ContractionUniquenessComplete.closedPoint Λ) (c ≫ p)
    ((Spec (.of Λ)).fromSpecResidueField (closedPoint Λ)) (𝟙 _) closedPointResidueFieldMap (𝟙 _)
    (by simp [hc]) (by rw [Category.comp_id, closedPointResidueFieldMap_comp_fromSpecResidueField])
  refine ((inv m).isOpenEmbedding.isInducing.topologicalKrullDim_le).trans ?_
  exact_mod_cast hdim

end Dominance

end Stacks.Models.SpecialFibreDescent

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The step of [Stacks, Tag 0E97] that goes through [Stacks, Tag 0E89].** Let `R` be a discrete
valuation ring with residue field `κ` and closed point `s`, let `W`, `X`, `X'` be proper models of
`V` and let `c : W ⟶ X`, `c' : W ⟶ X'` be morphisms of models, the special fibre `Wₛ` being of
dimension at most one. If the special fibres `Xₛ`, `X'ₛ` are identified over `κ` by an
isomorphism `φ` with `cₛ ≫ φ = c'ₛ`, and `𝒪_{Xₛ} ⟶ cₛ,* 𝒪_{Wₛ}` is an isomorphism with
`R¹cₛ,* 𝒪_{Wₛ} = 0`, then there is a unique isomorphism of models `X ≅ X'`.

The source's proof: over the completion `R^` the data give an isomorphism `X_{R^} ≅ X'_{R^}`
compatible with `c`, `c'`
(`AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds`), the special
fibres being unchanged; as `c` is scheme-theoretically dominant
(`Stacks.Models.SpecialFibreDescent.isSchemeTheoreticallyDominant_of_specialMap`) it descends
along the faithfully flat `Spec R^ ⟶ Spec R`
(`AlgebraicGeometry.exists_iso_desc_of_isSchemeTheoreticallyDominant`). It is a step of the proof
of [Stacks, Tag 0E97], so it is not registered. -/
theorem existsUnique_isModelHom_iso_of_specialFibre
    {V W X X' : Scheme.{u}} {v : V ⟶ Spec (.of K)} {pW : W ⟶ Spec (.of R)}
    {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {eW : V ≅ pullback pW (genericPointInclusion R K)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)}
    (hW : IsModel v pW eW) (hX : IsModel v p e) (hX' : IsModel v p' e')
    [IsProper pW] [IsProper p] [IsProper p']
    {c : W ⟶ X} {c' : W ⟶ X'} (hcX : IsModelHom pW p eW e c) (hcX' : IsModelHom pW p' eW e' c')
    (φ : pullback p (ContractionUniquenessComplete.closedPoint R) ≅
      pullback p' (ContractionUniquenessComplete.closedPoint R))
    (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : ContractionUniquenessComplete.specialMap pW p c hcX.1 ≫ φ.hom =
      ContractionUniquenessComplete.specialMap pW p' c' hcX'.1)
    (h0 : IsIso (C := (pullback p (ContractionUniquenessComplete.closedPoint R)).Modules)
      (Scheme.Modules.unitToPushforwardUnit
        (ContractionUniquenessComplete.specialMap pW p c hcX.1)))
    (hR : IsZero (((Scheme.Modules.pushforward
        (ContractionUniquenessComplete.specialMap pW p c hcX.1)).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback pW (ContractionUniquenessComplete.closedPoint R)).ringCatSheaf)))
    (hdim : topologicalKrullDim
      (pullback pW (ContractionUniquenessComplete.closedPoint R) : Scheme.{u}) ≤ 1) :
    ∃! f : X ≅ X', IsModelHom p p' e e' f.hom := by
  have : Flat pW := hW.1
  have : Flat p := hX.1
  have : Flat p' := hX'.1
  have : IsSchemeTheoreticallyDominant c :=
    SpecialFibreDescent.isSchemeTheoreticallyDominant_of_specialMap pW p c hcX.1 hdim h0 hR
  have : IsProper (c ≫ p) := by rw [hcX.1]; infer_instance
  have : IsProper c := IsProper.of_comp c p
  obtain ⟨φΛ, hφΛ, hφcΛ, h0Λ, hRΛ⟩ := SpecialFibreDescent.exists_specialFibre_data_baseChange pW
    (SpecialFibreDescent.completionMap R)
    (ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal R) R))
    (ContractionUniquenessComplete.closedPoint R) (SpecialFibreDescent.residueFieldCompletionMap R)
    (SpecialFibreDescent.closedPoint_comp_completionMap R) p p' c hcX.1 c' hcX'.1 φ hφ hφc h0 hR
  obtain ⟨ψ₀, hψ₀, hcψ₀, -⟩ := exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds
    (Λ := AdicCompletion (maximalIdeal R) R) inferInstance
    (pullback.snd pW (SpecialFibreDescent.completionMap R))
    (pullback.snd p (SpecialFibreDescent.completionMap R))
    (pullback.snd p' (SpecialFibreDescent.completionMap R))
    _ ((pullback.lift_snd _ _ _).trans (Category.comp_id _))
    _ ((pullback.lift_snd _ _ _).trans (Category.comp_id _)) φΛ hφΛ hφcΛ h0Λ hRΛ
  obtain ⟨ψ, hψ, -, hcψ⟩ := exists_iso_desc_of_isSchemeTheoreticallyDominant
    (SpecialFibreDescent.completionMap R) c hcX.1 c' hcX'.1 ψ₀ hψ₀ hcψ₀
  exact existsUnique_isModelHom_iso_of_comp_eq hX hcX hcX' ψ hψ hcψ

end Stacks.Models

end

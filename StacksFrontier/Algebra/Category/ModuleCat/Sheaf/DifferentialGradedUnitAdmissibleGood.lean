module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitFreeModule

/-!
# An extension of a free complex with zero differential by a good module is good

Let `(C, O)` be a ringed site. Let `0 ⟶ K ⟶ L ⟶ M ⟶ 0` be a sequence of cochain complexes of
`O`-modules which is split in every degree, and suppose that the differential of `M` is zero. Then
`L` is the mapping cone of a morphism `M[-1] ⟶ K`, namely the connecting morphism of the split
sequence. So when `K` is good in the sense of Tag 0FSA and `M` is a free complex with zero
differential on a family of presheaves of sets, `L` is good: the cone of a morphism of good
modules is good (Tag 0FSC at goodness), and `M[-1]` is again a free complex with zero
differential.

## Main definitions

* `CochainComplex.splitConnecting`: the connecting morphism `M[-1] ⟶ K` of a degreewise split
  short exact sequence whose third term has zero differential.
* `CochainComplex.splitConeIso`: `mappingCone (splitConnecting …) ≅ L`.

## Main results

* `SheafOfModules.isGoodToposBaseChange_of_split_freeOnPresheaves`: **the middle term is good.**

## References

* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w v₁ u₁ v₂ u₂

namespace CochainComplex

open HomComplex

section Split

variable {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]
  (S : ShortComplex (CochainComplex D ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval D _ n)).Splitting)
  (hM : ∀ p q, S.X₃.d p q = 0)

include σ

/-- The retraction of the first map in degree `p`. -/
def splR (p : ℤ) : S.X₂.X p ⟶ S.X₁.X p := (σ p).r

/-- The section of the second map in degree `p`. -/
def splS (p : ℤ) : S.X₃.X p ⟶ S.X₂.X p := (σ p).s

omit [HasBinaryBiproducts D] in
/-- The retraction `splR` is a left inverse of the first map in degree `p`. -/
@[reassoc (attr := simp)]
theorem split_f_r (p : ℤ) : S.f.f p ≫ splR S σ p = 𝟙 _ := (σ p).f_r

omit [HasBinaryBiproducts D] in
/-- The section `splS` is a right inverse of the second map in degree `p`. -/
@[reassoc (attr := simp)]
theorem split_s_g (p : ℤ) : splS S σ p ≫ S.g.f p = 𝟙 _ := (σ p).s_g

omit [HasBinaryBiproducts D] in
/-- In degree `p`, `r ≫ f + g ≫ s` is the identity of the middle term. -/
theorem split_id (p : ℤ) : splR S σ p ≫ S.f.f p + S.g.f p ≫ splS S σ p = 𝟙 _ := (σ p).id

omit [HasBinaryBiproducts D] in
/-- In degree `p`, the section followed by the retraction is zero. -/
@[reassoc (attr := simp)]
theorem split_s_r (p : ℤ) : splS S σ p ≫ splR S σ p = 0 := (σ p).s_r

omit σ [HasBinaryBiproducts D] in
/-- In degree `p`, the composite of the two maps of the short complex is zero. -/
@[reassoc (attr := simp)]
theorem split_f_g (p : ℤ) : S.f.f p ≫ S.g.f p = 0 := by
  rw [← HomologicalComplex.comp_f, S.zero, HomologicalComplex.zero_f]

omit [HasBinaryBiproducts D] in
/-- A morphism into the middle term in degree `p` that is killed by the second map is fixed by
`r ≫ f`. -/
theorem split_retract {T : D} (p : ℤ) (X : T ⟶ S.X₂.X p) (hX : X ≫ S.g.f p = 0) :
    X ≫ splR S σ p ≫ S.f.f p = X := by
  calc X ≫ splR S σ p ≫ S.f.f p = X ≫ (splR S σ p ≫ S.f.f p + S.g.f p ≫ splS S σ p) := by
        rw [Preadditive.comp_add, ← Category.assoc X (S.g.f p), hX, zero_comp, add_zero]
    _ = X := by rw [split_id, Category.comp_id]

omit σ [HasBinaryBiproducts D] in
include hM in
/-- When the third term has zero differential, the differential of the middle term followed by
the second map is zero. -/
@[reassoc (attr := simp)]
theorem split_d_g (p q : ℤ) : S.X₂.d p q ≫ S.g.f q = 0 := by
  rw [← S.g.comm, hM, comp_zero]

omit [HasBinaryBiproducts D] in
include hM in
/-- When the third term has zero differential, `s ≫ d` into degree `p` is fixed by `r ≫ f`. -/
theorem split_retract_d (p : ℤ) :
    (splS S σ (p + -1) ≫ S.X₂.d (p + -1) p) ≫ splR S σ p ≫ S.f.f p =
      splS S σ (p + -1) ≫ S.X₂.d (p + -1) p :=
  split_retract S σ p _ (by rw [Category.assoc, split_d_g S hM, comp_zero])

/-- **The connecting morphism `M[-1] ⟶ K` of a degreewise split short exact sequence whose third
term has zero differential**: in degree `p` it is `r ∘ d_L ∘ s`. -/
noncomputable def splitConnecting : (S.X₃⟦(-1 : ℤ)⟧) ⟶ S.X₁ where
  f p := splS S σ (p + -1) ≫ S.X₂.d (p + -1) p ≫ splR S σ p
  comm' p q _ := by
    rw [shiftFunctor_obj_d', hM, smul_zero, zero_comp]
    calc (splS S σ (p + -1) ≫ S.X₂.d (p + -1) p ≫ splR S σ p) ≫ S.X₁.d p q
        = (splS S σ (p + -1) ≫ S.X₂.d (p + -1) p ≫ splR S σ p) ≫ S.X₁.d p q ≫ S.f.f q ≫
            splR S σ q := by
          rw [split_f_r, Category.comp_id]
      _ = (splS S σ (p + -1) ≫ S.X₂.d (p + -1) p) ≫ (splR S σ p ≫ S.f.f p) ≫ S.X₂.d p q ≫
            splR S σ q := by
          rw [← S.f.comm_assoc]
          simp only [Category.assoc]
      _ = (splS S σ (p + -1) ≫ S.X₂.d (p + -1) p) ≫ S.X₂.d p q ≫ splR S σ q := by
          rw [← Category.assoc _ (splR S σ p ≫ S.f.f p), split_retract_d S σ hM p]
      _ = 0 := by simp

/-- The degree `-1` cochain `M[-1] ⟶ L` given by the sections. -/
noncomputable def splitDescCochain : Cochain (S.X₃⟦(-1 : ℤ)⟧) S.X₂ (-1) :=
  Cochain.mk fun _ q hpq => (S.X₃.XIsoOfEq hpq).hom ≫ splS S σ q

omit [HasBinaryBiproducts D] in
/-- The components of `splitDescCochain` are the sections, up to `XIsoOfEq`. -/
theorem splitDescCochain_v (p q : ℤ) (hpq : p + -1 = q) :
    (splitDescCochain S σ).v p q hpq = (S.X₃.XIsoOfEq hpq).hom ≫ splS S σ q := rfl

omit [HasBinaryBiproducts D] in
/-- The differential of `splitDescCochain` is `splitConnecting ≫ S.f`. -/
theorem splitDesc_eq :
    δ (-1) 0 (splitDescCochain S σ) = Cochain.ofHom (splitConnecting S σ hM ≫ S.f) := by
  refine Cochain.ext₀ _ _ fun p => ?_
  rw [δ_v (-1) 0 (by omega) _ p p (add_zero p) (p + -1) (p + 1) (by omega) rfl, Cochain.ofHom_v,
    shiftFunctor_obj_d', hM, smul_zero, zero_comp, smul_zero, add_zero, splitDescCochain_v,
    HomologicalComplex.comp_f]
  change _ = (splS S σ (p + -1) ≫ S.X₂.d (p + -1) p ≫ splR S σ p) ≫ S.f.f p
  rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  simpa only [Category.assoc] using (split_retract_d S σ hM p).symm

omit σ in
/-- The degree `1` cocycle `L ⟶ M[-1]` given by the projection. -/
noncomputable def splitLiftCocycle : Cocycle S.X₂ (S.X₃⟦(-1 : ℤ)⟧) 1 :=
  Cocycle.mk (Cochain.mk fun p q hpq => S.g.f p ≫ (S.X₃.XIsoOfEq (by omega : p = q + -1)).hom) 2
    (by omega) (by
      refine Cochain.ext _ _ fun p q hpq => ?_
      rw [δ_v 1 2 (by omega) _ p q hpq (q - 1) (p + 1) (by omega) rfl, Cochain.mk_v,
        Cochain.mk_v, shiftFunctor_obj_d', hM, smul_zero, comp_zero, zero_add,
        ← Category.assoc, split_d_g S hM, zero_comp, smul_zero, Cochain.zero_v])

omit σ [HasBinaryBiproducts D] in
/-- The components of `splitLiftCocycle` are the second map, up to `XIsoOfEq`. -/
theorem splitLiftCocycle_v (p q : ℤ) (hpq : p + 1 = q) :
    (splitLiftCocycle S hM).1.v p q hpq =
      S.g.f p ≫ (S.X₃.XIsoOfEq (by omega : p = q + -1)).hom :=
  rfl

omit [HasBinaryBiproducts D] in
/-- The differential of the cochain of retractions plus the composite of `splitLiftCocycle` with
`splitConnecting` is zero. -/
theorem splitLift_eq :
    δ 0 1 (Cochain.ofHoms fun p => splR S σ p) + (splitLiftCocycle S hM).1.comp
      (Cochain.ofHom (splitConnecting S σ hM)) (add_zero 1) = 0 := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : q = p + 1 := by omega
  rw [Cochain.add_v, δ_v 0 1 (by omega) _ p (p + 1) hpq p (p + 1) (by omega) rfl,
    Cochain.ofHoms_v, Cochain.ofHoms_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    splitLiftCocycle_v, Cochain.zero_v]
  change splR S σ p ≫ S.X₁.d p (p + 1) + (1 : ℤ).negOnePow • S.X₂.d p (p + 1) ≫ splR S σ (p + 1) +
    (S.g.f p ≫ (S.X₃.XIsoOfEq _).hom) ≫ splS S σ (p + 1 + -1) ≫ S.X₂.d (p + 1 + -1) (p + 1) ≫
      splR S σ (p + 1) = 0
  have hnat : ∀ {x y : ℤ} (h : x = y),
      (S.X₃.XIsoOfEq h).hom ≫ splS S σ y ≫ S.X₂.d y (p + 1) = splS S σ x ≫ S.X₂.d x (p + 1) := by
    rintro x y rfl
    simp
  rw [Category.assoc, reassoc_of% (hnat _), Int.negOnePow_one, Units.neg_smul, one_smul]
  have key : ∀ (Z : S.X₂.X p ⟶ S.X₁.X (p + 1)),
      S.f.f p ≫ Z = 0 → splS S σ p ≫ Z = 0 → Z = 0 := by
    intro Z h1 h2
    rw [← Category.id_comp Z, ← split_id S σ p, Preadditive.add_comp, Category.assoc,
      Category.assoc, h1, h2, comp_zero, comp_zero, add_zero]
  refine key _ ?_ ?_
  · rw [Preadditive.comp_add, Preadditive.comp_add, Preadditive.comp_neg,
      split_f_r_assoc, S.f.comm_assoc, split_f_r, Category.comp_id, split_f_g_assoc,
      zero_comp, add_zero, add_neg_cancel]
  · rw [Preadditive.comp_add, Preadditive.comp_add, Preadditive.comp_neg,
      reassoc_of% (split_s_r S σ p), zero_comp, zero_add, reassoc_of% (split_s_g S σ p),
      neg_add_cancel]

/-- The comparison `L ⟶ mappingCone (splitConnecting …)`. -/
noncomputable def splitConeLift : S.X₂ ⟶ mappingCone (splitConnecting S σ hM) :=
  mappingCone.lift _ (splitLiftCocycle S hM) (Cochain.ofHoms fun p => splR S σ p)
    (splitLift_eq S σ hM)

/-- The comparison `mappingCone (splitConnecting …) ⟶ L`. -/
noncomputable def splitConeDesc : mappingCone (splitConnecting S σ hM) ⟶ S.X₂ :=
  mappingCone.desc _ (splitDescCochain S σ) S.f (splitDesc_eq S σ hM)

/-- **A degreewise split short exact sequence whose third term has zero differential has its
middle term the mapping cone of its connecting morphism.** -/
noncomputable def splitConeIso : mappingCone (splitConnecting S σ hM) ≅ S.X₂ where
  hom := splitConeDesc S σ hM
  inv := splitConeLift S σ hM
  hom_inv_id := by
    ext n
    refine mappingCone.ext_from _ (n + 1) n rfl ?_ ?_
    · simp only [splitConeDesc, splitConeLift, HomologicalComplex.comp_f,
        mappingCone.inl_v_desc_f_assoc, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
        HomologicalComplex.id_f, Category.comp_id, splitDescCochain_v, splitLiftCocycle_v,
        Cochain.ofHoms_v, Preadditive.comp_add, Category.assoc, split_s_g_assoc,
        split_s_r_assoc, zero_comp, comp_zero, add_zero,
        HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    · simp only [splitConeDesc, splitConeLift, HomologicalComplex.comp_f,
        mappingCone.inr_f_desc_f_assoc, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
        HomologicalComplex.id_f, Category.comp_id, splitLiftCocycle_v, Cochain.ofHoms_v,
        Preadditive.comp_add, Category.assoc, split_f_g_assoc, zero_comp, zero_add,
        split_f_r_assoc]
  inv_hom_id := by
    ext n
    rw [splitConeDesc, splitConeLift, HomologicalComplex.comp_f,
      mappingCone.lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl, splitLiftCocycle_v,
      splitDescCochain_v, Cochain.ofHoms_v, HomologicalComplex.id_f, Category.assoc,
      HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, add_comm]
    exact split_id S σ n

end Split

end CochainComplex

namespace SheafOfModules

open CochainComplex DifferentialGradedModule

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- The shift down by one of a free complex with zero differential is the free complex on the
shifted family. -/
noncomputable def freeOnPresheavesComplexShiftIso (P : ℤ → (Y.Cᵒᵖ ⥤ Type w)) :
    (freeOnPresheavesComplex Y.O P)⟦(-1 : ℤ)⟧ ≅
      freeOnPresheavesComplex Y.O (fun p => P (p + -1)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun p q _ => by
    rw [shiftFunctor_obj_d', freeOnPresheavesComplex_d, freeOnPresheavesComplex_d, smul_zero,
      zero_comp, comp_zero])

/-- **A degreewise split extension of a free complex with zero differential by a good module is
good.** The middle term is the cone of the connecting morphism `M[-1] ⟶ K`, and the cone of a
morphism of good modules is good; `M[-1]` is again a free complex with zero differential. -/
theorem isGoodToposBaseChange_of_split_freeOnPresheaves
    {K L : CochainComplex (SheafOfModules.{w} (toRingCat Y.J Y.O)) ℤ}
    (P : ℤ → (Y.Cᵒᵖ ⥤ Type w)) (f : K ⟶ L) (g : L ⟶ freeOnPresheavesComplex Y.O P)
    (zero : f ≫ g = 0)
    (σ : ∀ n, ((ShortComplex.mk f g zero).map (HomologicalComplex.eval _ _ n)).Splitting)
    (hK : IsGoodToposBaseChange.{w, v₁, u₁} (ofComplex K)) :
    IsGoodToposBaseChange.{w, v₁, u₁} (ofComplex L) := by
  have hM : ∀ p q, (freeOnPresheavesComplex Y.O P).d p q = 0 := fun _ _ => rfl
  have hM' : IsGoodToposBaseChange.{w, v₁, u₁}
      (ofComplex ((freeOnPresheavesComplex Y.O P)⟦(-1 : ℤ)⟧)) :=
    isGoodToposBaseChange_of_iso (isoMk (freeOnPresheavesComplexShiftIso P).symm)
      (freeOnPresheaves_isGoodToposBaseChange (fun p => P (p + -1)))
  let φ : ofComplex ((freeOnPresheavesComplex Y.O P)⟦(-1 : ℤ)⟧) ⟶ ofComplex K :=
    homMk (splitConnecting (ShortComplex.mk f g zero) σ hM)
  refine isGoodToposBaseChange_of_iso (isoMk ?_) (cone_isGoodToposBaseChange φ hM' hK)
  exact eqToIso (conePackage φ).cone_complex ≪≫ splitConeIso (ShortComplex.mk f g zero) σ hM

end SheafOfModules

end

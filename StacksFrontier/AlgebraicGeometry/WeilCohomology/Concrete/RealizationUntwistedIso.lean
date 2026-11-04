module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMotiveTate
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationNameAction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealizationUnique
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# A realization restricted to correspondences of degree zero

Let `G : M_k ⥤ graded F-vector spaces` be a realization (side (2) of Stacks 0FHM) whose data
`H^*(X) = G(h(X))` (Stacks 0FHK) satisfy (A), (B), (C), and suppose that `G` acts on
correspondences of degree zero by `c ↦ (a ↦ pr₂,*(γ(c) ∪ pr₁^*a))`. Then the restriction of `G`
along `X ↦ (X, 1, 0)` is monoidally isomorphic to the realization of correspondences of degree
zero of Stacks 0FHL attached to these data, through `H^n(X) = G(h(X))^n`.

## Main definitions

* `Stacks.WeilCohomology.WeilRealization.untwistedIso`: the isomorphism
  `untwistedOfObj ⋙ G ≅ corrFunctor`, monoidal by
  `Stacks.WeilCohomology.WeilRealization.untwistedIso_isMonoidal`.

## Main results

* `Stacks.WeilCohomology.WeilRealization.rel_toWeilRealization_of_nat`: such a `G` is isomorphic
  to the realization `WeilDataAxioms.toWeilRealization` of its data (the round trip of 0FHM).

## Implementation notes

The motives `(X, 1, 0)` occur in two spellings, `untwistedOfObj.obj X` and
`TwistedKaroubi.ofObj (𝐎 X)`; comparing morphism types across them makes the elaborator unfold
the category of correspondences. The tensorator and unit of `untwistedOfObj` are therefore
compared with the Künneth morphism and the unit of `h(Spec k)` through generic transport lemmas
(`TwistedKaroubi.map_untwistedOfObj_μ`, `TwistedKaroubi.map_untwistedOfObj_ε`) whose object
equalities are closed by `rfl`, and underlying correspondences are compared up to `HEq`.

## References

* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CategoryTheory.GradedCategory Stacks.Chow

universe u w

namespace CategoryTheory.GradedObject.Monoidal

variable {R : Type w} [CommRing R]

/-- Two morphisms out of the unit `𝟙 = R[0]` of graded `R`-modules agree once they agree on `1`. -/
theorem tensorUnit_hom_ext {V : GradedObject ℤ (ModuleCat.{w} R)}
    {f g : 𝟙_ (GradedObject ℤ (ModuleCat.{w} R)) ⟶ V}
    (h : (f 0).hom (unitOne (R := R)) = (g 0).hom (unitOne (R := R))) : f = g := by
  funext n
  by_cases hn : n = 0
  · subst hn
    refine ModuleCat.hom_ext (LinearMap.ext fun u ↦ ?_)
    have hu : u = ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} R)).hom.hom u : R) • unitOne := by
      rw [unitOne, ← map_smul, smul_eq_mul, mul_one]
      exact (congrArg (fun φ ↦ φ.hom u)
        (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} R)).hom_inv_id).symm
    rw [hu, map_smul, map_smul, h]
  · exact (isInitialTensorUnitApply (I := ℤ) (C := ModuleCat.{w} R) n hn).hom_ext _ _

end CategoryTheory.GradedObject.Monoidal

namespace CategoryTheory.GradedCategory.TwistedKaroubi

variable {C : Type*} [Category C] [Preadditive C] [GradedCategory ℚ C]
  [MonoidalCategory C] [IsGradedMonoidal ℚ C] [SymmetricCategory C] [IsGradedBraided ℚ C]

omit [MonoidalCategory C] [IsGradedMonoidal ℚ C] [SymmetricCategory C] [IsGradedBraided ℚ C] in
/-- `J : X ↦ (X, 1, 0)` sends a morphism `f` of degree zero to `f : (X, 1, 0) ⟶ (Y, 1, 0)`. -/
theorem untwistedOfObj_map {X Y : DegreeZero ℚ C} (f : X ⟶ Y) :
    (untwistedOfObj C).map f = ofObjHom (DegreeZero.val f) (DegreeZero.val_mem f) :=
  hom_ext rfl

/-- The tensorator of `J : X ↦ (X, 1, 0)` is the identity of `X ⊗ Y`. -/
theorem untwistedOfObj_μ_val (X Y : DegreeZero ℚ C) :
    (Functor.LaxMonoidal.μ (untwistedOfObj C) X Y).val = 𝟙 (X.toC ⊗ Y.toC) := by
  rw [Functor.LaxMonoidal.comp_μ, comp_val, untwisted_μ_val, untwisted_map_val,
    Idempotents.toKaroubi_μ_f]
  exact (Category.comp_id _).trans (MonoidalCategory.id_tensorHom_id _ _)

/-- The unit of `J : X ↦ (X, 1, 0)` is the identity of `𝟙`. -/
theorem untwistedOfObj_ε_val : (Functor.LaxMonoidal.ε (untwistedOfObj C)).val = 𝟙 (𝟙_ C) := by
  rw [Functor.LaxMonoidal.comp_ε, comp_val, untwisted_ε_val, untwisted_map_val,
    Idempotents.toKaroubi_ε_f]
  exact Category.comp_id _

variable {D : Type*} [Category D] (G : TwistedKaroubi ℚ C ⥤ D)

/-- A functor on the tensorator of `J`, transported to any morphism with the same underlying
morphism `𝟙` between other spellings of the same objects. -/
theorem map_untwistedOfObj_μ {X Y : DegreeZero ℚ C} {M N : TwistedKaroubi ℚ C} (g : M ⟶ N)
    (hM : (untwistedOfObj C).obj X ⊗ (untwistedOfObj C).obj Y = M)
    (hN : (untwistedOfObj C).obj (X ⊗ Y) = N)
    (hg : HEq g.val (𝟙 (X.toC ⊗ Y.toC))) :
    G.map (Functor.LaxMonoidal.μ (untwistedOfObj C) X Y) =
      eqToHom (congrArg G.obj hM) ≫ G.map g ≫ eqToHom (congrArg G.obj hN).symm := by
  subst hM hN
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  congr 1
  exact hom_ext ((untwistedOfObj_μ_val X Y).trans (eq_of_heq hg).symm)

/-- A functor on the unit of `J`, transported to any morphism with underlying morphism `𝟙`
between other spellings of the same objects. -/
theorem map_untwistedOfObj_ε {M N : TwistedKaroubi ℚ C} (g : M ⟶ N)
    (hM : 𝟙_ (TwistedKaroubi ℚ C) = M)
    (hN : (untwistedOfObj C).obj (𝟙_ (DegreeZero ℚ C)) = N)
    (hg : HEq g.val (𝟙 (𝟙_ C))) :
    G.map (Functor.LaxMonoidal.ε (untwistedOfObj C)) =
      eqToHom (congrArg G.obj hM) ≫ G.map g ≫ eqToHom (congrArg G.obj hN).symm := by
  subst hM hN
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  congr 1
  exact hom_ext (untwistedOfObj_ε_val.trans (eq_of_heq hg).symm)

end CategoryTheory.GradedCategory.TwistedKaroubi

namespace Stacks.WeilCohomology.WeilRealization

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (G : WeilRealization k F)
  (hA : G.toWeilData.PoincareDuality) (hB : G.toWeilData.Kunneth)
  (hC : G.toWeilData.CycleClassAxiom hA.perfectPairing)
  (hnat : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory}
      (f : WeilData.dz X ⟶ WeilData.dz Y) (n : ℤ),
    G.corrMapG f n = WeilData.corrHomMap hA hB hC f n)

/-- **`G(h(X))^n = H^n(X)`**, the component of `untwistedIso`. -/
def untwistedIsoApp (X : DegreeZero ℚ (CorrespondenceCategory k)) :
    (TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G.functor).obj X ≅
      (WeilData.corrFunctor hA hB hC).obj X :=
  GradedObject.isoMk _ _ fun n ↦ ((G.cohAlg X.as).gradeEquiv n).symm.toModuleIso

include hnat in
/-- **The restriction of `G` to correspondences of degree zero is the realization of 0FHL**,
through `H^n(X) = G(h(X))^n`. -/
def untwistedIso :
    TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G.functor ≅
      WeilData.corrFunctor hA hB hC :=
  NatIso.ofComponents (G.untwistedIsoApp hA hB hC) fun {X Y} f ↦ by
    funext n
    ext v
    have h := LinearMap.congr_fun (hnat (X := X.as) (Y := Y.as) f n)
      (((G.cohAlg X.as).gradeEquiv n).symm v)
    have hv : (G.cohAlg X.as).gradeEquiv n (((G.cohAlg X.as).gradeEquiv n).symm v) = v :=
      LinearEquiv.apply_symm_apply _ _
    simp only [corrMapG, LinearMap.comp_apply, LinearEquiv.coe_coe] at h
    rw [hv] at h
    refine Eq.trans ?_ h
    rw [Functor.comp_map, TwistedKaroubi.untwistedOfObj_map]
    rfl

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

section Kunneth

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

attribute [local instance] braidedTK monoidalTK

/-- The Künneth morphism `κ : h(X) ⊗ h(Y) ⟶ h(X × Y)` is the identity correspondence of
`X × Y`. -/
theorem kunnethMot_val (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    HEq (kunnethMot X Y).val (𝟙 (𝐎 X ⊗ 𝐎 Y)) := by
  have h := CorrespondenceCategory.tensorHom_graphHom_tensorFst_tensorSnd_mul X Y
  rw [TwistedKaroubi.comp_val, TwistedKaroubi.tensorHom_val, ChowMotiveCat.motMap_val,
    ChowMotiveCat.motMap_val, ChowMotiveCat.mul_motive_val]
  generalize (graphHom (CorrespondenceCategory.tensorFst X Y) : 𝐎 X ⟶ 𝐎 (X ⊗ Y)) = f at h ⊢
  generalize (graphHom (CorrespondenceCategory.tensorSnd X Y) : 𝐎 Y ⟶ 𝐎 (X ⊗ Y)) = g at h ⊢
  generalize MonObj.mul (X := 𝐎 (X ⊗ Y)) = m at h ⊢
  exact heq_of_eq h

/-- The unit of the monoid `h(Spec k)` is the identity correspondence of `Spec k`. -/
theorem one_motive_point_val :
    HEq (MonObj.one
        (X := TwistedKaroubi.ofObj (R := ℚ)
          (𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))))).val
      (𝟙 (𝟙_ (CorrespondenceCategory k))) := by
  have h : (graphHom (toUnit (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) :
      𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) ⟶
        𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) =
        𝟙 (𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) := by
    rw [toUnit_unique (toUnit _) (𝟙 _)]
    exact graphHom_id _
  rw [ChowMotiveCat.one_motive_val, CorrespondenceCategory.one_eq_graphHom]
  generalize (graphHom (toUnit (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) :
      𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) ⟶
        𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) = f at h ⊢
  exact (heq_of_eq h).trans (congr_arg_heq (fun a ↦ 𝟙 a)
    (rfl : 𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) = 𝟙_ (CorrespondenceCategory k)))

/-- `κ` has underlying morphism `𝟙 (X ⊗ Y)`, in the spelling of `J : X ↦ (X, 1, 0)`. -/
theorem kunnethMot_val_heq (X Y : DegreeZero ℚ (CorrespondenceCategory k)) :
    HEq (kunnethMot X.as Y.as).val (𝟙 (X.toC ⊗ Y.toC)) :=
  (kunnethMot_val X.as Y.as).trans (congr_arg_heq (fun a ↦ 𝟙 a)
    (rfl : 𝐎 X.as ⊗ 𝐎 Y.as = X.toC ⊗ Y.toC))

end Kunneth

section Monoidal

attribute [local instance] WeilData.corrFunctorBraided

open GradedObject.Monoidal in
include hnat in
/-- `untwistedIso` is compatible with the tensorators: `G`'s product of `a ∈ G(h(X))^p` and
`b ∈ G(h(Y))^q`, pushed to `G(h(X × Y))`, is `pr₁^*a ∪ pr₂^*b`. -/
theorem untwistedIso_tensor (X Y : DegreeZero ℚ (CorrespondenceCategory k)) :
    Functor.LaxMonoidal.μ (TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G.functor)
        X Y ≫ (G.untwistedIso hA hB hC hnat).hom.app (X ⊗ Y) =
      ((G.untwistedIso hA hB hC hnat).hom.app X ⊗ₘ (G.untwistedIso hA hB hC hnat).hom.app Y) ≫
        Functor.LaxMonoidal.μ (WeilData.corrFunctor hA hB hC) X Y := by
  funext n
  refine tensorObj_hom_ext fun p q hpq x y ↦ ?_
  subst hpq
  simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [tensorHom_apply_ιTensorObj]
  apply Subtype.ext
  refine Eq.trans ?_ (congrArg Subtype.val (WeilData.corrFunctorμIso_hom_apply hA hB hC X Y p q
    (p + q) rfl ((G.untwistedIso hA hB hC hnat).hom.app X p x)
    ((G.untwistedIso hA hB hC hnat).hom.app Y q y))).symm
  have hmap := TwistedKaroubi.map_untwistedOfObj_μ G.functor
    (X := (X : DegreeZero ℚ (canonicalCorrespondenceCompositionData k).Obj))
    (Y := (Y : DegreeZero ℚ (canonicalCorrespondenceCompositionData k).Obj))
    (kunnethMot X.as Y.as) rfl rfl (kunnethMot_val_heq X Y)
  rw [Functor.LaxMonoidal.comp_μ, hmap]
  refine (ExternallyGradedAlgebra.gradeEquiv_symm_apply_coe _ _ _).trans ?_
  refine Eq.trans ?_ ((of_map_kunnethMot_gradedMul G X.as Y.as p q x y).trans ?_)
  · rfl
  · congr 2

include hnat in
/-- `untwistedIso` is compatible with the units: the unit of `G` is `1 ∈ H^0(Spec k)`. -/
theorem untwistedIso_unit :
    Functor.LaxMonoidal.ε (TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G.functor) ≫
        (G.untwistedIso hA hB hC hnat).hom.app (𝟙_ _) =
      Functor.LaxMonoidal.ε (WeilData.corrFunctor hA hB hC) := by
  refine GradedObject.Monoidal.tensorUnit_hom_ext ?_
  simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  apply Subtype.ext
  refine Eq.trans ?_ (WeilData.corrFunctorεIso_hom_unitOne hA hB hC).symm
  have hmap := TwistedKaroubi.map_untwistedOfObj_ε G.functor
    (MonObj.one (X := TwistedKaroubi.ofObj (R := ℚ)
      (𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)))))
    rfl rfl one_motive_point_val
  rw [Functor.LaxMonoidal.comp_ε, hmap]
  refine (ExternallyGradedAlgebra.gradeEquiv_symm_apply_coe _ _ _).trans ?_
  exact (ExternallyGradedAlgebra.one_eq_of _).symm

include hnat in
/-- **The isomorphism `untwistedIso` is monoidal**: `G`'s product `a · b` on `G(h(X)) ⊗ G(h(Y))`,
pushed to `G(h(X × Y))`, is the Künneth map `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, and the unit of `G` is
`F = H^*(Spec k)`. -/
instance untwistedIso_isMonoidal : NatTrans.IsMonoidal (G.untwistedIso hA hB hC hnat).hom where
  unit := G.untwistedIso_unit hA hB hC hnat
  tensor X Y := G.untwistedIso_tensor hA hB hC hnat X Y

include hnat in
/-- **The round trip of Stacks 0FHM**: if `G` acts on correspondences of degree zero as the
realization of its data (D0)–(D3), then `G` is isomorphic to the realization of Stacks 0FHL
attached to these data. -/
theorem rel_toWeilRealization_of_nat :
    (isoSetoid k F).r G (WeilDataAxioms.toWeilRealization ⟨G.toWeilData, hA, hB, hC⟩) :=
  rel_of_untwisted _ _ _ (G.untwistedIso hA hB hC hnat) (WeilDataAxioms.toWeilRealizationIso _)

end Monoidal

end Stacks.WeilCohomology.WeilRealization

end

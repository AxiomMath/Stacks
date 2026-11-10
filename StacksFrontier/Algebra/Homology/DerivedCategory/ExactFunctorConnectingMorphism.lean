module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactMapDerivedPlusIsoApp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.Homology.HomComplex.TargetShiftDegree

/-!
# Exact functors and the connecting morphisms of homology sequences

Let `E : 𝒜 ⥤ ℬ` be an exact functor between abelian categories. It acts degreewise on derived
categories, and it commutes with homology: `H ⁿ(E K) ≅ E(H ⁿ K)`. This file proves that this
comparison is compatible with the connecting morphisms of the long exact homology sequences of
triangles, and that the comparison `E(X)[0] ≅ RE(X[0])` with the right derived functor carries
the triangle of a short exact sequence to the image of that triangle.

Concretely, for a triangle `T` the connecting morphism `H ⁿ(T₃) ⟶ H ⁿ⁺¹(T₁)` is the image under
homology of the third morphism `T₃ ⟶ T₁⟦1⟧`, followed by the shift isomorphism
`H ⁿ(T₁⟦1⟧) ≅ H ⁿ⁺¹(T₁)`. The content is therefore that the comparison `E ∘ H ≅ H ∘ E`
commutes with these shift isomorphisms, the commutation `E(K⟦1⟧) ≅ E(K)⟦1⟧` being read on the
left; on cochain complexes this is the statement that `E` commutes with the identification of
the homology of a shifted complex, whose differentials carry a sign, and `E` is additive.

On the bounded below derived category the right derived functor `RE` is identified with the
degreewise action by `exactMapDerivedCategoryPlusIso`; this
identification is compatible with the shift, being the descent along the localization of the
unit of `RE` and of the degreewise comparison, both compatible with the shift.

## Main results

* `derivedHomologyIso_shiftIso` — the comparison of homology on the
  unbounded derived category commutes with the shift isomorphisms of homology.
* `derivedHomologyIso_homologySequenceδ` — the same comparison commutes
  with the connecting morphisms of the homology sequence of a triangle.
* `natTransCommShift_exactMapDerivedCategoryPlusIso` — the identification
  of `RE` with the degreewise action is compatible with the shift.
* `exactRightDerivedPlusHomologyIso_homologySequenceδ` — **an exact
  functor commutes with the connecting morphisms** on the bounded below derived category: read
  through `exactRightDerivedPlusHomologyIso`, the connecting morphism of
  the image of a triangle under `RE` is `E` of the connecting morphism of the triangle.
* `exactSingleFunctorRightDerivedPlusIso_singleδPlus` — the comparison
  `E(X)[0] ≅ RE(X[0])` is compatible with the connecting morphisms of the triangle of a short
  exact sequence and of its image under `RE`.

## Implementation notes

The objects of the various derived categories in play are equal only after unfolding the
definitions of lifts through full subcategories, of shift sequences induced along localizations
and of composite functors, so a rewrite in the concrete statements frequently produces a motive
that is not type-correct at reducible transparency. The rearrangements are therefore stated as
lemmas about morphisms in an arbitrary category and applied by `exact`, which compares the
concrete objects at default transparency.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

omit [PreservesFiniteLimits E] [PreservesFiniteColimits E] in
private theorem map_neg_eqToHom {X Y : A} (p : X = Y) (r : E.obj X = E.obj Y) :
    E.map (-eqToHom p) = 𝟙 _ ≫ (-eqToHom r) := by
  subst p
  simp

omit [Abelian A] [Abelian B] [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E] in
private theorem map_eqToHom' {X Y : A} (p : X = Y) (r : E.obj X = E.obj Y) :
    E.map (eqToHom p) = 𝟙 _ ≫ eqToHom r := by
  subst p
  simp

omit [PreservesFiniteLimits E] [PreservesFiniteColimits E] in
open HomologicalComplex in
/-- The image under `E` of the isomorphism `CochainComplex.shiftShortComplexFunctorIso` at a
complex `L` is that isomorphism at `E(L)`, composed with the commutation of `E` with the shift by
`1`. -/
theorem mapShortComplex_shiftShortComplexFunctorIso (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁)
    (L : CochainComplex A ℤ) :
    E.mapShortComplex.map ((CochainComplex.shiftShortComplexFunctorIso A 1 n₀ n₁ h).hom.app L) =
      (shortComplexFunctor B (.up ℤ) n₀).map
          (((E.mapHomologicalComplex (.up ℤ)).commShiftIso (1:ℤ)).hom.app L) ≫
        (CochainComplex.shiftShortComplexFunctorIso B 1 n₀ n₁ h).hom.app
          ((E.mapHomologicalComplex _).obj L) := by
  ext
  · simp only [Functor.comp_obj, Functor.mapShortComplex_obj, ShortComplex.map_X₁,
      Functor.mapShortComplex_map_τ₁, CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₁,
      Int.negOnePow_one, XIsoOfEq, eqToIso.hom, Units.smul_def, Units.val_neg, Units.val_one,
      Int.reduceNeg, neg_smul, one_smul, ShortComplex.comp_τ₁, shortComplexFunctor_map_τ₁,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Functor.mapHomologicalComplex_obj_X,
      CochainComplex.shiftFunctor_obj_X']
    exact map_neg_eqToHom E _ _
  · simp only [Functor.comp_obj, Functor.mapShortComplex_obj, ShortComplex.map_X₂,
      Functor.mapShortComplex_map_τ₂, CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₂,
      XIsoOfEq, eqToIso.hom, ShortComplex.comp_τ₂, shortComplexFunctor_map_τ₂,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Functor.mapHomologicalComplex_obj_X,
      CochainComplex.shiftFunctor_obj_X']
    exact map_eqToHom' E _ _
  · simp only [Functor.comp_obj, Functor.mapShortComplex_obj, ShortComplex.map_X₃,
      Functor.mapShortComplex_map_τ₃, CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₃,
      Int.negOnePow_one, XIsoOfEq, eqToIso.hom, Units.smul_def, Units.val_neg, Units.val_one,
      Int.reduceNeg, neg_smul, one_smul, ShortComplex.comp_τ₃, shortComplexFunctor_map_τ₃,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Functor.mapHomologicalComplex_obj_X,
      CochainComplex.shiftFunctor_obj_X']
    exact map_neg_eqToHom E _ _

open HomologicalComplex in
/-- The comparison `complexHomologyIso` of `E` with homology of cochain complexes commutes with
the shift isomorphisms `(homologyFunctor _ _ 0).shiftIso` relating the homology of `L⟦1⟧` in
degree `n₀` to the homology of `L` in degree `n₁ = 1 + n₀`. -/
theorem complexHomologyIso_shiftIso (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) (L : CochainComplex A ℤ) :
    (complexHomologyIso E (.up ℤ) n₀).hom.app (L⟦(1:ℤ)⟧) ≫
        E.map (((homologyFunctor A (.up ℤ) 0).shiftIso 1 n₀ n₁ h).hom.app L) =
      (homologyFunctor B (.up ℤ) n₀).map
          (((E.mapHomologicalComplex (.up ℤ)).commShiftIso (1:ℤ)).hom.app L) ≫
        ((homologyFunctor B (.up ℤ) 0).shiftIso 1 n₀ n₁ h).hom.app
          ((E.mapHomologicalComplex _).obj L) ≫
        (complexHomologyIso E (.up ℤ) n₁).hom.app L := by
  rw [complexHomologyIso_hom_app, complexHomologyIso_hom_app]
  have h₁ : ((homologyFunctor A (.up ℤ) 0).shiftIso 1 n₀ n₁ h).hom.app L =
      ShortComplex.homologyMap
        ((CochainComplex.shiftShortComplexFunctorIso A 1 n₀ n₁ h).hom.app L) :=
    CochainComplex.ShiftSequence.shiftIso_hom_app _ _ _ _ _
  have h₂ : ((homologyFunctor B (.up ℤ) 0).shiftIso 1 n₀ n₁ h).hom.app
        ((E.mapHomologicalComplex _).obj L) =
      ShortComplex.homologyMap ((CochainComplex.shiftShortComplexFunctorIso B 1 n₀ n₁ h).hom.app
        ((E.mapHomologicalComplex _).obj L)) :=
    CochainComplex.ShiftSequence.shiftIso_hom_app _ _ _ _ _
  rw [h₁, h₂]
  refine (ShortComplex.mapHomologyIso_hom_naturality
    ((CochainComplex.shiftShortComplexFunctorIso A 1 n₀ n₁ h).hom.app L) E).symm.trans ?_
  rw [mapShortComplex_shiftShortComplexFunctorIso]
  exact (congrArg (· ≫ _) (ShortComplex.homologyMap_comp _ _)).trans (Category.assoc _ _ _)

section Derived

variable [HasDerivedCategory A] [HasDerivedCategory B]

open DerivedCategory

private theorem id_chain₄ {𝒞 : Type*} [Category* 𝒞] {X₀ X₁ X₂ X₃ X₄ : 𝒞}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) :
    𝟙 _ ≫ a ≫ 𝟙 _ ≫ b ≫ 𝟙 _ ≫ c ≫ d = a ≫ b ≫ c ≫ d := by
  simp

/-- The shift isomorphism of homology on the derived category at the image of a complex, solved
for itself in `CochainComplex.HomComplex.shiftIso_hom_app_Q_obj`. -/
private theorem homologyFunctor_shiftIso_hom_app_Q {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) (M : CochainComplex C ℤ) :
    ((homologyFunctor C 0).shiftIso 1 n₀ n₁ h).hom.app (Q.obj M) =
      (homologyFunctor C n₀).map ((Q.commShiftIso (1 : ℤ)).inv.app M) ≫
        (homologyFunctorFactors C n₀).hom.app (M⟦(1 : ℤ)⟧) ≫
        ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso 1 n₀ n₁ h).hom.app M ≫
        (homologyFunctorFactors C n₁).inv.app M := by
  refine Eq.trans ?_ (congrArg ((homologyFunctor C n₀).map ((Q.commShiftIso (1 : ℤ)).inv.app M) ≫ ·)
    (CochainComplex.HomComplex.shiftIso_hom_app_Q_obj M 1 n₀ n₁ h))
  exact (Iso.inv_hom_id_map_assoc ((Q.commShiftIso (1 : ℤ)).app M) (homologyFunctor C n₀) _).symm

private theorem map_comp₄ {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟)
    {X₀ X₁ X₂ X₃ X₄ : 𝒞} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) :
    F.map (a ≫ b ≫ c ≫ d) = F.map a ≫ F.map b ≫ F.map c ≫ F.map d := by
  simp

/-- The rearrangement behind `derivedHomologyIso_shiftIso`, on variables. -/
private theorem shift_chain {𝒳 : Type*} [Category* 𝒳]
    {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ o₁₁ o₁₂ o₁₃ o₁₄ o₁₅ o₁₇ : 𝒳}
    {lhs : o₁ ⟶ o₅} {a₁ : o₁ ⟶ o₂} {a₂ : o₂ ⟶ o₃} {a₃ : o₃ ⟶ o₄} {a₄ : o₄ ⟶ o₅}
    {dinv : o₁ ⟶ o₆} {Hη : o₆ ⟶ o₇} {sDE : o₇ ⟶ o₈} {d₁ : o₈ ⟶ o₅}
    {b₁ : o₆ ⟶ o₉} {Hξh : o₉ ⟶ o₆} {dinvQ : o₂ ⟶ o₉}
    {Hφ : o₈ ⟶ o₁₀} {fBE : o₁₀ ⟶ o₁₁} {c₁ : o₁₁ ⟶ o₄}
    {HφS : o₇ ⟶ o₁₂} {sDQ : o₁₂ ⟶ o₁₀} {Hξ'inv : o₁₂ ⟶ o₁₃} {fB0S : o₁₃ ⟶ o₁₄}
    {sCB : o₁₄ ⟶ o₁₁} {fBEinv : o₁₁ ⟶ o₁₀}
    {Hφ₁ : o₉ ⟶ o₁₅} {HQκ : o₁₅ ⟶ o₁₃} {Hξ' : o₁₃ ⟶ o₁₂}
    {fBE₀ : o₁₅ ⟶ o₁₇} {HCκ : o₁₇ ⟶ o₁₄} {c₀ : o₁₇ ⟶ o₃} {a₂' : o₃ ⟶ o₂} {dQ₀ : o₉ ⟶ o₂}
    (s₁ : lhs = a₁ ≫ a₂ ≫ a₃ ≫ a₄)
    (s₂ : dinv ≫ b₁ = a₁ ≫ dinvQ) (hb : b₁ ≫ Hξh = 𝟙 _)
    (s₃ : d₁ = Hφ ≫ fBE ≫ c₁ ≫ a₄) (s₃' : dQ₀ = Hφ₁ ≫ fBE₀ ≫ c₀ ≫ a₂')
    (hd : dinvQ ≫ dQ₀ = 𝟙 _)
    (s₄ : Hξh ≫ Hη ≫ HφS = Hφ₁ ≫ HQκ ≫ Hξ')
    (s₅ : HφS ≫ sDQ = sDE ≫ Hφ)
    (s₆ : sDQ = Hξ'inv ≫ fB0S ≫ sCB ≫ fBEinv)
    (s₇ : c₀ ≫ a₃ = HCκ ≫ sCB ≫ c₁)
    (s₈ : HQκ ≫ fB0S = fBE₀ ≫ HCκ)
    (s₉ : fBEinv ≫ fBE = 𝟙 _) (s₁₀ : Hξ' ≫ Hξ'inv = 𝟙 _) (s₁₁ : a₂' ≫ a₂ = 𝟙 _) :
    lhs = dinv ≫ Hη ≫ sDE ≫ d₁ := by
  have e₁ : sDE ≫ d₁ = HφS ≫ Hξ'inv ≫ fB0S ≫ sCB ≫ c₁ ≫ a₄ := by
    rw [s₃, ← Category.assoc, ← s₅, Category.assoc, s₆]
    simp only [Category.assoc]
    rw [reassoc_of% s₉]
  have e₂ : dinv ≫ Hη = a₁ ≫ dinvQ ≫ Hξh ≫ Hη := by
    rw [← reassoc_of% s₂, reassoc_of% hb]
  have e₃ : Hφ₁ ≫ fBE₀ ≫ c₀ ≫ a₃ ≫ a₄ = dQ₀ ≫ a₂ ≫ a₃ ≫ a₄ := by
    rw [s₃']
    simp only [Category.assoc]
    rw [reassoc_of% s₁₁]
  rw [s₁, e₁, reassoc_of% e₂, reassoc_of% s₄, reassoc_of% s₁₀, reassoc_of% s₈,
    ← reassoc_of% s₇, e₃, reassoc_of% hd]

/-- The comparison `E ∘ H ≅ H ∘ E` of homology on derived categories commutes with the
shift isomorphisms of the two homology functors. -/
theorem derivedHomologyIso_shiftIso (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) (L : DerivedCategory A) :
    E.map (((homologyFunctor A 0).shiftIso 1 n₀ n₁ h).hom.app L) =
      (derivedHomologyIso E n₀).inv.app (L⟦(1:ℤ)⟧) ≫
        (homologyFunctor B n₀).map ((E.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app L) ≫
        ((homologyFunctor B 0).shiftIso 1 n₀ n₁ h).hom.app (E.mapDerivedCategory.obj L) ≫
        (derivedHomologyIso E n₁).hom.app L := by
  let α : (shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ homologyFunctor A n₀) ⋙ E ⟶
      homologyFunctor A n₁ ⋙ E :=
    Functor.whiskerRight ((homologyFunctor A 0).shiftIso 1 n₀ n₁ h).hom E
  let β : (shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ homologyFunctor A n₀) ⋙ E ⟶
      homologyFunctor A n₁ ⋙ E :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (shiftFunctor (DerivedCategory A) (1 : ℤ))
        (derivedHomologyIso E n₀).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (E.mapDerivedCategory.commShiftIso (1 : ℤ)).hom (homologyFunctor B n₀) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft E.mapDerivedCategory ((homologyFunctor B 0).shiftIso 1 n₀ n₁ h).hom ≫
      (derivedHomologyIso E n₁).hom
  have hαβ : α = β := by
    refine Localization.natTrans_ext Q (HomologicalComplex.quasiIso A (.up ℤ)) (fun M => ?_)
    simp only [α, β, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    refine shift_chain
      (a₁ := E.map ((homologyFunctor A n₀).map ((Q.commShiftIso (1 : ℤ)).inv.app M)))
      (a₂ := E.map ((homologyFunctorFactors A n₀).hom.app (M⟦(1 : ℤ)⟧)))
      (a₃ := E.map
        (((HomologicalComplex.homologyFunctor A (.up ℤ) 0).shiftIso 1 n₀ n₁ h).hom.app M))
      (a₄ := E.map ((homologyFunctorFactors A n₁).inv.app M))
      (b₁ := (homologyFunctor B n₀).map
        (E.mapDerivedCategory.map ((Q.commShiftIso (1 : ℤ)).inv.app M)))
      (Hξh := (homologyFunctor B n₀).map
        (E.mapDerivedCategory.map ((Q.commShiftIso (1 : ℤ)).hom.app M)))
      (dinvQ := (derivedHomologyIso E n₀).inv.app (Q.obj (M⟦(1 : ℤ)⟧)))
      (Hφ := (homologyFunctor B n₁).map (E.mapDerivedCategoryFactors.hom.app M))
      (fBE := (homologyFunctorFactors B n₁).hom.app ((E.mapHomologicalComplex _).obj M))
      (c₁ := (complexHomologyIso E (.up ℤ) n₁).hom.app M)
      (HφS := (homologyFunctor B n₀).map ((E.mapDerivedCategoryFactors.hom.app M)⟦(1 : ℤ)⟧'))
      (sDQ := ((homologyFunctor B 0).shiftIso 1 n₀ n₁ h).hom.app
        (Q.obj ((E.mapHomologicalComplex _).obj M)))
      (Hξ'inv := (homologyFunctor B n₀).map
        ((Q.commShiftIso (1 : ℤ)).inv.app ((E.mapHomologicalComplex _).obj M)))
      (fB0S := (homologyFunctorFactors B n₀).hom.app
        (((E.mapHomologicalComplex _).obj M)⟦(1 : ℤ)⟧))
      (sCB := ((HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftIso 1 n₀ n₁ h).hom.app
        ((E.mapHomologicalComplex _).obj M))
      (fBEinv := (homologyFunctorFactors B n₁).inv.app ((E.mapHomologicalComplex _).obj M))
      (Hφ₁ := (homologyFunctor B n₀).map (E.mapDerivedCategoryFactors.hom.app (M⟦(1 : ℤ)⟧)))
      (HQκ := (homologyFunctor B n₀).map
        (Q.map (((E.mapHomologicalComplex (.up ℤ)).commShiftIso (1:ℤ)).hom.app M)))
      (Hξ' := (homologyFunctor B n₀).map
        ((Q.commShiftIso (1 : ℤ)).hom.app ((E.mapHomologicalComplex _).obj M)))
      (fBE₀ := (homologyFunctorFactors B n₀).hom.app
        ((E.mapHomologicalComplex _).obj (M⟦(1 : ℤ)⟧)))
      (HCκ := (HomologicalComplex.homologyFunctor B (.up ℤ) n₀).map
        (((E.mapHomologicalComplex (.up ℤ)).commShiftIso (1:ℤ)).hom.app M))
      (c₀ := (complexHomologyIso E (.up ℤ) n₀).hom.app (M⟦(1 : ℤ)⟧))
      (a₂' := E.map ((homologyFunctorFactors A n₀).inv.app (M⟦(1 : ℤ)⟧)))
      (dQ₀ := (derivedHomologyIso E n₀).hom.app (Q.obj (M⟦(1 : ℤ)⟧)))
      ?_ ((derivedHomologyIso E n₀).inv.naturality
        ((Q.commShiftIso (1 : ℤ)).inv.app M)).symm ?_
      (derivedHomologyIso_hom_app_Q E n₁ M) (derivedHomologyIso_hom_app_Q E n₀ (M⟦(1 : ℤ)⟧))
      (Iso.inv_hom_id_app _ _) ?_
      (((homologyFunctor B 0).shiftIso 1 n₀ n₁ h).hom.naturality
        (E.mapDerivedCategoryFactors.hom.app M))
      (homologyFunctor_shiftIso_hom_app_Q n₀ n₁ h _)
      (complexHomologyIso_shiftIso E n₀ n₁ h M)
      ((homologyFunctorFactors B n₀).hom.naturality _)
      (Iso.inv_hom_id_app _ _) ?_ ?_
    · exact (congrArg E.map (homologyFunctor_shiftIso_hom_app_Q n₀ n₁ h M)).trans
        (map_comp₄ E _ _ _ _)
    · exact Iso.inv_hom_id_map (E.mapDerivedCategory.mapIso ((Q.commShiftIso (1 : ℤ)).app M))
        (homologyFunctor B n₀)
    · have hφ := NatTrans.shift_app_comm E.mapDerivedCategoryFactors.hom (1 : ℤ) M
      rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hφ
      have := congrArg (homologyFunctor B n₀).map hφ
      simp only [Functor.map_comp, Category.assoc] at this
      exact this
    · exact Iso.hom_inv_id_map ((Q.commShiftIso (1 : ℤ)).app ((E.mapHomologicalComplex _).obj M))
        (homologyFunctor B n₀)
    · exact Iso.inv_hom_id_map ((homologyFunctorFactors A n₀).app (M⟦(1 : ℤ)⟧)) E
  exact (NatTrans.congr_app hαβ L).trans (id_chain₄ _ _ _ _)

private theorem delta_chain {𝒳 : Type*} [Category* 𝒳] {o₁ o₂ o₃ o₄ o₅ o₆ o₇ : 𝒳}
    {dinv₃ : o₁ ⟶ o₂} {Hm : o₂ ⟶ o₃} {Hη : o₃ ⟶ o₄} {sB : o₄ ⟶ o₅} {d₁ : o₅ ⟶ o₇}
    {EHm : o₁ ⟶ o₆} {dinvS : o₆ ⟶ o₃} {EsA : o₆ ⟶ o₇} {Hmη : o₂ ⟶ o₄}
    (hmη : Hmη = Hm ≫ Hη)
    (hnat : dinv₃ ≫ Hm = EHm ≫ dinvS) (hkey : EsA = dinvS ≫ Hη ≫ sB ≫ d₁) :
    dinv₃ ≫ (Hmη ≫ sB) ≫ d₁ = EHm ≫ EsA := by
  rw [hmη, hkey, ← reassoc_of% hnat]
  simp only [Category.assoc]

/-- **An exact functor commutes with the connecting morphisms of the homology sequence** on the
unbounded derived category, through the comparison `E ∘ H ≅ H ∘ E`. -/
theorem derivedHomologyIso_homologySequenceδ (T : Pretriangulated.Triangle (DerivedCategory A))
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (derivedHomologyIso E n₀).inv.app T.obj₃ ≫
        (homologyFunctor B 0).homologySequenceδ (E.mapDerivedCategory.mapTriangle.obj T) n₀ n₁ h ≫
        (derivedHomologyIso E n₁).hom.app T.obj₁ =
      E.map ((homologyFunctor A 0).homologySequenceδ T n₀ n₁ h) := by
  have h' : 1 + n₀ = n₁ := by rw [add_comm 1, h]
  refine (delta_chain ((homologyFunctor B n₀).map_comp _ _)
    ((derivedHomologyIso E n₀).inv.naturality T.mor₃).symm
    (derivedHomologyIso_shiftIso E n₀ n₁ h' T.obj₁)).trans ?_
  exact (E.map_comp _ _).symm

end Derived

/-- **The commutation with the shift of a lift through a full subcategory stable under the
shift**, read through the inclusion: it is the commutation of the functor being lifted. -/
theorem ι_map_lift_commShiftIso_hom_app {𝒞 ℰ : Type*} [Category* 𝒞] [Category* ℰ]
    {G : Type*} [AddMonoid G] [HasShift 𝒞 G] [HasShift ℰ G] (P : ObjectProperty 𝒞)
    [P.IsStableUnderShift G] (F : ℰ ⥤ 𝒞) (hF : ∀ X, P (F.obj X)) [F.CommShift G] (a : G)
    (X : ℰ) :
    P.ι.map (((P.lift F hF).commShiftIso a).hom.app X) ≫
        (P.ι.commShiftIso a).hom.app ((P.lift F hF).obj X) =
      (F.commShiftIso a).hom.app X := by
  have h := NatTrans.shift_app_comm (P.liftCompιIso F hF).hom a X
  rw [Functor.commShiftIso_comp_hom_app] at h
  have h' : (P.ι.map (((P.lift F hF).commShiftIso a).hom.app X) ≫
        (P.ι.commShiftIso a).hom.app ((P.lift F hF).obj X)) ≫ (shiftFunctor 𝒞 a).map (𝟙 _) =
      𝟙 _ ≫ (F.commShiftIso a).hom.app X := h
  simpa using h'

section Plus

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

open DerivedCategory


/-- Under the inclusion `Plus.ι`, the commutation of `E.mapDerivedCategoryPlus` with the shift by
`a` is the commutation of `E.mapDerivedCategory` with that shift. -/
theorem ι_map_mapDerivedCategoryPlus_commShiftIso (a : ℤ) (X : Plus A) :
    Plus.ι.map ((E.mapDerivedCategoryPlus.commShiftIso a).hom.app X) ≫
        (Plus.ι.commShiftIso a).hom.app (E.mapDerivedCategoryPlus.obj X) =
      E.mapDerivedCategory.map ((Plus.ι.commShiftIso a).hom.app X) ≫
        (E.mapDerivedCategory.commShiftIso a).hom.app (Plus.ι.obj X) :=
  (ι_map_lift_commShiftIso_hom_app DerivedCategory.TStructure.t.plus
    (Plus.ι ⋙ E.mapDerivedCategory) (fun X => (E.mapDerivedCategoryPlus.obj X).property) a X).trans
    (Functor.commShiftIso_comp_hom_app _ _ a X)

/-- Under the inclusion `Plus.ι`, the commutation of `Plus.Qh` with the shift by `a` is the
commutation of `DerivedCategory.Qh` with that shift. -/
theorem ι_map_Qh_commShiftIso (a : ℤ) (K : HomotopyCategory.Plus A) :
    Plus.ι.map ((Plus.Qh.commShiftIso a).hom.app K) ≫
        (Plus.ι.commShiftIso a).hom.app (Plus.Qh.obj K) =
      DerivedCategory.Qh.map (((HomotopyCategory.Plus.ι A).commShiftIso a).hom.app K) ≫
        (DerivedCategory.Qh.commShiftIso a).hom.app ((HomotopyCategory.Plus.ι A).obj K) :=
  (ι_map_lift_commShiftIso_hom_app DerivedCategory.TStructure.t.plus
    (HomotopyCategory.Plus.ι A ⋙ DerivedCategory.Qh) (fun K => (Plus.Qh.obj K).property) a K).trans
    (Functor.commShiftIso_comp_hom_app _ _ a K)

omit [HasDerivedCategory A] [HasDerivedCategory B] [PreservesFiniteLimits E]
  [PreservesFiniteColimits E] in
/-- Under the inclusion `HomotopyCategory.Plus.ι`, the commutation of
`E.mapHomotopyCategoryPlus` with the shift by `a` is the commutation of
`E.mapHomotopyCategory` with that shift. -/
theorem ι_map_mapHomotopyCategoryPlus_commShiftIso (a : ℤ) (K : HomotopyCategory.Plus A) :
    (HomotopyCategory.Plus.ι B).map ((E.mapHomotopyCategoryPlus.commShiftIso a).hom.app K) ≫
        ((HomotopyCategory.Plus.ι B).commShiftIso a).hom.app (E.mapHomotopyCategoryPlus.obj K) =
      (E.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (((HomotopyCategory.Plus.ι A).commShiftIso a).hom.app K) ≫
        ((E.mapHomotopyCategory (ComplexShape.up ℤ)).commShiftIso a).hom.app
          ((HomotopyCategory.Plus.ι A).obj K) :=
  (ι_map_lift_commShiftIso_hom_app (HomotopyCategory.plus B)
    (HomotopyCategory.Plus.ι A ⋙ E.mapHomotopyCategory (ComplexShape.up ℤ))
    (fun K => (E.mapHomotopyCategoryPlus.obj K).property) a K).trans
    (Functor.commShiftIso_comp_hom_app _ _ a K)

private theorem factorsh_chain {𝒳 : Type*} [Category* 𝒳]
    {o₀ o₁ o₂ o₃ o₄ p₁ p₂ q₁ q₂ q₃ r₁ r₂ : 𝒳}
    {a₁ : o₀ ⟶ o₁} {a₂ : o₁ ⟶ o₂} {a₃ : o₂ ⟶ o₃} {a₄ : o₃ ⟶ o₄}
    {b₁ : o₀ ⟶ q₁} {b₂ : q₁ ⟶ q₂} {b₃ : q₂ ⟶ q₃} {b₄ : q₃ ⟶ o₄}
    {c₁ : o₁ ⟶ p₁} {c₂ : p₁ ⟶ o₃} {d₁ : o₀ ⟶ p₂} {d₂ : p₂ ⟶ p₁}
    {φ' : p₂ ⟶ r₁} {w₁ : r₁ ⟶ r₂} {w₂ : r₂ ⟶ o₄} {v₁ : q₁ ⟶ r₁} {t₁ : q₂ ⟶ r₂}
    {aa : o₀ ⟶ p₁} {dd : o₀ ⟶ p₁} {bb : q₁ ⟶ r₂} {vw : q₁ ⟶ r₂}
    (h₁ : a₂ ≫ a₃ = c₁ ≫ c₂) (haa : aa = a₁ ≫ c₁) (h₂ : aa = dd) (hdd : dd = d₁ ≫ d₂)
    (hD : d₂ ≫ c₂ ≫ a₄ = φ' ≫ w₁ ≫ w₂) (hn : d₁ ≫ φ' = b₁ ≫ v₁)
    (h₂' : b₃ ≫ b₄ = t₁ ≫ w₂) (hbb : bb = b₂ ≫ t₁) (h₃ : bb = vw) (hvw : vw = v₁ ≫ w₁) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ = b₁ ≫ b₂ ≫ b₃ ≫ b₄ := by
  have h₂'' : a₁ ≫ c₁ = d₁ ≫ d₂ := haa.symm.trans (h₂.trans hdd)
  have h₃' : b₂ ≫ t₁ = v₁ ≫ w₁ := hbb.symm.trans (h₃.trans hvw)
  rw [reassoc_of% h₁, reassoc_of% h₂'', hD, reassoc_of% hn, h₂', reassoc_of% h₃']

/-- The isomorphism `E.mapDerivedCategoryPlusFactorsh` commutes with the shifts by `ℤ`. -/
theorem natTransCommShift_mapDerivedCategoryPlusFactorsh :
    NatTrans.CommShift E.mapDerivedCategoryPlusFactorsh.hom ℤ := by
  refine Stacks.Triangulated.natTransCommShift_of_whiskerRight ℤ Plus.ι _ ?_
  refine ⟨fun a => ?_⟩
  ext K
  have hD := NatTrans.shift_app_comm E.mapDerivedCategoryFactorsh.hom a
    ((HomotopyCategory.Plus.ι A).obj K)
  simp only [Functor.commShiftIso_comp_hom_app] at hD
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  have h₁ := ι_map_mapDerivedCategoryPlus_commShiftIso E a (Plus.Qh.obj K)
  have h₂ := ι_map_Qh_commShiftIso (A := A) a K
  have h₂' := ι_map_Qh_commShiftIso (A := B) a (E.mapHomotopyCategoryPlus.obj K)
  have h₃ := ι_map_mapHomotopyCategoryPlus_commShiftIso E a K
  have hn := E.mapDerivedCategoryFactorsh.hom.naturality
    (((HomotopyCategory.Plus.ι A).commShiftIso a).hom.app K)
  simp only [Functor.map_comp, Category.assoc]
  simp only [Category.assoc] at hD
  exact factorsh_chain h₁ (E.mapDerivedCategory.map_comp _ _)
    (congrArg E.mapDerivedCategory.map h₂) (E.mapDerivedCategory.map_comp _ _) hD hn h₂'
    (DerivedCategory.Qh.map_comp _ _) (congrArg DerivedCategory.Qh.map h₃)
    (DerivedCategory.Qh.map_comp _ _)

attribute [local instance] Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  natTransCommShift_mapDerivedCategoryPlusFactorsh

variable [EnoughInjectives A]

/-- **The identification of the right derived functor of an exact functor with its degreewise
action is compatible with the shift.** -/
theorem natTransCommShift_exactMapDerivedCategoryPlusIso :
    NatTrans.CommShift (exactMapDerivedCategoryPlusIso E).hom ℤ := by
  refine NatTrans.commShift_of_whiskerLeft Plus.Qh _ ?_
  have h : Functor.whiskerLeft Plus.Qh (exactMapDerivedCategoryPlusIso E).hom =
      E.mapDerivedCategoryPlusFactorsh.hom ≫ E.rightDerivedFunctorPlusUnith := by
    refine NatTrans.ext (funext fun K => ?_)
    exact exactMapDerivedCategoryPlusIso_hom_app_Qh E K
  rw [h]
  infer_instance

private theorem id_comp_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ : 𝒳}
    (a : o₀ ⟶ o₁) (b : o₁ ⟶ o₂) (c : o₂ ⟶ o₃) : a ≫ 𝟙 _ ≫ b ≫ 𝟙 _ ≫ c = (a ≫ b) ≫ c := by
  simp

/-- The connecting morphism of the homology sequence of the image of a triangle under a functor
commuting with the shift. -/
private theorem homologySequenceδ_mapTriangle {C 𝒟 : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [Category* 𝒟] [HasShift 𝒟 ℤ] (F : 𝒟 ⥤ DerivedCategory C)
    [F.CommShift ℤ] (T : Pretriangulated.Triangle 𝒟) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C 0).homologySequenceδ (F.mapTriangle.obj T) n₀ n₁ h =
      (homologyFunctor C n₀).map (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        ((homologyFunctor C 0).shiftIso 1 n₀ n₁ (by omega)).hom.app (F.obj T.obj₁) := rfl

omit [EnoughInjectives A] in
/-- The connecting morphism of the homology sequence on the bounded below derived category is
the one on the unbounded derived category. -/
theorem plus_homologySequenceδ_eq {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (T : Pretriangulated.Triangle (Plus C)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (Plus.homologyFunctor C 0).homologySequenceδ T n₀ n₁ h =
      (homologyFunctor C 0).homologySequenceδ (Plus.ι.mapTriangle.obj T) n₀ n₁ h := by
  have e₁ : (Plus.homologyFunctor C 0).homologySequenceδ T n₀ n₁ h =
      (homologyFunctor C n₀).map (Plus.ι.map T.mor₃) ≫ 𝟙 _ ≫
        (homologyFunctor C n₀).map ((Plus.ι.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫ 𝟙 _ ≫
        ((homologyFunctor C 0).shiftIso 1 n₀ n₁ (by omega)).hom.app (Plus.ι.obj T.obj₁) := rfl
  rw [e₁, homologySequenceδ_mapTriangle, Functor.map_comp]
  exact id_comp_chain _ _ _

omit [EnoughInjectives A] in
/-- The connecting morphisms of the images of a triangle under `E⁺ ⋙ ι` and under `ι ⋙ E` agree,
the degreewise action on bounded below derived categories being the lift of the one on unbounded
derived categories. -/
theorem homologySequenceδ_ι_mapDerivedCategoryPlus (T : Pretriangulated.Triangle (Plus A))
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor B 0).homologySequenceδ
        (Plus.ι.mapTriangle.obj (E.mapDerivedCategoryPlus.mapTriangle.obj T)) n₀ n₁ h =
      (homologyFunctor B 0).homologySequenceδ
        (E.mapDerivedCategory.mapTriangle.obj (Plus.ι.mapTriangle.obj T)) n₀ n₁ h := by
  rw [homologySequenceδ_mapTriangle, homologySequenceδ_mapTriangle]
  refine congrArg (· ≫ _) (congrArg (homologyFunctor B n₀).map ?_)
  refine (congrArg (· ≫ _) (Plus.ι.map_comp _ _)).trans ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (ι_map_mapDerivedCategoryPlus_commShiftIso E 1 T.obj₁))).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (E.mapDerivedCategory.map_comp _ _).symm)

private theorem conj_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {d₀ : o₀ ⟶ o₁} {t₀ : o₁ ⟶ o₂} {δR : o₂ ⟶ o₃} {t₁ : o₃ ⟶ o₄} {d₁ : o₄ ⟶ o₅}
    {δE : o₁ ⟶ o₄} {t₁' : o₄ ⟶ o₃} {x : o₀ ⟶ o₅}
    (hnat : t₀ ≫ δR = δE ≫ t₁') (hinv : t₁' ≫ t₁ = 𝟙 _) (hx : d₀ ≫ δE ≫ d₁ = x) :
    d₀ ≫ t₀ ≫ δR ≫ t₁ ≫ d₁ = x := by
  rw [reassoc_of% hnat, reassoc_of% hinv, hx]

attribute [local instance] natTransCommShift_exactMapDerivedCategoryPlusIso

/-- **An exact functor commutes with the connecting morphisms of the homology sequence** on
the bounded below derived category: read through the comparison
`exactRightDerivedPlusHomologyIso` of `H ⁿ(RE(-))` with `E(H ⁿ(-))`, the
connecting morphism of the image of a triangle under `RE` is `E` of the connecting morphism of
the triangle. -/
theorem exactRightDerivedPlusHomologyIso_homologySequenceδ
    (T : Pretriangulated.Triangle (Plus A)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (exactRightDerivedPlusHomologyIso E n₀).inv.app T.obj₃ ≫
        (Plus.homologyFunctor B 0).homologySequenceδ (E.rightDerivedFunctorPlus.mapTriangle.obj T)
          n₀ n₁ h ≫
        (exactRightDerivedPlusHomologyIso E n₁).hom.app T.obj₁ =
      E.map ((Plus.homologyFunctor A 0).homologySequenceδ T n₀ n₁ h) := by
  have hnat := Stacks.Triangulated.homologySequenceδ_natTrans (Plus.homologyFunctor B 0)
    (exactMapDerivedCategoryPlusIso E).hom T n₀ n₁ h
  have hx : (derivedHomologyIso E n₀).inv.app (Plus.ι.obj T.obj₃) ≫
      (Plus.homologyFunctor B 0).homologySequenceδ (E.mapDerivedCategoryPlus.mapTriangle.obj T)
        n₀ n₁ h ≫
      (derivedHomologyIso E n₁).hom.app (Plus.ι.obj T.obj₁) =
      E.map ((Plus.homologyFunctor A 0).homologySequenceδ T n₀ n₁ h) := by
    rw [plus_homologySequenceδ_eq, homologySequenceδ_ι_mapDerivedCategoryPlus,
      plus_homologySequenceδ_eq]
    exact derivedHomologyIso_homologySequenceδ E (Plus.ι.mapTriangle.obj T) n₀ n₁ h
  have e₀ : (exactRightDerivedPlusHomologyIso E n₀).inv.app T.obj₃ =
      (derivedHomologyIso E n₀).inv.app (Plus.ι.obj T.obj₃) ≫
        ((Plus.homologyFunctor B 0).shift n₀).map
          ((exactMapDerivedCategoryPlusIso E).hom.app T.obj₃) := by
    simp [exactRightDerivedPlusHomologyIso]
    rfl
  have e₁ : (exactRightDerivedPlusHomologyIso E n₁).hom.app T.obj₁ =
      ((Plus.homologyFunctor B 0).shift n₁).map
          ((exactMapDerivedCategoryPlusIso E).app T.obj₁).inv ≫
        (derivedHomologyIso E n₁).hom.app (Plus.ι.obj T.obj₁) := by
    simp [exactRightDerivedPlusHomologyIso]
    rfl
  rw [e₀, e₁]
  exact (Category.assoc _ _ _).trans <| conj_chain hnat
    (Iso.hom_inv_id_map ((exactMapDerivedCategoryPlusIso E).app T.obj₁) _) hx

omit [EnoughInjectives A] in
/-- Under the inclusion `Plus.ι`, the component at `X` of `exactMapDerivedCategoryPlusSingle E n`
is the component at `X` of `E.mapDerivedCategorySingleFunctor n`. -/
theorem ι_map_exactMapDerivedCategoryPlusSingle_hom_app (n : ℤ) (X : A) :
    Plus.ι.map ((exactMapDerivedCategoryPlusSingle E n).hom.app X) =
      (E.mapDerivedCategorySingleFunctor n).hom.app X := by
  have := NatTrans.congr_app ((DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight
    A).map_preimage (X := Plus.singleFunctor A n ⋙ E.mapDerivedCategoryPlus)
      (Y := E ⋙ Plus.singleFunctor B n) (E.mapDerivedCategorySingleFunctor n).hom) X
  exact this

private theorem single_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ p₁ p₂ : 𝒳}
    {a : o₀ ⟶ o₁} {b : o₁ ⟶ o₂} {c : o₂ ⟶ o₃} {d : o₃ ⟶ o₄} {d' : o₂ ⟶ o₅} {μ₁ : o₅ ⟶ o₄}
    {b₁ : o₁ ⟶ o₆} {b₂ : o₆ ⟶ o₅} {Eδ : o₀ ⟶ o₆} {μ₃ : o₀ ⟶ p₁} {δ' : p₁ ⟶ o₄} {μ₁' : o₄ ⟶ o₅}
    {s : p₁ ⟶ p₂} {t : p₂ ⟶ o₄}
    (n₁ : c ≫ d = d' ≫ μ₁) (n₂ : b ≫ d' = b₁ ≫ b₂) (n₄ : a ≫ b₁ = Eδ)
    (n₅ : Eδ ≫ b₂ = μ₃ ≫ δ' ≫ μ₁') (n₆ : μ₁' ≫ μ₁ = 𝟙 _) (n₇ : s ≫ t = δ') :
    a ≫ b ≫ c ≫ d = μ₃ ≫ s ≫ t := by
  rw [n₁, reassoc_of% n₂, reassoc_of% n₄, reassoc_of% n₅, n₆, Category.comp_id, n₇]

omit [EnoughInjectives A] in
/-- The degreewise action of an exact functor on the bounded below derived category carries the
connecting morphism of the triangle of a short exact sequence to the connecting morphism of the
triangle of its image. -/
theorem mapDerivedCategoryPlus_singleδPlus {S : ShortComplex A} (hS : S.ShortExact) :
    E.mapDerivedCategoryPlus.map (Stacks.DerivedIndexing.singleδPlus hS) ≫
        (E.mapDerivedCategoryPlus.commShiftIso (1 : ℤ)).hom.app
          ((Plus.singleFunctor A 0).obj S.X₁) ≫
        ((exactMapDerivedCategoryPlusSingle E 0).hom.app S.X₁)⟦(1 : ℤ)⟧' =
      (exactMapDerivedCategoryPlusSingle E 0).hom.app S.X₃ ≫
        Stacks.DerivedIndexing.singleδPlus (hS.map_of_exact E) := by
  apply Plus.ι.map_injective
  rw [← cancel_mono
    ((Plus.ι.commShiftIso (1 : ℤ)).hom.app ((Plus.singleFunctor B 0).obj (E.obj S.X₁)))]
  simp only [Functor.map_comp, Category.assoc]
  have n₅ := hS.mapShiftedHom_singleδ E
  dsimp only [ShiftedHom.map] at n₅
  refine single_chain (Functor.commShiftIso_hom_naturality _ _ _)
    (ι_map_mapDerivedCategoryPlus_commShiftIso E 1 ((Plus.singleFunctor A 0).obj S.X₁))
    ((E.mapDerivedCategory.map_comp _ _).symm.trans
      (congrArg E.mapDerivedCategory.map (Stacks.DerivedIndexing.ι_map_singleδPlus hS))) n₅ ?_
    ?_
  · exact Iso.inv_hom_id_map ((E.mapDerivedCategorySingleFunctor 0).app S.X₁) _
  · exact Stacks.DerivedIndexing.ι_map_singleδPlus (hS.map_of_exact E)

private theorem single_chain₂ {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ : 𝒳}
    {σi₃ : o₀ ⟶ o₁} {τ₃ : o₁ ⟶ o₂} {Rδ : o₂ ⟶ o₃} {Rξ : o₃ ⟶ o₄}
    {Eδ : o₁ ⟶ o₅} {Eξ : o₅ ⟶ o₆} {τ₁S : o₆ ⟶ o₄} {τS : o₅ ⟶ o₃}
    {σ₃ : o₁ ⟶ o₀} {δ' : o₀ ⟶ o₇} {σi₁S : o₇ ⟶ o₆} {σ₁S : o₆ ⟶ o₇} {rhs : o₀ ⟶ o₄}
    (hnat : τ₃ ≫ Rδ = Eδ ≫ τS) (hshift : Eξ ≫ τ₁S = τS ≫ Rξ)
    (hsingle : Eδ ≫ Eξ ≫ σ₁S = σ₃ ≫ δ') (hσ : σi₃ ≫ σ₃ = 𝟙 _) (hσ' : σ₁S ≫ σi₁S = 𝟙 _)
    (hrhs : rhs = δ' ≫ σi₁S ≫ τ₁S) :
    σi₃ ≫ τ₃ ≫ Rδ ≫ Rξ = rhs := by
  have e : Eδ ≫ Eξ = σ₃ ≫ δ' ≫ σi₁S := by
    rw [← reassoc_of% hsingle, hσ', Category.comp_id]
  rw [reassoc_of% hnat, ← hshift, reassoc_of% e, reassoc_of% hσ, hrhs]

attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus in
/-- **The comparison `E(X)[0] ≅ RE(X[0])` of an exact functor carries the triangle of a short
exact sequence to the image under `RE` of the triangle**: it is compatible with the connecting
morphisms of the two triangles. -/
theorem exactSingleFunctorRightDerivedPlusIso_singleδPlus {S : ShortComplex A}
    (hS : S.ShortExact) :
    (exactSingleFunctorRightDerivedPlusIso E 0).hom.app S.X₃ ≫
        E.rightDerivedFunctorPlus.map (Stacks.DerivedIndexing.singleδPlus hS) ≫
        (E.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app
          ((Plus.singleFunctor A 0).obj S.X₁) =
      Stacks.DerivedIndexing.singleδPlus (hS.map_of_exact E) ≫
        ((exactSingleFunctorRightDerivedPlusIso E 0).hom.app S.X₁)⟦(1 : ℤ)⟧' := by
  have e₃ : (exactSingleFunctorRightDerivedPlusIso E 0).hom.app S.X₃ =
      (exactMapDerivedCategoryPlusSingle E 0).inv.app S.X₃ ≫
        (exactMapDerivedCategoryPlusIso E).hom.app
          ((Plus.singleFunctor A 0).obj S.X₃) := rfl
  have e₁ : (exactSingleFunctorRightDerivedPlusIso E 0).hom.app S.X₁ =
      (exactMapDerivedCategoryPlusSingle E 0).inv.app S.X₁ ≫
        (exactMapDerivedCategoryPlusIso E).hom.app
          ((Plus.singleFunctor A 0).obj S.X₁) := rfl
  rw [e₃, e₁, Category.assoc]
  exact single_chain₂ ((exactMapDerivedCategoryPlusIso E).hom.naturality _).symm
    (NatTrans.shift_app_comm (exactMapDerivedCategoryPlusIso E).hom 1 _)
    (mapDerivedCategoryPlus_singleδPlus E hS)
    ((exactMapDerivedCategoryPlusSingle E 0).inv_hom_id_app S.X₃)
    (Iso.hom_inv_id_map ((exactMapDerivedCategoryPlusSingle E 0).app S.X₁) _)
    (congrArg (_ ≫ ·) ((shiftFunctor (Plus B) (1 : ℤ)).map_comp _ _))

end Plus

end Stacks.DerivedFunctor

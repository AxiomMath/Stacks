module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.PositiveDegreeInjectivity
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The base change map and the connecting morphisms

Let `h ≫ f' = e ≫ g` be a commutative square of schemes as in [Stacks, Tag 0F02] and let
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0` be a short exact sequence of abelian sheaves on the small étale site of `T`.
The comparison diagram of [Stacks, Tag 0F03] needs the two connecting morphisms
`(f')⁻¹R ⁿg_* Q ⟶ (f')⁻¹R ⁿ⁺¹g_* F` and `R ⁿh_* e⁻¹Q ⟶ R ⁿ⁺¹h_* e⁻¹F` and the commutativity of
the square they form with the base change maps of [Stacks, Tag 0F02] in degrees `n` and `n + 1`.
This file constructs those two connecting morphisms and proves that square commutes.

Both connecting morphisms are the ones the long exact homology sequence of the bounded below
derived category attaches to the distinguished triangle `F[0] ⟶ I[0] ⟶ Q[0] ⟶ F[0]⟦1⟧` of the
short exact sequence, read through the identifications `baseChangeSourceIso` and
`baseChangeTargetIso` of `(f')⁻¹R ⁿg_*` and `R ⁿh_* e⁻¹` with cohomology of the bounded below
derived composites. The base change map in degree `n` is by construction the degree-`n`
cohomology of the derived comparison `smallEtaleDerivedBaseChangeAb`, so the square to be proved
is, after the identifications are stripped off, the compatibility of that single natural
transformation of functors on derived categories with the connecting morphisms — which is
`Stacks.Triangulated.homologySequenceδ_natTrans` as soon as the transformation is compatible
with the shift.

That compatibility with the shift is reduced, by
`Stacks.EtaleCohomology.natTransCommShift_smallEtaleDerivedBaseChangeAb`, to two statements about
*underived*, degreewise data on bounded below homotopy categories: that a natural transformation
of additive functors applied degreewise commutes with the shift, and that the comparison
isomorphism of a composite of two such degreewise functors does. The reduction runs through two
general steps, `Stacks.Cohomology.BaseChange.natTransCommShift_derived` and
`Stacks.Cohomology.BaseChange.natTransCommShift_onHomotopy`, which apply to any square of
additive functors, not only to the small étale sites.

Both degreewise statements are proved here, in each case by first proving the statement for
cochain complexes, then transporting it to the homotopy category of all cochain complexes along
the quotient functor, which is surjective on objects, and finally transporting it to the bounded
below subcategory along its inclusion, which is faithful. The three functors on bounded below
homotopy categories that occur are lifts through the full subcategory of bounded below complexes,
and the two criteria `Stacks.Triangulated.natTransCommShift_lift` and
`Stacks.Triangulated.natTransCommShift_liftComp` carry the compatibility down to such a lift from
the ambient homotopy category. The derived base change comparison is therefore compatible with
the shift unconditionally (`Stacks.EtaleCohomology.commShift_smallEtaleDerivedBaseChangeAb`), and
so is the commuting square (`Stacks.EtaleCohomology.higherBaseChangeMapAb_comm'`).

## Main definitions

* `Stacks.Cohomology.BaseChange.singleTrianglePlus` — the triangle
  `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[0]⟦1⟧` of a short exact sequence, in the bounded below derived
  category.
* `Stacks.EtaleCohomology.derivedBaseChangeSource`,
  `Stacks.EtaleCohomology.derivedBaseChangeTarget` — the two functors
  `R(f')⁻¹ Rg_*` and `Rh_* Re⁻¹` on bounded below derived categories that the derived base change
  comparison of [Stacks, Tag 0F02] goes between.
* `Stacks.EtaleCohomology.higherBaseChangeδSource`,
  `Stacks.EtaleCohomology.higherBaseChangeδTarget` — the connecting morphisms
  `(f')⁻¹R ⁿg_* Q ⟶ (f')⁻¹R ⁿ⁺¹g_* F` and `R ⁿh_* e⁻¹Q ⟶ R ⁿ⁺¹h_* e⁻¹F` of a short exact
  sequence.

## Main results

* `Stacks.Cohomology.BaseChange.comm_of_conjugate` — the elementary diagram lemma that transports
  a commuting square along isomorphisms of all four corners.
* `Stacks.Cohomology.BaseChange.natTransCommShift_mapHomologicalComplex`,
  `Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategory`,
  `Stacks.Cohomology.BaseChange.natTransCommShift_mapPlus` — a natural
  transformation of additive functors applied degreewise to cochain complexes, to their
  homotopy category, and to the bounded below homotopy category, commutes with the shift.
* `Stacks.Cohomology.BaseChange.natTransCommShift_mapHomologicalComplexCompIso`,
  `Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryCompIso`,
  `Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso` — the
  comparison isomorphism of a composite of additive functors applied degreewise to cochain
  complexes, to their homotopy category, and to the bounded below homotopy category, commutes
  with the shift.
* `Stacks.Cohomology.BaseChange.natTransCommShift_derived` — the derived descent of a comparison
  of a square of additive functors is compatible with the shift as soon as the comparison on
  bounded below homotopy categories is.
* `Stacks.Cohomology.BaseChange.natTransCommShift_onHomotopy` — the comparison on bounded below
  homotopy categories is compatible with the shift as soon as its degreewise ingredients are.
* `Stacks.EtaleCohomology.higherBaseChangeMapAb_comm` — **the base change map of
  [Stacks, Tag 0F02] commutes with the two connecting morphisms**, given that the derived base
  change comparison is compatible with the shift.
* `Stacks.EtaleCohomology.natTransCommShift_smallEtaleDerivedBaseChangeAb` — that hypothesis
  follows from the shift-compatibility of the degreewise ingredients of the base change map.
* `Stacks.EtaleCohomology.commShift_smallEtaleDerivedBaseChangeAb` — the derived base change
  comparison is compatible with the shift.
* `Stacks.EtaleCohomology.higherBaseChangeMapAb_comm'` — **the base change map of
  [Stacks, Tag 0F02] commutes with the two connecting morphisms**, with no hypothesis.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Cohomology.BaseChange

/-! ### Transporting a commuting square along isomorphisms -/

section Conjugate

variable {A : Type*} [Category* A]

/-- **A commuting square transported along isomorphisms of its four corners.** If `p₀` and `p₁`
correspond to `b₀` and `b₁` under isomorphisms `u₀, u₁` of the sources and `v₀, v₁` of the
targets, then a square commuting for `p₀, p₁` and a pair of vertical maps `dP, dQ` commutes for
`b₀, b₁` and the conjugated vertical maps. -/
public theorem comm_of_conjugate {S₀ S₁ P₀ P₁ T₀ T₁ Q₀ Q₁ : A}
    (u₀ : S₀ ≅ P₀) (u₁ : S₁ ≅ P₁) (v₀ : T₀ ≅ Q₀) (v₁ : T₁ ≅ Q₁)
    (b₀ : S₀ ⟶ T₀) (b₁ : S₁ ⟶ T₁) (p₀ : P₀ ⟶ Q₀) (p₁ : P₁ ⟶ Q₁)
    (dP : P₀ ⟶ P₁) (dQ : Q₀ ⟶ Q₁)
    (h₀ : u₀.hom ≫ p₀ = b₀ ≫ v₀.hom) (h₁ : u₁.hom ≫ p₁ = b₁ ≫ v₁.hom)
    (hd : p₀ ≫ dQ = dP ≫ p₁) :
    b₀ ≫ v₀.hom ≫ dQ ≫ v₁.inv = (u₀.hom ≫ dP ≫ u₁.inv) ≫ b₁ := by
  have k₁ : p₁ ≫ v₁.inv = u₁.inv ≫ b₁ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, h₁, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [← Category.assoc b₀, ← h₀, Category.assoc, reassoc_of% hd, k₁, Category.assoc,
    Category.assoc]

end Conjugate

/-! ### The triangle of a short exact sequence -/

section SingleTriangle

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **The triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[0]⟦1⟧` of a short exact sequence in the bounded
below derived category.** Its connecting map is `Stacks.DerivedIndexing.singleδPlus`, and it is
distinguished by `Stacks.DerivedIndexing.singleTrianglePlus_distinguished`. -/
public def singleTrianglePlus {S : ShortComplex C} (hS : S.ShortExact) :
    Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
    ((DerivedCategory.Plus.singleFunctor C 0).map S.g)
    (Stacks.DerivedIndexing.singleδPlus hS)

end SingleTriangle

/-! ### Degreewise natural transformations and the shift -/

section Degreewise

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G)

/-- **A natural transformation applied degreewise to cochain complexes is compatible with the
shift.** Both commutation isomorphisms are the identity in every degree, and the two sides of
the compatibility are `τ` in the shifted degree. -/
public theorem natTransCommShift_mapHomologicalComplex :
    NatTrans.CommShift (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)) ℤ := by
  constructor
  intro a
  ext K i
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    Category.id_comp, Category.comp_id]
  rfl

/-- The degreewise transformation on the homotopy category, whiskered by the quotient functor, is
the degreewise transformation on complexes read through the comparison isomorphisms of
`CategoryTheory.Functor.mapHomotopyCategoryFactors`. -/
public theorem whiskerLeft_quotient_mapHomotopyCategory :
    Functor.whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)) =
    (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ≫
      Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))
        (HomotopyCategory.quotient D (ComplexShape.up ℤ)) ≫
      (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv := by
  ext K
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **A natural transformation applied degreewise to the homotopy category of cochain complexes
is compatible with the shift.** Every object of the homotopy category is the image of a complex,
so the compatibility may be checked after whiskering by the quotient functor, where it is the
compatibility on complexes conjugated by two shift-compatible isomorphisms. -/
public theorem natTransCommShift_mapHomotopyCategory :
    NatTrans.CommShift (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)) ℤ := by
  have := natTransCommShift_mapHomologicalComplex τ
  refine Stacks.Triangulated.natTransCommShift_of_whiskerLeft ℤ
    (HomotopyCategory.quotient C (ComplexShape.up ℤ))
    HomotopyCategory.quotient_obj_surjective _ ?_
  rw [whiskerLeft_quotient_mapHomotopyCategory τ]
  infer_instance

end Degreewise

/-! ### Comparison isomorphisms for composites of degreewise functors -/

section CompIso

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]

/-- **The composite of two degreewise functors on the homotopy category is induced by the
composite of the degreewise functors on cochain complexes.** This is the two-step analogue of
`CategoryTheory.Functor.mapHomotopyCategoryFactors`, assembled from two copies of it. -/
public def mapHomotopyCategoryCompFactors (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] :
    HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          G.mapHomotopyCategory (ComplexShape.up ℤ)) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          G.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        HomotopyCategory.quotient E (ComplexShape.up ℤ) :=
  (Functor.associator (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (F.mapHomotopyCategory (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ))).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ)) ≪≫
    Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient D (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ)) ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) ≪≫
    (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (G.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient E (ComplexShape.up ℤ))).symm

/-- **The two-step comparison isomorphism is compatible with the shift.** Each of its five
factors is: the associators and the two one-step comparison isomorphisms are. -/
public theorem natTransCommShift_mapHomotopyCategoryCompFactors (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] :
    NatTrans.CommShift (mapHomotopyCategoryCompFactors F G).hom ℤ := by
  dsimp only [mapHomotopyCategoryCompFactors, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The two-step comparison isomorphism is the identity at the image of a cochain complex. -/
public theorem mapHomotopyCategoryCompFactors_hom_app (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (K : HomologicalComplex C (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryCompFactors F G).hom.app K = 𝟙 _ := by
  simp only [mapHomotopyCategoryCompFactors, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.mapHomotopyCategoryFactors,
    Category.id_comp, Category.comp_id]
  refine Eq.trans ?_ ((Category.comp_id ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
    (𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K)))).trans
    ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _))
  rfl

variable {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
  [F.Additive] [G.Additive] [H.Additive]

/-- **The comparison isomorphism of a composite of additive functors applied degreewise to
cochain complexes is compatible with the shift.** Every commutation isomorphism involved is the
identity in each degree, and both sides of the compatibility are `e` in the shifted degree. -/
public theorem natTransCommShift_mapHomologicalComplexCompIso :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom ℤ := by
  constructor
  intro a
  ext K i
  simp [Functor.commShiftIso_comp_hom_app]

/-- The comparison isomorphism on the homotopy category, whiskered by the quotient functor, is
the comparison isomorphism on complexes read through the two comparison isomorphisms of
`mapHomotopyCategoryCompFactors` and `CategoryTheory.Functor.mapHomotopyCategoryFactors`. -/
public theorem whiskerLeft_quotient_mapHomotopyCategoryCompIso :
    Functor.whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
        (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom =
      (mapHomotopyCategoryCompFactors F G).hom ≫
        Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom
          (HomotopyCategory.quotient E (ComplexShape.up ℤ)) ≫
        (H.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv := by
  ext K
  dsimp only [NatTrans.comp_app]
  rw [mapHomotopyCategoryCompFactors_hom_app F G K]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **The comparison isomorphism of a composite of additive functors applied degreewise to the
homotopy category of cochain complexes is compatible with the shift.** Every object of the
homotopy category is the image of a complex, so the compatibility may be checked after whiskering
by the quotient functor, where it is the comparison on complexes conjugated by two
shift-compatible isomorphisms. -/
public theorem natTransCommShift_mapHomotopyCategoryCompIso :
    NatTrans.CommShift (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom ℤ := by
  have := natTransCommShift_mapHomologicalComplexCompIso e
  exact Stacks.Triangulated.natTransCommShift_of_whiskerLeft_eq ℤ
    (HomotopyCategory.quotient C (ComplexShape.up ℤ))
    HomotopyCategory.quotient_obj_surjective _ (mapHomotopyCategoryCompFactors F G)
    (H.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    (Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom
      (HomotopyCategory.quotient E (ComplexShape.up ℤ)))
    (natTransCommShift_mapHomotopyCategoryCompFactors F G) inferInstance inferInstance
    (whiskerLeft_quotient_mapHomotopyCategoryCompIso e)

/-- **The comparison isomorphism of a composite of additive functors applied degreewise to the
bounded below homotopy category is compatible with the shift.** The three functors involved are
lifts through the full subcategories of bounded below complexes, and the comparison isomorphism
lifts the one on the homotopy category of all cochain complexes. -/
public theorem natTransCommShift_mapHomotopyCategoryPlusCompIso :
    NatTrans.CommShift (Functor.mapHomotopyCategoryPlusCompIso e).hom ℤ := by
  have := natTransCommShift_mapHomotopyCategoryCompIso e
  exact Stacks.Triangulated.natTransCommShift_liftComp (HomotopyCategory.plus D)
    (HomotopyCategory.plus E) ℤ _ _ _
    ((Functor.associator (HomotopyCategory.Plus.ι C) (F.mapHomotopyCategory (ComplexShape.up ℤ))
        (G.mapHomotopyCategory (ComplexShape.up ℤ))).hom ≫
      Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
        (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom)
    inferInstance (Functor.mapHomotopyCategoryPlusCompIso e).hom
    (fun _ ↦ (Category.id_comp _).symm)

end CompIso

/-! ### Degreewise constructions on the bounded below homotopy category -/

section DegreewisePlus

variable {A D : Type*} [Category* A] [Category* D] [Abelian A] [Abelian D]

/-- **A natural transformation applied degreewise on the bounded below homotopy category is
compatible with the shift.** The functors it goes between are the lifts through the full
subcategory of bounded below complexes of the degreewise functors on the homotopy category of all
cochain complexes, and `mapPlus τ` lifts the degreewise transformation there, which is compatible
with the shift by `natTransCommShift_mapHomotopyCategory`. -/
public theorem natTransCommShift_mapPlus {E H : A ⥤ D} [E.Additive] [H.Additive] (τ : E ⟶ H) :
    NatTrans.CommShift (mapPlus τ) ℤ := by
  have := natTransCommShift_mapHomotopyCategory τ
  exact Stacks.Triangulated.natTransCommShift_lift (HomotopyCategory.plus D) ℤ _ _
    (Functor.whiskerLeft (HomotopyCategory.Plus.ι A)
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)))
    inferInstance (mapPlus τ) (fun _ ↦ rfl)

end DegreewisePlus

/-! ### Shift-compatibility of a descended base change comparison -/

section DerivedShift

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]

/-- **The comparison on bounded below homotopy categories is compatible with the shift as soon
as its ingredients are.** `onHomotopy` is built from the comparison `e` for `RG`, the degreewise
transformation `mapPlus τ`, the two comparison isomorphisms for composites of degreewise
functors, and the derived-functor units of `RG'` and `RF'`; the units are compatible with the
shift, and the four remaining ingredients are the hypotheses. -/
public theorem natTransCommShift_onHomotopy (τ : F ⋙ G ⟶ G' ⋙ F')
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)
    (he : NatTrans.CommShift e.hom ℤ)
    (hτ : NatTrans.CommShift (mapPlus τ) ℤ)
    (h₁ : NatTrans.CommShift
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom ℤ)
    (h₂ : NatTrans.CommShift
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).hom ℤ) :
    NatTrans.CommShift (onHomotopy F F' G G' τ e) ℤ := by
  have := Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit F'
  have := Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit G'
  dsimp only [onHomotopy]
  infer_instance

/-- **The derived descent of a comparison is compatible with the shift as soon as the comparison
on bounded below homotopy categories is.** `derived` is the unique natural transformation out of
`RF ⋙ RG` through which `onHomotopy` factors, and `RF ⋙ RG` is a right derived functor with a
unit compatible with the shift, so the descent inherits the compatibility. -/
public theorem natTransCommShift_derived (τ : F ⋙ G ⟶ G' ⋙ F')
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)
    (hβ : NatTrans.CommShift (onHomotopy F F' G G' τ e) ℤ) :
    NatTrans.CommShift (derived F F' G G' τ e) ℤ := by
  have := Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit F
  let α := Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus ≫
    (Functor.associator DerivedCategory.Plus.Qh F.rightDerivedFunctorPlus
      G.rightDerivedFunctorPlus).hom
  let _ : (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor α
      (HomotopyCategory.Plus.quasiIso A) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso α
      (fun K ↦ by dsimp [α]; infer_instance)
  exact Stacks.Triangulated.natTransCommShift_rightDerivedDesc
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) α
    (HomotopyCategory.Plus.quasiIso A) ℤ
    (G'.rightDerivedFunctorPlus ⋙ F'.rightDerivedFunctorPlus) (onHomotopy F F' G G' τ e)

end DerivedShift

end Stacks.Cohomology.BaseChange

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

section BaseChangeSquare

variable {X' Y S' T : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The source `R(f')⁻¹ Rg_*` of the derived base change comparison of [Stacks, Tag 0F02], on
bounded below derived categories of abelian small étale sheaves. -/
public abbrev derivedBaseChangeSource :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (smallEtaleTopology X') Ab.{u + 1}) :=
  (smallEtalePushforwardAb g).rightDerivedFunctorPlus ⋙
    (smallEtalePullbackAb f').rightDerivedFunctorPlus

/-- The target `Rh_* Re⁻¹` of the derived base change comparison of [Stacks, Tag 0F02], on
bounded below derived categories of abelian small étale sheaves. -/
public abbrev derivedBaseChangeTarget :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (smallEtaleTopology X') Ab.{u + 1}) :=
  (smallEtalePullbackAb e).rightDerivedFunctorPlus ⋙
    (smallEtalePushforwardAb h).rightDerivedFunctorPlus

/-- **The connecting morphism `(f')⁻¹R ⁿg_* X₃ ⟶ (f')⁻¹R ⁿ⁺¹g_* X₁`** of a short exact sequence
of abelian sheaves on the small étale site of `T`: the connecting morphism of the long exact
homology sequence of the image of the triangle of the sequence under `R(f')⁻¹ Rg_*`, read through
the identification `baseChangeSourceIso` of `(f')⁻¹R ⁿg_*` with cohomology of that derived
composite. -/
public def higherBaseChangeδSource (q : ℕ)
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S.ShortExact) :
    (higherBaseChangeSource f' g q).obj S.X₃ ⟶
      (higherBaseChangeSource f' g (q + 1)).obj S.X₁ :=
  (baseChangeSourceIso f' g q).hom.app S.X₃ ≫
    (DerivedCategory.Plus.homologyFunctor
        (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).homologySequenceδ
      ((derivedBaseChangeSource f' g).mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hS)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
    (baseChangeSourceIso f' g (q + 1)).inv.app S.X₁

/-- **The connecting morphism `R ⁿh_* e⁻¹X₃ ⟶ R ⁿ⁺¹h_* e⁻¹X₁`** of a short exact sequence of
abelian sheaves on the small étale site of `T`: the connecting morphism of the long exact
homology sequence of the image of the triangle of the sequence under `Rh_* Re⁻¹`, read through
the identification `baseChangeTargetIso` of `R ⁿh_* e⁻¹` with cohomology of that derived
composite. -/
public def higherBaseChangeδTarget (q : ℕ)
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S.ShortExact) :
    (higherBaseChangeTarget h e q).obj S.X₃ ⟶
      (higherBaseChangeTarget h e (q + 1)).obj S.X₁ :=
  (baseChangeTargetIso h e q).hom.app S.X₃ ≫
    (DerivedCategory.Plus.homologyFunctor
        (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).homologySequenceδ
      ((derivedBaseChangeTarget h e).mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hS)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
    (baseChangeTargetIso h e (q + 1)).inv.app S.X₁

/-- **The base change map of [Stacks, Tag 0F02] commutes with the connecting morphisms.** For a
short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of abelian sheaves on the small étale site of `T`, the
base change maps in degrees `q` and `q + 1` form a commuting square with the connecting morphisms
`higherBaseChangeδSource` and `higherBaseChangeδTarget`.

The hypothesis is that the derived base change comparison `smallEtaleDerivedBaseChangeAb` is
compatible with the shift; `natTransCommShift_smallEtaleDerivedBaseChangeAb` reduces it to
statements about degreewise data. Given it, both connecting morphisms are the ones the homology
sequence attaches to one triangle, the base change map in each degree is the cohomology of the
single transformation `smallEtaleDerivedBaseChangeAb`, and the square is the naturality of the
connecting morphism in the triangle. -/
public theorem higherBaseChangeMapAb_comm (q : ℕ)
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S.ShortExact)
    (hτ : NatTrans.CommShift (smallEtaleDerivedBaseChangeAb f' g h e w) ℤ) :
    (higherBaseChangeMapAb f' g h e w q).app S.X₃ ≫ higherBaseChangeδTarget h e q hS =
      higherBaseChangeδSource f' g q hS ≫
        (higherBaseChangeMapAb f' g h e w (q + 1)).app S.X₁ :=
  Stacks.Cohomology.BaseChange.comm_of_conjugate
    ((baseChangeSourceIso f' g q).app S.X₃)
    ((baseChangeSourceIso f' g (q + 1)).app S.X₁)
    ((baseChangeTargetIso h e q).app S.X₃)
    ((baseChangeTargetIso h e (q + 1)).app S.X₁) _ _ _ _ _ _
    (baseChangeSourceIso_hom_app_comp f' g h e w q S.X₃)
    (baseChangeSourceIso_hom_app_comp f' g h e w (q + 1) S.X₁)
    (Stacks.Triangulated.homologySequenceδ_natTrans
      (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0)
      (smallEtaleDerivedBaseChangeAb f' g h e w)
      (Stacks.Cohomology.BaseChange.singleTrianglePlus hS) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl)

/-- **The derived base change comparison is compatible with the shift as soon as its degreewise
ingredients are.** The comparison `smallEtaleDerivedBaseChangeAb` is the derived descent of the
underived mate `smallEtaleBaseChangeAb`; the two steps of the descent carry shift-compatibility
along, and the comparison for `R(f')⁻¹` is the derived-functor unit of an exact functor, which is
compatible with the shift. What is left is the mate applied degreewise, and the two comparison
isomorphisms for composites of degreewise functors. -/
public theorem natTransCommShift_smallEtaleDerivedBaseChangeAb
    (hτ : NatTrans.CommShift
      (Stacks.Cohomology.BaseChange.mapPlus (smallEtaleBaseChangeAb f' g h e w)) ℤ)
    (h₁ : NatTrans.CommShift (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (smallEtalePushforwardAb g ⋙ smallEtalePullbackAb f'))).hom ℤ)
    (h₂ : NatTrans.CommShift (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (smallEtalePullbackAb e ⋙ smallEtalePushforwardAb h))).hom ℤ) :
    NatTrans.CommShift (smallEtaleDerivedBaseChangeAb f' g h e w) ℤ := by
  have hiso : IsIso (smallEtalePullbackAb f').rightDerivedFunctorPlusUnit :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso (smallEtalePullbackAb f')
  exact Stacks.Cohomology.BaseChange.natTransCommShift_derived (smallEtalePushforwardAb g)
    (smallEtalePushforwardAb h) (smallEtalePullbackAb f') (smallEtalePullbackAb e)
    (smallEtaleBaseChangeAb f' g h e w)
    (asIso (smallEtalePullbackAb f').rightDerivedFunctorPlusUnit)
    (Stacks.Cohomology.BaseChange.natTransCommShift_onHomotopy (smallEtalePushforwardAb g)
      (smallEtalePushforwardAb h) (smallEtalePullbackAb f') (smallEtalePullbackAb e)
      (smallEtaleBaseChangeAb f' g h e w)
      (asIso (smallEtalePullbackAb f').rightDerivedFunctorPlusUnit)
      (Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
        (smallEtalePullbackAb f'))
      hτ h₁ h₂)

/-- **The derived base change comparison is compatible with the shift.** The three pieces of
degreewise data its compatibility reduces to are the mate applied degreewise, which is
`Stacks.Cohomology.BaseChange.natTransCommShift_mapPlus`, and the two comparison isomorphisms for
composites of degreewise functors, which are
`Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso`. -/
public theorem commShift_smallEtaleDerivedBaseChangeAb :
    NatTrans.CommShift (smallEtaleDerivedBaseChangeAb f' g h e w) ℤ :=
  natTransCommShift_smallEtaleDerivedBaseChangeAb f' g h e w
    (Stacks.Cohomology.BaseChange.natTransCommShift_mapPlus
      (smallEtaleBaseChangeAb f' g h e w))
    (Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso
      (Iso.refl (smallEtalePushforwardAb g ⋙ smallEtalePullbackAb f')))
    (Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso
      (Iso.refl (smallEtalePullbackAb e ⋙ smallEtalePushforwardAb h)))

/-- **The base change map of [Stacks, Tag 0F02] commutes with the two connecting morphisms.** For
a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of abelian sheaves on the small étale site of `T`,
the base change maps in degrees `q` and `q + 1` form a commuting square with the connecting
morphisms `higherBaseChangeδSource` and `higherBaseChangeδTarget`. This is
`higherBaseChangeMapAb_comm` with its hypothesis discharged by
`commShift_smallEtaleDerivedBaseChangeAb`. -/
public theorem higherBaseChangeMapAb_comm' (q : ℕ)
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S.ShortExact) :
    (higherBaseChangeMapAb f' g h e w q).app S.X₃ ≫ higherBaseChangeδTarget h e q hS =
      higherBaseChangeδSource f' g q hS ≫
        (higherBaseChangeMapAb f' g h e w (q + 1)).app S.X₁ :=
  higherBaseChangeMapAb_comm f' g h e w q hS
    (commShift_smallEtaleDerivedBaseChangeAb f' g h e w)

end BaseChangeSquare

end Stacks.EtaleCohomology

end

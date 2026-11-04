module
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompQh
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

public import StacksFrontier.Homology.KFlat.BifunctorTransportComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# Transports of a derived bifunctor around a square of exact functors

Consider a square of exact functors between abelian categories `C₁ ⥤ C₂ ⥤ C₄` (`T`, then `R`)
and `C₁ ⥤ C₃ ⥤ C₄` (`L`, then `B`), both composites identified with one exact functor
`P : C₁ ⥤ C₄` by `cT : T ⋙ R ≅ P` and `cL : L ⋙ B ≅ P`, and bifunctors `F₁, …, F₄` on the four
corners with comparisons `εT, εR, εL, εB` along the four sides. If the four comparisons are
compatible with `cT ≪≫ cL.symm : T ⋙ R ≅ L ⋙ B` on objects of `C₁`, then the four derived
transports `derivedTransportProdIso` are compatible around the derived square, in the sense of
`Stacks.AffineProjectionFormula.TensorComparisonCompatible` — the one input of
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`.

## Main definitions

* `CochainComplex.KFlatBifunctor.squareEps`: the comparison along `P` induced by those along `L`
  and `B` through `cL`.

## Main results

* `CochainComplex.KFlatBifunctor.tensorComparisonCompatible_derivedTransportProdIso`.

## Implementation notes

The derived identifications of the two composites with `P.mapDerivedCategory` are
`Functor.mapDerivedCategoryCompIsoOfIso cT` and `… cL`, lifts along `Qh` of
`Functor.mapHomotopyCategoryCompIso`; this is the construction of the étale composition
isomorphisms `Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'`. Both composites
are compared with the transport along `P` by `derivedTransportIso_comp_app`, so no compatibility
is checked on the derived categories directly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace CochainComplex.KFlatBifunctor


/-- The arrow algebra behind `tensorComparisonCompatible_derivedTransportProdIso`, in a bare
category: two composites, each identified with a common transport after an isomorphism, agree
once those isomorphisms are composed through. -/
theorem square_chain {Dd : Type*} [Category Dd] (Q : Dd ⥤ Dd ⥤ Dd)
    {X₀ X₁ S₀ S₁ S₂ m n x y x' y' : Dd}
    (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ (Q.obj x).obj y) (b₁ : S₁ ⟶ S₂) (b₂ : S₂ ⟶ (Q.obj x').obj y')
    (i : x ⟶ m) (j : y ⟶ n) (ι : m ≅ x') (κ : n ≅ y') (d₁ : X₀ ⟶ S₀) (δ : S₀ ≅ S₁)
    (τP : S₀ ⟶ (Q.obj m).obj n)
    (h₁ : a₁ ≫ a₂ ≫ (Q.map i).app y ≫ (Q.obj m).map j = d₁ ≫ τP)
    (h₂ : b₁ ≫ b₂ ≫ (Q.map ι.inv).app y' ≫ (Q.obj m).map κ.inv = δ.inv ≫ τP) :
    a₁ ≫ a₂ ≫ (Q.map (i ≫ ι.hom)).app y ≫ (Q.obj x').map (j ≫ κ.hom) =
      (d₁ ≫ δ.hom) ≫ b₁ ≫ b₂ := by
  have h₂' : b₁ ≫ b₂ = δ.inv ≫ τP ≫ (Q.obj m).map κ.hom ≫ (Q.map ι.hom).app y' := by
    rw [← reassoc_of% h₂]
    simp [← Functor.map_comp, ← NatTrans.comp_app]
  rw [h₂', Category.assoc, Iso.hom_inv_id_assoc, ← reassoc_of% h₁]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [NatTrans.naturality, NatTrans.naturality_assoc]

section Square

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  (F₁ : C₁ ⥤ C₁ ⥤ C₁) (F₂ : C₂ ⥤ C₂ ⥤ C₂) (F₃ : C₃ ⥤ C₃ ⥤ C₃) (F₄ : C₄ ⥤ C₄ ⥤ C₄)
  {T : C₁ ⥤ C₂} {R : C₂ ⥤ C₄} {L : C₁ ⥤ C₃} {B : C₃ ⥤ C₄} {P : C₁ ⥤ C₄}
  [P.Additive] [B.Additive]
  (cL : L ⋙ B ≅ P)
  (εL : ∀ (a b : C₁), L.obj ((F₁.obj a).obj b) ≅ (F₃.obj (L.obj a)).obj (L.obj b))
  (εB : ∀ (a b : C₃), B.obj ((F₃.obj a).obj b) ≅ (F₄.obj (B.obj a)).obj (B.obj b))

/-- The comparison of `F₁` and `F₄` along `P`, obtained from those along `L` and along `B`
through `cL : L ⋙ B ≅ P`. -/
def squareEps (a b : C₁) :
    P.obj ((F₁.obj a).obj b) ≅ (F₄.obj (P.obj a)).obj (P.obj b) :=
  (cL.app _).symm ≪≫ B.mapIso (εL a b) ≪≫ εB (L.obj a) (L.obj b) ≪≫
    (F₄.mapIso (cL.app a)).app _ ≪≫ (F₄.obj (P.obj a)).mapIso (cL.app b)

omit [Abelian C₁] [Abelian C₃] [Abelian C₄] [P.Additive] [B.Additive] in
include εL εB in
/-- `squareEps` is natural in its first variable. -/
theorem squareEps_naturality₁
    (hεL₁ : ∀ {a a' : C₁} (f : a ⟶ a') (b : C₁),
      L.map ((F₁.map f).app b) ≫ (εL a' b).hom = (εL a b).hom ≫ (F₃.map (L.map f)).app (L.obj b))
    (hεB₁ : ∀ {a a' : C₃} (f : a ⟶ a') (b : C₃),
      B.map ((F₃.map f).app b) ≫ (εB a' b).hom = (εB a b).hom ≫ (F₄.map (B.map f)).app (B.obj b))
    {a a' : C₁} (f : a ⟶ a') (b : C₁) :
    P.map ((F₁.map f).app b) ≫ (squareEps F₁ F₃ F₄ cL εL εB a' b).hom =
      (squareEps F₁ F₃ F₄ cL εL εB a b).hom ≫ (F₄.map (P.map f)).app (P.obj b) := by
  have h₁ := cL.inv.naturality ((F₁.map f).app b)
  have h₂ := cL.hom.naturality f
  simp only [squareEps, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  have h₃ : B.map (L.map ((F₁.map f).app b)) ≫ B.map (εL a' b).hom =
      B.map (εL a b).hom ≫ B.map ((F₃.map (L.map f)).app (L.obj b)) := by
    rw [← B.map_comp, ← B.map_comp, hεL₁]
  have h₄ : (F₄.map (B.map (L.map f))).app (B.obj (L.obj b)) ≫
      (F₄.map (cL.hom.app a')).app (B.obj (L.obj b)) =
      (F₄.map (cL.hom.app a)).app (B.obj (L.obj b)) ≫
        (F₄.map (P.map f)).app (B.obj (L.obj b)) := by
    rw [← NatTrans.comp_app, ← F₄.map_comp, ← NatTrans.comp_app, ← F₄.map_comp]
    exact congrArg (fun t => (F₄.map t).app (B.obj (L.obj b))) h₂
  rw [reassoc_of% h₁]
  change cL.inv.app ((F₁.obj a).obj b) ≫ B.map (L.map ((F₁.map f).app b)) ≫ _ = _
  rw [reassoc_of% h₃, reassoc_of% (hεB₁ (L.map f) (L.obj b)), reassoc_of% h₄,
    NatTrans.naturality]

omit [Abelian C₁] [Abelian C₃] [Abelian C₄] [P.Additive] [B.Additive] in
include εL εB in
/-- `squareEps` is natural in its second variable. -/
theorem squareEps_naturality₂
    (hεL₂ : ∀ (a : C₁) {b b' : C₁} (g : b ⟶ b'),
      L.map ((F₁.obj a).map g) ≫ (εL a b').hom = (εL a b).hom ≫ (F₃.obj (L.obj a)).map (L.map g))
    (hεB₂ : ∀ (a : C₃) {b b' : C₃} (g : b ⟶ b'),
      B.map ((F₃.obj a).map g) ≫ (εB a b').hom = (εB a b).hom ≫ (F₄.obj (B.obj a)).map (B.map g))
    (a : C₁) {b b' : C₁} (g : b ⟶ b') :
    P.map ((F₁.obj a).map g) ≫ (squareEps F₁ F₃ F₄ cL εL εB a b').hom =
      (squareEps F₁ F₃ F₄ cL εL εB a b).hom ≫ (F₄.obj (P.obj a)).map (P.map g) := by
  have h₁ := cL.inv.naturality ((F₁.obj a).map g)
  have h₂ := cL.hom.naturality g
  simp only [squareEps, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  have h₃ : B.map (L.map ((F₁.obj a).map g)) ≫ B.map (εL a b').hom =
      B.map (εL a b).hom ≫ B.map ((F₃.obj (L.obj a)).map (L.map g)) := by
    rw [← B.map_comp, ← B.map_comp, hεL₂]
  have h₄ : (F₄.obj (P.obj a)).map (B.map (L.map g)) ≫ (F₄.obj (P.obj a)).map (cL.hom.app b') =
      (F₄.obj (P.obj a)).map (cL.hom.app b) ≫ (F₄.obj (P.obj a)).map (P.map g) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (F₄.obj (P.obj a)).map h₂
  rw [reassoc_of% h₁]
  change cL.inv.app ((F₁.obj a).obj b) ≫ B.map (L.map ((F₁.obj a).map g)) ≫ _ = _
  have h₅ := (F₄.map (cL.hom.app a)).naturality (B.map (L.map g))
  rw [reassoc_of% h₃, reassoc_of% (hεB₂ (L.obj a) (L.map g)), reassoc_of% h₅, h₄]

omit [Abelian C₁] [Abelian C₃] [Abelian C₄] [P.Additive] [B.Additive] in
include εL εB in
/-- `squareEps` is compatible with the comparisons along `L` and `B` and with `cL`, in the
form `derivedTransportCompNatTrans_eq` consumes. -/
theorem squareEps_compatible (a b : C₁) :
    B.map (εL a b).hom ≫ (εB (L.obj a) (L.obj b)).hom ≫
        (F₄.map (cL.hom.app a)).app (B.obj (L.obj b)) ≫ (F₄.obj (P.obj a)).map (cL.hom.app b) =
      cL.hom.app ((F₁.obj a).obj b) ≫ (squareEps F₁ F₃ F₄ cL εL εB a b).hom := by
  simp [squareEps]

section Compatible

variable [F₁.Additive] [∀ X, (F₁.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex C₁ ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F₁ (ComplexShape.up ℤ)]
  [F₂.Additive] [∀ X, (F₂.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex C₂ ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F₂ (ComplexShape.up ℤ)]
  [F₃.Additive] [∀ X, (F₃.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex C₃ ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F₃ (ComplexShape.up ℤ)]
  [F₄.Additive] [∀ X, (F₄.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex C₄ ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F₄ (ComplexShape.up ℤ)]
  [T.Additive] [R.Additive] [L.Additive]
  (cT : T ⋙ R ≅ P)
  (εT : ∀ (a b : C₁), T.obj ((F₁.obj a).obj b) ≅ (F₂.obj (T.obj a)).obj (T.obj b))
  (hεT₁ : ∀ {a a' : C₁} (f : a ⟶ a') (b : C₁),
    T.map ((F₁.map f).app b) ≫ (εT a' b).hom = (εT a b).hom ≫ (F₂.map (T.map f)).app (T.obj b))
  (hεT₂ : ∀ (a : C₁) {b b' : C₁} (g : b ⟶ b'),
    T.map ((F₁.obj a).map g) ≫ (εT a b').hom = (εT a b).hom ≫ (F₂.obj (T.obj a)).map (T.map g))
  (εR : ∀ (a b : C₂), R.obj ((F₂.obj a).obj b) ≅ (F₄.obj (R.obj a)).obj (R.obj b))
  (hεR₁ : ∀ {a a' : C₂} (f : a ⟶ a') (b : C₂),
    R.map ((F₂.map f).app b) ≫ (εR a' b).hom = (εR a b).hom ≫ (F₄.map (R.map f)).app (R.obj b))
  (hεR₂ : ∀ (a : C₂) {b b' : C₂} (g : b ⟶ b'),
    R.map ((F₂.obj a).map g) ≫ (εR a b').hom = (εR a b).hom ≫ (F₄.obj (R.obj a)).map (R.map g))
  (hεL₁ : ∀ {a a' : C₁} (f : a ⟶ a') (b : C₁),
    L.map ((F₁.map f).app b) ≫ (εL a' b).hom = (εL a b).hom ≫ (F₃.map (L.map f)).app (L.obj b))
  (hεL₂ : ∀ (a : C₁) {b b' : C₁} (g : b ⟶ b'),
    L.map ((F₁.obj a).map g) ≫ (εL a b').hom = (εL a b).hom ≫ (F₃.obj (L.obj a)).map (L.map g))
  (hεB₁ : ∀ {a a' : C₃} (f : a ⟶ a') (b : C₃),
    B.map ((F₃.map f).app b) ≫ (εB a' b).hom = (εB a b).hom ≫ (F₄.map (B.map f)).app (B.obj b))
  (hεB₂ : ∀ (a : C₃) {b b' : C₃} (g : b ⟶ b'),
    B.map ((F₃.obj a).map g) ≫ (εB a b').hom = (εB a b).hom ≫ (F₄.obj (B.obj a)).map (B.map g))
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) T]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) R]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) L]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) B]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) P]
  [∀ (X₁ X₂ : CochainComplex C₁ ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex T
      (((F₁.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj X₁).obj X₂))
      (ComplexShape.up ℤ)]
  [∀ (X₁ X₂ : CochainComplex C₂ ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex R
      (((F₂.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj X₁).obj X₂))
      (ComplexShape.up ℤ)]
  [∀ (X₁ X₂ : CochainComplex C₁ ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex L
      (((F₁.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj X₁).obj X₂))
      (ComplexShape.up ℤ)]
  [∀ (X₁ X₂ : CochainComplex C₃ ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex B
      (((F₃.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj X₁).obj X₂))
      (ComplexShape.up ℤ)]
  [∀ (X₁ X₂ : CochainComplex C₁ ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex P
      (((F₁.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj X₁).obj X₂))
      (ComplexShape.up ℤ)]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [(kFlatQLeft F₁).IsLocalization (kFlatQuasiIsoLeft F₁)]
  [(kFlatQ F₁).IsLocalization (kFlatQuasiIso F₁)]
  [(kFlatQLeft F₂).IsLocalization (kFlatQuasiIsoLeft F₂)]
  [(kFlatQ F₂).IsLocalization (kFlatQuasiIso F₂)]
  [(kFlatQLeft F₃).IsLocalization (kFlatQuasiIsoLeft F₃)]
  [(kFlatQ F₃).IsLocalization (kFlatQuasiIso F₃)]
  [(kFlatQLeft F₄).IsLocalization (kFlatQuasiIsoLeft F₄)]
  [(kFlatQ F₄).IsLocalization (kFlatQuasiIso F₄)]
  (hT₁ : ∀ K : CochainComplex C₁ ℤ, KFlatLeft F₁ K →
    KFlatLeft F₂ ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hT₂ : ∀ K : CochainComplex C₁ ℤ, KFlat F₁ K →
    KFlat F₂ ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hR₁ : ∀ K : CochainComplex C₂ ℤ, KFlatLeft F₂ K →
    KFlatLeft F₄ ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hR₂ : ∀ K : CochainComplex C₂ ℤ, KFlat F₂ K →
    KFlat F₄ ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hL₁ : ∀ K : CochainComplex C₁ ℤ, KFlatLeft F₁ K →
    KFlatLeft F₃ ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hL₂ : ∀ K : CochainComplex C₁ ℤ, KFlat F₁ K →
    KFlat F₃ ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hB₁ : ∀ K : CochainComplex C₃ ℤ, KFlatLeft F₃ K →
    KFlatLeft F₄ ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hB₂ : ∀ K : CochainComplex C₃ ℤ, KFlat F₃ K →
    KFlat F₄ ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hP₁ : ∀ K : CochainComplex C₁ ℤ, KFlatLeft F₁ K →
    KFlatLeft F₄ ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hP₂ : ∀ K : CochainComplex C₁ ℤ, KFlat F₁ K →
    KFlat F₄ ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

include hεL₁ hεL₂ hεB₁ hεB₂ hP₁ hP₂ in
/-- **The four derived transports around a square of exact functors are compatible**, in the
sense of `Stacks.AffineProjectionFormula.TensorComparisonCompatible`, as soon as the four
underived comparisons are compatible with `cT ≪≫ cL.symm : T ⋙ R ≅ L ⋙ B`. The two composites
around the derived square are identified with the derived functor of `P` through the
derived-category isomorphisms `Functor.mapDerivedCategoryCompIsoOfIso` of `cT` and `cL`. -/
theorem tensorComparisonCompatible_derivedTransportProdIso
    (hsq : ∀ (a b : C₁),
      R.map (εT a b).hom ≫ (εR (T.obj a) (T.obj b)).hom ≫
          (F₄.map ((cT ≪≫ cL.symm).hom.app a)).app (R.obj (T.obj b)) ≫
          (F₄.obj (B.obj (L.obj a))).map ((cT ≪≫ cL.symm).hom.app b) =
        (cT ≪≫ cL.symm).hom.app ((F₁.obj a).obj b) ≫ B.map (εL a b).hom ≫
          (εB (L.obj a) (L.obj b)).hom)
    (M N : DerivedCategory C₁) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible
      (Functor.mapDerivedCategoryCompIsoOfIso cT).symm
      (Functor.mapDerivedCategoryCompIsoOfIso cL).symm
      (Functor.uncurry.obj (derivedBifunctor F₁)) (Functor.uncurry.obj (derivedBifunctor F₂))
      (Functor.uncurry.obj (derivedBifunctor F₃)) (Functor.uncurry.obj (derivedBifunctor F₄))
      (derivedTransportProdIso F₁ F₃ L εL hεL₁ hεL₂ hL₁ hL₂).hom
      (derivedTransportProdIso F₂ F₄ R εR hεR₁ hεR₂ hR₁ hR₂).hom
      (derivedTransportProdIso F₁ F₂ T εT hεT₁ hεT₂ hT₁ hT₂).hom
      (derivedTransportProdIso F₃ F₄ B εB hεB₁ hεB₂ hB₁ hB₂).hom M N := by
  have hκ₁ := fun {a a' : C₁} (f : a ⟶ a') (b : C₁) =>
    squareEps_naturality₁ F₁ F₃ F₄ cL εL εB hεL₁ hεB₁ f b
  have hκ₂ := fun (a : C₁) {b b' : C₁} (g : b ⟶ b') =>
    squareEps_naturality₂ F₁ F₃ F₄ cL εL εB hεL₂ hεB₂ a g
  have hcL := squareEps_compatible F₁ F₃ F₄ cL εL εB
  have hcT : ∀ (a b : C₁), R.map (εT a b).hom ≫ (εR (T.obj a) (T.obj b)).hom ≫
      (F₄.map (cT.hom.app a)).app (R.obj (T.obj b)) ≫ (F₄.obj (P.obj a)).map (cT.hom.app b) =
      cT.hom.app ((F₁.obj a).obj b) ≫ (squareEps F₁ F₃ F₄ cL εL εB a b).hom := by
    intro a b
    have hea : cT.hom.app a = (cT ≪≫ cL.symm).hom.app a ≫ cL.hom.app a := by simp
    have heb : cT.hom.app b = (cT ≪≫ cL.symm).hom.app b ≫ cL.hom.app b := by simp
    have hn := (F₄.map (cL.hom.app a)).naturality ((cT ≪≫ cL.symm).hom.app b)
    rw [hea, heb]
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rw [← reassoc_of% hn, reassoc_of% (hsq a b), hcL]
    simp
  have h₁ := derivedTransportIso_comp_app F₁ F₂ F₄ T T T εT hεT₁ hεT₂ R R R εR hεR₁ hεR₂ P P P
    (squareEps F₁ F₃ F₄ cL εL εB) hκ₁ hκ₂ cT cT cT hcT hT₁ hT₂ hR₁ hR₂ hP₁ hP₂ M N
  have h₂ := derivedTransportIso_comp_app F₁ F₃ F₄ L L L εL hεL₁ hεL₂ B B B εB hεB₁ hεB₂ P P P
    (squareEps F₁ F₃ F₄ cL εL εB) hκ₁ hκ₂ cL cL cL hcL hL₁ hL₂ hB₁ hB₂ hP₁ hP₂ M N
  rw [Stacks.AffineProjectionFormula.TensorComparisonCompatible]
  simp only [Stacks.AffineProjectionFormula.squareCompositeIso_hom_app, Iso.symm_hom,
    Iso.symm_inv, derivedTransportProdIso_hom_app, Functor.uncurry_obj_map, Functor.comp_obj,
    Functor.prod_obj, Functor.uncurry_obj_obj]
  exact square_chain (derivedBifunctor F₄) _ _ _ _ _ _
    (Functor.mapDerivedCategoryCompIsoOfIso cL |>.app M)
    (Functor.mapDerivedCategoryCompIsoOfIso cL |>.app N) _
    (Functor.mapDerivedCategoryCompIsoOfIso cL |>.app (((derivedBifunctor F₁).obj M).obj N)) _ h₁ h₂

end Compatible

end Square

end CochainComplex.KFlatBifunctor

end

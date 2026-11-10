module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness
public import StacksFrontier.CategoryTheory.Subobject.CokernelComparisons
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceOfFilteredComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Bounded convergence of the Ext spectral sequence

For a filtered complex `M` and a derived object `K`, suppose that the Ext groups from the
quotients `M / F^p M` vanish for sufficiently negative `p` and that their canonical maps to the
Ext groups from `M` are isomorphisms for sufficiently positive `p`.  Then the Ext spectral
sequence of the filtration is bounded and converges to `Ext(M, K)`.

## Main definitions

* `extFromFilteredQuotient`: the canonical map from the Ext group of `M / F^p M` to that of `M`.

## Main results

* `extSpectralSequence_isBounded`: the Ext spectral sequence is bounded under the stated
  hypotheses.
* `extSpectralSequence_convergesToExt`: under the same hypotheses it converges to `Ext(M, K)`.

## Implementation notes

The equality of Ext groups in the source is expressed by invertibility of the canonical map
induced contravariantly by `M ⟶ M / F^p M`. Convergence identifies the infinity page with the
associated graded of the canonical
quotient-image filtration. Reversing its index by `p ↦ -p + 1` gives the decreasing filtration
on the cohomology of the filtered Hom complex, and implies `SpectralSequence.AbutsTo`.
The quotient is the existing `FilteredObject.quot` construction. Boundedness and convergence
are separate declarations because they are independent conclusions of the proposition.

## References

* [Stacks Project, Tag 0G1Z](https://stacks.math.columbia.edu/tag/0G1Z)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Injectives

attribute [local instance] HasDerivedCategory.standard

private noncomputable def equivShiftHom
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ] (G : C ⥤ D) [G.Additive] [G.IsEquivalence]
    [G.CommShift ℤ] {X Y : C} {X' Y' : D}
    (eX : G.obj X ≅ X') (eY : G.obj Y ≅ Y') (n : ℤ) :
    ShiftedHom X Y n ≃+ ShiftedHom X' Y' n :=
  (shiftedHomMapAddEquiv G X Y n).trans
    (shiftedHomIsoAddEquiv eX eY n)

private lemma equivShiftHom_precomp
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ] (G : C ⥤ D) [G.Additive] [G.IsEquivalence]
    [G.CommShift ℤ] {X Y K : C} {X' Y' K' : D}
    (eX : G.obj X ≅ X') (eY : G.obj Y ≅ Y') (eK : G.obj K ≅ K')
    (f : X ⟶ Y) (f' : X' ⟶ Y') (hf : G.map f ≫ eY.hom = eX.hom ≫ f')
    (n : ℤ) (x : ShiftedHom Y K n) :
    equivShiftHom G eX eK n (f ≫ x) = f' ≫ equivShiftHom G eY eK n x := by
  change eX.inv ≫ ShiftedHom.map (f ≫ x) G ≫ (shiftFunctor D n).map eK.hom = _
  rw [ShiftedHom.map, Functor.map_comp]
  have hf' : eX.inv ≫ G.map f = f' ≫ eY.inv := by
    calc
      eX.inv ≫ G.map f = eX.inv ≫ (G.map f ≫ eY.hom) ≫ eY.inv := by simp [Category.assoc]
      _ = eX.inv ≫ (eX.hom ≫ f') ≫ eY.inv := by rw [hf]
      _ = f' ≫ eY.inv := by simp [Category.assoc]
  calc
    eX.inv ≫ ((G.map f ≫ G.map x) ≫ (G.commShiftIso n).hom.app K) ≫
        (shiftFunctor D n).map eK.hom =
      (eX.inv ≫ G.map f) ≫
        (G.map x ≫ (G.commShiftIso n).hom.app K ≫ (shiftFunctor D n).map eK.hom) := by
          simp [Category.assoc]
    _ = f' ≫ equivShiftHom G eY eK n x := by
      rw [hf']
      dsimp [equivShiftHom]
      simp only [Category.assoc]
      congr 1
      dsimp [shiftedHomIsoAddEquiv,
        shiftedHomMapAddEquiv]
      change eY.inv ≫ G.map x ≫ (G.commShiftIso n).hom.app K ≫
          (shiftFunctor D n).map eK.hom =
        eY.inv ≫ (x.map G) ≫ (shiftFunctor D n).map eK.hom
      rw [ShiftedHom.map]
      simp only [Category.assoc]

private noncomputable def shrinkQuotientIso
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{w} A] (M : CochainComplex.Filtered A) (p : ℤ) :
    DerivedCategory.Q.obj
        (((ShrinkHoms.equivalence.{w} A).mapHomologicalComplex (ComplexShape.up ℤ)).functor.obj
          ((FilteredObject.quot (op p)).obj M)) ≅
      DerivedCategory.Q.obj
        ((FilteredObject.quot (op p)).obj
          (shrinkFilteredComplex M)) := by
  let eC := (ShrinkHoms.equivalence.{w} A).mapHomologicalComplex (ComplexShape.up ℤ)
  let := eC.isEquivalence_functor
  have : eC.functor.PreservesZeroMorphisms := by infer_instance
  have : PreservesColimitsOfShape WalkingParallelPair eC.functor := by infer_instance
  exact DerivedCategory.Q.mapIso
    (PreservesCokernel.iso eC.functor (M.filtration.ι.app (op p)))

private theorem shrinkQuotientIso_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{w} A] [(ShrinkHoms.equivalence.{w} A).functor.Additive]
    (M : CochainComplex.Filtered A) (q : ℤ) :
    let e := ShrinkHoms.equivalence.{w} A
    let G := e.functor.mapDerivedCategory
    let M' := shrinkFilteredComplex M
    let L := (FilteredObject.quot (op q)).obj M
    G.map (DerivedCategory.Q.map (FilteredObject.quotπ (op q) M)) ≫
      (e.functor.mapDerivedCategoryFactors.app L ≪≫ shrinkQuotientIso M q).hom =
      (e.functor.mapDerivedCategoryFactors.app M.X).hom ≫
        DerivedCategory.Q.map (FilteredObject.quotπ (op q) M') := by
  dsimp only
  let e := ShrinkHoms.equivalence.{w} A
  let M' := shrinkFilteredComplex M
  let L := (FilteredObject.quot (op q)).obj M
  let hqx := PreservesCokernel.iso
    (e.functor.mapHomologicalComplex (ComplexShape.up ℤ))
    (M.filtration.ι.app (op q))
  have hquotMap : (e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (FilteredObject.quotπ (op q) M) ≫ hqx.hom =
      FilteredObject.quotπ (op q) M' := by
    rw [FilteredObject.quotπ, PreservesCokernel.π_iso_hom]
    rfl
  have hn := e.functor.mapDerivedCategoryFactors_hom_naturality
    (FilteredObject.quotπ (op q) M)
  have hx : (e.functor.mapDerivedCategoryFactors.app L ≪≫ shrinkQuotientIso M q).hom =
      e.functor.mapDerivedCategoryFactors.hom.app L ≫ DerivedCategory.Q.map hqx.hom := by
    change e.functor.mapDerivedCategoryFactors.hom.app L ≫
      (DerivedCategory.Q.mapIso hqx).hom = _
    rw [Functor.mapIso_hom]
  have hQmap := congrArg DerivedCategory.Q.map hquotMap
  rw [Functor.map_comp] at hQmap
  rw [hx]
  -- The goal composes `G.map (Q.map _)`, whose target is `G.obj (Q.obj L)`, with a component of
  -- `mapDerivedCategoryFactors`, whose source is `(Q ⋙ G).obj L`; those agree only once
  -- `Functor.comp` unfolds, so the reassociation is supplied as a term rather than by `rw`.
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ DerivedCategory.Q.map hqx.hom) hn).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => e.functor.mapDerivedCategoryFactors.hom.app M.X ≫ z) hQmap)))


/-- The map `Ext^n(M / F^p M, K) ⟶ Ext^n(M, K)` induced by the quotient map. -/
public noncomputable def extFromFilteredQuotient
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (p n : ℤ) :
    AddCommGrpCat.of (DerivedCategory.Ext
      (DerivedCategory.Q.obj ((FilteredObject.quot (op p)).obj M)) K n) ⟶
      AddCommGrpCat.of (DerivedCategory.Ext (DerivedCategory.Q.obj M.X) K n) :=
  AddCommGrpCat.ofHom
    { toFun := fun f ↦ DerivedCategory.Q.map (FilteredObject.quotπ (op p) M) ≫ f
      map_zero' := by simp
      map_add' := by simp }

/-- If `e' ∘ f = g ∘ e` for equivalences `e` and `e'`, then `f` is bijective iff `g` is. -/
private theorem bijective_iff_of_comp_eq {α β γ δ E E' : Type*} [EquivLike E α γ]
    [EquivLike E' β δ] {f : α → β} {g : γ → δ} (e : E) (e' : E') (h : ∀ x, e' (f x) = g (e x)) :
    Function.Bijective f ↔ Function.Bijective g := by
  rw [← EquivLike.comp_bijective f e', ← EquivLike.bijective_comp e g]
  exact iff_of_eq (congrArg _ (funext h))

private theorem extFilteredHom_eventual_properties
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A)
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      IsZero (AddCommGrpCat.of (DerivedCategory.Ext
        (DerivedCategory.Q.obj ((FilteredObject.quot (op p)).obj M)) K n)))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p₁ ≤ p →
      IsIso (extFromFilteredQuotient K M p n)) :
    (∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (((extFilteredHom K M).filtration.obj (op p)).homology n)) ∧
    (∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap
        ((extFilteredHom K M).filtration.ι.app (op p)) n)) := by
  let e := ShrinkHoms.equivalence.{w} A
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let : e.functor.Additive := by
    change (ShrinkHoms.functor A).Additive
    infer_instance
  let G := e.functor.mapDerivedCategory
  let : G.IsEquivalence := mapDerivedCategory_isEquivalence e.functor
  let := HasDerivedCategory.standard (ShrinkHoms A)
  let M' := shrinkFilteredComplex M
  let K' := DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
  let N := filteredHomFilteredComplex (ShrinkHoms A) K' M'
  let kIso : G.obj K ≅ K' :=
    G.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      e.functor.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)
  let baseIso : G.obj (DerivedCategory.Q.obj M.X) ≅ DerivedCategory.Q.obj M'.X :=
    e.functor.mapDerivedCategoryFactors.app M.X
  have hzeroN : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((N.filtration.obj (op p)).homology n) := by
    intro n
    obtain ⟨q₀, hq₀⟩ := hzero n
    refine ⟨1 - q₀, ?_⟩
    intro p hp
    let q := -p + 1
    have hq : q ≤ q₀ := by dsimp [q]; omega
    let L := (FilteredObject.quot (op q)).obj M
    let L' := (FilteredObject.quot (op q)).obj M'
    let eX : G.obj (DerivedCategory.Q.obj L) ≅ DerivedCategory.Q.obj L' :=
      e.functor.mapDerivedCategoryFactors.app L ≪≫ shrinkQuotientIso M q
    let bridge := equivShiftHom G eX kIso n
    have hExtOrig : Subsingleton
        (DerivedCategory.Ext (DerivedCategory.Q.obj L) K n) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp (hq₀ q hq)
    have hExt : Subsingleton
        (DerivedCategory.Ext (DerivedCategory.Q.obj L') K' n) :=
      ⟨fun x y => bridge.symm.injective (hExtOrig.elim _ _)⟩
    let eStep := filteredHomComplexStepHomologyAddEquivExt
      (ShrinkHoms A) K' M' p n
    have hStep : Subsingleton
        ((filteredHomComplexStep (ShrinkHoms A) K' M' p).homology n) :=
      ⟨fun x y => eStep.injective (hExt.elim _ _)⟩
    have hSub : Subsingleton ((N.filtration.obj (op p)).homology n) :=
      ⟨fun x y => (HomologicalComplex.homologyMapIso
        (filteredHomComplexFiltrationStepIso (ShrinkHoms A) K' M' p)
          n).addCommGroupIsoToAddEquiv.injective (hStep.elim _ _)⟩
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr hSub
  have hisoN : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n) := by
    intro n
    obtain ⟨q₁, hq₁⟩ := hiso n
    refine ⟨1 - q₁, ?_⟩
    intro p hp
    let q := -p + 1
    have hq : q₁ ≤ q := by dsimp [q]; omega
    let L := (FilteredObject.quot (op q)).obj M
    let L' := (FilteredObject.quot (op q)).obj M'
    let eX : G.obj (DerivedCategory.Q.obj L) ≅ DerivedCategory.Q.obj L' :=
      e.functor.mapDerivedCategoryFactors.app L ≪≫ shrinkQuotientIso M q
    let eY := baseIso
    let bridgeX := equivShiftHom G eX kIso n
    let bridgeY := equivShiftHom G eY kIso n
    let f := DerivedCategory.Q.map (FilteredObject.quotπ (op q) M)
    let f' := DerivedCategory.Q.map (FilteredObject.quotπ (op q) M')
    have hnat : G.map f ≫ eX.hom = eY.hom ≫ f' :=
      shrinkQuotientIso_naturality M q
    let fShrink : AddCommGrpCat.of (DerivedCategory.Ext (DerivedCategory.Q.obj L') K' n) ⟶
        AddCommGrpCat.of (DerivedCategory.Ext (DerivedCategory.Q.obj M'.X) K' n) :=
      AddCommGrpCat.ofHom
        { toFun := fun x => f' ≫ x
          map_zero' := by simp
          map_add' := by simp }
    let fOrig := extFromFilteredQuotient K M q n
    have : IsIso (extFromFilteredQuotient K M q n) := hq₁ q hq
    have hmapNat (x : DerivedCategory.Ext (DerivedCategory.Q.obj L) K n) :
        bridgeY (fOrig.hom x) = fShrink.hom (bridgeX x) := by
      change bridgeY (f ≫ x) = f' ≫ bridgeX x
      exact equivShiftHom_precomp G eY eX kIso f f' hnat n x
    have hShrinkBij : Function.Bijective fShrink.hom :=
      (bijective_iff_of_comp_eq bridgeX bridgeY hmapNat).mp
        ((ConcreteCategory.isIso_iff_bijective fOrig).mp (inferInstance : IsIso fOrig))
    let stepIso := filteredHomComplexFiltrationStepIso
      (ShrinkHoms A) K' M' p
    let eStep := (HomologicalComplex.homologyMapIso stepIso n).addCommGroupIsoToAddEquiv.trans
      (filteredHomComplexStepHomologyAddEquivExt
        (ShrinkHoms A) K' M' p n)
    let eWhole := filteredHomComplexHomologyAddEquivExt
      (ShrinkHoms A) K' M' n
    let homMap := HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n
    have hcomm (x : (N.filtration.obj (op p)).homology n) :
        eWhole (homMap.hom x) = fShrink.hom (eStep x) := by
      change filteredHomComplexHomologyAddEquivExt
          (ShrinkHoms A) K' M' n
          (HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n x) =
        f' ≫ filteredHomComplexStepHomologyAddEquivExt
          (ShrinkHoms A) K' M' p n
          (HomologicalComplex.homologyMap stepIso.hom n x)
      exact filteredHomComplexHomologyAddEquivExt_ι
        (ShrinkHoms A) K' M' p n x
    have hHomBij : Function.Bijective homMap.hom :=
      (bijective_iff_of_comp_eq eStep eWhole hcomm).mpr hShrinkBij
    exact (ConcreteCategory.isIso_iff_bijective homMap).mpr hHomBij
  change (∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((N.filtration.obj (op p)).homology n)) ∧
    (∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n))
  exact ⟨hzeroN, hisoN⟩

private noncomputable def extHomologyEquiv
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (n : ℤ) :
    let e := ShrinkHoms.equivalence.{w} A
    let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
    let K' := DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
    let M' := shrinkFilteredComplex M
    let N := filteredHomFilteredComplex (ShrinkHoms A) K' M'
    N.X.homology n ≃+ DerivedCategory.Ext (DerivedCategory.Q.obj M.X) K n := by
  dsimp
  let e := ShrinkHoms.equivalence.{w} A
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let : e.functor.Additive := by
    change (ShrinkHoms.functor A).Additive
    infer_instance
  let G := e.functor.mapDerivedCategory
  let : G.IsEquivalence := mapDerivedCategory_isEquivalence e.functor
  let := HasDerivedCategory.standard (ShrinkHoms A)
  let M' := shrinkFilteredComplex M
  let K' := DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
  let baseIso : G.obj (DerivedCategory.Q.obj M.X) ≅
      DerivedCategory.Q.obj (eC.functor.obj M.X) :=
    e.functor.mapDerivedCategoryFactors.app M.X
  let kIso : G.obj K ≅ K' :=
    G.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      e.functor.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)
  exact (filteredHomComplexHomologyAddEquivExt
      (ShrinkHoms A) K' M' n).trans (equivShiftHom G baseIso kIso n).symm

private theorem extQuotientFiltration_eq_homologyImage
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (n p : ℤ) :
    let e := ShrinkHoms.equivalence.{w} A
    let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
    let K' := DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
    let M' := shrinkFilteredComplex M
    let N := filteredHomFilteredComplex (ShrinkHoms A) K' M'
    Subobject.mapIsoToOrderIso (AddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of (N.X.homology n))
      (Y := AddCommGrpCat.of (DerivedCategory.Ext (DerivedCategory.Q.obj M.X) K n))
      (extHomologyEquiv K M n))
        (imageSubobject (HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n)) =
          imageSubobject (extFromFilteredQuotient K M (-p + 1) n) := by
  dsimp
  let e := ShrinkHoms.equivalence.{w} A
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let : e.functor.Additive := by
    change (ShrinkHoms.functor A).Additive
    infer_instance
  let G := e.functor.mapDerivedCategory
  let : G.IsEquivalence := mapDerivedCategory_isEquivalence e.functor
  let := HasDerivedCategory.standard (ShrinkHoms A)
  let M' := shrinkFilteredComplex M
  let K' := DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
  let N := extFilteredHom K M
  let kIso : G.obj K ≅ K' :=
    G.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      e.functor.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)
  let baseIso : G.obj (DerivedCategory.Q.obj M.X) ≅
      DerivedCategory.Q.obj (eC.functor.obj M.X) :=
    e.functor.mapDerivedCategoryFactors.app M.X
  let q := -p + 1
  let L := (FilteredObject.quot (op q)).obj M
  let L' := (FilteredObject.quot (op q)).obj M'
  let eX : G.obj (DerivedCategory.Q.obj L) ≅ DerivedCategory.Q.obj L' :=
    e.functor.mapDerivedCategoryFactors.app L ≪≫ shrinkQuotientIso M q
  let eY := baseIso
  let f := DerivedCategory.Q.map (FilteredObject.quotπ (op q) M)
  let f' := DerivedCategory.Q.map (FilteredObject.quotπ (op q) M')
  have hnat : G.map f ≫ eX.hom = eY.hom ≫ f' :=
    shrinkQuotientIso_naturality M q
  let bridgeX := equivShiftHom G eX kIso n
  let bridgeY := equivShiftHom G baseIso kIso n
  let fOrig := extFromFilteredQuotient K M q n
  let fShrink : AddCommGrpCat.of (DerivedCategory.Ext
      (DerivedCategory.Q.obj L') K' n) ⟶
      AddCommGrpCat.of (DerivedCategory.Ext (DerivedCategory.Q.obj M'.X) K' n) :=
    AddCommGrpCat.ofHom
      { toFun := fun x => f' ≫ x
        map_zero' := by simp
        map_add' := by simp }
  have hmapNat (x : DerivedCategory.Ext (DerivedCategory.Q.obj L) K n) :
      bridgeY (fOrig.hom x) = fShrink.hom (bridgeX x) := by
    change bridgeY (f ≫ x) = f' ≫ bridgeX x
    exact equivShiftHom_precomp G baseIso eX kIso f f' hnat n x
  let stepIso := filteredHomComplexFiltrationStepIso
    (ShrinkHoms A) K' M' p
  let eStepShrunk := (HomologicalComplex.homologyMapIso stepIso n).addCommGroupIsoToAddEquiv.trans
    (filteredHomComplexStepHomologyAddEquivExt
      (ShrinkHoms A) K' M' p n)
  let eWholeShrunk := filteredHomComplexHomologyAddEquivExt
    (ShrinkHoms A) K' M' n
  let eWhole := eWholeShrunk.trans bridgeY.symm
  let eStep := eStepShrunk.trans bridgeX.symm
  let homMap := HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n
  have hcommShrink (x : (N.filtration.obj (op p)).homology n) :
      eWholeShrunk (homMap.hom x) = fShrink.hom (eStepShrunk x) :=
    filteredHomComplexHomologyAddEquivExt_ι
      (ShrinkHoms A) K' M' p n x
  have hcomm (x : (N.filtration.obj (op p)).homology n) :
      eWhole (homMap.hom x) = fOrig.hom (eStep x) := by
    change bridgeY.symm (eWholeShrunk (homMap.hom x)) =
      fOrig.hom (bridgeX.symm (eStepShrunk x))
    calc
      bridgeY.symm (eWholeShrunk (homMap.hom x)) =
          bridgeY.symm (fShrink.hom (eStepShrunk x)) :=
            congrArg bridgeY.symm (hcommShrink x)
      _ = fOrig.hom (bridgeX.symm (eStepShrunk x)) := by
        calc
          _ = bridgeY.symm
              (bridgeY (fOrig.hom (bridgeX.symm (eStepShrunk x)))) := by
                congr 1
                simpa using (hmapNat (bridgeX.symm (eStepShrunk x))).symm
          _ = fOrig.hom (bridgeX.symm (eStepShrunk x)) := by simp
  let eWholeCat := AddEquiv.toAddCommGrpIso
    (X := AddCommGrpCat.of (N.X.homology n))
    (Y := AddCommGrpCat.of (DerivedCategory.Ext (DerivedCategory.Q.obj M.X) K n)) eWhole
  let eStepCat := AddEquiv.toAddCommGrpIso
    (X := AddCommGrpCat.of ((N.filtration.obj (op p)).homology n))
    (Y := AddCommGrpCat.of (DerivedCategory.Ext
      (DerivedCategory.Q.obj ((FilteredObject.quot (op q)).obj M)) K n)) eStep
  have hmap : homMap ≫ eWholeCat.hom = eStepCat.hom ≫ fOrig :=
    AddCommGrpCat.hom_ext (AddMonoidHom.ext hcomm)
  have heWhole : eWhole = extHomologyEquiv K M n := rfl
  rw [← heWhole]
  change (Subobject.map eWholeCat.hom).obj (imageSubobject homMap) =
    imageSubobject fOrig
  calc
    (Subobject.map eWholeCat.hom).obj (imageSubobject homMap) =
        imageSubobject (homMap ≫ eWholeCat.hom) := Subobject.map_imageSubobject _ eWholeCat
    _ = imageSubobject (eStepCat.hom ≫ fOrig) :=
      congrArg (fun f => imageSubobject f) hmap
    _ = imageSubobject fOrig := imageSubobject_iso_comp eStepCat.hom fOrig

/-- The modular comparison `A/B ≅ (A ⊔ F)/(B ⊔ F)`, in the form in which the comparison of a
stable page with a graded piece of the filtration needs it: the numerator is `B` itself rather
than `(A ⊓ F) ⊔ B`, which the hypothesis `A ⊓ F ≤ B` identifies with `B`. -/
lemma nonempty_cokernel_sup_iso {C : Type*} [Category* C] [Abelian C]
    {X : C} (A B F : Subobject X) (hBA : B ≤ A) (hAF : A ⊓ F ≤ B) :
    Nonempty (cokernel (Subobject.ofLE B A hBA) ≅
      cokernel (Subobject.ofLE (B ⊔ F) (A ⊔ F) (sup_le_sup_right hBA F))) :=
  (Subobject.nonempty_cokernelOfLE_inf_sup_iso A F B hBA).map fun e =>
    Subobject.cokernelOfLEIsoOfEq hBA (sup_le inf_le_left hBA)
      (sup_eq_right.mpr hAF).symm rfl ≪≫ e

/-- An isomorphism `e : X ≅ Y` carries the quotient `Q / P` of two subobjects `P ≤ Q` of `X`
isomorphically onto the quotient of their images under `e`. -/
public noncomputable def subobjectQuotientMapIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasCokernels C]
    {X Y : C} (e : X ≅ Y) (P Q : Subobject X) (h : P ≤ Q) :
    cokernel (P.ofLE Q h) ≅
      cokernel ((Subobject.mapIsoToOrderIso e P).ofLE (Subobject.mapIsoToOrderIso e Q)
        ((Subobject.mapIsoToOrderIso e).map_rel_iff'.2 h)) :=
  cokernel.mapIso (P.ofLE Q h)
    ((Subobject.mapIsoToOrderIso e P).ofLE (Subobject.mapIsoToOrderIso e Q)
      ((Subobject.mapIsoToOrderIso e).map_rel_iff'.2 h))
    (Subobject.underlyingMapIso e P) (Subobject.underlyingMapIso e Q)
    (Subobject.underlyingMapIso_ofLE e P Q h)

/-- The canonical increasing filtration on Ext, given by the images of the quotient maps. -/
public noncomputable def extQuotientFiltration
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (n p : ℤ) :
    Subobject (AddCommGrpCat.of (DerivedCategory.Ext (DerivedCategory.Q.obj M.X) K n)) :=
  imageSubobject (extFromFilteredQuotient K M p n)

private theorem filteredHom_convergence_data
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A)
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ → IsZero (AddCommGrpCat.of (DerivedCategory.Ext
      (DerivedCategory.Q.obj ((FilteredObject.quot (op p)).obj M)) K n)))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p₁ ≤ p → IsIso (extFromFilteredQuotient K M p n)) :
    letI NC := extFilteredHom K M
    letI FF : ∀ (_p n : ℤ), Subobject (NC.X.X n) := CochainComplex.filtrationSubobject NC
    letI EE := CochainComplex.filteredSpectralSequence NC
    letI FHH : ∀ (n _p : ℤ), Subobject (NC.X.homology n) := fun n p =>
      imageSubobject (HomologicalComplex.homologyMap (NC.filtration.ι.app (op p)) n)
    (∀ n : ℤ, {p : ℤ | ¬ IsZero ((EE.page 1 (by omega)).X (p, n - p))}.Finite) ∧
    (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FHH n a = ⊤ ∧ FHH n b = ⊥) ∧
    (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (EE.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
    (∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ =>
          FF p n ⊓ (Subobject.pullback (NC.X.d n (n + 1))).obj (FF (p + r) (n + 1)) ⊔
            FF (p + 1) n)
        (kernelSubobject (NC.X.d n (n + 1)) ⊓ FF p n ⊔ FF (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ =>
          FF p n ⊓ (Subobject.«exists» (NC.X.d (n - 1) n)).obj (FF (p - r) (n - 1)) ⊔
            FF (p + 1) n)
        (imageSubobject (NC.X.d (n - 1) n) ⊓ FF p n ⊔ FF (p + 1) n)) ∧
    (∀ p n : ℤ,
      let C := (Subobject.pullback (NC.X.iCycles n)).obj (FF p n)
      let N := kernelSubobject (NC.X.d n (n + 1)) ⊓ FF p n ⊔ FF (p + 1) n
      let B := imageSubobject (NC.X.d (n - 1) n) ⊓ FF p n ⊔ FF (p + 1) n
      ∃ (a : (C : AddCommGrpCat.{w}) ⟶ (N : AddCommGrpCat.{w}))
        (b : (C : AddCommGrpCat.{w}) ⟶ image (HomologicalComplex.homologyMap
          (NC.filtration.ι.app (op p)) n))
        (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
          cokernel (image.preComp
            (HomologicalComplex.homologyMap (NC.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
            (HomologicalComplex.homologyMap (NC.filtration.ι.app (op p)) n))),
        C.arrow ≫ NC.X.iCycles n = a ≫ N.arrow ∧
        C.arrow ≫ NC.X.homologyπ n =
          b ≫ image.ι (HomologicalComplex.homologyMap
            (NC.filtration.ι.app (op p)) n) ∧
        a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
          b ≫ cokernel.π (image.preComp
            (HomologicalComplex.homologyMap (NC.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
            (HomologicalComplex.homologyMap
              (NC.filtration.ι.app (op p)) n))) := by
  obtain ⟨hzeroN, hisoN⟩ := extFilteredHom_eventual_properties K M hzero hiso
  let NC := extFilteredHom K M
  let F := CochainComplex.filtrationSubobject NC
  let Z := FilteredComplexSpectralSequence.cycles NC.X F
  let D := FilteredComplexSpectralSequence.boundaries NC.X F
  let FH : ∀ n p : ℤ, Subobject (NC.X.homology n) := fun n p =>
    imageSubobject (HomologicalComplex.homologyMap (NC.filtration.ι.app (op p)) n)
  let hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n :=
    fun p p' n hp => CochainComplex.filtrationSubobject_antitone NC p p' n hp
  let E := CochainComplex.filteredSpectralSequence NC
  have hE (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) :
      (E.page r (by omega)).X (p, q) ≅
        cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) := by
    subst hn
    exact FilteredComplexSpectralSequence.eIso NC.X F hanti r p q (p + q) (by omega) rfl
  exact CochainComplex.isBounded_and_converges_of_eventually_isZero_of_eventually_isIso NC F
    (fun _ _ => rfl) Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl) FH (fun _ _ => rfl)
    E hE hzeroN hisoN

/-- **Stacks 0G1Z, boundedness.** Under eventual vanishing and eventual comparison-isomorphism
for Ext from the filtered quotients, the Ext spectral sequence is bounded. -/
@[stacks 0G1Z "boundedness"]
public theorem extSpectralSequence_isBounded
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A)
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      IsZero (AddCommGrpCat.of (DerivedCategory.Ext
        (DerivedCategory.Q.obj ((FilteredObject.quot (op p)).obj M)) K n)))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p₁ ≤ p →
      IsIso (extFromFilteredQuotient K M p n)) :
    IsBounded (extSpectralSequence K M).1 := by
  rw [extSpectralSequence_fst]
  exact (filteredHom_convergence_data K M hzero hiso).1

/-- **Stacks 0G1Z, convergence.** Under eventual vanishing and eventual
comparison-isomorphism for Ext from the filtered quotients, the Ext spectral sequence converges
to the Ext groups from the underlying complex, with the canonical quotient-image filtration.
The graded quotient at `(p,q)` is the step from `-p` to `-p + 1`. -/
@[stacks 0G1Z "convergence"]
public theorem extSpectralSequence_convergesToExt
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A)
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      IsZero (AddCommGrpCat.of (DerivedCategory.Ext
        (DerivedCategory.Q.obj ((FilteredObject.quot (op p)).obj M)) K n)))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p₁ ≤ p →
      IsIso (extFromFilteredQuotient K M p n)) :
    let E := (extSpectralSequence K M).1
    ∃ hF : ∀ n : ℤ, Monotone (extQuotientFiltration K M n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ extQuotientFiltration K M n a = ⊥ ∧
        extQuotientFiltration K M n b = ⊤) ∧
      (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
      ∀ p q : ℤ, Nonempty
        (E.pageInfinity (p, q) ≅
          cokernel (Subobject.ofLE (extQuotientFiltration K M (p + q) (-p))
            (extQuotientFiltration K M (p + q) (-p + 1)) (hF (p + q) (by omega)))) := by
  dsimp only
  rw [extSpectralSequence_fst]
  let eC := (ShrinkHoms.equivalence.{w} A).mapHomologicalComplex (ComplexShape.up ℤ)
  let := HasDerivedCategory.standard (ShrinkHoms A)
  let K' := DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
  let M' := shrinkFilteredComplex M
  let N := filteredHomFilteredComplex (ShrinkHoms A) K' M'
  have hN : extFilteredHom K M = N := rfl
  let F := CochainComplex.filtrationSubobject N
  let Z := FilteredComplexSpectralSequence.cycles N.X F
  let D := FilteredComplexSpectralSequence.boundaries N.X F
  let FH : ∀ n p : ℤ, Subobject (N.X.homology n) := fun n p =>
    imageSubobject (HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n)
  let E0 := CochainComplex.filteredSpectralSequence N
  obtain ⟨hpageFinite, hfinite, _, _, hcompat⟩ :=
    filteredHom_convergence_data K M hzero hiso
  obtain ⟨hzeroN, hisoN⟩ := extFilteredHom_eventual_properties K M hzero hiso
  let hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n :=
    fun p p' n hp => CochainComplex.filtrationSubobject_antitone N p p' n hp
  let E1 := extFilteredHomSpectralSequence K M
  have hpageFinite1 : ∀ n : ℤ,
      {p : ℤ | ¬ IsZero ((E1.page 1).X (p, n - p))}.Finite := by
    intro n
    change {p : ℤ | ¬ IsZero
      (((CochainComplex.filteredSpectralSequence
        (extFilteredHom K M)).page 1 (by omega)).X
          (p, n - p))}.Finite
    rw [hN]
    exact hpageFinite n
  have hιcomp (n p p' : ℤ) (hp : p ≤ p') :
      HomologicalComplex.homologyMap (N.filtration.diagram.map (homOfLE hp).op) n ≫
          HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n =
        HomologicalComplex.homologyMap (N.filtration.ι.app (op p')) n := by
    rw [← HomologicalComplex.homologyMap_comp]
    congr 1
    exact N.filtration.diagram_map_comp_ι_app (homOfLE hp).op
  have hFHanti : ∀ n p p' : ℤ, p ≤ p' → FH n p' ≤ FH n p := by
    intro n p p' hp
    rw [show FH n p' = imageSubobject
        (HomologicalComplex.homologyMap (N.filtration.ι.app (op p')) n) by rfl, ← hιcomp n p p' hp]
    exact imageSubobject_comp_le _ _
  let ψ (n : ℤ) := AddEquiv.toAddCommGrpIso
    (X := AddCommGrpCat.of (N.X.homology n))
    (Y := AddCommGrpCat.of (DerivedCategory.Ext (DerivedCategory.Q.obj M.X) K n))
    (extHomologyEquiv K M n)
  let φ (n : ℤ) := Subobject.mapIsoToOrderIso (ψ n)
  have hFilEq (n k : ℤ) : φ n (FH n k) =
      extQuotientFiltration K M n (-k + 1) := by
    simpa only [N, φ, ψ, FH, extQuotientFiltration, Subobject.mapIsoToOrderIso] using
      extQuotientFiltration_eq_homologyImage K M n k
  have hF : ∀ n : ℤ, Monotone (extQuotientFiltration K M n) := by
    intro n s t hst
    calc
      extQuotientFiltration K M n s = φ n (FH n (-s + 1)) := by
        simpa using (hFilEq n (-s + 1)).symm
      _ ≤ φ n (FH n (-t + 1)) :=
        (φ n).monotone (hFHanti n (-t + 1) (-s + 1) (by omega))
      _ = extQuotientFiltration K M n t := by simpa using hFilEq n (-t + 1)
  have hfiniteExt : ∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧
      extQuotientFiltration K M n a = ⊥ ∧ extQuotientFiltration K M n b = ⊤ := by
    intro n
    obtain ⟨a, b, hab, ha, hb⟩ := hfinite n
    change FH n a = ⊤ at ha
    change FH n b = ⊥ at hb
    refine ⟨-b + 1, -a + 1, by omega, ?_, ?_⟩
    · rw [← hFilEq n b, hb]
      exact (φ n).map_bot
    · rw [← hFilEq n a, ha]
      exact (φ n).map_top
  have hInfinity0 (p q : ℤ) : E0.HasPageInfinityAt (p, q) :=
    CategoryTheory.SpectralSequence.hasPageInfinityAt_of_finite_page E0 1 (by omega)
      hpageFinite (p, q)
  have hInfinity1 (p q : ℤ) : E1.HasPageInfinityAt (p, q) :=
    CategoryTheory.SpectralSequence.hasPageInfinityAt_of_finite_page E1 1 (by omega)
      hpageFinite1 (p, q)
  refine ⟨hF, hfiniteExt, hInfinity1, ?_⟩
  intro p q
  let n := p + q
  let transition := HomologicalComplex.homologyMap
    (N.filtration.diagram.map (homOfLE (show p ≤ p + 1 by omega)).op) n
  let inclusion := HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n
  have hcomp : transition ≫ inclusion =
      HomologicalComplex.homologyMap (N.filtration.ι.app (op (p + 1))) n :=
    hιcomp n p (p + 1) (by omega)
  let P := imageSubobject (transition ≫ inclusion)
  let Q := imageSubobject inclusion
  have hP' : P = FH n (p + 1) := by
    dsimp [P, FH]
    rw [hcomp]
  have hQ' : Q = FH n p := rfl
  have hPQ : P ≤ Q := imageSubobject_comp_le transition inclusion
  have hP : φ n P = extQuotientFiltration K M n (-p) := by
    rw [hP']
    simpa using hFilEq n (p + 1)
  have hQ : φ n Q = extQuotientFiltration K M n (-p + 1) := by
    rw [hQ']
    simpa using hFilEq n p
  let eP := Subobject.isoOfEq (φ n P) (extQuotientFiltration K M n (-p)) hP
  let eQ := Subobject.isoOfEq (φ n Q) (extQuotientFiltration K M n (-p + 1)) hQ
  have heP : eP.hom ≫ (extQuotientFiltration K M n (-p)).arrow = (φ n P).arrow :=
    Subobject.ofLE_arrow hP.le
  have heQ : eQ.hom ≫ (extQuotientFiltration K M n (-p + 1)).arrow = (φ n Q).arrow :=
    Subobject.ofLE_arrow hQ.le
  let g := Subobject.ofLE (extQuotientFiltration K M n (-p))
    (extQuotientFiltration K M n (-p + 1)) (hF n (by omega))
  have hsq : (φ n P).ofLE (φ n Q) ((φ n).map_rel_iff'.2 hPQ) ≫ eQ.hom =
      eP.hom ≫ g := by
    apply (cancel_mono (extQuotientFiltration K M n (-p + 1)).arrow).1
    calc
      ((φ n P).ofLE (φ n Q) ((φ n).map_rel_iff'.2 hPQ) ≫ eQ.hom) ≫
          (extQuotientFiltration K M n (-p + 1)).arrow =
        (φ n P).ofLE (φ n Q) ((φ n).map_rel_iff'.2 hPQ) ≫ (φ n Q).arrow := by
          rw [Category.assoc, heQ]
      _ = (φ n P).arrow := Subobject.ofLE_arrow ((φ n).map_rel_iff'.2 hPQ)
      _ = eP.hom ≫ (extQuotientFiltration K M n (-p)).arrow := heP.symm
      _ = (eP.hom ≫ g) ≫ (extQuotientFiltration K M n (-p + 1)).arrow := by
        rw [Category.assoc, Subobject.ofLE_arrow]
  let eImg := Subobject.cokernelImagePreCompIso transition inclusion
  obtain ⟨_, _, eStable, _, _, _⟩ := hcompat p n
  let Zinf := kernelSubobject (N.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
  let Binf := imageSubobject (N.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
  let : E0.HasPageInfinityAt (p, q) := hInfinity0 p q
  let : E1.HasPageInfinityAt (p, q) := hInfinity1 p q
  let R := max (E0.rMin (p, q)) (E1.rMin (p, q))
  have hR0 : E0.rMin (p, q) ≤ R := le_max_left _ _
  have hR1 : E1.rMin (p, q) ≤ R := le_max_right _ _
  obtain ⟨b, hb⟩ := hzeroN (n + 1)
  obtain ⟨a, ha⟩ := hisoN n
  let S := max R (max (b - p) (p + 1 - a))
  have hS0 : E0.rMin (p, q) ≤ S := le_trans hR0 (le_max_left _ _)
  have hS1 : E1.rMin (p, q) ≤ S := le_trans hR1 (le_max_left _ _)
  have hSb : b ≤ p + S := by dsimp [S]; omega
  have hSa : p - S + 1 ≤ a := by dsimp [S]; omega
  have hSpos : 1 ≤ S := by
    have h : 1 ≤ E1.rMin (p, q) := by simpa using E1.LE_rMin (p, q)
    omega
  have hcycleSup : Z S p n ⊔ F (p + 1) n =
      kernelSubobject (N.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n := by
    let : Mono (HomologicalComplex.homologyMap
        (N.filtration.ι.app (op (p + S))) (n + 1)) := (hb (p + S) hSb).mono _
    change F p n ⊓ (Subobject.pullback (N.X.d n (n + 1))).obj
      (F (p + S) (n + 1)) ⊔ F (p + 1) n = _
    exact CochainComplex.cycles_sup_eq_of_mono_homologyMap N F
      (fun _ _ => rfl) p (p + S) n (by omega)
  have hsecondBoundary : (Subobject.exists (N.X.d (n - 1) n)).obj
      (Z (S - 1) (p - S + 1) (n - 1)) =
      F p n ⊓ (Subobject.exists (N.X.d (n - 1) n)).obj (F (p - S + 1) (n - 1)) := by
    dsimp only [Z, FilteredComplexSpectralSequence.cycles]
    rw [show n - 1 + 1 = n by omega,
      show p - S + 1 + (S - 1) = p by omega]
    rw [Regular.exists_inf_pullback_eq_exists_inf]
    simp [inf_comm]
  have hfirstLE : Z (S - 1) (p + 1) n ≤ F (p + 1) n :=
    FilteredComplexSpectralSequence.cycles_le_F N.X F (S - 1) (p + 1) n
  let : IsIso (HomologicalComplex.homologyMap
      (N.filtration.ι.app (op (p - S + 1))) n) := ha _ hSa
  have hBoundariesInf := CochainComplex.boundaries_inf_eq_of_mono_homologyMap N F
    (fun _ _ => rfl) p (p - S + 1) n (by omega)
  have hDformula : D S p n = Z (S - 1) (p + 1) n ⊔
      (imageSubobject (N.X.d (n - 1) n) ⊓ F p n) := by
    rw [show S = (S - 1) + 1 by omega]
    dsimp only [D, Z]
    have hsecondBoundary' : (Subobject.exists (N.X.d (n - 1) n)).obj
        (FilteredComplexSpectralSequence.cycles N.X F (S - 1) (p - (S - 1)) (n - 1)) =
        F p n ⊓ (Subobject.exists (N.X.d (n - 1) n)).obj (F (p - S + 1) (n - 1)) := by
      simpa only [show p - (S - 1) = p - S + 1 by omega] using hsecondBoundary
    rw [FilteredComplexSpectralSequence.boundaries_succ_eq, hsecondBoundary']
    rw [show (S - 1) + 1 - 1 = S - 1 by omega, hBoundariesInf]
  have hboundarySup : D S p n ⊔ F (p + 1) n =
      imageSubobject (N.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n := by
    rw [hDformula]
    exact le_antisymm (sup_le (sup_le (hfirstLE.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  let U := Z S p n
  let H := F (p + 1) n
  let A0 := imageSubobject (N.X.d (n - 1) n) ⊓ F p n
  have hA0U : A0 ≤ U := by
    apply le_inf inf_le_right
    apply (CategoryTheory.Subobject.le_pullback_iff _ _ _).2
    have hzero : A0.arrow ≫ N.X.d n (n + 1) = 0 := by
      rw [← Subobject.ofLE_arrow inf_le_left,
        Category.assoc, imageSubobject_arrow_comp_eq_zero (N.X.d_comp_d _ _ _)]
      simp
    rw [hzero]
    exact Subobject.factors_zero
  have hHUle : H ⊓ U ≤ D S p n := by
    have hUpull : U ≤ (Subobject.pullback (N.X.d n (n + 1))).obj
        (F (p + S) (n + 1)) := by
      change Z S p n ≤ (Subobject.pullback (N.X.d n (n + 1))).obj
        (F (p + S) (n + 1))
      exact inf_le_right
    have hcycle : H ⊓ U ≤ Z (S - 1) (p + 1) n :=
      FilteredComplexSpectralSequence.le_cycles N.X F
        (by simp [H])
        (by simpa only [show p + 1 + (S - 1) = p + S by omega] using
          le_trans inf_le_right hUpull)
    dsimp only [D, Z]
    rw [show S = (S - 1) + 1 by omega,
      FilteredComplexSpectralSequence.boundaries_succ_eq]
    exact le_sup_of_le_left hcycle
  have hBinfU : Binf ⊓ U ≤ D S p n := by
    have hmod : (A0 ⊔ H) ⊓ U = A0 ⊔ (H ⊓ U) :=
      sup_inf_assoc_of_le _ hA0U
    rw [show Binf = A0 ⊔ H by rfl, hmod]
    exact sup_le (by rw [hDformula]; exact le_sup_right) hHUle
  have hDleBinf : D S p n ≤ Binf := by
    change D S p n ≤ A0 ⊔ H
    rw [← hboundarySup]
    exact le_sup_left
  have hDU : D S p n ⊓ U = Binf ⊓ U :=
    le_antisymm (inf_le_inf hDleBinf le_rfl) (le_inf hBinfU inf_le_right)
  have hZinf : Zinf = U ⊔ H := by
    dsimp [Zinf, U, H]
    exact hcycleSup.symm
  have hBinfStable : Binf ⊓ Zinf = (D S p n ⊓ U) ⊔ H := by
    have hHinf : H ≤ Binf := by
      dsimp [H, Binf, A0]
      exact le_sup_right
    have hmod : Binf ⊓ Zinf = (Binf ⊓ U) ⊔ H := by
      rw [hZinf]
      exact (inf_sup_assoc_of_le U hHinf).symm
    rw [hmod, hDU]
  have hHUle' : U ⊓ H ≤ D S p n ⊓ U := by
    rw [inf_comm U H]
    exact le_inf hHUle inf_le_right
  obtain ⟨eAdd⟩ := nonempty_cokernel_sup_iso U (D S p n ⊓ U) H inf_le_right hHUle'
  have eStablePage : cokernel (Subobject.ofLE (D S p n ⊓ U) U inf_le_right) ≅
      cokernel (Subobject.ofLE (Binf ⊓ Zinf) Zinf inf_le_right) :=
    eAdd ≪≫ Subobject.cokernelOfLEIsoOfEq
      (sup_le_sup_right inf_le_right H) inf_le_right hBinfStable.symm hZinf.symm
  have hEStable : (E0.page S (by omega)).X (p, q) ≅
      cokernel (Subobject.ofLE (D S p n ⊓ Z S p n) (Z S p n) inf_le_right) := by
    dsimp [n]
    exact FilteredComplexSpectralSequence.eIso N.X F hanti S p q (p + q) (by omega) rfl
  have hpageEq : (E1.page R ((E1.LE_rMin (p, q)).trans hR1)).X (p, q) =
      (E0.page R ((E0.LE_rMin (p, q)).trans hR0)).X (p, q) := rfl
  let eInfinity : E1.pageInfinity (p, q) ≅ E0.pageInfinity (p, q) :=
    E1.pageInfinityIso (p, q) R ≪≫ eqToIso hpageEq ≪≫
      (E0.pageInfinityIso (p, q) R).symm
  let eStableToFH := E0.pageInfinityIso (p, q) S ≪≫ hEStable ≪≫
    eStablePage ≪≫ eStable ≪≫ eImg
  let eFHToExt := subobjectQuotientMapIso (ψ n) P Q hPQ ≪≫
    cokernel.mapIso
      ((φ n P).ofLE (φ n Q) ((φ n).map_rel_iff'.2 hPQ)) g eP eQ hsq
  exact ⟨eInfinity ≪≫ eStableToFH ≪≫ eFHToExt⟩

/-- Forgetting the specified quotient-image filtration recovers the abstract abutment. -/
public theorem extSpectralSequence_abutsToExt
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A)
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      IsZero (AddCommGrpCat.of (DerivedCategory.Ext
        (DerivedCategory.Q.obj ((FilteredObject.quot (op p)).obj M)) K n)))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p₁ ≤ p →
      IsIso (extFromFilteredQuotient K M p n)) :
    SpectralSequence.AbutsTo (extSpectralSequence K M).1
      (fun n ↦ AddCommGrpCat.of
        (DerivedCategory.Ext (DerivedCategory.Q.obj M.X) K n)) := by
  obtain ⟨hF, hfinite, hInf, hgraded⟩ := extSpectralSequence_convergesToExt K M hzero hiso
  refine ⟨hInf, (fun n p => extQuotientFiltration K M n (-p + 1)),
    (fun n p q hpq => hF n (by omega)), ?_, ?_⟩
  · intro n
    obtain ⟨a, b, hab, ha, hb⟩ := hfinite n
    refine ⟨-b + 1, -a + 1, by omega, ?_, ?_⟩
    · simpa using hb
    · simpa using ha
  · intro p q
    have hquot : ∀ (a b : ℤ), a = b →
        ∀ (ha : extQuotientFiltration K M (p + q) a ≤
            extQuotientFiltration K M (p + q) (-p + 1))
          (hb : extQuotientFiltration K M (p + q) b ≤
            extQuotientFiltration K M (p + q) (-p + 1)),
        cokernel (Subobject.ofLE _ _ ha) = cokernel (Subobject.ofLE _ _ hb) := by
      rintro a b rfl ha hb
      rfl
    obtain ⟨e⟩ := hgraded p q
    exact ⟨e ≪≫ eqToIso (hquot (-p) (-(p + 1) + 1) (by omega) _ _)⟩

end Stacks.Injectives

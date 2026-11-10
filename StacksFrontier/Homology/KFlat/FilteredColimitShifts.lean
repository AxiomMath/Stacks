module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Localization.FiniteProducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Split filtered resolutions and generation of the derived category by shifts of the ring

Let `R` be a ring. Every cochain complex of `R`-modules receives a quasi-isomorphism from a
complex carrying an exhaustive filtration whose successive inclusions split degreewise and
whose graded pieces are coproducts of shifts of the regular module. The filtration produces the
canonical mapping-telescope distinguished triangle in the derived category. Consequently a
property of objects of `D(R)` which is closed under coproducts, satisfies two-out-of-three for
distinguished triangles, and holds for every shift of `R`, holds for every object of `D(R)`:
the shifts of `R` generate `D(R)` under coproducts and distinguished triangles. This is the
remark of Stacks 09PB refining the K-flat resolution of Stacks 06Y4.

## Main definitions

* `CochainComplex.KFlat.SplitFilteredFreeResolution`: the filtered resolution of Stacks 09PB
  together with its canonical mapping-telescope triangle.

## Main results

* `CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts`: every complex of
  `R`-modules admits a `SplitFilteredFreeResolution`, and every property of objects of `D(R)`
  closed under coproducts, satisfying two-out-of-three for distinguished triangles and holding
  on all shifts of `R`, holds on all of `D(R)`.

## Implementation notes

The stage `F (-1) = 0` is represented by the separate description of `F 0` as a coproduct of
shifts. Successive quotients are represented by short exact sequences of complexes. The
telescope maps are characterized on the coproduct injections; this records their canonical
naturality without choosing an implementation of coproducts. The regular module is transported
into the independent module universe using `Shrink`; the smallness hypothesis makes this a
linearly equivalent copy of `R`.

Proving that the telescope triangle is distinguished needs `DerivedCategory.Q` to preserve
coproducts of arbitrary shape; this is established here by transporting coproducts through the
homotopy category and the localization, which is the bulk of the private
`CoproductBridge` namespace.

## References

* [The Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

attribute [local instance] HasDerivedCategory.standard

open Stacks.HomologyColimit

namespace CochainComplex.KFlat

universe u v w

/-- The split filtered resolution occurring in Stacks Project, Tag 09PB, including its canonical
mapping-telescope triangle. The maps `toP p` exhibit the stages as subcomplexes of `P`, and
`alpha_ι` and `beta_ι` characterize the two telescope maps on every summand. -/
structure SplitFilteredFreeResolution {R : Type u} [Ring R] [Small.{v} R]
    (M : CochainComplex (ModuleCat.{v} R) ℤ) where
  /-- The complex resolving `M`. -/
  P : CochainComplex (ModuleCat.{v} R) ℤ
  /-- The quasi-isomorphism from the resolution. -/
  f : P ⟶ M
  /-- The map `f` is a quasi-isomorphism. -/
  quasiIso : QuasiIso f
  /-- The nonnegative stages of the filtration. -/
  F : ℕ → CochainComplex (ModuleCat.{v} R) ℤ
  /-- The inclusion of one filtration stage in the next. -/
  inclusion : ∀ p, F p ⟶ F (p + 1)
  /-- The inclusion of each filtration stage in `P`. -/
  toP : ∀ p, F p ⟶ P
  inclusion_toP : ∀ p, inclusion p ≫ toP (p + 1) = toP p
  /-- Each inclusion `F p ⟶ P` is injective in every degree. -/
  toP_injective : ∀ p n, Function.Injective ((toP p).f n)
  /-- Each successive inclusion is split in every degree. -/
  inclusion_split : ∀ p n, IsSplitMono ((inclusion p).f n)
  /-- The filtration is exhaustive in every degree. -/
  exhaustive : ∀ n (x : P.X n), ∃ p, ∃ y : (F p).X n, (toP p).f n y = x
  /-- The quotient complex `F (p + 1) / F p`. -/
  quotient : ℕ → CochainComplex (ModuleCat.{v} R) ℤ
  /-- The projection `F (p + 1) ⟶ F (p + 1) / F p`. -/
  quotientMap : ∀ p, F (p + 1) ⟶ quotient p
  inclusion_quotientMap : ∀ p, inclusion p ≫ quotientMap p = 0
  /-- The sequence `F p ⟶ F (p + 1) ⟶ F (p + 1) / F p` is short exact. -/
  quotient_shortExact : ∀ p,
    (ShortComplex.mk (inclusion p) (quotientMap p) (inclusion_quotientMap p)).ShortExact
  /-- The shifts occurring in `F 0 = F 0 / F (-1)`. -/
  bottomShiftIndex : Type v
  /-- The shift of the summand of `F 0` indexed by each element of `bottomShiftIndex`. -/
  bottomShiftAmount : bottomShiftIndex → ℤ
  bottomIso : F 0 ≅ ∐ (fun j : bottomShiftIndex =>
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj
      (ModuleCat.of R (Shrink.{v} R)))
      ⟦bottomShiftAmount j⟧)
  /-- The shifts occurring in each successive quotient. -/
  shiftIndex : ℕ → Type v
  /-- The shift of the summand of the `p`-th quotient indexed by each element of `shiftIndex p`. -/
  shiftAmount : ∀ p, shiftIndex p → ℤ
  quotientIso : ∀ p, quotient p ≅ ∐ (fun j : shiftIndex p =>
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj
      (ModuleCat.of R (Shrink.{v} R)))
      ⟦shiftAmount p j⟧)
  /-- A chosen model for the coproduct of all filtration stages. -/
  telescope : CochainComplex (ModuleCat.{v} R) ℤ
  /-- The identification of `telescope` with the coproduct of the stages `F p`. -/
  telescopeIso : telescope ≅ ∐ F
  /-- The map `1 - shift` on the telescope. -/
  alpha : telescope ⟶ telescope
  /-- The map from the telescope induced by all inclusions `F p ⟶ P`. -/
  beta : telescope ⟶ P
  alpha_ι : ∀ p, Sigma.ι F p ≫ telescopeIso.inv ≫ alpha =
    Sigma.ι F p ≫ telescopeIso.inv -
      inclusion p ≫ Sigma.ι F (p + 1) ≫ telescopeIso.inv
  beta_ι : ∀ p, Sigma.ι F p ≫ telescopeIso.inv ≫ beta = toP p
  /-- The connecting morphism of the telescope triangle after replacing `P` by `M`. -/
  delta : DerivedCategory.Q.obj M ⟶ (DerivedCategory.Q.obj telescope)⟦(1 : ℤ)⟧
  telescope_distinguished : Triangle.mk (DerivedCategory.Q.map alpha)
    (DerivedCategory.Q.map (beta ≫ f)) delta ∈ distinguishedTriangles


set_option backward.isDefEq.respectTransparency false in
private theorem property_of_iso
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    (T : C → Prop)
    (htri : ∀ Δ : Triangle C, Δ ∈ distinguishedTriangles →
      (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧
      (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂))
    {X Y : C} (e : X ≅ Y) (hX : T X) : T Y := by
  have hzero : T (0 : C) :=
    (htri _ (contractible_distinguished X)).1 hX hX
  let Δ := Triangle.mk e.hom (0 : Y ⟶ 0) 0
  have hΔ : Δ ∈ distinguishedTriangles :=
    isomorphic_distinguished _ (contractible_distinguished X) _
      (Triangle.isoMk Δ (contractibleTriangle X) (Iso.refl _) e.symm (Iso.refl _)
        (by simp [Δ]) (by simp [Δ]) (by simp [Δ]))
  exact (htri Δ hΔ).2 hX hzero

private theorem property_coproduct_of_small
    {C : Type*} [Category* C] (T : C → Prop)
    (hiso : ∀ {X Y : C}, (X ≅ Y) → T X → T Y)
    (hsum : ∀ {I : Type v} (K : I → C) [HasCoproduct K],
      (∀ i, T (K i)) → T (∐ K))
    {I : Type w} [Small.{v} I] (K : I → C) [HasCoproduct K]
    (hK : ∀ i, T (K i)) : T (∐ K) := by
  let e := (equivShrink.{v} I).symm
  let L := K ∘ e
  have : HasCoproduct L := hasCoproduct_of_equiv_of_iso K L e (fun _ => Iso.refl _)
  exact hiso (Sigma.reindex e K) (hsum L (fun i => hK (e i)))

private theorem property_map_coproduct
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) (T : D → Prop)
    (hiso : ∀ {X Y : D}, (X ≅ Y) → T X → T Y)
    (hsum : ∀ {I : Type v} (K : I → D) [HasCoproduct K],
      (∀ i, T (K i)) → T (∐ K))
    {I : Type w} [Small.{v} I] (K : I → C) [HasCoproduct K]
    [PreservesColimit (Discrete.functor K) G]
    (hK : ∀ i, T (G.obj (K i))) : T (G.obj (∐ K)) := by
  have : HasCoproduct (fun i => G.obj (K i)) :=
    ⟨_, isColimitOfHasCoproductOfPreservesColimit G K⟩
  exact hiso (PreservesCoproduct.iso G K).symm
    (property_coproduct_of_small T hiso hsum _ hK)

namespace CoproductBridge

set_option backward.isDefEq.respectTransparency false

universe t

/-- `A` has exact coproducts indexed by the types of a universe: all such coproducts exist, and
each coproduct functor `colim : (Discrete J ⥤ A) ⥤ A` is exact.

This is Grothendieck's axiom AB4 for the index universe `t₁`, packaged as data rather than as a
typeclass so that it can be supplied at a universe chosen by the caller. A Grothendieck abelian
category satisfies it in its own Grothendieck universe: `HasCoproducts` and
`AB4OfSize.ofShape` are then both instances. -/
structure HasExactCoproducts.{t₁, u₁, v₁}
    (A : Type u₁) [Category.{v₁} A] [Abelian A] : Prop where

  /-- Coproducts indexed by the types of the universe `t₁` exist in `A`. -/
  hasCoproducts : HasCoproducts.{t₁} A

  /-- Each coproduct functor is exact: it preserves finite limits as well as the finite colimits
  it preserves formally, being a left adjoint. -/
  exact_colim : ∀ (J : Type t₁) ,
    haveI : HasCoproductsOfShape J A := hasCoproducts J
    PreservesFiniteLimits (colim (J := Discrete J) (C := A)) ∧
    PreservesFiniteColimits (colim (J := Discrete J) (C := A))

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

omit [HasDerivedCategory A] in
open _root_.HomotopyCategoryCoproduct in
private theorem homotopyCategory_termwiseDirectSum_isColimit
    (J : Type t) (K : J → CochainComplex A ℤ)
    [HasCoproductsOfShape J A] [HasCoproduct K] :
    Nonempty (IsColimit ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).mapCocone
      (Cofan.mk (∐ K) (Sigma.ι K)))) :=
  ⟨(isColimitMapCoconeCofanMkEquiv (HomotopyCategory.quotient A (ComplexShape.up ℤ)) K
    (Sigma.ι K)).symm (cleanColimit A K)⟩

omit [HasDerivedCategory A] in
private theorem homotopyCategory_hasCoproductsOfShape
    (J : Type t) [HasCoproductsOfShape J A] :
    HasCoproductsOfShape J (HomotopyCategory A (ComplexShape.up ℤ)) := by
  constructor
  intro F
  have hco : HasCoproduct (fun j => F.obj ⟨j⟩) :=
    ⟨⟨_, _root_.HomotopyCategoryCoproduct.cleanColimit A (fun j => (F.obj ⟨j⟩).as)⟩⟩
  exact hasColimit_of_iso (F := Discrete.functor (fun j => F.obj ⟨j⟩))
    (Discrete.natIso (fun ⟨j⟩ => Iso.refl _))

namespace L3Aux

private noncomputable def homπ (J : Type t) :
    (ShortComplex.functorEquivalence (Discrete J) A).inverse ⋙ ShortComplex.homologyFunctor
        (Discrete J ⥤ A)
      ≅ (Functor.whiskeringRight (Discrete J) (ShortComplex A) A).obj (ShortComplex.homologyFunctor
          A) :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun j => (ShortComplex.homologyFunctorIso ((evaluation (Discrete J) A).obj j)).symm.app
        ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K))
      (by rintro ⟨i⟩ ⟨j⟩ f
          obtain rfl : i = j := Discrete.eq_of_hom f
          obtain rfl : f = 𝟙 _ := by subsingleton
          simp))
    (by intro X Y f; ext ⟨j⟩
        dsimp [ShortComplex.homologyFunctorIso]
        exact ShortComplex.mapHomologyIso_inv_naturality
          ((ShortComplex.functorEquivalence (Discrete J) A).inverse.map f)
          ((evaluation (Discrete J) A).obj ⟨j⟩))

omit [HasDerivedCategory A] in
private lemma homπ_inv_app_app (J : Type t) (K : Discrete J ⥤ ShortComplex A) (j : Discrete J) :
    ((homπ A J).app K).inv.app j
      = (ShortComplex.homologyFunctorIso ((evaluation (Discrete J) A).obj j)).hom.app
          ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K) := by
  simp [homπ]

private noncomputable def termCofan (J : Type t) [HasCoproductsOfShape J A]
    (K : Discrete J ⥤ ShortComplex A) : Cocone K where
  pt := (colim (J:=Discrete J) (C:=A)).mapShortComplex.obj
      ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K)
  ι := {
    app := fun j => ShortComplex.homMk (colimit.ι (K ⋙ ShortComplex.π₁) j)
      (colimit.ι (K ⋙ ShortComplex.π₂) j) (colimit.ι (K ⋙ ShortComplex.π₃) j)
      (ι_colimMap _ _) (ι_colimMap _ _)
    naturality := by
      rintro ⟨i⟩ ⟨j⟩ f
      obtain rfl : i = j := Discrete.eq_of_hom f
      obtain rfl : f = 𝟙 _ := by subsingleton
      ext <;> simp }

private noncomputable def termIsColimit (J : Type t) [HasCoproductsOfShape J A]
    (K : Discrete J ⥤ ShortComplex A) : IsColimit (termCofan A J K) := by
  refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
  · exact (colimit.isColimit (K ⋙ ShortComplex.π₁)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (by intro j; simp [termCofan]))
  · exact (colimit.isColimit (K ⋙ ShortComplex.π₂)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (by intro j; simp [termCofan]))
  · exact (colimit.isColimit (K ⋙ ShortComplex.π₃)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (by intro j; simp [termCofan]))

omit [HasDerivedCategory A] in
private lemma legEq (J : Type t) [HasCoproductsOfShape J A]
    [(colim (J := Discrete J) (C := A)).PreservesHomology] (K : Discrete J ⥤ ShortComplex A) (j :
        Discrete J) :
    (ShortComplex.homologyFunctorIso ((evaluation (Discrete J) A).obj j)).hom.app
        ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K) ≫
      colimit.ι ((ShortComplex.homologyFunctor (Discrete J ⥤ A)).obj
          ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K)) j ≫
        ((ShortComplex.homologyFunctorIso (colim (J:=Discrete J) (C:=A))).app
            ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K)).inv
      = (ShortComplex.homologyFunctor A).map
          (((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K).mapNatTrans
            (Limits.colim.ι (J:=Discrete J) (C:=A) j)) := by
  rw [ShortComplex.homologyFunctor_map, ShortComplex.homologyMap_mapNatTrans]
  simp only [ShortComplex.homologyFunctorIso, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.app_inv]
  rfl

private noncomputable def pointIso (J : Type t) [HasCoproductsOfShape J A]
    [(colim (J := Discrete J) (C := A)).PreservesHomology] (K : Discrete J ⥤ ShortComplex A) :
    (ShortComplex.homologyFunctor A).obj
        ((colim (J:=Discrete J) (C:=A)).mapShortComplex.obj
          ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K))
      ≅ colimit (K ⋙ ShortComplex.homologyFunctor A) :=
  ((ShortComplex.homologyFunctorIso (colim (J:=Discrete J) (C:=A))).app
      ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K)) ≪≫
    (colim (J:=Discrete J) (C:=A)).mapIso ((homπ A J).app K)

private noncomputable def mappedIsColimit (J : Type t) [HasCoproductsOfShape J A]
    [(colim (J := Discrete J) (C := A)).PreservesHomology] (K : Discrete J ⥤ ShortComplex A) :
    IsColimit ((ShortComplex.homologyFunctor A).mapCocone (termCofan A J K)) :=
  (colimit.isColimit (K ⋙ ShortComplex.homologyFunctor A)).ofIsoColimit
    (Cocone.ext (pointIso A J K).symm (by
      intro j
      have hleg : (termCofan A J K).ι.app j
          = ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K).mapNatTrans
              (Limits.colim.ι (J:=Discrete J) (C:=A) j) := by
        ext <;> rfl
      simp only [pointIso, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv,
        Functor.mapCocone_ι_app, colimit.cocone_ι]
      rw [colim_map]
      simp only [ι_colimMap_assoc]
      rw [homπ_inv_app_app, hleg]
      exact legEq A J K j))

end L3Aux

omit [HasDerivedCategory A] in
private theorem shortComplex_homologyFunctor_preservesCoproducts
    (h : HasExactCoproducts.{t} A) (J : Type t)
    [HasCoproductsOfShape J A] :
    PreservesColimitsOfShape (Discrete J) (ShortComplex.homologyFunctor A) := by
  obtain ⟨hpl, hpc⟩ := h.exact_colim J
  have := hpl
  have := hpc
  have : (colim (J := Discrete J) (C := A)).PreservesHomology := inferInstance
  exact
    { preservesColimit := fun {K} =>
        preservesColimit_of_preserves_colimit_cocone (L3Aux.termIsColimit A J K)
          (L3Aux.mappedIsColimit A J K) }

omit [HasDerivedCategory A] in
private theorem homologicalComplex_homologyFunctor_preservesCoproducts
    (h : HasExactCoproducts.{t} A) (J : Type t)
    [HasCoproductsOfShape J A] (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n) := by
  have : PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n) :=
    ⟨fun {K} => preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
      (ShortComplex.isColimitOfIsColimitπ _
        (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ)
          ((ComplexShape.up ℤ).prev n)) (colimit.isColimit K))
        (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
          (colimit.isColimit K))
        (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ)
          ((ComplexShape.up ℤ).next n)) (colimit.isColimit K)))⟩
  have := shortComplex_homologyFunctor_preservesCoproducts A h J
  have : PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n ⋙
        ShortComplex.homologyFunctor A) := inferInstance
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso A (ComplexShape.up ℤ) n).symm

omit [HasDerivedCategory A] in
private theorem homotopyCategory_quotient_preservesCoproducts
    (J : Type t) [HasCoproductsOfShape J A] :
    PreservesColimitsOfShape (Discrete J)
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)) := by
  constructor
  intro K
  have : PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)) := by
    refine preservesColimit_of_preserves_colimit_cocone
      (coproductIsCoproduct (K.obj ∘ Discrete.mk)) ?_
    exact (homotopyCategory_termwiseDirectSum_isColimit A J (K.obj ∘ Discrete.mk)).some
  exact preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor).symm

omit [HasDerivedCategory A] in
private theorem homotopyCategory_homologyFunctor_preservesCoproducts
    (h : HasExactCoproducts.{t} A) (J : Type t)
    [HasCoproductsOfShape J A] (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) := by
  have := homotopyCategory_quotient_preservesCoproducts A J
  have := homologicalComplex_homologyFunctor_preservesCoproducts A h J n
  have : PreservesColimitsOfShape (Discrete J)
      (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) :=
    preservesColimitsOfShape_of_natIso
      (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) n).symm
  exact _root_.preservesColimitsOfShape_discrete_of_essSurj_comp
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) J

omit [HasDerivedCategory A] in
private theorem homotopyCategory_quasiIso_stableUnderCoproducts
    (h : HasExactCoproducts.{t} A) (J : Type t) :
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsStableUnderCoproductsOfShape J := by
  have : HasCoproductsOfShape J A := h.hasCoproducts J
  have hpres : ∀ n, PreservesColimitsOfShape (Discrete J)
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) :=
    fun n => homotopyCategory_homologyFunctor_preservesCoproducts A h J n
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X₁ X₂ _ _ f hf
  rw [HomotopyCategory.mem_quasiIso_iff]
  intro n
  have := hpres n
  have : ∀ j, IsIso ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).map (f j)) :=
    fun j => (HomotopyCategory.mem_quasiIso_iff _).mp (hf j) n
  set F := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n
  have hcomm : sigmaComparison F X₁ ≫ F.map (Limits.Sigma.map f)
      = Limits.Sigma.map (fun j => F.map (f j)) ≫ sigmaComparison F X₂ := by
    ext j
    rw [ι_comp_sigmaComparison_assoc, ← F.map_comp, Sigma.ι_map, F.map_comp,
      Sigma.ι_map_assoc, ι_comp_sigmaComparison]
  have : IsIso (Limits.Sigma.map (fun j => F.map (f j))) := by
    refine ⟨Limits.Sigma.map (fun j => inv (F.map (f j))), ?_, ?_⟩ <;> (ext j; simp)
  have : F.map (Limits.Sigma.map f)
      = inv (sigmaComparison F X₁) ≫ Limits.Sigma.map (fun j => F.map (f j)) ≫
        sigmaComparison F X₂ := by
    rw [← hcomm]
    simp
  rw [this]
  infer_instance

private theorem morphismProperty_pi_hasLeftCalculusOfFractions
    {J : Type t} {C : J → Type*} [∀ j, Category (C j)] (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions] :
    (MorphismProperty.pi W).HasLeftCalculusOfFractions := by
  have : (MorphismProperty.pi W).IsMultiplicative :=
    { id_mem := fun X j => (W j).id_mem (X j)
      comp_mem := fun f g hf hg j => (W j).comp_mem _ _ (hf j) (hg j) }
  constructor
  · intro X Y φ
    have hcomp : ∀ j, ∃ ψj : (W j).LeftFraction (X j) (Y j),
        φ.f j ≫ ψj.s = φ.s j ≫ ψj.f := fun j =>
      MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction
        (MorphismProperty.RightFraction.mk (φ.s j) (φ.hs j) (φ.f j))
    choose ψ hψ using hcomp
    refine ⟨{ Y' := fun j => (ψ j).Y', f := fun j => (ψ j).f, s := fun j => (ψ j).s,
              hs := fun j => (ψ j).hs }, ?_⟩
    funext j
    exact hψ j
  · intro X' X Y f₁ f₂ s hs hfs
    have hcomp : ∀ j, ∃ (Y' : C j) (t : Y j ⟶ Y'), ∃ (_ : W j t), f₁ j ≫ t = f₂ j ≫ t := fun j =>
      MorphismProperty.HasLeftCalculusOfFractions.ext (f₁ j) (f₂ j) (s j) (hs j)
        (congrFun hfs j)
    choose Y' t ht hfeq using hcomp
    exact ⟨Y', t, fun j => ht j, funext hfeq⟩

private theorem inv_pi_apply {J : Type t} {D : J → Type*} [∀ j, Category (D j)]
    {X Y : ∀ j, D j} (f : X ⟶ Y) [hf : IsIso f] (j : J) :
    haveI : IsIso (f j) := (isIso_pi_iff f).mp hf j
    (inv f) j = inv (f j) := by
  have : IsIso (f j) := (isIso_pi_iff f).mp hf j
  exact IsIso.eq_inv_of_hom_inv_id (congrFun (IsIso.hom_inv_id f) j)

private theorem functorPi_pi_isInvertedBy {J : Type t} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).ContainsIdentities] [∀ j, (L j).IsLocalization (W j)] :
    (MorphismProperty.pi W).IsInvertedBy (Functor.pi L) := by
  intro X Y s hs
  rw [isIso_pi_iff]
  intro j
  exact Localization.inverts (L j) (W j) _ (hs j)

private theorem functorPi_essSurj {J : Type t} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) [∀ j, (L j).EssSurj] :
    (Functor.pi L).EssSurj :=
  ⟨fun Y => ⟨fun j => (L j).objPreimage (Y j), ⟨Pi.isoMk fun j => (L j).objObjPreimageIso (Y j)⟩⟩⟩

private theorem functorPi_leftFraction_map_apply {J : Type t} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).ContainsIdentities] [∀ j, (L j).IsLocalization (W j)]
    (hinv : (MorphismProperty.pi W).IsInvertedBy (Functor.pi L))
    {X Y : ∀ j, C j} (φ : (MorphismProperty.pi W).LeftFraction X Y) (j : J) :
    (φ.map (Functor.pi L) hinv) j
      = (MorphismProperty.LeftFraction.mk (φ.f j) (φ.s j) (φ.hs j)).map (L j)
          (Localization.inverts (L j) (W j)) := by
  have : IsIso ((Functor.pi L).map φ.s) := hinv φ.s φ.hs
  change ((Functor.pi L).map φ.f ≫ inv ((Functor.pi L).map φ.s)) j = _
  have : IsIso ((L j).map (φ.s j)) := Localization.inverts (L j) (W j) _ (φ.hs j)
  change ((Functor.pi L).map φ.f) j ≫ (inv ((Functor.pi L).map φ.s)) j
      = (L j).map (φ.f j) ≫ inv ((L j).map (φ.s j))
  rw [Functor.pi_map]
  congr 1
  rw [inv_pi_apply ((Functor.pi L).map φ.s) j]
  rfl

private theorem functorPi_leftFraction_map_eq_iff {J : Type t} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions]
    [∀ j, (L j).IsLocalization (W j)]
    (hinv : (MorphismProperty.pi W).IsInvertedBy (Functor.pi L))
    {X Y : ∀ j, C j} (φ ψ : (MorphismProperty.pi W).LeftFraction X Y) :
    φ.map (Functor.pi L) hinv = ψ.map (Functor.pi L) hinv ↔
      MorphismProperty.LeftFractionRel φ ψ := by
  constructor
  · intro hmap
    have hcomp : ∀ j, MorphismProperty.LeftFractionRel
        (MorphismProperty.LeftFraction.mk (φ.f j) (φ.s j) (φ.hs j))
        (MorphismProperty.LeftFraction.mk (ψ.f j) (ψ.s j) (ψ.hs j)) := by
      intro j
      rw [← MorphismProperty.LeftFraction.map_eq_iff (L j) (W j),
          ← functorPi_leftFraction_map_apply L W hinv φ j,
          ← functorPi_leftFraction_map_apply L W hinv ψ j]
      exact congrFun hmap j
    choose Z t₁ t₂ hs hf hW using hcomp
    exact ⟨Z, t₁, t₂, funext hs, funext hf, fun j => hW j⟩
  · rintro ⟨Z, t₁, t₂, hs, hf, hW⟩
    funext j
    rw [functorPi_leftFraction_map_apply L W hinv φ j,
        functorPi_leftFraction_map_apply L W hinv ψ j]
    exact (MorphismProperty.LeftFraction.map_eq_iff (L j) (W j) _ _).mpr
      ⟨Z j, t₁ j, t₂ j, congrFun hs j, congrFun hf j, hW j⟩

private theorem functorPi_exists_leftFraction {J : Type t} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions]
    [∀ j, (L j).IsLocalization (W j)]
    (hinv : (MorphismProperty.pi W).IsInvertedBy (Functor.pi L))
    {X Y : ∀ j, C j} (g : (Functor.pi L).obj X ⟶ (Functor.pi L).obj Y) :
    ∃ φ : (MorphismProperty.pi W).LeftFraction X Y, g = φ.map (Functor.pi L) hinv := by
  have hcomp : ∀ j, ∃ φj : (W j).LeftFraction (X j) (Y j),
      g j = φj.map (L j) (Localization.inverts (L j) (W j)) := fun j =>
    Localization.exists_leftFraction (L j) (W j) (g j)
  choose φ hφ using hcomp
  refine ⟨{ Y' := fun j => (φ j).Y', f := fun j => (φ j).f, s := fun j => (φ j).s,
            hs := fun j => (φ j).hs }, ?_⟩
  funext j
  rw [functorPi_leftFraction_map_apply L W hinv _ j]
  exact hφ j

private theorem functorPi_lift_isEquivalence {J : Type t} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions]
    [∀ j, (L j).IsLocalization (W j)]
    [(MorphismProperty.pi W).HasLeftCalculusOfFractions] :
    (Localization.lift (Functor.pi L) (functorPi_pi_isInvertedBy L W)
      (MorphismProperty.pi W).Q).IsEquivalence := by
  set Lpi := Functor.pi L with hLpi
  set hinv := functorPi_pi_isInvertedBy L W with hhinv
  set Q := (MorphismProperty.pi W).Q with hQ
  set G' := Localization.lift Lpi hinv Q with hG'
  have fac : Q ⋙ G' ≅ Lpi := Localization.fac Lpi hinv Q
  have : ∀ j, (L j).EssSurj := fun j => Localization.essSurj (L j) (W j)
  have : Lpi.EssSurj := functorPi_essSurj L
  have hQs : Q.EssSurj := Localization.essSurj Q (MorphismProperty.pi W)
  have hQG'es : (Q ⋙ G').EssSurj := Functor.essSurj_of_iso fac.symm
  have essSurj : G'.EssSurj :=
    ⟨fun Z => ⟨Q.obj ((Q ⋙ G').objPreimage Z), ⟨(Q ⋙ G').objObjPreimageIso Z⟩⟩⟩
  have invQ : (MorphismProperty.pi W).IsInvertedBy Q :=
    Localization.inverts Q (MorphismProperty.pi W)
  have invQG' : (MorphismProperty.pi W).IsInvertedBy (Q ⋙ G') := by
    intro X Y s hs
    have := invQ s hs
    change IsIso (G'.map (Q.map s))
    infer_instance
  have keymap : ∀ {X Y : ∀ j, C j} (φ : (MorphismProperty.pi W).LeftFraction X Y),
      G'.map (φ.map Q invQ)
        = fac.hom.app X ≫ φ.map Lpi hinv ≫ fac.inv.app Y := by
    intro X Y φ
    rw [_root_.leftFraction_map_comp_functor Q G' φ invQ invQG']
    exact _root_.leftFraction_map_iso_transport Lpi (Q ⋙ G') fac.symm φ hinv invQG'
  have : G'.Faithful := by
    refine ⟨fun {a b} f₁ f₂ hf => ?_⟩
    set X := Q.objPreimage a with hX
    set Y := Q.objPreimage b with hY
    set eX : Q.obj X ≅ a := Q.objObjPreimageIso a with heX
    set eY : Q.obj Y ≅ b := Q.objObjPreimageIso b with heY
    set g₁ : Q.obj X ⟶ Q.obj Y := eX.hom ≫ f₁ ≫ eY.inv with hg1
    set g₂ : Q.obj X ⟶ Q.obj Y := eX.hom ≫ f₂ ≫ eY.inv with hg2
    suffices hg : g₁ = g₂ by
      have h2 : f₁ ≫ eY.inv = f₂ ≫ eY.inv := (cancel_epi eX.hom).mp hg
      exact (cancel_mono eY.inv).mp h2
    obtain ⟨φ₁, e₁⟩ := Localization.exists_leftFraction Q (MorphismProperty.pi W) g₁
    obtain ⟨φ₂, e₂⟩ := Localization.exists_leftFraction Q (MorphismProperty.pi W) g₂
    rw [e₁, e₂]
    have hG'g : G'.map (φ₁.map Q invQ) = G'.map (φ₂.map Q invQ) := by
      rw [← e₁, ← e₂, hg1, hg2, Functor.map_comp, Functor.map_comp, Functor.map_comp,
        Functor.map_comp, hf]
    rw [keymap φ₁, keymap φ₂] at hG'g
    have hLpi : φ₁.map Lpi hinv = φ₂.map Lpi hinv := by
      rw [← cancel_epi (fac.hom.app X), ← cancel_mono (fac.inv.app Y)]
      simpa [Category.assoc] using hG'g
    rw [MorphismProperty.LeftFraction.map_eq_iff Q (MorphismProperty.pi W)]
    exact (functorPi_leftFraction_map_eq_iff L W hinv φ₁ φ₂).mp hLpi
  have : G'.Full := by
    refine ⟨fun {a b} g => ?_⟩
    set X := Q.objPreimage a with hX
    set Y := Q.objPreimage b with hY
    set eX : Q.obj X ≅ a := Q.objObjPreimageIso a with heX
    set eY : Q.obj Y ≅ b := Q.objObjPreimageIso b with heY
    obtain ⟨φ, hφ⟩ := functorPi_exists_leftFraction L W hinv
      (fac.inv.app X ≫ (G'.map eX.hom ≫ g ≫ G'.map eY.inv) ≫ fac.hom.app Y)
    refine ⟨eX.inv ≫ φ.map Q invQ ≫ eY.hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, keymap φ, ← hφ]
    have key : G'.map eX.inv ≫ fac.hom.app X ≫ fac.inv.app X ≫ G'.map eX.hom ≫ g ≫
        G'.map eY.inv ≫ fac.hom.app Y ≫ fac.inv.app Y ≫ G'.map eY.hom = g := by
      slice_lhs 2 3 => rw [fac.hom_inv_id_app]
      slice_lhs 6 7 => rw [fac.hom_inv_id_app]
      simp
    simp only [Category.assoc] at key ⊢
    exact key
  exact { }

private theorem functor_pi_isLocalization_of_hasLeftCalculusOfFractions
    {J : Type t} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions]
    [∀ j, (L j).IsLocalization (W j)] :
    (Functor.pi L).IsLocalization (MorphismProperty.pi W) := by
  have := morphismProperty_pi_hasLeftCalculusOfFractions W
  have hinv := functorPi_pi_isInvertedBy L W
  have := functorPi_lift_isEquivalence L W
  exact Functor.IsLocalization.of_equivalence_target (MorphismProperty.pi W).Q
    (MorphismProperty.pi W) (Functor.pi L)
    (Localization.lift (Functor.pi L) hinv (MorphismProperty.pi W).Q).asEquivalence
    (Localization.fac (Functor.pi L) hinv (MorphismProperty.pi W).Q)

private theorem localizationFunctorCategory_discrete_isLocalization_of_countable
    {C : Type*} {D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
    (J : Type t) :
    ((Functor.whiskeringRight (Discrete J) C D).obj L).IsLocalization
      (W.functorCategory (Discrete J)) := by
  have : (Functor.pi (fun _ : J => L)).IsLocalization (MorphismProperty.pi (fun _ : J => W)) :=
    functor_pi_isLocalization_of_hasLeftCalculusOfFractions (fun _ => L) (fun _ => W)
  let E := piEquivalenceFunctorDiscrete J C
  let E' := piEquivalenceFunctorDiscrete J D
  let L₂ := (Functor.whiskeringRight (Discrete J) C D).obj L
  let L₁ := Functor.pi (fun (_ : J) => L)
  have : CatCommSq E.functor L₁ L₂ E'.functor :=
    ⟨(Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ E'.counitIso.symm ≪≫
      Functor.associator _ _ _≪≫ Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (by exact Iso.refl _) _) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm L₁) _ ≪≫ Functor.isoWhiskerRight L₁.leftUnitor _⟩
  refine Functor.IsLocalization.of_equivalences L₁
    (MorphismProperty.pi (fun _ => W)) L₂ _ E E' ?_ ?_
  · intro X Y f hf
    exact MorphismProperty.le_isoClosure _ _ (fun ⟨j⟩ => hf j)
  · intro X Y f hf
    have : ∀ (j : Discrete J), IsIso ((L₂.map f).app j) :=
      fun j => Localization.inverts L W _ (hf j)
    apply NatIso.isIso_of_isIso_app

namespace ColimAux

variable {C : Type*} {D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] (J : Type t)
    [HasCoproductsOfShape J C] [W.IsStableUnderCoproductsOfShape J]

private theorem inverts : (W.functorCategory (Discrete J)).IsInvertedBy (colim ⋙ L) :=
  fun _ _ f hf =>
  Localization.inverts L W (colim.map f) (MorphismProperty.colimMap f hf)

variable [W.ContainsIdentities]
    [((Functor.whiskeringRight (Discrete J) C D).obj L).IsLocalization (W.functorCategory (Discrete
        J))]

@[reducible]
private noncomputable def colimitFunctor : (Discrete J ⥤ D) ⥤ D :=
  Localization.lift (colim ⋙ L) (inverts L W J) ((Functor.whiskeringRight (Discrete J) C D).obj L)

private noncomputable def compColimitFunctorIso :
    (Functor.whiskeringRight (Discrete J) C D).obj L ⋙ colimitFunctor L W J ≅ colim ⋙ L :=
  Localization.fac (colim ⋙ L) (inverts L W J) ((Functor.whiskeringRight (Discrete J) C D).obj L)

private noncomputable local instance catCommSq :
    CatCommSq colim ((Functor.whiskeringRight (Discrete J) C D).obj L) L (colimitFunctor L W J) :=
  CatCommSq.mk (compColimitFunctorIso L W J).symm

private noncomputable local instance constCatCommSq :
    CatCommSq (Functor.const (Discrete J)) L
      ((Functor.whiskeringRight (Discrete J) C D).obj L) (Functor.const (Discrete J)) :=
  ⟨(Functor.compConstIso (Discrete J) L).symm⟩

private noncomputable def adj : colimitFunctor L W J ⊣ Functor.const (Discrete J) :=
  colimConstAdj.localization ((Functor.whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) L W (colimitFunctor L W J) (Functor.const (Discrete J))

private noncomputable def isColimitMapCocone (F : Discrete J ⥤ C) :
    IsColimit (L.mapCocone (colimit.cocone F)) :=
  (_root_.ColimAux.isColimitCoconeOfAdj (adj L W J) (F ⋙ L)).ofIsoColimit
    (Cocone.ext ((compColimitFunctorIso L W J).app F) (fun j => by
      have hunit := Adjunction.localization_unit_app colimConstAdj
        ((Functor.whiskeringRight (Discrete J) C D).obj L) (W.functorCategory (Discrete J)) L W
        (colimitFunctor L W J) (Functor.const (Discrete J)) F
      dsimp [_root_.ColimAux.coconeOfAdj, adj]
      erw [hunit]
      simp only [Functor.comp_obj, Functor.const_obj_obj, NatTrans.comp_app, Functor.const_map_app,
        CatCommSq.iso, Iso.symm_hom, Functor.whiskeringRight_obj_obj]
      dsimp [colimConstAdj, Functor.compConstIso]
      simp only [Category.assoc]
      rw [Iso.inv_hom_id_app]
      simp))

end ColimAux

private theorem localization_preservesCoproductsOfShape
    {C : Type*} {D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.ContainsIdentities] (J : Type t)
    [HasCoproductsOfShape J C] [W.IsStableUnderCoproductsOfShape J]
    [((Functor.whiskeringRight (Discrete J) C D).obj L).IsLocalization
      (W.functorCategory (Discrete J))] :
    PreservesColimitsOfShape (Discrete J) L := by
  exact
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
          (ColimAux.isColimitMapCocone L W J F) }

private theorem derivedCategory_Qh_preservesCoproductsOfShape
    (h : HasExactCoproducts.{t} A) (J : Type t)
    [HasCoproductsOfShape J (HomotopyCategory A (ComplexShape.up ℤ))] :
    PreservesColimitsOfShape (Discrete J) (DerivedCategory.Qh (C := A)) := by
  have : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsStableUnderCoproductsOfShape J :=
    homotopyCategory_quasiIso_stableUnderCoproducts A h J
  have := localizationFunctorCategory_discrete_isLocalization_of_countable
    (DerivedCategory.Qh (C := A)) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) J
  exact localization_preservesCoproductsOfShape
    (DerivedCategory.Qh (C := A)) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) J

/-- **The localization `Q : C(A) ⥤ D(A)` preserves `J`-indexed coproducts**, for every index type
`J` of a universe in which `A` has exact coproducts — with no countability restriction on `J`.

`Q` factors as `quotient ⋙ Qh` (`DerivedCategory.quotientCompQhIso`). The homotopy quotient
carries the termwise direct sum to a coproduct of `K(A)`, and `Qh` preserves `J`-coproducts
because the quasi-isomorphisms are stable under them, which is where exactness of the coproducts
is used. -/
theorem derivedCategory_Q_preservesCoproductsOfShape
    (h : HasExactCoproducts.{t} A) (J : Type t) :
    PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := A)) := by
  have : HasCoproductsOfShape J A := h.hasCoproducts J
  have : HasCoproductsOfShape J (HomotopyCategory A (ComplexShape.up ℤ)) :=
    homotopyCategory_hasCoproductsOfShape A J
  have := homotopyCategory_quotient_preservesCoproducts A J
  have := derivedCategory_Qh_preservesCoproductsOfShape A h J
  exact preservesColimitsOfShape_of_natIso (DerivedCategory.quotientCompQhIso A)

end CoproductBridge

private theorem moduleCat_Q_preservesCoproducts
    {R : Type u} [Ring R] [Small.{v} R] (I : Type v) :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := ModuleCat.{v} R)) := by
  apply CoproductBridge.derivedCategory_Q_preservesCoproductsOfShape
  refine ⟨inferInstance, fun J => ?_⟩
  have : HasExactColimitsOfShape (Discrete J) (ModuleCat.{v} R) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete J)
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})
  exact ⟨inferInstance, inferInstance⟩

namespace Telescope

variable {C : Type*} [Category C] [Preadditive C]

private noncomputable def alpha (D : ℕ ⥤ C) [HasCoproduct D.obj] : ∐ D.obj ⟶ ∐ D.obj :=
  Sigma.desc fun p => Sigma.ι D.obj p - D.map (homOfLE (Nat.le_succ p)) ≫ Sigma.ι D.obj (p + 1)

private noncomputable def beta (D : ℕ ⥤ C) [HasCoproduct D.obj] [HasColimit D] :
    ∐ D.obj ⟶ colimit D := Sigma.desc (colimit.ι D)

@[local simp] private lemma ι_alpha (D : ℕ ⥤ C) [HasCoproduct D.obj] (p : ℕ) :
    Sigma.ι D.obj p ≫ alpha D =
      Sigma.ι D.obj p - D.map (homOfLE (Nat.le_succ p)) ≫ Sigma.ι D.obj (p + 1) := by
  simp [alpha]

omit [Preadditive C] in
@[local simp] private lemma ι_beta (D : ℕ ⥤ C) [HasCoproduct D.obj] [HasColimit D] (p : ℕ) :
    Sigma.ι D.obj p ≫ beta D = colimit.ι D p := by simp [beta]

private lemma alpha_beta (D : ℕ ⥤ C) [HasCoproduct D.obj] [HasColimit D] :
    alpha D ≫ beta D = 0 := by
  ext p
  simp [alpha, beta, Preadditive.sub_comp]

private noncomputable def cocone (D : ℕ ⥤ C) [HasCoproduct D.obj]
    (s : CokernelCofork (alpha D)) : Cocone D where
  pt := s.pt
  ι := NatTrans.ofSequence (fun p => Sigma.ι D.obj p ≫ s.π) (by
    intro p
    have h := congrArg (Sigma.ι D.obj p ≫ ·) s.condition
    simp only [← Category.assoc, ι_alpha, Preadditive.sub_comp, comp_zero] at h
    simpa [Category.assoc] using (sub_eq_zero.mp h).symm)

private noncomputable def isCokernel (D : ℕ ⥤ C) [HasCoproduct D.obj] [HasColimit D] :
    IsColimit (CokernelCofork.ofπ (beta D) (alpha_beta D)) := by
  apply Cofork.IsColimit.mk _ (fun s => colimit.desc D (cocone D s))
  · intro s
    ext p
    simp [beta, cocone]
  · intro s m hm
    apply colimit.hom_ext (F := D)
    intro p
    have h := congrArg (Sigma.ι D.obj p ≫ ·) hm
    simpa [beta, cocone] using h

private noncomputable def retractions {F : ℕ → C} {X : C}
    (ι : ∀ p, F p ⟶ X) (r : ∀ p, F (p + 1) ⟶ F p) : ∀ p, F p ⟶ X
  | 0 => 0
  | p + 1 => r p ≫ (retractions ι r p - ι p)

private theorem isSplitMono_of_cofan {F : ℕ → C} {X : C}
    (ι : ∀ p, F p ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    (inc : ∀ p, F p ⟶ F (p + 1)) (hsplit : ∀ p, IsSplitMono (inc p))
    (a : X ⟶ X) (ha : ∀ p, ι p ≫ a = ι p - inc p ≫ ι (p + 1)) :
    IsSplitMono a := by
  let r := retractions ι (fun p => @retraction _ _ _ _ (inc p) (hsplit p))
  let ρ := hc.desc (Cofan.mk X r)
  have hρ (p : ℕ) : ι p ≫ ρ = r p := hc.fac _ ⟨p⟩
  refine ⟨⟨⟨ρ, ?_⟩⟩⟩
  apply hc.hom_ext
  rintro ⟨p⟩
  change ι p ≫ (a ≫ ρ) = ι p ≫ 𝟙 X
  rw [← Category.assoc, ha, Preadditive.sub_comp, Category.assoc, hρ, hρ]
  have hrec : inc p ≫ r (p + 1) = r p - ι p := by
    have := hsplit p
    simp [r, retractions, ← Category.assoc]
  rw [hrec, Category.comp_id]
  abel

end Telescope

namespace Resolution

open CochainComplex CochainComplex.HomComplex HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [Ring R] [Small.{v} R]

private noncomputable abbrev regular := ModuleCat.of R (Shrink.{v} R)

private noncomputable def regularMap {X : ModuleCat.{v} R} (x : X) : regular (R := R) ⟶ X :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton R X x).comp (Shrink.linearEquiv R R).toLinearMap)

private noncomputable def regularOne : regular (R := R) := (Shrink.linearEquiv R R).symm 1

@[local simp] private lemma regularMap_one {X : ModuleCat.{v} R} (x : X) :
    regularMap x (regularOne (R := R)) = x := by
  simp [regularMap, regularOne]

@[local simp] private lemma regularMap_comp {X Y : ModuleCat.{v} R} (x : X) (f : X ⟶ Y) :
    regularMap x ≫ f = regularMap (f x) := by
  ext r
  simp [regularMap]

@[local simp] private lemma regularMap_zero (X : ModuleCat.{v} R) :
    regularMap (0 : X) = 0 := by
  ext r
  simp [regularMap]

private noncomputable abbrev cell (n : ℤ) :=
  (singleFunctor (ModuleCat.{v} R) n).obj (regular (R := R))

private noncomputable def cellGenerator (n : ℤ) : (cell (R := R) n).X n :=
  (singleObjXSelf (.up ℤ) n (regular (R := R))).inv (regularOne (R := R))

private noncomputable def fromCell {X : CochainComplex (ModuleCat.{v} R) ℤ}
    (n : ℤ) (x : X.X n) (hx : X.d n (n + 1) x = 0) : cell n ⟶ X :=
  (Cocycle.fromSingleMk (regularMap x) (add_zero n) (n + 1) rfl (by simp [hx])).homOf

@[local simp] private lemma fromCell_cochain {X : CochainComplex (ModuleCat.{v} R) ℤ}
    (n : ℤ) (x : X.X n) (hx : X.d n (n + 1) x = 0) :
    Cochain.ofHom (fromCell n x hx) = Cochain.fromSingleMk (regularMap x) (add_zero n) := by
  simp [fromCell]

@[local simp] private lemma fromCell_generator {X : CochainComplex (ModuleCat.{v} R) ℤ}
    (n : ℤ) (x : X.X n) (hx : X.d n (n + 1) x = 0) :
    (fromCell n x hx).f n (cellGenerator n) = x := by
  have h := Cochain.congr_v (fromCell_cochain n x hx) n n (add_zero n)
  simp only [Cochain.ofHom_v, Cochain.fromSingleMk_v] at h
  rw [h]
  change ((singleObjXSelf (.up ℤ) n (regular (R := R))).inv ≫
    (singleObjXSelf (.up ℤ) n (regular (R := R))).hom ≫ regularMap x) regularOne = x
  rw [Iso.inv_hom_id_assoc]
  exact regularMap_one x

private noncomputable def cochainDesc {I : Type v}
    (K : I → CochainComplex (ModuleCat.{v} R) ℤ)
    {Y : CochainComplex (ModuleCat.{v} R) ℤ} {n : ℤ}
    (H : ∀ i, Cochain (K i) Y n) : Cochain (∐ K) Y n :=
  Cochain.mk fun p q hpq =>
    (_root_.HomotopyCategoryCoproduct.cdeg _ K p).desc
      { pt := Y.X q, ι := Discrete.natTrans fun ⟨i⟩ => (H i).v p q hpq }

omit [Small.{v} R] in
@[local simp] private lemma cochainDesc_ι {I : Type v}
    (K : I → CochainComplex (ModuleCat.{v} R) ℤ)
    {Y : CochainComplex (ModuleCat.{v} R) ℤ} {n : ℤ}
    (H : ∀ i, Cochain (K i) Y n) (i : I) :
    (Cochain.ofHom (Sigma.ι K i)).comp (cochainDesc K H) (zero_add n) = H i := by
  apply Cochain.ext
  intro p q hpq
  simpa [cochainDesc, Cochain.comp_v _ _ _ p p q (add_zero p) hpq] using
    (_root_.HomotopyCategoryCoproduct.cdeg _ K p).fac
      { pt := Y.X q, ι := Discrete.natTrans fun ⟨i⟩ => (H i).v p q hpq } ⟨i⟩

omit [Small.{v} R] in
private lemma cochain_ext {I : Type v}
    (K : I → CochainComplex (ModuleCat.{v} R) ℤ)
    {Y : CochainComplex (ModuleCat.{v} R) ℤ} {n : ℤ}
    {a b : Cochain (∐ K) Y n}
    (h : ∀ i, (Cochain.ofHom (Sigma.ι K i)).comp a (zero_add n) =
      (Cochain.ofHom (Sigma.ι K i)).comp b (zero_add n)) : a = b := by
  apply Cochain.ext
  intro p q hpq
  apply (_root_.HomotopyCategoryCoproduct.cdeg _ K p).hom_ext
  rintro ⟨i⟩
  simpa [Cochain.comp_v _ _ _ p p q (add_zero p) hpq] using
    Cochain.congr_v (h i) p q hpq

private abbrev Cycles (M : CochainComplex (ModuleCat.{v} R) ℤ) :=
  Σ n : ℤ, {x : M.X n // M.d n (n + 1) x = 0}

private noncomputable def bottom (M : CochainComplex (ModuleCat.{v} R) ℤ) :
    CochainComplex (ModuleCat.{v} R) ℤ := ∐ fun z : Cycles M => cell (R := R) z.1

private noncomputable def bottomMap (M : CochainComplex (ModuleCat.{v} R) ℤ) : bottom M ⟶ M :=
  Sigma.desc fun z : Cycles M => fromCell z.1 z.2.1 z.2.2

private structure Attachment {F M : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ M) where
  n : ℤ
  x : F.X (n + 1)
  y : M.X n
  cycle : F.d (n + 1) (n + 1 + 1) x = 0
  boundary : f.f (n + 1) x = M.d n (n + 1) y

private noncomputable def attachmentCells {F M : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ M) : CochainComplex (ModuleCat.{v} R) ℤ :=
  ∐ fun z : Attachment f => cell (R := R) (z.n + 1)

private noncomputable def attachmentMap {F M : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ M) : attachmentCells f ⟶ F :=
  Sigma.desc fun z : Attachment f => fromCell (z.n + 1) z.x z.cycle

private noncomputable def attachmentNullhomotopy {F M : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ M) : Cochain (attachmentCells f) M (-1) :=
  cochainDesc _ fun z : Attachment f => Cochain.fromSingleMk (regularMap z.y) (by omega)

private lemma attachmentNullhomotopy_δ {F M : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ M) :
    δ (-1) 0 (attachmentNullhomotopy f) = Cochain.ofHom (attachmentMap f ≫ f) := by
  apply cochain_ext (fun z : Attachment f => cell (R := R) (z.n + 1))
  intro z
  rw [← δ_ofHom_comp, attachmentNullhomotopy, cochainDesc_ι]
  rw [← Cochain.ofHom_comp, attachmentMap, Sigma.ι_comp_desc_assoc,
    Cochain.ofHom_comp, fromCell_cochain, ← Cochain.fromSingleMk_postcomp,
    Cochain.δ_fromSingleMk _ _ _ (z.n + 1) (add_zero _)]
  simp [z.boundary]

private noncomputable def next {F M : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ M) :=
  mappingCone (attachmentMap f)

private noncomputable def nextMap {F M : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ M) :
    next f ⟶ M :=
  mappingCone.desc _ (attachmentNullhomotopy f) f (attachmentNullhomotopy_δ f)

private noncomputable def nextInclusion {F M : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ M) :
    F ⟶ next f := mappingCone.inr _

@[local simp] private lemma nextInclusion_nextMap
    {F M : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ M) :
    nextInclusion f ≫ nextMap f = f := by simp [nextInclusion, nextMap]

section HomologyColimit

open Limits

variable {A : Type*} [Category A] [Abelian A]

end HomologyColimit

private theorem moduleCat_exactColimits_nat (R : Type u) [Ring R] :
    HasExactColimitsOfShape ℕ (ModuleCat.{v} R) := by
  have : AB5OfSize.{0, 0} AddCommGrpCat.{v} := AB5OfSize_of_univLE.{0, 0, v, v} _
  exact HasExactColimitsOfShape.domain_of_functor ℕ
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})

attribute [local instance] moduleCat_exactColimits_nat

private theorem moduleCat_forget_preservesColimits_nat (R : Type u) [Ring R] :
    Limits.PreservesColimitsOfShape ℕ (forget (ModuleCat.{v} R)) := by
  have : Limits.PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{v}) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE.{v, v, 0, 0} _
  exact inferInstanceAs (PreservesColimitsOfShape ℕ
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙ forget AddCommGrpCat.{v}))

attribute [local instance] moduleCat_forget_preservesColimits_nat

private theorem quasiIso_of_colimit_kills_kernels {R : Type u} [Ring R]
    (D : ℕ ⥤ CochainComplex (ModuleCat.{v} R) ℤ) (c : Limits.Cocone D)
    (hepi : ∀ n : ℤ, Epi (HomologicalComplex.homologyMap (c.ι.app 0) n))
    (hkill : ∀ (m : ℕ) (n : ℤ) (x : (D.obj m).homology n),
      HomologicalComplex.homologyMap (c.ι.app m) n x = 0 →
        HomologicalComplex.homologyMap (D.map (homOfLE (Nat.le_succ m))) n x = 0) :
    QuasiIso (Limits.colimit.desc D c) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n
  have := preservesColimitsOfShape_homologyFunctor (A := ModuleCat.{v} R) (J := ℕ)
    (ComplexShape.up ℤ) n
  have hc : Limits.IsColimit (H.mapCocone (Limits.colimit.cocone D)) :=
    Limits.isColimitOfPreserves H (Limits.colimit.isColimit D)
  have hfac (m : ℕ) : H.map (Limits.colimit.ι D m) ≫ H.map (Limits.colimit.desc D c) =
      H.map (c.ι.app m) := by rw [← H.map_comp, Limits.colimit.ι_desc]
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨m, y, hy⟩ := Limits.Concrete.isColimit_exists_rep (D ⋙ H) hc x
    have hy' : H.map (Limits.colimit.ι D m) y = x := hy
    have hz : H.map (c.ι.app m) y = 0 := by
      rw [← hfac]
      change H.map (Limits.colimit.desc D c) (H.map (Limits.colimit.ι D m) y) = 0
      rwa [hy']
    have hk := hkill m n y hz
    change H.map (D.map (homOfLE (Nat.le_succ m))) y = 0 at hk
    have hw := congrArg H.map (Limits.colimit.w D (homOfLE (Nat.le_succ m)))
    rw [H.map_comp] at hw
    rw [← hy', ← hw]
    change H.map (Limits.colimit.ι D (m + 1))
      (H.map (D.map (homOfLE (Nat.le_succ m))) y) = 0
    rw [hk, map_zero]
  · intro x
    obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyMap (c.ι.app 0) n)).mp (hepi n) x
    exact ⟨H.map (Limits.colimit.ι D 0) y,
      (congrArg (fun f : H.obj (D.obj 0) ⟶ H.obj c.pt => f y) (hfac 0)).trans hy⟩

/-- The generator of a cell is sent to a cocycle by any chain map out of the cell. -/
private lemma cell_generator_d_eq_zero {X : CochainComplex (ModuleCat.{v} R) ℤ} {n : ℤ}
    (g : cell (R := R) n ⟶ X) : X.d n (n + 1) (g.f n (cellGenerator n)) = 0 := by
  change (g.f n ≫ X.d n (n + 1)) _ = 0
  rw [g.comm]
  have hd : (cell (R := R) n).d n (n + 1) = 0 := HomologicalComplex.single_obj_d _ _ _ _ _
  rw [hd, zero_comp]
  rfl

private lemma nextInclusion_kills {F M : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ M) (n : ℤ) (x : F.X n) (hx : F.d n (n + 1) x = 0)
    (y : M.X (n - 1)) (hy : f.f n x = M.d (n - 1) n y) :
    ∃ w : (next f).X (n - 1), (next f).d (n - 1) n w = (nextInclusion f).f n x := by
  generalize hm : n - 1 = m at y hy ⊢
  obtain rfl : n = m + 1 := by omega
  let z : Attachment f := ⟨m, x, y, hx, hy⟩
  let g : cell (R := R) (m + 1) ⟶ attachmentCells f :=
    Sigma.ι (fun z : Attachment f => cell (R := R) (z.n + 1)) z
  have hg : g ≫ attachmentMap f = fromCell (m + 1) x hx := by
    simp [g, attachmentMap, z]
  let a := g.f (m + 1) (cellGenerator (m + 1))
  have ha : (attachmentCells f).d (m + 1) (m + 1 + 1) a = 0 := cell_generator_d_eq_zero g
  refine ⟨(mappingCone.inl (attachmentMap f)).v (m + 1) m (by omega) a, ?_⟩
  have h := mappingCone.inl_v_d (attachmentMap f) (m + 1) m (m + 1 + 1)
    (by omega) (by omega)
  have h' := congrArg (fun k : (attachmentCells f).X (m + 1) ⟶ (next f).X (m + 1) => k a) h
  have hax : (attachmentMap f).f (m + 1) a = x := by
    have e := congrArg (fun k : cell (m + 1) ⟶ F => k.f (m + 1) (cellGenerator (m + 1))) hg
    simpa [a] using e
  simpa [next, nextInclusion, ModuleCat.comp_apply, ha, hax] using h'

private theorem nextInclusion_kills_homologyKernel
    {F M : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ M) (n : ℤ)
    (x : F.homology n) (hx : homologyMap f n x = 0) :
    homologyMap (nextInclusion f) n x = 0 := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (F.homologyπ n)).mp inferInstance x
  obtain ⟨y, hy⟩ := (homologyMap_eq_zero_iff f n x z hz).mp hx
  apply (homologyMap_eq_zero_iff _ n x z hz).mpr
  apply nextInclusion_kills f n _ _ y hy.symm
  exact congrArg (fun k : F.cycles n ⟶ F.X (n + 1) => k z) (F.iCycles_d n (n + 1))

private theorem bottomMap_epi_homology (M : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) :
    Epi (homologyMap (bottomMap M) n) := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (M.homologyπ n)).mp inferInstance x
  have hzcycle : M.d n (n + 1) (M.iCycles n z) = 0 :=
    congrArg (fun k : M.cycles n ⟶ M.X (n + 1) => k z) (M.iCycles_d n (n + 1))
  let j : Cycles M := ⟨n, M.iCycles n z, hzcycle⟩
  let g : cell (R := R) n ⟶ bottom M :=
    Sigma.ι (fun z : Cycles M => cell (R := R) z.1) j
  have hg : g ≫ bottomMap M = fromCell n (M.iCycles n z) hzcycle := by
    simp [g, bottomMap, j]
  let a := g.f n (cellGenerator n)
  have ha : (bottom M).d n (n + 1) a = 0 := cell_generator_d_eq_zero g
  let c : (bottom M).cycles n :=
    ((bottom M).liftCycles (regularMap a) (n + 1) (by simp) (by simp [ha])) regularOne
  have hc : (bottom M).iCycles n c = a := by
    change (((bottom M).liftCycles _ _ _ _ ≫ (bottom M).iCycles n)) regularOne = a
    rw [liftCycles_i]
    exact regularMap_one a
  refine ⟨(bottom M).homologyπ n c, ?_⟩
  have hcmap : cyclesMap (bottomMap M) n c = z := by
    apply (ModuleCat.mono_iff_injective (M.iCycles n)).mp inferInstance
    have h := congrArg (fun k : (bottom M).cycles n ⟶ M.X n => k c)
      (cyclesMap_i (bottomMap M) n)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hc] at h
    rw [h]
    have h' := congrArg (fun k => k.f n (cellGenerator n)) hg
    change (bottomMap M).f n a = (fromCell n (M.iCycles n z) hzcycle).f n (cellGenerator n) at h'
    exact h'.trans (fromCell_generator _ _ _)
  have h := congrArg (fun k : (bottom M).cycles n ⟶ M.homology n => k c)
    (homologyπ_naturality (bottomMap M) n)
  change homologyMap (bottomMap M) n ((bottom M).homologyπ n c) =
    M.homologyπ n (cyclesMap (bottomMap M) n c) at h
  rw [h, hcmap, hz]

private noncomputable def stages (M : CochainComplex (ModuleCat.{v} R) ℤ) : ℕ → Over M
  | 0 => Over.mk (bottomMap M)
  | p + 1 => Over.mk (nextMap (stages M p).hom)

private noncomputable def stageInclusion (M : CochainComplex (ModuleCat.{v} R) ℤ) (p : ℕ) :
    stages M p ⟶ stages M (p + 1) :=
  Over.homMk (nextInclusion (stages M p).hom) (nextInclusion_nextMap _)

private noncomputable def diagram (M : CochainComplex (ModuleCat.{v} R) ℤ) :
    ℕ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  Functor.ofSequence (stageInclusion M) ⋙ Over.forget M

private noncomputable def augmentationCocone (M : CochainComplex (ModuleCat.{v} R) ℤ) :
    Cocone (diagram M) where
  pt := M
  ι := NatTrans.ofSequence (fun p => (stages M p).hom) (by
    intro p
    simp [diagram, stageInclusion, stages])

private lemma diagram_map_succ (M : CochainComplex (ModuleCat.{v} R) ℤ) (p : ℕ) :
    (diagram M).map (homOfLE (Nat.le_succ p)) = nextInclusion (stages M p).hom := by
  simp [diagram, stageInclusion]

private theorem augmentation_quasiIso (M : CochainComplex (ModuleCat.{v} R) ℤ) :
    QuasiIso (colimit.desc (diagram M) (augmentationCocone M)) := by
  apply quasiIso_of_colimit_kills_kernels
  · exact bottomMap_epi_homology M
  · intro p n x hx
    rw [diagram_map_succ]
    exact nextInclusion_kills_homologyKernel (stages M p).hom n x hx

private theorem nextInclusion_split {F M : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ M) (n : ℤ) : IsSplitMono ((nextInclusion f).f n) :=
  ⟨⟨⟨(mappingCone.snd (attachmentMap f)).v n n (add_zero n),
    mappingCone.inr_f_snd_v _ _⟩⟩⟩

private theorem diagram_map_succ_isSplitMono (M : CochainComplex (ModuleCat.{v} R) ℤ) (p : ℕ)
    (n : ℤ) : IsSplitMono (((diagram M).map (homOfLE (Nat.le_succ p))).f n) := by
  rw [diagram_map_succ]
  exact nextInclusion_split _ n

private theorem diagram_map_injective (M : CochainComplex (ModuleCat.{v} R) ℤ)
    {p q : ℕ} (a : p ⟶ q) (n : ℤ) : Function.Injective (((diagram M).map a).f n) := by
  have h := leOfHom a
  obtain rfl : a = homOfLE h := Subsingleton.elim _ _
  induction q, h using Nat.le_induction with
  | base => simpa using Function.injective_id
  | succ q h ih =>
    have e : homOfLE (h.trans (Nat.le_succ q)) = homOfLE h ≫ homOfLE (Nat.le_succ q) :=
      Subsingleton.elim _ _
    rw [e, Functor.map_comp, HomologicalComplex.comp_f]
    have := diagram_map_succ_isSplitMono M q n
    have hq : Function.Injective (((diagram M).map (homOfLE (Nat.le_succ q))).f n) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact hq.comp ih

private theorem colimit_ι_injective (M : CochainComplex (ModuleCat.{v} R) ℤ) (p : ℕ) (n : ℤ) :
    Function.Injective ((colimit.ι (diagram M) p).f n) := by
  let E := HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) n
  have hc := isColimitOfPreserves E (colimit.isColimit (diagram M))
  intro x y hxy
  obtain ⟨q, a, ha⟩ := (hc.eq_iff' x y).mp hxy
  exact diagram_map_injective M a n ha

private theorem colimit_exhaustive (M : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (x : (colimit (diagram M)).X n) :
    ∃ p, ∃ y : ((diagram M).obj p).X n, (colimit.ι (diagram M) p).f n y = x := by
  let E := HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) n
  exact Concrete.isColimit_exists_rep (diagram M ⋙ E)
    (isColimitOfPreserves E (colimit.isColimit (diagram M))) x

private noncomputable def cellIso (n : ℤ) :
    cell (R := R) n ≅ (cell (R := R) 0)⟦-n⟧ :=
  ((singleFunctors (ModuleCat.{v} R)).shiftIso (-n) n 0 (neg_add_cancel n)).symm.app _

/-- Coproducts of cochain complexes of modules, stated directly: instance search no longer
finds them within the default budget. -/
private local instance hasCoproductsCochainComplex :
    HasCoproducts.{v} (CochainComplex (ModuleCat.{v} R) ℤ) := fun J => by
  have : HasColimitsOfShape (Discrete J) (ModuleCat.{v} R) := inferInstance
  exact ⟨fun F => ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩⟩

private noncomputable def cellsIso {I : Type v} (n : I → ℤ) :
    (∐ fun i => cell (R := R) (n i)) ≅ ∐ fun i => (cell (R := R) 0)⟦-n i⟧ :=
  Sigma.mapIso (fun i => cellIso (n i))

private noncomputable def shiftedCellsIso {I : Type v} (n : I → ℤ) :
    (∐ fun i => cell (R := R) (n i))⟦(1 : ℤ)⟧ ≅
      ∐ fun i => (cell (R := R) 0)⟦-n i + 1⟧ :=
  PreservesCoproduct.iso (CategoryTheory.shiftFunctor _ (1 : ℤ)) _ ≪≫
    Sigma.mapIso (fun i => (CategoryTheory.shiftFunctor _ (1 : ℤ)).mapIso (cellIso (n i)) ≪≫
      (shiftFunctorAdd _ (-n i) 1).symm.app _)

private theorem telescope_shortExact (M : CochainComplex (ModuleCat.{v} R) ℤ) :
    (ShortComplex.mk (Telescope.alpha (diagram M)) (Telescope.beta (diagram M))
      (Telescope.alpha_beta (diagram M))).ShortExact := by
  let D := diagram M
  let S := ShortComplex.mk (Telescope.alpha D) (Telescope.beta D) (Telescope.alpha_beta D)
  have hm (n : ℤ) : IsSplitMono ((Telescope.alpha D).f n) := by
    let F := fun p => (D.obj p).X n
    let ι := fun p => (Sigma.ι D.obj p).f n
    let E := HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) n
    have hc : IsColimit (Cofan.mk ((∐ D.obj).X n) ι) :=
      (isColimitMapCoconeCofanMkEquiv E D.obj (Sigma.ι D.obj)).toFun
        (isColimitOfPreserves E (coproductIsCoproduct D.obj))
    apply Telescope.isSplitMono_of_cofan ι hc
      (fun p => (D.map (homOfLE (Nat.le_succ p))).f n)
    · exact fun p => diagram_map_succ_isSplitMono M p n
    · intro p
      exact HomologicalComplex.congr_hom (Telescope.ι_alpha D p) n
  have : Mono S.f := HomologicalComplex.mono_of_mono_f _ (fun n => by
    have := hm n
    infer_instance)
  have hc := Telescope.isCokernel D
  exact { exact := ShortComplex.exact_of_g_is_cokernel S hc
          mono_f := inferInstance
          epi_g := epi_of_isColimit_cofork hc }

private theorem exists_splitFilteredFreeResolution (M : CochainComplex (ModuleCat.{v} R) ℤ) :
    Nonempty (SplitFilteredFreeResolution M) := by
  let D := diagram M
  let f := colimit.desc D (augmentationCocone M)
  have hf : QuasiIso f := augmentation_quasiIso M
  let S := ShortComplex.mk (Telescope.alpha D) (Telescope.beta D) (Telescope.alpha_beta D)
  have hS : S.ShortExact := telescope_shortExact M
  let δ := inv (DerivedCategory.Q.map f) ≫ DerivedCategory.triangleOfSESδ hS
  have hδ : Triangle.mk (DerivedCategory.Q.map S.f)
      (DerivedCategory.Q.map (S.g ≫ f)) δ ∈ distinguishedTriangles := by
    apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (DerivedCategory.Q.map f)).symm
      ?_ ?_ ?_
    · simp
    · simp [DerivedCategory.triangleOfSES, Functor.map_comp]
    · simp [δ, DerivedCategory.triangleOfSES]
  refine ⟨{
    P := colimit D
    f := f
    quasiIso := hf
    F := D.obj
    inclusion := fun p => D.map (homOfLE (Nat.le_succ p))
    toP := colimit.ι D
    inclusion_toP := fun p => colimit.w D _
    toP_injective := colimit_ι_injective M
    inclusion_split := ?_
    exhaustive := colimit_exhaustive M
    quotient := fun p => (attachmentCells (stages M p).hom)⟦(1 : ℤ)⟧
    quotientMap := fun p =>
      (mappingCone.triangleRotateShortComplex (attachmentMap (stages M p).hom)).g
    inclusion_quotientMap := ?_
    quotient_shortExact := ?_
    bottomShiftIndex := Cycles M
    bottomShiftAmount := fun z => -z.1
    bottomIso := cellsIso (fun z : Cycles M => z.1)
    shiftIndex := fun p => Attachment (stages M p).hom
    shiftAmount := fun p z => -(z.n + 1) + 1
    quotientIso := fun p => shiftedCellsIso (fun z : Attachment (stages M p).hom => z.n + 1)
    telescope := ∐ D.obj
    telescopeIso := Iso.refl _
    alpha := S.f
    beta := S.g
    alpha_ι := ?_
    beta_ι := ?_
    delta := δ
    telescope_distinguished := hδ }⟩
  · exact diagram_map_succ_isSplitMono M
  · intro p
    dsimp [D]
    rw [diagram_map_succ]
    exact (mappingCone.triangleRotateShortComplex (attachmentMap (stages M p).hom)).zero
  · intro p
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    convert (mappingCone.triangleRotateShortComplexSplitting (attachmentMap (stages M p).hom)
      n).shortExact using 1
    simp only [D, diagram_map_succ, nextInclusion]
    rfl
  · intro p
    simpa [S] using Telescope.ι_alpha D p
  · intro p
    simpa [S] using Telescope.ι_beta D p

end Resolution

private theorem property_of_splitFilteredFreeResolution
    {R : Type u} [Ring R] [Small.{v} R]
    (hpres : ∀ I : Type v,
      PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := ModuleCat.{v} R)))
    (T : DerivedCategory (ModuleCat.{v} R) → Prop)
    (hsum : ∀ {I : Type v} (K : I → DerivedCategory (ModuleCat.{v} R)) [HasCoproduct K],
      (∀ i, T (K i)) → T (∐ K))
    (htri : ∀ Δ : Triangle (DerivedCategory (ModuleCat.{v} R)),
      Δ ∈ distinguishedTriangles →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧
        (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂))
    (hshift : ∀ k : ℤ, T (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
      (ModuleCat.of R (Shrink.{v} R)))⟦k⟧))
    {M : CochainComplex (ModuleCat.{v} R) ℤ} (r : SplitFilteredFreeResolution M) :
    T (DerivedCategory.Q.obj M) := by
  have hiso : ∀ {X Y}, (X ≅ Y) → T X → T Y := property_of_iso T htri
  have hcell (I : Type v) (s : I → ℤ) :
      T (DerivedCategory.Q.obj (∐ (fun i : I =>
        ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj
          (ModuleCat.of R (Shrink.{v} R)))⟦s i⟧))) := by
    have := hpres I
    exact property_map_coproduct DerivedCategory.Q T hiso hsum _ fun i =>
      hiso ((DerivedCategory.Q.commShiftIso (s i)).app _).symm (hshift (s i))
  have hF : ∀ p, T (DerivedCategory.Q.obj (r.F p)) := by
    intro p
    induction p with
    | zero =>
      exact hiso (DerivedCategory.Q.mapIso r.bottomIso).symm
        (hcell r.bottomShiftIndex r.bottomShiftAmount)
    | succ p hp =>
      have hquot : T (DerivedCategory.Q.obj (r.quotient p)) :=
        hiso (DerivedCategory.Q.mapIso (r.quotientIso p)).symm
          (hcell (r.shiftIndex p) (r.shiftAmount p))
      exact (htri _ (DerivedCategory.triangleOfSES_distinguished
        (r.quotient_shortExact p))).2 hp hquot
  have := hpres (ULift.{v} ℕ)
  have : PreservesColimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q (C := ModuleCat.{v} R)) :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift : ULift.{v} ℕ ≃ ℕ)) _
  have htel : T (DerivedCategory.Q.obj r.telescope) :=
    hiso (DerivedCategory.Q.mapIso r.telescopeIso).symm
      (property_map_coproduct DerivedCategory.Q T hiso hsum r.F hF)
  exact (htri _ r.telescope_distinguished).1 htel htel

private theorem property_of_exists_splitFilteredFreeResolution
    {R : Type u} [Ring R] [Small.{v} R]
    (hpres : ∀ I : Type v,
      PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := ModuleCat.{v} R)))
    (hres : ∀ M : CochainComplex (ModuleCat.{v} R) ℤ,
      Nonempty (SplitFilteredFreeResolution M))
    (T : DerivedCategory (ModuleCat.{v} R) → Prop)
    (hsum : ∀ {I : Type v} (K : I → DerivedCategory (ModuleCat.{v} R)) [HasCoproduct K],
      (∀ i, T (K i)) → T (∐ K))
    (htri : ∀ Δ : Triangle (DerivedCategory (ModuleCat.{v} R)),
      Δ ∈ distinguishedTriangles →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧
        (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂))
    (hshift : ∀ k : ℤ, T (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
      (ModuleCat.of R (Shrink.{v} R)))⟦k⟧))
    (K : DerivedCategory (ModuleCat.{v} R)) : T K := by
  obtain ⟨r⟩ := hres (DerivedCategory.Q.objPreimage K)
  exact property_of_iso T htri (DerivedCategory.Q.objObjPreimageIso K)
    (property_of_splitFilteredFreeResolution hpres T hsum htri hshift r)

/-- Every complex has a split filtered resolution whose graded pieces are
coproducts of shifts of the ring and whose filtration yields the canonical telescope triangle.
Moreover, a property of objects of `D(R)` that is preserved by coproducts, satisfies
two-out-of-three for distinguished triangles, and holds for every shift of `R`, holds for every
object of `D(R)`. -/
@[stacks 09PB]
theorem property_of_coproducts_of_two_out_of_three_of_shifts {R : Type u} [Ring R]
    [Small.{v} R] :
    (∀ M : CochainComplex (ModuleCat.{v} R) ℤ, Nonempty (SplitFilteredFreeResolution M)) ∧
      ∀ (T : DerivedCategory (ModuleCat.{v} R) → Prop),
        (∀ {I : Type v} (K : I → DerivedCategory (ModuleCat.{v} R)) [HasCoproduct K],
          (∀ i, T (K i)) → T (∐ K)) →
        (∀ (Δ : Triangle (DerivedCategory (ModuleCat.{v} R))),
          Δ ∈ distinguishedTriangles →
            (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧
            (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
            (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
        (∀ k : ℤ, T (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
          (ModuleCat.of R (Shrink.{v} R)))⟦k⟧)) →
        ∀ K, T K := by
  have hres := Resolution.exists_splitFilteredFreeResolution (R := R)
  refine ⟨hres, ?_⟩
  intro T hsum htri hshift K
  exact property_of_exists_splitFilteredFreeResolution moduleCat_Q_preservesCoproducts
    hres T hsum (fun Δ hΔ => ⟨(htri Δ hΔ).1, (htri Δ hΔ).2.1⟩) hshift K

end CochainComplex.KFlat

end

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlat.CoproductBridge

/-- A Grothendieck abelian category has exact coproducts indexed by the types of its Grothendieck
universe: the coproducts exist, each coproduct functor preserves finite colimits because it is a
left adjoint, and it preserves finite limits by `AB4OfSize.ofShape`. -/
theorem hasExactCoproducts_of_grothendieck.{t, u, v} {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{t} A] : HasExactCoproducts.{t} A :=
  ⟨inferInstance, fun _ ↦ ⟨inferInstance, inferInstance⟩⟩

/-- In a Grothendieck abelian category the localization `Q : C(A) ⥤ D(A)` preserves coproducts
indexed by an arbitrary type of the Grothendieck universe. -/
theorem preservesCoproducts_Q_of_grothendieck.{t, z, u, v} {A : Type u} [Category.{v} A]
    [Abelian A] [IsGrothendieckAbelian.{t} A] [HasDerivedCategory.{z} A] (I : Type t) :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) :=
  derivedCategory_Q_preservesCoproductsOfShape A hasExactCoproducts_of_grothendieck I

end CochainComplex.KFlat.CoproductBridge

end

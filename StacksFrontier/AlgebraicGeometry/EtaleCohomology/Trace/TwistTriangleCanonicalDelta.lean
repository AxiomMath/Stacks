module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusBoundary
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality

/-!
# The connecting morphism of the twisted triangle is the canonical one

Let `F₁ : 𝒞 ⥤ 𝒟` and `F₂ : 𝒟 ⥤ Mod_R` be additive functors, `F₁` preserving injective objects.
For a short exact sequence `0 → K₁ → K₂ → K₃ → 0` of bounded below complexes of `𝒞`,
`CategoryTheory.Functor.twistTriangle` reads the connecting morphism
`RF₂RF₁(K₃) ⟶ RF₂RF₁(K₁)[1]` off a twisted injective resolution chosen by choice.  This file
proves that it is the canonical one, the image under the exact functor `RF₂ ∘ RF₁` of the
connecting morphism `K₃ ⟶ K₁[1]` of the distinguished triangle of the sequence in `D⁺(𝒞)`
(`Stacks.Cohomology.RightDerivedBoundary.plusδ`).  In particular it does not depend on the
resolution, and it is natural in the short exact sequence.

For `F₁ = f_*` and `F₂ = Γ` this applies to
`Stacks.EtaleCohomology.compactSupportFrobeniusTriangle`: the connecting maps of the long exact
sequence of `H^i_c(X_k̄, -)` are natural in the short exact sequence as well as
`π_X^*`-equivariant. This is the naturality used for `H⁰_loc ⊆ H¹_c` in Weil II 1.8
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), for the transition maps of an ℓ-adic sheaf
and for the action of the coefficients.

The standard model `HasDerivedCategory.standard` is used because the twisted triangle is defined
there.

## Main results

* `Stacks.Cohomology.RightDerivedBoundary.ι_map_mapCochainComplexPlusDerivedUnit_app`: the unit
  `mapCochainComplexPlusDerivedUnit`, read in `D(ℬ)`, is `unitD`.
* `Stacks.Cohomology.RightDerivedBoundary.plusδ_comp_unit`: the unit carries the connecting
  morphism of `F` applied to a sequence to `RF` of the connecting morphism, in `D⁺(ℬ)`.
* `CategoryTheory.Functor.twistTriangle_mor₃_eq`: the connecting morphism of the twisted triangle
  is the canonical one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Pretriangulated

namespace Stacks.Cohomology.RightDerivedBoundary

section Unit

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

/-- The image in `D(𝒞)` of the component at `L` of `DerivedCategory.Plus.quotientCompQhIso` is the
component at `L.obj` of `DerivedCategory.quotientCompQhIso`. -/
theorem ι_map_plusQuotientCompQhIso_hom_app {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (L : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.quotientCompQhIso C).hom.app L) =
      (DerivedCategory.quotientCompQhIso C).hom.app L.obj := by
  rw [DerivedCategory.Plus.quotientCompQhIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  show 𝟙 _ ≫ (DerivedCategory.Qh.map (𝟙 _) ≫
    (DerivedCategory.quotientCompQhIso C).hom.app L.obj) = _
  rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The image in `D(𝒞)` of the inverse of `DerivedCategory.Plus.quotientCompQhIso` at `L` is the
inverse of `DerivedCategory.quotientCompQhIso` at `L.obj`. -/
theorem ι_map_plusQuotientCompQhIso_inv_app {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (L : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.quotientCompQhIso C).inv.app L) =
      (DerivedCategory.quotientCompQhIso C).inv.app L.obj := by
  rw [DerivedCategory.Plus.quotientCompQhIso, Functor.fullyFaithfulCancelRight_inv_app,
    Functor.map_preimage]
  show ((DerivedCategory.quotientCompQhIso C).inv.app L.obj ≫
    DerivedCategory.Qh.map (𝟙 _)) ≫ 𝟙 _ = _
  rw [Category.comp_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The two lifts to `D⁺` of `quotientCompQhIso` agree. -/
theorem plusQuotientCompQhIso_hom_app_eq {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (L : CochainComplex.Plus C) :
    (DerivedCategory.Plus.quotientCompQhIso C).hom.app L =
      (StacksDraft.DerivedSectionsComparison.quotientQhIsoQ C).hom.app L := by
  have hq : DerivedCategory.Plus.ι.map
      ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ C).hom.app L) =
        (DerivedCategory.quotientCompQhIso C).hom.app L.obj :=
    StacksDraft.DerivedSectionsComparison.liftNatIso_hom_app _ _ _ _ L
  exact Functor.map_injective DerivedCategory.Plus.ι ((ι_map_plusQuotientCompQhIso_hom_app L).trans
    hq.symm)

/-- **The unit of `mapCochainComplexPlusDerivedUnit`, read in `D(ℬ)`, is `unitD`.** -/
theorem ι_map_mapCochainComplexPlusDerivedUnit_app (L : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map ((Functor.mapCochainComplexPlusDerivedUnit F).app L) =
      unitD F L := by
  rw [Functor.mapCochainComplexPlusDerivedUnit_app, unitD, CategoryTheory.Functor.map_comp,
    ι_map_plusQuotientCompQhIso_inv_app, plusQuotientCompQhIso_hom_app_eq]
  exact whisker_eq _ (CategoryTheory.Functor.map_comp _ _ _)

variable [F.rightDerivedFunctorPlus.CommShift ℤ]
  [NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ]

/-- **The unit carries the connecting morphism of `F` applied to a short exact sequence to `RF`
of the connecting morphism**, in `D⁺(ℬ)`: for a short exact sequence `S` of bounded below
complexes which `F` keeps short exact,
`δ(F S) ≫ u(K₁)[1] = u(K₃) ≫ RF(δ S)`, `u : F(K) ⟶ RF(K)` the unit. -/
theorem plusδ_comp_unit (S : ShortComplex (CochainComplex.Plus A)) (hS : (toSC S).ShortExact)
    (hFS : (toSC (S.map F.mapCochainComplexPlus)).ShortExact) :
    plusδ (S.map F.mapCochainComplexPlus) hFS ≫
        ((Functor.mapCochainComplexPlusDerivedUnit F).app S.X₁)⟦(1 : ℤ)⟧' =
      (Functor.mapCochainComplexPlusDerivedUnit F).app S.X₃ ≫
        Functor.mapδ F.rightDerivedFunctorPlus (plusδ S hS) := by
  refine Functor.mapδ_cancel DerivedCategory.Plus.ι _ _ _ _ ?_
  rw [mapδ_ι_plusδ, ι_map_mapCochainComplexPlusDerivedUnit_app,
    ι_map_mapCochainComplexPlusDerivedUnit_app, ← Functor.mapδ_comp]
  exact triangleOfSESδ_comp_unitD F S hS hFS

end Unit

section Composite

/-- Two squares with a shifted side, pasted; stated on variables. -/
theorem shift_paste {C : Type*} [Category* C] [HasShift C ℤ] {X Y X' Y' X'' Y'' : C}
    (P : X ⟶ Y⟦(1 : ℤ)⟧) (u : Y ⟶ Y') (u' : X ⟶ X') (M : X' ⟶ Y'⟦(1 : ℤ)⟧) (w : Y' ⟶ Y'')
    (w' : X' ⟶ X'') (N : X'' ⟶ Y''⟦(1 : ℤ)⟧) (hA : P ≫ u⟦(1 : ℤ)⟧' = u' ≫ M)
    (hB : M ≫ w⟦(1 : ℤ)⟧' = w' ≫ N) : P ≫ (u ≫ w)⟦(1 : ℤ)⟧' = (u' ≫ w') ≫ N := by
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, hA, Category.assoc, hB, Category.assoc]

variable {A B E : Type*} [Category* A] [Category* B] [Category* E] [Abelian A] [Abelian B]
  [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
  [EnoughInjectives A] [EnoughInjectives B] (F₁ : A ⥤ B) (F₂ : B ⥤ E) [F₁.Additive] [F₂.Additive]
  [F₁.rightDerivedFunctorPlus.CommShift ℤ] [NatTrans.CommShift F₁.rightDerivedFunctorPlusUnit ℤ]
  [F₂.rightDerivedFunctorPlus.CommShift ℤ] [NatTrans.CommShift F₂.rightDerivedFunctorPlusUnit ℤ]

/-- **The composite of the two units `F₂F₁(K) ⟶ RF₂RF₁(K)` carries the connecting morphism of
`F₂F₁` applied to a short exact sequence to `RF₂RF₁` of its connecting morphism**, in `D⁺`, when
`F₁` and `F₂ ∘ F₁` keep the sequence short exact. -/
theorem plusδ_comp_twistComparison (S : ShortComplex (CochainComplex.Plus A))
    (hS : (toSC S).ShortExact) (h₁ : (toSC (S.map F₁.mapCochainComplexPlus)).ShortExact)
    (h₂ : (toSC ((S.map F₁.mapCochainComplexPlus).map F₂.mapCochainComplexPlus)).ShortExact) :
    plusδ ((S.map F₁.mapCochainComplexPlus).map F₂.mapCochainComplexPlus) h₂ ≫
        ((Functor.mapCochainComplexPlusDerivedUnit F₂).app (F₁.mapCochainComplexPlus.obj S.X₁) ≫
          F₂.rightDerivedFunctorPlus.map
            ((Functor.mapCochainComplexPlusDerivedUnit F₁).app S.X₁))⟦(1 : ℤ)⟧' =
      ((Functor.mapCochainComplexPlusDerivedUnit F₂).app (F₁.mapCochainComplexPlus.obj S.X₃) ≫
          F₂.rightDerivedFunctorPlus.map
            ((Functor.mapCochainComplexPlusDerivedUnit F₁).app S.X₃)) ≫
        Functor.mapδ F₂.rightDerivedFunctorPlus
          (Functor.mapδ F₁.rightDerivedFunctorPlus (plusδ S hS)) :=
  shift_paste _ _ _ _ _ _ _ (plusδ_comp_unit F₂ (S.map F₁.mapCochainComplexPlus) h₁ h₂)
    (Functor.mapδ_naturality F₂.rightDerivedFunctorPlus (plusδ (S.map F₁.mapCochainComplexPlus) h₁)
      (Functor.mapδ F₁.rightDerivedFunctorPlus (plusδ S hS))
      ((Functor.mapCochainComplexPlusDerivedUnit F₁).app S.X₃)
      ((Functor.mapCochainComplexPlusDerivedUnit F₁).app S.X₁) (plusδ_comp_unit F₁ S hS h₁))

end Composite

section PlusShortComplex

variable {A : Type*} [Category* A] [Abelian A]

/-- A short complex of cochain complexes whose terms are bounded below, as a short complex of
bounded below complexes. -/
abbrev plusShortComplex (S : ShortComplex (CochainComplex A ℤ)) (h₁ : CochainComplex.plus A S.X₁)
    (h₂ : CochainComplex.plus A S.X₂) (h₃ : CochainComplex.plus A S.X₃) :
    ShortComplex (CochainComplex.Plus A) :=
  ShortComplex.mk (ObjectProperty.homMk S.f : (⟨S.X₁, h₁⟩ : CochainComplex.Plus A) ⟶ ⟨S.X₂, h₂⟩)
    (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus A) ⟶ ⟨S.X₃, h₃⟩)
    (by ext : 1; exact S.zero)

/-- A morphism of short complexes of bounded below complexes. -/
abbrev plusShortComplexMap {S T : ShortComplex (CochainComplex A ℤ)} (φ : S ⟶ T)
    (h₁ : CochainComplex.plus A S.X₁) (h₂ : CochainComplex.plus A S.X₂)
    (h₃ : CochainComplex.plus A S.X₃) (h₁' : CochainComplex.plus A T.X₁)
    (h₂' : CochainComplex.plus A T.X₂) (h₃' : CochainComplex.plus A T.X₃) :
    plusShortComplex S h₁ h₂ h₃ ⟶ plusShortComplex T h₁' h₂' h₃' where
  τ₁ := ObjectProperty.homMk φ.τ₁
  τ₂ := ObjectProperty.homMk φ.τ₂
  τ₃ := ObjectProperty.homMk φ.τ₃
  comm₁₂ := by ext : 1; exact φ.comm₁₂
  comm₂₃ := by ext : 1; exact φ.comm₂₃

end PlusShortComplex

/-- Cancelling an isomorphism against its shifted inverse; stated on variables. -/
theorem shift_iso_cancel {C : Type*} [Category* C] [HasShift C ℤ] {a₁ a₃ c₁ c₃ : C}
    (δS : a₃ ⟶ a₁⟦(1 : ℤ)⟧) (tδ : c₃ ⟶ c₁⟦(1 : ℤ)⟧) (e₁ : a₁ ≅ c₁) (e₃ : a₃ ≅ c₃)
    (x₁ : a₁ ⟶ c₁) (x₃ : a₃ ⟶ c₃) (h₁ : e₁.hom = x₁) (h₃ : e₃.hom = x₃)
    (key : x₃ ≫ tδ = δS ≫ x₁⟦(1 : ℤ)⟧') : e₃.hom ≫ tδ ≫ e₁.inv⟦(1 : ℤ)⟧' = δS := by
  subst h₁ h₃
  rw [← Category.assoc, key, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- Two squares with a shifted side and invertible comparison maps, pasted; stated on variables. -/
theorem shift_iso_paste {C : Type*} [Category* C] [HasShift C ℤ] {a₁ a₃ b₁ b₃ c₁ c₃ : C}
    (δS : a₃ ⟶ a₁⟦(1 : ℤ)⟧) (δT : b₃ ⟶ b₁⟦(1 : ℤ)⟧) (tδ : c₃ ⟶ c₁⟦(1 : ℤ)⟧) (m₁ : a₁ ⟶ b₁)
    (m₃ : a₃ ⟶ b₃) (k₁ : c₁ ⟶ b₁) (k₃ : c₃ ⟶ b₃) [IsIso k₁] [IsIso k₃]
    (hN : δS ≫ m₁⟦(1 : ℤ)⟧' = m₃ ≫ δT) (hK : tδ ≫ k₁⟦(1 : ℤ)⟧' = k₃ ≫ δT) :
    (m₃ ≫ inv k₃) ≫ tδ = δS ≫ (m₁ ≫ inv k₁)⟦(1 : ℤ)⟧' := by
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc δS, hN, Category.assoc, Category.assoc]
  congr 1
  rw [IsIso.inv_comp_eq, ← Category.assoc, ← hK, Category.assoc,
    ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

end Stacks.Cohomology.RightDerivedBoundary

namespace CategoryTheory.Functor

open Stacks.Cohomology.RightDerivedBoundary

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit

section TwistTriangle

universe u v u₁ v₁

variable {R : Type u} [Ring R] {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
  {P : C ⥤ C} (F₁ : C ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R) [P.Additive] [F₁.Additive]
  [F₂.Additive] [P.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects]
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
  (h₁ : CochainComplex.plus C S.X₁) (h₂ : CochainComplex.plus C S.X₂)
  (h₃ : CochainComplex.plus C S.X₃)
  {τ : S ⟶ S.map (P.mapHomologicalComplex (ComplexShape.up ℤ))} (Rs : TwistResolution P τ)

omit [P.PreservesInjectiveObjects] in
/-- **The connecting morphism of the twisted triangle is the canonical one**: the image under
`RF₂ ∘ RF₁` of the connecting morphism of the distinguished triangle of the short exact sequence
in `D⁺(𝒞)`.  It does not depend on the twisted injective resolution. -/
theorem twistTriangle_mor₃_eq :
    (twistTriangle F₁ F₂ h₁ h₂ h₃ Rs).mor₃ =
      Functor.mapδ (F₂.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
        (Functor.mapδ F₁.rightDerivedFunctorPlus (plusδ (plusShortComplex S h₁ h₂ h₃) hS)) := by
  let Sp := plusShortComplex S h₁ h₂ h₃
  let Tp := plusShortComplex Rs.T Rs.plus₁ Rs.plus₂ Rs.plus₃
  let ψp : Sp ⟶ Tp := plusShortComplexMap Rs.ψ h₁ h₂ h₃ Rs.plus₁ Rs.plus₂ Rs.plus₃
  have hT : (toSC Tp).ShortExact := Rs.shortExact
  have h₁T : (toSC (Tp.map F₁.mapCochainComplexPlus)).ShortExact :=
    CochainComplex.shortExact_map_of_splitting Rs.split F₁
  have h₂T : (toSC ((Tp.map F₁.mapCochainComplexPlus).map F₂.mapCochainComplexPlus)).ShortExact :=
    Rs.image_shortExact F₁ F₂
  -- naturality of the canonical connecting morphism along the resolution
  have hN := Functor.mapδ_naturality (F₂.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (Functor.mapδ F₁.rightDerivedFunctorPlus (plusδ Sp hS))
    (Functor.mapδ F₁.rightDerivedFunctorPlus (plusδ Tp hT))
    (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψp.τ₃))
    (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψp.τ₁))
    (Functor.mapδ_naturality F₁.rightDerivedFunctorPlus _ _ _ _
      (Stacks.Cech.Hypercohomology.plusδ_naturality (S := Sp) (S' := Tp) hS hT ψp))
  -- the comparison carries the connecting morphism of the image to the canonical one
  have hK := Functor.mapδ_naturality DerivedCategory.Plus.ι _ _ _ _
    (plusδ_comp_twistComparison F₁ F₂ Tp hT h₁T h₂T)
  rw [mapδ_ι_plusδ, ← Functor.mapδ_comp] at hK
  have := isIso_twistComparison F₁ F₂ Tp.X₁ Rs.injective₁
  have := isIso_twistComparison F₁ F₂ Tp.X₃ Rs.injective₃
  have key := shift_iso_paste _ _ _ _ _
    (DerivedCategory.Plus.ι.map (twistComparison F₁ F₂ Tp.X₁))
    (DerivedCategory.Plus.ι.map (twistComparison F₁ F₂ Tp.X₃)) hN hK
  have hiso : ∀ {K T : CochainComplex.Plus C} (ψ : K ⟶ T) (_ : QuasiIso ψ.hom)
      (hT : ∀ n, Injective (T.obj.X n)), (twistResolutionIso F₁ F₂ ψ hT).hom =
        DerivedCategory.Plus.ι.map (F₂.rightDerivedFunctorPlus.map
          (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ))) ≫
        have := isIso_twistComparison F₁ F₂ T hT
        CategoryTheory.inv (DerivedCategory.Plus.ι.map (twistComparison F₁ F₂ T)) := by
    intro K T ψ _ hT
    have := isIso_twistComparison F₁ F₂ T hT
    rw [← CategoryTheory.Functor.map_inv
      (DerivedCategory.Plus.ι : DerivedCategory.Plus (ModuleCat.{max u v} R) ⥤ _)
      (twistComparison F₁ F₂ T)]
    exact CategoryTheory.Functor.map_comp
      (DerivedCategory.Plus.ι : DerivedCategory.Plus (ModuleCat.{max u v} R) ⥤ _) _ _
  dsimp only [twistTriangle, Triangle.mk_mor₃, TwistResolution.iso₁, TwistResolution.iso₃]
  exact shift_iso_cancel _ _ _ _ _ _ (hiso _ Rs.quasiIso₁ Rs.injective₁)
    (hiso _ Rs.quasiIso₃ Rs.injective₃) key

omit [F₁.PreservesInjectiveObjects] in
/-- **The connecting morphism of the canonical triangle is natural** in the short exact
sequence. -/
theorem mapδ_plusδ_naturality {S S' : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (h₁ : CochainComplex.plus C S.X₁) (h₂ : CochainComplex.plus C S.X₂)
    (h₃ : CochainComplex.plus C S.X₃) (h₁' : CochainComplex.plus C S'.X₁)
    (h₂' : CochainComplex.plus C S'.X₂) (h₃' : CochainComplex.plus C S'.X₃) (φ : S ⟶ S') :
    Functor.mapδ (F₂.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
        (Functor.mapδ F₁.rightDerivedFunctorPlus (plusδ (plusShortComplex S h₁ h₂ h₃) hS)) ≫
        (twistDerivedMap F₁ F₂ h₁ h₁' φ.τ₁)⟦(1 : ℤ)⟧' =
      twistDerivedMap F₁ F₂ h₃ h₃' φ.τ₃ ≫
        Functor.mapδ (F₂.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
          (Functor.mapδ F₁.rightDerivedFunctorPlus
            (plusδ (plusShortComplex S' h₁' h₂' h₃') hS')) :=
  Functor.mapδ_naturality (F₂.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) _ _ _ _
    (Functor.mapδ_naturality F₁.rightDerivedFunctorPlus _ _ _ _
      (Stacks.Cech.Hypercohomology.plusδ_naturality (S := plusShortComplex S h₁ h₂ h₃)
        (S' := plusShortComplex S' h₁' h₂' h₃') hS hS'
        (plusShortComplexMap φ h₁ h₂ h₃ h₁' h₂' h₃')))

omit [P.PreservesInjectiveObjects] in
/-- **The connecting morphism of the twisted triangle is natural** in the short exact sequence,
whatever the twisted injective resolutions. -/
theorem twistTriangle_mor₃_naturality {S S' : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : CochainComplex.plus C S.X₁)
    (h₂ : CochainComplex.plus C S.X₂) (h₃ : CochainComplex.plus C S.X₃)
    (h₁' : CochainComplex.plus C S'.X₁) (h₂' : CochainComplex.plus C S'.X₂)
    (h₃' : CochainComplex.plus C S'.X₃)
    {τ : S ⟶ S.map (P.mapHomologicalComplex (ComplexShape.up ℤ))}
    {τ' : S' ⟶ S'.map (P.mapHomologicalComplex (ComplexShape.up ℤ))}
    (Rs : TwistResolution P τ) (Rs' : TwistResolution P τ') (φ : S ⟶ S') :
    (twistTriangle F₁ F₂ h₁ h₂ h₃ Rs).mor₃ ≫ (twistDerivedMap F₁ F₂ h₁ h₁' φ.τ₁)⟦(1 : ℤ)⟧' =
      twistDerivedMap F₁ F₂ h₃ h₃' φ.τ₃ ≫ (twistTriangle F₁ F₂ h₁' h₂' h₃' Rs').mor₃ := by
  rw [twistTriangle_mor₃_eq F₁ F₂ hS h₁ h₂ h₃ Rs, twistTriangle_mor₃_eq F₁ F₂ hS' h₁' h₂' h₃' Rs']
  exact mapδ_plusδ_naturality F₁ F₂ hS hS' h₁ h₂ h₃ h₁' h₂' h₃' φ

end TwistTriangle

end CategoryTheory.Functor

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated

/-!
# The conclusion of Stacks 0DKV along distinguished triangles in its first argument

In Situation 0DKU fix `L₀ ∈ D(𝒪_{X₀})`.  For `A₀ ∈ D(𝒪_{X₀})` the conclusion of Stacks 0DKV
for the pair `(A₀, L₀)` is
`AlgebraicGeometry.Space.RelativeDescentSituation.HomDescent`: the comparison out of the colimit
of `Hom(Lf_{i0}^*A₀, Lf_{i0}^*L₀)` to `Hom(Lf_0^*A₀, Lf_0^*L₀)` is bijective.  This file shows
that the class of `A₀` for which it holds at every shift of `A₀` is a triangulated subcategory:
it contains `0`, and it contains the third object of a distinguished triangle as soon as it
contains the other two.  This is the five lemma in the colimit, applied to the long exact
sequences that `Hom(-, Lf_{i0}^*L₀)` and `Hom(-, Lf_0^*L₀)` attach to the images of one
distinguished triangle of `D(𝒪_{X₀})` under the triangulated functors `Lf_{i0}^*` and `Lf_0^*`.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_obj₃`: the five lemma.
* `AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_of_iso`: invariance under
  isomorphism of the first argument.
* `AlgebraicGeometry.Space.RelativeDescentSituation.ShiftedHomDescent` and its closure
  properties `shiftedHomDescent_obj₁`, `shiftedHomDescent_obj₂`, `shiftedHomDescent_obj₃` and
  `shiftedHomDescent_biprod`.

## Implementation notes

The shifts are kept in the first argument, so that every map of every long exact sequence is
precomposition with the image under `Lf_{i0}^*` (or `Lf_0^*`) of a single morphism of
`D(𝒪_{X₀})`.  The transition maps and comparison maps of the system of derived homomorphism
sets commute with such precompositions by naturality of the identifications
`Lg^* ⋙ Lf^* ≅ Lk^*`, so no compatibility of those identifications with the shift is needed.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- Exactness of `Hom(F(-), M)` at the second object of the image of a distinguished
triangle. -/
theorem exists_map_mor₂_comp_eq (T : Triangle C) (hT : T ∈ distTriang C) {M : D}
    (φ : F.obj T.obj₂ ⟶ M) (hφ : F.map T.mor₁ ≫ φ = 0) :
    ∃ χ : F.obj T.obj₃ ⟶ M, F.map T.mor₂ ≫ χ = φ := by
  obtain ⟨χ, hχ⟩ := Triangle.yoneda_exact₂ _ (F.map_distinguished T hT) φ hφ
  exact ⟨χ, hχ.symm⟩

/-- Exactness of `Hom(F(-), M)` at the third object of the image of a distinguished triangle,
with the shift of the first object kept inside `F`. -/
theorem exists_map_mor₃_comp_eq (T : Triangle C) (hT : T ∈ distTriang C) {M : D}
    (φ : F.obj T.obj₃ ⟶ M) (hφ : F.map T.mor₂ ≫ φ = 0) :
    ∃ ε : F.obj (T.obj₁⟦(1 : ℤ)⟧) ⟶ M, F.map T.mor₃ ≫ ε = φ := by
  obtain ⟨ε, hε⟩ := Triangle.yoneda_exact₃ _ (F.map_distinguished T hT) φ hφ
  refine ⟨(F.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ ε, ?_⟩
  rw [hε]
  exact (Category.assoc _ _ _).symm

/-- Exactness of `Hom(F(-), M)` at the shift of the first object of a distinguished
triangle. -/
theorem exists_map_shift_mor₁_comp_eq (T : Triangle C) (hT : T ∈ distTriang C) {M : D}
    (φ : F.obj (T.obj₁⟦(1 : ℤ)⟧) ⟶ M) (hφ : F.map T.mor₃ ≫ φ = 0) :
    ∃ β : F.obj (T.obj₂⟦(1 : ℤ)⟧) ⟶ M, F.map (T.mor₁⟦(1 : ℤ)⟧') ≫ β = φ := by
  obtain ⟨β, hβ⟩ := F.exists_map_mor₃_comp_eq T.rotate (rot_of_distTriang _ hT) φ hφ
  refine ⟨-β, ?_⟩
  rw [← hβ]
  dsimp [Triangle.rotate]
  rw [F.map_neg]
  exact (Preadditive.comp_neg _ _).trans (Preadditive.neg_comp _ _).symm

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [F.CommShift ℤ] [F.IsTriangulated] in
/-- The images of two consecutive morphisms of a distinguished triangle compose to zero. -/
theorem map_mor₁_comp_map_mor₂ [F.PreservesZeroMorphisms] (T : Triangle C)
    (hT : T ∈ distTriang C) : F.map T.mor₁ ≫ F.map T.mor₂ = 0 := by
  rw [← F.map_comp, comp_distTriang_mor_zero₁₂ _ hT, F.map_zero]

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [F.CommShift ℤ] [F.IsTriangulated] in
/-- The image of the third morphism of a distinguished triangle composes to zero with the image
of the shift of its first morphism. -/
theorem map_mor₃_comp_map_shift_mor₁ [F.PreservesZeroMorphisms] (T : Triangle C)
    (hT : T ∈ distTriang C) : F.map T.mor₃ ≫ F.map (T.mor₁⟦(1 : ℤ)⟧') = 0 := by
  have h' : T.mor₃ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 :=
    neg_eq_zero.mp ((Preadditive.comp_neg T.mor₃ (T.mor₁⟦(1 : ℤ)⟧')).symm.trans
      (comp_distTriang_mor_zero₂₃ _ (rot_of_distTriang _ hT)))
  rw [← F.map_comp, h', F.map_zero]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u v

attribute [local instance 10000] HasDerivedCategory.standard



namespace DerivedPullbackComposition

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (P : DerivedPullbackComposition B S hS)

/-- The map induced by a factorisation commutes with precomposition. -/
theorem factorHom_precomp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    {A A' L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))}
    (α : A' ⟶ A)
    (φ : (smallEtaleDerivedModulePullback B S hS g).obj A ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    P.factorHom f g k h A' L ((smallEtaleDerivedModulePullback B S hS g).map α ≫ φ) =
      (smallEtaleDerivedModulePullback B S hS k).map α ≫ P.factorHom f g k h A L φ := by
  have hn := (P.iso f g k h).inv.naturality α
  simp only [Functor.comp_map] at hn
  simp only [factorHom, Iso.homCongr_apply, Functor.map_comp, Category.assoc, Iso.app_inv,
    Iso.app_hom]
  rw [← reassoc_of% hn]

/-- The map induced by a factorisation is additive. -/
theorem factorHom_sub {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    (A L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (φ ψ : (smallEtaleDerivedModulePullback B S hS g).obj A ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    P.factorHom f g k h A L (φ - ψ) = P.factorHom f g k h A L φ - P.factorHom f g k h A L ψ := by
  simp only [factorHom, Iso.homCongr_apply, Functor.map_sub, Preadditive.sub_comp,
    Preadditive.comp_sub]

/-- The map induced by a factorisation sends zero to zero. -/
theorem factorHom_zero {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    (A L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    P.factorHom f g k h A L 0 = 0 := by
  simp only [factorHom, Iso.homCongr_apply, Functor.map_zero, zero_comp, comp_zero]

end DerivedPullbackComposition

namespace RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I) (P : DerivedPullbackComposition B S hS)

/-- The pullback along `D.stageToInitial i` has a left derived functor. -/
instance hasLeftDerivedFunctor_stageToInitial (i : D.LaterIndex) :
    (smallEtaleModulePullbackOnHomotopy B S hS (D.stageToInitial i)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS D.initialSource) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- The pullback along `D.limitToInitial` has a left derived functor. -/
instance hasLeftDerivedFunctor_limitToInitial :
    (smallEtaleModulePullbackOnHomotopy B S hS D.limitToInitial).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS D.initialSource) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- The pullback along `D.sourceTransition h` has a left derived functor. -/
instance hasLeftDerivedFunctor_sourceTransition {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    (smallEtaleModulePullbackOnHomotopy B S hS (D.sourceTransition h)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS (D.stageSource i)) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- The pullback along `D.sourceProjection i` has a left derived functor. -/
instance hasLeftDerivedFunctor_sourceProjection (i : D.LaterIndex) :
    (smallEtaleModulePullbackOnHomotopy B S hS (D.sourceProjection i)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS (D.stageSource i)) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- The derived pullback along `D.stageToInitial i` commutes with the shift. -/
instance commShift_stageToInitial (i : D.LaterIndex) :
    (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).CommShift ℤ :=
  commShift_smallEtaleDerivedModulePullback B S hS _

/-- The derived pullback along `D.limitToInitial` commutes with the shift. -/
instance commShift_limitToInitial :
    (smallEtaleDerivedModulePullback B S hS D.limitToInitial).CommShift ℤ :=
  commShift_smallEtaleDerivedModulePullback B S hS _

/-- The derived pullback along `D.stageToInitial i` is a triangulated functor. -/
instance isTriangulated_stageToInitial (i : D.LaterIndex) :
    (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).IsTriangulated :=
  isTriangulated_smallEtaleDerivedModulePullback B S hS _

/-- The derived pullback along `D.limitToInitial` is a triangulated functor. -/
instance isTriangulated_limitToInitial :
    (smallEtaleDerivedModulePullback B S hS D.limitToInitial).IsTriangulated :=
  isTriangulated_smallEtaleDerivedModulePullback B S hS _

/-- `D(𝒪_{X₀})`, in the spelling of the source of the derived pullbacks of the situation. -/
abbrev InitialDerived : Type (u + 1) :=
  DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS D.initialSource))

variable {D}

/-- The transition maps commute with precomposition by the image of a morphism `α : A' ⟶ A`. -/
theorem homTransition_precomp {A A' : D.InitialDerived} (L : D.InitialDerived) (α : A' ⟶ A)
    {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj A ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L) :
    D.homTransition P A' L h
        ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map α ≫ φ) =
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).map α ≫
        D.homTransition P A L h φ := by
  unfold homTransition
  exact P.factorHom_precomp _ _ _ _ α φ

/-- The comparison maps commute with precomposition by the image of a morphism `α : A' ⟶ A`. -/
theorem homComparison_precomp {A A' : D.InitialDerived} (L : D.InitialDerived) (α : A' ⟶ A)
    (i : D.LaterIndex)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj A ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L) :
    D.homComparison P A' L i
        ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map α ≫ φ) =
      (smallEtaleDerivedModulePullback B S hS D.limitToInitial).map α ≫
        D.homComparison P A L i φ := by
  unfold homComparison
  exact P.factorHom_precomp _ _ _ _ α φ

/-- The transition maps are additive. -/
theorem homTransition_sub (A L : D.InitialDerived) {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ ψ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj A ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L) :
    D.homTransition P A L h (φ - ψ) = D.homTransition P A L h φ - D.homTransition P A L h ψ := by
  unfold homTransition
  exact P.factorHom_sub (D.sourceTransition h) (D.stageToInitial i) (D.stageToInitial j)
    (D.sourceTransition_comp_stageToInitial h) A L φ ψ

/-- The comparison maps are additive. -/
theorem homComparison_sub (A L : D.InitialDerived) (i : D.LaterIndex)
    (φ ψ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj A ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L) :
    D.homComparison P A L i (φ - ψ) = D.homComparison P A L i φ - D.homComparison P A L i ψ := by
  unfold homComparison
  exact P.factorHom_sub (D.sourceProjection i) (D.stageToInitial i) D.limitToInitial
    (D.sourceProjection_comp_stageToInitial i) A L φ ψ

/-- The transition maps send zero to zero. -/
theorem homTransition_zero (A L : D.InitialDerived) {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.homTransition P A L h 0 = 0 := by
  unfold homTransition
  exact P.factorHom_zero (D.sourceTransition h) (D.stageToInitial i) (D.stageToInitial j)
    (D.sourceTransition_comp_stageToInitial h) A L

/-- The comparison maps send zero to zero. -/
theorem homComparison_zero (A L : D.InitialDerived) (i : D.LaterIndex) :
    D.homComparison P A L i 0 = 0 := by
  unfold homComparison
  exact P.factorHom_zero (D.sourceProjection i) (D.stageToInitial i) D.limitToInitial
    (D.sourceProjection_comp_stageToInitial i) A L

/-- The injectivity half of `HomDescent` in additive form: a morphism at a stage whose image at
the limit vanishes vanishes at a later stage. -/
theorem HomDescent.exists_homTransition_eq_zero {A L : D.InitialDerived}
    (hA : D.HomDescent P A L) {i : D.LaterIndex}
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj A ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L)
    (hφ : D.homComparison P A L i φ = 0) :
    ∃ (j : D.LaterIndex) (h : i.1 ≤ j.1), D.homTransition P A L h φ = 0 := by
  obtain ⟨j, h, hj⟩ := hA.2 i φ 0 (hφ.trans (D.homComparison_zero P A L i).symm)
  exact ⟨j, h, hj.trans (D.homTransition_zero P A L h)⟩

/-- A morphism at a stage, moved to a later stage. -/
theorem homComparison_homTransition' (A L : D.InitialDerived) {i j : D.LaterIndex}
    (h : i.1 ≤ j.1)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj A ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L) :
    D.homComparison P A L j (D.homTransition P A L h φ) = D.homComparison P A L i φ :=
  D.homComparison_homTransition P A L h φ

/-- Exactness of `Hom(Lf_{i0}^*(-), M)` at the third object of a distinguished triangle. -/
theorem exists_stage_mor₃_comp_eq (i : D.LaterIndex) (T : Triangle D.InitialDerived)
    (hT : T ∈ distTriang _) {M : DerivedCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (D.stageSource i)))}
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj T.obj₃ ⟶ M)
    (hφ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map T.mor₂ ≫ φ = 0) :
    ∃ ε : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj
        (T.obj₁⟦(1 : ℤ)⟧) ⟶ M,
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map T.mor₃ ≫ ε = φ :=
  Functor.exists_map_mor₃_comp_eq _ T hT φ hφ

/-- The transition maps of the system of derived homomorphism sets compose. -/
theorem homTransition_homTransition' (A L : D.InitialDerived) {i j k : D.LaterIndex}
    (hij : i.1 ≤ j.1) (hjk : j.1 ≤ k.1)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj A ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L) :
    D.homTransition P A L hjk (D.homTransition P A L hij φ) =
      D.homTransition P A L (hij.trans hjk) φ :=
  D.homTransition_homTransition P A L hij hjk φ

/-- The surjectivity half of the five lemma for Stacks 0DKV. -/
theorem homDescent_obj₃_surjective (T : Triangle D.InitialDerived)
    (hT : T ∈ distTriang _) (L : D.InitialDerived)
    (hA : D.HomDescent P T.obj₁ L) (hB : D.HomDescent P T.obj₂ L)
    (hA₁ : D.HomDescent P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L)
    (ψ : (smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj T.obj₃ ⟶
      (smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj L) :
    ∃ (i : D.LaterIndex)
      (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj T.obj₃ ⟶
        (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L),
      D.homComparison P T.obj₃ L i φ = ψ := by
  obtain ⟨i, φB, hφB⟩ := hB.1
    ((smallEtaleDerivedModulePullback B S hS D.limitToInitial).map T.mor₂ ≫ ψ)
  have h0 : D.homComparison P T.obj₁ L i
      ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map T.mor₁ ≫ φB) = 0 := by
    rw [homComparison_precomp, hφB, ← Category.assoc,
      Functor.map_mor₁_comp_map_mor₂ (smallEtaleDerivedModulePullback B S hS D.limitToInitial) T hT,
      zero_comp]
  obtain ⟨j, hij, hj⟩ := HomDescent.exists_homTransition_eq_zero P hA _ h0
  rw [homTransition_precomp] at hj
  obtain ⟨χ, hχ⟩ := Functor.exists_map_mor₂_comp_eq
    (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)) T hT _ hj
  have hd : (smallEtaleDerivedModulePullback B S hS D.limitToInitial).map T.mor₂ ≫
      (ψ - D.homComparison P T.obj₃ L j χ) = 0 := by
    rw [Preadditive.comp_sub, ← homComparison_precomp, hχ,
      homComparison_homTransition' P T.obj₂ L hij, hφB, sub_self]
  obtain ⟨ε, hε⟩ := Functor.exists_map_mor₃_comp_eq
    (smallEtaleDerivedModulePullback B S hS D.limitToInitial) T hT _ hd
  obtain ⟨k, εk, hεk⟩ := hA₁.1 ε
  obtain ⟨m, hjm, hkm⟩ := D.isDirected_laterIndex.directed j k
  refine ⟨m, D.homTransition P T.obj₃ L hjm χ +
    (smallEtaleDerivedModulePullback B S hS (D.stageToInitial m)).map T.mor₃ ≫
      D.homTransition P _ L hkm εk, ?_⟩
  have hadd : ∀ a b, D.homComparison P T.obj₃ L m (a + b) =
      D.homComparison P T.obj₃ L m a + D.homComparison P T.obj₃ L m b := fun a b ↦ by
    have := D.homComparison_sub P T.obj₃ L m (a + b) b
    rw [add_sub_cancel_right] at this
    rw [this, sub_add_cancel]
  rw [hadd, homComparison_precomp, homComparison_homTransition' P T.obj₃ L hjm,
    homComparison_homTransition' P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L hkm, hεk, hε,
    add_sub_cancel]

/-- The injectivity half of the five lemma for Stacks 0DKV. -/
theorem homDescent_obj₃_injective (T : Triangle D.InitialDerived)
    (hT : T ∈ distTriang _) (L : D.InitialDerived)
    (hB : D.HomDescent P T.obj₂ L) (hA₁ : D.HomDescent P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L)
    (hB₁ : D.HomDescent P (T.obj₂⟦(1 : ℤ)⟧ : D.InitialDerived) L) (i : D.LaterIndex)
    (φ φ' : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj T.obj₃ ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L)
    (hφ : D.homComparison P T.obj₃ L i φ = D.homComparison P T.obj₃ L i φ') :
    ∃ (j : D.LaterIndex) (h : i.1 ≤ j.1),
      D.homTransition P T.obj₃ L h φ = D.homTransition P T.obj₃ L h φ' := by
  have hz : D.homComparison P T.obj₃ L i (φ - φ') = 0 := by
    rw [homComparison_sub, hφ, sub_self]
  have h0 : D.homComparison P T.obj₂ L i
      ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map T.mor₂ ≫
        (φ - φ')) = 0 := by
    rw [homComparison_precomp, hz, comp_zero]
  obtain ⟨j, hij, hj⟩ := HomDescent.exists_homTransition_eq_zero P hB _ h0
  rw [homTransition_precomp] at hj
  obtain ⟨ε, hε⟩ := exists_stage_mor₃_comp_eq j T hT _ hj
  have hε0 : (smallEtaleDerivedModulePullback B S hS D.limitToInitial).map T.mor₃ ≫
      D.homComparison P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L j ε = 0 := by
    rw [← homComparison_precomp, hε, homComparison_homTransition' P T.obj₃ L hij, hz]
  obtain ⟨β, hβ⟩ := Functor.exists_map_shift_mor₁_comp_eq
    (smallEtaleDerivedModulePullback B S hS D.limitToInitial) T hT _ hε0
  obtain ⟨k, βk, hβk⟩ := hB₁.1 β
  obtain ⟨m, hjm, hkm⟩ := D.isDirected_laterIndex.directed j k
  have hm : D.homComparison P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L m
      (D.homTransition P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L hjm ε) =
      D.homComparison P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L m
        ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial m)).map
          (T.mor₁⟦(1 : ℤ)⟧') ≫
            D.homTransition P (T.obj₂⟦(1 : ℤ)⟧ : D.InitialDerived) L hkm βk) := by
    rw [homComparison_precomp,
      homComparison_homTransition' P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L hjm,
      homComparison_homTransition' P (T.obj₂⟦(1 : ℤ)⟧ : D.InitialDerived) L hkm, hβk, hβ]
  obtain ⟨n, hmn, hn⟩ := hA₁.2 m _ _ hm
  refine ⟨n, hij.trans (hjm.trans hmn), ?_⟩
  have e1 := (homTransition_homTransition' P T.obj₃ L hij (hjm.trans hmn) (φ - φ')).symm
  have e2 := homTransition_homTransition' P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L hjm hmn ε
  have h31n := Functor.map_mor₃_comp_map_shift_mor₁
    (smallEtaleDerivedModulePullback B S hS (D.stageToInitial n)) T hT
  rw [← sub_eq_zero, ← homTransition_sub, e1]
  rw [← hε]
  rw [homTransition_precomp]
  rw [← e2]
  have hfin := hn.trans (homTransition_precomp P L (T.mor₁⟦(1 : ℤ)⟧') hmn
    (D.homTransition P (T.obj₂⟦(1 : ℤ)⟧ : D.InitialDerived) L hkm βk))
  exact (congrArg ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial n)).map T.mor₃ ≫ ·)
    hfin).trans
    (((reassoc_of% h31n) _).trans zero_comp)

/-- **The five lemma for Stacks 0DKV.**  For a distinguished triangle `A ⟶ B ⟶ C ⟶ A⟦1⟧` of
`D(𝒪_{X₀})`, if the conclusion of the tag holds for `A`, `B`, `A⟦1⟧` and `B⟦1⟧` against `L`,
it holds for `C`. -/
theorem homDescent_obj₃ (T : Triangle D.InitialDerived)
    (hT : T ∈ distTriang _) (L : D.InitialDerived)
    (hA : D.HomDescent P T.obj₁ L) (hB : D.HomDescent P T.obj₂ L)
    (hA₁ : D.HomDescent P (T.obj₁⟦(1 : ℤ)⟧ : D.InitialDerived) L)
    (hB₁ : D.HomDescent P (T.obj₂⟦(1 : ℤ)⟧ : D.InitialDerived) L) :
    D.HomDescent P T.obj₃ L :=
  ⟨fun ψ ↦ homDescent_obj₃_surjective P T hT L hA hB hA₁ ψ,
    fun i φ φ' hφ ↦ homDescent_obj₃_injective P T hT L hB hA₁ hB₁ i φ φ' hφ⟩

/-- **The conclusion of Stacks 0DKV is invariant under isomorphism of its first argument.** -/
theorem homDescent_of_iso {A A' L : D.InitialDerived} (e : A ≅ A')
    (hA : D.HomDescent P A L) : D.HomDescent P A' L := by
  refine ⟨fun ψ ↦ ?_, fun i φ φ' hφ ↦ ?_⟩
  · obtain ⟨i, φ, hφ⟩ := hA.1
      ((smallEtaleDerivedModulePullback B S hS D.limitToInitial).map e.hom ≫ ψ)
    refine ⟨i, (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map e.inv ≫ φ, ?_⟩
    rw [homComparison_precomp, hφ, ← Category.assoc, ← Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · have h : D.homComparison P A L i
        ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map e.hom ≫ φ) =
        D.homComparison P A L i
          ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map e.hom ≫ φ') := by
      rw [homComparison_precomp, homComparison_precomp, hφ]
    obtain ⟨j, hij, hj⟩ := hA.2 i _ _ h
    refine ⟨j, hij, ?_⟩
    have key : ∀ χ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj A' ⟶
        (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L,
        D.homTransition P A' L hij χ =
          (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).map e.inv ≫
            D.homTransition P A L hij
              ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).map e.hom ≫ χ) :=
      fun χ ↦ by
        rw [homTransition_precomp, ← Category.assoc, ← Functor.map_comp, e.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp]
    rw [key φ, key φ', hj]

/-- The conclusion of Stacks 0DKV at every shift of the first argument. -/
def ShiftedHomDescent (A L : D.InitialDerived) : Prop :=
  ∀ n : ℤ, D.HomDescent P (A⟦n⟧ : D.InitialDerived) L

/-- `ShiftedHomDescent` is invariant under isomorphism of its first argument. -/
theorem shiftedHomDescent_of_iso {A A' L : D.InitialDerived} (e : A ≅ A')
    (hA : D.ShiftedHomDescent P A L) : D.ShiftedHomDescent P A' L :=
  fun n ↦ homDescent_of_iso P ((shiftFunctor _ n).mapIso e) (hA n)

/-- `ShiftedHomDescent` is stable under shifts of its first argument. -/
theorem shiftedHomDescent_shift {A L : D.InitialDerived} (hA : D.ShiftedHomDescent P A L)
    (m : ℤ) : D.ShiftedHomDescent P (A⟦m⟧ : D.InitialDerived) L :=
  fun n ↦ homDescent_of_iso P ((shiftFunctorAdd' _ m n (m + n) rfl).app A) (hA (m + n))

/-- **The class of first arguments satisfying the conclusion of Stacks 0DKV at every shift
contains the third object of a distinguished triangle whose other two objects it contains.** -/
theorem shiftedHomDescent_obj₃ (T : Triangle D.InitialDerived) (hT : T ∈ distTriang _)
    (L : D.InitialDerived) (hA : D.ShiftedHomDescent P T.obj₁ L)
    (hB : D.ShiftedHomDescent P T.obj₂ L) :
    D.ShiftedHomDescent P T.obj₃ L := fun n ↦
  homDescent_obj₃ P ((Triangle.shiftFunctor _ n).obj T) (Triangle.shift_distinguished T hT n) L
    (hA n) (hB n) (shiftedHomDescent_shift P hA n 1) (shiftedHomDescent_shift P hB n 1)

/-- The first object of a distinguished triangle, from the other two. -/
theorem shiftedHomDescent_obj₁ (T : Triangle D.InitialDerived) (hT : T ∈ distTriang _)
    (L : D.InitialDerived) (hB : D.ShiftedHomDescent P T.obj₂ L)
    (hC : D.ShiftedHomDescent P T.obj₃ L) :
    D.ShiftedHomDescent P T.obj₁ L :=
  shiftedHomDescent_obj₃ P T.invRotate.invRotate
    (inv_rot_of_distTriang _ (inv_rot_of_distTriang _ hT)) L
    (shiftedHomDescent_shift P hB (-1)) (shiftedHomDescent_shift P hC (-1))

/-- The second object of a distinguished triangle, from the other two. -/
theorem shiftedHomDescent_obj₂ (T : Triangle D.InitialDerived) (hT : T ∈ distTriang _)
    (L : D.InitialDerived) (hA : D.ShiftedHomDescent P T.obj₁ L)
    (hC : D.ShiftedHomDescent P T.obj₃ L) :
    D.ShiftedHomDescent P T.obj₂ L :=
  shiftedHomDescent_obj₃ P T.invRotate (inv_rot_of_distTriang _ hT) L
    (shiftedHomDescent_shift P hC (-1)) hA

/-- `ShiftedHomDescent` is stable under binary biproducts of its first argument. -/
theorem shiftedHomDescent_biprod {A A' L : D.InitialDerived} (hA : D.ShiftedHomDescent P A L)
    (hA' : D.ShiftedHomDescent P A' L) : D.ShiftedHomDescent P (A ⊞ A') L :=
  shiftedHomDescent_obj₂ P (binaryBiproductTriangle A A')
    (binaryBiproductTriangle_distinguished A A') L hA hA'

end RelativeDescentSituation

end AlgebraicGeometry.Space

end

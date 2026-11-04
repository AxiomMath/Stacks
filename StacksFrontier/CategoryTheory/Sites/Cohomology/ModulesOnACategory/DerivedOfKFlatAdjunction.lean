module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings

/-!
# Derived adjunction from K-flat resolutions

Let `L : Mod(R) ⥤ 𝒜` be an additive functor from modules over a commutative ring to an abelian
category, left adjoint to `G : 𝒜 ⥤ Mod(R)`. Assume `G` is exact, so that it induces
`G.mapDerivedCategory : D(𝒜) ⥤ D(Mod R)` with no deriving, and assume `L` carries a
quasi-isomorphism between K-flat complexes to a quasi-isomorphism. Then the total left derived
functor of `L` exists, and it is left adjoint to `G.mapDerivedCategory`. The derived functor is
computed on K-flat resolutions, which exist by [Stacks 06Y4].

## Main results

* `CochainComplex.KFlatAdjunction.hasLeftDerivedFunctor`: the total left derived functor of `L`
  exists.
* `CochainComplex.KFlatAdjunction.isIso_app_of_kFlat`: the comparison of any model of it with the
  degreewise `L` is invertible on K-flat complexes.
* `CochainComplex.KFlatAdjunction.derivedAdjunction`: any such model is left adjoint to
  `G.mapDerivedCategory`.
* `CochainComplex.KFlatAdjunction.isLeftDerivedFunctor_postcomp` and
  `CochainComplex.KFlatAdjunction.isLeftDerivedFunctor_postcompMapDerivedCategory`: the model is
  absolute, and after composition with the functor induced by an exact `E : 𝒜 ⥤ ℬ` it is a left
  derived functor of the degreewise `L ⋙ E`.
* `CochainComplex.KFlatAdjunction.isLeftDerivedFunctor_of_natIso`: the model transported along an
  isomorphism `L ≅ L'` of the functors being derived.

## References

* [The Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.LeftDerivedByResolutions

universe u v w u₁ v₁ w₁ u₂ v₂ w₂

namespace CochainComplex.KFlatAdjunction

variable {R : Type u} [CommRing R]

variable [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
  {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  (L : ModuleCat.{max u v} R ⥤ A) [L.Additive]

/-- The degreewise action of `L` on the unbounded homotopy category, followed by localization,
descends the degreewise action of `L` on cochain complexes: both apply `L` in each degree and
read the result in `D(𝒜)`. -/
public def quotientCompMapIso :
    HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ) ⋙
        (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (L.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (L.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso A)

section Exact

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- Degreewise `L`, localized and then pushed along the functor induced on derived categories by
an exact functor `E`, is the localization of the degreewise action of `L ⋙ E`. -/
public def mapCompMapDerivedCategoryIso :
    (L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ E.mapDerivedCategory ≅
      (L ⋙ E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (L.mapHomologicalComplex (ComplexShape.up ℤ)) E.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ E))
      (ComplexShape.up ℤ)) DerivedCategory.Q

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] in
/-- An exact functor carries a quasi-isomorphism of cochain complexes to a quasi-isomorphism,
degreewise. -/
public lemma quasiIso_mapHomologicalComplex_map {X Y : CochainComplex A ℤ} (f : X ⟶ Y)
    [QuasiIso f] : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have h : IsIso (DerivedCategory.Q.map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 ‹_›
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have : IsIso (E.mapDerivedCategoryFactors.hom.app X ≫
      DerivedCategory.Q.map ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
    rw [← E.mapDerivedCategoryFactors_hom_naturality f]; infer_instance
  exact IsIso.of_isIso_comp_left (E.mapDerivedCategoryFactors.hom.app X) _

/-- The comparison exhibiting `F ⋙ E.mapDerivedCategory` as a model of the total left derived
functor of `L ⋙ E`, for `F` a model of the total left derived functor of `L` with comparison
`β` and `E` exact. -/
public def postcompComparison
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory A)
    (β : DerivedCategory.Q ⋙ F ⟶
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ (F ⋙ E.mapDerivedCategory) ⟶
      (L ⋙ E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator DerivedCategory.Q F E.mapDerivedCategory).inv ≫
    whiskerRight β E.mapDerivedCategory ≫ (mapCompMapDerivedCategoryIso L E).hom

/-- `postcompComparison` evaluated at a complex: the comparison of `F` pushed along `E`, followed
by the identification of the degreewise actions of `L ⋙ E` and of `L` then `E`. -/
@[simp]
public lemma postcompComparison_app
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory A)
    (β : DerivedCategory.Q ⋙ F ⟶
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (postcompComparison L E F β).app K =
      E.mapDerivedCategory.map (β.app K) ≫
        (mapCompMapDerivedCategoryIso L E).hom.app K := by
  simp [postcompComparison]

end Exact

variable (hL : ∀ {X Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : X ⟶ Y), QuasiIso f →
  CochainComplex.KFlat X → CochainComplex.KFlat Y →
  QuasiIso ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map f))

include hL

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] in
/-- The homotopy-category form of the hypothesis on `L`: a quasi-isomorphism between K-flat
complexes becomes an isomorphism of `D(𝒜)` after applying `L` degreewise. -/
public lemma isIso_map_of_kFlat
    {X Y : HomotopyCategory (ModuleCat.{max u v} R) (ComplexShape.up ℤ)} (s : X ⟶ Y)
    (hs : HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ) s)
    (hX : CochainComplex.KFlat X.as) (hY : CochainComplex.KFlat Y.as) :
    IsIso ((L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map s) := by
  have hout : QuasiIso s.out :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff s.out).1
      (by rw [HomotopyCategory.quotient_map_out s]; exact hs)
  have h := hL s.out hout hX hY
  show IsIso (DerivedCategory.Qh.map ((L.mapHomotopyCategory (ComplexShape.up ℤ)).map s))
  rw [← HomotopyCategory.quotient_map_out s]
  exact (DerivedCategory.isIso_Qh_map_iff _).2
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 h)

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] in
/-- The degreewise `L`, read on the homotopy category and followed by localization, has a
pointwise total left derived functor: the K-flat complexes are a resolving class on which the
functor inverts the quasi-isomorphisms. -/
public lemma hasPointwiseLeftDerivedFunctor :
    (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) :=
  hasPointwiseLeftDerivedFunctor_of_resolutions
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
    (fun X => CochainComplex.KFlat X.as)
    CochainComplex.DerivedTensor.exists_kFlat_resolution_homotopy _
    (isIso_map_of_kFlat L hL)

/-- The comparison of any total left derived model of `L` with the degreewise `L` is invertible
on K-flat complexes. -/
public lemma isIso_app_of_kFlat
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory A)
    (β : DerivedCategory.Q ⋙ F ⟶
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (hK : CochainComplex.KFlat K) :
    IsIso (β.app K) :=
  CochainComplex.DerivedTensor.KFlatDerived.isIso_app_of_kFlat _
    (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (quotientCompMapIso L)
    (isIso_map_of_kFlat L hL) F β K hK

/-- **Transport along an isomorphism of the functor being derived.** If `F` with comparison `β`
is a model of the total left derived functor of `L` and `ε : L ≅ L'`, then `F` is a model of the
total left derived functor of `L'`, with the comparison corrected by `ε`. -/
public lemma isLeftDerivedFunctor_of_natIso {L' : ModuleCat.{max u v} R ⥤ A} [L'.Additive]
    (ε : L ≅ L')
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory A)
    (β : DerivedCategory.Q ⋙ F ⟶
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))] :
    F.IsLeftDerivedFunctor
      (β ≫ whiskerRight (NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ)).hom
        DerivedCategory.Q)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) := by
  refine CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat
    _ (L'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (quotientCompMapIso L') F _ fun K hK => ?_
  have := isIso_app_of_kFlat L hL F β K hK
  show IsIso (β.app K ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ)).hom.app K))
  infer_instance

/-- **The total left derived functor of `L` exists.** -/
public lemma hasLeftDerivedFunctor :
    (L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) := by
  have := hasPointwiseLeftDerivedFunctor L hL
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
  let Uh := L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let G : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory A :=
    Uh.totalLeftDerived DerivedCategory.Qh W
  let α : DerivedCategory.Qh ⋙ G ⟶ Uh := Uh.totalLeftDerivedCounit DerivedCategory.Qh W
  let β : DerivedCategory.Q ⋙ G ⟶
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    whiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).inv G ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (HomotopyCategory.quotient _ _) α ≫ (quotientCompMapIso L).hom
  have hβ : ∀ K : CochainComplex (ModuleCat.{max u v} R) ℤ, CochainComplex.KFlat K →
      IsIso (β.app K) := by
    intro K hK
    have := isIso_app_of_resolutions W (fun X => CochainComplex.KFlat X.as)
      CochainComplex.DerivedTensor.exists_kFlat_resolution_homotopy Uh
      (isIso_map_of_kFlat L hL) DerivedCategory.Qh G α
      ((HomotopyCategory.quotient _ _).obj K) hK
    dsimp [β]
    infer_instance
  have := CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat
    _ Uh (quotientCompMapIso L) G β hβ
  exact Functor.HasLeftDerivedFunctor.mk' (L := DerivedCategory.Q) (LF := G) (α := β)

variable {G : A ⥤ ModuleCat.{max u v} R} [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **A derived adjunction from K-flat resolutions.** Let `L ⊣ G` be an adjunction of additive
functors between the modules over a commutative ring and an abelian category, with `G` exact and
`L` carrying the quasi-isomorphisms between K-flat complexes to quasi-isomorphisms. Then any
model `F` of the total left derived functor of `L` is left adjoint to the functor induced by `G`
on unbounded derived categories. -/
public def derivedAdjunction (adj : L ⊣ G)
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory A)
    (β : DerivedCategory.Q ⋙ F ⟶
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))] :
    F ⊣ G.mapDerivedCategory := by
  let W_R := HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
  let W_A := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let γ : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.mapDerivedCategory := G.mapDerivedCategoryFactors.inv
  have : G.mapDerivedCategory.IsRightDerivedFunctor γ W_A :=
    Functor.isRightDerivedFunctor_of_inverts W_A _ G.mapDerivedCategoryFactors
  have : (G.mapDerivedCategory ⋙ F).IsRightDerivedFunctor
      (whiskerRight γ F ≫ (Functor.associator _ _ _).hom) W_A :=
    Functor.isRightDerivedFunctor_of_inverts W_A _
      ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight G.mapDerivedCategoryFactors F)
  have : (F ⋙ G.mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ whiskerRight β G.mapDerivedCategory) W_R :=
    CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_postcomp_of_isIso_on_kFlat
      _ (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (quotientCompMapIso L)
      F β (isIso_app_of_kFlat L hL F β) G.mapDerivedCategory
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).derived W_R W_A β γ

section Exact

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- **Absoluteness of the total left derived functor of `L`.** A model `F` of it stays a left
derived functor after composition with an arbitrary functor out of `D(𝒜)`, the comparison being
the whiskered one. -/
public lemma isLeftDerivedFunctor_postcomp {H : Type*} [Category H]
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory A)
    (β : DerivedCategory.Q ⋙ F ⟶
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))]
    (Ψ : DerivedCategory A ⥤ H) :
    (F ⋙ Ψ).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Q F Ψ).inv ≫ whiskerRight β Ψ)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) :=
  CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_postcomp_of_isIso_on_kFlat
    _ (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (quotientCompMapIso L)
    F β (isIso_app_of_kFlat L hL F β) Ψ

/-- **The total left derived functor of `L` composed with an exact functor.** If `F` with
comparison `β` is a model of the total left derived functor of `L` and `E : 𝒜 ⥤ ℬ` is exact,
then `F ⋙ E.mapDerivedCategory` is a model of the total left derived functor of `L ⋙ E`, with
comparison `postcompComparison L E F β`. -/
public lemma isLeftDerivedFunctor_postcompMapDerivedCategory
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory A)
    (β : DerivedCategory.Q ⋙ F ⟶
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))] :
    (F ⋙ E.mapDerivedCategory).IsLeftDerivedFunctor (postcompComparison L E F β)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) := by
  refine CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat
    _ ((L ⋙ E).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (quotientCompMapIso (L ⋙ E)) _ (postcompComparison L E F β) fun K hK => ?_
  have := isIso_app_of_kFlat L hL F β K hK
  rw [postcompComparison_app]
  infer_instance

end Exact

end CochainComplex.KFlatAdjunction

end

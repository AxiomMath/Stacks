module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapCompatibility
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ProperBaseChangeAtAPoint

/-!
# Invertibility criteria for the derived base change comparison

`Stacks.Cohomology.BaseChange.derived` descends a comparison `τ : F ⋙ G ⟶ G' ⋙ F'` of underived
composites of additive functors between abelian categories to the bounded below right derived
functors, `RF ⋙ RG ⟶ RG' ⋙ RF'`. This file gives three criteria for a component of the descended
comparison to be invertible.

* At a bounded below complex `K` at which the units of `RF` and `RG'` are invertible, the
  component at `K` is invertible exactly when the degreewise comparison `τ(K)`, followed by the
  unit of `RF'` at `G'(K)`, is (`isIso_derived_app_Qh_iff`). In particular it is invertible when
  `τ` is invertible on the terms of `K` and `G'(K)` has terms right acyclic for `F'`.
* For two squares stacked along the vertical direction,
  ```
  A₀ --H--> C₀
  |P        |P'
  A  --G'-> C
  |F        |F'
  B  --G--> D
  ```
  with `P` and `P'` preserving injective objects, and a bounded below complex `K` of injective
  objects of `A₀` at which the comparison of the upper square is invertible, the comparison of
  the outer rectangle is invertible at `K` exactly when the comparison of the lower square is
  invertible at `P(K)` (`isIso_derived_comp_app_iff`).
* When the comparison is compatible with the shift, it is invertible at the first vertex of a
  distinguished triangle as soon as it is invertible at the other two
  (`isIso_app_obj₁_of_triangle`).

## Main results

* `Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_iff`
* `Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_of_acyclic`
* `Stacks.Cohomology.BaseChange.isIso_derived_comp_app_iff`
* `Stacks.Cohomology.BaseChange.isIso_app_obj₁_of_triangle`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Shapes of the chases, in an arbitrary category -/

section Shapes

variable {𝒞 : Type*} [Category* 𝒞]

/-- A morphism `φ` with `u ≫ φ = ψ` for an isomorphism `u` is an isomorphism exactly when `ψ`
is. -/
theorem isIso_iff_of_isIso_comp_eq {X Y Z : 𝒞} {u : X ⟶ Y} [IsIso u] {φ : Y ⟶ Z} {ψ : X ⟶ Z}
    (h : u ≫ φ = ψ) : IsIso φ ↔ IsIso ψ := by
  subst h
  exact (isIso_comp_left_iff _ _).symm

/-- A fourfold composite whose outer factors are isomorphisms is an isomorphism exactly when the
composite of its two inner factors is. -/
theorem isIso_comp₄_iff {X₀ X₁ X₂ X₃ X₄ : 𝒞} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) [IsIso a] [IsIso d] : IsIso (a ≫ b ≫ c ≫ d) ↔ IsIso (b ≫ c) := by
  rw [← Category.assoc b c d]
  exact (isIso_comp_left_iff _ _).trans (isIso_comp_right_iff _ _)

/-- The shape of the vertical pasting chase. -/
theorem vertical_chase {X₀ X₁ X₂ Y₁ Y₂ Y₃ Z : 𝒞} {q₁ : X₀ ⟶ X₁} {q₂ : X₁ ⟶ X₂} {m : X₀ ⟶ X₂}
    {u₁ : X₁ ⟶ Y₁} {u₂ : X₂ ⟶ Y₂} {s : Y₁ ⟶ Y₂} {r : Y₂ ⟶ Y₃} {v : X₂ ⟶ Z} {c : Z ⟶ Y₃}
    {t : Y₁ ⟶ Y₃} {w : X₂ ⟶ X₂} (hm : m = q₁ ≫ q₂) (hw : w = 𝟙 X₂) (hc : v ≫ c = w ≫ u₂ ≫ r)
    (hnat : q₂ ≫ u₂ = u₁ ≫ s) (ht : t = s ≫ r) : (m ≫ v) ≫ c = (q₁ ≫ u₁) ≫ t := by
  rw [hw, Category.id_comp] at hc
  rw [hm, ht, Category.assoc, Category.assoc, hc, ← Category.assoc q₂, hnat]
  simp only [Category.assoc]

/-- Two out of three for a commutative square whose second and fourth sides are isomorphisms. -/
theorem isIso_iff_of_comp_eq_comp {X Y Y' Z : 𝒞} {a : X ⟶ Y} {c : Y ⟶ Z} {b : X ⟶ Y'}
    {d : Y' ⟶ Z} (hc : IsIso c) (hd : IsIso d) (h : a ≫ c = b ≫ d) : IsIso a ↔ IsIso b := by
  rw [← isIso_comp_right_iff a c, h]
  exact isIso_comp_right_iff _ _

end Shapes

section Pointwise

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  (τ : F ⋙ G ⟶ G' ⋙ F')
  (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)

/-- **The component of the descended comparison at a bounded below complex.** If the units of
`RF` and of `RG'` are invertible at `K`, the comparison is invertible at `K` exactly when the
degreewise comparison `τ(K)` followed by the unit of `RF'` at `G'(K)` is. -/
theorem isIso_derived_app_Qh_iff (K : HomotopyCategory.Plus A)
    (hF : IsIso (F.rightDerivedFunctorPlusUnit.app K))
    (hG' : IsIso (G'.rightDerivedFunctorPlusUnit.app K)) :
    IsIso ((derived F F' G G' τ e).app (DerivedCategory.Plus.Qh.obj K)) ↔
      IsIso (DerivedCategory.Plus.Qh.map ((mapPlus τ).app K) ≫
        F'.rightDerivedFunctorPlusUnit.app (G'.mapHomotopyCategoryPlus.obj K)) := by
  have h₁ := isIso_iff_of_isIso_comp_eq (derived_fac_app F F' G G' τ e K)
  rw [onHomotopy_app] at h₁
  exact h₁.trans (isIso_comp₄_iff _ _ _ _)

/-- **The acyclic criterion.** The descended comparison is invertible at a bounded below complex
`K` whose image under `F` and whose image under `G'` are computed by the units, and on whose
terms `τ` is invertible. -/
theorem isIso_derived_app_Qh_of_acyclic (K : HomotopyCategory.Plus A)
    (hF : IsIso (F.rightDerivedFunctorPlusUnit.app K))
    (hG' : IsIso (G'.rightDerivedFunctorPlusUnit.app K))
    (hF' : IsIso (F'.rightDerivedFunctorPlusUnit.app (G'.mapHomotopyCategoryPlus.obj K)))
    (hτ : ∀ n : ℤ, IsIso (τ.app (K.obj.as.X n))) :
    IsIso ((derived F F' G G' τ e).app (DerivedCategory.Plus.Qh.obj K)) := by
  have : IsIso ((mapPlus τ).app K) :=
    Stacks.Cohomology.ProperBaseChange.isIso_mapPlus_app_of_components _ _ τ hτ
  exact (isIso_derived_app_Qh_iff F F' G G' τ e K hF hG').2 (IsIso.comp_isIso' inferInstance hF')

end Pointwise

/-! ### Two squares stacked along the vertical direction -/

section Vertical

variable {A₀ C₀ A B C D : Type*} [Category* A₀] [Category* C₀] [Category* A] [Category* B]
  [Category* C] [Category* D]
  [Abelian A₀] [Abelian C₀] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A₀] [EnoughInjectives C₀] [EnoughInjectives A] [EnoughInjectives B]
  [EnoughInjectives C]
  (P : A₀ ⥤ A) (P' : C₀ ⥤ C) (H : A₀ ⥤ C₀)
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [P.Additive] [P'.Additive] [H.Additive]
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  (σ : P ⋙ G' ⟶ H ⋙ P') (τ : F ⋙ G ⟶ G' ⋙ F') (ρ : (P ⋙ F) ⋙ G ⟶ H ⋙ (P' ⋙ F'))
  (hρ : ∀ M : A₀, ρ.app M = τ.app (P.obj M) ≫ F'.map (σ.app M))
  (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)
  (e' : G'.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G'.rightDerivedFunctorPlus)

include hρ in
/-- The degreewise comparison of the outer rectangle is the degreewise comparison of the lower
square at `P(K)` followed by `F'` applied to the degreewise comparison of the upper square. -/
theorem mapPlus_comp_app (K : HomotopyCategory.Plus A₀) :
    (mapPlus ρ).app K =
      (mapPlus τ).app (P.mapHomotopyCategoryPlus.obj K) ≫
        F'.mapHomotopyCategoryPlus.map ((mapPlus σ).app K) := by
  ext
  obtain ⟨⟨L⟩, hL⟩ := K
  refine Eq.trans (congrArg (fun z => (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map z)
    (?_ : (NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ)).app L =
      (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app L))) ?_
  · ext i
    simpa using hρ (L.X i)
  · rw [Functor.map_comp]
    rfl

include hρ in
/-- The key identity of the vertical pasting: the comparison of the outer rectangle at `K`,
followed by the comparison `R(P' ⋙ F') ⟶ RP' ⋙ RF'`, is the comparison of the lower square at
`P(K)` followed by `RF'` applied to the comparison of the upper square at `K`. -/
theorem comp_rightDerivedFunctorPlusComp_app (K : HomotopyCategory.Plus A₀) :
    (DerivedCategory.Plus.Qh.map ((mapPlus ρ).app K) ≫
        (P' ⋙ F').rightDerivedFunctorPlusUnit.app (H.mapHomotopyCategoryPlus.obj K)) ≫
      (Functor.rightDerivedFunctorPlusComp P' F').app
        (DerivedCategory.Plus.Qh.obj (H.mapHomotopyCategoryPlus.obj K)) =
    (DerivedCategory.Plus.Qh.map ((mapPlus τ).app (P.mapHomotopyCategoryPlus.obj K)) ≫
        F'.rightDerivedFunctorPlusUnit.app
          (G'.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K))) ≫
      F'.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((mapPlus σ).app K) ≫
          P'.rightDerivedFunctorPlusUnit.app (H.mapHomotopyCategoryPlus.obj K)) :=
  vertical_chase
    (congrArg DerivedCategory.Plus.Qh.map (mapPlus_comp_app P P' H F F' G G' σ τ ρ hρ K) |>.trans
      (DerivedCategory.Plus.Qh.map_comp _ _))
    (map_mapHomotopyCategoryPlusCompIso_inv_app P' F' DerivedCategory.Plus.Qh _)
    (Functor.rightDerivedFunctorPlusComp_fac_app P' F' (H.mapHomotopyCategoryPlus.obj K))
    (F'.rightDerivedFunctorPlusUnit.naturality ((mapPlus σ).app K))
    (F'.rightDerivedFunctorPlus.map_comp _ _)

include hρ in
/-- **Vertical pasting, pointwise.** Let `K` be a bounded below complex of injective objects of
`A₀`, with `P` and `P'` preserving injective objects and the derived-functor units of `G'` and
`H` invertible. If the comparison of the upper square is invertible at `K`, then the comparison
of the outer rectangle is invertible at `K` exactly when the comparison of the lower square is
invertible at `P(K)`. -/
theorem isIso_derived_comp_app_iff [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects]
    [IsIso G'.rightDerivedFunctorPlusUnit] [IsIso H.rightDerivedFunctorPlusUnit]
    (K : HomotopyCategory.Plus A₀) (hK : ∀ n : ℤ, Injective (K.obj.as.X n))
    (hσ : IsIso ((derived P P' G' H σ e').app (DerivedCategory.Plus.Qh.obj K))) :
    IsIso ((derived (P ⋙ F) (P' ⋙ F') G H ρ e).app (DerivedCategory.Plus.Qh.obj K)) ↔
      IsIso ((derived F F' G G' τ e).app
        (DerivedCategory.Plus.Qh.obj (P.mapHomotopyCategoryPlus.obj K))) := by
  have hPK : ∀ n : ℤ, Injective ((P.mapHomotopyCategoryPlus.obj K).obj.as.X n) := fun n =>
    Functor.PreservesInjectiveObjects.injective_obj (hK n)
  have h₁ : IsIso ((P ⋙ F).rightDerivedFunctorPlusUnit.app K) := inferInstance
  have h₂ : IsIso (P.rightDerivedFunctorPlusUnit.app K) := inferInstance
  have h₃ : IsIso (F.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj K)) :=
    inferInstance
  have h₄ : IsIso (H.rightDerivedFunctorPlusUnit.app K) := inferInstance
  have h₅ : IsIso (G'.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj K)) :=
    inferInstance
  have hσ' := (isIso_derived_app_Qh_iff P P' G' H σ e' K h₂ h₄).1 hσ
  have hR : IsIso (F'.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map ((mapPlus σ).app K) ≫
        P'.rightDerivedFunctorPlusUnit.app (H.mapHomotopyCategoryPlus.obj K))) :=
    (F'.rightDerivedFunctorPlus.mapIso (@asIso _ _ _ _ _ hσ')).isIso_hom
  have hc : IsIso ((Functor.rightDerivedFunctorPlusComp P' F').app
      (DerivedCategory.Plus.Qh.obj (H.mapHomotopyCategoryPlus.obj K))) := inferInstance
  exact (isIso_derived_app_Qh_iff (P ⋙ F) (P' ⋙ F') G H ρ e K h₁ h₄).trans
    ((isIso_iff_of_comp_eq_comp hc hR
      (comp_rightDerivedFunctorPlusComp_app P P' H F F' G G' σ τ ρ hρ K)).trans
      (isIso_derived_app_Qh_iff F F' G G' τ e (P.mapHomotopyCategoryPlus.obj K) h₃ h₅).symm)

omit hρ in
/-- **Vertical pasting, pointwise, for an arbitrary spelling of the composite functors.** The
same statement as `isIso_derived_comp_app_iff`, for functors `PF` and `P'F'` equal to `P ⋙ F` and
`P' ⋙ F'`, with the comparison `ρ'` of the outer rectangle expressed through `ρ`. -/
theorem isIso_derived_comp_app_iff' [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects]
    [IsIso G'.rightDerivedFunctorPlusUnit] [IsIso H.rightDerivedFunctorPlusUnit]
    (PF : A₀ ⥤ B) [PF.Additive] (hPF : PF = P ⋙ F) (P'F' : C₀ ⥤ D) [P'F'.Additive]
    (hP'F' : P'F' = P' ⋙ F') (ρ' : PF ⋙ G ⟶ H ⋙ P'F')
    (hρ' : ∀ M : A₀, HEq (ρ'.app M) (τ.app (P.obj M) ≫ F'.map (σ.app M)))
    (K : HomotopyCategory.Plus A₀) (hK : ∀ n : ℤ, Injective (K.obj.as.X n))
    (hσ : IsIso ((derived P P' G' H σ e').app (DerivedCategory.Plus.Qh.obj K))) :
    IsIso ((derived PF P'F' G H ρ' e).app (DerivedCategory.Plus.Qh.obj K)) ↔
      IsIso ((derived F F' G G' τ e).app
        (DerivedCategory.Plus.Qh.obj (P.mapHomotopyCategoryPlus.obj K))) := by
  subst hPF hP'F'
  exact isIso_derived_comp_app_iff P P' H F F' G G' σ τ ρ' (fun M => eq_of_heq (hρ' M)) e e'
    K hK hσ

end Vertical

/-! ### Two squares stacked along the base -/

section Horizontal

variable {A B C D C₂ D₂ : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* C₂] [Category* D₂]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian C₂] [Abelian D₂]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [EnoughInjectives D]
  [EnoughInjectives C₂]
  (F : A ⥤ B) (F' : C ⥤ D) (F'' : C₂ ⥤ D₂)
  (G : B ⥤ D) (G' : A ⥤ C) (H : D ⥤ D₂) (H' : C ⥤ C₂)
  [F.Additive] [F'.Additive] [F''.Additive]
  [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (τ₁ : F ⋙ G ⟶ G' ⋙ F') (τ₂ : F' ⋙ H ⟶ H' ⋙ F'')
  {K : B ⥤ D₂} {K' : A ⥤ C₂} [K.Additive] [K'.Additive]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

/-- **Horizontal pasting, pointwise.** Let `ρ : F ⋙ K ⟶ K' ⋙ F''` be the comparison of a
rectangle whose horizontal functors `K`, `K'` are identified with the composites `G ⋙ H`,
`G' ⋙ H'`, and which is, through these identifications, the paste of the comparisons `τ₁` and
`τ₂` of two squares. Then the descended comparison of the rectangle is invertible at `X` exactly
when the descended comparison of the paste is. -/
theorem isIso_derived_app_iff_paste (α : G ⋙ H ≅ K) (β : G' ⋙ H' ≅ K')
    (ρ : F ⋙ K ⟶ K' ⋙ F'')
    (hρ : Functor.whiskerLeft F α.hom ≫ ρ ≫ Functor.whiskerRight β.inv F'' =
      pasteTrans F F' F'' G G' H H' τ₁ τ₂)
    (X : DerivedCategory.Plus A) :
    IsIso ((derived F F'' K K' ρ (exactUnitIso K)).app X) ↔
      IsIso ((derived F F'' (G ⋙ H) (G' ⋙ H') (pasteTrans F F' F'' G G' H H' τ₁ τ₂)
        (exactUnitIso (G ⋙ H))).app X) := by
  rw [← hρ, NatTrans.congr_app (derived_transport F F'' α β ρ) X]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  exact ⟨fun _ => inferInstance,
    fun h => (isIso_comp_right_iff _ _).1 ((isIso_comp_left_iff _ _).1 h)⟩

/-- **Horizontal pasting, the left square.** If the descended comparison of the second square is
invertible everywhere, the descended comparison of the paste is invertible at `X` exactly when
`RH` applied to the descended comparison of the first square at `X` is. -/
theorem isIso_derived_paste_app_iff_left
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (h₂ : IsIso (derived F' F'' H H' τ₂ (exactUnitIso H))) (X : DerivedCategory.Plus A) :
    IsIso ((derived F F'' (G ⋙ H) (G' ⋙ H') (pasteTrans F F' F'' G G' H H' τ₁ τ₂)
        (exactUnitIso (G ⋙ H))).app X) ↔
      IsIso (H.rightDerivedFunctorPlus.map ((derived F F' G G' τ₁ (exactUnitIso G)).app X)) := by
  rw [NatTrans.congr_app (derived_paste F F' F'' G G' H H' τ₁ τ₂) X]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have : IsIso ((derived F' F'' H H' τ₂ (exactUnitIso H)).app
      (G'.rightDerivedFunctorPlus.obj X)) := inferInstance
  rw [isIso_comp₄_iff]
  exact isIso_comp_right_iff _ _

/-- **Horizontal pasting, the right square.** If the descended comparison of the first square is
invertible at `X`, the descended comparison of the paste is invertible at `X` exactly when the
descended comparison of the second square is invertible at `RG'(X)`. -/
theorem isIso_derived_paste_app_iff_right
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H'] (X : DerivedCategory.Plus A)
    (h₁ : IsIso ((derived F F' G G' τ₁ (exactUnitIso G)).app X)) :
    IsIso ((derived F F'' (G ⋙ H) (G' ⋙ H') (pasteTrans F F' F'' G G' H H' τ₁ τ₂)
        (exactUnitIso (G ⋙ H))).app X) ↔
      IsIso ((derived F' F'' H H' τ₂ (exactUnitIso H)).app (G'.rightDerivedFunctorPlus.obj X)) := by
  rw [NatTrans.congr_app (derived_paste F F' F'' G G' H H' τ₁ τ₂) X]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [isIso_comp₄_iff]
  exact isIso_comp_left_iff _ _

end Horizontal

/-! ### Triangles -/

section Triangle

variable {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
  [HasShift 𝒞 ℤ] [HasShift 𝒟 ℤ] [HasZeroObject 𝒞] [HasZeroObject 𝒟]
  [Preadditive 𝒞] [Preadditive 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒞] [Pretriangulated 𝒟]
  {Φ Ψ : 𝒞 ⥤ 𝒟} [Φ.CommShift ℤ] [Ψ.CommShift ℤ] [Φ.IsTriangulated] [Ψ.IsTriangulated]
  (τ : Φ ⟶ Ψ) [NatTrans.CommShift τ ℤ]

/-- The morphism of triangles induced by a natural transformation compatible with the shift. -/
def triangleHom (T : Triangle 𝒞) : Φ.mapTriangle.obj T ⟶ Ψ.mapTriangle.obj T where
  hom₁ := τ.app T.obj₁
  hom₂ := τ.app T.obj₂
  hom₃ := τ.app T.obj₃
  comm₁ := τ.naturality T.mor₁
  comm₂ := τ.naturality T.mor₂
  comm₃ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ Φ.map T.mor₃ ≫ z)
          (NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z ↦ z ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app T.obj₁)
              (τ.naturality T.mor₃)).trans (Category.assoc _ _ _))))

/-- **Two out of three along a distinguished triangle.** A natural transformation of triangulated
functors compatible with the shift is invertible at the first vertex of a distinguished triangle
as soon as it is invertible at the other two. -/
theorem isIso_app_obj₁_of_triangle (T : Triangle 𝒞) (hT : T ∈ distTriang 𝒞)
    (h₂ : IsIso (τ.app T.obj₂)) (h₃ : IsIso (τ.app T.obj₃)) : IsIso (τ.app T.obj₁) :=
  isIso₁_of_isIso₂₃ (triangleHom τ T) (Φ.map_distinguished T hT) (Ψ.map_distinguished T hT)
    h₂ h₃

/-- A natural transformation of additive functors is invertible at a binary biproduct as soon
as it is invertible at the two summands. -/
theorem isIso_app_biprod [HasBinaryBiproducts 𝒞] [HasBinaryBiproducts 𝒟]
    [Φ.Additive] [Ψ.Additive] (X Y : 𝒞)
    (hX : IsIso (τ.app X)) (hY : IsIso (τ.app Y)) : IsIso (τ.app (X ⊞ Y)) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts Φ
  have := preservesBinaryBiproducts_of_preservesBiproducts Ψ
  have h : τ.app (X ⊞ Y) = (Φ.mapBiprod X Y).hom ≫ biprod.map (τ.app X) (τ.app Y) ≫
      (Ψ.mapBiprod X Y).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    ext
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc]
      exact (τ.naturality biprod.fst).symm
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc]
      exact (τ.naturality biprod.snd).symm
  rw [h]
  have : IsIso (biprod.map (τ.app X) (τ.app Y)) :=
    (biprod.mapIso (asIso (τ.app X)) (asIso (τ.app Y))).isIso_hom
  infer_instance

end Triangle

end Stacks.Cohomology.BaseChange

end

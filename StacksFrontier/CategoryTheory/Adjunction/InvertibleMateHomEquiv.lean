module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Homomorphisms out of a base-changed left adjoint, through an invertible mate

Let `ℓ ⊣ r` and `ℓ' ⊣ r'` be adjunctions with `ℓ : C ⥤ D`, `ℓ' : E ⥤ F`, and let `G : C ⥤ E`,
`H : D ⥤ F` be functors with a comparison `e : r ⋙ G ⟶ H ⋙ r'`. Its mate is the base change
morphism `β : G ⋙ ℓ' ⟶ ℓ ⋙ H`. When `β` is invertible,

`Hom_F(H(ℓ A), Y) ≃ Hom_E(G A, r' Y)`

by precomposition with `β_A` and adjunction, and this bijection carries the precomposition with
`H` of the counit `ℓ(r X) ⟶ X` to the map `φ ↦ e_X ≫ r' φ`.

## Main definitions

* `CategoryTheory.Adjunction.homEquivOfIsIsoMate`.

## Main results

* `CategoryTheory.Adjunction.homEquivOfIsIsoMate_counit`: compatibility with restriction.
* `CategoryTheory.Adjunction.homEquivOfIsIsoMate_naturality`: naturality in the target.
* `CategoryTheory.Adjunction.isIso_mateEquiv_symm_iff_isIso_mateEquiv`: when `G` and `H` are
  left adjoints, `β` is invertible exactly when the mate `RH ⋙ r ⟶ r' ⋙ RG` of `e` along the
  adjunctions of `H` and `G` is (the iterated mate is a conjugate).
* `CategoryTheory.Adjunction.mateEquiv_app_eq_of_fac`: the mate of a square of derived functors
  is the mate of the underlying square, read through comparison maps that are compatible with
  the units, the counits and the squares.
* `CategoryTheory.Adjunction.isIso_mateEquiv_of_fac`: the derived mate is invertible when every
  object is the class of some `K` at which the comparisons and the underived mate are.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄} [Category.{v₁} C]
  [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {ℓ : C ⥤ D} {r : D ⥤ C} {ℓ' : E ⥤ F} {r' : F ⥤ E} (adj : ℓ ⊣ r) (adj' : ℓ' ⊣ r')
  {G : C ⥤ E} {H : D ⥤ F} (e : TwoSquare r H G r')

/-- **Homomorphisms out of a base-changed left adjoint**: when the mate
`β : G ⋙ ℓ' ⟶ ℓ ⋙ H` of `e : r ⋙ G ⟶ H ⋙ r'` is invertible at `A`, morphisms
`H(ℓ A) ⟶ Y` correspond to morphisms `G A ⟶ r' Y`, by precomposition with `β_A` followed by the
adjunction `ℓ' ⊣ r'`. -/
def homEquivOfIsIsoMate (A : C) [IsIso (((mateEquiv adj adj').symm e).app A)] (Y : F) :
    (H.obj (ℓ.obj A) ⟶ Y) ≃ (G.obj A ⟶ r'.obj Y) where
  toFun x := adj'.homEquiv _ _ (((mateEquiv adj adj').symm e).app A ≫ x)
  invFun y := inv (((mateEquiv adj adj').symm e).app A) ≫ (adj'.homEquiv _ _).symm y
  left_inv x := by simp
  right_inv y := by simp

/-- The bijection `homEquivOfIsIsoMate` sends `x : H(ℓ A) ⟶ Y` to the adjoint along `ℓ' ⊣ r'` of
`β_A ≫ x`. -/
theorem homEquivOfIsIsoMate_apply (A : C) [IsIso (((mateEquiv adj adj').symm e).app A)] (Y : F)
    (x : H.obj (ℓ.obj A) ⟶ Y) :
    homEquivOfIsIsoMate adj adj' e A Y x =
      adj'.homEquiv _ _ (((mateEquiv adj adj').symm e).app A ≫ x) := rfl

/-- **The bijection is compatible with restriction**: precomposition with `H` of the counit
`ℓ(r X) ⟶ X` corresponds to `φ ↦ e_X ≫ r' φ`. -/
theorem homEquivOfIsIsoMate_counit (X : D) [IsIso (((mateEquiv adj adj').symm e).app (r.obj X))]
    {Y : F} (φ : H.obj X ⟶ Y) :
    homEquivOfIsIsoMate adj adj' e (r.obj X) Y (H.map (adj.counit.app X) ≫ φ) =
      e.app X ≫ r'.map φ := by
  rw [homEquivOfIsIsoMate_apply, ← Category.assoc, ← mateEquiv_counit_symm, Category.assoc,
    adj'.homEquiv_naturality_left, adj'.homEquiv_unit]
  simp

/-- **The bijection is natural in the target.** -/
theorem homEquivOfIsIsoMate_naturality (A : C) [IsIso (((mateEquiv adj adj').symm e).app A)]
    {Y Y' : F} (x : H.obj (ℓ.obj A) ⟶ Y) (y : Y ⟶ Y') :
    homEquivOfIsIsoMate adj adj' e A Y' (x ≫ y) =
      homEquivOfIsIsoMate adj adj' e A Y x ≫ r'.map y := by
  rw [homEquivOfIsIsoMate_apply, homEquivOfIsIsoMate_apply, ← Category.assoc,
    adj'.homEquiv_naturality_right]

/-- **The base change morphism is invertible exactly when the other mate is.** When `G ⊣ RG` and
`H ⊣ RH`, the mate `β : G ⋙ ℓ' ⟶ ℓ ⋙ H` of `e : r ⋙ G ⟶ H ⋙ r'` along `ℓ ⊣ r`, `ℓ' ⊣ r'` is
invertible if and only if the mate `RH ⋙ r ⟶ r' ⋙ RG` of `e` along `H ⊣ RH`, `G ⊣ RG` is: the
latter is the iterated mate of `β`, which is its conjugate along the composite adjunctions
`ℓ ⋙ H ⊣ RH ⋙ r` and `G ⋙ ℓ' ⊣ r' ⋙ RG` (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). -/
theorem isIso_mateEquiv_symm_iff_isIso_mateEquiv {RG : E ⥤ C} {RH : F ⥤ D} (adjG : G ⊣ RG)
    (adjH : H ⊣ RH) :
    IsIso ((mateEquiv adj adj').symm e) ↔ IsIso (mateEquiv adjH adjG e) := by
  have h : (mateEquiv adjH adjG e) =
      conjugateEquiv (adj.comp adjH) (adjG.comp adj') ((mateEquiv adj adj').symm e) := by
    rw [← iterated_mateEquiv_conjugateEquiv, Equiv.apply_symm_apply]
  rw [h]
  exact ⟨fun _ => inferInstance, fun _ => conjugateEquiv_of_iso (adj.comp adjH) (adjG.comp adj') _⟩

section Comparison

variable {KW : Type*} {KW' : Type*} {KY : Type*} {KY' : Type*} {DW : Type*} {DW' : Type*}
  {DY : Type*} {DY' : Type*} [Category* KW] [Category* KW'] [Category* KY] [Category* KY']
  [Category* DW] [Category* DW'] [Category* DY] [Category* DY']
  {QW : KW ⥤ DW} {QW' : KW' ⥤ DW'} {QY : KY ⥤ DY} {QY' : KY' ⥤ DY'}
  {g₀ : KW ⥤ KW'} {g₀' : KW' ⥤ KW} {h₀ : KY ⥤ KY'} {h₀' : KY' ⥤ KY}
  {j₀ : KW ⥤ KY} {j₀' : KW' ⥤ KY'}
  {Lg : DW ⥤ DW'} {Rg : DW' ⥤ DW} {Lh : DY ⥤ DY'} {Rh : DY' ⥤ DY}
  {Lj : DW ⥤ DY} {Lj' : DW' ⥤ DY'}

/-- **The mate of a square of derived functors is the mate of the underlying square.** Let
`g₀ ⊣ g₀'`, `h₀ ⊣ h₀'` be adjunctions (of homotopy categories, say) with a square
`e₀ : j₀ ⋙ h₀ ⟶ g₀ ⋙ j₀'`, and `Lg ⊣ Rg`, `Lh ⊣ Rh` adjunctions (of derived categories) with a
square `e : Lj ⋙ Lh ⟶ Lg ⋙ Lj'`. Suppose given comparisons `cg`, `ch`, `cj`, `cj'` from the
derived left adjoints and `ug`, `uh` into the derived right adjoints, compatible with the units,
the counits and the two squares. Then the mate `Rg ⋙ Lj ⟶ Lj' ⋙ Rh` of `e` at the class of `K`
is the class of the mate of `e₀` at `K`, read through the comparisons.

When the comparisons are invertible at `K` (for instance on K-injective `K`, with `j₀'`
preserving K-injectivity), this says the derived base change morphism is invertible there as
soon as the underived one is. -/
theorem mateEquiv_app_eq_of_fac (a₀ : g₀ ⊣ g₀') (b₀ : h₀ ⊣ h₀') (e₀ : TwoSquare j₀ g₀ h₀ j₀')
    (a : Lg ⊣ Rg) (b : Lh ⊣ Rh) (e : TwoSquare Lj Lg Lh Lj')
    (cg : ∀ M : KW, Lg.obj (QW.obj M) ⟶ QW'.obj (g₀.obj M))
    (ch : ∀ M : KY, Lh.obj (QY.obj M) ⟶ QY'.obj (h₀.obj M))
    (cj : ∀ M : KW, Lj.obj (QW.obj M) ⟶ QY.obj (j₀.obj M))
    (cj' : ∀ M : KW', Lj'.obj (QW'.obj M) ⟶ QY'.obj (j₀'.obj M))
    (ug : ∀ K : KW', QW.obj (g₀'.obj K) ⟶ Rg.obj (QW'.obj K))
    (uh : ∀ K : KY', QY.obj (h₀'.obj K) ⟶ Rh.obj (QY'.obj K))
    (hcj' : ∀ {M M' : KW'} (φ : M ⟶ M'), Lj'.map (QW'.map φ) ≫ cj' M' = cj' M ≫ QY'.map (j₀'.map φ))
    (huh : ∀ {K K' : KY'} (φ : K ⟶ K'), QY.map (h₀'.map φ) ≫ uh K' = uh K ≫ Rh.map (QY'.map φ))
    (hunit : ∀ M : KY, b.unit.app (QY.obj M) ≫ Rh.map (ch M) =
      QY.map (b₀.unit.app M) ≫ uh (h₀.obj M))
    (hcounit : ∀ K : KW', Lg.map (ug K) ≫ a.counit.app (QW'.obj K) =
      cg (g₀'.obj K) ≫ QW'.map (a₀.counit.app K))
    (he : ∀ K : KW, e.app (QW.obj K) ≫ Lj'.map (cg K) ≫ cj' (g₀.obj K) =
      Lh.map (cj K) ≫ ch (j₀.obj K) ≫ QY'.map (e₀.app K))
    (K : KW') :
    Lj.map (ug K) ≫ (mateEquiv a b e).app (QW'.obj K) ≫ Rh.map (cj' K) =
      cj (g₀'.obj K) ≫ QY.map ((mateEquiv a₀ b₀ e₀).app K) ≫ uh (j₀'.obj K) := by
  have hθ : (mateEquiv a b e).app (QW'.obj K) =
      b.unit.app (Lj.obj (Rg.obj (QW'.obj K))) ≫ Rh.map (e.app (Rg.obj (QW'.obj K))) ≫
        Rh.map (Lj'.map (a.counit.app (QW'.obj K))) := by
    simp [mateEquiv_apply]
  have hθ₀ : (mateEquiv a₀ b₀ e₀).app K =
      b₀.unit.app (j₀.obj (g₀'.obj K)) ≫ h₀'.map (e₀.app (g₀'.obj K)) ≫
        h₀'.map (j₀'.map (a₀.counit.app K)) := by
    simp [mateEquiv_apply]
  rw [hθ, hθ₀]
  simp only [Category.assoc, Functor.map_comp]
  have h4 : QY.map (h₀'.map (j₀'.map (a₀.counit.app K))) ≫ uh (j₀'.obj K) =
      uh (j₀'.obj (g₀.obj (g₀'.obj K))) ≫ Rh.map (QY'.map (j₀'.map (a₀.counit.app K))) :=
    huh _
  rw [reassoc_of% (b.unit_naturality (Lj.map (ug K))).symm, h4,
    reassoc_of% (huh (e₀.app (g₀'.obj K))),
    ← reassoc_of% (hunit (j₀.obj (g₀'.obj K))), reassoc_of% (b.unit_naturality (cj _)).symm]
  congr 1
  simp only [← Rh.map_comp]
  congr 1
  have h6 : Lj'.map (QW'.map (a₀.counit.app K)) ≫ cj' K =
      cj' (g₀.obj (g₀'.obj K)) ≫ QY'.map (j₀'.map (a₀.counit.app K)) :=
    hcj' _
  rw [reassoc_of% (e.naturality (ug K)), ← Lj'.map_comp_assoc, hcounit, Lj'.map_comp,
    Category.assoc, h6, reassoc_of% (he (g₀'.obj K))]

/-- **The derived base change morphism is invertible as soon as the underived one is, on enough
objects.** In the situation of `CategoryTheory.Adjunction.mateEquiv_app_eq_of_fac`, if every
object of the derived category is isomorphic to the class of an object `K` (a K-injective
complex, say) at which the comparisons `ug`, `cj`, `uh`, `cj'` and the underived mate are
invertible, then the mate of `e` is invertible. -/
theorem isIso_mateEquiv_of_fac (a₀ : g₀ ⊣ g₀') (b₀ : h₀ ⊣ h₀') (e₀ : TwoSquare j₀ g₀ h₀ j₀')
    (a : Lg ⊣ Rg) (b : Lh ⊣ Rh) (e : TwoSquare Lj Lg Lh Lj')
    (cg : ∀ M : KW, Lg.obj (QW.obj M) ⟶ QW'.obj (g₀.obj M))
    (ch : ∀ M : KY, Lh.obj (QY.obj M) ⟶ QY'.obj (h₀.obj M))
    (cj : ∀ M : KW, Lj.obj (QW.obj M) ⟶ QY.obj (j₀.obj M))
    (cj' : ∀ M : KW', Lj'.obj (QW'.obj M) ⟶ QY'.obj (j₀'.obj M))
    (ug : ∀ K : KW', QW.obj (g₀'.obj K) ⟶ Rg.obj (QW'.obj K))
    (uh : ∀ K : KY', QY.obj (h₀'.obj K) ⟶ Rh.obj (QY'.obj K))
    (hcj' : ∀ {M M' : KW'} (φ : M ⟶ M'), Lj'.map (QW'.map φ) ≫ cj' M' = cj' M ≫ QY'.map (j₀'.map φ))
    (huh : ∀ {K K' : KY'} (φ : K ⟶ K'), QY.map (h₀'.map φ) ≫ uh K' = uh K ≫ Rh.map (QY'.map φ))
    (hunit : ∀ M : KY, b.unit.app (QY.obj M) ≫ Rh.map (ch M) =
      QY.map (b₀.unit.app M) ≫ uh (h₀.obj M))
    (hcounit : ∀ K : KW', Lg.map (ug K) ≫ a.counit.app (QW'.obj K) =
      cg (g₀'.obj K) ≫ QW'.map (a₀.counit.app K))
    (he : ∀ K : KW, e.app (QW.obj K) ≫ Lj'.map (cg K) ≫ cj' (g₀.obj K) =
      Lh.map (cj K) ≫ ch (j₀.obj K) ≫ QY'.map (e₀.app K))
    (hK : ∀ X : DW', ∃ K : KW', Nonempty (QW'.obj K ≅ X) ∧ IsIso (ug K) ∧
      IsIso (cj (g₀'.obj K)) ∧ IsIso ((mateEquiv a₀ b₀ e₀).app K) ∧
      IsIso (uh (j₀'.obj K)) ∧ IsIso (cj' K)) :
    IsIso (mateEquiv a b e) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  obtain ⟨K, ⟨φ⟩, h₁, h₂, h₃, h₄, h₅⟩ := hK X
  have hfac := mateEquiv_app_eq_of_fac a₀ b₀ e₀ a b e cg ch cj cj' ug uh hcj' huh hunit hcounit
    he K
  have : IsIso ((mateEquiv a b e).app (QW'.obj K)) := by
    have h : (mateEquiv a b e).app (QW'.obj K) =
        inv (Lj.map (ug K)) ≫ (cj (g₀'.obj K) ≫ QY.map ((mateEquiv a₀ b₀ e₀).app K) ≫
          uh (j₀'.obj K)) ≫ inv (Rh.map (cj' K)) := by
      rw [← hfac]
      simp
    rw [h]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso _ φ).1 this

end Comparison

end CategoryTheory.Adjunction

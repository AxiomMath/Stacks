module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedDerivedFunctor
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# `Ru_{X/S, *}` vanishes when it vanishes locally on `X`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], and let
`u_{X/S, *} : Ab(Cris(X/S)) ⥤ Ab(X_Zar)` be the direct image, whose sections over an open `V` of
`X` are the limit of the sheaf over the objects `(U, T, δ)` of `Cris(X/S)` with `U ⊆ V`.

This file proves a vanishing criterion: `Ru_{X/S, *}ℋ = 0` as soon as, for every open `V` of `X`,
there is a covering presieve of `V` by opens `W` on which the right derived functors of
`ℋ ↦ Γ(W, u_{X/S, *}ℋ)` all vanish at `ℋ`. It also shows that the affine opens of `X` mapping into
an affine open of `S` form a covering family of `X_Zar`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `zariskiDirectImageSections`: the functor `ℋ ↦ Γ(V, u_{X/S, *}ℋ)` for an open `V` of `X`.
* `IsAffineOverAffine`: an affine open of `X` whose image lies in an affine open of `S`.

## Main results

* `zariskiDirectImageSections_obj`: its value is the sections of `u_{X/S, *}ℋ` over `V`.
* `isZero_rightDerived_zariskiDirectImage_of_locallyIsZero`: the criterion for `R^p u_{X/S, *}`
  at a natural number `p`.
* `isZero_higherZariskiDirectImage_of_locallyIsZero`: the same for the `ℤ`-indexed
  `higherZariskiDirectImage`, in every degree.
* `isZero_derivedZariskiDirectImage_of_forall_isZero_higher`: `Ru_{X/S, *}ℋ = 0` as soon as
  every `R^j u_{X/S, *}ℋ = 0`.
* `isZero_derivedZariskiDirectImage_of_locallyIsZero`: `Ru_{X/S, *}ℋ = 0` from the local
  vanishing.
* `isCoveringFamily_isAffineOverAffine`: the affine opens of `X` mapping into an affine open of
  `S` are a covering family of `X_Zar`.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- The sections `ℋ ↦ Γ(V, u_{X/S, *}ℋ)` over an open `V` of `X`, as a functor of `ℋ`: the
presheaf-valued form of `u_{X/S, *}` followed by evaluation at `V`. -/
abbrev zariskiDirectImageSections (V : S.X.Opens) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SheafifiedDerivedFunctor.presheafPart (J := opensTopology S)
      AddCommGrpCat.{u + 1} (zariskiDirectImage S) ⋙
    (evaluation (S.X.Opens)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)

/-- The value of `zariskiDirectImageSections` at `ℋ` is the sections of `u_{X/S, *}ℋ` over
`V`. -/
theorem zariskiDirectImageSections_obj (V : S.X.Opens)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (zariskiDirectImageSections S V).obj F = ((zariskiDirectImage S).obj F).obj.obj (op V) :=
  rfl

/-- The higher direct image `R^p u_{X/S, *}ℋ` is zero as soon as every open `V` of `X` admits a
covering presieve along whose members `W` the `p`-th right derived functor of
`ℋ ↦ Γ(W, u_{X/S, *}ℋ)` vanishes at `ℋ`. -/
theorem isZero_rightDerived_zariskiDirectImage_of_locallyIsZero (p : ℕ)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : ∀ V : S.X.Opens, ∃ R : Presieve V, Sieve.generate R ∈ opensTopology S V ∧
      ∀ ⦃W : S.X.Opens⦄ (f : W ⟶ V), R f →
        IsZero (((zariskiDirectImageSections S W).rightDerived p).obj F)) :
    IsZero (((zariskiDirectImage S).rightDerived p).obj F) :=
  Stacks.Cohomology.SheafifiedDerivedFunctor.isZero_rightDerived_of_locallyIsZero
    (zariskiDirectImage S) p F h

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- The `ℤ`-indexed higher direct image `R^j u_{X/S, *}ℋ` is zero in every degree `j` as soon as
every open `V` of `X` admits, for each `p : ℕ`, a covering presieve along whose members `W` the
`p`-th right derived functor of `ℋ ↦ Γ(W, u_{X/S, *}ℋ)` vanishes at `ℋ`. -/
theorem isZero_higherZariskiDirectImage_of_locallyIsZero (j : ℤ)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : ∀ (p : ℕ) (V : S.X.Opens), ∃ R : Presieve V, Sieve.generate R ∈ opensTopology S V ∧
      ∀ ⦃W : S.X.Opens⦄ (f : W ⟶ V), R f →
        IsZero (((zariskiDirectImageSections S W).rightDerived p).obj F)) :
    IsZero ((higherZariskiDirectImage S j).obj F) := by
  rcases lt_or_ge j 0 with hj | hj
  · exact Functor.isZero_rightDerivedPlus_of_neg (zariskiDirectImage S) F j hj
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, j = (p : ℤ) := ⟨j.toNat, by omega⟩
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (zariskiDirectImage S) rfl F).2
      (isZero_rightDerived_zariskiDirectImage_of_locallyIsZero S p F (h p))

/-- `Ru_{X/S, *}ℋ = 0` as soon as every `R^j u_{X/S, *}ℋ = 0`. -/
theorem isZero_derivedZariskiDirectImage_of_forall_isZero_higher
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : ∀ j : ℤ, IsZero ((higherZariskiDirectImage S j).obj F)) :
    IsZero ((derivedZariskiDirectImage S).obj F) := by
  have hiso : IsIso (0 : (derivedZariskiDirectImage S).obj F ⟶
      (derivedZariskiDirectImage S).obj F) := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro n
    rw [(DerivedCategory.Plus.homologyFunctor
      (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) n).map_zero]
    exact (h n).isIso (h n) 0
  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 ((derivedZariskiDirectImage S).obj F)
      = inv (0 : (derivedZariskiDirectImage S).obj F ⟶
          (derivedZariskiDirectImage S).obj F) ≫ (0 : _ ⟶ _) := (IsIso.inv_hom_id _).symm
    _ = 0 := comp_zero

/-- If every open `V` of `X` admits a covering presieve along whose members `W` all the right
derived functors of `ℋ ↦ Γ(W, u_{X/S, *}ℋ)` vanish at `ℋ`, then `Ru_{X/S, *}ℋ` is zero in
`D⁺(Ab(X_Zar))`. -/
theorem isZero_derivedZariskiDirectImage_of_locallyIsZero
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : ∀ (p : ℕ) (V : S.X.Opens), ∃ R : Presieve V, Sieve.generate R ∈ opensTopology S V ∧
      ∀ ⦃W : S.X.Opens⦄ (f : W ⟶ V), R f →
        IsZero (((zariskiDirectImageSections S W).rightDerived p).obj F)) :
    IsZero ((derivedZariskiDirectImage S).obj F) :=
  isZero_derivedZariskiDirectImage_of_forall_isZero_higher S F fun j ↦
    isZero_higherZariskiDirectImage_of_locallyIsZero S j F h

/-! ### The affine opens over an affine open of `S` are a covering family -/

/-- An open `V` of `X` is affine over an affine if it is affine and its image lies in an affine
open of `S`. -/
def IsAffineOverAffine (V : S.X.Opens) : Prop :=
  IsAffineOpen V ∧ ∃ W : S.S.scheme.Opens, IsAffineOpen W ∧
    V ≤ (Opens.map (sourceToBase S).base).obj W

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] in
/-- The affine opens of `X` mapping into an affine open of `S` are a covering family of
`X_Zar`. -/
theorem isCoveringFamily_isAffineOverAffine :
    (opensTopology S).IsCoveringFamily (IsAffineOverAffine S) := by
  refine fun V ↦ ⟨fun {W} _ ↦ IsAffineOverAffine S W, ?_, fun {W} _ hW ↦ hW⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨W, hWaff, hyW, -⟩ := Opens.isBasis_iff_nbhd.1 S.S.scheme.isBasis_affineOpens
    (U := ⊤) (x := (sourceToBase S).base x) trivial
  obtain ⟨V', hV'aff, hxV', hV'le⟩ := Opens.isBasis_iff_nbhd.1 S.X.isBasis_affineOpens
    (U := V ⊓ (Opens.map (sourceToBase S).base).obj W) (x := x) ⟨hx, hyW⟩
  exact ⟨V', homOfLE (hV'le.trans inf_le_left), ⟨V', 𝟙 V',
    homOfLE (hV'le.trans inf_le_left), ⟨hV'aff, W, hWaff, hV'le.trans inf_le_right⟩,
    Category.id_comp _⟩, hxV'⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

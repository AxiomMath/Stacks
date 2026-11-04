module

public import Mathlib.CategoryTheory.CofilteredSystem
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineCrystallineSite.CompletedToposMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim

/-!
# The derived limits of the crystalline level sections

[Stacks, Tag 07JL] exhibits a morphism of topoi `g : Sh(𝒞) ⟶ Sh(𝒞^∧)` from the little affine
crystalline category to its completion, and computes its higher direct images: for an abelian
sheaf `F` on `𝒞` and an object `B` of `𝒞^∧` with finite-level approximation `B_e`,

`R^p g_* F(B) = lim_e F(B_e)` for `p = 0`, `R^1 lim_e F(B_e)` for `p = 1`, and `0` for `p ≥ 2`.

This file shows that an inverse system of abelian groups with surjective successor transition
maps has vanishing derived limits in every degree `p ≥ 1`, and applies this to the inverse system
`Crystalline.finiteLevelSections` of [Stacks, Tag 07JL] on the affine side and to the systems
`e ↦ Γ((X, T(n)_e, δ(n)), F)` of level sections on the global small crystalline site, whose limits
are the terms `M(n)` of the complex of [Stacks, Tag 07JN]. The vanishing is stated in two forms:
for the two-term product model `Rlim.firstDerivedLimit` of the first derived limit, and for the
cohomology in every degree `p ≥ 1` of an arbitrary right derived functor of `lim`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.HasSurjectiveLevelRestrictions`: the
  condition on a cosimplicial system of thickenings and an abelian presheaf that every restriction
  map `Γ((X, T(n)_{e + 1}, δ(n)), F) ⟶ Γ((X, T(n)_e, δ(n)), F)` along a level transition is
  surjective.

## Main results

* `Rlim.isZero_firstDerivedLimit_of_surjective_succ` and
  `Rlim.isZero_homology_rightDerivedLimit_of_surjective_succ`: an inverse system of abelian
  groups whose successor transition maps are surjective has vanishing derived limits in every
  degree `p ≥ 1`, for an arbitrary right derived functor of `lim` in the second statement.
* `Crystalline.isZero_firstDerivedLimit_finiteLevelSections` and
  `Crystalline.isZero_homology_rightDerivedLimit_finiteLevelSections`: the same for the inverse
  system `e ↦ Γ(T_e, F)` of [Stacks, Tag 07JL].
* `isZero_firstDerivedLimit_sectionSystem` and `isZero_homology_rightDerivedLimit_sectionSystem`,
  in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`: the same for the level
  sections of a cosimplicial system of thickenings of the whole space on the global small
  crystalline site.
* `Rlim.isMittagLeffler_of_surjective_succ`: an inverse system of abelian groups with surjective
  successor transition maps is Mittag-Leffler.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks Project, Tag 0CQA](https://stacks.math.columbia.edu/tag/0CQA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

attribute [local instance] HasDerivedCategory.standard

universe uAb

/-- The inverse limit functor on inverse systems of abelian groups is additive. -/
noncomputable local instance : (lim : Rlim.InvSystemAb.{uAb} ⥤ Ab.{uAb}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### Derived limits of a surjective tower of abelian groups -/

namespace Rlim

universe w

/-- Every transition map of an inverse system of abelian groups whose successor transition maps
are surjective is an epimorphism. -/
private theorem epi_map_of_surjective_succ (A : Rlim.InvSystemAb.{w})
    (hA : ∀ n : ℕ, Function.Surjective
      (ConcreteCategory.hom (A.map (homOfLE (Nat.le_succ n)).op)))
    {i j : ℕᵒᵖ} (f : i ⟶ j) : Epi (A.map f) := by
  have hstep (n : ℕ) : Epi (A.map (homOfLE (Nat.le_succ n)).op) :=
    (AddCommGrpCat.epi_iff_surjective _).2 (hA n)
  have htrans (a b : ℕ) (hab : b ≤ a) : Epi (A.map (homOfLE hab).op) := by
    induction a, hab using Nat.le_induction with
    | base => simpa using (show Epi (𝟙 (A.obj (op b))) from inferInstance)
    | @succ a hab ih =>
      have hcomp : (homOfLE (hab.trans (Nat.le_succ a))).op =
          (homOfLE (Nat.le_succ a)).op ≫ (homOfLE hab).op := Subsingleton.elim _ _
      rw [hcomp, Functor.map_comp]
      exact epi_comp' (hstep a) ih
  rw [show f = (homOfLE f.unop.le).op from Subsingleton.elim _ _]
  exact htrans _ _ f.unop.le

/-- **An inverse system of abelian groups whose successor transition maps are surjective has
surjective transition maps.** -/
theorem surjective_map_of_surjective_succ (A : Rlim.InvSystemAb.{w})
    (hA : ∀ n : ℕ, Function.Surjective
      (ConcreteCategory.hom (A.map (homOfLE (Nat.le_succ n)).op)))
    {i j : ℕᵒᵖ} (f : i ⟶ j) : Function.Surjective (ConcreteCategory.hom (A.map f)) :=
  (AddCommGrpCat.epi_iff_surjective _).1 (epi_map_of_surjective_succ A hA f)

/-- **An inverse system of abelian groups whose successor transition maps are surjective is
Mittag-Leffler.** -/
theorem isMittagLeffler_of_surjective_succ (A : Rlim.InvSystemAb.{w})
    (hA : ∀ n : ℕ, Function.Surjective
      (ConcreteCategory.hom (A.map (homOfLE (Nat.le_succ n)).op))) :
    (A ⋙ forget Ab.{w}).IsMittagLeffler :=
  Functor.isMittagLeffler_of_surjective _ fun _ _ f ↦ surjective_map_of_surjective_succ A hA f

/-- **The first derived limit of an inverse system of abelian groups with surjective successor
transition maps vanishes**, in the two-term product model `Rlim.firstDerivedLimit`. -/
theorem isZero_firstDerivedLimit_of_surjective_succ (A : Rlim.InvSystemAb.{w})
    (hA : ∀ n : ℕ, Function.Surjective
      (ConcreteCategory.hom (A.map (homOfLE (Nat.le_succ n)).op))) :
    IsZero (Rlim.firstDerivedLimit A) := by
  obtain ⟨RF, α, hRF, -, -, hMLzero, -, -, -, -, -, hAny, -⟩ :=
    Rlim.lim_hasRightDerivedFunctor_and_computations.{w}
  obtain ⟨e⟩ := hAny RF α hRF A
  exact (hMLzero A (isMittagLeffler_of_surjective_succ A hA)).of_iso e.symm

/-- **The derived limits of an inverse system of abelian groups with surjective successor
transition maps vanish in every positive degree**, for an arbitrary right derived functor `RF` of
the inverse limit functor. -/
theorem isZero_homology_rightDerivedLimit_of_surjective_succ (A : Rlim.InvSystemAb.{w})
    (hA : ∀ n : ℕ, Function.Surjective
      (ConcreteCategory.hom (A.map (homOfLE (Nat.le_succ n)).op)))
    (RF : DerivedCategory Rlim.InvSystemAb.{w} ⥤ DerivedCategory Ab.{w})
    (α : (lim : Rlim.InvSystemAb.{w} ⥤ Ab.{w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{w} (ComplexShape.up ℤ)))
    (p : ℤ) (hp : 1 ≤ p) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{w} p).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{w} 0).obj A))) := by
  obtain ⟨RF₀, α₀, hRF₀, hhigh, -, -, -, -, -, -, -, hAny, -⟩ :=
    Rlim.lim_hasRightDerivedFunctor_and_computations.{w}
  rcases hp.lt_or_eq with hlt | heq
  · have h₁ : RF.IsLeftKanExtension α :=
      (Functor.isRightDerivedFunctor_iff_isLeftKanExtension RF α _).mp hRF
    have h₂ : RF₀.IsLeftKanExtension α₀ :=
      (Functor.isRightDerivedFunctor_iff_isLeftKanExtension RF₀ α₀ _).mp hRF₀
    exact (hhigh A p hlt).of_iso ((DerivedCategory.homologyFunctor Ab.{w} p).mapIso
      ((Functor.leftKanExtensionUnique RF α RF₀ α₀).app _))
  · obtain ⟨e⟩ := hAny RF α hRF A
    subst heq
    exact (isZero_firstDerivedLimit_of_surjective_succ A hA).of_iso e

end Rlim

/-! ### The inverse systems of [Stacks, Tag 07JL] -/

namespace Crystalline

universe u v w

/-- **The first derived limit of the inverse system `e ↦ Γ(T_e, F)` of [Stacks, Tag 07JL]
vanishes**, for an abelian presheaf on the little affine crystalline category whose restriction
maps along the transitions of a finite-level system are surjective. -/
theorem isZero_firstDerivedLimit_finiteLevelSections
    {S : AffineCrystallineSituation.{u, v}} {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) (F : CrystallineThickening.{u, v, w} S ⥤ Ab.{max u v (w + 1)})
    (hF : ∀ e : ℕ, Function.Surjective
      (ConcreteCategory.hom (F.map (T.transition (Nat.le_succ e))))) :
    IsZero (Rlim.firstDerivedLimit (finiteLevelSections T F)) :=
  Rlim.isZero_firstDerivedLimit_of_surjective_succ _ hF

/-- **Every derived limit of the inverse system `e ↦ Γ(T_e, F)` of [Stacks, Tag 07JL] vanishes in
positive degrees**, for an abelian presheaf whose restriction maps along the transitions of a
finite-level system are surjective, and for an arbitrary right derived functor of the inverse
limit functor. -/
theorem isZero_homology_rightDerivedLimit_finiteLevelSections
    {S : AffineCrystallineSituation.{u, v}} {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) (F : CrystallineThickening.{u, v, w} S ⥤ Ab.{max u v (w + 1)})
    (hF : ∀ e : ℕ, Function.Surjective
      (ConcreteCategory.hom (F.map (T.transition (Nat.le_succ e)))))
    (RF : DerivedCategory Rlim.InvSystemAb.{max u v (w + 1)} ⥤
      DerivedCategory Ab.{max u v (w + 1)})
    (α : (lim : Rlim.InvSystemAb.{max u v (w + 1)} ⥤ Ab.{max u v (w + 1)}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{max u v (w + 1)} (ComplexShape.up ℤ)))
    (p : ℤ) (hp : 1 ≤ p) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{max u v (w + 1)} p).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{max u v (w + 1)} 0).obj
        (finiteLevelSections T F)))) :=
  Rlim.isZero_homology_rightDerivedLimit_of_surjective_succ _ hF RF α hRF p hp

end Crystalline

/-! ### The level sections on the global small crystalline site -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

universe u

variable {S : GlobalCrystallineSituation.{u}}

/-- **The surjectivity of the restriction maps along the level transitions of a cosimplicial
system of thickenings**: for every degree `n` and every level `e` the restriction map

`Γ((X, T(n)_{e + 1}, δ(n)), F) ⟶ Γ((X, T(n)_e, δ(n)), F)`

is surjective. -/
def HasSurjectiveLevelRestrictions (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : Prop :=
  ∀ n e : ℕ, Function.Surjective (ConcreteCategory.hom
    (F.map ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op))

/-- **The first derived limit of the inverse system of level sections vanishes** when the
restriction maps along the level transitions are surjective. -/
theorem isZero_firstDerivedLimit_sectionSystem
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hF : HasSurjectiveLevelRestrictions T F) (n : ℕ) :
    IsZero (Rlim.firstDerivedLimit ((sectionSystem T F).obj ⦋n⦌)) :=
  Rlim.isZero_firstDerivedLimit_of_surjective_succ _ (hF n)

/-- **Every derived limit of the inverse system of level sections vanishes in positive degrees**
when the restriction maps along the level transitions are surjective, for an arbitrary right
derived functor of the inverse limit functor. -/
theorem isZero_homology_rightDerivedLimit_sectionSystem
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hF : HasSurjectiveLevelRestrictions T F) (n : ℕ)
    (RF : DerivedCategory Rlim.InvSystemAb.{u + 1} ⥤ DerivedCategory Ab.{u + 1})
    (α : (lim : Rlim.InvSystemAb.{u + 1} ⥤ Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u + 1} (ComplexShape.up ℤ)))
    (p : ℤ) (hp : 1 ≤ p) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} p).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u + 1} 0).obj
        ((sectionSystem T F).obj ⦋n⦌)))) :=
  Rlim.isZero_homology_rightDerivedLimit_of_surjective_succ _ (hF n) RF α hRF p hp

end Crystalline.GlobalCrystallineSituation.SmallSite

end

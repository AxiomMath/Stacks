module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.Basic

/-!
# Right exactness of the top higher direct image

For an additive functor `F` between abelian categories, with enough injectives in the source, and
a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the sequence
`R^n F(X₁) ⟶ R^n F(X₂) ⟶ R^n F(X₃)` is exact, and `R^{n₀} F(X₂) ⟶ R^{n₀} F(X₃)` is an
epimorphism as soon as `R^{n₀+1} F(X₁)` vanishes: the connecting morphism out of `R^{n₀} F(X₃)`
lands in `R^{n₀+1} F(X₁)`. Applied to the pushforward of sheaves of modules along a morphism of
schemes `f`, this gives the right exact sequence

> `R^d f_*(M₁) ⟶ R^d f_*(M₂) ⟶ R^d f_*(M₃) ⟶ 0`

of [Stacks, Tag 0EX3] (b) when the higher direct images of quasi-coherent modules vanish above
the degree `d`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.epi_rightDerivedPlus_map_g_of_isZero`: for an
  additive functor between abelian categories, `R^{n₀} F(X₂) ⟶ R^{n₀} F(X₃)` is epi as soon as
  `R^{n₀+1} F(X₁)` vanishes.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.epi_rightDerivedPlus_pushforward_map_of_isZero`:
  the same for the pushforward of sheaves of modules along a morphism of schemes.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.epi_rightDerivedPlus_pushforward_map_of_vanishes`:
  the same, with the vanishing hypothesis given for all degrees above `d` and all quasi-coherent
  modules.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Pretriangulated

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

section General

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- **One degree of right exactness from one degree of vanishing.** For an additive functor `F`
between abelian categories, with enough injectives in the source, and a short exact sequence
`S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the map `R^{n₀} F(X₂) ⟶ R^{n₀} F(X₃)` is an epimorphism as soon as
`R^{n₁} F(X₁)` vanishes, where `n₁ = n₀ + 1`. -/
theorem epi_rightDerivedPlus_map_g_of_isZero (F : C ⥤ D) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (h₁ : IsZero ((F.rightDerivedPlus n₁).obj S.X₁)) :
    Epi ((F.rightDerivedPlus n₀).map S.g) :=
  ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_epi_shift_map_mor₂_iff _
      (F.rightDerivedFunctorPlus.map_distinguished _
        (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)) n₀ n₁ h).2
    (h₁.eq_of_tgt _ _)

/-- For a short exact sequence `S`, the maps `R^n F(X₁) ⟶ R^n F(X₂) ⟶ R^n F(X₃)` compose to
zero. -/
theorem rightDerivedPlus_map_f_comp_map_g (F : C ⥤ D) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℤ) :
    (F.rightDerivedPlus n).map S.f ≫ (F.rightDerivedPlus n).map S.g = 0 :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequence_comp _
    (F.rightDerivedFunctorPlus.map_distinguished _
      (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)) n

/-- **Exactness of the derived sequence in the middle.** For an additive functor `F` between
abelian categories and a short exact sequence `S`, the sequence
`R^{n} F(X₁) ⟶ R^{n} F(X₂) ⟶ R^{n} F(X₃)` is exact in every degree. -/
theorem exact_map_rightDerivedPlus (F : C ⥤ D) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk ((F.rightDerivedPlus n).map S.f) ((F.rightDerivedPlus n).map S.g)
      (rightDerivedPlus_map_f_comp_map_g F hS n)).Exact :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequence_exact₂ _
    (F.rightDerivedFunctorPlus.map_distinguished _
      (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)) n

/-- **Right exactness of `R^{n₀} F` on one short exact sequence.** When `R^{n₁} F(X₁)` vanishes,
for `n₁ = n₀ + 1`, the sequence

> `R^{n₀} F(X₁) ⟶ R^{n₀} F(X₂) ⟶ R^{n₀} F(X₃) ⟶ 0`

is exact. -/
theorem exact_and_epi_map_rightDerivedPlus_of_isZero (F : C ⥤ D) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (h₁ : IsZero ((F.rightDerivedPlus n₁).obj S.X₁)) :
    (ShortComplex.mk ((F.rightDerivedPlus n₀).map S.f) ((F.rightDerivedPlus n₀).map S.g)
        (rightDerivedPlus_map_f_comp_map_g F hS n₀)).Exact ∧
      Epi ((F.rightDerivedPlus n₀).map S.g) :=
  ⟨exact_map_rightDerivedPlus F hS n₀,
    epi_rightDerivedPlus_map_g_of_isZero F hS n₀ n₁ h h₁⟩

end General

section Pushforward

variable {X Y : Scheme.{u}}

/-- **The exactness step of [Stacks, Tag 0EX3] (b).** For a morphism of schemes `f` and a short
exact sequence of sheaves of modules on `X`, the sequence of `d`-th higher direct images is
right exact as soon as the `(d+1)`-st higher direct image of the leftmost term vanishes. -/
theorem epi_rightDerivedPlus_pushforward_map_of_isZero (f : X ⟶ Y) (d : ℕ)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hvan : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus ((d : ℤ) + 1)).obj S.X₁)) :
    Epi (((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).map S.g) :=
  epi_rightDerivedPlus_map_g_of_isZero (Scheme.Modules.pushforward f) hS (d : ℤ) ((d : ℤ) + 1)
    rfl hvan

/-- **The exactness step of [Stacks, Tag 0EX3] (b), from the tag's own hypothesis.** If every
higher direct image of a quasi-coherent module vanishes in every degree above `d`, then the `d`-th
higher direct images of a short exact sequence whose leftmost term is quasi-coherent form a right
exact sequence. -/
theorem epi_rightDerivedPlus_pushforward_map_of_vanishes (f : X ⟶ Y) (d : ℕ)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (hqc : S.X₁.IsQuasicoherent)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ G : X.Modules, G.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj G)) :
    Epi (((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).map S.g) :=
  epi_rightDerivedPlus_pushforward_map_of_isZero f d hS
    (hvan ((d : ℤ) + 1) (lt_add_one _) S.X₁ hqc)

/-- **The right exact sequence of [Stacks, Tag 0EX3] (b).** With the tag's vanishing hypothesis
in force, the `d`-th higher direct images of a short exact sequence of sheaves of modules whose
leftmost term is quasi-coherent form the right exact sequence

> `R^d f_*(X₁) ⟶ R^d f_*(X₂) ⟶ R^d f_*(X₃) ⟶ 0`. -/
theorem exact_and_epi_rightDerivedPlus_pushforward_of_vanishes (f : X ⟶ Y) (d : ℕ)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (hqc : S.X₁.IsQuasicoherent)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ G : X.Modules, G.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj G)) :
    (ShortComplex.mk
        (((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).map S.f)
        (((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).map S.g)
        (rightDerivedPlus_map_f_comp_map_g (Scheme.Modules.pushforward f) hS
          (d : ℤ))).Exact ∧
      Epi (((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).map S.g) :=
  ⟨exact_map_rightDerivedPlus (Scheme.Modules.pushforward f) hS (d : ℤ),
    epi_rightDerivedPlus_pushforward_map_of_vanishes f d hS hqc hvan⟩

end Pushforward

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end

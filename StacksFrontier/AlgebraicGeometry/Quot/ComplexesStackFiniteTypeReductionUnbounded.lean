module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFiniteTypeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeSubalgebraModelUnbounded

/-!
# Stacks 0DLN, the reduction to a base of finite type over `ℤ`, for every ring

This is `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case`
without its hypothesis `#A < cf(cutoff)`, which is not in the source. That bound came from the
index bounds of the forms of Stacks 07SK and Stacks 084W used there. Here the descent step is
`AlgebraicGeometry.Space.exists_adjoinRing_model_unbounded`. It uses Stacks 07SK in its form
under the chapter's convention 07SD, and that convention holds for the system of the finitely
generated subrings of `A` whatever the cardinality of `A`.

Stacks 08K0 (flatness of the morphism) and Stacks 08K1 are hypotheses, stated at their content in
the situation of Stacks 084W under the convention 07SD. The other hypotheses are those of the
bounded form. The proof uses Stacks 08K0 only for the systems of the finitely generated subrings
of a ring, indexed by the opposite of a directed preorder, where it is proved
(`AlgebraicGeometry.Space.exists_isFlat_overPullback_map_of_chartLimitsInSite`); so
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded'`
has no hypothesis `h08K0`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded`:
  for every ring `A` with `Spec A` in the site, `Complexes_{X/Spec A}` is algebraic, given the
  finite type case.
* `ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded_of_flatDescent`: the
  same, with Stacks 08K0 asked only of the systems of the finitely generated subrings.
* `ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded_of_adjoinDescent`: the
  same, with Stacks 08K0 and Stacks 08K1 both asked only of those systems.
* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded'`:
  the same, with Stacks 08K0 proved.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u z

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}}

attribute [local instance] complexesCategory

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` for presheaves on the big fppf site is a deep instance search
/-- Pullbacks of presheaves on the big fppf site over the terminal scheme (instance search
times out without this shortcut). -/
local instance hasPullbacks_presheaf_ComplexesStackFiniteTypeReductionUnbounded
    (hZ : B.Contains (⊤_ Scheme.{u})) :
    HasPullbacks ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ComplexesStackFiniteTypeReductionUnbounded
    {hZ : B.Contains (⊤_ Scheme.{u})}
    {X Y Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 0DLN, the reduction to a base of finite type over `ℤ`, given Stacks 08K0 and Stacks
08K1 for the systems of finitely generated subrings.** This is
`ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded_of_flatDescent` with its
hypothesis `h08K1` also asked only of the systems `adjoinSiteDiagram B hZ A hA ⋙ yoneda`, as in
`AlgebraicGeometry.Space.exists_adjoinRing_model_unbounded_of_adjoinDescent`. The hypothesis
`h08K1` is put first. -/
theorem isAlgebraicStack_spec_of_finiteType_case_unbounded_of_adjoinDescent
    (h08K1 : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (hZ : B.Contains (⊤_ Scheme.{u})) (i : (Finset A)ᵒᵖ)
      {X Y : Over ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i)} (f : X ⟶ Y),
      IsQuasiCompactSpace B _ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAbsolutelyQuasiSeparated B _ hZ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAlgebraicSpace B _ hZ X.left → IsAlgebraicSpace B _ hZ Y.left →
      IsQuasiCompactSpace B _ hZ X.left → IsAbsolutelyQuasiSeparated B _ hZ hZ X.left →
      IsQuasiCompactSpace B _ hZ Y.left → IsAbsolutelyQuasiSeparated B _ hZ hZ Y.left →
      IsProper B _ hZ
        ((Over.pullback (limit.π (adjoinSiteDiagram B hZ A hA ⋙ yoneda) i)).map f).left →
      IsLocallyOfFiniteType B _ hZ f.left →
      ∃ (j : (Finset A)ᵒᵖ) (e : j ⟶ i),
        IsProper B _ hZ
          ((Over.pullback ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).map e)).map f).left)
    (h08K0 : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (hZ : B.Contains (⊤_ Scheme.{u})) (i : (Finset A)ᵒᵖ)
      {X Y : Over ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i)} (f : X ⟶ Y),
      IsQuasiCompactSpace B _ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAbsolutelyQuasiSeparated B _ hZ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAlgebraicSpace B _ hZ X.left → IsAlgebraicSpace B _ hZ Y.left →
      IsQuasiCompactSpace B _ hZ X.left → IsAbsolutelyQuasiSeparated B _ hZ hZ X.left →
      IsQuasiCompactSpace B _ hZ Y.left → IsAbsolutelyQuasiSeparated B _ hZ hZ Y.left →
      IsFlat B _ hZ
        ((Over.pullback (limit.π (adjoinSiteDiagram B hZ A hA ⋙ yoneda) i)).map f).left →
      IsLocallyOfFinitePresentation B _ hZ f.left →
      ∃ (j : (Finset A)ᵒᵖ) (e : j ⟶ i),
        IsFlat B _ hZ ((Over.pullback ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).map e)).map f).left)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLF : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      Stack.HasRepresentableDiagonal B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D) (h0DLF hS D)))
    (h0DLI : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS)
      {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y),
      ∃ (q : complexesBasedCategory D ⟶ baseBasedCategory D.Y)
        (t : complexesBasedCategory (D.baseChange g) ⟶ complexesBasedCategory D)
        (q' : complexesBasedCategory (D.baseChange g) ⟶ baseBasedCategory Y')
        (e : t ≫ q ≅ q' ≫ baseBasedMap g),
        Nonempty (Bicategory.IsTwoFibreProduct
          (⟨complexesBasedCategory (D.baseChange g), t, q', e⟩ :
            @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
              _ _ _ q (baseBasedMap g))))
    (hcase : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
        (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
        Nonempty (IsTerminal D'.Y) →
          Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D'))
    (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (D : ComplexesSituation B _ hA) (hD : Nonempty (IsTerminal D.Y)) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hA (complexesBasedCategory D) := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let gA := toTerminalSite B hZ hA
  let P := (spacesOverSmallerBaseFunctor B _ _ hA hZ gA).obj D.X
  -- `X ⟶ Spec A`, read over the final scheme, is proper, flat and of finite presentation
  obtain ⟨hDY⟩ := hD
  have hfY : D.f.hom ≫ (yonedaIsoOfIsTerminal hDY).hom = toYonedaId B _ hA D.X.obj :=
    comp_yonedaIsoOfIsTerminal_hom hDY D.f
  have hX : IsProper B _ hA (toYonedaId B _ hA D.X.obj) ∧
      IsFlat B _ hA (toYonedaId B _ hA D.X.obj) ∧
      IsFinitePresentation B _ hA (toYonedaId B _ hA D.X.obj) := by
    rw [← hfY]
    exact (isProper_isFlat_isFinitePresentation_comp_isIso_iff B _ hA D.f.hom
      (yonedaIsoOfIsTerminal hDY).hom).2 ⟨D.proper, D.flat, D.finitePresentation⟩
  have hp : IsProper B _ hZ P.1.hom ∧ IsFlat B _ hZ P.1.hom ∧
      IsFinitePresentation B _ hZ P.1.hom :=
    ⟨(isProper_spacesOverSmallerBaseFunctor_obj_hom_iff B hA hZ gA D.X).2 hX.1,
      (holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_obj_hom_iff B hA hZ gA D.X _).2 hX.2.1,
      (isFinitePresentation_spacesOverSmallerBaseFunctor_obj_hom_iff B hA hZ gA D.X).2 hX.2.2⟩
  -- Stacks 07SK (under the convention 07SD, which this system satisfies), 08K0, 08K1: a finite
  -- type model over some `Spec Λ_s`
  obtain ⟨s, X₁, hX₁, f₁, hf₁, π, hsq⟩ :=
    exists_adjoinRing_model_unbounded_of_adjoinDescent B hZ A hA (h08K1 A hA hZ) (h08K0 A hA hZ)
      P.2 P.1.hom hp
  let D₁ : ComplexesSituation B _ hZ :=
    { X := ⟨X₁, hX₁⟩
      Y := schemeSpace ((adjoinSiteDiagram B hZ A hA).obj (Opposite.op s))
      f := ObjectProperty.homMk f₁
      finitePresentation := hf₁.2.2
      proper := hf₁.1
      flat := hf₁.2.1 }
  -- the base change from the model
  exact isAlgebraicStack_of_finiteTypeModel hcomp h0DLF h0DLG h0DLI hcase hZ hA gA D ⟨hDY⟩
    (adjoinRing A s) (contains_spec_adjoinRing B A hA s)
    (toTerminalSite B hZ (contains_spec_adjoinRing B A hA s))
    ((adjoinSiteCone B hZ A hA).π.app (Opposite.op s)) D₁ (Iso.refl _) π hsq

/-- **Stacks 0DLN, the reduction to a base of finite type over `ℤ`, given Stacks 08K0 for the
systems of finitely generated subrings.** This is
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded`
with its hypothesis `h08K0` asked only of the systems `adjoinSiteDiagram B hZ A hA ⋙ yoneda`
of the spectra of the finitely generated subrings of a ring `A`, the systems at which the proof
uses it, as in `AlgebraicGeometry.Space.exists_adjoinRing_model_unbounded_of_flatDescent`. That
case is proved: `AlgebraicGeometry.Space.exists_isFlat_overPullback_map_of_chartLimitsInSite`,
giving
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded'`.
-/
theorem isAlgebraicStack_spec_of_finiteType_case_unbounded_of_flatDescent
    (h08K0 : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (hZ : B.Contains (⊤_ Scheme.{u})) (i : (Finset A)ᵒᵖ)
      {X Y : Over ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i)} (f : X ⟶ Y),
      IsQuasiCompactSpace B _ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAbsolutelyQuasiSeparated B _ hZ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAlgebraicSpace B _ hZ X.left → IsAlgebraicSpace B _ hZ Y.left →
      IsQuasiCompactSpace B _ hZ X.left → IsAbsolutelyQuasiSeparated B _ hZ hZ X.left →
      IsQuasiCompactSpace B _ hZ Y.left → IsAbsolutelyQuasiSeparated B _ hZ hZ Y.left →
      IsFlat B _ hZ
        ((Over.pullback (limit.π (adjoinSiteDiagram B hZ A hA ⋙ yoneda) i)).map f).left →
      IsLocallyOfFinitePresentation B _ hZ f.left →
      ∃ (j : (Finset A)ᵒᵖ) (e : j ⟶ i),
        IsFlat B _ hZ ((Over.pullback ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).map e)).map f).left)
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      (∀ (i : I) (Z : BigAffineFppf B S hS)
        (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
        (W : Over i ⥤ BigAffineFppf B S hS),
        (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
          (Over.post (X := i) D ⋙ Over.pullback g) ⋙
            Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
        ∀ c : Cone (((W ⋙ BigAffineFppf.inclusion B S hS) ⋙
            BigFppfOver.forget B S hS) ⋙ B.inclusion),
          IsLimit c → B.Contains c.pt) →
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
      ∀ (i : I) {X Y : Over (D.obj i)} (f : X ⟶ Y),
        IsQuasiCompactSpace B S hS (D.obj i) → IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i) →
        IsAlgebraicSpace B S hS X.left → IsAlgebraicSpace B S hS Y.left →
        IsQuasiCompactSpace B S hS X.left → IsAbsolutelyQuasiSeparated B S hS hZ X.left →
        IsQuasiCompactSpace B S hS Y.left → IsAbsolutelyQuasiSeparated B S hS hZ Y.left →
        IsProper B S hS ((Over.pullback (limit.π D i)).map f).left →
        IsLocallyOfFiniteType B S hS f.left →
        ∃ (j : I) (e : j ⟶ i), IsProper B S hS ((Over.pullback (D.map e)).map f).left)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLF : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      Stack.HasRepresentableDiagonal B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D) (h0DLF hS D)))
    (h0DLI : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS)
      {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y),
      ∃ (q : complexesBasedCategory D ⟶ baseBasedCategory D.Y)
        (t : complexesBasedCategory (D.baseChange g) ⟶ complexesBasedCategory D)
        (q' : complexesBasedCategory (D.baseChange g) ⟶ baseBasedCategory Y')
        (e : t ≫ q ≅ q' ≫ baseBasedMap g),
        Nonempty (Bicategory.IsTwoFibreProduct
          (⟨complexesBasedCategory (D.baseChange g), t, q', e⟩ :
            @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
              _ _ _ q (baseBasedMap g))))
    (hcase : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
        (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
        Nonempty (IsTerminal D'.Y) →
          Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D'))
    (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (D : ComplexesSituation B _ hA) (hD : Nonempty (IsTerminal D.Y)) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hA (complexesBasedCategory D) :=
  isAlgebraicStack_spec_of_finiteType_case_unbounded_of_adjoinDescent
    (fun A _ hA hZ i _ _ f => h08K1 hZ hZ _ (adjoinSiteDiagram_chartLimitsInSite B hZ A hA)
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).1
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).2.1 i f)
    h08K0 hcomp h0DLF h0DLG h0DLI hcase A hA D hD

/-- **Stacks 0DLN, the reduction from `S = B = Spec A` to `Λ` of finite type over `ℤ`, for every
ring `A`** (the fifth paragraph of the source's proof). Let `A` be a ring with `Spec A` in the
site, and let `D` be a situation of Stacks 0DLE over `S = Spec A` whose base is the final
algebraic space. Then `Complexes_{X/Spec A}` is an algebraic stack over `Spec A`.

This is `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case`
without its bound on the cardinality of `A`. The source writes `A` as the filtered colimit of its
finite type `ℤ`-subalgebras `Λ_s` and descends `X ⟶ Spec A` to a proper, flat, finitely presented
`X_s ⟶ Spec Λ_s` by Stacks 07SK, 08K0 and 08K1
(`AlgebraicGeometry.Space.exists_adjoinRing_model_unbounded`). Then `Complexes_{X/Spec A}` is a
base change of `Complexes_{X_s/Spec Λ_s}`, which is algebraic by the finite type case.

The hypotheses, apart from `hcase`, are each an input of the proof, stated at its content:

* `h08K0`, `h08K1`: Stacks 08K0 (flatness of the morphism) and Stacks 08K1, in the situation of
  Stacks 084W, with the index bound replaced by the chapter's convention 07SD;
* `hcomp`: the change-of-base comparison
  `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseComparison`, not a Stacks tag;
* `h0DLF`, `h0DLG`, `h0DLI`: Stacks 0DLF, 0DLG and Remark 0DLI, over every base scheme;
* `hcase`: the case `S = B = Spec Λ` with `Λ` of finite type over `ℤ`. -/
theorem isAlgebraicStack_spec_of_finiteType_case_unbounded
    (h08K0 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      (∀ (i : I) (Z : BigAffineFppf B S hS)
        (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
        (W : Over i ⥤ BigAffineFppf B S hS),
        (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
          (Over.post (X := i) D ⋙ Over.pullback g) ⋙
            Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
        ∀ c : Cone (((W ⋙ BigAffineFppf.inclusion B S hS) ⋙
            BigFppfOver.forget B S hS) ⋙ B.inclusion),
          IsLimit c → B.Contains c.pt) →
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
      ∀ (i : I) {X Y : Over (D.obj i)} (f : X ⟶ Y),
        IsQuasiCompactSpace B S hS (D.obj i) → IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i) →
        IsAlgebraicSpace B S hS X.left → IsAlgebraicSpace B S hS Y.left →
        IsQuasiCompactSpace B S hS X.left → IsAbsolutelyQuasiSeparated B S hS hZ X.left →
        IsQuasiCompactSpace B S hS Y.left → IsAbsolutelyQuasiSeparated B S hS hZ Y.left →
        IsFlat B S hS ((Over.pullback (limit.π D i)).map f).left →
        IsLocallyOfFinitePresentation B S hS f.left →
        ∃ (j : I) (e : j ⟶ i), IsFlat B S hS ((Over.pullback (D.map e)).map f).left)
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      (∀ (i : I) (Z : BigAffineFppf B S hS)
        (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
        (W : Over i ⥤ BigAffineFppf B S hS),
        (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
          (Over.post (X := i) D ⋙ Over.pullback g) ⋙
            Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
        ∀ c : Cone (((W ⋙ BigAffineFppf.inclusion B S hS) ⋙
            BigFppfOver.forget B S hS) ⋙ B.inclusion),
          IsLimit c → B.Contains c.pt) →
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
      ∀ (i : I) {X Y : Over (D.obj i)} (f : X ⟶ Y),
        IsQuasiCompactSpace B S hS (D.obj i) → IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i) →
        IsAlgebraicSpace B S hS X.left → IsAlgebraicSpace B S hS Y.left →
        IsQuasiCompactSpace B S hS X.left → IsAbsolutelyQuasiSeparated B S hS hZ X.left →
        IsQuasiCompactSpace B S hS Y.left → IsAbsolutelyQuasiSeparated B S hS hZ Y.left →
        IsProper B S hS ((Over.pullback (limit.π D i)).map f).left →
        IsLocallyOfFiniteType B S hS f.left →
        ∃ (j : I) (e : j ⟶ i), IsProper B S hS ((Over.pullback (D.map e)).map f).left)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLF : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      Stack.HasRepresentableDiagonal B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D) (h0DLF hS D)))
    (h0DLI : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS)
      {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y),
      ∃ (q : complexesBasedCategory D ⟶ baseBasedCategory D.Y)
        (t : complexesBasedCategory (D.baseChange g) ⟶ complexesBasedCategory D)
        (q' : complexesBasedCategory (D.baseChange g) ⟶ baseBasedCategory Y')
        (e : t ≫ q ≅ q' ≫ baseBasedMap g),
        Nonempty (Bicategory.IsTwoFibreProduct
          (⟨complexesBasedCategory (D.baseChange g), t, q', e⟩ :
            @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
              _ _ _ q (baseBasedMap g))))
    (hcase : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
        (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
        Nonempty (IsTerminal D'.Y) →
          Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D'))
    (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (D : ComplexesSituation B _ hA) (hD : Nonempty (IsTerminal D.Y)) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hA (complexesBasedCategory D) :=
  isAlgebraicStack_spec_of_finiteType_case_unbounded_of_flatDescent
    (fun A _ hA hZ i _ _ f => h08K0 hZ hZ _ (adjoinSiteDiagram_chartLimitsInSite B hZ A hA)
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).1
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).2.1 i f)
    h08K1 hcomp h0DLF h0DLG h0DLI hcase A hA D hD

/-- **Stacks 0DLN, the reduction from `S = B = Spec A` to `Λ` of finite type over `ℤ`, for every
ring `A`, with Stacks 08K0 proved.** This is
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded`
without its hypothesis `h08K0`. The proof uses Stacks 08K0 only for the systems of the spectra
of the finitely generated subrings of `A`, indexed by the opposite of the directed preorder
`Finset A`; there it is
`AlgebraicGeometry.Space.exists_isFlat_overPullback_map_of_chartLimitsInSite`, from the form of
Stacks 08K0 under the convention 07SD on the base. The other hypotheses are those of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded`;
`h08K1` (Stacks 08K1) remains a hypothesis. -/
theorem isAlgebraicStack_spec_of_finiteType_case_unbounded'
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      (∀ (i : I) (Z : BigAffineFppf B S hS)
        (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
        (W : Over i ⥤ BigAffineFppf B S hS),
        (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
          (Over.post (X := i) D ⋙ Over.pullback g) ⋙
            Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
        ∀ c : Cone (((W ⋙ BigAffineFppf.inclusion B S hS) ⋙
            BigFppfOver.forget B S hS) ⋙ B.inclusion),
          IsLimit c → B.Contains c.pt) →
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
      ∀ (i : I) {X Y : Over (D.obj i)} (f : X ⟶ Y),
        IsQuasiCompactSpace B S hS (D.obj i) → IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i) →
        IsAlgebraicSpace B S hS X.left → IsAlgebraicSpace B S hS Y.left →
        IsQuasiCompactSpace B S hS X.left → IsAbsolutelyQuasiSeparated B S hS hZ X.left →
        IsQuasiCompactSpace B S hS Y.left → IsAbsolutelyQuasiSeparated B S hS hZ Y.left →
        IsProper B S hS ((Over.pullback (limit.π D i)).map f).left →
        IsLocallyOfFiniteType B S hS f.left →
        ∃ (j : I) (e : j ⟶ i), IsProper B S hS ((Over.pullback (D.map e)).map f).left)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLF : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      Stack.HasRepresentableDiagonal B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D) (h0DLF hS D)))
    (h0DLI : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS)
      {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y),
      ∃ (q : complexesBasedCategory D ⟶ baseBasedCategory D.Y)
        (t : complexesBasedCategory (D.baseChange g) ⟶ complexesBasedCategory D)
        (q' : complexesBasedCategory (D.baseChange g) ⟶ baseBasedCategory Y')
        (e : t ≫ q ≅ q' ≫ baseBasedMap g),
        Nonempty (Bicategory.IsTwoFibreProduct
          (⟨complexesBasedCategory (D.baseChange g), t, q', e⟩ :
            @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
              _ _ _ q (baseBasedMap g))))
    (hcase : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
        (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
        Nonempty (IsTerminal D'.Y) →
          Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D'))
    (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (D : ComplexesSituation B _ hA) (hD : Nonempty (IsTerminal D.Y)) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hA (complexesBasedCategory D) :=
  isAlgebraicStack_spec_of_finiteType_case_unbounded_of_flatDescent
    (fun A _ hA hZ i _ _ f => exists_isFlat_overPullback_map_of_chartLimitsInSite B _ hZ hZ _
      (adjoinSiteDiagram_chartLimitsInSite B hZ A hA)
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).1
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).2.1 i f)
    h08K1 hcomp h0DLF h0DLG h0DLI hcase A hA D hD

end AlgebraicGeometry.Space.ComplexesSituation

end

module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesIsomPresheaf
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackIsomFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentableRestriction
public import StacksFrontier.AlgebraicGeometry.Quot.LinearEquationsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent

/-!
# The corrected form of Stacks 0DPW, from the conclusions of Stacks 0DLC

Stacks 0DPW asserts that the diagonal of `Complexes_{X/B}` over `B` is affine and of finite
presentation. As stated this is false: the source's proof applies Stacks 0DLC as if the open
`W(E, E')` of that lemma were all of `T`, and a counterexample exists over `X = P¹_{A²} → A²`.
The corrected statement is: the diagonal is representable by algebraic spaces and of finite
presentation, and for objects `(T, E)`, `(T, E')` over the same test scheme, `Isom(E, E')`
factors through the open `W(E, E') ∩ W(E', E) ⊆ T` of Stacks 0DLC and is affine and of finite
presentation over it.

This file proves the corrected statement for the relative derived Isom functor of any morphism
`f : X ⟶ Y`, assuming the conclusions of Stacks 0DLC for the four pairs `(M, N)`, `(N, M)`,
`(M, M)`, `(N, N)`.

## Main results

* `isAffineFinitePresentationAlgebraicSpaceOver_restrict_relativeDerivedIsomFunctor`:
  restricted to the test schemes over `ι : W ⟶ Y`, the Isom functor is affine and of finite
  presentation over `W` when the four restricted Hom functors are.
* `AlgebraicGeometry.Space.relativeDerivedIsomFunctor_corrected_of_opens`: the corrected 0DPW
  conclusion for the relative derived Isom functor, from the conclusions of Stacks 0DLC.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesIsom_corrected_of_opens`: the same at a pair
  of objects of `Complexes_{X/Y}` over one test scheme, with `Isom(x, y)` identified with the
  relative derived Isom functor.

## References

* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y W W' : AlgebraicSpaces B S hS}

/-- Composing test schemes with `j` and then with `ι'` is composing them with `j ≫ ι'`. -/
def schemesOverMapCompIso (j : W ⟶ W') (ι' : W' ⟶ Y) :
    CostructuredArrow.map (S := schemeSpaceFunctor B S hS) j ⋙ CostructuredArrow.map ι' ≅
      CostructuredArrow.map (j ≫ ι') :=
  NatIso.ofComponents (fun T => CostructuredArrow.isoMk (Iso.refl _) (by simp))
    (fun g => CostructuredArrow.hom_ext _ _ (by simp))

/-- **Restriction along a composite.** If the restriction of `R` along `ι'` is affine and of
finite presentation over `W'`, so is its restriction along `j ≫ ι' = ι` over `W`. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.restrict_comp
    {R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)} {ι' : W' ⟶ Y}
    (hR : IsAffineFinitePresentationAlgebraicSpaceOver W' ((CostructuredArrow.map ι').op ⋙ R))
    (j : W ⟶ W') {ι : W ⟶ Y} (hj : j ≫ ι' = ι) :
    IsAffineFinitePresentationAlgebraicSpaceOver W ((CostructuredArrow.map ι).op ⋙ R) := by
  subst hj
  exact (hR.baseChange j).of_iso
    (Functor.isoWhiskerRight (NatIso.op (schemesOverMapCompIso j ι')) R)

/-- Restricted to the test schemes over `ι : W ⟶ Y`, the relative derived Isom functor of `M`
and `N` is affine and of finite presentation over `W` when the four restricted Hom functors
between `M` and `N` are. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_restrict_relativeDerivedIsomFunctor
    (f : X ⟶ Y) (ι : W ⟶ Y) (M N : derivedModules B S hS X)
    (hMN : IsAffineFinitePresentationAlgebraicSpaceOver W
      ((CostructuredArrow.map ι).op ⋙ relativeDerivedHomFunctor f M N))
    (hNM : IsAffineFinitePresentationAlgebraicSpaceOver W
      ((CostructuredArrow.map ι).op ⋙ relativeDerivedHomFunctor f N M))
    (hMM : IsAffineFinitePresentationAlgebraicSpaceOver W
      ((CostructuredArrow.map ι).op ⋙ relativeDerivedHomFunctor f M M))
    (hNN : IsAffineFinitePresentationAlgebraicSpaceOver W
      ((CostructuredArrow.map ι).op ⋙ relativeDerivedHomFunctor f N N)) :
    IsAffineFinitePresentationAlgebraicSpaceOver W
      ((CostructuredArrow.map ι).op ⋙ relativeDerivedIsomFunctor f M N) := by
  have sq := (smallEtaleDerivedPullbackData B S hS).isPullback_relIsoFunctor
    (PullbackData.ConeTo.ofOver (baseChangeOver f))
    (smallEtaleDerivedPullbackData_isCoherent B S hS) M N
  have sq' : IsPullback
      (Functor.whiskerLeft (CostructuredArrow.map ι).op
        ((smallEtaleDerivedPullbackData B S hS).relIsoToPairs
          (PullbackData.ConeTo.ofOver (baseChangeOver f))
          (smallEtaleDerivedPullbackData_isCoherent B S hS) M N))
      (Functor.whiskerLeft (CostructuredArrow.map ι).op
        ((smallEtaleDerivedPullbackData B S hS).relIsoToPUnit
          (PullbackData.ConeTo.ofOver (baseChangeOver f))
          (smallEtaleDerivedPullbackData_isCoherent B S hS) M N))
      (Functor.whiskerLeft (CostructuredArrow.map ι).op
        ((smallEtaleDerivedPullbackData B S hS).relHomComposition
          (PullbackData.ConeTo.ofOver (baseChangeOver f))
          (smallEtaleDerivedPullbackData_isCoherent B S hS) M N))
      (Functor.whiskerLeft (CostructuredArrow.map ι).op
        ((smallEtaleDerivedPullbackData B S hS).relHomIdentities
          (PullbackData.ConeTo.ofOver (baseChangeOver f))
          (smallEtaleDerivedPullbackData_isCoherent B S hS) M N)) :=
    IsPullback.of_forall_isPullback_app fun T => sq.app ((CostructuredArrow.map ι).op.obj T)
  exact IsAffineFinitePresentationAlgebraicSpaceOver.of_isPullback sq'
    (hNM.prod hMN) (hMM.prod hNN)
    (IsAffineFinitePresentationAlgebraicSpaceOver.of_isTerminal isTerminalConstPUnitOnSchemesOver)

/-- A quasi-compact open immersion of algebraic spaces is of finite presentation. -/
theorem isFinitePresentation_of_isOpenImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {j : F ⟶ G} (hj : IsOpenImmersion B S hS j) (hqc : IsQuasiCompact B S hS j) :
    IsFinitePresentation B S hS j :=
  ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hj, hqc,
    isQuasiSeparated_of_isSeparated B S hS
      (isSeparated_of_mono j (mono_of_isOpenImmersion B S hS j hj))⟩

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_ComplexesDiagonalCorrected
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The corrected Stacks 0DPW for the relative derived Isom functor, from the conclusions of
Stacks 0DLC.** Let `f : X ⟶ Y`, `M, N ∈ D(𝒪_X)`, and suppose given the conclusions of
Stacks 0DLC for the pairs `(M, N)` and `(N, M)`: quasi-compact open immersions `ι₁ : W₁ ⟶ Y`,
`ι₂ : W₂ ⟶ Y` through which every test scheme with vanishing negative fibre Exts from `M` to `N`
(resp. from `N` to `M`) factors, over which `Hom(M, N)` (resp. `Hom(N, M)`) is affine and of
finite presentation; and that `Hom(M, M)`, `Hom(N, N)` are affine and of finite presentation over
`Y` and `M` has no negative fibrewise self-Exts (Stacks 0DLD).  Then the intersection
`ι : W = W₁ ∩ W₂ ⟶ Y` is a quasi-compact open immersion, `Isom(M, N)` factors through it, is
affine and of finite presentation over it, and is an algebraic space of finite presentation over
`Y`. -/
theorem relativeDerivedIsomFunctor_corrected_of_opens (f : X ⟶ Y) (M N : derivedModules B S hS X)
    {W₁ W₂ : AlgebraicSpaces B S hS} (ι₁ : W₁ ⟶ Y) (ι₂ : W₂ ⟶ Y)
    (hι₁ : IsOpenImmersion B S hS ι₁.hom) (hι₂ : IsOpenImmersion B S hS ι₂.hom)
    (hqc₁ : IsQuasiCompact B S hS ι₁.hom) (hqc₂ : IsQuasiCompact B S hS ι₂.hom)
    (hW₁ : ∀ T : SchemesOver Y, HasNoNegativeFibreExtOver f M N T →
      ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ W₁, t ≫ ι₁ = T.hom)
    (hW₂ : ∀ T : SchemesOver Y, HasNoNegativeFibreExtOver f N M T →
      ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ W₂, t ≫ ι₂ = T.hom)
    (hMN : IsAffineFinitePresentationAlgebraicSpaceOver W₁
      ((CostructuredArrow.map ι₁).op ⋙ relativeDerivedHomFunctor f M N))
    (hNM : IsAffineFinitePresentationAlgebraicSpaceOver W₂
      ((CostructuredArrow.map ι₂).op ⋙ relativeDerivedHomFunctor f N M))
    (hMM : IsAffineFinitePresentationAlgebraicSpaceOver Y (relativeDerivedHomFunctor f M M))
    (hNN : IsAffineFinitePresentationAlgebraicSpaceOver Y (relativeDerivedHomFunctor f N N))
    (hM : ∀ T : SchemesOver Y, HasNoNegativeFibreExtOver f M M T) :
    ∃ (W : AlgebraicSpaces B S hS) (ι : W ⟶ Y),
      IsOpenImmersion B S hS ι.hom ∧ IsQuasiCompact B S hS ι.hom ∧
      (∃ k₁ : W ⟶ W₁, k₁ ≫ ι₁ = ι) ∧ (∃ k₂ : W ⟶ W₂, k₂ ≫ ι₂ = ι) ∧
      (∀ T : SchemesOver Y, Nonempty ((relativeDerivedIsomFunctor f M N).obj (op T)) →
        ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ W, t ≫ ι = T.hom) ∧
      IsAffineFinitePresentationAlgebraicSpaceOver W
        ((CostructuredArrow.map ι).op ⋙ relativeDerivedIsomFunctor f M N) ∧
      IsFinitePresentationAlgebraicSpaceOver Y (relativeDerivedIsomFunctor f M N) := by
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS ι₁ ι₂
  let k₁ : AlgebraicSpaces.fiberProduct B S hS ι₁ ι₂ ⟶ W₁ :=
    ObjectProperty.homMk (pullback.fst ι₁.hom ι₂.hom)
  let k₂ : AlgebraicSpaces.fiberProduct B S hS ι₁ ι₂ ⟶ W₂ :=
    ObjectProperty.homMk (pullback.snd ι₁.hom ι₂.hom)
  have hk : k₁ ≫ ι₁ = k₂ ≫ ι₂ := sq.w
  have hιopen : IsOpenImmersion B S hS (k₁ ≫ ι₁).hom :=
    isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isPullback B S hS sq.flip hι₂) hι₁
  have hιqc : IsQuasiCompact B S hS (k₁ ≫ ι₁).hom :=
    isQuasiCompact_comp B S hS W₁.property Y.property _ _
      (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback ι₁.hom ι₂.hom).flip hqc₂) hqc₁
  have hfactor : ∀ T : SchemesOver Y,
      Nonempty ((relativeDerivedIsomFunctor f M N).obj (op T)) →
        ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ _, t ≫ (k₁ ≫ ι₁) = T.hom := by
    rintro T ⟨α⟩
    obtain ⟨h₁, h₂⟩ := hasNoNegativeFibreExtOver_of_relativeDerivedIsomFunctor f (hM T) α
    obtain ⟨t₁, ht₁⟩ := hW₁ T h₁
    obtain ⟨t₂, ht₂⟩ := hW₂ T h₂
    exact ⟨sq.lift t₁ t₂ (ht₁.trans ht₂.symm), by
      rw [← Category.assoc, sq.lift_fst, ht₁]⟩
  have hIsom : IsAffineFinitePresentationAlgebraicSpaceOver _
      ((CostructuredArrow.map (k₁ ≫ ι₁)).op ⋙ relativeDerivedIsomFunctor f M N) :=
    isAffineFinitePresentationAlgebraicSpaceOver_restrict_relativeDerivedIsomFunctor f _ M N
      (hMN.restrict_comp k₁ rfl) (hNM.restrict_comp k₂ hk.symm)
      (hMM.baseChange _) (hNN.baseChange _)
  exact ⟨_, k₁ ≫ ι₁, hιopen, hιqc, ⟨k₁, rfl⟩, ⟨k₂, hk.symm⟩, hfactor, hIsom,
    IsFinitePresentationAlgebraicSpaceOver.of_restrict
      (mono_of_isOpenImmersion B S hS _ hιopen)
      (isFinitePresentation_of_isOpenImmersion hιopen hιqc) hfactor hIsom⟩

namespace ComplexesSituation

attribute [local instance] complexesCategory

variable {D : ComplexesSituation B S hS} (A : ComplexesObject D)
  (E' : derivedModules B S hS (D.space A.T)) (h₁ : D.IsRelativelyPerfect A.T E')
  (h₂ : D.HasNoNegativeFibreExt A.T E')

/-- **The corrected Stacks 0DPW at a pair of objects `x = (T, E)`, `y = (T, E')` of
`Complexes_{X/Y}` over the same test scheme, from the conclusions of Stacks 0DLC.** Writing
`X_T ⟶ T` for the projection, suppose given the conclusions of Stacks 0DLC for `(E, E')` and
`(E', E)` (quasi-compact opens `W₁`, `W₂` of `T` through which every test scheme with vanishing
mixed negative fibre Exts factors, over which the Hom functors are affine and of finite
presentation) and of Stacks 0DLD, part (c), for `E` and `E'`.  Then the presheaf `Isom(x, y)` on
`(Sch/T)` is the relative derived Isom functor, which factors through the quasi-compact open
`W = W₁ ∩ W₂`, is affine and of finite presentation over `W`, and is an algebraic space of finite
presentation over `T`. Condition (2) of Stacks 0DLD for `E` is the field
`A.noNegativeFibreExt`. -/
theorem complexesIsom_corrected_of_opens
    {W₁ W₂ : AlgebraicSpaces B S hS} (ι₁ : W₁ ⟶ (schemeSpaceFunctor B S hS).obj A.T.left)
    (ι₂ : W₂ ⟶ (schemeSpaceFunctor B S hS).obj A.T.left)
    (hι₁ : IsOpenImmersion B S hS ι₁.hom) (hι₂ : IsOpenImmersion B S hS ι₂.hom)
    (hqc₁ : IsQuasiCompact B S hS ι₁.hom) (hqc₂ : IsQuasiCompact B S hS ι₂.hom)
    (hW₁ : ∀ T', HasNoNegativeFibreExtOver (D.projection A.T) A.E E' T' →
      ∃ t : (schemeSpaceFunctor B S hS).obj T'.left ⟶ W₁, t ≫ ι₁ = T'.hom)
    (hW₂ : ∀ T', HasNoNegativeFibreExtOver (D.projection A.T) E' A.E T' →
      ∃ t : (schemeSpaceFunctor B S hS).obj T'.left ⟶ W₂, t ≫ ι₂ = T'.hom)
    (hEE' : IsAffineFinitePresentationAlgebraicSpaceOver W₁
      ((CostructuredArrow.map ι₁).op ⋙ relativeDerivedHomFunctor (D.projection A.T) A.E E'))
    (hE'E : IsAffineFinitePresentationAlgebraicSpaceOver W₂
      ((CostructuredArrow.map ι₂).op ⋙ relativeDerivedHomFunctor (D.projection A.T) E' A.E))
    (hEE : IsAffineFinitePresentationAlgebraicSpaceOver _
      (relativeDerivedHomFunctor (D.projection A.T) A.E A.E))
    (hE'E' : IsAffineFinitePresentationAlgebraicSpaceOver _
      (relativeDerivedHomFunctor (D.projection A.T) E' E')) :
    Nonempty ((complexesFunctor D).isomPresheaf ⟨A, rfl⟩ ⟨sameTest A E' h₁ h₂, rfl⟩ ≅
      (overSchemeTest A.T.left).op ⋙ relativeDerivedIsomFunctor (D.projection A.T) A.E E') ∧
    ∃ (W : AlgebraicSpaces B S hS) (ι : W ⟶ (schemeSpaceFunctor B S hS).obj A.T.left),
      IsOpenImmersion B S hS ι.hom ∧ IsQuasiCompact B S hS ι.hom ∧
      (∃ k₁ : W ⟶ W₁, k₁ ≫ ι₁ = ι) ∧ (∃ k₂ : W ⟶ W₂, k₂ ≫ ι₂ = ι) ∧
      (∀ T', Nonempty ((relativeDerivedIsomFunctor (D.projection A.T) A.E E').obj (op T')) →
        ∃ t : (schemeSpaceFunctor B S hS).obj T'.left ⟶ W, t ≫ ι = T'.hom) ∧
      IsAffineFinitePresentationAlgebraicSpaceOver W
        ((CostructuredArrow.map ι).op ⋙ relativeDerivedIsomFunctor (D.projection A.T) A.E E') ∧
      IsFinitePresentationAlgebraicSpaceOver _
        (relativeDerivedIsomFunctor (D.projection A.T) A.E E') :=
  ⟨⟨complexesIsomPresheafIsoRelativeDerivedIsomFunctor A E' h₁ h₂⟩,
    relativeDerivedIsomFunctor_corrected_of_opens (D.projection A.T) A.E E' ι₁ ι₂ hι₁ hι₂ hqc₁
      hqc₂ hW₁ hW₂ hEE' hE'E hEE hE'E'
      (hasNoNegativeFibreExtOver_of_hasNoNegativeFibreExt A.T A.E A.noNegativeFibreExt)⟩

end ComplexesSituation

end AlgebraicGeometry.Space

end

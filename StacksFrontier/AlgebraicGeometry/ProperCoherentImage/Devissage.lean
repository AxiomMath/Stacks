module

public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Splitting
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# Dévissage for coherence of higher direct images

For a morphism of schemes `f : X ⟶ S`, write `P F` for the assertion that every higher direct
image `R ᵖ f_* F` of an `𝒪_X`-module `F` is coherent. The property `P` holds on the zero module
and is stable under extensions, for an arbitrary morphism `f`. When `f` is proper and `S` is
affine and locally Noetherian, `X` is Noetherian, and the dévissage of coherent modules on a
Noetherian scheme [Stacks, Tag 01YG] then shows that `P` holds on every coherent `𝒪_X`-module as
soon as it holds on the direct images of quasi-coherent ideal sheaves on integral closed
subschemes of `X`. Conversely, those direct images are themselves coherent, so the two
statements are equivalent.

All declarations are in the namespace `AlgebraicGeometry.ProperCoherentImage`.

## Main definitions

* `higherDirectImageDeltaFunctor`: the higher direct images along a morphism of schemes, as a
  cohomological `δ`-functor.
* `HigherDirectImageIsCoherentOnIntegralIdeals`: the statement that, for every proper morphism
  to an affine locally Noetherian scheme, `P` holds on the direct image of every quasi-coherent
  ideal sheaf on every integral closed subscheme.

## Main results

* `isCoherent_higherDirectImage_X₂_of_shortExact`: the property `P` is stable under extensions.
* `isCoherent_higherDirectImage_terminal`: `P` holds on the zero module.
* `isNoetherian_of_isProper_of_isAffine`: the source of a proper morphism to an affine locally
  Noetherian scheme is Noetherian.
* `isCoherent_higherDirectImage_of_integralIdeals`: for a proper morphism `f : X ⟶ S` to an
  affine locally Noetherian scheme, if `X` admits irreducible dévissage and `P` holds on the
  direct images of quasi-coherent ideal sheaves on integral closed subschemes of `X`, then `P`
  holds on every coherent `𝒪_X`-module.
* `higherDirectImageIsCoherentOnIntegralIdeals_iff_overAffineBase`: if every Noetherian scheme
  admits irreducible dévissage, then `HigherDirectImageIsCoherentOnIntegralIdeals` is equivalent
  to `HigherDirectImageIsCoherentOverAffineBase`.
* `higherDirectImageIsCoherent_of_integralIdeals`: if every Noetherian scheme admits irreducible
  dévissage, then `HigherDirectImageIsCoherentOnIntegralIdeals` implies
  `HigherDirectImageIsCoherent`.

## Implementation notes

The higher direct image `R ᵖ f_* F₂` of the middle term of a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is an extension of a subobject of `R ᵖ f_* F₃` by a quotient of
`R ᵖ f_* F₁`, and coherence does not pass to arbitrary subobjects or quotients. The quotient is
the cokernel of `δ : R ᵖ⁻¹ f_* F₃ ⟶ R ᵖ f_* F₁` and the subobject is the kernel of
`δ : R ᵖ f_* F₃ ⟶ R ᵖ⁺¹ f_* F₁`, so extension-stability follows from the five-term criterion
[Stacks, Tag 02MO (2)] for the weak Serre class of coherent modules, stated here as
`isCoherent_of_exact₄`. In degree `0` the first arrow of the five-term sequence is replaced by
`R ⁰ f_* F₁ --0--> R ⁰ f_* F₁`, whose exactness at the middle says that
`R ⁰ f_* F₁ ⟶ R ⁰ f_* F₂` is a monomorphism.

`CategoryTheory.DeltaFunctor.functor n` of `higherDirectImageDeltaFunctor f` is the `n`-th
higher direct image only after unfolding the definition, so it is written out at each use
rather than bound with `have`, which would make it opaque.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProperCoherentImage

/-! ### The five-term criterion for coherence -/

section FiveTerm

variable {Y : Type u} [TopologicalSpace Y]
  {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}

/-- If `A₀ ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄` is an exact sequence of sheaves of modules, given as three
exact short complexes, and `A₀`, `A₁`, `A₃`, `A₄` are coherent, then so is `A₂`. -/
theorem isCoherent_of_exact₄ {A₀ A₁ A₂ A₃ A₄ : SheafOfModules.{u} R}
    {f₀ : A₀ ⟶ A₁} {f₁ : A₁ ⟶ A₂} {f₂ : A₂ ⟶ A₃} {f₃ : A₃ ⟶ A₄}
    (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₀ : A₀.IsCoherent) (h₁ : A₁.IsCoherent) (h₃ : A₃.IsCoherent) (h₄ : A₄.IsCoherent) :
    A₂.IsCoherent :=
  ObjectProperty.prop_mid_of_exact₄
    (P := fun M : SheafOfModules.{u} R => M.IsCoherent)
    (fun _ hA => ObjectProperty.prop_obj₂_of_exact _ _ hA)
    w₀ w₁ w₂ e₀ e₁ e₂ h₀ h₁ h₃ h₄

end FiveTerm

attribute [local instance] HasDerivedCategory.standard

/-! ### The long exact sequence of higher direct images -/

/-- The higher direct images `R ᵖ f_*` along a morphism of schemes `f`, as a cohomological
`δ`-functor ([Stacks, Tag 010Q]): the long sequence
`0 ⟶ f_* F₁ ⟶ f_* F₂ ⟶ f_* F₃ ⟶ R ¹ f_* F₁ ⟶ ⋯` attached to a short exact sequence of
`𝒪_X`-modules is exact, and its connecting morphisms are natural in the sequence. -/
noncomputable def higherDirectImageDeltaFunctor {X S : Scheme.{u}} (f : X ⟶ S) :
    CategoryTheory.DeltaFunctor X.Modules S.Modules :=
  Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor (Scheme.Modules.pushforward f)
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure _)
    (Stacks.DerivedIndexing.canonicalδ _) (fun _ _ ↦ rfl)

/-- The degree-`n` functor of `higherDirectImageDeltaFunctor` is the `n`-th higher direct
image. -/
theorem higherDirectImageDeltaFunctor_functor {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    (higherDirectImageDeltaFunctor f).functor n =
      (Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ) :=
  rfl

/-! ### The two dévissage inputs -/

/-- Every higher direct image of the terminal, that is zero, `𝒪_X`-module is coherent. -/
theorem isCoherent_higherDirectImage_terminal {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj (⊤_ X.Modules)).IsCoherent := by
  refine ObjectProperty.prop_of_isZero
    (P := fun M : SheafOfModules.{u} S.ringCatSheaf => M.IsCoherent) ?_
  change IsZero (((higherDirectImageDeltaFunctor f).functor p).obj (⊤_ X.Modules))
  exact Functor.map_isZero _ ((isZero_zero X.Modules).of_iso
    (HasZeroObject.zeroIsoTerminal (C := X.Modules)).symm)

/-- Let `f : X ⟶ S` be a morphism of schemes and `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` a short exact
sequence of `𝒪_X`-modules. If every higher direct image of `F₁` and every higher direct image
of `F₃` along `f` is coherent, then so is every higher direct image of `F₂`. -/
theorem isCoherent_higherDirectImage_X₂_of_shortExact {X S : Scheme.{u}} (f : X ⟶ S)
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    (h₁ : ∀ p : ℕ, (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₁).IsCoherent)
    (h₃ : ∀ p : ℕ, (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₃).IsCoherent)
    (p : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₂).IsCoherent := by
  match p with
  | 0 =>
      exact isCoherent_of_exact₄
        (f₀ := (0 : ((higherDirectImageDeltaFunctor f).functor 0).obj T.X₁ ⟶
          ((higherDirectImageDeltaFunctor f).functor 0).obj T.X₁))
        (f₁ := ((higherDirectImageDeltaFunctor f).functor 0).map T.f)
        (f₂ := ((higherDirectImageDeltaFunctor f).functor 0).map T.g)
        (f₃ := (higherDirectImageDeltaFunctor f).δ hT 0)
        zero_comp ((higherDirectImageDeltaFunctor f).map_f_comp_map_g (S := T) 0)
        ((higherDirectImageDeltaFunctor f).map_g_δ hT 0)
        ((ShortComplex.exact_iff_mono _ rfl).2 ((higherDirectImageDeltaFunctor f).mono_map_f hT))
        ((higherDirectImageDeltaFunctor f).exact_map hT 0)
        ((higherDirectImageDeltaFunctor f).exact_δ₁ hT 0)
        (h₁ 0) (h₁ 0) (h₃ 0) (h₁ 1)
  | (q + 1) =>
      exact isCoherent_of_exact₄
        (f₀ := (higherDirectImageDeltaFunctor f).δ hT q)
        (f₁ := ((higherDirectImageDeltaFunctor f).functor (q + 1)).map T.f)
        (f₂ := ((higherDirectImageDeltaFunctor f).functor (q + 1)).map T.g)
        (f₃ := (higherDirectImageDeltaFunctor f).δ hT (q + 1))
        ((higherDirectImageDeltaFunctor f).δ_map_f hT q)
        ((higherDirectImageDeltaFunctor f).map_f_comp_map_g (S := T) (q + 1))
        ((higherDirectImageDeltaFunctor f).map_g_δ hT (q + 1))
        ((higherDirectImageDeltaFunctor f).exact_δ₂ hT q)
        ((higherDirectImageDeltaFunctor f).exact_map hT (q + 1))
        ((higherDirectImageDeltaFunctor f).exact_δ₁ hT (q + 1))
        (h₃ q) (h₁ (q + 1)) (h₃ (q + 1)) (h₁ (q + 2))

/-! ### Noetherianness of the source -/

/-- The source of a proper morphism to an affine locally Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_isProper_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S]
    [IsLocallyNoetherian S] [IsProper f] : IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

/-! ### The dévissage reduction -/

/-- The statement that, for every proper morphism to an affine locally Noetherian scheme, every
higher direct image of the direct image of a quasi-coherent ideal sheaf on an integral closed
subscheme of the source is coherent. -/
def HigherDirectImageIsCoherentOnIntegralIdeals : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsAffine S → IsLocallyNoetherian S → IsProper f →
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      ∀ I : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
        I.toSheafOfModules.IsQuasicoherent → ∀ p : ℕ,
          (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj
            ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)).IsCoherent

/-- Let `f : X ⟶ S` be a proper morphism to an affine locally Noetherian scheme, such that `X`
admits irreducible dévissage. If every higher direct image along `f` of the direct image of a
quasi-coherent ideal sheaf on an integral closed subscheme of `X` is coherent, then every higher
direct image along `f` of every coherent `𝒪_X`-module is coherent. -/
theorem isCoherent_higherDirectImage_of_integralIdeals {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (hirr : Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage X)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      ∀ I : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
        I.toSheafOfModules.IsQuasicoherent → ∀ p : ℕ,
          (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj
            ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)).IsCoherent)
    (F : X.Modules) (hF : F.IsCoherent) (p : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F).IsCoherent :=
  have : IsNoetherian X := isNoetherian_of_isProper_of_isAffine f
  Stacks.AlgebraicGeometry.IdealPowerSmul.property_of_irreducibleDevissage hirr
    (fun G => ∀ q : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj G).IsCoherent)
    (isCoherent_higherDirectImage_terminal f)
    (fun _ hT _ _ _ hP₁ hP₃ => isCoherent_higherDirectImage_X₂_of_shortExact f hT hP₁ hP₃)
    (fun i hi hZ I hI => hideal i hi hZ I hI)
    F hF p

/-- If every Noetherian scheme admits irreducible dévissage, then
`HigherDirectImageIsCoherentOnIntegralIdeals` implies
`HigherDirectImageIsCoherentOverAffineBase`. -/
theorem higherDirectImageIsCoherentOverAffineBase_of_integralIdeals
    (hirr : ∀ Y : Scheme.{u}, IsNoetherian Y →
      Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage Y)
    (hideal : HigherDirectImageIsCoherentOnIntegralIdeals.{u}) :
    HigherDirectImageIsCoherentOverAffineBase.{u} := fun X S f hS hN hf F hF p =>
  isCoherent_higherDirectImage_of_integralIdeals f
    (hirr X (isNoetherian_of_isProper_of_isAffine f))
    (fun i hi hZ I hI q => hideal X S f ‹_› ‹_› ‹_› i hi hZ I hI q) F hF p

/-- `HigherDirectImageIsCoherentOverAffineBase` implies
`HigherDirectImageIsCoherentOnIntegralIdeals`. -/
theorem higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase
    (haff : HigherDirectImageIsCoherentOverAffineBase.{u}) :
    HigherDirectImageIsCoherentOnIntegralIdeals.{u} := by
  intro X S f hS hN hf Z i hi _hZ I hI p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact haff X S f ‹_› ‹_› ‹_› _
    (ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit i I hI) p

/-- If every Noetherian scheme admits irreducible dévissage, then
`HigherDirectImageIsCoherentOnIntegralIdeals` is equivalent to
`HigherDirectImageIsCoherentOverAffineBase`. -/
theorem higherDirectImageIsCoherentOnIntegralIdeals_iff_overAffineBase
    (hirr : ∀ Y : Scheme.{u}, IsNoetherian Y →
      Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage Y) :
    HigherDirectImageIsCoherentOnIntegralIdeals.{u} ↔
      HigherDirectImageIsCoherentOverAffineBase.{u} :=
  ⟨higherDirectImageIsCoherentOverAffineBase_of_integralIdeals hirr,
    higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase⟩

/-- If every Noetherian scheme admits irreducible dévissage, then
`HigherDirectImageIsCoherentOnIntegralIdeals` implies `HigherDirectImageIsCoherent`. -/
theorem higherDirectImageIsCoherent_of_integralIdeals
    (hirr : ∀ Y : Scheme.{u}, IsNoetherian Y →
      Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage Y)
    (hideal : HigherDirectImageIsCoherentOnIntegralIdeals.{u}) :
    HigherDirectImageIsCoherent.{u} :=
  higherDirectImageIsCoherent_of_overAffineBase
    (higherDirectImageIsCoherentOverAffineBase_of_integralIdeals hirr hideal)

end AlgebraicGeometry.ProperCoherentImage

end

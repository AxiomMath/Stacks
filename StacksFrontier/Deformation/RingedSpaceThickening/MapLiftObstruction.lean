module

public import StacksFrontier.Deformation.RingedSpaceThickening.FlatLift
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction to lifting a map of flat modules across a thickening (Stacks 08LL)

Let

```
X  --i-->  X'
|          |
f          f'
v          v
S  --t-->  S'
```

be a morphism of thickenings of ringed spaces (**Stacks 08KZ**) whose upper arrow is a first
order thickening, with ideal sheaves `ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)` on `X'` and
`𝒥 = ker(𝒪_{S'} ⟶ t_* 𝒪_S)` on `S'`, and suppose the square is *strict* (**Stacks 08L1**). Let
`ℱ'` and `𝒢'` be `𝒪_{X'}`-modules, put `ℱ = i^* ℱ'` and `𝒢 = i^* 𝒢'`, and let `φ : ℱ ⟶ 𝒢` be
`𝒪_X`-linear. If `ℱ'` and `𝒢'` are flat over `S'`, there is a class

    o(φ) ∈ Ext¹_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)

whose vanishing is necessary and sufficient for the existence of an `𝒪_{X'}`-linear map
`φ' : ℱ' ⟶ 𝒢'` lifting `φ`, that is one with `i^* φ' = φ`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.flatLiftSelf`: an `𝒪_{X'}`-module flat over `S'`,
  read as a flat lift of its own restriction to `X`.
* `AlgebraicGeometry.RingedSpaceThickening.idealTensorIsoRestrictionTensorBaseIdeal`: the
  identification `ℐ ⊗_{𝒪_X} 𝒢 ≅ 𝒢 ⊗_{𝒪_X} f^* 𝒥` of **Stacks 08LI** for a module flat over `S'`
  across a strict square.
* `AlgebraicGeometry.RingedSpaceThickening.mapLiftObstruction`: **Stacks 08LL**, the class
  `o(φ)`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.mapLiftObstruction_eq_zero_iff`: **Stacks 08LL**, the
  class `o(φ)` vanishes if and only if `φ` lifts.
* `AlgebraicGeometry.RingedSpaceThickening.kernelExtension_f_comp_of_mapLift`: a lift of `φ`
  restricts on ideal multiples to `1 ⊗ φ`, which is what makes a lift into a map of the two
  kernel extensions in the sense of **Stacks 08L6**.
* `AlgebraicGeometry.RingedSpaceThickening.kernelExtension_g_comp_of_mapLift` and
  `AlgebraicGeometry.RingedSpaceThickening.mapLift_of_kernelExtension_g_comp`: reducing to `φ`
  on the quotients of the two kernel extensions is the same thing as lifting `φ`.

## Implementation notes

The construction is the source's second proof. Because `ℱ'` is flat over `S'` and the square is
strict, **Stacks 08LI** turns the canonical surjection `ℱ' ⟶ i_* ℱ` into an extension

    0 ⟶ i_*(ℐ ⊗_{𝒪_X} ℱ) ⟶ ℱ' ⟶ i_* ℱ ⟶ 0

as in **Stacks 08L4** whose canonical map is the identity: this is
`AlgebraicGeometry.RingedSpaceThickening.FlatLift.kernelExtension` together with
`FlatLift.kernelExtension_action`, the normalization `c_{ℱ'} = 1` of **Stacks 08LM**. With that
normalization on both sides, the compatibility hypothesis of **Stacks 08L6** for `φ` and
`ψ = 1 ⊗ φ` is the identity `1 ≫ (1 ⊗ φ) = (1 ⊗ φ) ≫ 1`, so **Stacks 08L6** applies and
produces a class in `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} 𝒢)` whose vanishing is equivalent to the existence
of a map `ℱ' ⟶ 𝒢'` compatible with `φ` and `1 ⊗ φ`. **Stacks 08LI** identifies the coefficient
module `ℐ ⊗_{𝒪_X} 𝒢` with the source's `𝒢 ⊗_{𝒪_X} f^* 𝒥`, which moves the class into the group
the source states it in; the identification is an isomorphism, hence a monomorphism after the
shift, so vanishing is preserved in both directions.

What remains is that a compatible map is the same thing as a lift. Compatibility with `φ` on
the quotients says `φ' ≫ η_{𝒢'} = η_{ℱ'} ≫ i_* φ` for the unit `η` of `i^* ⊣ i_*`; since `η`
is natural, `η_{ℱ'}` is an epimorphism across a thickening and `i_*` is faithful, that is
exactly `i^* φ' = φ`. Compatibility with `1 ⊗ φ` on the kernels is then automatic, and that is
`kernelExtension_f_comp_of_mapLift`: the two normalizations say that the ideal action on `ℱ'`
and on `𝒢'` factors through the respective extensions, the ideal action is natural in the
module, and the comparison `ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_*(ℐ ⊗_{𝒪_X} ℱ)` of **Stacks 08L4** is
natural in `ℱ`; cancelling the two epimorphisms `ℐ ⊗ η_{ℱ'}` and that comparison leaves the
required identity.

Only the upper thickening is required to be first order. The lower one is first order in the
source's situation, but the hypothesis is not used: the coefficient module `𝒢 ⊗_{𝒪_X} f^* 𝒥` is
`AlgebraicGeometry.RingedSpaceThickening.restrictionTensorBaseIdeal`, built from `f^* t^* 𝒥`
directly rather than through the identification `(f')^* 𝒥 = f^* 𝒥` that the first order
hypothesis on `t` supplies.

## References

* [Stacks Project, Tag 08LL](https://stacks.math.columbia.edu/tag/08LL)
* [Stacks Project, Tag 08L6](https://stacks.math.columbia.edu/tag/08L6)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
* [Stacks Project, Tag 08LM](https://stacks.math.columbia.edu/tag/08LM)
* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe w u

namespace CategoryTheory

/-- **The bracketing of the cancellation of `kernelExtension_f_comp_of_mapLift`.** With `u` and
`d` epimorphisms, two factorizations `h1` and `h2` of `a` and `a'`, a naturality square `h3`
relating them, and two compatibilities `h5` and `h6`, the maps `f` and `f'` are intertwined by
`p` and `pp`.

It is stated for an arbitrary category because the only content is the bracketing: a goal
mentioning the tensor product of sheaves of modules on a ringed space is not type-correct at the
`implicit` transparency at which `rw` and `simp only` match their patterns, because the two
spellings `structureSheafRing` and
`structureSheafRing` of the structure sheaf are
identified only at default transparency. -/
theorem comp_eq_of_factorizations_of_epi_of_epi {C : Type*} [Category C]
    {T U K M T' U' L N : C}
    (u : T ⟶ U) (d : U ⟶ K) (f : K ⟶ M) (p : M ⟶ N)
    (tp : T ⟶ T') (u' : T' ⟶ U') (d' : U' ⟶ L) (f' : L ⟶ N)
    (a : T ⟶ M) (a' : T' ⟶ N) (q : U ⟶ U') (pp : K ⟶ L)
    (hu : Epi u) (hd : Epi d)
    (h1 : u ≫ d ≫ f = a) (h2 : u' ≫ d' ≫ f' = a')
    (h3 : a ≫ p = tp ≫ a') (h5 : tp ≫ u' = u ≫ q) (h6 : q ≫ d' = d ≫ pp) :
    f ≫ p = pp ≫ f' := by
  refine (cancel_epi d).1 ((cancel_epi u).1 ?_)
  rw [reassoc_of% h1, h3, ← h2, reassoc_of% h5, reassoc_of% h6]

end CategoryTheory

namespace AlgebraicGeometry.RingedSpaceThickening

variable {D : MorphismOfThickenings.{u}}

/-! ### A module flat over the thickened base as a flat lift of its own restriction -/

/-- An `𝒪_{X'}`-module flat over `S'`, read as a flat lift of its restriction `i^* ℱ'` along
the identity. -/
noncomputable def flatLiftSelf (F' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F') :
    FlatLift D ((modulePullback D.i).obj F') where
  module' := F'
  flat := hF'
  identification := Iso.refl _

/-- The canonical surjection of the tautological flat lift is the unit of `i^* ⊣ i_*`. -/
theorem flatLiftSelf_reduction (F' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F') :
    (flatLiftSelf F' hF').reduction =
      (modulePullbackPushforwardAdjunction D.i).unit.app F' :=
  (congrArg (fun z => (modulePullbackPushforwardAdjunction D.i).unit.app F' ≫ z)
    ((modulePushforward D.i).map_id ((modulePullback D.i).obj F'))).trans (Category.comp_id _)

/-- The surjection of the kernel extension of the tautological flat lift is the unit of
`i^* ⊣ i_*`. -/
theorem flatLiftSelf_kernelExtension_g (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F') :
    ((flatLiftSelf F' hF').kernelExtension hi hs).g =
      (modulePullbackPushforwardAdjunction D.i).unit.app F' :=
  (FlatLift.kernelExtension_g hi hs (flatLiftSelf F' hF')).trans
    (flatLiftSelf_reduction F' hF')

/-! ### Compatibility of a lift with the two kernel extensions -/

/-- **A lift of `φ` reduces to `φ` on the quotients of the two kernel extensions.** The square
expressing it is naturality of the unit of `i^* ⊣ i_*`. -/
theorem kernelExtension_g_comp_of_mapLift (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F')
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G')
    (φ' : F' ⟶ G') (hφ' : (modulePullback D.i).map φ' = φ) :
    φ' ≫ ((flatLiftSelf G' hG').kernelExtension hi hs).g =
      ((flatLiftSelf F' hF').kernelExtension hi hs).g ≫ (modulePushforward D.i).map φ := by
  rw [flatLiftSelf_kernelExtension_g hi hs G' hG', flatLiftSelf_kernelExtension_g hi hs F' hF',
    ← hφ']
  exact (modulePullbackPushforwardAdjunction D.i).unit.naturality φ'

/-- **A map reducing to `φ` on the quotients of the two kernel extensions is a lift of `φ`.**
The unit of `i^* ⊣ i_*` is an epimorphism across a thickening and `i_*` is faithful, so the
square of `kernelExtension_g_comp_of_mapLift` determines `i^* φ'`. -/
theorem mapLift_of_kernelExtension_g_comp (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F')
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G')
    (φ' : F' ⟶ G')
    (h : φ' ≫ ((flatLiftSelf G' hG').kernelExtension hi hs).g =
      ((flatLiftSelf F' hF').kernelExtension hi hs).g ≫ (modulePushforward D.i).map φ) :
    (modulePullback D.i).map φ' = φ := by
  have hfaithful : (modulePushforward D.i).Faithful :=
    (closedQuotientOfIsThickening D.i D.i_isThickening).faithful_modulePushforward
  have hepi : Epi ((modulePullbackPushforwardAdjunction D.i).unit.app F') :=
    epi_unit_app_of_isThickening D.i D.i_isThickening F'
  have hnat : (modulePullbackPushforwardAdjunction D.i).unit.app F' ≫
        (modulePushforward D.i).map ((modulePullback D.i).map φ') =
      φ' ≫ (modulePullbackPushforwardAdjunction D.i).unit.app G' :=
    ((modulePullbackPushforwardAdjunction D.i).unit.naturality φ').symm
  rw [flatLiftSelf_kernelExtension_g hi hs G' hG',
    flatLiftSelf_kernelExtension_g hi hs F' hF'] at h
  exact (modulePushforward D.i).map_injective ((cancel_epi
    ((modulePullbackPushforwardAdjunction D.i).unit.app F')).1 (hnat.trans h))

/-- The normalized comparison of **Stacks 08L4** is the comparison itself: by definition it is
the comparison followed by the direct image of an identity. -/
theorem idealTensorAction_eq_extensionTensorComparison
    (F : SheafOfModules.{u} (structureSheafRing D.X)) :
    idealTensorAction D F = extensionTensorComparison D.i F :=
  (congrArg (fun z => extensionTensorComparison D.i F ≫ z)
    ((modulePushforward D.i).map_id (idealTensor D F))).trans (Category.comp_id _)

-- The comparison of Tag 08L4 is named at the tensor product's `.obj`-applied spelling and the
-- map of the pair at the uncurried one; reconciling them needs `Functor.uncurry` and nothing
-- below it, so the tensor product itself is kept folded here.
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- **A lift of `φ` restricts to `1 ⊗ φ` on the kernels of the two kernel extensions.**

Both extensions are normalized (`FlatLift.kernelExtension_action`), so the ideal action on `ℱ'`
is `ℐ ⊗ η_{ℱ'}` followed by the comparison of **Stacks 08L4** and the injection of the
extension, and likewise for `𝒢'`. The ideal action is natural in the module and the comparison
is natural in `ℱ`; together with the square of `kernelExtension_g_comp_of_mapLift` this gives
the required identity once the two epimorphisms `ℐ ⊗ η_{ℱ'}` and the comparison are
cancelled. -/
theorem kernelExtension_f_comp_of_mapLift (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F')
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G')
    (φ' : F' ⟶ G') (hφ' : (modulePullback D.i).map φ' = φ) :
    ((flatLiftSelf F' hF').kernelExtension hi hs).f ≫ φ' =
      (modulePushforward D.i).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map
              (((𝟙 (idealSheafPullback D.i)), φ) :
                ((idealSheafPullback D.i), ((modulePullback D.i).obj F')) ⟶
                ((idealSheafPullback D.i), ((modulePullback D.i).obj G'))))) ≫
        ((flatLiftSelf G' hG').kernelExtension hi hs).f := by
  -- The normalization: the ideal action factors through each kernel extension.
  have hnorm : ∀ (H' : SheafOfModules.{u} (structureSheafRing D.X'))
      (hH' : AlgebraicGeometry.IsFlatOver D.f' H'),
      (idealTensorFunctor D.i).map ((flatLiftSelf H' hH').kernelExtension hi hs).g ≫
        idealTensorAction D ((modulePullback D.i).obj H') ≫
          ((flatLiftSelf H' hH').kernelExtension hi hs).f =
      (idealActionNatTrans D.i).app H' := fun H' hH' =>
    (flatLiftSelf H' hH').descendedAction_of_isKernelExtension hi
      ((flatLiftSelf H' hH').isKernelExtension_kernelExtension hi hs)
  -- Naturality of the ideal action at the lift.
  have hact : (idealActionNatTrans D.i).app F' ≫ φ' =
      (idealTensorFunctor D.i).map φ' ≫ (idealActionNatTrans D.i).app G' :=
    ((idealActionNatTrans D.i).naturality φ').symm
  -- Naturality of the comparison of Tag 08L4 at `φ`.
  have hcmp : (idealTensorFunctor D.i).map ((modulePushforward D.i).map φ) ≫
        idealTensorAction D ((modulePullback D.i).obj G') =
      idealTensorAction D ((modulePullback D.i).obj F') ≫
        (modulePushforward D.i).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map
              (((𝟙 (idealSheafPullback D.i)), φ) :
                ((idealSheafPullback D.i), ((modulePullback D.i).obj F')) ⟶
                ((idealSheafPullback D.i), ((modulePullback D.i).obj G'))))) := by
    rw [idealTensorAction_eq_extensionTensorComparison,
      idealTensorAction_eq_extensionTensorComparison, idealTensorFunctor_map]
    exact (extensionTensorComparison_naturality D.i ((modulePullback D.i).obj F')
      ((modulePullback D.i).obj G') φ).symm
  -- The ideal tensor of the quotient square of the lift.
  have h5 := ((idealTensorFunctor D.i).map_comp _ _).symm.trans
    ((congrArg (idealTensorFunctor D.i).map
      (kernelExtension_g_comp_of_mapLift hi hs F' G' hF' hG' φ φ' hφ')).trans
      ((idealTensorFunctor D.i).map_comp _ _))
  exact CategoryTheory.comp_eq_of_factorizations_of_epi_of_epi _ _ _ _ _ _ _ _ _ _ _ _
    (idealTensorFunctor_epi D.i _ ((flatLiftSelf F' hF').kernelExtension hi hs).epi_g)
    (epi_idealTensorAction D ((modulePullback D.i).obj F'))
    (hnorm F' hF') (hnorm G' hG') hact h5 hcmp

/-! ### The coefficient module of the source -/

/-- **The ideal action identifies `i^* ℐ ⊗_{𝒪_X} 𝒢` with the ideal multiple `ℐ𝒢'`**, for a
module flat over `S'` across a strict square: this is `isIso_restrictedIdealAction_of_isFlatOver`
with the **Stacks 01CD** comparison, itself invertible, cancelled on the left. -/
theorem isIso_sourceIdealActionImage (hs : D.IsStrict)
    (G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G') :
    IsIso (sourceIdealActionImage D G') := by
  have hcmp : IsIso ((Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app
    (D.idealI, G')) := inferInstance
  have h : IsIso ((Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app (D.idealI, G') ≫
      sourceIdealActionImage D G') :=
    isIso_restrictedIdealAction_of_isFlatOver D hs G' hG'
  exact IsIso.of_isIso_comp_left
    ((Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app (D.idealI, G'))
    (sourceIdealActionImage D G')

/-- **Stacks Project, Tag 08LI.** For a strict morphism of thickenings and an `𝒪_{X'}`-module
`𝒢'` flat over `S'`, the coefficient module `ℐ ⊗_{𝒪_X} 𝒢` of **Stacks 08LM** is the source's
`𝒢 ⊗_{𝒪_X} f^* 𝒥`: both are the ideal multiple `ℐ𝒢'`, the first by `sourceIdealActionImage`
and the second by `infinitesimalTensorIso`. -/
noncomputable def idealTensorIsoRestrictionTensorBaseIdeal (hs : D.IsStrict)
    (G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G') :
    idealTensor D ((modulePullback D.i).obj G') ≅ restrictionTensorBaseIdeal D G' :=
  @asIso _ _ _ _ (sourceIdealActionImage D G')
      (isIso_sourceIdealActionImage hs G' hG') ≪≫
    (infinitesimalTensorIso D hs G' hG').symm

-- The canonical map of the extension is named at the tensor product's `.obj`-applied spelling
-- and the map of the pair at the uncurried one; reconciling them needs `Functor.uncurry` and
-- nothing below it, so the tensor product itself is kept folded here.
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The compatibility hypothesis of **Stacks 08L6** for the two kernel extensions of
**Stacks 08LM** and the pair `(φ, 1 ⊗ φ)`: both extensions are normalized, so the square is the
identity `1 ≫ (1 ⊗ φ) = (1 ⊗ φ) ≫ 1`. -/
theorem kernelExtension_action_compat (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F')
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G') :
    (firstOrderExtensionAction D.i ((modulePullback D.i).obj F')
          (idealTensor D ((modulePullback D.i).obj F')) hi
          ((flatLiftSelf F' hF').kernelExtension hi hs)).val ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map
            (((𝟙 (idealSheafPullback D.i)), φ) :
              ((idealSheafPullback D.i), ((modulePullback D.i).obj F')) ⟶
              ((idealSheafPullback D.i), ((modulePullback D.i).obj G')))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map
          (((𝟙 (idealSheafPullback D.i)), φ) :
            ((idealSheafPullback D.i), ((modulePullback D.i).obj F')) ⟶
            ((idealSheafPullback D.i), ((modulePullback D.i).obj G')))) ≫
        (firstOrderExtensionAction D.i ((modulePullback D.i).obj G')
          (idealTensor D ((modulePullback D.i).obj G')) hi
          ((flatLiftSelf G' hG').kernelExtension hi hs)).val := by
  rw [FlatLift.kernelExtension_action hi hs (flatLiftSelf F' hF'),
    FlatLift.kernelExtension_action hi hs (flatLiftSelf G' hG')]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-! ### The obstruction class -/

section Obstruction

variable [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing D.X))]

omit [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X))] in
/-- Composing a degree one `Ext` class with the shift of an isomorphism of its target does not
change whether it vanishes: the isomorphism is a monomorphism. -/
theorem zExt_comp_shift_mapIso_eq_zero_iff
    {B B' : SheafOfModules.{u} (structureSheafRing D.X)}
    (A : SheafOfModules.{u} (structureSheafRing D.X)) (e : B ≅ B')
    (o : CategoryTheory.Abelian.zExt A B 1) :
    o ≫ ((shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X)))
            (1 : ℤ)).mapIso
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing D.X)) 0).mapIso e)).hom = 0 ↔ o = 0 := by
  simpa only [zero_comp] using
    cancel_mono (f := ((shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X)))
        (1 : ℤ)).mapIso
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing D.X)) 0).mapIso e)).hom) (g := o) (h := 0)

-- The coefficient modules are named at the tensor product's `.obj`-applied spelling and the
-- map of the pair at the uncurried one; reconciling them needs `Functor.uncurry` and nothing
-- below it, so the tensor product itself is kept folded here.
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The class of **Stacks 08L6**, with its vanishing criterion, for the two kernel extensions of
**Stacks 08LM** attached to `ℱ'` and `𝒢'` and the pair `(φ, 1 ⊗ φ)`. It lives in
`Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} 𝒢)`, which **Stacks 08LI** identifies with the source's group. -/
noncomputable abbrev kernelExtensionObstruction (hi : IsFirstOrderThickening D.i)
    (hs : D.IsStrict) (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F')
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G') :=
  mapLiftingObstruction D.i hi ((modulePullback D.i).obj F')
    (idealTensor D ((modulePullback D.i).obj F')) ((modulePullback D.i).obj G')
    (idealTensor D ((modulePullback D.i).obj G'))
    ((flatLiftSelf F' hF').kernelExtension hi hs)
    ((flatLiftSelf G' hG').kernelExtension hi hs) φ
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map
        (((𝟙 (idealSheafPullback D.i)), φ) :
          ((idealSheafPullback D.i), ((modulePullback D.i).obj F')) ⟶
          ((idealSheafPullback D.i), ((modulePullback D.i).obj G')))))
    (kernelExtension_action_compat hi hs F' G' hF' hG' φ)

/-- The identification of **Stacks 08LI** carrying `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} 𝒢)` into the
source's `Ext¹_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)`, read in the derived category after the shift. -/
noncomputable abbrev coefficientShiftIso (hs : D.IsStrict)
    (G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G') :=
  (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X))) (1 : ℤ)).mapIso
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing D.X)) 0).mapIso
      (idealTensorIsoRestrictionTensorBaseIdeal hs G' hG'))

/-- **Stacks Project, Tag 08LL.** The obstruction class
`o(φ) ∈ Ext¹_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)` to lifting an `𝒪_X`-linear `φ : ℱ ⟶ 𝒢` between the
restrictions of two `𝒪_{X'}`-modules flat over `S'`, across a strict morphism of thickenings
whose upper arrow is a first order thickening.

It is the class of **Stacks 08L6** for the two kernel extensions of **Stacks 08LM** and the
pair `(φ, 1 ⊗ φ)`, carried into the source's group along the identification
`idealTensorIsoRestrictionTensorBaseIdeal` of **Stacks 08LI**. Its vanishing criterion is
`AlgebraicGeometry.RingedSpaceThickening.mapLiftObstruction_eq_zero_iff`. -/
@[stacks 08LL "the obstruction class"]
noncomputable def mapLiftObstruction (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F')
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G') :
    CategoryTheory.Abelian.zExt ((modulePullback D.i).obj F')
      (restrictionTensorBaseIdeal D G') 1 :=
  (kernelExtensionObstruction hi hs F' G' hF' hG' φ).val ≫
    (coefficientShiftIso hs G' hG').hom

/-- **Stacks Project, Tag 08LL.** The vanishing of the obstruction class `o(φ)` is necessary and
sufficient for `φ` to lift to an `𝒪_{X'}`-linear map `φ' : ℱ' ⟶ 𝒢'`, that is one with
`i^* φ' = φ`. -/
@[stacks 08LL "the vanishing criterion"]
theorem mapLiftObstruction_eq_zero_iff (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F')
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G') :
    mapLiftObstruction hi hs F' G' hF' hG' φ = 0 ↔ Nonempty (MapLift D.i F' G' φ) := by
  refine Iff.trans
    (zExt_comp_shift_mapIso_eq_zero_iff ((modulePullback D.i).obj F')
      (idealTensorIsoRestrictionTensorBaseIdeal hs G' hG')
      (kernelExtensionObstruction hi hs F' G' hF' hG' φ).val)
    ((kernelExtensionObstruction hi hs F' G' hF' hG' φ).property.trans ?_)
  constructor
  · rintro ⟨φ', _, hquot⟩
    exact ⟨⟨φ', mapLift_of_kernelExtension_g_comp hi hs F' G' hF' hG' φ φ' hquot⟩⟩
  · rintro ⟨⟨φ', hφ'⟩⟩
    exact ⟨φ', kernelExtension_f_comp_of_mapLift hi hs F' G' hF' hG' φ φ' hφ',
      kernelExtension_g_comp_of_mapLift hi hs F' G' hF' hG' φ φ' hφ'⟩

/-- **Stacks Project, Tag 08LL.** Let `(f, f')` be a morphism of thickenings of ringed spaces
whose upper arrow `i : X ⟶ X'` is a first order thickening, let `ℱ'` and `𝒢'` be
`𝒪_{X'}`-modules, put `ℱ = i^* ℱ'` and `𝒢 = i^* 𝒢'`, and let `φ : ℱ ⟶ 𝒢` be `𝒪_X`-linear.
Assume `ℱ'` and `𝒢'` are flat over `S'` and that `(f, f')` is strict. Then there exists

    o(φ) ∈ Ext¹_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)

whose vanishing is a necessary and sufficient condition for the existence of an `𝒪_{X'}`-linear
map `φ' : ℱ' ⟶ 𝒢'` with `i^* φ' = φ`.

The source asserts existence of the class, not uniqueness, and that is what is stated here; the
class itself is `AlgebraicGeometry.RingedSpaceThickening.mapLiftObstruction` and its criterion
`AlgebraicGeometry.RingedSpaceThickening.mapLiftObstruction_eq_zero_iff`. -/
@[stacks 08LL]
theorem exists_mapLiftObstruction (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F')
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G') :
    ∃ o : CategoryTheory.Abelian.zExt ((modulePullback D.i).obj F')
        (restrictionTensorBaseIdeal D G') 1,
      (o = 0 ↔ Nonempty (MapLift D.i F' G' φ)) :=
  ⟨mapLiftObstruction hi hs F' G' hF' hG' φ,
    mapLiftObstruction_eq_zero_iff hi hs F' G' hF' hG' φ⟩

end Obstruction

end AlgebraicGeometry.RingedSpaceThickening

end

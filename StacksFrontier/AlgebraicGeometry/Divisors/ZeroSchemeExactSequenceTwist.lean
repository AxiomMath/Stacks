module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact
import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisted exact sequence of a regular section

Let `L` be an invertible module on a scheme `X`, let `s` be a regular global section of `L`
([Stacks, Tag 01WY]) and let `i : Z(s) ⟶ X` be the inclusion of its zero scheme
([Stacks, Tag 02OQ]). For an invertible module `M` on `X`, tensoring the sequence of
[Stacks, Tag 0C6K] with `M` gives the short exact sequence

`0 ⟶ M ⟶ M ⊗ L ⟶ i_* i^* (M ⊗ L) ⟶ 0`,

whose first map is multiplication by `s` in the second factor and whose second map is the unit
of the pullback–pushforward adjunction. This is the twisted form of
`AlgebraicGeometry.shortExact_zeroScheme_of_isRegularSection`, and it is what computes the
cohomology of a twist by an effective Cartier divisor.

## Main results

* `AlgebraicGeometry.shortExact_zeroScheme_twist_of_isRegularSection`: **the twisted sequence
  is short exact**, in the shape of the untwisted statement.
* `AlgebraicGeometry.exists_cokernelIso_unit_zeroScheme_twist`: the unit realizes
  `i_* i^* (M ⊗ L)` as the cokernel of multiplication by `s`, compatibly with the cokernel
  projection. No regularity hypothesis is needed for this.
* `AlgebraicGeometry.tensorSection_comp_unit_zeroScheme_eq_zero`: the composite of the two maps
  of the twisted sequence vanishes.
* `AlgebraicGeometry.isEquivalence_tensorLeft`: tensoring by an invertible module is an
  equivalence, [Stacks, Tag 01CS] for the tensor product sheaf on a scheme.
* `AlgebraicGeometry.pullback_whiskerLeft_eq_zero`: pullback kills a morphism tensored with an
  invertible module as soon as it kills the morphism.
* `AlgebraicGeometry.pullback_eq_zero_of_comp_unit_eq_zero` and
  `AlgebraicGeometry.comp_unit_eq_zero_of_pullback_eq_zero`: for a closed immersion `i`, a
  morphism is killed by `i^*` exactly when its composite with the unit of `i^* ⊣ i_*` vanishes.
* `AlgebraicGeometry.essImage_tensor_pushforward`: a direct image along a morphism of schemes
  stays a direct image after tensoring with an invertible module.

The same three statements hold with the invertibility of `M` dropped — `M` an arbitrary
`𝒪_X`-module and only `L` invertible — which is the form [Stacks, Tag 08A0] needs, its `M` being
`ℱ(-1)` for a coherent `ℱ`:

* `AlgebraicGeometry.tensorSection_comp_unit_zeroScheme_eq_zero'`,
  `AlgebraicGeometry.isIso_unit_app_cokernel_tensorSection'` and
  `AlgebraicGeometry.exists_cokernelIso_unit_zeroScheme_twist'`;
* `AlgebraicGeometry.pullback_whiskerLeft_eq_zero'` and
  `AlgebraicGeometry.essImage_tensor_pushforward'`, the two inputs in their general form;
* `AlgebraicGeometry.preservesZeroMorphisms_tensorLeft` and
  `AlgebraicGeometry.preservesFiniteColimits_tensorLeft`: **tensoring by an arbitrary module is
  right exact**, [Stacks, Tag 05NB] for the tensor product sheaf on a scheme.

## Implementation notes

**The shape of the argument.** The twisted sequence is *not* obtained by transporting the
untwisted short exact sequence through the equivalence `M ⊗ -`: that would produce
`M ⊗ i_* i^* L` as its third term, and identifying that term with `i_* i^* (M ⊗ L)`
*compatibly with the unit* is extra work. Instead the cokernel criterion
`AlgebraicGeometry.exists_cokernelIso_of_isIso_unit_app` is applied directly to the twisted
map, and it produces the comparison with `i_* i^* (M ⊗ L)` together with its compatibility with
the unit. That criterion asks for two things, and the equivalence `M ⊗ -` is used for both:

* the composite of the twisted map with the unit vanishes. Equivalently, by the adjunction, the
  twisted map is killed by `i^*`; and by [Stacks, Tag 01CD], which is unconditional here
  (`Stacks.RingedSpace.comparisonNatTrans_app_isIso`), `i^*(M ⊗ -)` is `i^*M ⊗ i^*(-)`, while
  tensoring by the invertible `i^*M` ([Stacks, Tag 0B8L]) is an equivalence and hence additive.
  So the twisted map is killed because the untwisted one is.
* the unit is an isomorphism at the cokernel of the twisted map. That cokernel is
  `M ⊗ i_* i^* L`, because `M ⊗ -` is an equivalence and the untwisted cokernel is `i_* i^* L`
  ([Stacks, Tag 0C6K]); and `M ⊗ i_* i^* L` is a direct image along `i` by the projection
  formula for an invertible factor (`Stacks.ProjectionFormula.projectionFormulaIso`,
  [Stacks, Tag 0FZE] in that case), so the essential-image half of [Stacks, Tag 08KS] applies.
  Only an isomorphism of *objects* is needed here, which is why the projection formula is used
  with no compatibility clause.

**Where invertibility of `M` is actually used, and what replaces it.** Only two consequences of
the equivalence `M ⊗ -` enter: that it sends the zero morphism to the zero morphism, and that it
carries the untwisted cokernel to the twisted one. Both are consequences of right exactness of
`M ⊗ -`, which holds for an arbitrary `M` by [Stacks, Tag 05NB]
(`Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafRight`, whose
endofunctor is the monoidal `MonoidalCategory.tensorLeft` of this file on the nose). The third
use, the projection formula, is replaced by
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`, which is general in both
module arguments at the cost of requiring `i` to be a closed immersion — which the inclusion of a
zero scheme is. Invertibility of `L` is *not* removable: it is what makes the untwisted sequence
of [Stacks, Tag 0C6K] exist.

**Which monoidal structure.** `Stacks.SheafOfModules.sheafTensorMonoidal`, whose
tensor product is the tensor product sheaf of [Stacks, Tag 01CA] on the nose: its data are those
of `Stacks.SheafOfModules.sheafTensorStruct`, so that `A ⊗ B` is computed by
`Stacks.SheafOfModules.Tensor.sheafTensor`, `M ◁ g` is `Stacks.SheafOfModules.sheafifyWhiskerLeft`
and `ρ_ M` is `Stacks.SheafOfModules.Invertible.tensorProductRightUnitor`, all by `rfl`. It is
also the tensor product that the pullback comparison of Tag 01CD and the projection formula are
stated for, so no comparison of tensor products intervenes below. The structure has the sheaf of
rings and its sheaf condition as explicit arguments, so `attribute [local instance]` does not fire
on it; it is re-exported here at a scheme as the local instance
`AlgebraicGeometry.schemeModulesMonoidal`, as `Stacks.Divisors.schemeModulesMonoidal` does for
the canonical section pairing.

**Spelling.** The scheme-level `AlgebraicGeometry.Scheme.Modules.pushforward` and the
ringed-space-level `Stacks.RingedSpace.pushforwardFunctor` the projection formula and Tag 01CD
are stated for are equal by `rfl`, as are the two pullbacks and the two tensor products — but
not *syntactically*, so `rw` cannot cross between them. Every step that does so is a `have`
whose type is written in the scheme-level spelling and whose proof is the ringed-space-level
lemma, which only has to be checked up to definitional equality. No transparency option is
involved.

**Why the tensor equivalence is applied as a term.**
`AlgebraicGeometry.SheafOfModules.tensorLeftFunctor_isEquivalence` is an instance, but instance
search does not find it at a scheme, because the sheaf-condition argument of the tensor functor
then has to be unified under the `AlgebraicGeometry.Scheme.ringCatSheaf` spelling. It is
therefore applied as a term, once, in `AlgebraicGeometry.isEquivalence_tensorLeft`.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules (sheafTensorMonoidal sheafTensorSymmetric)

/-- The tensor product sheaf of [Stacks, Tag 01CA] as a monoidal structure on the
`𝒪_X`-modules of a scheme. -/
local instance schemeModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

/-- The symmetry of [Stacks, Tag 01CU] on the `𝒪_X`-modules of a scheme. -/
local instance schemeModulesSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  sheafTensorSymmetric X.sheaf.obj X.ringCatSheaf.property

/-- A morphism that is an isomorphism is a monomorphism. The hypothesis is an argument rather
than an instance, so that it can be supplied up to definitional equality. -/
private theorem mono_of_isIso' {C : Type*} [Category C] {A B : C} (f : A ⟶ B) (hf : IsIso f) :
    Mono f := by
  have := hf
  infer_instance

/-- A functor preserving monomorphisms carries a monomorphism to one. The hypothesis is an
argument rather than an instance, so that it can be supplied up to definitional equality. -/
private theorem mono_map' {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    [F.PreservesMonomorphisms] {A B : C} (f : A ⟶ B) (hf : Mono f) : Mono (F.map f) := by
  have := hf
  infer_instance

/-- A composite of two monomorphisms is a monomorphism. Both hypotheses are arguments rather
than instances, so that they can be supplied up to definitional equality. -/
private theorem mono_comp' {C : Type*} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) := by
  have := hf
  have := hg
  infer_instance

/-- **Tensoring by an invertible module is an equivalence** of the category of `𝒪_X`-modules.
This is [Stacks, Tag 01CS] for the tensor product sheaf. -/
theorem isEquivalence_tensorLeft (X : Scheme.{u}) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    (tensorLeft M).IsEquivalence :=
  SheafOfModules.tensorLeftFunctor_isEquivalence X.sheaf.obj X.ringCatSheaf.property M

/-- Pullback kills `M ◁ g` when it kills `g`, as soon as tensoring by `h^* M` preserves zero
morphisms. -/
private theorem pullback_whiskerLeft_eq_zero_of_preservesZeroMorphisms {X Z : Scheme.{u}}
    (h : Z ⟶ X) (M : X.Modules)
    [(tensorLeft ((Scheme.Modules.pullback h).obj M)).PreservesZeroMorphisms]
    {A B : X.Modules} (g : A ⟶ B) (hg : (Scheme.Modules.pullback h).map g = 0) :
    (Scheme.Modules.pullback h).map (M ◁ g) = 0 := by
  have hzero : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩))).map
      (((Scheme.Modules.pullback h).map (𝟙 M), (Scheme.Modules.pullback h).map g) :
        ((Scheme.Modules.pullback h).obj M, (Scheme.Modules.pullback h).obj A) ⟶
          ((Scheme.Modules.pullback h).obj M, (Scheme.Modules.pullback h).obj B)) = 0 := by
    rw [hg, CategoryTheory.Functor.map_id]
    exact (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ _ _).trans
      (CategoryTheory.Functor.map_zero (tensorLeft ((Scheme.Modules.pullback h).obj M))
        ((Scheme.Modules.pullback h).obj A) ((Scheme.Modules.pullback h).obj B))
  have hwhisker : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).map
        (((𝟙 M, g)) : ((M, A) : X.Modules × X.Modules) ⟶ ((M, B) : X.Modules × X.Modules)) =
      M ◁ g :=
    Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ (𝟙 M) g
  have hnat : (Scheme.Modules.pullback h).map (M ◁ g) ≫
        (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
          ((M, B) : X.Modules × X.Modules) =
      (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
          ((M, A) : X.Modules × X.Modules) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩))).map
          (((Scheme.Modules.pullback h).map (𝟙 M), (Scheme.Modules.pullback h).map g) :
            ((Scheme.Modules.pullback h).obj M, (Scheme.Modules.pullback h).obj A) ⟶
              ((Scheme.Modules.pullback h).obj M, (Scheme.Modules.pullback h).obj B)) := by
    rw [← hwhisker]
    exact (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).naturality
      (X := ((M, A) : X.Modules × X.Modules)) (Y := ((M, B) : X.Modules × X.Modules)) (𝟙 M, g)
  have hiso : IsIso ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
      ((M, B) : X.Modules × X.Modules)) :=
    Stacks.RingedSpace.comparisonNatTrans_app_isIso h.toLRSHom.toShHom
      ((M, B) : X.Modules × X.Modules)
  exact (mono_of_isIso' _ hiso).right_cancellation _ _
    ((hnat.trans (((congrArg (fun k =>
      (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
        ((M, A) : X.Modules × X.Modules) ≫ k) hzero).trans comp_zero))).trans zero_comp.symm)

/-- **Tensoring with an invertible module preserves vanishing under pullback.** If `h^* g = 0`
then `h^*(M ⊗ g) = 0`: by [Stacks, Tag 01CD] the comparison `h^*(M ⊗ -) ≅ h^*M ⊗ h^*(-)` is
natural, and tensoring by the invertible `h^*M` ([Stacks, Tag 0B8L]) is an equivalence, hence
kills the zero morphism. -/
theorem pullback_whiskerLeft_eq_zero {X Z : Scheme.{u}} (h : Z ⟶ X) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] {A B : X.Modules}
    (g : A ⟶ B) (hg : (Scheme.Modules.pullback h).map g = 0) :
    (Scheme.Modules.pullback h).map (M ◁ g) = 0 := by
  have : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property
      ((Scheme.Modules.pullback h).obj M) :=
    @Stacks.InvertiblePullback.isInvertible_pullback' _ _ h.toLRSHom.toShHom M ‹_›
  have := isEquivalence_tensorLeft Z ((Scheme.Modules.pullback h).obj M)
  exact pullback_whiskerLeft_eq_zero_of_preservesZeroMorphisms h M g hg

/-- **A morphism killed by the unit of `i^* ⊣ i_*` is killed by `i^*`**, for `i` a closed
immersion: the unit is an epimorphism and `i_*` is faithful ([Stacks, Tag 08KS]). -/
theorem pullback_eq_zero_of_comp_unit_eq_zero {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {A B : X.Modules} (g : A ⟶ B)
    (hg : g ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B = 0) :
    (Scheme.Modules.pullback i).map g = 0 := by
  have hnat : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫
      (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map g) =
      g ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B :=
    Adjunction.unit_naturality _ g
  have h1 : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫
      (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map g) =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫ 0 := by
    rw [hnat, hg, comp_zero]
  have := Stacks.ClosedImmersion.epi_unit_app i A
  have := Stacks.ClosedImmersion.faithful_pushforward i
  exact ((Scheme.Modules.pushforward i).map_eq_zero_iff).mp ((cancel_epi _).mp h1)

/-- **A morphism killed by `i^*` is killed by the unit of `i^* ⊣ i_*`**: the composite with the
unit is the adjoint transpose of `i^*` of the morphism. -/
theorem comp_unit_eq_zero_of_pullback_eq_zero {X Z : Scheme.{u}} (i : Z ⟶ X) {A B : X.Modules}
    (g : A ⟶ B) (hg : (Scheme.Modules.pullback i).map g = 0) :
    g ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B = 0 := by
  have hnat : g ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map g) :=
    (Adjunction.unit_naturality _ g).symm
  rw [hnat, hg, CategoryTheory.Functor.map_zero, comp_zero]

/-- **A direct image tensored with an invertible module is again a direct image.** This is the
projection formula [Stacks, Tag 0FZE] for an invertible factor, which identifies `i_* N ⊗ M`
with `i_*(N ⊗ i^* M)`, preceded by the symmetry of the tensor product. -/
theorem essImage_tensor_pushforward {X Z : Scheme.{u}} (i : Z ⟶ X) (N : Z.Modules)
    (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    (Scheme.Modules.pushforward i).essImage (M ⊗ (Scheme.Modules.pushforward i).obj N) := by
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ ‹_›
  have pf : ((Scheme.Modules.pushforward i).obj N ⊗ M) ≅
      (Scheme.Modules.pushforward i).obj (N ⊗ (Scheme.Modules.pullback i).obj M) :=
    Stacks.ProjectionFormula.projectionFormulaIso i.toLRSHom.toShHom N M
  exact ⟨_, ⟨(β_ M ((Scheme.Modules.pushforward i).obj N) ≪≫ pf).symm⟩⟩

/-- Multiplication by a section in the second factor of `M ⊗ L`, followed by the unit of the
zero scheme adjunction, vanishes as soon as pullback kills `M ◁ g` whenever it kills `g`. -/
private theorem tensorSection_comp_unit_zeroScheme_eq_zero_of_whisker (X : Scheme.{u})
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (M : X.Modules)
    (hM : ∀ {A B : X.Modules} (g : A ⟶ B),
      (Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).map g = 0 →
        (Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).map (M ◁ g) = 0) :
    ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app (M ⊗ L) = 0 := by
  refine comp_unit_eq_zero_of_pullback_eq_zero _ _ ?_
  have hw := hM _ (pullback_eq_zero_of_comp_unit_eq_zero _ _
    (section_comp_unit_zeroScheme_eq_zero X L s))
  refine (CategoryTheory.Functor.map_comp _ (ρ_ M).inv (M ◁ L.unitHomEquiv.symm s)).trans ?_
  exact (congrArg (fun k => (Scheme.Modules.pullback
    (zeroScheme X L (s.eval (op ⊤))).subschemeι).map (ρ_ M).inv ≫ k) hw).trans comp_zero

/-- The unit is an isomorphism at the cokernel of multiplication by the section on `M ⊗ L`, when
`M ⊗ -` is right exact and `M ⊗ i_* i^* L` is a direct image along `i`. -/
private theorem isIso_unit_app_cokernel_tensorSection_of_essImage (X : Scheme.{u})
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (M : X.Modules) [(tensorLeft M).PreservesZeroMorphisms]
    [PreservesFiniteColimits (tensorLeft M)]
    (hess : (Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).essImage
      (M ⊗ (Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L))) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app
      (cokernel ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s))) := by
  obtain ⟨e, -⟩ := exists_cokernelIso_unit_zeroScheme X L s
  have ecok : cokernel ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≅
      M ⊗ (Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L) :=
    cokernelEpiComp (ρ_ M).inv (M ◁ L.unitHomEquiv.symm s) ≪≫
      (PreservesCokernel.iso (tensorLeft M) (L.unitHomEquiv.symm s)).symm ≪≫
        (tensorLeft M).mapIso e
  have := Stacks.ClosedImmersion.full_pushforward
    (zeroScheme X L (s.eval (op ⊤))).subschemeι
  have := Stacks.ClosedImmersion.faithful_pushforward
    (zeroScheme X L (s.eval (op ⊤))).subschemeι
  obtain ⟨N, ⟨eN⟩⟩ := hess
  exact (Adjunction.isIso_unit_app_iff_mem_essImage _).mpr ⟨N, ⟨eN ≪≫ ecok.symm⟩⟩

/-- **Multiplication by a global section in the second factor of `M ⊗ L`, followed by
restriction to the zero scheme of the section, is zero.** This is the vanishing of the composite
in the twisted sequence; the untwisted vanishing is
`AlgebraicGeometry.section_comp_unit_zeroScheme_eq_zero`. -/
theorem tensorSection_comp_unit_zeroScheme_eq_zero (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app (M ⊗ L) = 0 := by
  refine tensorSection_comp_unit_zeroScheme_eq_zero_of_whisker X L s M ?_
  exact fun g hg => pullback_whiskerLeft_eq_zero _ M g hg

/-- **The unit is an isomorphism at the cokernel of multiplication by the section on `M ⊗ L`.**
The cokernel is `M ⊗ i_* i^* L`, since tensoring by `M` is an equivalence and the untwisted
cokernel is `i_* i^* L` ([Stacks, Tag 0C6K]); that is a direct image along `i`, so the
essential-image half of [Stacks, Tag 08KS] applies. -/
theorem isIso_unit_app_cokernel_tensorSection (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app
      (cokernel ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s))) := by
  have := isEquivalence_tensorLeft X M
  exact isIso_unit_app_cokernel_tensorSection_of_essImage X L s M
    (essImage_tensor_pushforward _ _ M)

/-- **The twisted form of [Stacks, Tag 0C6K], first assertion.** For invertible modules `L` and
`M` on a scheme `X` and a global section `s` of `L`, the unit of the pullback–pushforward
adjunction along the inclusion `i` of the zero scheme `Z(s)` realizes `i_* i^* (M ⊗ L)` as the
cokernel of multiplication by `s` in the second factor of `M ⊗ L`.

No regularity hypothesis on `s` is needed. -/
theorem exists_cokernelIso_unit_zeroScheme_twist (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    ∃ e : cokernel ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≅
        (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj (M ⊗ L)),
      cokernel.π ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (M ⊗ L) := by
  dsimp only
  have := isIso_unit_app_cokernel_tensorSection X L s M
  exact exists_cokernelIso_of_isIso_unit_app
    (Scheme.Modules.pullbackPushforwardAdjunction (zeroScheme X L (s.eval (op ⊤))).subschemeι) _
    (tensorSection_comp_unit_zeroScheme_eq_zero X L s M)

/-- **The twisted form of [Stacks, Tag 0C6K], second assertion.** Let `L` be an invertible
module on a scheme `X` with a regular global section `s` ([Stacks, Tag 01WY]), let `i` be the
inclusion of the zero scheme of `s` and let `M` be an invertible module on `X`. Then

`0 ⟶ M ⟶ M ⊗ L ⟶ i_* i^* (M ⊗ L) ⟶ 0`

is short exact, the first map being multiplication by `s` in the second factor and the second
the unit of `i^* ⊣ i_*`. -/
theorem shortExact_zeroScheme_twist_of_isRegularSection (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    let f : M ⟶ M ⊗ L := (ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s
    let g : M ⊗ L ⟶ (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj (M ⊗ L)) :=
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (M ⊗ L)
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by
  dsimp only
  have := isEquivalence_tensorLeft X M
  have hmono : Mono ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) :=
    mono_comp' _ _ (mono_of_isIso' _ inferInstance)
      (mono_map' (tensorLeft M) (L.unitHomEquiv.symm s) hs)
  obtain ⟨e, he⟩ := exists_cokernelIso_unit_zeroScheme_twist X L s M
  exact ShortComplex.shortExact_of_cokernelIso _ hmono e he

/-! ### The twisted sequence for an arbitrary module factor -/

/-- **Tensoring by an arbitrary `𝒪_X`-module preserves zero morphisms.** No invertibility is
needed: the tensor product sheaf is the sheafification of the objectwise tensor product, which
is additive in each variable. -/
theorem preservesZeroMorphisms_tensorLeft (X : Scheme.{u}) (M : X.Modules) :
    (tensorLeft M).PreservesZeroMorphisms :=
  Stacks.SheafOfModules.TensorLocalProperties.preservesZeroMorphisms_tensorSheafRight
    (Opens.grothendieckTopology X) X.sheaf M

/-- **Tensoring by an arbitrary `𝒪_X`-module is right exact**, that is, preserves finite
colimits. This is [Stacks, Tag 05NB] for the tensor product sheaf of [Stacks, Tag 01CA] on a
scheme, and it is what replaces the equivalence `M ⊗ -` when `M` is not invertible. -/
@[sga "4 IV 12.9" "special case"]
theorem preservesFiniteColimits_tensorLeft (X : Scheme.{u}) (M : X.Modules) :
    PreservesFiniteColimits (tensorLeft M) := by
  have h : PreservesColimitsOfSize.{u, u} (tensorLeft M) :=
    Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafRight
      (Opens.grothendieckTopology X) X.sheaf M
  have h0 : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Tensoring with an arbitrary module preserves vanishing under pullback.** If `h^* g = 0`
then `h^*(M ⊗ g) = 0`: the comparison `h^*(M ⊗ -) ≅ h^*M ⊗ h^*(-)` of [Stacks, Tag 01CD] is
natural and an isomorphism unconditionally, and `h^*M ⊗ -` kills the zero morphism. This is
`AlgebraicGeometry.pullback_whiskerLeft_eq_zero` with the invertibility of `M` dropped. -/
theorem pullback_whiskerLeft_eq_zero' {X Z : Scheme.{u}} (h : Z ⟶ X) (M : X.Modules)
    {A B : X.Modules} (g : A ⟶ B) (hg : (Scheme.Modules.pullback h).map g = 0) :
    (Scheme.Modules.pullback h).map (M ◁ g) = 0 := by
  have := preservesZeroMorphisms_tensorLeft Z ((Scheme.Modules.pullback h).obj M)
  exact pullback_whiskerLeft_eq_zero_of_preservesZeroMorphisms h M g hg

/-- **A direct image along a closed immersion tensored with an arbitrary module is again a
direct image.** This is the projection formula [Stacks, Tag 0FZE] at a closed immersion, which
needs neither quasi-coherence nor invertibility of either factor, preceded by the symmetry of
the tensor product. -/
theorem essImage_tensor_pushforward' {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (N : Z.Modules) (M : X.Modules) :
    (Scheme.Modules.pushforward i).essImage (M ⊗ (Scheme.Modules.pushforward i).obj N) := by
  have pf : ((Scheme.Modules.pushforward i).obj N ⊗ M) ≅
      (Scheme.Modules.pushforward i).obj (N ⊗ (Scheme.Modules.pullback i).obj M) :=
    Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i N M
  exact ⟨_, ⟨(β_ M ((Scheme.Modules.pushforward i).obj N) ≪≫ pf).symm⟩⟩

/-- **Multiplication by a global section in the second factor of `M ⊗ L`, followed by
restriction to the zero scheme of the section, is zero**, for an *arbitrary* module `M`. This is
`AlgebraicGeometry.tensorSection_comp_unit_zeroScheme_eq_zero` with the invertibility of `M`
dropped. -/
theorem tensorSection_comp_unit_zeroScheme_eq_zero' (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (M : X.Modules) :
    ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app (M ⊗ L) = 0 := by
  exact tensorSection_comp_unit_zeroScheme_eq_zero_of_whisker X L s M
    fun g hg => pullback_whiskerLeft_eq_zero' _ M g hg

/-- **The unit is an isomorphism at the cokernel of multiplication by the section on `M ⊗ L`**,
for an *arbitrary* module `M`. The cokernel is `M ⊗ i_* i^* L`, because `M ⊗ -` is right exact
and the untwisted cokernel is `i_* i^* L` ([Stacks, Tag 0C6K]); that is a direct image along the
closed immersion `i`, so the essential-image half of [Stacks, Tag 08KS] applies. -/
theorem isIso_unit_app_cokernel_tensorSection' (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (M : X.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app
      (cokernel ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s))) := by
  have := preservesZeroMorphisms_tensorLeft X M
  have := preservesFiniteColimits_tensorLeft X M
  exact isIso_unit_app_cokernel_tensorSection_of_essImage X L s M
    (essImage_tensor_pushforward' _ _ M)

/-- **The twisted form of [Stacks, Tag 0C6K], first assertion, for an arbitrary module `M`.**
For an invertible `L` on a scheme `X` with a global section `s` and *any* `𝒪_X`-module `M`, the
unit of the pullback–pushforward adjunction along the inclusion `i` of the zero scheme `Z(s)`
realizes `i_* i^* (M ⊗ L)` as the cokernel of multiplication by `s` in the second factor of
`M ⊗ L`. No regularity hypothesis on `s` is needed. -/
theorem exists_cokernelIso_unit_zeroScheme_twist' (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (M : X.Modules) :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    ∃ e : cokernel ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≅
        (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj (M ⊗ L)),
      cokernel.π ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (M ⊗ L) := by
  dsimp only
  have := isIso_unit_app_cokernel_tensorSection' X L s M
  exact exists_cokernelIso_of_isIso_unit_app
    (Scheme.Modules.pullbackPushforwardAdjunction (zeroScheme X L (s.eval (op ⊤))).subschemeι) _
    (tensorSection_comp_unit_zeroScheme_eq_zero' X L s M)

end AlgebraicGeometry

end

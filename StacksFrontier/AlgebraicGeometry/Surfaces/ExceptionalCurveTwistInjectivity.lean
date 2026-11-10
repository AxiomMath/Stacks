module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Sections
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionPairing
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorCanonicalSection
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve

/-!
# Twisting by an exceptional curve of non-positive degree is injective on `H¹`

Let `E ⊆ X` be an exceptional curve of the first kind on a scheme `X`, let `ℒ` be an invertible
`𝒪_X`-module, and let `n` be the degree of `ℒ|_E` on `𝐏¹`. If `n ≤ 0` then multiplication by the
canonical section `1_E` induces an injection

`H¹(X, ℒ) ↪ H¹(X, ℒ(E))`.

This is assertion (2) of [Stacks, Tag 0C2J].

## Main results

* `Stacks.Surfaces.mono_rightDerived_one_map_tensorCanonicalSection`: **assertion (2) of Tag
  0C2J.**
* `Stacks.Surfaces.isZero_sections_tensorPushforwardUnit`: the cohomological input, that
  `Γ(X, 𝓜 ⊗ i_*𝒪_E)` vanishes as soon as `𝓜` restricts to a negative twist on `𝐏¹`.
* `Stacks.Surfaces.mono_rightDerived_one_map_map_tensorLeft`: the long-exact-sequence step, that
  vanishing of `Γ(X, 𝓜 ⊗ X₃)` for a short exact sequence makes `H¹` of `𝓜 ⊗ X₁ ⟶ 𝓜 ⊗ X₂` a
  monomorphism.

## The argument

Tensor the ideal sequence `0 ⟶ ℐ_E ⟶ 𝒪_X ⟶ i_*𝒪_E ⟶ 0` of [Stacks, Tag 01WX] by
`𝓜 = ℒ ⊗ 𝒪_X(E)`. Tensoring by an invertible module is an equivalence, so the result is again
short exact, and its first map becomes the map of the conclusion once the first term is
identified: `𝓜 ⊗ ℐ_E = ℒ ⊗ (𝒪_X(E) ⊗ ℐ_E) ≅ ℒ` by the evaluation pairing, and under that
identification the map is multiplication by `1_E`. That last compatibility is the content of
`Stacks.Divisors.tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor`; without it the
conclusion would be about a map only isomorphic to the canonical one.

The third term is `𝓜 ⊗ i_*𝒪_E ≅ i_*(i^*𝓜)` by the projection formula for a closed immersion,
so its global sections are the global sections of `i^*𝓜` on `E`, which along the chosen
isomorphism `e : 𝐏¹ ≅ E` are the global sections of
`e^*i^*𝓜 ≅ (e^*i^*ℒ) ⊗ (e^*i^*𝒪_X(E)) ≅ 𝒪(n) ⊗ 𝒪(-1) ≅ 𝒪(n-1)`.
Here `e^*i^*𝒪_X(E) ≅ 𝒪(-1)` is the normal-sheaf clause of [Stacks, Tag 0B3P] composed with the
defining property of an exceptional curve of the first kind, and the twists multiply by
[Stacks, Tag 01MT]. Since `n ≤ 0` the degree `n - 1` is negative, so those sections vanish, and
the connecting morphism out of them is zero.

## Implementation notes

**Only assertion (2).** Assertion (1) of the tag needs the comparison
`H^q(X, i_*N) ≅ H^q(E, N)` for a closed immersion in positive degree; the library's form of
[Stacks, Tag 01XK] is stated over an affine base, so it does not apply to an arbitrary `X`.
Nothing of assertion (1) is claimed here.

**The degree hypothesis.** "`n` is the degree of `ℒ|_E` as an invertible module on `𝐏¹`" is
recorded as an isomorphism `e^*i^*ℒ ≅ 𝒪(n)`, which is what having degree `n` means for an
invertible module on the projective line and the form in which the source's proof uses it.

**Noetherianness is not assumed.** The source states the lemma for `X` Noetherian, but
assertion (2) needs nothing of it: the argument above is an exact sequence, the projection
formula and a vanishing statement on `𝐏¹`. The statement below is therefore a generalization of
the tag, not a weakening.

**The canonical module category and tensor functor.** Everything is stated over
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, and `H¹` is the first right derived functor of
`AlgebraicGeometry.moduleGlobalSections X`. The monomorphism statements use the native functor
`(Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj 𝓜`; the coherence statements use `◁`
for the same tensor product. Their maps are identified before applying `rightDerived 1`, so
the conversion does not unfold injective resolutions. The factor universes and the module
category of the monoidal structure are specified at these boundaries.

## References

* [Stacks Project, Tag 0C2J](https://stacks.math.columbia.edu/tag/0C2J)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.Divisors
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover twistMultiplicationIso)
open RingedSpaceModuleAdjunction (modulePullback modulePushforward)
open Stacks.SheafOfModules (sheafTensorMonoidal sheafTensorSymmetric)

universe u

namespace Stacks.Surfaces

attribute [local instance] HasDerivedCategory.standard MvPolynomial.gradedAlgebra

/-- The tensor product sheaf as the monoidal structure on `𝒪_X`-modules, at the spelling
`SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))` of that category. -/
noncomputable local instance schemeModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory (_root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) :=
  sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

/-- The symmetry of [Stacks, Tag 01CU], at the same spelling. -/
noncomputable local instance schemeModulesSymmetric (X : Scheme.{u}) :
    SymmetricCategory (_root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) :=
  sheafTensorSymmetric X.sheaf.obj X.ringCatSheaf.property

/-! ### The long exact sequence step -/

/-- **Vanishing of `Fⁿ(X₃)` makes `Fⁿ⁺¹(X₁) ⟶ Fⁿ⁺¹(X₂)` a monomorphism**, for a cohomological
δ-functor. This is the dual of `Stacks.AmpleCohomologicalCriterion.epi_map_g_of_isZero`, read off
`exact_δ₂`: the connecting morphism leaves a zero object, hence is zero. -/
theorem mono_map_f_of_isZero {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : DeltaFunctor A B) {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h : IsZero ((F.functor n).obj S.X₃)) : Mono ((F.functor (n + 1)).map S.f) :=
  (ShortComplex.exact_iff_mono _ (h.eq_of_src _ 0)).1 (F.exact_δ₂ hS n)

variable {X : Scheme.{u}}

/-- **`Γ(X, X₃) = 0` makes `H¹(X, X₁) ⟶ H¹(X, X₂)` a monomorphism** for a short exact sequence
of `𝒪_X`-modules. Degree zero of the long exact sequence is identified with global sections by
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`. -/
theorem mono_rightDerived_one_map_f
    {S : ShortComplex (_root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))} (hS : S.ShortExact)
    (h : IsZero ((moduleGlobalSections X).obj S.X₃)) :
    Mono (((moduleGlobalSections X).rightDerived 1).map S.f) :=
  mono_map_f_of_isZero (Stacks.AmpleCohomologicalCriterion.sectionsDeltaFunctor X ⊤) hS 0
    (h.of_iso ((Functor.rightDerivedZeroIsoSelf (moduleGlobalSections X)).app S.X₃))

/-- Tensoring on the left by `𝓜` lands on the monoidal tensor product: the two spellings of
`𝓜 ⊗ ℱ` are the same object. -/
theorem tensorLeft_obj_eq_tensorObj (M A : _root_.SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj M).obj A = M ⊗ A := rfl

/-- **The same after tensoring by an invertible module.** Tensoring a short exact sequence by an
invertible `𝒪_X`-module `𝓜` keeps it short exact, so vanishing of `Γ(X, 𝓜 ⊗ X₃)` makes
`H¹(X, 𝓜 ⊗ X₁) ⟶ H¹(X, 𝓜 ⊗ X₂)` a monomorphism.

The twisted sequence is the image of `S` under the native functor
`(Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj 𝓜`, rather than a separately assembled
short complex, so its morphisms agree before applying `rightDerived 1`. -/
theorem mono_rightDerived_one_map_map_tensorLeft (M : _root_.SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (S : ShortComplex (_root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))) (hS : S.ShortExact)
    (h : IsZero ((moduleGlobalSections X).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj M).obj S.X₃))) :
    letI : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj M).Additive :=
      Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive X.sheaf M
    Mono (((moduleGlobalSections X).rightDerived 1).map
      ((S.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj M)).f)) := by
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj M).Additive :=
    Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive X.sheaf M
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj M).IsEquivalence :=
    AlgebraicGeometry.SheafOfModules.tensorLeftFunctor_isEquivalence X.presheaf
      (structureSheafRing X.toRingedSpace).property M
  exact mono_rightDerived_one_map_f (X := X)
    (S := S.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj M))
    (hS.map_of_exact _) h

/-- **The ideal sequence `0 ⟶ ℐ_E ⟶ 𝒪_X ⟶ i_*𝒪_E ⟶ 0` of a closed subscheme**, named so that
the twisted sequence below has a stable spelling. -/
def idealShortComplex (E : X.IdealSheafData) :
    ShortComplex (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) :=
  ShortComplex.mk (idealSheafInclusion E)
    (_root_.SheafOfModules.unitToPushforwardObjUnit
      (RingedSpaceModuleAdjunction.structureSheafHom E.subschemeι.toLRSHom.toShHom))
    (kernel.condition (C := _root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) _)

/-- The ideal sequence of a closed subscheme is short exact, by
`Stacks.Cohomology.AmpleH1.shortExact_idealSheaf`. -/
theorem idealShortComplex_shortExact (E : X.IdealSheafData) :
    (idealShortComplex E).ShortExact :=
  Stacks.Cohomology.AmpleH1.shortExact_idealSheaf E.subschemeι

/-- **Transporting a monomorphism across two isomorphisms inside a functor image.** -/
private theorem mono_map_comp_of_isIso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A A' B B' : C} (u : A ⟶ A') (v : A' ⟶ B) (w : B ⟶ B')
    (hu : IsIso (F.map u)) (hv : Mono (F.map v)) (hw : IsIso (F.map w)) :
    Mono (F.map (u ≫ v ≫ w)) := by
  have := hu
  have := hv
  have := hw
  rw [F.map_comp, F.map_comp]
  exact mono_comp _ _

/-! ### Identifying the first term of the twisted ideal sequence -/

/-- The evaluation pairing `𝒪_X(E) ⊗ ℐ_E ≅ 𝒪_X` of an effective Cartier divisor, read at the
monoidal structure. -/
def evaluationPairingIso (E : X.IdealSheafData) [IsEffectiveCartierDivisor E] :
    MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
        (invertibleSheaf' E) (negativeTwist' E) ≅
      𝟙_ (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) :=
  haveI := isTensorInvertible_negativeTwist E
  Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' E)

/-- **`(ℒ ⊗ 𝒪_X(E)) ⊗ ℐ_E ≅ ℒ`**: the first term of the ideal sequence of `E` twisted by
`ℒ ⊗ 𝒪_X(E)` is `ℒ` itself, through the evaluation pairing of `Stacks.Divisors`. -/
def twistedIdealIso (E : X.IdealSheafData) [IsEffectiveCartierDivisor E]
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) :
    MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
        (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
          L (invertibleSheaf' E)) (negativeTwist' E) ≅ L :=
  α_ L (invertibleSheaf' E) (negativeTwist' E) ≪≫
    whiskerLeftIso L (evaluationPairingIso E) ≪≫ ρ_ L

/-- **Contracting `𝒪_X(E) ⊗ ℐ_E` against the ideal inclusion is the evaluation pairing followed
by multiplication by `1_E`.** This is
`Stacks.Divisors.tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor`, with its two tensor
operations named as the whiskering and the right unit constraint of the monoidal structure. -/
theorem whiskerLeft_idealSheafInclusion_comp_rightUnitor (E : X.IdealSheafData)
    [IsEffectiveCartierDivisor E] :
    MonoidalCategoryStruct.whiskerLeft (C := _root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
          (invertibleSheaf' E) (idealSheafInclusion E) ≫
        (MonoidalCategoryStruct.rightUnitor
          (C := _root_.SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) (invertibleSheaf' E)).hom =
      (evaluationPairingIso E).hom ≫ canonicalSectionHom E :=
  tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor E

/-- **The monoidal identity behind
`Stacks.Surfaces.twistedIdealIso_hom_comp_tensorCanonicalSection`.** Let `ι : I ⟶ 𝟙` and
`c : 𝟙 ⟶ P` be paired by a trivialization `ev : P ⊗ I ≅ 𝟙` in the sense of `hev`. Then
contracting the `I` slot of `(L ⊗ P) ⊗ I` against `ι` agrees, after the identification
`(L ⊗ P) ⊗ I ≅ L` built from `ev`, with multiplying `L` by `c`. -/
private theorem whiskerLeft_rightUnitor_eq_of_trivialization {C : Type*} [Category C]
    [MonoidalCategory C] {I P : C} (L : C) (ι : I ⟶ 𝟙_ C) (c : 𝟙_ C ⟶ P) (ev : P ⊗ I ≅ 𝟙_ C)
    (hev : P ◁ ι ≫ (ρ_ P).hom = ev.hom ≫ c) :
    ((α_ L P I).hom ≫ L ◁ ev.hom ≫ (ρ_ L).hom) ≫ ((ρ_ L).inv ≫ L ◁ c) =
      ((L ⊗ P) ◁ ι) ≫ (ρ_ (L ⊗ P)).hom := by
  calc ((α_ L P I).hom ≫ L ◁ ev.hom ≫ (ρ_ L).hom) ≫ ((ρ_ L).inv ≫ L ◁ c)
      = (α_ L P I).hom ≫ L ◁ (ev.hom ≫ c) := by
        rw [MonoidalCategory.whiskerLeft_comp]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (α_ L P I).hom ≫ L ◁ (P ◁ ι ≫ (ρ_ P).hom) := by rw [hev]
    _ = ((L ⊗ P) ◁ ι) ≫ (α_ L P (𝟙_ C)).hom ≫ L ◁ (ρ_ P).hom := by
        rw [MonoidalCategory.whiskerLeft_comp, ← Category.assoc,
          ← MonoidalCategory.associator_naturality_right, Category.assoc]
    _ = ((L ⊗ P) ◁ ι) ≫ (ρ_ (L ⊗ P)).hom := by monoidal

/-- **The twisted ideal inclusion is multiplication by the canonical section.** Under
`Stacks.Surfaces.twistedIdealIso` and the right unit constraint, the map
`(ℒ ⊗ 𝒪_X(E)) ⊗ ℐ_E ⟶ (ℒ ⊗ 𝒪_X(E)) ⊗ 𝒪_X` obtained by tensoring the ideal inclusion becomes
multiplication by `1_E`, `ℒ ⟶ ℒ ⊗ 𝒪_X(E)`.

The one nonformal input is
`Stacks.Divisors.tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor`, which says that
contracting `𝒪_X(E) ⊗ ℐ_E` against the ideal inclusion is the evaluation pairing followed by
multiplication by `1_E`; the rest is the coherence of the monoidal structure. -/
theorem twistedIdealIso_hom_comp_tensorCanonicalSection (E : X.IdealSheafData)
    [IsEffectiveCartierDivisor E] (L : _root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) :
    (twistedIdealIso E L).hom ≫ tensorCanonicalSection E L =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj
        (MonoidalCategory.tensorObj
            (C := _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) L
            (invertibleSheaf' E))).map (idealSheafInclusion E) ≫
        (MonoidalCategoryStruct.rightUnitor
          (C := _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
          (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) L
            (invertibleSheaf' E))).hom :=
  whiskerLeft_rightUnitor_eq_of_trivialization L (idealSheafInclusion E) (canonicalSectionHom E)
    (evaluationPairingIso E) (whiskerLeft_idealSheafInclusion_comp_rightUnitor E)

/-! ### Identifying the third term of the twisted ideal sequence -/

/-- **`𝓜 ⊗ i_*𝒪_Z ≅ i_*(i^*𝓜)` for a closed immersion `i`**: the projection formula for a closed
immersion of [Stacks, Tag 0FZE], with the braiding putting the direct image in the first slot
and the left unit constraint removing `𝒪_Z`. -/
def tensorPushforwardUnitIso {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) :
    MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) M
        ((modulePushforward i.toLRSHom.toShHom).obj
          (𝟙_ (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (Z).sheaf))))) ≅
      (modulePushforward i.toLRSHom.toShHom).obj
        ((modulePullback i.toLRSHom.toShHom).obj M) :=
  BraidedCategory.braiding (C := _root_.SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) M
      ((modulePushforward i.toLRSHom.toShHom).obj
        (𝟙_ (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (Z).sheaf))))) ≪≫
    Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i
      (𝟙_ (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (Z).sheaf)))) M ≪≫
    (modulePushforward i.toLRSHom.toShHom).mapIso
      (MonoidalCategory.leftUnitor (C := _root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (Z).sheaf)))
        ((modulePullback i.toLRSHom.toShHom).obj M))

/-- Restriction of scalars leaves the underlying group of a module alone, so it preserves
vanishing. -/
private theorem isZero_restrictScalars {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    {N : ModuleCat.{u} S} (h : IsZero N) :
    IsZero ((ModuleCat.restrictScalars φ).obj N) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  exact h

/-- **The global sections of `𝓜 ⊗ i_*𝒪_E` vanish when `𝓜` pulls back to a negative twist on the
projective line.** The module is `i_*(i^*𝓜)` by the projection formula, its sections are the
sections of `i^*𝓜` on `E`, and along `e` those are the sections of `𝒪(d)` on `𝐏¹`, which vanish
for `d < 0`. -/
theorem isZero_sections_tensorPushforwardUnit (E : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ E.subscheme)
    (M : _root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) {d : ℤ} (hd : d < 0)
    (hiso : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj M) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) d) :
    IsZero ((moduleGlobalSections X).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj M).obj
        ((modulePushforward E.subschemeι.toLRSHom.toShHom).obj
          (𝟙_ (_root_.SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (E.subscheme).sheaf))))))) := by
  change IsZero ((moduleGlobalSections X).obj
    (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) M
      ((modulePushforward E.subschemeι.toLRSHom.toShHom).obj
      (𝟙_ (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf E.subscheme.sheaf))))))
  refine IsZero.of_iso ?_
    ((moduleGlobalSections X).mapIso (tensorPushforwardUnitIso E.subschemeι M))
  refine IsZero.of_iso ?_ ((Stacks.Cohomology.AffineBase.pushforwardSectionsIso
    E.subschemeι).app ((modulePullback E.subschemeι.toLRSHom.toShHom).obj M))
  refine isZero_restrictScalars _ ?_
  refine IsZero.of_iso ?_ (Stacks.ClosedImmersion.sectionsIsoPullbackOfIsIso e.hom
    ((modulePullback E.subschemeι.toLRSHom.toShHom).obj M))
  refine isZero_restrictScalars _ ?_
  refine IsZero.of_iso ?_
    ((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).mapIso hiso)
  exact IsZero.of_iso (Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_zero_of_neg k hd)
    ((Functor.rightDerivedZeroIsoSelf
      (Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤)).app _).symm

/-! ### The twist of an exceptional curve -/

/-- **The coordinate standard opens of `𝐏ⁿ` are cut out by elements of degree one**, which is
the hypothesis of [Stacks, Tag 01MT] under which the twists `𝒪(m)` multiply. -/
theorem degreeOneCover_homogeneousSubmodule (R : Type u) [CommRing R] (n : ℕ) :
    DegreeOneCover (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := by
  refine top_le_iff.1 ?_
  rw [← Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top R n]
  exact iSup_le fun i => le_iSup_of_le
    ⟨MvPolynomial.X i, (MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_X _ _)⟩ le_rfl

/-- **`e^*i^*𝒪_X(E) ≅ 𝒪(-1)` for an exceptional curve of the first kind.** The normal-sheaf
clause of [Stacks, Tag 0B3P] identifies `i^*𝒪_X(E)` with the normal sheaf of `E` in `X`, and
being an exceptional curve of the first kind says exactly that the normal sheaf pulls back to
`𝒪(-1)` along `e`. -/
def pullbackInvertibleSheafIso (E : X.IdealSheafData) (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ E.subscheme}
    (hE : E.IsExceptionalCurveOfFirstKind k e) :
    (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj (invertibleSheaf' E)) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1) :=
  haveI := hE.isEffectiveCartierDivisor
  (modulePullback e.hom.toLRSHom.toShHom).mapIso
      (Stacks.Divisors.normalSheafIsoInvertibleSheaf E).symm ≪≫
    hE.nonempty_normalSheafIso.some

/-- **`e^*i^*(ℒ ⊗ 𝒪_X(E)) ≅ 𝒪(n - 1)` when `ℒ|_E` has degree `n`.** Pullback commutes with the
tensor product unconditionally ([Stacks, Tag 01CD]), and the two twists multiply by
[Stacks, Tag 01MT]. -/
def pullbackTwistIso (E : X.IdealSheafData) (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ E.subscheme} (hE : E.IsExceptionalCurveOfFirstKind k e)
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) {n : ℤ}
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj L) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) :
    (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj
          (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
            L (invertibleSheaf' E))) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + -1) :=
  (modulePullback e.hom.toLRSHom.toShHom).mapIso
      ((Stacks.RingedSpace.comparisonBifunctorIso
        E.subschemeι.toLRSHom.toShHom).app (L, invertibleSheaf' E)) ≪≫
    (Stacks.RingedSpace.comparisonBifunctorIso e.hom.toLRSHom.toShHom).app
      ((modulePullback E.subschemeι.toLRSHom.toShHom).obj L,
        (modulePullback E.subschemeι.toLRSHom.toShHom).obj (invertibleSheaf' E)) ≪≫
    MonoidalCategory.tensorIso
      (C := _root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf ((projectiveLineProj k)).sheaf)))
      hdeg (pullbackInvertibleSheafIso E k hE) ≪≫
    twistMultiplicationIso (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (degreeOneCover_homogeneousSubmodule k 1) n (-1)

/-! ### Assertion (2) of Tag 0C2J -/

/-- **[Stacks, Tag 0C2J], assertion (2).** Let `E ⊆ X` be an exceptional curve of the first kind
on a scheme `X`, let `ℒ` be an invertible `𝒪_X`-module, and let `n` be the degree of `ℒ|_E` as an
invertible module on `𝐏¹`, recorded as an isomorphism `e^*i^*ℒ ≅ 𝒪(n)`. If `n ≤ 0` then
multiplication by the canonical section `1_E` makes `H¹(X, ℒ)` a submodule of `H¹(X, ℒ(E))`.

The map is `Stacks.Divisors.tensorCanonicalSection`, the canonical map `ℒ ⟶ ℒ ⊗ 𝒪_X(E)` of
multiplication by `1_E`, and not merely some isomorphic copy of it. -/
@[stacks 0C2J "assertion (2): injectivity on H^1 when the degree is non-positive"]
theorem mono_rightDerived_one_map_tensorCanonicalSection (E : X.IdealSheafData) (k : Type u)
    [Field k] {e : projectiveLineProj k ≅ E.subscheme}
    (hE : E.IsExceptionalCurveOfFirstKind k e)
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    {n : ℤ} (hn : n ≤ 0)
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj L) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) :
    Mono (((moduleGlobalSections X).rightDerived 1).map (tensorCanonicalSection E L)) := by
  have _hcartier := hE.isEffectiveCartierDivisor
  have hMinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
        L (invertibleSheaf' E)) := by
    have hL : Stacks.SheafOfModules.IsInvertible X.presheaf
        (structureSheafRing X.toRingedSpace).property L :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
    have hP : Stacks.SheafOfModules.IsInvertible X.presheaf
        (structureSheafRing X.toRingedSpace).property (invertibleSheaf' E) :=
      isTensorInvertible_invertibleSheaf E
    exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf
      (structureSheafRing X.toRingedSpace).property L (invertibleSheaf' E)).toAlgebraicGeometry
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{_, _, u, u, u} X.sheaf
    (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) L (invertibleSheaf' E))
  have hzero := isZero_sections_tensorPushforwardUnit E k e
    (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) L
      (invertibleSheaf' E)) (d := n + -1) (by omega) (pullbackTwistIso E k hE L hdeg)
  have hmono := mono_rightDerived_one_map_map_tensorLeft
    (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) L
      (invertibleSheaf' E))
    (idealShortComplex E) (idealShortComplex_shortExact E) hzero
  have hfac : tensorCanonicalSection E L = (twistedIdealIso E L).inv ≫
      (((idealShortComplex E).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj
            (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) L
              (invertibleSheaf' E)))).f ≫
        (MonoidalCategoryStruct.rightUnitor
          (C := _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
          (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))) L
            (invertibleSheaf' E))).hom) :=
    (Iso.eq_inv_comp (twistedIdealIso E L)).2
      (twistedIdealIso_hom_comp_tensorCanonicalSection E L)
  rw [hfac]
  exact mono_map_comp_of_isIso _ _ _ _
    (((moduleGlobalSections X).rightDerived 1).mapIso (twistedIdealIso E L)).isIso_inv hmono
    (((moduleGlobalSections X).rightDerived 1).mapIso (MonoidalCategoryStruct.rightUnitor
      (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) _)).isIso_hom

end Stacks.Surfaces

end

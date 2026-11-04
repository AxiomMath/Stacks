module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallySmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local Künneth decomposition of the relative forms of a smooth morphism

Let `f : X ⟶ Y` be a smooth morphism of schemes over a base `S`, with `g : Y ⟶ S` the structure
morphism of the target. The transitivity sequence

`0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0`

is short exact ([Stacks, Tags 06B6, 02K4]) with finite locally free quotient ([Stacks, Tag
02G1]), hence splits over an open neighbourhood of every point of `X`. Over such an open the
Künneth decomposition of an exterior power along a splitting applies, so the relative forms of
`X` over `S` decompose:

`⨁_{p + q = n} (⋀^p(f^*Ω_{Y/S})|_U ⊗_{𝒪_U} ⋀^q(Ω_{X/Y})|_U) ≅ ⋀^n(Ω_{X/S})|_U`.

The decomposition depends on the chosen section `Ω_{X/Y}|_U ⟶ Ω_{X/S}|_U`: two splittings of a
short complex have sections differing by a morphism that factors through `S.f`, and retractions
differing by a morphism that factors through `S.g`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsShortComplex`: the transitivity sequence
  `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` as a short complex of `𝒪_X`-modules.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsShortComplexRestrict`: its restriction to
  an open of `X`.

## Main results

* `CategoryTheory.ShortComplex.Splitting.s_sub_s` and
  `CategoryTheory.ShortComplex.Splitting.r_sub_r`: **the ambiguity of a splitting**: two
  sections differ by a morphism factoring through `S.f`, two retractions by one factoring
  through `S.g`.
* `AlgebraicGeometry.Scheme.Hom.shortExact_relativeDifferentialsShortComplex`: the transitivity
  sequence of a formally smooth morphism is short exact, in the packaged form.
* `AlgebraicGeometry.Scheme.Modules.isIso_exteriorPowerProdHom_of_splitting`: for a split short
  complex of `𝒪_X`-modules the Künneth comparison of exterior powers is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.exists_nonempty_splitting_relativeDifferentialsRestrict`: the
  transitivity sequence of a smooth morphism splits over an open neighbourhood of every point.
* `AlgebraicGeometry.Scheme.Hom.exists_isIso_exteriorPowerProdHom_relativeDifferentials`:
  **the local Künneth decomposition of the relative forms of a smooth morphism.**

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 06B6](https://stacks.math.columbia.edu/tag/06B6)
* [Stacks Project, Tag 02K4](https://stacks.math.columbia.edu/tag/02K4)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace CategoryTheory.ShortComplex.Splitting

variable {C : Type*} [Category C] [Preadditive C] {T : ShortComplex C}

/-- The difference of two sections of a split short complex `T` factors through `T.f`:
`sp.s - sp'.s = (sp.s ≫ sp'.r) ≫ T.f`. -/
theorem s_sub_s (sp sp' : T.Splitting) : sp.s - sp'.s = (sp.s ≫ sp'.r) ≫ T.f := by
  have h : sp.s ≫ (sp'.r ≫ T.f + T.g ≫ sp'.s) = sp.s := by rw [sp'.id, Category.comp_id]
  rw [Preadditive.comp_add, ← Category.assoc sp.s sp'.r T.f, ← Category.assoc sp.s T.g sp'.s,
    sp.s_g, Category.id_comp] at h
  exact sub_eq_iff_eq_add.2 h.symm

/-- The difference of two retractions of a split short complex `T` factors through `T.g`:
`sp.r - sp'.r = T.g ≫ sp'.s ≫ sp.r`. -/
theorem r_sub_r (sp sp' : T.Splitting) : sp.r - sp'.r = T.g ≫ sp'.s ≫ sp.r := by
  have h : (sp'.r ≫ T.f + T.g ≫ sp'.s) ≫ sp.r = sp.r := by rw [sp'.id, Category.id_comp]
  rw [Preadditive.add_comp, Category.assoc, sp.f_r, Category.comp_id, Category.assoc] at h
  exact sub_eq_iff_eq_add.2 (h.symm.trans (add_comm _ _))

end CategoryTheory.ShortComplex.Splitting

namespace AlgebraicGeometry.Scheme.Modules

/-- **The Künneth comparison of exterior powers along a splitting of a short complex of
`𝒪_X`-modules is an isomorphism.** For a split short complex `0 ⟶ ℱ ⟶ ℋ ⟶ 𝒢 ⟶ 0` the wedge
product assembles `⋀^p ℱ ⊗ ⋀^q 𝒢` with `p + q = n` into `⋀^n ℋ`, along the inclusion of the
sub and the section of the quotient. -/
theorem isIso_exteriorPowerProdHom_of_splitting {Z : Scheme.{u}} {T : ShortComplex Z.Modules}
    (sp : T.Splitting)
    (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Z.carrier) T.X₁)
    (AG : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Z.carrier) T.X₃)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Z.carrier) T.X₂) (n : ℕ) :
    IsIso (_root_.SheafOfModules.exteriorPowerProdHom AF AG A T.f sp.s n) :=
  _root_.SheafOfModules.isIso_exteriorPowerProdHom AF AG A T.f sp.r sp.s T.g sp.f_r sp.s_g
    T.zero sp.s_r sp.id n

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-! ### The transitivity sequence as a short complex -/

/-- The canonical map `f^*Ω_{Y/S} ⟶ Ω_{X/S}` followed by `Ω_{X/S} ⟶ Ω_{X/Y}` vanishes. -/
theorem relativeDifferentialsMap_comp_toRelativeDifferentials_eq_zero (f : X ⟶ Y) (g : Y ⟶ S) :
    relativeDifferentialsMap f g (f ≫ g) (𝟙 S) (Category.comp_id (f ≫ g)).symm ≫
      f.toRelativeDifferentials g = 0 :=
  (toRelativeDifferentials_exact f g).elim fun h _ => h

/-- **The transitivity sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0`** of a composable
pair `X ⟶ Y ⟶ S`, as a short complex of `𝒪_X`-modules. -/
def relativeDifferentialsShortComplex (f : X ⟶ Y) (g : Y ⟶ S) : ShortComplex X.Modules :=
  ShortComplex.mk _ _ (relativeDifferentialsMap_comp_toRelativeDifferentials_eq_zero f g)

/-- The first object of `relativeDifferentialsShortComplex f g` is `f^*Ω_{Y/S}`. -/
@[simp]
theorem relativeDifferentialsShortComplex_X₁ (f : X ⟶ Y) (g : Y ⟶ S) :
    (relativeDifferentialsShortComplex f g).X₁ =
      (Scheme.Modules.pullback f).obj (relativeDifferentials g) :=
  rfl

/-- The middle object of `relativeDifferentialsShortComplex f g` is `Ω_{X/S}`. -/
@[simp]
theorem relativeDifferentialsShortComplex_X₂ (f : X ⟶ Y) (g : Y ⟶ S) :
    (relativeDifferentialsShortComplex f g).X₂ = relativeDifferentials (f ≫ g) :=
  rfl

/-- The last object of `relativeDifferentialsShortComplex f g` is `Ω_{X/Y}`. -/
@[simp]
theorem relativeDifferentialsShortComplex_X₃ (f : X ⟶ Y) (g : Y ⟶ S) :
    (relativeDifferentialsShortComplex f g).X₃ = relativeDifferentials f :=
  rfl

/-- The transitivity sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` of a formally smooth
morphism `f` is short exact. -/
@[ega "IV 17.2.3", sga "1 II 4.3" "more general", sga "6 VIII 5.2" "partial"]
theorem shortExact_relativeDifferentialsShortComplex (f : X ⟶ Y) (g : Y ⟶ S)
    (hf : FormallySmooth f) : (relativeDifferentialsShortComplex f g).ShortExact :=
  (toRelativeDifferentials_shortExact f g hf).elim fun _ h => h

/-- The transitivity sequence of `X ⟶ Y ⟶ S`, restricted to an open `U` of `X`. -/
abbrev relativeDifferentialsShortComplexRestrict (f : X ⟶ Y) (g : Y ⟶ S) (U : X.Opens) :
    ShortComplex (U : Scheme.{u}).Modules :=
  (relativeDifferentialsShortComplex f g).map (Scheme.Modules.restrictFunctor U.ι)

/-! ### The local splitting and the local Künneth decomposition -/

/-- The transitivity sequence of a smooth morphism `f : X ⟶ Y` splits over an open
neighbourhood of every point of `X`. -/
@[ega "IV 16.4.24", ega "IV 17.2.3" "(ii), special case", sga "1 II 4.3" "more general"]
theorem exists_nonempty_splitting_relativeDifferentialsRestrict (f : X ⟶ Y) (g : Y ⟶ S)
    [Smooth f] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty (relativeDifferentialsShortComplexRestrict f g U).Splitting :=
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) (relativeDifferentialsShortComplex f g).X₃ :=
    isFiniteLocallyFree_relativeDifferentials f
  Scheme.Modules.exists_nonempty_splitting_restrict_of_isFiniteLocallyFree
    (relativeDifferentialsShortComplex f g)
    (shortExact_relativeDifferentialsShortComplex f g
      (Stacks.Smooth.formallySmoothScheme_of_smooth f)) x

/-- **The relative forms of a smooth morphism decompose locally along the transitivity
sequence.** For `f : X ⟶ Y` smooth over a base `S` every point of `X` has an open neighbourhood
`U` over which `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` splits and, for every `n`, the wedge
product is an isomorphism

`⨁_{p + q = n} (⋀^p(f^*Ω_{Y/S})|_U ⊗_{𝒪_U} ⋀^q(Ω_{X/Y})|_U) ≅ ⋀^n(Ω_{X/S})|_U`. -/
@[ega "IV 17.2.3" "(ii), special case"]
theorem exists_isIso_exteriorPowerProdHom_relativeDifferentials (f : X ⟶ Y) (g : Y ⟶ S)
    [Smooth f] (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (sp : (relativeDifferentialsShortComplexRestrict f g U).Splitting), ∀ n : ℕ,
      IsIso (_root_.SheafOfModules.exteriorPowerProdHom
        (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
          (relativeDifferentialsShortComplexRestrict f g U).X₁)
        (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
          (relativeDifferentialsShortComplexRestrict f g U).X₃)
        (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
          (relativeDifferentialsShortComplexRestrict f g U).X₂)
        (relativeDifferentialsShortComplexRestrict f g U).f sp.s n) := by
  obtain ⟨U, hxU, ⟨sp⟩⟩ := exists_nonempty_splitting_relativeDifferentialsRestrict f g x
  exact ⟨U, hxU, sp, fun n => Scheme.Modules.isIso_exteriorPowerProdHom_of_splitting sp _ _ _ n⟩

end AlgebraicGeometry.Scheme.Hom

end

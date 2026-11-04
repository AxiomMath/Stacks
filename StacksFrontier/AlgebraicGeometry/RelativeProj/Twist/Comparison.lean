module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# The twist comparison across a morphism of homogeneous spectra

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings whose irrelevant ideals
satisfy `ℬ₊ ≤ 𝒜₊.map φ`, so that `r = AlgebraicGeometry.Proj.map φ : Proj ℬ ⟶ Proj 𝒜` is
defined. This file constructs, for every integer `n`, the canonical comparison

`θ : r^* 𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)`

of twisting sheaves. It is produced from its adjoint transpose
`𝒪_{Proj 𝒜}(n) ⟶ r_* 𝒪_{Proj ℬ}(n)`, which is written down explicitly: a section of
`𝒪_{Proj 𝒜}(n)` over an open `U` is a family of degree-`n` fractions indexed by the points of
`U`, and `φ` localizes each such fraction at the prime below a point of `r^{-1}U`.

## Main definitions

* `Stacks.ProjTwistComparison.fibreMap`: the comparison of module fibres at a homogeneous prime
  of `ℬ` and its preimage, which for the twists of the structure sheaf is
  `Localization.localRingHom`.
* `Stacks.ProjTwistComparison.sectionFun` and
  `Stacks.ProjTwistComparison.sectionsMap`: the comparison on sections, as a map of fraction
  families and then as a map of the section modules.
* `Stacks.ProjTwistComparison.pushforwardTwistMap`: the adjoint transpose
  `𝒪_{Proj 𝒜}(n) ⟶ r_* 𝒪_{Proj ℬ}(n)`.
* `Stacks.ProjTwistComparison.twistMap`: the comparison `θ` itself.

## Main results

* `Stacks.ProjTwistComparison.locallyModuleFraction_sectionFun`: the comparison carries
  degree-`n` fractions to degree-`n` fractions.
* `Stacks.ProjTwistComparison.fibreMap_smul` and
  `Stacks.ProjTwistComparison.fibreMap_val_smul`: the comparison is semilinear over the
  structure-sheaf map of `AlgebraicGeometry.Proj.map`.
* `Stacks.ProjTwistComparison.homEquiv_twistMap`: the adjoint transpose of `θ` is
  `pushforwardTwistMap`.

## Implementation notes

The comparison is defined pointwise because the twisting sheaf is defined pointwise:
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒜 n` is the associated sheaf of the
shifted regular module, whose sections over `U` are the dependent functions
`∀ x : U, LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl A` that are locally a
homogeneous fraction `m / s` with `deg m = deg s + n`. The fibres are full localizations, so the
fibre comparison is `Localization.localRingHom` and nothing graded appears in it; the grading
enters only in `locallyModuleFraction_sectionFun`, where `φ` is applied to a numerator and a
denominator of given degrees.

Degrees of numerators live in `ℤ`, through
`AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading`, which is the zero submodule in
negative degrees. `map_mem_integerGrading` therefore splits on the sign; no hypothesis relating
`n` to the degree of the denominator is needed.

Semilinearity is the only step where the definition of `AlgebraicGeometry.Proj.map` is used.
Its structure-sheaf map is, by construction, the pointwise `HomogeneousLocalization.localRingHom`,
and `HomogeneousLocalization.val_localRingHom` identifies the underlying fraction of that with
`Localization.localRingHom` of the underlying fraction — which is exactly `fibreMap`. The
morphism of sheaves of modules is then assembled with `ConcreteCategory.ofHom` so that the
module structures are taken from the `ModuleCat` objects of the expected type rather than
re-synthesized; the two `letI`s supply the module structures on the associated-sheaf sections
that `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf` itself installs locally.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjTwistComparison

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)

/-- The comparison of module fibres: the localization of `φ` at a homogeneous prime of `ℬ` and
its preimage. For the regular module this is `Localization.localRingHom`. -/
def fibreMap (y : ProjectiveSpectrum ℬ)
    (z : ModuleFiber (M := A) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    ModuleFiber (M := B) ℬ y :=
  Localization.localRingHom
    (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal
    y.asHomogeneousIdeal.toIdeal φ.toRingHom rfl z

/-- The fibre comparison on a fraction: apply `φ` to the numerator and the denominator. -/
@[simp] theorem fibreMap_mk (y : ProjectiveSpectrum ℬ) (m : A)
    (s : (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl) :
    fibreMap φ hφ y (LocalizedModule.mk m s) =
      LocalizedModule.mk (φ m) ⟨φ s, s.2⟩ :=
  Localization.localRingHom_mk ..

omit [GradedRing 𝒜] [GradedRing ℬ] in
/-- The image of an integer-graded piece under a homomorphism of graded rings. -/
theorem map_mem_integerGrading {i : ℤ} {m : A} (hm : m ∈ integerGrading (S := A) 𝒜 i) :
    φ m ∈ integerGrading (S := B) ℬ i := by
  rcases le_or_gt 0 i with hi | hi
  · simp only [integerGrading, hi, reduceIte, mem_homogeneousSubmodule] at hm ⊢
    exact φ.map_mem hm
  · rw [integerGrading_neg _ _ hi, Submodule.mem_bot] at hm ⊢
    rw [hm, map_zero]

variable (n : ℤ)

/-- The comparison on sections, as a map of dependent functions into the module fibres: a
degree-`n` fraction family on an open of `Proj 𝒜` is carried to one on any open of `Proj ℬ`
mapping into it. -/
def sectionFun (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap φ hφ ⁻¹' U.1)
    (a : ∀ x : U, ModuleFiber (M := A) 𝒜 x.1) (y : V) : ModuleFiber (M := B) ℬ y.1 :=
  fibreMap φ hφ y.1 (a ⟨ProjectiveSpectrum.comapFun φ hφ y.1, hUV y.2⟩)

/-- The comparison carries degree-`n` fractions to degree-`n` fractions. -/
theorem locallyModuleFraction_sectionFun (U : Opens (ProjectiveSpectrum.top 𝒜))
    (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap φ hφ ⁻¹' U.1)
    (a : ∀ x : U, ModuleFiber (M := A) 𝒜 x.1)
    (ha : (locallyModuleFraction 𝒜 (twistGrading (S := A) 𝒜 n)).pred a) :
    (locallyModuleFraction ℬ (twistGrading (S := B) ℬ n)).pred
      (sectionFun φ hφ U V hUV a) := by
  rintro ⟨p, hpV⟩
  obtain ⟨W, hmemW, iWU, k, m, s, hm, hs, hns, hfrac⟩ :=
    ha ⟨ProjectiveSpectrum.comapFun φ hφ p, hUV hpV⟩
  exact ⟨W.comap (ProjectiveSpectrum.comap φ hφ) ⊓ V, ⟨hmemW, hpV⟩, Opens.infLERight _ _,
    k, φ m, φ s, map_mem_integerGrading φ hm, φ.map_mem hs,
    fun y hmem => hns ⟨_, y.2.1⟩ hmem,
    fun y => (congrArg (fibreMap φ hφ y.1) (hfrac ⟨_, y.2.1⟩)).trans
      (fibreMap_mk φ hφ y.1 m ⟨s, hns ⟨_, y.2.1⟩⟩)⟩

/-- The comparison on the sections of the twisting sheaves over an open and its preimage. -/
def sectionsMap (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    moduleSections 𝒜 (twistGrading (S := A) 𝒜 n) U →
      moduleSections ℬ (twistGrading (S := B) ℬ n)
        (U.comap (ProjectiveSpectrum.comap φ hφ)) :=
  fun a => ⟨sectionFun φ hφ U _ Set.Subset.rfl a.1,
    locallyModuleFraction_sectionFun φ hφ n U _ Set.Subset.rfl a.1 a.2⟩

/-- The value of the comparison of sections at a point. -/
@[simp] theorem sectionsMap_apply (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : moduleSections 𝒜 (twistGrading (S := A) 𝒜 n) U)
    (y : U.comap (ProjectiveSpectrum.comap φ hφ)) :
    (sectionsMap φ hφ n U a).1 y = fibreMap φ hφ y.1 (a.1 ⟨_, y.2⟩) := rfl

/-- The fibre comparison is semilinear over the comparison of local rings. -/
theorem fibreMap_smul (y : ProjectiveSpectrum ℬ)
    (u : Localization
      (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl)
    (z : ModuleFiber (M := A) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    fibreMap φ hφ y (u • z) =
      Localization.localRingHom
        (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal
        y.asHomogeneousIdeal.toIdeal φ.toRingHom rfl u • fibreMap φ hφ y z :=
  map_mul (Localization.localRingHom _ _ φ.toRingHom rfl) u z

/-- The fibre comparison is semilinear over the comparison of structure-sheaf sections: the
scalar `c` acting over `U` acts, after comparison, as its image under the structure-sheaf map of
`AlgebraicGeometry.Proj.map`. -/
theorem fibreMap_val_smul (U : Opens (ProjectiveSpectrum.top 𝒜))
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U))
    (y : U.comap (ProjectiveSpectrum.comap φ hφ))
    (z : ModuleFiber (M := A) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y.1)) :
    fibreMap φ hφ y.1 (HomogeneousLocalization.val
        (c.1 (⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩ : U)) • z) =
      HomogeneousLocalization.val
        (HomogeneousLocalization.localRingHom φ
          (ProjectiveSpectrum.comapFun φ hφ y.1).asHomogeneousIdeal.toIdeal
          y.1.asHomogeneousIdeal.toIdeal rfl
          (c.1 (⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩ : U))) • fibreMap φ hφ y.1 z := by
  rw [fibreMap_smul]
  exact congrArg (· • fibreMap φ hφ y.1 z) (HomogeneousLocalization.val_localRingHom
    (c.1 (⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩ : U))).symm

/-- The comparison morphism `𝒪_{Proj 𝒜}(n) ⟶ r_* 𝒪_{Proj ℬ}(n)`. -/
def pushforwardTwistMap :
    twistingSheaf 𝒜 n ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Proj.map φ hφ)).obj (twistingSheaf ℬ n) := by
  letI : ∀ U, Module
      (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj U)
      ((modulePresheaf 𝒜 (twistGrading (S := A) 𝒜 n)).obj U) :=
    fun U => modulePresheafModule 𝒜 _ U
  letI : ∀ U, Module
      (((ProjectiveSpectrum.Proj.structureSheaf ℬ).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj U)
      ((modulePresheaf ℬ (twistGrading (S := B) ℬ n)).obj U) :=
    fun U => modulePresheafModule ℬ _ U
  exact
    { val :=
        { app := fun U => ConcreteCategory.ofHom
            { toFun := sectionsMap φ hφ n U.unop
              map_add' := fun _ _ => Subtype.ext (funext fun _ =>
                map_add (Localization.localRingHom _ _ φ.toRingHom rfl) _ _)
              map_smul' := fun c a => Subtype.ext (funext fun y =>
                fibreMap_val_smul φ hφ U.unop c y
                  (a.1 ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩)) }
          naturality := fun _ => rfl } }

/-- **The canonical twist comparison** `θ : r^* 𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)`, where
`r = AlgebraicGeometry.Proj.map φ`. It is the morphism adjoint to
`Stacks.ProjTwistComparison.pushforwardTwistMap`, hence canonical: it is the unique morphism
whose adjoint transpose is the pointwise localization of `φ` on degree-`n` fractions. -/
def twistMap :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Proj.map φ hφ)).obj (twistingSheaf 𝒜 n) ⟶ twistingSheaf ℬ n :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (AlgebraicGeometry.Proj.map φ hφ)).homEquiv _ _).symm (pushforwardTwistMap φ hφ n)

/-- The adjoint transpose of `θ` is the explicit pointwise comparison. -/
theorem homEquiv_twistMap :
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.Proj.map φ hφ)).homEquiv _ _) (twistMap φ hφ n) =
      pushforwardTwistMap φ hφ n :=
  Equiv.apply_symm_apply _ _

end Stacks.ProjTwistComparison

end

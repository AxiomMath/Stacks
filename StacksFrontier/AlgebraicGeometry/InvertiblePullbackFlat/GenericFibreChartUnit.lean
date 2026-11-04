module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreChartGenerator
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreTrivialization

/-!
# The unit of `A ⊗_R K` that the penultimate paragraph of Tag 0BD7 asks for

`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/GenericFibreChart.lean` reduces the
penultimate paragraph of [Stacks, Tag 0BD7] at a point `x` to a single unproved input: a **unit**
of `Ideal.Fiber ⊥ Γ(X, U)`, the source's `A ⊗_R K`, for an affine chart `x ∈ U ≤ f ⁻¹ᵁ V`. Its
module docstring records that nothing in the development produced one. This file produces one, and
with it states the paragraph at `x` with no hypothesis the tag does not have.

The element is not merely *some* unit — `∃ b, IsUnit b` is inhabited by `1` in any ring — but the
**coordinate of the trivializing section of `ℒ_ξ` against the chart's generator**
(`AlgebraicGeometry.genericFiberChartCoord`), and that is where assumption (5) enters. One
isomorphism `ℒ_ξ ≅ 𝒪_{X_ξ}` gives, through `Stacks.SheafOfModules.generatorOfIso`, a generator of
`ℒ_ξ` on *every* open of the generic fibre at once; the chart's own generator is the pullback of a
generator of `ℒ` on `U` (`AlgebraicGeometry.genericFiberChartGenerator`); and two generators of an
invertible module on one open differ by a unit
(`Stacks.SheafOfModules.isUnit_of_smul_eq_generator`). Pointwise invertibility of `ℒ` would give a
generator near each point and so a different section at each chart; the single isomorphism is what
makes the coordinate at every chart the coordinate of one section.

## Main definitions

* `AlgebraicGeometry.genericFiberChartSections`: the ring map
  `Γ(X_ξ, genericFiberChartOpens) →+* Ideal.Fiber ⊥ Γ(X, U)` of the chart, the sections of the
  generic fibre over the chart read in the chart's own ring.
* `AlgebraicGeometry.genericFiberTrivGenerator`: the generator of `ℒ_ξ` on an arbitrary open
  supplied by a trivialization of `ℒ_ξ` — assumption (5) of the tag.
* `AlgebraicGeometry.genericFiberChartCoord`: the coordinate of that generator against the
  chart's generator, read in `Ideal.Fiber ⊥ Γ(X, U)`.

## Main results

* `AlgebraicGeometry.bijective_genericFiberChartSections`: that map is a **bijection**, so the
  chart's ring of sections *is* `Ideal.Fiber ⊥ Γ(X, U)`.
* `AlgebraicGeometry.genericFiberChartSections_appLE_fiberι`: the chart's sections map carries
  the restriction of a section `a` of `𝒪_X` on `U` to `1 ⊗ₜ a`.
* `AlgebraicGeometry.genericFiberTrivGenerator_val_eq`: the defining equation of the coordinate —
  the trivializing generator is the ratio times the chart's generator.
* `AlgebraicGeometry.isUnit_genericFiberChartCoord`: **the coordinate is a unit.**
* `AlgebraicGeometry.exists_isUnit_mul_eq_genericFiberChartCoord`: the penultimate paragraph of
  [Stacks, Tag 0BD7] at `x`, with the coordinate in place of the hypothesis `b` of
  `AlgebraicGeometry.exists_isUnit_mul_eq_of_isUnit_fiberBot_chart`.
* `AlgebraicGeometry.exists_chart_isUnit_mul_eq_of_isTrivial_genericFiber`: the same at an
  arbitrary point of `X`, the chart supplied by
  `AlgebraicGeometry.exists_affine_chart_generator_mem`, so that no hypothesis beyond the tag's
  own remains.

## Implementation notes

The ratio of the two generators is left inline rather than given a definition of its own stated at
the type `↑Γ(X_ξ, genericFiberChartOpens f hV hU e hx)`. That spelling of the sections of the
structure sheaf and the spelling `Stacks.SheafOfModules.generatorRatio` returns are equal but not
reducibly so, and a definition at the first one makes the scalar action on `ℒ_ξ` in
`genericFiberTrivGenerator_val_eq` unsynthesizable — `failed to synthesize HSMul`. Applying the
ring map of `genericFiberChartSections`, whose domain *is* stated at the `Γ` spelling, is
unaffected, because function application needs only definitional equality.

`AlgebraicGeometry.genericFiberChartSections` is `AlgebraicGeometry.Scheme.Hom.appLE` of the chart
immersion followed by `AlgebraicGeometry.Scheme.ΓSpecIso`, stated as a ring map rather than as an
isomorphism: only a ring map is needed to carry a unit, and the inclusion `⊤ ≤ ι ⁻¹ᵁ ι.opensRange`
it is taken along is `fun p _ => ⟨p, rfl⟩`. It *is* an isomorphism —
`AlgebraicGeometry.bijective_genericFiberChartSections` — and that is what a consumer wanting to
move an equation the other way, from the chart's sections into `Ideal.Fiber ⊥ Γ(X, U)`, needs.

**No goal mentioning the chart admits `rw` or `simp`.** The chart definitions carry the instance
`letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩`, whose membership proof has type
`x ∈ f ⁻¹ᵁ V` where `f x ∈ V` is wanted; the two agree only by unfolding `Opens.map`, so every
such goal is rejected as not type-correct at `implicit` transparency and both tactics refuse
before they begin. `AlgebraicGeometry.genericFiberChartSections_appLE_fiberι` is therefore a
single `Eq.trans` chain built from `CategoryTheory.Category.assoc`, `congrArg` with the motive
written out, and lemmas proved in contexts where the chart does not occur — the same discipline
`GenericFibreChartGenerator.lean` records for the legs of the chart square.

No tag attribute: every statement below carries an affine chart and a point of `X`, neither of
which [Stacks, Tag 0BD7] has, and the tag's own declaration is not closed here.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.SheafOfModules
open scoped TensorProduct

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] {x : X}
  {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
  (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)
  (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))

/-- **The sections of the generic fibre over the chart, read in the chart's own ring.** The chart
immersion is an open immersion onto `AlgebraicGeometry.genericFiberChartOpens`, so its `appLE`
followed by `AlgebraicGeometry.Scheme.ΓSpecIso` lands in `Ideal.Fiber ⊥ Γ(X, U)`. -/
def genericFiberChartSections :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    ↑Γ(f.fiber (genericPoint Y), genericFiberChartOpens f hV hU e hx) →+*
      ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)) :=
  letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  letI := isOpenImmersion_genericFiberChartι f hV hU e hx
  ((genericFiberChartι f hV hU e hx).appLE
      (genericFiberChartOpens f hV hU e hx) ⊤ (fun p _ => ⟨p, rfl⟩) ≫
    (Scheme.ΓSpecIso (CommRingCat.of ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)))).hom).hom

/-- **The chart's sections map is a bijection.** The chart immersion is an open immersion *onto*
`AlgebraicGeometry.genericFiberChartOpens`, so its `app` there is an isomorphism and the
restriction it is composed with is one between equal opens. -/
theorem bijective_genericFiberChartSections :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    Function.Bijective (genericFiberChartSections f hV hU e hx) := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  let := isOpenImmersion_genericFiberChartι f hV hU e hx
  have h0 : IsIso ((genericFiberChartι f hV hU e hx).app
      (genericFiberChartOpens f hV hU e hx)) :=
    Scheme.Hom.isIso_app _ _ le_rfl
  have h1 : IsIso (homOfLE (show (⊤ : (Spec (CommRingCat.of
      ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)))).Opens) ≤
      genericFiberChartι f hV hU e hx ⁻¹ᵁ genericFiberChartOpens f hV hU e hx from
        fun p _ => ⟨p, rfl⟩)) :=
    ⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hfull : IsIso (((genericFiberChartι f hV hU e hx).app
        (genericFiberChartOpens f hV hU e hx) ≫
      (Spec (CommRingCat.of ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)))).presheaf.map
        (homOfLE (show (⊤ : (Spec (CommRingCat.of
            ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)))).Opens) ≤
          genericFiberChartι f hV hU e hx ⁻¹ᵁ genericFiberChartOpens f hV hU e hx from
            fun p _ => ⟨p, rfl⟩)).op) ≫
      (Scheme.ΓSpecIso
        (CommRingCat.of ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)))).hom) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hfull

/-- **Reading an affine chart's sections through `AlgebraicGeometry.Scheme.ΓSpecIso`.** For a
morphism out of `Spec R` that is the spectrum of `φ : Γ(X, U) → R` followed by `hU.fromSpec`, the
sections map on `U` is `φ`. -/
private theorem appLE_top_eq_of_eq_specMap_comp_fromSpec {Z : Scheme.{u}} {W : Z.Opens}
    (hW : IsAffineOpen W) {R : CommRingCat.{u}} (φ : Γ(Z, W) ⟶ R) (m : Spec R ⟶ Z)
    (hm : m = Spec.map φ ≫ hW.fromSpec) (hle : (⊤ : (Spec R).Opens) ≤ m ⁻¹ᵁ W) :
    m.appLE W ⊤ hle ≫ (Scheme.ΓSpecIso R).hom = φ := by
  subst hm
  have h1 : (Spec.map φ ≫ hW.fromSpec).appLE W ⊤ hle =
      hW.fromSpec.appLE W ⊤ (le_of_eq hW.fromSpec_preimage_self.symm) ≫ (Spec.map φ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (Spec.map φ) hW.fromSpec W ⊤ ⊤ _ le_top).symm
  have h2 : hW.fromSpec.appLE W ⊤ (le_of_eq hW.fromSpec_preimage_self.symm) =
      (Scheme.ΓSpecIso Γ(Z, W)).inv := by
    rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    simp
  rw [h1, h2, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- **The chart's sections map on the image of `Γ(X, U)`.** A section `a` of `𝒪_X` on `U`,
restricted to the chart of the generic fibre, is read by
`AlgebraicGeometry.genericFiberChartSections` as `1 ⊗ₜ a`. This is the one equation that, by
`AlgebraicGeometry.eq_stalkFiberBotToGenericStalk_comp_chartFiberBotToStalkFiberBot`, pins the
chart coordinate down inside the function field. -/
theorem genericFiberChartSections_appLE_fiberι (a : ↑Γ(X, U)) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    genericFiberChartSections f hV hU e hx
        (((f.fiberι (genericPoint Y)).appLE U (genericFiberChartOpens f hV hU e hx)
          (genericFiberChartOpens_le f hV hU e hx)).hom a) =
      (1 : (⊥ : Ideal ↑Γ(Y, V)).ResidueField) ⊗ₜ[↑Γ(Y, V)] a := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  let : Algebra ↑Γ(X, U) ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)) :=
    Algebra.TensorProduct.rightAlgebra
  let := isOpenImmersion_genericFiberChartι f hV hU e hx
  have key : (f.fiberι (genericPoint Y)).appLE U (genericFiberChartOpens f hV hU e hx)
        (genericFiberChartOpens_le f hV hU e hx) ≫
      ((genericFiberChartι f hV hU e hx).appLE
        (genericFiberChartOpens f hV hU e hx) ⊤ (fun p _ => ⟨p, rfl⟩) ≫
        (Scheme.ΓSpecIso
          (CommRingCat.of ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)))).hom) =
      CommRingCat.ofHom (algebraMap ↑Γ(X, U) ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (Scheme.ΓSpecIso
            (CommRingCat.of ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)))).hom)
          (Scheme.Hom.appLE_comp_appLE (genericFiberChartι f hV hU e hx)
            (f.fiberι (genericPoint Y)) U (genericFiberChartOpens f hV hU e hx) ⊤ _ _)).trans
        (appLE_top_eq_of_eq_specMap_comp_fromSpec hU _ _
          (genericFiberChartι_comp_fiberι f hV hU e hx) _))
  exact congrArg (fun m : Γ(X, U) ⟶
    CommRingCat.of ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)) => m.hom a) key

variable
  (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
    (f.fiber (genericPoint Y)).presheaf
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
      (f.fiber (genericPoint Y)).IsSheaf)
    ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L))

/-- **Assumption (5) of [Stacks, Tag 0BD7] as a generator.** One trivialization of `ℒ_ξ` gives a
generator of `ℒ_ξ` on every open of the generic fibre, the same section read on each; this is the
quantifier order that pointwise invertibility does not supply. -/
def genericFiberTrivGenerator (W : (f.fiber (genericPoint Y)).Opens) :
    GeneratorSections (f.fiber (genericPoint Y)).toRingedSpace
      ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L) W :=
  generatorOfIso _ hgen.some

variable (hL : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
  (genU : GeneratorSections X.toRingedSpace L U)

/-- **The defining equation of the chart coordinate.** On the chart of the generic fibre the
trivializing generator is the ratio times the chart's own generator. -/
theorem genericFiberTrivGenerator_val_eq :
    (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx)).val =
      generatorRatio _ (genericFiberChartOpens f hV hU e hx)
          (genericFiberChartGenerator f hV hU e hx L hL genU)
          (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx)) •
        (genericFiberChartGenerator f hV hU e hx L hL genU).val :=
  generatorRatio_spec _ _ _ _

/-- **The source's `s` as an element of `A ⊗_R K`.** The coordinate of the trivializing section of
`ℒ_ξ` against the chart's generator, read in `Ideal.Fiber ⊥ Γ(X, U)` through
`AlgebraicGeometry.genericFiberChartSections`. -/
def genericFiberChartCoord :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)) :=
  genericFiberChartSections f hV hU e hx
    (generatorRatio _ (genericFiberChartOpens f hV hU e hx)
      (genericFiberChartGenerator f hV hU e hx L hL genU)
      (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx)))

/-- **The chart coordinate is a unit of `A ⊗_R K`.** Two generators of an invertible module on one
open differ by a unit, and a ring map carries a unit to a unit. This is the input that
`GenericFibreChart.lean` left unproved. -/
theorem isUnit_genericFiberChartCoord :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    IsUnit (genericFiberChartCoord f hV hU e hx L hgen hL genU) :=
  IsUnit.map (genericFiberChartSections f hV hU e hx)
    (isUnit_of_smul_eq_generator _ (genericFiberChartOpens f hV hU e hx)
      (genericFiberChartGenerator f hV hU e hx L hL genU)
      (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx)) _
      (generatorRatio_spec _ _ _ _))

/-- **The penultimate paragraph of [Stacks, Tag 0BD7] at a point, with the unit produced.** For a
flat `f` with integral fibres over an integral normal base, an affine chart `x ∈ U ≤ f ⁻¹ᵁ V` with
a generator of `ℒ` on `U`, and `ℒ_ξ` trivial, there are nonzero `g, r ∈ 𝒪_{Y, f x}` and a unit `u`
of `𝒪_{X, x}` with `r s = g u`, where `s` is the image of the chart coordinate. -/
theorem exists_isUnit_mul_eq_genericFiberChartCoord [Flat f]
    [IsIntegral X] [IsNormal Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hfib : ∀ y : Y, IsIntegral (f.fiber y)) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    letI : Algebra ↑(X.presheaf.stalk x)
        ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) :=
      Algebra.TensorProduct.rightAlgebra
    ∃ (g r : ↑(Y.presheaf.stalk (f x))) (u : ↑(X.presheaf.stalk x)),
      g ≠ 0 ∧ r ≠ 0 ∧ IsUnit u ∧
        algebraMap ↑(Y.presheaf.stalk (f x))
              ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) r
            * chartFiberBotToStalkFiberBot f hV e hx
                (genericFiberChartCoord f hV hU e hx L hgen hL genU) =
          algebraMap ↑(Y.presheaf.stalk (f x))
              ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) g
            * algebraMap ↑(X.presheaf.stalk x)
              ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) u :=
  exists_isUnit_mul_eq_of_isUnit_fiberBot_chart f hfib hV e hx _
    (isUnit_genericFiberChartCoord f hV hU e hx L hgen hL genU)

/-- **The penultimate paragraph of [Stacks, Tag 0BD7] at an arbitrary point of `X`.** Under the
tag's own hypotheses alone — `f` flat with integral fibres, `X` and `Y` integral and locally
Noetherian, `Y` normal, `ℒ` invertible, `ℒ_ξ` trivial — every point of `X` has an affine chart
carrying a generator of `ℒ`, and at it the paragraph's conclusion holds for the chart coordinate
of the trivializing section.

The chart is existentially quantified but the coordinate is not: it is
`AlgebraicGeometry.genericFiberChartCoord` of the chart that is produced, so the `s` of the
equation is the trivializing section of `ℒ_ξ` read there and not an unrelated unit. -/
theorem exists_chart_isUnit_mul_eq_of_isTrivial_genericFiber (g : X ⟶ Y) [Flat g]
    [IsIntegral X] [IsNormal Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (hM : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property M)
    (hfib : ∀ y : Y, IsIntegral (g.fiber y))
    (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
      (g.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (g.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (g.fiberι (genericPoint Y))).obj M))
    (z : X) :
    ∃ (V : Y.Opens) (U : X.Opens) (hV : IsAffineOpen V) (hU : IsAffineOpen U)
      (e : U ≤ g ⁻¹ᵁ V) (hz : z ∈ U) (genU : GeneratorSections X.toRingedSpace M U),
      letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (g.appLE V U e).hom.toAlgebra
      letI : Algebra ↑(Y.presheaf.stalk (g z)) ↑(X.presheaf.stalk z) :=
        (g.stalkMap z).hom.toAlgebra
      letI : Nonempty ↥(V.toScheme) := ⟨⟨g z, e hz⟩⟩
      letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
      letI : Algebra ↑(X.presheaf.stalk z)
          ((⊥ : Ideal ↑(Y.presheaf.stalk (g z))).Fiber ↑(X.presheaf.stalk z)) :=
        Algebra.TensorProduct.rightAlgebra
      ∃ (a r : ↑(Y.presheaf.stalk (g z))) (u : ↑(X.presheaf.stalk z)),
        a ≠ 0 ∧ r ≠ 0 ∧ IsUnit u ∧
          algebraMap ↑(Y.presheaf.stalk (g z))
                ((⊥ : Ideal ↑(Y.presheaf.stalk (g z))).Fiber ↑(X.presheaf.stalk z)) r
              * chartFiberBotToStalkFiberBot g hV e hz
                  (genericFiberChartCoord g hV hU e hz M hgen hM genU) =
            algebraMap ↑(Y.presheaf.stalk (g z))
                ((⊥ : Ideal ↑(Y.presheaf.stalk (g z))).Fiber ↑(X.presheaf.stalk z)) a
              * algebraMap ↑(X.presheaf.stalk z)
                ((⊥ : Ideal ↑(Y.presheaf.stalk (g z))).Fiber ↑(X.presheaf.stalk z)) u := by
  obtain ⟨V, U, hV, hU, e, hz, ⟨genU⟩⟩ := exists_affine_chart_generator_mem g M hM z
  exact ⟨V, U, hV, hU, e, hz, genU,
    exists_isUnit_mul_eq_genericFiberChartCoord g hV hU e hz M hgen hM genU hfib⟩

end AlgebraicGeometry

end

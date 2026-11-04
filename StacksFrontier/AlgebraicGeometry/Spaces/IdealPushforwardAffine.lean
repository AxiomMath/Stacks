module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction

/-!
# Projecting an ideal through an affine morphism of algebraic spaces

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `F` be an `𝒪_Y`-module on the small étale site of `Y` and let `I ⊆ 𝒪_X` be a
sheaf of ideals on the small étale site of `X`.  Multiplying the direct image `f_*F` by `I`
agrees with pushing forward the product of `F` by the inverse-image ideal `f⁻¹I`:

`I · f_*F = f_*((f⁻¹I) · F)`.

## Main definitions

* `AlgebraicGeometry.Space.chartSectionsRing` is the ring of regular functions on an étale
  chart, and `AlgebraicGeometry.Space.chartSectionsIdeal` the sections of a sheaf of ideals over
  one.
* `AlgebraicGeometry.Space.chartIdealPullbackHom` is the pullback of regular functions
  `𝒪_X(Q) ⟶ 𝒪_Y(Q ×_X Y)` along `f` over an étale chart `Q` of `X`, that is, the structure map
  of Stacks 03G8 for a representable morphism read on sections over one chart.
* `AlgebraicGeometry.Space.pushforwardIdealMultipleSections` is the ideal multiple `I · f_*F`
  of the direct image, on sections over an étale chart of `X`.
* `AlgebraicGeometry.Space.pullbackIdealMultipleSections` is the multiple of `F` by the
  inverse-image ideal, on sections over the base-changed chart of `Y`.

## Main results

* `AlgebraicGeometry.Space.ideal_smul_pushforward_sections_eq` identifies the two submodules
  sectionwise over every étale chart of `X`.  This is the chart-sections form of the identity
  of Stacks 0GF8.
* `AlgebraicGeometry.Space.ideal_smul_pushforward_sections_eq_of_representable` is the same
  identity for a representable morphism.
* `AlgebraicGeometry.Space.relativelyRepresentable_hom_of_isAffineHom`: an affine morphism of
  algebraic spaces is representable.
* `AlgebraicGeometry.Space.pushforwardChartModule_eq_pushforward`: the sections of the direct
  image over an étale chart of `X` are the sections of `F` over the base-changed chart, with
  the action of `𝒪_X` restricted along the structure map.
* `AlgebraicGeometry.Space.smul_mem_pushforwardIdealMultipleSections` and
  `AlgebraicGeometry.Space.smul_mem_pullbackIdealMultipleSections`: each of the two submodules
  contains the products `a · s`, on the left of a section `a` of `I` and a section of the direct
  image, on the right of its pullback and a section of `F`.

## References

* [Stacks Project, Tag 0GF8](https://stacks.math.columbia.edu/tag/0GF8)
* [Stacks Project, Tag 01YP](https://stacks.math.columbia.edu/tag/01YP)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe m u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- An affine morphism of algebraic spaces is representable. -/
theorem relativelyRepresentable_hom_of_isAffineHom (f : Y ⟶ X)
    (hf : IsAffineHom B S hS f.hom) : yoneda.relativelyRepresentable f.hom :=
  (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS Y.2 X.2 hf).1

/-- The ring `𝒪_Z(Q)` of regular functions on an étale chart `Q` of an algebraic space `Z`, as
the sections over `Q` of `AlgebraicGeometry.Space.smallEtaleRingSheaf`. -/
abbrev chartSectionsRing (Z : AlgebraicSpaces B S hS) (Q : SmallEtale B S hS Z.1) : Type u :=
  (smallEtaleRingSheaf B S hS Z.1 Z.2).obj.obj (op Q)

/-- Regular functions on an étale chart form a *commutative* ring, extending the ring structure
of `AlgebraicGeometry.Space.chartSectionsRing`. -/
instance chartSectionsRing_commRing (Z : AlgebraicSpaces B S hS) (Q : SmallEtale B S hS Z.1) :
    CommRing (chartSectionsRing B S hS Z Q) :=
  letI r : Ring (chartSectionsRing B S hS Z Q) := inferInstance
  { r with
    mul_comm := by
      change ∀ a b : (structureSheaf B S hS Z.1 Z.2).obj.obj (op Q), a * b = b * a
      exact fun a b => mul_comm a b }

/-- The sections over an étale chart `Q` of a sheaf of ideals `I ⊆ 𝒪_Z`, as an ideal of
`AlgebraicGeometry.Space.chartSectionsRing`. -/
abbrev chartSectionsIdeal (Z : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z.1 Z.2)).Submodule)
    (Q : SmallEtale B S hS Z.1) : Ideal (chartSectionsRing B S hS Z Q) :=
  I.obj (op Q)

/-- Pullback of regular functions along a representable `f : Y ⟶ X` over an étale chart `Q` of
`X`: the ring map `𝒪_X(Q) ⟶ 𝒪_Y(Q ×_X Y)` given by the structure map of Stacks 03G8. -/
def chartIdealPullbackHom (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
    (Q : SmallEtale B S hS X.1) :
    chartSectionsRing B S hS X Q →+*
      chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q) :=
  ((smallBaseChangeSharp B S hS f hf).hom.app (op Q)).hom

section

variable (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
  (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)
  (F : SheafOfModules.{m} (smallEtaleRingSheaf B S hS Y.1 Y.2))
  (Q : SmallEtale B S hS X.1)

/-- The `𝒪_X(Q)`-module structure on the sections of `F` over the base-changed chart `Q ×_X Y`,
by restriction of scalars along `f♯`. -/
@[instance_reducible]
def pushforwardChartModule :
    Module (chartSectionsRing B S hS X Q)
      (F.val.obj (op ((smallBaseChange B S hS f hf).obj Q))) :=
  Module.compHom _ (chartIdealPullbackHom B S hS f hf Q)

/-- The sections of the direct image `f_*F` over an étale chart `Q` of `X` are the sections of
`F` over the base-changed chart `Q ×_X Y`, with the `𝒪_X(Q)`-action of
`AlgebraicGeometry.Space.pushforwardChartModule`. -/
theorem pushforwardChartModule_eq_pushforward :
    pushforwardChartModule B S hS f hf F Q =
      (((smallBaseChangeModulePushforward B S hS f hf).obj F).val.obj (op Q)).isModule :=
  rfl

/-- The sections, over an étale chart `Q` of `X`, of the ideal multiple `I · f_*F` of the direct
image: the `𝒪_X(Q)`-submodule `I(Q) · (f_*F)(Q)` of `(f_*F)(Q)`. -/
def pushforwardIdealMultipleSections :
    Set (F.val.obj (op ((smallBaseChange B S hS f hf).obj Q))) :=
  letI := pushforwardChartModule B S hS f hf F Q
  ↑(chartSectionsIdeal B S hS X I Q •
    (⊤ : Submodule (chartSectionsRing B S hS X Q)
      (F.val.obj (op ((smallBaseChange B S hS f hf).obj Q)))))

/-- The sections, over the base-changed chart `Q ×_X Y` of `Y`, of the multiple of `F` by the
inverse-image ideal: the `𝒪_Y(Q ×_X Y)`-multiple of `F(Q ×_X Y)` by the ideal generated by the
pulled-back sections of `I` over `Q`. -/
def pullbackIdealMultipleSections :
    Set (F.val.obj (op ((smallBaseChange B S hS f hf).obj Q))) :=
  ↑(Ideal.map (chartIdealPullbackHom B S hS f hf Q) (chartSectionsIdeal B S hS X I Q) •
    (⊤ : Submodule (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q))
      (F.val.obj (op ((smallBaseChange B S hS f hf).obj Q)))))

/-- The ideal multiple of the direct image contains the products `a · s` of a section `a` of `I`
over the chart with a section `s` of the direct image. -/
theorem smul_mem_pushforwardIdealMultipleSections
    {a : chartSectionsRing B S hS X Q} (ha : a ∈ chartSectionsIdeal B S hS X I Q)
    (s : F.val.obj (op ((smallBaseChange B S hS f hf).obj Q))) :
    letI := pushforwardChartModule B S hS f hf F Q
    a • s ∈ pushforwardIdealMultipleSections B S hS f hf I F Q :=
  let := pushforwardChartModule B S hS f hf F Q
  Submodule.smul_mem_smul ha Submodule.mem_top

/-- The inverse-image ideal multiple contains the products `f♯(a) · s` of the pullback of a
section `a` of `I` over the chart with a section `s` of `F`. -/
theorem smul_mem_pullbackIdealMultipleSections
    {a : chartSectionsRing B S hS X Q} (ha : a ∈ chartSectionsIdeal B S hS X I Q)
    (s : F.val.obj (op ((smallBaseChange B S hS f hf).obj Q))) :
    chartIdealPullbackHom B S hS f hf Q a • s ∈
      pullbackIdealMultipleSections B S hS f hf I F Q :=
  Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top

/-- The ideal multiple of the direct image and the inverse-image ideal multiple agree on
sections over every étale chart, for any *representable* morphism. -/
theorem ideal_smul_pushforward_sections_eq_of_representable :
    pushforwardIdealMultipleSections B S hS f hf I F Q =
      pullbackIdealMultipleSections B S hS f hf I F Q := by
  let _ : Algebra (chartSectionsRing B S hS X Q)
      (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q)) :=
    (chartIdealPullbackHom B S hS f hf Q).toAlgebra
  let _ := pushforwardChartModule B S hS f hf F Q
  have _ : IsScalarTower (chartSectionsRing B S hS X Q)
      (chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q))
      (F.val.obj (op ((smallBaseChange B S hS f hf).obj Q))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h := Submodule.restrictScalars_map_smul_eq
    (S := chartSectionsRing B S hS X Q)
    (R := chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q))
    (M := F.val.obj (op ((smallBaseChange B S hS f hf).obj Q)))
    (chartSectionsIdeal B S hS X I Q) ⊤
  rw [Submodule.restrictScalars_top] at h
  exact congrArg SetLike.coe h.symm

end

section

variable (f : Y ⟶ X) (haff : IsAffineHom B S hS f.hom)
  (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)
  (F : SheafOfModules.{m} (smallEtaleRingSheaf B S hS Y.1 Y.2))
  (Q : SmallEtale B S hS X.1)

/-- **The chart-sections form of Stacks 0GF8.**  Let `S` be a scheme, let `f : Y ⟶ X` be a
morphism of algebraic spaces over `S`, let `F` be a sheaf of modules on `Y` and let
`I ⊆ 𝒪_X` be a sheaf of ideals on `X`.  If `f` is affine then

`I · f_*F = f_*((f⁻¹I) · F)`.

The inverse-image ideal `f⁻¹I` is a sheaf of ideals of `f⁻¹𝒪_X`, and it acts on `F` through the
structure map `f♯ : f⁻¹𝒪_X ⟶ 𝒪_Y` of Stacks 03G8; the product `f⁻¹I · F` is generated by the
local products `a · s` with `a` a local section of `f⁻¹I` and `s` a local section of `F`, and
`I · f_*F` is the analogous product on `X`.

The equality is stated on sections over every étale chart `Q` of `X`. -/
theorem ideal_smul_pushforward_sections_eq :
    pushforwardIdealMultipleSections B S hS f
        (relativelyRepresentable_hom_of_isAffineHom B S hS f haff) I F Q =
      pullbackIdealMultipleSections B S hS f
        (relativelyRepresentable_hom_of_isAffineHom B S hS f haff) I F Q :=
  ideal_smul_pushforward_sections_eq_of_representable B S hS f _ I F Q

end

end AlgebraicGeometry.Space

end

end

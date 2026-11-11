module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningDifferentialsIso
import StacksCore.Tactic.StacksAttribute

/-!
# Differentials of the universal first-order thickening of a formally unramified morphism

Let `h : Z ⟶ X` be a formally unramified morphism of algebraic spaces over `S`, let `Z ⊂ Z'` be
its universal first-order thickening, with structure morphism `h' : Z' ⟶ X` and closed immersion
`i : Z ⟶ Z'`, and let `p : X ⟶ Y` be a morphism to a base algebraic space.  Stacks 060E says
that the canonical map `dh' : (h')^*Ω_{X/Y} ⟶ Ω_{Z'/Y}` of Stacks 04CX induces an isomorphism
`h^*Ω_{X/Y} ⟶ Ω_{Z'/Y} ⊗ 𝒪_Z`.

The thickening is the library's Stacks 0607 datum
`AlgebraicGeometry.Space.UniversalFirstOrderThickening`, which exists for every formally
unramified morphism by Stacks 0606,
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`.
This file states the tag in that shape, with source the inverse image along `h` itself, and
derives it from `IsUniversalFirstOrderThickening.isIso_restrict_of_isSheafOfDifferentialsMap`
of `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningDifferentialsIso.lean`, which states
it for the smaller space of the thickening read as a subfunctor of `Z'`.  The passage between the
two is the identification of `Z` with that subfunctor, an isomorphism, and the comparison
`i^*(h')^* ≅ (i ≫ h')^*` of Stacks 03LU.

## Main definitions

* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.sourceToAmbient`: the closed immersion
  `i : Z ⟶ Z'`.
* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.pullbackSheafOfDifferentialsIso`: the
  isomorphism `h^*Ω_{X/Y} ≅ Ω_{Z'/Y} ⊗ 𝒪_Z` of Stacks 060E.
* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.pullbackSheafOfDifferentialsMap`: its
  forward map, the map of Stacks 060E.

## Main results

In the namespace `AlgebraicGeometry.Space.UniversalFirstOrderThickening`:

* `isIso_modulePullback_map_of_isSheafOfDifferentialsMap`: **Stacks 060E**, `i^*c` is an
  isomorphism for any realization `c` of the map of Stacks 04CX.
* `isIso_pullbackSheafOfDifferentialsMap`: **Stacks 060E**, the map
  `h^*Ω_{X/Y} ⟶ Ω_{Z'/Y} ⊗ 𝒪_Z` is an isomorphism.

## References

* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

namespace UniversalFirstOrderThickening

variable {W : AlgebraicSpaces B S hS} {h : W ⟶ X}

/-- The identification of `Z` with the smaller space of the universal first-order thickening `t`
of `h : Z ⟶ X`, as a morphism to the algebraic space
`AlgebraicGeometry.Space.universalThickeningSubSpace` of `t`. -/
abbrev sourceToSubSpace (t : UniversalFirstOrderThickening B S hS h) :
    W ⟶ universalThickeningSubSpace B S hS t.isUniversal :=
  ObjectProperty.homMk t.sourceIso.hom

/-- The closed immersion `i : Z ⟶ Z'` of the universal first-order thickening `t` of a formally
unramified morphism `h : Z ⟶ X`: the identification of `Z` with the smaller space of `t`,
followed by the inclusion of that smaller space into the ambient space `Z'`. -/
abbrev sourceToAmbient (t : UniversalFirstOrderThickening B S hS h) : W ⟶ t.ambient :=
  t.sourceToSubSpace ≫ universalThickeningInclusion B S hS t.isUniversal

/-- The closed immersion `i : Z ⟶ Z'` followed by the structure morphism `h' : Z' ⟶ X` of the
universal first-order thickening of `h` is `h`. -/
theorem sourceToAmbient_comp_toBase (t : UniversalFirstOrderThickening B S hS h) :
    t.sourceToAmbient ≫ t.toBase = h :=
  ObjectProperty.hom_ext _ (by
    change (t.sourceIso.hom ≫ t.sub.ι) ≫ t.toBase.hom = h.hom
    rw [Category.assoc]
    exact t.sourceIso_ι_toBase)

/-- **Stacks 060E.**  Let `h : Z ⟶ X` be a formally unramified morphism of algebraic spaces over
`S`, let `Z ⊂ Z'` be its universal first-order thickening `t`, with structure morphism
`h' : Z' ⟶ X` and closed immersion `i : Z ⟶ Z'`, and let `p : X ⟶ Y` be a morphism to a base
algebraic space.  For any realization `c` of the canonical map
`dh' : (h')^*Ω_{X/Y} ⟶ Ω_{Z'/Y}` of Stacks 04CX, the restriction `i^*c` is an isomorphism; its
source is `h^*Ω_{X/Y}` through `i ≫ h' = h`, and its target is `Ω_{Z'/Y} ⊗ 𝒪_Z`. -/
@[stacks 060E]
theorem isIso_modulePullback_map_of_isSheafOfDifferentialsMap
    (t : UniversalFirstOrderThickening B S hS h) (p : X ⟶ Y)
    {c : (modulePullback B S hS t.toBase).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS (t.toBase ≫ p)}
    (hc : IsSheafOfDifferentialsMap B S hS t.toBase p (t.toBase ≫ p) c) :
    IsIso ((modulePullback B S hS t.sourceToAmbient).map c) := by
  have h₀ := t.isUniversal.isIso_restrict_of_isSheafOfDifferentialsMap B S hS p hc
  have h₁ : IsIso ((modulePullback B S hS t.sourceToSubSpace).map
      ((modulePullback B S hS (universalThickeningInclusion B S hS t.isUniversal)).map c)) :=
    Functor.map_isIso _ _
  have h₂ : IsIso ((modulePullback B S hS (universalThickeningInclusion B S hS t.isUniversal) ⋙
      modulePullback B S hS t.sourceToSubSpace).map c) := by
    rw [Functor.comp_map]
    exact h₁
  exact (NatIso.isIso_map_iff (modulePullbackCompIso B S hS t.sourceToSubSpace
    (universalThickeningInclusion B S hS t.isUniversal)) c).1 h₂

/-- The comparison map `c_{h'} = dh' : (h')^*Ω_{X/Y} ⟶ Ω_{Z'/Y}` of Stacks 04CX for the
universal first-order thickening `t` of `h`, restricted along the closed immersion
`i : Z ⟶ Z'`, is an isomorphism. -/
instance isIso_modulePullback_map_sheafOfDifferentialsMap
    (t : UniversalFirstOrderThickening B S hS h) (p : X ⟶ Y) :
    IsIso ((modulePullback B S hS t.sourceToAmbient).map
      (sheafOfDifferentialsMap B S hS t.toBase p (t.toBase ≫ p) (𝟙 Y)
        (Category.comp_id (t.toBase ≫ p)).symm)) :=
  t.isIso_modulePullback_map_of_isSheafOfDifferentialsMap p
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS t.toBase p (t.toBase ≫ p) (𝟙 Y)
      (Category.comp_id (t.toBase ≫ p)).symm)

/-- The isomorphism `h^*Ω_{X/Y} ≅ Ω_{Z'/Y} ⊗ 𝒪_Z` of Stacks 060E, for the universal first-order
thickening `t` of `h : Z ⟶ X`: the identification `h^*Ω_{X/Y} = i^*(h')^*Ω_{X/Y}` coming from
`i ≫ h' = h` (Stacks 03LU), followed by the restriction `i^*c_{h'}` along the closed immersion
`i : Z ⟶ Z'` of the comparison map `c_{h'} = dh'` of Stacks 04CX. -/
noncomputable def pullbackSheafOfDifferentialsIso
    (t : UniversalFirstOrderThickening B S hS h) (p : X ⟶ Y) :
    (modulePullback B S hS h).obj (sheafOfDifferentials B S hS p) ≅
      (modulePullback B S hS t.sourceToAmbient).obj
        (sheafOfDifferentials B S hS (t.toBase ≫ p)) :=
  eqToIso (congrArg (fun f ↦ (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p))
      t.sourceToAmbient_comp_toBase.symm) ≪≫
    ((modulePullbackCompIso B S hS t.sourceToAmbient t.toBase).app
      (sheafOfDifferentials B S hS p)).symm ≪≫
    asIso ((modulePullback B S hS t.sourceToAmbient).map
      (sheafOfDifferentialsMap B S hS t.toBase p (t.toBase ≫ p) (𝟙 Y)
        (Category.comp_id (t.toBase ≫ p)).symm))

/-- The map `h^*Ω_{X/Y} ⟶ Ω_{Z'/Y} ⊗ 𝒪_Z` of Stacks 060E induced by `dh'`: the forward map of
`AlgebraicGeometry.Space.UniversalFirstOrderThickening.pullbackSheafOfDifferentialsIso`, that is
the identification `h^*Ω_{X/Y} = i^*(h')^*Ω_{X/Y}` followed by `i^*c_{h'}`. -/
noncomputable def pullbackSheafOfDifferentialsMap
    (t : UniversalFirstOrderThickening B S hS h) (p : X ⟶ Y) :
    (modulePullback B S hS h).obj (sheafOfDifferentials B S hS p) ⟶
      (modulePullback B S hS t.sourceToAmbient).obj
        (sheafOfDifferentials B S hS (t.toBase ≫ p)) :=
  (t.pullbackSheafOfDifferentialsIso p).hom

/-- **Stacks 060E.**  Let `h : Z ⟶ X` be a formally unramified morphism of algebraic spaces over
`S` and `Z ⊂ Z'` its universal first-order thickening `t`, with structure morphism
`h' : Z' ⟶ X`.  For a morphism `p : X ⟶ Y` to a base algebraic space, the canonical map
`dh' : (h')^*Ω_{X/Y} ⟶ Ω_{Z'/Y}` induces an isomorphism `h^*Ω_{X/Y} ⟶ Ω_{Z'/Y} ⊗ 𝒪_Z`. -/
@[stacks 060E]
theorem isIso_pullbackSheafOfDifferentialsMap
    (t : UniversalFirstOrderThickening B S hS h) (p : X ⟶ Y) :
    IsIso (t.pullbackSheafOfDifferentialsMap p) :=
  (t.pullbackSheafOfDifferentialsIso p).isIso_hom

end UniversalFirstOrderThickening

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Derived

/-!
# Morphisms of compactifications and base change

Morphisms between base changes of compactifications, used to compare base change maps of
`Rf_!` computed through different compactifications ([Stacks, Tag 0F7L]).

## Main definitions

* `AlgebraicGeometry.CompactificationOf.baseChangeHom`: the base change of a morphism of
  compactifications.
* `AlgebraicGeometry.CompactificationOf.toBaseChange`: the morphism from a compactification of the
  base change into the base change of a compactification, given a map of ambient schemes
  compatible with the immersions and the structure morphisms.
* `AlgebraicGeometry.CompactificationOf.withImmersion`: the same compactification with its open
  immersion replaced by an equal morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  (sq : IsPullback g' f' f g)

/-- The morphism `X̄₁ ×_Y Y' ⟶ X̄₂ ×_Y Y'` induced by a morphism of compactifications. -/
noncomputable abbrev baseChangeMap {j₁ j₂ : CompactificationOf (Over.mk f)} (ψ : j₁ ⟶ j₂) :
    pullback j₁.toBase g ⟶ pullback j₂.toBase g :=
  pullback.map j₁.toBase g j₂.toBase g (Hom.map ψ) (𝟙 Y') (𝟙 Y)
    (by rw [map_comp_toBase, Category.comp_id]) (by rw [Category.id_comp, Category.comp_id])

/-- **The base change of a morphism of compactifications**: a morphism `ψ : j₁ ⟶ j₂` of
compactifications of `X` over `Y` induces `X̄₁ ×_Y Y' ⟶ X̄₂ ×_Y Y'`, a morphism of the base
changes. -/
noncomputable def baseChangeHom {j₁ j₂ : CompactificationOf (Over.mk f)} (ψ : j₁ ⟶ j₂) :
    j₁.baseChange sq ⟶ j₂.baseChange sq :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk (baseChangeMap (g := g) ψ) (by simp))
    (by
      apply Over.OverMorphism.ext
      change baseChangeImmersion sq j₁ ≫ baseChangeMap (g := g) ψ = baseChangeImmersion sq j₂
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, baseChangeImmersion_fst_assoc,
          baseChangeImmersion_fst, immersion_comp_map]
      · rw [Category.assoc, pullback.lift_snd, baseChangeImmersion_snd_assoc,
          baseChangeImmersion_snd, Category.comp_id]))

/-- The ambient morphism of `baseChangeHom` lies over the ambient morphism of `ψ`. -/
lemma baseChangeHom_map_fst {j₁ j₂ : CompactificationOf (Over.mk f)} (ψ : j₁ ⟶ j₂) :
    Hom.map (baseChangeHom sq ψ) ≫ pullback.fst j₂.toBase g =
      pullback.fst j₁.toBase g ≫ Hom.map ψ :=
  pullback.lift_fst _ _ _

/-- **A compactification of the base change maps to the base change of a compactification**:
for a compactification `j'` of `X'` over `Y'` and `φ : X̄' ⟶ X̄` compatible with the open
immersions and with the structure morphisms, the morphism `X̄' ⟶ X̄ ×_Y Y'` with components `φ`
and the structure morphism of `j'`. -/
noncomputable def toBaseChange (j : CompactificationOf (Over.mk f))
    (j' : CompactificationOf (Over.mk f')) (φ : j'.space ⟶ j.space)
    (hφ : j'.immersion ≫ φ = g' ≫ j.immersion) (w : j'.toBase ≫ g = φ ≫ j.toBase) :
    j' ⟶ j.baseChange sq :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk (pullback.lift φ j'.toBase w.symm) (pullback.lift_snd _ _ _))
    (by
      apply Over.OverMorphism.ext
      change j'.immersion ≫ pullback.lift φ j'.toBase w.symm = baseChangeImmersion sq j
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hφ, baseChangeImmersion_fst]
      · rw [Category.assoc, pullback.lift_snd, baseChangeImmersion_snd, immersion_toBase]))

/-- The ambient morphism of `toBaseChange` lies over `φ`. -/
lemma toBaseChange_map_fst (j : CompactificationOf (Over.mk f))
    (j' : CompactificationOf (Over.mk f')) (φ : j'.space ⟶ j.space)
    (hφ : j'.immersion ≫ φ = g' ≫ j.immersion) (w : j'.toBase ≫ g = φ ≫ j.toBase) :
    Hom.map (toBaseChange sq j j' φ hφ w) ≫ pullback.fst j.toBase g = φ :=
  pullback.lift_fst _ _ _

end AlgebraicGeometry.CompactificationOf

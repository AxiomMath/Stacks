module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallySmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative differentials and étale localization

For a commutative square of schemes

```
X₁ <--f-- X₂
|         |
p₁        p₂
v         v
S₁ <--g-- S₂
```

whose two horizontal arrows are étale, the canonical map `f^* Ω_{X₁/S₁} ⟶ Ω_{X₂/S₂}` is an
isomorphism: the sheaf of relative differentials is insensitive to étale localization of the
source and of the base.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_comp`: for a composable pair
  with the first morphism étale, the canonical map `f^* Ω_{Y/S} ⟶ Ω_{X/S}` is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isIso_toRelativeDifferentials_of_etale`: for a composable pair
  with the second morphism étale, the canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_etale`: **Stacks Project,
  Tag 04BX.** For a commutative square whose two horizontal arrows are étale, the canonical map
  `f^* Ω_{X₁/S₁} ⟶ Ω_{X₂/S₂}` is an isomorphism.

## References

* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-- An étale morphism of schemes is formally smooth. -/
@[ega "IV 17.14.1" "partial",
  sga "3 III 0.16" "special case",
  sga "3 III 0.17" "special case",
  sga "3 XV 1.1" "special case"]
private theorem formallySmooth_of_etale (f : X ⟶ Y) [Etale f] : FormallySmooth f :=
  Stacks.Smooth.formallySmoothScheme_of_smooth f

/-- For a composable pair `X ⟶ Y ⟶ S` whose first morphism is étale, the canonical map
`f^* Ω_{Y/S} ⟶ Ω_{X/S}` is an isomorphism. -/
@[ega "IV 17.2.4" "special case", sga "1 II 4.1", sga "6 VIII 5.2" "Clause"]
theorem isIso_relativeDifferentialsMap_of_comp (f : X ⟶ Y) (g : Y ⟶ S) [Etale f] :
    IsIso (relativeDifferentialsMap f g (f ≫ g) (𝟙 S) (Category.comp_id (f ≫ g)).symm) := by
  obtain ⟨hc, hshort⟩ := toRelativeDifferentials_shortExact f g (formallySmooth_of_etale f)
  exact hshort.isIso_f_iff.2 (isZero_relativeDifferentials_of_formallyUnramified f)

/-- For a composable pair `X ⟶ Y ⟶ S` whose second morphism is étale, the canonical map
`Ω_{X/S} ⟶ Ω_{X/Y}` is an isomorphism. -/
theorem isIso_toRelativeDifferentials_of_etale (f : X ⟶ Y) (g : Y ⟶ S) [Etale g] :
    IsIso (f.toRelativeDifferentials g) := by
  obtain ⟨hc, hexact⟩ := toRelativeDifferentials_exact f g
  have hzero : IsZero ((Scheme.Modules.pullback f).obj (relativeDifferentials g)) :=
    Functor.map_isZero _ (isZero_relativeDifferentials_of_formallyUnramified g)
  have hmono : Mono (f.toRelativeDifferentials g) :=
    ((ShortComplex.mk _ _ hc).exact_iff_mono (hzero.eq_of_src _ _)).mp hexact
  have := toRelativeDifferentials_epi f g
  exact isIso_of_mono_of_epi _

/-- The canonical map of a commutative square whose source morphism is the identity and whose
base morphism is étale is an isomorphism. -/
theorem isIso_relativeDifferentialsMap_id_of_etale {S₁ S₂ : Scheme.{u}} (q : X ⟶ S₁)
    (p : X ⟶ S₂) (g : S₂ ⟶ S₁) (hq : q = p ≫ g) [Etale g] (hcomm : 𝟙 X ≫ q = p ≫ g) :
    IsIso (relativeDifferentialsMap (𝟙 X) q p g hcomm) := by
  subst hq
  have : IsIso ((Scheme.Modules.pullbackId X).inv.app (relativeDifferentials (p ≫ g)) ≫
      relativeDifferentialsMap (𝟙 X) (p ≫ g) p g hcomm) :=
    isIso_toRelativeDifferentials_of_etale p g
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.pullbackId X).inv.app _) _

/-- The canonical maps of two squares stacked horizontally compose to the canonical map of the
outer square, in the form of the defining compatibility: the composite of `a` and `b`, read
through the component of the isomorphism identifying the pullback along an identity with the
identity functor, is compatible with the universal derivations of the outer square. -/
theorem isRelativeDifferentialsMap_comp_id {X' S' : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S)
    (p' : X' ⟶ S')
    (a : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶
      relativeDifferentials (f ≫ p))
    (b : (Scheme.Modules.pullback (𝟙 X')).obj (relativeDifferentials (f ≫ p)) ⟶
      relativeDifferentials p')
    (ha : IsRelativeDifferentialsMap f p (f ≫ p) a)
    (hb : IsRelativeDifferentialsMap (𝟙 X') (f ≫ p) p' b) :
    IsRelativeDifferentialsMap f p p'
      (a ≫ ((Scheme.Modules.pullbackId X').inv.app (relativeDifferentials (f ≫ p)) ≫ b)) :=
  isRelativeDifferentialsMap_comp f p (f ≫ p) p' a b ha hb

/-- **Stacks Project, Tag 04BX.** In a commutative square of schemes whose two horizontal
arrows `f : X₂ ⟶ X₁` and `g : S₂ ⟶ S₁` are étale, the canonical map
`f^* Ω_{X₁/S₁} ⟶ Ω_{X₂/S₂}` is an isomorphism. -/
@[stacks 04BX]
theorem isIso_relativeDifferentialsMap_of_etale {X₁ X₂ S₁ S₂ : Scheme.{u}} (f : X₂ ⟶ X₁)
    (p₁ : X₁ ⟶ S₁) (p₂ : X₂ ⟶ S₂) (g : S₂ ⟶ S₁) (hcomm : f ≫ p₁ = p₂ ≫ g)
    [Etale f] [Etale g] :
    IsIso (relativeDifferentialsMap f p₁ p₂ g hcomm) := by
  have := isIso_relativeDifferentialsMap_of_comp f p₁
  have := isIso_relativeDifferentialsMap_id_of_etale (f ≫ p₁) p₂ g hcomm
    ((Category.id_comp _).trans hcomm)
  rw [← relativeDifferentialsMap_comp f p₁ (f ≫ p₁) p₂ g rfl hcomm]
  infer_instance

end AlgebraicGeometry.Scheme.Hom

end

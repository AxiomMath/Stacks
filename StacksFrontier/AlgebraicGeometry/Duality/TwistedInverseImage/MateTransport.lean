module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousCompCoherence
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionExtra

/-!
# Transporting a mate along an isomorphism of right adjoints

`CategoryTheory.mateEquiv` turns a two-square of left adjoints into one of right adjoints. The
right adjoint of an adjunction is only determined up to canonical isomorphism, so a mate computed
from one presentation of it has to be compared with the mate computed from another. This file
records that comparison: replacing either adjunction by its transport along an isomorphism of its
right adjoint whiskers the mate, and changes it in no other way.

The application is [Stacks, Tag 0ATQ]. There the transformation `ξ` of [Stacks, Tag 0A9K] for a
cartesian square is a mate under the two adjunctions `Rf_* ⊣ f^×` and `Rf'_* ⊣ (f')^×` of
[Stacks, Tag 0A9E] — see
`Stacks.Duality.twistedInverseImageBaseChangeMap_eq_mateEquiv_symm` — and the identity
`ξ_rect = ξ_bot ≫ₕ ξ_top` for a vertical stack of two cartesian squares is
`CategoryTheory.mateEquiv_hcomp`. But `mateEquiv_hcomp` delivers the mate under the *composite*
adjunction `CategoryTheory.Adjunction.comp`, whose right adjoint is `g^× ⋙ f^×`, whereas the
rectangle's own `ξ` is the mate under `Stacks.Duality.twistedInverseImageAdjunction (f ≫ g)`,
whose right adjoint is `(f ≫ g)^×`. The isomorphism between the two is the comparison of
[Stacks, Tag 0ATX], and `twistedInverseImageAdjunction_eq_ofNatIsoRight` below says that the
second adjunction *is* the first transported along it — so the two lemmas here are exactly what
bridges the gap.

## Main results

* `CategoryTheory.mateEquiv_ofNatIsoRight_bot` and
  `CategoryTheory.mateEquiv_ofNatIsoRight_top` — transporting the bottom, resp. the top,
  adjunction of the square along an isomorphism of its right adjoint post-, resp. pre-composes
  the mate with that isomorphism whiskered.
* `Stacks.Duality.twistedInverseImageAdjunction_eq_ofNatIsoRight` — the adjunction
  `R(f ≫ g)_* ⊣ (f ≫ g)^×` is the composite adjunction `R(f ≫ g)_* ⊣ g^× ⋙ f^×` of
  `Stacks.Duality.twistedInverseImageCompAdjunction` read through the comparison of
  [Stacks, Tag 0ATX].

## Implementation notes

`CategoryTheory.Adjunction.ofNatIsoRight` changes the unit by `whiskerLeft` of the isomorphism
and the counit by `whiskerRight` of its inverse, and `CategoryTheory.mateEquiv` uses the unit of
the bottom adjunction and the counit of the top one. So the bottom transport is a plain
post-composition, while the top transport needs the naturality of the unit of the bottom
adjunction and of the two-square itself to move the isomorphism past them; that is the only
difference between the two proofs.

`twistedInverseImageAdjunction_eq_ofNatIsoRight` is
`CategoryTheory.Adjunction.eq_ofNatIsoRight_of_conjugateEquiv_id` together with
`CategoryTheory.Adjunction.rightAdjointUniq_hom_eq_conjugateEquiv`: the comparison of
[Stacks, Tag 0ATX] is by construction a `CategoryTheory.Adjunction.rightAdjointUniq`, whose
underlying map is the mate of the identity, which is what that lemma asks for.

## References

* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ R₁' : D ⥤ C} {L₂ : E ⥤ F} {R₂ R₂' : F ⥤ E}

/-- **Transporting the bottom adjunction of a square along an isomorphism of its right adjoint
post-composes the mate.** For `adj₁ : L₁ ⊣ R₁`, `adj₂ : L₂ ⊣ R₂` and `e : R₂ ≅ R₂'`, the mate of
a two-square taken with `adj₂` read through `e` is its mate taken with `adj₂`, followed by `e`
whiskered by `H`. -/
theorem mateEquiv_ofNatIsoRight_bot (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₂ ≅ R₂')
    (α : TwoSquare G L₁ L₂ H) :
    mateEquiv adj₁ (adj₂.ofNatIsoRight e) α =
      TwoSquare.mk _ _ _ _
        (mateEquiv adj₁ adj₂ α ≫ Functor.whiskerLeft H e.hom) := by
  ext X
  simp [mateEquiv, Adjunction.ofNatIsoRight]

/-- **Transporting the top adjunction of a square along an isomorphism of its right adjoint
pre-composes the mate.** For `adj₁ : L₁ ⊣ R₁`, `adj₂ : L₂ ⊣ R₂` and `e : R₁ ≅ R₁'`, the mate of a
two-square taken with `adj₁` read through `e` is `e.inv` whiskered by `G`, followed by its mate
taken with `adj₁`. -/
theorem mateEquiv_ofNatIsoRight_top (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₁')
    (α : TwoSquare G L₁ L₂ H) :
    mateEquiv (adj₁.ofNatIsoRight e) adj₂ α =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerRight e.inv G ≫ mateEquiv adj₁ adj₂ α) := by
  ext X
  have h1 := adj₂.unit.naturality (G.map (e.inv.app X))
  have h2 := α.naturality (e.inv.app X)
  simp only [Functor.id_map, Functor.comp_map] at h1 h2
  have key : G.map (e.inv.app X) ≫ adj₂.unit.app (G.obj (R₁.obj X)) ≫
        R₂.map (α.app (R₁.obj X)) =
      adj₂.unit.app (G.obj (R₁'.obj X)) ≫ R₂.map (α.app (R₁'.obj X)) ≫
        R₂.map (H.map (L₁.map (e.inv.app X))) := by
    rw [← Category.assoc, h1, Category.assoc, ← R₂.map_comp, h2, R₂.map_comp]
  simpa [mateEquiv, Adjunction.ofNatIsoRight] using
    congrArg (· ≫ R₂.map (H.map (adj₁.counit.app X))) key.symm

end CategoryTheory

namespace Stacks.Duality

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpushfg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (f ≫ g)).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward g hpushg).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (f ≫ g) hpushfg).IsLeftAdjoint]

/-- **The adjunction exhibiting `(f ≫ g)^×` is the composite adjunction read through the
comparison of [Stacks, Tag 0ATX].** Both `(f ≫ g)^×` and `g^× ⋙ f^×` are right adjoints of the
restricted derived direct image along `f ≫ g`; the comparison
`Stacks.Duality.twistedInverseImageCompIso` is the uniqueness isomorphism between them, and the
adjunction for `(f ≫ g)^×` is the one for `g^× ⋙ f^×` transported along it.

This is what lets a mate computed under the composite adjunction — which is what
`CategoryTheory.mateEquiv_hcomp` produces for a horizontal composite of two-squares — be compared
with a mate computed under `Stacks.Duality.twistedInverseImageAdjunction (f ≫ g)`, through
`CategoryTheory.mateEquiv_ofNatIsoRight_bot` and
`CategoryTheory.mateEquiv_ofNatIsoRight_top`. -/
theorem twistedInverseImageAdjunction_eq_ofNatIsoRight :
    twistedInverseImageAdjunction (f ≫ g) hpushfg =
      (twistedInverseImageCompAdjunction f g hpushf hpushg hpushfg).ofNatIsoRight
        (twistedInverseImageCompIso f g hpushf hpushg hpushfg).symm :=
  Adjunction.eq_ofNatIsoRight_of_conjugateEquiv_id
    (twistedInverseImageCompAdjunction f g hpushf hpushg hpushfg)
    (twistedInverseImageAdjunction (f ≫ g) hpushfg)
    (twistedInverseImageCompIso f g hpushf hpushg hpushfg).symm rfl

end Stacks.Duality

end

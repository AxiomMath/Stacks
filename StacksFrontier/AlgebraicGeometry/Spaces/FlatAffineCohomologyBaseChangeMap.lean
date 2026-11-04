module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeGlobalSectionsRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CommRing
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison map of Stacks 073K, part (2)

For the cartesian square of **Stacks 073J**

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

with `Y = Spec(A)` and `Y' = Spec(B)` affine and `g` flat, **Stacks 073K, part (2)** asserts
that `H^i(X, 𝓕) ⊗_A B = H^i(X', 𝓕')`.  This file forms that comparison map.

The two sides are modules over `B = Γ(Y', 𝒪_{Y'})`: the right hand side through `f'`, and the
left hand side because it is the extension of scalars along `A = Γ(Y, 𝒪_Y) ⟶ B` of
`H^i(X, 𝓕)` read over `A` through `f`.  The map itself is the pullback map on cohomology along
`g'` of `AlgebraicGeometry.Space.cohomologyPullbackMap` — which is available because `g'` is
flat and affine, both inherited from `g` across the square — read over `A` and then transposed
across the adjunction between extension and restriction of scalars.  That transposition is
exactly where the commuting square of global function rings
`AlgebraicGeometry.Space.BaseChangeDiagram.globalSectionsRingHomSite_sq` enters: it is what
identifies the `A`-module `H^i(X', 𝓕')` obtained through `g'` and `f` with the one obtained
through `f'` and `g`.

## Main definitions

* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologySource` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyTarget`: the two sides
  `H^i(X, 𝓕) ⊗_A B` and `H^i(X', 𝓕')` of part (2), as `Γ(Y', 𝒪_{Y'})`-modules.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap`: **the comparison
  map of part (2)**, `H^i(X, 𝓕) ⊗_A B ⟶ H^i(X', 𝓕')`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_isAffineSpace`: a morphism of affine algebraic spaces
  is an affine morphism.
* `AlgebraicGeometry.Space.BaseChangeDiagram.isAffineHom_g'` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.isFlat_g'`: for affine `Y` and `Y'` and flat `g`,
  the projection `g'` is affine and flat, which is what makes the pullback map on cohomology
  along it exist.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_adjoint`: **the
  comparison map is the scalar extension of the pullback map on cohomology along `g'`.**  Its
  transpose across the adjunction is that pullback map, read over `Γ(Y, 𝒪_Y)` and across the
  square of global function rings.  Since the transposition is a bijection this equation
  determines the map.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_eq`: the same
  equation written out — the comparison map is the extension of scalars of that pullback map
  followed by the counit of the adjunction.

## Implementation notes

*Why `Γ(Y, 𝒪_Y)` and not `A`.*  The coordinate ring of an affine algebraic space `Y` is its
ring of global regular functions, so `A` and `B` of the source are
`Stacks.Cohomology.SiteModules.GlobalSectionRing` of the structure sheaves of `Y` and `Y'`, and
the ring map `A ⟶ B` is `AlgebraicGeometry.Space.globalSectionsRingHomSite` of `g`.  The
affineness of `Y` and `Y'` is carried as the hypotheses it is in the source, and is used for
exactly one thing: it is what makes `g`, and hence `g'`, an affine morphism, which is what the
pullback map on cohomology of
`StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback` requires.

*Commutativity of the scalars.*  Extension of scalars is defined only between commutative
rings, and `Γ(Y, 𝒪_Y) = RingCat.sectionsSubring _` is commutative only by a lemma, the sheaf of
rings over which modules are taken being the structure sheaf with commutativity forgotten.
`AlgebraicGeometry.RingedSite.globalSectionsCommRing` supplies it and is activated locally
here; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.GlobalSections.CommRing` for why it is not a global instance.

*The two restrictions of scalars.*  Both ways round the square give `H^i(X', 𝓕')` the structure
of a `Γ(Y, 𝒪_Y)`-module, and `ModuleCat.restrictScalarsComp'` identifies each
with restriction along the composite ring map.  The two composites agree by
`AlgebraicGeometry.Space.BaseChangeDiagram.globalSectionsRingHomSite_sq`, and that is the only
place commutativity of the square of spaces is used.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of affine algebraic spaces is an affine morphism.**  Both source and target
are isomorphic to presheaves represented by affine objects of the site, the morphism between
those is represented by a morphism of the site by full faithfulness of the Yoneda embedding,
and a morphism of affine objects of the site is affine by
`AlgebraicGeometry.Space.isAffineHom_yoneda_map`. -/
theorem isAffineHom_of_isAffineSpace {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAffineSpace B S hS X) (hY : IsAffineSpace B S hS Y) :
    IsAffineHom B S hS f := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hX
  obtain ⟨T', hT', ⟨e'⟩⟩ := hY
  have := hT
  have := hT'
  have hrep : IsAffineHom B S hS (e.inv ≫ f ≫ e'.hom) := by
    have hpre : e.inv ≫ f ≫ e'.hom =
        yoneda.map (yoneda.preimage (e.inv ≫ f ≫ e'.hom)) := (yoneda.map_preimage _).symm
    rw [hpre]
    exact isAffineHom_yoneda_map B S hS _
  have h₂ : IsAffineHom B S hS ((e.inv ≫ f ≫ e'.hom) ≫ e'.inv) :=
    isAffineHom_comp_iso e'.inv hrep
  have h₃ : IsAffineHom B S hS (e.hom ≫ (e.inv ≫ f ≫ e'.hom) ≫ e'.inv) :=
    isAffineHom_iso_comp e.hom h₂
  simpa using h₃

variable {B S hS}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

/-- **The projection `g' : X' ⟶ X` of the square is an affine morphism** when the two bases are
affine.  A morphism of affine algebraic spaces is affine, and affineness of a morphism is
stable under base change (**Stacks 03WI**). -/
theorem isAffineHom_g' (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) :
    IsAffineHom B S hS D.g'.hom :=
  isAffineHom_hom_of_isPullback D.isPullback.flip
    (isAffineHom_of_isAffineSpace B S hS D.g.hom hY' hY)

/-- **The projection `g' : X' ⟶ X` of the square is flat** when `g` is.  This is **Stacks
03MO**, flatness being stable under base change. -/
theorem isFlat_g' (hg : IsFlat B S hS D.g.hom) : IsFlat B S hS D.g'.hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback D.isPullback.flip hg

/-- The ring map `A = Γ(Y, 𝒪_Y) ⟶ Γ(X', 𝒪_{X'})` obtained by going along the top of the square
and then down: it is also the one obtained by going down and then along the bottom, by
`AlgebraicGeometry.Space.BaseChangeDiagram.globalSectionsRingHomSite_sq`. -/
abbrev globalSectionsRingHomSiteDiag :
    RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj →+*
      RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O).obj :=
  (globalSectionsRingHomSite B S hS D.g').comp (globalSectionsRingHomSite B S hS D.f)

/-- Reading a `Γ(X', 𝒪_{X'})`-module over `A = Γ(Y, 𝒪_Y)` through the top-then-down route of the
square is reading it over `A` through the down-then-bottom route.  This is
`AlgebraicGeometry.Space.BaseChangeDiagram.globalSectionsRingHomSite_sq` turned into an
isomorphism of restriction-of-scalars functors. -/
def restrictScalarsSquareIso :
    globalSectionsRestrictScalars B S hS D.g' ⋙ globalSectionsRestrictScalars B S hS D.f ≅
      globalSectionsRestrictScalars B S hS D.f' ⋙ globalSectionsRestrictScalars B S hS D.g :=
  (ModuleCat.restrictScalarsComp'.{u + 1} (globalSectionsRingHomSite B S hS D.f)
      (globalSectionsRingHomSite B S hS D.g') D.globalSectionsRingHomSiteDiag rfl).symm ≪≫
    ModuleCat.restrictScalarsComp'.{u + 1} (globalSectionsRingHomSite B S hS D.g)
      (globalSectionsRingHomSite B S hS D.f') D.globalSectionsRingHomSiteDiag
      D.globalSectionsRingHomSite_sq

/-- `H^i(X, 𝓕)` read as an `A = Γ(Y, 𝒪_Y)`-module through `f`.  This is the left hand side of
**Stacks 073K**, part (2) before extension of scalars. -/
abbrev affineCohomologyOverBase (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    ModuleCat.{u + 1} (RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj) :=
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  (globalSectionsRestrictScalars B S hS D.f).obj
    (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).rightDerived i).obj D.F)

/-- **The left hand side of Stacks 073K, part (2)**: `H^i(X, 𝓕) ⊗_A B`, the extension of
scalars along `A = Γ(Y, 𝒪_Y) ⟶ B = Γ(Y', 𝒪_{Y'})` of the cohomology of `𝓕` read as an
`A`-module through `f`. -/
abbrev affineCohomologySource (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    ModuleCat.{u + 1} (RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS D.Y'.1 D.Y'.2).O).obj) :=
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (globalSectionsRingHomSite B S hS D.g)).obj (D.affineCohomologyOverBase i)

/-- **The right hand side of Stacks 073K, part (2)**: `H^i(X', 𝓕')` read as a
`B = Γ(Y', 𝒪_{Y'})`-module through `f'`. -/
abbrev affineCohomologyTarget (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    ModuleCat.{u + 1} (RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS D.Y'.1 D.Y'.2).O).obj) :=
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  (globalSectionsRestrictScalars B S hS D.f').obj
    (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i).obj
      D.pulledBack)

/-- The pullback map on cohomology along `g'`, read as a map of `A = Γ(Y, 𝒪_Y)`-modules and
then across the square: `H^i(X, 𝓕) ⟶ H^i(X', 𝓕')` over `A`, the right hand side read through
`f'` and `g`.

This is the transpose of the comparison map of **Stacks 073K**, part (2) across the adjunction
between extension and restriction of scalars along `A ⟶ B`. -/
def affineCohomologyPullbackOverBase (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (D.affineCohomologyOverBase i ⟶
      (globalSectionsRestrictScalars B S hS D.g).obj (D.affineCohomologyTarget i)) :=
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have := enoughInjectives_modules B S hS D.X.1 D.X.2
  (globalSectionsRestrictScalars B S hS D.f).map
      (cohomologyPullbackMap B S hS D.g' (D.isAffineHom_g' hY hY') (D.isFlat_g' hg) D.F
        D.isQuasicoherent i) ≫
    (D.restrictScalarsSquareIso.hom.app
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i).obj
        D.pulledBack))

/-- **The comparison map of Stacks 073K, part (2)**: the canonical
`B = Γ(Y', 𝒪_{Y'})`-linear map `H^i(X, 𝓕) ⊗_A B ⟶ H^i(X', 𝓕')` for a cartesian square of
algebraic spaces with affine bases and flat `g`.

It is the transpose, across the adjunction between extension and restriction of scalars along
`A ⟶ B`, of the pullback map on cohomology along `g'`; see
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_adjoint`.

This map is an isomorphism:
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`. -/
def affineCohomologyBaseChangeMap (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (D.affineCohomologySource i ⟶ D.affineCohomologyTarget i) :=
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have := enoughInjectives_modules B S hS D.X.1 D.X.2
  ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (globalSectionsRingHomSite B S hS D.g)).homEquiv _ _).symm
      (D.affineCohomologyPullbackOverBase hg hY hY' i)

/-- **The comparison map of part (2) is literally a scalar extension followed by the counit**:
`H^i(X, 𝓕) ⊗_A B ⟶ H^i(X', 𝓕') ⊗_A B ⟶ H^i(X', 𝓕')`, the first map the extension of scalars of
the pullback map on cohomology along `g'` and the second the counit of the adjunction.

This is the transpose of
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_adjoint` written
out. -/
theorem affineCohomologyBaseChangeMap_eq (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    D.affineCohomologyBaseChangeMap hg hY hY' i =
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (globalSectionsRingHomSite B S hS D.g)).map
          (D.affineCohomologyPullbackOverBase hg hY hY' i) ≫
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
          (globalSectionsRingHomSite B S hS D.g)).counit.app (D.affineCohomologyTarget i) :=
  Adjunction.homEquiv_counit _ _ _ _

/-- **The comparison map of Stacks 073K, part (2) is the scalar extension of the pullback map
on cohomology along `g'`.**  Its transpose across the adjunction between extension and
restriction of scalars is that pullback map, read over `A = Γ(Y, 𝒪_Y)` through `f` and carried
across the square of global function rings.

The transposition is a bijection, so this equation determines the map. -/
theorem affineCohomologyBaseChangeMap_adjoint (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (globalSectionsRingHomSite B S hS D.g)).homEquiv _ _)
        (D.affineCohomologyBaseChangeMap hg hY hY' i) =
      D.affineCohomologyPullbackOverBase hg hY hY' i :=
  Equiv.apply_symm_apply _ _

end BaseChangeDiagram

end AlgebraicGeometry.Space

end

end

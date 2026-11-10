module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraQuotientFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial

/-!
# `Sym(ℱ)/ℐ` is functorial, and morphisms out of it

`Stacks.SymQuotientAlgebra.symQuotientAlgebra ℱ ℐ` is the quasi-coherent `𝒪_X`-algebra of finite
presentation `Sym(ℱ)/ℐ`, the direct image of the structure sheaf of the closed subscheme
`𝐙(ℐ) ⊆ 𝐕(ℱ)`. This file supplies the two things a directed system of such algebras needs:

* **transition morphisms.** For `f : ℱ ⟶ ℱ'` and quasi-coherent ideals `ℐ` on `𝐕(ℱ)` and `𝒥` on
  `𝐕(ℱ')` with `ℐ ≤ 𝒥.map 𝐕(f)`, the morphism `𝐙(𝒥) ⟶ 𝐙(ℐ)` over `X` and hence
  `Sym(ℱ)/ℐ ⟶ Sym(ℱ')/𝒥`, functorially in `(f, ℐ, 𝒥)`.
* **the factorisation.** A morphism of schemes `q : Y ⟶ 𝐕(ℱ)` over `X` whose kernel ideal
  contains `ℐ` factors uniquely through `𝐙(ℐ)`, and the factorisation gives a morphism of
  algebra sheaves `Sym(ℱ)/ℐ ⟶ (Y ⟶ X)_* 𝒪_Y` compatible with the transition morphisms.

## Main definitions

* `Stacks.SymQuotientAlgebra.symQuotientOver`: the closed subscheme `𝐙(ℐ) ⊆ 𝐕(ℱ)` with its
  structure morphism to `X`, as an object of `CategoryTheory.Over X`. Its pushed-forward
  structure sheaf is `symQuotientAlgebra` on the nose.
* `Stacks.SymQuotientAlgebra.symQuotientOverMap` and
  `Stacks.SymQuotientAlgebra.symQuotientAlgebraMap`: **the transition morphisms**, of schemes
  over `X` and of algebra sheaves.
* `Stacks.SymQuotientAlgebra.liftOver` and `Stacks.SymQuotientAlgebra.quotientAlgebraLift`:
  **the factorisation** of a morphism into `𝐕(ℱ)` killing `ℐ`, and the induced morphism of
  algebra sheaves out of `Sym(ℱ)/ℐ`.

## Main results

* `Stacks.SymQuotientAlgebra.symQuotientOverMap_id`, `symQuotientOverMap_comp`,
  `symQuotientAlgebraMap_id` and `symQuotientAlgebraMap_comp`: **functoriality.**
* `Stacks.SymQuotientAlgebra.liftOver_unique`: the factorisation is unique, and
  `liftOver_comp_symQuotientOverMap` / `quotientAlgebraLift_comp`: **the factorisations of one
  morphism through a growing family of ideals form a cone**, resp. a cocone of algebra sheaves.
  This is the naturality square the cocone of a directed system of quotients needs.

## Implementation notes

Every proof is cancellation of the mono `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`: a
closed immersion is a preimmersion and hence a monomorphism, so a morphism into `𝐙(ℐ)` is
determined by its composite into the ambient `𝐕(ℱ)`. That is what makes the functoriality
statements and the two cone statements hold without any further input — `Mathlib`'s
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap` and
`AlgebraicGeometry.IsClosedImmersion.lift` supply the morphisms, and both are characterized by
their composite with `subschemeι` (`subschemeMap_subschemeι`, `lift_fac`).

The hypothesis of a transition morphism is `ℐ ≤ 𝒥.map 𝐕(f)` and not `ℐ.comap 𝐕(f) ≤ 𝒥`; the two
are equivalent by `AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le`, and the first
is the one `subschemeMap` consumes.

These are the transition morphisms of the system of [Stacks, Tag 05JS], whose index set is the
pairs `(i, ℐ)` with `i` in a directed system of finitely presented quasi-coherent modules and `ℐ`
a *finite type* quasi-coherent ideal of `𝐕(ℱᵢ)`. Nothing here depends on finite type; where it is
needed, `Stacks.SymQuotientAlgebra.isOfFinitePresentation_symQuotientAlgebra` takes it in the
form `∀ V : affineOpens, (ℐ.ideal V).FG`.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.SymQuotientAlgebra

variable {X : Scheme.{u}} (E E' E'' : SheafOfModules.{u} X.ringCatSheaf)
  [E.IsQuasicoherent] [E'.IsQuasicoherent] [E''.IsQuasicoherent]

/-! ### The closed subscheme cut out by `ℐ`, as a scheme over `X` -/

/-- **The closed subscheme `𝐙(ℐ) ⊆ 𝐕(ℱ)` with its structure morphism to `X`**, as an object of
the category of schemes over `X`. Its pushed-forward structure sheaf is `Sym(ℱ)/ℐ`. -/
abbrev symQuotientOver (I : (Scheme.Modules.vectorBundle X E).IdealSheafData) : Over X :=
  Over.mk (I.subschemeι ≫ Scheme.Modules.vectorBundleToBase X E)

/-- The pushed-forward structure sheaf of `𝐙(ℐ)` is `Sym(ℱ)/ℐ`, on the nose. -/
theorem pushforwardAlgebra_symQuotientOver
    (I : (Scheme.Modules.vectorBundle X E).IdealSheafData) :
    pushforwardAlgebra (symQuotientOver E I).hom = symQuotientAlgebra E I :=
  rfl

/-! ### The transition morphisms -/

variable (f : E ⟶ E') (g : E' ⟶ E'')
  (I : (Scheme.Modules.vectorBundle X E).IdealSheafData)
  (J : (Scheme.Modules.vectorBundle X E').IdealSheafData)
  (K : (Scheme.Modules.vectorBundle X E'').IdealSheafData)

/-- The restriction of `𝐕(f)` to the two closed subschemes is a morphism over `X`: the triangle
over `X` formed by the two structure morphisms commutes. -/
theorem subschemeMap_comp_symQuotientOver_hom
    (h : I ≤ J.map (Scheme.Modules.vectorBundleMap X f).left) :
    Scheme.IdealSheafData.subschemeMap J I (Scheme.Modules.vectorBundleMap X f).left h ≫
        (symQuotientOver E I).hom = (symQuotientOver E' J).hom := by
  change Scheme.IdealSheafData.subschemeMap J I
          (Scheme.Modules.vectorBundleMap X f).left h ≫
        I.subschemeι ≫ Scheme.Modules.vectorBundleToBase X E =
      J.subschemeι ≫ Scheme.Modules.vectorBundleToBase X E'
  rw [← Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι, Category.assoc,
    Scheme.Modules.vectorBundleMap_left_comp]

/-- **The transition morphism `𝐙(𝒥) ⟶ 𝐙(ℐ)` of schemes over `X`** attached to `f : ℱ ⟶ ℱ'` and
ideals with `ℐ ≤ 𝒥.map 𝐕(f)`: the restriction of `𝐕(f) : 𝐕(ℱ') ⟶ 𝐕(ℱ)` to the two closed
subschemes. -/
def symQuotientOverMap (h : I ≤ J.map (Scheme.Modules.vectorBundleMap X f).left) :
    symQuotientOver E' J ⟶ symQuotientOver E I :=
  Over.homMk
    (Scheme.IdealSheafData.subschemeMap J I (Scheme.Modules.vectorBundleMap X f).left h)
    (subschemeMap_comp_symQuotientOver_hom E E' f I J h)

/-- **The transition morphism is the restriction of `𝐕(f)`**, which characterizes it: a morphism
into a closed subscheme is determined by its composite with the closed immersion. -/
@[reassoc]
theorem symQuotientOverMap_left_subschemeι
    (h : I ≤ J.map (Scheme.Modules.vectorBundleMap X f).left) :
    (symQuotientOverMap E E' f I J h).left ≫ I.subschemeι =
      J.subschemeι ≫ (Scheme.Modules.vectorBundleMap X f).left :=
  Scheme.IdealSheafData.subschemeMap_subschemeι J I _ h

/-- Two morphisms of schemes over `X` into `𝐙(ℐ)` agree as soon as their composites with the
closed immersion into `𝐕(ℱ)` do. -/
theorem symQuotientOver_hom_ext {Y : Over X} {u v : Y ⟶ symQuotientOver E I}
    (h : u.left ≫ I.subschemeι = v.left ≫ I.subschemeι) : u = v :=
  Over.OverMorphism.ext ((cancel_mono I.subschemeι).1 h)

/-- **The transition morphism of an identity is the identity.** -/
theorem symQuotientOverMap_id
    (h : I ≤ I.map (Scheme.Modules.vectorBundleMap X (𝟙 E)).left) :
    symQuotientOverMap E E (𝟙 E) I I h = 𝟙 (symQuotientOver E I) := by
  refine symQuotientOver_hom_ext E I ?_
  refine (symQuotientOverMap_left_subschemeι E E (𝟙 E) I I h).trans ?_
  rw [Scheme.Modules.vectorBundleMap_id]
  exact (Category.comp_id _).trans (Category.id_comp I.subschemeι).symm

/-- **The transition morphism of a composite is the composite of the transition morphisms.** -/
theorem symQuotientOverMap_comp
    (hf : I ≤ J.map (Scheme.Modules.vectorBundleMap X f).left)
    (hg : J ≤ K.map (Scheme.Modules.vectorBundleMap X g).left)
    (hfg : I ≤ K.map (Scheme.Modules.vectorBundleMap X (f ≫ g)).left) :
    symQuotientOverMap E E'' (f ≫ g) I K hfg =
      symQuotientOverMap E' E'' g J K hg ≫ symQuotientOverMap E E' f I J hf := by
  refine symQuotientOver_hom_ext E I ?_
  rw [symQuotientOverMap_left_subschemeι, Scheme.Modules.vectorBundleMap_comp, Over.comp_left,
    Over.comp_left, Category.assoc, symQuotientOverMap_left_subschemeι,
    symQuotientOverMap_left_subschemeι_assoc]

/-- **The transition morphism `Sym(ℱ)/ℐ ⟶ Sym(ℱ')/𝒥` of algebra sheaves**: the direct image of
the transition morphism of closed subschemes.

Its source and target are written as the pushed-forward structure sheaves of the two closed
subschemes, which are `Stacks.SymQuotientAlgebra.symQuotientAlgebra` by
`pushforwardAlgebra_symQuotientOver`; stating it at that spelling instead makes the elaborator
unify two expressions for the projection `𝐕(ℱ) ⟶ X` and the resulting `whnf` unfolds the
glueing that builds the relative spectrum. -/
def symQuotientAlgebraMap (h : I ≤ J.map (Scheme.Modules.vectorBundleMap X f).left) :
    pushforwardAlgebra (symQuotientOver E I).hom ⟶
      pushforwardAlgebra (symQuotientOver E' J).hom :=
  pushforwardAlgebraMap (symQuotientOverMap E E' f I J h)

/-- **Functoriality of `Sym(ℱ)/ℐ`**: an identity induces the identity. -/
theorem symQuotientAlgebraMap_id
    (h : I ≤ I.map (Scheme.Modules.vectorBundleMap X (𝟙 E)).left) :
    symQuotientAlgebraMap E E (𝟙 E) I I h =
      𝟙 (pushforwardAlgebra (symQuotientOver E I).hom) := by
  rw [symQuotientAlgebraMap, symQuotientOverMap_id, pushforwardAlgebraMap_id]

/-- **Functoriality of `Sym(ℱ)/ℐ`**: a composite induces the composite. -/
theorem symQuotientAlgebraMap_comp
    (hf : I ≤ J.map (Scheme.Modules.vectorBundleMap X f).left)
    (hg : J ≤ K.map (Scheme.Modules.vectorBundleMap X g).left)
    (hfg : I ≤ K.map (Scheme.Modules.vectorBundleMap X (f ≫ g)).left) :
    symQuotientAlgebraMap E E'' (f ≫ g) I K hfg =
      symQuotientAlgebraMap E E' f I J hf ≫ symQuotientAlgebraMap E' E'' g J K hg := by
  rw [symQuotientAlgebraMap, symQuotientAlgebraMap, symQuotientAlgebraMap,
    ← pushforwardAlgebraMap_comp, symQuotientOverMap_comp E E' E'' f g I J K hf hg hfg]

/-! ### Morphisms out of `Sym(ℱ)/ℐ` -/

/-- The kernel ideal of the closed immersion `𝐙(ℐ) ⟶ 𝐕(ℱ)` is `ℐ`, so a morphism whose kernel
ideal contains `ℐ` satisfies the hypothesis of `AlgebraicGeometry.IsClosedImmersion.lift`. -/
theorem ker_subschemeι_le {Y : Over X}
    (q : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E)) (hI : I ≤ q.left.ker) :
    I.subschemeι.ker ≤ q.left.ker := by
  rwa [Scheme.IdealSheafData.ker_subschemeι]

/-- The factorisation of `q` through the closed immersion is a morphism over `X`. -/
theorem lift_comp_symQuotientOver_hom {Y : Over X}
    (q : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E)) (hI : I ≤ q.left.ker) :
    IsClosedImmersion.lift I.subschemeι q.left (ker_subschemeι_le E I q hI) ≫
        (symQuotientOver E I).hom = Y.hom := by
  change IsClosedImmersion.lift I.subschemeι q.left (ker_subschemeι_le E I q hI) ≫
      I.subschemeι ≫ Scheme.Modules.vectorBundleToBase X E = Y.hom
  rw [← Category.assoc, IsClosedImmersion.lift_fac]
  exact Over.w q

/-- **A morphism of schemes over `X` into `𝐕(ℱ)` whose kernel ideal contains `ℐ` factors through
the closed subscheme `𝐙(ℐ)`.** -/
def liftOver {Y : Over X} (q : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E))
    (hI : I ≤ q.left.ker) : Y ⟶ symQuotientOver E I :=
  Over.homMk (IsClosedImmersion.lift I.subschemeι q.left (ker_subschemeι_le E I q hI))
    (lift_comp_symQuotientOver_hom E I q hI)

/-- The factorisation composed with the closed immersion is the original morphism. -/
@[reassoc]
theorem liftOver_left_subschemeι {Y : Over X}
    (q : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E)) (hI : I ≤ q.left.ker) :
    (liftOver E I q hI).left ≫ I.subschemeι = q.left :=
  IsClosedImmersion.lift_fac _ _ _

/-- **The factorisation is unique**, the closed immersion being a monomorphism. -/
theorem liftOver_unique {Y : Over X} (q : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E))
    (hI : I ≤ q.left.ker) (u : Y ⟶ symQuotientOver E I)
    (hu : u.left ≫ I.subschemeι = q.left) : u = liftOver E I q hI :=
  symQuotientOver_hom_ext E I (hu.trans (liftOver_left_subschemeι E I q hI).symm)

/-- **The factorisations of one morphism through a growing family of ideals form a cone**: if
`q' : Y ⟶ 𝐕(ℱ')` lifts `q = q' ≫ 𝐕(f)`, then the factorisation of `q'` through `𝐙(𝒥)` followed
by the transition morphism is the factorisation of `q` through `𝐙(ℐ)`.

This is the naturality square the cocone of a directed system of quotient algebras needs. -/
theorem liftOver_comp_symQuotientOverMap {Y : Over X}
    (q' : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E'))
    (hJ : J ≤ q'.left.ker)
    (hI : I ≤ (q' ≫ Scheme.Modules.vectorBundleMap X f).left.ker)
    (h : I ≤ J.map (Scheme.Modules.vectorBundleMap X f).left) :
    liftOver E' J q' hJ ≫ symQuotientOverMap E E' f I J h =
      liftOver E I (q' ≫ Scheme.Modules.vectorBundleMap X f) hI := by
  refine liftOver_unique E I _ hI _ ?_
  rw [Over.comp_left, Category.assoc, symQuotientOverMap_left_subschemeι,
    liftOver_left_subschemeι_assoc, Over.comp_left]

/-- **The morphism of algebra sheaves `Sym(ℱ)/ℐ ⟶ (Y ⟶ X)_* 𝒪_Y`** induced by a morphism
`q : Y ⟶ 𝐕(ℱ)` of schemes over `X` whose kernel ideal contains `ℐ`. -/
def quotientAlgebraLift {Y : Over X} (q : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E))
    (hI : I ≤ q.left.ker) :
    pushforwardAlgebra (symQuotientOver E I).hom ⟶ pushforwardAlgebra Y.hom :=
  pushforwardAlgebraMap (liftOver E I q hI)

/-- **The morphisms of algebra sheaves out of a growing family of quotients form a cocone** over
the pushed-forward structure sheaf of `Y`: the transition morphism followed by the morphism out
of the larger quotient is the morphism out of the smaller one. -/
theorem quotientAlgebraLift_comp {Y : Over X}
    (q' : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E'))
    (hJ : J ≤ q'.left.ker)
    (hI : I ≤ (q' ≫ Scheme.Modules.vectorBundleMap X f).left.ker)
    (h : I ≤ J.map (Scheme.Modules.vectorBundleMap X f).left) :
    symQuotientAlgebraMap E E' f I J h ≫ quotientAlgebraLift E' J q' hJ =
      quotientAlgebraLift E I (q' ≫ Scheme.Modules.vectorBundleMap X f) hI := by
  rw [symQuotientAlgebraMap, quotientAlgebraLift, ← pushforwardAlgebraMap_comp,
    liftOver_comp_symQuotientOverMap E E' f I J q' hJ hI h, quotientAlgebraLift]

end Stacks.SymQuotientAlgebra

end

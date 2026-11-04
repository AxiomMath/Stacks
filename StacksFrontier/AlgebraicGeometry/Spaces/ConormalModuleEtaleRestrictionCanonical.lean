module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalPullbackComparisonComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The étale restriction of the conormal module is the canonical map, functorially

Let `Z ⊆ X` be a closed subspace of an algebraic space over a scheme `S` contained in a big fppf
site `B`, let `φ : U ⟶ X` be étale and let

```
Z_U --p--> Z
|i_U       |i
U  --φ-->  X
```

be a cartesian square, so that `Z_U = U ×_X Z`.  This file proves Stacks 04CO in the shape the
source asserts it — *canonically and functorially in `U`*:

* the identification `p^*𝒞_{Z/X} ≅ 𝒞_{Z_U/U}` **is the canonical map of Stacks 04CP**, no
  separate construction being made: the canonical map is invertible because `φ` is étale, hence
  flat, which is the flat clause of Stacks 04CQ;
* that identification is **functorial in the étale source**: for a further étale `ψ : V ⟶ U` the
  identification for `ψ ≫ φ` is the identification for `φ` restricted along `ψ`, composed with
  the identification for `ψ`, read through the composition comparison of Stacks 03LU.

Functoriality is the composition law for the canonical map, which is part (3) of Stacks 04G2
(`AlgebraicGeometry.Space.conormalMap_comp`); it holds for arbitrary commutative squares and so
in particular for the étale ones, and nothing beyond it is needed.

## Main definitions

* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso`: **Stacks 04CO**, the
  identification `p^*𝒞_{Z/X} ≅ 𝒞_{Z_U/U}`, as the canonical map of Stacks 04CP.

## Main results

* `AlgebraicGeometry.Space.isFlat_smallEtaleRingedToposHom_of_isEtale`: an étale morphism of
  algebraic spaces induces a flat morphism of small étale ringed topoi.
* `AlgebraicGeometry.Space.isIso_conormalMap_of_isPullback_of_isEtale`: the canonical map of
  Stacks 04CP is invertible at a fibre product square whose transverse morphism is étale.
* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_comp`: **Stacks 04CO, the
  functoriality in the étale source `U`.**

## Implementation notes

**Why the identification is taken to be the canonical map.**  Stacks 04CO asserts an
identification that is canonical and functorial; the canonical map of Stacks 04CP is the only
map of the two conormal modules the square provides, so taking the identification to *be* that
map is what makes both assertions statements about one object rather than about a construction
that would then have to be compared with it.  This development also carries a separately built
isomorphism of the same two modules,
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean`, assembled from the
square comparison of Stacks 03LU, the identification of the inverse image with étale restriction
of Stacks 03LW and the equality of defining ideal sheaves.  That one is *not* known to agree with
the canonical map — see `What is not proved` — and it is not functorial in `U` for the reason
recorded there; the two statements below do not depend on it.

**The flatness input was available all along.**  The flat clause of Stacks 04CQ is stated for
flatness of the induced morphism of small étale ringed topoi, and the "What is not proved"
section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeFlat.lean` records that the
passage from `AlgebraicGeometry.Space.IsFlat` to that form is the one declaration missing.  It is
not missing: it is Stacks 073C,
`AlgebraicGeometry.Space.isFlat_iff_smallEtaleRingedToposHom_isFlat`, and composing it with
`AlgebraicGeometry.Space.isFlat_of_isEtale` is the whole of
`AlgebraicGeometry.Space.isFlat_smallEtaleRingedToposHom_of_isEtale` below.

**The hypotheses of the functoriality statement are exactly those of the tag.**  The étaleness of
the composite and the cartesianness of the outer rectangle are *derived*, not carried: the former
from `AlgebraicGeometry.Space.isEtale_comp`, the latter by pasting the two cartesian squares.  The
squares are arbitrary fibre product squares rather than the canonical inverse-image squares, which
is more general and which `AlgebraicGeometry.Space.isPullback_preimageSubspace` instantiates.

## What is not proved

* **The closed case only.**  Stacks 04CO is stated for an immersion `i : Z ⟶ X` with `Z_U`
  locally closed in `U`; what is proved here is the closed case, the case
  `AlgebraicGeometry.Space.conormalMap` carries.  The identification itself *is* available at
  full immersion generality, as
  `AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionEtaleRestriction.lean`, and so is
  the canonical map, as `AlgebraicGeometry.Space.conormalMapOfImmersions` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionFunctorial.lean`.  What the
  immersion case of the two statements below needs is named precisely:
  * for the invertibility, `IsIso (conormalAlgebraSquarePieceMap B S hS i i' f g hsq 1)` at a
    cartesian square with `g` étale.  The flat clause for the square map,
    `AlgebraicGeometry.Space.isIso_conormalAlgebraSquareMapOfPullbackHom_app_of_isFlat`, carries
    four hypotheses (`hunit`, `h0`, `h1`, `hι`) and so does not supply it;
  * for the functoriality, nothing further: the composition law at immersion generality **is**
    in the library, as `AlgebraicGeometry.Space.conormalMapOfImmersions_comp` of
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquarePieceMapCompositionLaw.lean`, with
    `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` as its ideal-side form.  Of
    the composition laws for the three factors of
    `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap`, two are in the library —
    `AlgebraicGeometry.Space.squarePullbackCompIso_paste` of
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquarePieceMapComposition.lean` for the
    comparison and `AlgebraicGeometry.Space.kernelIdealSquareMap_comp` of
    `StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMapComposition.lean` for the
    ideal sheaves — and the third is not needed, the two containments entering the law only
    through the single map `AlgebraicGeometry.Space.kernelIdealSquareMap`.

* **That the separately built isomorphism of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` is this one is not
  proved.**  Identifying them amounts to identifying
  `AlgebraicGeometry.Space.idealSheafMap`, which is defined by transposing twice, with the
  Stacks 03LW comparison followed by the equality of defining ideal sheaves; the module
  documentation of that file records why no statement brings the two descriptions to a common
  form.  Nothing below rests on that identification.

## References

* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 073C](https://stacks.math.columbia.edu/tag/073C)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' X'' : AlgebraicSpaces B S hS}

/-! ### Étale morphisms induce flat morphisms of small étale ringed topoi -/

/-- **An étale morphism of algebraic spaces induces a flat morphism of small étale ringed
topoi.**  An étale morphism is flat in the chartwise sense of Stacks 03ML, part (1), by
`AlgebraicGeometry.Space.isFlat_of_isEtale`, and chartwise flatness is flatness of the induced
morphism of small étale ringed topoi by Stacks 073C.

This is the form of flatness that the flat clause of Stacks 04CQ consumes. -/
theorem isFlat_smallEtaleRingedToposHom_of_isEtale (g : X ⟶ X')
    (hg : IsEtale B S hS g.hom) :
    (smallEtaleRingedToposHom B S hS g).IsFlat :=
  (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS g).mp (isFlat_of_isEtale B S hS hg)

/-! ### Stacks 04CO: the identification is the canonical map of Stacks 04CP -/

/-- **The canonical map of Stacks 04CP is invertible at an étale fibre product square.**  For a
fibre product square of closed subspaces whose transverse morphism `g` is étale, the canonical map
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of Stacks 04CP is an isomorphism.

This is the flat clause of Stacks 04CQ,
`AlgebraicGeometry.Space.isIso_conormalMap_of_isPullback_of_isFlat`, at the flatness supplied by
`AlgebraicGeometry.Space.isFlat_smallEtaleRingedToposHom_of_isEtale`. -/
theorem isIso_conormalMap_of_isPullback_of_isEtale
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hcart : IsPullback Z.1.ι f.hom g.hom Z'.1.ι)
    (hg : IsEtale B S hS g.hom) :
    IsIso (conormalMap B S hS Z Z' g f hsq) :=
  isIso_conormalMap_of_isPullback_of_isFlat B S hS Z Z' g f hsq hcart
    (isFlat_smallEtaleRingedToposHom_of_isEtale B S hS g hg)

/-- **Stacks 04CO.**  Let `Z ⊆ X` be a closed subspace of an algebraic space over `S`, let
`g : X' ⟶ X` be étale — written `φ : U ⟶ X` in the source — and let

```
Z_U --f--> Z
|          |
U  --g-->  X
```

be a cartesian square, so that `Z_U = U ×_X Z` is the inverse image of `Z`.  Then the inverse
image along `f` of the conormal module of `Z` in `X` is the conormal module of `Z_U` in `U`:

`𝒞_{Z/X}|_{Z_U} = f^*𝒞_{Z/X} ≅ 𝒞_{Z_U/U}`.

The identification is the canonical map of Stacks 04CP itself, which is invertible by
`AlgebraicGeometry.Space.isIso_conormalMap_of_isPullback_of_isEtale`; it is therefore canonical by
construction, and functorial in the étale source by
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_comp`. -/
@[stacks 04CO "the identification, as the canonical map of 04CP, for an etale source"]
noncomputable def conormalModuleEtaleRestrictionCanonicalIso
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hcart : IsPullback Z.1.ι f.hom g.hom Z'.1.ι)
    (hg : IsEtale B S hS g.hom) :
    (modulePullback B S hS f).obj (conormalModule B S hS X' Z') ≅
      conormalModule B S hS X Z :=
  @asIso _ _ _ _ (conormalMap B S hS Z Z' g f hsq)
    (isIso_conormalMap_of_isPullback_of_isEtale B S hS Z Z' g f hsq hcart hg)

/-- The identification of Stacks 04CO is the canonical map of Stacks 04CP on the nose. -/
theorem conormalModuleEtaleRestrictionCanonicalIso_hom
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hcart : IsPullback Z.1.ι f.hom g.hom Z'.1.ι)
    (hg : IsEtale B S hS g.hom) :
    (conormalModuleEtaleRestrictionCanonicalIso B S hS Z Z' g f hsq hcart hg).hom =
      conormalMap B S hS Z Z' g f hsq :=
  rfl

/-! ### Stacks 04CO: functoriality in the étale source -/

/-- **Stacks 04CO, the functoriality in the étale source `U`.**  Let `Z ⊆ X` be a closed
subspace, let `g' : X' ⟶ X''` and `g : X ⟶ X'` be étale — written `φ : U ⟶ X` and `ψ : V ⟶ U` in
the source — and let the two squares

```
Z   --f--> Z'  --f'--> Z''
|          |           |
X   --g--> X'  --g'--> X''
```

both be cartesian.  Then the identification of Stacks 04CO for the composite `g ≫ g'` is the
composition comparison of Stacks 03LU for `f` and `f'`, followed by the inverse image along `f`
of the identification for `g'`, followed by the identification for `g`.

The étaleness of the composite and the cartesianness of the outer rectangle are derived from the
hypotheses, so what is assumed is exactly what the tag assumes.  The proof is the composition law
for the canonical map, part (3) of Stacks 04G2
(`AlgebraicGeometry.Space.conormalMap_comp`), together with
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_hom`: because the
identification *is* the canonical map, its functoriality is that law and needs nothing further.
In particular the composition law for the identification of Stacks 03LW is not needed, which is
what blocks the functoriality of the separately built isomorphism of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean`. -/
@[stacks 04CO "functoriality in the etale source U"]
theorem conormalModuleEtaleRestrictionCanonicalIso_comp
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1)
    (Z'' : ClosedSubspaces B S hS X''.1) (g : X ⟶ X') (g' : X' ⟶ X'')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (f' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X' Z' ≫ g' = f' ≫ subspaceInclusion B S hS X'' Z'')
    (hcart : IsPullback Z.1.ι f.hom g.hom Z'.1.ι)
    (hcart' : IsPullback Z'.1.ι f'.hom g'.hom Z''.1.ι)
    (hg : IsEtale B S hS g.hom) (hg' : IsEtale B S hS g'.hom) :
    (conormalModuleEtaleRestrictionCanonicalIso B S hS Z Z'' (g ≫ g') (f ≫ f')
          (by rw [← Category.assoc, hsq, Category.assoc, hsq', Category.assoc])
          ((hcart.flip.paste_horiz hcart'.flip).flip)
          (isEtale_comp B S hS hg hg')).hom =
      (modulePullbackCompIso B S hS f f').inv.app (conormalModule B S hS X'' Z'') ≫
        (modulePullback B S hS f).map
            (conormalModuleEtaleRestrictionCanonicalIso B S hS Z' Z'' g' f' hsq' hcart' hg').hom ≫
          (conormalModuleEtaleRestrictionCanonicalIso B S hS Z Z' g f hsq hcart hg).hom :=
  conormalMap_comp B S hS g g' Z Z' Z'' f f' hsq hsq' _

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageIdeal

/-!
# The scheme-theoretic image of a quasi-compact morphism is étale-local on the target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `g : V ⟶ Y` be étale.  Part (3) of Stacks 082Z asserts that if `f` is
*quasi-compact* then forming its scheme-theoretic image commutes with the base change of the
target along `g`: the scheme-theoretic image of `X ×_Y V ⟶ V` is the inverse image along `g` of
the scheme-theoretic image of `f`.

Both sides are closed subspaces of `V` — the first by Stacks 082X, the second by Stacks 083Q —
and a closed subspace is determined by its defining ideal sheaf of Stacks 03MB,
`AlgebraicGeometry.Space.definingIdealSheaf_injective`.  So the statement is an equality of
ideals on each étale scheme chart `W` of `V`, and quasi-compactness turns both sides into
kernels of structure maps: by Stacks 082Z the defining ideal sheaf of the scheme-theoretic image
of a quasi-compact morphism *is* the kernel ideal sheaf of its structure map, and `X ×_Y V ⟶ V`
is quasi-compact because quasi-compactness is stable under base change, Stacks 03HF.  That the
kernel ideal sheaf is étale-local on the target is
`AlgebraicGeometry.Space.kernelIdealSheaf_fibreProduct_obj`, which identifies the kernel ideal
of `X ×_Y V ⟶ V` on `W` with the kernel ideal of `f` on the chart `g ∘ W` of `Y`.

What remains is to recognise the defining ideal of the inverse image on `W` as the defining
ideal of the image on `g ∘ W`.  Both are computed, by
`AlgebraicGeometry.Space.definingIdealAt_eq_ker` and
`AlgebraicGeometry.Space.definingIdealAt_preimage`, as the kernel of pullback of regular
functions along a canonical base change formed along `W ⟶ V ⟶ Y`, and
`AlgebraicGeometry.Space.smallEtalePostcomp_obj_hom` says that this composite is exactly the
structure morphism of the chart `g ∘ W`.  No transport is involved: étale postcomposition with
`g` leaves the underlying object of the big fppf site of `S` unchanged, so the two ideals are
ideals of one ring.

Reducedness is assumed nowhere, so this is independent of the reduced case
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale`, part (2) of
Stacks 0830, which needs no quasi-compactness but does need the source to be reduced.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_smallEtalePostcomp`: the
  defining ideal of the inverse image of a closed subspace along an étale morphism, read on a
  chart of the source, is the defining ideal of the subspace read on the postcomposed chart.
* `Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact`
  is **part (3) of Stacks 082Z**: the scheme-theoretic image of a quasi-compact morphism of
  algebraic spaces over `S` commutes with étale base change of the target.  The primed variant
  of that name states the same for morphisms of presheaves carrying algebraicity hypotheses.

## References

* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section EtaleLocal

variable {X Y V : AlgebraicSpaces B S hS}

/-- **The defining ideal of an inverse image along an étale morphism.** For `g : V ⟶ Y` étale
and a closed subspace `Z ⊆ Y`, the defining ideal of `g⁻¹(Z)` on an étale scheme chart `W` of
`V` is the defining ideal of `Z` on the chart `g ∘ W` of `Y`: both are the kernel of pullback of
regular functions along the canonical base change of `Z` formed along `W ⟶ V ⟶ Y`. -/
theorem definingIdealAt_preimage_eq_definingIdealAt_smallEtalePostcomp
    (g : V ⟶ Y) (hg : IsEtale B S hS g.hom) (Z : ClosedSubspaces B S hS Y.1)
    (W : SmallEtale B S hS V.1) :
    definingIdealAt B S hS Y Z (op ((smallEtalePostcomp B S hS g hg).obj W)) =
      definingIdealAt B S hS V (⟨Z.1.preimage g.hom,
        isClosedSubspace_preimage B S hS g.hom Z.1 Y.2 V.2 Z.2⟩ :
        ClosedSubspaces B S hS V.1) (op W) :=
  (definingIdealAt_eq_ker B S hS Y Z ((smallEtalePostcomp B S hS g hg).obj W)).trans
    (definingIdealAt_preimage B S hS g Z W).symm

/-- **Stacks 082Z, part (3).** The scheme-theoretic image of a *quasi-compact* morphism
`f : X ⟶ Y` of algebraic spaces over `S` commutes with étale base change of the target: for
`g : V ⟶ Y` étale, the scheme-theoretic image of `X ×_Y V ⟶ V` is the inverse image along `g` of
the scheme-theoretic image of `f`.

Both sides are closed subspaces of `V`, hence are determined by their defining ideal sheaves,
and on an étale scheme chart `W` of `V` both of those ideals are the kernel ideal of `f` on the
chart `g ∘ W` of `Y` — by Stacks 082Z for the base change of `f` and for `f` itself. -/
@[stacks 082Z "part (3): compatibility with étale localization of the target"]
theorem schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact
    (f : X ⟶ Y) (g : V ⟶ Y) (hf : IsQuasiCompact B S hS f.hom)
    (hg : IsEtale B S hS g.hom) :
    schemeTheoreticImageSubfunctor B S hS (pullback.snd f.hom g.hom) =
      (schemeTheoreticImageSubfunctor B S hS f.hom).preimage g.hom := by
  have hf' : IsQuasiCompact B S hS (pullback.snd f.hom g.hom) :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f.hom g.hom) hf
  have hpt : ∀ W : (SmallEtale B S hS V.1)ᵒᵖ,
      definingIdealAt B S hS V (⟨schemeTheoreticImageSubfunctor B S hS
            (pullback.snd f.hom g.hom),
          isClosedSubspace_schemeTheoreticImageSubfunctor B S hS
            (pullback.snd f.hom g.hom) V.2⟩ : ClosedSubspaces B S hS V.1) W =
        definingIdealAt B S hS V (⟨(schemeTheoreticImageSubfunctor B S hS f.hom).preimage g.hom,
          isClosedSubspace_preimage B S hS g.hom _ Y.2 V.2
            (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f.hom Y.2)⟩ :
          ClosedSubspaces B S hS V.1) W := fun W =>
    (congrArg (fun N : (SheafOfModules.unit (structureRingSheaf B S hS V)).Submodule => N.obj W)
          (definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf B S hS
            (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
              AlgebraicSpaces.fiberProduct B S hS f g ⟶ V) hf')).trans
      ((kernelIdealSheaf_fibreProduct_obj B S hS f g hg W.unop).trans
        ((congrArg (fun N : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule =>
              N.obj (op ((smallEtalePostcomp B S hS g hg).obj W.unop)))
            (definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf B S hS f hf).symm).trans
          (definingIdealAt_preimage_eq_definingIdealAt_smallEtalePostcomp B S hS g hg
            (schemeTheoreticImage B S hS f.hom Y.2) W.unop)))
  exact congrArg Subtype.val (definingIdealSheaf_injective B S hS V
    (le_antisymm (fun W => (hpt W).le) fun W => (hpt W).ge))

/-- **Stacks 082Z, part (3)**, for morphisms of presheaves on the big fppf category over `S`
carrying algebraicity hypotheses: the scheme-theoretic image of a quasi-compact morphism
commutes with étale base change of the target. -/
theorem schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact'
    {X Y V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : V ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hV : IsAlgebraicSpace B S hS V) (hf : IsQuasiCompact B S hS f)
    (hg : IsEtale B S hS g) :
    schemeTheoreticImageSubfunctor B S hS (pullback.snd f g) =
      (schemeTheoreticImageSubfunctor B S hS f).preimage g :=
  schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact B S hS
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
    (ObjectProperty.homMk g : (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) hf hg

end EtaleLocal

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChange

/-!
# The twisted inverse image and restriction to a quasi-compact open, for qcqs schemes

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes, let `V ⊆ Y` be a
quasi-compact open subscheme and set `U = f⁻¹(V)`, so that

```
U --j'--> X
|         |
f|_U      f
v         v
V --j---> Y
```

is cartesian. Write `a` and `a'` for the right adjoints of `Rf_*` and `R(f|_U)_*` on the
quasi-coherent derived categories ([Stacks, Tag 0A9E]). [Stacks, Tag 0A9L] is the transformation

```
(j')^* ∘ a ⟶ (j')^* ∘ a ∘ Rj_* ∘ j^* ⟶ (j')^* ∘ Rj'_* ∘ a' ∘ j^* ⟶ a' ∘ j^*
```

of functors `D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_U)`: the unit of `j^* ⊣ Rj_*`, then the inverse of the
isomorphism `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` of [Stacks, Tag 0A9K], then the counit of
`(j')^* ⊣ Rj'_*`; together with the remark that it is an isomorphism at `K` exactly when
`a(K)|_U ⟶ a(Rj_*(K|_V))|_U` is.

## Main results

* `Stacks.Duality.OpenImmersion.qcqsTwistedInverseImageRestrictionMap` — the transformation
  `(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L].
* `Stacks.Duality.OpenImmersion.isIso_qcqsTwistedInverseImageRestrictionMap_app_iff` — its
  component at `K` is invertible if and only if `(j')^*(a(K ⟶ Rj_*(K|_V)))` is.

## Implementation notes

The transformation is `Stacks.Duality.OpenImmersion.twistedInverseImageRestrictionMap`, which is
stated for an arbitrary cartesian square along an open immersion and so takes the preservation of
quasi-coherence by each pushforward and restriction, the existence of `a` and `a'`, and the
invertibility of `ξ` as arguments. Here every one of them is proved: quasi-coherence of `Rf_*` by
[Stacks, Tag 08D5] (`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`), of
the restrictions by `Stacks.Duality.OpenImmersion.isQuasicoherent_homology_derivedRestrict`, the
right adjoints by the instance form of Tag 0A9E
(`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs`), and
`IsIso ξ` by the open-immersion case of Tag 0A9K
(`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion`). This file
lies downstream of both, which the module of the general transformation cannot. The cartesian
square is `AlgebraicGeometry.isPullback_morphismRestrict`, with `U = f ⁻¹ᵁ V` and `f|_U = f ∣_ V`.

Two instances make the schemes of the square quasi-compact and quasi-separated: an open subscheme
of a quasi-separated scheme is quasi-separated, and the preimage of a quasi-compact open under a
quasi-compact morphism is quasi-compact.

## References

* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

/-- An open subscheme of a quasi-separated scheme is quasi-separated. -/
instance Scheme.Opens.quasiSeparatedSpace {X : Scheme.{u}} [QuasiSeparatedSpace X] (U : X.Opens) :
    QuasiSeparatedSpace U :=
  quasiSeparatedSpace_of_quasiSeparated U.ι

/-- The preimage of a quasi-compact open subscheme under a quasi-compact morphism is
quasi-compact. -/
instance Scheme.Hom.compactSpace_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (V : Y.Opens) [CompactSpace V] : CompactSpace (f ⁻¹ᵁ V) :=
  QuasiCompact.compactSpace_of_compactSpace (f ∣_ V)

end AlgebraicGeometry

namespace Stacks.Duality.OpenImmersion

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] (V : Y.Opens) [CompactSpace V]

/-- **Stacks Project, Tag 0A9L.** For a morphism `f : X ⟶ Y` of quasi-compact and
quasi-separated schemes and a quasi-compact open `V ⊆ Y`, with `U = f⁻¹(V)`, `j : V ⟶ Y` and
`j' : U ⟶ X` the inclusions, the transformation `(j')^* ∘ a ⟶ a' ∘ j^*` of functors
`D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_U)`, where `a` and `a'` are the right adjoints of `Rf_*` and
`R(f|_U)_*`: the unit of `j^* ⊣ Rj_*`, then the inverse of the isomorphism
`ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` of [Stacks, Tag 0A9K], then the counit of `(j')^* ⊣ Rj'_*`.

It is `Stacks.Duality.OpenImmersion.twistedInverseImageRestrictionMap` for the square
`AlgebraicGeometry.isPullback_morphismRestrict`, every argument of which is proved here. -/
@[stacks 0A9L]
def qcqsTwistedInverseImageRestrictionMap :
    twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⋙
        quasiCoherentDerivedRestrict (f ⁻¹ᵁ V).ι
          (isQuasicoherent_homology_derivedRestrict (f ⁻¹ᵁ V).ι) ⟶
      quasiCoherentDerivedRestrict V.ι (isQuasicoherent_homology_derivedRestrict V.ι) ⋙
        twistedInverseImage (f ∣_ V) (isQuasicoherent_homology_derivedPushforward_of_qcqs _) :=
  twistedInverseImageRestrictionMap (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedRestrict _)
    (isQuasicoherent_homology_derivedRestrict _)
    (isPullback_morphismRestrict f V).flip

/-- **Stacks Project, Tag 0A9L, the criterion.** The transformation
`Stacks.Duality.OpenImmersion.qcqsTwistedInverseImageRestrictionMap` is an isomorphism when
evaluated on `K` if and only if `a(K)|_U ⟶ a(Rj_*(K|_V))|_U`, the restriction to `U` of `a`
applied to the unit of `j^* ⊣ Rj_*` at `K`, is an isomorphism: the other two arrows of the
composite are invertible. -/
@[stacks 0A9L "the isomorphism criterion: invertible at `K` iff `a(K)|_U ⟶ a(Rj_*(K|_V))|_U` is"]
theorem isIso_qcqsTwistedInverseImageRestrictionMap_app_iff
    (K : quasiCoherentDerivedCategory Y) :
    IsIso ((qcqsTwistedInverseImageRestrictionMap f V).app K) ↔
      IsIso ((quasiCoherentDerivedRestrict (f ⁻¹ᵁ V).ι
          (isQuasicoherent_homology_derivedRestrict (f ⁻¹ᵁ V).ι)).map
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          ((quasiCoherentDerivedRestrictAdjunction V.ι
            (isQuasicoherent_homology_derivedRestrict V.ι)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).unit.app K))) := by
  simp [qcqsTwistedInverseImageRestrictionMap, twistedInverseImageRestrictionMap]

end Stacks.Duality.OpenImmersion

end

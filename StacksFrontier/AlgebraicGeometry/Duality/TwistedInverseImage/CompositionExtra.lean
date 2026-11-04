module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition

/-!
# The twisted inverse image of a composite: the adjunction, the canonical map, the qcqs case

`Stacks.Duality.twistedInverseImageCompIso` is the comparison

  `(f ≫ g)^× ≅ g^× ⋙ f^×`

of the twisted inverse images of [Stacks, Tag 0A9E], obtained by uniqueness of right adjoints:
the composite of the adjunctions `Rf_* ⊣ f^×` and `Rg_* ⊣ g^×`, read along the composition
formula `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`, exhibits `g^× ⋙ f^×` as a right adjoint of `R(f ≫ g)_*`.
This file names that composite adjunction, identifies the comparison through it, and discharges
every argument of the comparison for quasi-compact quasi-separated morphisms.

## Main definitions

All in the namespace `Stacks.Duality`.

* `twistedInverseImageCompAdjunction` — the adjunction `R(f ≫ g)_* ⊣ g^× ⋙ f^×`.
* `twistedInverseImageCompIsoOfQcqs` — `(f ≫ g)^× ≅ g^× ⋙ f^×` for quasi-compact
  quasi-separated `f` and `g` with quasi-compact targets, where [Stacks, Tag 0A9E] supplies the
  three adjointness instances and part (1) of [Stacks, Tag 08D5] the three quasi-coherence
  arguments, so that nothing is left to supply beyond the two morphisms.

## Main results

* `twistedInverseImageCompIso_obj_hom_naturality` — the isomorphism is natural, recorded on
  objects because that is the shape in which the source uses it.
* `twistedInverseImageCompIso_hom_app_eq` — the inverse of the isomorphism is the mate of the
  composition formula for derived direct image, i.e. it is *the* canonical map and not merely
  some isomorphism. This identifies it through the counits of the adjunctions.

## Implementation notes

*Relation to Tag 0ATX.* The source's `f^!` on `FTS_S` is built from a compactification, and its
Lemma 48.16.3 compares the functors attached to two chosen compactifications of a composite with
those of compactifications of the factors. What is here is the composition law for the right
adjoint `f^×` of [Stacks, Tag 0A9E], which is `f^!` exactly when `f` is proper, by clause (2) of
[Stacks, Tag 0AU3].

*The derived category model.* As in the rest of the duality development, the derived categories
are the locally small ones of `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the only
model at which `D_QCoh(𝒪_X)` has the direct sums that [Stacks, Tag 0A9E] needs.

## References

* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

section Composition

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

/-- The adjunction `R(f ≫ g)_* ⊣ g^× ⋙ f^×` obtained by composing `Rf_* ⊣ f^×` with
`Rg_* ⊣ g^×` and transporting the left-hand side along the composition formula
`Stacks.Duality.quasiCoherentDerivedPushforwardCompIso`. It exhibits `g^× ⋙ f^×` as a right
adjoint of the same functor as `(f ≫ g)^×`; it is the adjunction through which
`Stacks.Duality.twistedInverseImageCompIso` is defined. -/
def twistedInverseImageCompAdjunction :
    quasiCoherentDerivedPushforward (f ≫ g) hpushfg ⊣
      twistedInverseImage g hpushg ⋙ twistedInverseImage f hpushf :=
  ((twistedInverseImageAdjunction f hpushf).comp
    (twistedInverseImageAdjunction g hpushg)).ofNatIsoLeft
      (quasiCoherentDerivedPushforwardCompIso f g hpushf hpushg hpushfg)

/-- The composition isomorphism is natural: for `u : K ⟶ L` in `D_QCoh(𝒪_Z)`, applying
`g^× ⋙ f^×` to `u` and then comparing agrees with comparing and then applying `(f ≫ g)^×`.
This is the naturality square of `Stacks.Duality.twistedInverseImageCompIso`, recorded on
objects because that is the form in which the source uses the comparison. -/
theorem twistedInverseImageCompIso_obj_hom_naturality {K L : quasiCoherentDerivedCategory Z}
    (u : K ⟶ L) :
    (twistedInverseImage (f ≫ g) hpushfg).map u ≫
        (twistedInverseImageCompIso f g hpushf hpushg hpushfg).hom.app L =
      (twistedInverseImageCompIso f g hpushf hpushg hpushfg).hom.app K ≫
        (twistedInverseImage f hpushf).map ((twistedInverseImage g hpushg).map u) :=
  (twistedInverseImageCompIso f g hpushf hpushg hpushfg).hom.naturality u

/-- **The isomorphism is the canonical one**, pinned down by the adjunctions rather than
chosen: transposing its inverse at `K` under `R(f ≫ g)_* ⊣ (f ≫ g)^×` gives the counit of the
composite adjunction `R(f ≫ g)_* ⊣ g^× ⋙ f^×` at `K`. This is
`CategoryTheory.Adjunction.homEquiv_symm_rightAdjointUniq_hom_app` for the two adjunctions
involved, and it is what makes `Stacks.Duality.twistedInverseImageCompIso` *the* comparison map
of [Stacks, Tag 0ATX] rather than some isomorphism between the two functors. -/
theorem twistedInverseImageCompIso_hom_app_eq (K : quasiCoherentDerivedCategory Z) :
    ((twistedInverseImageAdjunction (f ≫ g) hpushfg).homEquiv _ K).symm
        ((twistedInverseImageCompIso f g hpushf hpushg hpushfg).inv.app K) =
      (twistedInverseImageCompAdjunction f g hpushf hpushg hpushfg).counit.app K := by
  rw [twistedInverseImageCompIso, Adjunction.rightAdjointUniq_inv_app]
  exact Adjunction.homEquiv_symm_rightAdjointUniq_hom_app _ _ K

end Composition

/-! ### The quasi-compact quasi-separated case, with no input beyond the morphisms -/

section Qcqs

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
  [QuasiCompact g] [QuasiSeparated g] [CompactSpace Y] [CompactSpace Z]

/-- **[Stacks, Tag 0ATX] for the twisted inverse image, with no input beyond the two
morphisms.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be quasi-compact quasi-separated morphisms of
schemes with `Y` and `Z` quasi-compact. Then

  `(f ≫ g)^× ≅ g^× ⋙ f^×`.

Part (1) of [Stacks, Tag 08D5], in the form
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`, supplies the three
quasi-coherence arguments, and [Stacks, Tag 0A9E], in the form
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward`, supplies the three
adjointness instances; the composite `f ≫ g` is quasi-compact and quasi-separated because `f`
and `g` are. So this is `Stacks.Duality.twistedInverseImageCompIso` with every argument
discharged. -/
def twistedInverseImageCompIsoOfQcqs :
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward g
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (f ≫ g)
    twistedInverseImage (f ≫ g) (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g)) ≅
      twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g) ⋙
        twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) :=
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward g
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (f ≫ g)
  twistedInverseImageCompIso f g (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))

end Qcqs

end Stacks.Duality

end

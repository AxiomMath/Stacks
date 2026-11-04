module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperRestriction

/-!
# The base change map of Tag 0AA6 along an open immersion is the map of Tag 0A9L

Let

```
U --j'--> X
|         |
f'        f
v         v
V --j---> Y
```

be a cartesian square of schemes in which `j` (hence `j'`) is an open immersion, and write `a`,
`a'` for the twisted inverse images of `f`, `f'` of [Stacks, Tag 0A9E]. The source attaches two
transformations `D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_U)` to it:

* the base change map `L(j')^* ∘ a ⟶ a' ∘ Lj^*` of [Stacks, Tag 0AA6],
  `Stacks.Duality.twistedInverseImageBaseChangeMap`, built from the derived pullbacks;
* the map `(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L],
  `Stacks.Duality.OpenImmersion.twistedInverseImageRestrictionMap`, built from the exact
  restrictions.

The source says that the second "is a special case" of the first. Here this is made precise: both
`Lj^*` and `j^*` are left adjoint to `Rj_*` on the quasi-coherent derived categories, so they are
identified by the uniqueness of adjoints (`quasiCoherentDerivedPullbackIsoRestrict`), and through
that identification one map is invertible at an object exactly when the other is
(`isIso_twistedInverseImageBaseChangeMap_app_iff`). So [Stacks, Tag 0A9P] (2) gives the
invertibility of the base change map of Tag 0AA6 on `D^+_QCoh(𝒪_Y)` for `f` proper over a
Noetherian `Y` (`isIso_twistedInverseImageBaseChangeMap_app_of_isProper`).

## Main results

All in the namespace `Stacks.Duality`.

* `twistedInverseImageBaseChangeMap_app_eq` — the base change map of Tag 0AA6 on an object.
* `quasiCoherentDerivedPullbackIsoRestrict` — `Lj^* ≅ j^*` on `D_QCoh` for an open immersion.
* `isIso_twistedInverseImageBaseChangeMap_app_iff` — invertibility of the one map is invertibility
  of the other.
* `isIso_twistedInverseImageBaseChangeMap_app_of_isProper` — the base change map of Tag 0AA6 is
  invertible on `D^+_QCoh(𝒪_Y)` when `f` is proper and `Y` Noetherian.

## References

* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open OpenImmersion

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  (hpushj' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward j').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushj : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward j).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
  (sq : IsPullback j' f' f j)
  [IsIso (twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf hpushf' hpushj sq)]

/-- **The base change map of [Stacks, Tag 0AA6] on an object**: `L(j')^*` of `a` of the unit of
`Lj^* ⊣ Rj_*`, then `L(j')^*` of `ξ⁻¹`, then the counit of `L(j')^* ⊣ Rj'_*`. -/
theorem twistedInverseImageBaseChangeMap_app_eq (K : quasiCoherentDerivedCategory Y) :
    (twistedInverseImageBaseChangeMap j' f' f j hpushj' hpushf hpushf' hpushj sq).app K =
      (quasiCoherentDerivedPullback' j').map ((twistedInverseImage f hpushf).map
          ((quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
            hpushj).unit.app K)) ≫
        (quasiCoherentDerivedPullback' j').map
          ((inv (twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf hpushf'
            hpushj sq)).app ((quasiCoherentDerivedPullback' j).obj K)) ≫
        (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
            hpushj').counit.app
          ((twistedInverseImage f' hpushf').obj ((quasiCoherentDerivedPullback' j).obj K)) := by
  simp [twistedInverseImageBaseChangeMap]

variable [IsOpenImmersion j] [IsOpenImmersion j']

/-- **Derived pullback and restriction along an open immersion agree on `D_QCoh`**, as the two
left adjoints of the derived direct image. -/
def quasiCoherentDerivedPullbackIsoRestrict {W Z : Scheme.{u}} (i : W ⟶ Z) [IsOpenImmersion i]
    (hpushi : ∀ (K : quasiCoherentDerivedCategory W) (n : ℤ),
      ((DerivedCategory.homologyFunctor Z.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent) :
    quasiCoherentDerivedPullback' i ≅
      quasiCoherentDerivedRestrict i (isQuasicoherent_homology_derivedRestrict i) :=
  ((quasiCoherentDerivedRestrictAdjunction i (isQuasicoherent_homology_derivedRestrict i)
    hpushi).leftAdjointUniq
    (quasiCoherentDerivedAdjunction i (isQuasicoherent_homology_derivedPullback' i) hpushi)).symm

/-- **The base change map of [Stacks, Tag 0AA6] along an open immersion is invertible at an
object exactly when the map of [Stacks, Tag 0A9L] is.** Both are invertible exactly when the
image of the unit `K ⟶ Rj_*(K|_V)` under `a` and restriction to `U` is: for the second this is
`Stacks.Duality.isIso_twistedInverseImageRestrictionMap_app_iff`, and for the first the same
argument applies once the counit of `L(j')^* ⊣ Rj'_*` is known to be invertible, which it is
because `L(j')^*` and `(j')^*` are both left adjoint to `Rj'_*`
(`quasiCoherentDerivedPullbackIsoRestrict`). The units of `Lj^* ⊣ Rj_*` and `j^* ⊣ Rj_*` differ by
the same identification. -/
theorem isIso_twistedInverseImageBaseChangeMap_app_iff (K : quasiCoherentDerivedCategory Y) :
    IsIso ((twistedInverseImageBaseChangeMap j' f' f j hpushj' hpushf hpushf' hpushj sq).app K) ↔
      IsIso ((twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj
          (isQuasicoherent_homology_derivedRestrict j)
          (isQuasicoherent_homology_derivedRestrict j') sq).app K) := by
  let adj₁ := quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j) hpushj
  let adj₂ := quasiCoherentDerivedRestrictAdjunction j (isQuasicoherent_homology_derivedRestrict j)
    hpushj
  let adj₁' := quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
    hpushj'
  let adj₂' := quasiCoherentDerivedRestrictAdjunction j'
    (isQuasicoherent_homology_derivedRestrict j') hpushj'
  let e := adj₂.leftAdjointUniq adj₁
  let e' := adj₂'.leftAdjointUniq adj₁'
  let a := twistedInverseImage f hpushf
  have hc₂ : IsIso adj₂'.counit := isIso_liftDerivedRestrictPushforwardAdjunction_counit j' _ _ _ _
  have hc₁ : ∀ Z, IsIso (adj₁'.counit.app Z) := fun Z =>
    IsIso.of_isIso_fac_left (Adjunction.leftAdjointUniq_hom_app_counit adj₂' adj₁' Z)
  have hη : adj₁.unit.app K = adj₂.unit.app K ≫
      (quasiCoherentDerivedPushforward j hpushj).map (e.hom.app K) :=
    (Adjunction.unit_leftAdjointUniq_hom_app adj₂ adj₁ K).symm
  rw [isIso_twistedInverseImageRestrictionMap_app_iff, twistedInverseImageBaseChangeMap_app_eq,
    isIso_comp_right_iff,
    ← NatIso.isIso_map_iff e' (a.map (adj₁.unit.app K)), hη, Functor.map_comp, Functor.map_comp]
  exact isIso_comp_right_iff _ _

/-- **The base change map of [Stacks, Tag 0AA6] is invertible on `D^+_QCoh` for a proper
morphism over a Noetherian scheme and an open immersion of the base.** This is
[Stacks, Tag 0A9P] (2), `Stacks.Duality.isIso_twistedInverseImageRestrictionMap_app_of_isProper`,
read through `isIso_twistedInverseImageBaseChangeMap_app_iff`. -/
theorem isIso_twistedInverseImageBaseChangeMap_app_of_isProper [IsNoetherian Y] [IsProper f]
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso ((twistedInverseImageBaseChangeMap j' f' f j hpushj' hpushf hpushf' hpushj sq).app K) :=
  (isIso_twistedInverseImageBaseChangeMap_app_iff j' f' f j hpushj' hpushf hpushf' hpushj sq
    K).2 (isIso_twistedInverseImageRestrictionMap_app_of_isProper j' f' f j sq K hK)

end Stacks.Duality

end

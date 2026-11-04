module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangeIsIso

/-!
# The base change map for the twisted inverse image of a Tor independent square

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of quasi-compact and quasi-separated schemes with `f` and `g` Tor
independent, and let `a`, `a'` be the right adjoints of `Rf_*`, `Rf'_*` on `D_QCoh`
([Stacks, Tag 0A9E]). Equation 48.5.0.1 of [Stacks, Tag 0AA6] is the transformation
`D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_{X'})`

```
L(g')^* ∘ a ⟶ L(g')^* ∘ a ∘ Rg_* ∘ Lg^* ⟵ L(g')^* ∘ Rg'_* ∘ a' ∘ Lg^* ⟶ a' ∘ Lg^*
```

whose middle arrow is `L(g')^* ⋆ ξ ⋆ Lg^*` for `ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*`, invertible by
[Stacks, Tag 0A9K]. Under `L(g')^* ⊣ Rg'_*` it corresponds to the transformation
`a ⟶ a ∘ Rg_* ∘ Lg^* ⟵ Rg'_* ∘ a' ∘ Lg^*`.

## Main definitions

* `Stacks.Duality.torIndependentTwistedInverseImageBaseChange` — the base change map
  `L(g')^* ∘ a ⟶ a' ∘ Lg^*` of [Stacks, Tag 0AA6].

## Main results

* `Stacks.Duality.torIndependentTwistedInverseImageBaseChange_homEquiv` — its transpose under
  `L(g')^* ⊣ Rg'_*` is `a(η_K) ≫ ξ⁻¹`.

## References

* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **The base change map `L(g')^* ∘ a ⟶ a' ∘ Lg^*` of [Stacks, Tag 0AA6]**, Equation 48.5.0.1,
for a cartesian square of quasi-compact and quasi-separated schemes with `f` and `g` Tor
independent: the unit of `Lg^* ⊣ Rg_*`, then the inverse of `L(g')^* ⋆ ξ ⋆ Lg^*`, which exists by
[Stacks, Tag 0A9K], then the counit of `L(g')^* ⊣ Rg'_*`. -/
@[stacks 0AA6]
def torIndependentTwistedInverseImageBaseChange (sq : IsPullback g' f' f g)
    (hTor : TorIndependent f g) :
    twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⋙
        quasiCoherentDerivedPullback' g' ⟶
      quasiCoherentDerivedPullback' g ⋙
        twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f') :=
  haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
  twistedInverseImageBaseChangeMap g' f' f g
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq

/-- **The adjoint form of the base change map of [Stacks, Tag 0AA6].** Under
`L(g')^* ⊣ Rg'_*` the component at `K` of `L(g')^* ∘ a ⟶ a' ∘ Lg^*` corresponds to
`a(K) ⟶ a(Rg_* Lg^* K) ⟵ Rg'_* a'(Lg^* K)`, the image under `a` of the unit of `Lg^* ⊣ Rg_*`
followed by the inverse of `ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*`. -/
@[stacks 0AA6 "the adjoint form a ⟶ a ∘ Rg_* ∘ Lg^* ⟵ Rg'_* ∘ a' ∘ Lg^*"]
theorem torIndependentTwistedInverseImageBaseChange_homEquiv (sq : IsPullback g' f' f g)
    (hTor : TorIndependent f g) (K : quasiCoherentDerivedCategory Y) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
    (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g')).homEquiv _ _
        ((torIndependentTwistedInverseImageBaseChange sq hTor).app K) =
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          ((quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).unit.app K) ≫
        (inv (twistedInverseImagePushforwardBaseChange g' f' f g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq)).app
            ((quasiCoherentDerivedPullback' g).obj K) := by
  rw [Equiv.apply_eq_iff_eq_symm_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc]
  simp only [torIndependentTwistedInverseImageBaseChange, twistedInverseImageBaseChangeMap,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id]
  exact congrArg (_ ≫ _ ≫ ·) (Category.comp_id _)

end Stacks.Duality

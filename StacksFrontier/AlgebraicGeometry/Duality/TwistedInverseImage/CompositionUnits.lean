module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionAssociativity
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DerivedPullbackUnitLaws
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.RightAdjointCompositorUnits
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion

/-!
# The two unit laws for the composition isomorphism of the twisted inverse image

Let `f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves
quasi-coherence of cohomology and whose restricted derived direct image has a right adjoint, and
write `p^×` for that right adjoint — the twisted inverse image of [Stacks, Tag 0A9E]. The
comparison `(p ≫ q)^× ≅ q^× ⋙ p^×` of [Stacks, Tag 0ATX] is
`Stacks.Duality.twistedInverseImageCompIso`, and `(𝟙 Y)^× ≅ 𝟭` is
`Stacks.Duality.twistedInverseImageIdIso`. This file proves that the two are compatible: the
comparison at `f ≫ 𝟙 Y` and at `𝟙 X ≫ f` is the identity comparison, whiskered.

These are conditions (b) and (c) of the definition of a pseudofunctor (Categories, Definition
4.29.5, [Stacks, Tag 003N]), whose condition (a) is
`Stacks.Duality.isIso_twistedInverseImageIdIso_hom_and_compIso_hom` below and whose condition
(d) is `Stacks.Duality.twistedInverseImageCompIso_hom_assoc_whiskering`. All four are about `f^×`;
the statement of [Stacks, Tag 0ATY], about `f^!`, is
`Stacks.Duality.exists_upperShriekPseudofunctor`.

Everything here is formal, and each statement is reduced to the same statement one level down:
the twisted inverse image is a right adjoint of derived direct image on the quasi-coherent
derived categories, which is the restriction of derived direct image on the unbounded derived
categories, which is a right adjoint of derived pullback. So the input is the pair of unit laws
for the composition isomorphism of *derived pullback*, and that pair is
`Stacks.Duality.derivedPullbackCompIso_id_comp` and
`Stacks.Duality.derivedPullbackCompIso_comp_id`.

## Main results

All in the namespace `Stacks.Duality`.

* `derivedPushforwardCompIso_id_comp` and `derivedPushforwardCompIso_comp_id` — the unit laws
  for the composition isomorphism `Rp_* ⋙ Rq_* ≅ R(p ≫ q)_*` of derived direct image on the
  unbounded derived categories of a scheme.
* `quasiCoherentDerivedPushforwardCompIso_id_comp_eq_leftUnitor` and
  `quasiCoherentDerivedPushforwardCompIso_comp_id_eq_rightUnitor` — the same on the quasi-coherent
  derived categories.
* `twistedInverseImageCompIso_id_comp_eq_rightUnitor_symm` and
  `twistedInverseImageCompIso_comp_id_eq_leftUnitor_symm` — the two unit laws for the comparison
  of [Stacks, Tag 0ATX], that is conditions (b) and (c) of [Stacks, Tag 0ATY].
* `isIso_twistedInverseImageIdIso_hom_and_compIso_hom` — condition (a) of [Stacks, Tag 0ATY],
  that the unit and the compositors are invertible. The proof is `inferInstance` twice: both
  data are `Iso`-typed, being built by uniqueness of a right adjoint.

## Implementation notes

*The input.* The unit laws for derived pullback,

```
L(𝟙 Y ≫ g)^* = Lg^* ⋙ L(𝟙 Y)^* ≅ Lg^*      and      L(f ≫ 𝟙 Y)^* = L(𝟙 Y)^* ⋙ Lf^* ≅ Lf^*
```

are proved at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` --
the only one at which `D_QCoh(𝒪_X)` has the direct sums [Stacks, Tag 0A9E] needs -- in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/DerivedPullbackUnitLaws.lean`. They
were hypotheses of the theorems below until that file was written, because
`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_id_comp` and
`...derivedPullbackCompIsoCanonical_comp_id` prove them only at
`CategoryTheory.HasDerivedCategory.standard` and `CategoryTheory.HasDerivedCategory` carries the
localization as data, so neither model's statement transports to the other -- exactly as for the
cocycle law; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/DerivedPullbackCocycle.lean`. Nothing
below carries a hypothesis beyond the quasi-coherence inputs of [Stacks, Tag 08D5] and the
adjointness of [Stacks, Tag 0A9E] that `Stacks.Duality.twistedInverseImage` needs in order to
exist at all.

*The route.* Each level is the mates calculus:
`CategoryTheory.Adjunction.rightAdjointCompNatTrans_comp_id` and
`...rightAdjointCompNatTrans_id_comp` carry a unit law from a compositor of left adjoints to its
mate, and `CategoryTheory.Adjunction.rightAdjointUniq_ofNatIsoLeft_comp_inv` identifies the
compositors here — all of which are built by uniqueness of a right adjoint — with such mates.
The bridge between a unit datum built by uniqueness of a right adjoint and the identification of
the left adjoints it was built from is
`CategoryTheory.Adjunction.leftAdjointIdIso_rightAdjointUniq_ofNatIsoLeft`.

*Relation to [Stacks, Tag 0ATY].* [Stacks, Tag 0ATY] asserts that the constructions of its
Lemmas 48.16.2 and 48.16.3 define a pseudofunctor `f ↦ f^!` in the sense of Categories,
Definition 4.29.5 ([Stacks, Tag 003N]). That statement is proved, for `f^!` on `D⁺_QCoh` and as a
bundled `CategoryTheory.Pseudofunctor`, by `Stacks.Duality.exists_upperShriekPseudofunctor` and
`Stacks.Duality.upperShriekPseudofunctor` in
`StacksFrontier/AlgebraicGeometry/Duality/Compactification/ShriekPseudofunctor.lean`, where the tag
is registered. The statements here are the corresponding conditions for the twisted inverse
image `f ↦ f^×` of [Stacks, Tag 0A9E] (the case of proper morphisms): the unit and compositors
are invertible, the two unit coherences, and the cocycle condition
`Stacks.Duality.twistedInverseImageCompIso_hom_assoc_whiskering`, which the chase for `f^!` uses.

*The source category.* Over a Noetherian base every object of `AlgebraicGeometry.FTS S` has
locally Noetherian quasi-compact underlying space, by
`AlgebraicGeometry.FTS.isLocallyNoetherian` and `AlgebraicGeometry.FTS.compactSpace`, so every
morphism of `FTS S` is quasi-compact and quasi-separated with quasi-compact target and
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward` applies to it. The
assignment `f ↦ f^×` is therefore total on `FTS S`, and the quasi-coherence hypotheses and
adjointness instances of the theorems below are all dischargeable there.

## References

* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 003N](https://stacks.math.columbia.edu/tag/003N)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0A9N](https://stacks.math.columbia.edu/tag/0A9N)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

/-! ### Derived direct image on the unbounded derived categories -/

section Unbounded

variable {X Y Z : Scheme.{u}}

/-- The identification of `L(𝟙 Y)^*` with the identity functor is the mate of the identification
of `R(𝟙 Y)_*` with the identity functor. The latter is *defined* as the comparison of two right
adjoints of `L(𝟙 Y)^*` read through the former, so this is
`CategoryTheory.Adjunction.leftAdjointIdIso_rightAdjointUniq_ofNatIsoLeft`. -/
theorem leftAdjointIdIso_derivedPushforwardIdIso (Y : Scheme.{u}) :
    Adjunction.leftAdjointIdIso (derivedAdjunction (𝟙 Y)) (derivedPushforwardIdIso Y) =
      derivedPullbackIdIso Y :=
  Adjunction.leftAdjointIdIso_rightAdjointUniq_ofNatIsoLeft (derivedAdjunction (𝟙 Y))
    (derivedPullbackIdIso Y)

/-- **The left unit law for the composition isomorphism of derived direct image.** Identifying
`R(𝟙 Y)_* ⋙ Rg_*` with `R(𝟙 Y ≫ g)_*` is the identification of `R(𝟙 Y)_*` with the identity
functor, whiskered by `Rg_*`.

Derived direct image is a right adjoint of derived pullback and both comparisons are the mates
of the corresponding comparisons of derived pullbacks, so this is
`CategoryTheory.Adjunction.rightAdjointCompNatTrans_comp_id` applied to the hypothesis. -/
theorem derivedPushforwardCompIso_id_comp (g : Y ⟶ Z) :
    derivedPushforwardCompIso (𝟙 Y) g =
      isoWhiskerRight (derivedPushforwardIdIso Y) (derivedPushforward g) ≪≫
        leftUnitor (derivedPushforward g) := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
  rw [derivedPushforwardCompIso, Adjunction.rightAdjointUniq_ofNatIsoLeft_comp_inv]
  refine Adjunction.rightAdjointCompNatTrans_comp_id (derivedAdjunction g)
    (derivedAdjunction (𝟙 Y)) (derivedPushforwardIdIso Y) _ ?_
  exact congrArg Iso.hom
    ((derivedPullbackCompIso_id_comp Y g).trans
      (by rw [leftAdjointIdIso_derivedPushforwardIdIso]))

/-- **The right unit law for the composition isomorphism of derived direct image.** Identifying
`Rf_* ⋙ R(𝟙 Y)_*` with `R(f ≫ 𝟙 Y)_*` is the identification of `R(𝟙 Y)_*` with the identity
functor, whiskered by `Rf_*`. -/
theorem derivedPushforwardCompIso_comp_id (f : X ⟶ Y) :
    derivedPushforwardCompIso f (𝟙 Y) =
      isoWhiskerLeft (derivedPushforward f) (derivedPushforwardIdIso Y) ≪≫
        rightUnitor (derivedPushforward f) := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
  rw [derivedPushforwardCompIso, Adjunction.rightAdjointUniq_ofNatIsoLeft_comp_inv]
  refine Adjunction.rightAdjointCompNatTrans_id_comp (derivedAdjunction (𝟙 Y))
    (derivedAdjunction f) (derivedPushforwardIdIso Y) _ ?_
  exact congrArg Iso.hom
    ((derivedPullbackCompIso_comp_id f).trans
      (by rw [leftAdjointIdIso_derivedPushforwardIdIso]))

end Unbounded

/-! ### Derived direct image on the quasi-coherent derived categories -/

section QuasiCoherent

variable {X Y Z : Scheme.{u}}

/-- **The left unit law for the composition isomorphism of derived direct image on the
quasi-coherent derived categories.** The isomorphism is the ambient one read on the full
subcategories, componentwise, so the law is the ambient one at each object. -/
theorem quasiCoherentDerivedPushforwardCompIso_id_comp_eq_leftUnitor (g : Y ⟶ Z)
    (hpushid : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward (𝟙 Y)).obj K.obj)).IsQuasicoherent)
    (hpushg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor Z.Modules i).obj
        ((derivedPushforward g).obj K.obj)).IsQuasicoherent) :
    quasiCoherentDerivedPushforwardCompIso (𝟙 Y) g hpushid hpushg hpushg =
      isoWhiskerRight (quasiCoherentDerivedPushforwardIdIso Y hpushid)
          (quasiCoherentDerivedPushforward g hpushg) ≪≫
        leftUnitor (quasiCoherentDerivedPushforward g hpushg) := by
  refine Iso.ext (NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ ?_))
  exact NatTrans.congr_app (congrArg Iso.hom (derivedPushforwardCompIso_id_comp g)) K.obj

/-- **The right unit law for the composition isomorphism of derived direct image on the
quasi-coherent derived categories.** -/
theorem quasiCoherentDerivedPushforwardCompIso_comp_id_eq_rightUnitor (f : X ⟶ Y)
    (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (hpushid : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward (𝟙 Y)).obj K.obj)).IsQuasicoherent) :
    quasiCoherentDerivedPushforwardCompIso f (𝟙 Y) hpushf hpushid hpushf =
      isoWhiskerLeft (quasiCoherentDerivedPushforward f hpushf)
          (quasiCoherentDerivedPushforwardIdIso Y hpushid) ≪≫
        rightUnitor (quasiCoherentDerivedPushforward f hpushf) := by
  refine Iso.ext (NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ ?_))
  exact NatTrans.congr_app (congrArg Iso.hom (derivedPushforwardCompIso_comp_id f)) K.obj

end QuasiCoherent

/-! ### The twisted inverse image -/

section TwistedInverseImage

variable {X Y Z : Scheme.{u}}

/-- The identification of `R(𝟙 Y)_*` on `D_QCoh(𝒪_Y)` with the identity functor is the mate of
the identification of `(𝟙 Y)^×` with the identity functor, the latter being defined as the
comparison of two right adjoints read through the former. -/
theorem leftAdjointIdIso_twistedInverseImageIdIso (Y : Scheme.{u})
    (hpushid : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward (𝟙 Y)).obj K.obj)).IsQuasicoherent) :
    Adjunction.leftAdjointIdIso (twistedInverseImageAdjunction (𝟙 Y) hpushid)
        (twistedInverseImageIdIso Y hpushid) =
      quasiCoherentDerivedPushforwardIdIso Y hpushid :=
  Adjunction.leftAdjointIdIso_rightAdjointUniq_ofNatIsoLeft
    (twistedInverseImageAdjunction (𝟙 Y) hpushid) (quasiCoherentDerivedPushforwardIdIso Y hpushid)

/-- **Condition (a) of [Stacks, Tag 0ATY]**: every datum of the assignment `f ↦ f^×` is
invertible. For a scheme `X` the identification `(𝟙 X)^× ≅ 𝟭` of
`Stacks.Duality.twistedInverseImageIdIso`, and for a composable pair `f`, `g` the comparison
`(f ≫ g)^× ≅ g^× ⋙ f^×` of [Stacks, Tag 0ATX], are isomorphisms of functors.

The proof is `inferInstance` twice: both data are produced by uniqueness of a right adjoint,
`CategoryTheory.Adjunction.rightAdjointUniq`, which returns an `Iso`, so invertibility holds by
construction. The statement records condition (a) of the definition of a pseudofunctor
(Categories, Definition 4.29.5, [Stacks, Tag 003N]) for `f ↦ f^×`, and it assumes nothing that
`Stacks.Duality.twistedInverseImageCompIso_id_comp_eq_rightUnitor_symm` does not: the binders are
exactly the quasi-coherence inputs of [Stacks, Tag 08D5] and the adjointness of
[Stacks, Tag 0A9E] that the two data need in order to exist. -/
theorem isIso_twistedInverseImageIdIso_hom_and_compIso_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (hpushidX : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward (𝟙 X)).obj K.obj)).IsQuasicoherent)
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
    [(quasiCoherentDerivedPushforward (f ≫ g) hpushfg).IsLeftAdjoint] :
    IsIso (twistedInverseImageIdIso X hpushidX).hom ∧
      IsIso (twistedInverseImageCompIso f g hpushf hpushg hpushfg).hom :=
  ⟨inferInstance, inferInstance⟩

/-- **Condition (b) of [Stacks, Tag 0ATY]**, the left unit law for the comparison of
[Stacks, Tag 0ATX]: the comparison `(𝟙 X ≫ g)^× ≅ g^× ⋙ (𝟙 X)^×` is the identification of
`(𝟙 X)^×` with the identity functor, whiskered by `g^×`.

The twisted inverse image is a right adjoint of derived direct image on the quasi-coherent
derived categories and the comparison of [Stacks, Tag 0ATX] is the mate of the composition
isomorphism of the latter, by `Stacks.Duality.twistedInverseImageCompIso_hom_eq`, so this is
`CategoryTheory.Adjunction.rightAdjointCompNatTrans_id_comp` applied to
`Stacks.Duality.quasiCoherentDerivedPushforwardCompIso_id_comp_eq_leftUnitor`. -/
theorem twistedInverseImageCompIso_id_comp_eq_rightUnitor_symm (g : X ⟶ Z)
    (hpushid : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward (𝟙 X)).obj K.obj)).IsQuasicoherent)
    (hpushg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Z.Modules i).obj
        ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
    [instg : (quasiCoherentDerivedPushforward g hpushg).IsLeftAdjoint] :
    @twistedInverseImageCompIso X X Z (𝟙 X) g hpushid hpushg hpushg
        (isLeftAdjoint_quasiCoherentDerivedPushforward_id X hpushid) instg instg =
      (isoWhiskerLeft (twistedInverseImage g hpushg)
          (twistedInverseImageIdIso X hpushid) ≪≫
        rightUnitor (twistedInverseImage g hpushg)).symm := by
  refine Iso.ext ?_
  rw [@twistedInverseImageCompIso_hom_eq X X Z (𝟙 X) g hpushid hpushg hpushg
    (isLeftAdjoint_quasiCoherentDerivedPushforward_id X hpushid) instg instg]
  refine Adjunction.rightAdjointCompNatTrans_id_comp
    (twistedInverseImageAdjunction (𝟙 X) hpushid) (twistedInverseImageAdjunction g hpushg)
    (twistedInverseImageIdIso X hpushid) _ ?_
  exact congrArg Iso.hom
    ((quasiCoherentDerivedPushforwardCompIso_id_comp_eq_leftUnitor g hpushid hpushg).trans
      (by rw [leftAdjointIdIso_twistedInverseImageIdIso]))

/-- **Condition (c) of [Stacks, Tag 0ATY]**, the right unit law for the comparison of
[Stacks, Tag 0ATX]: the comparison `(f ≫ 𝟙 Y)^× ≅ (𝟙 Y)^× ⋙ f^×` is the identification of
`(𝟙 Y)^×` with the identity functor, whiskered by `f^×`. -/
theorem twistedInverseImageCompIso_comp_id_eq_leftUnitor_symm (f : X ⟶ Y)
    (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (hpushid : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward (𝟙 Y)).obj K.obj)).IsQuasicoherent)
    [instf : (quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint] :
    @twistedInverseImageCompIso X Y Y f (𝟙 Y) hpushf hpushid hpushf instf
        (isLeftAdjoint_quasiCoherentDerivedPushforward_id Y hpushid) instf =
      (isoWhiskerRight (twistedInverseImageIdIso Y hpushid)
          (twistedInverseImage f hpushf) ≪≫
        leftUnitor (twistedInverseImage f hpushf)).symm := by
  refine Iso.ext ?_
  rw [@twistedInverseImageCompIso_hom_eq X Y Y f (𝟙 Y) hpushf hpushid hpushf instf
    (isLeftAdjoint_quasiCoherentDerivedPushforward_id Y hpushid) instf]
  refine Adjunction.rightAdjointCompNatTrans_comp_id
    (twistedInverseImageAdjunction f hpushf) (twistedInverseImageAdjunction (𝟙 Y) hpushid)
    (twistedInverseImageIdIso Y hpushid) _ ?_
  exact congrArg Iso.hom
    ((quasiCoherentDerivedPushforwardCompIso_comp_id_eq_rightUnitor f hpushf hpushid).trans
      (by rw [leftAdjointIdIso_twistedInverseImageIdIso]))

end TwistedInverseImage

end Stacks.Duality

end

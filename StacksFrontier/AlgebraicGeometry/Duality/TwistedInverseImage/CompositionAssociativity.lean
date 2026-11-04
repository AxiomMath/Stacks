module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DerivedPullbackCocycle
public import StacksFrontier.CategoryTheory.Comma.Over.PullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionExtra

/-!
# The cocycle identity for the composition isomorphism of the twisted inverse image

Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ T` be morphisms of schemes along which derived direct
image preserves quasi-coherence of cohomology, and suppose the restricted derived direct images
along them and along the three composites have right adjoints. Writing `p^×` for the right
adjoint of `Rp_*` on the quasi-coherent derived categories — the twisted inverse image of
[Stacks, Tag 0A9E] — `Stacks.Duality.twistedInverseImageCompIso` is the canonical isomorphism
`(p ≫ q)^× ≅ q^× ⋙ p^×` carrying [Stacks, Tag 0ATX], and there are two ways of using it to
identify `(f ≫ g ≫ h)^×` with `h^× ⋙ g^× ⋙ f^×`: through `f ≫ g` or through `g ≫ h`. This file
proves that they agree,

```
(f ≫ g ≫ h)^×  →  h^× ⋙ (f ≫ g)^×  →  h^× ⋙ g^× ⋙ f^×
(f ≫ g ≫ h)^×  →  (g ≫ h)^× ⋙ f^×  →  h^× ⋙ g^× ⋙ f^×
```

which in the source's order of composition is the commutative square

```
(h ∘ g ∘ f)^!  --γ_{A+B}-->  f^! ∘ (h ∘ g)^!
     |γ_{B+C}                     |γ_C
(g ∘ f)^! ∘ h^!  --γ_A-->  f^! ∘ g^! ∘ h^!
```

whose commutativity is the whole of the source's proof of its Lemma 48.16.4.

## Main results

All in the namespace `Stacks.Duality`.

* `twistedInverseImageCompIso_hom_eq` — the comparison of [Stacks, Tag 0ATX] is the mate, under
  the three adjunctions of [Stacks, Tag 0A9E], of the composition isomorphism
  `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of derived direct image. This is what makes the cocycle identity a
  formal consequence of the one for derived direct image.
* `derivedPushforwardCompIso_cocycle` — the cocycle identity for
  `Stacks.Duality.derivedPushforwardCompIso` on the unbounded derived categories.
* `quasiCoherentDerivedPushforwardCompIso_hom_assoc_whiskering` — the cocycle identity for
  `Stacks.Duality.quasiCoherentDerivedPushforwardCompIso`, the composition isomorphism of derived
  direct image on the quasi-coherent derived categories.
* `twistedInverseImageCompIso_hom_assoc_whiskering` — the cocycle identity for
  `Stacks.Duality.twistedInverseImageCompIso`, that is the commutative square displayed above.

## Implementation notes

*The route.* Every isomorphism in the chain is a mate: `p^×` is the right adjoint of `Rp_*`, and
`Rp_*` is the right adjoint of `Lp^*`. So the cocycle identity is carried twice along
`CategoryTheory.Adjunction.rightAdjointCompNatTrans_assoc`, which transports it from a family of
compositors of left adjoints to the compositors of the right adjoints, starting from the cocycle
identity for derived pullback, `Stacks.Duality.derivedPullbackCompComparison_cocycle`.

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

The *source category* is not among the obstructions. Over a Noetherian base every object of
`AlgebraicGeometry.FTS S` has locally Noetherian quasi-compact underlying space, by
`AlgebraicGeometry.FTS.isLocallyNoetherian` and `AlgebraicGeometry.FTS.compactSpace`, so every
morphism of `FTS S` is quasi-compact and quasi-separated with quasi-compact target and
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward` applies to every one of
them. The assignment `f ↦ f^×` is therefore total on `FTS S`, and the hypotheses `hpushf`,
`hpushg`, `hpushfg` and the three adjointness instances below — the same ones
`Stacks.Duality.twistedInverseImageCompIso` takes — are all dischargeable there.

*Why the derived-pullback step is redone.* See the module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/DerivedPullbackCocycle.lean`: the
cocycle identity for derived pullback and derived direct image of sheaves of modules on ringed
spaces is proved in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/CompositionAssociativity.lean`, but
only at `CategoryTheory.HasDerivedCategory.standard`, while `Stacks.Duality.twistedInverseImage`
lives at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` — the only
one at which `D_QCoh(𝒪_X)` has the direct sums [Stacks, Tag 0A9E] needs.

## References

* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 003N](https://stacks.math.columbia.edu/tag/003N)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0A9N](https://stacks.math.columbia.edu/tag/0A9N)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

/-! ### Derived direct image on the unbounded derived categories -/

section Unbounded

variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of derived direct image is the mate,
under the two derived adjunctions of [Stacks, Tag 079W], of the composition isomorphism
`Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of derived pullback. This is how it is defined; the equation records
it in the form the mates calculus consumes. -/
private theorem derivedPushforwardCompIso_inv_eq :
    (derivedPushforwardCompIso f g).inv =
      Adjunction.rightAdjointCompNatTrans (derivedAdjunction g) (derivedAdjunction f)
        (derivedAdjunction (f ≫ g)) (derivedPullbackCompIso f g).hom := by
  ext K
  simp [derivedPushforwardCompIso, Adjunction.rightAdjointCompNatTrans,
    Adjunction.rightAdjointUniq, conjugateEquiv]

/-- **The cocycle identity for the composition isomorphism of derived direct image** on the
unbounded derived categories of schemes. Derived direct image is the right adjoint of derived
pullback and its compositor is the mate of the compositor of derived pullback, so this is
`CategoryTheory.Adjunction.rightAdjointCompNatTrans_assoc` applied to
`Stacks.Duality.derivedPullbackCompComparison_cocycle`. -/
theorem derivedPushforwardCompIso_cocycle :
    Functor.isoWhiskerRight (derivedPushforwardCompIso f g) (derivedPushforward h) ≪≫
        derivedPushforwardCompIso (f ≫ g) h =
      Functor.associator (derivedPushforward f) (derivedPushforward g)
            (derivedPushforward h) ≪≫
        Functor.isoWhiskerLeft (derivedPushforward f) (derivedPushforwardCompIso g h) ≪≫
          derivedPushforwardCompIso f (g ≫ h) := by
  have e₃ : (derivedPushforwardCompIso (f ≫ g) h).inv =
      Adjunction.rightAdjointCompNatTrans (derivedAdjunction h) (derivedAdjunction (f ≫ g))
        (derivedAdjunction (f ≫ g ≫ h)) (derivedPullbackCompIso (f ≫ g) h).hom :=
    derivedPushforwardCompIso_inv_eq (f ≫ g) h
  have key := Adjunction.rightAdjointCompNatTrans_assoc (derivedAdjunction h)
    (derivedAdjunction g) (derivedAdjunction f) (derivedAdjunction (g ≫ h))
    (derivedAdjunction (f ≫ g)) (derivedAdjunction (f ≫ g ≫ h))
    (derivedPullbackCompIso g h).hom (derivedPullbackCompIso f g).hom
    (derivedPullbackCompIso (f ≫ g) h).hom (derivedPullbackCompIso f (g ≫ h)).hom
    (by
      have hp : Functor.whiskerLeft (derivedPullback h) (derivedPullbackCompIso f g).hom ≫
            (derivedPullbackCompIso (f ≫ g) h).hom =
          (Functor.associator (derivedPullback h) (derivedPullback g)
              (derivedPullback f)).inv ≫
            Functor.whiskerRight (derivedPullbackCompIso g h).hom (derivedPullback f) ≫
              (derivedPullbackCompIso f (g ≫ h)).hom :=
        derivedPullbackCompComparison_cocycle f.toLRSHom.toShHom g.toLRSHom.toShHom
          h.toLRSHom.toShHom
      exact (Iso.inv_comp_eq _).1 hp.symm)
  rw [← derivedPushforwardCompIso_inv_eq f g, ← derivedPushforwardCompIso_inv_eq g h, ← e₃,
    ← derivedPushforwardCompIso_inv_eq f (g ≫ h)] at key
  refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Category.assoc]
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).2 ((Category.assoc _ _ _).trans key.symm)

end Unbounded

/-! ### Derived direct image on the quasi-coherent derived categories -/

section QuasiCoherent

variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpushh : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((derivedPushforward h).obj K.obj)).IsQuasicoherent)
  (hpushfg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (f ≫ g)).obj K.obj)).IsQuasicoherent)
  (hpushgh : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((derivedPushforward (g ≫ h)).obj K.obj)).IsQuasicoherent)
  (hpushfgh : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((derivedPushforward (f ≫ g ≫ h)).obj K.obj)).IsQuasicoherent)

/-- **The cocycle identity for the composition isomorphism of derived direct image on the
quasi-coherent derived categories.** The isomorphism is the ambient one of
`Stacks.Duality.derivedPushforwardCompIso` read on the full subcategories, componentwise, so the
identity is the ambient one at each object. -/
theorem quasiCoherentDerivedPushforwardCompIso_hom_assoc_whiskering :
    Functor.whiskerRight
          (quasiCoherentDerivedPushforwardCompIso f g hpushf hpushg hpushfg).hom
          (quasiCoherentDerivedPushforward h hpushh) ≫
        (quasiCoherentDerivedPushforwardCompIso (f ≫ g) h hpushfg hpushh hpushfgh).hom =
      (Functor.associator (quasiCoherentDerivedPushforward f hpushf)
            (quasiCoherentDerivedPushforward g hpushg)
            (quasiCoherentDerivedPushforward h hpushh)).hom ≫
        Functor.whiskerLeft (quasiCoherentDerivedPushforward f hpushf)
          (quasiCoherentDerivedPushforwardCompIso g h hpushg hpushh hpushgh).hom ≫
          (quasiCoherentDerivedPushforwardCompIso f (g ≫ h) hpushf hpushgh hpushfgh).hom := by
  have amb := congrArg Iso.hom (derivedPushforwardCompIso_cocycle f g h)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom] at amb
  exact NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ (NatTrans.congr_app amb K.obj))

end QuasiCoherent

/-! ### The twisted inverse image -/

section TwistedInverseImage

variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)

/-- **The comparison of [Stacks, Tag 0ATX] is a mate.** Under the adjunctions `Rf_* ⊣ f^×`,
`Rg_* ⊣ g^×` and `R(f ≫ g)_* ⊣ (f ≫ g)^×` of [Stacks, Tag 0A9E], the isomorphism
`(f ≫ g)^× ≅ g^× ⋙ f^×` is the natural transformation conjugate to the composition isomorphism
`Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of derived direct image. This is what pins the comparison down: the
coherence satisfied by the compositor of derived direct image passes to it formally. -/
theorem twistedInverseImageCompIso_hom_eq
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
    (twistedInverseImageCompIso f g hpushf hpushg hpushfg).hom =
      Adjunction.rightAdjointCompNatTrans (twistedInverseImageAdjunction f hpushf)
        (twistedInverseImageAdjunction g hpushg) (twistedInverseImageAdjunction (f ≫ g) hpushfg)
        (quasiCoherentDerivedPushforwardCompIso f g hpushf hpushg hpushfg).hom := by
  ext K
  simp [twistedInverseImageCompIso, Adjunction.rightAdjointCompNatTrans,
    Adjunction.rightAdjointUniq, conjugateEquiv]

variable
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpushh : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((derivedPushforward h).obj K.obj)).IsQuasicoherent)
  (hpushfg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (f ≫ g)).obj K.obj)).IsQuasicoherent)
  (hpushgh : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((derivedPushforward (g ≫ h)).obj K.obj)).IsQuasicoherent)
  (hpushfgh : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((derivedPushforward (f ≫ g ≫ h)).obj K.obj)).IsQuasicoherent)
  [instf : (quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [instg : (quasiCoherentDerivedPushforward g hpushg).IsLeftAdjoint]
  [insth : (quasiCoherentDerivedPushforward h hpushh).IsLeftAdjoint]
  [instfg : (quasiCoherentDerivedPushforward (f ≫ g) hpushfg).IsLeftAdjoint]
  [instgh : (quasiCoherentDerivedPushforward (g ≫ h) hpushgh).IsLeftAdjoint]
  [instfgh : (quasiCoherentDerivedPushforward (f ≫ g ≫ h) hpushfgh).IsLeftAdjoint]

/-- **The cocycle identity for the composition isomorphism of the twisted inverse image.** For
`f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ W` the two ways of identifying `(f ≫ g ≫ h)^×` with
`h^× ⋙ g^× ⋙ f^×` through the comparison of [Stacks, Tag 0ATX] — one through `f ≫ g`, the other
through `g ≫ h` — agree. In the source's order of composition this is the commutative square

```
(h ∘ g ∘ f)^!  --γ_{A+B}-->  f^! ∘ (h ∘ g)^!
     |γ_{B+C}                     |γ_C
(g ∘ f)^! ∘ h^!  --γ_A-->  f^! ∘ g^! ∘ h^!
```

of [Stacks, Tag 0ATY], which is condition (d) — the cocycle condition — of the definition of a
pseudo functor ([Stacks, Tag 003N]) and the whole content of the source's proof of its Lemma
48.16.4. Conditions (b) and (c) are the two theorems of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/CompositionUnits.lean`. The statement
for `f^!` is `Stacks.Duality.upperShriekCompIsoAtModel_cocycle`, which uses this one.

Each comparison is the mate of the composition isomorphism of derived direct image, by
`Stacks.Duality.twistedInverseImageCompIso_hom_eq`, so the identity is
`CategoryTheory.Adjunction.rightAdjointCompNatTrans_assoc` applied to
`Stacks.Duality.quasiCoherentDerivedPushforwardCompIso_hom_assoc_whiskering`. -/
theorem twistedInverseImageCompIso_hom_assoc_whiskering :
    (@twistedInverseImageCompIso X Z W (f ≫ g) h hpushfg hpushh hpushfgh
          instfg insth instfgh).hom ≫
        Functor.whiskerLeft (twistedInverseImage h hpushh)
          (twistedInverseImageCompIso f g hpushf hpushg hpushfg).hom =
      (twistedInverseImageCompIso f (g ≫ h) hpushf hpushgh hpushfgh).hom ≫
        Functor.whiskerRight
            (twistedInverseImageCompIso g h hpushg hpushh hpushgh).hom
            (twistedInverseImage f hpushf) ≫
          (Functor.associator (twistedInverseImage h hpushh) (twistedInverseImage g hpushg)
            (twistedInverseImage f hpushf)).hom := by
  simp only [@twistedInverseImageCompIso_hom_eq X Z W (f ≫ g) h hpushfg hpushh hpushfgh
      instfg insth instfgh,
    twistedInverseImageCompIso_hom_eq f g hpushf hpushg hpushfg,
    twistedInverseImageCompIso_hom_eq f (g ≫ h) hpushf hpushgh hpushfgh,
    twistedInverseImageCompIso_hom_eq g h hpushg hpushh hpushgh]
  exact Adjunction.rightAdjointCompNatTrans_assoc
    (twistedInverseImageAdjunction f hpushf) (twistedInverseImageAdjunction g hpushg)
    (twistedInverseImageAdjunction h hpushh) (twistedInverseImageAdjunction (f ≫ g) hpushfg)
    (twistedInverseImageAdjunction (g ≫ h) hpushgh)
    (twistedInverseImageAdjunction (f ≫ g ≫ h) hpushfgh) _ _ _ _
    (quasiCoherentDerivedPushforwardCompIso_hom_assoc_whiskering f g h hpushf hpushg hpushh
      hpushfg hpushgh hpushfgh)

end TwistedInverseImage

end Stacks.Duality

end

module

public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleGlobalDescent
public import StacksFrontier.CategoryTheory.Sites.Descent.PrestackOfCover
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonDescentBaseChange

/-!
# Effective descent of étale sheaves is local for an étale covering of the target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `{g i : Y i ⟶ Y}` be an étale covering. Effective descent of spaces-étale
sheaves along `f` — the assertion that a sheaf on `Y` may be recovered from a sheaf on `X`
together with a gluing datum over `X ×_Y X` — can be tested on the covering: if it holds for
the base change `X ×_Y Y i ⟶ Y i` of `f` along each member and for the base change
`X ×_Y Y i ×_Y Y j ⟶ Y i ×_Y Y j` along each pairwise overlap, then it holds for `f`. This is
**Stacks 0GFT**.

## Main definitions

* `AlgebraicGeometry.Space.spacesChosenPullback`: the fibre product of two morphisms of
  algebraic spaces, as a chosen fibre product;
* `AlgebraicGeometry.Space.spacesEtalePseudofunctorAdjunction`: the adjunction of Stacks 03G2
  between the spaces-étale inverse and direct images, with its left adjoint spelled as the
  `map` of `AlgebraicGeometry.Space.spacesEtalePseudofunctor`.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_isEtaleCovering` is
  **Stacks 0GFT** for the pseudofunctor of spaces-étale inverse images;
* `AlgebraicGeometry.Space.isIso_mateEquiv_commSqTwoSquare`: the base-change `2`-cell of the
  pseudofunctor of spaces-étale inverse images, attached to a cartesian square with étale
  bottom arrow, is invertible (Stacks 03LR, part (1));
* `AlgebraicGeometry.Space.isPrestackFor_ofArrows_singleton`: the full faithfulness half, and
  `AlgebraicGeometry.Space.isIso_singletonDescentAdjunction_counit`: the essential
  surjectivity half.

## References

* [Stacks Project, Tag 0GFT](https://stacks.math.columbia.edu/tag/0GFT)
* [Stacks Project, Tag 0GFS](https://stacks.math.columbia.edu/tag/0GFS)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe t u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse-image 2-cell of a cartesian square -/

section

variable {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The composition comparison of the spaces-étale inverse images is the mate of the one for
the direct images. -/
theorem spacesEtaleInverseImage_comp_hom {U V W : AlgebraicSpaces B S hS}
    (h : U ⟶ V) (k : V ⟶ W) :
    (spacesEtaleInverseImage_comp B S hS h k).hom =
      (conjugateEquiv ((spacesEtaleAdjunction B S hS k).comp (spacesEtaleAdjunction B S hS h))
          (spacesEtaleAdjunction B S hS (h ≫ k))).symm
        (spacesEtaleSheafPushforwardComp B S hS h k).inv := rfl

/-- The inverse of the composition comparison of the spaces-étale inverse images is the mate of
the composition comparison of the direct images. -/
theorem spacesEtaleInverseImage_comp_inv {U V W : AlgebraicSpaces B S hS}
    (h : U ⟶ V) (k : V ⟶ W) :
    (spacesEtaleInverseImage_comp B S hS h k).inv =
      (conjugateEquiv (spacesEtaleAdjunction B S hS (h ≫ k))
          ((spacesEtaleAdjunction B S hS k).comp (spacesEtaleAdjunction B S hS h))).symm
        (spacesEtaleSheafPushforwardComp B S hS h k).hom := rfl

/-- The mate of the identification of the inverse images of two equal morphisms is the
identification of their direct images. -/
theorem conjugateEquiv_spacesEtaleInverseImage_eqToHom {U V : AlgebraicSpaces B S hS}
    {u v : U ⟶ V} (e : u = v) :
    conjugateEquiv (spacesEtaleAdjunction B S hS u) (spacesEtaleAdjunction B S hS v)
        (eqToHom (congrArg (fun k : U ⟶ V => spacesEtaleInverseImage B S hS k) e.symm)) =
      eqToHom (congrArg (fun k : U ⟶ V => spacesEtaleSheafPushforward B S hS k) e) := by
  subst e
  simp

/-- The comparison isomorphism attached to a commutative square, written out through the two
composition constraints of the pseudofunctor and the identification of the two composites. -/
theorem spacesEtalePseudofunctor_isoMapOfCommSq_hom (w : i ≫ f = f' ≫ g) :
    (Cat.Hom.toNatIso ((spacesEtalePseudofunctor B S hS).isoMapOfCommSq
        (CommSq.mk w).op.toLoc)).hom =
      (((spacesEtalePseudofunctor B S hS).mapComp g.op.toLoc f'.op.toLoc).inv.toNatTrans ≫
        (eqToHom (congrArg (fun k : X' ⟶ Y =>
          (spacesEtalePseudofunctor B S hS).map k.op.toLoc) w.symm)).toNatTrans) ≫
        ((spacesEtalePseudofunctor B S hS).mapComp f.op.toLoc i.op.toLoc).hom.toNatTrans :=
  (congrArg (fun e => e.hom.toNatTrans)
    (Pseudofunctor.isoMapOfCommSq_eq_comp (spacesEtalePseudofunctor B S hS) w)).trans
      (Category.assoc _ _ _).symm

/-- The identification of the `map`s of two equal morphisms, read on the underlying
functors. -/
theorem eqToHom_spacesEtalePseudofunctor_map_toNatTrans {U V : AlgebraicSpaces B S hS}
    {u v : U ⟶ V} (e : u = v) :
    (eqToHom (congrArg (fun k : U ⟶ V =>
        (spacesEtalePseudofunctor B S hS).map k.op.toLoc) e)).toNatTrans =
      eqToHom (congrArg (fun k : U ⟶ V => spacesEtaleInverseImage B S hS k) e) := by
  subst e
  rfl

/-- The inverse-image `2`-cell of a commutative square, assembled from the composition
comparison of the inverse images on the two diagonals. -/
theorem spacesEtaleInverseImage_isoMapOfCommSq_hom (w : i ≫ f = f' ≫ g) :
    (Cat.Hom.toNatIso ((spacesEtalePseudofunctor B S hS).isoMapOfCommSq
        (CommSq.mk w).op.toLoc)).hom =
      ((spacesEtaleInverseImage_comp B S hS f' g).inv ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => spacesEtaleInverseImage B S hS k) w.symm)) ≫
        (spacesEtaleInverseImage_comp B S hS i f).hom := by
  exact (spacesEtalePseudofunctor_isoMapOfCommSq_hom B S hS i f' f g w).trans <|
    congrArg (fun z => (((spacesEtalePseudofunctor B S hS).mapComp
      g.op.toLoc f'.op.toLoc).inv.toNatTrans ≫ z) ≫
    ((spacesEtalePseudofunctor B S hS).mapComp f.op.toLoc i.op.toLoc).hom.toNatTrans)
    (eqToHom_spacesEtalePseudofunctor_map_toNatTrans B S hS w.symm)

/-- **The inverse-image comparison of a commutative square is conjugate to the direct-image
one.** -/
theorem conjugateEquiv_spacesEtalePseudofunctor_isoMapOfCommSq (w : i ≫ f = f' ≫ g) :
    conjugateEquiv ((spacesEtaleAdjunction B S hS f).comp (spacesEtaleAdjunction B S hS i))
        ((spacesEtaleAdjunction B S hS g).comp (spacesEtaleAdjunction B S hS f'))
        (Cat.Hom.toNatIso ((spacesEtalePseudofunctor B S hS).isoMapOfCommSq
          (CommSq.mk w).op.toLoc)).hom =
      spacesPushforwardCompSquare B S hS i f' f g w := by
  rw [spacesEtaleInverseImage_isoMapOfCommSq_hom B S hS i f' f g w,
    ← conjugateEquiv_comp _ (spacesEtaleAdjunction B S hS (i ≫ f)) _,
    ← conjugateEquiv_comp _ (spacesEtaleAdjunction B S hS (f' ≫ g)) _,
    spacesEtaleInverseImage_comp_hom, spacesEtaleInverseImage_comp_inv,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    conjugateEquiv_spacesEtaleInverseImage_eqToHom B S hS w]
  rfl

/-- The base-change `2`-cell of Stacks 03LR, part (1), on the spaces-étale topoi is the mate of
the comparison of the two composite direct images. -/
theorem spacesToposBaseChangeSquare_eq (sq : IsPullback i f' f g) :
    spacesToposBaseChangeSquare B S hS i f' f g sq =
      (mateEquiv (spacesEtaleAdjunction B S hS i) (spacesEtaleAdjunction B S hS g)).symm
        (TwoSquare.mk _ _ _ _ (spacesPushforwardCompSquare B S hS i f' f g sq.w)) := rfl

/-- **The mate of the inverse-image `2`-cell of a cartesian square is the base-change `2`-cell
of Stacks 03LR, part (1).** -/
theorem mateEquiv_spacesEtalePseudofunctor_isoMapOfCommSq (sq : IsPullback i f' f g) :
    (mateEquiv (spacesEtaleAdjunction B S hS f) (spacesEtaleAdjunction B S hS f')
        (commSqTwoSquare (spacesEtalePseudofunctor B S hS) sq.w)).natTrans =
      spacesToposBaseChangeSquare B S hS i f' f g sq := by
  have key := iterated_mateEquiv_conjugateEquiv (spacesEtaleAdjunction B S hS f)
    (spacesEtaleAdjunction B S hS f') (spacesEtaleAdjunction B S hS g)
    (spacesEtaleAdjunction B S hS i)
    (commSqTwoSquare (spacesEtalePseudofunctor B S hS) sq.w)
  rw [conjugateEquiv_spacesEtalePseudofunctor_isoMapOfCommSq B S hS i f' f g sq.w] at key
  rw [spacesToposBaseChangeSquare_eq B S hS i f' f g sq]
  exact (Equiv.eq_symm_apply (mateEquiv (spacesEtaleAdjunction B S hS i)
    (spacesEtaleAdjunction B S hS g))).mpr key

/-- **Stacks 03LR, part (1), for the pseudofunctor of spaces-étale inverse images.** For a
cartesian square with étale bottom arrow, the base-change `2`-cell obtained as the mate of the
inverse-image comparison is invertible. -/
theorem isIso_mateEquiv_spacesEtalePseudofunctor_isoMapOfCommSq (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    IsIso (mateEquiv (spacesEtaleAdjunction B S hS f) (spacesEtaleAdjunction B S hS f')
      (commSqTwoSquare (spacesEtalePseudofunctor B S hS) sq.w)).natTrans :=
  (congrArg IsIso (mateEquiv_spacesEtalePseudofunctor_isoMapOfCommSq B S hS i f' f g sq)).mpr
    (isIso_spacesToposBaseChangeSquare B S hS i f' f g sq hg)

end

/-! ### Chosen fibre products and the inverse-image adjunction -/

/-- The fibre product of two morphisms of algebraic spaces over `S`, as a chosen fibre
product. -/
noncomputable def spacesChosenPullback {U V W : AlgebraicSpaces B S hS}
    (a : U ⟶ W) (b : V ⟶ W) : ChosenPullback a b where
  pullback := AlgebraicSpaces.fiberProduct B S hS a b
  p₁ := ObjectProperty.homMk (pullback.fst a.hom b.hom)
  p₂ := ObjectProperty.homMk (pullback.snd a.hom b.hom)
  condition := ObjectProperty.hom_ext _ pullback.condition
  isLimit := (AlgebraicSpaces.isPullback_fiberProduct B S hS a b).isLimit

/-- The fibres of the pseudofunctor of spaces-étale inverse images have equalizers. -/
instance hasEqualizers_spacesEtalePseudofunctor_obj (U : AlgebraicSpaces B S hS) :
    HasEqualizers ((spacesEtalePseudofunctor B S hS).obj (.mk (.op U))) :=
  inferInstanceAs (HasEqualizers (Sheaf (SpacesEtale.topology B S hS U) (Type (u + 1))))

/-- The inverse images of the pseudofunctor of spaces-étale inverse images preserve finite
limits. -/
instance preservesFiniteLimits_spacesEtalePseudofunctor_map
    {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) :
    PreservesFiniteLimits ((spacesEtalePseudofunctor B S hS).map h.op.toLoc).toFunctor :=
  (spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi.preservesFiniteLimits

/-- The adjunction of Stacks 03G2 between the spaces-étale inverse and direct images, with its
left adjoint written as the `map` of `AlgebraicGeometry.Space.spacesEtalePseudofunctor`. -/
noncomputable def spacesEtalePseudofunctorAdjunction {U V : AlgebraicSpaces B S hS}
    (h : U ⟶ V) :
    ((spacesEtalePseudofunctor B S hS).map h.op.toLoc).toFunctor ⊣
      spacesEtaleSheafPushforward B S hS h :=
  spacesEtaleAdjunction B S hS h

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03LR, part (1), on components.** For a cartesian square with étale bottom arrow
the base-change `2`-cell of the pseudofunctor is invertible at every sheaf. -/
theorem isIso_mateEquiv_commSqTwoSquare {X' Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom)
    (M : (spacesEtalePseudofunctor B S hS).obj (.mk (.op X))) :
    IsIso ((mateEquiv (spacesEtalePseudofunctorAdjunction B S hS f)
      (spacesEtalePseudofunctorAdjunction B S hS f')
      (commSqTwoSquare (spacesEtalePseudofunctor B S hS) sq.w)).natTrans.app M) := by
  have h : IsIso (mateEquiv (spacesEtalePseudofunctorAdjunction B S hS f)
      (spacesEtalePseudofunctorAdjunction B S hS f')
      (commSqTwoSquare (spacesEtalePseudofunctor B S hS) sq.w)).natTrans :=
    isIso_mateEquiv_spacesEtalePseudofunctor_isoMapOfCommSq B S hS i f' f g sq hg
  exact NatIso.isIso_app_of_isIso _ M

/-- **The counit of singleton descent along `f` becomes invertible after an étale base
change** along which descent is effective. -/
theorem isIso_singletonPullFunctor_map_counit_of_isEtale
    (f : X ⟶ Y) {V : AlgebraicSpaces B S hS} (gv : V ⟶ Y) (hgv : IsEtale B S hS gv.hom)
    (PP : ChosenPullback f gv) (XX : ChosenPullback f f) (QQ : ChosenPullback PP.p₂ PP.p₂)
    (j : QQ.pullback ⟶ XX.pullback) (hjp : IsPullback j QQ.p XX.p gv)
    (hs₁ : QQ.p₁ ≫ PP.p₁ = j ≫ XX.p₁) (hs₂ : QQ.p₂ ≫ PP.p₁ = j ≫ XX.p₂)
    [((spacesEtalePseudofunctor B S hS).toDescentData
      (fun _ : Unit => PP.p₂)).IsEquivalence]
    (D : (spacesEtalePseudofunctor B S hS).DescentData (fun _ : Unit => f)) :
    IsIso ((Pseudofunctor.singletonPullFunctor (spacesEtalePseudofunctor B S hS) f gv PP
        PP.isPullback.w).map
      ((Pseudofunctor.singletonDescentAdjunction (spacesEtalePseudofunctor B S hS) f XX
        (spacesEtalePseudofunctorAdjunction B S hS f)
        (spacesEtalePseudofunctorAdjunction B S hS XX.p)).counit.app D)) :=
  Pseudofunctor.isIso_singletonPullFunctor_map_counit
    (spacesEtalePseudofunctor B S hS) f gv PP XX QQ PP.isPullback.w j hjp.w hs₁ hs₂
    (spacesEtalePseudofunctorAdjunction B S hS f)
    (spacesEtalePseudofunctorAdjunction B S hS XX.p)
    (spacesEtalePseudofunctorAdjunction B S hS PP.p₂)
    (spacesEtalePseudofunctorAdjunction B S hS QQ.p)
    (fun M => isIso_mateEquiv_commSqTwoSquare B S hS PP.p₁ PP.p₂ f gv PP.isPullback hgv M)
    (fun N => isIso_mateEquiv_commSqTwoSquare B S hS j QQ.p XX.p gv hjp hgv N) D

/-! ### The étale-local criterion -/

variable {I : Type t} (f : X ⟶ Y) (Ycov : I → AlgebraicSpaces B S hS) (g : ∀ i, Ycov i ⟶ Y)
  (hg : IsEtaleCovering B S hS (fun i => (Ycov i).1) (fun i => (g i).hom))

include hg in
/-- **Stacks 041F for the chosen fibre products.** The first projections of the fibre products
of an étale covering with a morphism `t` into its target form an étale covering of the source
of `t`. -/
theorem isEtaleCovering_spacesChosenPullback_p₁ {T : AlgebraicSpaces B S hS} (t : T ⟶ Y) :
    IsEtaleCovering B S hS
      (fun i => ((spacesChosenPullback B S hS t (g i)).pullback).1)
      (fun i => ((spacesChosenPullback B S hS t (g i)).p₁).hom) :=
  isEtaleCovering_pullback B S hS t.hom T.property (fun i => (Ycov i).1)
    (fun i => (g i).hom) hg

include hg in
/-- **Stacks 0GFS for a base-changed étale covering.** Descent along the base change of an
étale covering along any morphism `t` is effective. -/
theorem isEquivalence_toDescentData_spacesChosenPullback_p₁
    {T : AlgebraicSpaces B S hS} (t : T ⟶ Y) :
    ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun i => (spacesChosenPullback B S hS t (g i)).p₁)).IsEquivalence :=
  SpacesEtale.isEquivalence_toDescentData_spacesEtalePseudofunctor_of_isEtaleCovering B S hS
    _ _ (isEtaleCovering_spacesChosenPullback_p₁ B S hS Ycov g hg t)

include hg in
/-- **The essential surjectivity half of Stacks 0GFT.** The counit of the adjunction
reconstructing a sheaf from a descent datum along `f` is an isomorphism. -/
theorem isIso_singletonDescentAdjunction_counit
    (hY : ∀ i, ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun _ : Unit => (spacesChosenPullback B S hS f (g i)).p₂)).IsEquivalence)
    (D : (spacesEtalePseudofunctor B S hS).DescentData (fun _ : Unit => f)) :
    IsIso ((Pseudofunctor.singletonDescentAdjunction (spacesEtalePseudofunctor B S hS) f
      (spacesChosenPullback B S hS f f) (spacesEtalePseudofunctorAdjunction B S hS f)
      (spacesEtalePseudofunctorAdjunction B S hS
        (spacesChosenPullback B S hS f f).p)).counit.app D) := by
  apply Pseudofunctor.descentData_isIso_of_components
  intro ⟨⟩
  refine Pseudofunctor.isIso_of_descent_components _
    (fun i => (spacesChosenPullback B S hS f (g i)).p₁)
    (isEquivalence_toDescentData_spacesChosenPullback_p₁ B S hS Ycov g hg f) _ fun i ↦ ?_
  have := hY i
  let XX := spacesChosenPullback B S hS f f
  let PP := spacesChosenPullback B S hS f (g i)
  let ZZ := spacesChosenPullback B S hS XX.p (g i)
  let QQ := ChosenPullback.baseChangedSelf f (g i) PP XX ZZ
  have hQp : QQ.p = ZZ.p₂ := ChosenPullback.baseChangedSelf_p f (g i) PP XX ZZ
  have hZ : IsPullback ZZ.p₁ QQ.p XX.p (g i) := hQp ▸ ZZ.isPullback
  have := isIso_singletonPullFunctor_map_counit_of_isEtale B S hS f (g i) (hg.etale i)
    PP XX QQ ZZ.p₁ hZ
    (ChosenPullback.baseChangedSelf_p₁_fst f (g i) PP XX ZZ)
    (ChosenPullback.baseChangedSelf_p₂_fst f (g i) PP XX ZZ) D
  exact @Functor.map_isIso _ _ _ _ _ _
    (Pseudofunctor.DescentData.component (spacesEtalePseudofunctor B S hS)
      (fun _ : Unit => PP.p₂) ()) _ this

/-- Effective descent along the base change of `f` along `t` makes the pseudofunctor a prestack
for the pullback along `t` of the sieve generated by `f`. -/
private theorem isPrestackFor_pullback_singleton_of_equivalence {T : AlgebraicSpaces B S hS}
    (t : T ⟶ Y)
    (h : ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun _ : Unit => (spacesChosenPullback B S hS f t).p₂)).IsEquivalence) :
    (spacesEtalePseudofunctor B S hS).IsPrestackFor
      ((Sieve.ofArrows (fun _ : Unit => X) (fun _ => f)).pullback t).arrows :=
  Pseudofunctor.isPrestackFor_pullback_of_equivalence _ (fun _ : Unit => f) t
    (fun _ => (spacesChosenPullback B S hS f t).pullback)
    (fun _ => (spacesChosenPullback B S hS f t).p₂)
    (fun _ => (spacesChosenPullback B S hS f t).p₁)
    (fun _ => (spacesChosenPullback B S hS f t).isPullback.flip) h

include hg in
/-- **The full faithfulness half of Stacks 0GFT.** The pseudofunctor is a prestack for the
sieve generated by `f`. -/
theorem isPrestackFor_ofArrows_singleton
    (hY : ∀ i, ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun _ : Unit => (spacesChosenPullback B S hS f (g i)).p₂)).IsEquivalence)
    (hYY : ∀ i j, ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun _ : Unit => (spacesChosenPullback B S hS f
        (spacesChosenPullback B S hS (g i) (g j)).p).p₂)).IsEquivalence) :
    (spacesEtalePseudofunctor B S hS).IsPrestackFor
      (Sieve.ofArrows (fun _ : Unit => X) (fun _ => f)).arrows :=
  Pseudofunctor.isPrestackFor_of_cover (spacesEtalePseudofunctor B S hS) g
    (fun i j => spacesChosenPullback B S hS (g i) (g j)) _
    (Pseudofunctor.isPrestackFor_of_equivalence _ g
      (SpacesEtale.isEquivalence_toDescentData_spacesEtalePseudofunctor_of_isEtaleCovering
        B S hS Ycov g hg))
    (fun t => Pseudofunctor.isPrestackFor_pullback_of_equivalence _ g t
      (fun i => (spacesChosenPullback B S hS t (g i)).pullback)
      (fun i => (spacesChosenPullback B S hS t (g i)).p₁)
      (fun i => (spacesChosenPullback B S hS t (g i)).p₂)
      (fun i => (spacesChosenPullback B S hS t (g i)).isPullback)
      (isEquivalence_toDescentData_spacesChosenPullback_p₁ B S hS Ycov g hg t))
    (fun i => isPrestackFor_pullback_singleton_of_equivalence B S hS f (g i) (hY i))
    (fun i j => isPrestackFor_pullback_singleton_of_equivalence B S hS f
      (spacesChosenPullback B S hS (g i) (g j)).p (hYY i j))

include hg in
/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `{g i : Y i ⟶ Y}` be an
étale covering. If
spaces-étale sheaves on `Y i` are equivalent, via the canonical descent datum, to descent data
for the base change `X ×_Y Y i ⟶ Y i` of `f`, and likewise over each pairwise overlap
`Y i ×_Y Y j`, then spaces-étale sheaves on `Y` are equivalent to descent data for `f`
itself. -/
@[stacks 0GFT "for the pseudofunctor of spaces-étale inverse images"]
theorem isEquivalence_toDescentData_singleton_of_isEtaleCovering
    (hY : ∀ i, ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun _ : Unit => (spacesChosenPullback B S hS f (g i)).p₂)).IsEquivalence)
    (hYY : ∀ i j, ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun _ : Unit => (spacesChosenPullback B S hS f
        (spacesChosenPullback B S hS (g i) (g j)).p).p₂)).IsEquivalence) :
    ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun _ : Unit => f)).IsEquivalence := by
  have hpre := isPrestackFor_ofArrows_singleton B S hS f Ycov g hg hY hYY
  rw [Sieve.ofArrows, Pseudofunctor.IsPrestackFor_generate_iff,
    Pseudofunctor.isPrestackFor_ofArrows_iff] at hpre
  have := hpre.some.full
  have := hpre.some.faithful
  have : ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).EssSurj :=
    ⟨fun D ↦ by
      have := isIso_singletonDescentAdjunction_counit B S hS f Ycov g hg hY D
      exact ⟨_, ⟨asIso ((Pseudofunctor.singletonDescentAdjunction
        (spacesEtalePseudofunctor B S hS) f (spacesChosenPullback B S hS f f)
        (spacesEtalePseudofunctorAdjunction B S hS f)
        (spacesEtalePseudofunctorAdjunction B S hS
          (spacesChosenPullback B S hS f f).p)).counit.app D)⟩⟩⟩
  exact { }

end AlgebraicGeometry.Space

end

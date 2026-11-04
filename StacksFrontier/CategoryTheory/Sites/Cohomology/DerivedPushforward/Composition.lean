module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksCore.Tactic.StacksAttribute

/-! # Composition of unbounded total direct images

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi. Stacks 0D6E asserts `Rg_* ∘ Rf_* = R(g ∘ f)_*` as functors
`D(O_C) ⟶ D(O_E)`.

The equality of functors is expressed here as a natural isomorphism, and the isomorphism is
not chosen: a right derived functor is a left Kan extension along the localization
`Qh : K(O_C) ⥤ D(O_C)`, so `R(g ∘ f)_*` maps uniquely to any other functor equipped with a
transformation from degreewise `(g ∘ f)_*`. `derivedPushforwardCompUnit` is the transformation
that `Rg_* ∘ Rf_*` carries — the underived composition isomorphism of
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso`, followed by the two derived
units — and `derivedPushforwardComparison` is the induced map. The content of the tag is that
this canonical comparison is invertible, which is `derivedPushforwardComparison_isIso`.

## The criterion

Over a Grothendieck abelian category a functor on the unbounded homotopy category has a right
derived functor computed by K-injective complexes
(`Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective`). The converse direction is
what makes a *given* candidate recognisable as the derived functor:
`Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective` says
that a unit which is invertible at every K-injective complex already exhibits its target as
the right derived functor. Both halves rest on the fact that every object of `D(A)` is
isomorphic to the image of a K-injective complex.

Applied to `Rg_* ∘ Rf_*`, the three factors of `derivedPushforwardCompUnit` at a K-injective
complex `I` are: the underived composition isomorphism, which is invertible for every `I`;
the unit of `Rg_*` at `f_*I`; and `Rg_*` applied to the unit of `Rf_*` at `I`, which is
invertible because `I` is K-injective. So the whole criterion reduces to the single question
of whether the unit of `Rg_*` is invertible at `f_*I`.

## What is assumed

That last question is the mathematical content of Stacks 0D6E, and it is *not* formally
automatic: Stacks 093Y shows that `f_*` carries K-injective complexes of `O_C`-modules to
K-injective complexes of `O_D`-modules only when `f` is **flat**, because the identity
`Hom_{K(O_D)}(F, f_*I) = Hom_{K(O_C)}(f^*F, I)` is only useful when `f^*` is exact. The
unconditional proof in the source runs instead through the unbounded derived pullbacks: `Rg_*`
and `Rf_*` are right adjoint to `Lg^*` and `Lf^*` (Stacks 07A6), `Lf^* ∘ Lg^* = L(g ∘ f)^*`
(Stacks 0D6D), and the conclusion follows from uniqueness of adjoints. None of `Lf^*`
(Stacks 06YY), the adjunction (Stacks 07A6) or the composition of derived pullbacks
(Stacks 0D6D) is available **for this file's `AlgebraicGeometry.RingedToposHom`**, which is why
the hypothesis is carried here. All three *are* available for a morphism of ringed topoi
presented by a morphism of sites, `AlgebraicGeometry.RingedToposSiteHom`, and there Stacks 0D6E
is unconditional:
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`,
`derivedAdjunction`, `Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso`
and `isIso_derivedPushforwardComparison_unconditional` in
`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi`.

So the theorems below take the missing input as an explicit named hypothesis, in the shape
Stacks 093Y supplies it: that degreewise `f_*` preserves K-injectivity. Everything else — the
canonical comparison, its reduction to a pointwise question about K-injective complexes, and
the K-injective criterion itself — is proved. The two definitions
`pushforwardToDerivedCategory`, `derivedPushforwardCompUnit` and the comparison
`derivedPushforwardComparison` are unconditional.

## Main definitions

* `Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective`: a
  unit invertible at every K-injective complex exhibits a right derived functor.
* `AlgebraicGeometry.RingedToposHom.pushforwardToDerivedCategory`: degreewise direct image on
  the unbounded homotopy category, followed by the localization to the derived category.
* `AlgebraicGeometry.RingedToposHom.derivedPushforwardCompUnit`: the transformation from
  degreewise `(g ∘ f)_*` to `Rg_* ∘ Rf_*`.
* `AlgebraicGeometry.RingedToposHom.derivedPushforwardComparison`: the comparison
  `R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*` induced by the universal property.

## Main results

* `AlgebraicGeometry.RingedToposHom.isRightDerivedFunctor_derivedPushforwardCompUnit`:
  `Rg_* ∘ Rf_*` is a right derived functor of degreewise `(g ∘ f)_*`.
* `AlgebraicGeometry.RingedToposHom.derivedPushforwardComparison_isIso`: the canonical
  comparison is invertible, i.e. Stacks 0D6E, under the hypothesis recorded above.

## References

* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Cohomology.UnboundedComplexes

universe w v u v₂ u₂ v₃ u₃

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/-- **The K-injective criterion for a right derived functor**, converse to
`Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective`. Over a Grothendieck abelian
category, if `α : F ⟶ L ⋙ RF` is invertible at the image of every K-injective complex, then
`RF` is a right derived functor of `F` with unit `α`.

The right derived functor exists by `hasPointwiseRightDerivedFunctor`, and its own unit is
invertible at K-injective complexes; so the comparison from it to `RF` is invertible there
too, and every object of the localization is isomorphic to the image of a K-injective
complex. -/
theorem isRightDerivedFunctor_of_isIso_app_isKInjective {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) {D : Type u₃} [Category.{v₃} D]
    (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] (RF : D ⥤ H)
    (α : F ⟶ L ⋙ RF)
    (hα : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have hpt : F.HasPointwiseRightDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := hasPointwiseRightDerivedFunctor _
  rw [Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (F.totalRightDerived L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (F.totalRightDerivedUnit L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)), NatTrans.isIso_iff_isIso_app]
  intro Z
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso L Z
  rw [NatTrans.isIso_app_iff_of_iso _ e.symm]
  have h₁ := isIso_app_of_isKInjective F L _
    (F.totalRightDerivedUnit L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) I hI
  have h₂ := hα I hI
  exact IsIso.of_isIso_fac_left (Functor.rightDerived_fac_app _ _ _ _ _ _)

end Stacks.Cohomology.UnboundedComplexes

namespace AlgebraicGeometry.RingedToposHom

universe w w' w'' v u v' u' v'' u'' dX dY dZ

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]

section Unit

variable [HasDerivedCategory.{dX} X.Modules] [HasDerivedCategory.{dY} Y.Modules]
  [HasDerivedCategory.{dZ} Z.Modules]

/-- Degreewise direct image of complexes of sheaves of modules along a morphism of ringed
topoi, read as a functor from the unbounded homotopy category of the source to the unbounded
derived category of the target. A right derived functor of this is `Rf_*`.

This is `Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy` with the derived category
of the target left as an instance argument instead of being pinned to
`CategoryTheory.HasDerivedCategory.standard`. -/
abbrev pushforwardToDerivedCategory (f : RingedToposHom X Y) :
    HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤ DerivedCategory Y.Modules :=
  (pushforwardModules f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

variable (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
  (Rf : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
  (Rg : DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules)
  (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
  (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)

/-- The transformation from degreewise `(g ∘ f)_*` to the composite `Rf_* ⋙ Rg_*` of two
right derived direct images: the underived composition isomorphism
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` on homotopy categories, then the
unit of `Rg_*` at the direct image under `f`, then `Rg_*` applied to the unit of `Rf_*`.

This is the unit with respect to which `Rf_* ⋙ Rg_*` is a right derived functor of degreewise
`(g ∘ f)_*`, and hence the one the comparison of Stacks 0D6E is induced by. -/
def derivedPushforwardCompUnit :
    pushforwardToDerivedCategory (g.comp f) ⟶ DerivedCategory.Qh ⋙ (Rf ⋙ Rg) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (pushforwardModulesCompIso f g).symm (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((pushforwardModules f).mapHomotopyCategory (ComplexShape.up ℤ)) αg ≫
    Functor.whiskerRight αf Rg

variable [UnivLE.{u, w}] [UnivLE.{v, w}] [UnivLE.{u', w'}] [UnivLE.{v', w'}]
  [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
  [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))]

/-- **The reduction of Stacks 0D6E to a statement about K-injective complexes.** If degreewise
`f_*` preserves K-injectivity — Stacks 093Y, which holds whenever `f` is flat — then
`Rf_* ⋙ Rg_*`, with the unit `derivedPushforwardCompUnit`, is a right derived functor of
degreewise `(g ∘ f)_*`.

By `Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective` it
suffices that the unit be invertible at each K-injective `I`, where it is the composite of the
underived composition isomorphism, the unit of `Rg_*` at the K-injective complex `f_*I`, and
`Rg_*` applied to the unit of `Rf_*` at `I`. -/
theorem isRightDerivedFunctor_derivedPushforwardCompUnit
    (hf : ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
      CochainComplex.IsKInjective
        (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    (Rf ⋙ Rg).IsRightDerivedFunctor (derivedPushforwardCompUnit f g Rf Rg αf αg)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ _ _ _ fun I hI ↦ ?_
  have h₂ : IsIso (αg.app (((pushforwardModules f).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
      (pushforwardToDerivedCategory g) DerivedCategory.Qh Rg αg _ (hf I hI)
  have h₃ : IsIso (αf.app ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
      (pushforwardToDerivedCategory f) DerivedCategory.Qh Rf αf I hI
  simp only [derivedPushforwardCompUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

end Unit

section Comparison

variable [HasDerivedCategory.{dX} X.Modules] [HasDerivedCategory.{dY} Y.Modules]
  [HasDerivedCategory.{dZ} Z.Modules]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
  (Rf : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
  (Rg : DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules)
  (Rh : DerivedCategory X.Modules ⥤ DerivedCategory Z.Modules)
  (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
  (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
  (αh : pushforwardToDerivedCategory (g.comp f) ⟶ DerivedCategory.Qh ⋙ Rh)
  [Rh.IsRightDerivedFunctor αh (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]

/-- The canonical comparison `R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*`, induced by the universal property of
the right derived functor `Rh = R(g ∘ f)_*`: it is the unique map whose composite with the
unit `αh` is `derivedPushforwardCompUnit`. -/
def derivedPushforwardComparison : Rh ⟶ Rf ⋙ Rg :=
  Rh.rightDerivedDesc αh (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) _
    (derivedPushforwardCompUnit f g Rf Rg αf αg)

/-- **Stacks 0D6E.** The canonical comparison `R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*` is a natural
isomorphism, so that `Rg_* ∘ Rf_* = R(g ∘ f)_*` as functors `D(O_C) ⟶ D(O_E)`.

Both sides are right derived functors of degreewise `(g ∘ f)_*` — the second by
`isRightDerivedFunctor_derivedPushforwardCompUnit` — and the comparison between two right
derived functors of one functor is invertible.

The hypothesis `hf`, that degreewise `f_*` preserves K-injectivity, stands in for the
unbounded derived pullback: the source proves the statement unconditionally from the
adjunctions `Lf^* ⊣ Rf_*`, `Lg^* ⊣ Rg_*` and `Lf^* ∘ Lg^* = L(g ∘ f)^*`, which are not
available for `AlgebraicGeometry.RingedToposHom`. For a morphism of ringed topoi presented by
a morphism of sites they are, and the statement is then unconditional:
`isIso_derivedPushforwardComparison_unconditional` in
`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi`.
Stacks 093Y supplies `hf` for a flat morphism. -/
theorem derivedPushforwardComparison_isIso
    [UnivLE.{u, w}] [UnivLE.{v, w}] [UnivLE.{u', w'}] [UnivLE.{v', w'}]
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))]
    (hf : ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
      CochainComplex.IsKInjective
        (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    IsIso (derivedPushforwardComparison f g Rf Rg Rh αf αg αh) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc Rh αh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) (Rf ⋙ Rg)
    (derivedPushforwardCompUnit f g Rf Rg αf αg)).mp
    (isRightDerivedFunctor_derivedPushforwardCompUnit f g Rf Rg αf αg hf)

end Comparison

end AlgebraicGeometry.RingedToposHom

end

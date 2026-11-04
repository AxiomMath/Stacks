module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeStalkEquality
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkPushforwardUnitSquare
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCompositionAssembly

/-!
# The derived stalk of an adjoint transpose along a closed immersion

For a closed immersion `i : Z ⟶ X` and a point `z` of `Z`, this file computes the derived stalk at
`i z` of the adjoint transpose `M ⟶ Ri_* Y` of a morphism `Li^* M ⟶ Y`, and records the coherence
of the derived stalk formula with the composition of derived pullbacks of Tag 0D5S.

## Main results

* `AlgebraicGeometry.derivedStalk_homEquiv_comp_derivedStalkPushforward`: for `v : Li^* M ⟶ Y`,
  the derived stalk at `i z` of the transpose `M ⟶ Ri_* Y`, followed by
  `AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`, is the unit of
  `AlgebraicGeometry.derivedStalkGermAdjunction` followed by derived restriction of scalars of
  `AlgebraicGeometry.derivedPullbackStalkIso` read backwards and the derived stalk of `v`.
* `AlgebraicGeometry.derivedStalk_transpose_comp_derivedStalkPushforward` and
  `AlgebraicGeometry.derivedStalk_transposeSplit_comp_derivedStalkPushforward`: the same with one
  further morphism of `D(𝒪_Z)` appended, for a transpose given by an equation, and for one whose
  adjoint is a three-fold composite.
* `AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_derivedStalk_compIso` and
  `AlgebraicGeometry.derivedStalk_compIso_inv_comp_derivedPullbackStalkIso`: the coherence of the
  comparison of Tag 0D5S with the derived stalk formula, with the outer isomorphisms cancelled.
* `AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_eqToHom_comp`: for `φ₁ = φ₂ : X ⟶ Y`, the
  stalk formula for `φ₁` read backwards, the derived stalk of a transport of the derived pullback
  at an object, and the stalk formula for `φ₂` compose to the transport of the target.

## Implementation notes

The equations mix `AlgebraicGeometry.Scheme.Modules` with
`CategoryTheory.SheafOfModules (structureSheafRing _)`, and the spellings `i z` and
`i.toLRSHom.toShHom.hom.base z` of the image point, which are definitionally but not reducibly
equal. `transposeFold`, `cancelBoth`, `shiftHead` and `retailComp` state the cancellations for
free objects and morphisms of arbitrary categories and are applied by `exact`, so that the
conversion is paid once; `retailComp` is proved by `congrArg` because a rewrite would build a
motive over the whole factorization.

The kernel cannot afford some of the conversions the natural statements would demand:

* the transpose enters `derivedStalk_transpose_comp_derivedStalkPushforward` as a variable `t`
  with an equation `ht`, since substituting the derived base change map makes the kernel time
  out;
* `derivedStalk_transposeSplit_comp_derivedStalkPushforward` keeps the three factors of the
  adjoint separate, since converting `Functor.map` of a composite produced by unification into
  `Functor.map` of a written copy is over the kernel's budget;
* `derivedPullbackStalkIso_inv_comp_eqToHom_comp` transports along an equation of objects rather
  than of derived pullback functors, since identifying the functors makes the kernel unfold
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

universe u

namespace StacksDraft.DerivedStalkCounitChase

variable {C D : Type*} [Category C] [Category D]

/-- If `st = sη ≫ srv`, `srv ≫ Φy = Φm ≫ R.map sv` and `sη ≫ Φm = gu ≫ R.map ψinv`, then
`st ≫ Φy = gu ≫ R.map (ψinv ≫ sv)`. -/
theorem transposeFold (R : C ⥤ D) {o₀ o₁ o₂ : D} {n₁ n₂ n₃ : C}
    (st : o₀ ⟶ o₁) (Φy : o₁ ⟶ R.obj n₂) (sη : o₀ ⟶ o₂) (srv : o₂ ⟶ o₁)
    (Φm : o₂ ⟶ R.obj n₁) (sv : n₁ ⟶ n₂) (gu : o₀ ⟶ R.obj n₃) (ψinv : n₃ ⟶ n₁)
    (h1 : st = sη ≫ srv)
    (h2 : srv ≫ Φy = Φm ≫ R.map sv)
    (h3 : sη ≫ Φm = gu ≫ R.map ψinv) :
    st ≫ Φy = gu ≫ R.map (ψinv ≫ sv) := by
  rw [h1, Category.assoc, h2, ← Category.assoc, h3, Category.assoc, ← R.map_comp]

/-- If `A ≫ B = Cm ≫ Dm` with `A' ≫ A` and `Dm ≫ D'` identities, then `A' ≫ Cm = B ≫ D'`. -/
theorem cancelBoth {a b c d : D} {A : a ⟶ b} {B : b ⟶ d} {Cm : a ⟶ c} {Dm : c ⟶ d}
    {A' : b ⟶ a} {D' : d ⟶ c} (hA : A' ≫ A = CategoryStruct.id b)
    (hD : Dm ≫ D' = CategoryStruct.id c) (h : A ≫ B = Cm ≫ Dm) :
    A' ≫ Cm = B ≫ D' := by
  have e1 : A' ≫ Cm ≫ Dm ≫ D' = B ≫ D' := by
    rw [← Category.assoc Cm Dm D', ← h, Category.assoc, ← Category.assoc A', hA,
      Category.id_comp]
  rwa [hD, Category.comp_id] at e1

/-- A middle morphism which is the identity. -/
theorem idMiddle {a b c : D} (p : a ⟶ b) (m : b ⟶ b) (q : b ⟶ c) (r : a ⟶ c)
    (hm : m = CategoryStruct.id b) (hq : p ≫ q = r) : p ≫ m ≫ q = r := by
  rw [hm, Category.id_comp, hq]

/-- Two composable morphisms replaced by a third, in front of a tail. -/
theorem shiftHead {o₀ o₁ o₂ o₃ : D} (sp : o₀ ⟶ o₁) (sq : o₁ ⟶ o₂) (sr : o₀ ⟶ o₂)
    (tail : o₂ ⟶ o₃) (x : o₀ ⟶ o₃) (h : sp ≫ sq = sr) (hx : sr ≫ tail = x) :
    sp ≫ sq ≫ tail = x := by
  rw [← Category.assoc, h, hx]

/-- A functor carried over a four-fold composite whose first three factors are bracketed. -/
theorem map_comp₄ (F : C ⥤ D) {x₀ x₁ x₂ x₃ x₄ : C} (a : x₀ ⟶ x₁) (b : x₁ ⟶ x₂) (c : x₂ ⟶ x₃)
    (e : x₃ ⟶ x₄) : F.map ((a ≫ b ≫ c) ≫ e) =
      F.map a ≫ F.map b ≫ F.map c ≫ F.map e := by
  simp

/-- If `L = gu ≫ R.map (ι ≫ m)` and `m = m'`, then `L = gu ≫ R.map (ι ≫ m')`. -/
theorem retailComp (R : C ⥤ D) {a : D} {n p q : C} (L : a ⟶ R.obj q) (gu : a ⟶ R.obj n)
    (ι : n ⟶ p) {m m' : p ⟶ q} (h : L = gu ≫ R.map (ι ≫ m)) (hm : m = m') :
    L = gu ≫ R.map (ι ≫ m') :=
  h.trans (congrArg (fun s => gu ≫ R.map (ι ≫ s)) hm)

end StacksDraft.DerivedStalkCounitChase

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

section Composition

variable {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W) (x : X)

/-- The stalk formula for `f` at the derived pullback along `g`, followed by the merged stalk
formulas, is the derived stalk of the Tag 0D5S comparison followed by that for `f ≫ g`. -/
private theorem derivedPullbackStalkIso_hom_app_comp_eq (N : DerivedCategory W.Modules) :
    (derivedPullbackStalkIso f x).hom.app
          ((derivedPullback g.toLRSHom.toShHom).obj N) ≫
        ((totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor.map
            ((derivedPullbackStalkIso g (f x)).hom.app N) ≫
          (derivedStalkExtensionCompIso f g x).hom.app
            ((derivedStalkFunctor (g (f x))).obj N)) =
      (derivedStalkFunctor x).map
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
            f.toLRSHom.toShHom g.toLRSHom.toShHom).hom.app N) ≫
        (derivedPullbackStalkIso (f ≫ g) x).hom.app N :=
  (derivedPullbackStalkCompIso_hom_app f g x N).symm.trans
    (congr_app (derivedPullbackStalkCompIso_hom_eq f g x) N)

/-- The stalk formula for `f` read backwards at the derived pullback along `g`, followed by the
derived stalk of the Tag 0D5S comparison, is derived extension of scalars along the germ map of
`f` of the stalk formula for `g`, followed by the merge of the two extensions of scalars and the
stalk formula for `f ≫ g` read backwards. -/
theorem derivedPullbackStalkIso_inv_comp_derivedStalk_compIso (N : DerivedCategory W.Modules) :
    (derivedPullbackStalkIso f x).inv.app ((derivedPullback g.toLRSHom.toShHom).obj N) ≫
        (derivedStalkFunctor x).map
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
            f.toLRSHom.toShHom g.toLRSHom.toShHom).hom.app N) =
      ((totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor.map
            ((derivedPullbackStalkIso g (f x)).hom.app N) ≫
          (derivedStalkExtensionCompIso f g x).hom.app
            ((derivedStalkFunctor (g (f x))).obj N)) ≫
        (derivedPullbackStalkIso (f ≫ g) x).inv.app N := by
  have h := derivedPullbackStalkIso_hom_app_comp_eq f g x N
  exact StacksDraft.DerivedStalkCounitChase.cancelBoth
    ((derivedPullbackStalkIso f x).inv_hom_id_app
      ((derivedPullback g.toLRSHom.toShHom).obj N))
    ((derivedPullbackStalkIso (f ≫ g) x).hom_inv_id_app N) h

/-- The derived stalk of the Tag 0D5S comparison read backwards, followed by the stalk formula
for `f` and derived extension of scalars along the germ map of `f` of the stalk formula for `g`,
is the stalk formula for `f ≫ g` followed by the merge of the two extensions of scalars read
backwards. -/
theorem derivedStalk_compIso_inv_comp_derivedPullbackStalkIso (N : DerivedCategory W.Modules) :
    (derivedStalkFunctor x).map
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
            f.toLRSHom.toShHom g.toLRSHom.toShHom).inv.app N) ≫
        (derivedPullbackStalkIso f x).hom.app
            ((derivedPullback g.toLRSHom.toShHom).obj N) ≫
          (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor.map
            ((derivedPullbackStalkIso g (f x)).hom.app N) =
      (derivedPullbackStalkIso (f ≫ g) x).hom.app N ≫
        (derivedStalkExtensionCompIso f g x).inv.app
          ((derivedStalkFunctor (g (f x))).obj N) := by
  have h := derivedPullbackStalkIso_hom_app_comp_eq f g x N
  have hA := StacksDraft.DerivedStalkComponentChase.map_inv_hom (derivedStalkFunctor x)
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      f.toLRSHom.toShHom g.toLRSHom.toShHom).inv.app N)
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      f.toLRSHom.toShHom g.toLRSHom.toShHom).hom.app N)
    (Iso.inv_hom_id_app _ _)
  exact StacksDraft.DerivedStalkCounitChase.cancelBoth hA
    ((derivedStalkExtensionCompIso f g x).hom_inv_id_app
      ((derivedStalkFunctor (g (f x))).obj N))
    (h.symm.trans (Category.assoc _ _ _).symm)

section Transport

variable {X Y : Scheme.{u}}

/-- For two equal morphisms `φ₁ = φ₂ : X ⟶ Y` the stalk formula for `φ₁` read backwards, the
derived stalk of a transport of the derived pullback *at the object* `N`, and the stalk formula for
`φ₂`, compose to the transport of the target. -/
theorem derivedPullbackStalkIso_inv_comp_eqToHom_comp {φ₁ φ₂ : X ⟶ Y} (h : φ₁ = φ₂) (x : X)
    (N : DerivedCategory Y.Modules)
    (e : (derivedPullback φ₁.toLRSHom.toShHom).obj N =
      (derivedPullback φ₂.toLRSHom.toShHom).obj N) :
    (derivedPullbackStalkIso φ₁ x).inv.app N ≫
        (derivedStalkFunctor x).map (eqToHom e) ≫
        (derivedPullbackStalkIso φ₂ x).hom.app N =
      eqToHom (congrArg (fun ψ : X ⟶ Y =>
        (totalDerivedExtensionScalars.{u, u, u} (ψ.stalkMap x).hom).functor.obj
          ((derivedStalkFunctor (ψ x)).obj N)) h) := by
  subst h
  exact StacksDraft.DerivedStalkCounitChase.idMiddle _ _ _ _
    ((CategoryTheory.eqToHom_refl _ e) ▸ CategoryTheory.Functor.map_id
      (derivedStalkFunctor x) ((derivedPullback φ₁.toLRSHom.toShHom).obj N))
    (Iso.inv_hom_id_app _ _)

end Transport

end Composition

section Transpose

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (z : Z)

/-- For a morphism `v : Li^* M ⟶ Y` of `D(𝒪_Z)`, the derived stalk at `i z` of its transpose
`M ⟶ Ri_* Y`, followed by the derived stalk of `Ri_*` on the image, is the unit of
`derivedStalkGermAdjunction` followed by derived restriction of scalars of
`AlgebraicGeometry.derivedPullbackStalkIso` read backwards and the derived stalk of `v`. -/
theorem derivedStalk_homEquiv_comp_derivedStalkPushforward
    {M : DerivedCategory X.Modules} {Y : DerivedCategory Z.Modules}
    (v : (derivedPullback i.toLRSHom.toShHom).obj M ⟶ Y) :
    (AlgebraicGeometry.derivedStalkFunctor (i z)).map
          ((derivedAdjunction i.toLRSHom.toShHom).homEquiv M Y v) ≫
        (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app Y =
      (AlgebraicGeometry.derivedStalkGermAdjunction i z).unit.app
          ((AlgebraicGeometry.derivedStalkFunctor (i z)).obj M) ≫
        (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom).mapDerivedCategory.map
          ((AlgebraicGeometry.derivedPullbackStalkIso i z).inv.app M ≫
            (AlgebraicGeometry.derivedStalkFunctor z).map v) :=
  StacksDraft.DerivedStalkCounitChase.transposeFold
    (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom).mapDerivedCategory
    ((AlgebraicGeometry.derivedStalkFunctor (i z)).map
      ((derivedAdjunction i.toLRSHom.toShHom).homEquiv M Y v))
    ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app Y)
    ((AlgebraicGeometry.derivedStalkFunctor (i z)).map
      ((derivedAdjunction i.toLRSHom.toShHom).unit.app M))
    ((derivedPushforward i.toLRSHom.toShHom ⋙
      AlgebraicGeometry.derivedStalkFunctor (i z)).map v)
    ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app
      ((derivedPullback i.toLRSHom.toShHom).obj M))
    ((AlgebraicGeometry.derivedStalkFunctor z).map v)
    ((AlgebraicGeometry.derivedStalkGermAdjunction i z).unit.app
      ((AlgebraicGeometry.derivedStalkFunctor (i z)).obj M))
    ((AlgebraicGeometry.derivedPullbackStalkIso i z).inv.app M)
    ((congrArg (fun t => (AlgebraicGeometry.derivedStalkFunctor (i z)).map t)
        ((derivedAdjunction i.toLRSHom.toShHom).homEquiv_unit (f := v))).trans
      ((AlgebraicGeometry.derivedStalkFunctor (i z)).map_comp _ _))
    (show (derivedPushforward i.toLRSHom.toShHom ⋙
          AlgebraicGeometry.derivedStalkFunctor (i z)).map v ≫
        (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app Y =
      (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app
          ((derivedPullback i.toLRSHom.toShHom).obj M) ≫
        (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom).mapDerivedCategory.map
          ((AlgebraicGeometry.derivedStalkFunctor z).map v) from
      ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing
        i z).hom.naturality v))
    (AlgebraicGeometry.derivedStalkPushforwardUnitSquareAt_all i z M).symm

/-- For a transpose `t : M ⟶ Ri_* Y₀` of `v : Li^* M ⟶ Y₀` and a morphism `u : Y₀ ⟶ Y` of
`D(𝒪_Z)`, the derived stalk at `i z` of `t`, followed by that of `Ri_* u` and by
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`, is the unit of
`AlgebraicGeometry.derivedStalkGermAdjunction` followed by derived restriction of scalars of
`AlgebraicGeometry.derivedPullbackStalkIso` read backwards and the derived stalk of `v ≫ u`. -/
theorem derivedStalk_transpose_comp_derivedStalkPushforward
    {M : DerivedCategory X.Modules} {Y₀ Y : DerivedCategory Z.Modules}
    (t : M ⟶ (derivedPushforward i.toLRSHom.toShHom).obj Y₀)
    (v : (derivedPullback i.toLRSHom.toShHom).obj M ⟶ Y₀)
    (ht : t = (derivedAdjunction i.toLRSHom.toShHom).homEquiv M Y₀ v) (u : Y₀ ⟶ Y) :
    (AlgebraicGeometry.derivedStalkFunctor (i z)).map t ≫
        (derivedPushforward i.toLRSHom.toShHom ⋙
          AlgebraicGeometry.derivedStalkFunctor (i z)).map u ≫
        (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app Y =
      (AlgebraicGeometry.derivedStalkGermAdjunction i z).unit.app
          ((AlgebraicGeometry.derivedStalkFunctor (i z)).obj M) ≫
        (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom).mapDerivedCategory.map
          ((AlgebraicGeometry.derivedPullbackStalkIso i z).inv.app M ≫
            (AlgebraicGeometry.derivedStalkFunctor z).map (v ≫ u)) :=
  StacksDraft.DerivedStalkCounitChase.shiftHead _ _
    ((AlgebraicGeometry.derivedStalkFunctor (i z)).map
      ((derivedAdjunction i.toLRSHom.toShHom).homEquiv M Y (v ≫ u))) _ _
    (show (AlgebraicGeometry.derivedStalkFunctor (i z)).map t ≫
          (derivedPushforward i.toLRSHom.toShHom ⋙
            AlgebraicGeometry.derivedStalkFunctor (i z)).map u =
        (AlgebraicGeometry.derivedStalkFunctor (i z)).map
          ((derivedAdjunction i.toLRSHom.toShHom).homEquiv M Y (v ≫ u)) from
      (((AlgebraicGeometry.derivedStalkFunctor (i z)).map_comp t
        ((derivedPushforward i.toLRSHom.toShHom).map u)).symm.trans
        (congrArg (fun s => (AlgebraicGeometry.derivedStalkFunctor (i z)).map s)
          (((congrArg (fun s => s ≫ (derivedPushforward i.toLRSHom.toShHom).map u) ht).trans
            ((derivedAdjunction i.toLRSHom.toShHom).homEquiv_naturality_right v u).symm)))))
    (derivedStalk_homEquiv_comp_derivedStalkPushforward i z (v ≫ u))

/-- `derivedStalk_transpose_comp_derivedStalkPushforward` for a transpose whose adjoint is a
three-fold composite `v₁ ≫ v₂ ≫ v₃`, with the derived stalk of each factor appearing separately.
-/
theorem derivedStalk_transposeSplit_comp_derivedStalkPushforward
    {M : DerivedCategory X.Modules} {Y₀ Y A₁ A₂ : DerivedCategory Z.Modules}
    (t : M ⟶ (derivedPushforward i.toLRSHom.toShHom).obj Y₀)
    (v₁ : (derivedPullback i.toLRSHom.toShHom).obj M ⟶ A₁) (v₂ : A₁ ⟶ A₂) (v₃ : A₂ ⟶ Y₀)
    (ht : t = (derivedAdjunction i.toLRSHom.toShHom).homEquiv M Y₀ (v₁ ≫ v₂ ≫ v₃))
    (u : Y₀ ⟶ Y) :
    (AlgebraicGeometry.derivedStalkFunctor (i z)).map t ≫
        (derivedPushforward i.toLRSHom.toShHom ⋙
          AlgebraicGeometry.derivedStalkFunctor (i z)).map u ≫
        (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app Y =
      (AlgebraicGeometry.derivedStalkGermAdjunction i z).unit.app
          ((AlgebraicGeometry.derivedStalkFunctor (i z)).obj M) ≫
        (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom).mapDerivedCategory.map
          ((AlgebraicGeometry.derivedPullbackStalkIso i z).inv.app M ≫
            (AlgebraicGeometry.derivedStalkFunctor z).map v₁ ≫
              (AlgebraicGeometry.derivedStalkFunctor z).map v₂ ≫
                (AlgebraicGeometry.derivedStalkFunctor z).map v₃ ≫
                  (AlgebraicGeometry.derivedStalkFunctor z).map u) :=
  StacksDraft.DerivedStalkCounitChase.retailComp _ _ _ _
    (derivedStalk_transpose_comp_derivedStalkPushforward i z t (v₁ ≫ v₂ ≫ v₃) ht u)
    (StacksDraft.DerivedStalkCounitChase.map_comp₄
      (AlgebraicGeometry.derivedStalkFunctor z) v₁ v₂ v₃ u)

end Transpose

end AlgebraicGeometry


end

end

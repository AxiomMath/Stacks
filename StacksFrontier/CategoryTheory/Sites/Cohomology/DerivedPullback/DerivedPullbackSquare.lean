module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The two derived pullbacks around a 2-commutative square of ringed topoi

Let
```
              g'
  (Sh(𝒞'), 𝒪_{𝒞'}) ⟶ (Sh(𝒞), 𝒪_𝒞)
        | f'                | f
        v                   v
  (Sh(𝒟'), 𝒪_{𝒟'}) ⟶ (Sh(𝒟), 𝒪_𝒟)
              g
```
be a square of morphisms of ringed topoi commuting up to a 2-isomorphism `s : g ∘ f' ≅ f ∘ g'`.
Both composites `L(f')^* ∘ Lg^*` and `L(g')^* ∘ Lf^*` are left derived functors of the
degreewise pullback along the composite, since K-flat complexes with flat terms compute every
derived pullback and are carried to such complexes by every pullback ([Stacks, Tag 06YY],
[Stacks, Tag 0G7E]). The isomorphism `m : (f')^* g^* ≅ (g')^* f^*` of the underived pullbacks
around the square therefore induces an isomorphism

`Σ : L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*`,

characterized by its compatibility with the comparisons from derived to underived pullbacks.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.squarePullbackHomotopyIso`: `m` on homotopy
  categories.
* `AlgebraicGeometry.RingedToposHom.TwoIso.derivedPullbackSquareIso`: the isomorphism `Σ`.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoIso.derivedPullbackSquareIso_hom_app_comp`: `Σ` followed
  by the comparisons to the underived pullbacks along `f` and `g'` is the comparisons along `g`
  and `f'` followed by `m`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Sheaves.DerivedPullback (pullbackComplexFunctor)

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)]
  [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)]
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X} (s : TwoIso (g.comp f') (f.comp g'))

/-- The isomorphism `m : (f')^* g^* ≅ (g')^* f^*` of the pullbacks around the square, on the
unbounded homotopy categories. -/
def squarePullbackHomotopyIso :
    Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f' ≅
      Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g' :=
  Quotient.natIsoLift _ (NatIso.ofComponents
    (fun K => (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      (squarePullbackComplexIso s K))
    (fun {K L} φ => by
      have h := squarePullbackComplexIso_hom_naturality s φ
      change (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((pullbackComplexFunctor f'.toModulesHom).map
            ((pullbackComplexFunctor g.toModulesHom).map φ)) ≫
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (squarePullbackComplexIso s L).hom =
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (squarePullbackComplexIso s K).hom ≫
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            ((pullbackComplexFunctor g'.toModulesHom).map
              ((pullbackComplexFunctor f.toModulesHom).map φ))
      rw [← Functor.map_comp, ← Functor.map_comp, h]))

omit [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)] [HasSheafify Y'.J (Type u)]
  [HasSheafify Y.J (Type u)] in
/-- On the image of a complex `K`, the isomorphism `squarePullbackHomotopyIso s` is the image
of `squarePullbackComplexIso s K` in the homotopy category. -/
theorem squarePullbackHomotopyIso_hom_app
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (squarePullbackHomotopyIso s).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (squarePullbackComplexIso s K).hom :=
  rfl

/-- The comparison of `L(f')^* ∘ Lg^*` with the degreewise pullbacks along `g` and `f'`. -/
def squareCounitLeft :
    DerivedCategory.Qh ⋙ (derivedPullback g ⋙ derivedPullback f') ⟶
      Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f' ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (derivedPullbackComparison g) (derivedPullback f') ≫
    Functor.whiskerLeft (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g)
      (derivedPullbackComparison f')

/-- The comparison of `L(g')^* ∘ Lf^*` with the degreewise pullbacks along `f` and `g'`. -/
def squareCounitRight :
    DerivedCategory.Qh ⋙ (derivedPullback f ⋙ derivedPullback g') ⟶
      Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g' ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (derivedPullbackComparison f) (derivedPullback g') ≫
    Functor.whiskerLeft (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f)
      (derivedPullbackComparison g')

/-- The component of `squareCounitRight` at `K` is `L(g')^*` applied to the comparison for `f`
at `K`, followed by the comparison for `g'` at the degreewise pullback of `K` along `f`. -/
theorem squareCounitRight_app
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    (squareCounitRight (f := f) (g' := g')).app K =
      (derivedPullback g').map ((derivedPullbackComparison f).app K) ≫
        (derivedPullbackComparison g').app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f).obj K) :=
  rfl

/-- The component of `squareCounitLeft` at `K` is `L(f')^*` applied to the comparison for `g`
at `K`, followed by the comparison for `f'` at the degreewise pullback of `K` along `g`. -/
theorem squareCounitLeft_app
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    (squareCounitLeft (g := g) (f' := f')).app K =
      (derivedPullback f').map ((derivedPullbackComparison g).app K) ≫
        (derivedPullbackComparison f').app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g).obj K) :=
  rfl

omit [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)] [HasSheafify Y'.J (Type u)]
  [HasSheafify Y.J (Type u)] in
/-- The degreewise pullback along `f` followed by the one along `g'` carries a quasi-isomorphism
between K-flat complexes with flat terms to an isomorphism of `D(𝒪_{𝒞'})`. -/
theorem squarePullback_invertsQuasiIso
    {K M : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)} (t : K ⟶ M) (ht : quasiIsoTarget (Y := Y) t)
    (hK : IsKFlat (Y := Y) K) (hM : IsKFlat (Y := Y) M) :
    IsIso ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f ⋙
      Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g' ⋙ DerivedCategory.Qh).map t) := by
  have h : quasiIsoTarget (Y := X)
      ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f).map t) :=
    (DerivedCategory.isIso_Qh_map_iff _).1 (pullbackInvertsQuasiIso_isKFlat f t ht hK hM)
  exact pullbackInvertsQuasiIso_isKFlat g' _ h
    (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy f K hK)
    (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy f M hM)

/-- `L(g')^* ∘ Lf^*` is a left derived functor of the degreewise pullback along `f` followed by
the one along `g'`. -/
theorem isLeftDerivedFunctor_squareCounitRight :
    (derivedPullback f ⋙ derivedPullback g').IsLeftDerivedFunctor
      (squareCounitRight (f := f) (g' := g')) (quasiIsoTarget (Y := Y)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (quasiIsoTarget (Y := Y)) (IsKFlat (Y := Y))
    (Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.hasResolutions_isKFlat' (Y := Y))
    (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f ⋙
      Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g' ⋙ DerivedCategory.Qh)
    (fun t ht hK hM => squarePullback_invertsQuasiIso t ht hK hM)
    DerivedCategory.Qh (derivedPullback f ⋙ derivedPullback g') squareCounitRight
    (fun K hK => by
      rw [squareCounitRight_app]
      open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
      have h₁ := isIso_derivedPullbackComparison_app_isKFlat f K hK
      open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
      have h₂ := isIso_derivedPullbackComparison_app_isKFlat g' _
        (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy f K hK)
      infer_instance)

/-- The comparison of `L(f')^* ∘ Lg^*` with the degreewise pullbacks, followed by `m`: a map to
the degreewise pullback along `f` followed by the one along `g'`. -/
def squareCounitLeftTransported :
    DerivedCategory.Qh ⋙ (derivedPullback g ⋙ derivedPullback f') ⟶
      Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g' ⋙ DerivedCategory.Qh :=
  squareCounitLeft ≫ Functor.whiskerRight (squarePullbackHomotopyIso s).hom DerivedCategory.Qh

omit [HasSheafify X.J (Type u)] in
/-- `L(f')^* ∘ Lg^*` is also a left derived functor of the degreewise pullback along `f`
followed by the one along `g'`, through `m`. -/
theorem isLeftDerivedFunctor_squareCounitLeftTransported :
    (derivedPullback g ⋙ derivedPullback f').IsLeftDerivedFunctor
      (squareCounitLeftTransported s) (quasiIsoTarget (Y := Y)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (quasiIsoTarget (Y := Y)) (IsKFlat (Y := Y))
    (Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.hasResolutions_isKFlat' (Y := Y))
    (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f ⋙
      Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g' ⋙ DerivedCategory.Qh)
    (fun t ht hK hM => squarePullback_invertsQuasiIso t ht hK hM)
    DerivedCategory.Qh (derivedPullback g ⋙ derivedPullback f') (squareCounitLeftTransported s)
    (fun K hK => by
      open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
      have h₁ := isIso_derivedPullbackComparison_app_isKFlat g K hK
      open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
      have h₂ := isIso_derivedPullbackComparison_app_isKFlat f' _
        (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy g K hK)
      change IsIso ((squareCounitLeft (g := g) (f' := f')).app K ≫
        DerivedCategory.Qh.map ((squarePullbackHomotopyIso s).hom.app K))
      rw [squareCounitLeft_app]
      infer_instance)

/-- **The two derived pullbacks around a 2-commutative square of ringed topoi agree**:
`Σ : L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*`, the isomorphism of left derived functors of the degreewise
pullback along the composite induced by the isomorphism `m` of the underived pullbacks. -/
def derivedPullbackSquareIso :
    derivedPullback g ⋙ derivedPullback f' ≅ derivedPullback f ⋙ derivedPullback g' :=
  have := isLeftDerivedFunctor_squareCounitRight (f := f) (g' := g')
  have := isLeftDerivedFunctor_squareCounitLeftTransported s
  have : IsIso ((derivedPullback f ⋙ derivedPullback g').leftDerivedLift squareCounitRight
      (quasiIsoTarget (Y := Y)) (derivedPullback g ⋙ derivedPullback f')
      (squareCounitLeftTransported s)) :=
    ((derivedPullback f ⋙ derivedPullback g').isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      squareCounitRight (quasiIsoTarget (Y := Y)) _ _).1 inferInstance
  asIso ((derivedPullback f ⋙ derivedPullback g').leftDerivedLift squareCounitRight
      (quasiIsoTarget (Y := Y)) (derivedPullback g ⋙ derivedPullback f')
      (squareCounitLeftTransported s))

/-- **`Σ` is compatible with the comparisons to the underived pullbacks**: at an object of the
homotopy category, `Σ` followed by the comparisons along `f` and `g'` is the comparisons along
`g` and `f'` followed by `m`. -/
theorem derivedPullbackSquareIso_hom_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    (derivedPullbackSquareIso s).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullback g').map ((derivedPullbackComparison f).app K) ≫
        (derivedPullbackComparison g').app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f).obj K) =
      (derivedPullback f').map ((derivedPullbackComparison g).app K) ≫
        (derivedPullbackComparison f').app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy g).obj K) ≫
        DerivedCategory.Qh.map ((squarePullbackHomotopyIso s).hom.app K) := by
  have := isLeftDerivedFunctor_squareCounitRight (f := f) (g' := g')
  have h := (derivedPullback f ⋙ derivedPullback g').leftDerived_fac_app squareCounitRight
    (quasiIsoTarget (Y := Y)) (derivedPullback g ⋙ derivedPullback f')
    (squareCounitLeftTransported s) K
  rw [squareCounitRight_app] at h
  simpa [squareCounitLeftTransported, squareCounitLeft_app, derivedPullbackSquareIso] using h

end AlgebraicGeometry.RingedToposHom.TwoIso

end

module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.Factorization
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.PullbackFunctorIso
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.EffectiveCriterion

/-!
# Pullback of canonical descent data along a commutative square

Let `f ≫ a = a' ≫ h` be a commutative square with vertical arrows `a : X ⟶ S` and
`a' : X' ⟶ S'`. For a scheme `U` over `S` the canonical descent datum `X ×_S U` relative to
`X / S` pulls back along the square to the canonical descent datum `X' ×_{S'} (S' ×_S U)`
relative to `X' / S'`, because `X' ×_X (X ×_S U) = X' ×_S U = X' ×_{S'} (S' ×_S U)`. Hence a
pullback functor on descent data carries effective descent data to effective descent data, and
the scheme realising the pullback is the restriction of the realising scheme to the new base.

## Main definitions

* `AlgebraicGeometry.DescentData.trivialPullbackFunctorIso` identifies the pullback of a
  trivial descent datum along the square expressing `h` as a base change of `𝟙 S` with the
  trivial descent datum of `S' ×_S U`.
* `AlgebraicGeometry.DescentData.canonicalPullbackFunctorIso` is the resulting natural
  isomorphism `canonicalFunctor a ⋙ P.functor ≅ Over.pullback h ⋙ canonicalFunctor a'`, with
  `AlgebraicGeometry.DescentData.canonicalDatumPullbackIso` its component at a scheme over `S`.

## Main results

* `AlgebraicGeometry.DescentData.isEffective_pullback`: effectivity of a descent datum
  relative to `X / S` is inherited by its pullback relative to `X' / S'`.
-/


@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

section Trivial

variable {S S' : Scheme.{u}} (h : S' ⟶ S)

/-- The pullback of a descent datum relative to `𝟙 S` along the square expressing `h` as a
base change of `𝟙 S` is the trivial descent datum of `S' ×_S U`. -/
def trivialPullbackDatumIso (P : PullbackFunctor (𝟙 S) (𝟙 S') h h (by simp))
    (T : DescentData (fun _ : Unit ↦ 𝟙 S)) :
    P.functor.obj T ≅ (trivialFunctor S').obj ((Over.pullback h).obj (T.obj ())) := by
  refine isoOfActOn (P.objIso T) ?_
  rw [actOn_id (P.functor.obj T),
    actOn_id ((trivialFunctor S').obj ((Over.pullback h).obj (T.obj ()))), actOnMap_fst]

/-- Pullback along the square expressing `h : S' ⟶ S` as a base change of `𝟙 S` carries the
trivial descent datum of `U` to the trivial descent datum of `S' ×_S U`. -/
def trivialPullbackFunctorIso (P : PullbackFunctor (𝟙 S) (𝟙 S') h h (by simp)) :
    trivialFunctor S ⋙ P.functor ≅ Over.pullback h ⋙ trivialFunctor S' :=
  NatIso.ofComponents (fun U ↦ trivialPullbackDatumIso h P ((trivialFunctor S).obj U)) (by
    intro U V g
    refine DescentData.hom_ext ?_
    intro i
    cases i
    exact (P.map ((trivialFunctor S).map g)).symm)

end Trivial

section Squares

variable {S S' X X' : Scheme.{u}}

/-- The pullback functor of the square with vertical arrows `𝟙 S` and `a'` whose horizontal
arrow is the composite `f ≫ a`. -/
abbrev compositePullbackFunctor (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S) (f : X' ⟶ X)
    (comm : f ≫ a = a' ≫ h) :
    PullbackFunctor (𝟙 S) a' h (f ≫ a) (by simp [comm]) :=
  pullbackFunctor (𝟙 S) a' h (f ≫ a) (by simp [comm])

/-- The pullback functor of the same square, with the horizontal arrow written as `a' ≫ h`. -/
abbrev basePullbackFunctor (a' : X' ⟶ S') (h : S' ⟶ S) :
    PullbackFunctor (𝟙 S) a' h (a' ≫ h) (by simp) :=
  pullbackFunctor (𝟙 S) a' h (a' ≫ h) (by simp)

/-- The pullback functor of the square expressing `h` as a base change of `𝟙 S`. -/
abbrev trivialBasePullbackFunctor (h : S' ⟶ S) :
    PullbackFunctor (𝟙 S) (𝟙 S') h h (by simp) :=
  pullbackFunctor (𝟙 S) (𝟙 S') h h (by simp)

end Squares

section Square

variable {S S' X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} {h : S' ⟶ S} {f : X' ⟶ X}
  {comm : f ≫ a = a' ≫ h} (P : PullbackFunctor a a' h f comm)

include comm in
/-- **Pullback of canonical descent data.** The canonical descent datum of `U` relative to
`X / S`, pulled back along the square, is the canonical descent datum of `S' ×_S U` relative
to `X' / S'`. -/
def canonicalPullbackFunctorIso :
    canonicalFunctor a ⋙ P.functor ≅ Over.pullback h ⋙ canonicalFunctor a' :=
  Functor.associator (trivialFunctor S) (canonicalPullbackFunctor a).functor P.functor ≪≫
    Functor.isoWhiskerLeft (trivialFunctor S)
      ((pullbackFactorizationIso (compositePullbackFunctor a a' h f comm)
            (canonicalPullbackFunctor a) P).symm ≪≫
        (pullbackFunctorIsoOfSpec (compositePullbackFunctor a a' h f comm)
            (basePullbackFunctor a' h)).iso ≪≫
        pullbackFactorizationIso (basePullbackFunctor a' h) (trivialBasePullbackFunctor h)
          (canonicalPullbackFunctor a')) ≪≫
    (Functor.associator (trivialFunctor S) (trivialBasePullbackFunctor h).functor
      (canonicalPullbackFunctor a').functor).symm ≪≫
    Functor.isoWhiskerRight (trivialPullbackFunctorIso h (trivialBasePullbackFunctor h))
      (canonicalPullbackFunctor a').functor ≪≫
    Functor.associator (Over.pullback h) (trivialFunctor S')
      (canonicalPullbackFunctor a').functor

include comm in
/-- The pullback of the canonical descent datum of `U` is the canonical descent datum of
`S' ×_S U`. -/
def canonicalDatumPullbackIso (U : Over S) :
    P.functor.obj ((canonicalFunctor a).obj U) ≅
      (canonicalFunctor a').obj ((Over.pullback h).obj U) :=
  (canonicalPullbackFunctorIso P).app U

include comm in
/-- **Effectivity is inherited by pullbacks of descent data.** If a descent datum relative to
`X / S` is the canonical descent datum of `U`, its pullback along the square is the canonical
descent datum of `S' ×_S U`. -/
theorem isEffective_pullback {D : DescentData (fun _ : Unit ↦ a)} (hD : D.IsEffective) :
    (P.functor.obj D).IsEffective := by
  obtain ⟨U, ⟨e⟩⟩ := hD
  exact ⟨(Over.pullback h).obj U,
    ⟨(canonicalDatumPullbackIso P U).symm ≪≫ P.functor.mapIso e⟩⟩

end Square

end AlgebraicGeometry.DescentData

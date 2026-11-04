module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi

/-!
# The derived pullback-pushforward adjunction from the K-flat comparison clause

Tag 07A6's adjunction `Lf^* ⊣ Rf_*` over a ringed topos is built by
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackPushforwardAdjunction`
relative to a *resolving datum* for `f^*`, and at the
K-flat class the resolving half is discharged there, leaving the exactness half
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat`.

That exactness half is **not** the shape in which Tag 06YY states its own conclusion.  Tag
06YY states that the canonical comparison `Lf^* K ⟶ f^* K` is invertible on a complex that
is K-flat with flat terms.  This file closes the gap between the two shapes: the comparison
clause *implies* the exactness clause, by the naturality square of the comparison together
with the fact that `Qh` inverts quasi-isomorphisms.

The consequence is that Tag 07A6's remaining input is implied by one already-stated Tag 06YY
clause, rather than by a bespoke exactness property, and the implication is machine-checked
rather than asserted in a comment.

**This reduction cannot discharge the input.**  As the elaborated signature shows,
`Stacks.Sheaves.RingedToposDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat_of_flat`
  takes
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` as an explicit argument — the
same declaration carries it as a section variable `hinv` and `include`s it — so the
clause reached here is itself a consequence of the
input it replaces, and feeding it back is circular.  The reduction that is not is
`pullbackInvertsQuasiIso_isKFlat_of_acyclic_pullbackComplex`.

## Main results

* `pullbackInvertsQuasiIso_isKFlat_of_isIso_derivedPullbackComparison`: the
  comparison clause implies the exactness clause.
* `pullbackInvertsQuasiIso_isKFlat_of_isIso_derivedPullbackComparison_obj`: the
  same, with the hypothesis taken in Tag 06YY's own `HomotopyCategory.quotient`-of-a-complex
  shape.
* `derivedPullbackPushforwardAdjunctionOfComparison`,
  `derivedPullbackPushforwardAdjunctionOfComparison_unit_fac`,
  `derivedPullbackPushforwardAdjunctionOfComparison_counit_fac`: the Tag 07A6
  adjunction and its two factorization identities, from that one clause.

## Implementation notes

*Why the naturality square suffices.*  Write `α` for the comparison
`Qh ⋙ Lf^* ⟶ f^*`-on-homotopy.  For a quasi-isomorphism `s : K ⟶ M` between complexes in the
K-flat class, naturality reads
`(Qh ⋙ Lf^*).map s ≫ α.app M = α.app K ≫ (f^* on homotopy).map s`.  The left factor is
invertible because `Qh` inverts `s` and a functor carries isomorphisms to isomorphisms, and
the two components of `α` are invertible by hypothesis; so the remaining factor is a
composite of isomorphisms.  No exactness of `f^*` is used directly — it enters only through
the hypothesis.

*The universe narrowing is inherited, not chosen here.*
  `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction` states its results
for `X Y : AlgebraicGeometry.RingedTopos.{w, w, w}`, with the two topoi's site universes
collapsed onto one, although `AlgebraicGeometry.RingedToposSiteHom` keeps them independent.
This file follows that narrowing because it consumes those declarations; it is not a decision
taken here.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe w

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ))]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- If the canonical comparison `Lf^* ⟶ f^*` is invertible on every K-flat complex with flat
terms, then degreewise pullback inverts the quasi-isomorphisms between such complexes.  This
turns Tag 06YY's comparison clause into the exactness clause that Tag 07A6's resolving datum
asks for. -/
theorem pullbackInvertsQuasiIso_isKFlat_of_isIso_derivedPullbackComparison
    (h : ∀ M : HomotopyCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ),
      IsKFlat (Y := Y) M → IsIso ((derivedPullbackComparison f).app M)) :
    PullbackInvertsQuasiIso f (IsKFlat (Y := Y)) := by
  intro K M s hs hK hM
  have hQ : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ)) s hs
  have hL : IsIso ((DerivedCategory.Qh ⋙ derivedPullback f).map s) := by
    rw [Functor.comp_map]
    infer_instance
  have hαK := h K hK
  have hαM := h M hM
  have key : (derivedPullbackComparison f).app K ≫ (pullbackOnHomotopy f).map s =
      (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫
        (derivedPullbackComparison f).app M :=
    ((derivedPullbackComparison f).naturality s).symm
  have hcomp : IsIso ((derivedPullbackComparison f).app K ≫ (pullbackOnHomotopy f).map s) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_left ((derivedPullbackComparison f).app K)
    ((pullbackOnHomotopy f).map s)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Tag 06YY's comparison clause, stated on the image of a cochain complex under the
homotopy-category quotient, implies the exactness clause of Tag 07A6's resolving datum. -/
theorem pullbackInvertsQuasiIso_isKFlat_of_isIso_derivedPullbackComparison_obj
    (h : ∀ K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      IsKFlat (Y := Y) ((HomotopyCategory.quotient _ (.up ℤ)).obj K) →
        IsIso ((derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) :
    PullbackInvertsQuasiIso f (IsKFlat (Y := Y)) := by
  refine pullbackInvertsQuasiIso_isKFlat_of_isIso_derivedPullbackComparison f (fun M hM => ?_)
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  exact h N hM

/-- **Tag 07A6 from the Tag 06YY comparison clause.**  If the canonical comparison
`Lf^* ⟶ f^*` is invertible on the K-flat complexes with flat terms, then the derived pullback
is left adjoint to the derived pushforward.  The resolving half of the datum is Tag 06YS
(`hasResolutions_isKFlat`), and the pushforward half is unconditional. -/
noncomputable def derivedPullbackPushforwardAdjunctionOfComparison
    (h : ∀ M : HomotopyCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ),
      IsKFlat (Y := Y) M → IsIso ((derivedPullbackComparison f).app M)) :
    derivedPullback f ⊣ derivedPushforward f :=
  derivedPullbackPushforwardAdjunction f _ hasResolutions_isKFlat
    (pullbackInvertsQuasiIso_isKFlat_of_isIso_derivedPullbackComparison f h)

/-- The unit of `derivedPullbackPushforwardAdjunctionOfComparison` agrees with the ordinary
pullback--pushforward unit after applying the canonical comparison maps. -/
theorem derivedPullbackPushforwardAdjunctionOfComparison_unit_fac
    (h : ∀ M : HomotopyCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ),
      IsKFlat (Y := Y) M → IsIso ((derivedPullbackComparison f).app M))
    (M : HomotopyCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ)) :
    (derivedPullbackPushforwardAdjunctionOfComparison f h).unit.app
          (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward f).map ((derivedPullbackComparison f).app M) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
        (derivedPushforwardUnit f).app
          ((f.pullbackTopos.mapHomotopyCategory (.up ℤ)).obj M) :=
  derivedPullbackPushforwardAdjunction_unit_fac f _ hasResolutions_isKFlat
    (pullbackInvertsQuasiIso_isKFlat_of_isIso_derivedPullbackComparison f h) M

/-- The counit of `derivedPullbackPushforwardAdjunctionOfComparison` agrees with the ordinary
pullback--pushforward counit after applying the canonical comparison maps. -/
theorem derivedPullbackPushforwardAdjunctionOfComparison_counit_fac
    (h : ∀ M : HomotopyCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ),
      IsKFlat (Y := Y) M → IsIso ((derivedPullbackComparison f).app M))
    (K : HomotopyCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ)) :
    (derivedPullback f).map ((derivedPushforwardUnit f).app K) ≫
        (derivedPullbackPushforwardAdjunctionOfComparison f h).counit.app
          (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app
          ((f.pushforwardTopos.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app K) :=
  derivedPullbackPushforwardAdjunction_counit_fac f _ hasResolutions_isKFlat
    (pullbackInvertsQuasiIso_isKFlat_of_isIso_derivedPullbackComparison f h) K

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

end

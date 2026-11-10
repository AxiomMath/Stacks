module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackAlongRingedTopoi

/-!
# Tag 07A6's remaining input, reduced to one acyclicity statement about `f^*`

Tag 07A6's adjunction `Lf^* ⊣ Rf_*` over a ringed topos is built by
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackPushforwardAdjunction`
relative to a resolving datum for `f^*`.  At the class of K-flat complexes with flat terms the
resolving half is discharged, from Tag 06YS, by
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat`, and the
pushforward half is unconditional, so the single remaining input is the exactness half
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat`: that degreewise pullback
carries a *quasi-isomorphism between* complexes of the class to an isomorphism of `D(O)`.

This file replaces that morphism-level input by a statement about a *single* complex:

> the degreewise pullback of an acyclic K-flat complex with flat terms is acyclic.

That is the shape in which the source's argument supplies it, and the shape the Tag 0G7E
machinery produces, so the reduction is what connects Tag 07A6 to Tags 05VD and 0G6R.

## Main results

* `pullbackInvertsQuasiIso_isKFlat_of_acyclic_pullbackComplex`: the acyclicity
  statement implies the exactness half of the resolving datum.
* `derivedPullbackPushforwardAdjunctionOfAcyclic`,
  `derivedPullbackPushforwardAdjunctionOfAcyclic_unit_fac`,
  `derivedPullbackPushforwardAdjunctionOfAcyclic_counit_fac`: the whole
  conclusion of Tag 07A6 — the adjunction and its two factorization identities — from that one
  acyclicity statement.

## Implementation notes

*Why a reduction to a single complex is the one that helps.*  The companion reduction
`pullbackInvertsQuasiIso_isKFlat_of_isIso_derivedPullbackComparison` sends the same input to
Tag 06YY's comparison clause
`Stacks.Sheaves.RingedToposDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat_of_flat`.
That reduction is sound as an implication but **cannot discharge anything**: by its
elaborated signature, that declaration takes
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` as an explicit argument — the
same declaration carries it as the parameter `hinv` and includes it — so the clause it
reduces to is itself a consequence of the input it was meant to replace.  The reduction here
goes to a statement that no declaration in the tree derives from
`PullbackInvertsQuasiIso`, and whose inputs are Tags 05VD and 0G6R.

*The mapping cone, not the abstract third vertex.*  `HomotopyCategory.quasiIso` is
`(HomotopyCategory.subcategoryAcyclic _).trW`, so a quasi-isomorphism is exactly a morphism
sitting in a distinguished triangle with acyclic third vertex, and
`CategoryTheory.ObjectProperty.trW_iff_of_distinguished` reads that off *any* distinguished
triangle on the morphism.  The third vertex must nevertheless be taken to be the mapping cone
of a representative `Quot.out s`, and **not** the abstract vertex produced by
`trW_iff`: `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` asks for flatness of
the *terms*, which is not invariant under homotopy equivalence, so the abstract vertex need not lie
in the class even though the cone does
(`Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone`).  This is the same constraint
that shapes `Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated`.

*Why no comparison of `f^*` with the cone is needed.*  Degreewise pullback is additive, so
`CategoryTheory.Functor.mapHomotopyCategory` of it is a triangulated functor
(`Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean`), and the image of the
mapping-cone triangle is again distinguished.  Reading
`trW_iff_of_distinguished` on that image is what turns acyclicity of `f^*` of the cone into the
quasi-isomorphism property of `f^*s`, with no iso `f^*(cone φ) ≅ cone (f^*φ)` written out.  The
only transport is `CategoryTheory.Functor.mapHomotopyCategoryFactors`, which moves between
`f^*` applied after the quotient and the quotient applied after degreewise `f^*`, and acyclicity
is closed under isomorphism.

*The hypothesis is spelled with Tag 0G7E's pullback functor.*
`Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f` is the functor `f^*` on complexes
that every conclusion of Stacks Tag 0G7E is stated with, so the hypothesis below is written with it
rather than with a second spelling of `f.pullbackTopos.mapHomologicalComplex`.

*What is not proved here.*  The converse — that
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` implies the acyclicity
statement, which would make the two equivalent and so settle that this reduction is not a
strengthening — is **not** proved.  It would be the quasi-isomorphism `0 ⟶ K` for an acyclic
`K` of the class, and the tree has no declaration putting the zero complex in the class: there
is no K-flatness statement for a zero or zero-isomorphic complex under
`CochainComplex.KFlatBifunctor.KFlat` anywhere in either tree.  So the acyclicity statement is
recorded as sufficient, not as equivalent.

*No tag is placed in this file.*  Everything here is a reduction of Tag 07A6's remaining
hypothesis, not an assertion of the source, and the conclusions carry a hypothesis that
Tag 07A6 itself does not have.

*The universe narrowing is inherited, not chosen here.*
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction` states its results for
`X Y : AlgebraicGeometry.RingedTopos.{w, w, w}`, with the two topoi's site universes collapsed
onto one, although `AlgebraicGeometry.RingedToposSiteHom` keeps them independent.  Tag 0G7E is
pinned at the same `RingedTopos.{u, u, u}` and records three independent forcings of it.  This
file consumes both and follows them; it takes no decision.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

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

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The exactness half of Tag 07A6's resolving datum, from one acyclicity statement.**  If
degreewise pullback carries every *acyclic* K-flat complex of `O'`-modules with flat terms to an
acyclic complex, then it carries every quasi-isomorphism *between* K-flat complexes with flat
terms to an isomorphism of `D(O)`.

The cone of such a quasi-isomorphism is acyclic, and is again K-flat with flat terms by
`Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone`; its degreewise pullback is then
acyclic by hypothesis, and reading `CategoryTheory.ObjectProperty.trW_iff_of_distinguished` on the
image of the mapping-cone triangle under the triangulated functor `K(f^*)` gives the
conclusion. -/
theorem pullbackInvertsQuasiIso_isKFlat_of_acyclic_pullbackComplex
    (hac : ∀ K : CochainComplex
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, w, w, w} Y.O) K →
      (∀ i : ℤ, SheafOfModules.IsFlat.{w, w, w, w} (O := Y.O) (K.X i)) →
      K.Acyclic → ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K).Acyclic)
        :
    PullbackInvertsQuasiIso f (IsKFlat (Y := Y)) := by
  intro K M s hs hK hM
  obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨M₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  -- Replace `s` by the image of a representative chain map, so that the mapping-cone triangle
  -- of that representative has `s` itself as its first morphism, up to no rewriting at all.
  obtain ⟨s₀, rfl⟩ : ∃ s₀ : K₀ ⟶ M₀,
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s₀ = s :=
    ⟨Quot.out s, HomotopyCategory.quotient_map_out s⟩
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished s₀
  -- The cone of `s₀` is acyclic, because its image in the homotopy category is a
  -- quasi-isomorphism.
  have hacyc : (CochainComplex.mappingCone s₀).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    refine (ObjectProperty.trW_iff_of_distinguished
      (HomotopyCategory.subcategoryAcyclic
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) _ hT).1 ?_
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact hs
  -- The cone is K-flat with flat terms, so its degreewise pullback is acyclic.
  have hcone := Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone s₀ hK hM
  let cone := CochainComplex.mappingCone s₀
  have hpull := hac cone hcone.1 hcone.2 hacyc
  -- Read the quasi-isomorphism property off the image of the mapping-cone triangle.
  have hFT := (f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).map_distinguished _ hT
  have h3 : HomotopyCategory.subcategoryAcyclic
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone s₀))) :=
    ObjectProperty.prop_of_iso _
      (((f.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
        (CochainComplex.mappingCone s₀)).symm)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hpull)
  have hq : HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
      ((f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s₀)) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact (ObjectProperty.trW_iff_of_distinguished
      (HomotopyCategory.subcategoryAcyclic
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) _ hFT).2 h3
  exact Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) _ hq

section Adjunction

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

/-- **Tag 07A6 from the acyclicity statement.**  If degreewise pullback carries every acyclic
K-flat complex with flat terms to an acyclic complex, the derived pullback is left adjoint to
the derived pushforward. -/
noncomputable def derivedPullbackPushforwardAdjunctionOfAcyclic
    (hac : ∀ K : CochainComplex
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, w, w, w} Y.O) K →
      (∀ i : ℤ, SheafOfModules.IsFlat.{w, w, w, w} (O := Y.O) (K.X i)) →
      K.Acyclic → ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K).Acyclic)
        :
    derivedPullback f ⊣ derivedPushforward f :=
  derivedPullbackPushforwardAdjunction f _ hasResolutions_isKFlat
    (pullbackInvertsQuasiIso_isKFlat_of_acyclic_pullbackComplex f hac)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The unit of `derivedPullbackPushforwardAdjunctionOfAcyclic` agrees with the ordinary
pullback--pushforward unit after applying the canonical comparison maps. -/
theorem derivedPullbackPushforwardAdjunctionOfAcyclic_unit_fac
    (hac : ∀ K : CochainComplex
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, w, w, w} Y.O) K →
      (∀ i : ℤ, SheafOfModules.IsFlat.{w, w, w, w} (O := Y.O) (K.X i)) →
      K.Acyclic → ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K).Acyclic)
    (M : HomotopyCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)) :
    (derivedPullbackPushforwardAdjunctionOfAcyclic f hac).unit.app
          (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward f).map ((derivedPullbackComparison f).app M) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
        (derivedPushforwardUnit f).app
          ((f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  derivedPullbackPushforwardAdjunction_unit_fac f _ hasResolutions_isKFlat
    (pullbackInvertsQuasiIso_isKFlat_of_acyclic_pullbackComplex f hac) M

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The counit of `derivedPullbackPushforwardAdjunctionOfAcyclic` agrees with the ordinary
pullback--pushforward counit after applying the canonical comparison maps. -/
theorem derivedPullbackPushforwardAdjunctionOfAcyclic_counit_fac
    (hac : ∀ K : CochainComplex
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, w, w, w} Y.O) K →
      (∀ i : ℤ, SheafOfModules.IsFlat.{w, w, w, w} (O := Y.O) (K.X i)) →
      K.Acyclic → ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K).Acyclic)
    (K : HomotopyCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) :
    (derivedPullback f).map ((derivedPushforwardUnit f).app K) ≫
        (derivedPullbackPushforwardAdjunctionOfAcyclic f hac).counit.app
          (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app
          ((f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app K) :=
  derivedPullbackPushforwardAdjunction_counit_fac f _ hasResolutions_isKFlat
    (pullbackInvertsQuasiIso_isKFlat_of_acyclic_pullbackComplex f hac) K

end Adjunction

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

end

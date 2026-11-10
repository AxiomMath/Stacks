module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTraceSheafHom
public import
 StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor

/-!
# The two models of Tag 0A77 agree, and the trace in the bifunctor model

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces.  [Stacks, Tag 0A77] identifies
derived sheaf Hom with exact support, followed by derived pushforward, with the derived internal
Hom from `i_* 𝒪_Z`:

`Ri_* R ℰom(𝒪_Z, -) ≅ R ℰom_{𝒪_X}(i_* 𝒪_Z, -)`.

The right-hand side has two realizations:

* the **total-right-derived model**, `derivedHomSheafFromPushforwardStructureSheaf`, the right
  derived functor of the underived internal Hom `ℰom_{𝒪_X}(i_* 𝒪_Z, -)`, with the isomorphism
  `derivedModulePushforwardDerivedSheafHomExactSupportIso`; and
* the **bifunctor model**, the derived internal Hom bifunctor evaluated at the derived
  pushforward `Ri_* 𝒪_Z` of the structure sheaf, with the isomorphism
  `derivedSheafHomExactSupportPushforwardNatIso`.

The two isomorphisms have the *same source functor*, `R ℰom(𝒪_Z, -) ⋙ Ri_*`, so there is exactly
one isomorphism of the two targets through which they agree.  This file names it, proves that it
is the unique such isomorphism, and uses it to carry the trace — the counit of [Stacks, Tag 0A76]
— over to the bifunctor model.

## Main definitions

* `derivedSheafHomPushforwardModelComparison`: the comparison
  `R ℰom_{𝒪_X}(Ri_* 𝒪_Z, -) ≅ R ℰom_{𝒪_X}(i_* 𝒪_Z, -)` of the two models of [Stacks, Tag 0A77].
* `bifunctorEvaluationAtOne`: the map `R ℰom_{𝒪_X}(Ri_* 𝒪_Z, -) ⟶ 𝟭` in the bifunctor model,
  the derived evaluation at the section `1` read through that comparison.

## Main results

* `derivedSheafHomPushforwardModelComparison_fac`: the bifunctor model of [Stacks, Tag 0A77],
  followed by the comparison, is the total-right-derived model;
  `derivedSheafHomPushforwardModelComparison_uniq` and
  `existsUnique_derivedSheafHomPushforwardModelComparison` say that this determines the
  comparison, so nothing is chosen in it.
* `derivedSheafHomExactSupportPushforwardNatIso_hom_comp_bifunctorEvaluationAtOne`: **the
  counit compatibility in the bifunctor model.** The trace `Ri_* R ℰom(𝒪_Z, K) ⟶ K` — the counit
  of [Stacks, Tag 0A76] — is the bifunctor model of [Stacks, Tag 0A77] followed by
  `bifunctorEvaluationAtOne`.  This is the triangle of [Stacks, Tag 0B6M] read in the model whose
  target is the derived internal Hom *bifunctor*, which is the model that contravariant exactness
  ([Stacks, Tag 08I0]) applies to.
* `bifunctorEvaluationAtOne_uniq`: `bifunctorEvaluationAtOne` is the only transformation out of
  the bifunctor model satisfying that compatibility, since the isomorphism of
  [Stacks, Tag 0A77] is epi.

## Implementation notes

The comparison is *forced*: the two isomorphisms of [Stacks, Tag 0A77] share their source
functor, so an isomorphism of their targets making them agree exists and is unique, and is
necessarily the composite of one with the inverse of the other.  Consequently
`derivedSheafHomPushforwardModelComparison_fac` is a cancellation and carries no mathematical
content beyond the two isomorphisms it compares; what the file adds is a trace map and a counit
compatibility stated for the bifunctor model.

`bifunctorEvaluationAtOne` is defined through the comparison, not inside the bifunctor model
itself as precomposition with a derived unit `𝒪_X ⟶ Ri_* 𝒪_Z` followed by the identification
`R ℰom_{𝒪_X}(𝒪_X, -) ≅ 𝟭` (`AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso`); the
two descriptions are not compared here. `derivedSheafHomExactSupportPushforwardNatIso` is
described only through `derivedSheafHomPushforwardNatIso_app`, whose components are given at the
classes of K-injective cochain complexes.

The category of `𝒪_X`-modules carries two definitionally equal spellings here, as it does where
`derivedSheafHomExactSupportPushforwardNatIso` is defined:
the total-right-derived model is stated over `structureSheafRing` and the bifunctor over
`Stacks.SheafOfModules.StructureSheafModules`.  The two meet only once `sheafCompose` and
`AlgebraicGeometry.SheafedSpace.sheaf` are unfolded, so both are made locally
`instance_reducible` here too; without that the two isomorphisms of [Stacks, Tag 0A77] do not
even typecheck as isomorphisms between functors of the same pair of categories.

## References

* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0B6M](https://stacks.math.columbia.edu/tag/0B6M)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **The comparison of the two models of [Stacks, Tag 0A77]:**

`R ℰom_{𝒪_X}(Ri_* 𝒪_Z, -) ≅ R ℰom_{𝒪_X}(i_* 𝒪_Z, -)`,

the derived internal Hom bifunctor evaluated at `Ri_* 𝒪_Z` on the left, and the total right
derived functor of the underived internal Hom from `i_* 𝒪_Z` on the right.

Both forms of [Stacks, Tag 0A77] — `derivedSheafHomExactSupportPushforwardNatIso` for the
bifunctor and `derivedModulePushforwardDerivedSheafHomExactSupportIso` for the total right
derived functor — have `R ℰom(𝒪_Z, -) ⋙ Ri_*` as their source, so this is the only isomorphism
through which they agree (`derivedSheafHomPushforwardModelComparison_uniq`). -/
def derivedSheafHomPushforwardModelComparison :
    (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op ((modulePushforward S.i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)))) ≅
      S.derivedHomSheafFromPushforwardStructureSheaf :=
  S.derivedSheafHomExactSupportPushforwardNatIso.symm ≪≫
    S.derivedModulePushforwardDerivedSheafHomExactSupportIso

/-- **The two models of [Stacks, Tag 0A77] agree.** The bifunctor model, followed by the
comparison of the two models, is the total-right-derived model. -/
theorem derivedSheafHomPushforwardModelComparison_fac :
    S.derivedSheafHomExactSupportPushforwardNatIso.hom ≫
        S.derivedSheafHomPushforwardModelComparison.hom =
      S.derivedModulePushforwardDerivedSheafHomExactSupportIso.hom :=
  S.derivedSheafHomExactSupportPushforwardNatIso.hom_inv_id_assoc _

/-- The componentwise form of `derivedSheafHomPushforwardModelComparison_fac`. -/
@[reassoc]
theorem derivedSheafHomPushforwardModelComparison_fac_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    S.derivedSheafHomExactSupportPushforwardNatIso.hom.app K ≫
        S.derivedSheafHomPushforwardModelComparison.hom.app K =
      S.derivedModulePushforwardDerivedSheafHomExactSupportIso.hom.app K :=
  by rw [← NatTrans.comp_app, S.derivedSheafHomPushforwardModelComparison_fac]

/-- The comparison of the two models of [Stacks, Tag 0A77] is the unique isomorphism through
which the two forms of that tag agree: they share their source functor, so an
isomorphism of their targets intertwining them is determined. -/
theorem derivedSheafHomPushforwardModelComparison_uniq
    (e : (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op ((modulePushforward S.i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)))) ≅
      S.derivedHomSheafFromPushforwardStructureSheaf)
    (he : S.derivedSheafHomExactSupportPushforwardNatIso.hom ≫ e.hom =
      S.derivedModulePushforwardDerivedSheafHomExactSupportIso.hom) :
    e = S.derivedSheafHomPushforwardModelComparison :=
  Iso.ext ((Iso.cancel_iso_hom_left S.derivedSheafHomExactSupportPushforwardNatIso _ _).mp
    (he.trans S.derivedSheafHomPushforwardModelComparison_fac.symm))

/-- There is a unique isomorphism of the two models of [Stacks, Tag 0A77] through which the two
forms of that tag agree. -/
theorem existsUnique_derivedSheafHomPushforwardModelComparison :
    ∃! e : (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op ((modulePushforward S.i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)))) ≅
      S.derivedHomSheafFromPushforwardStructureSheaf,
      S.derivedSheafHomExactSupportPushforwardNatIso.hom ≫ e.hom =
        S.derivedModulePushforwardDerivedSheafHomExactSupportIso.hom :=
  ⟨S.derivedSheafHomPushforwardModelComparison,
    S.derivedSheafHomPushforwardModelComparison_fac,
    fun e he => S.derivedSheafHomPushforwardModelComparison_uniq e he⟩

/-- **The map `R ℰom_{𝒪_X}(Ri_* 𝒪_Z, -) ⟶ 𝟭` in the bifunctor model of [Stacks, Tag 0A77]**: the
derived evaluation at the section `1` of the total-right-derived model, read through the
comparison of the two models.

It is the unique transformation out of the bifunctor model which the trace of [Stacks, Tag 0A76]
factors through, by `bifunctorEvaluationAtOne_uniq`. -/
def bifunctorEvaluationAtOne :
    (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op ((modulePushforward S.i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)))) ⟶
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :=
  S.derivedSheafHomPushforwardModelComparison.hom ≫ S.derivedEvaluationAtOne

/-- **The counit compatibility of [Stacks, Tag 0A77] in the bifunctor model**, that is, the
triangle of [Stacks, Tag 0B6M] with the derived internal Hom *bifunctor* as the middle term:
the trace `Ri_* R ℰom(𝒪_Z, K) ⟶ K` — the counit of [Stacks, Tag 0A76] — is the isomorphism
`Ri_* R ℰom(𝒪_Z, -) ≅ R ℰom_{𝒪_X}(Ri_* 𝒪_Z, -)` followed by `bifunctorEvaluationAtOne`.

The same statement for the total-right-derived model is
`derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne`; this
is that statement transported along the comparison of the two models, which is what the
bifunctor model needs in order to be usable where contravariant exactness of the derived
internal Hom ([Stacks, Tag 08I0]) is applied in the source variable. -/
theorem derivedSheafHomExactSupportPushforwardNatIso_hom_comp_bifunctorEvaluationAtOne :
    S.derivedSheafHomExactSupportPushforwardNatIso.hom ≫ S.bifunctorEvaluationAtOne =
      S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit := by
  rw [bifunctorEvaluationAtOne, ← Category.assoc,
    S.derivedSheafHomPushforwardModelComparison_fac,
    S.derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne]

/-- The componentwise form of the counit compatibility in the bifunctor model. -/
@[reassoc]
theorem derivedSheafHomExactSupportPushforwardNatIso_hom_app_comp_bifunctorEvaluationAtOne
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    S.derivedSheafHomExactSupportPushforwardNatIso.hom.app K ≫
        S.bifunctorEvaluationAtOne.app K =
      S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app K :=
  by rw [← NatTrans.comp_app,
    S.derivedSheafHomExactSupportPushforwardNatIso_hom_comp_bifunctorEvaluationAtOne]

/-- `bifunctorEvaluationAtOne` is the only transformation out of the bifunctor model of
[Stacks, Tag 0A77] through which the trace of [Stacks, Tag 0A76] factors. -/
theorem bifunctorEvaluationAtOne_uniq
    (t : (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op ((modulePushforward S.i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)))) ⟶
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))))
    (ht : S.derivedSheafHomExactSupportPushforwardNatIso.hom ≫ t =
      S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit) :
    t = S.bifunctorEvaluationAtOne :=
  (Iso.cancel_iso_hom_left S.derivedSheafHomExactSupportPushforwardNatIso _ _).mp
    (ht.trans
      S.derivedSheafHomExactSupportPushforwardNatIso_hom_comp_bifunctorEvaluationAtOne.symm)

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end

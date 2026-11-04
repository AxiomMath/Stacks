module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalUniversal
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.LeftDerived

/-! # A natural transformation of additive functors is a morphism of δ-functors

`StacksFrontier/CategoryTheory/Abelian/DeltaFunctor/LeftDerived.lean` presents the left derived
functors of an additive functor `F : C ⥤ D` as a homological δ-functor. Mathlib's
`CategoryTheory.NatTrans.leftDerived` turns a natural transformation `α : F ⟶ G` into natural
transformations `Lₙ F ⟶ Lₙ G`. This file proves that this family commutes with the connecting
morphisms, so that it is a morphism of homological δ-functors
`F.leftDerivedHomologicalDeltaFunctor ⟶ G.leftDerivedHomologicalDeltaFunctor`.

That is exactly what the universality of the δ-functors is applied to: a comparison of two
derived functors on different categories is assembled out of the comparison induced by a natural
transformation of the functors being derived, and the comparison is usable only once it is known
to be a morphism of δ-functors rather than merely a family of natural transformations.

The proof is the one of `CategoryTheory.ShortComplex.Horseshoe.δ_naturality`, with the roles of
the two variables exchanged: there a morphism of short exact sequences is fixed and the functor
is varied, here the sequence is fixed and the functor varies. Both reduce to
`HomologicalComplex.HomologySequence.δ_naturality` for a morphism of the two mapped horseshoe
sequences — here the morphism `α` induces degreewise, through
`CategoryTheory.NatTrans.mapHomologicalComplex` — because
`CategoryTheory.ProjectiveResolution.leftDerived_app_eq` presents
`CategoryTheory.NatTrans.leftDerived` by the same conjugated-homology formula that
`CategoryTheory.Functor.leftDerived_map_eq` gives for `Lₙ F` of a morphism.

## Main definitions

* `CategoryTheory.ShortComplex.Horseshoe.mapSesNatTrans`: the morphism of mapped horseshoe
  sequences induced by a natural transformation of the functors.
* `CategoryTheory.NatTrans.leftDerivedDeltaFunctorHom`: the resulting morphism of homological
  δ-functors.

## Main results

* `CategoryTheory.ShortComplex.Horseshoe.δ_natTrans` and
  `CategoryTheory.Functor.leftDerivedδ_natTrans`: the connecting morphisms commute with
  `CategoryTheory.NatTrans.leftDerived`.

## Implementation notes

`CategoryTheory.ProjectiveResolution.leftDerived_app_eq` is stated with the comparison spelled
`P.isoLeftDerivedObj F n` and the homology map spelled `(homologyFunctor D _ n).map`, while the
connecting morphism of the horseshoe is stated with `Horseshoe.isoPA` and
`HomologicalComplex.homologyMap`. The two spellings agree only by unfolding the `def`s `isoPA`
and `mapSes`, which `rw` will not do: `rw [Iso.inv_hom_id_assoc]` reports no occurrence of a
pattern that prints exactly. The two restatements `natTrans_app_X₁_eq` and `natTrans_app_X₃_eq`
therefore record the formula once at the horseshoe's own spelling, each proved by `exact` in
term mode, which checks the definitional equality at default transparency; after that the proof
of `δ_natTrans` is a rewrite chain in a single spelling, exactly as `δ_naturality` is.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v u v₂ u₂

namespace CategoryTheory.ShortComplex.Horseshoe

variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C} (H : Horseshoe S)
  [HasProjectiveResolutions C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)

/-- The morphism between the two images of a horseshoe sequence induced by a natural
transformation `α : F ⟶ G` of additive functors: degreewise the component of `α`, assembled by
`CategoryTheory.NatTrans.mapHomologicalComplex`. -/
def mapSesNatTrans : H.mapSes F ⟶ H.mapSes G :=
  H.ses.mapNatTrans (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ))

/-- `CategoryTheory.NatTrans.leftDerived` at `S.X₁` is computed by the horseshoe, in the spelling
in which the connecting morphism of the horseshoe is stated. -/
lemma natTrans_app_X₁_eq (n : ℕ) :
    (NatTrans.leftDerived α n).app S.X₁ = (H.isoPA F n).hom ≫
      HomologicalComplex.homologyMap (mapSesNatTrans H α).τ₁ n ≫ (H.isoPA G n).inv :=
  ProjectiveResolution.leftDerived_app_eq α H.PA n

/-- `CategoryTheory.NatTrans.leftDerived` at `S.X₃` is computed by the horseshoe, in the spelling
in which the connecting morphism of the horseshoe is stated. -/
lemma natTrans_app_X₃_eq (n : ℕ) :
    (NatTrans.leftDerived α n).app S.X₃ = (H.isoPC F n).hom ≫
      HomologicalComplex.homologyMap (mapSesNatTrans H α).τ₃ n ≫ (H.isoPC G n).inv :=
  ProjectiveResolution.leftDerived_app_eq α H.PC n

/-- **The connecting morphism of a horseshoe is natural in the functor being derived.** A natural
transformation `α : F ⟶ G` of additive functors commutes with the connecting morphisms read off a
horseshoe. -/
lemma δ_natTrans (n : ℕ) :
    H.δ F n ≫ (NatTrans.leftDerived α n).app S.X₁ =
      (NatTrans.leftDerived α (n + 1)).app S.X₃ ≫ H.δ G n := by
  have hnat := HomologicalComplex.HomologySequence.δ_naturality (mapSesNatTrans H α)
    (H.mapSes_shortExact F) (H.mapSes_shortExact G) (n + 1) n (down_rel_succ n)
  rw [natTrans_app_X₁_eq H α n, natTrans_app_X₃_eq H α (n + 1), δ, δ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hnat]

end CategoryTheory.ShortComplex.Horseshoe

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

open ShortComplex

/-- **The connecting morphism of the left derived functors is natural in the functor.** -/
lemma leftDerivedδ_natTrans {S : ShortComplex C} (hS : S.ShortExact) {F G : C ⥤ D}
    [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    F.leftDerivedδ hS n ≫ (NatTrans.leftDerived α n).app S.X₁ =
      (NatTrans.leftDerived α (n + 1)).app S.X₃ ≫ G.leftDerivedδ hS n :=
  Horseshoe.δ_natTrans (horseshoe hS) α n

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **A natural transformation of additive functors induces a morphism of the homological
δ-functors of their left derived functors.** The components are
`CategoryTheory.NatTrans.leftDerived` and the compatibility with the connecting morphisms is
`CategoryTheory.Functor.leftDerivedδ_natTrans`. -/
def leftDerivedDeltaFunctorHom {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.leftDerivedHomologicalDeltaFunctor ⟶ G.leftDerivedHomologicalDeltaFunctor where
  app n := NatTrans.leftDerived α n
  comm hS n := Functor.leftDerivedδ_natTrans hS α n

/-- The components of `CategoryTheory.NatTrans.leftDerivedDeltaFunctorHom`. -/
@[simp]
lemma leftDerivedDeltaFunctorHom_app {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    (n : ℕ) :
    (leftDerivedDeltaFunctorHom α).app n = NatTrans.leftDerived α n :=
  rfl

end CategoryTheory.NatTrans

end

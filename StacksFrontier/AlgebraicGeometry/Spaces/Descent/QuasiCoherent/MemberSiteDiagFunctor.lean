module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteDiagonal

/-!
# The charts of one member, as a functor to the site of the charts of the members

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces étale over `X`.  Reading a morphism of charts of one member as a morphism of the
site of the charts of the members,
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagHom`, is functorial; this file carries
that functor and the identifications a consumer of the sheaf condition on the charts of the
members needs on top of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbFunctor_map_memberDiagHom_eq`.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagFunctor`: the charts of one member of
  the family, as a functor into the site of the charts of the members.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagFunctor_map` and
  `.memberDiagHom_id`: the functor reads a morphism of charts as
  `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagHom` does, and an identity as an
  identity.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagHom_comp_congr`: two morphisms of charts
  of one member with a common composite stay so when read as morphisms of the site.  This is the
  commutation a compatible family on a sieve of the site is read at.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagRestrict_obj`: the presheaf of abelian
  groups of a descent datum, read along that functor, has the sections of the component module on
  the nose.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagSect_type` and `.memberDiagSect_type'`:
  the two spellings of the sections of that presheaf over a chart of a member, **with an abelian
  group mapping in**, are one type.  This is the identification the sheaf condition for a presheaf
  of abelian groups is tested at, `CategoryTheory.Presheaf.IsSheaf` being the sheaf condition of
  every `CategoryTheory.coyoneda` reading, and it is the form in which a family of sections on a
  sieve of the charts of the members is read as a family of sections of the component module.

## Implementation notes

`AlgebraicGeometry.Space.QuasiCoherentDescent.opComp_map` states the restriction map of a presheaf
read along a functor with **every datum a variable**.  It is `rfl`, and it is stated because the
instantiation of a variable is a first-order assignment while the same reduction performed on the
presheaf of a descent datum is a timeout: the presheaf's restriction map carries the transition of
the datum, and reducing a composite functor's restriction map down to it unfolds that transition.

`.memberDiagSect_type` is a **theorem** and not a coercion carried by a `def`.  The same
identification in the type of a `def` whose body is the section itself is a kernel timeout, while
the identification as an equation of types is affordable; so a consumer transports along it rather
than relying on the two spellings to be recognized.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

/-- **The restriction map of a presheaf read along a functor**, with every datum a variable: it is
the presheaf's restriction map at the morphism the functor produces.  See the implementation
notes for why this is stated at variables. -/
theorem opComp_map {D C A : Type*} [Category D] [Category C] [Category A]
    (F : D ⥤ C) (P : Cᵒᵖ ⥤ A) {p q : Dᵒᵖ} (g : p ⟶ q) :
    (F.op ⋙ P).map g = P.map (F.map g.unop).op := rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### The charts of one member as a functor -/

/-- **Reading the identity morphism of a chart of a member as a morphism of the site of the charts
of the members gives the identity.**  The site is an induced category, so the equation is the
equation of the underlying morphisms of charts of `X`, where it is functoriality of the étale
restriction along the member morphism. -/
theorem memberDiagHom_id {i : I} (V : SmallEtale B S hS (Yi i).1) :
    memberDiagHom B S hS Yi f hf (𝟙 V) = 𝟙 (memberPair B S hS Yi f hf i V) :=
  InducedCategory.hom_ext ((smallEtalePostcomp B S hS (f i) (hf i)).map_id V)

/-- **The charts of one member of the family, as a functor into the site of the charts of the
members.**  On objects it is
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberPair` at that member, and on morphisms it is
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagHom`; the two laws are `.memberDiagHom_id`
and `.memberDiagHom_comp`. -/
def memberDiagFunctor (i : I) :
    SmallEtale B S hS (Yi i).1 ⥤ MemberSite B S hS Yi f hf where
  obj V := memberPair B S hS Yi f hf i V
  map g := memberDiagHom B S hS Yi f hf g
  map_id V := memberDiagHom_id B S hS Yi f hf V
  map_comp h g := memberDiagHom_comp B S hS Yi f hf h g

/-- The functor of the charts of one member sends a chart to the corresponding object of the site
of the charts of the members. -/
theorem memberDiagFunctor_obj (i : I) (V : SmallEtale B S hS (Yi i).1) :
    (memberDiagFunctor B S hS Yi f hf i).obj V = memberPair B S hS Yi f hf i V := rfl

/-- The functor of the charts of one member reads a morphism of charts of that member as a
morphism of the site of the charts of the members. -/
theorem memberDiagFunctor_map (i : I) {W V : SmallEtale B S hS (Yi i).1} (a : W ⟶ V) :
    (memberDiagFunctor B S hS Yi f hf i).map a = memberDiagHom B S hS Yi f hf a := rfl

/-- **Two morphisms of charts of one member with a common composite have a common composite when
read as morphisms of the site of the charts of the members.**  This is the commutation a
compatible family on a sieve of the site is read at, so that the compatibility of such a family
restricted to the arrows inside one member is the compatibility of the original family at the
morphisms of the site those arrows produce. -/
theorem memberDiagHom_comp_congr {i : I} {Z Y₁ Y₂ V : SmallEtale B S hS (Yi i).1}
    (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) (a₁ : Y₁ ⟶ V) (a₂ : Y₂ ⟶ V) (h : g₁ ≫ a₁ = g₂ ≫ a₂) :
    memberDiagHom B S hS Yi f hf g₁ ≫ memberDiagHom B S hS Yi f hf a₁ =
      memberDiagHom B S hS Yi f hf g₂ ≫ memberDiagHom B S hS Yi f hf a₂ :=
  ((memberDiagHom_comp B S hS Yi f hf g₁ a₁).symm.trans
      (congrArg (fun k : Z ⟶ V => memberDiagHom B S hS Yi f hf k) h)).trans
    (memberDiagHom_comp B S hS Yi f hf g₂ a₂)

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

variable (D : DescentDatum B S hS Yi f)
  (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
    (fun _ => inferInstance)
    (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))

/-! ### The presheaf of a descent datum read on the charts of one member -/

/-- **The presheaf of abelian groups of a descent datum, read along the charts of one member, has
the sections of the component module at that member.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctorOfLawsV_obj_memberPair` read through
the functor of the charts of that member, at an arbitrary object of the opposite site. -/
theorem memberDiagRestrict_obj (i : I) (W : (SmallEtale B S hS (Yi i).1)ᵒᵖ) :
    ((memberDiagFunctor B S hS Yi f hf i).op ⋙
        memberFunctorOfLawsV B S hS Yi f hf hL).obj W =
      (D.F i).val.presheaf.obj W := rfl

/-- **The two spellings of the sections of the presheaf of abelian groups of a descent datum over
a chart of a member, with an abelian group mapping in, are one type.**  The sheaf condition of a
presheaf of abelian groups is the sheaf condition of every `CategoryTheory.coyoneda` reading of
it, so this is the identification a family of sections on a sieve of the charts of the members is
read as a family of sections of the component module along. -/
theorem memberDiagSect_type (E : AddCommGrpCat.{u}) (i : I) (W : SmallEtale B S hS (Yi i).1) :
    (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)).obj
        (Opposite.op (memberPair B S hS Yi f hf i W)) =
      ((D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E)).obj (Opposite.op W) := rfl

/-- `.memberDiagSect_type` with the abelian group hom written out, which is the spelling a
consumer holding a section of the component module meets. -/
theorem memberDiagSect_type' (E : AddCommGrpCat.{u}) (i : I)
    (W : SmallEtale B S hS (Yi i).1) :
    (E ⟶ (memberFunctorOfLawsV B S hS Yi f hf hL).obj
        (Opposite.op (memberPair B S hS Yi f hf i W))) =
      (E ⟶ (D.F i).val.presheaf.obj (Opposite.op W)) := rfl

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end

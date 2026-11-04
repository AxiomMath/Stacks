module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSite
public import StacksFrontier.CategoryTheory.Adjunction.Mates
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct and inverse image for base change, across the two presentations of the small étale site

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of its underlying category. There
are two small étale sites attached to `S`: the site `AlgebraicGeometry.SmallEtale B S.obj
S.property` of Stacks 021B, whose objects are cut down by the size bound of `B`, and Mathlib's
site `AlgebraicGeometry.Scheme.Etale` of *all* schemes étale over `S`. They have the same
sheaves, by `AlgebraicGeometry.SmallEtale.sheafEquiv`, and base change along `f` is available on
both. This file identifies the two base changes on sheaves: the square of direct images
commutes, and so therefore does the square of inverse images.

Concretely, writing `ρ_S` for restriction of sheaves along the embedding
`AlgebraicGeometry.SmallEtale.toEtaleSite` — the functor underlying the equivalence of sheaf
categories — the content is a natural isomorphism
```
f_* ⋙ ρ_S  ≅  ρ_T ⋙ f_*
```
between functors from sheaves on Mathlib's small étale site of `T` to sheaves on the bounded
small étale site of `S`, the left `f_*` being direct image for Mathlib's presentation and the
right one direct image for the bounded presentation; together with the comparison of the left
adjoints,
```
ρ_S⁻¹ ⋙ f⁻¹  ≅  f⁻¹ ⋙ ρ_T⁻¹ .
```
The coefficient category is arbitrary, and in particular both `Type (u + 1)` — the home of the
sheaves of sets for which the base change of a finite direct image is proved in
`AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans` — and `AddCommGrpCat.{max (u + 1) v)}` —
the home of the abelian sheaves of the proper base change development — are instances.

The one geometric input is
`AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso`, the comparison of the two base changes
on the *sites*, which holds because both are fibre products and the inclusion of the
size-bounded category of schemes preserves fibre products. Everything here is the passage from
that comparison of sites to the comparison of sheaf functors.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso` — the commuting square of
  direct images, at an arbitrary coefficient category.
* `AlgebraicGeometry.SmallEtale.toEtaleSitePullbackBaseChangeIso` — the commuting square of
  inverse images, for arbitrary chosen left adjoints of the four direct images.
* `AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso` — the same square with the two
  restriction functors replaced by the equivalences
  `AlgebraicGeometry.SmallEtale.sheafEquiv` they underlie.

## Main results

* `AlgebraicGeometry.SmallEtale.conjugateEquiv_toEtaleSitePullbackBaseChangeIso_hom` pins the
  square of inverse images down: its conjugate, under the two composite adjunctions, is the
  inverse of the square of direct images. Since conjugation is a bijection this determines the
  comparison of inverse images completely, and it is what a consumer that has to match it with
  another construction needs.

## Implementation notes

**Why the left adjoints are arguments rather than functors of `f`.** A left adjoint of a direct
image is only determined up to isomorphism, and the proper base change development, the
extension-by-zero development and Mathlib's `CategoryTheory.Functor.sheafPullback` each pick a
different representative of it. Taking the four adjunctions as arguments lets each consumer use
its own, and makes
`AlgebraicGeometry.SmallEtale.conjugateEquiv_toEtaleSitePullbackBaseChangeIso_hom` the statement
that the comparison is independent of that choice in the only sense available: it is the one
whose conjugate is the comparison of direct images.

**The spelling of the continuity hypothesis.** `AlgebraicGeometry.SmallEtale.topology` and
`AlgebraicGeometry.Scheme.smallEtaleTopology` are topologies on categories built from `S.obj`
and from `B.inclusion.obj S`, which are definitionally but not syntactically equal, so instance
search does not find the continuity of base change for Mathlib's presentation in the spelling in
which the statements below need it.
`AlgebraicGeometry.SmallEtale.isContinuous_inclusionSmallEtaleBaseChange` is that restatement,
in the style of `AlgebraicGeometry.smallEtaleBaseChange_isContinuous_of_contains`; the
continuity of the two composites is introduced inside the proof, since the same mismatch defeats
`CategoryTheory.Functor.isContinuous_comp` when its functor arguments are left implicit.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 021D](https://stacks.math.columbia.edu/tag/021D)
* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v' u' u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u})

/-- **Base change is continuous for Mathlib's presentation of the small étale site**, in the
spelling in which the schemes are presented as objects of the underlying category of a big étale
site.

`Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous` is stated for a morphism of schemes,
so its conclusion names the topologies `Scheme.smallEtaleTopology S.obj` and
`Scheme.smallEtaleTopology T.obj` while the functor it is about has source and target the small
étale sites of `B.inclusion.obj S` and `B.inclusion.obj T`. The two schemes are definitionally
equal, so the statement below typechecks, but instance search cannot pass between the two
spellings; this is the restatement it does find. -/
@[sga "4 IV 4.10.6" "1°, special case"]
public instance isContinuous_inclusionSmallEtaleBaseChange {S T : B.Scheme} (f : T ⟶ S) :
    Functor.IsContinuous (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f))
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
  Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous _

variable {S T : B.Scheme} (f : T ⟶ S) (A : Type u') [Category.{v'} A]

/-- **The two presentations of the small étale site have the same direct image along base
change.** Direct image along base change for Mathlib's presentation, followed by restriction
along the embedding of the bounded site of `S`, is restriction along the embedding of the
bounded site of `T` followed by direct image along base change for the bounded presentation.

Both direct images are restriction along a base change functor of sites, so this is the
comparison `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso` of the two base changes on
sites, read on sheaves: the two composites of sites agreeing, their restrictions agree, and
restriction along a composite is the composite of the restrictions on the nose. -/
public noncomputable def toEtaleSitePushforwardBaseChangeIso :
    (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).sheafPushforwardContinuous
          A S.obj.smallEtaleTopology T.obj.smallEtaleTopology ⋙
        (toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
          (topology B S.obj S.property) S.obj.smallEtaleTopology ≅
      (toEtaleSite B T.obj T.property).sheafPushforwardContinuous A
          (topology B T.obj T.property) T.obj.smallEtaleTopology ⋙
        (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous A
          (topology B S.obj S.property) (topology B T.obj T.property) := by
  have hc : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous (B.inclusion.map f)
  have hc1 : (toEtaleSite B S.obj S.property ⋙
      Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ S.obj.smallEtaleTopology _
  have hc2 : (AlgebraicGeometry.smallEtaleBaseChange B f ⋙
      toEtaleSite B T.obj T.property).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (topology B T.obj T.property) _
  exact Functor.sheafPushforwardContinuousComp' (F := toEtaleSite B S.obj S.property)
      (G := Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f))
      (Iso.refl _) _ _ _ _ ≪≫
    Functor.sheafPushforwardContinuousIso (toEtaleSiteBaseChangeIso B f).symm _ _ _ ≪≫
      (Functor.sheafPushforwardContinuousComp'
        (F := AlgebraicGeometry.smallEtaleBaseChange B f)
        (G := toEtaleSite B T.obj T.property) (Iso.refl _) _ _ _ _).symm

section Pullback

variable
  {LU : Sheaf S.obj.smallEtaleTopology A ⥤ Sheaf T.obj.smallEtaleTopology A}
  {LB : Sheaf (topology B S.obj S.property) A ⥤ Sheaf (topology B T.obj T.property) A}
  {ES : Sheaf (topology B S.obj S.property) A ⥤ Sheaf S.obj.smallEtaleTopology A}
  {ET : Sheaf (topology B T.obj T.property) A ⥤ Sheaf T.obj.smallEtaleTopology A}
  (adjU : LU ⊣ (Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map f)).sheafPushforwardContinuous A
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology)
  (adjB : LB ⊣ (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (topology B S.obj S.property) (topology B T.obj T.property))
  (adjS : ES ⊣ (toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
      (topology B S.obj S.property) S.obj.smallEtaleTopology)
  (adjT : ET ⊣ (toEtaleSite B T.obj T.property).sheafPushforwardContinuous A
      (topology B T.obj T.property) T.obj.smallEtaleTopology)

/-- **The two presentations of the small étale site have the same inverse image along base
change.** The left adjoint of restriction along the embedding of the bounded site of `S`,
followed by inverse image along base change for Mathlib's presentation, is inverse image along
base change for the bounded presentation followed by the left adjoint of restriction along the
embedding of the bounded site of `T`.

This is `AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso` read on left
adjoints: the two composites of direct images are isomorphic, hence the two composites of their
left adjoints are, canonically. -/
public noncomputable def toEtaleSitePullbackBaseChangeIso : ES ⋙ LU ≅ LB ⋙ ET :=
  Adjunction.leftAdjointUniq
    ((adjS.comp adjU).ofNatIsoRight (toEtaleSitePushforwardBaseChangeIso B f A))
    (adjB.comp adjT)

/-- **The comparison of inverse images is the one whose conjugate is the comparison of direct
images.** Conjugation under the two composite adjunctions is a bijection between natural
transformations of the left adjoints and natural transformations of the right adjoints in the
opposite direction, so this equation determines
`AlgebraicGeometry.SmallEtale.toEtaleSitePullbackBaseChangeIso` completely, and in particular
makes it independent of which left adjoints of the four direct images were chosen. -/
public theorem conjugateEquiv_toEtaleSitePullbackBaseChangeIso_hom :
    conjugateEquiv (adjB.comp adjT) (adjS.comp adjU)
        (toEtaleSitePullbackBaseChangeIso B f A adjU adjB adjS adjT).hom =
      (toEtaleSitePushforwardBaseChangeIso B f A).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (adjS.comp adjU) (toEtaleSitePushforwardBaseChangeIso B f A) (adjB.comp adjT)

end Pullback

/-- **The equivalence of the two sheaf categories commutes with inverse image along base
change.** The version of `AlgebraicGeometry.SmallEtale.toEtaleSitePullbackBaseChangeIso` in
which the two left adjoints of the restriction functors are the quasi-inverses supplied by
`AlgebraicGeometry.SmallEtale.sheafEquiv`, the equivalence of the sheaves of the two
presentations of the small étale site. -/
public noncomputable def sheafEquivPullbackBaseChangeIso [HasLimitsOfSize.{u, u} A]
    {LU : Sheaf S.obj.smallEtaleTopology A ⥤ Sheaf T.obj.smallEtaleTopology A}
    {LB : Sheaf (topology B S.obj S.property) A ⥤ Sheaf (topology B T.obj T.property) A}
    (adjU : LU ⊣ (Stacks.EtaleCohomology.smallEtaleBaseChange
        (B.inclusion.map f)).sheafPushforwardContinuous A
        S.obj.smallEtaleTopology T.obj.smallEtaleTopology)
    (adjB : LB ⊣ (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (topology B S.obj S.property) (topology B T.obj T.property)) :
    (sheafEquiv B S.obj S.property A).functor ⋙ LU ≅
      LB ⋙ (sheafEquiv B T.obj T.property A).functor :=
  toEtaleSitePullbackBaseChangeIso B f A adjU adjB
    (sheafEquiv B S.obj S.property A).toAdjunction
    (sheafEquiv B T.obj T.property A).toAdjunction

end AlgebraicGeometry.SmallEtale

end

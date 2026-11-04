module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Representability.GroupSchemeCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Representability on all schemes over a base and on a big fppf site

The representability criterion of [Stacks, Tag 0B9Q],
`AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor`, is stated for a functor
`G : (Over (Spec k))ᵒᵖ ⥤ GrpCat.{u}` on **all** schemes over `Spec k`, with values in `u`-small
groups. The Picard functor `Stacks.PicardFunctor.picardFunctor` of [Stacks, Tag 0B9L] lives on the
slice `AlgebraicGeometry.BigFppfOver B S hS` of a big fppf site — the schemes below a size cutoff —
and its values are classes of invertible modules, in `Type (u + 1)`. This file is the comparison
between the two settings.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.fullyFaithfulToOver`: full faithfulness of
  `AlgebraicGeometry.BigFppfOver.toOver`, which regards an `S`-scheme of the site as an
  `S`-scheme.

## Main results

* `CategoryTheory.Functor.RepresentableBy.ofNatEquiv`: a representation is transported along a
  natural bijection of type-valued functors in **different universes**; Mathlib's
  `CategoryTheory.Functor.RepresentableBy.ofIso` asks for the same universe.
* `AlgebraicGeometry.BigFppfOver.isRepresentable_of_representableBy`: a functor on all schemes
  over `S` which is represented by an `S`-scheme of the site is representable on the site, after
  transport along any natural bijection with a functor on the site.
* `AlgebraicGeometry.BigFppfOver.isRepresentable_of_grp_iso`: the same for the output of
  Tag 0B9Q, a group object `X` of `Over S` with `yonedaGrp.obj X ≅ G`.

## Implementation notes

The size of the representing scheme is a hypothesis of the last two results and not a consequence
of the others: a scheme represented on all of `Over S` need not lie below the cutoff of `B`, and
whether it does is a property of the representing scheme, so it is stated there.

## References

* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 001P](https://stacks.math.columbia.edu/tag/001P)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w w' v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **A representation is transported along a natural bijection**, between type-valued functors
in possibly different universes. -/
def RepresentableBy.ofNatEquiv {F : Cᵒᵖ ⥤ Type w} {F' : Cᵒᵖ ⥤ Type w'}
    (eq : ∀ X : Cᵒᵖ, F.obj X ≃ F'.obj X)
    (heq : ∀ {X X' : Cᵒᵖ} (g : X ⟶ X') (a : F.obj X), eq X' (F.map g a) = F'.map g (eq X a))
    {Y : C} (e : F.RepresentableBy Y) : F'.RepresentableBy Y where
  homEquiv := e.homEquiv.trans (eq _)
  homEquiv_comp f g := by
    change eq _ (e.homEquiv (f ≫ g)) = F'.map f.op (eq _ (e.homEquiv g))
    rw [e.homEquiv_comp, heq]

end CategoryTheory.Functor

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Regarding an `S`-scheme of the site as an `S`-scheme is fully faithful: the site is a full
subcategory of schemes. -/
def fullyFaithfulToOver : (toOver B S hS).FullyFaithful :=
  haveI : B.inclusion.Full := ObjectProperty.full_ι _
  haveI : B.inclusion.Faithful := ObjectProperty.faithful_ι _
  Functor.FullyFaithful.ofFullyFaithful (Over.post (X := B.obj hS) B.inclusion)

/-- **A functor on all `S`-schemes which is represented by an `S`-scheme of the site is
representable on the site.** More precisely: let `G` be a functor on `Over S` represented by `Y`,
with `Y` below the cutoff of `B`, and let `P` be a functor on the site with a natural bijection
`G(T) ≃ P(T)` for the `S`-schemes `T` of the site. Then `P` is representable, by `Y` itself. The
two functors may take values in different universes. -/
theorem isRepresentable_of_representableBy {G : (Over S)ᵒᵖ ⥤ Type w}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w'} {Y : Over S} (e : G.RepresentableBy Y)
    (hY : B.Contains Y.left)
    (eq : ∀ T : (BigFppfOver B S hS)ᵒᵖ, G.obj ((toOver B S hS).op.obj T) ≃ P.obj T)
    (heq : ∀ {T T' : (BigFppfOver B S hS)ᵒᵖ} (g : T ⟶ T') (a : G.obj ((toOver B S hS).op.obj T)),
      eq T' (G.map ((toOver B S hS).op.map g) a) = P.map g (eq T a)) :
    P.IsRepresentable :=
  have : B.inclusion.Full := ObjectProperty.full_ι _
  let Y' : BigFppfOver B S hS := Over.mk (Y := B.obj hY) (B.inclusion.preimage Y.hom)
  let e' : G.RepresentableBy ((toOver B S hS).obj Y') :=
    e.ofIsoObj (Over.isoMk (Iso.refl _)
      ((Category.id_comp _).trans
        (B.inclusion.map_preimage (X := B.obj hY) (Y := B.obj hS) Y.hom).symm))
  ((e'.ofFullyFaithful (fullyFaithfulToOver B S hS) (Iso.refl _)).ofNatEquiv
    (F' := P) eq heq).isRepresentable

/-- **The output of [Stacks, Tag 0B9Q], read on a big fppf site.** A group object `X` of
`Over S` representing `G` by `yonedaGrp.obj X ≅ G`, with `X` below the cutoff of `B`, makes every
functor on the site naturally in bijection with `G` representable. -/
theorem isRepresentable_of_grp_iso {G : (Over S)ᵒᵖ ⥤ GrpCat.{u}} (X : Grp (Over S))
    (eX : yonedaGrp.obj X ≅ G) (hX : B.Contains X.X.left)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w'}
    (eq : ∀ T : (BigFppfOver B S hS)ᵒᵖ, G.obj ((toOver B S hS).op.obj T) ≃ P.obj T)
    (heq : ∀ {T T' : (BigFppfOver B S hS)ᵒᵖ} (g : T ⟶ T') (a : G.obj ((toOver B S hS).op.obj T)),
      eq T' ((G.map ((toOver B S hS).op.map g)).hom a) = P.map g (eq T a)) :
    P.IsRepresentable :=
  isRepresentable_of_representableBy B S hS
    (G := G ⋙ CategoryTheory.forget GrpCat)
    ((yonedaGrpObjRepresentableBy X.X).ofIso
      (Functor.isoWhiskerRight eX (CategoryTheory.forget GrpCat)))
    hX eq heq

end AlgebraicGeometry.BigFppfOver

end

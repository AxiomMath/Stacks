module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SmallSections

/-!
# First cohomology under a change of the universe of the sections

Let `(C, J)` be a site and let `A` and `X` be abelian sheaves on it whose groups of sections
live in two different universes, identified by a family of additive bijections natural in the
object.  The two cannot be compared by a morphism of sheaves, and `CategoryTheory.Abelian.Ext`
out of the constant sheaf offers no comparison either: the universe lift of abelian sheaves has
no left adjoint, and the available comparisons of `Ext` along a fully faithful exact functor ask
for enough injectives in the smaller coefficient category *and* for the lift to preserve them.

In degree one there is no such obstruction, because `H^1` has a description — isomorphism
classes of torsors, [Stacks, Tag 03AJ] — in which the universe of the sections of the
coefficient sheaf plays no role.  A torsor under `X` is a torsor under `A` once its action is
read through the bijections, and its sections are then no bigger than those of `A`, so it
shrinks to a torsor under `A` with sections in the universe of `A`.  Triviality is the existence
of a global section, which the shrinking preserves in both directions.  Hence the vanishing of
`H^1` transports, in both directions and across arbitrary `Ext` universes on the two sides.

## Main definitions

* `PseudoTorsor.ofGroupEquiv`: a pseudo-torsor under one sheaf of groups read as a pseudo-torsor
  under another, along a family of group isomorphisms on sections natural in the object.  The
  underlying presheaf is untouched, so the torsor condition is literally the same condition.

## Main results

* `Stacks.Cohomology.Torsors.subsingleton_torsorIsoClasses_of_natAddEquiv`: the vanishing of the
  torsor classes transports along a natural family of additive bijections on sections.
* `Stacks.Cohomology.Torsors.subsingleton_sheafH_one_iff_torsorIsoClasses`: the vanishing of
  `H^1` is the vanishing of the torsor classes; in particular it does not depend on the `Ext`
  universe.
* `Stacks.Cohomology.Torsors.subsingleton_sheafH_one_of_natAddEquiv`: **the vanishing of the
  first cohomology transports along a natural family of additive bijections on sections**, with
  the universes of the sections and the `Ext` universes on the two sides unrelated.

## Implementation notes

`PseudoTorsor.ofGroupEquiv` takes the group isomorphisms in the direction `𝒢(U) ≃* 𝒢'(U)` and
turns a pseudo-torsor under `𝒢'` into one under `𝒢`: that is the direction in which the
shrinking of `Stacks.PseudoTorsor.shrink` is then available, the shrinking landing in the
universe of the sections of the group it is taken under.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 03AI](https://stacks.math.columbia.edu/tag/03AI)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

@[expose] public section

open CategoryTheory Opposite

universe w w' r t v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace PseudoTorsor

/-- **A pseudo-torsor read under another sheaf of groups.**  Given a family of group
isomorphisms `e U : 𝒢(U) ≃* 𝒢'(U)` natural in the object, a pseudo-torsor under `𝒢'` becomes a
pseudo-torsor under `𝒢` with the same underlying presheaf, a section `g` of `𝒢` acting as
`e U g` does. -/
public def ofGroupEquiv {𝒢 : SheafOfGroups.{r} (C := C) J} {𝒢' : SheafOfGroups.{t} (C := C) J}
    (e : ∀ U, 𝒢.presheaf.obj U ≃* 𝒢'.presheaf.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (g : 𝒢.presheaf.obj U),
      e V (𝒢.presheaf.map f g) = 𝒢'.presheaf.map f (e U g))
    (F : PseudoTorsor.{w} 𝒢') : PseudoTorsor.{w} 𝒢 where
  presheaf := F.presheaf
  isSheaf := F.isSheaf
  act U g x := F.act U (e U g) x
  one_act U x := by rw [map_one, F.one_act]
  mul_act U g h x := by rw [map_mul, F.mul_act]
  naturality f g s := by rw [F.naturality, he]
  simplyTransitive U hne s x := by
    obtain ⟨g, hg, hu⟩ := F.simplyTransitive U hne s x
    refine ⟨(e U).symm g, ?_, fun g' hg' =>
      (e U).injective ((hu _ hg').trans ((e U).apply_symm_apply g).symm)⟩
    change F.act U (e U ((e U).symm g)) s = x
    rw [MulEquiv.apply_symm_apply]
    exact hg

/-- Reading a pseudo-torsor under another sheaf of groups leaves its underlying presheaf
untouched, so it is locally nonempty exactly when the original one is. -/
public theorem isTorsor_ofGroupEquiv
    {𝒢 : SheafOfGroups.{r} (C := C) J} {𝒢' : SheafOfGroups.{t} (C := C) J}
    (e : ∀ U, 𝒢.presheaf.obj U ≃* 𝒢'.presheaf.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (g : 𝒢.presheaf.obj U),
      e V (𝒢.presheaf.map f g) = 𝒢'.presheaf.map f (e U g))
    (F : PseudoTorsor.{w} 𝒢') :
    (F.ofGroupEquiv e he).IsTorsor ↔ F.IsTorsor := Iff.rfl

end PseudoTorsor

namespace Stacks.Cohomology.Torsors

attribute [local instance] PseudoTorsor.small_presheaf_obj

/-- **The vanishing of the torsor classes transports along a natural family of additive
bijections on sections.**  A torsor under `X` is a torsor under `A` once its action is read
through the bijections; its sections are then no bigger than those of `A`, so it shrinks to a
torsor under `A`, which is trivial by hypothesis and therefore has a global section.  The
shrinking does not change the presheaf of the torsor up to a natural bijection, so the original
torsor has a global section too, hence is trivial. -/
public theorem subsingleton_torsorIsoClasses_of_natAddEquiv
    (A : Sheaf J AddCommGrpCat.{r}) (X : Sheaf J AddCommGrpCat.{t})
    (e : ∀ U, A.obj.obj U ≃+ X.obj.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.obj.obj U),
      e V (A.obj.map f x) = X.obj.map f (e U x))
    (h : Subsingleton (torsorIsoClasses A)) :
    Subsingleton (torsorIsoClasses X) := by
  let hmul : ∀ U : Cᵒᵖ, (abelianSheafAsGroupSheaf A).presheaf.obj U ≃*
      (abelianSheafAsGroupSheaf X).presheaf.obj U :=
    fun U => AddEquiv.toMultiplicative (e U)
  have hmulnat {U V : Cᵒᵖ} (f : U ⟶ V) (g : (abelianSheafAsGroupSheaf A).presheaf.obj U) :
      hmul V ((abelianSheafAsGroupSheaf A).presheaf.map f g) =
        (abelianSheafAsGroupSheaf X).presheaf.map f (hmul U g) :=
    Multiplicative.toAdd.injective (he f (Multiplicative.toAdd g))
  have trivialOf (F : AbelianTorsor X) :
      Quotient.mk (torsorSetoid X)
          ⟨trivialTorsor (abelianSheafAsGroupSheaf X),
            trivialTorsor_isTorsor (abelianSheafAsGroupSheaf X)⟩ =
        Quotient.mk (torsorSetoid X) F := by
    rw [torsor_class_eq_trivial_iff]
    let F₀ := F.1.ofGroupEquiv hmul hmulnat
    have hshrink : F₀.shrink.IsTorsor :=
      (PseudoTorsor.shrink_isTorsor F₀).2 ((PseudoTorsor.isTorsor_ofGroupEquiv _ _ F.1).2 F.2)
    have hsections : Nonempty (GlobalSections F₀.shrink.presheaf) := by
      rw [← torsor_class_eq_trivial_iff A ⟨F₀.shrink, hshrink⟩]
      exact h.elim _ _
    obtain ⟨s, hs⟩ := (nonempty_globalSections_iff_sectionFamily F₀.shrink.presheaf).1 hsections
    refine (nonempty_globalSections_iff_sectionFamily F.1.presheaf).2
      ⟨fun U => F₀.shrinkEquiv U (s U), fun {U V} f => ?_⟩
    show F₀.presheaf.map f (F₀.shrinkEquiv U (s U)) = F₀.shrinkEquiv V (s V)
    rw [← PseudoTorsor.shrinkEquiv_map F₀ f (s U), hs f]
  exact ⟨fun a b => Quotient.inductionOn₂ a b fun a b => (trivialOf a).symm.trans (trivialOf b)⟩

variable [HasSheafify J AddCommGrpCat.{r}] [HasExt.{w} (Sheaf J AddCommGrpCat.{r})]

/-- **The vanishing of the first cohomology of an abelian sheaf is the vanishing of its torsor
classes**, [Stacks, Tag 03AJ].  In particular it does not depend on the `Ext` universe. -/
public theorem subsingleton_sheafH_one_iff_torsorIsoClasses (A : Sheaf J AddCommGrpCat.{r}) :
    Subsingleton (Sheaf.H.{w} A 1) ↔ Subsingleton (torsorIsoClasses A) :=
  (torsorIsoClassesEquivH1.{w} A).subsingleton_congr.symm

/-- **The vanishing of the first cohomology transports along a natural family of additive
bijections on the sections.**  Both the universe of the sections and the `Ext` universe may
differ on the two sides: the first cohomology is the set of isomorphism classes of torsors,
[Stacks, Tag 03AJ], and that description sees only the sections of the coefficient sheaf up to
bijection. -/
public theorem subsingleton_sheafH_one_of_natAddEquiv
    [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{t})]
    (A : Sheaf J AddCommGrpCat.{r}) (X : Sheaf J AddCommGrpCat.{t})
    (e : ∀ U, A.obj.obj U ≃+ X.obj.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.obj.obj U),
      e V (A.obj.map f x) = X.obj.map f (e U x))
    (h : Subsingleton (Sheaf.H.{w} A 1)) :
    Subsingleton (Sheaf.H.{w'} X 1) :=
  (subsingleton_sheafH_one_iff_torsorIsoClasses.{w'} X).2
    (subsingleton_torsorIsoClasses_of_natAddEquiv A X e he
      ((subsingleton_sheafH_one_iff_torsorIsoClasses.{w} A).1 h))

end Stacks.Cohomology.Torsors

end

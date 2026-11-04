module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSitePushforward

/-!
# The exterior-algebra universal property across a change of presentation of a site

`SheafOfModules.GradedAlgebra.pushforward` carries a sheaf of graded algebras along a
continuous functor of sites, and carries invertibility of a homomorphism with it, but it does
**not** carry `SheafOfModules.GradedAlgebra.IsExteriorAlgebra`: that is a universal property,
quantifying over all sheaves of graded algebras on its own site, and a functor of sites says
nothing about those test objects. The implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSitePushforward.lean` record exactly this,
and name what the transfer would need: the pushforward has to be an equivalence on graded
algebras.

This file supplies that, and the hypotheses it needs are weaker than an equivalence on graded
algebras: nothing beyond **essential surjectivity of the functor of sites** together with
**fullness and faithfulness of the pushforward of sheaves of modules**. Essential surjectivity
on graded algebras is never used, and no multiplication is transported anywhere.

The reason the weaker hypotheses suffice is the direction in which a test object travels. To
prove `IsExteriorAlgebra A ι` from `IsExteriorAlgebra (F_* A) (F_* ι)` one is *given* a test
algebra `T` on the site of `A`, and `F_* T` is then a test algebra on the other site, where the
hypothesis applies; what has to come back is the resulting homomorphism, so only fullness of
`SheafOfModules.GradedAlgebra.UnitalHom.sitePushforward` is at stake, and faithfulness for the
uniqueness clause. Fullness is in turn the one place essential surjectivity of the functor of
sites enters: the pushforward being full gives a degreewise morphism, and its two laws —
multiplicativity and unitality — are then known only over the objects in the image of the
functor, from which they are propagated by naturality.

## Main results

* `SheafOfModules.GradedAlgebra.UnitalHom.exists_sitePushforward_eq`: **fullness of
  `sitePushforward` on unital homomorphisms.** Every homomorphism of the pushed-forward sheaves
  of graded algebras is the pushforward of a homomorphism.
* `SheafOfModules.GradedAlgebra.UnitalHom.sitePushforward_injective`: faithfulness, the clause
  uniqueness in a universal property needs.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_sitePushforward`: **the universal property
  of an exterior algebra descends along the pushforward.** If `F_* A` with the pushed-forward
  generator is the exterior algebra of `F_* M`, then `A` with `ι` is the exterior algebra of `M`.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_sitePushforward`: its form at the
  identity generator, which is the form every statement of [Stacks, Tag 0BQY] is in and the one
  that chains with
  `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_ofDegreewiseIso`.

The three propagation lemmas are stated separately, because each is about one law of one
structure and none of them mentions a pushforward:

* `SheafOfModules.GradedAlgebra.map_mul_of_iso` and `map_one_of_hom`: the two laws of a unital
  homomorphism hold over an object of the site as soon as they hold over an object admitting a
  morphism to it — an isomorphism for the multiplicative law, any morphism at all for the unit.
* `SheafOfModules.GradedAlgebra.SquareZero.of_iso`: the same for the square-zero condition on a
  degree-one generator.

And the hypotheses are supplied, once and for all, by an equivalence of sites:

* `Stacks.Sites.pushforwardModuleEquivOfSiteEquiv`: **the pushforward of sheaves of modules
  along an equivalence of sites, with no change of scalars, is an equivalence of categories**,
  for an arbitrary sheaf of rings on the target site, with
  `Stacks.Sites.full_pushforward_of_siteEquiv` and `faithful_pushforward_of_siteEquiv` the two
  halves of it that the transfer uses. This is Mathlib's
  `SheafOfModules.pushforwardPushforwardEquivalence` at the identity structure map, for which
  the companion structure map in the other direction is forced to be restriction along the
  counit of the equivalence of sites (`Stacks.Sites.pushforwardRingSheafCounit`), after which
  one of its two coherence conditions is an identity and the other is the triangle identity.

## Implementation notes

**Why an isomorphism and not merely a morphism, for the two laws that need one.** The
multiplicative law and the square-zero condition quantify over local sections over the object
in question, so propagating them from `W` to `V` needs every section over `V` to be a
restriction of a section over `W`; that is `exists_val_map_eq`, which uses that the morphism
`W ⟶ V` of the site is invertible. The unital law quantifies over nothing — the unit is a
global section — so for it any morphism `W ⟶ V` does.

**No `@[stacks]` attribute.** Nothing here is a clause of a tag. This is the transport
primitive which the local-to-global step of [Stacks, Tag 0BQY] consumes at the one link of its
chain of presentations that changes the site, the link between the slice site `Opens X / U` over
which the gluing runs and the open subspace `Opens ↥U` on which the local statements are proved.
Its instance there is
`Stacks.SheafOfModules.isExteriorAlgebra_id_of_openSubspaceGradedAlgebra`.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t a v v' u u'

namespace SheafOfModules.GradedAlgebra

section Propagation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- **Restriction along an isomorphism of the site is surjective on sections.** Every section
over the target of an invertible morphism of the site is the restriction of a section over its
source, namely of the restriction along the inverse. -/
theorem exists_val_map_eq {M : _root_.SheafOfModules.{a} R} {V W : Cᵒᵖ} (e : V ≅ W)
    (y : M.val.obj W) : ∃ x : M.val.obj V, M.val.map e.hom x = y :=
  ⟨M.val.map e.inv y, by
    rw [← PresheafOfModules.map_comp_apply, e.inv_hom_id]
    simp
    rfl⟩

/-- **Multiplicativity of a degreewise family of morphisms propagates along an isomorphism of
the site.** If the degreewise morphisms `u` carry products of homogeneous local sections over
`W` to products, they do so over any object `V` isomorphic to `W`: every section over `V`
restricts from one over `W`, and both multiplications and `u` commute with restriction. -/
theorem map_mul_of_iso (u : ∀ n : ℤ, A.piece n ⟶ B.piece n) (i j : ℤ) {V W : Cᵒᵖ} (e : W ≅ V)
    (h : ∀ (x : (A.piece i).val.obj W) (y : (A.piece j).val.obj W),
      (u (i + j)).val.app W ((A.mul i j).app W x y) =
        (B.mul i j).app W ((u i).val.app W x) ((u j).val.app W y))
    (x : (A.piece i).val.obj V) (y : (A.piece j).val.obj V) :
    (u (i + j)).val.app V ((A.mul i j).app V x y) =
      (B.mul i j).app V ((u i).val.app V x) ((u j).val.app V y) := by
  obtain ⟨x₀, rfl⟩ := exists_val_map_eq (M := A.piece i) e x
  obtain ⟨y₀, rfl⟩ := exists_val_map_eq (M := A.piece j) e y
  rw [PresheafOfModules.naturality_apply (u i).val e.hom x₀,
    PresheafOfModules.naturality_apply (u j).val e.hom y₀,
    ← (A.mul i j).naturality e.hom x₀ y₀,
    PresheafOfModules.naturality_apply (u (i + j)).val e.hom _, h x₀ y₀,
    (B.mul i j).naturality e.hom]

/-- **Unitality of a degreewise family of morphisms propagates along any morphism of the
site.** The unit is a global section, so there is nothing to quantify over and no invertibility
is needed: a morphism `W ⟶ V` of the site suffices. -/
theorem map_one_of_hom (u : ∀ n : ℤ, A.piece n ⟶ B.piece n) {V W : Cᵒᵖ} (g : W ⟶ V)
    (h : (u 0).val.app W (A.one.eval W) = B.one.eval W) :
    (u 0).val.app V (A.one.eval V) = B.one.eval V := by
  have hA : A.one.eval V = (A.piece 0).val.map g (A.one.eval W) :=
    (PresheafOfModules.sections_property A.one g).symm
  have hB : B.one.eval V = (B.piece 0).val.map g (B.one.eval W) :=
    (PresheafOfModules.sections_property B.one g).symm
  rw [hA, hB, PresheafOfModules.naturality_apply (u 0).val g _, h]

variable {M : _root_.SheafOfModules.{a} R}

/-- **The square-zero condition on a degree-one generator propagates along an isomorphism of
the site.** Every local section over `V` restricts from one over `W`, the generator and the
multiplication commute with restriction, and restriction carries `0` to `0`. -/
theorem SquareZero.of_iso {ι : M ⟶ A.piece 1} {V W : Cᵒᵖ} (e : W ≅ V)
    (h : ∀ s : M.val.obj W, (A.mul 1 1).app W (ι.val.app W s) (ι.val.app W s) = 0)
    (s : M.val.obj V) : (A.mul 1 1).app V (ι.val.app V s) (ι.val.app V s) = 0 := by
  obtain ⟨s₀, rfl⟩ := exists_val_map_eq (M := M) e s
  rw [PresheafOfModules.naturality_apply ι.val e.hom s₀, ← (A.mul 1 1).naturality e.hom, h s₀]
  exact map_zero _

end Propagation

section Descent

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [F.IsContinuous J K] {S : Sheaf J RingCat.{t}} {R : Sheaf K RingCat.{t}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{t} J K).obj R)
  {A B : GradedAlgebra.{t, a} R}

/-- The isomorphism witnessing essential surjectivity of the functor of sites, read in the
opposite category: every object of the target site is isomorphic to the image of its
preimage. -/
abbrev objPreimageOpIso [F.EssSurj] (V : Dᵒᵖ) :
    (op (F.obj (F.objPreimage V.unop)) : Dᵒᵖ) ≅ V :=
  (F.objObjPreimageIso V.unop).op.symm

/-- **A degreewise family of morphisms whose pushforward is a unital homomorphism is one.** The
two laws are known over every object in the image of the functor of sites, the pushforward of a
sheaf of modules having the sections of the original over the image object, and propagate from
there by `SheafOfModules.GradedAlgebra.map_mul_of_iso` and `map_one_of_hom`. -/
noncomputable def UnitalHom.ofPushforwardMap [F.EssSurj] (u : ∀ n : ℤ, A.piece n ⟶ B.piece n)
    (W : UnitalHom (_root_.SheafOfModules.GradedAlgebra.pushforward φ A)
      (_root_.SheafOfModules.GradedAlgebra.pushforward φ B))
    (hu : ∀ n : ℤ, (_root_.SheafOfModules.pushforward.{a} φ).map (u n) = W.app n) :
    UnitalHom A B where
  app := u
  map_mul i j V x y := by
    refine map_mul_of_iso u i j (objPreimageOpIso (F := F) V) (fun x₀ y₀ => ?_) x y
    have h := W.map_mul i j (op (F.objPreimage V.unop)) x₀ y₀
    simp only [← hu] at h
    exact h
  map_one V := by
    refine map_one_of_hom u (objPreimageOpIso (F := F) V).hom ?_
    have h := W.map_one (op (F.objPreimage V.unop))
    simp only [← hu] at h
    exact h

/-- **Faithfulness of the pushforward on unital homomorphisms.** A unital homomorphism is a
degreewise morphism plus two conditions, so it is determined by its degreewise morphisms, and
those are determined by their pushforwards as soon as the pushforward of sheaves of modules is
faithful. -/
theorem UnitalHom.sitePushforward_injective
    [(_root_.SheafOfModules.pushforward.{a} φ).Faithful] {g h : UnitalHom A B}
    (e : g.sitePushforward φ = h.sitePushforward φ) : g = h :=
  UnitalHom.ext fun n => (_root_.SheafOfModules.pushforward.{a} φ).map_injective
    (congrArg (UnitalHom.app · n) e)

/-- **Fullness of the pushforward on unital homomorphisms.** Every homomorphism of the
pushed-forward sheaves of graded algebras is the pushforward of one of the originals: fullness
of the pushforward of sheaves of modules produces the degreewise morphisms, and
`SheafOfModules.GradedAlgebra.UnitalHom.ofPushforwardMap` supplies their two laws. -/
theorem UnitalHom.exists_sitePushforward_eq [F.EssSurj]
    [(_root_.SheafOfModules.pushforward.{a} φ).Full]
    (W : UnitalHom (_root_.SheafOfModules.GradedAlgebra.pushforward φ A)
      (_root_.SheafOfModules.GradedAlgebra.pushforward φ B)) :
    ∃ w : UnitalHom A B, w.sitePushforward φ = W :=
  ⟨UnitalHom.ofPushforwardMap φ
    (fun n => (_root_.SheafOfModules.pushforward.{a} φ).preimage (W.app n)) W
    (fun n => Functor.map_preimage _ _),
   UnitalHom.ext fun n => by
    rw [UnitalHom.sitePushforward_app]
    exact Functor.map_preimage _ _⟩

/-- **The universal property of an exterior algebra descends along the pushforward of sheaves of
graded algebras.** If the pushforward of `A` with the pushforward of the degree-one generator
`ι` is the exterior algebra of the pushforward of `M`, then `A` with `ι` is the exterior algebra
of `M`.

This is the transfer the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSitePushforward.lean` record as needing more
than continuity, and the hypotheses are the whole of what it needs: the functor of sites is
essentially surjective and the pushforward of sheaves of modules is full and faithful. In
particular it holds whenever the two sites present the same topos.

A test algebra travels *forwards*: the universal property to be proved is handed a sheaf of
graded algebras on the site of `A`, which pushes forward to a test object for the hypothesis.
What has to travel backwards is only the homomorphism the hypothesis produces, which is
`SheafOfModules.GradedAlgebra.UnitalHom.exists_sitePushforward_eq`, and the uniqueness clause,
which is `UnitalHom.sitePushforward_injective`. No sheaf of graded algebras is ever constructed
on the site of `A`, so essential surjectivity of the pushforward on graded algebras — the
hypothesis one might expect — is not used. -/
theorem IsExteriorAlgebra.of_sitePushforward [F.EssSurj]
    [(_root_.SheafOfModules.pushforward.{a} φ).Full]
    [(_root_.SheafOfModules.pushforward.{a} φ).Faithful]
    {M : _root_.SheafOfModules.{a} R} {ι : M ⟶ A.piece 1}
    (h : IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.pushforward φ A)
      (genSitePushforward φ ι)) : IsExteriorAlgebra A ι := by
  refine ⟨fun V s => SquareZero.of_iso (objPreimageOpIso (F := F) V)
    (fun s₀ => h.1 (op (F.objPreimage V.unop)) s₀) s, fun T κ hκ => ?_⟩
  obtain ⟨w, hw⟩ := UnitalHom.exists_sitePushforward_eq φ
    (h.desc (_root_.SheafOfModules.GradedAlgebra.pushforward φ T)
      (genSitePushforward φ κ) (hκ.sitePushforward φ))
  have hdesc : ∀ g : UnitalHom A T, ι ≫ g.app 1 = κ →
      g.sitePushforward φ = w.sitePushforward φ := fun g hg =>
    (h.desc_unique _ _ (hκ.sitePushforward φ)
      ((CategoryTheory.Functor.map_comp _ ι (g.app 1)).symm.trans
        (congrArg (_root_.SheafOfModules.pushforward.{a} φ).map hg))).trans hw.symm
  have hwκ : ι ≫ w.app 1 = κ := by
    refine (_root_.SheafOfModules.pushforward.{a} φ).map_injective ?_
    rw [CategoryTheory.Functor.map_comp, ← UnitalHom.sitePushforward_app, hw]
    exact h.desc_extends _ (genSitePushforward φ κ) (hκ.sitePushforward φ)
  exact ⟨w, hwκ, fun g hg => UnitalHom.sitePushforward_injective φ (hdesc g hg)⟩

/-- **The descent of the universal property at the identity generator.** If the pushforward of
`A` is the exterior algebra of its own degree-one piece, then so is `A`.

This is the form in which the local-to-global step of [Stacks, Tag 0BQY] crosses the one link of
its chain of presentations that changes the site: neither the source nor the target module
appears, so it composes with
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_ofDegreewiseIso` at the links that stay on
one site, with no bookkeeping about generators. -/
theorem IsExteriorAlgebra.id_of_sitePushforward [F.EssSurj]
    [(_root_.SheafOfModules.pushforward.{a} φ).Full]
    [(_root_.SheafOfModules.pushforward.{a} φ).Faithful]
    (h : IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.pushforward φ A)
      (𝟙 ((_root_.SheafOfModules.GradedAlgebra.pushforward φ A).piece 1))) :
    IsExteriorAlgebra A (𝟙 (A.piece 1)) :=
  IsExteriorAlgebra.of_sitePushforward φ (ι := 𝟙 (A.piece 1)) (by
    rwa [genSitePushforward, CategoryTheory.Functor.map_id])

end Descent

end SheafOfModules.GradedAlgebra

section SiteEquivalence

/-! ### An equivalence of sites

All three hypotheses of `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_sitePushforward` hold
when the functor of sites is one half of an **equivalence of sites** — an equivalence of
categories which is continuous in both directions — and the structure map is the identity, for
an arbitrary sheaf of rings on the target site. That is the shape in which they are met in
practice, and the shape in which the open subspace of a ringed space meets them. -/

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D} (eqv : C ≌ D)
  [eqv.functor.IsContinuous J K] [eqv.inverse.IsContinuous K J] (R : Sheaf K RingCat.{t})

/-- **A sheaf of rings carried along an equivalence of sites.** -/
abbrev pushforwardRingSheafOfEquiv : Sheaf J RingCat.{t} :=
  (eqv.functor.sheafPushforwardContinuous RingCat.{t} J K).obj R

/-- **The structure map going the other way**, out of which the inverse of the equivalence on
sheaves of modules is a pushforward: restriction along the counit of the equivalence of sites,
the composite `eqv.inverse ⋙ eqv.functor` being the identity up to that counit. -/
def pushforwardRingSheafCounit :
    R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{t} K J).obj
      (pushforwardRingSheafOfEquiv J eqv R) :=
  ⟨Functor.whiskerRight (NatTrans.op eqv.counit) R.obj⟩

/-- The component of `pushforwardRingSheafCounit` at `V` is the restriction map of `R` along
the counit of the equivalence at `V`. -/
@[simp] theorem pushforwardRingSheafCounit_hom_app (V : Dᵒᵖ) :
    (pushforwardRingSheafCounit J eqv R).hom.app V = R.obj.map (eqv.counit.app V.unop).op := rfl

/-- **Pushforward of sheaves of modules along an equivalence of sites, with no change of
scalars, is an equivalence.** This is Mathlib's
`SheafOfModules.pushforwardPushforwardEquivalence` at the identity structure map, whose
companion in the other direction is then forced to be restriction along the counit, after which
the first of its two coherence conditions is an identity and the second is the triangle identity
of the equivalence of sites. -/
noncomputable def pushforwardModuleEquivOfSiteEquiv :
    _root_.SheafOfModules.{a} R ≌
      _root_.SheafOfModules.{a} (pushforwardRingSheafOfEquiv J eqv R) :=
  _root_.SheafOfModules.pushforwardPushforwardEquivalence (eqv := eqv)
    (𝟙 (pushforwardRingSheafOfEquiv J eqv R)) (pushforwardRingSheafCounit J eqv R)
    (by
      ext V : 2
      change R.obj.map (eqv.counit.app V.unop).op =
        R.obj.map (eqv.counit.app V.unop).op ≫ 𝟙 _
      simp)
    (by
      ext V : 2
      change R.obj.map (eqv.counit.app (eqv.functor.obj V.unop)).op ≫
        R.obj.map (eqv.functor.map (eqv.unit.app V.unop)).op = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, ← op_comp]
      simp)

/-- The pushforward along an equivalence of sites with no change of scalars is full. -/
instance full_pushforward_of_siteEquiv :
    (_root_.SheafOfModules.pushforward.{a} (𝟙 (pushforwardRingSheafOfEquiv J eqv R))).Full :=
  inferInstanceAs ((pushforwardModuleEquivOfSiteEquiv.{t, a} J eqv R).functor).Full

/-- The pushforward along an equivalence of sites with no change of scalars is faithful. -/
instance faithful_pushforward_of_siteEquiv :
    (_root_.SheafOfModules.pushforward.{a} (𝟙 (pushforwardRingSheafOfEquiv J eqv R))).Faithful :=
  inferInstanceAs ((pushforwardModuleEquivOfSiteEquiv.{t, a} J eqv R).functor).Faithful

end Stacks.Sites

end SiteEquivalence

end

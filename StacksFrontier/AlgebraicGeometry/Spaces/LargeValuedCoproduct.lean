module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.CategoryTheory.Sites.CoproductUniversality

/-!
# A coproduct of algebraic spaces, in an arbitrary value universe

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 02WQ** says that a coproduct
`G = ∐ᵢ Fᵢ` of algebraic spaces over `S` is an algebraic space over `S`, provided chosen
surjective étale scheme atlases of the members have a coproduct inside the site.
`AlgebraicGeometry.isAlgebraicSpace_coproduct` proves it for presheaves with values in
`Type u`, the value universe of the site. This file carries it over to the value universe
`max w u` with `w` independent of `u`, which is the generality in which a formal algebraic
space — a sheaf of `Type (u + 1)` — lives, and in which the coproducts occurring in that
theory are formed.

## Main results

* `AlgebraicGeometry.Space.small_of_sieveOfSection_mem`: the sections of a sheaf are pointwise
  `u`-small as soon as they are pointwise `u`-small on a subfunctor containing every section
  locally.
* `AlgebraicGeometry.Space.exists_shrink_isColimit_cofan_of_small`: a coproduct cocone of pointwise
  `u`-small sheaves of `Type (max w u)` is the universe lift of one of sheaves of `Type u`.
  This is the shared input of every transport of a statement about coproducts of sheaves into
  a value universe above the site's own.
* `AlgebraicGeometry.Space.small_of_isColimit_cofan`: a coproduct of algebraic spaces over `S`
  indexed by a `u`-small type is pointwise `u`-small.
* `AlgebraicGeometry.Space.isAlgebraicSpaceULift_coproduct`: **Stacks 02WQ** for presheaves
  with values in `Type (max w u)`.
* `AlgebraicGeometry.Space.isAlgebraicSpaceULift_coproduct_of_size_le`: the same with the
  disjoint union of the atlases inside the site replaced by a uniform size bound.

## Implementation notes

*The descent to the value universe of the site.* As in
`AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_relative_surjective_etale`, the presheaves
involved are pointwise `u`-small, hence universe lifts of presheaves of `Type u`, and the
algebraic-space condition is unchanged by the lift
(`AlgebraicGeometry.Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff`). The one thing that is
not automatic is that the shrunk family still has the shrunk coproduct for its coproduct: the
category of sheaves of `Type u` on this site is not known to have coproducts at all, the plus
construction being unavailable one universe below the objects of the site. What replaces the
construction is a transport of the universal property along the fully faithful lift
`CategoryTheory.uliftFunctor`: a cofan of sheaves of `Type u` is lifted to a cofan of sheaves of
`Type (max w u)`, where the hypothesis applies, and the resulting morphism is brought back down
by fullness. No coproduct of sheaves of `Type u` is formed. That transport is
`CategoryTheory.Sheaf.isColimitCofanOfCompUliftFunctor`, and the shrink-and-descend package it
produces is `AlgebraicGeometry.Space.exists_shrink_isColimit_cofan_of_small`, which Stacks 02WQ
below and the transports of Stacks 02WO share.

*Smallness of the coproduct.* The members are pointwise `u`-small because they are algebraic
spaces (`AlgebraicGeometry.Space.small_of_isAlgebraicSpaceULift`), and the union of their
ranges is therefore pointwise `u`-small when the index type is, being the image of a dependent
sum. Every section of the coproduct lies in that union after restriction along a covering sieve
(`CategoryTheory.Sheaf.sieveOfSection_iSup_range_mem`), and a section of a sheaf is determined
by its restrictions along the arrows of a covering sieve out of a small model of the site, so
the coproduct is pointwise `u`-small too. This is the only place the index type is asked to be
`u`-small; the statement in the value universe of the site asks nothing of it, because its
proof never counts sections.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe w v u

namespace AlgebraicGeometry.Space

/-! ### Smallness of the sections of a sheaf, from a small subfunctor covering them -/

/-- The sections of a sheaf on an essentially `u`-small site are pointwise `u`-small as soon as
they are pointwise `u`-small on a subfunctor `R` which contains every section locally: a section
is determined by its restrictions along the arrows of the covering sieve on which it lies in
`R`, and those arrows may be taken out of a small model of the site. -/
theorem small_of_sieveOfSection_mem
    {D : Type*} [Category* D] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology D} {Q : Dᵒᵖ ⥤ Type*}
    (hQ : Presheaf.IsSheaf J Q) (R : Subfunctor Q)
    (hR : ∀ (X : D) (x : Q.obj (op X)), R.sieveOfSection x ∈ J X)
    (hsmall : ∀ X : D, Small.{u} (R.obj (op X))) (X : D) :
    Small.{u} (Q.obj (op X)) := by
  let e := equivSmallModel.{u} D
  let E := e.inverse
  let _ : ∀ V : SmallModel.{u} D, Small.{u} (E.obj V ⟶ X) := fun _ => inferInstance
  let _ : ∀ V : SmallModel.{u} D, Small.{u} (R.obj (op (E.obj V))) := fun V => hsmall _
  apply small_of_injective (f := fun (x : Q.obj (op X))
    (V : SmallModel.{u} D) (g : E.obj V ⟶ X) =>
      {y : R.obj (op (E.obj V)) | (y : Q.obj (op (E.obj V))) = Q.map g.op x})
  intro x x' hx
  refine (((isSheaf_iff_isSheaf_of_type J Q).1 hQ).isSeparated _ (hR X x)).ext ?_
  intro Y g hg
  let V := e.functor.obj Y
  let iso : E.obj V ≅ Y := (e.unitIso.app Y).symm
  have hinj : Function.Injective (Q.map iso.hom.op) :=
    ((isIso_iff_bijective (Q.map iso.hom.op)).1 inferInstance).1
  apply hinj
  have hmem0 : R.sieveOfSection x (iso.hom ≫ g) :=
    (R.sieveOfSection x).downward_closed hg iso.hom
  let y : R.obj (op (E.obj V)) := ⟨Q.map (iso.hom ≫ g).op x, hmem0⟩
  have hset : {y : R.obj (op (E.obj V)) |
        (y : Q.obj (op (E.obj V))) = Q.map (iso.hom ≫ g).op x} =
      {y : R.obj (op (E.obj V)) |
        (y : Q.obj (op (E.obj V))) = Q.map (iso.hom ≫ g).op x'} :=
    congrFun (congrFun hx V) (iso.hom ≫ g)
  have hy : (y : Q.obj (op (E.obj V))) = Q.map (iso.hom ≫ g).op x := rfl
  have hy' : (y : Q.obj (op (E.obj V))) = Q.map (iso.hom ≫ g).op x' := hset.subset hy
  have hfinal : Q.map (iso.hom ≫ g).op x = Q.map (iso.hom ≫ g).op x' := hy.symm.trans hy'
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using hfinal

/-! ### Joint local surjectivity of the legs, in an arbitrary value universe -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The legs of a coproduct cocone of sheaves of sets are jointly locally surjective**, for a
value universe independent of the universe of the objects of the site: every section of the
vertex lies, after restriction along a covering sieve, in the image of one of the legs.

This is `CategoryTheory.Sheaf.sheafify_iSup_range_eq_top` with the value universe of the sheaves
decoupled from the universe of the morphisms of the site; the proof is the same, the
sheafification of a *subfunctor* being available in any value universe. -/
theorem sheafify_iSup_range_eq_top_ulift
    {I : Type v} {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) :
    (⨆ i, Subfunctor.range (ι i).hom).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
  let J := BigFppfOver.topology B S hS
  have hG' : Presieve.IsSheaf J G.obj := (isSheaf_iff_isSheaf_of_type J _).1 G.property
  let R : Subfunctor G.obj := ⨆ i, Subfunctor.range (ι i).hom
  let Z : Sheaf J (Type (max w u)) := ⟨(R.sheafify J).toFunctor,
    (isSheaf_iff_isSheaf_of_type J _).2 (Subfunctor.sheafify_isSheaf (G := R) hG')⟩
  let m : Z ⟶ G := ObjectProperty.homMk (R.sheafify J).ι
  have hm : Mono m := Sheaf.mono_of_injective m fun _ => Subtype.val_injective
  let κ : ∀ i, Fᵢ i ⟶ Z := fun i => ObjectProperty.homMk
    (Subfunctor.lift (ι i).hom ((le_iSup _ i).trans (Subfunctor.le_sheafify J R)))
  have hκ : ∀ i, κ i ≫ m = ι i := fun _ => rfl
  have : IsIso m := Limits.isIso_of_isColimit_cofan_fac hG m κ hκ
  rw [Subfunctor.eq_top_iff_isIso]
  exact Functor.map_isIso (ObjectProperty.ι _) m

/-- Joint local surjectivity of the legs of a coproduct cocone of sheaves of sets, in the form
a consumer uses, for a value universe independent of the universe of the objects of the site. -/
theorem sieveOfSection_iSup_range_mem_ulift
    {I : Type v} {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) (W : BigFppfOver B S hS) (x : G.obj.obj (op W)) :
    (⨆ i, Subfunctor.range (ι i).hom).sieveOfSection x ∈ BigFppfOver.topology B S hS W := by
  have hx : x ∈ ((⨆ i, Subfunctor.range (ι i).hom).sheafify
      (BigFppfOver.topology B S hS)).obj (op W) := by
    rw [sheafify_iSup_range_eq_top_ulift B S hS ι hG]; trivial
  exact hx

/-! ### Smallness of a coproduct of algebraic spaces -/

/-- A coproduct of pointwise `u`-small sheaves over `S` indexed by a `u`-small type is
pointwise `u`-small. -/
private theorem small_of_isColimit_cofan_aux {I : Type v} [Small.{u} I]
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hFᵢ : ∀ i, FunctorToTypes.Small.{u} (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) :
    FunctorToTypes.Small.{u} G.obj := by
  have hsmall : ∀ X : BigFppfOver B S hS,
      Small.{u} ((⨆ i, Subfunctor.range (ι i).hom).obj (op X)) := by
    intro X
    let _ : ∀ i, Small.{u} ((Fᵢ i).obj.obj (op X)) := fun i => hFᵢ i (op X)
    apply small_of_surjective (f := fun (p : Σ i, (Fᵢ i).obj.obj (op X)) =>
      (⟨(ι p.1).hom.app (op X) p.2, by
        rw [Subfunctor.iSup_obj, Set.mem_iUnion]
        exact ⟨p.1, p.2, rfl⟩⟩ : (⨆ i, Subfunctor.range (ι i).hom).obj (op X)))
    rintro ⟨y, hy⟩
    rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hy
    obtain ⟨i, z, hz⟩ := hy
    exact ⟨⟨i, z⟩, Subtype.ext hz⟩
  intro T
  exact small_of_sieveOfSection_mem G.property _
    (fun X x => sieveOfSection_iSup_range_mem_ulift B S hS ι hG X x) hsmall T.unop

/-- **A coproduct of algebraic spaces over `S` indexed by a `u`-small type is pointwise
`u`-small**, for presheaves with values in `Type (max w u)`. The members are pointwise `u`-small
because they are algebraic spaces, so the union of their ranges is; and every section of the
coproduct lies in that union after restriction along a covering sieve. -/
theorem small_of_isColimit_cofan {I : Type v} [Small.{u} I]
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hFᵢ : ∀ i, IsAlgebraicSpaceULift.{w} B S hS (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) :
    FunctorToTypes.Small.{u} G.obj :=
  small_of_isColimit_cofan_aux B S hS
    (fun i => small_of_isAlgebraicSpaceULift B S hS (hFᵢ i)) ι hG

/-- **A coproduct of pointwise `u`-small sheaves over `S` indexed by a `u`-small type is
pointwise `u`-small**, for presheaves with values in `Type (max w u)`. The union of the ranges
of the legs is pointwise `u`-small, being the image of a dependent sum; and every section of
the coproduct lies in that union after restriction along a covering sieve.

Members which are algebraic spaces satisfy the hypothesis by
`AlgebraicGeometry.Space.small_of_isAlgebraicSpaceULift`, which is the form Stacks 02WQ uses
it in. -/
theorem small_of_isColimit_cofan' {I : Type v} [Small.{u} I]
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hFᵢ : ∀ i, FunctorToTypes.Small.{u} (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) :
    FunctorToTypes.Small.{u} G.obj :=
  small_of_isColimit_cofan_aux B S hS hFᵢ ι hG

/-! ### Descent of a coproduct cocone to the value universe of the site -/

/-- **A coproduct cocone of pointwise `u`-small sheaves on the big fppf site of `S`, with values
in `Type (max w u)` and indexed by a `u`-small type, is the universe lift of a coproduct cocone
of sheaves of `Type u`.** The isomorphisms `eF` and `eP` identify the lifts of the shrunk
sheaves with the given ones, and the last two clauses say that the legs correspond across them,
read in each direction.

This is the shared input of every statement about a coproduct of sheaves in a value universe
above the site's own which is proved by transport rather than rebuilt. The shrunk family is a
coproduct cocone by `CategoryTheory.Sheaf.isColimitCofanOfCompUliftFunctor` -- the category of
sheaves of `Type u` on this site is not known to have coproducts at all, the plus construction
being unavailable one universe below the objects of the site, so the universal property is
transported along the fully faithful lift rather than a coproduct being formed. Smallness of the
vertex comes from `AlgebraicGeometry.Space.small_of_isColimit_cofan`. -/
theorem exists_shrink_isColimit_cofan_of_small {I : Type v} [Small.{u} I]
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hFᵢ : ∀ i, FunctorToTypes.Small.{u} (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) :
    ∃ (F₀ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
      (G₀ : Sheaf (BigFppfOver.topology B S hS) (Type u)) (ι₀ : ∀ i, F₀ i ⟶ G₀)
      (eF : ∀ i, (F₀ i).obj ⋙ uliftFunctor.{w} ≅ (Fᵢ i).obj)
      (eG : G₀.obj ⋙ uliftFunctor.{w} ≅ G.obj),
      Nonempty (IsColimit (Cofan.mk G₀ ι₀)) ∧
      (∀ (i : I) (T : (BigFppfOver B S hS)ᵒᵖ) (z : (F₀ i).obj.obj T),
        (ι i).hom.app T ((eF i).hom.app T (ULift.up z))
          = eG.hom.app T (ULift.up ((ι₀ i).hom.app T z))) ∧
      (∀ (i : I) (T : (BigFppfOver B S hS)ᵒᵖ) (y : (Fᵢ i).obj.obj T),
        (ι₀ i).hom.app T ((eF i).inv.app T y).down
          = (eG.inv.app T ((ι i).hom.app T y)).down) := by
  classical
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let _ : ∀ i, FunctorToTypes.Small.{u} (Fᵢ i).obj := hFᵢ
  let _ : FunctorToTypes.Small.{u} G.obj := small_of_isColimit_cofan' B S hS hFᵢ ι hG
  let F' : I → (Cᵒᵖ ⥤ Type u) := fun i => FunctorToTypes.shrink.{u} (Fᵢ i).obj
  let G' : Cᵒᵖ ⥤ Type u := FunctorToTypes.shrink.{u} G.obj
  let eF : ∀ i, F' i ⋙ uliftFunctor.{w} ≅ (Fᵢ i).obj := fun i =>
    shrinkCompUliftFunctorIso (Fᵢ i).obj
  let eG : G' ⋙ uliftFunctor.{w} ≅ G.obj := shrinkCompUliftFunctorIso G.obj
  have hsheaf : ∀ (P : Cᵒᵖ ⥤ Type u) (Q : Sheaf J (Type (max w u))),
      (P ⋙ uliftFunctor.{w} ≅ Q.obj) → Presheaf.IsSheaf J P := fun P Q e => by
    have h1 : Presheaf.IsSheaf J (P ⋙ uliftFunctor.{w}) :=
      (Presheaf.isSheaf_of_iso_iff e).mpr Q.property
    simpa only [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff] using h1
  have hG'sheaf : Presheaf.IsSheaf J G' := hsheaf _ G eG
  have hF'sheaf : ∀ i, Presheaf.IsSheaf J (F' i) := fun i => hsheaf _ _ (eF i)
  let Gsh : Sheaf J (Type u) := ⟨G', hG'sheaf⟩
  let Fsh : I → Sheaf J (Type u) := fun i => ⟨F' i, hF'sheaf i⟩
  let ιsh : ∀ i, Fsh i ⟶ Gsh := fun i =>
    ObjectProperty.homMk (FunctorToTypes.shrinkMap.{u} (ι i).hom)
  have hcompat : ∀ (i : I) (T : Cᵒᵖ) (z : (Fsh i).obj.obj T),
      (ι i).hom.app T ((eF i).hom.app T (ULift.up z))
        = eG.hom.app T (ULift.up ((ιsh i).hom.app T z)) := by
    intro i T z
    show (ι i).hom.app T ((equivShrink ((Fᵢ i).obj.obj T)).symm z)
      = (equivShrink (G.obj.obj T)).symm
        ((equivShrink (G.obj.obj T))
          ((ι i).hom.app T ((equivShrink ((Fᵢ i).obj.obj T)).symm z)))
    rw [Equiv.symm_apply_apply]
  have hcompat' : ∀ (i : I) (T : Cᵒᵖ) (y : (Fᵢ i).obj.obj T),
      (ιsh i).hom.app T ((eF i).inv.app T y).down
        = (eG.inv.app T ((ι i).hom.app T y)).down := by
    intro i T y
    show (equivShrink (G.obj.obj T))
        ((ι i).hom.app T ((equivShrink ((Fᵢ i).obj.obj T)).symm
          ((equivShrink ((Fᵢ i).obj.obj T)) y)))
      = (equivShrink (G.obj.obj T)) ((ι i).hom.app T y)
    rw [Equiv.symm_apply_apply]
  exact ⟨Fsh, Gsh, ιsh, eF, eG,
    ⟨Sheaf.isColimitCofanOfCompUliftFunctor ιsh ι hG eF eG hcompat⟩, hcompat, hcompat'⟩

/-! ### Stacks 02WQ in an arbitrary value universe -/

/-- **Stacks 02WQ** for presheaves with values in a universe `max w u` independent of the
universe `u` of the schemes. A coproduct of algebraic spaces over `S`, indexed by a `u`-small
type and with values in `Type (max w u)`, is an algebraic space over `S`, provided the chosen
surjective étale scheme atlases of the members have a coproduct inside the big fppf site
over `S`.

The presheaves involved are pointwise `u`-small, so they are universe lifts of presheaves of
`Type u` and the algebraic-space condition transports along the lift; the universal property of
the coproduct transports along it too, by fullness, so no coproduct of sheaves of `Type u` is
formed. -/
@[stacks 02WQ "in an arbitrary value universe, for a `u`-small index type; the index is \
unrestricted in `AlgebraicGeometry.isAlgebraicSpace_coproduct`, which is the same statement in \
the value universe of the site"]
theorem isAlgebraicSpaceULift_coproduct {I : Type v} [Small.{u} I]
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hFᵢ : ∀ i, IsAlgebraicSpaceULift.{w} B S hS (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    (U : I → BigFppfOver B S hS)
    (a : ∀ i, (uliftYoneda.{w}).obj (U i) ⟶ (Fᵢ i).obj)
    (hsurj : ∀ i, (surjectiveOnSite B S hS).relative (uliftYoneda.{w}) (a i))
    (hetale : ∀ i, (etaleOnSite B S hS).relative (uliftYoneda.{w}) (a i))
    {V : BigFppfOver B S hS} {j : ∀ i, U i ⟶ V} (hV : IsColimit (Cofan.mk V j)) :
    IsAlgebraicSpaceULift.{w} B S hS G.obj := by
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max w u))).obj uliftFunctor.{w}
  obtain ⟨Fsh, Gsh, ιsh, eF, eG, ⟨hGcolim⟩, -, -⟩ :=
    exists_shrink_isColimit_cofan_of_small B S hS
      (fun i => small_of_isAlgebraicSpaceULift B S hS (hFᵢ i)) ι hG
  -- the algebraic-space condition descends to the value universe of the site
  have hF'alg : ∀ i, IsAlgebraicSpace B S hS (Fsh i).obj := fun i =>
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS (Fsh i).obj).mp
      (isAlgebraicSpaceULift_of_iso B S hS (eF i).symm (hFᵢ i))
  -- the atlases descend to the value universe of the site
  let a' : ∀ i, yoneda.obj (U i) ⟶ (Fsh i).obj := fun i => H.preimage (a i ≫ (eF i).inv)
  have hmapa' : ∀ i, H.map (a' i) = a i ≫ (eF i).inv := fun i => H.map_preimage _
  have key : ∀ (P : MorphismProperty C) (i : I), P.relative (uliftYoneda.{w}) (a i) →
      P.relative yoneda (a' i) := by
    intro P i hP
    refine (relative_comp_map_iff yoneda H P (a' i)).mp ?_
    rw [hmapa']
    exact MorphismProperty.RespectsIso.postcomp _ (eF i).inv _ hP
  -- Stacks 02WQ in the value universe of the site
  have hG'alg : IsAlgebraicSpace B S hS Gsh.obj :=
    isAlgebraicSpace_coproduct B S hS (fun i => (Fsh i).obj) hF'alg Gsh ιsh hGcolim U a'
      (fun i => key _ i (hsurj i)) (fun i => key _ i (hetale i)) V j hV
  exact isAlgebraicSpaceULift_of_iso B S hS eG
    ((isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Gsh.obj).mpr hG'alg)

/-- **Stacks 02WQ under a uniform size bound on the atlases**, for presheaves with values in
`Type (max w u)`. A coproduct of algebraic spaces over `S`, indexed by a type of the working
universe of cardinality at most an infinite cardinal `μ` below the site's cutoff and with
chosen atlases of size at most `μ`, is an algebraic space over `S`.

This is `AlgebraicGeometry.Space.isAlgebraicSpaceULift_coproduct` with the disjoint union of the
atlases inside the site replaced by the size bound which produces it, through
`AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_le`. It is the form in which the
affine opens of an object of the site supply the bound, `μ` being the size of that object. -/
theorem isAlgebraicSpaceULift_coproduct_of_size_le {I : Type u}
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hFᵢ : ∀ i, IsAlgebraicSpaceULift.{w} B S hS (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    (U : I → BigFppfOver B S hS)
    (a : ∀ i, (uliftYoneda.{w}).obj (U i) ⟶ (Fᵢ i).obj)
    (hsurj : ∀ i, (surjectiveOnSite B S hS).relative (uliftYoneda.{w}) (a i))
    (hetale : ∀ i, (etaleOnSite B S hS).relative (uliftYoneda.{w}) (a i))
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hI : #I ≤ μ)
    (hsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (U i)).size ≤ μ) :
    IsAlgebraicSpaceULift.{w} B S hS G.obj := by
  obtain ⟨V, j, ⟨hV⟩⟩ :=
    BigFppfOver.exists_isColimit_cofan_of_size_le B S hS U hℵ hμ hI hsize
  exact isAlgebraicSpaceULift_coproduct B S hS hFᵢ ι hG U a hsurj hetale hV

end AlgebraicGeometry.Space

end

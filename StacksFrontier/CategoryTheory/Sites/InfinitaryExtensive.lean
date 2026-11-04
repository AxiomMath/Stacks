module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Limits.VanKampenCoproducts

/-!
# Coproducts of sheaves of types are stable under pullback at any index type

Mathlib knows that a category of sheaves of types is `CategoryTheory.FinitaryExtensive`
(`CategoryTheory.SheafOfTypes.finitary_extensive`), which makes a *binary* sheaf coproduct
stable under pullback. This file removes the finiteness restriction: an arbitrary coproduct of
sheaves of types is a van Kampen colimit, so pulling it back along any morphism of sheaves
decomposes the source as a coproduct again.

This is the fact that lets a representable sheaf be split along an arbitrary coproduct of
subfunctors, which is what the algebraicity of a coproduct of algebraic spaces (Stacks 02WQ)
and the glueing of algebraic spaces along an open covering (Stacks 02WR) both need.

## Main definitions

* `CategoryTheory.Limits.Types.sigmaCofan` is the cofan of types whose vertex is the sigma
  type, together with `CategoryTheory.Limits.Types.isColimitSigmaCofan`.

## Main results

* `CategoryTheory.Limits.Types.nonempty_isColimit_iff` and
  `CategoryTheory.Limits.Types.nonempty_isColimit_iff_existsUnique` characterise the colimit
  cofans of types, and `CategoryTheory.Limits.Types.existsUnique_of_isPullback` together with
  its converse `CategoryTheory.Limits.Types.isPullback_of_existsUnique` do the same for
  pullback squares of types.
* `CategoryTheory.Limits.Types.isVanKampenColimit_of_isColimit_discrete`: a colimit cofan of
  types is van Kampen, at an arbitrary index type.
* `CategoryTheory.isVanKampenColimit_of_isColimit_discrete_presheaf`: the same for presheaves
  of types.
* `CategoryTheory.Sheaf.isVanKampenColimit_of_isColimit_discrete`: the same for sheaves of
  types.
* `CategoryTheory.Sheaf.nonempty_isColimit_cofanMk_of_isPullback` and
  `CategoryTheory.Sheaf.isColimitCofanMkPullback` are the forms the geometric applications
  use: if `G` is the coproduct of the `Fᵢ` and `t : A ⟶ G` is any morphism of sheaves, then
  `A` is the coproduct of the pullbacks `Fᵢ ×_G A`. The first takes the pullback squares as
  arguments, so it does not ask for pullbacks to exist in the sheaf category and does not
  commit the caller to a particular choice of them.
* `CategoryTheory.Sheaf.exists_isColimit_cofan_pullback_of_comp`: the base change of a morphism
  `a : G ⟶ X` out of a coproduct along any `t : A ⟶ X` is the coproduct of the base changes of
  the restrictions `ι i ≫ a`, compatibly with both projections. This is the form a morphism
  `∐ᵢ Zᵢ ⟶ X` given by its restrictions is base changed in.

## Implementation notes

The type-level step is element chasing, and both halves of it go through one characterisation
of a colimit cofan of types: a cofan is a colimit exactly when every element of the vertex is
the image of exactly one element of exactly one summand. Pullback squares of types are read on
elements the same way, through `CategoryTheory.Limits.PullbackCone.isLimitEquivBijective`.

Passing from types to presheaves is `CategoryTheory.isVanKampenColimit_of_evaluation`, and
passing from presheaves to sheaves is `CategoryTheory.IsVanKampenColimit.map_reflective`
applied to `CategoryTheory.sheafificationAdjunction`, exactly as Mathlib's
`CategoryTheory.finitaryExtensive_of_reflective` does in the binary case; the instances asked
for by that lemma are supplied by left exactness of sheafification.

The index type carries `Small.{w} I`, `w` being the universe of the values of the sheaves.
That is not an artefact: the proof compares the given cofan with the coproduct of the underlying
diagram of presheaves, and a coproduct of `Type w`-valued presheaves indexed by `I` lands in
`Type w` only when `I` is `w`-small. Nor can smallness be derived from the colimit hypothesis,
since a cofan of initial objects with initial vertex is a colimit cofan for an index type of
any size. A caller holding a larger index type must reindex along
`CategoryTheory.Discrete.equivalence (equivShrink I)` and use
`CategoryTheory.IsVanKampenColimit.whiskerEquivalence_iff`; that reindexing is done once, in
`CategoryTheory.Limits.Types.isVanKampenColimit_of_isColimit_discrete`, so every statement
below it asks only for `Small.{w} I`.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v' v u

namespace CategoryTheory.Limits.Types


section Cofan

variable {I : Type w} (X : I → Type w)

/-- The cofan of types whose vertex is the sigma type and whose legs are the inclusions. -/
def sigmaCofan : Cofan X :=
  Cofan.mk (Σ i, X i) fun i ↦ ↾fun x ↦ (⟨i, x⟩ : Σ i, X i)

/-- `CategoryTheory.Limits.Types.sigmaCofan` is a colimit cofan. -/
def isColimitSigmaCofan : IsColimit (sigmaCofan X) :=
  Cofan.IsColimit.mk _ (fun t ↦ ↾fun q ↦ t.inj q.1 q.2) (fun _ _ ↦ rfl) fun _ _ hm ↦
    ConcreteCategory.hom_ext _ _ fun ⟨i, x⟩ ↦ ConcreteCategory.congr_hom (hm i) x

/-- A cofan of types is a colimit exactly when the map out of the sigma type assembled from
its legs is a bijection. -/
theorem nonempty_isColimit_iff (c : Cofan X) :
    Nonempty (IsColimit c) ↔ Function.Bijective fun q : Σ i, X i ↦ c.inj q.1 q.2 :=
  ⟨fun ⟨hc⟩ ↦ ((isColimitSigmaCofan X).coconePointUniqueUpToIso hc).toEquiv.bijective,
    fun hbij ↦ ⟨IsColimit.ofIsoColimit (isColimitSigmaCofan X)
      (Cocone.ext (Equiv.ofBijective _ hbij).toIso fun _ ↦
        ConcreteCategory.hom_ext _ _ fun _ ↦ rfl)⟩⟩

/-- The element-level form of `CategoryTheory.Limits.Types.nonempty_isColimit_iff`: a cofan of
types is a colimit exactly when every element of the vertex is the image of exactly one
element of exactly one summand. -/
theorem nonempty_isColimit_iff_existsUnique (c : Cofan X) :
    Nonempty (IsColimit c) ↔ ∀ z : c.pt, ∃! q : Σ i, X i, c.inj q.1 q.2 = z :=
  (nonempty_isColimit_iff X c).trans (Function.bijective_iff_existsUnique _)

end Cofan

section Pullback

variable {P X Y Z : Type w}

/-- An element-level reading of a pullback square of types: a compatible pair of elements
lifts uniquely to the vertex. -/
theorem existsUnique_of_isPullback {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) {x : X} {y : Y} (hxy : f x = g y) :
    ∃! p : P, fst p = x ∧ snd p = y := by
  obtain ⟨hl⟩ := h.isLimit'
  obtain ⟨hinj, hsurj⟩ := (PullbackCone.isLimitEquivBijective _) hl
  obtain ⟨p, hp⟩ := hsurj ⟨⟨x, y⟩, hxy⟩
  rw [Subtype.ext_iff, Prod.ext_iff] at hp
  exact ⟨p, hp, fun p' hp' ↦ hinj
    (Subtype.ext (Prod.ext (hp'.1.trans hp.1.symm) (hp'.2.trans hp.2.symm)))⟩

/-- The converse of `CategoryTheory.Limits.Types.existsUnique_of_isPullback`: a commuting
square of types in which every compatible pair of elements lifts uniquely to the vertex is a
pullback square. -/
theorem isPullback_of_existsUnique (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hw : fst ≫ f = snd ≫ g)
    (h : ∀ (x : X) (y : Y), f x = g y → ∃! p : P, fst p = x ∧ snd p = y) :
    IsPullback fst snd f g := by
  refine IsPullback.of_isLimit ((PullbackCone.isLimitEquivBijective
    (PullbackCone.mk fst snd hw)).symm ((Function.bijective_iff_existsUnique _).2 fun q ↦ ?_))
  obtain ⟨p, hp, huniq⟩ := h q.1.1 q.1.2 q.2
  exact ⟨p, Subtype.ext (Prod.ext hp.1 hp.2), fun p' hp' ↦
    huniq p' (Prod.ext_iff.1 (Subtype.ext_iff.1 hp'))⟩

end Pullback

section VanKampen

private theorem isVanKampenColimit_of_isColimit_discrete_aux {I : Type w}
    {F : Discrete I ⥤ Type w} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  have hdisc : ∀ G : Discrete I ⥤ Type w, ∃ X : I → Type w, G = Discrete.functor X := fun G ↦
    ⟨G.obj ∘ Discrete.mk,
      Functor.hext (fun _ ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp)⟩
  obtain ⟨X, rfl⟩ := hdisc F
  have hcol := (nonempty_isColimit_iff_existsUnique X c).1 ⟨hc⟩
  intro F' c' α f hcomm _
  obtain ⟨X', rfl⟩ := hdisc F'
  have hsq : ∀ j, c'.ι.app j ≫ f = α.app j ≫ c.ι.app j := fun j ↦
    (NatTrans.congr_app hcomm j).symm
  have hcomm' : ∀ (i : I) (x : X' i),
      f (Cofan.inj c' i x) = Cofan.inj c i (α.app ⟨i⟩ x) := fun i x ↦
    ConcreteCategory.congr_hom (hsq ⟨i⟩) x
  refine ⟨fun hc' ⟨i⟩ ↦ ?_, fun hpb ↦ ?_⟩
  · refine isPullback_of_existsUnique _ _ _ _ (hsq ⟨i⟩) fun z y hzy ↦ ?_
    obtain ⟨⟨k, x⟩, hq, huniq⟩ := (nonempty_isColimit_iff_existsUnique X' c').1 hc' z
    obtain ⟨w, -, hu⟩ := hcol (Cofan.inj c i y)
    have hsig : (⟨k, α.app ⟨k⟩ x⟩ : Σ j, X j) = ⟨i, y⟩ :=
      (hu ⟨k, α.app ⟨k⟩ x⟩ (show Cofan.inj c k (α.app ⟨k⟩ x) = Cofan.inj c i y by
        rwa [← hcomm' k x, hq])).trans (hu ⟨i, y⟩ rfl).symm
    obtain rfl : k = i := congrArg Sigma.fst hsig
    exact ⟨x, ⟨hq, by simpa using hsig⟩, fun x' hx' ↦ by simpa using huniq ⟨k, x'⟩ hx'.1⟩
  · refine (nonempty_isColimit_iff_existsUnique X' c').2 fun z ↦ ?_
    obtain ⟨⟨i, y⟩, hq, huniq⟩ := hcol (f z)
    obtain ⟨x, ⟨hx1, -⟩, hxu⟩ := existsUnique_of_isPullback (hpb ⟨i⟩) hq.symm
    refine ⟨⟨i, x⟩, hx1, fun ⟨k, x'⟩ hq' ↦ ?_⟩
    have hsig : (⟨k, α.app ⟨k⟩ x'⟩ : Σ j, X j) = ⟨i, y⟩ :=
      huniq _ (show Cofan.inj c k (α.app ⟨k⟩ x') = f z by rw [← hcomm' k x', hq'])
    obtain rfl : k = i := congrArg Sigma.fst hsig
    simp [hxu x' ⟨hq', by simpa using hsig⟩]

/-- **An arbitrary colimit cofan of types is a van Kampen colimit.** Mathlib's
`CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts` gives this for a finite index
type; there is no finiteness hypothesis here, only the smallness that a coproduct of
`Type w`-valued objects needs in order to land in `Type w` again. -/
theorem isVanKampenColimit_of_isColimit_discrete {I : Type v'} [Small.{w} I]
    {F : Discrete I ⥤ Type w} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  refine (IsVanKampenColimit.whiskerEquivalence_iff
    (Discrete.equivalence (equivShrink.{w} I)).symm).mp ?_
  exact _root_.CategoryTheory.isVanKampenColimit_of_isColimit_discreteTypes
    ((IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence (equivShrink.{w} I)).symm) hc)

end VanKampen

end CategoryTheory.Limits.Types

namespace CategoryTheory

/-! ### Van Kampen descent for coproducts of presheaves and of sheaves -/

variable {C : Type u} [Category.{v} C]

/-- **An arbitrary colimit cofan of presheaves of types is a van Kampen colimit.** -/
theorem isVanKampenColimit_of_isColimit_discrete_presheaf {I : Type v'} [Small.{w} I]
    (F : Discrete I ⥤ C ⥤ Type w) (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c :=
  isVanKampenColimit_of_evaluation F c fun x ↦
    Types.isVanKampenColimit_of_isColimit_discrete
      (isColimitOfPreserves ((evaluation C (Type w)).obj x) hc)

/-- **An arbitrary colimit cofan of sheaves of types is a van Kampen colimit**, hence in
particular a universal one: it stays a colimit after pullback along any morphism of sheaves.
Mathlib's `CategoryTheory.SheafOfTypes.finitary_extensive` gives this for a binary coproduct;
there is no finiteness hypothesis here. -/
theorem Sheaf.isVanKampenColimit_of_isColimit_discrete (J : GrothendieckTopology C)
    [HasSheafify J (Type w)] {I : Type v'} [Small.{w} I] {F : Discrete I ⥤ Sheaf J (Type w)}
    {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  let adj := sheafificationAdjunction J (Type w)
  have : PreservesColimitsOfSize.{w, w} (presheafToSheaf J (Type w)) :=
    adj.leftAdjoint_preservesColimits
  refine (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor).hom).mp ?_
  refine ((isVanKampenColimit_of_isColimit_discrete_presheaf _ _
    (colimit.isColimit (F ⋙ sheafToPresheaf J (Type w)))).map_reflective adj).of_iso
    (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves (presheafToSheaf J (Type w)) (colimit.isColimit _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm hc

/-- **A family of pullback squares over a coproduct of sheaves of types exhibits the source as
a coproduct.** If `G` is the coproduct of the family `Fᵢ`, if `t : A ⟶ G` is any morphism of
sheaves, and if each `Aᵢ` sits in a pullback square over `t` and `ι i`, then `A` is the
coproduct of the `Aᵢ`. The squares are supplied, so no pullbacks need exist in the sheaf
category. -/
theorem Sheaf.nonempty_isColimit_cofanMk_of_isPullback (J : GrothendieckTopology C)
    [HasSheafify J (Type w)] {I : Type v'} [Small.{w} I] {Fᵢ : I → Sheaf J (Type w)}
    {G : Sheaf J (Type w)} (ι : ∀ i, Fᵢ i ⟶ G) (hcoprod : IsColimit (Cofan.mk G ι))
    {A : Sheaf J (Type w)} (t : A ⟶ G) {Aᵢ : I → Sheaf J (Type w)} (p : ∀ i, Aᵢ i ⟶ A)
    (q : ∀ i, Aᵢ i ⟶ Fᵢ i) (hpb : ∀ i, IsPullback (p i) (q i) t (ι i)) :
    Nonempty (IsColimit (Cofan.mk A p)) :=
  (Sheaf.isVanKampenColimit_of_isColimit_discrete J hcoprod).isUniversal (Cofan.mk A p)
    (Discrete.natTrans fun i ↦ q i.as) t
    (NatTrans.ext (funext fun ⟨i⟩ ↦ (hpb i).w.symm))
    (NatTrans.Equifibered.of_discrete _) fun j ↦ hpb j.as

/-- **Pulling back a coproduct of sheaves of types decomposes the source as a coproduct.** If
`G` is the coproduct of the family `Fᵢ` and `t : A ⟶ G` is any morphism of sheaves, then `A`
is the coproduct of the fibre products `Fᵢ ×_G A`. -/
noncomputable def Sheaf.isColimitCofanMkPullback (J : GrothendieckTopology C)
    [HasSheafify J (Type w)]
    {I : Type v'} [Small.{w} I] {Fᵢ : I → Sheaf J (Type w)} {G : Sheaf J (Type w)}
    (ι : ∀ i, Fᵢ i ⟶ G)
    (hcoprod : IsColimit (Cofan.mk G ι)) {A : Sheaf J (Type w)} (t : A ⟶ G) :
    IsColimit (Cofan.mk A fun i ↦ pullback.snd (ι i) t) :=
  (Sheaf.nonempty_isColimit_cofanMk_of_isPullback J ι hcoprod t _
    (fun i ↦ pullback.fst (ι i) t) fun i ↦ (IsPullback.of_hasPullback (ι i) t).flip).some

/-- **The base change of a morphism out of a coproduct of sheaves of types is the coproduct of
the base changes of its restrictions to the summands.** If `G` is the coproduct of the family
`Fᵢ` with legs `ι i`, if `a : G ⟶ X` is any morphism of sheaves and `t : A ⟶ X` is the morphism
one base changes along, then the comparison morphisms `A ×_X Fᵢ ⟶ A ×_X G` exhibit `A ×_X G` as
the coproduct of the `A ×_X Fᵢ`, and they commute with both projections.

This is the form taken by the base change of a morphism `∐ᵢ Zᵢ ⟶ X` presented by its
restrictions `g i : Zᵢ ⟶ X`, where `a` is `CategoryTheory.Limits.Sigma.desc g` and `ι i ≫ a` is
`g i`: the base change along a point of `X` decomposes as the coproduct of the base changes of
the `g i`, compatibly with the projection to the point. It is
`CategoryTheory.Sheaf.isColimitCofanMkPullback` read at `pullback.snd t a : A ×_X G ⟶ G` rather
than at a morphism into `G` given in advance, the comparison morphisms being produced by pasting
the two pullback squares over `X`. -/
theorem Sheaf.exists_isColimit_cofan_pullback_of_comp (J : GrothendieckTopology C)
    [HasSheafify J (Type w)] [HasPullbacks (Sheaf J (Type w))]
    {I : Type v'} [Small.{w} I] {Fᵢ : I → Sheaf J (Type w)} {G : Sheaf J (Type w)}
    (ι : ∀ i, Fᵢ i ⟶ G) (hcoprod : IsColimit (Cofan.mk G ι))
    {X A : Sheaf J (Type w)} (a : G ⟶ X) (t : A ⟶ X) :
    ∃ l : ∀ i, pullback t (ι i ≫ a) ⟶ pullback t a,
      (∀ i, l i ≫ pullback.fst t a = pullback.fst t (ι i ≫ a)) ∧
      (∀ i, l i ≫ pullback.snd t a = pullback.snd t (ι i ≫ a) ≫ ι i) ∧
      Nonempty (IsColimit (Cofan.mk (pullback t a) l)) := by
  have hA : IsPullback (pullback.fst t a) (pullback.snd t a) t a := IsPullback.of_hasPullback t a
  have hi : ∀ i, IsPullback (pullback.fst t (ι i ≫ a)) (pullback.snd t (ι i ≫ a)) t (ι i ≫ a) :=
    fun i => IsPullback.of_hasPullback t (ι i ≫ a)
  refine ⟨fun i => hA.lift (pullback.fst t (ι i ≫ a)) (pullback.snd t (ι i ≫ a) ≫ ι i)
      (by rw [Category.assoc, ← (hi i).w]), fun i => hA.lift_fst _ _ _,
    fun i => hA.lift_snd _ _ _,
    Sheaf.nonempty_isColimit_cofanMk_of_isPullback J ι hcoprod (pullback.snd t a) _
      (fun i => pullback.snd t (ι i ≫ a)) fun i => ?_⟩
  refine (IsPullback.of_bot ?_ (hA.lift_snd _ _ _).symm hA.flip).flip
  rw [hA.lift_fst]
  exact (hi i).flip

end CategoryTheory

end

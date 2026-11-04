module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSheafCriterion

/-!
# Zariski locality of the square conditions of the h sheaf criterion

The conditions of the h sheaf criterion Stacks 0EVI which concern almost blowup squares ask
that a presheaf turn a square of the site into a cartesian square of sets.  The proof of Stacks
0EVI begins by observing that this is a local condition on the base: if a presheaf is a sheaf
for the Zariski topology and the restriction of a square to the members of a Zariski covering
of its base has cartesian image, and so does its restriction to the members of Zariski coverings
of the pairwise intersections, then the image of the square itself is cartesian.

This file proves the first half of that observation — joint injectivity of the two restriction
maps of a square is local on the base — in the form the induction of Stacks 0EVI consumes: the
restricted squares are given by arbitrary morphisms making the obvious diagrams commute, rather
than as fibre products, so that the base changes supplied by Stacks 0EV7 can be used directly.

## Main definitions

* `AlgebraicGeometry.BigHOver.IsSeparatedSquare`: the two restriction maps of a square are
  jointly injective.

## Main results

* `AlgebraicGeometry.BigHOver.isSeparatedSquare_of_zariskiCover`: joint injectivity is local on
  the base for a sheaf for the Zariski topology.

## Implementation notes

Only commutativity of the two squares relating a restricted square to the original one is used,
so no fibre products are needed: a restriction of the square over a member `U` of the covering
is any pair of morphisms to `U` together with morphisms to the modification and to the centre
making the two squares over `U` commute.  Every base change of the square is of that form.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- The two restriction maps of a square of the big h category over `S` are jointly injective:
two sections over the base which agree over the modification and over the centre are equal.

This is the separatedness half of the requirement that the image of the square be cartesian. -/
public def IsSeparatedSquare {X X' Z : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) : Prop :=
  ∀ s t : F.obj (op X), F.map b.op s = F.map b.op t → F.map z.op s = F.map z.op t → s = t

/-- Restricting along the two sides of a commutative square gives the same result. -/
private theorem map_map_eq_of_comp_eq {A₁ A₂ A₃ A₄ : BigHOver B S hS} {g : A₁ ⟶ A₂} {h : A₂ ⟶ A₄}
    {g' : A₁ ⟶ A₃} {h' : A₃ ⟶ A₄} (w : g ≫ h = g' ≫ h') (x : F.obj (op A₄)) :
    F.map g.op (F.map h.op x) = F.map g'.op (F.map h'.op x) := by
  have hh := congrArg F.map (congrArg Quiver.Hom.op w)
  simp only [op_comp, Functor.map_comp] at hh
  exact ConcreteCategory.congr_hom hh x

/-- If a section over `W` restricts to the restriction of a section `s` over `Y` along a
pullback square, then it does so along every commutative square from `T`. -/
private theorem map_eq_of_isPullback {P Y W T X : BigHOver B S hS}
    {q : P ⟶ Y} {p : P ⟶ W} {g : Y ⟶ X} {f : W ⟶ X} (h : IsPullback q p g f)
    (u : T ⟶ Y) (v : T ⟶ W) (hk : u ≫ g = v ≫ f) (σ : F.obj (op W)) (s : F.obj (op Y))
    (hσ : F.map p.op σ = F.map q.op s) : F.map v.op σ = F.map u.op s := by
  have e : F.map (h.lift u v hk ≫ p).op σ = F.map (h.lift u v hk ≫ q).op s := by
    simp only [op_comp, Functor.map_comp, types_comp_apply, hσ]
  rwa [h.lift_snd, h.lift_fst] at e

/-- Two local sections that restrict to the restrictions of `s` along pullbacks of the covering
have equal restrictions to the pullback of `g` along the common composite. -/
private theorem map_snd_pullback_eq {P X Y A A' Pi Pj : BigHOver B S hS} {g : P ⟶ X}
    {fi : A ⟶ X} {fj : A' ⟶ X} (gi : Y ⟶ A) (gj : Y ⟶ A') (hg : gi ≫ fi = gj ≫ fj)
    {qi : Pi ⟶ P} {pi : Pi ⟶ A} {qj : Pj ⟶ P} {pj : Pj ⟶ A'}
    (hi : IsPullback qi pi g fi) (hj : IsPullback qj pj g fj)
    (σi : F.obj (op A)) (σj : F.obj (op A')) (s : F.obj (op P))
    (hσi : F.map pi.op σi = F.map qi.op s) (hσj : F.map pj.op σj = F.map qj.op s)
    [HasPullback g (gi ≫ fi)] :
    F.map (pullback.snd g (gi ≫ fi)).op (F.map gi.op σi) =
      F.map (pullback.snd g (gi ≫ fi)).op (F.map gj.op σj) := by
  have hc := pullback.condition (f := g) (g := gi ≫ fi)
  have h₁ := map_eq_of_isPullback B S hS F hi (pullback.fst g (gi ≫ fi))
    (pullback.snd g (gi ≫ fi) ≫ gi) (by rw [hc, Category.assoc]) σi s hσi
  have h₂ := map_eq_of_isPullback B S hS F hj (pullback.fst g (gi ≫ fi))
    (pullback.snd g (gi ≫ fi) ≫ gj)
    (hc.trans ((congrArg (pullback.snd g (gi ≫ fi) ≫ ·) hg).trans
      (Category.assoc _ _ _).symm)) σj s hσj
  simp only [op_comp, Functor.map_comp, types_comp_apply] at h₁ h₂
  exact h₁.trans h₂.symm

/-- **Joint injectivity of the restriction maps of a square is local on the base.** If a presheaf
on the big h category over `S` is a sheaf for the Zariski topology and the restriction of a
square to every member of a Zariski covering of its base has jointly injective restriction maps,
then so does the square itself.

A restriction of the square to a member `U` of the covering is recorded by a modification and a
centre over `U` together with morphisms to the modification and to the centre of the square
making the two squares over `U` commute; the base change of the square along `U ⟶ X` is of that
form. -/
public theorem isSeparatedSquare_of_zariskiCover
    (hzar : BigHOver.IsZariskiSheaf B S hS F)
    {X X' Z : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X)
    (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X))
    (X'i Zi : E.I₀ → BigHOver B S hS)
    (bi : ∀ i, X'i i ⟶ E.X i) (zi : ∀ i, Zi i ⟶ E.X i)
    (qb : ∀ i, X'i i ⟶ X') (qz : ∀ i, Zi i ⟶ Z)
    (hqb : ∀ i, bi i ≫ E.f i = qb i ≫ b) (hqz : ∀ i, zi i ≫ E.f i = qz i ≫ z)
    (hsep : ∀ i, IsSeparatedSquare B S hS F (bi i) (zi i)) :
    IsSeparatedSquare B S hS F b z := by
  intro s t hb hz
  refine (hzar X E hE).isSeparatedFor.ext ?_
  rintro Y f ⟨i⟩
  refine hsep i _ _ ?_ ?_
  · rw [map_map_eq_of_comp_eq B S hS F (hqb i), map_map_eq_of_comp_eq B S hS F (hqb i), hb]
  · rw [map_map_eq_of_comp_eq B S hS F (hqz i), map_map_eq_of_comp_eq B S hS F (hqz i), hz]

/-- **Cartesianness of the image of a square is local on the base.** If a presheaf on the big h
category over `S` is a sheaf for the Zariski topology, the restriction of a square to every
member of a Zariski covering of its base has cartesian image, and every base change of the pair
consisting of the modification and the centre has jointly injective restriction maps, then the
image of the square itself is cartesian.

The restricted squares are taken as data: their modification and centre are required to be fibre
products of the modification and the centre of the square — which every base change is — while
their exceptional corner is only required to commute with the one of the square.  The families
of modifications and of centres are themselves required to be Zariski coverings, which again
every base change of a Zariski covering is; this is what identifies the glued section over the
base on the modification and on the centre.

The universal separatedness hypothesis is the one the induction of Stacks 0EVI has available
from `AlgebraicGeometry.BigHOver.isSeparatedSquare_of_zariskiCover` together with the
cartesianness it is proving: it is needed over the objects appearing in the compatibility
condition for the covering, which are arbitrary. -/
public theorem isPullback_of_zariskiCover
    (hzar : BigHOver.IsZariskiSheaf B S hS F)
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (hsep : ∀ (W W' Wz : BigHOver B S hS) (w : W ⟶ X) (bw : W' ⟶ W) (zw : Wz ⟶ W)
      (qbw : W' ⟶ X') (qzw : Wz ⟶ Z), IsPullback qbw bw b w → IsPullback qzw zw z w →
      IsSeparatedSquare B S hS F bw zw)
    (C : PreZeroHypercover.{u + 1} X)
    (hC : (C.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X))
    (X'i Zi Ei : C.I₀ → BigHOver B S hS)
    (bi : ∀ i, X'i i ⟶ C.X i) (zi : ∀ i, Zi i ⟶ C.X i)
    (di : ∀ i, Ei i ⟶ X'i i) (ei : ∀ i, Ei i ⟶ Zi i)
    (qb : ∀ i, X'i i ⟶ X') (qz : ∀ i, Zi i ⟶ Z) (qe : ∀ i, Ei i ⟶ E)
    (hqb : ∀ i, IsPullback (qb i) (bi i) b (C.f i))
    (hqz : ∀ i, IsPullback (qz i) (zi i) z (C.f i))
    (hqd : ∀ i, di i ≫ qb i = qe i ≫ d) (hqe : ∀ i, ei i ≫ qz i = qe i ≫ e)
    (hCb : ((PreZeroHypercover.mk C.I₀ X'i qb).map
      (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X'))
    (hCz : ((PreZeroHypercover.mk C.I₀ Zi qz).map
      (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj Z))
    (hcart : ∀ i, IsPullback (F.map (zi i).op) (F.map (bi i).op)
      (F.map (ei i).op) (F.map (di i).op)) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map d.op) := by
  have : HasPullbacks B.Schemes := inferInstance
  have hsepi (i : C.I₀) : IsSeparatedSquare B S hS F (bi i) (zi i) := by
    intro s t hb hz
    exact ((Limits.Types.isPullback_iff _ _ _ _).1 (hcart i)).2.1 s t ⟨hz, hb⟩
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg F.map (congrArg Quiver.Hom.op hw)
    simpa only [op_comp, CategoryTheory.Functor.map_comp] using h
  · rintro s t ⟨hz, hb⟩
    exact isSeparatedSquare_of_zariskiCover B S hS F hzar b z C hC X'i Zi bi zi qb qz
      (fun i => (hqb i).w.symm) (fun i => (hqz i).w.symm) hsepi s t hb hz
  · intro t s' hed
    -- the local sections over the members of the covering
    have hlocal (i : C.I₀) : ∃ si : F.obj (op (C.X i)),
        F.map (zi i).op si = F.map (qz i).op t ∧
          F.map (bi i).op si = F.map (qb i).op s' := by
      have hagree : F.map (ei i).op (F.map (qz i).op t) =
          F.map (di i).op (F.map (qb i).op s') := by
        rw [map_map_eq_of_comp_eq B S hS F (hqe i), hed,
          map_map_eq_of_comp_eq B S hS F (hqd i).symm]
      obtain ⟨si, h₁, h₂⟩ := ((Limits.Types.isPullback_iff _ _ _ _).1 (hcart i)).2.2
        (F.map (qz i).op t) (F.map (qb i).op s') hagree
      exact ⟨si, h₁, h₂⟩
    choose si hsiz hsib using hlocal
    -- the local sections are compatible, by separatedness of the base change of the square
    have hcompat : Presieve.Arrows.Compatible F C.f si := by
      intro i j Y gi gj hgij
      refine hsep Y (Limits.pullback b (gi ≫ C.f i)) (Limits.pullback z (gi ≫ C.f i))
        (gi ≫ C.f i) (Limits.pullback.snd b (gi ≫ C.f i))
        (Limits.pullback.snd z (gi ≫ C.f i)) (Limits.pullback.fst b (gi ≫ C.f i))
        (Limits.pullback.fst z (gi ≫ C.f i)) (IsPullback.of_hasPullback _ _)
        (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
      · exact map_snd_pullback_eq B S hS F gi gj hgij (hqb i) (hqb j) _ _ s' (hsib i) (hsib j)
      · exact map_snd_pullback_eq B S hS F gi gj hgij (hqz i) (hqz j) _ _ t (hsiz i) (hsiz j)
    -- glue the local sections and check the two restrictions
    obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff F C.f).1 (hzar X C hC) si hcompat
    refine ⟨s, ?_, ?_⟩
    · refine (hzar Z (PreZeroHypercover.mk C.I₀ Zi qz) hCz).isSeparatedFor.ext ?_
      rintro Y f ⟨i⟩
      rw [map_map_eq_of_comp_eq B S hS F (hqz i).w, hs i, hsiz i]
    · refine (hzar X' (PreZeroHypercover.mk C.I₀ X'i qb) hCb).isSeparatedFor.ext ?_
      rintro Y f ⟨i⟩
      rw [map_map_eq_of_comp_eq B S hS F (hqb i).w, hs i, hsib i]

end BigHOver

end AlgebraicGeometry

end

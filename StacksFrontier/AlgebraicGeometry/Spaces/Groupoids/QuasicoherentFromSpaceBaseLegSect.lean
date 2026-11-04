module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseLegTransition

/-!
# The transition morphism of a kernel-pair groupoid, read on sections over a chart

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let `φ : U ⟶ X` be a morphism with
`R = U ×_X U` and `t`, `s` the two projections — the situation of Stacks 03M3.  A quasi-coherent
module `(ℱ, α)` on the groupoid, in the sense of Stacks 0441, reads a pair of morphisms
`a, b : P ⟶ U` with `a ≫ φ = b ≫ φ` as a morphism `a^*ℱ ⟶ b^*ℱ`, namely
`AlgebraicGeometry.Space.legTransition`.  When `a` and `b` are moreover étale, the inverse images
`a^*ℱ` and `b^*ℱ` are étale restriction by Stacks 03LW, so that morphism is a map from the group
of sections of `ℱ` over the chart `Y ≫ a` of `U` to its group of sections over the chart
`Y ≫ b`, for every chart `Y` of the test space `P`.  That reading is the subject of this file.

## Main definitions

* `AlgebraicGeometry.Space.transitionSect` reads an arbitrary morphism between two inverse
  images of a module along étale morphisms on sections over a chart.
* `AlgebraicGeometry.Space.legSectHom`: the reading of `AlgebraicGeometry.Space.legTransition`
  over a chart of the test space, as a morphism of the two groups of sections.
* `AlgebraicGeometry.Space.legSect`: that reading, on a section.

## Main results

* `AlgebraicGeometry.Space.transitionSect_id`, `AlgebraicGeometry.Space.transitionSect_comp`,
  `AlgebraicGeometry.Space.transitionSect_restrict` and
  `AlgebraicGeometry.Space.transitionSect_transitionReindex`: the calculus of the reading of an
  arbitrary such morphism — the identity, a composite, restriction along a morphism of charts,
  and **a reindexing along an étale morphism of test spaces, which is read over the induced
  chart.**
* `AlgebraicGeometry.Space.legSect_eq_etaleSect`: the reading of the transition morphism is that
  morphism read through the identification of Stacks 03LW on either side.
* `AlgebraicGeometry.Space.legSect_self`: **a pair of equal morphisms is read as the identity.**
* `AlgebraicGeometry.Space.legSect_of_eq`: a pair of morphisms which happen to be equal is read
  as the transport along the resulting equality of charts.
* `AlgebraicGeometry.Space.legSect_comp`: **the reading is multiplicative along a triple of
  morphisms.**
* `AlgebraicGeometry.Space.legSect_restrict`: **the reading is natural in the chart.**
* `AlgebraicGeometry.Space.legSect_comp_left`: **the reading is natural in the test space** — the
  reading of a pair precomposed with an étale morphism `q`, over a chart `Y`, is the reading of
  the pair itself over the chart of `P` that `q` induces.

## Implementation notes

Everything is stated on sections over a chart, never on the modules themselves: at the level of
modules the composite of two readings hits a kernel timeout (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentFromSpaceBaseLegTransition.lean`).

The calculus is carried out at an abstract morphism of inverse images,
`AlgebraicGeometry.Space.transitionSect`, and only then instantiated at
`AlgebraicGeometry.Space.legTransition`: at the concrete morphism, reconciling a section of an
inverse image with a section over the composite chart makes the elaborator unfold the
`CategoryTheory.eqToHom` factors of `AlgebraicGeometry.Space.legTransition`, and the reduction
does not terminate.

Naturality in the test space assumes
`AlgebraicGeometry.Space.QuasiCoherentDescent.EtaleRestrictionComp`, the compatibility of the
comparison of Stacks 03LU with étale restriction.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Abstract

variable {C D U V W : AlgebraicSpaces B S hS}

/-- Reading a section of an étale restriction back as a section of the inverse image commutes
with restriction along a morphism of charts. -/
private theorem etaleSectInv_restrict (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) {Y Y' : SmallEtale B S hS D.1} (c : Y' ⟶ Y)
    (s : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (.op Y)) :
    etaleSectInv B S hS g hg M Y'
        (M.val.map ((smallEtalePostcomp B S hS g hg).map c).op s) =
      ((modulePullback B S hS g).obj M).val.map c.op (etaleSectInv B S hS g hg M Y s) := by
  have h := etaleSect_restrict B S hS g hg M c (etaleSectInv B S hS g hg M Y s)
  rw [etaleSect_etaleSectInv] at h
  exact (congrArg (etaleSectInv B S hS g hg M Y') h).symm.trans
    (etaleSectInv_etaleSect B S hS g hg M Y' _)

/-- A reindexed transition morphism, read on sections over a chart: the three factors of
`AlgebraicGeometry.Space.transitionReindex` are applied in turn. -/
private theorem transitionReindex_val_app (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (f : W ⟶ V)
    (Y : SmallEtale B S hS W.1)
    (x : ((modulePullback B S hS (f ≫ a)).obj F).val.obj (.op Y)) :
    (transitionReindex B S hS F ψ f).val.app (.op Y) x =
      ((modulePullbackCompIso B S hS f b).hom.app F).val.app (.op Y)
        (((modulePullback B S hS f).map ψ).val.app (.op Y)
          (((modulePullbackCompIso B S hS f a).inv.app F).val.app (.op Y) x)) :=
  rfl

/-- **A morphism between two inverse images of a module along étale morphisms, read on sections
over a chart.**  A section of the module over the chart `Y ≫ a` is read back as a section of
`a^*ℱ` over `Y`, carried by the morphism, and read again as a section over the chart `Y ≫ b`. -/
def transitionSect (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (Y : SmallEtale B S hS V.1)
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    F.val.obj (.op ((smallEtalePostcomp B S hS b hb).obj Y)) :=
  etaleSect B S hS b hb F Y (ψ.val.app (.op Y) (etaleSectInv B S hS a ha F Y m))

/-- The reading of a morphism of inverse images is that morphism read through the identification
of Stacks 03LW on either side. -/
theorem transitionSect_eq (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (Y : SmallEtale B S hS V.1)
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    transitionSect B S hS F ψ ha hb Y m =
      etaleSect B S hS b hb F Y (ψ.val.app (.op Y) (etaleSectInv B S hS a ha F Y m)) :=
  rfl

/-- The identity of an inverse image is read as the identity on sections. -/
theorem transitionSect_id (F : Modules.{u, u} B S hS U.1 U.2) {a : V ⟶ U}
    (ha : IsEtale B S hS a.hom) (Y : SmallEtale B S hS V.1)
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    transitionSect B S hS F (𝟙 ((modulePullback B S hS a).obj F)) ha ha Y m = m :=
  etaleSect_etaleSectInv B S hS a ha F Y m

/-- A composite of two morphisms of inverse images is read as the composite of the two
readings. -/
theorem transitionSect_comp (F : Modules.{u, u} B S hS U.1 U.2) {a b c : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (χ : (modulePullback B S hS b).obj F ⟶ (modulePullback B S hS c).obj F)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hc : IsEtale B S hS c.hom)
    (Y : SmallEtale B S hS V.1)
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    transitionSect B S hS F χ hb hc Y (transitionSect B S hS F ψ ha hb Y m) =
      transitionSect B S hS F (ψ ≫ χ) ha hc Y m :=
  congrArg (fun y => etaleSect B S hS c hc F Y (χ.val.app (.op Y) y))
    (etaleSectInv_etaleSect B S hS b hb F Y
      (ψ.val.app (.op Y) (etaleSectInv B S hS a ha F Y m)))

/-- The reading of a morphism of inverse images is natural in the chart: restricting a section
along a morphism of charts and reading it is reading it and restricting the result. -/
theorem transitionSect_restrict (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    {Y Y' : SmallEtale B S hS V.1} (c : Y' ⟶ Y)
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    transitionSect B S hS F ψ ha hb Y'
        (F.val.map ((smallEtalePostcomp B S hS a ha).map c).op m) =
      F.val.map ((smallEtalePostcomp B S hS b hb).map c).op
        (transitionSect B S hS F ψ ha hb Y m) :=
  ((congrArg (fun y => etaleSect B S hS b hb F Y' (ψ.val.app (.op Y') y))
        (etaleSectInv_restrict B S hS a ha F c m)).trans
      (congrArg (etaleSect B S hS b hb F Y')
        (val_app_restrict B S hS ψ c (etaleSectInv B S hS a ha F Y m)))).trans
    (etaleSect_restrict B S hS b hb F c (ψ.val.app (.op Y) (etaleSectInv B S hS a ha F Y m)))

/-- **The reading of a morphism of inverse images is natural in the test space.**  Its
reindexing along an étale morphism `q` of test spaces, read over a chart `Y`, is the morphism
itself read over the chart that `q` induces, provided the comparisons of Stacks 03LU along `q`
followed by `a` and by `b` are compatible with étale restriction. -/
theorem transitionSect_transitionReindex (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (q : W ⟶ V)
    (hq : IsEtale B S hS q.hom) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hqa : IsEtale B S hS (q ≫ a).hom) (hqb : IsEtale B S hS (q ≫ b).hom)
    (hca : EtaleRestrictionComp B S hS q a hq ha hqa)
    (hcb : EtaleRestrictionComp B S hS q b hq hb hqb) (Y : SmallEtale B S hS W.1)
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS (q ≫ a) hqa).obj Y))) :
    transitionSect B S hS F (transitionReindex B S hS F ψ q) hqa hqb Y m =
      transitionSect B S hS F ψ ha hb ((smallEtalePostcomp B S hS q hq).obj Y) m := by
  have hB := transitionReindex_val_app B S hS F ψ q Y
    (etaleSectInv B S hS (q ≫ a) hqa F Y m)
  have hC := hcb.comp_app F Y
    (((modulePullback B S hS q).map ψ).val.app (.op Y)
      (((modulePullbackCompIso B S hS q a).inv.app F).val.app (.op Y)
        (etaleSectInv B S hS (q ≫ a) hqa F Y m)))
  have hD := etaleSect_map B S hS q hq ψ Y
    (((modulePullbackCompIso B S hS q a).inv.app F).val.app (.op Y)
      (etaleSectInv B S hS (q ≫ a) hqa F Y m))
  have key : etaleSect B S hS q hq ((modulePullback B S hS a).obj F) Y
      (((modulePullbackCompIso B S hS q a).inv.app F).val.app (.op Y)
        (etaleSectInv B S hS (q ≫ a) hqa F Y m)) =
      etaleSectInv B S hS a ha F ((smallEtalePostcomp B S hS q hq).obj Y) m := by
    have h := (etaleSect_comp_inv B S hS q a hq ha hqa hca F Y
        (etaleSectInv B S hS (q ≫ a) hqa F Y m)).trans
      (etaleSect_etaleSectInv B S hS (q ≫ a) hqa F Y m)
    exact (etaleSectInv_etaleSect B S hS a ha F
        ((smallEtalePostcomp B S hS q hq).obj Y) _).symm.trans
      (congrArg (etaleSectInv B S hS a ha F ((smallEtalePostcomp B S hS q hq).obj Y)) h)
  exact (((congrArg (etaleSect B S hS (q ≫ b) hqb F Y) hB).trans hC).trans
      (congrArg (etaleSect B S hS b hb F ((smallEtalePostcomp B S hS q hq).obj Y)) hD)).trans
    (congrArg (fun y => etaleSect B S hS b hb F ((smallEtalePostcomp B S hS q hq).obj Y)
        (ψ.val.app (.op ((smallEtalePostcomp B S hS q hq).obj Y)) y)) key)

end Abstract

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
  (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
  (Z : QuasicoherentModule B S hS G) {P Q : AlgebraicSpaces B S hS}

/-- **The transition morphism, read on sections over a chart of a test space.**  For a pair of
étale morphisms `a, b : P ⟶ U` with equal composites to `X`, the morphism
`AlgebraicGeometry.Space.legTransition` between the two inverse images of the underlying module
is, over a chart `Y` of `P`, a morphism from the sections of the module over the chart `Y ≫ a`
of `U` to its sections over the chart `Y ≫ b`. -/
def legSectHom (a b : P ⟶ G.objects) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hab : a ≫ φ = b ≫ φ) (Y : SmallEtale B S hS P.1) :
    Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y)) ⟶
      Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS b hb).obj Y)) :=
  ((modulePullbackIsoEtaleModulePullback B S hS a ha).inv.app Z.F.obj).val.app (.op Y) ≫
    (legTransition B S hS G φ hpb Z a b hab).val.app (.op Y) ≫
      ((modulePullbackIsoEtaleModulePullback B S hS b hb).hom.app Z.F.obj).val.app (.op Y)

/-- **The transition morphism, read on a section over a chart of a test space.**  It is
`AlgebraicGeometry.Space.transitionSect` at `AlgebraicGeometry.Space.legTransition`: the section
is read back as a section of the inverse image along `a`, carried by the transition morphism,
and read again as a section over the chart `Y ≫ b`. -/
def legSect (a b : P ⟶ G.objects) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hab : a ≫ φ = b ≫ φ) (Y : SmallEtale B S hS P.1)
    (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS b hb).obj Y)) :=
  transitionSect B S hS Z.F.obj (legTransition B S hS G φ hpb Z a b hab) ha hb Y m

/-- The reading of a section is the transition morphism read through the identification of
Stacks 03LW on either side. -/
theorem legSect_eq_etaleSect (a b : P ⟶ G.objects) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ) (Y : SmallEtale B S hS P.1)
    (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    legSect B S hS G φ hpb Z a b ha hb hab Y m =
      etaleSect B S hS b hb Z.F.obj Y
        ((legTransition B S hS G φ hpb Z a b hab).val.app (.op Y)
          (etaleSectInv B S hS a ha Z.F.obj Y m)) :=
  transitionSect_eq B S hS Z.F.obj (legTransition B S hS G φ hpb Z a b hab) ha hb Y m

/-- **A pair of equal morphisms is read as the identity on sections.** -/
theorem legSect_self (a : P ⟶ G.objects) (ha : IsEtale B S hS a.hom)
    (Y : SmallEtale B S hS P.1)
    (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    legSect B S hS G φ hpb Z a a ha ha rfl Y m = m :=
  (congrArg (fun ψ => transitionSect B S hS Z.F.obj ψ ha ha Y m)
      (legTransition_self B S hS G φ hpb Z a)).trans
    (transitionSect_id B S hS Z.F.obj ha Y m)

/-- A pair of morphisms which happen to be equal is read as the transport of sections along the
resulting equality of the two composite charts. -/
theorem legSect_of_eq {a b : P ⟶ G.objects} (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ) (e : a = b)
    (Y : SmallEtale B S hS P.1)
    (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    legSect B S hS G φ hpb Z a b ha hb hab Y m =
      eqToHom (congrArg (fun V : SmallEtale B S hS G.objects.1 =>
          Z.F.obj.val.presheaf.obj (.op V))
        (smallEtalePostcomp_obj_congr B S hS ha hb e Y)) m := by
  subst e
  exact legSect_self B S hS G φ hpb Z a ha Y m

/-- **The reading is multiplicative along a triple of morphisms**: reading along `a, b` and then
along `b, c` is reading along `a, c`. -/
theorem legSect_comp (a b c : P ⟶ G.objects) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hc : IsEtale B S hS c.hom) (hab : a ≫ φ = b ≫ φ)
    (hbc : b ≫ φ = c ≫ φ) (hac : a ≫ φ = c ≫ φ) (Y : SmallEtale B S hS P.1)
    (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    legSect B S hS G φ hpb Z b c hb hc hbc Y (legSect B S hS G φ hpb Z a b ha hb hab Y m) =
      legSect B S hS G φ hpb Z a c ha hc hac Y m :=
  (transitionSect_comp B S hS Z.F.obj (legTransition B S hS G φ hpb Z a b hab)
      (legTransition B S hS G φ hpb Z b c hbc) ha hb hc Y m).trans
    (congrArg (fun ψ => transitionSect B S hS Z.F.obj ψ ha hc Y m)
      (legTransition_comp B S hS G φ hpb Z a b c hab hbc hac))

/-- **The reading is natural in the chart**: restricting a section along a morphism of charts and
reading it is reading it and restricting the result. -/
theorem legSect_restrict (a b : P ⟶ G.objects) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ) {Y Y' : SmallEtale B S hS P.1}
    (c : Y' ⟶ Y) (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    legSect B S hS G φ hpb Z a b ha hb hab Y'
        (Z.F.obj.val.map ((smallEtalePostcomp B S hS a ha).map c).op m) =
      Z.F.obj.val.map ((smallEtalePostcomp B S hS b hb).map c).op
        (legSect B S hS G φ hpb Z a b ha hb hab Y m) :=
  transitionSect_restrict B S hS Z.F.obj (legTransition B S hS G φ hpb Z a b hab) ha hb c m

/-- **The reading is natural in the test space.**  For an étale morphism `q : Q ⟶ P` of test
spaces, the reading of the precomposed pair over a chart `Y` of `Q` is the reading of the
original pair over the chart of `P` that `q` induces, provided the comparisons of Stacks 03LU
along `q` followed by `a` and by `b` are compatible with étale restriction. -/
theorem legSect_comp_left (q : Q ⟶ P) (hq : IsEtale B S hS q.hom) (a b : P ⟶ G.objects)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ)
    (hqa : IsEtale B S hS (q ≫ a).hom) (hqb : IsEtale B S hS (q ≫ b).hom)
    (hab' : (q ≫ a) ≫ φ = (q ≫ b) ≫ φ)
    (hca : QuasiCoherentDescent.EtaleRestrictionComp B S hS q a hq ha hqa)
    (hcb : QuasiCoherentDescent.EtaleRestrictionComp B S hS q b hq hb hqb)
    (Y : SmallEtale B S hS Q.1)
    (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS (q ≫ a) hqa).obj Y))) :
    legSect B S hS G φ hpb Z (q ≫ a) (q ≫ b) hqa hqb hab' Y m =
      legSect B S hS G φ hpb Z a b ha hb hab ((smallEtalePostcomp B S hS q hq).obj Y) m :=
  (congrArg (fun ψ => transitionSect B S hS Z.F.obj ψ hqa hqb Y m)
      (transitionReindex_legTransition B S hS G φ hpb Z q a b hab hab').symm).trans
    (transitionSect_transitionReindex B S hS Z.F.obj
      (legTransition B S hS G φ hpb Z a b hab) q hq ha hb hqa hqb hca hcb Y m)

end AlgebraicGeometry.Space

end

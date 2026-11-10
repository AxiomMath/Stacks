module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityCoefficients
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale-local criterion for base change on small étale sites

Consider a cartesian square of schemes

```
X <--h-- Y
|f       |e
S <--g-- T
```

and an étale covering `{Uᵢ → X}` such that each `Uᵢ → S` factors as `Uᵢ → Vᵢ → S` with
`Vᵢ → S` étale.  Writing `Yᵢ = Uᵢ ×_X Y` and `Tᵢ = Vᵢ ×_S T`, the induced squares

```
Uᵢ <--hᵢ-- Yᵢ
|fᵢ        |eᵢ
Vᵢ <--gᵢ-- Tᵢ
```

are again cartesian.  This file carries out the argument of Stacks 0EZR for the base change map
of sheaves of sets: the restriction to `Uᵢ` of the base change map of the outer square is the
base change map of the `i`-th local square, up to the base change maps of the `i`-th upper and
lower squares, which are invertible because those squares are cartesian with both
inverse-image legs étale.  Since the `Uᵢ` cover `X`, invertibility over each `Uᵢ` gives
invertibility.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt_cube` — the compatibility of the two
  decompositions of the rectangle `Uᵢ ⟶ X ⟶ S`, at arbitrary coefficients.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isIso_local` — **Stacks 0EZR,
  part (1)**: the base change map of the outer square is invertible if the base change maps of
  the local squares are.

## Implementation notes

The comparison of the two decompositions is carried out on the *direct image* side, where the
base change map is a mate and every ingredient is computed on sections: the identity
`smallEtaleSquarePushforwardIsoAt_cube` between the two composites of square comparisons of
direct images reduces, through
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt_app`, to the corresponding identity
`Stacks.EtaleCohomology.siteSquare_cube` between composites of comparisons of base change
functors of sites, and that one to the uniqueness of a morphism into a fibre product.  The
passage from the identity of 2-squares to the invertibility statement is the formal
`Stacks.EtaleCohomology.isIso_map_mate_of_cube`.

Both the identity of site comparisons and the identity of direct image comparisons are stated
for the data of Stacks 0EZR, which is `Stacks.EtaleCohomology.EtaleLocalBaseChangeData`; the
direct image one is stated at arbitrary coefficients, since parts (2) and (3) of the source
need it for abelian sheaves.

Two statements the étale-local argument needs are deliberately *not* made at a section of a
sheaf, since asking the kernel to recognize two spellings of one such section makes it evaluate
the square comparisons on the fibre products of the small étale sites.  The cube identity is
turned into an identity of 2-squares already at arbitrary coefficients, by
`smallEtaleSquarePushforwardIsoAt_cube_twoSquare`; and the four base change maps the formal
`isIso_map_mate_of_cube_app` speaks of are handed to it as variables, identified with the mates
they stand for by equations between natural transformations.

## References

* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe w t u v z

namespace Stacks.EtaleCohomology

/-! ### The cube identity, on variables

The identity of 2-squares that `Stacks.EtaleCohomology.isIso_map_mate_of_cube` consumes is
equivalent, by `CategoryTheory.TwoSquare.ext`, to an identity between the two threefold
composites its sides have at an object.  Stated on variables in abstract categories, that
equivalence is cheap; at the sheaf categories of the small étale sites, unfolding the horizontal
composite and the two whiskerings inside the goal is not. -/

section CubeOnVariables

/-- **The cube identity from its components.**  For four 2-squares arranged as a cube and two
comparisons `r₁`, `r₂` of its two pairs of composite sides, the two ways around the cube agree as
soon as they agree at every object. -/
theorem twoSquare_cube_of_app {A B C D E F G H : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* E] [Category* F] [Category* G] [Category* H]
    {Re : B ⥤ A} {Rf : D ⥤ C} {Rq : F ⥤ B} {Ru : H ⥤ D}
    {Ra : E ⥤ A} {Rv : G ⥤ C} {Ri : F ⥤ E} {Rj : H ⥤ G}
    {g : A ⥤ C} {h : B ⥤ D} {gi : E ⥤ G} {hi : F ⥤ H}
    (s : TwoSquare Re h g Rf) (t : TwoSquare Rq hi h Ru)
    (s' : TwoSquare Ri hi gi Rj) (t' : TwoSquare Ra gi g Rv)
    (r₁ : Rq ⋙ Re ≅ Ri ⋙ Ra) (r₂ : Ru ⋙ Rf ≅ Rj ⋙ Rv)
    (hyp : ∀ P, s.app (Rq.obj P) ≫ Rf.map (t.app P) ≫ r₂.hom.app (hi.obj P) =
      g.map (r₁.hom.app P) ≫ t'.app (Ri.obj P) ≫ Rv.map (s'.app P)) :
    (t.hComp s).whiskerBottom r₂.hom = (s'.hComp t').whiskerTop r₁.hom := by
  apply NatTrans.ext
  funext P
  simpa [TwoSquare.hComp, TwoSquare.whiskerBottom, TwoSquare.whiskerTop] using hyp P

/-- **Three of the four mates of a cube are invertible, hence so is the image of the fourth**,
with every mate named by a variable.  This is
`Stacks.EtaleCohomology.isIso_map_mate_of_cube` restated so that a concrete instance can supply
its hypotheses and read off its conclusion without ever being asked to compare two spellings of
a mate *at an object*.

The four mates in play are the variables `ms`, `mt`, `mt'`, `ms'`, each identified with the mate
it stands for by an equation placed after the hypotheses that mention it.  An instance therefore
hands the invertibility statements over unchanged — the variable is determined by them — and
discharges the equations by `rfl`, where the two spellings are compared as natural
transformations and agree after unfolding a definition.  A hypothesis about a spelled-out mate
at an object is what must be avoided: there the comparison goes through the component of a
natural transformation, which the kernel answers by reducing the mate to the units and counits
of the concrete adjunctions, hence to the fibre products of the small étale sites.

For the same reason the cube identity is taken in the 2-square form
`twoSquare_cube_of_app` produces, not at an object. -/
theorem isIso_map_mate_of_cube_app {A B C D E F G H : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* E] [Category* F] [Category* G] [Category* H]
    {Le : A ⥤ B} {Re : B ⥤ A} {Lf : C ⥤ D} {Rf : D ⥤ C}
    {Lq : B ⥤ F} {Rq : F ⥤ B} {Lu : D ⥤ H} {Ru : H ⥤ D}
    {La : A ⥤ E} {Ra : E ⥤ A} {Lv : C ⥤ G} {Rv : G ⥤ C}
    {Li : E ⥤ F} {Ri : F ⥤ E} {Lj : G ⥤ H} {Rj : H ⥤ G}
    {g : A ⥤ C} {h : B ⥤ D} {gi : E ⥤ G} {hi : F ⥤ H}
    (s : TwoSquare Re h g Rf) (t : TwoSquare Rq hi h Ru)
    (s' : TwoSquare Ri hi gi Rj) (t' : TwoSquare Ra gi g Rv)
    (r₁ : Rq ⋙ Re ≅ Ri ⋙ Ra) (r₂ : Ru ⋙ Rf ≅ Rj ⋙ Rv)
    (hc : (t.hComp s).whiskerBottom r₂.hom = (s'.hComp t').whiskerTop r₁.hom)
    (ae : Le ⊣ Re) (af : Lf ⊣ Rf) (aq : Lq ⊣ Rq) (au : Lu ⊣ Ru)
    (aa : La ⊣ Ra) (av : Lv ⊣ Rv) (ai : Li ⊣ Ri) (aj : Lj ⊣ Rj)
    (X : A) (ms : TwoSquare g Le Lf h)
    (mt : TwoSquare h Lq Lu hi) (mt' : TwoSquare g La Lv gi) (ms' : TwoSquare gi Li Lj hi)
    (ht : ∀ P, IsIso (mt.app P))
    (ht' : ∀ P, IsIso (mt'.app P))
    (hs' : IsIso (ms'.app (La.obj X)))
    (hms : ms = (mateEquiv ae af).symm s)
    (hmt : mt = (mateEquiv aq au).symm t)
    (hmt' : mt' = (mateEquiv aa av).symm t')
    (hms' : ms' = (mateEquiv ai aj).symm s') :
    IsIso (Lu.map (ms.app X)) := by
  subst hms hmt hmt' hms'
  have := ht (Le.obj X)
  have := ht' X
  exact isIso_map_mate_of_cube ae af aq au aa av ai aj s t s' t' r₁ r₂ hc X

end CubeOnVariables

/-! ### The two decompositions of the rectangle, on sites -/

section SiteCube

variable (A : Type w) [Category.{t} A] {X S : Scheme.{u}}

/-- Base change of a morphism of sites, followed by a projection to the base and a further
morphism. -/
private lemma baseChange_map_projection {X S Z : Scheme.{u}} (f : X ⟶ S) {V W : S.Etale}
    (k : V ⟶ W)
    {p : W.left ⟶ Z} {q : V.left ⟶ Z} (hk : k.left ≫ p = q) :
    ((smallEtaleBaseChange f).map k).left ≫ (pullback.fst W.hom f ≫ p) =
      pullback.fst V.hom f ≫ q :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ p) (baseChange_map_left_fst f k)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun m => pullback.fst V.hom f ≫ m) hk)))

/-- Three morphisms over a common object compose to a morphism over it. -/
private lemma comp_three_projection {C : Type*} [Category* C] {A B D E Z : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    {pA : A ⟶ Z} {pB : B ⟶ Z} {pD : D ⟶ Z} {pE : E ⟶ Z}
    (ha : a ≫ pB = pA) (hb : b ≫ pD = pB) (hc : c ≫ pE = pD) :
    (a ≫ b ≫ c) ≫ pE = pA := by
  simp only [Category.assoc, hc, hb, ha]

/-- **The two decompositions of the rectangle `Uᵢ ⟶ X ⟶ S` agree, on sites.**  The comparison of
the two composite base change functors around the rectangle obtained by stacking the outer square
on the `i`-th upper square is the one obtained by stacking the `i`-th local square on the `i`-th
lower square, both read through the comparisons attached to the factorization `Uᵢ → Vᵢ → S` of
`Uᵢ → X → S` and to the compatibility of `eᵢ` with `e`.

Both sides are morphisms into the threefold fibre product `(V ×_S T) ×_T Y ×_Y Yᵢ`, and they
agree because they agree after each of its two projections: after the projection to `V` by the
three instances of `siteSquare_hom_fst`, and after the projection to `Yᵢ` because both are
morphisms of the small étale site of `Yᵢ`. -/
private theorem siteSquare_cube (D : EtaleLocalBaseChangeData.{u, z, t, w} A) (i : D.I)
    (V : D.S.Etale) :
    (smallEtaleBaseChange (D.h_i i)).map
        ((siteSquare (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm).hom.app V) ≫
      (siteSquare (D.toY_i i) (D.h_i i) D.h (D.u i)
        (D.upper_cartesian i).w.symm).hom.app ((smallEtaleBaseChange D.f).obj V) ≫
      (smallEtaleBaseChange (D.toY_i i)).map
        ((siteSquare D.e D.h D.g D.f D.cartesian.w.symm).hom.app V) =
    (siteSquare (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
        (D.local_cartesian i).w.symm).hom.app ((smallEtaleBaseChange (D.v i)).obj V) ≫
      (smallEtaleBaseChange (D.e_i i)).map
        ((siteSquare (D.toT_i i) (D.g_i i) D.g (D.v i)
          (D.lower_cartesian i).w.symm).hom.app V) ≫
      (siteSquare (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
        (D.e_i_compatible i).symm).hom.app ((smallEtaleBaseChange D.g).obj V) := by
  have ha := baseChange_map_projection (D.h_i i) _
    (siteSquare_hom_fst (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm V)
  have hb := (reassoc_of% (siteSquare_hom_fst (D.toY_i i) (D.h_i i) D.h (D.u i)
    (D.upper_cartesian i).w.symm ((smallEtaleBaseChange D.f).obj V))) (pullback.fst V.hom D.f)
  have hc := baseChange_map_projection (D.toY_i i) _
    (siteSquare_hom_fst D.e D.h D.g D.f D.cartesian.w.symm V)
  have hd := (reassoc_of% (siteSquare_hom_fst (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
    (D.local_cartesian i).w.symm ((smallEtaleBaseChange (D.v i)).obj V)))
    (pullback.fst V.hom (D.v i))
  have hx := baseChange_map_projection (D.e_i i) _
    (siteSquare_hom_fst (D.toT_i i) (D.g_i i) D.g (D.v i) (D.lower_cartesian i).w.symm V)
  have hy := (reassoc_of% (siteSquare_hom_fst (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
    (D.e_i_compatible i).symm ((smallEtaleBaseChange D.g).obj V))) (pullback.fst V.hom D.g)
  set a := (smallEtaleBaseChange (D.h_i i)).map
    ((siteSquare (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm).hom.app V)
  set b := (siteSquare (D.toY_i i) (D.h_i i) D.h (D.u i)
    (D.upper_cartesian i).w.symm).hom.app ((smallEtaleBaseChange D.f).obj V)
  set c := (smallEtaleBaseChange (D.toY_i i)).map
    ((siteSquare D.e D.h D.g D.f D.cartesian.w.symm).hom.app V)
  set d := (siteSquare (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
    (D.local_cartesian i).w.symm).hom.app ((smallEtaleBaseChange (D.v i)).obj V)
  set x := (smallEtaleBaseChange (D.e_i i)).map
    ((siteSquare (D.toT_i i) (D.g_i i) D.g (D.v i) (D.lower_cartesian i).w.symm).hom.app V)
  set y := (siteSquare (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
    (D.e_i_compatible i).symm).hom.app ((smallEtaleBaseChange D.g).obj V)
  apply MorphismProperty.Over.Hom.ext
  let q := (IsPullback.of_hasPullback (pullback.snd (pullback.snd V.hom D.g) D.e)
    (D.toY_i i)).paste_horiz
      ((IsPullback.of_hasPullback (pullback.snd V.hom D.g) D.e).paste_horiz
        (IsPullback.of_hasPullback V.hom D.g))
  apply q.hom_ext
  · exact (comp_three_projection a.left b.left c.left ha hb hc).trans
      (comp_three_projection d.left x.left y.left hd hx hy).symm
  · exact (comp_three_projection a.left b.left c.left (MorphismProperty.Over.w a)
      (MorphismProperty.Over.w b) (MorphismProperty.Over.w c)).trans
      (comp_three_projection d.left x.left y.left (MorphismProperty.Over.w d)
        (MorphismProperty.Over.w x) (MorphismProperty.Over.w y)).symm

end SiteCube

/-! ### The two decompositions of the rectangle, on direct images -/

section PushforwardCube

variable (A : Type w) [Category.{t} A]

/-- The direct image of a morphism of sheaves, on sections. -/
private lemma pushAt_map_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G : Sheaf (smallEtaleTopology X) A} (a : F ⟶ G) (V : Y.Etale) :
    ((smallEtalePushforwardAt f A).map a).hom.app (op V) =
      a.hom.app (op ((smallEtaleBaseChange f).obj V)) :=
  rfl

/-- The sections of a direct image, contravariantly. -/
private lemma pushAt_obj_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology X) A) {V W : Y.Etale} (a : V ⟶ W) :
    ((smallEtalePushforwardAt f A).obj F).obj.map a.op =
      F.obj.map ((smallEtaleBaseChange f).map a).op :=
  rfl

/-- The threefold composite of contravariant maps of a presheaf, compared along an identity of
the two composites of site morphisms.  The six factors are variables, which is what keeps the
comparison at a cost the kernel can pay. -/
private lemma comp₃_map_op_congr {B C : Type*} [Category* B] [Category* C] (G : Bᵒᵖ ⥤ C)
    {W X Y Z X' Y' : B} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (d : W ⟶ X') (e : X' ⟶ Y') (f : Y' ⟶ Z) (h : a ≫ b ≫ c = d ≫ e ≫ f)
    {p : G.obj (op Z) ⟶ G.obj (op Y)} {q : G.obj (op Y) ⟶ G.obj (op X)}
    {r : G.obj (op X) ⟶ G.obj (op W)} {p' : G.obj (op Z) ⟶ G.obj (op Y')}
    {q' : G.obj (op Y') ⟶ G.obj (op X')} {r' : G.obj (op X') ⟶ G.obj (op W)}
    (hp : p = G.map c.op) (hq : q = G.map b.op) (hr : r = G.map a.op)
    (hp' : p' = G.map f.op) (hq' : q' = G.map e.op) (hr' : r' = G.map d.op) :
    p ≫ q ≫ r = p' ≫ q' ≫ r' := by
  subst hp hq hr hp' hq' hr'
  rw [map_op_triple, map_op_triple, h]

/-! #### The six sectionwise factors of the cube

Each factor of the two sides of the cube is, on sections, a contravariant map of `F`.  The six
computations are instances of two declarations: assembled inline into the cube they hand the
kernel one proof term carrying six rewriting motives over sections of composites of three direct
images, and that is past the budget. -/

section CubeFactors

variable (D : EtaleLocalBaseChangeData.{u, z, t, w} A) (i : D.I)
  (F : Sheaf (smallEtaleTopology (D.Y_i i)) A) (V : D.S.Etale)

/-- The comparison of a square at the direct image of a sheaf, on sections. -/
private lemma square_pushAt_obj_app {Y T X S Z : Scheme.{u}} (k : Z ⟶ Y)
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (F : Sheaf (smallEtaleTopology Z) A) (V : S.Etale) :
    ((smallEtaleSquarePushforwardIsoAt e h g f w A).hom.app
        ((smallEtalePushforwardAt k A).obj F)).hom.app (op V) =
      F.obj.map ((smallEtaleBaseChange k).map ((siteSquare e h g f w).hom.app V)).op := by
  rw [smallEtaleSquarePushforwardIsoAt_app A e h g f w _ V, pushAt_obj_map A k F]

/-- The direct image of the comparison of a square, on sections. -/
private lemma square_pushAt_map_app {Y T X S R : Scheme.{u}} (k : S ⟶ R)
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (F : Sheaf (smallEtaleTopology Y) A) (V : R.Etale) :
    ((smallEtalePushforwardAt k A).map
        ((smallEtaleSquarePushforwardIsoAt e h g f w A).hom.app F)).hom.app (op V) =
      F.obj.map ((siteSquare e h g f w).hom.app ((smallEtaleBaseChange k).obj V)).op := by
  rw [pushAt_map_app A k _ V, smallEtaleSquarePushforwardIsoAt_app A e h g f w F _]

end CubeFactors


/-- The two threefold composites of the cube, on sections: the identity `siteSquare_cube` read
through the six sectionwise computations. -/
private lemma cube_component_app (D : EtaleLocalBaseChangeData.{u, z, t, w} A) (i : D.I)
    (F : Sheaf (smallEtaleTopology (D.Y_i i)) A) (V : D.S.Etale) :
    ((smallEtaleSquarePushforwardIsoAt D.e D.h D.g D.f D.cartesian.w.symm A).hom.app
          ((smallEtalePushforwardAt (D.toY_i i) A).obj F)).hom.app (op V) ≫
        ((smallEtalePushforwardAt D.f A).map
          ((smallEtaleSquarePushforwardIsoAt (D.toY_i i) (D.h_i i) D.h (D.u i)
            (D.upper_cartesian i).w.symm A).hom.app F)).hom.app (op V) ≫
        ((smallEtaleSquarePushforwardIsoAt (D.u i) (D.f_i i) D.f (D.v i)
          (D.factorization i).symm A).hom.app
            ((smallEtalePushforwardAt (D.h_i i) A).obj F)).hom.app (op V) =
      ((smallEtalePushforwardAt D.g A).map
          ((smallEtaleSquarePushforwardIsoAt (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
            (D.e_i_compatible i).symm A).hom.app F)).hom.app (op V) ≫
        ((smallEtaleSquarePushforwardIsoAt (D.toT_i i) (D.g_i i) D.g (D.v i)
          (D.lower_cartesian i).w.symm A).hom.app
            ((smallEtalePushforwardAt (D.e_i i) A).obj F)).hom.app (op V) ≫
        ((smallEtalePushforwardAt (D.v i) A).map
          ((smallEtaleSquarePushforwardIsoAt (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
            (D.local_cartesian i).w.symm A).hom.app F)).hom.app (op V) :=
  comp₃_map_op_congr F.obj _ _ _ _ _ _ (siteSquare_cube A D i V)
    (square_pushAt_obj_app A _ _ _ _ _ _ F V) (square_pushAt_map_app A _ _ _ _ _ _ F V)
    (square_pushAt_obj_app A _ _ _ _ _ _ F V) (square_pushAt_map_app A _ _ _ _ _ _ F V)
    (square_pushAt_obj_app A _ _ _ _ _ _ F V) (square_pushAt_map_app A _ _ _ _ _ _ F V)

/-- **The two decompositions of the rectangle `Uᵢ ⟶ X ⟶ S` agree, on direct images.**  The
comparison of the two composite direct images around the rectangle obtained by stacking the outer
square on the `i`-th upper square is the one obtained by stacking the `i`-th local square on the
`i`-th lower square, both read through the comparisons attached to the factorization `Uᵢ → Vᵢ → S`
of `Uᵢ → X → S` and to the compatibility of `eᵢ` with `e`.

This is the cube identity the étale-local argument runs on, in the form
`Stacks.EtaleCohomology.isIso_map_mate_of_cube_app` consumes: at a sheaf, where both sides are
threefold composites of comparisons of direct images.  On sections those composites are
contravariant maps of `F`, by the six sectionwise computations, and the identity between them
is `siteSquare_cube`. -/
theorem smallEtaleSquarePushforwardIsoAt_cube (D : EtaleLocalBaseChangeData.{u, z, t, w} A)
    (i : D.I)
    (F : Sheaf (smallEtaleTopology (D.Y_i i)) A) :
    (smallEtaleSquarePushforwardIsoAt D.e D.h D.g D.f D.cartesian.w.symm A).hom.app
          ((smallEtalePushforwardAt (D.toY_i i) A).obj F) ≫
        (smallEtalePushforwardAt D.f A).map
          ((smallEtaleSquarePushforwardIsoAt (D.toY_i i) (D.h_i i) D.h (D.u i)
            (D.upper_cartesian i).w.symm A).hom.app F) ≫
        (smallEtaleSquarePushforwardIsoAt (D.u i) (D.f_i i) D.f (D.v i)
          (D.factorization i).symm A).hom.app
            ((smallEtalePushforwardAt (D.h_i i) A).obj F) =
      (smallEtalePushforwardAt D.g A).map
          ((smallEtaleSquarePushforwardIsoAt (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
            (D.e_i_compatible i).symm A).hom.app F) ≫
        (smallEtaleSquarePushforwardIsoAt (D.toT_i i) (D.g_i i) D.g (D.v i)
          (D.lower_cartesian i).w.symm A).hom.app
            ((smallEtalePushforwardAt (D.e_i i) A).obj F) ≫
        (smallEtalePushforwardAt (D.v i) A).map
          ((smallEtaleSquarePushforwardIsoAt (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
            (D.local_cartesian i).w.symm A).hom.app F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  cases V with
  | op V => exact cube_component_app A D i F V

/-- **The cube identity of Stacks 0EZR as an identity of 2-squares.**  This is
`smallEtaleSquarePushforwardIsoAt_cube` read through `twoSquare_cube_of_app`: the two ways around
the cube, as 2-squares from `Uᵢ_étale` to `S_étale`, agree.

It is stated and proved here, at arbitrary coefficients `A`, rather than at the sheaves of sets
where it is used.  The passage from the identity at a sheaf to the identity of 2-squares matches
two spellings of one composite of sections — the one the formal lemma's variables produce and the
one the concrete comparisons produce — and with `A` a variable the two are reconciled by the
reduction of `CategoryTheory.Functor.comp` alone.  At `A = Type _` the same reconciliation
continues into the sheaves themselves, and from there into the fibre products of the small étale
sites, which is past the kernel's budget. -/
private lemma smallEtaleSquarePushforwardIsoAt_cube_twoSquare
    (D : EtaleLocalBaseChangeData.{u, z, t, w} A) (i : D.I) :
    TwoSquare.whiskerBottom
        (TwoSquare.hComp
          (smallEtaleSquarePushforwardIsoAt (D.toY_i i) (D.h_i i) D.h (D.u i)
            (D.upper_cartesian i).w.symm A).hom
          (smallEtaleSquarePushforwardIsoAt D.e D.h D.g D.f D.cartesian.w.symm A).hom)
        (smallEtaleSquarePushforwardIsoAt (D.u i) (D.f_i i) D.f (D.v i)
          (D.factorization i).symm A).hom =
      TwoSquare.whiskerTop
        (TwoSquare.hComp
          (smallEtaleSquarePushforwardIsoAt (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
            (D.local_cartesian i).w.symm A).hom
          (smallEtaleSquarePushforwardIsoAt (D.toT_i i) (D.g_i i) D.g (D.v i)
            (D.lower_cartesian i).w.symm A).hom)
        (smallEtaleSquarePushforwardIsoAt (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
          (D.e_i_compatible i).symm A).hom :=
  twoSquare_cube_of_app _ _ _ _
    (smallEtaleSquarePushforwardIsoAt (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
      (D.e_i_compatible i).symm A)
    (smallEtaleSquarePushforwardIsoAt (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm A)
    (smallEtaleSquarePushforwardIsoAt_cube A D i)

end PushforwardCube

/-! ### Stacks 0EZR, part (1): sheaves of sets -/

section OrdinaryLocal

variable (A : Type w) [Category.{t} A]

/-- Restriction along an étale morphism is left adjoint to the direct image, at arbitrary
coefficients: the adjunction induced on sheaves by the site-level adjunction
`AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeAdj`.  For sheaves of sets this is
`Stacks.EtaleCohomology.smallEtaleSetsRestrictionAdjunction`. -/
def smallEtaleRestrictionAdjunctionAt {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleRestrictionAt j A ⊣ smallEtalePushforwardAt j A :=
  (smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous (E := A)
    (smallEtaleTopology U) (smallEtaleTopology X)

/-- **The inverse-image/direct-image adjunction for sheaves of sets, with the direct image named
`Stacks.EtaleCohomology.smallEtalePushforwardAt`.**  This is
`Stacks.EtaleCohomology.smallEtaleSetsAdjunction`; only the name of its right adjoint differs,
`Stacks.EtaleCohomology.smallEtaleDirectImage` being the direct image at arbitrary coefficients
specialized to sheaves of sets.

The spelling matters for the application of `isIso_map_mate_of_cube_app` below.  The six
comparisons of direct images it is handed are stated with `smallEtalePushforwardAt`, and the
cube identity it consumes refers to the direct images through the *adjunctions*; with the two
names mixed, the identity the formal lemma asks for and the identity
`smallEtaleSquarePushforwardIsoAt_cube` proves are two spellings of one statement, and
reconciling them at a section of a sheaf makes the kernel evaluate the comparisons on the fibre
products of the small étale sites. -/
@[sga "4 VII 1.4" "partial", sga "4½ Arcata 2.3.3"]
def smallEtaleSetsAdjunctionAt {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleInverseImage.{u, v} f ⊣ smallEtalePushforwardAt f (Type (max (u + 1) v)) :=
  smallEtaleSetsAdjunction.{u, v} f

/-- **The members of the covering of Stacks 0EZR cover the final object of the small étale
site.**  The covering is an étale covering of `X` in the sense of
`AlgebraicGeometry.Scheme.etalePrecoverage`, that is, the images of its members cover the points
of `X`; that is exactly the condition for the sieve they generate on the final object of
`X_étale` to be covering. -/
theorem etaleCover_coversTop (D : EtaleLocalBaseChangeData.{u, z, t, w} A)
    (hEt : ∀ i, Etale (D.u i)) :
    D.X.smallEtaleTopology.CoversTop fun i => smallEtaleObj (D.u i) := by
  classical
  have (i : D.I) : Etale (D.u i) := hEt i
  let U : D.I → D.X.Etale := fun i => smallEtaleObj (D.u i)
  let top : D.X.Etale := smallEtaleObj (𝟙 D.X)
  have : IsIso top.hom := inferInstanceAs (IsIso (𝟙 D.X))
  let a : ∀ i, U i ⟶ top := fun i =>
    MorphismProperty.Over.homMk (D.u i) (Category.comp_id (D.u i)) trivial
  have htop : Sieve.ofArrows U a ∈ D.X.smallEtaleTopology top := by
    rw [ofArrows_mem_smallEtaleTopology_iff a]
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, y, rfl⟩ := ((Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp D.cover).1 x
    exact Set.mem_iUnion.2 ⟨i, Set.mem_range.2 ⟨y, rfl⟩⟩
  exact (D.X.smallEtaleTopology.coversTop_iff_of_isTerminal top (isTerminalOfIsIsoHom top) U).2
    (D.X.smallEtaleTopology.superset_covering (Sieve.ofArrows_le_ofObjects U a) htop)

/-- The base change map for sheaves of sets is the mate of the comparison of the two composite
direct images: this is its definition, read in the vocabulary of
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt`. -/
theorem smallEtaleSetsBaseChange_eq_mate {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f) :
    smallEtaleSetsBaseChange.{u, v} e h g f w =
      (mateEquiv (smallEtaleSetsAdjunction.{u, v} e)
        (smallEtaleSetsAdjunction.{u, v} f)).symm
          (smallEtaleSquarePushforwardIsoAt e h g f w (Type (max (u + 1) v))).hom :=
  rfl

/-- The per-member step of Stacks 0EZR, part (1): over a member `Uᵢ` of the covering, the
restriction of the base change map of the outer square is invertible, the base change map being
read as a mate along the adjunctions of `smallEtaleSetsAdjunctionAt`.

The two decompositions of the rectangle `Uᵢ ⟶ X ⟶ S` agree by
`smallEtaleSquarePushforwardIsoAt_cube_twoSquare`; the base change maps of the `i`-th upper and
lower squares are invertible by
`isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback`, those squares being cartesian with
both inverse-image legs étale; and the one of the `i`-th local square is the hypothesis.  The
passage from these three to the restriction of the fourth is the formal
`isIso_map_mate_of_cube_app`.

Every mate the formal lemma speaks of is handed to it as a variable, so the four `rfl`s at the
end are its only comparisons of two spellings of a mate, and they are comparisons of natural
transformations.  The adjunctions are supplied to
`isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback` explicitly rather than left to
unification, which is what makes the two variables standing for the upper and lower base change
maps determined by the invertibility statements themselves. -/
private lemma isIso_etaleRestrictionAt_map_mate
    (D : EtaleLocalBaseChangeData.{u, z, _, _} (Type (max (u + 1) v))) (i : D.I)
    [Etale (D.u i)]
    (hlocal : IsIso ((smallEtaleSetsBaseChange.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
      (D.local_cartesian i).w.symm).app ((smallEtaleInverseImage.{u, v} (D.toT_i i)).obj D.F))) :
    IsIso ((etaleRestrictionAt (D.u i) (Type (max (u + 1) v))).map
      (((mateEquiv (smallEtaleSetsAdjunctionAt.{u, v} D.e)
        (smallEtaleSetsAdjunctionAt.{u, v} D.f)).symm
          (smallEtaleSquarePushforwardIsoAt D.e D.h D.g D.f D.cartesian.w.symm
            (Type (max (u + 1) v))).hom).app D.F)) :=
  have : Etale (D.v i) := D.etale_v i
  have : Etale (D.toY_i i) := Etale.etale_of_isPullback_snd (D.upper_cartesian i)
  have : Etale (D.toT_i i) := Etale.etale_of_isPullback_snd (D.lower_cartesian i)
  isIso_map_mate_of_cube_app
    (smallEtaleSquarePushforwardIsoAt D.e D.h D.g D.f D.cartesian.w.symm
      (Type (max (u + 1) v))).hom
    (smallEtaleSquarePushforwardIsoAt (D.toY_i i) (D.h_i i) D.h (D.u i)
      (D.upper_cartesian i).w.symm (Type (max (u + 1) v))).hom
    (smallEtaleSquarePushforwardIsoAt (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
      (D.local_cartesian i).w.symm (Type (max (u + 1) v))).hom
    (smallEtaleSquarePushforwardIsoAt (D.toT_i i) (D.g_i i) D.g (D.v i)
      (D.lower_cartesian i).w.symm (Type (max (u + 1) v))).hom
    (smallEtaleSquarePushforwardIsoAt (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
      (D.e_i_compatible i).symm (Type (max (u + 1) v)))
    (smallEtaleSquarePushforwardIsoAt (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm
      (Type (max (u + 1) v)))
    (smallEtaleSquarePushforwardIsoAt_cube_twoSquare (Type (max (u + 1) v)) D i)
    (smallEtaleSetsAdjunctionAt.{u, v} D.e)
    (smallEtaleSetsAdjunctionAt.{u, v} D.f)
    (smallEtaleRestrictionAdjunctionAt (Type (max (u + 1) v)) (D.toY_i i))
    (smallEtaleRestrictionAdjunctionAt (Type (max (u + 1) v)) (D.u i))
    (smallEtaleSetsAdjunctionAt.{u, v} (D.toT_i i)) (smallEtaleSetsAdjunctionAt.{u, v} (D.v i))
    (smallEtaleSetsAdjunctionAt.{u, v} (D.e_i i)) (smallEtaleSetsAdjunctionAt.{u, v} (D.f_i i))
    D.F
    ((mateEquiv (smallEtaleSetsAdjunctionAt.{u, v} D.e)
      (smallEtaleSetsAdjunctionAt.{u, v} D.f)).symm
        (smallEtaleSquarePushforwardIsoAt D.e D.h D.g D.f D.cartesian.w.symm
          (Type (max (u + 1) v))).hom)
    _ _ _
    (fun P => isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback
      (Type (max (u + 1) v)) (D.toY_i i) (D.h_i i) D.h (D.u i)
      (D.upper_cartesian i).w.symm (D.upper_cartesian i).flip
      (smallEtaleRestrictionAdjunctionAt (Type (max (u + 1) v)) (D.toY_i i))
      (smallEtaleRestrictionAdjunctionAt (Type (max (u + 1) v)) (D.u i)) P)
    (fun P => isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback
      (Type (max (u + 1) v)) (D.toT_i i) (D.g_i i) D.g (D.v i)
      (D.lower_cartesian i).w.symm (D.lower_cartesian i).flip
      (smallEtaleSetsAdjunctionAt.{u, v} (D.toT_i i))
      (smallEtaleSetsAdjunctionAt.{u, v} (D.v i)) P)
    hlocal rfl rfl rfl rfl

/-- The per-member step, in the vocabulary of the base change map: the latter is by definition
the mate of `isIso_etaleRestrictionAt_map_mate`'s square comparison. -/
private lemma isIso_etaleRestrictionAt_map_smallEtaleSetsBaseChange
    (D : EtaleLocalBaseChangeData.{u, z, _, _} (Type (max (u + 1) v))) (i : D.I)
    [Etale (D.u i)]
    (hlocal : IsIso ((smallEtaleSetsBaseChange.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
      (D.local_cartesian i).w.symm).app ((smallEtaleInverseImage.{u, v} (D.toT_i i)).obj D.F))) :
    IsIso ((etaleRestrictionAt (D.u i) (Type (max (u + 1) v))).map
      ((smallEtaleSetsBaseChange.{u, v} D.e D.h D.g D.f D.cartesian.w.symm).app D.F)) := by
  rw [smallEtaleSetsBaseChange_eq_mate]
  exact isIso_etaleRestrictionAt_map_mate D i hlocal

/-- **Stacks 0EZR, part (1).**  Let

```
X <--h-- Y
|f       |e
S <--g-- T
```

be a cartesian square of schemes, let `{Uᵢ → X}` be an étale covering such that each `Uᵢ → S`
factors as `Uᵢ → Vᵢ → S` with `Vᵢ → S` étale, and let `F` be a sheaf of sets on the small étale
site of `T`.  If for every `i` the base change map
`fᵢ^{-1} g_{i,*} Fᵢ ⟶ h_{i,*} eᵢ^{-1} Fᵢ` of the `i`-th local square is an isomorphism, where
`Fᵢ = F|_{Vᵢ ×_S T}` is the inverse image of `F` along `Tᵢ ⟶ T`, then the base change map
`f^{-1} g_* F ⟶ h_* e^{-1} F` of the outer square is an isomorphism.

The argument is the source's: over each member of the covering the restriction of the outer base
change map is invertible by
`isIso_etaleRestrictionAt_map_smallEtaleSetsBaseChange`, and invertibility of a morphism of
sheaves on the small étale site is a local condition
(`Stacks.EtaleCohomology.isIso_of_isIso_etaleRestrictionAt`). -/
theorem isIso_smallEtaleSetsBaseChange_app_of_isIso_local
    (D : EtaleLocalBaseChangeData.{u, z, _, _} (Type (max (u + 1) v)))
    (hlocal : ∀ i, IsIso ((smallEtaleSetsBaseChange.{u, v} (D.e_i i) (D.h_i i) (D.g_i i)
      (D.f_i i) (D.local_cartesian i).w.symm).app
        ((smallEtaleInverseImage.{u, v} (D.toT_i i)).obj D.F))) :
    IsIso ((smallEtaleSetsBaseChange.{u, v} D.e D.h D.g D.f D.cartesian.w.symm).app D.F) := by
  have hEt : ∀ i, Etale (D.u i) := ((Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp D.cover).2
  have (i : D.I) : Etale (D.u i) := hEt i
  exact isIso_of_isIso_etaleRestrictionAt _ D.u
    (etaleCover_coversTop (Type (max (u + 1) v)) D hEt)
    fun i => isIso_etaleRestrictionAt_map_smallEtaleSetsBaseChange D i (hlocal i)

end OrdinaryLocal

end Stacks.EtaleCohomology

end

module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityCriterion
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeAffineLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
import all
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityRightSquareCube
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityCriterion

/-!
# Base change for pushforward over a separably closed field

Let `k` be a separably closed field and consider a cartesian square of schemes

```
X <--h-- Y
|f       |e
Spec k <--g-- T
```

with `g` quasi-compact and quasi-separated. This file proves that the canonical base change map
`f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf of sets `F` on the small étale site of
`T`, with no hypothesis on `X`: this is Tag 0EZY.

## The argument

Isomorphisms of sheaves of sets on the small étale site of `X` are detected on stalks at
geometric points (Tag 03PU). Fix a geometric point `x̄` of `X`, let `Z = Spec(O^{sh}_{X,x̄})` be
the strict henselization with its canonical morphism `ι : Z ⟶ X`, and `W = Y ×_X Z`. Since `x̄`
lifts to `Z` above its closed point, the stalk at `x̄` of a sheaf on `X` is the set of global
sections over `Z` of its inverse image along `ι`; so it suffices to show that `ι⁻¹` of the base
change map is bijective on global sections over `Z`. Stack the square of `ι` over the given
square:

```
Z <--- W
|ι     |
X <--- Y
|f     |e
Spec k <--g-- T
```

By the pasting law for mates (the cube of comparisons of composite direct images, with the
trivial factorization of `Z ⟶ X ⟶ Spec k` through `Spec k`), the base change map of the outer
rectangle is, up to isomorphisms, `ι⁻¹` of the base change map of the lower square followed by
the base change map of the upper square. Two of these are bijective on global sections over `Z`:

* the upper square: `h` is quasi-compact and quasi-separated, as a base change of `g`, so this
  is Tag 03Q9 for sheaves of sets in degree zero
  (`Stacks.EtaleCohomology.isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization`);
* the outer rectangle: `Z ⟶ Spec k` is flat (the base is a field), quasi-compact (both are
  affine), and geometrically connected, because `Z` is the spectrum of a local ring, hence
  connected, and over a separably closed field connected implies geometrically connected
  (Tag 0363). So Tag 0A3H applies to `Z ⟶ Spec k` and to its base change `W ⟶ T`, which is the
  first paragraph of the proof of Tag 0EZX at the final object of `Z_étale`
  (`Stacks.EtaleCohomology.local_baseChange_compatible`).

Hence the third, `Γ(Z, ι⁻¹ β)`, is bijective too.

## Relation to the source's proof

The source reduces to `X` affine (Tag 0EZR), writes `X` as a cofiltered limit of affine schemes
of finite type over `Spec k`, passes to the limit by Tag 0EZT and concludes by Tag 0EZX. The limit
passage is carried out here once and for all at the strict henselization: the limit argument is
the one inside Tag 03Q9 for sheaves of sets, and Tag 0EZX is applied to the local scheme
`Spec(O^{sh}_{X,x̄})` directly, where its covering condition is trivial. This is the argument of
Tag 0F00, specialized to `S = Spec k`.

## The hypothesis on `g`

Section 0EZW of the source, which contains Tag 0EZY, fixes at its start the convention that the
cartesian squares considered have `g` quasi-compact and quasi-separated, and Tag 0EZT, through
which the source's proof passes, assumes it. It cannot be dropped. Let `T = ∐_{n ∈ ℕ} Spec k`,
so that `g` is not quasi-compact, let `X = Spec(∏_{n ∈ ℕ} k)`, whose underlying space is the
Stone-Čech compactification `βℕ`, let `F` be the constant sheaf `{0, 1}` on `T`, and let `x` be a
free ultrafilter on `ℕ`. Then `Y = ∐_n X`, and the sections of `h_* e⁻¹ F` over an étale `U ⟶ X`
are the sequences of locally constant functions `U → {0, 1}`, while the stalk of `f⁻¹ g_* F` at
`x` is `F(T) = {0, 1}^ℕ`, mapping to the germs of constant sequences. Let `s_n` be the indicator
of the closure in `βℕ` of `{m : the n-th binary digit of m is 1}`. If the germ of `(s_n)` at `x`
were that of a constant sequence, then on some étale neighbourhood `U` of `x` every `s_n` would
be constant; the image of `U` is open and contains a clopen neighbourhood of `x`, on which every
`s_n` would then be constant, and such a neighbourhood meets `ℕ` in an infinite set (the
ultrafilter is free) whose members would share all their binary digits. So the base change map is
not surjective on stalks at `x`.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_of_quasiCompact`: for a
  cartesian square over `Spec k`, `k` separably closed, with `g` quasi-compact and
  quasi-separated, the base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf
  of sets `F` on the small étale site of `T`.

## Implementation notes

The pasting is done once, in general, by `isIso_map_inverseImage_smallEtaleSetBaseChange_of_cube`,
whose corners are all variables, and only then instantiated at the strict henselization. The
sheaf `G = e⁻¹F` on `Y` is an explicit argument of that lemma, tied to `F` by an equation the
caller closes by `rfl`: the lemma needs it in the spelling of the adjunction it pastes with, the
caller has it in the spelling of Tag 03Q9, and identifying the two spellings inside the statement
of an invertibility, instead of in that one equation, is a deterministic timeout.

## References

* [Stacks Project, Tag 0EZY](https://stacks.math.columbia.edu/tag/0EZY)
* [Stacks Project, Tag 0EZW](https://stacks.math.columbia.edu/tag/0EZW)
* [Stacks Project, Tag 0EZX](https://stacks.math.columbia.edu/tag/0EZX)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0F00](https://stacks.math.columbia.edu/tag/0F00)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
* [Stacks Project, Tag 0363](https://stacks.math.columbia.edu/tag/0363)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u v

namespace Stacks.EtaleCohomology

/-! ### Mates of a cube, after a functor -/

section Mates

/-- `isIso_mate_symm_iff`, after a functor: invertibility of the image under `Φ` of a component
of a mate is unchanged by replacing the two right adjoints by isomorphic ones, provided the two
2-squares correspond under those isomorphisms. -/
private lemma isIso_map_mate_symm_of
    {A B C D K : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* K]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁')
    (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂')
    {G : A ⥤ C} {H : B ⥤ D}
    (s : TwoSquare R₁ H G R₂) (s' : TwoSquare R₁' H G R₂')
    (r₁ : R₁ ≅ R₁') (r₂ : R₂ ≅ R₂')
    (hs : s.whiskerBottom r₂.hom = s'.whiskerTop r₁.hom) (Φ : D ⥤ K) (X : A)
    (h : IsIso (Φ.map (((mateEquiv a₁' a₂').symm s').app X))) :
    IsIso (Φ.map (((mateEquiv a₁ a₂).symm s).app X)) := by
  let l₁ := (conjugateIsoEquiv a₁ a₁').symm r₁
  let l₂ := (conjugateIsoEquiv a₂ a₂').symm r₂
  have hl₁ : conjugateEquiv a₁ a₁' l₁.hom = r₁.hom :=
    (conjugateEquiv a₁ a₁').apply_symm_apply _
  have hl₂ : conjugateEquiv a₂ a₂' l₂.hom = r₂.hom :=
    (conjugateEquiv a₂ a₂').apply_symm_apply _
  have he : ((mateEquiv a₁ a₂).symm s).whiskerRight l₂.hom =
      ((mateEquiv a₁' a₂').symm s').whiskerLeft l₁.hom := by
    apply (mateEquiv a₁ a₂').injective
    rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, hl₁, hl₂, hs]
  have hx := congrArg (fun t => t.app X) he
  change l₂.hom.app (G.obj X) ≫ _ = _ ≫ H.map (l₁.hom.app X) at hx
  have hx' := congrArg Φ.map hx
  rw [Φ.map_comp, Φ.map_comp] at hx'
  have : IsIso (Φ.map (l₂.hom.app (G.obj X)) ≫ Φ.map (((mateEquiv a₁ a₂).symm s).app X)) := by
    rw [hx']
    infer_instance
  exact IsIso.of_isIso_comp_left (Φ.map (l₂.hom.app (G.obj X))) _

/-- **`isIso_map_mate_of_cube`, after a functor.** Given eight adjunctions arranged as a cube and
the identity `hc` expressing that the two ways around it agree, invertibility under `Φ` of the
three mates `t`, `t'`, `s'` forces invertibility under `Φ` of the image under `Lu` of the mate
of `s`. -/
private lemma isIso_map_map_mate_of_cube
    {A B C D E F G H K : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* E] [Category* F] [Category* G] [Category* H] [Category* K]
    {Le : A ⥤ B} {Re : B ⥤ A} {Lf : C ⥤ D} {Rf : D ⥤ C}
    {Lq : B ⥤ F} {Rq : F ⥤ B} {Lu : D ⥤ H} {Ru : H ⥤ D}
    {La : A ⥤ E} {Ra : E ⥤ A} {Lv : C ⥤ G} {Rv : G ⥤ C}
    {Li : E ⥤ F} {Ri : F ⥤ E} {Lj : G ⥤ H} {Rj : H ⥤ G}
    (ae : Le ⊣ Re) (af : Lf ⊣ Rf) (aq : Lq ⊣ Rq) (au : Lu ⊣ Ru)
    (aa : La ⊣ Ra) (av : Lv ⊣ Rv) (ai : Li ⊣ Ri) (aj : Lj ⊣ Rj)
    {g : A ⥤ C} {h : B ⥤ D} {gi : E ⥤ G} {hi : F ⥤ H}
    (s : TwoSquare Re h g Rf) (t : TwoSquare Rq hi h Ru)
    (s' : TwoSquare Ri hi gi Rj) (t' : TwoSquare Ra gi g Rv)
    (r₁ : Rq ⋙ Re ≅ Ri ⋙ Ra) (r₂ : Ru ⋙ Rf ≅ Rj ⋙ Rv)
    (hc : (t.hComp s).whiskerBottom r₂.hom = (s'.hComp t').whiskerTop r₁.hom)
    (Φ : H ⥤ K) (X : A)
    (ht : IsIso (Φ.map (((mateEquiv aq au).symm t).app (Le.obj X))))
    (ht' : IsIso (Φ.map (Lj.map (((mateEquiv aa av).symm t').app X))))
    (hs' : IsIso (Φ.map (((mateEquiv ai aj).symm s').app (La.obj X)))) :
    IsIso (Φ.map (Lu.map (((mateEquiv ae af).symm s).app X))) := by
  have h₂ : IsIso (Φ.map (((mateEquiv (aa.comp ai) (av.comp aj)).symm (s'.hComp t')).app X)) := by
    rw [mate_symm_hcomp, TwoSquare.vComp_app]
    change IsIso (Φ.map (Lj.map (((mateEquiv aa av).symm t').app X) ≫
      ((mateEquiv ai aj).symm s').app (La.obj X)))
    rw [Φ.map_comp]
    infer_instance
  have h₁ := isIso_map_mate_symm_of (ae.comp aq) (aa.comp ai) (af.comp au)
    (av.comp aj) (t.hComp s) (s'.hComp t') r₁ r₂ hc Φ X h₂
  rw [mate_symm_hcomp, TwoSquare.vComp_app] at h₁
  change IsIso (Φ.map (Lu.map (((mateEquiv ae af).symm s).app X) ≫
    ((mateEquiv aq au).symm t).app (Le.obj X))) at h₁
  rw [Φ.map_comp] at h₁
  exact IsIso.of_isIso_comp_right _ (Φ.map (((mateEquiv aq au).symm t).app (Le.obj X)))

/-- A morphism inverted by `H` is inverted by `F` followed by `G` when `H ≅ F ⋙ G`, in the
spelling `G.map (F.map φ)`. -/
theorem isIso_map_map_of_isIso_map {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (α : H ≅ F ⋙ G) {A B : C} (φ : A ⟶ B)
    (h : IsIso (H.map φ)) : IsIso (G.map (F.map φ)) :=
  (NatIso.isIso_map_iff α φ).1 h

end Mates

/-! ### The cube of comparisons for a stacked square and a factorization -/

section Cube

variable {X Y S T U Yi V Ti : Scheme.{u}}
  (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
  (u : U ⟶ X) (hi : Yi ⟶ U) (toY : Yi ⟶ Y) (wu : toY ≫ h = hi ≫ u)
  (fi : U ⟶ V) (v : V ⟶ S) (wf : u ≫ f = fi ≫ v)
  (ei : Yi ⟶ Ti) (gi : Ti ⟶ V) (wl : ei ≫ gi = hi ≫ fi)
  (toT : Ti ⟶ T) (wt : toT ≫ g = gi ≫ v)
  (wc : toY ≫ e = ei ≫ toT)

/-- **The cube of site comparisons commutes**, for arbitrary commutative data: stacking the
square `(e, h, g, f)` on the square `(toY, hi, h, u)` gives the same rectangle `U ⟶ X ⟶ S` as
stacking the square `(ei, hi, gi, fi)` on the square `(toT, gi, g, v)`, because
`U ⟶ X ⟶ S` equals `U ⟶ V ⟶ S`. -/
private lemma siteSquare_cube_of_factorization (W : S.Etale) :
    (smallEtaleBaseChange hi).map ((siteSquare u fi f v wf).hom.app W) ≫
      (siteSquare toY hi h u wu).hom.app ((smallEtaleBaseChange f).obj W) ≫
      (smallEtaleBaseChange toY).map ((siteSquare e h g f w).hom.app W) =
    (siteSquare ei hi gi fi wl).hom.app ((smallEtaleBaseChange v).obj W) ≫
      (smallEtaleBaseChange ei).map ((siteSquare toT gi g v wt).hom.app W) ≫
      (siteSquare toY ei e toT wc).hom.app ((smallEtaleBaseChange g).obj W) := by
  let a := (smallEtaleBaseChange hi).map ((siteSquare u fi f v wf).hom.app W)
  let b := (siteSquare toY hi h u wu).hom.app ((smallEtaleBaseChange f).obj W)
  let c := (smallEtaleBaseChange toY).map ((siteSquare e h g f w).hom.app W)
  let d := (siteSquare ei hi gi fi wl).hom.app ((smallEtaleBaseChange v).obj W)
  let e' := (smallEtaleBaseChange ei).map ((siteSquare toT gi g v wt).hom.app W)
  let f' := (siteSquare toY ei e toT wc).hom.app ((smallEtaleBaseChange g).obj W)
  let lhs := a ≫ b ≫ c
  let rhs := d ≫ e' ≫ f'
  change lhs = rhs
  have ha := baseChange_map_projection hi _ (siteSquare_hom_fst u fi f v wf W)
  have hb := siteSquare_hom_fst_assoc toY hi h u wu ((smallEtaleBaseChange f).obj W)
    (pullback.fst W.hom f)
  have hc := baseChange_map_projection toY _ (siteSquare_hom_fst e h g f w W)
  have hd := siteSquare_hom_fst_assoc ei hi gi fi wl ((smallEtaleBaseChange v).obj W)
    (pullback.fst W.hom v)
  have he := baseChange_map_projection ei _ (siteSquare_hom_fst toT gi g v wt W)
  have hf := siteSquare_hom_fst_assoc toY ei e toT wc ((smallEtaleBaseChange g).obj W)
    (pullback.fst W.hom g)
  apply MorphismProperty.Over.Hom.ext
  refine ((IsPullback.of_hasPullback
    (pullback.snd (pullback.snd W.hom g) e) toY).paste_horiz
      ((IsPullback.of_hasPullback (pullback.snd W.hom g) e).paste_horiz
        (IsPullback.of_hasPullback W.hom g))).hom_ext ?_ ?_
  · have three : ∀ {A B D E Z : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
        {pA : A ⟶ Z} {pB : B ⟶ Z} {pD : D ⟶ Z} {pE : E ⟶ Z},
        a ≫ pB = pA → b ≫ pD = pB → c ≫ pE = pD → (a ≫ b ≫ c) ≫ pE = pA := by
      intro _ _ _ _ _ a b c _ _ _ _ ha hb hc
      simp only [Category.assoc, hc, hb, ha]
    exact (three _ _ _ ha hb hc).trans (three _ _ _ hd he hf).symm
  · exact (MorphismProperty.Over.w lhs).trans (MorphismProperty.Over.w rhs).symm

/-- **The cube of right-square comparisons commutes**, for arbitrary commutative data: the
horizontal composite of the comparisons of the squares `(toY, hi, h, u)` and `(e, h, g, f)`,
whiskered by that of `(u, fi, f, v)`, equals the horizontal composite of the comparisons of
`(ei, hi, gi, fi)` and `(toT, gi, g, v)`, whiskered by that of `(toY, ei, e, toT)`. -/
private lemma rightSquare_cube_of_factorization :
    (TwoSquare.hComp (rightSquare.{u, v} toY hi h u wu).hom
      (rightSquare.{u, v} e h g f w).hom).whiskerBottom
        (rightSquare.{u, v} u fi f v wf).hom =
    (TwoSquare.hComp (rightSquare.{u, v} ei hi gi fi wl).hom
      (rightSquare.{u, v} toT gi g v wt).hom).whiskerTop
          (rightSquare.{u, v} toY ei e toT wc).hom := by
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  cases W with
  | op W =>
    dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    rw [rightSquare_app e h g f w ((push.{u, v} toY).obj F) W]
    rw [push_map_app f ((rightSquare.{u, v} toY hi h u wu).hom.app F) W]
    rw [rightSquare_app toY hi h u wu F ((smallEtaleBaseChange f).obj W)]
    rw [rightSquare_app u fi f v wf ((push.{u, v} hi).obj F) W]
    rw [push_map_app g ((rightSquare.{u, v} toY ei e toT wc).hom.app F) W]
    rw [rightSquare_app toY ei e toT wc F ((smallEtaleBaseChange g).obj W)]
    rw [rightSquare_app toT gi g v wt ((push.{u, v} ei).obj F) W]
    rw [push_map_app v ((rightSquare.{u, v} ei hi gi fi wl).hom.app F) W]
    rw [rightSquare_app ei hi gi fi wl F ((smallEtaleBaseChange v).obj W)]
    rw [push_obj_map toY F ((siteSquare e h g f w).hom.app W)]
    rw [push_obj_map hi F ((siteSquare u fi f v wf).hom.app W)]
    rw [push_obj_map ei F ((siteSquare toT gi g v wt).hom.app W)]
    exact map_op_three_congr F.obj _ _ _ _ _ _
      (siteSquare_cube_of_factorization e h g f w u hi toY wu fi v wf ei gi wl toT wt wc W)

include wf wc in
/-- **The base change map pulled back along `u`, after a functor, from three others.** For the
stacked data of `rightSquare_cube_of_factorization`, if the base change maps of the square
`(toY, hi, h, u)` and of the square `(ei, hi, gi, fi)` become invertible after `Φ`, and the base
change map of the square `(toT, gi, g, v)` is invertible, then so is the image under `Φ` of the
inverse image along `u` of the base change map of the square `(e, h, g, f)`. Here `G` is the
inverse image of `F` on `Y`, as recorded by `hG`. -/
private lemma isIso_map_inverseImage_smallEtaleSetBaseChange_of_cube {K : Type*} [Category* K]
    (Φ : Sheaf (smallEtaleTopology U) (Type (max (u + 1) v)) ⥤ K)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v)))
    (hG : (invImage.{u, v} e).obj F = G)
    (ht : IsIso (Φ.map ((smallEtaleSetBaseChange.{u, v} toY hi h u wu).app G)))
    (ht' : IsIso ((smallEtaleSetsBaseChange.{u, v} toT gi g v wt).app F))
    (hs' : IsIso (Φ.map ((smallEtaleSetBaseChange.{u, v} ei hi gi fi wl).app
      ((smallEtaleInverseImage.{u, v} toT).obj F)))) :
    IsIso (Φ.map ((smallEtaleInverseImage.{u, v} u).map
      ((smallEtaleSetBaseChange.{u, v} e h g f w).app F))) := by
  subst hG
  rw [smallEtaleSetBaseChange_eq_smallEtaleSetsBaseChange.{v}] at ht hs' ⊢
  rw [smallEtaleSetsBaseChange_eq.{u, v}] at ht ht' hs' ⊢
  exact isIso_map_map_mate_of_cube (adj.{u, v} e) (adj.{u, v} f) (adj.{u, v} toY)
    (adj.{u, v} u) (adj.{u, v} toT) (adj.{u, v} v) (adj.{u, v} ei) (adj.{u, v} fi)
    (rightSquare.{u, v} e h g f w).hom (rightSquare.{u, v} toY hi h u wu).hom
    (rightSquare.{u, v} ei hi gi fi wl).hom (rightSquare.{u, v} toT gi g v wt).hom
    (rightSquare.{u, v} toY ei e toT wc) (rightSquare.{u, v} u fi f v wf)
    (rightSquare_cube_of_factorization.{u, v} e h g f w u hi toY wu fi v wf ei gi wl toT wt wc)
    Φ F ht inferInstance hs'

include wf wc in
/-- `isIso_map_inverseImage_smallEtaleSetBaseChange_of_cube_of_inverseImage` with the sheaf `G`
tied to `F` in the spelling of the adjunctions the cube identity pastes. -/
private lemma isIso_map_inverseImage_smallEtaleSetBaseChange_of_cube_of_inverseImage_aux
    {K : Type*} [Category* K] (Φ : Sheaf (smallEtaleTopology U) (Type (max (u + 1) v)) ⥤ K)
    (Ψ : Sheaf (smallEtaleTopology V) (Type (max (u + 1) v)) ⥤ K)
    (ε : Ψ ≅ smallEtaleInverseImage.{u, v} fi ⋙ Φ)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v)))
    (hG : (invImage.{u, v} e).obj F = G)
    (ht : IsIso (Φ.map ((smallEtaleSetBaseChange.{u, v} toY hi h u wu).app G)))
    (ht' : IsIso (Ψ.map ((smallEtaleSetBaseChange.{u, v} toT gi g v wt).app F)))
    (hs' : IsIso (Φ.map ((smallEtaleSetBaseChange.{u, v} ei hi gi fi wl).app
      ((smallEtaleInverseImage.{u, v} toT).obj F)))) :
    IsIso (Φ.map ((smallEtaleInverseImage.{u, v} u).map
      ((smallEtaleSetBaseChange.{u, v} e h g f w).app F))) := by
  subst hG
  rw [smallEtaleSetBaseChange_eq_smallEtaleSetsBaseChange.{v}] at ht ht' hs' ⊢
  rw [smallEtaleSetsBaseChange_eq.{u, v}] at ht ht' hs' ⊢
  exact isIso_map_map_mate_of_cube (adj.{u, v} e) (adj.{u, v} f) (adj.{u, v} toY)
    (adj.{u, v} u) (adj.{u, v} toT) (adj.{u, v} v) (adj.{u, v} ei) (adj.{u, v} fi)
    (rightSquare.{u, v} e h g f w).hom (rightSquare.{u, v} toY hi h u wu).hom
    (rightSquare.{u, v} ei hi gi fi wl).hom (rightSquare.{u, v} toT gi g v wt).hom
    (rightSquare.{u, v} toY ei e toT wc) (rightSquare.{u, v} u fi f v wf)
    (rightSquare_cube_of_factorization.{u, v} e h g f w u hi toY wu fi v wf ei gi wl toT wt wc)
    Φ F ht (isIso_map_map_of_isIso_map (invImage.{u, v} fi) Φ Ψ ε _ ht') hs'

include wf wc in
/-- **The base change map pulled back along `u`, after a functor, from three others, with the
square over `v` only invertible after inverse image.** For the stacked data of
`rightSquare_cube_of_factorization`, if the base change maps of the square `(toY, hi, h, u)` and
of the square `(ei, hi, gi, fi)` become invertible after `Φ`, and the base change map of the
square `(toT, gi, g, v)` becomes invertible after a functor `Ψ` with `Ψ ≅ fi⁻¹ ⋙ Φ`, then so does
the image under `Φ` of the inverse image along `u` of the base change map of the square
`(e, h, g, f)`. Here `G` is the inverse image of `F` on `Y`, as recorded by `hG`. -/
lemma isIso_map_inverseImage_smallEtaleSetBaseChange_of_cube_of_inverseImage {K : Type*}
    [Category* K] (Φ : Sheaf (smallEtaleTopology U) (Type (max (u + 1) v)) ⥤ K)
    (Ψ : Sheaf (smallEtaleTopology V) (Type (max (u + 1) v)) ⥤ K)
    (ε : Ψ ≅ smallEtaleInverseImage.{u, v} fi ⋙ Φ)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v)))
    (hG : (smallEtaleInverseImage.{u, v} e).obj F = G)
    (ht : IsIso (Φ.map ((smallEtaleSetBaseChange.{u, v} toY hi h u wu).app G)))
    (ht' : IsIso (Ψ.map ((smallEtaleSetBaseChange.{u, v} toT gi g v wt).app F)))
    (hs' : IsIso (Φ.map ((smallEtaleSetBaseChange.{u, v} ei hi gi fi wl).app
      ((smallEtaleInverseImage.{u, v} toT).obj F)))) :
    IsIso (Φ.map ((smallEtaleInverseImage.{u, v} u).map
      ((smallEtaleSetBaseChange.{u, v} e h g f w).app F))) :=
  isIso_map_inverseImage_smallEtaleSetBaseChange_of_cube_of_inverseImage_aux e h g f w u hi toY
    wu fi v wf ei gi wl toT wt wc Φ Ψ ε F G hG ht ht' hs'

end Cube

/-! ### Tag 0EZY -/

section SepClosedField

/-- The spectrum of a local ring is connected. -/
private lemma connectedSpace_primeSpectrum_of_isLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] : ConnectedSpace (PrimeSpectrum R) := by
  refine connectedSpace_iff_clopen.2 ⟨⟨IsLocalRing.closedPoint R⟩, fun s hs => ?_⟩
  by_cases hc : IsLocalRing.closedPoint R ∈ s
  · right
    have h := (IsLocalRing.closed_point_mem_iff (U := ⟨s, hs.isOpen⟩)).mp hc
    exact congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) =>
      (U : Set (PrimeSpectrum R))) h
  · left
    have h := (IsLocalRing.closed_point_mem_iff (U := ⟨sᶜ, hs.compl.isOpen⟩)).mp hc
    have h' := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) =>
      (U : Set (PrimeSpectrum R))) h
    simpa using h'

variable {X Y T : Scheme.{u}}

/-- A map of sheaves of sets on the small étale site which is bijective on sections over the final
object is invertible on global sections. -/
private lemma isIso_Γ_map_of_bijective_terminal {Z : Scheme.{u}}
    {P Q : Sheaf (smallEtaleTopology Z) (Type (u + 1))} (φ : P ⟶ Q)
    (hφ : Function.Bijective (φ.hom.app (op (Scheme.Etale.mk (𝟙 Z))))) :
    IsIso ((Sheaf.Γ (smallEtaleTopology Z) (Type (u + 1))).map φ) := by
  refine (NatIso.isIso_map_iff
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) (Type (u + 1))
      (isTerminalEtaleMkId Z)) φ).2 ?_
  exact (isIso_iff_bijective _).2 hφ

variable (k : Type u) [Field k] [IsSepClosed k] (B : BigEtaleSite.{u}) (hX : B.Contains X)
  (f : X ⟶ Spec (.of k)) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ Spec (.of k))

/-- The strict henselization of a scheme over a separably closed field at a geometric point is
geometrically connected over the field. -/
private lemma geometricallyConnected_strictHenselizationToBase_comp (x : GeometricPoint X) :
    GeometricallyConnected (strictHenselizationToBase B X hX x ≫ f) := by
  have : ConnectedSpace (strictHenselization B X hX x) :=
    connectedSpace_primeSpectrum_of_isLocalRing (etaleLocalRing B X hX x)
  exact (geometricallyConnected_iff_connectedSpace k _).2 inferInstance

/-- **A cartesian square whose left side is flat, quasi-compact and geometrically connected**:
its base change map is bijective on global sections. -/
private lemma isIso_Γ_smallEtaleSetBaseChange_of_geometricallyConnected {Z W S : Scheme.{u}}
    (fi : Z ⟶ S) (hi : W ⟶ Z) (ei : W ⟶ T) (g : T ⟶ S) (sq : IsPullback hi ei fi g)
    [Flat fi] [QuasiCompact fi] [GeometricallyConnected fi]
    (G : Sheaf (smallEtaleTopology T) (Type (u + 1))) :
    IsIso ((Sheaf.Γ (smallEtaleTopology Z) (Type (u + 1))).map
      ((smallEtaleSetBaseChange.{u, 0} ei hi g fi sq.w.symm).app G)) := by
  refine isIso_Γ_map_of_bijective_terminal _ ?_
  exact local_baseChange_compatible.{u, 0} fi hi ei g sq G
    ⟨Scheme.Etale.mk (𝟙 S), fi, (Category.comp_id _).trans (Category.id_comp _).symm,
      ‹Flat fi›, ‹QuasiCompact fi›, ‹GeometricallyConnected fi›⟩

/-- **The base change map is bijective on global sections over the strict henselization, after
inverse image to it.** Let `ι : Z = Spec(O^{sh}_{X,x̄}) ⟶ X` be the strict henselization at a
geometric point `x̄`. For a cartesian square over `Spec k`, `k` separably closed, with `g`
quasi-compact and quasi-separated, `ι⁻¹` of the base change map is bijective on global sections
over `Z`. -/
private theorem isIso_Γ_inverseImage_smallEtaleSetBaseChange (sq : IsPullback h e f g)
    [QuasiCompact g] [QuasiSeparated g] (F : Sheaf (smallEtaleTopology T) (Type (u + 1)))
    (x : GeometricPoint X) :
    IsIso ((Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) (Type (u + 1))).map
      ((smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B X hX x)).map
        ((smallEtaleSetBaseChange.{u, 0} e h g f sq.w.symm).app F))) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : GeometricallyConnected (strictHenselizationToBase B X hX x ≫ f) :=
    geometricallyConnected_strictHenselizationToBase_comp k B hX f x
  have wf : strictHenselizationToBase B X hX x ≫ f =
      (strictHenselizationToBase B X hX x ≫ f) ≫ 𝟙 (Spec (.of k)) := (Category.comp_id _).symm
  have sq' : IsPullback (pullback.snd h (strictHenselizationToBase B X hX x))
      (pullback.fst h (strictHenselizationToBase B X hX x) ≫ e)
      (strictHenselizationToBase B X hX x ≫ f) g :=
    (IsPullback.of_hasPullback h (strictHenselizationToBase B X hX x)).flip.paste_vert sq
  have wt : 𝟙 T ≫ g = g ≫ 𝟙 (Spec (.of k)) := (Category.id_comp _).trans (Category.comp_id _).symm
  have wc : pullback.fst h (strictHenselizationToBase B X hX x) ≫ e =
      (pullback.fst h (strictHenselizationToBase B X hX x) ≫ e) ≫ 𝟙 T :=
    (Category.comp_id _).symm
  have ht := isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization B X hX x h
    ((smallEtaleInverseImage.{u, 0} e).obj F)
  have hs' := isIso_Γ_smallEtaleSetBaseChange_of_geometricallyConnected
    (strictHenselizationToBase B X hX x ≫ f) (pullback.snd h (strictHenselizationToBase B X hX x))
    (pullback.fst h (strictHenselizationToBase B X hX x) ≫ e) g sq'
    ((smallEtaleInverseImage.{u, 0} (𝟙 T)).obj F)
  have ht' := baseChange_isIso_of_etale.{u, 0} (𝟙 T) g g (𝟙 (Spec (.of k))) wt
    IsPullback.of_id_fst F
  exact isIso_map_inverseImage_smallEtaleSetBaseChange_of_cube.{u, 0} e h g f sq.w.symm
    (strictHenselizationToBase B X hX x) (pullback.snd h (strictHenselizationToBase B X hX x))
    (pullback.fst h (strictHenselizationToBase B X hX x)) pullback.condition
    (strictHenselizationToBase B X hX x ≫ f) (𝟙 (Spec (.of k))) wf
    (pullback.fst h (strictHenselizationToBase B X hX x) ≫ e) g sq'.w.symm (𝟙 T) wt wc
    (Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) (Type (u + 1))) F
    ((smallEtaleInverseImage.{u, 0} e).obj F) rfl ht ht' hs'

/-- **The stalk at a geometric point is the global sections of the inverse image to the strict
henselization.** For a geometric point `x̄` of `X` with strict henselization
`ι : Spec(O^{sh}_{X,x̄}) ⟶ X`, the stalk functor at `x̄` on sheaves of sets is isomorphic to `ι⁻¹`
followed by global sections. -/
@[sga "4 VIII 4.8", sga "4 VIII 7.7"]
private def sheafFiberIsoInverseImageGammaStrictHenselization (x : GeometricPoint X) :
    (pointSmallEtale x.hom).sheafFiber (A := Type (u + 1)) ≅
      smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B X hX x) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) (Type (u + 1)) :=
  eqToIso (congrArg (fun y : Spec (.of x.residueField) ⟶ X =>
      (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
      (geometricPointToStrictHenselization_comp B X hX x).symm) ≪≫
    (smallEtaleInverseImageStalkIso.{0, u} (strictHenselizationToBase B X hX x)
      (geometricPointToStrictHenselization B X hX x)).symm ≪≫
    Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B X hX x))
      (sheafFiberClosedPointIsoGamma.{u, 0} (geometricPointToStrictHenselization B X hX x)
        (geometricPointToStrictHenselization_base_default B X hX x))

/-- **Stalks at a geometric point detect isomorphisms through the strict henselization.** A map
of sheaves of sets on the small étale site of `X` is bijective on stalks at a geometric point `x̄`
if and only if its inverse image to the strict henselization `Spec(O^{sh}_{X,x̄})` is bijective on
global sections. -/
theorem isIso_sheafFiber_map_iff_isIso_Γ_map_inverseImage_strictHenselization
    (x : GeometricPoint X) {P Q : Sheaf (smallEtaleTopology X) (Type (u + 1))} (φ : P ⟶ Q) :
    IsIso ((pointSmallEtale x.hom).sheafFiber.map φ) ↔
      IsIso ((Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) (Type (u + 1))).map
        ((smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B X hX x)).map φ)) :=
  NatIso.isIso_map_iff (sheafFiberIsoInverseImageGammaStrictHenselization B hX x) φ

omit hX in
/-- Let `k` be a separably closed field and consider a cartesian square of schemes

```
X <--h-- Y
|f       |e
Spec k <--g-- T
```

with `g` quasi-compact and quasi-separated. Then the canonical base change map
`f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf of sets `F` on the small étale site of
`T`. Nothing is assumed of `X`. -/
@[stacks 0EZY "the tag's statement for an arbitrary scheme `X` over the spectrum of a separably \
closed field, with nothing assumed of `X` and no result of the source assumed. The assumption \
that `g` be quasi-compact and quasi-separated is the standing convention of Section 0EZW, stated \
at its start for every cartesian diagram of the section, and the source's proof passes through \
Tag 0EZT, which assumes it; it cannot be dropped (see this file's module docstring for a \
counterexample with `g` not quasi-compact). The proof is the stalkwise one of Tag 0F00 \
specialized to `S = Spec k`: stalks at geometric points detect isomorphisms; the stalk at `x̄` is \
global sections over the strict henselization `Z = Spec(O^sh_{X,x̄})`; the pasting law for the \
base change maps of the square of `Z ⟶ X` stacked on the given square splits the base change map \
of the outer rectangle into `Γ(Z, ι⁻¹ β)` followed by the base change map of the square of \
`Z ⟶ X` over `h`; the latter is bijective on global sections by Tag 03Q9 for sheaves of sets \
(`isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization`, `h` being quasi-compact and \
quasi-separated as a base change of `g`), and the former composite is bijective by the first \
paragraph of Tag 0EZX (`local_baseChange_compatible`) at the final object of `Z_étale`, \
`Z ⟶ Spec k` being flat, quasi-compact and geometrically connected (Z is local, hence \
connected, and connected implies geometrically connected over a separably closed field, Tag \
0363). The source's reduction to `X` affine of finite type through Tags 0EZR and 0EZT is \
replaced by this: its limit argument is the one inside Tag 03Q9."]
theorem isIso_smallEtaleSetBaseChange_of_isSepClosed_of_quasiCompact
    (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) (Type (u + 1))) :
    IsIso ((smallEtaleSetBaseChange.{u, 0} e h g f sq.w.symm).app F) := by
  have := small_single.{u} X
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({X} : Set Scheme.{u})
  have hX : B.Contains X := hB X rfl
  refine isIso_of_geometricStalk_family.{0, u} (fun z : X ↦ (GeometricPoint.ofPoint X z).hom) ?_ _
    fun z ↦ ?_
  · refine Set.eq_univ_iff_forall.mpr fun z ↦ Set.mem_iUnion.mpr ⟨z, default, ?_⟩
    exact GeometricPoint.ofPoint_liesOver X z
  · exact (NatIso.isIso_map_iff
      (sheafFiberIsoInverseImageGammaStrictHenselization B hX (GeometricPoint.ofPoint X z)) _).2
      (isIso_Γ_inverseImage_smallEtaleSetBaseChange k B hX f h e g sq F
        (GeometricPoint.ofPoint X z))

end SepClosedField

end Stacks.EtaleCohomology

end

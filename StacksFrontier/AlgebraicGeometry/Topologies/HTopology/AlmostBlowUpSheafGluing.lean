module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCartesian

/-!
# Cartesianness of the image of a square is local on the base

Let `F` be a presheaf of sets on the big h category over a scheme `S` which is a sheaf for the
Zariski topology, and let

```
E ⟶ X'
↓    ↓ b
Z ⟶ X
```

be a cartesian square of the site. The proof of More on Flatness, Lemma 0EVI repeatedly uses that
whether `F` sends this square to a cartesian square of sets can be checked locally on `X`: if the
base changes of the square to the members of an affine open covering of `X`, and to the affine
opens of their pairwise overlaps, are sent to cartesian squares, then so is the square itself.
This file proves that statement, in the form in which it is used: the local squares range over
the base changes along a class of morphisms from affine objects which contains the members of an
affine open covering and is stable under precomposition with open immersions from affine objects.

## Main results

* `CategoryTheory.IsPullback.map_op_eq_map_op`: sections of a presheaf agreeing over the corner of
  a cartesian square agree along any commuting square over it.
* `AlgebraicGeometry.BigHOver.isPullback_map_of_isPullback_map_pullback`: the gluing statement.

## Implementation notes

The base change of the square along `g : V ⟶ X` is formed with the fibre products of the site:
its modification is `pullback.fst g b`, its centre `pullback.fst g z`, and its exceptional corner
the fibre product of these two, so that its cartesianness holds by construction. The amalgamation
step uses the sheaf condition for the covering in its pullback form,
`CategoryTheory.Presieve.isSheafFor_arrows_iff_pullbacks`, so that compatibility only has to be
checked on the overlaps of the covering, which are open in `X`; this is why the class of local
morphisms need only be stable under precomposition with open immersions.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.IsPullback

/-- Let `(e, p, z, b)` be a cartesian square in a category and let `F` be a presheaf of sets. A
section over `Z` and a section over `X'` with the same restriction to `E` have the same
restriction along any pair of morphisms completing `(z, b)` to a commuting square: both are
restrictions of their common restriction to `E`, along the morphism to `E` the square provides. -/
theorem map_op_eq_map_op {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type v)
    {X X' Z E V : C} {b : X' ⟶ X} {z : Z ⟶ X} {p : E ⟶ X'} {e : E ⟶ Z}
    (hsq : IsPullback e p z b) {t : F.obj (Opposite.op Z)} {s : F.obj (Opposite.op X')}
    (hc : F.map e.op t = F.map p.op s) {a : V ⟶ Z} {f : V ⟶ X'} (hcomm : a ≫ z = f ≫ b) :
    F.map a.op t = F.map f.op s := by
  have h₁ : hsq.lift a f hcomm ≫ e = a := hsq.lift_fst a f hcomm
  have h₂ : hsq.lift a f hcomm ≫ p = f := hsq.lift_snd a f hcomm
  calc F.map a.op t = F.map (hsq.lift a f hcomm ≫ e).op t := by rw [h₁]
    _ = F.map (hsq.lift a f hcomm ≫ p).op s := by
        rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hc]
    _ = F.map f.op s := by rw [h₂]

end CategoryTheory.IsPullback

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Squares of the site and their underlying squares of schemes -/

/-- The square of underlying schemes of a cartesian square of the site is cartesian. -/
theorem isPullback_toScheme_map {X₁ X₂ X₃ X₄ : BigHOver B S hS} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {d : X₃ ⟶ X₄} (h : IsPullback t l r d) :
    IsPullback ((BigHOver.toScheme B S hS).map t) ((BigHOver.toScheme B S hS).map l)
      ((BigHOver.toScheme B S hS).map r) ((BigHOver.toScheme B S hS).map d) :=
  h.map (BigHOver.toScheme B S hS)

/-- The underlying morphism of schemes of the first projection of a fibre product of the site
along an open immersion is an open immersion. -/
theorem isOpenImmersion_toScheme_map_pullback_fst {X Y Z : BigHOver B S hS} (f : Y ⟶ X)
    (g : Z ⟶ X) [IsOpenImmersion ((BigHOver.toScheme B S hS).map g)] :
    IsOpenImmersion ((BigHOver.toScheme B S hS).map (pullback.fst f g)) := by
  have hiso : IsIso (pullbackComparison (BigHOver.toScheme B S hS) f g) := inferInstance
  rw [← pullbackComparison_comp_fst (BigHOver.toScheme B S hS) f g]
  infer_instance

/-! ### Gluing cartesianness -/

variable {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}

/-- A section over the base of a base changed square whose restrictions to the two corners are
restrictions of given sections over `Z` and over `X'` restricts, along any morphism through which
the base change factors via `z` (resp. via `b`), to the corresponding restriction of the given
section. -/
theorem map_op_eq_of_map_fst_eq {X Y V T : BigHOver B S hS} {y : Y ⟶ X}
    (g : V ⟶ X) {w : F.obj (op V)} {t : F.obj (op Y)}
    (hw : F.map (pullback.fst g y).op w = F.map (pullback.snd g y).op t)
    (m : T ⟶ V) (a : T ⟶ Y) (hm : m ≫ g = a ≫ y) :
    F.map m.op w = F.map a.op t :=
  (IsPullback.of_hasPullback g y).map_op_eq_map_op F hw hm

/-- **Injectivity, locally.** Let `h : W ⟶ X` be a morphism of the site and let `W` be covered by
affine opens along each of which, composed with `h`, the image under `F` of the base change of
`(z, b)` is cartesian. Then two sections over `W` which agree after restriction along every
morphism through which `h` factors via `z` or via `b` are equal. -/
theorem eq_of_isPullback_map_pullback (hZ : IsZariskiSheaf B S hS F)
    {X X' Z : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X)
    {W : BigHOver B S hS} (h : W ⟶ X)
    (U : ((BigHOver.toScheme B S hS).obj W).OpenCover.{u + 1})
    (g : ∀ i, (preZeroHypercoverOfOpenCover U).X i ⟶ X)
    (hg : ∀ i, (preZeroHypercoverOfOpenCover U).f i ≫ h = g i)
    (hU : ∀ i, IsPullback (F.map (pullback.fst (g i) z).op) (F.map (pullback.fst (g i) b).op)
      (F.map (pullback.fst (pullback.fst (g i) z) (pullback.fst (g i) b)).op)
      (F.map (pullback.snd (pullback.fst (g i) z) (pullback.fst (g i) b)).op))
    {x y : F.obj (op W)}
    (hz : ∀ {T : BigHOver B S hS} (t : T ⟶ W) (a : T ⟶ Z), t ≫ h = a ≫ z →
      F.map t.op x = F.map t.op y)
    (hb : ∀ {T : BigHOver B S hS} (t : T ⟶ W) (a : T ⟶ X'), t ≫ h = a ≫ b →
      F.map t.op x = F.map t.op y) :
    x = y := by
  apply (preZeroHypercoverOfOpenCover_isSheafFor hZ W U).isSeparatedFor.ext
  rintro V f ⟨i⟩
  refine Types.ext_of_isPullback (hU i) ?_ ?_
  · simp only [← Functor.map_comp_apply, ← op_comp]
    exact hz _ (pullback.snd _ z) (by rw [Category.assoc, hg]; exact pullback.condition)
  · simp only [← Functor.map_comp_apply, ← op_comp]
    exact hb _ (pullback.snd _ b) (by rw [Category.assoc, hg]; exact pullback.condition)

/-- An affine open cover of the underlying scheme of an object of the site, indexed in the
universe of the families of the site. -/
noncomputable abbrev affineCover (W : BigHOver B S hS) :
    ((BigHOver.toScheme B S hS).obj W).OpenCover.{u + 1} :=
  (Scheme.affineOpenCover.{u} ((BigHOver.toScheme B S hS).obj W)).openCover.reindex
    (Equiv.ulift.{u + 1, u})

/-- The members of `AlgebraicGeometry.BigHOver.affineCover` are affine. -/
theorem isAffine_affineCover (W : BigHOver B S hS) (i : (affineCover W).I₀) :
    IsAffine ((BigHOver.toScheme B S hS).obj
      ((preZeroHypercoverOfOpenCover (affineCover W)).X i)) :=
  Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)

/-- The members of the family of the site attached to an open cover are open immersions. -/
theorem isOpenImmersion_preZeroHypercoverOfOpenCover {W : BigHOver B S hS}
    (U : ((BigHOver.toScheme B S hS).obj W).OpenCover.{u + 1}) (i : U.I₀) :
    IsOpenImmersion ((BigHOver.toScheme B S hS).map ((preZeroHypercoverOfOpenCover U).f i)) :=
  inferInstanceAs (IsOpenImmersion (U.f i))

/-- **Cartesianness of the image of a square is local on the base.** Let `F` be a presheaf of
sets on the big h category over `S` which is a sheaf for the Zariski topology, and let
`(e, p, z, b)` be a cartesian square of the site with base `X`. Let `P` be a class of morphisms
to `X` from objects with affine underlying scheme, stable under precomposition with open
immersions from affine objects, which contains the members of an affine open covering of `X`, and
along each member of which the image under `F` of the base change of the square is cartesian.
Then the image under `F` of the square is cartesian. -/
theorem isPullback_map_of_isPullback_map_pullback (hZ : IsZariskiSheaf B S hS F)
    {X X' Z E : BigHOver B S hS} {b : X' ⟶ X} {z : Z ⟶ X} {p : E ⟶ X'} {e : E ⟶ Z}
    (hsq : IsPullback e p z b)
    (P : ∀ {V : BigHOver B S hS}, (V ⟶ X) → Prop)
    (hPcomp : ∀ {V V' : BigHOver B S hS} (k : V' ⟶ V) (g : V ⟶ X),
      IsAffine ((BigHOver.toScheme B S hS).obj V') →
      IsOpenImmersion ((BigHOver.toScheme B S hS).map k) → P g → P (k ≫ g))
    (U : ((BigHOver.toScheme B S hS).obj X).OpenCover.{u + 1})
    (hU : ∀ i, IsAffine (U.X i) ∧ P ((preZeroHypercoverOfOpenCover U).f i))
    (hH : ∀ {V : BigHOver B S hS} (g : V ⟶ X), IsAffine ((BigHOver.toScheme B S hS).obj V) →
      P g →
      IsPullback (F.map (pullback.fst g z).op) (F.map (pullback.fst g b).op)
        (F.map (pullback.fst (pullback.fst g z) (pullback.fst g b)).op)
        (F.map (pullback.snd (pullback.fst g z) (pullback.fst g b)).op)) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op) := by
  let EX := preZeroHypercoverOfOpenCover U
  have hEX : Presieve.IsSheafFor F (Presieve.ofArrows EX.X EX.f) :=
    preZeroHypercoverOfOpenCover_isSheafFor hZ X U
  have hUmem : (EX.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X) := by
    simpa [EX, preZeroHypercoverOfOpenCover, PreZeroHypercover.presieve₀,
      PreZeroHypercover.map] using U.mem₀
  -- the local cartesian squares
  have hloc : ∀ i, IsPullback (F.map (pullback.fst (EX.f i) z).op)
      (F.map (pullback.fst (EX.f i) b).op)
      (F.map (pullback.fst (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b)).op)
      (F.map (pullback.snd (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b)).op) :=
    fun i ↦ hH (EX.f i) (hU i).1 (hU i).2
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hsq.w]
  · intro x y hxy
    refine eq_of_isPullback_map_pullback hZ b z (𝟙 X) U EX.f (fun i ↦ Category.comp_id _)
      hloc ?_ ?_
    · intro T t a ht
      rw [Category.comp_id] at ht
      rw [ht, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hxy.1]
    · intro T t a ht
      rw [Category.comp_id] at ht
      rw [ht, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hxy.2]
  · intro t s' hc
    have key : ∀ i, ∃ w : F.obj (op (EX.X i)),
        F.map (pullback.fst (EX.f i) z).op w = F.map (pullback.snd (EX.f i) z).op t ∧
          F.map (pullback.fst (EX.f i) b).op w = F.map (pullback.snd (EX.f i) b).op s' := by
      intro i
      refine Types.exists_of_isPullback (hloc i) _ _ ?_
      have hcomm : (pullback.fst (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b) ≫
            pullback.snd (EX.f i) z) ≫ z
          = (pullback.snd (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b) ≫
            pullback.snd (EX.f i) b) ≫ b := by
        have c₁ : pullback.fst (EX.f i) z ≫ EX.f i = pullback.snd (EX.f i) z ≫ z :=
          pullback.condition
        have c₂ : pullback.fst (EX.f i) b ≫ EX.f i = pullback.snd (EX.f i) b ≫ b :=
          pullback.condition
        have c₃ : pullback.fst (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b) ≫
              pullback.fst (EX.f i) z
            = pullback.snd (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b) ≫
              pullback.fst (EX.f i) b := pullback.condition
        rw [Category.assoc, ← c₁, ← Category.assoc, c₃, Category.assoc, c₂, ← Category.assoc]
      simpa only [op_comp, Functor.map_comp_apply] using
        hsq.map_op_eq_map_op F hc hcomm
    choose w hw₁ hw₂ using key
    have hcompat : Presieve.Arrows.PullbackCompatible F EX.f w := by
      intro i j
      let W := pullback (EX.f i) (EX.f j)
      refine eq_of_isPullback_map_pullback hZ b z (pullback.fst (EX.f i) (EX.f j) ≫ EX.f i)
        (affineCover W)
        (fun k ↦ ((preZeroHypercoverOfOpenCover (affineCover W)).f k ≫
          pullback.fst (EX.f i) (EX.f j)) ≫ EX.f i)
        (fun k ↦ (Category.assoc _ _ _).symm) (fun k ↦ ?_) ?_ ?_
      · have hopen : IsOpenImmersion ((BigHOver.toScheme B S hS).map
            ((preZeroHypercoverOfOpenCover (affineCover W)).f k ≫
              pullback.fst (EX.f i) (EX.f j))) := by
          have := isOpenImmersion_preZeroHypercoverOfOpenCover (affineCover W) k
          have := isOpenImmersion_preZeroHypercoverOfOpenCover U j
          have := isOpenImmersion_toScheme_map_pullback_fst (EX.f i) (EX.f j)
          rw [Functor.map_comp]
          infer_instance
        exact hH _ (isAffine_affineCover W k)
          (hPcomp _ (EX.f i) (isAffine_affineCover W k) hopen (hU i).2)
      · intro T t a ht
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
          ← op_comp]
        rw [← Category.assoc] at ht
        rw [map_op_eq_of_map_fst_eq (EX.f i) (hw₁ i) _ a ht,
          map_op_eq_of_map_fst_eq (EX.f j) (hw₁ j) _ a
            (by rw [Category.assoc, ← pullback.condition, ← Category.assoc, ht])]
      · intro T t a ht
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
          ← op_comp]
        rw [← Category.assoc] at ht
        rw [map_op_eq_of_map_fst_eq (EX.f i) (hw₂ i) _ a ht,
          map_op_eq_of_map_fst_eq (EX.f j) (hw₂ j) _ a
            (by rw [Category.assoc, ← pullback.condition, ← Category.assoc, ht])]
    obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff_pullbacks F EX.f).mp hEX w hcompat
    have glue : ∀ {Y : BigHOver B S hS} (c : Y ⟶ X) (r : F.obj (op Y)),
        (∀ i, F.map (pullback.fst (EX.f i) c).op (w i) = F.map (pullback.snd (EX.f i) c).op r) →
          F.map c.op s = r := by
      intro Y c r hw
      apply (isSheafFor_pullback_of_zariskiCover hZ EX hUmem c).isSeparatedFor.ext
      rintro V f ⟨W, a, h, ⟨i⟩, hcomm⟩
      rw [← Functor.map_comp_apply, ← op_comp, ← hcomm, op_comp, Functor.map_comp_apply, hs i]
      exact map_op_eq_of_map_fst_eq (EX.f i) (hw i) a f hcomm
    exact ⟨s, glue z t hw₁, glue b s' hw₂⟩

end BigHOver

end AlgebraicGeometry

end

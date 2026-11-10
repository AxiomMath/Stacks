module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RelationFibreMinimalGenerators
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SliceUnramifiedAt
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFinitePresentationChartAtPoint

/-!
# Slicing a smooth relation to an unramified slice (the étale analogue of the chart of Stacks 06MF)

Let `a, b : R ⟶ U` be morphisms of schemes with `b` **smooth**, and let `r₀` be a point of `R` at
which the maximal ideal of `𝒪_{U, a r₀}` **generates** the maximal ideal of the local ring
`𝒪_{b⁻¹(b r₀), r₀}` of the fibre of `b`. That hypothesis — the source's
`φ(𝔪_u) 𝒪_{V, v} = 𝔪_v` of Morphisms, Lemma 29.36.14 (**Stacks 02GF**) — is what the chart
construction of **Stacks 06N3** has in hand where that of **Stacks 06MF** has only isolation of
the double-fibre point, and this file carries it through the two slicing steps of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/CohenMacaulaySlice/RelationSlice.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFinitePresentationChartAtPoint.lean`, replacing their
**quasi-finiteness** datum by an **unramifiedness** datum.

The slicing sequence is
`AlgebraicGeometry.exists_mem_maximalIdeal_isRegular_ofList_eq_maximalIdeal_fiberStalk_of_smooth`
rather than `AlgebraicGeometry.exists_mem_maximalIdeal_isRegular_fiberStalk_of_smooth`: it
generates the maximal ideal of the fibre stalk outright, so the local ring of the fibre of the
slice is the **residue field** `κ(r₀)` and not merely a zero-dimensional ring, and
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk` turns that,
together with finite separability of `κ(r₀)` over `κ(b r₀)`, into unramifiedness of the slice
over `U` along `b` at the sliced point. Everything else — the regular sequence, the zero scheme
of its pullbacks, the flatness and local finite presentation of **Stacks 06LI**, the slice taken
downstairs, the fibre product square identifying the slice upstairs with its base change — is
exactly as in the flat case, those steps using only the regularity of the sequence.

Isolation of the double-fibre point is **not** assumed: the flat and locally finitely presented
conclusions of **Stacks 06LI** need only the regular sequence, and the generation hypothesis
gives one. So the lemmas below are not a strengthening of the flat ones under an extra
hypothesis but the same slicing under a different one.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_unramified_of_smooth`: the
  unramified analogue of
  `AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth` — the zero scheme
  inside an affine neighbourhood `W` of `r₀` of the pullbacks of functions on `U` is flat and
  locally of finite presentation over `U` along `b`, and **unramified over `U` along `b`** at the
  point above `r₀`.
* `AlgebraicGeometry.exists_mono_flat_surjective_slice_unramified_of_smooth`: the unramified
  analogue of `AlgebraicGeometry.exists_mono_flat_surjective_slice_of_smooth` — the slice taken
  downstairs, together with the slice of the relation covering it by a flat, locally finitely
  presented, surjective morphism, the fibre product square which identifies the one with the base
  change of the other, and the **unramifiedness datum** at the point above `r₀`.

## Implementation notes

The residue field extension the unramifiedness needs is a hypothesis of the source's situation
and not of the slicing, so — exactly as the flat lemmas carry closedness of `r₀` in its fibre
under `b` — it is carried **inside** the conclusion, as the antecedent of an implication, so that
the lemmas' own hypotheses are the generation hypothesis and nothing else. It is stated at `r₀`
and at `b`, before any slicing, which is the form in which **Stacks 056U**
(`AlgebraicGeometry.dense_closedPoints_with_finite_separable_residueField_of_smooth`) delivers
it; the transport to the sliced point is inside
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk`, along the
residue field isomorphism of the preimmersion.

`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk` states its data
at the image point `ι z` of the slice's point. The slicing proof has that image point only up to
a propositional equality — the point of the zero scheme lies over the chosen point of `W`, which
lies over `r₀` — so it is restated below at a **variable** point with the equality as a
`subst`-able hypothesis, the shape
`Stacks.AlgebraicGeometry.quasiFiniteAt_comp_of_isRegular_fiberStalk` already has; writing the
data out at the concrete image point instead does not elaborate.

`AlgebraicGeometry.isPullback_of_mono_restrict` of
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFinitePresentationChartAtPoint.lean` — the step that
factors the second projection of a fibre product square through a monomorphism — was private to
that file and is used here, so it is no longer private; nothing else about that file changed.

No `@[stacks]` attribute is claimed: **Stacks 06LI** is registered on
`Stacks.AlgebraicGeometry.exists_affineOpen_regularImmersion_flat_of_isRegular_fiber`,
**Stacks 02GF** on `AlgebraicGeometry.unramifiedAt_tfae`, and this is a step of the chart
construction of **Stacks 06N3**, not any whole tag.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Theorem 101.21.6 (Tag 06N3)](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The unramifiedness criterion of **Stacks 02GF** for a slice, with the image point of the
slice's point taken as a variable and the identification as a `subst`-able hypothesis. This is
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk` at the shape
`Stacks.AlgebraicGeometry.quasiFiniteAt_comp_of_isRegular_fiberStalk` has. -/
private theorem unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk_point
    {X S Z : Scheme.{u}} (ι : Z ⟶ X) [IsPreimmersion ι] (f : X ⟶ S)
    [LocallyOfFiniteType (ι ≫ f)] (z : Z) (x : X) (hx : ι z = x)
    {r : ℕ} (h : Fin r → X.presheaf.stalk x)
    (hzero : ∀ k, (ι.stalkMap z).hom (hx.symm ▸ h k) = 0)
    (hgen : Ideal.ofList
        (List.ofFn fun k => ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
          ((f.fiberι_asFiber x).symm ▸ h k)) =
      maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
    (hsep : letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite (S.residueField (f x)) (X.residueField x) ∧
        Algebra.IsSeparable (S.residueField (f x)) (X.residueField x)) :
    UnramifiedAt (ι ≫ f) z := by
  subst hx
  exact Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk ι f z h
    hzero hgen hsep

/-- `appLE` on `⊤` only depends on the morphism, up to equality of morphisms. -/
private theorem appLE_top_congr_of_eq {W U : Scheme.{u}} (V : U.Opens) (x : Γ(U, V))
    {f g : W ⟶ U} (h : f = g) (e : (⊤ : W.Opens) ≤ f ⁻¹ᵁ V) (e' : (⊤ : W.Opens) ≤ g ⁻¹ᵁ V) :
    (f.appLE V ⊤ e).hom x = (g.appLE V ⊤ e').hom x := by
  subst h
  rfl

/-- Pulling back a section over `V` along `g` after restricting along `f` is the pullback along
`g ≫ f`. -/
private theorem appTop_appLE_apply {W Y U : Scheme.{u}} (g : W ⟶ Y) (f : Y ⟶ U) (V : U.Opens)
    (e : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ V) (e' : (⊤ : W.Opens) ≤ (g ≫ f) ⁻¹ᵁ V) (x : Γ(U, V)) :
    g.appTop.hom ((f.appLE V ⊤ e).hom x) = ((g ≫ f).appLE V ⊤ e').hom x := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.Hom.appLE_comp_appLE g f V ⊤ (g ⁻¹ᵁ ⊤) e le_rfl)) x

/-- **The slicing step of the étale chart construction, with an unramified slice.** Let
`a, b : R ⟶ U` with `b` smooth and let `r₀ : R` be a point at which the maximal ideal of
`𝒪_{U, a r₀}` generates the maximal ideal of the local ring of the fibre of `b` through `r₀`.
Then there are an affine open `V ∋ a r₀` of `U`, functions `s₁, …, s_d ∈ Γ(U, V)` whose germs at
`a r₀` lie in the maximal ideal, and an affine open neighbourhood `jW : W ⟶ R` of `r₀` mapping
into `a⁻¹(V)`, such that the zero scheme in `W` of the pullbacks of the `s_i` along `W ⟶ R ⟶ U`
is flat and locally of finite presentation over `U` along `b`. If moreover `κ(r₀)` is finite
separable over `κ(b r₀)`, that zero scheme is **unramified over `U` along `b`** at every point of
it lying over the chosen point of `W`.

This is `AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth` with the
slicing sequence of
`AlgebraicGeometry.exists_mem_maximalIdeal_isRegular_ofList_eq_maximalIdeal_fiberStalk_of_smooth`
in place of that of **Stacks 06LC**: it generates the maximal ideal of the fibre stalk, so the
local ring of the fibre of the slice is `κ(r₀)` and
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk` applies where
only quasi-finiteness was available. See the module documentation. -/
theorem exists_isOpenImmersion_flat_zeroScheme_pullback_unramified_of_smooth {R U : Scheme.{u}}
    (a b : R ⟶ U) [Smooth b] (r₀ : R)
    (hmap : Ideal.map ((b.fiberι (b r₀) ≫ a).stalkMap (b.asFiber r₀)).hom
          (maximalIdeal (U.presheaf.stalk ((b.fiberι (b r₀) ≫ a) (b.asFiber r₀))))
        = maximalIdeal ((b.fiber (b r₀)).presheaf.stalk (b.asFiber r₀))) :
    ∃ (d : ℕ) (V : U.Opens) (hrV : a r₀ ∈ V) (s : Fin d → Γ(U, V)),
      IsAffineOpen V ∧
        (∀ i, U.presheaf.germ V (a r₀) hrV (s i) ∈
          maximalIdeal (U.presheaf.stalk (a r₀))) ∧
        ∃ (W : Scheme.{u}) (jW : W ⟶ R) (_ : IsOpenImmersion jW) (w : W)
            (hWV : (⊤ : W.Opens) ≤ (jW ≫ a) ⁻¹ᵁ V) (c : Fin d → Γ(W, ⊤)),
          IsAffine W ∧ jW w = r₀ ∧
            (∀ i, c i = ((jW ≫ a).appLE V ⊤ hWV).hom (s i)) ∧
            Flat ((Scheme.IdealSheafData.ofIdealTop
                (Ideal.ofList (List.ofFn c))).subschemeι ≫ jW ≫ b) ∧
            LocallyOfFinitePresentation ((Scheme.IdealSheafData.ofIdealTop
                (Ideal.ofList (List.ofFn c))).subschemeι ≫ jW ≫ b) ∧
            ((letI := (b.residueFieldMap r₀).hom.toAlgebra;
                Module.Finite (U.residueField (b r₀)) (R.residueField r₀) ∧
                  Algebra.IsSeparable (U.residueField (b r₀)) (R.residueField r₀)) →
              ∀ t₀ : (Scheme.IdealSheafData.ofIdealTop
                  (Ideal.ofList (List.ofFn c))).subscheme,
                (Scheme.IdealSheafData.ofIdealTop
                  (Ideal.ofList (List.ofFn c))).subschemeι t₀ = w →
                UnramifiedAt ((Scheme.IdealSheafData.ofIdealTop
                  (Ideal.ofList (List.ofFn c))).subschemeι ≫ jW ≫ b) t₀) := by
  classical
  obtain ⟨d, t, hmem, -, hreg, hgen⟩ :=
    exists_mem_maximalIdeal_isRegular_ofList_eq_maximalIdeal_fiberStalk_of_smooth a b r₀ hmap
  obtain ⟨V, hrV, hV, s, hs⟩ := Stacks.AlgebraicGeometry.exists_isAffineOpen_germ_eq (a r₀) t
  -- shrink `R` to the preimage of `V`, where the pullbacks of the `s i` are global functions
  have hr₀' : r₀ ∈ a ⁻¹ᵁ V := hrV
  set ι' : (a ⁻¹ᵁ V).toScheme ⟶ R := (a ⁻¹ᵁ V).ι with hι'
  set r₀' : (a ⁻¹ᵁ V).toScheme := ⟨r₀, hr₀'⟩ with hr₀'def
  have hle : (⊤ : (a ⁻¹ᵁ V).toScheme.Opens) ≤ (ι' ≫ a) ⁻¹ᵁ V := fun x _ => x.2
  set c₀ : Fin d → Γ((a ⁻¹ᵁ V).toScheme, ⊤) :=
    fun i => ((ι' ≫ a).appLE V ⊤ hle).hom (s i) with hc₀
  -- the germ at `r₀` of the pullback of `s i` is the image of the germ of `s i`
  have hgerm : ∀ i, (a ⁻¹ᵁ V).toScheme.presheaf.germ ⊤ r₀' trivial (c₀ i)
      = (ι'.stalkMap r₀').hom ((a.stalkMap r₀).hom (t i)) := by
    intro i
    have h2 : (U.presheaf.germ V ((ι' ≫ a) r₀') hrV) (s i) = t i := hs i
    have hgs := Scheme.Hom.germ_stalkMap_apply (ι' ≫ a) V r₀' hrV (s i)
    have hres := (a ⁻¹ᵁ V).toScheme.presheaf.germ_res_apply (homOfLE hle) r₀' trivial
      ((ι' ≫ a).app V (s i))
    have hfinal : ((ι' ≫ a).stalkMap r₀').hom (t i)
        = (ι'.stalkMap r₀').hom ((a.stalkMap r₀).hom (t i)) := by
      rw [Scheme.Hom.stalkMap_comp]
      rfl
    calc (a ⁻¹ᵁ V).toScheme.presheaf.germ ⊤ r₀' trivial (c₀ i)
        = (a ⁻¹ᵁ V).toScheme.presheaf.germ ((ι' ≫ a) ⁻¹ᵁ V) r₀' hrV
            ((ι' ≫ a).app V (s i)) := hres
      _ = ((ι' ≫ a).stalkMap r₀').hom
            ((U.presheaf.germ V ((ι' ≫ a) r₀') hrV) (s i)) := hgs.symm
      _ = ((ι' ≫ a).stalkMap r₀').hom (t i) := by rw [h2]
      _ = (ι'.stalkMap r₀').hom ((a.stalkMap r₀).hom (t i)) := hfinal
  -- carry the regular sequence across the open immersion
  have hreg' := Stacks.AlgebraicGeometry.isRegular_fiber_comp_of_isOpenImmersion ι' b r₀'
    (fun i => (a.stalkMap r₀).hom (t i)) hreg
  -- cut the slice
  have hflatAt : IsFlatAt (ι' ≫ b).toLRSHom.toShHom r₀' :=
    (Flat.iff_flat_stalkMap (ι' ≫ b)).1 inferInstance r₀'
  obtain ⟨W, j, hj, w, hWaff, hjw, hflat, hlfp⟩ :=
    Stacks.AlgebraicGeometry.exists_affineOpenImmersion_flat_zeroScheme_of_isRegular_fiber
      (ι' ≫ b) r₀' c₀ hflatAt
      (by
        refine (congrArg List.ofFn (funext fun i => ?_)) ▸ hreg'
        rw [hgerm i])
  have _ := hj
  set cW : Fin d → Γ(W, ⊤) := fun i => j.appTop (c₀ i) with hcW
  set D : W.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn cW))
    with hDdef
  have hWV : (⊤ : W.Opens) ≤ ((j ≫ ι') ≫ a) ⁻¹ᵁ V := fun x _ => hle (x := j x) trivial
  have hjw' : (j ≫ ι') w = r₀ := by
    change ι' (j w) = r₀
    rw [hjw]
    rfl
  have hWV' : (⊤ : W.Opens) ≤ (j ≫ ι' ≫ a) ⁻¹ᵁ V := fun x _ => hle (x := j x) trivial
  refine ⟨d, V, hrV, s, hV, fun i => hs i ▸ hmem i, W, j ≫ ι', inferInstance, w, hWV,
    cW, hWaff, hjw', fun i => ?_, ?_, ?_, ?_⟩
  · exact (appTop_appLE_apply j (ι' ≫ a) V hle hWV' (s i)).trans
      (appLE_top_congr_of_eq V (s i) (Category.assoc j ι' a).symm hWV' hWV)
  · rw [Category.assoc]
    exact hflat
  · rw [Category.assoc]
    exact hlfp
  -- the slice is unramified over `U` along `b` at the point above `w`
  · intro hsep t₀ ht₀
    have : IsAffine W := hWaff
    have hx : (D.subschemeι ≫ j ≫ ι') t₀ = r₀ := by
      change ι' (j (D.subschemeι t₀)) = r₀
      rw [ht₀, hjw]
      rfl
    rw [show D.subschemeι ≫ (j ≫ ι') ≫ b = (D.subschemeι ≫ j ≫ ι') ≫ b from
      (Category.assoc _ _ _).symm]
    have : LocallyOfFinitePresentation ((D.subschemeι ≫ j ≫ ι') ≫ b) := by
      simpa only [Category.assoc] using hlfp
    have : LocallyOfFiniteType ((D.subschemeι ≫ j ≫ ι') ≫ b) := inferInstance
    refine unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk_point
      (D.subschemeι ≫ j ≫ ι') b t₀ r₀ hx (fun k => (a.stalkMap r₀).hom (t k)) ?_ hgen hsep
    intro k
    have hjp : j (D.subschemeι t₀) = r₀' := by rw [ht₀]; exact hjw
    -- the germ of `cW k` at the point of `W` is the pullback of the chosen germ of `𝒪_{U, a r₀}`
    have hgermW : W.presheaf.germ ⊤ (D.subschemeι t₀) trivial (cW k)
        = ((j ≫ ι').stalkMap (D.subschemeι t₀)).hom
            (hx.symm ▸ (a.stalkMap r₀).hom (t k)) := by
      have h1 : W.presheaf.germ ⊤ (D.subschemeι t₀) trivial (cW k)
          = (j.stalkMap (D.subschemeι t₀)).hom
              ((a ⁻¹ᵁ V).toScheme.presheaf.germ ⊤ (j (D.subschemeι t₀)) trivial (c₀ k)) :=
        Stacks.AlgebraicGeometry.germ_appTop_eq_stalkMap_germ j (D.subschemeι t₀) (c₀ k)
      have h2 := Stacks.AlgebraicGeometry.germ_top_cast_eq hjp (c₀ k)
      have h3 := Stacks.AlgebraicGeometry.stalkMap_comp_cast j ι' (D.subschemeι t₀) hjp hx
        ((a.stalkMap r₀).hom (t k))
      rw [h1, h2, hgerm k]
      exact h3.symm
    rw [Stacks.AlgebraicGeometry.stalkMap_comp_apply_cast D.subschemeι (j ≫ ι') t₀ hx
      ((a.stalkMap r₀).hom (t k)), ← hgermW]
    -- the sections cutting the slice pull back to zero on it
    have happ : (D.subschemeι.appTop) (cW k) = 0 := by
      change (D.subschemeι.appTop).hom (cW k) = 0
      refine RingHom.mem_ker.mp ?_
      rw [hDdef, Stacks.AlgebraicGeometry.ker_appTop_subschemeι_ofIdealTop
        (Ideal.ofList (List.ofFn cW))]
      exact Ideal.subset_span (List.mem_ofFn.mpr ⟨k, rfl⟩)
    have hfinal : (D.subschemeι.stalkMap t₀)
        (W.presheaf.germ ⊤ (D.subschemeι t₀) trivial (cW k)) = 0 := by
      rw [← Stacks.AlgebraicGeometry.germ_appTop_eq_stalkMap_germ D.subschemeι t₀ (cW k), happ,
        map_zero]
    exact hfinal

/-- **The slicing step of the étale chart construction, with the slice taken downstairs.** Let
`a, b : R ⟶ U` be smooth morphisms of schemes and let `r₀ : R` be a point at which the maximal
ideal of `𝒪_{U, a r₀}` generates the maximal ideal of the local ring of the fibre of `b` through
`r₀`. Then there are schemes `Zs` and `Ts`, monomorphisms `ιZ : Zs ⟶ U` and `j : Ts ⟶ R`, a
morphism `kk : Ts ⟶ Zs` with `kk ≫ ιZ = j ≫ a` which is flat, locally of finite presentation and
surjective, and a point `t₀` of `Ts` over `r₀`, such that `j ≫ b` is flat and locally of finite
presentation — and, as soon as `κ(r₀)` is finite separable over `κ(b r₀)`, **unramified at `t₀`**.

That last conjunct is the unramifiedness datum **Stacks 06N2** consumes, where
`AlgebraicGeometry.exists_mono_flat_surjective_slice_of_smooth` delivers the quasi-finiteness
datum **Stacks 06ME** consumes: the chart is `Zs ⟶ U ⟶ 𝒳` and `Ts` covers the base change of it
along a smooth chart `U ⟶ 𝒳`, so unramifiedness of `j ≫ b` at `t₀` is unramifiedness of that
base change at the point above `kk t₀`. The extra input is carried inside the conclusion, as the
antecedent of an implication, so that the lemma's own hypothesis is the generation hypothesis and
nothing else.

The construction of `Zs`, `Ts`, `kk` and the fibre product square is the one of
`AlgebraicGeometry.exists_mono_flat_surjective_slice_of_smooth`, run on
`AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_unramified_of_smooth`: `Zs` is
the zero scheme, inside an affine open `V ∋ a r₀` of `U`, of functions `s₁, …, s_d ∈ Γ(U, V)`
vanishing at `a r₀`, cut down to the open image of the affine neighbourhood `W` of `r₀`, and `Ts`
is the zero scheme in `W` of the pullbacks of the `s_i`. Since `V` is affine,
`Stacks.AlgebraicGeometry.comap_ofIdealTop` identifies `Ts` with the base change of `Zs` along
`W ⟶ V`, which makes `kk` a base change of a smooth morphism, surjective onto the piece of `Zs`
over the image of `W`; that identification is the fibre product square in the conclusion. -/
theorem exists_mono_flat_surjective_slice_unramified_of_smooth {R U : Scheme.{u}}
    (a b : R ⟶ U) [Smooth a] [Smooth b] (r₀ : R)
    (hmap : Ideal.map ((b.fiberι (b r₀) ≫ a).stalkMap (b.asFiber r₀)).hom
          (maximalIdeal (U.presheaf.stalk ((b.fiberι (b r₀) ≫ a) (b.asFiber r₀))))
        = maximalIdeal ((b.fiber (b r₀)).presheaf.stalk (b.asFiber r₀))) :
    ∃ (Zs Ts : Scheme.{u}) (ιZ : Zs ⟶ U) (j : Ts ⟶ R) (kk : Ts ⟶ Zs) (t₀ : Ts),
      Mono ιZ ∧ Mono j ∧ kk ≫ ιZ = j ≫ a ∧
        Flat kk ∧ LocallyOfFinitePresentation kk ∧ Function.Surjective kk.base ∧
        Flat (j ≫ b) ∧ LocallyOfFinitePresentation (j ≫ b) ∧ j t₀ = r₀ ∧
        ((letI := (b.residueFieldMap r₀).hom.toAlgebra;
            Module.Finite (U.residueField (b r₀)) (R.residueField r₀) ∧
              Algebra.IsSeparable (U.residueField (b r₀)) (R.residueField r₀)) →
          UnramifiedAt (j ≫ b) t₀) ∧
        ∃ (W : Scheme.{u}) (jW : W ⟶ R) (jT : Ts ⟶ W), IsOpenImmersion jW ∧ jT ≫ jW = j ∧
          IsPullback jT kk (jW ≫ a) ιZ := by
  classical
  obtain ⟨d, V, hrV, s, hVaff, hmem, W, jW, hjW, w, hWV, cf, hWaff, hjw, hcf, hflat, hlfp,
      hun⟩ :=
    exists_isOpenImmersion_flat_zeroScheme_pullback_unramified_of_smooth a b r₀ hmap
  have := hjW
  have : IsAffine V.toScheme := hVaff
  have hVtop : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun x _ => x.2
  -- factor `jW ≫ a` through the affine open `V`
  set gV : W ⟶ V.toScheme := W.topIso.inv ≫ (jW ≫ a).resLE V ⊤ hWV with hgVdef
  have hgV : gV ≫ V.ι = jW ≫ a := by
    exact topIso_inv_resLE_comp_ι _ _ _
  have hgVsmooth : Smooth gV := by rw [hgVdef]; infer_instance
  -- the functions cutting the slice, read on the affine open `V`
  set sV : Fin d → Γ(V.toScheme, ⊤) := fun i => (V.ι.appLE V ⊤ hVtop).hom (s i) with hsVdef
  have hWV2 : (⊤ : W.Opens) ≤ (gV ≫ V.ι) ⁻¹ᵁ V := by rw [hgV]; exact hWV
  have hgVapp : ∀ i, gV.appTop.hom (sV i) = cf i := by
    intro i
    rw [hcf i, appLE_top_congr_of_eq V (s i) hgV.symm hWV hWV2]
    exact appTop_appLE_apply gV V.ι V hVtop hWV2 (s i)
  -- the zero scheme downstairs and its pullback upstairs
  set D : V.toScheme.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn sV)) with hDdef
  have hcomap : D.comap gV =
      Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn cf)) := by
    rw [hDdef, Stacks.AlgebraicGeometry.comap_ofIdealTop gV (Ideal.ofList (List.ofFn sV))]
    congr 1
    rw [show (Ideal.ofList (List.ofFn sV)) = Ideal.span {x | x ∈ List.ofFn sV} from rfl,
      Ideal.map_span]
    refine congrArg Ideal.span (Set.ext fun x => ?_)
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_ofFn]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hgVapp i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨sV i, ⟨i, rfl⟩, hgVapp i⟩
  rw [← hcomap] at hflat hlfp hun
  -- the point of the slice upstairs over `r₀`
  have hgerm : ∀ f ∈ List.ofFn cf, W.presheaf.germ ⊤ w trivial f ∈
      maximalIdeal (W.presheaf.stalk w) := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    have hbo : W.basicOpen (cf i) = ⊤ ⊓ (jW ≫ a) ⁻¹ᵁ U.basicOpen (s i) := by
      rw [hcf i]
      exact Scheme.basicOpen_appLE (jW ≫ a) ⊤ V hWV (s i)
    have hnot : (jW ≫ a) w ∉ U.basicOpen (s i) := by
      have hru : (jW ≫ a) w = a r₀ := by
        change a (jW w) = a r₀
        rw [hjw]
      rw [hru, U.mem_basicOpen (s i) (a r₀) hrV]
      exact (IsLocalRing.mem_maximalIdeal _).1 (hmem i)
    refine (IsLocalRing.mem_maximalIdeal _).2 fun hu => hnot ?_
    have hw : w ∈ W.basicOpen (cf i) := (W.mem_basicOpen_top (cf i) w).2 hu
    rw [hbo] at hw
    exact hw.2
  have hwmem : w ∈ (D.comap gV).support := by
    rw [hcomap]
    exact mem_support_ofIdealTop_of_germ_mem_maximalIdeal w (List.ofFn cf) hgerm
  have hwrange : w ∈ Set.range (D.comap gV).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hwmem
  obtain ⟨t₀, ht₀⟩ := hwrange
  -- the covering morphism from the slice upstairs to the slice downstairs
  set kkfull : (D.comap gV).subscheme ⟶ D.subscheme :=
    (D.comapIso gV).hom ≫ pullback.snd gV D.subschemeι with hkkfulldef
  have hkkι : kkfull ≫ D.subschemeι = (D.comap gV).subschemeι ≫ gV := by
    rw [hkkfulldef, Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  have hkkflat : Flat kkfull := by rw [hkkfulldef]; infer_instance
  have hkklfp : LocallyOfFinitePresentation kkfull := by rw [hkkfulldef]; infer_instance
  have hkkιpt : ∀ t, gV ((D.comap gV).subschemeι t) = D.subschemeι (kkfull t) := fun t => by
    change ((D.comap gV).subschemeι ≫ gV) t = (kkfull ≫ D.subschemeι) t
    rw [hkkι]
  have hisosurj : Function.Surjective ((D.comapIso gV).hom.base) := fun x =>
    ⟨(D.comapIso gV).inv.base x, by
      change ((D.comapIso gV).inv ≫ (D.comapIso gV).hom) x = x
      rw [Iso.inv_hom_id]
      rfl⟩
  have hrangekk : Set.range kkfull.base = D.subschemeι.base ⁻¹' Set.range gV.base := by
    rw [← Scheme.Pullback.range_snd (f := gV) (g := D.subschemeι)]
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨t, rfl⟩ := hx
      exact ⟨(D.comapIso gV).hom t, by rw [hkkfulldef]; rfl⟩
    · obtain ⟨yy, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hisosurj yy
      exact ⟨t, by rw [hkkfulldef]; rfl⟩
  -- cut the slice downstairs down to the open image of `W`
  have hgVopen : IsOpen (Set.range gV.base) := gV.isOpenMap.isOpen_range
  set O : V.toScheme.Opens := ⟨Set.range gV.base, hgVopen⟩ with hOdef
  set Oz : D.subscheme.Opens := D.subschemeι ⁻¹ᵁ O with hOzdef
  have hekk : (⊤ : (D.comap gV).subscheme.Opens) ≤ kkfull ⁻¹ᵁ Oz := fun t _ =>
    show D.subschemeι (kkfull t) ∈ O from ⟨(D.comap gV).subschemeι t, hkkιpt t⟩
  set kk : (D.comap gV).subscheme ⟶ Oz.toScheme :=
    (D.comap gV).subscheme.topIso.inv ≫ kkfull.resLE Oz ⊤ hekk with hkkdef
  have hkkfac : kk ≫ Oz.ι = kkfull := by
    exact topIso_inv_resLE_comp_ι _ _ _
  have hkkfacpt : ∀ t, Oz.ι (kk t) = kkfull t := fun t => by
    change (kk ≫ Oz.ι) t = kkfull t
    rw [hkkfac]
  refine ⟨Oz.toScheme, (D.comap gV).subscheme, Oz.ι ≫ D.subschemeι ≫ V.ι,
    (D.comap gV).subschemeι ≫ jW, kk, t₀, inferInstance, inferInstance,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, hkkfac, hkkι, Category.assoc, hgV, Category.assoc]
  · rw [hkkdef]; infer_instance
  · rw [hkkdef]; infer_instance
  · intro ζ
    have hmemζ : (Oz.ι ζ) ∈ Set.range kkfull.base := by
      rw [hrangekk]
      exact ζ.2
    obtain ⟨t, ht⟩ := hmemζ
    exact ⟨t, Subtype.ext ((hkkfacpt t).trans ht)⟩
  · rw [Category.assoc]; exact hflat
  · rw [Category.assoc]; exact hlfp
  · change jW ((D.comap gV).subschemeι t₀) = r₀
    rw [ht₀, hjw]
  · intro hsep
    rw [Category.assoc]
    exact hun hsep t₀ ht₀
  · -- the slice upstairs is the base change of the slice downstairs along `W ⟶ U`
    refine ⟨W, jW, (D.comap gV).subschemeι, hjW, rfl, ?_⟩
    have hs : IsPullback (D.comap gV).subschemeι kkfull gV D.subschemeι :=
      isPullback_of_isClosedImmersion _ _ _ _ hkkι.symm (by simp)
    have hsOz : IsPullback (D.comap gV).subschemeι kk gV (Oz.ι ≫ D.subschemeι) :=
      isPullback_of_mono_restrict hs hkkfac
    have hfin := isPullback_comp_mono hsOz V.ι
    rw [hgV, Category.assoc] at hfin
    exact hfin

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FibreQuasiFiniteAt
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.GermsToSections
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RelationFibreRegularSequence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.ZeroScheme

/-!
# Slicing a smooth relation by equations pulled back along the other leg (Stacks 06MF)

Let `a, b : R ⟶ U` be morphisms of schemes with `b` **smooth**, and let `r₀` be a point of `R` at
which the double fibre — the scheme-theoretic fibre over `a r₀` of `b.fiber (b r₀) ⟶ R ⟶ U` along
`a` — has `r₀` as an isolated point.  This file performs the slicing step of the chart
construction of **Stacks 06MF**: there are an affine open `V ∋ a r₀` of `U`, functions
`s₁, …, s_d ∈ Γ(U, V)` vanishing at `a r₀`, and an affine open neighbourhood `W` of `r₀` inside
`a⁻¹(V)` such that the zero scheme inside `W` of the pullbacks `a^*s₁, …, a^*s_d` is **flat and
locally of finite presentation over `U` along `b`**, and — as soon as `r₀` is closed in its
fibre under `b` — **quasi-finite over `U` along `b` at the point above `r₀`**.

The functions are pulled back along `a`, not chosen on `R`: that is what makes the zero scheme a
base change of `W` over the zero scheme of the `s_i` in `U`, which is how the descent step of
**Stacks 06MF** uses it.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth`: the slice.

## Implementation notes

Three inputs are chained.
`AlgebraicGeometry.exists_mem_maximalIdeal_isRegular_fiberStalk_of_smooth` produces the regular
sequence in the local ring of the fibre of `b`, as germs at `a r₀` pulled back along `a`;
`Stacks.AlgebraicGeometry.exists_isAffineOpen_germ_eq` realizes those germs as sections on one
affine open `V ∋ a r₀`; and
`Stacks.AlgebraicGeometry.exists_affineOpenImmersion_flat_zeroScheme_of_isRegular_fiber` —
**Stacks 06LI** for prescribed global functions — cuts the slice.

The middle step forces the source to be shrunk: Stacks 06LI asks for *global* functions on the
source, and the pullbacks `a^*s_i` are only defined on `a⁻¹(V)`.  So the lemma is applied to
`(a ⁻¹ᵁ V).ι ≫ b` rather than to `b`, and the regular-sequence hypothesis is carried across the
open immersion by
`Stacks.AlgebraicGeometry.isRegular_fiber_comp_of_isOpenImmersion`; the germ of the pullback of a
section is computed by `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply` through the unfolding
of `AlgebraicGeometry.Scheme.Hom.appLE`.

The functions cutting the slice are returned as an explicit family `c` on `W` together with the
equation identifying each `c i` with the pullback of `s i` along `W ⟶ R ⟶ U`, rather than as that
pullback itself, so that the flatness conclusion is stated about the family Stacks 06LI returns
and the identification is a separate, purely section-level, equation.

The quasi-finiteness conclusion is the one the chart of **Stacks 06MF** needs at the point it
produces, and it is the whole reason the *length* of the regular sequence is carried:
`AlgebraicGeometry.exists_mem_maximalIdeal_isRegular_fiberStalk_of_smooth` returns a sequence as
long as `dim 𝒪_{b.fiber (b r₀), r₀}`, so the local ring of the fibre of the slice — a quotient of
that one in which the whole sequence vanishes — is zero-dimensional, and
`Stacks.AlgebraicGeometry.quasiFiniteAt_comp_of_isRegular_fiberStalk` turns that, together with
the finiteness of the residue-field extension at a point closed in its fibre, into
quasi-finiteness through the fibre-dimension formula of **Stacks 02FX**.  The extra input — that
`r₀` is closed in its fibre under `b` — is carried *inside* the conclusion, as the hypothesis of
an implication, so that the lemma's own hypotheses are unchanged.

No `@[stacks]` attribute is claimed: **Stacks 06LI** is registered on
`Stacks.AlgebraicGeometry.exists_affineOpen_regularImmersion_flat_of_isRegular_fiber`, and this
is a step of **Stacks 06MF**, not the whole tag.

## References

* [Stacks Project, Tag 06LC](https://stacks.math.columbia.edu/tag/06LC)
* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The slicing step of the chart construction of Stacks 06MF.**  Let `a, b : R ⟶ U` with `b`
smooth and let `r₀ : R` be a point at which the double fibre of `(a, b)` is isolated.  Then there
are an affine open `V ∋ a r₀` of `U`, functions `s₁, …, s_d ∈ Γ(U, V)` whose germs at `a r₀` lie
in the maximal ideal, and an affine open neighbourhood `jW : W ⟶ R` of `r₀` mapping into
`a⁻¹(V)`, such that the zero scheme in `W` of the pullbacks of the `s_i` along `W ⟶ R ⟶ U` is
flat and locally of finite presentation over `U` along `b`.  If moreover `r₀` is closed in its
fibre under `b`, that zero scheme is **quasi-finite over `U` along `b`** at every point of it
lying over the chosen point of `W`. -/
theorem exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth {R U : Scheme.{u}}
    (a b : R ⟶ U) [Smooth b] (r₀ : R)
    (hiso : IsIsolatedPoint ((b.fiberι (b r₀) ≫ a).asFiber (b.asFiber r₀))) :
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
            (IsClosed ({b.asFiber r₀} : Set (b.fiber (b r₀))) →
              ∀ t₀ : (Scheme.IdealSheafData.ofIdealTop
                  (Ideal.ofList (List.ofFn c))).subscheme,
                (Scheme.IdealSheafData.ofIdealTop
                  (Ideal.ofList (List.ofFn c))).subschemeι t₀ = w →
                quasiFiniteAt ((Scheme.IdealSheafData.ofIdealTop
                  (Ideal.ofList (List.ofFn c))).subschemeι ≫ jW ≫ b) t₀) := by
  classical
  obtain ⟨d, t, hmem, hdim, hreg⟩ :=
    exists_mem_maximalIdeal_isRegular_fiberStalk_of_smooth a b r₀ hiso
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
    show ι' (j w) = r₀
    rw [hjw]
    rfl
  refine ⟨d, V, hrV, s, hV, fun i => hs i ▸ hmem i, W, j ≫ ι', inferInstance, w, hWV,
    cW, hWaff, hjw', fun i => ?_, ?_, ?_, ?_⟩
  · rw [hcW, hc₀, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.Hom.appLE_comp_appLE j (ι' ≫ a) V ⊤ (j ⁻¹ᵁ ⊤) hle le_rfl)) (s i)
  · rw [Category.assoc]
    exact hflat
  · rw [Category.assoc]
    exact hlfp
  -- the slice is quasi-finite over `U` along `b` at the point above `w`
  · intro hclosed t₀ ht₀
    have : IsAffine W := hWaff
    have hx : (D.subschemeι ≫ j ≫ ι') t₀ = r₀ := by
      show (j ≫ ι') (D.subschemeι t₀) = r₀
      rw [ht₀]
      exact hjw'
    rw [show D.subschemeι ≫ (j ≫ ι') ≫ b = (D.subschemeι ≫ j ≫ ι') ≫ b from
      (Category.assoc _ _ _).symm]
    have : LocallyOfFinitePresentation ((D.subschemeι ≫ j ≫ ι') ≫ b) := by
      simpa only [Category.assoc] using hlfp
    have : LocallyOfFiniteType ((D.subschemeι ≫ j ≫ ι') ≫ b) := inferInstance
    refine Stacks.AlgebraicGeometry.quasiFiniteAt_comp_of_isRegular_fiberStalk
      (D.subschemeι ≫ j ≫ ι') b t₀ r₀ hx (fun k => (a.stalkMap r₀).hom (t k)) ?_ hreg hdim
      hclosed
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
      show (D.subschemeι.appTop).hom (cW k) = 0
      refine RingHom.mem_ker.mp ?_
      rw [hDdef, Stacks.AlgebraicGeometry.ker_appTop_subschemeι_ofIdealTop
        (Ideal.ofList (List.ofFn cW))]
      exact Ideal.subset_span (List.mem_ofFn.mpr ⟨k, rfl⟩)
    have hfinal : (D.subschemeι.stalkMap t₀)
        (W.presheaf.germ ⊤ (D.subschemeι t₀) trivial (cW k)) = 0 := by
      rw [← Stacks.AlgebraicGeometry.germ_appTop_eq_stalkMap_germ D.subschemeι t₀ (cW k), happ,
        map_zero]
    exact hfinal

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback

/-!
# The inverse image of the ideal sheaf of a closed subspace, read on étale charts

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S` and
let `Z ⊆ X` be a closed subspace. Two sheaves of ideals are attached to `Z` on an étale scheme
chart `A` of `X`:

* the ideal sheaf `AlgebraicGeometry.Space.idealSheafDataOfChart` that the defining ideal sheaf
  `𝓘_Z ⊆ 𝒪_X` induces on the scheme underlying `A`, and
* the kernel of pullback of regular functions along the canonical base change `Z ×_X A ⟶ A`,
  which is a closed immersion of schemes.

They agree. Moreover, if `f : Y ⟶ X` is a morphism of algebraic spaces, `A` an étale chart of
`Y`, `A'` an étale chart of `X` and `g : A ⟶ A'` a morphism of the site lying over `f`, then the
inverse image along `g` of the chart ideal sheaf of `𝓘_Z` on `A'` is the chart ideal sheaf on `A`
of the defining ideal sheaf of the inverse image `f⁻¹(Z) ⊆ Y`. So the closed subspace `f⁻¹(Z)` of
`AlgebraicGeometry.Space.preimageClosedSubspace` realises, chart by chart, the inverse image of
the sheaf of ideals of `Z`.

## Main results

* `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`: the ideal sheaf that `𝓘_Z`
  induces on an étale chart is the ideal sheaf of the base change of `Z` to that chart.
* `AlgebraicGeometry.Space.comap_idealSheafDataOfChart_of_hom`: the inverse image of the chart
  ideal sheaf of `𝓘_Z` along a morphism of charts over `f : Y ⟶ X` is the chart ideal sheaf of
  the defining ideal sheaf of `f⁻¹(Z)`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- The map on sections induced by the inclusion of an open subscheme, from the sections over that
open to the global functions on it, is the inverse of `AlgebraicGeometry.Scheme.Opens.topIso`. -/
private theorem appLE_ι_top_eq_topIso_inv {X : Scheme.{u}} (V : X.Opens) :
    V.ι.appLE V ⊤ V.ι_preimage_self.ge = V.topIso.inv := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- Transporting an ideal of the sections over an open subscheme to the global functions on it
and back is the identity. -/
private theorem map_topIso_hom_map_topIso_inv {X : Scheme.{u}} (V : X.Opens)
    (I : Ideal Γ(X, V)) :
    Ideal.map (V.topIso.hom.hom) (Ideal.map (V.topIso.inv.hom) I) = I := by
  rw [Ideal.map_map,
    show (V.topIso.hom.hom).comp (V.topIso.inv.hom) = RingHom.id Γ(X, V) from
      congrArg CommRingCat.Hom.hom V.topIso.inv_hom_id,
    Ideal.map_id]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The ideal sheaf of a closed subspace on an étale chart -/

/-- The sheaf of ideals that the defining ideal sheaf of a closed subspace induces on an étale
chart is the ideal sheaf of the base change of that subspace to the chart: for a closed subspace
`Z ⊆ X` and an étale scheme chart `A` of `X`, taking the sections of `𝓘_Z` over the étale charts
cut out by the affine opens of `A` (`AlgebraicGeometry.Space.idealSheafDataOfChart`) agrees with
base changing the closed immersion `Z ⟶ X` along `A ⟶ X` and taking the kernel of pullback of
regular functions. -/
theorem ker_rep_snd_eq_idealSheafDataOfChart (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker =
      idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A := by
  refine Scheme.IdealSheafData.ext (funext fun V ↦ ?_)
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (openChart B S hS X.1 A V.1).1.left) := V.2
  have hTop : IsAffineOpen (⊤ : ((BigFppfOver.toScheme B S hS).obj
      (openChart B S hS X.1 A V.1).1.left).Opens) := isAffineOpen_top _
  have haff : ((BigFppfOver.toScheme B S hS).map
        (Z.2.2.rep.snd (openChart B S hS X.1 A V.1).1.hom)).ker =
      Scheme.IdealSheafData.ofIdealTop
        (definingIdealAt B S hS X Z (op (openChart B S hS X.1 A V.1))) :=
    ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS X Z (openChart B S hS X.1 A V.1)
  have hcomap : ((BigFppfOver.toScheme B S hS).map
        (Z.2.2.rep.snd (openChart B S hS X.1 A V.1).1.hom)).ker =
      (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker).comap V.1.ι := by
    have h := schemeKer_snd_comp B S hS Z A.1.hom (openSubHom A.1.left V.1)
    rwa [toScheme_map_openSubHom B S hS _ V.1] at h
  have hsec : definingIdealAt B S hS X Z (op (openChart B S hS X.1 A V.1)) =
      Ideal.map (V.1.topIso.inv.hom)
        ((((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker).ideal V) := by
    refine (Stacks.Divisors.ideal_ofIdealTop_top hTop _).symm.trans ?_
    refine (congrArg (fun J ↦ Scheme.IdealSheafData.ideal J ⟨⊤, hTop⟩)
      (haff.symm.trans hcomap)).trans ?_
    refine Eq.trans (Stacks.IdealSheaf.ideal_comap_appLE
      (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker) V.1.ι V
      ⟨⊤, hTop⟩ V.1.ι_preimage_self.ge) ?_
    exact congrArg (fun φ ↦ Ideal.map (CommRingCat.Hom.hom φ) _)
      (appLE_ι_top_eq_topIso_inv V.1)
  show (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker).ideal V =
    Ideal.map (openChartTopRingHom B S hS X A V.1)
      (definingIdealAt B S hS X Z (op (openChart B S hS X.1 A V.1)))
  rw [hsec]
  exact (map_topIso_hom_map_topIso_inv V.1 _).symm

/-! ### The inverse image along a morphism of algebraic spaces -/

variable {B S hS}

/-- Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S`, let `Z ⊆ X` be a closed subspace,
let `A` be an étale scheme chart of `Y`, let `A'` be an étale scheme chart of `X` and let `g` be a
morphism of the big fppf category over `S` from the scheme of `A` to the scheme of `A'` lying over
`f`. Then the inverse image along `g` of the sheaf of ideals that `𝓘_Z` induces on `A'` is the
sheaf of ideals that `𝓘_{f⁻¹(Z)}` induces on `A`. -/
theorem comap_idealSheafDataOfChart_of_hom {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS Y.1)
    (A' : SmallEtale B S hS X.1) (g : A.1.left ⟶ A'.1.left)
    (hg : yoneda.map g ≫ A'.1.hom = A.1.hom ≫ f.hom) :
    (idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A').comap
        ((BigFppfOver.toScheme B S hS).map g) =
      idealSheafDataOfChart B S hS Y
        (definingIdealSheaf B S hS Y (preimageClosedSubspace f Z))
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS Y
          (preimageClosedSubspace f Z)) A := by
  have key : ((BigFppfOver.toScheme B S hS).map
        ((preimageClosedSubspace f Z).2.2.rep.snd A.1.hom)).ker =
      (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A'.1.hom)).ker).comap
        ((BigFppfOver.toScheme B S hS).map g) := by
    have h := schemeKer_snd_preimage B S hS f Z A
    rwa [← hg, schemeKer_snd_comp B S hS Z A'.1.hom g] at h
  rw [← ker_rep_snd_eq_idealSheafDataOfChart B S hS Y (preimageClosedSubspace f Z) A,
    ← ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z A', key]

end Space

end AlgebraicGeometry

end

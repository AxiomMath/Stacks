module

public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierRangeOfEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ContainingDivisorFibre
public import StacksFrontier.AlgebraicGeometry.Divisors.PrincipalSlice
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FibrePrincipalDictionary

/-!
# Local regular equations of an effective Cartier divisor on a chart

Let `W` be a scheme of the big fppf site and `J` an effective Cartier divisor on `W`
(Stacks 01WR). Every point of `J` has, inside every open neighbourhood, an affine open
neighbourhood `A` on which `J` is cut out by a single nonzerodivisor. This is the local input of
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_range_of_etaleChart` (Stacks 083C,
condition (4)), written in the form that lemma asks for: an open subobject `A ⟶ W` of the site,
the fibre product `P ×_W A` of the site, and an isomorphism of it with the closed subscheme of
`A` cut out by the equation.

Combined with that lemma: if `e : W ⟶ X` is an étale chart of an algebraic space and
`P ⟶ W` is the closed subscheme of an effective Cartier divisor on `W` whose composite to `X`
is a closed immersion, then the range of `P ⟶ X` is an effective Cartier divisor on `X`
(Stacks 083B). This is how a divisor of an étale chart of a family of curves becomes a divisor of
the family, in the proof that families of curves are étale locally schemes (Stacks 0E6F).

## Main results

* `AlgebraicGeometry.Space.exists_regular_equation_of_isEffectiveCartierDivisor`: the local
  equations.
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_range_of_etaleChart_of_ideal`: the range of
  a closed immersion through an étale chart which is an effective Cartier divisor on the chart.

## References

* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

open Stacks.Divisors in
/-- **Local regular equations of an effective Cartier divisor on a scheme of the site.** Let
`J` be an effective Cartier divisor on the scheme of `W`, and `j : P ⟶ W` a morphism of the site
identified with the closed immersion of `J` by an isomorphism `ε`. For every point `v` of `P` and
every open `O` of `W` containing `j(v)` there are an open subobject `ι : A ⟶ W` of the site with
`A` affine, contained in `O` and through `j(v)`, and a nonzerodivisor `f` on `A` such that the
fibre product `P ×_W A` of the site is the closed subscheme of `A` cut out by `f`. -/
theorem exists_regular_equation_of_isEffectiveCartierDivisor {W P : BigFppfOver B S hS}
    (j : P ⟶ W) (J : ((𝒯).obj W).IdealSheafData) (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
    (ε : (𝒯).obj P ≅ J.subscheme) (hε : (𝒯).map j = ε.hom ≫ J.subschemeι)
    (v : (𝒯).obj P) (O : ((𝒯).obj W).Opens) (hvO : (𝒯).map j v ∈ O) :
    ∃ (U R : BigFppfOver B S hS) (ι : U ⟶ W) (r : R ⟶ P) (k : R ⟶ U) (w : (𝒯).obj U),
      _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map ι) ∧ IsAffine ((𝒯).obj U) ∧
      Set.range ((𝒯).map ι) ⊆ O ∧ (𝒯).map ι w = (𝒯).map j v ∧ IsPullback r k j ι ∧
      ∃ (f : Γ((𝒯).obj U, ⊤))
        (iso : (𝒯).obj R ≅ (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subscheme),
        IsRegular f ∧ (𝒯).map k =
          iso.hom ≫ (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι := by
  set x := (𝒯).map j v
  -- `J` restricted to `O` is an effective Cartier divisor, being a flat pullback
  have hJO : Stacks.Divisors.IsEffectiveCartierDivisor (J.comap O.ι) :=
    isPullbackDefined_of_flat O.ι J hJ
  obtain ⟨A, hA, hxA, hAO, b, hb, hJA⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor_comap J hJO x hvO
  have : IsAffine A.toScheme := hA
  have hcA : B.Contains A.toScheme :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B A.ι W.left.property
  let U : BigFppfOver B S hS := BigFppfOver.siteObjectOver B S hS W hcA A.ι
  let ι : U ⟶ W := BigFppfOver.siteMapOver B S hS W hcA A.ι
  have hι : (𝒯).map ι = A.ι := rfl
  -- the equation on `A`
  have hT : IsAffineOpen (⊤ : A.toScheme.Opens) := isAffineOpen_top A.toScheme
  set f : Γ(A.toScheme, ⊤) := A.topIso.inv.hom b with hf
  have hfreg : IsRegular f :=
    Stacks.Divisors.isRegular_ringEquiv A.topIso.symm.commRingCatIsoToRingEquiv hb
  have hcomap : J.comap A.ι = Scheme.IdealSheafData.ofIdealTop (Ideal.span {f}) := by
    refine Scheme.IdealSheafData.ext_of_isAffine ?_
    rw [Stacks.IdealSheaf.ideal_comap_ι_top J hA hT, hJA, Ideal.map_span, Set.image_singleton,
      Scheme.IdealSheafData.ofIdealTop_ideal,
      show (homOfLE (le_top (a := (⊤ : A.toScheme.Opens)))) = 𝟙 _ from rfl]
    simp only [CategoryTheory.op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id,
      Ideal.map_id, hf]
  have hcomap' : J.comap ((𝒯).map ι) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {(f : Γ((𝒯).obj U, ⊤))}) := hcomap
  -- the fibre product of the site and its image square of schemes
  have sq := (IsPullback.of_hasPullback j ι).map (𝒯)
  have sq' : IsPullback ((𝒯).map (pullback.snd j ι)) ((𝒯).map (pullback.fst j ι) ≫ ε.hom)
      ((𝒯).map ι) J.subschemeι :=
    IsPullback.of_iso sq.flip (Iso.refl _) (Iso.refl _) ε (Iso.refl _) (by simp) (by simp)
      (by simp) (by simpa using hε)
  have key : ∀ I : ((𝒯).obj U).IdealSheafData, J.comap ((𝒯).map ι) = I →
      ∃ iso : (𝒯).obj (pullback j ι) ≅ I.subscheme,
        (𝒯).map (pullback.snd j ι) = iso.hom ≫ I.subschemeι := by
    rintro I rfl
    refine ⟨sq'.isoPullback ≪≫ (J.comapIso ((𝒯).map ι)).symm, ?_⟩
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      ← Scheme.IdealSheafData.comapIso_hom_fst J ((𝒯).map ι), Iso.inv_hom_id_assoc,
      IsPullback.isoPullback_hom_fst]
  obtain ⟨iso, hiso⟩ := key _ hcomap'
  refine ⟨U, pullback j ι, ι, pullback.fst j ι, pullback.snd j ι, ⟨x, hxA⟩, ?_, hA, ?_, rfl,
    IsPullback.of_hasPullback j ι, f, iso, hfreg, hiso⟩
  · show _root_.AlgebraicGeometry.IsOpenImmersion A.ι; infer_instance
  · show Set.range A.ι ⊆ O; rw [Scheme.Opens.range_ι]; exact hAO

open Stacks.Divisors in
/-- **The range of a closed immersion through an étale chart which is an effective Cartier divisor
on the chart.** Let `e : W ⟶ X` be an étale morphism from a scheme of the site to an algebraic
space and `j : P ⟶ W` a morphism of the site identified with the closed immersion of an effective
Cartier divisor `J` on `W`. If `P ⟶ W ⟶ X` is a closed immersion, its range is an effective
Cartier divisor on `X` (Stacks 083B). -/
theorem isEffectiveCartierDivisor_range_of_etaleChart_of_ideal
    {X : AlgebraicSpaces B S hS} {W P : BigFppfOver B S hS} (e : yoneda.obj W ⟶ X.1)
    (he : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf e) (j : P ⟶ W)
    (hπ : IsClosedImmersion B S hS (yoneda.map j ≫ e))
    (J : ((𝒯).obj W).IdealSheafData) (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
    (ε : (𝒯).obj P ≅ J.subscheme) (hε : (𝒯).map j = ε.hom ≫ J.subschemeι) :
    Space.IsEffectiveCartierDivisor B S hS X
      ⟨Subfunctor.range (yoneda.map j ≫ e), isClosedSubspace_range_of_isClosedImmersion B S hS _
        (isAlgebraicSpace_yoneda B S hS P) hπ⟩ :=
  isEffectiveCartierDivisor_range_of_etaleChart e he j hπ fun v O hvO =>
    exists_regular_equation_of_isEffectiveCartierDivisor j J hJ ε hε v O hvO

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RepresentableConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Thickenings.Transitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Comp
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified

/-!
# Universal first-order thickenings of representable algebraic spaces are scheme-theoretic

Let `T` and `U` be objects of the big fppf site over a scheme `S`, let `Z ⊆ h_T` be a closed
subspace of the algebraic space represented by `T`, with representing scheme `Z₀` and closed
immersion `j : Z₀ ⟶ T`, and let `r : T ⟶ U` be a morphism of the site.  If `Z ⊂ h_T` is a
universal first-order thickening of `Z` over `h_U`, in the sense of Stacks 0602 for algebraic
spaces, then `j : Z₀ ⟶ T` is a universal first-order thickening of `Z₀` over `U` in the sense
of schemes.

The morphism `Z₀ ⟶ U` is formally unramified, being a closed immersion followed by the structure
morphism of a universal first-order thickening, which is formally unramified by Stacks 0609.
The scheme-level universal first-order thickening of `Z₀ ⟶ U` lies in the site
(`AlgebraicGeometry.Space.siteThickeningObj`) and represents a universal first-order thickening
of algebraic spaces; the two space-level thickenings are canonically isomorphic, so the
isomorphism is represented by an isomorphism of schemes over `U` carrying one inclusion to the
other, and the universal property of schemes transports along it.

## Main results

* `Stacks.Thickenings.IsUniversalFirstOrderThickening.comp_iso`: the universal property of
  schemes transports along an isomorphism of the ambient scheme.
* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_representedClosedHom`: the
  statement.

## References

* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0609](https://stacks.math.columbia.edu/tag/0609)
* [Stacks Project, Tag 04EW](https://stacks.math.columbia.edu/tag/04EW)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Thickenings

/-- **The universal property of a first-order thickening transports along an isomorphism of
the ambient scheme.** -/
theorem IsUniversalFirstOrderThickening.comp_iso {Z X A A' : Scheme.{u}} {h : Z ⟶ X}
    {i : Z ⟶ A} {p : A ⟶ X} (hu : IsUniversalFirstOrderThickening h i p) (e : A ≅ A') :
    IsUniversalFirstOrderThickening h (i ≫ e.hom) (e.inv ≫ p) where
  isFirstOrderThickening :=
    IsFirstOrderThickening.of_comp_mono (i ≫ e.hom) e.inv
      (by simpa using hu.isFirstOrderThickening)
  inclusion_toBase := by simpa using hu.inclusion_toBase
  existsUnique_lift := by
    intro T T' j hj a b hab
    obtain ⟨c, ⟨hc₁, hc₂⟩, hc⟩ := hu.existsUnique_lift j hj a b hab
    refine ⟨c ≫ e.hom, ⟨by rw [← Category.assoc, hc₁, Category.assoc], by simpa using hc₂⟩,
      fun c' ⟨h₁, h₂⟩ => ?_⟩
    have := hc (c' ≫ e.inv) ⟨by rw [← Category.assoc, h₁]; simp, by simpa using h₂⟩
    rw [← this]
    simp

end Stacks.Thickenings

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A universal first-order thickening of algebraic spaces with representable ambient space is
a universal first-order thickening of schemes.**  Let `Z ⊆ h_T` be a closed subspace, with
representing scheme `Z₀` and closed immersion `j : Z₀ ⟶ T`, which is a universal first-order
thickening of `Z` over `h_U` for a morphism `r : T ⟶ U`.  Then `j` is a universal first-order
thickening of `Z₀` over `U`. -/
theorem isUniversalFirstOrderThickening_representedClosedHom {T U : BigFppfOver B S hS}
    (Zc : ClosedSubspaces B S hS (yoneda.obj T)) (r : T ⟶ U)
    (hU : IsUniversalFirstOrderThickening B S hS Zc.1 (schemeSpaceMap r)) :
    Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T Zc ≫ r))
      ((BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T Zc))
      ((BigFppfOver.toScheme B S hS).map r) := by
  -- `Z₀ ⟶ U` is formally unramified: a closed immersion followed by the formally unramified
  -- structure morphism of a universal first-order thickening (Stacks 0609)
  have hmono : Mono (yoneda.map (representedClosedHom B S hS T Zc)) := by
    rw [yoneda_map_representedClosedHom]
    have : IsIso (Zc.2.2.rep.fst (idEtaleChart B S hS T).1.hom) :=
      isIso_representedClosedMap_hom B S hS T Zc
    have : Mono (Zc.2.2.rep.fst (idEtaleChart B S hS T).1.hom) := IsIso.mono_of_iso _
    exact mono_comp (Zc.2.2.rep.fst (idEtaleChart B S hS T).1.hom) Zc.1.ι
  have hfu' : FormallyUnramified
      ((schemeSpaceFunctor B S hS).map (representedClosedHom B S hS T Zc ≫ r)).hom := by
    change FormallyUnramified (yoneda.map (representedClosedHom B S hS T Zc ≫ r))
    rw [yoneda.map_comp]
    exact formallyUnramified_comp _ _
      (formallyUnramified_of_mono (yoneda.map (representedClosedHom B S hS T Zc)))
      (formallyUnramified_of_isUniversalFirstOrderThickening B S hS Zc.1 (schemeSpaceMap r) hU)
  have : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T Zc ≫ r)) :=
    formallyUnramified_map_of_formallyUnramified B S hS _ hfu'
  -- the space-level thickening in hand
  let s : UniversalFirstOrderThickening B S hS
      ((schemeSpaceFunctor B S hS).map (representedClosedHom B S hS T Zc ≫ r)) :=
    { formallyUnramified := hfu'
      ambient := schemeSpace T
      toBase := schemeSpaceMap r
      sub := Zc.1
      isUniversal := hU
      sourceIso := @asIso _ _ _ _ (representedClosedMap B S hS T Zc).hom
        (isIso_representedClosedMap_hom B S hS T Zc)
      sourceIso_ι_toBase := by
        change (Zc.2.2.rep.fst (idEtaleChart B S hS T).1.hom ≫ Zc.1.ι) ≫ yoneda.map r = _
        rw [← yoneda_map_representedClosedHom]
        exact (yoneda.map_comp _ _).symm }
  have ht := isUniversal_siteThickening B S hS (representedClosedHom B S hS T Zc ≫ r)
  have hres := UniversalFirstOrderThickening.representedAmbientIso_restrict s _ _ ht
  have hover := UniversalFirstOrderThickening.representedAmbientIso_over s _ _ ht
  -- the isomorphism of ambient spaces is represented by an isomorphism of the site
  let E : T ≅ siteThickeningObj B S hS (representedClosedHom B S hS T Zc ≫ r) :=
    Functor.FullyFaithful.preimageIso Yoneda.fullyFaithful
      ((ObjectProperty.ι _).mapIso (UniversalFirstOrderThickening.representedAmbientIso s _ _ ht))
  have hE : yoneda.map E.hom =
      (UniversalFirstOrderThickening.representedAmbientIso s _ _ ht).hom.hom :=
    Yoneda.fullyFaithful.map_preimage _
  have h₁ : representedClosedHom B S hS T Zc ≫ E.hom =
      siteThickeningInclusion B S hS (representedClosedHom B S hS T Zc ≫ r) := by
    have := isIso_representedClosedMap_hom B S hS T Zc
    have key := congrArg (fun m => (representedClosedMap B S hS T Zc).hom ≫ m) hres
    have l : (representedClosedMap B S hS T Zc).hom ≫ (s.sub.ι ≫
        (UniversalFirstOrderThickening.representedAmbientIso s _ _ ht).hom.hom) =
        yoneda.map (representedClosedHom B S hS T Zc ≫ E.hom) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (yoneda_map_representedClosedHom B S hS T Zc).symm).trans
        ((congrArg (yoneda.map (representedClosedHom B S hS T Zc) ≫ ·) hE.symm).trans
          (yoneda.map_comp _ _).symm))
    have r : (representedClosedMap B S hS T Zc).hom ≫
        (UniversalFirstOrderThickening.subComparison s
          (UniversalFirstOrderThickening.ofSite s.formallyUnramified _ _ ht) ≫
          (UniversalFirstOrderThickening.ofSite s.formallyUnramified _ _ ht).sub.ι) =
        yoneda.map (siteThickeningInclusion B S hS (representedClosedHom B S hS T Zc ≫ r)) :=
      (congrArg ((representedClosedMap B S hS T Zc).hom ≫ ·) (Category.assoc _ _ _)).trans
        ((IsIso.hom_inv_id_assoc _ _).trans (Subfunctor.toRange_ι _))
    exact yoneda.map_injective (l.symm.trans (key.trans r))
  have h₂ : E.hom ≫ siteThickeningToBase B S hS (representedClosedHom B S hS T Zc ≫ r) = r :=
    yoneda.map_injective (by rw [yoneda.map_comp, hE]; exact congrArg (fun f => f.hom) hover)
  have hu := Stacks.Thickenings.IsUniversalFirstOrderThickening.comp_iso ht
    ((BigFppfOver.toScheme B S hS).mapIso E).symm
  have h₁' : (BigFppfOver.toScheme B S hS).map
        (siteThickeningInclusion B S hS (representedClosedHom B S hS T Zc ≫ r)) ≫
      ((BigFppfOver.toScheme B S hS).mapIso E).symm.hom =
      (BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T Zc) := by
    rw [Iso.symm_hom, Functor.mapIso_inv, ← Functor.map_comp, ← h₁, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have h₂' : ((BigFppfOver.toScheme B S hS).mapIso E).symm.inv ≫
      (BigFppfOver.toScheme B S hS).map
        (siteThickeningToBase B S hS (representedClosedHom B S hS T Zc ≫ r)) =
      (BigFppfOver.toScheme B S hS).map r := by
    rw [Iso.symm_inv, Functor.mapIso_hom, ← Functor.map_comp, h₂]
  rwa [h₁', h₂'] at hu

end AlgebraicGeometry.Space

end

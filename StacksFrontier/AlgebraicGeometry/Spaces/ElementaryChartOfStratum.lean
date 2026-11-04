module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartKernelPair

/-!
# The elementary chart of a stratum of Stacks 07ST

Stacks 07ST (`AlgebraicGeometry.Space.exists_finiteFiltration_of_isQuasiCompactSpace`) gives,
for every stratum `U_p ⊇ U_{p+1}` of a quasi-compact quasi-separated algebraic space, a scheme
`V_p` with a surjective étale morphism `f_p : V_p ⟶ U_p` which is an isomorphism over the
reduced closed complement `T_p` of `U_{p+1}`. This file packages such data as an
`AlgebraicGeometry.Space.ElementaryChart`: the kernel pair of `f_p` and the inverse image
`W = f_p⁻¹(U_{p+1})` are represented by objects of the site, the latter with an open immersion
into `V_p`. This is step (e) of the proof of absolute Noetherian approximation, Stacks 07SU:
"`W = f^{-1}(U) ⊂ V` is a quasi-compact open subscheme étale over `U`".

## Main definitions

* `AlgebraicGeometry.Space.ElementaryChart.ofStratum`: the elementary chart of a surjective
  étale morphism from an object of the site which is an isomorphism over a closed subspace
  complementary to an open subspace.

## References

* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ElementaryChart

/-- **Step (e) of Stacks 07SU: the elementary chart of a stratum.** A surjective étale morphism
`f : V ⟶ X` from an object of the site, an open subspace `U ⊆ X` and a closed subspace `T ⊆ X`
whose points are the complement of those of `U`, over which `f` is an isomorphism. The kernel
pair of `f` is represented through the representability of `f`, and `W = f⁻¹(U)` through that of
the open immersion `U ⟶ X`. -/
noncomputable def ofStratum {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (het : IsEtale B S hS f) (U T : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hT : IsClosedSubspace B S hS T)
    (hrange : Set.range (pointsMap B S hS T.toFunctor T.ι) =
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ)
    (hiso : IsIso (pullback.fst T.ι f)) : ElementaryChart X V where
  f := f
  etale_f := presheaf_etale_of_isEtale B S hS het
  R := hsurj.rep.pullback f
  s := hsurj.rep.fst' f
  t := hsurj.rep.snd f
  isPullback := hsurj.rep.isPullback' f
  U := U
  W := hU.2.rep.pullback f
  j := hU.2.rep.snd f
  isOpenImmersion_j := hU.2.property_snd f
  p := hU.2.rep.fst f
  isPullback_W := (hU.2.rep.isPullback f).flip
  T := T
  range_T := hrange
  rep_T := hT.2.rep
  isIso_fst := hiso

end ElementaryChart

end AlgebraicGeometry.Space

end

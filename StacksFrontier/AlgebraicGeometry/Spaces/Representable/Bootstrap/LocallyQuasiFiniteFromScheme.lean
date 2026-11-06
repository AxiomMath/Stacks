module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria

/-!
# Locally quasi-finite morphisms out of a scheme are representable

Let `S` be a scheme contained in a big fppf site `B`, let `F` be a presheaf of sets on the big
fppf site of `S`, and let `X` be an object of that site — a scheme over `S`. A morphism
`a : h_X ⟶ F` which is representable by algebraic spaces and locally quasi-finite is
representable by *schemes*.

The input is Stacks 03XX, representability of a separated locally quasi-finite algebraic space
over a representable one. What this file supplies is the separatedness: because the source of
`a` is representable, each fibre product `h_U ×_F h_X` sits inside the absolute product
`h_{X ⨯ U}` of the site, the comparison morphism being a monomorphism, and a monomorphism is
separated. Local quasi-finiteness of the comparison follows from local quasi-finiteness of the
projection to `h_U`, which the hypothesis on `a` provides, by cancellation (Stacks 03XN).

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_of_isLocallyQuasiFinite_of_schemeSource`:
  **Stacks 0AHV**.

## Implementation notes

The source of `a` is a representable presheaf rather than an arbitrary algebraic space, which
is what makes the comparison into the absolute product available; the statement is therefore
phrased for `a : yoneda.obj X ⟶ F` with `X` an object of the site, matching the source's
hypothesis that `X` is a scheme over `S`. No hypothesis is placed on `F` beyond the two the
source makes on `a`: that it is representable by algebraic spaces and that it is locally
quasi-finite in the sense of Stacks 03XZ, i.e. `AlgebraicGeometry.Space.HasProperty` applied
to local quasi-finiteness of morphisms of algebraic spaces over `S`.

The source's proof forms `X ×_{Spec ℤ} T`; here the absolute product is taken in the site
`AlgebraicGeometry.BigFppfOver B S hS`, whose terminal object is `S` itself, so the product
used is `X ×_S T`. The two differ, but only the monomorphy and the local quasi-finiteness of
the comparison are used, and both hold for the product over any base through which the two
morphisms to `F` factor.

## References

* [Stacks Project, Tag 0AHV](https://stacks.math.columbia.edu/tag/0AHV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
instance hasPullbacks_presheaf_LocallyQuasiFiniteFromScheme (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_LocallyQuasiFiniteFromScheme
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Binary products of presheaves on the big fppf site (instance search times out without
this shortcut). -/
instance (priority := high) hasBinaryProducts_presheaf_LocallyQuasiFiniteFromScheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasBinaryProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- The comparison from a fibre product to the product of its two factors, taken in the order
opposite to the one the fibre product is written in, is a monomorphism: a pair of morphisms
into the fibre product agreeing after both projections agree. -/
private theorem mono_prodLift_pullback_swap {C : Type w} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasBinaryProduct Y X] :
    Mono (prod.lift (pullback.snd f g) (pullback.fst f g)) :=
  ⟨fun _ _ h => pullback.hom_ext (by simpa using h =≫ prod.snd)
    (by simpa using h =≫ prod.fst)⟩

/-- **Stacks 0AHV.** Let `F` be a presheaf of sets on the big fppf site of `S` and let `X` be a
scheme over `S`, that is an object of the site. A morphism `a : h_X ⟶ F` which is representable
by algebraic spaces and locally quasi-finite is representable by schemes.

The hypothesis of local quasi-finiteness is the one of Stacks 03XZ: every base change of `a`
along a scheme-valued point of `F` is a locally quasi-finite morphism of algebraic spaces
over `S`. -/
@[stacks 0AHV]
theorem relativelyRepresentable_of_isLocallyQuasiFinite_of_schemeSource
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : BigFppfOver B S hS) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (a : yoneda.obj X ⟶ F)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hlqf : HasProperty B S hS
      (fun ⦃_ _⦄ φ => IsLocallyQuasiFinite B S hS φ.hom) a ha) :
    yoneda.relativelyRepresentable a := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  rw [yoneda_relativelyRepresentable_iff_pullback_representable]
  intro U ξ₀
  set ξ : yoneda.obj U ⟶ F := yonedaEquiv.symm ξ₀ with hξ
  have hP : IsAlgebraicSpace B S hS (pullback ξ a) := ha U ξ
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hV : IsAlgebraicSpace B S hS (yoneda.obj (X ⨯ U)) :=
    isAlgebraicSpace_yoneda B S hS (X ⨯ U)
  -- The comparison of the fibre product `h_U ×_F h_X` with the absolute product `h_{X ⨯ U}`.
  have hcmono : Mono (prod.lift (pullback.snd ξ a) (pullback.fst ξ a)) :=
    mono_prodLift_pullback_swap ξ a
  set f : pullback ξ a ⟶ yoneda.obj (X ⨯ U) :=
    prod.lift (pullback.snd ξ a) (pullback.fst ξ a) ≫ (PreservesLimitPair.iso yoneda X U).inv
      with hf
  have hfmono : Mono f := by
    rw [hf]; exact mono_comp' hcmono (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_inv _))
  -- It is a factorisation of the projection to `h_U`, hence locally quasi-finite.
  have hfsnd : f ≫ yoneda.map prod.snd = pullback.fst ξ a := by
    rw [hf, Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]
  have hfcomp : IsLocallyQuasiFinite B S hS (f ≫ yoneda.map prod.snd) := by
    rw [hfsnd]; exact hlqf U ξ
  have hfqf : IsLocallyQuasiFinite B S hS f :=
    isLocallyQuasiFinite_of_comp B S hS hP hV hU f (yoneda.map prod.snd) hfcomp
  exact isRepresentable_of_locallyQuasiFinite_separated B S hS _ _ hP hV f inferInstance hfqf
    (isSeparated_of_mono f hfmono)

end AlgebraicGeometry.Space

end

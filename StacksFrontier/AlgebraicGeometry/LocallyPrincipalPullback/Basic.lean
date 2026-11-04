module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap

/-!
# Pullback of locally principal closed subschemes

The scheme-theoretic inverse image of a locally principal closed subscheme under any morphism
of schemes is locally principal.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Divisors.isLocallyPrincipal_comap` states that pulling back the defining ideal sheaf
  preserves local principality.

## Implementation notes

Closed subschemes are represented by their ideal sheaf data. The inverse image under a scheme
morphism is `AlgebraicGeometry.Scheme.IdealSheafData.comap`; its associated closed subscheme is
canonically isomorphic to the fibre product by
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`.

The source leaves the proof to the reader. It is affine-local: around a point `x` choose an
affine open `U ∋ f x` on which the ideal of `I` is principal, then an affine open `V ∋ x` inside
`f⁻¹ U`; the restricted morphism `V → U` is a morphism of affine schemes, so
`Stacks.IdealSheaf.ideal_comap_top_of_isAffine` identifies the ideal of the inverse image on `V`
with the image of the ideal on `U`, and the image of a principal ideal is principal. The two
`HEq` transports are needed because the ideal of an inverse image is indexed by the affine opens
of the *restricted* scheme, whose ring of global sections is equal — but not syntactically equal
— to the sections over the corresponding open of the ambient scheme.

## References

* [Stacks Project, Tag 053P](https://stacks.math.columbia.edu/tag/053P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.Divisors

/-- The image of a principal ideal along a ring map is principal. -/
private lemma isPrincipal_map {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (J : Ideal R) (hJ : J.IsPrincipal) :
    (J.map φ).IsPrincipal := by
  obtain ⟨a, rfl⟩ := hJ
  exact ⟨φ a, by rw [Ideal.map_span, Set.image_singleton]⟩

/-- Principality transports along an equality of carrier rings together with a heterogeneous
equality of ideals. -/
private lemma isPrincipal_heq {A B : CommRingCat.{u}} (hAB : A = B)
    {J : Ideal A} {K : Ideal B} (hJK : HEq J K)
    (hJ : J.IsPrincipal) : K.IsPrincipal := by
  cases hAB
  simpa only [eq_of_heq hJK] using hJ

/-- The ring of global sections of an open subscheme is the ring of sections over the open. -/
private lemma Gamma_top_toScheme_eq {X : Scheme.{u}} (U : X.Opens) :
    Γ(U.toScheme, ⊤) = Γ(X, U) := by
  change Γ(X, (Scheme.Hom.opensFunctor U.ι).obj ⊤) = Γ(X, U)
  rw [Scheme.Opens.ι_image_top]

/-- **Stacks Project, Tag 053P.** The inverse image of a locally principal closed subscheme is
locally principal. -/
@[stacks 053P]
theorem isLocallyPrincipal_comap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData)
    (hI : IsLocallyPrincipal I) :
    IsLocallyPrincipal (I.comap f) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hI (f x)
  change f x ∈ U.1 at hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ U.1 from hxU) (f ⁻¹ᵁ U.1).isOpen
  let V' : X.affineOpens := ⟨V, hV⟩
  have hVU' : V ≤ f ⁻¹ᵁ U.1 := hVU
  let g : Scheme.Opens.toScheme V ⟶ U.1.toScheme := f.resLE U.1 V hVU'
  have hcomp : (I.comap f).comap (Scheme.Opens.ι V) = (I.comap U.1.ι).comap g := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      show g ≫ U.1.ι = _ from Scheme.Hom.resLE_comp_ι f hVU']
  have : IsAffine (Scheme.Opens.toScheme V) := hV
  have : IsAffine U.1.toScheme := U.2
  have hbaseP : ((I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩).IsPrincipal :=
    isPrincipal_heq (Gamma_top_toScheme_eq U.1).symm (ideal_comap_top_heq I U).symm hU
  have htarget := ideal_comap_top_heq (I.comap f) V'
  rw [hcomp] at htarget
  have hlocal :
      (((I.comap U.1.ι).comap g).ideal ⟨⊤,
        isAffineOpen_top (Scheme.Opens.toScheme V)⟩).IsPrincipal := by
    rw [Stacks.IdealSheaf.ideal_comap_top_of_isAffine (I.comap U.1.ι) g]
    exact isPrincipal_map g.appTop.hom _ hbaseP
  exact ⟨V', hxV, isPrincipal_heq (Gamma_top_toScheme_eq V) htarget hlocal⟩

end Stacks.Divisors

end

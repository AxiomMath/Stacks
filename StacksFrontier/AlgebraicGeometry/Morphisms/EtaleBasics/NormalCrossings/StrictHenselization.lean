module

public import StacksFrontier.AlgebraicGeometry.Etale.NormalCrossings.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.WeaklyEtalePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.StalkStrictHenselization
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes

/-!
# Normal crossings divisors become strict after strict henselization

Let `D` be a normal crossings divisor on a locally Noetherian scheme `X` and let `x` be a point of
`D`. The pullback of `D` to the spectrum of a strict henselization of the local ring `𝒪_{X, x}` is
a strict normal crossings divisor. This is the forward implication of the characterization of
normal crossings divisors by their strict henselizations.

## Main results

* `Stacks.Divisors.spec_map_comp_fromSpecStalk_comp_eq`: a morphism out of the spectrum of a ring
  receiving the local ring of `U` at `q` agrees, after composing to `X`, with the morphism built
  from the compatible structure map of `𝒪_{X, g q}`.
* `Stacks.Divisors.isStrictNormalCrossingsDivisor_comap_fromSpecStalk_of_isNormalCrossingsDivisor`:
  the pullback of a normal crossings divisor to the spectrum of a strict henselization of a local
  ring at a point of the divisor has strict normal crossings.

## Implementation notes

An étale neighbourhood `g : U ⟶ X` of `x` on which `D` already has strict normal crossings is
furnished by the definition of a normal crossings divisor; a strict henselization `Ash` of
`𝒪_{X, x}` is also one of `𝒪_{U, q}` for a lift `q` of `x`, so `Spec Ash` maps to `U` over `X`,
weakly étale-ly because `𝒪_{U, q} → Ash` is ind-étale and `𝒪_U → 𝒪_{U, q}` is a localization.
Weakly étale pullback then preserves strict normal crossings.

## References

* [Stacks Project, Tag 0CBS](https://stacks.math.columbia.edu/tag/0CBS)
* [Stacks Project, Tag 0CBP](https://stacks.math.columbia.edu/tag/0CBP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- A morphism out of the spectrum of a ring receiving the local ring of `U` at `q` agrees, after
composing to `X`, with the morphism built from the compatible structure map of `𝒪_{X, g q}`. -/
private theorem spec_map_comp_fromSpecStalk_comp {U X : Scheme.{u}} (g : U ⟶ X) (q : U)
    {R : CommRingCat.{u}} (b : U.presheaf.stalk q ⟶ R) (a : X.presheaf.stalk (g q) ⟶ R)
    (hcomp : g.stalkMap q ≫ b = a) :
    Spec.map b ≫ U.fromSpecStalk q ≫ g = Spec.map a ≫ X.fromSpecStalk (g q) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk (f := g) (x := q), ← Category.assoc,
    ← Spec.map_comp, ← hcomp, Spec.map_comp]

/-- **A morphism out of the spectrum of a ring receiving the local ring of `U` at `q` agrees,
after composing to `X`, with the morphism built from the compatible structure map of
`𝒪_{X, g q}`.**  Both morphisms are the one induced by the compatible pair, read through
`AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk`. -/
public alias spec_map_comp_fromSpecStalk_comp_eq := spec_map_comp_fromSpecStalk_comp

/-- **The strict henselization of a normal crossings divisor has strict normal crossings.** For `D`
a normal crossings divisor on a locally Noetherian scheme `X` and `x` a point of `D`, the pullback
of `D` to the spectrum of a strict henselization of `𝒪_{X, x}` is a strict normal crossings
divisor. -/
@[stacks 0CBS "(1) ⇒ (2)"]
theorem isStrictNormalCrossingsDivisor_comap_fromSpecStalk_of_isNormalCrossingsDivisor
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : IsNormalCrossingsDivisor D) (x : X) (hx : ∃ y : D.subscheme, D.subschemeι y = x)
    (L : Type u) [Field L]
    [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) L]
    [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) L]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash]
    [Algebra (X.presheaf.stalk x) Ash]
    [IsLocalRing.IsHenselization (X.presheaf.stalk x) L Ash] :
    haveI : IsNoetherianRing Ash :=
      IsLocalRing.isNoetherianRing_of_isHenselization (A := X.presheaf.stalk x) L
    IsStrictNormalCrossingsDivisor (D.comap
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Ash)) ≫
        X.fromSpecStalk x)) := by
  have : IsNoetherianRing Ash :=
    IsLocalRing.isNoetherianRing_of_isHenselization (A := X.presheaf.stalk x) L
  obtain ⟨y, hy⟩ := hx
  obtain ⟨U, g, hU, hg, ⟨q, hq⟩, hE⟩ := hD.2 y
  have hgx : g q = x := hq.trans hy
  subst hgx
  let := hU
  have := hg
  let : Algebra (X.presheaf.stalk (g q)) (U.presheaf.stalk q) := (g.stalkMap q).hom.toAlgebra
  obtain ⟨algB, algκ, htower, hlocal, hsc, hH⟩ :=
    AlgebraicGeometry.exists_isHenselization_stalk_of_etale g q L Ash
  let := algB
  let := algκ
  have := htower
  have := hlocal
  have := hH
  have hwe : Algebra.WeaklyEtale (U.presheaf.stalk q) Ash :=
    Algebra.weaklyEtale_of_ind_etale
      (IsLocalRing.IsHenselization.ind_etale (R := U.presheaf.stalk q) (L := L) (Rh := Ash))
  have : WeaklyEtale
      (Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk q) Ash))) := by
    refine weaklyEtale_specMap _ ?_
    have he : (CommRingCat.ofHom (algebraMap (U.presheaf.stalk q) Ash)).hom.toAlgebra = algB :=
      Algebra.algebra_ext _ _ fun _ => rfl
    exact he ▸ hwe
  have := weaklyEtale_fromSpecStalk U q
  have hglue : Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk q) Ash)) ≫
      U.fromSpecStalk q ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (g q)) Ash)) ≫
        X.fromSpecStalk (g q) := by
    refine spec_map_comp_fromSpecStalk_comp g q _ _ (CommRingCat.hom_ext (RingHom.ext fun z => ?_))
    exact (IsScalarTower.algebraMap_apply (X.presheaf.stalk (g q)) (U.presheaf.stalk q) Ash z).symm
  have key := isStrictNormalCrossingsDivisor_comap_comp_of_weaklyEtale g
    (Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk q) Ash)) ≫ U.fromSpecStalk q) D hE
  rw [Category.assoc, hglue] at key
  exact key

end Stacks.Divisors

end

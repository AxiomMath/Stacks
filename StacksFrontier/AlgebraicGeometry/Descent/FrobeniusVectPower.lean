module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundles
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPullback

/-!
# Iterated Frobenius pullback of vector bundles and the Frobenius factorisation

Let `p` be a prime and `X` a scheme in characteristic `p`. Iterating pullback along the
absolute Frobenius `N` times is the same as restricting along the `N`-fold absolute Frobenius
`F^N`, and on an affine scheme `X = Spec A` the latter is restriction along `Spec` of the
`p ^ N`-power endomorphism of `A`. The point of this identification is the Frobenius
factorisation of Stacks Example 0EVG: when `f ^ n` annihilates `J` and `n + 1 ≤ p ^ N`, the
`p ^ N`-power map of `A` factors through `A ⧸ (J ⊓ fA)`
(`MilnorPatching.OneGeneratorFrobenius.betaHom`), so the `N`-fold Frobenius pullback of a
vector bundle on `Spec A` is restricted from the exceptional corner of the one-generator
square.

To say any of that one needs pullback of vector bundles to be pseudofunctorial, which this
file also supplies: `AlgebraicGeometry.Scheme.Vect.pullbackId`,
`AlgebraicGeometry.Scheme.Vect.pullbackComp` and
`AlgebraicGeometry.Scheme.Vect.pullbackCongr` are the three structural isomorphisms, lifted
from their counterparts for sheaves of modules.

## Main definitions

* `AlgebraicGeometry.Scheme.Vect.pullbackId`, `AlgebraicGeometry.Scheme.Vect.pullbackComp` and
  `AlgebraicGeometry.Scheme.Vect.pullbackCongr`: the pseudofunctoriality of restriction of
  vector bundles — restriction along an identity, along a composite, and along equal
  morphisms.
* `AlgebraicGeometry.frobeniusPullbackIterIso`: the `N`-fold Frobenius pullback is restriction
  along the `N`-fold absolute Frobenius.
* `AlgebraicGeometry.frobeniusPullbackIterSpecIso`: on `Spec A` that is restriction along
  `Spec` of the `p ^ N`-power endomorphism of `A`.
* `AlgebraicGeometry.betaVectIso` and `AlgebraicGeometry.betaVectIso'`: the two factorisations
  of the `p ^ N`-power map through `A ⧸ (J ⊓ fA)`, read on vector bundles.

## Main results

* `AlgebraicGeometry.frobeniusPullback_eq_vectPullback`: the endofunctor
  `AlgebraicGeometry.frobeniusPullback` is restriction along the absolute Frobenius.

## Implementation notes

`AlgebraicGeometry.frobeniusPullback` and
`AlgebraicGeometry.Scheme.Vect.pullback (absoluteFrobenius …)` are both
`CategoryTheory.ObjectProperty.lift` of the same functor on sheaves of modules, hence equal by
`rfl`; `AlgebraicGeometry.frobeniusPullback_eq_vectPullback` records this so that the
iteration can be rewritten into restrictions and the pseudofunctoriality applied. For the same
reason the three structural isomorphisms are assembled componentwise by
`CategoryTheory.NatIso.ofComponents` and `CategoryTheory.ObjectProperty.isoMk` from
`AlgebraicGeometry.Scheme.Modules.pullbackId`, `…pullbackComp` and `…pullbackCongr`, and the
`simp` lemmas computing their components on underlying modules are `rfl`. In particular
`pullbackCongr` is *not* defined as an `eqToIso`, so that its component is the component of
the Mathlib isomorphism on the nose.

The orientation of `AlgebraicGeometry.Scheme.Vect.pullbackComp` mirrors
`AlgebraicGeometry.Scheme.Modules.pullbackComp`: for `g : X ⟶ Y` and `h : Y ⟶ Z` it compares
`pullback h ⋙ pullback g` with `pullback (g ≫ h)`. Since `Spec` is contravariant, a
factorisation `β ∘ mk = Frob` of ring maps therefore becomes a comparison of
`pullback (Spec.map mk) ⋙ pullback (Spec.map β)` with `pullback (Spec.map Frob)`, which is the
order in which `AlgebraicGeometry.betaVectIso` is stated.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public section

open CategoryTheory Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Pseudofunctoriality of restriction of vector bundles -/

namespace Scheme.Vect

variable {X Y Z : Scheme.{u}}

variable (X) in
/-- **Restriction of a vector bundle along the identity is the identity.** This is
`AlgebraicGeometry.Scheme.Modules.pullbackId` transported to the full subcategories of finite
locally free modules. -/
noncomputable def pullbackId : pullback (𝟙 X) ≅ 𝟭 X.Vect :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((Scheme.Modules.pullbackId X).app M.obj))
    (fun {_ _} φ ↦ ObjectProperty.hom_ext _
      ((Scheme.Modules.pullbackId X).hom.naturality φ.hom))

/-- The component of `AlgebraicGeometry.Scheme.Vect.pullbackId` on underlying sheaves of
modules is the component of `AlgebraicGeometry.Scheme.Modules.pullbackId`. -/
@[simp]
lemma pullbackId_hom_app_hom (M : X.Vect) :
    ((pullbackId X).hom.app M).hom = (Scheme.Modules.pullbackId X).hom.app M.obj :=
  rfl

/-- The component of the inverse of `AlgebraicGeometry.Scheme.Vect.pullbackId` on underlying
sheaves of modules is the component of the inverse of
`AlgebraicGeometry.Scheme.Modules.pullbackId`. -/
@[simp]
lemma pullbackId_inv_app_hom (M : X.Vect) :
    ((pullbackId X).inv.app M).hom = (Scheme.Modules.pullbackId X).inv.app M.obj :=
  rfl

/-- **Restriction of a vector bundle along a composite is the composite of the restrictions.**
This is `AlgebraicGeometry.Scheme.Modules.pullbackComp` transported to the full subcategories
of finite locally free modules, with the same orientation: restricting along `h : Y ⟶ Z` and
then along `g : X ⟶ Y` is restricting along `g ≫ h`. -/
noncomputable def pullbackComp (g : X ⟶ Y) (h : Y ⟶ Z) :
    pullback h ⋙ pullback g ≅ pullback (g ≫ h) :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((Scheme.Modules.pullbackComp g h).app M.obj))
    (fun {_ _} φ ↦ ObjectProperty.hom_ext _
      ((Scheme.Modules.pullbackComp g h).hom.naturality φ.hom))

/-- The component of `AlgebraicGeometry.Scheme.Vect.pullbackComp` on underlying sheaves of
modules is the component of `AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
@[simp]
lemma pullbackComp_hom_app_hom (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Vect) :
    ((pullbackComp g h).hom.app M).hom = (Scheme.Modules.pullbackComp g h).hom.app M.obj :=
  rfl

/-- The component of the inverse of `AlgebraicGeometry.Scheme.Vect.pullbackComp` on underlying
sheaves of modules is the component of the inverse of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
@[simp]
lemma pullbackComp_inv_app_hom (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Vect) :
    ((pullbackComp g h).inv.app M).hom = (Scheme.Modules.pullbackComp g h).inv.app M.obj :=
  rfl

/-- **Restrictions of vector bundles along equal morphisms agree.** This is
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` transported to the full subcategories of
finite locally free modules. -/
noncomputable def pullbackCongr {g h : X ⟶ Y} (e : g = h) : pullback g ≅ pullback h :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((Scheme.Modules.pullbackCongr e).app M.obj))
    (fun {_ _} φ ↦ ObjectProperty.hom_ext _
      ((Scheme.Modules.pullbackCongr e).hom.naturality φ.hom))

/-- The component of `AlgebraicGeometry.Scheme.Vect.pullbackCongr` on underlying sheaves of
modules is the component of `AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
@[simp]
lemma pullbackCongr_hom_app_hom {g h : X ⟶ Y} (e : g = h) (M : Y.Vect) :
    ((pullbackCongr e).hom.app M).hom = (Scheme.Modules.pullbackCongr e).hom.app M.obj :=
  rfl

/-- The component of the inverse of `AlgebraicGeometry.Scheme.Vect.pullbackCongr` on underlying
sheaves of modules is the component of the inverse of
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
@[simp]
lemma pullbackCongr_inv_app_hom {g h : X ⟶ Y} (e : g = h) (M : Y.Vect) :
    ((pullbackCongr e).inv.app M).hom = (Scheme.Modules.pullbackCongr e).inv.app M.obj :=
  rfl

end Scheme.Vect

/-! ### Iterated Frobenius pullback is restriction along a Frobenius power -/

/-- **Frobenius pullback of vector bundles is restriction along the absolute Frobenius.** Both
functors are the lift to finite locally free modules of pullback along
`Stacks.Frobenius.absoluteFrobenius`, so the two spellings agree definitionally. -/
lemma frobeniusPullback_eq_vectPullback (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) :
    frobeniusPullback X p hX = Scheme.Vect.pullback (absoluteFrobenius X p hX) :=
  rfl

/-- **The `N`-fold Frobenius pullback of vector bundles is restriction along the `N`-fold
absolute Frobenius.** The case `N = 0` is restriction along the identity, and the inductive
step is `AlgebraicGeometry.Scheme.Vect.pullbackComp` together with
`AlgebraicGeometry.absoluteFrobeniusPow_succ_eq_comp`. -/
noncomputable def frobeniusPullbackIterIso (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) : ∀ N : ℕ,
    frobeniusPullbackIter X p hX N ≅ Scheme.Vect.pullback (absoluteFrobeniusPow X p hX N)
  | 0 =>
      eqToIso (frobeniusPullbackIter_zero X p hX) ≪≫ (Scheme.Vect.pullbackId X).symm ≪≫
        Scheme.Vect.pullbackCongr (absoluteFrobeniusPow_zero X p hX).symm
  | N + 1 =>
      eqToIso (by
        rw [frobeniusPullbackIter_succ, frobeniusPullback_eq_vectPullback]) ≪≫
      Functor.isoWhiskerRight (frobeniusPullbackIterIso X p hX N)
          (Scheme.Vect.pullback (absoluteFrobenius X p hX)) ≪≫
        Scheme.Vect.pullbackComp (absoluteFrobenius X p hX) (absoluteFrobeniusPow X p hX N) ≪≫
          Scheme.Vect.pullbackCongr (absoluteFrobeniusPow_succ_eq_comp X p hX N).symm

/-- **On an affine scheme the `N`-fold Frobenius pullback is restriction along `Spec` of the
`p ^ N`-power map.** This is `AlgebraicGeometry.frobeniusPullbackIterIso` combined with
`AlgebraicGeometry.specMap_eq_absoluteFrobeniusPow`, whose hypothesis is
`MilnorPatching.OneGeneratorFrobenius.frobeniusPow_apply`. -/
noncomputable def frobeniusPullbackIterSpecIso (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (hp : (p : A) = 0) (N : ℕ) :
    frobeniusPullbackIter (Spec (CommRingCat.of A)) p
        (AlgebraicGeometry.isInCharacteristic_spec A p hp) N ≅
      Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N))) :=
  frobeniusPullbackIterIso (Spec (CommRingCat.of A)) p (isInCharacteristic_spec A p hp) N ≪≫
    Scheme.Vect.pullbackCongr (specMap_eq_absoluteFrobeniusPow
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N) p N
      (isInCharacteristic_spec A p hp)
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow_apply A p hp N)).symm

/-! ### The Frobenius factorisation on vector bundles -/

/-- **The Frobenius factorisation of Stacks Example 0EVG, read on vector bundles.** If `f ^ n`
annihilates `J`, the prime `p` vanishes in `A` and `n + 1 ≤ p ^ N`, then the `p ^ N`-power map
of `A` factors as `A ⟶ A ⧸ (J ⊓ fA) ⟶ A` through
`MilnorPatching.OneGeneratorFrobenius.betaHom`. Applying `Spec` reverses the factorisation,
so restricting a vector bundle on `Spec A` along `Spec` of the quotient map and then along
`Spec` of the factorisation is restricting it along `Spec` of the `p ^ N`-power map. -/
noncomputable def betaVectIso (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N) :
    Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (J ⊓ Ideal.span {f})))) ⋙
      Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN))) ≅
    Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N))) :=
  Scheme.Vect.pullbackComp
      (Spec.map (CommRingCat.ofHom
        (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ⊓ Ideal.span {f})))) ≪≫
    Scheme.Vect.pullbackCongr (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
        MilnorPatching.OneGeneratorFrobenius.betaHom_comp_mk])

/-- **The other Frobenius factorisation of Stacks Example 0EVG, read on vector bundles.**
Postcomposing `MilnorPatching.OneGeneratorFrobenius.betaHom` with the quotient map gives the
`p ^ N`-power map of `A ⧸ (J ⊓ fA)`, so restricting a vector bundle on `Spec (A ⧸ (J ⊓ fA))`
along `Spec` of the factorisation and then along `Spec` of the quotient map is restricting it
along `Spec` of that power map. The vanishing of `p` in the quotient is
`MilnorPatching.OneGeneratorFrobenius.natCast_quotient_eq_zero`. -/
noncomputable def betaVectIso' (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N) :
    Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN))) ⋙
      Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (J ⊓ Ideal.span {f})))) ≅
    Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ (J ⊓ Ideal.span {f})) p
        (MilnorPatching.OneGeneratorFrobenius.natCast_quotient_eq_zero f J hp) N))) :=
  Scheme.Vect.pullbackComp
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ⊓ Ideal.span {f}))))
      (Spec.map (CommRingCat.ofHom
        (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN))) ≪≫
    Scheme.Vect.pullbackCongr (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
        MilnorPatching.OneGeneratorFrobenius.mk_comp_betaHom])

end AlgebraicGeometry

module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPower
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.AffineVect
public import StacksFrontier.RingTheory.MilnorPatching.OneGeneratorFinProj

/-!
# Gluing a vector bundle across the one-generator square, up to a Frobenius twist

Let `A` be a commutative ring, let `f : A`, let `J ⊆ A` be an ideal annihilated by `f ^ n`, let
`p` be a prime vanishing in `A` and let `N` satisfy `n + 1 ≤ p ^ N`. The one-generator almost
blowup square of Stacks Example 0EVG is the square of affine schemes attached to

```
A ⧸ (J ⊓ fA) ---> A ⧸ J
     |               |
     v               v
   A ⧸ fA  ---> A ⧸ (J + fA)
```

This file proves the object-level half of Stacks Tag 0EXC: a vector bundle `E₁` on the centre
`Spec (A ⧸ fA)`, a vector bundle `E₂` on the modification `Spec (A ⧸ J)` and an isomorphism of
their restrictions to the exceptional corner `Spec (A ⧸ (J + fA))` glue to a vector bundle `E`
on `Spec A` whose restrictions to the centre and to the modification are the `N`-th Frobenius
twists of `E₁` and of `E₂`.

The route is the one of the Stacks proof. Milnor patching for the displayed square is available
on finite projective modules
(`MilnorPatching.OneGeneratorFrobenius.exists_oneGeneratorFinProjEquivalence`), so the pair
`(E₁, E₂, u)` is first transported to finite projective modules by the affine comparison
`AlgebraicGeometry.tildeVect`, where it is an object of a categorical pullback; patching produces
a finite projective `A ⧸ (J ⊓ fA)`-module `L`, and `E` is the restriction of `L^~` along `Spec`
of the Frobenius factorisation `MilnorPatching.OneGeneratorFrobenius.betaHom`. The two
restrictions of `E` are then computed by the two commuting squares of ring maps recorded here:
the composite `A ⧸ (J ⊓ fA) → A → A ⧸ fA` is the `p ^ N`-power map of `A ⧸ fA` after the
reduction `A ⧸ (J ⊓ fA) → A ⧸ fA`, and likewise for `J` in place of `fA`.

Only the existence of the two isomorphisms is asserted; no compatibility over the exceptional
corner is claimed.

## Main results

* `AlgebraicGeometry.OneGeneratorSquare.mk_comp_betaHom_centre` and
  `AlgebraicGeometry.OneGeneratorSquare.mk_comp_betaHom_modification`: the two factorisations of
  the Frobenius factorisation `MilnorPatching.OneGeneratorFrobenius.betaHom` after reduction to
  the centre and to the modification.
* `AlgebraicGeometry.OneGeneratorSquare.specMap_betaHom_centre_square` and
  `AlgebraicGeometry.OneGeneratorSquare.specMap_betaHom_modification_square`: the same two
  identities read as commuting squares of affine schemes.
* `AlgebraicGeometry.exists_vect_of_compatible_pair`: the object-level content of Stacks Tag
  0EXC.

## Implementation notes

The two commuting squares are stated as equalities of morphisms of schemes and fed to
`AlgebraicGeometry.vectPullbackSquareIso`, which is the composite of
`AlgebraicGeometry.Scheme.Vect.pullbackComp`, `…pullbackCongr` and the inverse of
`…pullbackComp` assembled once and for all with the four morphisms of the square still
variables. Instantiating that isomorphism at the concrete morphisms `Spec.map (…)` is a plain
term application, whereas unfolding the structural isomorphisms themselves at those morphisms
exhausts the heartbeat budget.

Every transport between finite projective modules and vector bundles is done through
`AlgebraicGeometry.tildeVectPullbackIso`, which is the only compatibility of the affine
comparison with base change that is needed; the comparison is used through its full faithfulness
(`CategoryTheory.Functor.preimageIso`) and its essential surjectivity
(`CategoryTheory.Functor.objObjPreimageIso`) rather than through the bundled equivalence, so
that no inverse functor ever has to be named. Those three instances are introduced by hand at
the head of the proof: instance search does not find
`AlgebraicGeometry.tildeVect_essSurj`, `…tildeVect_full` and `…tildeVect_faithful` when the ring
is the bundled `CommRingCat.of (A ⧸ 𝔞)` rather than a variable, although applying them directly
elaborates.

The statement records only the existence of the two isomorphisms. Their compatibility with the
given isomorphism over the exceptional corner cannot be read off
`MilnorPatching.OneGeneratorFrobenius.exists_oneGeneratorFinProjEquivalence`, which asserts the
two identifications of the components of the patching equivalence separately and so says nothing
about the structural isomorphism of the categorical pullback.

The object of the categorical pullback that Milnor patching is applied to is produced together
with the two equations identifying its components, so that the two reductions of the patched
module are compared with `L₁` and `L₂` by `CategoryTheory.eqToIso` instead of by a defeq check
against an anonymous constructor.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open MilnorPatching.OneGeneratorFrobenius

namespace OneGeneratorSquare

/-! ### The Frobenius factorisation after reduction to the centre and the modification -/

/-- **The Frobenius factorisation reduced to the centre.** Composing
`MilnorPatching.OneGeneratorFrobenius.betaHom` with the quotient map `A ⟶ A ⧸ fA` gives the
`p ^ N`-power map of `A ⧸ fA` precomposed with the reduction `A ⧸ (J ⊓ fA) ⟶ A ⧸ fA`: both
sides send the class of `x` to the class of `x ^ p ^ N`. -/
theorem mk_comp_betaHom_centre (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N) :
    (Ideal.Quotient.mk (Ideal.span {f})).comp
        (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN) =
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ Ideal.span {f}) p
          (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N).comp
        (Ideal.Quotient.factor (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})) := by
  refine RingHom.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := J ⊓ Ideal.span {f}) z
  simp [map_pow]

/-- **The Frobenius factorisation reduced to the modification.** Composing
`MilnorPatching.OneGeneratorFrobenius.betaHom` with the quotient map `A ⟶ A ⧸ J` gives the
`p ^ N`-power map of `A ⧸ J` precomposed with the reduction `A ⧸ (J ⊓ fA) ⟶ A ⧸ J`: both sides
send the class of `x` to the class of `x ^ p ^ N`. -/
theorem mk_comp_betaHom_modification (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N) :
    (Ideal.Quotient.mk J).comp
        (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN) =
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ J) p
          (natCast_quotient_eq_zero A p hp J) N).comp
        (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J)) := by
  refine RingHom.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := J ⊓ Ideal.span {f}) z
  simp [map_pow]

/-! ### The two commuting squares of affine schemes -/

/-- **The centre square.** `Spec` of
`AlgebraicGeometry.OneGeneratorSquare.mk_comp_betaHom_centre`: restricting from
`Spec (A ⧸ (J ⊓ fA))` to `Spec A` along the Frobenius factorisation and then to the centre is
the same as restricting to the centre along the reduction and then along `Spec` of the
`p ^ N`-power map. -/
theorem specMap_betaHom_centre_square (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N) :
    Spec.map (toCtr A f) ≫
        Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN)) =
      Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ Ideal.span {f}) p
            (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f}))) := by
  have h : toCtr A f = CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})) := rfl
  rw [h, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    mk_comp_betaHom_centre A f J n hann p hp N hN]

/-- **The modification square.** `Spec` of
`AlgebraicGeometry.OneGeneratorSquare.mk_comp_betaHom_modification`: restricting from
`Spec (A ⧸ (J ⊓ fA))` to `Spec A` along the Frobenius factorisation and then to the
modification is the same as restricting to the modification along the reduction and then along
`Spec` of the `p ^ N`-power map. -/
theorem specMap_betaHom_modification_square (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (n : ℕ) (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N) :
    Spec.map (toMod A J) ≫
        Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN)) =
      Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ J) p
            (natCast_quotient_eq_zero A p hp J) N)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (inf_le_left : J ⊓ Ideal.span {f} ≤ J))) := by
  have h : toMod A J = CommRingCat.ofHom (Ideal.Quotient.mk J) := rfl
  rw [h, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    mk_comp_betaHom_modification A f J n hann p hp N hN]

end OneGeneratorSquare

/-! ### The object-level gluing -/

/-- **The object-level content of Stacks Tag 0EXC.** Let `f ^ n` annihilate the ideal `J`, let
the prime `p` vanish in `A` and let `n + 1 ≤ p ^ N`. Given a vector bundle `E₁` on the centre
`Spec (A ⧸ fA)`, a vector bundle `E₂` on the modification `Spec (A ⧸ J)` and an isomorphism `u`
of their restrictions to the exceptional corner `Spec (A ⧸ (J + fA))`, there is a vector bundle
`E` on `Spec A` whose restriction to the centre is the `N`-th Frobenius twist of `E₁` and whose
restriction to the modification is the `N`-th Frobenius twist of `E₂`.

No compatibility of the two isomorphisms with `u` over the exceptional corner is asserted. -/
theorem exists_vect_of_compatible_pair (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N)
    (E₁ : (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Vect)
    (E₂ : (Spec (CommRingCat.of (A ⧸ J))).Vect)
    (u : (Scheme.Vect.pullback (Spec.map (OneGeneratorSquare.ctrToExc A f J))).obj E₁ ≅
      (Scheme.Vect.pullback (Spec.map (OneGeneratorSquare.modToExc A f J))).obj E₂) :
    ∃ (E : (Spec (CommRingCat.of A)).Vect),
      Nonempty ((Scheme.Vect.pullback (Spec.map (OneGeneratorSquare.toCtr A f))).obj E ≅
        (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow
            (A ⧸ Ideal.span {f}) p
            (OneGeneratorSquare.natCast_quotient_eq_zero A p hp (Ideal.span {f}))
            N)))).obj E₁) ∧
      Nonempty ((Scheme.Vect.pullback (Spec.map (OneGeneratorSquare.toMod A J))).obj E ≅
        (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ J) p
            (OneGeneratorSquare.natCast_quotient_eq_zero A p hp J) N)))).obj E₂) := by
  have := tildeVect_essSurj (CommRingCat.of (A ⧸ Ideal.span {f}))
  have := tildeVect_essSurj (CommRingCat.of (A ⧸ J))
  have := tildeVect_full (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))
  have := tildeVect_faithful (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))
  -- Read the hypothesis with the two surjections onto the exceptional corner spelled out.
  have u' : (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (surjection f J)))).obj E₁ ≅
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (toBase f J)))).obj E₂ := u
  -- Transport the two vector bundles to finite projective modules.
  obtain ⟨L₁, ⟨e₁⟩⟩ := Functor.EssSurj.mem_essImage (tildeVect _) E₁
  obtain ⟨L₂, ⟨e₂⟩⟩ := Functor.EssSurj.mem_essImage (tildeVect _) E₂
  -- Transport the isomorphism over the exceptional corner to the two extensions of scalars.
  have v : (FinProj.extendScalars (CommRingCat.ofHom (toBase f J))).obj L₂ ≅
      (FinProj.extendScalars (CommRingCat.ofHom (surjection f J))).obj L₁ :=
    (tildeVect (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))).preimageIso
      (((tildeVectPullbackIso (CommRingCat.ofHom (toBase f J))).app L₂).symm ≪≫
        (Scheme.Vect.pullback
            (Spec.map (CommRingCat.ofHom (toBase f J)))).mapIso e₂ ≪≫ u'.symm ≪≫
        (Scheme.Vect.pullback
            (Spec.map (CommRingCat.ofHom (surjection f J)))).mapIso e₁.symm ≪≫
        (tildeVectPullbackIso (CommRingCat.ofHom (surjection f J))).app L₁)
  -- Package the pair as an object of the categorical pullback, with its two components named.
  obtain ⟨Y, hY₁, hY₂⟩ : ∃ Y : CategoricalPullback
        (FinProj.extendScalars (CommRingCat.ofHom (toBase f J)))
        (FinProj.extendScalars (CommRingCat.ofHom (surjection f J))),
      (CategoricalPullback.π₁ _ _).obj Y = L₂ ∧ (CategoricalPullback.π₂ _ _).obj Y = L₁ :=
    ⟨{ fst := L₂, snd := L₁, iso := v }, rfl, rfl⟩
  -- Milnor patching for the one-generator square.
  obtain ⟨q, ⟨i₁⟩, ⟨i₂⟩⟩ :=
    MilnorPatching.OneGeneratorFrobenius.exists_oneGeneratorFinProjEquivalence A f J
  obtain ⟨L, ⟨j₁⟩, ⟨j₂⟩⟩ :
      ∃ L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))),
        Nonempty ((FinProj.extendScalars (CommRingCat.ofHom
            (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).obj L ≅ L₂) ∧
          Nonempty ((FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.factor
            (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).obj L ≅ L₁) := by
    refine ⟨q.inverse.obj Y, ⟨?_⟩, ⟨?_⟩⟩
    · exact (i₁.app (q.inverse.obj Y)).symm ≪≫
        (CategoricalPullback.π₁ _ _).mapIso (q.counitIso.app Y) ≪≫ eqToIso hY₁
    · exact (i₂.app (q.inverse.obj Y)).symm ≪≫
        (CategoricalPullback.π₂ _ _).mapIso (q.counitIso.app Y) ≪≫ eqToIso hY₂
  -- The patched module, restricted along the Frobenius factorisation.
  refine ⟨(Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
      (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN)))).obj
        ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L), ⟨?_⟩, ⟨?_⟩⟩
  · exact (vectPullbackSquareIso (OneGeneratorSquare.specMap_betaHom_centre_square
          A f J n hann p hp N hN)).app
        ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L) ≪≫
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ Ideal.span {f}) p
            (OneGeneratorSquare.natCast_quotient_eq_zero A p hp (Ideal.span {f})) N)))).mapIso
        ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
              (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).app L ≪≫
          (tildeVect (CommRingCat.of (A ⧸ Ideal.span {f}))).mapIso j₂ ≪≫ e₁)
  · exact (vectPullbackSquareIso (OneGeneratorSquare.specMap_betaHom_modification_square
          A f J n hann p hp N hN)).app
        ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L) ≪≫
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ J) p
            (OneGeneratorSquare.natCast_quotient_eq_zero A p hp J) N)))).mapIso
        ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
              (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).app L ≪≫
          (tildeVect (CommRingCat.of (A ⧸ J))).mapIso j₁ ≪≫ e₂)

end AlgebraicGeometry

end

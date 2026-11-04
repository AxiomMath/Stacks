module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.RingTheory.IntegrallyClosed.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Smooth.Normal

/-!
# Normality is local in the smooth, hence in the étale, topology

[Stacks, Tag 034F] states that the property "`S` is normal" of a scheme is local in the smooth
topology. This file proves the étale instance of that statement,

```
CategoryTheory.ObjectProperty.IsLocal
  (fun X : Scheme.{u} => AlgebraicGeometry.IsNormal X) AlgebraicGeometry.Scheme.etalePrecoverage
```

which is the form item (7) of Remark 03E7 consumes: it is what turns
`AlgebraicGeometry.Space.HasEtaleLocalProperty` — Definition 03E6 — at normality from a
some-chart condition into the every-chart equivalence of Lemma 03E8.

The two halves of locality are proved by the two routes of the source. Ascent is the affine
statement that a smooth algebra over a normal ring is normal (Algebra, Lemma 033C, available as
`Algebra.isNormalRing_of_smooth`), transported to schemes along an affine open cover. Descent is
the affine statement that normality descends along a faithfully flat ring map (Algebra, Lemma
033G, available as `isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat`), applied on
stalks: a flat morphism induces flat local homomorphisms of local rings, which are therefore
faithfully flat.

## Main results

* `AlgebraicGeometry.isNormal_of_smooth`: the source of a smooth morphism with normal target is
  normal. This is the ascent half, Stacks 033C at the level of schemes.
* `AlgebraicGeometry.isNormal_of_etale`: the étale case of the same statement, which is the
  normality half of Stacks 0BQL.
* `AlgebraicGeometry.isNormal_of_forall_exists_flat`: a scheme every point of which lies in the
  image of a flat morphism from a normal scheme is normal. This is the descent half, Stacks 033G
  at the level of schemes.
* `AlgebraicGeometry.isLocal_isNormal_etalePrecoverage`: **Stacks 034F** for the étale
  precoverage — normality is a local object property.

## Implementation notes

The source proves 034F by checking the three conditions of Lemma 0349 — Zariski locality,
ascent along a smooth morphism of affines, descent along a surjective smooth morphism of
affines. Lemma 0349 is not available in this library, and `CategoryTheory.ObjectProperty.IsLocal`
asks for the two implications directly, so the two implications are proved directly. Zariski
locality is not needed as a separate step: it is absorbed into the two affine arguments, as
`AlgebraicGeometry.isNormal_tfae` already states normality to be local on an open cover.

The statement is proved for the étale precoverage rather than the smooth one, which is what the
algebraic-spaces layer consumes; both affine inputs are the smooth ones, so nothing but the
precoverage would change in the smooth version. Note that `Scheme.etalePrecoverage` requires its
members to be *jointly surjective* as well as étale, which is what makes the descent half
applicable.

`AlgebraicGeometry.IsNormal.of_openCover` and the two affine translations
`AlgebraicGeometry.isNormal_of_isNormalRing_appTop`,
`AlgebraicGeometry.isNormalRing_appTop_of_isNormal` are stated here because
`AlgebraicGeometry.isNormal_tfae` is the only public interface to them: the corresponding
helpers in `StacksFrontier/AlgebraicGeometry/Properties/Normal.lean` are `private`.

`AlgebraicGeometry.isNormal_of_smooth` and `AlgebraicGeometry.isNormal_of_forall_exists_flat`
carry no tag. Tags 033C and 033G are statements about *rings*, already carried by
`Algebra.isNormalRing_of_smooth` and
`isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat`; these are the scheme-level
consequences, exactly as `AlgebraicGeometry.isReduced_of_smooth` is the untagged scheme-level
consequence of Tag 033B.

## References

* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
* [Stacks Project, Tag 033G](https://stacks.math.columbia.edu/tag/033G)
* [Stacks Project, Tag 033I](https://stacks.math.columbia.edu/tag/033I)
* [Stacks Project, Tag 033J](https://stacks.math.columbia.edu/tag/033J)
* [Stacks Project, Tag 0349](https://stacks.math.columbia.edu/tag/0349)
* [Stacks Project, Tag 034F](https://stacks.math.columbia.edu/tag/034F)
* [Stacks Project, Tag 03E7](https://stacks.math.columbia.edu/tag/03E7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-! ### Descent of normality along a faithfully flat map of local rings -/

/-- **Stacks 033G for a local ring downstairs.** If `A → B` is faithfully flat with `B` an
integrally closed domain, and `A` is local, then `A` is an integrally closed domain.

An integrally closed domain is a normal ring (`IsNormalRing.of_isIntegrallyClosed`), normality
descends along a faithfully flat map, and a local normal ring is an integrally closed domain
(`IsNormalRing.of_isLocalRing`). -/
@[ega "IV 2.1.13" "special case", ega "IV 7.5.3" "(vi)"]
theorem isDomain_and_isIntegrallyClosed_of_faithfullyFlat (A B : Type*) [CommRing A]
    [IsLocalRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] [IsDomain B]
    [IsIntegrallyClosed B] : IsDomain A ∧ IsIntegrallyClosed A := by
  have hA : IsNormalRing A := isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat
    (IsNormalRing.of_isIntegrallyClosed B)
  exact hA.of_isLocalRing

namespace AlgebraicGeometry

/-! ### Normality on affine opens and on open covers -/

/-- The global sections of a normal affine scheme form a normal ring. This is the direction
`1 → 2` of `AlgebraicGeometry.isNormal_tfae` read at the affine open `⊤`. -/
theorem isNormalRing_appTop_of_isNormal (X : Scheme.{u}) [IsAffine X] [IsNormal X] :
    IsNormalRing Γ(X, ⊤) := by
  have h : IsNormal X ↔ ∀ U : X.affineOpens, IsNormalRing Γ(X, U) :=
    (isNormal_tfae X).out 1 2
  exact h.mp ‹IsNormal X› ⟨⊤, isAffineOpen_top X⟩

/-- An affine scheme whose global sections form a normal ring is normal. This is the direction
`3 → 1` of `AlgebraicGeometry.isNormal_tfae` at the one-member affine open cover `{⊤}`. -/
theorem isNormal_of_isNormalRing_appTop {X : Scheme.{u}} [IsAffine X]
    (hX : IsNormalRing Γ(X, ⊤)) : IsNormal X := by
  have h : IsNormal X ↔
      ∃ (I : Type u) (U : I → X.affineOpens),
        IsOpenCover (fun i ↦ (U i : X.Opens)) ∧ ∀ i, IsNormalRing Γ(X, U i) :=
    (isNormal_tfae X).out 1 3
  exact h.mpr ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top X⟩, IsOpenCover.mk (by simp), fun _ => hX⟩

/-- **Normality is local on an open cover.** A scheme covered by normal schemes along open
immersions is normal.

This is the direction `4 → 1` of `AlgebraicGeometry.isNormal_tfae`, with the members of the
cover replaced by their open ranges. -/
theorem IsNormal.of_openCover {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} X)
    (h𝒰 : ∀ i, IsNormal (𝒰.X i)) : IsNormal X := by
  have h : IsNormal X ↔
      ∃ (I : Type u) (U : I → X.Opens), IsOpenCover U ∧ ∀ i, IsNormal (U i).toScheme :=
    (isNormal_tfae X).out 1 4
  exact h.mpr ⟨𝒰.I₀, fun i => (𝒰.f i).opensRange, 𝒰.isOpenCover_opensRange,
    fun i => @isNormal_of_iso _ _ (𝒰.f i).isoOpensRange.symm (h𝒰 i)⟩

/-- Normality of a scheme is closed under isomorphisms, as an object property. -/
instance isClosedUnderIsomorphisms_isNormal :
    ObjectProperty.IsClosedUnderIsomorphisms (fun X : Scheme.{u} => IsNormal X) where
  of_iso e hX := @isNormal_of_iso _ _ e.symm hX

/-! ### Ascent: the source of a smooth morphism with normal target is normal -/

/-- **A scheme smooth over a normal affine scheme is normal.** On an affine open of the source
the sections form a smooth algebra over the global sections of the target, which are a normal
ring, so Stacks 033C applies; normality is local on the source.

This is the affine-target case of `AlgebraicGeometry.isNormal_of_smooth`, and the companion of
`AlgebraicGeometry.isReduced_of_smooth_of_isAffine`. -/
@[sga "3 X 8.4" "special case"]
theorem isNormal_of_smooth_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsAffine Y]
    [IsNormal Y] : IsNormal X := by
  refine IsNormal.of_openCover X.affineCover fun i => ?_
  let : Algebra Γ(Y, ⊤) Γ(X.affineCover.X i, ⊤) := (X.affineCover.f i ≫ f).appTop.hom.toAlgebra
  have : Algebra.Smooth Γ(Y, ⊤) Γ(X.affineCover.X i, ⊤) :=
    (HasRingHomProperty.appTop @Smooth (X.affineCover.f i ≫ f)
      (HasRingHomProperty.comp_of_isOpenImmersion @Smooth (X.affineCover.f i) f ‹_›)).toAlgebra
  exact isNormal_of_isNormalRing_appTop
    (Algebra.isNormalRing_of_smooth Γ(Y, ⊤) Γ(X.affineCover.X i, ⊤)
      (isNormalRing_appTop_of_isNormal Y))

/-- **Stacks 033C for schemes.** The source of a smooth morphism with normal target is normal.

The affine-target case is `AlgebraicGeometry.isNormal_of_smooth_of_isAffine`; the general case
follows by base change along an affine open cover of the target, which is an open cover of the
source. -/
@[sga "3 X 8.9"]
theorem isNormal_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsNormal Y] :
    IsNormal X := by
  let 𝒰 := Y.affineOpenCover.openCover
  refine IsNormal.of_openCover (𝒰.pullback₁ f) fun i => ?_
  have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hnorm : IsNormal (𝒰.X i) := isNormal_of_iso (𝒰.f i).isoOpensRange
  have hs : Smooth (pullback.snd f (𝒰.f i)) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback f (𝒰.f i))
      ‹Smooth f›
  exact @isNormal_of_smooth_of_isAffine _ _ (pullback.snd f (𝒰.f i)) hs
    (inferInstanceAs (IsAffine (Spec _))) hnorm

/-- The source of an étale morphism with normal target is normal, an étale morphism being
smooth. -/
@[stacks 0BQL "normality"]
theorem isNormal_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsNormal Y] :
    IsNormal X :=
  isNormal_of_smooth f

/-! ### Descent: normality along a flat surjection -/

/-- **Stacks 033G for schemes**, in pointwise form: a scheme is normal as soon as every point of
it lies in the image of a flat morphism from a normal scheme.

At a point, the chosen morphism induces a flat local homomorphism of local rings on stalks,
which is therefore faithfully flat, and normality of a local ring descends along it by
`isDomain_and_isIntegrallyClosed_of_faithfullyFlat`. -/
@[ega "IV 11.3.13" "more general",
  ega "IV 2.1.13" "more general",
  ega "IV 6.5.4" "Clause (i), special case"]
theorem isNormal_of_forall_exists_flat {X : Scheme.{u}}
    (H : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Flat f ∧ IsNormal Y ∧
      x ∈ Set.range f.base) :
    IsNormal X := by
  rw [isNormal_iff_stalk_normal]
  intro x
  obtain ⟨Y, f, hflat, hnorm, y, rfl⟩ := H x
  let : Algebra (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := Flat.stalkMap f y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : IsDomain (Y.presheaf.stalk y) := hnorm.stalk_isDomain y
  have : IsIntegrallyClosed (Y.presheaf.stalk y) := hnorm.stalk_normal y
  obtain ⟨h₁, h₂⟩ := isDomain_and_isIntegrallyClosed_of_faithfullyFlat
    (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)
  exact ⟨h₁, h₂⟩

/-! ### Stacks 034F for the étale precoverage -/

/-- **Stacks 034F for the étale precoverage.** Normality of a scheme is a local object property
for `AlgebraicGeometry.Scheme.etalePrecoverage`: a scheme étale over a normal scheme is normal,
and a scheme covered by normal schemes étale over it is normal.

The source states Lemma 034F for the smooth topology; the étale precoverage is what the
algebraic-spaces layer consumes, and both affine inputs — Stacks 033C for ascent and Stacks 033G
for descent — are the smooth ones, so nothing is lost by restricting.

This is item (7) of Remark 03E7: it is the instance that
`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale` needs in order to turn
`AlgebraicGeometry.Space.IsNormal` — Definition 03E6 at normality — from a some-chart condition
into an every-chart equivalence. -/
@[stacks 034F "for the étale precoverage, `AlgebraicGeometry.Scheme.etalePrecoverage`, rather \
  than for the smooth one; normality of a scheme is `AlgebraicGeometry.IsNormal`, Definition \
  033I, i.e. every local ring is a normal domain", sga "1 II 3.1" "special case"]
instance isLocal_isNormal_etalePrecoverage :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsNormal X) Scheme.etalePrecoverage where
  component {X R} hR Y f hf hX := by
    have : Etale f := hR.2 hf
    have : IsNormal X := hX
    exact isNormal_of_etale f
  of_presieve {X R} hR H := by
    refine isNormal_of_forall_exists_flat fun x => ?_
    obtain ⟨Y, f, hf, hx⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).1 hR.1 x
    have : Etale f := hR.2 hf
    exact ⟨Y, f, inferInstance, H hf, hx⟩

end AlgebraicGeometry

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionDisjointUnion

/-!
# The affine chart of a finite fpqc covering, and the descended ring as an object of the site

Effective descent for affine morphisms along an fpqc covering — Stacks 0245 — is consumed by
`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc`, and hence by Stacks 041Z, in one
special shape only: the base is an **affine** object of the big fppf site of `S` and the
covering is a **finite** family of **affine** objects. Neither the Zariski reduction of the
source nor the Zariski gluing of the descended scheme is needed there, because a finite
coproduct of affine objects of the site is again an affine object of the site. This file
supplies the two pieces of bookkeeping that the special shape needs on either side of the
already-available affine descent argument of
`StacksFrontier.AlgebraicGeometry.Descent.AffineHomDescentCocycle`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_affine_chart_of_finite_fpqc`: **the chart.** A finite
  fpqc covering family of an affine object of the big fppf category over `S` by affine objects
  is refined by a single morphism `q : c ⟶ Z` of the site whose source is affine and whose
  underlying morphism of schemes is surjective, flat and quasi-compact, namely the morphism out
  of the coproduct of the family. The coproduct cofan is returned alongside, so that the family
  can be recovered from `q` through
  `AlgebraicGeometry.IsAlgebraicSpace.isSheafFor_ofArrows_of_isSheafFor_singleton_cofanDesc`.
* `AlgebraicGeometry.exists_bigFppfOver_Spec_of_injective_appTop`: **the descended ring as an
  object of the site.** If `C` is a ring under `Γ(a)` for an affine object `a` of the site and
  `C ⟶ Γ(v)` is injective for some object `v` of the site with affine underlying scheme, then
  `Spec C` is the underlying scheme of an object of the big fppf category over `S`, with the
  morphism induced by `Γ(a) ⟶ C` as its morphism to `a`.

## Implementation notes

*Why the chart carries no size hypothesis.* The coproduct is taken in the site itself, where it
exists by `AlgebraicGeometry.hasFiniteCoproducts_bigFppfOver` — the size cutoff is closed under
finite coproducts of schemes by Stacks 000R (2), which needs no more than the two fields
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` and
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof`. **No regularity of the cutoff is used**,
and none is available: a strong prelimit which is also regular is inaccessible.

*How the chart's three properties are obtained.* The canonical functor to schemes preserves
finite coproducts, so `AlgebraicGeometry.BigFppfOver.exists_iso_sigma_of_isColimit_cofan`
identifies the underlying morphism of `q` with `Sigma.desc` of the family up to the comparison
isomorphism. Flatness is then Zariski locality at the source, surjectivity is joint
surjectivity of the family — which is part of membership in
`AlgebraicGeometry.Scheme.fpqcPrecoverage` — and quasi-compactness is automatic once both ends
are affine. Affineness of the source is affineness of a finite coproduct of affine schemes,
transported along the comparison isomorphism. This is the computation performed inline in the
proof of `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isSheafFor_singleton_affine`,
isolated here because the descent side of Stacks 0245 needs the chart itself rather than only
the sheaf condition for it.

*The size bound for the descended ring.* `AlgebraicGeometry.Scheme.size_Spec_lt_of_mk_le` is
Stacks 000R (9): `Spec C` lies in the site as soon as `#C` is bounded by `size(T) ^ ℵ₀` for
some object `T` of the site. Injectivity of `C ⟶ Γ(v)` gives `#C ≤ #Γ(v)`, and
`AlgebraicGeometry.Scheme.size_of_isAffine` computes `size(v) = max {ℵ₀, #Γ(v)}`, so `T = v`
serves. The injectivity hypothesis is exactly the first conclusion of
`AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isPullback`, which records it for this
purpose. The structure morphism of the new object is the composite
`Spec C ⟶ Spec Γ(a) ≅ a ⟶ S`, so no choice is involved and the returned isomorphism with
`Spec C` is the identity.

*What the two statements are.* The first is a statement about the ambient category of a big
fppf site which the source does not make; the second is an application of Stacks 000R (9),
whose tag sits on `AlgebraicGeometry.Scheme.size_Spec_lt_of_mk_le`. Stacks 0245, by contrast,
is effectivity of a descent datum relative to an arbitrary fpqc covering of an arbitrary
scheme; the two statements here are the bookkeeping on either side of the chart that the
special shape of the covering consumed by Stacks 041Z needs.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The affine chart of a finite fpqc covering -/

namespace BigFppfOver

/-- **A finite fpqc covering of an affine object of the site by affine objects is refined by a
single morphism of affine objects.** Let `Z` be an object of the big fppf category over `S`
with affine underlying scheme and let `{w i : W i ⟶ Z}` be a finite family of morphisms whose
sources have affine underlying scheme and which is an fpqc covering family after transport to
schemes. Then there are an object `c` of the site, a coproduct cofan `{inj i : W i ⟶ c}` and a
morphism `q : c ⟶ Z` with `inj i ≫ q = w i`, such that `c` has affine underlying scheme and
the underlying morphism of `q` is surjective, flat and quasi-compact.

This is the chart that the descent side of Stacks 0245 consumes in the shape in which
`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc` presents it, and it is the
covering-level half of the disjoint union step of Stacks 0APL; the sheaf-condition half is
`AlgebraicGeometry.IsAlgebraicSpace.isSheafFor_ofArrows_of_isSheafFor_singleton_cofanDesc`,
which consumes the cofan returned here. -/
@[sga "3 IV 6.3.1" "footnote (58), i = 1"]
theorem exists_affine_chart_of_finite_fpqc
    {Z : BigFppfOver B S hS} (hZ : IsAffine ((toScheme B S hS).obj Z))
    {ι : Type v} [Finite ι] (W : ι → BigFppfOver B S hS) (w : ∀ i, W i ⟶ Z)
    (hWaff : ∀ i, IsAffine ((toScheme B S hS).obj (W i)))
    (hmem : Presieve.ofArrows W w ∈
      Scheme.fpqcPrecoverage.comap (toScheme B S hS) Z) :
    ∃ (c : BigFppfOver B S hS) (inj : ∀ i, W i ⟶ c) (q : c ⟶ Z),
      Nonempty (IsColimit (Cofan.mk c inj)) ∧
      IsAffine ((toScheme B S hS).obj c) ∧
      Surjective ((toScheme B S hS).map q) ∧
      Flat ((toScheme B S hS).map q) ∧
      QuasiCompact ((toScheme B S hS).map q) ∧
      ∀ i, inj i ≫ q = w i := by
  set G := toScheme B S hS with hG
  have hc : IsColimit (Cofan.mk (∐ W) (Sigma.ι W)) := coproductIsCoproduct W
  obtain ⟨e, he⟩ := exists_iso_sigma_of_isColimit_cofan W hc
  have hWaff' (i : ι) : IsAffine (G.obj (W i)) := hWaff i
  have hcaff : IsAffine (G.obj (∐ W)) := IsAffine.of_isIso e.inv
  -- the comparison isomorphism identifies `G.map (Sigma.desc w)` with the coproduct descent
  have hgdesc : e.hom ≫ G.map (Sigma.desc w) = Sigma.desc fun i ↦ G.map (w i) := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, he i, ← Functor.map_comp, Sigma.ι_comp_desc]
    have hfac : (Cofan.mk (∐ W) (Sigma.ι W)).inj i ≫ Sigma.desc w = w i := by simp
    exact congrArg G.map hfac
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hmem
  obtain ⟨-, hfl⟩ := hmem
  obtain ⟨hjs, hwflat⟩ := (Scheme.ofArrows_mem_precoverage_iff _).mp hfl
  have _hfri : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _hsri : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- an iso-stable property passes from the coproduct descent to `G.map (Sigma.desc w)`
  have transport (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
      (h : P (Sigma.desc fun i ↦ G.map (w i))) : P (G.map (Sigma.desc w)) := by
    rw [← hgdesc] at h
    exact (P.cancel_left_of_respectsIso e.hom _).mp h
  have hflat : Flat (G.map (Sigma.desc w)) := by
    have hw (i : ι) : Flat (G.map (w i)) := hwflat i
    exact transport (@Flat.{u}) inferInstance
  have hsurj : Surjective (G.map (Sigma.desc w)) := by
    refine transport (@Surjective.{u}) ⟨fun y ↦ ?_⟩
    obtain ⟨i, z, hzy⟩ := hjs y
    refine ⟨Sigma.ι (fun i ↦ G.obj (W i)) i z, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    exact hzy
  have hZ' := hZ
  have hqc : QuasiCompact (G.map (Sigma.desc w)) := inferInstance
  exact ⟨∐ W, Sigma.ι W, Sigma.desc w, ⟨hc⟩, hcaff, hsurj, hflat, hqc,
    fun i ↦ Sigma.ι_comp_desc _ _⟩

end BigFppfOver

/-! ### The descended ring as an object of the site -/

/-- **A ring under the sections of an affine object of the site, embedded in the sections of
another object of the site, has an affine spectrum in the site.** Let `a` and `v` be objects of
the big fppf category over `S` with affine underlying schemes, let `k : Γ(a) ⟶ C` and let
`p : C ⟶ Γ(v)` be injective. Then there are an object `b` of the site, a morphism `b ⟶ a` and
an isomorphism of `Spec C` with the underlying scheme of `b` carrying `Spec k` to that
morphism.

This is the passage from the descended ring of
`AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isPullback` — the affine case of
Stacks 0245 — back to the site. It is Stacks 000R (9) applied to the object `v`: injectivity of
`p` bounds `#C` by `#Γ(v)`, and `AlgebraicGeometry.Scheme.size_of_isAffine` identifies
`max {ℵ₀, #Γ(v)}` with the size of `v`, which lies below the cutoff because `v` is an object of
the site. Only the two fields `AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` and
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` are consulted; no regularity of the
cutoff is used. -/
theorem exists_bigFppfOver_Spec_of_injective_appTop
    {a v : BigFppfOver B S hS}
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hv : IsAffine ((BigFppfOver.toScheme B S hS).obj v))
    {C : CommRingCat.{u}} (k : Γ((BigFppfOver.toScheme B S hS).obj a, ⊤) ⟶ C)
    {p : C ⟶ Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)} (hp : Function.Injective p.hom) :
    ∃ (b : BigFppfOver B S hS) (i : b ⟶ a)
      (ε : (BigFppfOver.toScheme B S hS).obj b ≅ Spec C),
      ε.hom ≫ Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv =
        (BigFppfOver.toScheme B S hS).map i := by
  have _ := ha
  have _ := hv
  have hmk : Cardinal.mk C ≤ ((BigFppfOver.toScheme B S hS).obj v).size ^ ℵ₀ := by
    refine le_trans (le_trans (Cardinal.mk_le_of_injective hp) (le_max_right ℵ₀ _)) ?_
    rw [← Scheme.size_of_isAffine ((BigFppfOver.toScheme B S hS).obj v)]
    exact self_le_power _ one_le_aleph0
  have hsize : (Spec C).size < B.cutoff :=
    Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit C v.left.2 hmk
  exact ⟨Over.mk (Y := (⟨Spec C, hsize⟩ : B.Schemes))
      (ObjectProperty.homMk ((Spec.map k ≫
        ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫ a.hom.hom)),
    Over.homMk
      (ObjectProperty.homMk
        (Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv))
      (by apply ObjectProperty.hom_ext; rfl),
    Iso.refl _, Category.id_comp _⟩

end AlgebraicGeometry

end

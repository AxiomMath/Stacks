module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.GradedPiece
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerShortExact
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernels
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Limits.BiproductMatrixFunctor

/-!
# The exact sequences of the adic filtration, and their direct images

For `p : U ⟶ Spec A`, an ideal `I ⊆ A` and a quasi-coherent `𝒪_U`-module `ℱ`, the `n`-th step of
the `I`-adic filtration of `ℱ` sits in a short exact sequence

```
0 ⟶ Iⁿ(ℱ/Iⁿ⁺¹ℱ) ⟶ ℱ/Iⁿ⁺¹ℱ ⟶ ℱ/Iⁿℱ ⟶ 0
```

whose first term is the graded piece `Stacks.BaseAdicFiltration.gradedPiece`, identified as
`k = dim_κ Iⁿ/Iⁿ⁺¹` copies of `ℱ/Iℱ` by
`Stacks.BaseAdicFiltration.exists_isoDirectSum_gradedPiece`.  This file builds that
sequence, and pushes it forward along a morphism `f : U ⟶ V`:

```
0 ⟶ f_*(Iⁿ(ℱ/Iⁿ⁺¹ℱ)) ⟶ f_*(ℱ/Iⁿ⁺¹ℱ) ⟶ f_*(ℱ/Iⁿℱ) ⟶ 0 ,
      with  f_*(Iⁿ(ℱ/Iⁿ⁺¹ℱ)) ≅ ⨁_{i<k} f_*(ℱ/Iℱ) .
```

This is the shape the filtration argument of [Stacks, Tag 0E3X] reads backwards by induction: the
source's sequence

```
0 → (f_*𝒪_X) ⊗_κ 𝔪ⁱ/𝔪ⁱ⁺¹ → f_*(𝒪_U/𝔪ⁱ⁺¹𝒪_U) → f_*(𝒪_U/𝔪ⁱ𝒪_U) → 0
```

is the displayed one for `ℱ = 𝒪_U` and `I = 𝔪`, with `(f_*𝒪_X) ⊗_κ 𝔪ⁱ/𝔪ⁱ⁺¹` presented as
`k = dim_κ 𝔪ⁱ/𝔪ⁱ⁺¹` copies of `f_*𝒪_X = f_*(𝒪_U/𝔪𝒪_U)`.

Right exactness is the only part that needs an input beyond the filtration: direct image is left
exact but not right exact, and what makes the last map surjective is the vanishing of `R¹f_*` on
the graded piece.  That vanishing is *deduced* here from the vanishing of `R¹f_*` on the special
fibre `ℱ/Iℱ` — the hypothesis `R¹f_*𝒪_X = 0` of the tag — because a right derived functor of an
additive functor is additive and so annihilates a finite biproduct of objects it annihilates.
Carrying the tensor factor as a biproduct rather than as `⊗_κ 𝔪ⁱ/𝔪ⁱ⁺¹` is what makes that step a
single lemma application, which is why
`Stacks.BaseAdicFiltration.exists_isoDirectSum_gradedPiece` presents the graded piece in that
form.

## Main definitions

* `Stacks.BaseAdicFiltration.adicQuotientIso` — the identification
  `(ℱ/Iⁿ⁺¹ℱ)/Iⁿ(ℱ/Iⁿ⁺¹ℱ) ≅ ℱ/Iⁿℱ`, with the compatibility of the projections out of `ℱ`.
* `Stacks.BaseAdicFiltration.gradedShortComplex` — the short complex
  `Iⁿ(ℱ/Iⁿ⁺¹ℱ) ⟶ ℱ/Iⁿ⁺¹ℱ ⟶ ℱ/Iⁿℱ`.

## Main results

* `Stacks.BaseAdicFiltration.gradedShortComplex_shortExact` — it is short exact.
* `Stacks.BaseAdicFiltration.isZero_rightDerived_one_gradedPiece_of_additive`,
  `shortExact_map_gradedShortComplex` and `exists_isoDirectSum_map_gradedPiece` — the same for an
  arbitrary additive, left exact functor out of `U.Modules` in place of a direct image, which is
  what lets the sequence be carried along a bare continuous map of the underlying spaces.
* `Stacks.BaseAdicFiltration.isZero_rightDerived_one_gradedPiece` — `R¹f_*` annihilates the graded
  piece as soon as it annihilates the special fibre.
* `Stacks.BaseAdicFiltration.shortExact_map_pushforward_gradedShortComplex` — **the direct image
  sequence**, short exact under that vanishing.
* `Stacks.BaseAdicFiltration.exists_isoDirectSum_pushforward_gradedPiece` — its first term is a
  finite direct sum of copies of `f_*(ℱ/Iℱ)`.
* `Stacks.BaseAdicFiltration.exists_shortExact_pushforward_of_isArtinianRing` — the two combined
  over an Artinian local base, which is the statement [Stacks, Tag 0E3X] consumes.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe v' u' u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.BaseAdicFiltration

attribute [local instance] hasFiniteBiproducts_schemeModules

variable {A : Type u} [CommRing A] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (n : ℕ) (F : U.Modules) [F.IsQuasicoherent]

/-! ### The short exact sequence of the filtration -/

/-- **The quotient of `ℱ/Iⁿ⁺¹ℱ` by the `n`-th step of its filtration is `ℱ/Iⁿℱ`**, and under
that identification the two projections out of `ℱ` compose to the projection `ℱ ⟶ ℱ/Iⁿℱ`.

This is `Stacks.Algebraization.doubleIdealPowerQuotientIso` for `Iⁿ⁺¹ ⊆ Iⁿ`; dividing by `Iⁿ⁺¹`
first is invisible modulo `Iⁿ`. -/
def adicQuotientIso :
    {e : adicQuotient p I n (adicQuotient p I (n + 1) F) ≅ adicQuotient p I n F //
      adicProj p I (n + 1) F ≫ adicProj p I n (adicQuotient p I (n + 1) F) ≫ e.hom =
        adicProj p I n F} := by
  haveI : IsIso (idealPowerQuotientMap (baseIdeal p I) (baseIdeal p I) n n le_rfl
      (adicProj p I n F)) :=
    isIso_idealPowerQuotientMap_cokernel_π (baseIdeal p I) (baseIdeal p I) n n le_rfl F
  exact doubleIdealPowerQuotientIso (baseIdeal p I) (baseIdeal p I) n (n + 1)
    (Scheme.IdealSheafData.pow_le_pow_of_le (baseIdeal p I) (Nat.le_succ n))
    (adicProj p I n F) (idealPowerMultiple_idealPowerQuotient_eq_bot (baseIdeal p I) n F)

/-- `Stacks.BaseAdicFiltration.adicQuotientIso`, retyped as a morphism out of the third term of
`Stacks.Algebraization.idealPowerQuotientShortComplex`.  The two types are equal by `rfl`, but
only at default transparency, which a `def` forces and the elaboration of a composite does
not. -/
def adicQuotientShortComplexIso :
    (idealPowerQuotientShortComplex (baseIdeal p I) n (adicQuotient p I (n + 1) F)).X₃ ≅
      adicQuotient p I n F :=
  (adicQuotientIso p I n F).1

/-- The underlying morphism of `Stacks.BaseAdicFiltration.adicQuotientShortComplexIso`. -/
abbrev adicQuotientShortComplexHom :
    (idealPowerQuotientShortComplex (baseIdeal p I) n (adicQuotient p I (n + 1) F)).X₃ ⟶
      adicQuotient p I n F :=
  (adicQuotientShortComplexIso p I n F).hom

/-- **The short complex `Iⁿ(ℱ/Iⁿ⁺¹ℱ) ⟶ ℱ/Iⁿ⁺¹ℱ ⟶ ℱ/Iⁿℱ`.** The first map is the inclusion of
the graded piece and the second is the projection onto the quotient by it, read as `ℱ/Iⁿℱ`
through `Stacks.BaseAdicFiltration.adicQuotientIso`.

Both maps are named through the fields of
`Stacks.Algebraization.idealPowerQuotientShortComplex` rather than written out.  That is not
cosmetic: `U.ringCatSheaf` has type `TopCat.Sheaf RingCat ↑U.toPresheafedSpace` where
`SheafOfModules.Submodule.toSheafOfModules` asks for `Sheaf (Opens.grothendieckTopology ↥U)
RingCat`, and although those are the same type, a composite written out with a subsheaf as its
source carries two different `Category` instances, so `rw` does not see it as a composite and
the zero morphism out of it is not synthesised. -/
def gradedShortComplex : ShortComplex U.Modules :=
  ShortComplex.mk (C := U.Modules)
    (idealPowerQuotientShortComplex (baseIdeal p I) n (adicQuotient p I (n + 1) F)).f
    ((idealPowerQuotientShortComplex (baseIdeal p I) n (adicQuotient p I (n + 1) F)).g ≫
      adicQuotientShortComplexHom p I n F)
    (by
      rw [← Category.assoc,
        (idealPowerQuotientShortComplex (baseIdeal p I) n (adicQuotient p I (n + 1) F)).zero,
        zero_comp])

/-- The first term of `Stacks.BaseAdicFiltration.gradedShortComplex` is the graded piece
`Iⁿ(ℱ/Iⁿ⁺¹ℱ)`. -/
@[simp]
theorem gradedShortComplex_X₁ :
    (gradedShortComplex p I n F).X₁ = (gradedPiece p I n F).toSheafOfModules := rfl

/-- The middle term of `Stacks.BaseAdicFiltration.gradedShortComplex` is `ℱ/Iⁿ⁺¹ℱ`. -/
@[simp]
theorem gradedShortComplex_X₂ :
    (gradedShortComplex p I n F).X₂ = adicQuotient p I (n + 1) F := rfl

/-- The third term of `Stacks.BaseAdicFiltration.gradedShortComplex` is `ℱ/Iⁿℱ`. -/
@[simp]
theorem gradedShortComplex_X₃ :
    (gradedShortComplex p I n F).X₃ = adicQuotient p I n F := rfl

/-- The first map of `Stacks.BaseAdicFiltration.gradedShortComplex` is the inclusion of the graded
piece `Iⁿ(ℱ/Iⁿ⁺¹ℱ)` into `ℱ/Iⁿ⁺¹ℱ`. -/
@[simp]
theorem gradedShortComplex_f :
    (gradedShortComplex p I n F).f = (gradedPiece p I n F).ι := rfl

/-- The second map of `Stacks.BaseAdicFiltration.gradedShortComplex` is the projection of
`ℱ/Iⁿ⁺¹ℱ` onto its quotient by the graded piece, composed with the identification of that
quotient with `ℱ/Iⁿℱ`. -/
@[simp]
theorem gradedShortComplex_g :
    (gradedShortComplex p I n F).g =
      (idealPowerQuotientShortComplex (baseIdeal p I) n (adicQuotient p I (n + 1) F)).g ≫
        adicQuotientShortComplexHom p I n F :=
  rfl

/-- **The sequence `0 → Iⁿ(ℱ/Iⁿ⁺¹ℱ) → ℱ/Iⁿ⁺¹ℱ → ℱ/Iⁿℱ → 0` is short exact.**

It is the kernel-cokernel sequence of the subsheaf `Iⁿ(ℱ/Iⁿ⁺¹ℱ)` of `ℱ/Iⁿ⁺¹ℱ`
(`Stacks.Algebraization.idealPowerQuotientShortComplex_shortExact`) with its third term renamed
along `Stacks.BaseAdicFiltration.adicQuotientIso`. -/
theorem gradedShortComplex_shortExact : (gradedShortComplex p I n F).ShortExact := by
  have e : idealPowerQuotientShortComplex (baseIdeal p I) n (adicQuotient p I (n + 1) F) ≅
      gradedShortComplex p I n F :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (adicQuotientShortComplexIso p I n F)
      ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.id_comp _)
  exact ShortComplex.shortExact_of_iso e
    (idealPowerQuotientShortComplex_shortExact (baseIdeal p I) n
      (adicQuotient p I (n + 1) F))

/-! ### The image of the filtration sequence under a left exact functor -/

section FunctorTransport

variable {D : Type u'} [Category.{v'} D] [Abelian D] (G : U.Modules ⥤ D) [G.Additive]

/-- An abelian category has finite biproducts. -/
local instance hasFiniteBiproducts_of_abelian : HasFiniteBiproducts D :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **`R¹G` annihilates the graded piece as soon as it annihilates the special fibre.** The graded
piece is a finite direct sum of copies of `ℱ/Iℱ`, and a right derived functor of an additive
functor is additive, hence annihilates a finite biproduct of objects it annihilates
(`CategoryTheory.Functor.isZero_obj_biproduct`). -/
theorem isZero_rightDerived_one_gradedPiece_of_additive [IsNoetherianRing A] [I.IsMaximal]
    (hflat : FlatStalks p F)
    (h : IsZero ((G.rightDerived 1).obj (specialFibre p I F))) :
    IsZero ((G.rightDerived 1).obj ((gradedPiece p I n F).toSheafOfModules)) := by
  obtain ⟨k, ⟨iso⟩⟩ := exists_isoDirectSum_gradedPiece p I n F hflat
  exact IsZero.of_iso
    (Functor.isZero_obj_biproduct (G.rightDerived 1)
      (fun _ : Fin k => specialFibre p I F) fun _ => h)
    (((G.rightDerived 1).mapIso iso).symm)

/-- **The image of the filtration sequence under a left exact additive functor.** Given that `R¹G`
annihilates the special fibre `ℱ/Iℱ`, the sequence

```
0 ⟶ G(Iⁿ(ℱ/Iⁿ⁺¹ℱ)) ⟶ G(ℱ/Iⁿ⁺¹ℱ) ⟶ G(ℱ/Iⁿℱ) ⟶ 0
```

is short exact.  Left exactness of `G` gives exactness and monomorphy; surjectivity on the right
is the vanishing of `R¹G` on the graded piece, which
`Stacks.BaseAdicFiltration.isZero_rightDerived_one_gradedPiece_of_additive` supplies. -/
theorem shortExact_map_gradedShortComplex [IsNoetherianRing A] [I.IsMaximal]
    [PreservesFiniteLimits G] (hflat : FlatStalks p F)
    (h : IsZero ((G.rightDerived 1).obj (specialFibre p I F))) :
    ((gradedShortComplex p I n F).map G).ShortExact :=
  Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one G
    (gradedShortComplex_shortExact p I n F)
    (isZero_rightDerived_one_gradedPiece_of_additive p I n F G hflat h)

/-- **The first term of the image sequence is a finite direct sum of copies of `G(ℱ/Iℱ)`**, the
number of copies being `dim_{A/I} Iⁿ/Iⁿ⁺¹`: an additive functor carries the decomposition of the
graded piece to a decomposition of its image. -/
theorem exists_isoDirectSum_map_gradedPiece [IsNoetherianRing A] [I.IsMaximal]
    (hflat : FlatStalks p F) :
    ∃ k : ℕ, Nonempty
      ((⨁ fun _ : Fin k => G.obj (specialFibre p I F)) ≅
        G.obj ((gradedPiece p I n F).toSheafOfModules)) := by
  obtain ⟨k, ⟨iso⟩⟩ := exists_isoDirectSum_gradedPiece p I n F hflat
  exact ⟨k, ⟨(G.mapBiproduct (fun _ : Fin k => specialFibre p I F)).symm ≪≫ G.mapIso iso⟩⟩

end FunctorTransport

/-! ### The direct image sequence -/

section Pushforward

variable {V : Scheme.{u}} (f : U ⟶ V)

/-- **`R¹f_*` annihilates the graded piece as soon as it annihilates the special fibre.** The
graded piece is a finite direct sum of copies of `ℱ/Iℱ`, and a right derived functor of an
additive functor is additive, hence annihilates a finite biproduct of objects it annihilates
(`CategoryTheory.Functor.isZero_obj_biproduct`).

For `ℱ = 𝒪_U` and `I` the maximal ideal of an Artinian local base this is the step of
[Stacks, Tag 0E3X] reading `R¹f_*(𝔪ⁱ𝒪_U/𝔪ⁱ⁺¹𝒪_U) = 0` off `R¹f_*𝒪_X = 0`. -/
theorem isZero_rightDerived_one_gradedPiece [IsNoetherianRing A] [I.IsMaximal]
    (hflat : FlatStalks p F)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj (specialFibre p I F))) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      ((gradedPiece p I n F).toSheafOfModules)) :=
  isZero_rightDerived_one_gradedPiece_of_additive p I n F (Scheme.Modules.pushforward f) hflat h

/-- **The direct image of the filtration sequence.**  Given that `R¹f_*` annihilates the special
fibre `ℱ/Iℱ`, the sequence

```
0 ⟶ f_*(Iⁿ(ℱ/Iⁿ⁺¹ℱ)) ⟶ f_*(ℱ/Iⁿ⁺¹ℱ) ⟶ f_*(ℱ/Iⁿℱ) ⟶ 0
```

is short exact.  Left exactness of direct image is automatic; surjectivity on the right is the
vanishing of `R¹f_*` on the graded piece, which
`Stacks.BaseAdicFiltration.isZero_rightDerived_one_gradedPiece` supplies. -/
theorem shortExact_map_pushforward_gradedShortComplex [IsNoetherianRing A] [I.IsMaximal]
    (hflat : FlatStalks p F)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj (specialFibre p I F))) :
    ((gradedShortComplex p I n F).map (Scheme.Modules.pushforward f)).ShortExact :=
  shortExact_map_gradedShortComplex p I n F (Scheme.Modules.pushforward f) hflat h

/-- **The first term of the direct image sequence is a finite direct sum of copies of
`f_*(ℱ/Iℱ)`**, the number of copies being `dim_{A/I} Iⁿ/Iⁿ⁺¹`.

This is the formalization of the source's `(f_*𝒪_X) ⊗_κ 𝔪ⁿ/𝔪ⁿ⁺¹`: direct image is additive, so
it carries the decomposition of the graded piece to a decomposition of its direct image. -/
theorem exists_isoDirectSum_pushforward_gradedPiece [IsNoetherianRing A] [I.IsMaximal]
    (hflat : FlatStalks p F) :
    ∃ k : ℕ, Nonempty
      ((⨁ fun _ : Fin k => (Scheme.Modules.pushforward f).obj (specialFibre p I F)) ≅
        (Scheme.Modules.pushforward f).obj ((gradedPiece p I n F).toSheafOfModules)) :=
  exists_isoDirectSum_map_gradedPiece p I n F (Scheme.Modules.pushforward f) hflat

/-- **The sequence [Stacks, Tag 0E3X] reads backwards by induction, over an Artinian local
base.** For `A` Artinian local with maximal ideal `𝔪`, `ℱ` flat over `A` at every point and
`R¹f_*(ℱ/𝔪ℱ) = 0`, there is a `k` — namely `dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹` — and a short exact sequence

```
0 ⟶ ⨁_{i<k} f_*(ℱ/𝔪ℱ) ⟶ f_*(ℱ/𝔪ⁿ⁺¹ℱ) ⟶ f_*(ℱ/𝔪ⁿℱ) ⟶ 0 ,
```

which for `ℱ = 𝒪_U` is the source's

```
0 → (f_*𝒪_X) ⊗_κ 𝔪ⁿ/𝔪ⁿ⁺¹ → f_*(𝒪_U/𝔪ⁿ⁺¹𝒪_U) → f_*(𝒪_U/𝔪ⁿ𝒪_U) → 0 .
```

The sequence is the pushforward of `Stacks.BaseAdicFiltration.gradedShortComplex` with its first
term rewritten. -/
theorem exists_shortExact_pushforward_of_isArtinianRing [IsArtinianRing A] [IsLocalRing A]
    (hflat : FlatStalks p F)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (specialFibre p (IsLocalRing.maximalIdeal A) F))) :
    ∃ (k : ℕ) (S : ShortComplex V.Modules), S.ShortExact ∧
      Nonempty (S.X₁ ≅
        (⨁ fun _ : Fin k => (Scheme.Modules.pushforward f).obj
          (specialFibre p (IsLocalRing.maximalIdeal A) F))) ∧
      Nonempty (S.X₂ ≅ (Scheme.Modules.pushforward f).obj
        (adicQuotient p (IsLocalRing.maximalIdeal A) (n + 1) F)) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward f).obj
        (adicQuotient p (IsLocalRing.maximalIdeal A) n F)) := by
  obtain ⟨k, ⟨iso⟩⟩ := exists_isoDirectSum_pushforward_gradedPiece p
    (IsLocalRing.maximalIdeal A) n F f hflat
  exact ⟨k, (gradedShortComplex p (IsLocalRing.maximalIdeal A) n F).map
      (Scheme.Modules.pushforward f),
    shortExact_map_pushforward_gradedShortComplex p (IsLocalRing.maximalIdeal A) n F f hflat h,
    ⟨iso.symm⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

end Pushforward

end Stacks.BaseAdicFiltration

end

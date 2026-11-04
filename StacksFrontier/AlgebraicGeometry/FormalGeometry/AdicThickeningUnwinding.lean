module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicThickeningCoherentSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedImmersionAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization.AdicSystem
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme

/-!
# Unwinding the completion functor along the adic thickenings

**Stacks 088F** restates Stacks 088E geometrically, against systems of coherent modules on the
adic thickenings `Xₙ = X ×_{Spec A} Sₙ`. The library's carrier for 088E, however, is stated
against `Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f)` — inverse systems of
coherent `𝒪_X`-modules annihilated by the powers of `𝓘 = I · 𝒪_X`, with quotient transitions —
and the two encodings are not the same data. Passing between them is the bookkeeping the remark
performs silently, and this file carries it out.

The bridge is one isomorphism. Write `vₙ : Xₙ ⟶ X` for the projection
`pullback.fst f (adicThickeningι A I n)`. It is a closed immersion whose ideal sheaf is exactly
`𝓘 ⁿ⁺¹`, so Stacks 0EL1 identifies the `n`-th term of the `𝓘`-adic completion of a coherent
`𝒪_X`-module `ℱ` with the direct image of its restriction to `Xₙ`:

  `ℱ / 𝓘 ⁿ⁺¹ ℱ  ≅  (vₙ)_* (ℱ|_{Xₙ})`.

Read left to right this computes the terms of `Stacks.Algebraization.completionFunctor` in the
thickening picture; read right to left, together with full faithfulness of `(vₙ)_*` along a
closed immersion, it recovers an isomorphism of modules *on* `Xₙ` from an isomorphism of their
direct images. Those are the two directions the unwinding needs.

## The identification the module docstring of `AdicThickeningCoherentSystem` calls missing

That file records the unwinding as unavailable because the comparison "needs in addition an
identification of `adicBaseChange A I f n` with the closed subscheme of
`baseIdealSheaf A I f ^ (n + 1)` … and nothing in the library provides it". That assessment is
too pessimistic, and this file does not supply such an identification. Stacks 0EL1 is available in
the library for an **arbitrary** closed immersion presenting the infinitesimal neighbourhood —
`Stacks.Algebraization.idealQuotientPushforwardIso`, whose hypothesis is only `v.ker = 𝓘 ⁿ⁺¹` for
the morphism `v` one actually has. The fibre product `Xₙ` is such a presentation, by
`AlgebraicGeometry.AdicFiniteAlgebra.ker_adicBaseChange_fst`, so no comparison with
`Scheme.IdealSheafData.subscheme` is needed anywhere.

## Main definitions

* `AlgebraicGeometry.adicThickeningCompletionPushforwardIso` — the isomorphism displayed above,
  identifying the `n`-th term of the `𝓘`-adic completion with the direct image of the restriction
  to the `n`-th thickening.

## Main results

* `AlgebraicGeometry.adicThickeningCompletionPushforwardIso_projection` — the normalization: the
  isomorphism carries the projection to a term of the completion to the unit of the
  pullback–pushforward adjunction. Since the projection is an epimorphism this pins it down.
* `AlgebraicGeometry.adicThickeningCompletionPushforwardIso_naturality` — it is natural in the
  coherent module, so it is an isomorphism of functors and not merely a termwise coincidence.
* `AlgebraicGeometry.adicThickeningCompletion_iso_of_pushforward_iso` — the recovery direction:
  an isomorphism of the direct images of two modules on `Xₙ` comes from an isomorphism of the
  modules themselves, by full faithfulness of direct image along a closed immersion.

## Implementation notes

`IsLocallyNoetherian X` is taken as an instance binder rather than derived inside each statement
from `IsNoetherianRing A` and `LocallyOfFiniteType f`. It is the hypothesis
`Stacks.Algebraization.completionFunctor` actually carries, and deriving it in the statement — as
`Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper` must, having only a proper
`f` — forces a `letI` into the type and blocks stating naturality as an equation between
composites. `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` supplies it at every call
site that has the ring-level hypotheses instead.

The kernel computation is `Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst` for
the ideal `I ^ (n + 1)`, moved across
`Stacks.Cohomology.FormalFunctions.baseIdealSheaf_pow`; it type-checks because
`adicThickeningι A I n` is a `def` that unfolds to
`Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))`, so the two spellings of the
thickening are definitionally equal though not syntactically so.

Naturality is proved by cancelling the epimorphism
`Stacks.Algebraization.completionProjection`: against it the left side becomes the unit at the
source composed with the completed map, by `Stacks.Algebraization.completionFunctor_map_quotient`,
and the right side the same composite read through the unit at the target — which is the
naturality of the adjunction unit. Nothing rewrites under `completionFunctor`.

The two rearrangements that step performs are done by the private lemmas of the first section,
stated in an abstract category and applied as terms, rather than by `rw` on the goals
themselves. `AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` and
the coherent modules live in a full subcategory of the latter; the two presentations reach their
category instance by different paths, so a composite mixing them is not type-correct at
`implicit` transparency and associativity rewriting on it fails.

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf baseIdealSheaf_pow)

universe u

namespace AlgebraicGeometry

open Stacks.Algebraization

/-! ### Rearranging composites that mix the two presentations

Plain category theory, used below on composites that mix the coherent modules with
`AlgebraicGeometry.Scheme.Modules`; see the implementation notes for why these are applied as
terms rather than rewritten. -/

section Rearrange

variable {C : Type*} [Category C]

/-- **Cancelling a retraction pair in the middle of a composite.** -/
private theorem comp_comp_eq_of_comp_eq_id {W Y Z V : C} (a : W ⟶ Y) {m : Y ⟶ Z} {n : Z ⟶ Y}
    (hm : m ≫ n = 𝟙 Y) (p : Y ⟶ V) : (a ≫ m) ≫ n ≫ p = a ≫ p := by
  rw [Category.assoc, ← Category.assoc m, hm, Category.id_comp]

/-- **Transporting a naturality square across two normalizations.** The shape of the naturality
step below: the two composites out of `W` agree because each factors through a normalization — `d`
through `g` and `a` through `w` — and the square relating `c` to `w` commutes. -/
private theorem comp_comp_eq_comp_comp_of_square {W Y₁ Y₂ Z T V : C} {a : W ⟶ Y₁} {b : Y₁ ⟶ Y₂}
    {e : Y₂ ⟶ Z} {c : W ⟶ T} {d : T ⟶ Y₂} {u : Y₁ ⟶ V} {v : V ⟶ Z} {g : T ⟶ Z} {w : W ⟶ V}
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ e = g) (h₃ : a ≫ u = w) (h₄ : c ≫ g = w ≫ v) :
    a ≫ b ≫ e = a ≫ u ≫ v := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, h₄, ← h₃, Category.assoc]

end Rearrange

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### The unwinding -/

variable [IsLocallyNoetherian X]

/-- **The terms of the adic completion are the direct images of the restrictions to the
thickenings.** For a coherent `𝒪_X`-module `ℱ`,

  `ℱ / 𝓘 ⁿ⁺¹ ℱ  ≅  (vₙ)_* (ℱ|_{Xₙ})`,  `vₙ : Xₙ ⟶ X`,

the left side being the `n`-th term of `Stacks.Algebraization.completionFunctor` and the right the
direct image of `AlgebraicGeometry.adicThickeningCompletion`.

This is Stacks 0EL1 at the presentation of the `(n+1)`-st infinitesimal neighbourhood given by the
fibre product `Xₙ`, whose ideal sheaf is `𝓘 ⁿ⁺¹` by
`AlgebraicGeometry.AdicFiniteAlgebra.ker_adicBaseChange_fst`. It is the bookkeeping between the two
encodings of a formal system that Stacks 088F performs silently: `Coh(X, 𝓘)` on the left of the
remark's arrow, systems of modules on the thickenings on the right. -/
public def adicThickeningCompletionPushforwardIso
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    ((completionFunctor X (baseIdealSheaf A I f)).obj F).obj.obj (op n) ≅
      (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).obj
        (adicThickeningCompletion A I f F.obj n) :=
  haveI : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  eqToIso (completionFunctor_obj X (baseIdealSheaf A I f) F n) ≪≫
    idealQuotientPushforwardIso (baseIdealSheaf A I f) (n + 1) F.obj
      (pullback.fst f (adicThickeningι A I n))
      (AdicFiniteAlgebra.ker_adicBaseChange_fst A I f n)

/-- **The normalization of the unwinding.** The canonical projection of `ℱ` onto the `n`-th term
of its completion, followed by the identification, is the unit of the pullback–pushforward
adjunction along `Xₙ ⟶ X`. Since the projection is an epimorphism
(`Stacks.Algebraization.epi_completionProjection`), this determines the identification uniquely. -/
@[simp]
public theorem adicThickeningCompletionPushforwardIso_projection
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    completionProjection X (baseIdealSheaf A I f) F n ≫
        (adicThickeningCompletionPushforwardIso A I f F n).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.fst f (adicThickeningι A I n))).unit.app F.obj :=
  have : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  (comp_comp_eq_of_comp_eq_id (C := X.Modules)
      (cokernel.π (C := X.Modules)
        ((idealPowerMultiple (baseIdealSheaf A I f) (n + 1) F.obj).ι))
      ((eqToHom_trans (completionFunctor_obj X (baseIdealSheaf A I f) F n).symm
        (completionFunctor_obj X (baseIdealSheaf A I f) F n)).trans (eqToHom_refl _ _))
      _).trans
    (idealQuotientPushforwardMap_π (baseIdealSheaf A I f) (n + 1) F.obj
      (pullback.fst f (adicThickeningι A I n)) (AdicFiniteAlgebra.ker_adicBaseChange_fst A I f n))

/-- **The unwinding is natural in the coherent module.** So the two encodings of a formal system
are identified compatibly with morphisms, and the isomorphism above is an isomorphism of functors
rather than a termwise coincidence.

Both sides are tested against the epimorphism
`Stacks.Algebraization.completionProjection`. Against it the left side is the unit at `F`
followed by the completed map, by `Stacks.Algebraization.completionFunctor_map_quotient` and the
normalization above, and the right side is the unit at `G` preceded by the map — which is the
naturality of the adjunction unit. -/
public theorem adicThickeningCompletionPushforwardIso_naturality
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (φ : F ⟶ G) (n : ℕ) :
    ((completionFunctor X (baseIdealSheaf A I f)).map φ).hom.app (op n) ≫
        (adicThickeningCompletionPushforwardIso A I f G n).hom =
      (adicThickeningCompletionPushforwardIso A I f F n).hom ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map
          ((Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map φ.hom) := by
  have hepi := epi_completionProjection X (baseIdealSheaf A I f) F n
  refine (@cancel_epi _ _ _ _ _ (completionProjection X (baseIdealSheaf A I f) F n) hepi _ _).mp ?_
  exact comp_comp_eq_comp_comp_of_square (C := X.Modules)
    (completionFunctor_map_quotient X (baseIdealSheaf A I f) φ n)
    (adicThickeningCompletionPushforwardIso_projection A I f G n)
    (adicThickeningCompletionPushforwardIso_projection A I f F n)
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst f (adicThickeningι A I n))).unit.naturality φ.hom)

/-! ### Recovering an isomorphism on the thickening -/

/-- **An isomorphism of direct images comes from an isomorphism on the thickening.** Direct image
along the closed immersion `Xₙ ⟶ X` is fully faithful (Stacks 087T, as
`Stacks.ClosedImmersion.fullyFaithfulPushforward`), so it reflects isomorphisms through its
preimage.

This is the direction in which the unwinding is consumed: an algebraization produced on `X` is
compared with a prescribed system through the direct images of the restrictions, and this carries
that comparison back to the modules on `Xₙ` that the systems of
`AlgebraicGeometry.AdicCoherentModuleSystem` are made of. -/
public def adicThickeningCompletion_iso_of_pushforward_iso (n : ℕ)
    {G H : (adicBaseChange A I f n).Modules}
    (e : (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).obj G ≅
      (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).obj H) :
    G ≅ H :=
  (Stacks.ClosedImmersion.fullyFaithfulPushforward
    (pullback.fst f (adicThickeningι A I n))).preimageIso e

/-- **The unwinding, in the form in which an algebraization is consumed.** Suppose a coherent
`𝒪_X`-module `ℱ` is given together with, for every `n`, an identification of the `n`-th term of
its `𝓘`-adic completion with the direct image of a prescribed module `S n` on the `n`-th
thickening. Then `ℱ|_{Xₙ} ≅ S n` for every `n`.

This is what turns an algebraization produced on `X` — an object of
`Stacks.Algebraization.CoherentModulesProperOver` whose completion matches a prescribed formal
system — into the thickening-by-thickening comparison that
`AlgebraicGeometry.AdicCoherentModuleSystem` and the hypothesis
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` are stated with. The hypothesis is phrased
termwise, with no inverse system assembled, so it is available from an isomorphism of systems by
evaluating at `n` and needs none of the transition data.

Both of the file's directions are used: the unwinding rewrites the term of the completion as a
direct image, and full faithfulness of direct image along the closed immersion `Xₙ ⟶ X` brings the
resulting comparison back down to `Xₙ`. -/
public def adicThickeningCompletion_iso_of_completion_term_iso
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (S : ∀ n : ℕ, (adicBaseChange A I f n).Modules)
    (e : ∀ n : ℕ, ((completionFunctor X (baseIdealSheaf A I f)).obj F).obj.obj (op n) ≅
      (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).obj (S n))
    (n : ℕ) :
    adicThickeningCompletion A I f F.obj n ≅ S n :=
  adicThickeningCompletion_iso_of_pushforward_iso A I f n
    ((adicThickeningCompletionPushforwardIso A I f F n).symm ≪≫ e n)

end AlgebraicGeometry

end

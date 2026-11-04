module

public import StacksFrontier.AlgebraicGeometry.AffineBlowupLift.Chart
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Blowup
public import StacksFrontier.AlgebraicGeometry.Lift.Dense
public import StacksFrontier.AlgebraicGeometry.Lift.Generator

/-!
# The existence half of Tag 0806: a morphism to the blowup, glued from affine charts

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on it, and `f : Y ⟶ X` a morphism along
which the inverse image of `I` is an effective Cartier divisor. This file produces a morphism
`Y ⟶ Bl_I(X)` over `X` — the hypothesis `hlift` of the reduction of [Stacks, Tag 0806] in
`StacksFrontier/AlgebraicGeometry/BlowUpUniversal/Basic.lean` and of its two successors.

Nothing new is proved about blowups. The three inputs are each already available:

* `Stacks.AlgebraicGeometry.AffineBlowupLift.toBlowUp` builds the morphism out of an affine
  scheme `Spec B` whenever `B` is a `Γ(X, U)`-algebra in which the image of a section
  `a ∈ I.ideal U` is a nonzerodivisor generating `I.ideal U · B`, together with
  `toBlowUp_blowUpToBase` placing it over `X`;
* `Stacks.Tag0806Lift.exists_affineOpen_section_generator` produces exactly such data at every
  point of `Y`, with `B = Γ(Y, V)` for an affine open `V` of `Y` inside `f⁻¹(U)`;
* `Stacks.Tag0806Lift.over_hom_unique_of_dense` — the already-proved uniqueness half of
  Tag 0806, weakened to take the density directly — makes the local morphisms agree on
  overlaps, so `AlgebraicGeometry.Scheme.Cover.glueMorphisms` glues them.

## Main results

* `Stacks.Tag0806Lift.exists_affineOpen_hom_blowUp`: the local lift, on an affine open
  neighbourhood of any point of `Y`.
* `Stacks.Tag0806Lift.nonempty_over_hom_blowUp`: **the `hlift` hypothesis**, at the exact shape
  the three reductions ask for.
* `Stacks.Tag0806Lift.nonempty_isTerminal_blowUp_of'''`: the reduction of [Stacks, Tag 0806]
  with **two** hypotheses, both of them Tag 02OS.

## Implementation notes

**The overlap compatibility needs no restriction-stability statement about effective Cartier
divisors.** `Stacks.AlgebraicGeometry.BlowUpUniversal.over_hom_unique` asks that the inverse
image of the centre be an effective Cartier divisor on the source, and the overlap of two
members of the cover is an open subscheme of `Y`, so applying it there would require that
`Stacks.Divisors.IsEffectiveCartierDivisor` restricts to an open subscheme — a statement about
invertibility of a sheaf of modules transported across an open immersion, which genuinely
needs a compiler escape. It is not needed: `over_hom_unique`
uses that hypothesis *only* to produce the scheme-theoretic density of the complement, and
density restricts along any open immersion for free
(`isSchemeTheoreticallyDense_preimage`), because
`AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense` already quantifies over every open
of the ambient scheme.

**The base compatibility is a four-rewrite computation.** `toBlowUp_blowUpToBase` states the
composite with the blowup morphism as `Spec.map (algebraMap Γ(X, U) Γ(Y, V))` followed by
`U.isoSpec.inv ≫ U.ι`. The algebra structure is `(f.appLE U V).hom.toAlgebra`, so the first
factor is `Spec.map (f.appLE U V)`; the second is `U.fromSpec` by
`AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι`; and
`AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec` turns the composite into
`V.fromSpec ≫ f`. Precomposing with `V.isoSpec.hom` and using
`AlgebraicGeometry.IsAffineOpen.isoSpec_hom_fromSpec` leaves `V.ι ≫ f`.

## What is not claimed

**No `@[stacks 0806]` attribute is attached.** Tag 0806 carries a single unlabelled tag, so
there is no partial credit, and one hypothesis of the reduction is still open: `hcartier`, which
is [Stacks, Tag 02OS (2)] — that the exceptional divisor is an effective Cartier divisor on the
blowup. Its affine-local input is available at the blowup charts
(`AlgebraicGeometry.affineBlowup_isRegular` and `AlgebraicGeometry.affineBlowup_ideal_map`), but
turning an affine-local nonzerodivisor description into invertibility of the ideal sheaf is the
**reverse** direction of [Stacks, Tag 01WS], which this repository does not yet have — only the
forward direction, `Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor`, is proved.

**No attribute from the chapter on relative `Proj` either.** The morphism into the blowup is
glued here directly from affine charts. The general description of morphisms into a relative
`Proj` by invertible quotients of the graded algebra is not what this file proves, and no tag of
that chapter is claimed by it.

## References

* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.BlowUpUniversal

universe u

namespace Stacks.Tag0806Lift

variable {X : Scheme.{u}}

/-- **The local lift.** Every point of `Y` has an affine open neighbourhood `V` carrying a
morphism `V ⟶ Bl_I(X)` over `X`.

`exists_affineOpen_section_generator` supplies an affine open `U` of `X`, the affine `V` inside
`f⁻¹(U)`, and a section `a ∈ I.ideal U` whose image generates the restricted ideal by a
nonzerodivisor; `Stacks.AlgebraicGeometry.AffineBlowupLift.toBlowUp` then maps
`Spec Γ(Y, V) ≅ V` into the blowup through the chart attached to `a`. -/
theorem exists_affineOpen_hom_blowUp {Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f)) (y : Y) :
    ∃ (V : Y.affineOpens) (g : (V : Y.Opens).toScheme ⟶ blowUp I),
      y ∈ (V : Set Y) ∧ g ≫ blowUpToBase I = (V : Y.Opens).ι ≫ f := by
  obtain ⟨U, hU⟩ := Stacks.Divisors.exists_affineOpens_mem (f y)
  obtain ⟨V, hVU, hyV, a, haJ, hnzd, hgen⟩ :=
    exists_affineOpen_section_generator I f hD U (show y ∈ f ⁻¹ᵁ (U : X.Opens) from hU)
  let _ : Algebra (X.presheaf.obj (op (U : X.Opens))) Γ(Y, (V : Y.Opens)) :=
    (f.appLE (U : X.Opens) (V : Y.Opens) hVU).hom.toAlgebra
  have halg : (algebraMap (X.presheaf.obj (op (U : X.Opens))) Γ(Y, (V : Y.Opens))) =
      (f.appLE (U : X.Opens) (V : Y.Opens) hVU).hom :=
    RingHom.algebraMap_toAlgebra _
  have hnzd' : algebraMap (X.presheaf.obj (op (U : X.Opens))) Γ(Y, (V : Y.Opens))
      ((⟨a, haJ⟩ : I.ideal U) : X.presheaf.obj (op (U : X.Opens))) ∈
      nonZeroDivisors Γ(Y, (V : Y.Opens)) := by
    rwa [halg]
  have hIB' : (I.ideal U).map
        (algebraMap (X.presheaf.obj (op (U : X.Opens))) Γ(Y, (V : Y.Opens))) =
      Ideal.span {algebraMap (X.presheaf.obj (op (U : X.Opens))) Γ(Y, (V : Y.Opens))
        ((⟨a, haJ⟩ : I.ideal U) : X.presheaf.obj (op (U : X.Opens)))} := by
    rwa [halg, ← Stacks.IdealSheaf.ideal_comap_appLE I f U V hVU]
  refine ⟨V, V.2.isoSpec.hom ≫
    Stacks.AlgebraicGeometry.AffineBlowupLift.toBlowUp I U ⟨a, haJ⟩ _ hnzd' hIB', hyV, ?_⟩
  rw [Category.assoc, Stacks.AlgebraicGeometry.AffineBlowupLift.toBlowUp_blowUpToBase,
    show CommRingCat.ofHom
        (algebraMap (X.presheaf.obj (op (U : X.Opens))) Γ(Y, (V : Y.Opens))) =
      f.appLE (U : X.Opens) (V : Y.Opens) hVU from by rw [halg]; rfl]
  have hUa : IsAffineOpen (U : X.Opens) := U.2
  have hVa : IsAffineOpen (V : Y.Opens) := V.2
  show hVa.isoSpec.hom ≫ Spec.map (f.appLE (U : X.Opens) (V : Y.Opens) hVU) ≫
    hUa.fromSpec = _
  rw [IsAffineOpen.SpecMap_appLE_fromSpec f hUa hVa hVU, ← Category.assoc,
    IsAffineOpen.isoSpec_hom_fromSpec]

/-- **The `hlift` hypothesis of [Stacks, Tag 0806], discharged.** Every object of `Sch/X` whose
inverse image of the centre is an effective Cartier divisor admits a morphism to the blowup over
the base.

`Y` is covered by the affine opens of `exists_affineOpen_hom_blowUp`; the local morphisms agree
on overlaps by `over_hom_unique_of_dense`, whose density hypothesis is supplied on the overlap by
`isSchemeTheoreticallyDense_preimage` from the density on `Y`; and
`AlgebraicGeometry.Scheme.Cover.glueMorphisms` glues them. -/
theorem nonempty_over_hom_blowUp (I : X.IdealSheafData)
    (hmono : Mono (blowUpToBase I ∣_ supportCompl I))
    (Z : Over X) (hZ : IsCartierOver I Z) :
    Nonempty (Z ⟶ Over.mk (blowUpToBase I)) := by
  choose V g hmem hcomm using fun y : Z.left => exists_affineOpen_hom_blowUp I Z.hom hZ y
  -- The complement of the divisor is scheme-theoretically dense in `Z.left`.
  have hdZ : Scheme.Opens.IsSchemeTheoreticallyDense (Z.hom ⁻¹ᵁ supportCompl I) := by
    rw [preimage_supportCompl]
    exact Stacks.CartierAffineLocal.isSchemeTheoreticallyDense_supportCompl _ hZ
  -- The local morphisms agree on overlaps, by uniqueness over the dense complement.
  have hglue : ∀ x y : Z.left,
      pullback.fst (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫ g x =
      pullback.snd (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫ g y := by
    intro x y
    have hq : pullback.fst (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫
        (V x : Z.left.Opens).ι =
        pullback.snd (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫
          (V y : Z.left.Opens).ι := pullback.condition
    have hdense : Scheme.Opens.IsSchemeTheoreticallyDense
        ((Over.mk (pullback.fst (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫
          (V x : Z.left.Opens).ι ≫ Z.hom) : Over X).hom ⁻¹ᵁ supportCompl I) := by
      show Scheme.Opens.IsSchemeTheoreticallyDense
        ((pullback.fst (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫
          (V x : Z.left.Opens).ι ≫ Z.hom) ⁻¹ᵁ supportCompl I)
      rw [← Category.assoc, Scheme.Hom.comp_preimage]
      exact isSchemeTheoreticallyDense_preimage _ hdZ
    have h1 : (pullback.fst (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫ g x) ≫
        blowUpToBase I =
        pullback.fst (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫
          (V x : Z.left.Opens).ι ≫ Z.hom := by
      rw [Category.assoc, hcomm x]
    have h2 : (pullback.snd (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫ g y) ≫
        blowUpToBase I =
        pullback.fst (V x : Z.left.Opens).ι (V y : Z.left.Opens).ι ≫
          (V x : Z.left.Opens).ι ≫ Z.hom := by
      rw [Category.assoc, hcomm y, ← Category.assoc, ← hq, Category.assoc]
    exact congrArg (fun h : (Over.mk (pullback.fst (V x : Z.left.Opens).ι
          (V y : Z.left.Opens).ι ≫ (V x : Z.left.Opens).ι ≫ Z.hom) : Over X) ⟶
            Over.mk (blowUpToBase I) => h.left)
      (over_hom_unique_of_dense I hmono
        (Stacks.AlgebraicGeometry.BlowUpSeparatedInput.isSeparated_blowUpToBase I) hdense
        (Over.homMk _ h1) (Over.homMk _ h2))
  -- The affine opens cover `Z.left`, so the local morphisms glue.
  obtain ⟨u, hu⟩ : ∃ u : Z.left ⟶ blowUp I, u ≫ blowUpToBase I = Z.hom := by
    let 𝒰 : Z.left.OpenCover := Scheme.Cover.mkOfCovers Z.left
      (fun y => ((V y : Z.left.Opens)).toScheme) (fun y => (V y : Z.left.Opens).ι)
      (fun x => ⟨x, ⟨x, hmem x⟩, rfl⟩) (fun _ => inferInstance)
    refine ⟨𝒰.glueMorphisms g hglue, Scheme.Cover.hom_ext 𝒰 _ _ fun x => ?_⟩
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms 𝒰 g hglue x]
    exact hcomm x
  exact ⟨Over.homMk u hu⟩

/-- **The reduction of [Stacks, Tag 0806] with only the two assertions of Tag 02OS left.** The
blowup of `X` in `I` is a final object of the full subcategory of `Sch/X` whose objects have
effective Cartier inverse image of the centre, given

* `hcartier`: the exceptional divisor is an effective Cartier divisor on the blowup —
  [Stacks, Tag 02OS (2)];
* `hiso`: the blowup morphism is an isomorphism over the complement of the centre —
  [Stacks, Tag 02OS (1)].

The other three inputs of the Stacks proof are now theorems: separatedness
([Stacks, Tag 01O2]) is `Stacks.AlgebraicGeometry.BlowUpSeparatedInput.isSeparated_blowUpToBase`,
the density ([Stacks, Tag 07ZU]) is
`Stacks.CartierAffineLocal.forall_isSchemeTheoreticallyDense_supportCompl`, and the existence of
a lift is `nonempty_over_hom_blowUp` above.

No `@[stacks 0806]` attribute is attached: two hypotheses Tag 0806 does not carry remain, and
Tag 0806 has a single unlabelled tag, so there is no partial credit. -/
theorem nonempty_isTerminal_blowUp_of''' (I : X.IdealSheafData)
    (hcartier : IsCartierOver I (Over.mk (blowUpToBase I)))
    (hiso : IsIso (blowUpToBase I ∣_ supportCompl I)) :
    ∃ h : IsCartierOver I (Over.mk (blowUpToBase I)),
      Nonempty (IsTerminal (⟨Over.mk (blowUpToBase I), h⟩ : CartierOver I)) := by
  have hmono : Mono (blowUpToBase I ∣_ supportCompl I) := by
    have := hiso
    infer_instance
  exact Stacks.CartierAffineLocal.nonempty_isTerminal_blowUp_of'' I hcartier hiso
    (nonempty_over_hom_blowUp I hmono)

end Stacks.Tag0806Lift

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagonal of a morphism of affine schemes, and its conormal data

[Stacks, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2) identifies the sheaf of relative
differentials of `f : X ⟶ S` with the conormal sheaf of the diagonal `Δ : X ⟶ X ×_S X`. The
affine case of that identification is Mathlib's *definition* of `KaehlerDifferential`: for
`Spec S ⟶ Spec R` the diagonal is `Spec` of the multiplication map `S ⊗[R] S ⟶ S`, the ideal
of that closed immersion is `KaehlerDifferential.ideal R S`, and `Ω[S⁄R]` is by definition its
`Ideal.Cotangent`. This file assembles the four facts that make that sentence usable: the
factorization, the closed immersion, the ideal, and — the part that fixes the *sign* — the
identification of the section `p₂^♯ b - p₁^♯ b` of [Stacks, Tag 08S2] with the element
`1 ⊗ b - b ⊗ 1` whose class is `d b`.

It also records the coborder bookkeeping that a *closed* diagonal collapses: the construction
of the conormal sheaf goes through `AlgebraicGeometry.Scheme.Hom.coborderRange`, and for a
closed immersion that open is the whole target, so the "restricted diagonal" of the tag is the
diagonal itself up to the canonical identification `↑(⊤ : X.Opens) ≅ X`.

## Main results

* `Stacks.DiagonalConormal.coborderRange_eq_top`: the coborder neighbourhood of the image of a
  *closed* immersion of schemes is `⊤`. Nothing affine is used.
* `Stacks.DiagonalConormal.liftCoborder_comp_eq`: consequently its canonical closed
  factorization is the morphism itself, read through `AlgebraicGeometry.Scheme.isoOfEq` and
  `AlgebraicGeometry.Scheme.topIso`.
* `Stacks.DiagonalConormal.ker_lmulHom`: the ideal of the affine diagonal is
  `KaehlerDifferential.ideal`, by `rfl`.
* `Stacks.DiagonalConormal.kaehlerDifferential_eq_cotangent` and
  `Stacks.DiagonalConormal.toCotangent_one_tmul_sub_tmul_one`: `Ω[S⁄R]` *is* the conormal
  module `I ⧸ I²` of that ideal, and the generator `1 ⊗ b - b ⊗ 1` goes to `d b`; both by
  `rfl`.
* `Stacks.DiagonalConormal.diagonal_specMap_eq` and
  `Stacks.DiagonalConormal.isClosedImmersion_diagonal_specMap`: the diagonal of a morphism of
  affine schemes is `Spec` of the multiplication map followed by an isomorphism, hence a
  closed immersion; and `Stacks.DiagonalConormal.coborderRange_diagonal_specMap_eq_top`.
* `Stacks.DiagonalConormal.appTop_fst_specMap`,
  `Stacks.DiagonalConormal.appTop_snd_specMap` and
  `Stacks.DiagonalConormal.appTop_snd_sub_fst_specMap`: **the sign.** On global sections the
  two projections of `X ×_S X` are the two inclusions `b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b`, so the
  section `p₂^♯ b - p₁^♯ b` of [Stacks, Tag 08S2] is `1 ⊗ b - b ⊗ 1`. This is the element
  Mathlib's `KaehlerDifferential.D` is built from, so the tag's sign convention and Mathlib's
  agree, with no sign to insert anywhere.
* `Stacks.DiagonalConormal.toCotangent_appTop_snd_sub_fst_specMap`: the two previous groups
  combined — the conormal class of `p₂^♯ b - p₁^♯ b` is `d b`.

## Route

`AlgebraicGeometry.diagonal_SpecMap` is Mathlib's factorization of the affine diagonal and
`AlgebraicGeometry.pullbackSpecIso_inv_fst`, `AlgebraicGeometry.pullbackSpecIso_inv_snd`
identify the two projections after it. Those are equalities of morphisms of schemes; the
section-level statements are obtained by applying `AlgebraicGeometry.Scheme.Hom.comp_appTop`
and then `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`, which computes the map on global
sections of a `Spec.map`. Subtraction passes through because `Scheme.Hom.appTop` is a ring
homomorphism.

The coborder statement is `IsClosed.coborder_eq` applied to the range of a closed immersion,
which is closed by `AlgebraicGeometry.Scheme.Hom.isClosedEmbedding`; `coborderRange` is that
coborder carried into `X.Opens`, so the two sides are compared with
`TopologicalSpace.Opens.ext`.

## Vocabulary

No clause of any tag is stated here, and no `stacks` attribute is attached. This is an input to [Stacks, Tag 08S2] and to the part (2) clauses of
[Stacks, Tag 01R3].

## What is not done

* **No conormal sheaf appears.** Everything here is about the *ideal* of the affine diagonal
  and about `Ideal.Cotangent` of that ideal as a module. The identification of
  `Stacks.Conormal.conormalSheaf` of the diagonal with `Ω[S⁄R]` additionally needs the affine
  model `Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` transported from the
  quotient presentation `Spec (A ⧸ I) ⟶ Spec A` to the surjection presentation
  `Spec.map (lmulHom R S)`; the two differ by the isomorphism of schemes induced by
  `(S ⊗[R] S) ⧸ ker (lmul') ≅ S`. That transport is recorded as missing in the
  "What is not done" section of
  `StacksDraft.AlgebraicGeometry.F3.Conormal.Locality`.
* **Nothing global.** No assembly of these affine identifications into a morphism of sheaves
  on an arbitrary scheme is made here.
* **No statement for a general morphism of `CommRingCat`.** The results are stated for
  `[Algebra R S]` and `Spec.map (CommRingCat.ofHom (algebraMap R S))`, which is the form
  `AlgebraicGeometry.diagonal_SpecMap` is given in. A chart of a general `f : X ⟶ S` arrives
  as a morphism of `CommRingCat`, and converting it needs `RingHom.toAlgebra` as a local
  instance.

## Universe situation

`R` and `S` lie in the same universe `u`: `AlgebraicGeometry.pullbackSpecIso` is stated for
three rings in one universe. `AlgebraicGeometry.Scheme.{u}` for the coborder results, which
carry no further universe constraint.

## Transparency gotchas

`AlgebraicGeometry.Scheme.Hom.coborderRange` takes an `IsImmersion` instance argument, so an
equation in `f` cannot be rewritten inside it: `rw [← f.liftCoborder_ι]` fails with "motive is
not type correct" because the instance in `f.liftCoborder` would have to change type with it.
`liftCoborder_comp_eq` is therefore assembled with `congrArg` and `Eq.trans` out of
`AlgebraicGeometry.Scheme.homOfLE_ι`, whose statement mentions no instance.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct TopologicalSpace

universe u

namespace Stacks.DiagonalConormal

/-! ### The coborder neighbourhood of a closed immersion -/

/-- **The coborder neighbourhood of the image of a closed immersion is the whole target.**
`AlgebraicGeometry.Scheme.Hom.coborderRange` is the coborder of the range, and the coborder of
a *closed* set is everything. -/
theorem coborderRange_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    f.coborderRange = ⊤ :=
  Opens.ext f.isClosedEmbedding.isClosed_range.coborder_eq

/-- An open which is the whole space, compared with the whole space: the comparison
`AlgebraicGeometry.Scheme.isoOfEq` followed by `AlgebraicGeometry.Scheme.topIso` is the
inclusion of the open. Both identifications are the inclusion `X.homOfLE`, definitionally. -/
theorem isoOfEq_hom_comp_topIso {X : Scheme.{u}} {U : X.Opens} (h : U = ⊤) :
    (X.isoOfEq h).hom ≫ X.topIso.hom = U.ι :=
  X.homOfLE_ι h.le

/-- **The canonical closed factorization of a closed immersion is the morphism itself.** The
conormal sheaf of an immersion `i` is built from `i.liftCoborder : X ⟶ i.coborderRange`; when
`i` is a closed immersion that target is `⊤`, and this records that `i.liftCoborder` is then
`i` read through the canonical identification `↑(⊤ : Y.Opens) ≅ Y`. -/
theorem liftCoborder_comp_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    f.liftCoborder ≫ (Y.isoOfEq (coborderRange_eq_top f)).hom ≫ Y.topIso.hom = f :=
  (congrArg (fun g => f.liftCoborder ≫ g)
    (isoOfEq_hom_comp_topIso (coborderRange_eq_top f))).trans f.liftCoborder_ι

/-! ### The multiplication map and its ideal -/

section Affine

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The multiplication map `S ⊗[R] S ⟶ S`, `a ⊗ b ↦ a * b`, as a morphism of `CommRingCat`.
`Spec` of it is the diagonal of `Spec S ⟶ Spec R`, up to the comparison of the fibre product
with `Spec (S ⊗[R] S)`. -/
noncomputable abbrev lmulHom : CommRingCat.of (S ⊗[R] S) ⟶ CommRingCat.of S :=
  CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := S)).toRingHom

/-- The multiplication map is surjective: `b ⊗ 1` is a preimage of `b`. -/
theorem surjective_lmulHom : Function.Surjective (ConcreteCategory.hom (lmulHom R S)) :=
  fun s => ⟨s ⊗ₜ[R] 1, by simp⟩

/-- `Spec` of the multiplication map is a closed immersion, the map being surjective. -/
instance isClosedImmersion_specMap_lmulHom : IsClosedImmersion (Spec.map (lmulHom R S)) :=
  IsClosedImmersion.spec_of_surjective _ (surjective_lmulHom R S)

/-- **The ideal of the affine diagonal is the Kähler ideal.** `KaehlerDifferential.ideal` is
*defined* as the kernel of the multiplication map, so this holds by `rfl`; it is recorded
because the geometric side names the ideal as a kernel and the differentials side names it as
`KaehlerDifferential.ideal`. -/
theorem ker_lmulHom :
    RingHom.ker (ConcreteCategory.hom (lmulHom R S)) = KaehlerDifferential.ideal R S :=
  rfl

/-- **`Ω[S⁄R]` is the conormal module of the Kähler ideal.** `KaehlerDifferential` is
*defined* as `Ideal.Cotangent` of that ideal, i.e. as `I ⧸ I²`, so this holds by `rfl`. This
is the affine case of [Stacks, Tag 08S2] with no work in it at all; the work in the tag is
making the two sides into sheaves on an arbitrary scheme. -/
@[ega "IV 16.3.1" "affine case", ega "IV 17.13.5" "special case", sga "7 VI 5.5" "special case"]
theorem kaehlerDifferential_eq_cotangent :
    Ω[S⁄R] = (KaehlerDifferential.ideal R S).Cotangent :=
  rfl

/-- `1 ⊗ b - b ⊗ 1` lies in the ideal of the affine diagonal. -/
theorem one_tmul_sub_tmul_one_mem_ker (b : S) :
    (1 : S) ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S) ∈ RingHom.ker (ConcreteCategory.hom (lmulHom R S)) :=
  KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b

/-- **The generator formula of the affine case.** The conormal class of `1 ⊗ b - b ⊗ 1` is
`d b`. `KaehlerDifferential.D` is defined by this very formula, so it holds by `rfl`; the
content is that the ideal is spelled as `RingHom.ker` of the multiplication map, which is the
spelling the geometric side produces. -/
theorem toCotangent_one_tmul_sub_tmul_one (b : S) :
    (RingHom.ker (ConcreteCategory.hom (lmulHom R S))).toCotangent
        ⟨(1 : S) ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S), one_tmul_sub_tmul_one_mem_ker R S b⟩ =
      KaehlerDifferential.D R S b :=
  rfl

/-! ### The diagonal of a morphism of affine schemes -/

/-- The diagonal of `Spec S ⟶ Spec R` is `Spec` of the multiplication map followed by the
comparison of `Spec (S ⊗[R] S)` with the fibre product. This is Mathlib's
`AlgebraicGeometry.diagonal_SpecMap`, restated with the multiplication map named. -/
theorem diagonal_specMap_eq :
    pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (lmulHom R S) ≫ (pullbackSpecIso R S S).inv :=
  diagonal_SpecMap R S

/-- The diagonal of a morphism of affine schemes is a closed immersion: it is `Spec` of a
surjection followed by an isomorphism. -/
@[ega "IV 16.3.1" "special case"]
instance isClosedImmersion_diagonal_specMap :
    IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S)))) := by
  rw [diagonal_specMap_eq R S]
  infer_instance

/-- The coborder neighbourhood used to build the conormal sheaf of the affine diagonal is the
whole of `Spec S ×_{Spec R} Spec S`. So no restriction of the ambient scheme is involved in
the affine case of [Stacks, Tag 08S2]. -/
theorem coborderRange_diagonal_specMap_eq_top :
    (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S)))).coborderRange = ⊤ :=
  coborderRange_eq_top _

/-! ### The two projections on global sections -/

/-- Reading a global section of `Spec S` through a projection of the fibre product and the
comparison with `Spec (S ⊗[R] S)` is the corresponding ring map followed by `ΓSpecIso`. -/
private theorem appTop_pullbackSpecIso_inv_comp
    (g : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⟶ Spec (CommRingCat.of S))
    (φ : CommRingCat.of S ⟶ CommRingCat.of (S ⊗[R] S))
    (hg : (pullbackSpecIso R S S).inv ≫ g = Spec.map φ) (b : S) :
    ((pullbackSpecIso R S S).inv.appTop).hom
        ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv b)) =
      (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] S))).inv (φ b) := by
  have h := Scheme.Hom.comp_appTop (pullbackSpecIso R S S).inv g
  rw [hg] at h
  refine (congr($h ((Scheme.ΓSpecIso (CommRingCat.of S)).inv b))).symm.trans ?_
  exact (congr($(Scheme.ΓSpecIso_inv_naturality φ) b)).symm

/-- On global sections, the first projection of `Spec S ×_{Spec R} Spec S` is `b ↦ b ⊗ 1`,
read through the comparison with `Spec (S ⊗[R] S)`. -/
theorem appTop_fst_specMap (b : S) :
    ((pullbackSpecIso R S S).inv.appTop).hom
        (((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of S)).inv b)) =
      (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] S))).inv (b ⊗ₜ[R] (1 : S)) :=
  appTop_pullbackSpecIso_inv_comp R S _ _ (pullbackSpecIso_inv_fst R S S) b

/-- On global sections, the second projection of `Spec S ×_{Spec R} Spec S` is `b ↦ 1 ⊗ b`,
read through the comparison with `Spec (S ⊗[R] S)`. -/
theorem appTop_snd_specMap (b : S) :
    ((pullbackSpecIso R S S).inv.appTop).hom
        (((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of S)).inv b)) =
      (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] S))).inv ((1 : S) ⊗ₜ[R] b) :=
  appTop_pullbackSpecIso_inv_comp R S _ _ (pullbackSpecIso_inv_snd R S S) b

/-- **The sign of [Stacks, Tag 08S2].** The section `p₂^♯ b - p₁^♯ b` of the tag is
`1 ⊗ b - b ⊗ 1`, read through the comparison of the fibre product with `Spec (S ⊗[R] S)`.
That is exactly the element whose conormal class Mathlib calls `d b`, so the tag's convention
and `KaehlerDifferential.D` agree on the nose. -/
theorem appTop_snd_sub_fst_specMap (b : S) :
    ((pullbackSpecIso R S S).inv.appTop).hom
        ((((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
              (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv b)) -
          (((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
              (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv b))) =
      (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] S))).inv
        ((1 : S) ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S)) := by
  rw [map_sub, appTop_snd_specMap, appTop_fst_specMap, ← map_sub]

/-- **The affine case of [Stacks, Tag 08S2], on generators.** The section
`p₂^♯ b - p₁^♯ b` of the structure sheaf of `Spec S ×_{Spec R} Spec S` lies in the ideal of the
diagonal, and its conormal class in `I ⧸ I²` is `d b`.

The statement is phrased on the element of `S ⊗[R] S` that
`Stacks.DiagonalConormal.appTop_snd_sub_fst_specMap` identifies the section with; the two
together are the generator clause of the tag in the affine model. -/
theorem toCotangent_appTop_snd_sub_fst_specMap (b : S)
    (c : S ⊗[R] S)
    (hc : (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] S))).inv c =
      ((pullbackSpecIso R S S).inv.appTop).hom
        ((((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
              (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv b)) -
          (((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
              (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv b)))) :
    ∃ hmem : c ∈ RingHom.ker (ConcreteCategory.hom (lmulHom R S)),
      (RingHom.ker (ConcreteCategory.hom (lmulHom R S))).toCotangent ⟨c, hmem⟩ =
        KaehlerDifferential.D R S b := by
  have hceq : c = (1 : S) ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S) :=
    (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] S))).inv).1
      (hc.trans (appTop_snd_sub_fst_specMap R S b))
  subst hceq
  exact ⟨one_tmul_sub_tmul_one_mem_ker R S b, toCotangent_one_tmul_sub_tmul_one R S b⟩

end Affine

end Stacks.DiagonalConormal

end

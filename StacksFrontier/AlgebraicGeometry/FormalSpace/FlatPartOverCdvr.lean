module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic

/-!
# The maximal flat closed formal subspace over a complete discrete valuation ring

Let `A` be a complete discrete valuation ring and let `X` be a locally Noetherian formal
algebraic space over `A`, that is a locally Noetherian formal algebraic space together with a
structure morphism `p : X ⟶ Spf A`. **Stacks 0GD8** says that there is a closed immersion
`X' ⟶ X` of formal algebraic spaces with `X'` flat over `A` which is universal: every morphism
`Y ⟶ X` with `Y` a locally Noetherian formal algebraic space flat over `A` factors through
`X'`. The source only asks for the existence of a factorization, not for its uniqueness, and
that is what is stated here.

The source's proof has two halves.

*The affine half.* With `π ∈ A` a uniformizer, an `A`-module is flat exactly when its
`π`-power torsion vanishes, and over a discrete valuation ring the `π`-power torsion is the
whole torsion submodule. So for `X = Spf B` one takes `X' = Spf B'` with `B'` the quotient of
`B` by its `A`-torsion: that quotient is torsion free, hence flat over `A`, the projection
`B ⟶ B'` is surjective, so `Spf B' ⟶ Spf B` is a closed immersion, and any `A`-algebra
homomorphism from `B` to a torsion-free `A`-algebra kills the torsion and therefore factors
through `B'`. **This half is proved here, unconditionally, at the level of rings**; see
`Algebra.baseTorsionIdeal`, `Algebra.flat_quotient_baseTorsionIdeal`,
`Algebra.baseTorsionIdeal_le_ker` and `Algebra.exists_flat_quotient_of_isDiscreteValuationRing`.

*The gluing half.* For general `X` one applies the affine half to each member of an atlas
`{Xᵢ ⟶ X}` as in Definition 0AIM, observes that the resulting closed subspaces agree over the
fibre products `Xᵢ ×_X Xⱼ`, and assembles `X'` as the quotient of `∐ Xᵢ'` by the étale
equivalence relation `∐ Xᵢ' ×_X Xⱼ'` using Spaces, Theorem 02WW; the glued morphism is
representable by Bootstrap, Lemma 046J and a closed immersion by Spaces, Lemma 03KD. The
universal property is then read off from the étale covering `{Xᵢ ×_X Y ⟶ Y}` of a test object.

## Main definitions

* `Algebra.baseTorsionIdeal`: the ideal of `A`-torsion elements of an algebra over a domain
  `A`. This is the `π`-power torsion ideal of the source's proof.
* `Algebra.liftBaseTorsionIdeal`: the factorization of an algebra homomorphism into a
  torsion-free algebra through the quotient by the torsion ideal.
* `AlgebraicGeometry.FormalSpace.HasAffineFlatParts`,
  `AlgebraicGeometry.FormalSpace.FlatPartsDescend`,
  `AlgebraicGeometry.FormalSpace.FactorizationDescendsAlongAffineEtaleCover`,
  `AlgebraicGeometry.FormalSpace.HasFlatAffineCoverOfFlat` and
  `AlgebraicGeometry.FormalSpace.FlatnessLocalityInputs`: five inputs of the proof of Stacks
  0GD8, each named once together with the Stacks tags it uses. The first four are theorems of
  the library, proved in `StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvrAffine` and
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvrDescent`. The fifth,
  `FlatnessLocalityInputs`, is stated over every fppf sheaf mapping to `Spf A` and cannot hold
  when `Spf A` is affine; see its docstring.

## Main results

* `Algebra.flat_quotient_baseTorsionIdeal`: over a discrete valuation ring the quotient by the
  torsion ideal is flat.
* `Algebra.exists_flat_quotient_of_isDiscreteValuationRing`: the affine half of **Stacks
  0GD8** at the level of rings — the quotient by the `A`-torsion is a flat quotient of `B`
  through which every `A`-algebra homomorphism from `B` into a flat `A`-algebra factors.
* `AlgebraicGeometry.FormalSpace.exists_flat_isClosedImmersion_of_isLocallyNoetherian`: the
  assembly of the proof of Stacks 0GD8 from the five inputs, taken as hypotheses. Its
  hypotheses `hSpfAaffine` and `hloc` cannot hold together, so it is vacuous and is not a
  formalization of Stacks 0GD8. **Stacks 0GD8** itself is
  `AlgebraicGeometry.FormalSpace.exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete`, in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvrFull`, which supplies the inputs.

## Implementation notes

"`X` is flat over `A`" is read, as the source does, as flatness of the structure morphism
`X ⟶ Spf A` in the sense of Definition 0GCC, that is
`AlgebraicGeometry.FormalSpace.IsFlat`. The base is `formalSpectrum D` for a quotient system
`D` presenting `A` over `S`, which is how this library spells `Spf A`.

The ring-theoretic half needs neither completeness nor Noetherianness and is stated at its
natural generality: the torsion ideal and its universal property hold over any domain, and
flatness of the quotient only needs `A` to be a Bézout domain, which a discrete valuation ring
is. Completeness of `A` plays no role in the source's argument either; it is part of the
standing hypothesis of Section 0GD7 and is carried in the statement of the geometric theorem
for faithfulness.

### The five inputs

`AlgebraicGeometry.FormalSpace.exists_flat_isClosedImmersion_of_isLocallyNoetherian` states
both halves of the source's conclusion and takes five inputs of the source's proof as
hypotheses; none of them mentions the conclusion.

* `hpart`, the affine half as a statement about formal spectra, is
  `AlgebraicGeometry.FormalSpace.hasAffineFlatParts`.
* `hdesc`, the gluing step (Stacks 02WW with Bootstrap, Lemma 046J and Spaces, Lemma 03KD),
  is `AlgebraicGeometry.FormalSpace.flatPartsDescend`.
* `hfac`, the descent of a factorization through a closed immersion along an affine étale
  covering of the source (Stacks 03KD with the monomorphism property of Stacks 0AQB), is
  `AlgebraicGeometry.FormalSpace.factorizationDescendsAlongAffineEtaleCover`.
* `hrefine`, the covering `{Xᵢ ×_X Y ⟶ Y}` of a test object (Stacks 0AJ3, Stacks 0AJ2,
  Stacks 0AQ8 and Stacks 0GCG), is `AlgebraicGeometry.FormalSpace.hasFlatAffineCoverOfFlat`.
* `hloc` bundles the four hypotheses of `AlgebraicGeometry.FormalSpace.isFlat_tfae`, this
  library's form of **Stacks 0GCD**, with the source of the morphism quantified over. As
  stated, its first conjunct quantifies over every fppf sheaf `X'` mapping to `Spf A`, not only
  formal algebraic spaces, and together with `hSpfAaffine` it is unsatisfiable (see the
  docstring of `AlgebraicGeometry.FormalSpace.FlatnessLocalityInputs`). The unconditional proof
  of Stacks 0GD8 does not use it: it reads flatness of `X'` over `A` off the atlas by the
  affine flat parts through Remark 0ANI instead.

What the proof here does with them is the assembly: it reads the atlas off the locally
Noetherian hypothesis, produces the affine flat parts, glues, exhibits the glued space as
locally Noetherian through the atlas by the flat parts, deduces flatness over `A` from
condition (4) of Stacks 0GCD read on that atlas, and assembles the factorization of a test
object from the factorizations of the members of its covering.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03KD](https://stacks.math.columbia.edu/tag/03KD)
* [Stacks Project, Tag 046J](https://stacks.math.columbia.edu/tag/046J)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0AQB](https://stacks.math.columbia.edu/tag/0AQB)
* [Stacks Project, Tag 0GC9](https://stacks.math.columbia.edu/tag/0GC9)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCD](https://stacks.math.columbia.edu/tag/0GCD)
* [Stacks Project, Tag 0GCG](https://stacks.math.columbia.edu/tag/0GCG)
* [Stacks Project, Tag 0GD7](https://stacks.math.columbia.edu/tag/0GD7)
* [Stacks Project, Tag 0GD8](https://stacks.math.columbia.edu/tag/0GD8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-! ### The torsion ideal and the flat quotient -/

universe v w x

variable (A : Type v) [CommRing A] [IsDomain A] (B : Type w) [CommRing B] [Algebra A B]

/-- The ideal of `A`-torsion elements of an algebra `B` over a domain `A`: those `b` killed by
some nonzero scalar. Over a discrete valuation ring with uniformizer `π` this is the
`π`-power torsion ideal appearing in the proof of Stacks 0GD8. The underlying additive
subgroup is `Submodule.torsion A B`; it is an ideal because `a • (c * b) = c * (a • b)`. -/
def baseTorsionIdeal : Ideal B where
  carrier := (Submodule.torsion A B : Set B)
  add_mem' h₁ h₂ := Submodule.add_mem _ h₁ h₂
  zero_mem' := Submodule.zero_mem _
  smul_mem' c x hx := by
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by rw [smul_eq_mul, ← mul_smul_comm, ha, mul_zero]⟩

theorem mem_baseTorsionIdeal {b : B} :
    b ∈ baseTorsionIdeal A B ↔ ∃ a : A, a ≠ 0 ∧ a • b = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.1, nonZeroDivisors.ne_zero a.2, ha⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, h⟩

/-- A nonzero scalar acts injectively on a torsion-free module over a domain. -/
theorem eq_zero_of_smul_eq_zero {C : Type*} [AddCommGroup C] [Module A C]
    [Module.IsTorsionFree A C] {a : A} (ha : a ≠ 0) {c : C} (hc : a • c = 0) : c = 0 :=
  Module.IsTorsionFree.isSMulRegular (R := A) (M := C) (IsRegular.of_ne_zero ha)
    (by simpa using hc)

/-- The quotient of an algebra over a domain by its torsion ideal is torsion free: if `a • b`
lies in the torsion ideal, say `a' * (a • b) = 0` with `a' ≠ 0`, then `(a' * a) • b = 0` and
`a' * a ≠ 0`, so `b` already lies in the torsion ideal. -/
instance isTorsionFree_quotient_baseTorsionIdeal :
    Module.IsTorsionFree A (B ⧸ baseTorsionIdeal A B) := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h₁ : (Ideal.Quotient.mkₐ A (baseTorsionIdeal A B)) ((a : A) • b) = 0 := by
    rw [map_smul]; exact ha
  obtain ⟨a', ha', hb⟩ := (mem_baseTorsionIdeal A B).mp (Ideal.Quotient.eq_zero_iff_mem.mp h₁)
  change _ = (0 : B ⧸ baseTorsionIdeal A B)
  refine Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_baseTorsionIdeal A B).mpr
    ⟨a' * (a : A), mul_ne_zero ha' (nonZeroDivisors.ne_zero a.2), ?_⟩)
  rw [mul_smul]
  exact hb

/-- Over a discrete valuation ring the quotient by the torsion ideal is flat. A discrete
valuation ring is a principal ideal domain, hence a Bézout domain, and over a Bézout domain a
module is flat exactly when it has no torsion. -/
theorem flat_quotient_baseTorsionIdeal [IsDiscreteValuationRing A] :
    Module.Flat A (B ⧸ baseTorsionIdeal A B) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- An algebra homomorphism into a torsion-free algebra kills the torsion ideal: a nonzero
scalar killing `b` also kills its image. -/
theorem baseTorsionIdeal_le_ker {C : Type*} [CommRing C] [Algebra A C]
    [Module.IsTorsionFree A C] (f : B →ₐ[A] C) :
    baseTorsionIdeal A B ≤ RingHom.ker f.toRingHom := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := (mem_baseTorsionIdeal A B).mp hb
  exact eq_zero_of_smul_eq_zero A ha (show a • f b = 0 by rw [← map_smul, hab, map_zero])

/-- The factorization of an algebra homomorphism into a torsion-free algebra through the
quotient by the torsion ideal. -/
def liftBaseTorsionIdeal {C : Type*} [CommRing C] [Algebra A C] [Module.IsTorsionFree A C]
    (f : B →ₐ[A] C) : (B ⧸ baseTorsionIdeal A B) →ₐ[A] C :=
  Ideal.Quotient.liftₐ _ f fun _ hb ↦ baseTorsionIdeal_le_ker A B f hb

@[simp]
theorem liftBaseTorsionIdeal_mk {C : Type*} [CommRing C] [Algebra A C]
    [Module.IsTorsionFree A C] (f : B →ₐ[A] C) (b : B) :
    liftBaseTorsionIdeal A B f (Ideal.Quotient.mk (baseTorsionIdeal A B) b) = f b :=
  rfl

/-- **The affine half of Stacks 0GD8, at the level of rings.** Let `A` be a discrete valuation
ring and `B` an `A`-algebra. There is a surjection `B ⟶ B'` of `A`-algebras with `B'` flat
over `A` such that every `A`-algebra homomorphism from `B` into a flat `A`-algebra factors
through it. One takes `B' = B ⧸ baseTorsionIdeal A B`: it is torsion free, hence flat, and a
flat algebra is torsion free, so every such homomorphism kills the torsion ideal. -/
theorem exists_flat_quotient_of_isDiscreteValuationRing [IsDiscreteValuationRing A] :
    ∃ (B' : Type w) (_ : CommRing B') (_ : Algebra A B') (q : B →ₐ[A] B'),
      Function.Surjective q ∧ Module.Flat A B' ∧
        ∀ (C : Type x) (_ : CommRing C) (_ : Algebra A C), Module.Flat A C →
          ∀ f : B →ₐ[A] C, ∃ g : B' →ₐ[A] C, g.comp q = f := by
  refine ⟨B ⧸ baseTorsionIdeal A B, inferInstance, inferInstance,
    Ideal.Quotient.mkₐ A (baseTorsionIdeal A B), Ideal.Quotient.mk_surjective,
    flat_quotient_baseTorsionIdeal A B, fun C _ _ hC f ↦ ?_⟩
  have : Module.IsTorsionFree A C := Module.Flat.isTorsionFree
  exact ⟨liftBaseTorsionIdeal A B f, AlgHom.ext fun b ↦ rfl⟩

end Algebra

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (D : QuotientSystem B S hS A)

/-! ### The inputs of the proof -/

/-- The affine half of **Stacks 0GD8** as a statement about formal spectra: every Noetherian
affine formal algebraic space `U` representable étale over `X` carries a closed immersion
`Z ⟶ U` with `Z` Noetherian affine and flat over `A`, through which every Noetherian affine
formal algebraic space flat over `A` and mapping to `U` factors.

Its ring-theoretic content is `Algebra.exists_flat_quotient_of_isDiscreteValuationRing`
in this file: the quotient of the presenting ring by its `A`-torsion is flat over `A` and
receives every homomorphism into a flat `A`-algebra. The statement itself is proved, for a
discrete valuation ring `A` with an adic topology, as
`AlgebraicGeometry.FormalSpace.hasAffineFlatParts`. -/
abbrev HasAffineFlatParts {X : FppfSheaf B S hS} (p : X ⟶ formalSpectrum D) : Prop :=
  ∀ (U : FppfSheaf B S hS) (v : U ⟶ X), IsAffineFormalAlgebraicSpace B S hS U →
    IsNoetherian B S hS U → IsRepresentableEtale B S hS v →
    ∃ (Z : FppfSheaf B S hS) (z : Z ⟶ U),
      IsAffineFormalAlgebraicSpace B S hS Z ∧ IsNoetherian B S hS Z ∧
        IsClosedImmersion B S hS z ∧ IsFlat B S hS (z ≫ v ≫ p) ∧
        ∀ (W : FppfSheaf B S hS) (w : W ⟶ U), IsAffineFormalAlgebraicSpace B S hS W →
          IsNoetherian B S hS W → IsFlat B S hS (w ≫ v ≫ p) → ∃ r : W ⟶ Z, r ≫ z = w

/-- The gluing step of **Stacks 0GD8**: a family of closed immersions `Zᵢ ⟶ Uᵢ` into the
members of an affine étale covering of `X`, flat over `A` and mutually compatible in the sense
that a Noetherian affine formal algebraic space flat over `A` mapping to `Uᵢ` factors through
`Zᵢ`, glues to a closed immersion `X' ⟶ X` for which the `Zᵢ` form an affine étale covering of
`X'` compatibly with the covering of `X`.

This is Spaces, Theorem **02WW** — `X'` is the quotient of `∐ Zᵢ` by the étale equivalence
relation `∐ Zᵢ ×_X Zⱼ` — together with Bootstrap, Lemma **046J**, which makes `X' ⟶ X`
representable by algebraic spaces, and Spaces, Lemma **03KD**, which makes it a closed
immersion. The conclusion asserts nothing about flatness and nothing about a universal
property; those are deduced from it in `exists_flat_isClosedImmersion_of_isLocallyNoetherian`.
It is proved, for `X` a formal algebraic space, as
`AlgebraicGeometry.FormalSpace.flatPartsDescend`, with `X'` the image sheaf of `∐ Zᵢ ⟶ X`. -/
abbrev FlatPartsDescend {X : FppfSheaf B S hS} (p : X ⟶ formalSpectrum D) : Prop :=
  ∀ {I : Type (u + 1)} (U : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U u →
    ∀ (Z : I → FppfSheaf B S hS) (z : ∀ i, Z i ⟶ U i),
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i)) →
      (∀ i, IsNoetherian B S hS (Z i)) →
      (∀ i, IsClosedImmersion B S hS (z i)) →
      (∀ i, IsFlat B S hS (z i ≫ u i ≫ p)) →
      (∀ (i : I) (W : FppfSheaf B S hS) (w : W ⟶ U i),
        IsAffineFormalAlgebraicSpace B S hS W → IsNoetherian B S hS W →
        IsFlat B S hS (w ≫ u i ≫ p) → ∃ r : W ⟶ Z i, r ≫ z i = w) →
      ∃ (X' : FppfSheaf B S hS) (ι : X' ⟶ X) (ζ : ∀ i, Z i ⟶ X'),
        IsFormalAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS ι ∧
          IsAffineEtaleCover B S hS Z ζ ∧ ∀ i, ζ i ≫ ι = z i ≫ u i

/-- The descent of a factorization through a closed immersion along an affine étale covering of
the source: if every member of a covering of `Y` maps to `X'` compatibly with `q : Y ⟶ X`, then
`q` itself factors through the closed immersion `ι : X' ⟶ X`. This is Spaces, Lemma **03KD**
together with the monomorphism property of **Stacks 0AQB**, which is what makes the local
factorizations agree on overlaps and glue. It is pure sheaf descent: neither `A` nor flatness
occurs in it. It is proved as
`AlgebraicGeometry.FormalSpace.factorizationDescendsAlongAffineEtaleCover`. -/
abbrev FactorizationDescendsAlongAffineEtaleCover : Prop :=
  ∀ {X' X Y : FppfSheaf B S hS} (ι : X' ⟶ X) (q : Y ⟶ X), IsClosedImmersion B S hS ι →
    ∀ {J : Type (u + 1)} (W : J → FppfSheaf B S hS) (w : ∀ j, W j ⟶ Y),
      IsAffineEtaleCover B S hS W w →
      (∀ j, ∃ r : W j ⟶ X', r ≫ ι = w j ≫ q) → ∃ r : Y ⟶ X', r ≫ ι = q

/-- The covering of a test object used in the last step of **Stacks 0GD8**: a locally
Noetherian formal algebraic space `Y` flat over `A` and mapping to `X` admits an affine étale
covering by Noetherian affine formal algebraic spaces which are flat over `A` and which map to
the members of a given affine étale covering of `X`, compatibly with `Y ⟶ X`.

In the source these are the charts of the fibre products `Xᵢ ×_X Y`. That those are formal
algebraic spaces is **Stacks 0AJ3**, that they admit Noetherian affine coverings refining the
given one uses **Stacks 0AJ2** and **Stacks 0AQ8**, and that they are flat over `A` is
**Stacks 0GCG**, since the projection `Xᵢ ×_X Y ⟶ Y` is representable and étale, hence flat.
It is proved, for `X` a formal algebraic space, as
`AlgebraicGeometry.FormalSpace.hasFlatAffineCoverOfFlat`. -/
abbrev HasFlatAffineCoverOfFlat {X : FppfSheaf B S hS} (p : X ⟶ formalSpectrum D) : Prop :=
  ∀ {I : Type (u + 1)} (U : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U u →
    ∀ (Y : FppfSheaf B S hS) (q : Y ⟶ X), IsLocallyNoetherian B S hS Y →
      IsFlat B S hS (q ≫ p) →
      ∃ (J : Type (u + 1)) (W : J → FppfSheaf B S hS) (w : ∀ j, W j ⟶ Y) (k : J → I)
        (m : ∀ j, W j ⟶ U (k j)),
        IsAffineEtaleCover B S hS W w ∧ (∀ j, IsNoetherian B S hS (W j)) ∧
          (∀ j, w j ≫ q = m j ≫ u (k j)) ∧ ∀ j, IsFlat B S hS (m j ≫ u (k j) ≫ p)

/-- The four hypotheses of `AlgebraicGeometry.FormalSpace.isFlat_tfae`, this library's form of
**Stacks 0GCD**, with the source of the morphism quantified over: the morphism whose flatness
is concluded in Stacks 0GD8 is produced during the proof, so the inputs cannot be stated for a
fixed morphism. They are **Stacks 0AJ3** that a fibre product with an affine étale chart is a
formal algebraic space, the covering refinement of **Stacks 0AJ2**, and the two locality axioms
of **Stacks 0GC9** read on affine formal algebraic spaces through **Stacks 0AN8** and **Stacks
0AN9**.

**This hypothesis cannot hold when `Spf A` is affine.** Its first conjunct quantifies over
*every* fppf sheaf `X'` with a map `f` to `formalSpectrum D`, not only over formal algebraic
spaces. Taking `V = formalSpectrum D` and `v = 𝟙`, which is representable étale by
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_id`, it says that `pullback (𝟙 _) f ≅ X'`
is a formal algebraic space whenever `formalSpectrum D` is affine. That is false: a formal
algebraic space satisfies the set-theoretic condition of Definition 0AIM, an epimorphism from
the sheaf of a single object of the site, which the coproduct of `Type u`-many copies of
`Spf A` (mapping to `Spf A` by the codiagonal) does not admit. The restriction of the
quantifier to formal algebraic `X'` would have sufficed for its one use. -/
abbrev FlatnessLocalityInputs : Prop :=
  (∀ {X' : FppfSheaf B S hS} (f : X' ⟶ formalSpectrum D) (V : FppfSheaf B S hS)
      (v : V ⟶ formalSpectrum D), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f)) ∧
    ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom ∧
    ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom ∧
    ∀ {X' : FppfSheaf B S hS} (f : X' ⟶ formalSpectrum D),
      HasEtaleRefinementOfSourceCover B S hS f

/-! ### Stacks 0GD8 -/

/-- Reading flatness of a morphism between affine formal algebraic spaces on the identity
charts of its source and target returns the chart-tested condition for the morphism itself. -/
private theorem hasPropertyOnAffineChartMap_of_isFlat {U V : FppfSheaf B S hS} (t : U ⟶ V)
    (hU : IsAffineFormalAlgebraicSpace B S hS U) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (ht : IsFlat B S hS t) :
    HasPropertyOnAffineChartMap B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom t :=
  (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS t).mp ht U V (𝟙 U) (𝟙 V) t hU hV
    (isRepresentableEtale_id B S hS U) (isRepresentableEtale_id B S hS V) (by simp)

/-- **An assembly of the proof of Stacks 0GD8 from five inputs; vacuous as stated.** This is
not a formalization of Stacks 0GD8: its hypotheses `hSpfAaffine` and `hloc` cannot hold
together, since the first conjunct of `hloc` (`FlatnessLocalityInputs`) is stated over every
fppf sheaf mapping to `Spf A` and, with `Spf A` affine, would make every such sheaf a formal
algebraic space (see the docstring of `AlgebraicGeometry.FormalSpace.FlatnessLocalityInputs`).
It is kept as a record of the assembly. Stacks 0GD8, unconditional, is
`AlgebraicGeometry.FormalSpace.exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete`.

Let `A` be a complete discrete
valuation ring and let `X` be a locally Noetherian formal algebraic space over `S` with a
structure morphism `p : X ⟶ Spf A`, and grant the five inputs `hpart`, `hdesc`, `hfac`,
`hrefine` and `hloc` of the source's proof. Then
there is a closed immersion `ι : X' ⟶ X` of formal algebraic spaces with `X'` locally
Noetherian and flat over `A` such that every morphism `q : Y ⟶ X` with `Y` a locally
Noetherian formal algebraic space flat over `A` factors through `ι`.

The atlas of `X` supplied by the locally Noetherian hypothesis is turned into a family of
affine flat parts by `hpart`; those are mutually compatible, since the universal property of
one of them applies to any Noetherian affine formal algebraic space flat over `A` mapping to
the corresponding chart, so they glue by `hdesc` to a closed immersion `ι : X' ⟶ X` whose
sources form an affine étale covering of `X'`. That covering exhibits `X'` as locally
Noetherian, and reading condition (4) of Stacks 0GCD on it gives flatness of `X'` over `A`.
For the universal property, `hrefine` covers a test object `Y` by Noetherian affine formal
algebraic spaces which are flat over `A` and map to the charts of `X`; each of them factors
through the corresponding flat part and hence through `X'`, and `hfac` glues those
factorizations.

Stacks 0GD8 itself, with the inputs supplied, is
`AlgebraicGeometry.FormalSpace.exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete`. -/
theorem exists_flat_isClosedImmersion_of_isLocallyNoetherian
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    (_hAadic : TopologicalRing.IsAdic A)
    (_hAcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hSpfAaffine : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    (hSpfA : IsFormalAlgebraicSpace B S hS (formalSpectrum D))
    {X : FppfSheaf B S hS} (hX : IsLocallyNoetherian B S hS X) (p : X ⟶ formalSpectrum D)
    (hpart : HasAffineFlatParts B S hS D p)
    (hdesc : FlatPartsDescend B S hS D p)
    (hfac : FactorizationDescendsAlongAffineEtaleCover B S hS)
    (hrefine : HasFlatAffineCoverOfFlat B S hS D p)
    (hloc : FlatnessLocalityInputs B S hS D) :
    ∃ (X' : FppfSheaf B S hS) (ι : X' ⟶ X),
      IsClosedImmersion B S hS ι ∧ IsLocallyNoetherian B S hS X' ∧
        IsFlat B S hS (ι ≫ p) ∧
        ∀ (Y : FppfSheaf B S hS) (q : Y ⟶ X), IsLocallyNoetherian B S hS Y →
          IsFlat B S hS (q ≫ p) → ∃ r : Y ⟶ X', r ≫ ι = q := by
  classical
  obtain ⟨hpbinput, hasc, hdescloc, hrefinput⟩ := hloc
  obtain ⟨-, I, U, u, hUaffine, hUetale, hUsurj, hUnoeth⟩ := hX
  choose Z z hZaffine hZnoeth hZclosed hZflat hZuniv using
    fun i ↦ hpart (U i) (u i) (hUaffine i) (hUnoeth i) (hUetale i)
  obtain ⟨X', ι, ζ, hX'fas, hιclosed, hZcover, hζ⟩ :=
    hdesc U u ⟨hUaffine, hUetale, hUsurj⟩ Z z hZaffine hZnoeth hZclosed hZflat
      fun i W w hWaffine hWnoeth hWflat ↦ hZuniv i W w hWaffine hWnoeth hWflat
  refine ⟨X', ι, hιclosed, ⟨hX'fas, I, Z, ζ, hZcover.1, hZcover.2.1, hZcover.2.2, hZnoeth⟩,
    ?_, ?_⟩
  · have hchart : ∀ i, HasPropertyOnAffineChartMap B S hS
        TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom (ζ i ≫ ι ≫ p) := by
      intro i
      have hrw : ζ i ≫ ι ≫ p = z i ≫ u i ≫ p := by
        rw [← Category.assoc, hζ i, Category.assoc]
      rw [hrw]
      exact hasPropertyOnAffineChartMap_of_isFlat B S hS (z i ≫ u i ≫ p) (hZaffine i)
        hSpfAaffine (hZflat i)
    have hsrc : HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic
        TopologicalRing.IsFlatHom (ι ≫ p) :=
      ⟨I, Z, ζ, hZcover, fun i ↦
        ⟨formalSpectrum D, 𝟙 (formalSpectrum D), ζ i ≫ ι ≫ p, hSpfAaffine,
          isRepresentableEtale_id B S hS (formalSpectrum D), by simp, hchart i⟩⟩
    exact ((isFlat_tfae B S hS (ι ≫ p) hSpfA (hpbinput (ι ≫ p)) hasc hdescloc
      (hrefinput (ι ≫ p))).out 4 1).mp hsrc
  · intro Y q hY hqflat
    obtain ⟨J, W, w, k, m, hWcover, hWnoeth, hWsq, hWflat⟩ :=
      hrefine U u ⟨hUaffine, hUetale, hUsurj⟩ Y q hY hqflat
    refine hfac ι q hιclosed W w hWcover fun j ↦ ?_
    obtain ⟨r, hr⟩ := hZuniv (k j) (W j) (m j) (hWcover.1 j) (hWnoeth j) (hWflat j)
    refine ⟨r ≫ ζ (k j), ?_⟩
    rw [Category.assoc, hζ (k j), ← Category.assoc, hr, hWsq j]

end AlgebraicGeometry.FormalSpace

end

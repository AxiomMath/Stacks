module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# The naive cotangent complex commutes with filtered colimits

All rings are commutative with unit, and `Λ` is a directed set: a nonempty preordered set
in which any two elements have a common upper bound. A *system of ring maps over `Λ`*
consists of directed systems of rings `(R i)` and `(S i)`, with transition ring
homomorphisms `R i → R j` and `S i → S j` for `i ≤ j`, together with ring homomorphisms
`R i → S i` commuting with the transition maps. Set `R = colim_i R i` and
`S = colim_i S i`.

## Main definitions

* `RingMapSystemUnbundled`: a system of ring maps over `Λ` as above.
* For `A → B`, the canonical presentation is the polynomial ring `A[B]` over `A` with
  variables indexed by `B`, with surjection `A[B] → B`, `[b] ↦ b`, of kernel `I_{B/A}`;
  the naive cotangent complex `NL_{B/A}` is the two-term complex
  `I/I² → Ω_{A[B]/A} ⊗ B` (degree `1` to degree `0`). A commuting square of rings induces
  a morphism of two-term complexes `NL_{B/A} → NL_{B'/A'}`, so the `NL_{S i / R i}` form a
  directed system of two-term complexes; its colimit `colimCotangent →
  colimCotangentSpace` is taken degreewise as a colimit of abelian groups, the
  differential `colimDifferential` being the colimit of the stage differentials.
* `comparisonCotangent`, `comparisonCotangentSpace`: the two degreewise components of the
  canonical comparison morphism `colim_i NL_{S i / R i} → NL_{S/R}`.

## Main results

* `isIso_colim_NL`: the comparison morphism is an isomorphism of two-term complexes, that
  is, a bijection in each homological degree, compatibly with the differentials.

## Implementation notes

* The canonical presentation `A[B] → B` is `Algebra.Generators.self A B`, whose ring is
  `MvPolynomial B A` (variables indexed by `B`).
* The naive cotangent complex `NL_{B/A}` is the extension
  `(Algebra.Generators.self A B).toExtension`, whose `Cotangent` is `I/I²` (degree `1`),
  whose `CotangentSpace` is `Ω ⊗ B` (degree `0`), and whose `cotangentComplex` is the
  differential. That the functoriality maps commute with the differentials is
  `Algebra.Extension.CotangentSpace.map_cotangentComplex`.
* The degreewise colimit is realized as a `Module.DirectLimit` over `ℤ` (every abelian
  group is a `ℤ`-module and additive maps are `ℤ`-linear), with transition maps the
  additive parts of the canonical functoriality maps `Extension.Cotangent.map` and
  `Extension.CotangentSpace.map`; the result is then naturally an `S`-module. The
  `DecidableEq` needed internally by `Module.DirectLimit` is supplied by classical choice
  (`open scoped Classical`), so it is not a hypothesis of any statement.
* The functoriality maps are realized by `Generators.defaultHom`, the canonical morphism of
  presentations, together with `Extension.Cotangent.map` and
  `Extension.CotangentSpace.map`.
-/

@[expose] public section

-- needed file-wide: `comparisonCotangent_toColim`, `polyColim_transport`, `polyColim_surj`,
-- `polyColim_zero_exact`, `homIinf_transHom_comp`, `transHom_trans`,
-- `comparisonCotangentSpace_toColim` and `comparison_chain_map` rewrite through the colimit
-- transport maps, whose patterns match only when defeq may unfold them past the default
-- transparency
set_option backward.isDefEq.respectTransparency false

open Algebra

/-- A *system of ring maps over the directed set `Λ`*: directed
systems of rings `(R i)`, `(S i)` with transition ring homomorphisms `fR`, `fS`
forming directed systems, together with ring maps `g i : R i → S i` commuting
with the transition maps. -/
structure RingMapSystemUnbundled.{u} (Λ : Type*) [Preorder Λ] where
  /-- The directed system of "source" rings `R_λ`. -/
  R : Λ → Type u
  /-- The directed system of "target" rings `S_λ`. -/
  S : Λ → Type u
  /-- The commutative ring structure on each `R_λ`. -/
  commRingR : ∀ i, CommRing (R i)
  /-- The commutative ring structure on each `S_λ`. -/
  commRingS : ∀ i, CommRing (S i)
  /-- Transition ring homomorphisms `R_λ → R_μ` for `λ ≤ μ`. -/
  fR : ∀ ⦃i j⦄, i ≤ j → R i →+* R j
  /-- Transition ring homomorphisms `S_λ → S_μ` for `λ ≤ μ`. -/
  fS : ∀ ⦃i j⦄, i ≤ j → S i →+* S j
  fR_id : ∀ i (x : R i), fR (le_refl i) x = x
  fR_comp : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : R i),
    fR hjk (fR hij x) = fR (hij.trans hjk) x
  fS_id : ∀ i (x : S i), fS (le_refl i) x = x
  fS_comp : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : S i),
    fS hjk (fS hij x) = fS (hij.trans hjk) x
  /-- The ring maps `R_λ → S_λ`. -/
  g : ∀ i, R i →+* S i
  /-- The squares `R_λ → S_λ → S_μ = R_λ → R_μ → S_μ` commute. -/
  square : ∀ ⦃i j⦄ (h : i ≤ j) (x : R i), fS h (g i x) = g j (fR h x)

namespace RingMapSystemUnbundled

variable {Λ : Type*} [Preorder Λ] (sys : RingMapSystemUnbundled Λ)

attribute [instance] RingMapSystemUnbundled.commRingR RingMapSystemUnbundled.commRingS

/-- The colimit ring `R = colim_λ R_λ`. -/
abbrev Rinf := Ring.DirectLimit sys.R (fun _ _ h => sys.fR h)

/-- The colimit ring `S = colim_λ S_λ`. -/
abbrev Sinf := Ring.DirectLimit sys.S (fun _ _ h => sys.fS h)

/-- Per-stage algebra structure `R_λ`-algebra `S_λ`, coming from `g λ`. -/
instance algebraStage (i : Λ) : Algebra (sys.R i) (sys.S i) := (sys.g i).toAlgebra

/-- The induced colimit ring map `R = colim R_λ → colim S_λ = S`. -/
noncomputable def gInf : sys.Rinf →+* sys.Sinf :=
  Ring.DirectLimit.lift sys.R (fun _ _ h => sys.fR h) sys.Sinf
    (fun i => (Ring.DirectLimit.of sys.S (fun _ _ h => sys.fS h) i).comp (sys.g i))
    (by
      intro i j hij x
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← sys.square hij x]
      exact Ring.DirectLimit.of_f hij (sys.g i x))

/-- The colimit `R = colim R_λ` is an algebra over which `S = colim S_λ` is an
algebra, via the induced ring map. -/
noncomputable instance algebraInf : Algebra sys.Rinf sys.Sinf := sys.gInf.toAlgebra

/-- Cocone ring map `R_λ → R`. -/
noncomputable def toRinf (i : Λ) : sys.R i →+* sys.Rinf :=
  Ring.DirectLimit.of sys.R (fun _ _ h => sys.fR h) i

/-- Cocone ring map `S_λ → S`. -/
noncomputable def toSinf (i : Λ) : sys.S i →+* sys.Sinf :=
  Ring.DirectLimit.of sys.S (fun _ _ h => sys.fS h) i

/-- The `S_λ`-algebra structure on `S` given by the cocone map `S_λ → S`. -/
noncomputable instance algebraSiSinf (i : Λ) : Algebra (sys.S i) sys.Sinf :=
  (sys.toSinf i).toAlgebra
/-- The `R_λ`-algebra structure on `R` given by the cocone map `R_λ → R`. -/
noncomputable instance algebraRiRinf (i : Λ) : Algebra (sys.R i) sys.Rinf :=
  (sys.toRinf i).toAlgebra
/-- The `R_λ`-algebra structure on `S` given by the composite `R_λ → S_λ → S`. -/
noncomputable instance algebraRiSinf (i : Λ) : Algebra (sys.R i) sys.Sinf :=
  ((sys.toSinf i).comp (sys.g i)).toAlgebra

/-- Cocone compatibility: `R_λ → R → S` equals `R_λ → S_λ → S`. -/
theorem toSinf_g (i : Λ) (x : sys.R i) :
    sys.toSinf i (sys.g i x) = sys.gInf (sys.toRinf i x) := by
  rw [toRinf, toSinf, gInf, Ring.DirectLimit.lift_of]; rfl

/-- The tower `R_λ → R → S`: the composite `R_λ → R → S` agrees with `R_λ → S_λ → S`. -/
instance towerRiRinfSinf (i : Λ) : IsScalarTower (sys.R i) sys.Rinf sys.Sinf := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change ((sys.toSinf i).comp (sys.g i)) x = sys.gInf (sys.toRinf i x)
  simp only [RingHom.comp_apply]
  exact sys.toSinf_g i x

/-- The tower `R_λ → S_λ → S`, whose composite is the structure map of `S` over `R_λ`. -/
instance towerRiSiSinf (i : Λ) : IsScalarTower (sys.R i) (sys.S i) sys.Sinf := by
  apply IsScalarTower.of_algebraMap_eq; intro x; rfl

/-- The naive cotangent complex `NL_{S_λ/R_λ}`, as a Mathlib `Extension` built
from the canonical presentation `R_λ[S_λ] → S_λ`.  Its `.Cotangent` is the
degree-1 term `I_λ/I_λ²` and its `.CotangentSpace` is the degree-0 term
`Ω_{R_λ[S_λ]/R_λ} ⊗ S_λ`, with `.cotangentComplex` the differential. -/
noncomputable abbrev NL (i : Λ) : Extension (sys.R i) (sys.S i) :=
  (Generators.self (sys.R i) (sys.S i)).toExtension

/-- The naive cotangent complex `NL_{S/R}` of the colimit. -/
noncomputable abbrev NLinf : Extension sys.Rinf sys.Sinf :=
  (Generators.self sys.Rinf sys.Sinf).toExtension

/-- Stage-to-stage transition map on the degree-1 term `I_λ/I_λ² → I_μ/I_μ²`,
the additive (`ℤ`-linear) part of the canonical functoriality map of `NL`. -/
noncomputable def cotMap {i j : Λ} (h : i ≤ j) :
    (sys.NL i).Cotangent →ₗ[ℤ] (sys.NL j).Cotangent :=
  letI aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  letI aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  letI aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  haveI tRRS : IsScalarTower (sys.R i) (sys.R j) (sys.S j) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ((sys.fS h).comp (sys.g i)) x = (sys.g j) (sys.fR h x)
    simp [RingHom.comp_apply, sys.square h x]
  haveI tRSS : IsScalarTower (sys.R i) (sys.S i) (sys.S j) := by
    apply IsScalarTower.of_algebraMap_eq; intro x; rfl
  letI hom := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self (sys.R j) (sys.S j))
  (Extension.Cotangent.map hom.toExtensionHom).toAddMonoidHom.toIntLinearMap

/-- Stage-to-stage transition map on the degree-0 term
`Ω_{R_λ[S_λ]/R_λ} ⊗ S_λ → Ω_{R_μ[S_μ]/R_μ} ⊗ S_μ`. -/
noncomputable def cotSpaceMap {i j : Λ} (h : i ≤ j) :
    (sys.NL i).CotangentSpace →ₗ[ℤ] (sys.NL j).CotangentSpace :=
  letI aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  letI aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  letI aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  haveI tRRS : IsScalarTower (sys.R i) (sys.R j) (sys.S j) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ((sys.fS h).comp (sys.g i)) x = (sys.g j) (sys.fR h x)
    simp [RingHom.comp_apply, sys.square h x]
  haveI tRSS : IsScalarTower (sys.R i) (sys.S i) (sys.S j) := by
    apply IsScalarTower.of_algebraMap_eq; intro x; rfl
  letI hom := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self (sys.R j) (sys.S j))
  (Extension.CotangentSpace.map hom.toExtensionHom).toAddMonoidHom.toIntLinearMap

/-- The scalar towers `R i → R j → S j` and `R i → S i → S j` for the transition maps. -/
private theorem isScalarTower_transition {i j : Λ} (h : i ≤ j) :
    letI : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
    letI : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
    letI : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
    IsScalarTower (sys.R i) (sys.R j) (sys.S j) ∧ IsScalarTower (sys.R i) (sys.S i) (sys.S j) := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  refine ⟨.of_algebraMap_eq fun x => ?_, .of_algebraMap_eq fun _ => rfl⟩
  simp [aRS, aRR, RingHom.algebraMap_toAlgebra, sys.square h x]

/-- **The transition maps commute with the differentials.**
This is the assertion in Definition 4 that the `NL_{S_λ/R_λ}` form a *directed
system of two-term complexes*: the degree-1 transition map followed by the
differential of `NL_μ` equals the differential of `NL_λ` followed by the degree-0
transition map. -/
theorem cotMap_cotangentComplex {i j : Λ} (h : i ≤ j) (x : (sys.NL i).Cotangent) :
    (sys.NL j).cotangentComplex (sys.cotMap h x)
      = sys.cotSpaceMap h ((sys.NL i).cotangentComplex x) := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  let hom := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self (sys.R j) (sys.S j))
  exact (Extension.CotangentSpace.map_cotangentComplex hom.toExtensionHom x).symm

/-- Cocone map on the degree-1 term `I_λ/I_λ² → I/I²`. -/
noncomputable def cotMapInf (i : Λ) :
    (sys.NL i).Cotangent →ₗ[ℤ] sys.NLinf.Cotangent :=
  letI hom := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self sys.Rinf sys.Sinf)
  (Extension.Cotangent.map hom.toExtensionHom).toAddMonoidHom.toIntLinearMap

/-- Cocone map on the degree-0 term `Ω_{R_λ[S_λ]/R_λ} ⊗ S_λ → Ω_{R[S]/R} ⊗ S`. -/
noncomputable def cotSpaceMapInf (i : Λ) :
    (sys.NL i).CotangentSpace →ₗ[ℤ] sys.NLinf.CotangentSpace :=
  letI hom := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self sys.Rinf sys.Sinf)
  (Extension.CotangentSpace.map hom.toExtensionHom).toAddMonoidHom.toIntLinearMap

/-- **The cocone maps commute with the differentials.**
The degree-1 cocone map followed by the differential of `NL_{S/R}` equals the
differential of `NL_{S_λ/R_λ}` followed by the degree-0 cocone map.  This is the
stage-level chain-map property of the comparison morphism. -/
theorem cotMapInf_cotangentComplex (i : Λ) (x : (sys.NL i).Cotangent) :
    sys.NLinf.cotangentComplex (sys.cotMapInf i x)
      = sys.cotSpaceMapInf i ((sys.NL i).cotangentComplex x) := by
  let hom := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self sys.Rinf sys.Sinf)
  exact (Extension.CotangentSpace.map_cotangentComplex hom.toExtensionHom x).symm

/-- The scalar towers `S i → S j → S` and `R i → R j → R` for the cocone maps. -/
private theorem isScalarTower_cocone {i j : Λ} (h : i ≤ j) :
    letI : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
    letI : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
    IsScalarTower (sys.S i) (sys.S j) sys.Sinf ∧ IsScalarTower (sys.R i) (sys.R j) sys.Rinf := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  exact ⟨.of_algebraMap_eq fun x => (Ring.DirectLimit.of_f h x).symm,
    .of_algebraMap_eq fun x => (Ring.DirectLimit.of_f h x).symm⟩

/-! ### Compatibility of the cocone maps with the transition maps

Both `cotMapInf_comp_cotMap` and `cotSpaceMapInf_comp_cotSpaceMap` are instances
of the same statement: the two presentation morphisms

* `homIJ  := (self R_i S_i).defaultHom (self R_j S_j)`     (the `i ≤ j` transition)
* `homJ∞  := (self R_j S_j).defaultHom (self R_∞ S_∞)`     (cocone at stage `j`)
* `homI∞  := (self R_i S_i).defaultHom (self R_∞ S_∞)`     (cocone at stage `i`)

satisfy `homJ∞ ∘ homIJ = homI∞` as morphisms of generators, and `Cotangent.map` /
`CotangentSpace.map` are functorial (`Extension.Cotangent.map_comp`,
`Extension.CotangentSpace.map_comp`).  Hence
`map(homJ∞) ∘ map(homIJ) = map(homJ∞ ∘ homIJ) = map(homI∞)`, which (after the
`.toAddMonoidHom.toIntLinearMap` packaging used to land in `→ₗ[ℤ]`) is exactly
the claimed identity.

The single mathematical fact behind both is the *uniqueness of canonical
presentation morphisms* (`defaultHom_comp_eq` below): any two morphisms of
`Generators.self` presentations with the same underlying ring maps coincide,
because a `Hom` out of `self R S` is determined on the variable `[s]` by the
constraint `aeval (self R' S').val (val [s]) = algebraMap S S' s` together with
the canonical choice `defaultHom_val : val a = (self R' S').σ (algebraMap _ _ a)`.
Concretely `(homJ∞ ∘ homIJ).val` and `homI∞.val` both send the variable `[s]`
to a polynomial whose image under the structure ring map is `toSinf j (fS h s)
= toSinf i s` (cocone compatibility of `toSinf`), and the two agree by
`Generators.Hom.ext`. -/

/-- **Uniqueness of canonical presentation morphisms, in degree 1.**
The composite of the `i ≤ j` transition presentation morphism with the stage-`j`
cocone presentation morphism equals the stage-`i` cocone presentation morphism.

Both sides are morphisms `self R_i S_i → self R_∞ S_∞` of `Generators` over the same
colimit cocone ring maps `R_i → R_∞`, `S_i → S_∞`; these agree because
`toSinf j ∘ fS h = toSinf i` and `toRinf j ∘ fR h = toRinf i`, the defining cocone
identities of `Ring.DirectLimit`.  Applying `Generators.Hom.ext`, it remains to check that
the two `val`s agree on each variable `[s]` (`s : S_i`).  By `defaultHom_val`,
`homI∞.val [s] = σ_∞ (algebraMap (S_i) (S_∞) s) = σ_∞ (toSinf i s)`, while
`(homJ∞.comp homIJ).val [s]` reduces, via the composition formula for
`Generators.Hom.comp` and `defaultHom_val` twice, to `σ_∞ (toSinf j (fS h s))`; these are
equal because `toSinf j (fS h s) = toSinf i s` by `Ring.DirectLimit.of_f`. -/
theorem cotMapInf_comp_cotMap {i j : Λ} (h : i ≤ j) (x : (sys.NL i).Cotangent) :
    sys.cotMapInf j (sys.cotMap h x) = sys.cotMapInf i x := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  obtain ⟨tSiSjSinf, tRiRjRinf⟩ := sys.isScalarTower_cocone h
  let homIJ := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self (sys.R j) (sys.S j))
  let homJinf := (Generators.self (sys.R j) (sys.S j)).defaultHom
    (Generators.self sys.Rinf sys.Sinf)
  let homIinf := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self sys.Rinf sys.Sinf)
  have hom_eq : homJinf.comp homIJ = homIinf := by
    apply Generators.Hom.ext
    funext s
    show (homJinf.comp homIJ).val s = homIinf.val s
    rw [Generators.Hom.comp_val]
    simp only [homIJ, homJinf, homIinf, Generators.defaultHom_val, Function.comp_apply,
      Generators.self_val, id_eq, Generators.self_σ, MvPolynomial.aeval_X]
    congr 1
    show sys.toSinf j (sys.fS h s) = sys.toSinf i s
    exact Ring.DirectLimit.of_f h s
  show (Extension.Cotangent.map homJinf.toExtensionHom)
        ((Extension.Cotangent.map homIJ.toExtensionHom) x)
      = (Extension.Cotangent.map homIinf.toExtensionHom) x
  rw [← hom_eq, Generators.Hom.toExtensionHom_comp, Extension.Cotangent.map_comp]
  rfl

/-- The cocone maps `cotSpaceMapInf` are compatible with the transition maps.
Identical argument to `cotMapInf_comp_cotMap` but in degree 0, using
`Extension.CotangentSpace.map_comp` / `CotangentSpace.map_id` and the same
`defaultHom`-uniqueness fact `homJ∞.comp homIJ = homI∞`.  (One `Hom` equality
serves both degrees, since `Cotangent.map` and `CotangentSpace.map` are both
functorial in the same morphism of `Generators`.) -/
theorem cotSpaceMapInf_comp_cotSpaceMap {i j : Λ} (h : i ≤ j)
    (x : (sys.NL i).CotangentSpace) :
    sys.cotSpaceMapInf j (sys.cotSpaceMap h x) = sys.cotSpaceMapInf i x := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  obtain ⟨tSiSjSinf, tRiRjRinf⟩ := sys.isScalarTower_cocone h
  let homIJ := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self (sys.R j) (sys.S j))
  let homJinf := (Generators.self (sys.R j) (sys.S j)).defaultHom
    (Generators.self sys.Rinf sys.Sinf)
  let homIinf := (Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self sys.Rinf sys.Sinf)
  have hom_eq : homJinf.comp homIJ = homIinf := by
    apply Generators.Hom.ext
    funext s
    show (homJinf.comp homIJ).val s = homIinf.val s
    rw [Generators.Hom.comp_val]
    simp only [homIJ, homJinf, homIinf, Generators.defaultHom_val, Function.comp_apply,
      Generators.self_val, id_eq, Generators.self_σ, MvPolynomial.aeval_X]
    congr 1
    show sys.toSinf j (sys.fS h s) = sys.toSinf i s
    exact Ring.DirectLimit.of_f h s
  show (Extension.CotangentSpace.map homJinf.toExtensionHom)
        ((Extension.CotangentSpace.map homIJ.toExtensionHom) x)
      = (Extension.CotangentSpace.map homIinf.toExtensionHom) x
  rw [← hom_eq, Generators.Hom.toExtensionHom_comp, Extension.CotangentSpace.map_comp]
  rfl

section Colimit

open Classical in
/-- The colimit of the degree-1 terms `colim_λ I_λ/I_λ²`, taken as a colimit of
abelian groups (`ℤ`-modules). -/
noncomputable abbrev colimCotangent :=
  Module.DirectLimit (R := ℤ) (fun i => (sys.NL i).Cotangent)
    (fun _ _ h => sys.cotMap h)

open Classical in
/-- The colimit of the degree-0 terms `colim_λ Ω_{R_λ[S_λ]/R_λ} ⊗ S_λ`. -/
noncomputable abbrev colimCotangentSpace :=
  Module.DirectLimit (R := ℤ) (fun i => (sys.NL i).CotangentSpace)
    (fun _ _ h => sys.cotSpaceMap h)

open Classical in
/-- Cocone map `I_λ/I_λ² → colim_λ I_λ/I_λ²` into the degree-1 colimit. -/
noncomputable def toColimCotangent (i : Λ) :
    (sys.NL i).Cotangent →ₗ[ℤ] sys.colimCotangent :=
  Module.DirectLimit.of ℤ Λ (fun i => (sys.NL i).Cotangent) (fun _ _ h => sys.cotMap h) i

open Classical in
/-- Cocone map `Ω_λ ⊗ S_λ → colim_λ Ω_λ ⊗ S_λ` into the degree-0 colimit. -/
noncomputable def toColimCotangentSpace (i : Λ) :
    (sys.NL i).CotangentSpace →ₗ[ℤ] sys.colimCotangentSpace :=
  Module.DirectLimit.of ℤ Λ (fun i => (sys.NL i).CotangentSpace)
    (fun _ _ h => sys.cotSpaceMap h) i

-- this proof's elaboration needs more than the default heartbeat budget
open Classical in
/-- **The colimit differential** `colim_λ I_λ/I_λ² → colim_λ Ω_λ ⊗ S_λ`,
i.e. the differential of the two-term complex `colim_λ NL_{S_λ/R_λ}`.  It is the
colimit of the stage differentials `(NL_λ).cotangentComplex`; well-definedness
uses `cotMap_cotangentComplex` (the transition maps commute with the
differentials). -/
noncomputable def colimDifferential :
    sys.colimCotangent →ₗ[ℤ] sys.colimCotangentSpace :=
  Module.DirectLimit.lift ℤ Λ (fun i => (sys.NL i).Cotangent) (fun _ _ h => sys.cotMap h)
    (fun i => (sys.toColimCotangentSpace i).comp
      ((sys.NL i).cotangentComplex.toAddMonoidHom.toIntLinearMap))
    (by
      intro i j h x
      simp only [LinearMap.comp_apply]
      change sys.toColimCotangentSpace j ((sys.NL j).cotangentComplex (sys.cotMap h x))
        = sys.toColimCotangentSpace i ((sys.NL i).cotangentComplex x)
      rw [sys.cotMap_cotangentComplex h x, toColimCotangentSpace, toColimCotangentSpace]
      exact Module.DirectLimit.of_f)

open Classical in
/-- The canonical comparison map `colim_λ (I_λ/I_λ²) → I/I²` in degree 1. -/
noncomputable def comparisonCotangent :
    sys.colimCotangent →ₗ[ℤ] sys.NLinf.Cotangent :=
  Module.DirectLimit.lift ℤ Λ (fun i => (sys.NL i).Cotangent) (fun _ _ h => sys.cotMap h)
    (fun i => sys.cotMapInf i) (fun _ _ h x => sys.cotMapInf_comp_cotMap h x)

open Classical in
/-- The canonical comparison map `colim_λ (Ω_λ ⊗ S_λ) → Ω ⊗ S` in degree 0. -/
noncomputable def comparisonCotangentSpace :
    sys.colimCotangentSpace →ₗ[ℤ] sys.NLinf.CotangentSpace :=
  Module.DirectLimit.lift ℤ Λ (fun i => (sys.NL i).CotangentSpace)
    (fun _ _ h => sys.cotSpaceMap h)
    (fun i => sys.cotSpaceMapInf i) (fun _ _ h x => sys.cotSpaceMapInf_comp_cotSpaceMap h x)

/-! ### Degreewise bijectivity of the comparison maps

Both bijectivity statements follow the same two-part schema for a map out of a
filtered colimit `Module.DirectLimit`:

* **Surjectivity.** Every element of the target `NL_∞` arises from some finite
  stage.  This is the statement "the colimit cocone is jointly surjective onto
  the colimit object", which here is *not* automatic from `DirectLimit` alone —
  it is the genuine content "`R[S] = colim R_λ[S_λ]`, `I = colim I_λ`,
  `Ω⊗S = colim Ω_λ⊗S_λ`".  Concretely an element of `NLinf.Cotangent` (resp.
  `CotangentSpace`) is represented by a polynomial / differential form over the
  colimit ring `R_∞[S_∞]`, which involves only finitely many coefficients and
  variables; by filteredness all of them are defined over a single stage `λ`,
  so the element is `cotMapInf λ` (resp. `cotSpaceMapInf λ`) of a stage-`λ`
  element, i.e. lies in the image of the cocone, hence of the comparison map.

* **Injectivity.** If a colimit element maps to `0`, it already maps to `0` at
  some stage.  Using `Module.DirectLimit.of.zero_exact` (which needs the
  `DirectedSystem` instance and `IsDirectedOrder Λ`, both available from
  `[IsDirected]` and `[Nonempty]`), an element of `colimCotangent` is
  `toColimCotangent i y` for some `i, y`; if `comparisonCotangent` sends it to
  `0` then `cotMapInf i y = 0` in `NLinf.Cotangent`, and the "becomes zero at a
  later stage" property of filtered colimits (exactness) gives `j ≥ i` with
  `cotMap (i≤j) y = 0`, whence `toColimCotangent i y = toColimCotangent j
  (cotMap _ y) = 0`.

In degree `0`, `(self R S).toExtension.CotangentSpace` is the *free* `S`-module on `S`
with basis `cotangentSpaceBasis` (`cotangentSpaceBasis_apply : e_b = 1 ⊗ₜ D R _ (X b)`).
Under `CotangentSpace.map` of `defaultHom`, `map_tmul` gives
`e_b ↦ 1 ⊗ₜ D _ _ (X (algebraMap b)) = e_{toSinf b}` up to the `S`-scalar.  So the
comparison map is, basis-wise, induced by `colim_λ S_λ^{(S_λ)} → S^{(S)}`, i.e. "free
modules commute with filtered colimits on the colimit of the index sets `S_λ → S`";
bijectivity reduces to `S = colim S_λ` together with that commutation.  Degree `1`
additionally needs "kernels commute with filtered colimits" applied to `R_λ[S_λ] → S_λ`
(the polynomial-ring colimit `R[S] = colim R_λ[S_λ]` plus exactness of filtered colimits),
and then the quotient by `I_λ²`. -/

/-- `comparisonCotangent` evaluated on a cocone generator is `cotMapInf`. -/
theorem comparisonCotangent_toColim (i : Λ) (z : (sys.NL i).Cotangent) :
    sys.comparisonCotangent (sys.toColimCotangent i z) = sys.cotMapInf i z := by
  classical
  rw [comparisonCotangent, toColimCotangent, Module.DirectLimit.lift_of]

/-- Named cocone presentation morphism at stage `i`: `R_i[S_i] → R_∞[S_∞]`. -/
noncomputable def homIinf (i : Λ) :
    (Generators.self (sys.R i) (sys.S i)).Hom (Generators.self sys.Rinf sys.Sinf) :=
  (Generators.self (sys.R i) (sys.S i)).defaultHom (Generators.self sys.Rinf sys.Sinf)

/-- On the class of a kernel element, the degree-1 cocone map is the functoriality map of
the cocone presentation morphism `homIinf i`. -/
theorem cotMapInf_mk (i : Λ) (x : (sys.NL i).ker) :
    sys.cotMapInf i (Extension.Cotangent.mk x)
      = Extension.Cotangent.map (sys.homIinf i).toExtensionHom (Extension.Cotangent.mk x) := by
  rfl

/-! ### Polynomial-ring colimit infrastructure

The cocone presentation algebra map `Φ_i := (homIinf i).toAlgHom : R_i[S_i] →
R_∞[S_∞]` factors as `map (toRinf i) ∘ rename (toSinf i)`: variables go via the
colimit map `S_i → S_∞`, coefficients via `R_i → R_∞`.  This concrete form is
what turns the abstract "the naive cotangent complex commutes with colimits"
into the elementary statement "`R[S] = colim_λ R_λ[S_λ]`", i.e. that the cocone maps
`Φ_λ` are jointly surjective and exact (an element mapping to `0` already dies at
a finite stage).  What follows is the factorization, kernel compatibility, and the two
analytic colimit facts. -/

/-- **Factorization of the cocone algebra map.** `Φ_i = (homIinf i).toAlgHom`
sends a polynomial by base-changing coefficients along `toRinf i` and renaming
variables along `toSinf i`. -/
theorem homIinf_apply (i : Λ) (p : (sys.NL i).Ring) :
    (sys.homIinf i).toExtensionHom.toAlgHom p
      = MvPolynomial.rename (sys.toSinf i)
          (MvPolynomial.map (sys.toRinf i) p) := by
  show ((Generators.self (sys.R i) (sys.S i)).defaultHom
      (Generators.self sys.Rinf sys.Sinf)).toAlgHom p = _
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, MvPolynomial.map_C, MvPolynomial.rename_C]
    show (algebraMap (sys.R i) (MvPolynomial sys.Sinf sys.Rinf)) a
        = MvPolynomial.C ((sys.toRinf i) a)
    rw [IsScalarTower.algebraMap_apply (sys.R i) sys.Rinf (MvPolynomial sys.Sinf sys.Rinf) a,
      MvPolynomial.algebraMap_eq]
    rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p b hp =>
    rw [map_mul, hp, Generators.Hom.toAlgHom_X, Generators.defaultHom_val]
    simp only [Generators.self_σ, map_mul, MvPolynomial.rename_X, MvPolynomial.map_X,
      Function.comp_apply, Generators.self_val, id_eq]
    rfl

/-- **Kernel compatibility.** Evaluating after the cocone map equals applying the
colimit map after evaluating: `(aeval id) (Φ_i p) = toSinf i ((aeval id) p)`.
Hence `p ∈ I_i ⇒ Φ_i p ∈ I_∞` and conversely a descended `p` lies in the stage
kernel iff its evaluation vanishes in `S_∞`. -/
theorem aeval_homIinf (i : Λ) (p : (sys.NL i).Ring) :
    (MvPolynomial.aeval (R := sys.Rinf) (id : sys.Sinf → sys.Sinf))
        ((sys.homIinf i).toExtensionHom.toAlgHom p)
      = sys.toSinf i ((MvPolynomial.aeval (R := sys.R i) (id : sys.S i → sys.S i)) p) := by
  rw [homIinf_apply]
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.rename_C, MvPolynomial.aeval_C]
    show (algebraMap sys.Rinf sys.Sinf) ((algebraMap (sys.R i) sys.Rinf) a)
      = (algebraMap (sys.S i) sys.Sinf) ((algebraMap (sys.R i) (sys.S i)) a)
    rw [← IsScalarTower.algebraMap_apply (sys.R i) sys.Rinf sys.Sinf a,
      ← IsScalarTower.algebraMap_apply (sys.R i) (sys.S i) sys.Sinf a]
  | add p q hp hq => simp [hp, hq]
  | mul_X p b hp => simp [hp]

/-- Transport a stage-`j₁` polynomial to stage `j` along `j₁ ≤ j`. -/
private theorem polyColim_transport {j₁ j : Λ} (h : j₁ ≤ j) (qt : (sys.NL j₁).Ring) :
    MvPolynomial.rename (sys.toSinf j) (MvPolynomial.map (sys.toRinf j)
        (MvPolynomial.rename (sys.fS h) (MvPolynomial.map (sys.fR h) qt)))
      = MvPolynomial.rename (sys.toSinf j₁) (MvPolynomial.map (sys.toRinf j₁) qt) := by
  rw [MvPolynomial.map_rename, MvPolynomial.rename_rename, MvPolynomial.map_map]
  have hS : (sys.toSinf j) ∘ (sys.fS h) = sys.toSinf j₁ := by
    funext x; exact Ring.DirectLimit.of_f h x
  have hR : (sys.toRinf j).comp (sys.fR h) = sys.toRinf j₁ := by
    ext a; exact Ring.DirectLimit.of_f h a
  rw [hS, hR]

/-- **Joint surjectivity of the polynomial cocone maps (`R[S] = colim R_λ[S_λ]`,
existence half).** Every polynomial `q ∈ R_∞[S_∞]` is the image, under some stage
cocone map `Φ_j` (`j ≥ i`), of a polynomial `qt ∈ R_j[S_j]`.

Proof sketch: `q` uses finitely many variables (`MvPolynomial.exists_finset_rename`)
each of which, lying in `S_∞ = colim S_λ`, is `toSinf` of a stage element
(`Ring.DirectLimit.exists_of`); its finitely many coefficients lie in
`R_∞ = colim R_λ` and similarly descend; merge all the finitely many stages with
`i` into one `j` by directedness, and reassemble `qt` via `rename`/`map`. -/
theorem polyColim_surj [IsDirected Λ (· ≤ ·)] [Nonempty Λ] (i : Λ)
    (q : sys.NLinf.Ring) :
    ∃ (j : Λ) (_ : i ≤ j) (qt : (sys.NL j).Ring),
      (sys.homIinf j).toExtensionHom.toAlgHom qt = q := by
  suffices h : ∃ (j : Λ) (_ : i ≤ j) (qt : (sys.NL j).Ring),
      MvPolynomial.rename (sys.toSinf j) (MvPolynomial.map (sys.toRinf j) qt) = q by
    obtain ⟨j, hij, qt, hqt⟩ := h
    exact ⟨j, hij, qt, by rw [homIinf_apply]; exact hqt⟩
  induction q using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨k, x, hx⟩ := Ring.DirectLimit.exists_of (G := sys.R) a
    obtain ⟨j, hij, hkj⟩ := directed_of (· ≤ ·) i k
    refine ⟨j, hij, MvPolynomial.C (sys.fR hkj x), ?_⟩
    rw [MvPolynomial.map_C, MvPolynomial.rename_C]
    congr 1
    show Ring.DirectLimit.of sys.R (fun _ _ h => sys.fR h) j (sys.fR hkj x) = a
    rw [Ring.DirectLimit.of_f hkj x]; exact hx
  | add p₁ p₂ hp₁ hp₂ =>
    obtain ⟨j₁, hij₁, qt₁, hqt₁⟩ := hp₁
    obtain ⟨j₂, hij₂, qt₂, hqt₂⟩ := hp₂
    obtain ⟨j, hj₁, hj₂⟩ := directed_of (· ≤ ·) j₁ j₂
    refine ⟨j, hij₁.trans hj₁,
      MvPolynomial.rename (sys.fS hj₁) (MvPolynomial.map (sys.fR hj₁) qt₁)
        + MvPolynomial.rename (sys.fS hj₂) (MvPolynomial.map (sys.fR hj₂) qt₂), ?_⟩
    rw [map_add, map_add, sys.polyColim_transport hj₁ qt₁, sys.polyColim_transport hj₂ qt₂,
      hqt₁, hqt₂]
  | mul_X p s hp =>
    obtain ⟨j₁, hij₁, qt₁, hqt₁⟩ := hp
    obtain ⟨k, y, hy⟩ := Ring.DirectLimit.exists_of (G := sys.S) s
    obtain ⟨j, hj₁, hk⟩ := directed_of (· ≤ ·) j₁ k
    refine ⟨j, hij₁.trans hj₁,
      MvPolynomial.rename (sys.fS hj₁) (MvPolynomial.map (sys.fR hj₁) qt₁)
        * MvPolynomial.X (sys.fS hk y), ?_⟩
    rw [map_mul, map_mul, sys.polyColim_transport hj₁ qt₁, hqt₁,
      MvPolynomial.map_X, MvPolynomial.rename_X]
    have hys : sys.toSinf j (sys.fS hk y) = s := by
      show Ring.DirectLimit.of sys.S (fun _ _ h => sys.fS h) j (sys.fS hk y) = s
      rw [Ring.DirectLimit.of_f hk y]; exact hy
    rw [hys]

open Classical in
/-- Coefficient of `rename g' (map φ' qt)` at `d`, as the fiber sum over the
support monomials whose `mapDomain g'` equals `d`. -/
theorem mvpoly_coeff_rename_map
    {σ τ' : Type*} {K K'' : Type*} [CommRing K] [CommRing K'']
    (qt : MvPolynomial σ K) (g' : σ → τ') (φ' : K →+* K'') (d : τ' →₀ ℕ) :
    (MvPolynomial.rename g' (MvPolynomial.map φ' qt)).coeff d
      = ∑ m ∈ (qt.support.filter (fun m => Finsupp.mapDomain g' m = d)),
          φ' (qt.coeff m) := by
  classical
  -- Extending a fiber sum from a polynomial's support to any larger finset (the
  -- extra terms vanish because the coefficient is zero off the support).
  have ext : ∀ (R : MvPolynomial σ K) (T : Finset (σ →₀ ℕ)), R.support ⊆ T →
      ∑ m ∈ R.support.filter (fun m => Finsupp.mapDomain g' m = d), φ' (R.coeff m)
      = ∑ m ∈ T.filter (fun m => Finsupp.mapDomain g' m = d), φ' (R.coeff m) := by
    intro R T hsub
    apply Finset.sum_subset (Finset.filter_subset_filter _ hsub)
    intro m hmT hmR
    rw [Finset.mem_filter] at hmT
    have hm0 : R.coeff m = 0 := by
      by_contra hc
      exact hmR (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr hc, hmT.right⟩)
    rw [hm0, map_zero]
  induction qt using MvPolynomial.induction_on' with
  | monomial u r =>
    rw [MvPolynomial.map_monomial, MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial]
    by_cases hr : r = 0
    · subst hr; simp
    · rw [MvPolynomial.support_monomial, ite_eq_right hr, Finset.filter_singleton]
      by_cases hd : Finsupp.mapDomain g' u = d
      · rw [ite_eq_left hd, ite_eq_left hd, Finset.sum_singleton, MvPolynomial.coeff_monomial,
            ite_eq_left rfl]
      · rw [ite_eq_right hd, ite_eq_right hd, Finset.sum_empty]
  | add p q hp hq =>
    rw [map_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      ext p (p.support ∪ q.support) Finset.subset_union_left,
      ext q (p.support ∪ q.support) Finset.subset_union_right,
      ext (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]

open Classical in
/-- **Abstract descent for `rename`/`map` of a multivariate polynomial.** If the
variable map `g'` refines the collisions of `g` on the support of `qt`, and each
`g`-fiber sum of coefficients vanishes after applying `φ'`, then
`rename g' (map φ' qt) = 0`. -/
theorem mvpoly_rename_map_descends
    {σ τ τ' : Type*} {K K'' : Type*} [CommRing K] [CommRing K'']
    (qt : MvPolynomial σ K) (g : σ → τ) (g' : σ → τ') (φ' : K →+* K'')
    (hColl : ∀ m ∈ qt.support, ∀ m' ∈ qt.support,
      Finsupp.mapDomain g m = Finsupp.mapDomain g m' →
      Finsupp.mapDomain g' m = Finsupp.mapDomain g' m')
    (hCoeff : ∀ e : τ →₀ ℕ,
      φ' (∑ m ∈ qt.support.filter (fun m => Finsupp.mapDomain g m = e),
        qt.coeff m) = 0) :
    MvPolynomial.rename g' (MvPolynomial.map φ' qt) = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [mvpoly_coeff_rename_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  set Sd := qt.support.filter (fun m => Finsupp.mapDomain g' m = d) with hSd
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun m => Finsupp.mapDomain g m)
      (t := Sd.image (fun m => Finsupp.mapDomain g m))
      (fun m hm => Finset.mem_image_of_mem _ hm)]
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨m₀, hm₀, hm₀e⟩ := he
  have hfiltereq : Sd.filter (fun m => Finsupp.mapDomain g m = e)
      = qt.support.filter (fun m => Finsupp.mapDomain g m = e) := by
    apply Finset.ext
    intro m
    simp only [hSd, Finset.mem_filter]
    rw [hSd, Finset.mem_filter] at hm₀
    refine ⟨fun ⟨⟨hmem, _⟩, hge⟩ => ⟨hmem, hge⟩, fun ⟨hmem, hge⟩ => ⟨⟨hmem, ?_⟩, hge⟩⟩
    rw [hColl m hmem m₀ hm₀.1 (by rw [hge, hm₀e]), hm₀.2]
  rw [hfiltereq, ← map_sum]
  exact hCoeff e

/-- **Collision transfer.** If on a finite set `V` the map `w` is constant on the
fibers of `u`, then equal `mapDomain u`-images imply equal `mapDomain w`-images
(for monomials supported in `V`). -/
theorem mapDomain_collision_transfer
    {σ A B : Type*} [Inhabited B] (V : Finset σ) (u : σ → A) (w : σ → B)
    (hcompat : ∀ v ∈ V, ∀ v' ∈ V, u v = u v' → w v = w v')
    (m m' : σ →₀ ℕ) (hm : m.support ⊆ V) (hm' : m'.support ⊆ V)
    (h : Finsupp.mapDomain u m = Finsupp.mapDomain u m') :
    Finsupp.mapDomain w m = Finsupp.mapDomain w m' := by
  classical
  set ρ : A → B := fun a => if h : ∃ v ∈ V, u v = a then w h.choose else default with hρ
  have hρu : ∀ v ∈ V, ρ (u v) = w v := by
    intro v hv
    have hex : ∃ v' ∈ V, u v' = u v := ⟨v, hv, rfl⟩
    rw [hρ]
    simp only [hex, dite_eq_left]
    obtain ⟨hc1, hc2⟩ := hex.choose_spec
    exact hcompat _ hc1 v hv hc2
  have key : ∀ (p : σ →₀ ℕ), p.support ⊆ V →
      Finsupp.mapDomain w p = Finsupp.mapDomain ρ (Finsupp.mapDomain u p) := by
    intro p hp
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun v hv => (hρu v (hp hv)).symm
  rw [key m hm, key m' hm', h]

/-- A finite set of elements of a stage ring all dying in the colimit ring already dies at a
common finite stage. -/
private theorem finset_zero_realize [IsDirected Λ (· ≤ ·)] [Nonempty Λ] {G : Λ → Type*}
    [∀ i, CommRing (G i)] (f : ∀ ⦃i j⦄, i ≤ j → G i →+* G j) (f_id : ∀ i x, f (le_refl i) x = x)
    (f_comp : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) x, f hjk (f hij x) = f (hij.trans hjk) x)
    {i : Λ} (xs : Finset (G i)) (hxs : ∀ x ∈ xs, Ring.DirectLimit.of G (fun _ _ h => f h) i x = 0) :
    ∃ (j : Λ) (h : i ≤ j), ∀ x ∈ xs, f h x = 0 := by
  have : IsDirectedOrder Λ := inferInstance
  have : DirectedSystem G (fun i j h => ⇑(f h)) := ⟨f_id, fun _ _ _ hij hjk x => f_comp hij hjk x⟩
  classical
  induction xs using Finset.induction with
  | empty => exact ⟨i, le_refl i, fun x hx => by simp at hx⟩
  | @insert a s ha ih =>
    obtain ⟨j, hj, hjall⟩ := ih fun x hx => hxs x (Finset.mem_insert_of_mem hx)
    obtain ⟨k, hik, hak⟩ := Ring.DirectLimit.of.zero_exact (f' := f) (i := i) (x := a)
      (hxs a (Finset.mem_insert_self a s))
    obtain ⟨m, hjm, hkm⟩ := directed_of (· ≤ ·) j k
    refine ⟨m, hj.trans hjm, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rw [← f_comp hik hkm x, hak, map_zero]
    · rw [← f_comp hj hjm x, hjall x hx, map_zero]

/-- A finite set of stage-`i` elements all dying in `Sinf` already dies at a
common finite stage. -/
theorem fS_zero_realize_aux [IsDirected Λ (· ≤ ·)] [Nonempty Λ] {i : Λ}
    (xs : Finset (sys.S i)) (hxs : ∀ x ∈ xs, sys.toSinf i x = 0) :
    ∃ (j : Λ) (h : i ≤ j), ∀ x ∈ xs, sys.fS h x = 0 :=
  finset_zero_realize sys.fS sys.fS_id sys.fS_comp xs hxs

/-- A finite set of stage-`i` ring elements all dying in `Rinf` already dies at a
common finite stage. -/
theorem fR_zero_realize_aux [IsDirected Λ (· ≤ ·)] [Nonempty Λ] {i : Λ}
    (xs : Finset (sys.R i)) (hxs : ∀ x ∈ xs, sys.toRinf i x = 0) :
    ∃ (j : Λ) (h : i ≤ j), ∀ x ∈ xs, sys.fR h x = 0 :=
  finset_zero_realize sys.fR sys.fR_id sys.fR_comp xs hxs

/-- Factorization of the transition default-hom algebra map: a polynomial is sent by
base-changing coefficients along `fR h` and renaming variables along `fS h`. -/
theorem transHom_apply_aux {i j : Λ} (h : i ≤ j) (p : (sys.NL i).Ring) :
    letI aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
    letI aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
    letI aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
    haveI tRRS : IsScalarTower (sys.R i) (sys.R j) (sys.S j) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change ((sys.fS h).comp (sys.g i)) x = (sys.g j) (sys.fR h x)
      simp [RingHom.comp_apply, sys.square h x]
    haveI tRSS : IsScalarTower (sys.R i) (sys.S i) (sys.S j) := by
      apply IsScalarTower.of_algebraMap_eq; intro x; rfl
    ((Generators.self (sys.R i) (sys.S i)).defaultHom
      (Generators.self (sys.R j) (sys.S j))).toExtensionHom.toAlgHom p
      = MvPolynomial.rename (sys.fS h) (MvPolynomial.map (sys.fR h) p) := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  show ((Generators.self (sys.R i) (sys.S i)).defaultHom
      (Generators.self (sys.R j) (sys.S j))).toAlgHom p = _
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, MvPolynomial.map_C, MvPolynomial.rename_C]
    show (algebraMap (sys.R i) (MvPolynomial (sys.S j) (sys.R j))) a
        = MvPolynomial.C ((sys.fR h) a)
    rw [IsScalarTower.algebraMap_apply (sys.R i) (sys.R j) (MvPolynomial (sys.S j) (sys.R j)) a,
      MvPolynomial.algebraMap_eq]
    rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p b hp =>
    rw [map_mul, hp, Generators.Hom.toAlgHom_X, Generators.defaultHom_val]
    simp only [Generators.self_σ, map_mul, MvPolynomial.rename_X, MvPolynomial.map_X,
      Function.comp_apply, Generators.self_val, id_eq]
    rfl

/-- **Exactness of the polynomial cocone maps (`R[S] = colim R_λ[S_λ]`, kernel half).**
If a stage polynomial `qt ∈ R_j[S_j]` maps to `0` in `R_∞[S_∞]` under the cocone map
`Φ_j`, then it already dies at a finite stage `k ≥ j`, i.e. its image under the transition
map `Φ_{jk}` is `0`.

By the factorization `Φ_j = map (toRinf j) ∘ rename (toSinf j)`, the equation `Φ_j qt = 0`
is a finite system of coefficient and variable identities in the colimits `R_∞` and `S_∞`;
each of them is realized at a finite stage (`Ring.DirectLimit.of.zero_exact` on `R_λ` for
the coefficients, and collisions of variables `toSinf j a = toSinf j b` realized at a stage
on `S_λ`), and directedness merges them into a single `k`. -/
theorem polyColim_zero_exact [IsDirected Λ (· ≤ ·)] [Nonempty Λ] {j : Λ}
    (qt : (sys.NL j).Ring)
    (hq : (sys.homIinf j).toExtensionHom.toAlgHom qt = 0) :
    ∃ (k : Λ) (h : j ≤ k),
      letI aRR : Algebra (sys.R j) (sys.R k) := (sys.fR h).toAlgebra
      letI aSS : Algebra (sys.S j) (sys.S k) := (sys.fS h).toAlgebra
      letI aRS : Algebra (sys.R j) (sys.S k) := ((sys.fS h).comp (sys.g j)).toAlgebra
      haveI tRRS : IsScalarTower (sys.R j) (sys.R k) (sys.S k) := by
        apply IsScalarTower.of_algebraMap_eq
        intro x
        change ((sys.fS h).comp (sys.g j)) x = (sys.g k) (sys.fR h x)
        simp [RingHom.comp_apply, sys.square h x]
      haveI tRSS : IsScalarTower (sys.R j) (sys.S j) (sys.S k) := by
        apply IsScalarTower.of_algebraMap_eq; intro x; rfl
      ((Generators.self (sys.R j) (sys.S j)).defaultHom
        (Generators.self (sys.R k) (sys.S k))).toExtensionHom.toAlgHom qt = 0 := by
  classical
  rw [homIinf_apply] at hq
  -- finite variable set and fiber-sum function
  set V : Finset (sys.S j) := qt.support.biUnion (fun m => m.support) with hV
  set σfun : (sys.Sinf →₀ ℕ) → sys.R j :=
    fun e => ∑ m ∈ qt.support.filter (fun m => Finsupp.mapDomain (sys.toSinf j) m = e),
      qt.coeff m with hσfun
  -- ∞-coefficient vanishing
  have hinfCoeff : ∀ e : sys.Sinf →₀ ℕ, sys.toRinf j (σfun e) = 0 := by
    intro e
    rw [hσfun]
    simp only [map_sum]
    rw [← mvpoly_coeff_rename_map qt (sys.toSinf j) (sys.toRinf j) e, hq,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  -- realize variable collisions at a stage k1
  set xsV : Finset (sys.S j) :=
    ((V ×ˢ V).image (fun p => p.fst - p.snd)).filter (fun z => sys.toSinf j z = 0) with hxsV
  have hxsVz : ∀ z ∈ xsV, sys.toSinf j z = 0 := by
    intro z hz
    rw [hxsV, Finset.mem_filter] at hz
    exact hz.right
  obtain ⟨k1, hk1, hk1all⟩ := sys.fS_zero_realize_aux xsV hxsVz
  -- realize coefficient fiber-sums at a stage k2
  set E : Finset (sys.Sinf →₀ ℕ) := qt.support.image (fun m => Finsupp.mapDomain (sys.toSinf j) m)
    with hE
  set xsR : Finset (sys.R j) := E.image σfun with hxsR
  have hxsRz : ∀ x ∈ xsR, sys.toRinf j x = 0 := by
    intro x hx
    rw [hxsR, Finset.mem_image] at hx
    obtain ⟨e, _, rfl⟩ := hx
    exact hinfCoeff e
  obtain ⟨k2, hk2, hk2all⟩ := sys.fR_zero_realize_aux xsR hxsRz
  -- merge k1, k2
  obtain ⟨k, hk1k, hk2k⟩ := directed_of (· ≤ ·) k1 k2
  have h : j ≤ k := hk1.trans hk1k
  refine ⟨k, h, ?_⟩
  -- prepare instances (as in transHom_apply)
  let aRR : Algebra (sys.R j) (sys.R k) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S j) (sys.S k) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R j) (sys.S k) := ((sys.fS h).comp (sys.g j)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  have : Inhabited (sys.S k) := ⟨0⟩
  -- reduce the goal to a `rename`/`map` statement
  rw [sys.transHom_apply_aux h qt]
  -- now apply the abstract descent lemma
  apply mvpoly_rename_map_descends qt (sys.toSinf j) (sys.fS h) (sys.fR h)
  · -- Coll: collisions of toSinf j refine to collisions of fS h
    intro m hm m' hm' heq
    have hcompat : ∀ v ∈ V, ∀ v' ∈ V,
        sys.toSinf j v = sys.toSinf j v' → sys.fS h v = sys.fS h v' := by
      intro v hv v' hv' hvv
      have hmem : (v - v') ∈ xsV := by
        rw [hxsV, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_image]
          exact ⟨(v, v'), Finset.mem_product.mpr ⟨hv, hv'⟩, rfl⟩
        · rw [map_sub, hvv, sub_self]
      have hz1 : sys.fS hk1 (v - v') = 0 := hk1all _ hmem
      have : sys.fS h (v - v') = 0 := by
        rw [← sys.fS_comp hk1 hk1k (v - v'), hz1, map_zero]
      rw [map_sub, sub_eq_zero] at this
      exact this
    have hmV : m.support ⊆ V := by
      rw [hV]; exact Finset.subset_biUnion_of_mem (fun m => m.support) hm
    have hm'V : m'.support ⊆ V := by
      rw [hV]; exact Finset.subset_biUnion_of_mem (fun m => m.support) hm'
    exact mapDomain_collision_transfer V (sys.toSinf j) (sys.fS h) hcompat m m' hmV hm'V heq
  · -- Coeff: each fiber-sum vanishes after fR h
    intro e
    by_cases he : e ∈ E
    · have hx : σfun e ∈ xsR := by
        rw [hxsR, Finset.mem_image]; exact ⟨e, he, rfl⟩
      have hz2 : sys.fR hk2 (σfun e) = 0 := hk2all _ hx
      have : sys.fR h (σfun e) = 0 := by
        rw [← sys.fR_comp hk2 hk2k (σfun e), hz2, map_zero]
      simpa [hσfun] using this
    · -- e ∉ E: the fiber is empty, sum is 0
      have hempty : qt.support.filter (fun m => Finsupp.mapDomain (sys.toSinf j) m = e) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro m hm hcontra
        exact he (by rw [hE, Finset.mem_image]; exact ⟨m, hm, hcontra⟩)
      rw [hempty, Finset.sum_empty, map_zero]

/-- Factorization of the transition default-hom algebra map analogous to
`homIinf_apply`. -/
alias transHom_apply := RingMapSystemUnbundled.transHom_apply_aux

/-- Kernel compatibility for the transition default-hom, analogous to
`aeval_homIinf`. -/
theorem aeval_transHom {i j : Λ} (h : i ≤ j) (p : (sys.NL i).Ring) :
    letI aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
    letI aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
    letI aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
    haveI tRRS : IsScalarTower (sys.R i) (sys.R j) (sys.S j) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change ((sys.fS h).comp (sys.g i)) x = (sys.g j) (sys.fR h x)
      simp [RingHom.comp_apply, sys.square h x]
    haveI tRSS : IsScalarTower (sys.R i) (sys.S i) (sys.S j) := by
      apply IsScalarTower.of_algebraMap_eq; intro x; rfl
    (MvPolynomial.aeval (R := sys.R j) (id : sys.S j → sys.S j))
        (((Generators.self (sys.R i) (sys.S i)).defaultHom
          (Generators.self (sys.R j) (sys.S j))).toExtensionHom.toAlgHom p)
      = sys.fS h ((MvPolynomial.aeval (R := sys.R i) (id : sys.S i → sys.S i)) p) := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  rw [sys.transHom_apply h]
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.rename_C, MvPolynomial.aeval_C]
    show (algebraMap (sys.R j) (sys.S j)) ((sys.fR h) a)
      = (sys.fS h) ((algebraMap (sys.R i) (sys.S i)) a)
    show (sys.g j) ((sys.fR h) a) = (sys.fS h) ((sys.g i) a)
    rw [sys.square h a]
  | add p q hp hq => simp [hp, hq]
  | mul_X p b hp => simp [hp]

/-- The cocone composition identity at the polynomial-algebra level: the stage-`j`
cocone map composed with the `i ≤ j` transition map equals the stage-`i` cocone
map. -/
theorem homIinf_transHom_comp [IsDirected Λ (· ≤ ·)] [Nonempty Λ] {i j : Λ}
    (h : i ≤ j) (p : (sys.NL i).Ring) :
    letI aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
    letI aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
    letI aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
    haveI tRRS : IsScalarTower (sys.R i) (sys.R j) (sys.S j) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change ((sys.fS h).comp (sys.g i)) x = (sys.g j) (sys.fR h x)
      simp [RingHom.comp_apply, sys.square h x]
    haveI tRSS : IsScalarTower (sys.R i) (sys.S i) (sys.S j) := by
      apply IsScalarTower.of_algebraMap_eq; intro x; rfl
    (sys.homIinf j).toExtensionHom.toAlgHom
        (((Generators.self (sys.R i) (sys.S i)).defaultHom
          (Generators.self (sys.R j) (sys.S j))).toExtensionHom.toAlgHom p)
      = (sys.homIinf i).toExtensionHom.toAlgHom p := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  rw [sys.homIinf_apply j, sys.homIinf_apply i, sys.transHom_apply h]
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.rename_C]
    congr 1
    show sys.toRinf j (sys.fR h a) = sys.toRinf i a
    exact Ring.DirectLimit.of_f h a
  | add p q hp hq => simp [hp, hq]
  | mul_X p b hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.rename_X]
    rw [hp]
    congr 1
    show MvPolynomial.X (sys.toSinf j (sys.fS h b)) = MvPolynomial.X (sys.toSinf i b)
    congr 1
    exact Ring.DirectLimit.of_f h b

/-- The transition composition identity at the polynomial-algebra level. -/
theorem transHom_trans [IsDirected Λ (· ≤ ·)] [Nonempty Λ] {i j k : Λ}
    (hij : i ≤ j) (hjk : j ≤ k) (p : (sys.NL i).Ring) :
    letI aRRj : Algebra (sys.R i) (sys.R j) := (sys.fR hij).toAlgebra
    letI aSSj : Algebra (sys.S i) (sys.S j) := (sys.fS hij).toAlgebra
    letI aRSj : Algebra (sys.R i) (sys.S j) := ((sys.fS hij).comp (sys.g i)).toAlgebra
    letI aRRk : Algebra (sys.R j) (sys.R k) := (sys.fR hjk).toAlgebra
    letI aSSk : Algebra (sys.S j) (sys.S k) := (sys.fS hjk).toAlgebra
    letI aRSk : Algebra (sys.R j) (sys.S k) := ((sys.fS hjk).comp (sys.g j)).toAlgebra
    letI aRRik : Algebra (sys.R i) (sys.R k) := (sys.fR (hij.trans hjk)).toAlgebra
    letI aSSik : Algebra (sys.S i) (sys.S k) := (sys.fS (hij.trans hjk)).toAlgebra
    letI aRSik : Algebra (sys.R i) (sys.S k) := ((sys.fS (hij.trans hjk)).comp (sys.g i)).toAlgebra
    haveI tRRSj : IsScalarTower (sys.R i) (sys.R j) (sys.S j) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change ((sys.fS hij).comp (sys.g i)) x = (sys.g j) (sys.fR hij x)
      simp [RingHom.comp_apply, sys.square hij x]
    haveI tRSSj : IsScalarTower (sys.R i) (sys.S i) (sys.S j) := by
      apply IsScalarTower.of_algebraMap_eq; intro x; rfl
    haveI tRRSk : IsScalarTower (sys.R j) (sys.R k) (sys.S k) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change ((sys.fS hjk).comp (sys.g j)) x = (sys.g k) (sys.fR hjk x)
      simp [RingHom.comp_apply, sys.square hjk x]
    haveI tRSSk : IsScalarTower (sys.R j) (sys.S j) (sys.S k) := by
      apply IsScalarTower.of_algebraMap_eq; intro x; rfl
    haveI tRRSik : IsScalarTower (sys.R i) (sys.R k) (sys.S k) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change ((sys.fS (hij.trans hjk)).comp (sys.g i)) x = (sys.g k) (sys.fR (hij.trans hjk) x)
      simp [RingHom.comp_apply, sys.square (hij.trans hjk) x]
    haveI tRSSik : IsScalarTower (sys.R i) (sys.S i) (sys.S k) := by
      apply IsScalarTower.of_algebraMap_eq; intro x; rfl
    ((Generators.self (sys.R j) (sys.S j)).defaultHom
        (Generators.self (sys.R k) (sys.S k))).toExtensionHom.toAlgHom
        (((Generators.self (sys.R i) (sys.S i)).defaultHom
          (Generators.self (sys.R j) (sys.S j))).toExtensionHom.toAlgHom p)
      = ((Generators.self (sys.R i) (sys.S i)).defaultHom
          (Generators.self (sys.R k) (sys.S k))).toExtensionHom.toAlgHom p := by
  let aRRj : Algebra (sys.R i) (sys.R j) := (sys.fR hij).toAlgebra
  let aSSj : Algebra (sys.S i) (sys.S j) := (sys.fS hij).toAlgebra
  let aRSj : Algebra (sys.R i) (sys.S j) := ((sys.fS hij).comp (sys.g i)).toAlgebra
  let aRRk : Algebra (sys.R j) (sys.R k) := (sys.fR hjk).toAlgebra
  let aSSk : Algebra (sys.S j) (sys.S k) := (sys.fS hjk).toAlgebra
  let aRSk : Algebra (sys.R j) (sys.S k) := ((sys.fS hjk).comp (sys.g j)).toAlgebra
  let aRRik : Algebra (sys.R i) (sys.R k) := (sys.fR (hij.trans hjk)).toAlgebra
  let aSSik : Algebra (sys.S i) (sys.S k) := (sys.fS (hij.trans hjk)).toAlgebra
  let aRSik : Algebra (sys.R i) (sys.S k) := ((sys.fS (hij.trans hjk)).comp (sys.g i)).toAlgebra
  obtain ⟨tRRSj, tRSSj⟩ := sys.isScalarTower_transition hij
  obtain ⟨tRRSk, tRSSk⟩ := sys.isScalarTower_transition hjk
  obtain ⟨tRRSik, tRSSik⟩ := sys.isScalarTower_transition (hij.trans hjk)
  rw [sys.transHom_apply hjk, sys.transHom_apply hij, sys.transHom_apply (hij.trans hjk)]
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.rename_C]
    congr 1
    show sys.fR hjk (sys.fR hij a) = sys.fR (hij.trans hjk) a
    exact sys.fR_comp hij hjk a
  | add p q hp hq => simp [hp, hq]
  | mul_X p b hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.rename_X]
    rw [hp]
    congr 1
    congr 1
    exact sys.fS_comp hij hjk b

/-- Descend a single colimit-kernel element to a finite stage where its
preimage already lies in the stage kernel. -/
theorem descend_one [IsDirected Λ (· ≤ ·)] [Nonempty Λ] (i : Λ) (a : sys.NLinf.Ring)
    (ha : (MvPolynomial.aeval (R := sys.Rinf) (id : sys.Sinf → sys.Sinf)) a = 0) :
    ∃ (m : Λ) (_ : i ≤ m) (ã : (sys.NL m).Ring),
      (MvPolynomial.aeval (R := sys.R m) (id : sys.S m → sys.S m)) ã = 0 ∧
      (sys.homIinf m).toExtensionHom.toAlgHom ã = a := by
  classical
  obtain ⟨m₀, him₀, ã₀, hã₀⟩ := sys.polyColim_surj i a
  -- the evaluation of `ã₀` dies in `Sinf`
  have hz : sys.toSinf m₀ ((MvPolynomial.aeval (R := sys.R m₀)
      (id : sys.S m₀ → sys.S m₀)) ã₀) = 0 := by
    rw [← sys.aeval_homIinf m₀ ã₀, hã₀, ha]
  -- realize this vanishing at a finite stage
  have directedS : DirectedSystem sys.S (fun i j h => ⇑(sys.fS h)) :=
    ⟨fun i x => sys.fS_id i x, fun i j k hij hjk x => sys.fS_comp hij hjk x⟩
  obtain ⟨m, hm, hfsz⟩ := Ring.DirectLimit.of.zero_exact (f' := sys.fS) (i := m₀)
    (x := (MvPolynomial.aeval (R := sys.R m₀) (id : sys.S m₀ → sys.S m₀)) ã₀) hz
  let aRR : Algebra (sys.R m₀) (sys.R m) := (sys.fR hm).toAlgebra
  let aSS : Algebra (sys.S m₀) (sys.S m) := (sys.fS hm).toAlgebra
  let aRS : Algebra (sys.R m₀) (sys.S m) := ((sys.fS hm).comp (sys.g m₀)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition hm
  refine ⟨m, him₀.trans hm,
    ((Generators.self (sys.R m₀) (sys.S m₀)).defaultHom
      (Generators.self (sys.R m) (sys.S m))).toExtensionHom.toAlgHom ã₀, ?_, ?_⟩
  · rw [sys.aeval_transHom hm ã₀, hfsz]
  · rw [sys.homIinf_transHom_comp hm ã₀, hã₀]

-- this proof's elaboration needs more than the default heartbeat budget
/-- Descend a whole list of colimit-kernel factor pairs to a common finite stage,
preserving the products' total sum under the cocone map and the kernel membership
of each factor. -/
theorem descend_list [IsDirected Λ (· ≤ ·)] [Nonempty Λ] (i : Λ)
    (L : List (sys.NLinf.Ring × sys.NLinf.Ring))
    (hL : ∀ pr ∈ L,
      (MvPolynomial.aeval (R := sys.Rinf) (id : sys.Sinf → sys.Sinf)) pr.1 = 0 ∧
      (MvPolynomial.aeval (R := sys.Rinf) (id : sys.Sinf → sys.Sinf)) pr.2 = 0) :
    ∃ (m : Λ) (_ : i ≤ m) (L' : List ((sys.NL m).Ring × (sys.NL m).Ring)),
      (∀ pr ∈ L',
        (MvPolynomial.aeval (R := sys.R m) (id : sys.S m → sys.S m)) pr.1 = 0 ∧
        (MvPolynomial.aeval (R := sys.R m) (id : sys.S m → sys.S m)) pr.2 = 0) ∧
      (sys.homIinf m).toExtensionHom.toAlgHom
          ((L'.map (fun pr => pr.1 * pr.2)).sum)
        = (L.map (fun pr => pr.1 * pr.2)).sum := by
  classical
  induction L with
  | nil =>
    obtain ⟨m₀⟩ := (inferInstance : Nonempty Λ)
    obtain ⟨m, hm, _⟩ := directed_of (· ≤ ·) i m₀
    exact ⟨m, hm, [], by simp, by simp only [List.map_nil, List.sum_nil]; exact map_zero _⟩
  | cons pr t ih =>
    have ht : ∀ pr' ∈ t,
        (MvPolynomial.aeval (R := sys.Rinf) (id : sys.Sinf → sys.Sinf)) pr'.fst = 0 ∧
        (MvPolynomial.aeval (R := sys.Rinf) (id : sys.Sinf → sys.Sinf)) pr'.snd = 0 :=
      fun pr' hpr' => hL pr' (List.mem_cons_of_mem _ hpr')
    obtain ⟨mt, himt, t', ht', hsumt⟩ := ih ht
    have hpr := hL pr (by simp)
    obtain ⟨ma, hima, ã, hãk, hãΦ⟩ := sys.descend_one i pr.fst hpr.left
    obtain ⟨mb, himb, bb, hbbk, hbbphi⟩ := sys.descend_one i pr.snd hpr.right
    -- merge the three stages `mt, ma, mb` into one `m ≥ i`
    obtain ⟨m1, hm1a, hm1b⟩ := directed_of (· ≤ ·) ma mb
    obtain ⟨m, hmt, hm1⟩ := directed_of (· ≤ ·) mt m1
    have him : i ≤ m := himt.trans hmt
    -- push `ã`, `bb` to stage `m`
    let aRRa : Algebra (sys.R ma) (sys.R m) := (sys.fR (hm1a.trans hm1)).toAlgebra
    let aSSa : Algebra (sys.S ma) (sys.S m) := (sys.fS (hm1a.trans hm1)).toAlgebra
    let aRSa : Algebra (sys.R ma) (sys.S m) := ((sys.fS (hm1a.trans hm1)).comp (sys.g
        ma)).toAlgebra
    obtain ⟨tRRSa, tRSSa⟩ := sys.isScalarTower_transition (hm1a.trans hm1)
    let aRRb : Algebra (sys.R mb) (sys.R m) := (sys.fR (hm1b.trans hm1)).toAlgebra
    let aSSb : Algebra (sys.S mb) (sys.S m) := (sys.fS (hm1b.trans hm1)).toAlgebra
    let aRSb : Algebra (sys.R mb) (sys.S m) := ((sys.fS (hm1b.trans hm1)).comp (sys.g
        mb)).toAlgebra
    obtain ⟨tRRSb, tRSSb⟩ := sys.isScalarTower_transition (hm1b.trans hm1)
    let aRRt : Algebra (sys.R mt) (sys.R m) := (sys.fR hmt).toAlgebra
    let aSSt : Algebra (sys.S mt) (sys.S m) := (sys.fS hmt).toAlgebra
    let aRSt : Algebra (sys.R mt) (sys.S m) := ((sys.fS hmt).comp (sys.g mt)).toAlgebra
    obtain ⟨tRRSt, tRSSt⟩ := sys.isScalarTower_transition hmt
    set ãm := ((Generators.self (sys.R ma) (sys.S ma)).defaultHom
      (Generators.self (sys.R m) (sys.S m))).toExtensionHom.toAlgHom ã with hãm
    set bbm := ((Generators.self (sys.R mb) (sys.S mb)).defaultHom
      (Generators.self (sys.R m) (sys.S m))).toExtensionHom.toAlgHom bb with hbbm
    set t'm : List ((sys.NL m).Ring × (sys.NL m).Ring) :=
      t'.map (fun q => (((Generators.self (sys.R mt) (sys.S mt)).defaultHom
        (Generators.self (sys.R m) (sys.S m))).toExtensionHom.toAlgHom q.fst,
        ((Generators.self (sys.R mt) (sys.S mt)).defaultHom
        (Generators.self (sys.R m) (sys.S m))).toExtensionHom.toAlgHom q.snd)) with ht'm
    refine ⟨m, him, (ãm, bbm) :: t'm, ?_, ?_⟩
    · -- kernel membership of each pushed pair
      intro pr' hpr'
      rw [List.mem_cons] at hpr'
      rcases hpr' with rfl | hpr'
      · refine ⟨?_, ?_⟩
        · show (MvPolynomial.aeval (R := sys.R m) (id : sys.S m → sys.S m)) ãm = 0
          rw [hãm, sys.aeval_transHom (hm1a.trans hm1) ã, hãk, map_zero]
        · show (MvPolynomial.aeval (R := sys.R m) (id : sys.S m → sys.S m)) bbm = 0
          rw [hbbm, sys.aeval_transHom (hm1b.trans hm1) bb, hbbk, map_zero]
      · rw [ht'm, List.mem_map] at hpr'
        obtain ⟨q, hq, rfl⟩ := hpr'
        refine ⟨?_, ?_⟩
        · show (MvPolynomial.aeval (R := sys.R m) (id : sys.S m → sys.S m))
            (((Generators.self (sys.R mt) (sys.S mt)).defaultHom
              (Generators.self (sys.R m) (sys.S m))).toExtensionHom.toAlgHom q.fst) = 0
          rw [sys.aeval_transHom hmt q.fst, (ht' q hq).left, map_zero]
        · show (MvPolynomial.aeval (R := sys.R m) (id : sys.S m → sys.S m))
            (((Generators.self (sys.R mt) (sys.S mt)).defaultHom
              (Generators.self (sys.R m) (sys.S m))).toExtensionHom.toAlgHom q.snd) = 0
          rw [sys.aeval_transHom hmt q.snd, (ht' q hq).right, map_zero]
    · -- cocone map of the sum
      simp only [List.map_cons, List.sum_cons, map_add, map_mul]
      congr 1
      · -- head pair
        rw [hãm, hbbm, sys.homIinf_transHom_comp (hm1a.trans hm1) ã,
          sys.homIinf_transHom_comp (hm1b.trans hm1) bb, hãΦ, hbbphi]
      · -- tail
        rw [← hsumt, ht'm, List.map_map]
        -- general: cocone-comp distributes over the list sum
        have htail : ∀ (s : List ((sys.NL mt).Ring × (sys.NL mt).Ring)),
            (sys.homIinf m).toExtensionHom.toAlgHom
              ((s.map ((fun pr => pr.fst * pr.snd) ∘
                (fun q => (((Generators.self (sys.R mt) (sys.S mt)).defaultHom
                  (Generators.self (sys.R m) (sys.S m))).toExtensionHom.toAlgHom q.fst,
                  ((Generators.self (sys.R mt) (sys.S mt)).defaultHom
                  (Generators.self (sys.R m) (sys.S m))).toExtensionHom.toAlgHom q.snd)))).sum)
              = (sys.homIinf mt).toExtensionHom.toAlgHom
                ((s.map (fun pr => pr.fst * pr.snd)).sum) := by
          intro s
          induction s with
          | nil => simp only [List.map_nil, List.sum_nil]; rw [map_zero, map_zero]
          | cons q s ihs =>
            simp only [List.map_cons, List.sum_cons, map_add, map_mul, Function.comp_apply]
            rw [sys.homIinf_transHom_comp hmt q.fst, sys.homIinf_transHom_comp hmt q.snd, ihs]
        exact htail t'

-- this proof's elaboration needs more than the default heartbeat budget
/-- The genuine analytic core (polynomial-ring colimit descent): if a polynomial
`p ∈ R_i[S_i]` has image (under the cocone map to `R_∞[S_∞]`) lying in the
square of the colimit kernel `I = ker(R_∞[S_∞] → S_∞)`, then it already lies in the
square of the stage kernel `I_j` after pushing to some finite stage `j ≥ i`.
This is "polynomial rings commute with filtered colimits" + "filtered colimits
are exact (kernels commute)".  It is a pure statement about the polynomial-ring
maps; it does not mention `comparisonCotangent` or any bijectivity. -/
theorem kerSq_descends [IsDirected Λ (· ≤ ·)] [Nonempty Λ] (i : Λ)
    (p : (sys.NL i).Ring)
    (hp : (sys.homIinf i).toExtensionHom.toAlgHom p ∈ (sys.NLinf.ker) ^ 2) :
    ∃ (j : Λ) (h : i ≤ j),
      letI aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
      letI aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
      letI aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
      haveI tRRS : IsScalarTower (sys.R i) (sys.R j) (sys.S j) := by
        apply IsScalarTower.of_algebraMap_eq
        intro x
        change ((sys.fS h).comp (sys.g i)) x = (sys.g j) (sys.fR h x)
        simp [RingHom.comp_apply, sys.square h x]
      haveI tRSS : IsScalarTower (sys.R i) (sys.S i) (sys.S j) := by
        apply IsScalarTower.of_algebraMap_eq; intro x; rfl
      ((Generators.self (sys.R i) (sys.S i)).defaultHom
        (Generators.self (sys.R j) (sys.S j))).toExtensionHom.toAlgHom p
          ∈ (sys.NL j).ker ^ 2 := by
  classical
  -- `Φ_i p` lies in `I_∞ * I_∞`; extract a list of factor pairs.
  have extract : ∀ {A : Type _} [CommRing A] (I J : Ideal A) (x : A), x ∈ I * J →
      ∃ (L : List (A × A)), (∀ p ∈ L, p.fst ∈ I ∧ p.snd ∈ J) ∧
        x = (L.map (fun p => p.fst * p.snd)).sum := by
    intro A _ I J x hx
    refine Submodule.mul_induction_on hx
      (fun a ha b hb => ⟨[(a, b)], ?_, ?_⟩) ?_
    · intro pr hpr
      rw [List.mem_singleton] at hpr
      rw [hpr]
      exact ⟨ha, hb⟩
    · simp
    rintro x y ⟨L1, h1, rfl⟩ ⟨L2, h2, rfl⟩
    exact ⟨L1 ++ L2, fun p hp => (List.mem_append.mp hp).elim (h1 p) (h2 p), by simp⟩
  rw [sq] at hp
  obtain ⟨L, hLmem, hLsum⟩ := extract _ _ _ hp
  -- each factor lies in the colimit kernel, i.e. its evaluation vanishes
  have hLaeval : ∀ pr ∈ L,
      (MvPolynomial.aeval (R := sys.Rinf) (id : sys.Sinf → sys.Sinf)) pr.fst = 0 ∧
      (MvPolynomial.aeval (R := sys.Rinf) (id : sys.Sinf → sys.Sinf)) pr.snd = 0 := by
    intro pr hpr
    exact ⟨(hLmem pr hpr).left, (hLmem pr hpr).right⟩
  -- descend the whole list to a common stage `j₁ ≥ i`
  obtain ⟨j₁, hij₁, L', hL'mem, hL'sum⟩ := sys.descend_list i L hLaeval
  -- cocone-composition: `Φ_{j₁}(Φ_{i j₁} p) = Φ_i p = Φ_{j₁}(Σ L' products)`
  let aRRj₁ : Algebra (sys.R i) (sys.R j₁) := (sys.fR hij₁).toAlgebra
  let aSSj₁ : Algebra (sys.S i) (sys.S j₁) := (sys.fS hij₁).toAlgebra
  let aRSj₁ : Algebra (sys.R i) (sys.S j₁) := ((sys.fS hij₁).comp (sys.g i)).toAlgebra
  obtain ⟨tRRSj₁, tRSSj₁⟩ := sys.isScalarTower_transition hij₁
  set Φij₁p := ((Generators.self (sys.R i) (sys.S i)).defaultHom
    (Generators.self (sys.R j₁) (sys.S j₁))).toExtensionHom.toAlgHom p with hΦij₁p
  set sumL' := (L'.map (fun pr => pr.fst * pr.snd)).sum with hsumL'
  have hzero : (sys.homIinf j₁).toExtensionHom.toAlgHom (Φij₁p - sumL') = 0 := by
    rw [map_sub]
    rw [hΦij₁p, sys.homIinf_transHom_comp hij₁ p, hsumL', hL'sum, ← hLsum, sub_self]
  -- this difference dies at a later stage `j ≥ j₁`
  obtain ⟨j, hj₁j, hjzero⟩ := sys.polyColim_zero_exact (Φij₁p - sumL') hzero
  refine ⟨j, hij₁.trans hj₁j, ?_⟩
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR (hij₁.trans hj₁j)).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS (hij₁.trans hj₁j)).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS (hij₁.trans hj₁j)).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition (hij₁.trans hj₁j)
  -- instances for the `j₁ ≤ j` transition
  let aRRj : Algebra (sys.R j₁) (sys.R j) := (sys.fR hj₁j).toAlgebra
  let aSSj : Algebra (sys.S j₁) (sys.S j) := (sys.fS hj₁j).toAlgebra
  let aRSj : Algebra (sys.R j₁) (sys.S j) := ((sys.fS hj₁j).comp (sys.g j₁)).toAlgebra
  obtain ⟨tRRSj, tRSSj⟩ := sys.isScalarTower_transition hj₁j
  -- `hjzero` says `Φ_{j₁ j}(Φij₁p) = Φ_{j₁ j}(sumL')`
  rw [map_sub, sub_eq_zero] at hjzero
  -- `Φ_{i j} p = Φ_{j₁ j}(Φij₁p) = Φ_{j₁ j}(sumL')`
  have hgoal : ((Generators.self (sys.R i) (sys.S i)).defaultHom
      (Generators.self (sys.R j) (sys.S j))).toExtensionHom.toAlgHom p
      = ((Generators.self (sys.R j₁) (sys.S j₁)).defaultHom
        (Generators.self (sys.R j) (sys.S j))).toExtensionHom.toAlgHom sumL' := by
    rw [← hjzero, hΦij₁p, sys.transHom_trans hij₁ hj₁j p]
  rw [hgoal]
  -- now push the list to stage `j` and show the sum lies in `I_j ^ 2`
  set Ψ : (sys.NL j₁).Ring →ₐ[sys.R j₁] (sys.NL j).Ring :=
    ((Generators.self (sys.R j₁) (sys.S j₁)).defaultHom
      (Generators.self (sys.R j) (sys.S j))).toExtensionHom.toAlgHom with hΨ
  -- `Ψ` distributes the cocone map over the list sum of products
  have hΨsum : ∀ (s : List ((sys.NL j₁).Ring × (sys.NL j₁).Ring)),
      Ψ ((s.map (fun pr => pr.fst * pr.snd)).sum)
        = (s.map (fun pr => Ψ pr.fst * Ψ pr.snd)).sum := by
    intro s
    induction s with
    | nil => simp only [List.map_nil, List.sum_nil]; exact map_zero _
    | cons q s ihs =>
      simp only [List.map_cons, List.sum_cons, map_add, map_mul, ihs]
  show Ψ sumL' ∈ (sys.NL j).ker ^ 2
  rw [hsumL', hΨsum, sq]
  apply list_sum_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  -- `Ψ q.1 ∈ I_j`, `Ψ q.2 ∈ I_j`
  apply Ideal.mul_mem_mul
  · show (MvPolynomial.aeval (R := sys.R j) (id : sys.S j → sys.S j)).toRingHom (Ψ q.fst) = 0
    rw [hΨ]
    show (MvPolynomial.aeval (R := sys.R j) (id : sys.S j → sys.S j)) _ = 0
    rw [sys.aeval_transHom hj₁j q.fst, (hL'mem q hq).left, map_zero]
  · show (MvPolynomial.aeval (R := sys.R j) (id : sys.S j → sys.S j)).toRingHom (Ψ q.snd) = 0
    rw [hΨ]
    show (MvPolynomial.aeval (R := sys.R j) (id : sys.S j → sys.S j)) _ = 0
    rw [sys.aeval_transHom hj₁j q.snd, (hL'mem q hq).right, map_zero]

/-- **Kernel-colimit exactness in degree 1.** If a stage-`i` class `y : I_i/I_i²` maps to
`0` in `I/I²`, then it already dies at a finite stage `j ≥ i`, i.e. `cotMap (i≤j) y = 0`
in `I_j/I_j²`.

Lift `y` to `f_i ∈ I_i = ker (R_i[S_i] → S_i)`; the hypothesis says that the image of `f_i`
in `I = ker (R[S] → S)` lies in `I²`.  Since `R[S] = colim_λ R_λ[S_λ]` (polynomial rings
commute with filtered colimits) and `I = colim_λ I_λ` (filtered colimits are exact, so
kernels commute), the finitely many generators witnessing `f_i ∈ I²` are realized at some
stage `j ≥ i`, giving `f_j ∈ I_j²`. -/
theorem cotMapInf_eq_zero_of_stage [IsDirected Λ (· ≤ ·)] [Nonempty Λ] (i : Λ)
    (y : (sys.NL i).Cotangent) (hy : sys.cotMapInf i y = 0) :
    ∃ (j : Λ) (h : i ≤ j), sys.cotMap h y = 0 := by
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective y
  -- `hy` says the image of `x.val` under the cocone polynomial map lies in `I_∞²`.
  rw [cotMapInf_mk, Extension.Cotangent.map_mk, Extension.Cotangent.mk_eq_zero_iff] at hy
  -- Descend the membership to a finite stage `j`.
  obtain ⟨j, h, hj⟩ := sys.kerSq_descends i x.val hy
  refine ⟨j, h, ?_⟩
  -- `cotMap h (mk x) = mk ⟨homIJ.toAlgHom x.val, _⟩`, which is `0` by `mk_eq_zero_iff`.
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  show (Extension.Cotangent.map ((Generators.self (sys.R i) (sys.S i)).defaultHom
      (Generators.self (sys.R j) (sys.S j))).toExtensionHom) (Extension.Cotangent.mk x) = 0
  rw [Extension.Cotangent.map_mk, Extension.Cotangent.mk_eq_zero_iff]
  exact hj

/-- **Degree-1 injectivity of the comparison map.** Any element of `colimCotangent` is
`toColimCotangent i y` for some `i` and `y`; if `comparisonCotangent` sends it to `0` then
`cotMapInf i y = 0` in `NLinf.Cotangent = I/I²`, so by `cotMapInf_eq_zero_of_stage` the
class `y` already dies at some stage `j ≥ i`, whence `toColimCotangent i y = 0`. -/
theorem comparisonCotangent_injective [IsDirected Λ (· ≤ ·)] [Nonempty Λ] :
    Function.Injective sys.comparisonCotangent := by
  classical
  have : IsDirectedOrder Λ := inferInstance
  rw [injective_iff_map_eq_zero]
  intro z
  refine Module.DirectLimit.induction_on z (fun i y => ?_)
  intro hy
  change sys.comparisonCotangent (sys.toColimCotangent i y) = 0 at hy
  rw [comparisonCotangent_toColim] at hy
  -- The hard kernel-colimit step: `y` already dies at a finite stage `j ≥ i`.
  obtain ⟨j, h, hj⟩ := sys.cotMapInf_eq_zero_of_stage i y hy
  -- Hence `toColimCotangent i y = toColimCotangent j (cotMap h y) = 0`.
  change sys.toColimCotangent i y = 0
  rw [show sys.toColimCotangent i y = sys.toColimCotangent j (sys.cotMap h y) from
    (Module.DirectLimit.of_f (hij := h)).symm, hj, map_zero]

/-- **Degree-1 surjectivity of the comparison map.**
Every `ξ ∈ NLinf.Cotangent = I/I²` lifts to `f ∈ I = ker (R[S] → S)`, and `f` is a
polynomial with finitely many monomials, using finitely many variables `[s]` (`s ∈ S`) and
coefficients in `R`.  Since `R = colim R_λ`, `S = colim S_λ` and `R[S] = colim R_λ[S_λ]`,
`f` is the image of some `f_λ ∈ R_λ[S_λ]`, and exactness of filtered colimits gives
`f_λ ∈ I_λ`.  Then `ξ` is `cotMapInf λ` of the class of `f_λ`, i.e.
`comparisonCotangent (toColimCotangent λ [f_λ])`. -/
theorem comparisonCotangent_surjective [IsDirected Λ (· ≤ ·)] [Nonempty Λ] :
    Function.Surjective sys.comparisonCotangent := by
  classical
  intro ξ
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective ξ
  -- `x.property : x ∈ ker`, i.e. `aeval id x.val = 0`.
  have hxval : (MvPolynomial.aeval (R := sys.Rinf) (id : sys.Sinf → sys.Sinf)) x.val = 0 :=
    x.property
  -- Descend the polynomial `x.val` to a finite stage `m`, landing in the stage kernel.
  obtain ⟨m, _, ã, hãk, hãΦ⟩ := sys.descend_one (Classical.arbitrary Λ) x.val hxval
  -- Package `ã` as a stage-`m` kernel element.
  refine ⟨sys.toColimCotangent m (Extension.Cotangent.mk ⟨ã, hãk⟩), ?_⟩
  rw [comparisonCotangent_toColim, cotMapInf_mk, Extension.Cotangent.map_mk]
  -- It remains to compare the two `mk`s; their `.val`s agree by `hãΦ`.
  congr 1
  exact Subtype.ext hãΦ

/-- **Stacks Tag 07BQ, Lemma 10.134.9, degree 1.**
The canonical comparison map `colim_λ (I_λ/I_λ²) → I/I²` is a bijection (an
isomorphism of abelian groups).

A filtered-colimit computation.
Surjectivity — a class in `I/I² ⊆ R[S]/…` lifts to `f ∈ I = ker(R[S]→S)`; `f`
is a polynomial with finitely many monomials, each using finitely many variables
`[s]` and coefficients in `R`.  Since `R = colim R_λ`, `S = colim S_λ`, and `R[S]
= colim R_λ[S_λ]` (polynomial rings commute with filtered colimits), `f` is the
image of some `f_λ ∈ R_λ[S_λ]`; because filtered colimits are exact, the kernel
`I = colim I_λ`, so we may take `f_λ ∈ I_λ`.  Then `[f]` is `cotMapInf λ` of the
class of `f_λ`, hence in the image of `comparisonCotangent`.  Injectivity —
if `[f_λ]` maps to `0` in `I/I²`, then `f_λ ∈ I²` after pushing to `R[S]`;
finite generation of the relevant data and filteredness give `μ ≥ λ` with `f_μ ∈
I_μ²` already, so the class dies at stage `μ`, i.e. `toColimCotangent` of it is
`0` (`Module.DirectLimit.of.zero_exact`). -/
theorem comparisonCotangent_bijective [IsDirected Λ (· ≤ ·)] [Nonempty Λ] :
    Function.Bijective sys.comparisonCotangent := by
  -- Decompose into surjectivity and injectivity; each is a filtered-colimit fact.
  -- Formal-phase plan:
  --  * surjectivity: helper_07bq `comparisonCotangent_surjective` — every element of
  --    `NLinf.Cotangent` is `cotMapInf i` of a stage element (polynomial rings +
  --    kernels commute with filtered colimits).
  --  * injectivity: helper_07bq `comparisonCotangent_injective` — via
  --    `Module.DirectLimit.of.zero_exact` and "I_λ² captures the relation at a
  --    later stage".
  refine ⟨?_, ?_⟩
  · -- injectivity of `comparisonCotangent`
    exact sys.comparisonCotangent_injective
  · -- surjectivity of `comparisonCotangent`
    exact sys.comparisonCotangent_surjective

/-- The functoriality map of the canonical presentation morphism sends the basis vector `e_b`
of the cotangent space to `e_{algebraMap b}`. -/
private theorem cotangentSpace_map_defaultHom_basis {R S R' S' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S'] (b : S) :
    Extension.CotangentSpace.map ((Generators.self R S).defaultHom
        (Generators.self R' S')).toExtensionHom ((Generators.self R S).cotangentSpaceBasis b)
      = (Generators.self R' S').cotangentSpaceBasis (algebraMap S S' b) := by
  rw [Generators.cotangentSpaceBasis_apply]
  erw [Extension.CotangentSpace.map_tmul]
  rw [Generators.cotangentSpaceBasis_apply]
  congr 1
  · exact map_one _
  · congr 1
    show ((Generators.self R S).defaultHom (Generators.self R' S')).toAlgHom (MvPolynomial.X b)
      = MvPolynomial.X (algebraMap S S' b)
    rw [Generators.Hom.toAlgHom_X, Generators.defaultHom_val]
    show (Generators.self R' S').σ _ = MvPolynomial.X (algebraMap S S' b)
    rw [Generators.self_σ]
    rfl

-- this proof's elaboration needs more than the default heartbeat budget
/-- The cocone map `cotSpaceMapInf` sends the stage basis vector `e_b` (for `b : S i`) to
the colimit basis vector `e_{toSinf i b}`. -/
theorem cotSpaceMapInf_basis (i : Λ) (b : sys.S i) :
    sys.cotSpaceMapInf i ((Generators.self (sys.R i) (sys.S i)).cotangentSpaceBasis b)
      = (Generators.self sys.Rinf sys.Sinf).cotangentSpaceBasis (sys.toSinf i b) := by
  rw [cotSpaceMapInf]
  exact cotangentSpace_map_defaultHom_basis b

/-- Semilinearity of `cotSpaceMapInf i` over the cocone ring map `toSinf i`. -/
theorem cotSpaceMapInf_smul (i : Λ) (s : sys.S i) (x : (sys.NL i).CotangentSpace) :
    sys.cotSpaceMapInf i (s • x) = sys.toSinf i s • sys.cotSpaceMapInf i x := by
  rw [cotSpaceMapInf]
  simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe]
  rw [map_smul]
  rw [← IsScalarTower.algebraMap_smul sys.Sinf s]
  rfl

/-- `comparisonCotangentSpace` evaluated on a cocone generator is `cotSpaceMapInf`. -/
theorem comparisonCotangentSpace_toColim (i : Λ) (z : (sys.NL i).CotangentSpace) :
    sys.comparisonCotangentSpace (sys.toColimCotangentSpace i z) = sys.cotSpaceMapInf i z := by
  classical
  rw [comparisonCotangentSpace, toColimCotangentSpace, Module.DirectLimit.lift_of]

-- this proof's elaboration needs more than the default heartbeat budget
/-- The transition map `cotSpaceMap h` sends `e_b` (`b : S i`) to `e_{fS h b}`. -/
theorem cotSpaceMap_basis {i j : Λ} (h : i ≤ j) (b : sys.S i) :
    sys.cotSpaceMap h ((Generators.self (sys.R i) (sys.S i)).cotangentSpaceBasis b)
      = (Generators.self (sys.R j) (sys.S j)).cotangentSpaceBasis (sys.fS h b) := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  rw [cotSpaceMap]
  exact cotangentSpace_map_defaultHom_basis b

/-- Semilinearity of `cotSpaceMap h` over the transition ring map `fS h`. -/
theorem cotSpaceMap_smul {i j : Λ} (h : i ≤ j) (s : sys.S i) (x : (sys.NL i).CotangentSpace) :
    sys.cotSpaceMap h (s • x) = sys.fS h s • sys.cotSpaceMap h x := by
  let aRR : Algebra (sys.R i) (sys.R j) := (sys.fR h).toAlgebra
  let aSS : Algebra (sys.S i) (sys.S j) := (sys.fS h).toAlgebra
  let aRS : Algebra (sys.R i) (sys.S j) := ((sys.fS h).comp (sys.g i)).toAlgebra
  obtain ⟨tRRS, tRSS⟩ := sys.isScalarTower_transition h
  rw [cotSpaceMap]
  simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe]
  rw [map_smul]
  rw [← IsScalarTower.algebraMap_smul (sys.S j) s]
  rfl

/-- Every `t • e_c` (`t c : Sinf`) is in the range of the comparison map. -/
theorem smul_basis_mem_range [IsDirected Λ (· ≤ ·)] [Nonempty Λ] (t c : sys.Sinf) :
    t • (Generators.self sys.Rinf sys.Sinf).cotangentSpaceBasis c
      ∈ LinearMap.range sys.comparisonCotangentSpace := by
  obtain ⟨ic, bc, rfl⟩ := Ring.DirectLimit.exists_of c
  obtain ⟨it, bt, rfl⟩ := Ring.DirectLimit.exists_of t
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) ic it
  -- transport `bc` and `bt` to stage `k`
  refine ⟨sys.toColimCotangentSpace k ((sys.fS hjk bt) • (Generators.self (sys.R k) (sys.S
      k)).cotangentSpaceBasis (sys.fS hik bc)), ?_⟩
  rw [comparisonCotangentSpace_toColim, cotSpaceMapInf_smul, cotSpaceMapInf_basis]
  congr 1
  · show sys.toSinf k (sys.fS hjk bt) = sys.toSinf it bt
    exact Ring.DirectLimit.of_f hjk bt
  · congr 1
    show sys.toSinf k (sys.fS hik bc) = sys.toSinf ic bc
    exact Ring.DirectLimit.of_f hik bc

/-- A finite set of stage-`i` elements all dying in `Sinf` already dies at a common finite
stage `j ≥ i`. -/
alias fS_zero_realize := RingMapSystemUnbundled.fS_zero_realize_aux

/-- **Degree-0 injectivity of the comparison map**, i.e. the injective direction of "free
modules commute with filtered colimits".

Any `z : colimCotangentSpace` is `toColimCotangentSpace i y` for some `i` and `y`, and if
`comparisonCotangentSpace z = 0` then `cotSpaceMapInf i y = 0`.  It therefore suffices to
find `j ≥ i` with `cotSpaceMap (i≤j) y = 0`, since
`toColimCotangentSpace i y = toColimCotangentSpace j (cotSpaceMap _ y)`.

Write `y = ∑_{b∈t} f b • e_b` with `f = (cotangentSpaceBasis (self (R i) (S i))).repr y`.
The hypothesis `cotSpaceMapInf i y = 0` says that
`∑_{b∈t} toSinf i (f b) • e_{toSinf i b} = 0` in the free `Sinf`-module on `Sinf`.  By
linear independence of `cotangentSpaceBasis (self Rinf Sinf)`, grouping the finite support
`t` into the fibers of `toSinf i : S i → Sinf` gives, for each `d`, a vanishing fiber sum
`∑_{toSinf i b = d} toSinf i (f b) = 0` in `Sinf`.  Each such vanishing of a finite sum,
and each coincidence `toSinf i b = toSinf i b'`, is realized at a finite stage; since the
data is finite, directedness produces a single `j ≥ i` realizing them all.  At that `j`,
regrouping shows that `cotSpaceMap (i≤j) y = ∑_{b∈t} fS h (f b) • e_{fS h b}` collapses to
`0`. -/
theorem comparisonCotangentSpace_injective [IsDirected Λ (· ≤ ·)] [Nonempty Λ] :
    Function.Injective sys.comparisonCotangentSpace := by
  classical
  have : IsDirectedOrder Λ := inferInstance
  rw [injective_iff_map_eq_zero]
  intro z
  refine Module.DirectLimit.induction_on z (fun i y => ?_)
  intro hy
  change sys.comparisonCotangentSpace (sys.toColimCotangentSpace i y) = 0 at hy
  rw [comparisonCotangentSpace_toColim] at hy
  -- It suffices to find `j ≥ i` with `cotSpaceMap h y = 0`.
  suffices hsuff : ∃ (j : Λ) (h : i ≤ j), sys.cotSpaceMap h y = 0 by
    obtain ⟨j, h, hj⟩ := hsuff
    change sys.toColimCotangentSpace i y = 0
    rw [show sys.toColimCotangentSpace i y = sys.toColimCotangentSpace j (sys.cotSpaceMap h y) from
      (Module.DirectLimit.of_f (hij := h)).symm, hj, map_zero]
  classical
  -- Notation for the two free bases.
  set Bi := (Generators.self (sys.R i) (sys.S i)).cotangentSpaceBasis with hBi
  set Binf := (Generators.self sys.Rinf sys.Sinf).cotangentSpaceBasis with hBinf
  set f := Bi.repr y with hf
  set t := f.support with ht
  -- `y` as a finite combination of basis vectors.
  have hy_expand : y = ∑ b ∈ t, f b • Bi b := by
    conv_lhs => rw [← Bi.linearCombination_repr y]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  -- image of `cotSpaceMapInf i y` as a combination of `Binf`.
  have hmap : sys.cotSpaceMapInf i y = ∑ b ∈ t, sys.toSinf i (f b) • Binf (sys.toSinf i b) := by
    rw [hy_expand, map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [cotSpaceMapInf_smul, cotSpaceMapInf_basis]
  -- The fiber of `b` under `toSinf i`, intersected with `t`.
  set fib : sys.S i → Finset (sys.S i) :=
    fun b => t.filter (fun b'' => sys.toSinf i b'' = sys.toSinf i b) with hfibdef
  set σ : sys.S i → sys.S i := fun b => ∑ b' ∈ fib b, f b' with hσdef
  -- Fiber sums vanish in `Sinf`: this is the content of `hy`.
  have hrepr0 : Binf.repr (sys.cotSpaceMapInf i y) = 0 := by rw [hy, map_zero]
  rw [hmap, map_sum] at hrepr0
  have hreprsingle : ∀ b ∈ t, Binf.repr (sys.toSinf i (f b) • Binf (sys.toSinf i b))
      = Finsupp.single (sys.toSinf i b) (sys.toSinf i (f b)) := by
    intro b _
    rw [map_smul, Binf.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl hreprsingle] at hrepr0
  -- Evaluate the Finsupp at each colimit index to get fiber-sum vanishing.
  have hfib : ∀ b ∈ t, sys.toSinf i (σ b) = 0 := by
    intro b hb
    have hval := congrArg (fun (F : sys.Sinf →₀ sys.Sinf) => F (sys.toSinf i b)) hrepr0
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finsupp.coe_zero,
      Pi.zero_apply] at hval
    rw [hσdef, hfibdef, map_sum]
    rw [← hval]
    rw [Finset.sum_filter]
  -- Assemble the finite set of stage-`i` elements that vanish in `Sinf`.
  set xs : Finset (sys.S i) :=
    (t.image σ) ∪ (((t ×ˢ t).image (fun p => p.fst - p.snd)).filter
      (fun z => sys.toSinf i z = 0)) with hxsdef
  have hxs : ∀ x ∈ xs, sys.toSinf i x = 0 := by
    intro x hx
    rw [hxsdef, Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [Finset.mem_image] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      exact hfib b hb
    · rw [Finset.mem_filter] at hx
      exact hx.right
  obtain ⟨j, h, hall⟩ := sys.fS_zero_realize xs hxs
  -- (P3) the fiber sums die at stage `j`.
  have hP3 : ∀ b ∈ t, sys.fS h (σ b) = 0 := by
    intro b hb
    apply hall
    rw [hxsdef, Finset.mem_union]
    left
    rw [Finset.mem_image]
    exact ⟨b, hb, rfl⟩
  -- (P1) `toSinf i`-coincidences become `fS h`-coincidences at stage `j`.
  have hP1 : ∀ b ∈ t, ∀ b' ∈ t, sys.toSinf i b = sys.toSinf i b' → sys.fS h b = sys.fS h b' := by
    intro b hb b' hb' heq
    have hmem : (b - b') ∈ xs := by
      rw [hxsdef, Finset.mem_union]
      right
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_image]
        exact ⟨(b, b'), Finset.mem_product.mpr ⟨hb, hb'⟩, rfl⟩
      · rw [map_sub, heq, sub_self]
    have := hall _ hmem
    rw [map_sub, sub_eq_zero] at this
    exact this
  -- Now compute `cotSpaceMap h y` and show it is `0`.
  refine ⟨j, h, ?_⟩
  set Bj := (Generators.self (sys.R j) (sys.S j)).cotangentSpaceBasis with hBj
  have hmapj : sys.cotSpaceMap h y = ∑ b ∈ t, sys.fS h (f b) • Bj (sys.fS h b) := by
    rw [hy_expand, map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [cotSpaceMap_smul, cotSpaceMap_basis]
  rw [hmapj]
  -- regroup over fibers of `toSinf i`.
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun b => sys.toSinf i b)
    (t := t.image (fun b => sys.toSinf i b)) (fun b hb => Finset.mem_image_of_mem _ hb)]
  refine Finset.sum_eq_zero (fun d hd => ?_)
  -- inner sum over the `d`-fiber
  rw [Finset.mem_image] at hd
  obtain ⟨b₀, hb₀, hb₀d⟩ := hd
  -- the relevant fiber equals `fib b₀`
  have hfiltereq : t.filter (fun b => sys.toSinf i b = d) = fib b₀ := by
    rw [hfibdef]
    apply Finset.filter_congr
    intro b _
    rw [hb₀d]
  rw [hfiltereq]
  -- within `fib b₀`, all `Bj (fS h b)` equal `Bj (fS h b₀)`.
  have hconst : ∀ b ∈ fib b₀, sys.fS h (f b) • Bj (sys.fS h b)
      = sys.fS h (f b) • Bj (sys.fS h b₀) := by
    intro b hb
    rw [hfibdef, Finset.mem_filter] at hb
    have : sys.fS h b = sys.fS h b₀ := hP1 b hb.left b₀ hb₀ hb.right
    rw [this]
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_smul]
  have : ∑ b ∈ fib b₀, sys.fS h (f b) = sys.fS h (σ b₀) := by
    rw [hσdef, map_sum]
  rw [this, hP3 b₀ hb₀, zero_smul]

/-- **Stacks Tag 07BQ, Lemma 10.134.9, degree 0.**
The canonical comparison map `colim_λ (Ω_λ ⊗ S_λ) → Ω ⊗ S` is a bijection.

Informal proof (free-module / filtered-colimit computation): the degree-0 term
`Ω_{R[S]/R} ⊗_{R[S]} S` is the *free* `S`-module on the symbols `d[s]`, `s ∈ S`
(`Algebra.Generators.cotangentSpaceBasis` for `self R S`, indexed by `S`), and
likewise `Ω_{R_λ[S_λ]/R_λ} ⊗ S_λ` is free on `d[s_λ]`, `s_λ ∈ S_λ`.  The cocone
map `cotSpaceMapInf λ` sends the basis vector `d[s_λ]` to `d[toSinf λ s_λ]`
(`CotangentSpace.map_tmul` + `cotangentSpaceBasis_apply`).  Hence the comparison
map is the colimit of the free-module functor applied to the maps of index sets
`S_λ → S`; since `S = colim S_λ` and the free-module functor commutes with
filtered colimits, the comparison map is bijective.  Surjectivity: any
`ω ∈ Ω⊗S` is a finite `S`-combination `∑ c_b d[b]`; the finitely many `b ∈ S`
and `c_b ∈ S` all come from a single stage `λ` (filteredness of `S = colim
S_λ`), giving a preimage at stage `λ`.  Injectivity: a stage-`λ` combination
mapping to `0` has all coefficients `0` in `S`; each coefficient becomes `0` at
a later stage, and (filteredness) a common later stage `μ` kills the whole
combination, so it is `0` in the colimit (`Module.DirectLimit.of.zero_exact`). -/
theorem comparisonCotangentSpace_bijective [IsDirected Λ (· ≤ ·)] [Nonempty Λ] :
    Function.Bijective sys.comparisonCotangentSpace := by
  -- Decompose into surjectivity and injectivity. ATTACK THIS DEGREE FIRST: the
  -- free-basis structure (`Algebra.Generators.cotangentSpaceBasis`) makes the
  -- colimit computation explicit.
  -- Formal-phase plan:
  --  * surjectivity: helper_07bq `comparisonCotangentSpace_surjective` — write a
  --    target element in the basis `cotangentSpaceBasis` of `NLinf`, pull the
  --    finitely many basis indices/coefficients back to a common stage.
  --  * injectivity: helper_07bq `comparisonCotangentSpace_injective` — basis
  --    coefficients vanish, use `Module.DirectLimit.of.zero_exact`.
  refine ⟨?_, ?_⟩
  · -- injectivity of `comparisonCotangentSpace`: packaged as a named subgoal
    -- (free module commutes with filtered colimit, injective direction).
    exact sys.comparisonCotangentSpace_injective
  · -- surjectivity of `comparisonCotangentSpace`
    intro ω
    -- write ω in the basis of NLinf, as a finite Sinf-combination
    have hrange : ω ∈ LinearMap.range sys.comparisonCotangentSpace := by
      have hsum : ω = ((Generators.self sys.Rinf sys.Sinf).cotangentSpaceBasis.repr ω).sum
          (fun c t => t • (Generators.self sys.Rinf sys.Sinf).cotangentSpaceBasis c) := by
        conv_lhs => rw [← (Generators.self sys.Rinf
            sys.Sinf).cotangentSpaceBasis.linearCombination_repr ω]
        rw [Finsupp.linearCombination_apply]
      rw [hsum]
      refine Submodule.sum_mem _ (fun c _ => ?_)
      exact sys.smul_basis_mem_range _ c
    obtain ⟨z, hz⟩ := hrange
    exact ⟨z, hz⟩

/-- **Stacks Tag 07BQ, Lemma 10.134.9, chain-map compatibility.**
The degreewise comparison maps form a morphism of two-term complexes: the colimit
differential `colimDifferential` followed by the degree-0 comparison map equals the
degree-1 comparison map followed by the differential `NL_{S/R}.cotangentComplex`.
This is the global chain-map equation
`comparisonCotangentSpace ∘ colimDifferential = NLinf.cotangentComplex ∘ comparisonCotangent`
on the *colimit* (not merely on stage cocone maps). -/
theorem comparison_chain_map [Nonempty Λ] [IsDirectedOrder Λ]
    (x : sys.colimCotangent) :
    sys.comparisonCotangentSpace (sys.colimDifferential x)
      = sys.NLinf.cotangentComplex (sys.comparisonCotangent x) := by
  classical
  refine Module.DirectLimit.induction_on x (fun i y => ?_)
  -- evaluate `colimDifferential` on the cocone generator `of i y`
  have hdiff : sys.colimDifferential (sys.toColimCotangent i y)
      = sys.toColimCotangentSpace i ((sys.NL i).cotangentComplex y) := by
    rw [colimDifferential, toColimCotangent, Module.DirectLimit.lift_of]; rfl
  change sys.comparisonCotangentSpace (sys.colimDifferential (sys.toColimCotangent i y))
    = sys.NLinf.cotangentComplex (sys.comparisonCotangent (sys.toColimCotangent i y))
  rw [hdiff, comparisonCotangent_toColim, comparisonCotangentSpace_toColim,
    sys.cotMapInf_cotangentComplex i y]

/-- **Stacks Tag 07BQ, Lemma 10.134.9 (packaged).**
The canonical comparison morphism `colim_λ NL_{S_λ/R_λ} → NL_{S/R}` is an
isomorphism of two-term complexes: it is a bijection in each homological degree
(degree 1 and degree 0) and the two degreewise comparison maps commute with the
differentials (the colimit differential `colimDifferential` and the differential
`NL_{S/R}.cotangentComplex`).  This bundles the three theorems above. -/
@[stacks 07BQ]
theorem isIso_colim_NL [IsDirected Λ (· ≤ ·)] [Nonempty Λ] :
    Function.Bijective sys.comparisonCotangent ∧
    Function.Bijective sys.comparisonCotangentSpace ∧
    (∀ x : sys.colimCotangent,
      sys.comparisonCotangentSpace (sys.colimDifferential x)
        = sys.NLinf.cotangentComplex (sys.comparisonCotangent x)) :=
  ⟨sys.comparisonCotangent_bijective, sys.comparisonCotangentSpace_bijective,
    fun x => sys.comparison_chain_map x⟩

end Colimit

end RingMapSystemUnbundled

module

public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjFromSections
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Power

/-!
# The ratios `ψ(a)/ψ(f)^n`, and the chart they build

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, let `d > 0`, let `Y` be a scheme and `L` an invertible
`𝒪_Y`-module. The first step of the proof of [Stacks, Tag 01N8] takes a graded ring map
`ψ : A^{(d)} → Γ_*(Y, L)`, fixes `f ∈ 𝒜 d`, puts `s = ψ(f)`, and produces the ring map

  `ψ_{(f)} : A_{(f)} → Γ(Y_s, 𝒪_Y)`,  `a / f ^ n ↦ ψ(a) / s ^ n`,

well defined because `s` trivializes `L` over `Y_s` ([Stacks, Tag 01CY]). This file produces it,
as a `Stacks.MorphismToProj.HomogeneousRatios`, and hence the chart morphism
`Y_s ⟶ D₊(f) ⊆ U_d` of the sibling file.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`: the product of two global sections
  of tensor powers of `L`, on honest sections.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`: **the input datum `ψ`** — a
  degreewise additive family `𝒜 (n * d) →+ Γ(L ^⊗ n, ⊤)` that is multiplicative across degrees.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.pow`: the section `s ^ n`,
  *defined as* `ψ(f ^ n)`; see the implementation notes.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.ratio`: **the ratio `x / s ^ n`**
  of a global section of `L ^⊗ n` by the `n`-th power, over an open inside `Y_s`.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.homogeneousRatios`: **the family
  of homogeneous ratios `a / f ^ n ↦ ψ(a) / s ^ n`**, which is the ring map `A_{(f)} → Γ(Y_s, 𝒪_Y)`
  of the source through `Stacks.MorphismToProj.HomogeneousRatios.lift`.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.chart` and
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.toDegreeOpen`: **the chart
  morphism** `Y_s ⟶ D₊(f)`, and the same read into `U_d`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartFromRatios.nonvanishingOpen_mulSections`: `Y_{st} = Y_s ⊓ Y_t`
  on honest sections, and `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections_comm` the
  commutativity of the product up to the transport the grading forces.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.resTop_mulSections_smul_right` and
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.resTop_mulSections_smul_left`: **the ratio is
  multiplicative**, one factor at a time. These two are the whole computational content of
  `map_mul` below.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.le_nonvanishingOpen_pow`:
  **`Y_s ⊆ Y_{s^n}` for every `n`, including `n = 0`.** One open serves every degree at once.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.resTop_eq_ratio_smul`:
  **the degreewise identity `ψ(a)|_{Y_s} = (a/f^n) · (s^n)|_{Y_s}`** — clause (b) of
  [Stacks, Tag 01N8] — and
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.resTop_eq_lift_smul` the same
  with the scalar named as the value of the lifted ring map on the fraction `a/f^n`.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.ratio_res`,
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.lift_mk_res` and
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.lift_res`: **the ratios, and the
  ring map they induce, are compatible with restriction.**
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.homOfLE_chart` and
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.homOfLE_toDegreeOpen`: **the
  chart over `W` restricts to the chart over a smaller open.** This is the input the gluing step
  of [Stacks, Tag 01N8] consumes: on the overlap `Y_{ψ(f)} ⊓ Y_{ψ(f')}` both charts are the
  restrictions of the charts of `f` and of `f'`, so their agreement is an identity of ring maps
  out of `A_{(f)}`, checkable on the fractions `a / f ^ n` alone.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.preimage_basicOpen_toDegreeOpen`:
  clause (a) of [Stacks, Tag 01N8] on this one chart.

## Implementation notes

**The `Γ_*` spelling, and the bridge.** Everything here is in the *sections* spelling: a global
section of `L ^⊗ n` is an element of `Γ(L ^⊗ n, ⊤)`, as in
`Stacks.AlgebraicGeometry.MorphismsIntoProj.psiPullbackVeroneseHom` and in the uniqueness half
`StacksFrontier/AlgebraicGeometry/Constructions/ProjSectionsUniqueness.lean`. The reusable sheaf-side
facts about products of sections live in the `Stacks.GradedSections` spelling, where a section is
a morphism `𝟙 ⟶ L ^⊗ n`; `Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf` and
`Stacks.SectionProduct.globalSection` are the two directions of the carrier bridge, and
`mulSections` is the only definition that crosses it. Exactly four imported facts are used
through it: `Stacks.SectionProduct.globalSection`, `Stacks.SectionProduct.globalSection_mul`,
`Stacks.SectionProduct.nonvanishingOpen_mul` and `Stacks.GradedSections.mul_comm'`.

**`s ^ n` is `ψ(f ^ n)`, deliberately, and
`Stacks.TensorPowerTrivialize.sectionPow` is not used.** The powers of the trivializing section
are *values of `ψ`*, not iterated products formed on the sheaf side, so `powDeg`, `sectionPow`,
`trivializationPow` and `resTop_sectionPow` of
`StacksFrontier/AlgebraicGeometry/TensorPowerTrivialize/Power.lean` are all avoided. Three things
follow, and a reader tempted to reintroduce that bridge should weigh them.

* No degree transport. `sectionPow L u k` has degree `powDeg n k`, and the grading of
  `Stacks.GradedSections.mul` forces a `powCongr` wherever two such powers meet; here the degree
  of `pow ψ n` is `n` on the nose and the degree of a product is `n + m` on the nose.
* The multiplicativity `s ^ n · s ^ m = s ^ (n + m)` is an instance of `ψ`'s own multiplicativity
  (`f ^ n · f ^ m = f ^ (n + m)` in `A`), not a lemma about iterated products.
* **Degree `0` is not a special case.** `sectionPow` is indexed from the *first* power precisely
  because the zeroth would be the unit section of the section ring, and nothing in the imported
  files identifies the nonvanishing locus of that unit with all of `Y` — their own "What is not
  done" records the gap. Here `pow ψ 0 = ψ(1)` is just another value of `ψ`, and
  `le_nonvanishingOpen_pow` covers `n = 0` by the same induction as every other degree, off
  `Stacks.SectionProduct.nonvanishingOpen_mul` applied to `s = ψ(1) · s`.

**The unit axiom is not assumed.** `VeroneseSections` requires additivity in each degree and
multiplicativity across degrees, but *not* `ψ(1) = 1`. A graded ring map of course satisfies it;
it is omitted because nothing below needs it — `pow ψ 0 = ψ(1)` serves as the basis section in
degree `0` whether or not it is the unit — and leaving it out keeps the datum as weak as the
construction permits.

**The local monoidal instances.** The monoidal structure on `Y.Modules`, and hence `L ^⊗ n`
itself, is available only through the local instances of `Stacks.SheafInternalHom`; they are
reintroduced here with `attribute [local instance]`, exactly as
`StacksFrontier/AlgebraicGeometry/TensorPowerTrivialize/Power.lean` does. A downstream file that
wants to *state* anything below must do the same. The transported ring structure
`Stacks.SectionRingGeometric.gradedGlobalSectionsCommRing` is deliberately never brought into
scope: its addition is not the direct sum's own instance, which is the elaboration failure its
docstring warns about.

**`W` is a hypothesis, not `Y_s` itself.** The construction needs only an open `W` inside
`Y_{ψ(f)}`, so that is what is assumed. Taking `W = Y_{ψ(f)}` gives the source's chart; leaving it
free lets a caller use the nonvanishing open of a section of `L` rather than of `L ^⊗ 1` — the two
differ by the left unitor `𝟙 ⊗ L ≅ L`, and deferring that transport to the caller keeps it out of
every statement here.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open Stacks.SheafOfModules.TensorSheafification
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap powCongr)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowerTrivialize (resTop trivEquiv)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartFromRatios

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The product of global sections of tensor powers, on honest sections -/

section Bridge

variable {Y : Scheme.{u}} (L : Y.Modules)

/-- Restriction of global sections to an open, as an additive map. -/
def resTopHom (M : Y.Modules) (V : Y.Opens) : Γ(M, ⊤) →+ Γ(M, V) :=
  AddMonoidHom.mk' (fun x => resTop M x V) fun x y => map_add _ x y

/-- The map `resTopHom M V` sends a global section `x` to its restriction `x|_V`. -/
@[simp] theorem resTopHom_apply (M : Y.Modules) (V : Y.Opens) (x : Γ(M, ⊤)) :
    resTopHom M V x = resTop M x V := rfl

/-- A global section of a tensor power, read as a morphism out of the monoidal unit. This is the
inverse of `Stacks.SectionProduct.globalSection`, and the two are the carrier bridge between the
sections spelling used here and the `Stacks.GradedSections` spelling of the imported facts. -/
def secOf {n : ℕ} (s : Γ(natTensorPow L n, ⊤)) : powSections L n :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y (natTensorPow L n)).symm s

/-- The map `Stacks.SectionProduct.globalSection` is a left inverse of `secOf`. -/
@[simp] theorem globalSection_secOf {n : ℕ} (s : Γ(natTensorPow L n, ⊤)) :
    globalSection Y (natTensorPow L n) (secOf L s) = s :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
    (natTensorPow L n)).apply_symm_apply s

/-- The map `secOf` is a left inverse of `Stacks.SectionProduct.globalSection`. -/
@[simp] theorem secOf_globalSection {n : ℕ} (s : powSections L n) :
    secOf L (globalSection Y (natTensorPow L n) s) = s :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
    (natTensorPow L n)).symm_apply_apply s

/-- **The product of two global sections of tensor powers, on honest sections**: multiplication by
the first factor, which is a morphism of sheaves of modules and so acts on sections over every
open, applied to the second. The degree is `n + m` on the nose. -/
def mulSections {n m : ℕ} (s : Γ(natTensorPow L n, ⊤)) (t : Γ(natTensorPow L m, ⊤)) :
    Γ(natTensorPow L (n + m), ⊤) :=
  (mulMap (secOf L s) m).app ⊤ t

/-- The product on honest sections is the product of the section ring of [Stacks, Tag 01CV]. -/
theorem mulSections_globalSection {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    mulSections L (globalSection Y _ s) (globalSection Y _ t)
      = globalSection Y _ (mul s t) := by
  rw [Stacks.SectionProduct.globalSection_mul, mulSections, secOf_globalSection]

/-- **The product restricts to multiplication by the first factor**, over any open. -/
theorem resTop_mulSections {n m : ℕ} (s : Γ(natTensorPow L n, ⊤)) (t : Γ(natTensorPow L m, ⊤))
    (V : Y.Opens) :
    resTop (natTensorPow L (n + m)) (mulSections L s t) V
      = (mulMap (secOf L s) m).app V (resTop (natTensorPow L m) t V) :=
  Stacks.TensorPowerTrivialize.resTop_app _ _ _

variable [Stacks.Ample.IsInvertibleModule Y L]

/-- **`Y_{st} = Y_s ⊓ Y_t`** on honest sections: `Stacks.SectionProduct.nonvanishingOpen_mul`
through the carrier bridge. -/
theorem nonvanishingOpen_mulSections {n m : ℕ} (s : Γ(natTensorPow L n, ⊤))
    (t : Γ(natTensorPow L m, ⊤)) :
    nonvanishingOpen Y (natTensorPow L (n + m)) (mulSections L s t)
      = nonvanishingOpen Y (natTensorPow L n) s ⊓ nonvanishingOpen Y (natTensorPow L m) t := by
  have h := Stacks.SectionProduct.nonvanishingOpen_mul L n m (secOf L s) (secOf L t)
  rwa [← mulSections_globalSection, globalSection_secOf, globalSection_secOf] at h

/-- **The product of global sections of tensor powers is commutative**, up to the transport
`Stacks.GradedSections.powCongr` that the grading forces. The braiding of an invertible module
with itself is trivial (`Stacks.SectionRingGeometric.schemeHasTrivialSelfBraiding`), which is
what `Stacks.GradedSections.mul_comm'` needs. -/
theorem mulSections_comm {n m : ℕ} (s : Γ(natTensorPow L n, ⊤)) (t : Γ(natTensorPow L m, ⊤)) :
    (powCongr L (Nat.add_comm n m)).app ⊤ (mulSections L s t) = mulSections L t s := by
  rw [← globalSection_secOf L s, ← globalSection_secOf L t, mulSections_globalSection,
    mulSections_globalSection, ← Stacks.SectionProduct.globalSection_comp,
    Stacks.GradedSections.mul_comm']

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **The ratio is multiplicative in the second factor.** If the restriction of `t` is `y` times
the restriction of `u`, then the same holds for the products with a fixed `s`. One application of
`Scheme.Modules.Hom.app_smul`: multiplication by `s` is a morphism of sheaves of modules. -/
theorem resTop_mulSections_smul_right {n m : ℕ} (s : Γ(natTensorPow L n, ⊤))
    {t u : Γ(natTensorPow L m, ⊤)} {V : Y.Opens} {y : Γ(Y, V)}
    (h : resTop (natTensorPow L m) t V = y • resTop (natTensorPow L m) u V) :
    resTop (natTensorPow L (n + m)) (mulSections L s t) V
      = y • resTop (natTensorPow L (n + m)) (mulSections L s u) V := by
  rw [resTop_mulSections, resTop_mulSections, h, Scheme.Modules.Hom.app_smul]

/-- **The ratio is multiplicative in the first factor.** The companion of
`resTop_mulSections_smul_right`, obtained from it by commuting the product; this is the only place
`Stacks.GradedSections.mul_comm'` is used, and the transport it introduces is `Γ(Y, V)`-linear, so
it passes the scalar through. -/
theorem resTop_mulSections_smul_left {n m : ℕ} {s u : Γ(natTensorPow L n, ⊤)}
    (t : Γ(natTensorPow L m, ⊤)) {V : Y.Opens} {x : Γ(Y, V)}
    (h : resTop (natTensorPow L n) s V = x • resTop (natTensorPow L n) u V) :
    resTop (natTensorPow L (n + m)) (mulSections L s t) V
      = x • resTop (natTensorPow L (n + m)) (mulSections L u t) V := by
  have key : ∀ v : Γ(natTensorPow L n, ⊤),
      resTop (natTensorPow L (n + m)) (mulSections L v t) V
        = (powCongr L (Nat.add_comm m n)).app V
            (resTop (natTensorPow L (m + n)) (mulSections L t v) V) := fun v => by
    rw [← Stacks.TensorPowerTrivialize.resTop_app, mulSections_comm]
  rw [key s, key u, resTop_mulSections_smul_right L t h, Scheme.Modules.Hom.app_smul]

end Bridge

/-! ### The input datum: a degreewise multiplicative family of sections -/

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

/-- **The graded map `ψ : A^{(d)} → Γ_*(Y, L)` of [Stacks, Tag 01N8], degreewise.** For each `n` an
additive map from the degree-`nd` part of `A` to the global sections of `L ^⊗ n`, multiplicative
across degrees.

This is the Veronese grading: the degree-`n` part of `A^{(d)}` is `𝒜 (n * d)` and the degree-`n`
part of `Γ_*(Y, L)` is `Γ(L ^⊗ n, ⊤)`. The unit axiom `ψ(1) = 1` is *not* required; see the
module's implementation notes. -/
structure VeroneseSections (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {Y : Scheme.{u}}
    (L : Y.Modules) where
  /-- The degree-`n` component, a map `𝒜 (n * d) →+ Γ(L ^⊗ n, ⊤)`. -/
  toFun : ∀ n : ℕ, 𝒜 (n * d) →+ Γ(natTensorPow L n, ⊤)
  /-- Multiplicativity across degrees. -/
  map_mul : ∀ (n m : ℕ) (a : 𝒜 (n * d)) (b : 𝒜 (m * d)) (ab : 𝒜 ((n + m) * d)),
    (ab : A) = (a : A) * (b : A) → toFun (n + m) ab = mulSections L (toFun n a) (toFun m b)

namespace VeroneseSections

variable {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  (ψ : VeroneseSections 𝒜 d L) {f : A}

/-- **The `n`-th power `s ^ n` of the trivializing section `s = ψ(f)`**, defined as `ψ(f ^ n)`.
See the module's implementation notes for why it is defined this way rather than as an iterated
product on the sheaf side. -/
def pow (hf : f ∈ 𝒜 d) (n : ℕ) : Γ(natTensorPow L n, ⊤) :=
  ψ.toFun n ⟨f ^ n, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hf n⟩

/-- The value of `ψ` on any element of degree `nd` whose underlying element is `f ^ n` is the
`n`-th power. -/
theorem toFun_eq_pow (hf : f ∈ 𝒜 d) (n : ℕ) (a : 𝒜 (n * d)) (ha : (a : A) = f ^ n) :
    ψ.toFun n a = ψ.pow hf n :=
  congrArg (fun z : 𝒜 (n * d) => ψ.toFun n z) (Subtype.ext ha)

/-- **`s ^ n · s ^ m = s ^ (n + m)`**: an instance of the multiplicativity of `ψ`, because
`f ^ n · f ^ m = f ^ (n + m)` in `A`. -/
theorem mulSections_pow (hf : f ∈ 𝒜 d) (n m : ℕ) :
    mulSections L (ψ.pow hf n) (ψ.pow hf m) = ψ.pow hf (n + m) :=
  (ψ.map_mul n m _ _ _ (pow_add f n m)).symm

variable [Stacks.Ample.IsInvertibleModule Y L]

/-- **`Y_s ⊆ Y_{s^n}` for every `n`, including `n = 0`.** A power of the trivializing section is
nonvanishing wherever the section is, so a single open inside `Y_s` is inside the nonvanishing
open of every power at once. Induction off `nonvanishingOpen_mulSections`, with `n = 0` discharged
by the same step as every other degree, applied to `s = ψ(1) · s`. -/
theorem le_nonvanishingOpen_pow (hf : f ∈ 𝒜 d) (n : ℕ) :
    nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hf 1)
      ≤ nonvanishingOpen Y (natTensorPow L n) (ψ.pow hf n) := by
  induction n with
  | zero =>
      have h := nonvanishingOpen_mulSections L (ψ.pow hf 0) (ψ.pow hf 1)
      rw [ψ.mulSections_pow hf 0 1] at h
      exact h.le.trans inf_le_left
  | succ n ih =>
      have h := nonvanishingOpen_mulSections L (ψ.pow hf n) (ψ.pow hf 1)
      rw [ψ.mulSections_pow hf n 1] at h
      rw [h]
      exact le_inf ih le_rfl

/-! ### The ratio by a power of the trivializing section -/

section Ratio

variable (hf : f ∈ 𝒜 d) {W : Y.Opens}
  (hW : W ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hf 1))

include hW

/-- Every power of the trivializing section is nonvanishing on `W`. -/
theorem le_nonvanishingOpen (n : ℕ) :
    W ≤ nonvanishingOpen Y (natTensorPow L n) (ψ.pow hf n) :=
  hW.trans (ψ.le_nonvanishingOpen_pow hf n)

/-- **The ratio `x / s ^ n`** of a global section of `L ^⊗ n` by the `n`-th power of the
trivializing section, over an open `W` inside `Y_s`. This is division by a nonvanishing section,
the trivialization clause of [Stacks, Tag 01CY]. -/
def ratio (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) : Γ(Y, W) :=
  (trivEquiv (natTensorPow L n) (ψ.pow hf n)
    (ψ.le_nonvanishingOpen hf hW n)).symm (resTop (natTensorPow L n) x W)

/-- The ratio, as an additive map. -/
def ratioHom (n : ℕ) : Γ(natTensorPow L n, ⊤) →+ Γ(Y, W) :=
  ((trivEquiv (natTensorPow L n) (ψ.pow hf n)
    (ψ.le_nonvanishingOpen hf hW n)).symm.toAddMonoidHom).comp (resTopHom (natTensorPow L n) W)

/-- The map `ratioHom` sends a global section `x` of `L ^⊗ n` to the ratio `x / s ^ n`. -/
@[simp] theorem ratioHom_apply (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) :
    ψ.ratioHom hf hW n x = ψ.ratio hf hW n x := rfl

/-- **The identity that defines the ratio**: `x|_W = (x / s^n) · (s^n)|_W`. -/
theorem resTop_eq_ratio_smul (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) :
    resTop (natTensorPow L n) x W
      = ψ.ratio hf hW n x • resTop (natTensorPow L n) (ψ.pow hf n) W :=
  (Stacks.TensorPowerTrivialize.trivEquiv_symm_smul (natTensorPow L n) (ψ.pow hf n)
    (ψ.le_nonvanishingOpen hf hW n) (resTop (natTensorPow L n) x W)).symm

/-- **The ratio is the unique such scalar.** -/
theorem ratio_eq_of_resTop_eq {n : ℕ} {x : Γ(natTensorPow L n, ⊤)} {c : Γ(Y, W)}
    (h : resTop (natTensorPow L n) x W = c • resTop (natTensorPow L n) (ψ.pow hf n) W) :
    ψ.ratio hf hW n x = c := by
  rw [ratio, h]
  exact (trivEquiv (natTensorPow L n) (ψ.pow hf n)
    (ψ.le_nonvanishingOpen hf hW n)).symm_apply_apply c

/-- The ratio of a power by itself is `1`. This is what makes `map_one` and `map_den` of the
homogeneous ratios below hold. -/
@[simp] theorem ratio_pow (n : ℕ) : ψ.ratio hf hW n (ψ.pow hf n) = 1 :=
  ψ.ratio_eq_of_resTop_eq hf hW (by rw [one_smul])

/-- **The ratios are compatible with restriction.** The ratio computed over a smaller open is the
restriction of the ratio computed over `W`. This is the compatibility that makes the charts of
[Stacks, Tag 01N8] glue: on the overlap `Y_s ⊓ Y_{s'}` the two charts are built from restrictions
of one and the same family of ratios. -/
theorem ratio_res {W' : Y.Opens} (h : W' ≤ W) (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) :
    Y.presheaf.map (homOfLE h).op (ψ.ratio hf hW n x) = ψ.ratio hf (h.trans hW) n x := by
  refine (ψ.ratio_eq_of_resTop_eq hf (h.trans hW) ?_).symm
  have h0 := congrArg (fun z : Γ(natTensorPow L n, W) =>
    (natTensorPow L n).presheaf.map (homOfLE h).op z) (ψ.resTop_eq_ratio_smul hf hW n x)
  rwa [Stacks.TensorPowerTrivialize.res_resTop,
    Stacks.TensorPowerTrivialize.map_smul_resTop] at h0

/-! ### The homogeneous ratios, and the chart -/

/-- **The family of homogeneous ratios `a / f ^ n ↦ ψ(a) / s ^ n`** of [Stacks, Tag 01N8].
Through `Stacks.MorphismToProj.HomogeneousRatios.lift` this is the ring map
`ψ_{(f)} : A_{(f)} → Γ(Y_s, 𝒪_Y)` of the source, and through
`Stacks.MorphismToProj.HomogeneousRatios.chart` it is the chart morphism `Y_s ⟶ D₊(f)`.

The three conditions are the three displayed facts about ratios. `map_one` and `map_den` are
`ratio_pow`: in degrees `0` and `1` the numerator *is* the basis section, because `s ^ 0 = ψ(1)`
and `s ^ 1 = ψ(f)`. `map_mul` is `resTop_mulSections_smul_right` followed by
`resTop_mulSections_smul_left`, dividing one factor at a time, and then
`mulSections_pow`. -/
def homogeneousRatios : Stacks.MorphismToProj.HomogeneousRatios 𝒜 hf ↥Γ(Y, W) where
  toFun n := (ψ.ratioHom hf hW n).comp (ψ.toFun n)
  map_one a ha := by
    change ψ.ratio hf hW 0 (ψ.toFun 0 a) = 1
    rw [ψ.toFun_eq_pow hf 0 a (by rw [ha, pow_zero]), ratio_pow]
  map_mul n m a b ab hab := by
    change ψ.ratio hf hW (n + m) (ψ.toFun (n + m) ab)
      = ψ.ratio hf hW n (ψ.toFun n a) * ψ.ratio hf hW m (ψ.toFun m b)
    refine ψ.ratio_eq_of_resTop_eq hf hW ?_
    rw [ψ.map_mul n m a b ab hab,
      resTop_mulSections_smul_right L (ψ.toFun n a)
        (ψ.resTop_eq_ratio_smul hf hW m (ψ.toFun m b)),
      resTop_mulSections_smul_left L (ψ.pow hf m)
        (ψ.resTop_eq_ratio_smul hf hW n (ψ.toFun n a)),
      ψ.mulSections_pow hf n m, smul_smul, mul_comm]
  map_den a ha := by
    change ψ.ratio hf hW 1 (ψ.toFun 1 a) = 1
    rw [ψ.toFun_eq_pow hf 1 a (by rw [ha, pow_one]), ratio_pow]

/-- **The degreewise identity of [Stacks, Tag 01N8], clause (b)**:
`ψ(a)|_W = ψ_{(f)}(a/f^n) · (s^n)|_W`, with the scalar named as the value of the lifted ring map
on the fraction `a / f ^ n`. -/
theorem resTop_eq_lift_smul (hd : 0 < d) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) (a : 𝒜 (n * d))
    (ha : (a : A) = x) :
    resTop (natTensorPow L n) (ψ.toFun n a) W
      = (ψ.homogeneousRatios hf hW).lift hd
          (HomogeneousLocalization.Away.mk 𝒜 hf n x hx)
        • resTop (natTensorPow L n) (ψ.pow hf n) W := by
  rw [(ψ.homogeneousRatios hf hW).lift_mk hd n x hx a ha]
  exact ψ.resTop_eq_ratio_smul hf hW n (ψ.toFun n a)

/-- **The ring map `ψ_{(f)} : A_{(f)} → Γ(Y_s, 𝒪_Y)` is compatible with restriction**, on the
fractions `a / f ^ n`. Together with
`Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext` — two ring maps out of `A_{(f)}` agreeing on
every such fraction are equal — this says the ring map for a smaller open is the restriction of
the ring map for `W`, which is the algebraic half of the gluing of the charts. -/
theorem lift_mk_res (hd : 0 < d) {W' : Y.Opens} (h : W' ≤ W) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    Y.presheaf.map (homOfLE h).op
        ((ψ.homogeneousRatios hf hW).lift hd (HomogeneousLocalization.Away.mk 𝒜 hf n x hx))
      = (ψ.homogeneousRatios hf (h.trans hW)).lift hd
          (HomogeneousLocalization.Away.mk 𝒜 hf n x hx) := by
  have hxm : x ∈ 𝒜 (n * d) := by simpa [smul_eq_mul] using hx
  rw [(ψ.homogeneousRatios hf hW).lift_mk hd n x hx ⟨x, hxm⟩ rfl,
    (ψ.homogeneousRatios hf (h.trans hW)).lift_mk hd n x hx ⟨x, hxm⟩ rfl]
  exact ψ.ratio_res hf hW h n (ψ.toFun n ⟨x, hxm⟩)

/-- **The ring map for a smaller open is the restriction of the ring map for `W`**, as an
equality of ring maps out of `A_{(f)}`. `lift_mk_res` through
`Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext`. -/
theorem lift_res (hd : 0 < d) {W' : Y.Opens} (h : W' ≤ W) :
    (ψ.homogeneousRatios hf (h.trans hW)).lift hd
      = (CommRingCat.Hom.hom (Y.presheaf.map (homOfLE h).op)).comp
          ((ψ.homogeneousRatios hf hW).lift hd) :=
  Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hf fun n x hx =>
    (ψ.lift_mk_res hf hW hd h n x hx).symm

/-- **The chart morphism `W ⟶ D₊(f)`** of [Stacks, Tag 01N8]. -/
def chart (hd : 0 < d) : W.toScheme ⟶ (AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme :=
  (ψ.homogeneousRatios hf hW).chart hd

/-- **The chart morphism read into the degree-`d` open `U_d`**, which is the target the pair of
[Stacks, Tag 01N8] is indexed by. -/
def toDegreeOpen (hd : 0 < d) :
    W.toScheme ⟶ (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).toScheme :=
  (ψ.homogeneousRatios hf hW).toDegreeOpen hd

/-- **The chart agrees with the chart of a smaller open.** The charts attached to `W` and to an
open `W' ≤ W` are compatible with the inclusion, because the ratio families are (`lift_res`).
Applied with `W' = Y_{ψ(f)} ⊓ Y_{ψ(f')}`, this is what reduces the agreement of two charts on
their overlap to an identity of ring maps out of `A_{(f)}`. -/
theorem homOfLE_chart (hd : 0 < d) {W' : Y.Opens} (h : W' ≤ W) :
    Y.homOfLE h ≫ ψ.chart hf hW hd = ψ.chart hf (h.trans hW) hd := by
  rw [chart, chart, Stacks.MorphismToProj.HomogeneousRatios.chart,
    Stacks.MorphismToProj.HomogeneousRatios.chart, ← Category.assoc,
    (ψ.homogeneousRatios hf hW).homOfLE_toSpecAway hd h
      (ψ.homogeneousRatios hf (h.trans hW)) (ψ.lift_res hf hW hd h)]

/-- `homOfLE_chart` read into the degree-`d` open `U_d`. -/
theorem homOfLE_toDegreeOpen (hd : 0 < d) {W' : Y.Opens} (h : W' ≤ W) :
    Y.homOfLE h ≫ ψ.toDegreeOpen hf hW hd = ψ.toDegreeOpen hf (h.trans hW) hd := by
  rw [toDegreeOpen, toDegreeOpen, Stacks.MorphismToProj.HomogeneousRatios.toDegreeOpen,
    Stacks.MorphismToProj.HomogeneousRatios.toDegreeOpen, ← Category.assoc]
  exact congrArg (· ≫ _) (ψ.homOfLE_chart hf hW hd h)

/-- **Clause (a) of [Stacks, Tag 01N8] on this one chart**: the preimage of `D₊(f)` is all of `W`.
For the glued morphism the preimage is `Y_{ψ(f)}`, and on the chart — where `W` is that open —
this is the statement. -/
theorem preimage_basicOpen_toDegreeOpen (hd : 0 < d) :
    Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜 (ψ.toDegreeOpen hf hW hd)
        ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f = ⊤ :=
  (ψ.homogeneousRatios hf hW).preimage_basicOpen_toDegreeOpen hd

end Ratio

end VeroneseSections

end Stacks.AlgebraicGeometry.ProjChartFromRatios

end

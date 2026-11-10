module

public import Mathlib.RingTheory.Length
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.FirstInequality
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.StrictColength
public import StacksFrontier.RingTheory.Ideal.RadicalMaximalQuotient
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.ResidualFactorization
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap

/-!
# The strict first inequality of [Stacks, Tag 0AGT], up to the twist

Let `(A, 𝔪)` be a regular local ring of dimension two, `b : X ⟶ Spec A` the blowup of `Spec A`
in `𝔪`, `E` the exceptional divisor, `𝔪ⁿ ⊆ I ⊆ 𝔪` an ideal and `d` the largest integer with
`I·𝒪_X ⊆ 𝒪_X(-dE)`. The source's chain of inequalities is

`length_A(A/I) ≥ length_A Γ(X, 𝒪_X/I·𝒪_X) > length_A Γ(X, 𝒪_X(-dE)/I·𝒪_X)
  = length_A Γ(X, 𝒪_X/ℐ')`

and this file supplies everything up to the last equality: the strict inequality

`length_A(A/I) > length_A Γ(X, 𝒪_X(-dE)/I·𝒪_X)`.

## Main results

* `Stacks.Length.length_restrictScalars_ker_lt` — **a proper submodule has strictly smaller
  length, in the shape this argument needs it.** For `S` an `R`-algebra of finite length over
  `R` and `ρ : S ⟶ T` a ring map to a nontrivial ring, the kernel of `ρ`, read as an
  `R`-submodule of `S`, has length strictly smaller than `S`. It is proper because `ρ 1 = 1 ≠ 0`.
* `Stacks.Length.length_quotient_ne_top_of_pow_le` — **the finiteness.** For `R` Noetherian,
  `m` maximal and `mⁿ ⊆ I` with `n ≠ 0`, the quotient `R/I` has finite length over `R`.
* `Stacks.Divisors.mem_range_app_sumKernelMap_iff` — **what the kernel is.** For `D` an effective
  Cartier divisor and `C` with `C·D ≤ D`, a section of `𝒪_{C·D}` over the whole space comes from
  `𝒪_X(-D)|_C` exactly when it dies in `Γ(D.subscheme, 𝒪)`. So the kernel above *is* the group of
  global sections of the first term of [Stacks, Tag 0C4T].
* `Stacks.Divisors.length_ker_inclusion_lt_length_quotient` — **the strict inequality, in general
  and on variables.** For `f : X ⟶ Y` with `Y` affine, `J` an ideal of `Γ(Y, 𝒪_Y)` of finite
  colength, `D = J·𝒪_X` and any proper `E ≥ D`: if `f` and the inclusion of the subscheme cut out
  by `D` are both surjective on global functions, then the kernel of
  `Γ(D.subscheme, 𝒪) ⟶ Γ(E.subscheme, 𝒪)` has length strictly smaller than `Γ(Y, 𝒪_Y)/J`.
* `Stacks.Blowup.Colength.length_ker_inclusion_lt_length_quotient_blowUp` — **the same at the
  blowup of a regular local surface**, with the source's hypotheses and no others.

## Implementation notes

**The middle term is read as a kernel of a map of rings, not as sections of a sheaf of
modules.** `Γ(X, 𝒪_X(-dE)/I·𝒪_X)` is the first term of the sequence of [Stacks, Tag 0C4T], a
sheaf of `𝒪_X`-modules, and `AlgebraicGeometry.Scheme.Modules` is a `def`, so instance search
does not cross it: no `Module ↑Γ(Y, ⊤) ↑Γ(ℱ, ⊤)` is found for `ℱ` a sheaf of modules, at either
spelling of the ring. Left exactness of global sections identifies that term with the kernel of
the restriction `Γ(D.subscheme, 𝒪) ⟶ Γ(E.subscheme, 𝒪)`, a map of *rings* whose kernel is an
ideal, hence an `R`-submodule for any `R`-algebra structure on `Γ(D.subscheme, 𝒪)`. The
identification is `Stacks.Divisors.mem_range_app_sumKernelMap_iff`; everything else here runs on
the ring side, where `Submodule.length_lt` applies with no bookkeeping.

**Properness of the kernel is `ρ 1 = 1 ≠ 0`, not the exact sequence.** The source argues that the
image of `1` in `Γ(X, 𝒪_X/𝒪_X(-dE))` is nonzero because `d > 0`. Once the middle term is a kernel
of a ring map that is exactly `1 ∉ ker ρ`, which needs only that the target is nontrivial —
`Stacks.Divisors.nontrivial_sections_subscheme_of_ne_top` applied to `E ≠ ⊤`. The sheaf-level
statement `Stacks.Blowup.Colength.notMem_range_residualSections` says the same thing and is not
needed on this route.

**The `R`-algebra structure is the restriction of scalars already used by the non-strict half.**
`Stacks.Divisors.length_globalSections_subscheme_le_of_surjective` states its module structure as
`Module.compHom _ φ`; here the same structure is written `φ.toAlgebra`, which also supplies the
`IsScalarTower` that `Submodule.restrictScalars` wants. The two are definitionally equal —
`Module.compHom` is a reducible abbreviation whose only datum is `fun r x ↦ φ r * x` — so the two
statements compose with no bridge.

**Where each of the source's hypotheses enters.** `ringKrullDim A = 2` and regularity give the
two surjections, through
`AlgebraicGeometry.surjective_appTop_blowUpToBase_maximalIdeal` and
`Stacks.Blowup.Colength.surjective_appTop_comap_ofIdealTop_blowUp`. The containment `𝔪ⁿ ⊆ I` is
used in exactly one place, to make `A/I` Artinian and hence of finite length. The containment
`I ⊆ 𝔪` is used to produce `d > 0`, through
`Stacks.Blowup.Colength.pos_order_of_le_center`, and to rule out `n = 0`; `d > 0` with the
maximality of `d` is what makes `E ^ d` proper.

The blowup, its structure morphism and its exceptional ideal are written with their
`AlgebraicGeometry.` prefixes throughout: the enclosing namespace `Stacks.Blowup` carries a
second blowup `Stacks.Blowup.blowUp` with its own `blowUpToBase` and `exceptionalIdeal`, and
inside `Stacks.Blowup.Colength` the bare names resolve to those.

## What the source's clause (3) still waits on

One equality, `Γ(X, 𝒪_X(-dE)/I·𝒪_X) = Γ(X, 𝒪_X/ℐ')`: the invertible sheaf `𝒪_X(dE)` is trivial
on the finite set of closed points supporting the quotient. Its ingredients are
`AlgebraicGeometry.length_globalSections_eq_sum_length_stalk` and
`AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor`. Until it is
proved the attribute for clause (3)'s first inequality stays off: what is proved here bounds the
sections of `𝒪_X(-dE)/I·𝒪_X`, which the source only afterwards identifies with those of
`𝒪_X/ℐ'`.

## This inequality is not the `descent` hypothesis that Tag 0AHH consumes

Eight theorems under `StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/` carry a hypothesis
binder named `descent` (paths below are relative to `StacksFrontier/AlgebraicGeometry/`):
Tag 0AHH and Tag 0AHI at
`ResolutionOfSurfaces/QuadraticTransformations/PointBlowupChain.lean:158` and `:231`, three
consumers at `ResolutionOfSurfaces/QuadraticTransformations/FactorizationBirationalMaps.lean:146`,
`:360` and `:444`, Tag 0C5H at
`ResolutionOfSurfaces/QuadraticTransformations/DominateRationalMap.lean:99`, Tag 0BIB at
`ResolutionOfSurfaces/EmbeddedResolution/CartierAfterPointBlowups.lean:237` and Tag 0BIC at
`ResolutionOfSurfaces/EmbeddedResolution/NormalCrossingsAfterPointBlowups.lean:394`. All eight
are one proposition, named `Stacks.ResolutionOfSurfaces.PointBlowupColengthDescent`
(`ResolutionOfSurfaces/QuadraticTransformations/FactorizationBirationalMaps.lean:126`).

**That proposition is not the inequality proved here, and no respelling turns one into the
other.** It is the globalization step inside the *proof* of [Stacks, Tag 0AHH] — the step the
source writes as "(some details omitted)" — which *consumes* Tag 0AGT at the local ring
`𝒪_{Y, y}` and transports its conclusion to the blowup of an arbitrary scheme `Y` at an
arbitrary closed point. Beyond the last equality recorded in the section above, it needs:

* **A maximal `d`, which it must exhibit.** Every result in the library takes `d` together with
  `hle` and `hmax` as hypotheses: `Stacks.Blowup.Colength.pos_order_of_le_center`
  (`Blowup/Colength/PositiveOrder.lean:146`),
  `Stacks.Blowup.Colength.exists_exceptionalIdeal_pow_mul_eq_comap` (`:167`) and
  `Stacks.Blowup.Colength.length_ker_inclusion_lt_length_quotient_blowUp` below all do. No
  declaration in the tree produces the source's "largest integer `d` with `I·𝒪_X ⊆ 𝒪_X(-dE)`",
  whose upper bound `d ≤ n` comes from `𝔪ⁿ ⊆ I`.
* **The transport from `Y` to `Spec 𝒪_{Y, y}`.** `descent` quantifies over every scheme `Y` and
  compares `AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)` on `Y`
  with the blowup of `Spec 𝒪_{Y, y}` in its maximal ideal, which is the only thing this file and
  the rest of `Blowup/Colength/` speak about. That is the flat cartesian square of Tag 0AHH's
  proof, and nothing in the tree builds it: the one comap-invariance of a stalk colength is
  `colength_comap_iso`
  (`ResolutionOfSurfaces/EmbeddedResolution/CurveStrictTransform.lean:985`, private), and it
  requires `IsIso`.
* **A calculus for the measure, which does not exist.**
  `Stacks.ResolutionOfSurfaces.totalColength`
  (`ResolutionOfSurfaces/QuadraticTransformations/PointBlowupChain.lean:108`) is
  `∑ x ∈ S, length_{𝒪_{Y,x}}(𝒪_{Y,x}/J_x)` — lengths over the *stalks*, where this file's
  inequality is over `Γ(Spec A, 𝒪)`. Exactly two declarations say anything about it:
  `Stacks.ResolutionOfSurfaces.length_quotient_stalk_eq_zero_of_notMem_support`
  (`ResolutionOfSurfaces/QuadraticTransformations/PointBlowupChain.lean:115`) and the upper bound
  `Stacks.ResolutionOfSurfaces.totalColength_le_length_globalSections`
  (`ResolutionOfSurfaces/QuadraticTransformations/TotalColengthGlobalBound.lean:53`). There is
  no additivity over a `Finset`, nothing comparing the measure across a blowup, and no
  declaration anywhere whose *conclusion* is a strict inequality between two `totalColength`s.
* **`ringKrullDim ((blowUp M).presheaf.stalk z) = 2` at the points of `S'`.** The global form of
  Tag 0AGR, `AlgebraicGeometry.isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton`
  (`Blowup/RegularSurfaceBlowupGlobal.lean:326`), gives `IsRegular (blowUp M)` together with
  `topologicalKrullDim (blowUp M) = 2`. The first yields `IsRegularLocalRing` at every point; the
  second does *not* yield dimension two at a nominated closed point. This is the same gap that
  blocks the `resInherited` binder of [Stacks, Tag 0BIC].

What this file does supply, once the last equality above is in place, is the strict comparison at
the single point `y`; those four items are what stand between that and `descent`.

The four are stated relative to what this file has available. They are discharged elsewhere:
`Stacks.ResolutionOfSurfaces.CartierDescent.pointBlowupColengthDescent` is proved
unconditionally, with the transport step above as its globalization, and with it Tags 0AHH,
0BIB and 0BIC no longer need their `descent` binder. The enumeration above says what is
reachable here, not that the mathematics is open.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Length

/-- **The kernel of a ring map to a nontrivial ring is a proper submodule, so it is strictly
shorter.** Let `S` be an algebra over `R` with `S` of finite length as an `R`-module, and let
`ρ : S →+* T` be a ring map with `T` nontrivial. Then the kernel of `ρ`, viewed as an
`R`-submodule of `S`, satisfies

`length_R (ker ρ) < length_R S`.

Properness of the kernel is `ρ 1 = 1 ≠ 0`. The two instances that `Submodule.length_lt` wants are
read off the finiteness of the length through `Module.length_ne_top_iff` and
`isFiniteLength_iff_isNoetherian_isArtinian`. -/
public theorem length_restrictScalars_ker_lt {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Nontrivial T] [Algebra R S] (ρ : S →+* T) (hfin : Module.length R S ≠ ⊤) :
    Module.length R ↥((RingHom.ker ρ).restrictScalars R) < Module.length R S := by
  have hfl := isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hfin)
  let : IsNoetherian R S := hfl.1
  let : IsArtinian R S := hfl.2
  refine Submodule.length_lt ?_
  intro h
  have hmem : (1 : S) ∈ (RingHom.ker ρ).restrictScalars R := h ▸ Submodule.mem_top
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, map_one] at hmem
  exact one_ne_zero hmem

/-- **A quotient by an ideal containing a power of a maximal ideal has finite length.** For `R`
Noetherian, `m` a maximal ideal, `n ≠ 0` and `m ^ n ≤ I`,

`length_R (R/I) ≠ ⊤`.

The ring `R/m ^ n` is Artinian, so it has finite length over itself, hence over `R` because
`R ↠ R/m ^ n` is surjective, and `R/I` is a quotient of it. -/
public theorem length_quotient_ne_top_of_pow_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    (m : Ideal R) [m.IsMaximal] {n : ℕ} (hn : n ≠ 0) {I : Ideal R} (hI : m ^ n ≤ I) :
    Module.length R (R ⧸ I) ≠ ⊤ := by
  let : IsArtinianRing (R ⧸ m ^ n) := isArtinianRing_quotient_pow_of_isMaximal m hn
  have hle : Module.length R (R ⧸ I) ≤ Module.length R (R ⧸ m ^ n) :=
    Module.length_le_of_surjective ((m ^ n).liftQ I.mkQ (by rwa [Submodule.ker_mkQ]))
      fun y => (I.mkQ_surjective y).elim fun r hr => ⟨(m ^ n).mkQ r, hr⟩
  refine ne_top_of_le_ne_top ?_ hle
  rw [Module.length_eq_of_surjective (R := R ⧸ m ^ n) (S := R) (M := R ⧸ m ^ n)
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end Stacks.Length

namespace Stacks.Divisors

/-- **The global sections of `𝒪_X(-D)|_C` are the kernel of a map of rings.** For `D` an
effective Cartier divisor and `C` an ideal sheaf with `C · D ≤ D`, a global section of
`𝒪_{C·D}` lies in the image of the first map of [Stacks, Tag 0C4T] exactly when its restriction
to the subscheme cut out by `D` vanishes.

Left exactness of `Γ(X, -)` identifies the sections of the first term with the kernel of the map
to the sections of the third, and that map, over `⊤`, is the ring map of the inclusion of closed
subschemes `Scheme.IdealSheafData.inclusion`. This is what lets the strict inequality be run on
the ring side; see the module documentation. -/
public theorem mem_range_app_sumKernelMap_iff {X : Scheme.{u}} (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D) (x : Γ((C * D).subscheme, ⊤)) :
    x ∈ Set.range ((sumKernelMap D C hD).val.app (op (⊤ : X.Opens))) ↔
      (Scheme.IdealSheafData.inclusion hsub).appTop.hom x = 0 := by
  have hex := Stacks.SectionsExact.exact_app_of_shortExact X ⊤
    (shortExact_sumKernelMap_sheafOfModules D C hD hsub)
  have hbridge := Stacks.SectionsExact.modulesApp_apply
    (Scheme.IdealSheafData.closedSubschemeRestriction hsub) ⊤ x
  have e1 := Scheme.IdealSheafData.closedSubschemeRestriction_app_top hsub x
  exact (hex x).symm.trans (Iff.of_eq (congrArg (· = 0) (hbridge.symm.trans e1)))

/-- **The strict first inequality of [Stacks, Tag 0AGT] clause (3), in general and on
variables.** Let `f : X ⟶ Y` be a morphism of schemes with `Y` affine, let `J` be an ideal of
`Γ(Y, 𝒪_Y)` with `Γ(Y, 𝒪_Y)/J` of finite length, let `D = J·𝒪_X` be the inverse-image ideal
sheaf and let `E` be any *proper* ideal sheaf with `D ≤ E`. If `f` induces a surjection on global
functions and so does the inclusion of the subscheme cut out by `D`, then

`length (ker (Γ(D.subscheme, 𝒪) ⟶ Γ(E.subscheme, 𝒪))) < length (Γ(Y, 𝒪_Y)/J)`

over `Γ(Y, 𝒪_Y)`, the sections of `𝒪_{D.subscheme}` carrying the module structure restricted
along the composite ring map.

The non-strict half is
`Stacks.Divisors.length_globalSections_subscheme_le_of_surjective`; the strictness is
`Stacks.Length.length_restrictScalars_ker_lt`, whose nontriviality hypothesis is
`Stacks.Divisors.nontrivial_sections_subscheme_of_ne_top` applied to `E ≠ ⊤`.

Stated on variables `f`, `J`, `E` so that the unifier never meets a blowup written out as a
relative `Proj`. -/
public theorem length_ker_inclusion_lt_length_quotient {Y : Scheme.{u}} [IsAffine Y]
    (J : Ideal Γ(Y, ⊤)) {X : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective (f.appTop).hom)
    (hZ : Function.Surjective
      (((Scheme.IdealSheafData.ofIdealTop J).comap f).subschemeι.appTop).hom)
    {E : X.IdealSheafData}
    (hle : (Scheme.IdealSheafData.ofIdealTop J).comap f ≤ E) (hE : E ≠ ⊤)
    (hfin : Module.length ↑Γ(Y, ⊤) (↑Γ(Y, ⊤) ⧸ J) ≠ ⊤) :
    letI : Algebra ↑Γ(Y, ⊤) ↑Γ(((Scheme.IdealSheafData.ofIdealTop J).comap f).subscheme, ⊤) :=
      ((((Scheme.IdealSheafData.ofIdealTop J).comap f).subschemeι ≫ f).appTop).hom.toAlgebra
    Module.length ↑Γ(Y, ⊤)
        ↥((RingHom.ker (Scheme.IdealSheafData.inclusion hle).appTop.hom).restrictScalars
          ↑Γ(Y, ⊤)) <
      Module.length ↑Γ(Y, ⊤) (↑Γ(Y, ⊤) ⧸ J) := by
  let : Algebra ↑Γ(Y, ⊤) ↑Γ(((Scheme.IdealSheafData.ofIdealTop J).comap f).subscheme, ⊤) :=
    ((((Scheme.IdealSheafData.ofIdealTop J).comap f).subschemeι ≫ f).appTop).hom.toAlgebra
  have hmid : Module.length ↑Γ(Y, ⊤)
      ↑Γ(((Scheme.IdealSheafData.ofIdealTop J).comap f).subscheme, ⊤) ≤
      Module.length ↑Γ(Y, ⊤) (↑Γ(Y, ⊤) ⧸ J) :=
    length_globalSections_subscheme_le_of_surjective J f hf hZ
  have : Nontrivial ↑Γ(E.subscheme, ⊤) := nontrivial_sections_subscheme_of_ne_top E hE
  exact lt_of_lt_of_le
    (Stacks.Length.length_restrictScalars_ker_lt _ (ne_top_of_le_ne_top hfin hmid)) hmid

end Stacks.Divisors

namespace Stacks.Blowup.Colength

/-- **The strict first inequality of [Stacks, Tag 0AGT] clause (3), up to the twist.** Let
`(A, 𝔪)` be a regular local ring with `ringKrullDim A = 2`, let `b : X ⟶ Spec A` be the blowup
of `Spec A` in `𝔪`, let `I` be an ideal of `Γ(Spec A, 𝒪)` with `𝔪ⁿ ⊆ I ⊆ 𝔪`, and let `d` be
maximal with `I·𝒪_X ⊆ E ^ d` for `E` the exceptional ideal sheaf. Then

`length_A Γ(X, 𝒪_X(-dE)/I·𝒪_X) < length_A (A/I)`,

the left-hand side read as the kernel of the restriction
`Γ(X, 𝒪_X/I·𝒪_X) ⟶ Γ(X, 𝒪_X/𝒪_X(-dE))` — which is what it is, by
`Stacks.Divisors.mem_range_app_sumKernelMap_iff`.

Exactly the source's hypotheses: regularity and dimension two, `𝔪ⁿ ⊆ I`, `I ⊆ 𝔪`, and the
maximality of `d`. Positivity of `d` is not assumed; it is the source's own first conclusion and
is derived here from `I ⊆ 𝔪` through `Stacks.Blowup.Colength.pos_order_of_le_center`, as is
`n ≠ 0`.

This is the whole of the source's chain except its last equality
`Γ(X, 𝒪_X(-dE)/I·𝒪_X) = Γ(X, 𝒪_X/ℐ')`, which is why no attribute for the tag sits here; see the
module documentation. -/
public theorem length_ker_inclusion_lt_length_quotient_blowUp (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (I : Ideal Γ(Spec (CommRingCat.of A), ⊤)) {n : ℕ}
    (hmn : (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (IsLocalRing.maximalIdeal A)) ^ n ≤ I)
    (him : I ≤ Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (IsLocalRing.maximalIdeal A))
    (d : ℕ)
    (hle : (Scheme.IdealSheafData.ofIdealTop I).comap
        (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
            (IsLocalRing.maximalIdeal A)))) ≤
      AlgebraicGeometry.exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
          (IsLocalRing.maximalIdeal A))) ^ d)
    (hmax : ∀ e : ℕ, (Scheme.IdealSheafData.ofIdealTop I).comap
        (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
            (IsLocalRing.maximalIdeal A)))) ≤
      AlgebraicGeometry.exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
          (IsLocalRing.maximalIdeal A))) ^ e → e ≤ d) :
    letI : Algebra ↑Γ(Spec (CommRingCat.of A), ⊤)
        ↑Γ(((Scheme.IdealSheafData.ofIdealTop I).comap
          (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
            (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
              (IsLocalRing.maximalIdeal A))))).subscheme, ⊤) :=
      ((((Scheme.IdealSheafData.ofIdealTop I).comap
        (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
            (IsLocalRing.maximalIdeal A))))).subschemeι ≫
        AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
            (IsLocalRing.maximalIdeal A)))).appTop).hom.toAlgebra
    Module.length ↑Γ(Spec (CommRingCat.of A), ⊤)
        ↥((RingHom.ker (Scheme.IdealSheafData.inclusion hle).appTop.hom).restrictScalars
          ↑Γ(Spec (CommRingCat.of A), ⊤)) <
      Module.length ↑Γ(Spec (CommRingCat.of A), ⊤)
        (↑Γ(Spec (CommRingCat.of A), ⊤) ⧸ I) := by
  have : IsNoetherianRing ↑Γ(Spec (CommRingCat.of A), ⊤) :=
    isNoetherianRing_of_surjective A ↑Γ(Spec (CommRingCat.of A), ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have hmaxl : (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (IsLocalRing.maximalIdeal A)).IsMaximal :=
    (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).map_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv)
  have hn : n ≠ 0 := by
    rintro rfl
    exact hmaxl.ne_top (top_le_iff.mp (le_trans (by simpa using hmn) him))
  have hsheaf : Scheme.IdealSheafData.ofIdealTop I ≤
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        (IsLocalRing.maximalIdeal A)) :=
    Scheme.IdealSheafData.le_of_isAffine (by
      simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
      exact Ideal.map_mono him)
  have hd : 0 < d := pos_order_of_le_center _ _ d hsheaf ⟨hle, hmax⟩
  exact Stacks.Divisors.length_ker_inclusion_lt_length_quotient I _
    (AlgebraicGeometry.surjective_appTop_blowUpToBase_maximalIdeal A hdim)
    (surjective_appTop_comap_ofIdealTop_blowUp A hdim I) hle
    (ne_top_exceptionalIdeal_pow_of_maximal _ _ d hd hmax)
    (Stacks.Length.length_quotient_ne_top_of_pow_le _ hn hmn)

end Stacks.Blowup.Colength

end

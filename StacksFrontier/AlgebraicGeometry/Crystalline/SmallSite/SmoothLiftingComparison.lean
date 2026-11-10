module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PerfectnessReduction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmoothLifting
public import StacksFrontier.AlgebraicGeometry.DeRham.BaseDerivedGlobalSections
public import StacksFrontier.Homology.Perfect.Filtration
public import StacksFrontier.Homology.Perfect.StupidFiltration

/-!
# [Stacks, Tag 07MW] part (3): crystalline cohomology is the de Rham cohomology of a lifting

Remark [Stacks, Tag 07MW] fixes a prime `p`, a divided power ring `(A, I, γ)` with `p` nilpotent
in `A`, `S = Spec(A)`, `S₀ = V(I)`, a scheme `Y` smooth over `S`, and `X = Y ×_S S₀`.  It asserts
three things about a crystal `ℱ` in quasi-coherent `𝒪_{X/S}`-modules:

1. `γ` extends to the ideal of `X` in `Y`, so that `(X, Y, γ)` is an object of `Cris(X/S)`;
2. the restriction `ℱ_Y` carries a canonical integrable connection
   `∇ : ℱ_Y ⟶ ℱ_Y ⊗_{𝒪_Y} Ω_{Y/S}`;
3. `RΓ(Cris(X/S), ℱ) = RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` in `D(A)`.

Part (1) is formalized, as
`Crystalline.GlobalCrystallineSituation.smoothLiftingCrystallineThickening`
of `StacksFrontier/AlgebraicGeometry/Crystalline/SmoothLifting.lean`.  **This file states part
(3)**, as the proposition `DeRhamComparison07MW`, and reduces the perfectness remark
[Stacks, Tag 07MX] to it together with one further named proposition.

## The situation, and how it differs from the one of [Stacks, Tag 07MZ]

`Situation07MW` bundles the data and hypotheses of the remark, field for field: `S` affine, `p`
nilpotent in `A`, the scheme `Y` with its smooth structure morphism, and the cartesian square
exhibiting `X` as `Y ×_S S₀`.  These are exactly the standing hypotheses of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmoothLifting.lean`, so part (1) of the remark is
available at every `Situation07MW` and is recorded as
`Situation07MW.crystallineThickening`.

`...SmallSite.DeRhamComparison07MZ` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompleteComparisonStatements.lean` is the
same *shape* of conclusion — `RΓ(Cris(X/S), ℱ) ≅ RΓ(Y, ℱ_Y ⊗ Ω^•_{Y/S})` — but it is **not this
statement**, and neither implies the other.  Remark [Stacks, Tag 07MZ] asks for `A` Noetherian and
`p`-adically complete with `p` nilpotent only in `A/I`, for `Y` proper over `S`, and for `ℱ` of
finite type; this remark asks for `p` nilpotent in `A` itself, nothing of `A` besides, nothing of
`Y` besides smoothness, and nothing of `ℱ` besides being a crystal in quasi-coherent modules.  The
hypothesis sets cross: `p` nilpotent in `A` is stronger than `p` nilpotent in `A/I` and makes the
completeness hypothesis free, while properness, Noetherianness and finite type are hypotheses
07MW does not have.  The warning in the module documentation of `CompleteComparison.lean` about
reusing part (1) of 07MW inside `Situation07MZ` is the same observation.

What the two statements do share is the de Rham side, and it is shared *as code*: both are stated
against `AlgebraicGeometry.Scheme.Hom.derivedBaseGlobalSections` and
`AlgebraicGeometry.Scheme.Hom.ModuleWithConnection` of
`StacksFrontier/AlgebraicGeometry/DeRham/BaseDerivedGlobalSections.lean`, which is the construction
underlying `Situation07MZ`, stated for a bare morphism of schemes.

## Why `ℱ_Y` is existentially quantified

The source names `ℱ_Y`: it is the restriction of `ℱ` to the object `(X, Y, γ)` of part (1), and
part (2) says that restriction carries a canonical integrable connection.  Part (2) is **not**
stated in this library — see the "What is and is not proved" section of `SmoothLifting.lean` and
of `SmoothLiftingDifferentials.lean` — so there is no term for "the restriction of `ℱ` with its
canonical connection" to write on the right hand side.  `DeRhamComparison07MW` therefore asserts
the existence of a module with integrable connection for which the comparison holds, exactly as
`DeRhamComparison07MZ` does for the same reason.

This is weaker than the remark by precisely the identification of the witness with the
restriction, and that is the only thing it is weaker by.  Supplying part (2) would let the
existential be replaced by the named restriction without changing anything else here.

The existential is not vacuous in the trivial sense: the type it ranges over is inhabited for
every morphism of schemes, by
`AlgebraicGeometry.Scheme.Hom.structureModuleWithConnection`, the structure sheaf with its
canonical connection `∇(b) = 1 ⊗ d b`.

## What is and is not proved

Nothing here proves part (3), and **no tag attribute is placed**: `DeRhamComparison07MW` is a
proposition, and the reduction below has it as a hypothesis.  Part (3) is the conclusion of
[Stacks, Lemma 60.21.4, Tag 07LH], which this library states and does not prove — as
`...SmallSite.Computes07LH` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmoothPresentationDeRham.lean`, whose reduction to
[Stacks, Tag 07LG] is `computes07LH_of_computes07LG` — plus the globalisation of that affine
statement over `X_{Zar}`, which is also missing.

What *is* proved is a reduction of [Stacks, Tag 07MX] to part (3).  It is the source's argument
for that remark, and it takes two named propositions and one piece of data beyond 07MX's own
hypotheses:

* `Situation07MW S` itself — **a global smooth lifting `Y` of `X` over `S` must be given.**
  [Stacks, Tag 07MX] assumes `X` smooth over `S₀` and nothing more, and a smooth lifting over `S`
  of a smooth `S₀`-scheme need not exist globally; the source's own proof of 07MX therefore works
  with local liftings and descends, which is the step this reduction replaces by a hypothesis.
  This is a genuine extra input and not a restatement of 07MX.
* `DeRhamComparison07MW` — part (3) of the remark.
* `StupidFiltration07MW` — that the de Rham side carries a finite decreasing filtration with
  perfect graded pieces.  This is the stupid filtration `σ^{≥ q}` of the twisted de Rham complex:
  its graded pieces are the shifts of `RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})`, which are perfect by
  [Stacks, Tag 07VK] (1), `Stacks.AlgebraicGeometry.ProperFlatGlobalSections`
  `.isPerfect_derivedGlobalSections`, once `Y ⟶ S` is proper and the twisted forms are coherent
  and flat.  **The filtration itself is now built**, by
  `Situation07MW.stupidFiltration07MW_of_isPerfect_deRhamGradedPiece`, from two conditions on the
  *terms* of the twisted complex: that `ℱ_Y ⊗ Ω^q_{Y/S}` vanishes for `q` above some bound — the
  relative dimension of the smooth `Y ⟶ S` — and that each `RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})` is perfect,
  which is where [Stacks, Tag 07VK] (1) enters.  Neither of those is discharged here, and both
  are additions to `Situation07MW`, which asks nothing of `Y` beyond smoothness; what the
  construction removes is the filtration, not the conditions on the forms.

The conclusion is `...SmallSite.Perfect07MX` and **not** `Perfect07MY`.  07MY assumes `p`
nilpotent only in `A/I`, with `A` `p`-adically complete instead; `Situation07MW` and part (1) of
the remark both need `p` nilpotent in `A` itself, which 07MY does not supply, so this route does
not reach 07MY.  It reaches the weaker of the two remarks, and `perfect07MX_of_perfect07MY` of
`SmallSite/PerfectnessReduction.lean` runs the other way.  The source gets 07MY from 07MX by a
derived limit over the levels `A/p^eA`, [Stacks, Tag 07MV], whose tower this library does not
have.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `Situation07MW` — the data and hypotheses of Remark [Stacks, Tag 07MW].
* `Situation07MW.crystallineThickening` — part (1) of the remark at that data.
* `DeRhamComparison07MW` — **part (3) of Remark [Stacks, Tag 07MW]**.
* `Situation07MW.deRhamGlobalSectionsUnbounded` — the de Rham side as an object of `D(A)`.
* `StupidFiltration07MW` — a finite decreasing filtration of the de Rham side with perfect graded
  pieces.
* `Situation07MW.deRhamGradedPiece` — `RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})` in degree `q`, the `q`-th graded
  piece of the stupid filtration.

## Main results

* `isPerfect_deRhamGlobalSectionsUnbounded` — the de Rham side is perfect given such a
  filtration.
* `Situation07MW.isPerfect_deRhamGlobalSectionsUnbounded_of_isPerfect_deRhamGradedPiece` —
  **the stupid filtration, built**: the de Rham side is perfect once the twisted forms vanish
  in large degrees and each `RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})` is perfect.
* `Situation07MW.stupidFiltration07MW_of_isPerfect_deRhamGradedPiece` — `StupidFiltration07MW`
  from those same two conditions.
* `perfect07MX_of_deRhamComparison07MW` — **[Stacks, Tag 07MX] follows from part (3) of
  [Stacks, Tag 07MW], a global smooth lifting, and the stupid filtration.**
* `perfect07MX_of_deRhamComparison07MW_of_isPerfect_deRhamGradedPiece` — the same with the
  filtration hypothesis replaced by the two conditions on the terms of the twisted complex.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07MX](https://stacks.math.columbia.edu/tag/07MX)
* [Stacks Project, Tag 07MY](https://stacks.math.columbia.edu/tag/07MY)
* [Stacks Project, Tag 07MZ](https://stacks.math.columbia.edu/tag/07MZ)
* [Stacks Project, Tag 066R](https://stacks.math.columbia.edu/tag/066R)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The situation of [Stacks, Tag 07MW] -/

/-- **The situation of Remark [Stacks, Tag 07MW].**  On top of a global crystalline situation
`(p, (S, I, γ), X)` the remark fixes: `S = Spec(A)` affine, `p` nilpotent in `A`, a scheme `Y`
smooth over `S`, and an identification of `X` with the closed fibre `Y ×_S S₀`.

These are the standing hypotheses of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmoothLifting.lean`, so part (1) of the remark holds
at every such bundle; see `Situation07MW.crystallineThickening`.

This is a bundle of data, not an assertion, and carries no tag attribute. -/
structure Situation07MW (S : GlobalCrystallineSituation.{u}) where
  /-- `S = Spec(A)` is affine, so that `A = Γ(S, 𝒪_S)`. -/
  isAffine : IsAffine S.S.scheme
  /-- `p` is nilpotent in `A`. -/
  prime_nilpotent : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))
  /-- The scheme `Y` of the remark. -/
  Y : Scheme.{u}
  /-- The structure morphism `Y ⟶ S`. -/
  toBase : Y ⟶ S.S.scheme
  /-- `Y ⟶ S` is smooth. -/
  isSmooth : Smooth toBase
  /-- The map `X ⟶ Y` presenting `X` as the closed fibre of `Y`. -/
  toY : S.X ⟶ Y
  /-- `X = Y ×_S S₀`: the square on `X`, `Y`, `S₀` and `S` is cartesian. -/
  cartesian : IsPullback toY S.toClosedFiber toBase (DividedPowerScheme.closedFiberι S.S)

namespace Situation07MW

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)

/-- **Part (1) of Remark [Stacks, Tag 07MW] at the data of the remark**: the object `(X, Y, γ)` of
`Cris(X/S)` given by the smooth lifting.  This is
`Crystalline.GlobalCrystallineSituation.smoothLiftingCrystallineThickening` applied to the fields
of `T`; the tag sits there, not here. -/
def crystallineThickening : CrystallineThickening S :=
  have := T.isAffine
  have := T.isSmooth
  smoothLiftingCrystallineThickening S T.prime_nilpotent T.Y T.toBase T.toY T.cartesian

/-! ### Part (3) of the remark -/

variable [HasDerivedCategory.{u + 1} (ModuleSheaf S)]

/-- **Part (3) of Remark [Stacks, Tag 07MW].**  In the situation of the remark, for every crystal
`ℱ` in quasi-coherent `𝒪_{X/S}`-modules there is an `𝒪_Y`-module `ℱ_Y` with integrable connection
`∇ : ℱ_Y ⟶ ℱ_Y ⊗_{𝒪_Y} Ω_{Y/S}` such that

`RΓ(Cris(X/S), ℱ) = RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S})`

in `D(A)`.

The left hand side is `...SmallSite.moduleULiftDerivedGlobalSections`, the object of `D⁺(Mod_A)`
that [Stacks, Tag 07MX] and [Stacks, Tag 07MY] are stated about.  The right hand side is
`AlgebraicGeometry.Scheme.Hom.derivedBaseGlobalSections` of the twisted de Rham complex
`AlgebraicGeometry.Scheme.Hom.ModuleWithConnection.complex`, whose differential is constrained by
the Leibniz rule `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`; it is the twisted complex of the remark and not
an arbitrary complex with the same terms, and the connection appearing in that rule is required
to be integrable.

The coefficient hypothesis is `SheafOfModules.IsQuasicoherentOnSite` and nothing else, which
under this library's convention *is* "a crystal in quasi-coherent `𝒪_{X/S}`-modules", being
condition (1) of [Stacks, Tag 07IT].  No separate crystal hypothesis may be added alongside it,
and the remark asks no finiteness of `ℱ`, so none is asked here.

`ℱ_Y` is existentially quantified rather than named, because part (2) of the remark — the
canonical connection on the restriction of `ℱ` — is not available; the module documentation says
what that costs and what would remove it.

This is a proposition, not a theorem: nothing here proves it, and it carries no tag attribute. -/
def DeRhamComparison07MW : Prop :=
  ∀ F : _root_.SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
    ∃ M : ModuleWithConnection T.toBase,
      Nonempty (moduleULiftDerivedGlobalSections S F ≅
        derivedBaseGlobalSections T.toBase M.complex)

/-! ### The de Rham side in the unbounded derived category -/

/-- **`RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` as an object of the unbounded derived category `D(A)`**,
which is where perfectness is a condition.  The category of the inclusion is named explicitly for
the reason given in `SmallSite/PerfectnessReduction.lean`: left to instance search, the derived
category model of `ModuleCat.{u + 1} A` is found by `ModuleCat.hasDerivedCategory`, which holds
only when the module universe equals the ring universe and so is the wrong model here. -/
abbrev deRhamGlobalSectionsUnbounded (M : ModuleWithConnection T.toBase) :
    DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  (DerivedCategory.Plus.ι (C := ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))).obj
    (derivedBaseGlobalSections T.toBase M.complex)

/-- **The stupid filtration of the de Rham side, with perfect graded pieces.**  For every
`𝒪_Y`-module with integrable connection there are a finite decreasing filtration
`RΓ(Y, ℱ_Y ⊗ Ω^•_{Y/S}) = L_0 ← L_1 ← ⋯ ← L_n = 0` of the de Rham side in `D(A)` and graded
pieces `G_i` fitting into distinguished triangles `L_{i+1} ⟶ L_i ⟶ G_i ⟶ L_{i+1}⟦1⟧`, with every
`G_i` perfect.

This is the filtration the source's argument for [Stacks, Tag 07MX] uses: `L_q` is the image
under `RΓ(Y, -)` of the stupid filtration `σ^{≥ q}` of the twisted de Rham complex, so that `G_q`
is `RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})` shifted into degree `q`, and the graded pieces are perfect by
[Stacks, Tag 07VK] (1) applied to the coherent flat `𝒪_Y`-modules `ℱ_Y ⊗ Ω^q_{Y/S}` over the
proper `Y ⟶ S`.

This names the filtration and the perfectness of its graded pieces together, as the one input
`isPerfect_deRhamGlobalSectionsUnbounded` consumes.  The shape is that of
`StacksDraft.Perfect.isPerfect_of_filtration_desc`, which is where the content is used, so
nothing is assumed beyond what that lemma needs.

The filtration half is no longer open: `stupidFiltration07MW_of_isPerfect_deRhamGradedPiece`
proves this proposition from two conditions on the *terms* of the twisted complex, the vanishing
of `ℱ_Y ⊗ Ω^q_{Y/S}` in large degrees and the perfectness of each `RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})`.
Those conditions are not discharged.

This is a proposition, not a theorem, and carries no tag attribute. -/
def StupidFiltration07MW : Prop :=
  ∀ M : ModuleWithConnection T.toBase,
    ∃ (L G : ℕ → DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))) (n : ℕ),
      L 0 = T.deRhamGlobalSectionsUnbounded M ∧ IsZero (L n) ∧
        (∀ i < n, StacksDraft.Perfect.IsPerfect.{u, u + 1, u + 2} (G i)) ∧
        ∀ i < n, ∃ (a : L (i + 1) ⟶ L i) (b : L i ⟶ G i)
          (c : G i ⟶ (L (i + 1))⟦(1 : ℤ)⟧), Triangle.mk a b c ∈ distinguishedTriangles

omit [HasDerivedCategory (ModuleSheaf S)] in
/-- **The de Rham side is a perfect object of `D(A)` once it carries a finite filtration with
perfect graded pieces.**  This is [Stacks, Tag 066R] iterated,
`StacksDraft.Perfect.isPerfect_of_filtration_desc`, at the filtration
`StupidFiltration07MW` supplies. -/
theorem isPerfect_deRhamGlobalSectionsUnbounded (h : T.StupidFiltration07MW)
    (M : ModuleWithConnection T.toBase) :
    StacksDraft.Perfect.IsPerfect.{u, u + 1, u + 2} (T.deRhamGlobalSectionsUnbounded M) := by
  obtain ⟨L, G, n, hL0, hzero, hG, hT⟩ := h M
  rw [← hL0]
  exact StacksDraft.Perfect.isPerfect_of_filtration_desc L G n hzero hG hT

/-! ### The stupid filtration, built -/

section Built

open ZeroObject

attribute [local instance] AlgebraicGeometry.Scheme.Hom.wEqualsLocallyBijective
  AlgebraicGeometry.Scheme.Hom.enoughInjectives
  AlgebraicGeometry.Scheme.Hom.evaluation_additive
  AlgebraicGeometry.Scheme.Hom.baseGlobalSectionsFunctor_additive

/-- **The `q`-th graded piece of the stupid filtration of the de Rham side**:
`RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^q_{Y/S})` placed in degree `q`, as an object of `D(A)`.

This is `RΓ(Y, -)` of the single complex on the degree-`q` term of
`AlgebraicGeometry.Scheme.Hom.ModuleWithConnection.complex`, which is the twisted form
`ℱ_Y ⊗_{𝒪_Y} Ω^q_{Y/S}` by `ModuleWithConnection.complex_X`.  It is the object
[Stacks, Tag 07VK] (1) is about, once `Y ⟶ S` is proper and the form is coherent and flat. -/
abbrev deRhamGradedPiece (M : ModuleWithConnection T.toBase) (q : ℕ) :
    DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  StacksDraft.StupidFiltration.derivedSingle (baseGlobalSectionsFunctor T.toBase) (q : ℤ)
    (M.complex.X q)

omit [HasDerivedCategory (ModuleSheaf S)] in
/-- **The de Rham side is perfect once the twisted forms vanish in large degrees and each
`RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})` is perfect.**

This *is* the stupid filtration argument, carried out: `σ^{≥ q}` of the twisted de Rham complex
gives termwise split short exact sequences, hence distinguished triangles of `K⁺`, and
`RΓ(Y, -) = R(baseGlobalSectionsFunctor)` is exact, so the triangles descend to `D(A)` with the
`q`-th graded piece `RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})` in degree `q`.  Then [Stacks, Tag 066R] iterated
finishes.  All of that is
`StacksDraft.StupidFiltration.isPerfect_derivedObjNat`; here it is only instantiated.

Neither hypothesis is discharged, and both are genuine conditions on `Y ⟶ S` and on `ℱ_Y` that
`Situation07MW` does not supply:

* `hvanish` is the relative dimension bound — `Ω^q_{Y/S} = 0` for `q` above the relative
  dimension of the smooth `Y ⟶ S`.  It holds for `Y ⟶ S` smooth of bounded relative dimension
  and is false for a smooth morphism of unbounded relative dimension, so it cannot be dropped.
* `hgraded` is [Stacks, Tag 07VK] (1) at the twisted forms, which asks for `Y ⟶ S` proper and
  for `ℱ_Y ⊗ Ω^q_{Y/S}` coherent and flat.  `Situation07MW` asks nothing of `Y` beyond
  smoothness and nothing of `ℱ`, so this too is an addition and not a restatement.

What is bought is that the hypotheses now speak about the *individual terms* of the complex,
which is where [Stacks, Tag 07VK] applies, instead of about a filtration of the whole object;
`StupidFiltration07MW` bundled the two together with the filtration itself. -/
theorem isPerfect_deRhamGlobalSectionsUnbounded_of_isPerfect_deRhamGradedPiece
    (M : ModuleWithConnection T.toBase) (n : ℕ)
    (hvanish : ∀ q : ℕ, n ≤ q → IsZero (M.complex.X q))
    (hgraded : ∀ q : ℕ, q < n →
      StacksDraft.Perfect.IsPerfect.{u, u + 1, u + 2} (T.deRhamGradedPiece M q)) :
    StacksDraft.Perfect.IsPerfect.{u, u + 1, u + 2} (T.deRhamGlobalSectionsUnbounded M) :=
  StacksDraft.StupidFiltration.isPerfect_derivedObjNat
    (baseGlobalSectionsFunctor T.toBase) M.complex n hvanish hgraded

omit [HasDerivedCategory (ModuleSheaf S)] in
/-- **`StupidFiltration07MW` follows from the vanishing of the twisted forms in large degrees
together with the perfectness of each `RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})`.**

The filtration `StupidFiltration07MW` asks for is produced by
`isPerfect_deRhamGlobalSectionsUnbounded_of_isPerfect_deRhamGradedPiece`, which proves the
*stronger* statement that the de Rham side is perfect outright; the existential of
`StupidFiltration07MW` is then satisfied by the one-step filtration `X ← 0`, whose single graded
piece is `X` itself.  **The content is in the theorem above and not here**: the genuine stupid
filtration, with its graded pieces named by the terms of the complex, has already been consumed
there, and a one-step filtration carries no information (see the module documentation of
`StacksFrontier/Homology/Perfect/Filtration.lean`).  This lemma exists only so that
`perfect07MX_of_deRhamComparison07MW`, which is stated against `StupidFiltration07MW`, can be
used unchanged. -/
theorem stupidFiltration07MW_of_isPerfect_deRhamGradedPiece
    (h : ∀ M : ModuleWithConnection T.toBase, ∃ n : ℕ,
      (∀ q : ℕ, n ≤ q → IsZero (M.complex.X q)) ∧
      ∀ q : ℕ, q < n →
        StacksDraft.Perfect.IsPerfect.{u, u + 1, u + 2} (T.deRhamGradedPiece M q)) :
    T.StupidFiltration07MW := by
  intro M
  obtain ⟨n, hvanish, hgraded⟩ := h M
  have hX := T.isPerfect_deRhamGlobalSectionsUnbounded_of_isPerfect_deRhamGradedPiece M n
    hvanish hgraded
  refine ⟨fun q => match q with
      | 0 => T.deRhamGlobalSectionsUnbounded M
      | _ + 1 => 0,
    fun _ => T.deRhamGlobalSectionsUnbounded M, 1, rfl, isZero_zero _, fun i hi => ?_,
    fun i hi => ?_⟩ <;> obtain rfl : i = 0 := by omega
  exacts [hX, ⟨0, 𝟙 _, 0, contractible_distinguished₁ _⟩]

end Built

end Situation07MW

/-! ### [Stacks, Tag 07MX] from part (3) of [Stacks, Tag 07MW] -/

variable (S : GlobalCrystallineSituation.{u}) [HasDerivedCategory.{u + 1} (ModuleSheaf S)]

/-- **[Stacks, Tag 07MX] follows from part (3) of Remark [Stacks, Tag 07MW], a global smooth
lifting of `X` over `S`, and the stupid filtration of the de Rham complex.**

Given the comparison, a crystal in finite locally free quasi-coherent `𝒪_{X/S}`-modules is in
particular quasi-coherent on the site, so the comparison applies to it and identifies
`RΓ(Cris(X/S), ℱ)` with `RΓ(Y, ℱ_Y ⊗ Ω^•_{Y/S})` in `D⁺(Mod_A)`; `D⁺(Mod_A) ⟶ D(Mod_A)` carries
that to an isomorphism in `D(A)`, and the de Rham side is perfect by
`Situation07MW.isPerfect_deRhamGlobalSectionsUnbounded`.  Perfectness is invariant under
isomorphism — a bounded finite projective representative of one object is one of the other — so
the crystalline side is perfect, which is the conclusion of the remark.

**This is not a proof of [Stacks, Tag 07MX].**  Two of the three inputs are not discharged, and
the third, `Situation07MW S`, is a genuine addition to the remark's hypotheses: 07MX assumes `X`
smooth over `S₀`, and a smooth lifting of `X` over `S` need not exist globally.  Of the remark's
own hypotheses the proof uses only `S` affine and `p` nilpotent in `A`, both of which
`Situation07MW` carries; properness and smoothness of `X/S₀` enter only through
`StupidFiltration07MW`, where the perfectness of the graded pieces comes from
[Stacks, Tag 07VK] (1) over a proper `Y ⟶ S`.

The conclusion is 07MX and not 07MY; the module documentation says why this route cannot reach
07MY. -/
theorem perfect07MX_of_deRhamComparison07MW (T : Situation07MW S)
    (hcomp : T.DeRhamComparison07MW) (hfil : T.StupidFiltration07MW) : Perfect07MX S := by
  intro _ _ _ _ F hF
  obtain ⟨M, ⟨e⟩⟩ := hcomp F hF.isQuasicoherentOnSite
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨e'⟩⟩ :=
    T.isPerfect_deRhamGlobalSectionsUnbounded hfil M
  exact ⟨P, a, b, ha, hb, hfin, hproj,
    ⟨(DerivedCategory.Plus.ι (C := ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))).mapIso e ≪≫ e'⟩⟩

section Built

attribute [local instance] AlgebraicGeometry.Scheme.Hom.wEqualsLocallyBijective
  AlgebraicGeometry.Scheme.Hom.enoughInjectives
  AlgebraicGeometry.Scheme.Hom.evaluation_additive
  AlgebraicGeometry.Scheme.Hom.baseGlobalSectionsFunctor_additive

/-- **[Stacks, Tag 07MX] follows from part (3) of Remark [Stacks, Tag 07MW], a global smooth
lifting of `X` over `S`, the vanishing of the twisted forms `ℱ_Y ⊗ Ω^q_{Y/S}` in large degrees,
and the perfectness of each `RΓ(Y, ℱ_Y ⊗ Ω^q_{Y/S})`.**

This is `perfect07MX_of_deRhamComparison07MW` with its filtration hypothesis discharged: the
stupid filtration is now constructed rather than assumed, by
`Situation07MW.isPerfect_deRhamGlobalSectionsUnbounded_of_isPerfect_deRhamGradedPiece`.  What is
left of that hypothesis is the two conditions on the terms of the twisted de Rham complex — the
relative dimension bound and [Stacks, Tag 07VK] (1) at the twisted forms — and those are stated
about the terms, where they can be checked, and not about the filtration.

**This is still not a proof of [Stacks, Tag 07MX]**, and no tag attribute is placed: `hcomp` is
part (3) of the remark, which this library does not prove, `hgraded` is not discharged, and
`Situation07MW S` is a genuine addition to the remark's hypotheses for the reason given in
`perfect07MX_of_deRhamComparison07MW`. -/
theorem perfect07MX_of_deRhamComparison07MW_of_isPerfect_deRhamGradedPiece (T : Situation07MW S)
    (hcomp : T.DeRhamComparison07MW)
    (hgraded : ∀ M : ModuleWithConnection T.toBase, ∃ n : ℕ,
      (∀ q : ℕ, n ≤ q → IsZero (M.complex.X q)) ∧
      ∀ q : ℕ, q < n →
        StacksDraft.Perfect.IsPerfect.{u, u + 1, u + 2} (T.deRhamGradedPiece M q)) :
    Perfect07MX S :=
  perfect07MX_of_deRhamComparison07MW S T hcomp
    (T.stupidFiltration07MW_of_isPerfect_deRhamGradedPiece hgraded)

end Built

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

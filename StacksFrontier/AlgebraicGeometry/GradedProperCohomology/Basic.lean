module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleTwistVanishing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a graded module over a graded algebra, along a proper morphism

[Stacks, Tag 0897] says: let `A` be a Noetherian ring, `B` a finitely generated graded
`A`-algebra, `f : X ⟶ Spec A` a proper morphism, and set `𝓑 = f^* B̃`. Let `F` be a
quasi-coherent graded `𝓑`-module of finite type. Then

1. for every `p ≥ 0` the graded `B`-module `H^p(X, F) = ⨁ₙ H^p(X, Fₙ)` is a finite
   `B`-module, and
2. if `L` is an ample invertible `𝒪_X`-module there is a `d₀` with
   `H^p(X, F ⊗ L^{⊗d}) = 0` for all `p > 0` and all `d ≥ d₀` — one `d₀` serving every
   degree `p` **and** every graded degree `n` at once.

Both parts are proved in the source by the *same* base change. Put
`X' = Spec(B) ×_{Spec(A)} X`, with its two projections `π : X' ⟶ X` and `f' : X' ⟶ Spec B`.
Then `f'` is proper ([Stacks, Tag 01W4]), `B` is Noetherian (Hilbert basis), `X'` is the
relative spectrum of `𝓑` over `X` ([Stacks, Tag 01LX]) so `π` is affine, and `F`
corresponds to a single coherent `𝒪_{X'}`-module `F'` with `π_* F' = F`
([Stacks, Tag 01SB] and [Stacks, Tag 01XZ]). Because `π` is affine,
`H^p(X, F) = H^p(X', F')` by [Stacks, Tag 089W], and part (1) is [Stacks, Tag 02O6] for
`f'`; with `L' = π^* L`, ample by [Stacks, Tag 0892], the projection formula
([Stacks, Tag 01E8]) gives `π_*(F' ⊗ L') = F ⊗ L` and part (2) is [Stacks, Tag 02O1]
for `f'`.

**This file carries the vocabulary of both parts and the implication that reads off part (2)
from that base change, and takes the base change itself as named hypotheses**, so `X'`, `f'`,
`F'` and `L'` are binders and the comparison with the cohomology upstairs is a hypothesis.

*Do not read that as a claim that the ingredients are absent from the library* — an earlier
version of this note said that none of [Stacks, Tag 01LX], [Stacks, Tag 01SB] or
[Stacks, Tag 01W4] was available, and that is false. All three are:

* [Stacks, Tag 01LX], the relative spectrum of a quasi-coherent algebra sheaf with its affine
  structure morphism and `π_* 𝒪 ≅ 𝒜`, is
  `Stacks.AffineAlgebraEquivalence.relativeSpec`, `relativeSpecToBase`,
  `isAffineHom_relativeSpecToBase` and `pushforwardAlgebraIso`, repackaged over the base as
  `Stacks.AlgebraicGeometry.FiniteTypeDominating.relativeSpecOver` and `relativeSpecOverIso`;
  its base change `Spec_S(𝒜) ×_S T ≅ Spec_T(g^* 𝒜)` is
  `Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`. For the Rees algebra of
  `ℐ = I · 𝒪_X` the relative spectrum is built in
  `StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesBaseChange` as
  `Stacks.Cohomology.FormalFunctions.reesRelativeSpec`.
* [Stacks, Tag 01SB], the equivalence between quasi-coherent `𝒪_{X'}`-modules and
  quasi-coherent `π_* 𝒪_{X'}`-modules for an affine `π`, is
  `Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward`.
* [Stacks, Tag 01W4], properness under base change, is Mathlib's
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange`, with the two pullback legs available as
  instances.

What is genuinely missing, and is why the base change is still a binder here, is the *ungraded*
realization of a `SheafOfModules.GradedModule` as a module over the ungraded realization of its
graded algebra: without it the graded module `F` cannot be turned into the single module `F'` on
`X'` that [Stacks, Tag 01SB] would transport. The companion gap list is in the implementation
notes of `StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesBaseChange`.

Part (1)
is `moduleFinite_gradedCohomologySum` in
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness`, which is
where it can be stated with [Stacks, Tag 02O6] *proved* rather than assumed. What is *not*
assumed is the cohomological content:

* part (1) uses [Stacks, Tag 02O6] — the finiteness of `H^i(X, F)` over a Noetherian ring for
  a proper morphism — which is stated here as the proposition `Tag02O6`, exactly as the source
  states that tag (over a ring, not over an affine scheme), and *proved* as `tag02O6` in
  `StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness`;
* part (2) uses [Stacks, Tag 02O1], which *is* carried, as
  `exists_isZero_rightDerivedPlus_pushforward_tensorPowModule` in the namespace
  `Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing`,
  itself granted its single hypothesis `VanishingOverAffineBase`; and it uses
  [Stacks, Tag 01XK], which is carried unconditionally, to turn the vanishing of
  `R^p f'_* (F' ⊗ L'^{⊗d})` into the vanishing of `H^p(X', F' ⊗ L'^{⊗d})`. Ampleness of
  `L' = π^* L` is not assumed either: it is derived from the source's own ampleness of `L` by
  [Stacks, Tag 0892] part (2) for the affine `π` and [Stacks, Tag 01VK] for the affine base.
  So the only hypothesis part (2) adds beyond the base change is `VanishingOverAffineBase`,
  which is [Stacks, Tag 02O1]'s own.

The vocabulary is the library's throughout and nothing is defined in parallel: graded
algebras and graded modules on a scheme are `SheafOfModules.GradedAlgebra` and
`SheafOfModules.GradedModule` ([Stacks, Tag 0FQW] and [Stacks, Tag 0FQZ]), finite type for a
graded module in part (2) is `Stacks.Coherent.IsFiniteTypeOnAffine` — the very predicate
[Stacks, Tag 087Z] (`Stacks.Coherent.finiteTypeAssociatedGradedData`) produces — and the
twists are `Stacks.RelativeVeryAmple.tensorModules` of `Stacks.Ample.tensorPowModule`.

## Main definitions

* `cohomologyOf X p N` is `H^p(X, N)` as a module over `Γ(X, ⊤)`.
* `specAlgebraRingHom R g` is the ring map `R →+* Γ(Y, ⊤)` attached to `g : Y ⟶ Spec R`,
  through which `H^p(Y, −)` is a module over the base ring.
* `Tag02O6` is [Stacks, Tag 02O6] as a proposition.
* `pieceModule F n` is the degree-`n` homogeneous piece `Fₙ` read as an `𝒪_X`-module, and
  `pieceTwist F L n d` is its twist `Fₙ ⊗ L^{⊗d}`.
* `gradedCohomologySum F p` is the graded cohomology `⨁ₙ H^p(X, Fₙ)` of [Stacks, Tag 0897]
  part (1).

## Main results

* `exists_isZero_pieceTwistCohomology` — **[Stacks, Tag 0897] part (2)**, granted the base
  change and [Stacks, Tag 02O1]'s hypothesis `VanishingOverAffineBase`.

## Implementation notes

The graded `B`-module structure on `⨁ₙ H^p(X, Fₙ)` is an instance binder of part (1) rather
than a construction: it is the action induced by the graded action of `𝓑` on `F`, which
exists only once `𝓑` is known to be `f^* B̃`, and that identification is precisely what the
base change supplies. The hypothesis `cmp` pins that action down to the extent the source's
proof does — it makes the comparison with `H^p(X', F')` `B`-linear — and nothing weaker than
a `B`-linear comparison could carry finiteness across.

The source's own hypotheses are all kept, so that the statements are the tag's: `A`
Noetherian, `B` a finitely generated graded `A`-algebra, `f` proper, the pieces of `F`
quasi-coherent and `F` of finite type. Two of them are inert in these particular
implications and are named `_hqc` and `_hft` for that reason: quasi-coherence and finite
type of `F` enter the source's argument only in producing `F'` and its coherence, which here
are binders. `f` and its properness are likewise used only through the base change. They are
retained because dropping them would state something other than [Stacks, Tag 0897].

Cohomology is `Functor.rightDerived` of `Stacks.Cohomology.AffineBase.moduleGlobalSections`,
the `ℕ`-indexed spelling used by the neighbouring chapter-30 and formal-geometry modules;
[Stacks, Tag 01XK] and [Stacks, Tag 02O1] are both stated with `rightDerivedPlus` over `ℤ`,
and `Stacks.DerivedIndexing.rightDerivedIso` passes between the two.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Cohomology, and the base ring it is a module over -/

/-- `H^p(X, N)` for an `𝒪_X`-module `N`, as a module over the ring `Γ(X, ⊤)` of global
functions. -/
abbrev cohomologyOf (X : Scheme.{u}) (p : ℕ) (N : X.Modules) : ModuleCat.{u} Γ(X, ⊤) :=
  ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj N

/-- The ring homomorphism `R →+* Γ(Y, ⊤)` attached to a morphism `g : Y ⟶ Spec R`: the
global functions of `Spec R` identified with `R`, pushed forward along `g`. Restriction of
scalars along it is how `H^p(Y, −)` is read as a module over the base ring. -/
abbrev specAlgebraRingHom (R : Type u) [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of R)) : R →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop).hom

/-- **[Stacks, Tag 02O6]** as a proposition, in the shape the source states it: for a proper
morphism `g : Y ⟶ Spec R` with `R` Noetherian and a coherent `𝒪_Y`-module `G`, the
cohomology `H^i(Y, G)` is a finite `R`-module in every degree.

No declaration in this library carries this, so it appears as a hypothesis. The equivalent
scheme-indexed shape is the hypothesis `h02O6` of
`Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_rightDerived_of_moduleFinite_cohomology`;
the ring-indexed shape is used here because the conclusion of [Stacks, Tag 0897] part (1) is
finiteness over the ring `B` itself. -/
def Tag02O6 : Prop :=
  ∀ (R : Type u) [CommRing R], IsNoetherianRing R →
    ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of R)), IsProper g →
      ∀ G : Y.Modules, _root_.SheafOfModules.IsCoherent G → ∀ i : ℕ,
        Module.Finite R
          ↥((ModuleCat.restrictScalars (specAlgebraRingHom R g)).obj (cohomologyOf Y i G))

/-! ### The homogeneous pieces of a graded module, and their twists -/

variable {X : Scheme.{u}}
  {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- The degree-`n` homogeneous piece `Fₙ` of a graded module, read as an `𝒪_X`-module. -/
abbrev pieceModule (F : _root_.SheafOfModules.GradedModule 𝓑) (n : ℤ) : X.Modules :=
  F.piece n

/-- The twist `Fₙ ⊗ L^{⊗d}` of the degree-`n` homogeneous piece of a graded module by a
tensor power of an invertible `𝒪_X`-module. -/
abbrev pieceTwist (F : _root_.SheafOfModules.GradedModule 𝓑) (L : X.Modules)
    [IsInvertibleModule X L] (n d : ℤ) : X.Modules :=
  tensorModules X (pieceModule F n) (tensorPowModule X L d)

/-- The graded cohomology `H^p(X, F) = ⨁ₙ H^p(X, Fₙ)` of a graded module: the object whose
finiteness is [Stacks, Tag 0897] part (1). -/
abbrev gradedCohomologySum (F : _root_.SheafOfModules.GradedModule 𝓑) (p : ℕ) : Type u :=
  DirectSum ℤ fun n : ℤ => ↥(cohomologyOf X p (pieceModule F n))

/-! ### Part (2): vanishing of the higher cohomology of the twists -/

/-- **[Stacks, Tag 0897] part (2), granted the base change and [Stacks, Tag 02O1]'s own
hypothesis.** Let `A` be a Noetherian ring, `B` a finitely generated graded `A`-algebra,
`f : X ⟶ Spec A` proper, `F` a quasi-coherent graded `𝓑`-module of finite type and `L` an
invertible `𝒪_X`-module. Then there is a `d₀` such that

`H^p(X, Fₙ ⊗ L^{⊗d}) = 0` for every `p > 0`, every `d ≥ d₀` and **every** graded degree `n`,

the uniformity in `n` being the whole point: it is what [Stacks, Tag 0884] consumes.

The hypotheses beyond the source's are the base change of the source's proof —
`f' : X' ⟶ Spec B` proper, the affine projection `π : X' ⟶ X`, a coherent `F'` on `X'`, and
the comparison `hcmp` of the vanishing of `H^p(X', F' ⊗ (π^* L)^{⊗d})` with that of every
`H^p(X, Fₙ ⊗ L^{⊗d})`, which is [Stacks, Tag 089W] along `π` together with the projection
formula [Stacks, Tag 01E8] — plus `hvan`, which is [Stacks, Tag 02O1]'s own hypothesis and
not an extra one. Ampleness is *not* assumed upstairs: the source's own `hL : IsAmple X L`
is used, and `π^* L` is ample on `X'` because `π` is affine ([Stacks, Tag 0892] part (2),
`Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`), hence ample relative to `f'`
because `Spec B` is affine ([Stacks, Tag 01VK],
`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`).

The uniformity in `n` is not assumed and is not smuggled in by `hcmp`: `hcmp` turns *one*
vanishing statement upstairs into the vanishing of *all* the graded pieces downstairs,
exactly as the single coherent sheaf `F'` on `X'` accounts for the whole graded module `F`.
What is proved here is that the bound `d₀` exists at all: [Stacks, Tag 02O1] applied to
`f'`, `F'` and `π^* L` gives a `d₀` above which `R^p f'_*(F' ⊗ (π^* L)^{⊗d})` vanishes for
every `p > 0`, [Stacks, Tag 01XK] turns that into the vanishing of
`H^p(X', F' ⊗ (π^* L)^{⊗d})` — `Spec B` is affine and `f'`, being proper, is quasi-compact
and quasi-separated — and `hcmp` transports it to `X`. -/
@[stacks 0897 "part (2), with the base change X' = Spec(B) ×_Spec(A) X and the comparison of \
the vanishing of H^p(X', F' tensor (pi^* L)^d) with that of the H^p(X, F_n tensor L^d) \
(089W, 01E8) as hypotheses; 02O1 enters through its own hypothesis VanishingOverAffineBase, \
and ampleness of pi^* L is derived from that of L by 0892 and 01VK"]
theorem exists_isZero_pieceTwistCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule 𝓑)
    (_hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (_hft : Stacks.Coherent.IsFiniteTypeOnAffine F)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    (hvan : Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase.{u})
    {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of B)) [IsProper f']
    (π : X' ⟶ X) [_root_.AlgebraicGeometry.IsAffineHom π]
    (F' : X'.Modules) [F'.IsCoherent]
    (hcmp : ∀ p d : ℕ,
      IsZero ((ModuleCat.restrictScalars f'.appTop.hom).obj
          (cohomologyOf X' p
            (tensorModules X' F'
              (tensorPowModule X' (Stacks.AmpleLocallyClosed.pullbackModule π L) (d : ℤ))))) →
        ∀ n : ℤ, IsZero (cohomologyOf X p (pieceTwist F L n (d : ℤ)))) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (cohomologyOf X p (pieceTwist F L n (d : ℤ))) := by
  have hBN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hSN : _root_.AlgebraicGeometry.IsNoetherian (Spec (.of B)) :=
    _root_.AlgebraicGeometry.isNoetherian_Spec.mpr hBN
  -- `π^* L` is ample on `X'` because `π` is affine, hence ample relative to `f'` because
  -- the base `Spec B` is affine.
  have hL' : Stacks.RelativeAmple.IsRelativelyAmple f'
      (Stacks.AmpleLocallyClosed.pullbackModule π L) :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f' _).mpr
      (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom π L hL)
  obtain ⟨d₀, hd₀⟩ :=
    RelativeAmpleTwistVanishing.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
      hvan f' F' (Stacks.AmpleLocallyClosed.pullbackModule π L) hL'
  refine ⟨d₀, fun d hd p hp => hcmp p d ?_⟩
  -- The twist upstairs, and its quasi-coherence.
  have hGqc :
      (tensorModules X' F' (tensorPowModule X'
        (Stacks.AmpleLocallyClosed.pullbackModule π L) (d : ℤ))).IsQuasicoherent :=
    RelativeAmpleTwistVanishing.isQuasicoherent_tensorPowTwist F' _ (d : ℤ)
  -- [Stacks, Tag 02O1]: the higher direct image vanishes.
  have hz :
      IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus (p : ℤ)).obj
        (tensorModules X' F' (tensorPowModule X'
          (Stacks.AmpleLocallyClosed.pullbackModule π L) (d : ℤ)))) := hd₀ d p hd hp
  -- Its global sections on the affine base vanish with it.
  have hz0 :
      IsZero ((Stacks.Cohomology.AffineBase.moduleGlobalSections (Spec (.of B))).obj
        (((Scheme.Modules.pushforward f').rightDerivedPlus (p : ℤ)).obj
          (tensorModules X' F' (tensorPowModule X'
            (Stacks.AmpleLocallyClosed.pullbackModule π L) (d : ℤ))))) :=
    Functor.map_isZero _ hz
  -- [Stacks, Tag 01XK]: those global sections are the cohomology upstairs.
  have hz1 :
      IsZero ((ModuleCat.restrictScalars f'.appTop.hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections X').rightDerivedPlus
          (p : ℤ)).obj (tensorModules X' F' (tensorPowModule X'
            (Stacks.AmpleLocallyClosed.pullbackModule π L) (d : ℤ))))) :=
    hz0.of_iso
      ((Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward f'
        (p : ℤ)).app ⟨_, hGqc⟩)
  -- Passing from the `ℤ`-indexed to the `ℕ`-indexed derived functor.
  exact hz1.of_iso
    ((ModuleCat.restrictScalars f'.appTop.hom).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Stacks.Cohomology.AffineBase.moduleGlobalSections X') p).app _))

end Stacks.AlgebraicGeometry.GradedProperCohomology

end

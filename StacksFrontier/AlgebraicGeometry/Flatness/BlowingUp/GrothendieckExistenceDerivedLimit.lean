module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceSituation
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.DerivedLimitBounded
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QuasiCoherentAffineAmplitude

/-!
# The derived limit of a compatible system of flat modules is bounded, in degrees at least zero

In Situation [Stacks, Tag 0CTC] the sheaves `Fₙ` on the closed subschemes `Xₙ ⊆ X` are pushed
forward to `X` along the closed immersions `iₙ : Xₙ → X` and assembled into an inverse system of
`𝒪_X`-modules. Writing `K` for a derived limit of that system in `D(𝒪_X)`, the content of
[Stacks, Tag 0CTD] is that

* `DQ_X(K)` is a derived limit of the system `(iₙ,* Fₙ)` in `D_QCoh(𝒪_X)`, which is the displayed
  equality `R lim_{D_QCoh(𝒪_X)}(Fₙ) = DQ_X(R lim_{D(𝒪_X)} Fₙ)` of the source; and
* `DQ_X(K)` lies in `D^b_QCoh(𝒪_X)` with nonzero cohomology sheaves only in degrees `≥ 0`.

## Main definitions and results

* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.pushforwardTransition` — the
  transition map `iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ` of the pushed-forward system, built from the comparison
  isomorphism `φₙ` of the situation.
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.pushforwardSystem` — that system as
  a functor `ℕᵒᵖ ⥤ 𝒪_X`-modules, and
  `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.derivedPushforwardSystem` — its
  image in `D(𝒪_X)` under the degree-zero single-object functor.
* `ExistenceSituation.isQuasicoherent_pushforwardSystem_obj` and
  `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.affineAmplitudeIn_derivedSystem_obj`
  — the terms of the system are quasi-coherent, so their hypercohomology over the affine opens of
  `X` is concentrated in degree zero.
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.compactSpace` and
  `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.quasiSeparatedSpace` — the scheme of
  the situation is quasi-compact and quasi-separated, which is what makes the coherator of
  [Stacks, Tag 0CR0] and the bound of [Stacks, Tag 0CSA] applicable to it.
* `AlgebraicGeometry.GrothendieckExistence.isDerivedLimit_coherator_obj_pushforwardSystem` — the
  displayed equality of [Stacks, Tag 0CTD].

## The shape of the proof

The source proves [Stacks, Tag 0CTD] by citing Derived Categories of Schemes, Example
[Stacks, Tag 0CSB], whose argument is the following. The coherator is a right adjoint, so it
commutes with the countable product in a derived-limit triangle and is exact, whence the displayed
equality. For the boundedness: over an affine open `U` the Milnor short exact sequence

`0 ⟶ R¹lim H^{m-1}(U, Fₙ) ⟶ H^m(U, R lim Fₙ) ⟶ lim H^m(U, Fₙ) ⟶ 0`

of [Stacks, Tag 0D60] together with the vanishing of the higher cohomology of a quasi-coherent
sheaf on an affine open ([Stacks, Tag 01XB]) shows that `H^m(U, R lim Fₙ)` vanishes unless
`m ∈ [0, 1]`, and then the bounded cohomological dimension of the coherator ([Stacks, Tag 0CSA])
puts `DQ_X(R lim Fₙ)` in `D^b_QCoh(𝒪_X)` with cohomology sheaves in degrees `≥ 0`.

Both halves of that argument hold for an arbitrary inverse system in `D(𝒪_X)` whose terms have
affine hypercohomology in a single interval `[a, b]`: they are
`AlgebraicGeometry.GrothendieckExistence.isDerivedLimit_coherator_obj`, and
`AlgebraicGeometry.GrothendieckExistence.affineAmplitudeIn_of_isDerivedLimit` combined with
[Stacks, Tag 0CSA], which together give the statements of [Stacks, Tag 0DIC]. What this file
adds is the passage from Situation [Stacks, Tag 0CTC] to such a system, namely the system
`(iₙ,* Fₙ)`, and the specialization of the interval to `[0, 0]`, which is what turns the
conclusion `D^-_QCoh(𝒪_X)` of Tag 0DIC into the sharper `D^b_QCoh(𝒪_X)` with cohomology in
degrees `≥ 0` of Tag 0CTD.

## The carried hypotheses

The coherator and the three inputs `hmv`, `hmvTop`, `haffine` of [Stacks, Tag 0CSA] are arguments,
exactly as they are in [Stacks, Tag 0CSA] and [Stacks, Tag 0CR2]: Tag 0CR0 is available in this
repository only with compact generation of `D_QCoh(𝒪_X)` as a hypothesis, and the bound of
Tag 0CSA is proved at a different model of the derived category. Nothing new is assumed about
them here, and nothing else is assumed at all.

In particular the two statements specific to Tag 0CTD are proved rather than carried.

*Quasi-coherence of the pushed-forward sheaves.* The sheaf `Fₙ` is of finite presentation, hence
quasi-coherent, and `iₙ : Xₙ → X` is a closed immersion
(`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.closedSchemeProjection`), hence an
affine morphism, so `iₙ,* Fₙ` is quasi-coherent by [Stacks, Tag 02KG]; that is
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`.

*Serre vanishing in the hypercohomology spelling.* That a quasi-coherent `𝒪_X`-module, viewed as
an object of `D(𝒪_X)` in degree zero, has hypercohomology over every affine open of `X`
concentrated in degree zero is `Stacks.Duality.Coherator.affineAmplitudeIn_zero_zero_single`. It is
[Stacks, Tag 01XB] transported from the spelling `Stacks.Cohomology.Hgroup`, the classical
`ℕ`-indexed right derived functor of `AddCommGrpCat`-valued sections, to the spelling
`Stacks.Duality.Coherator.AffineAmplitudeIn`, the homology of the total right derived functor of
`Γ(X, U)`-module-valued sections on the unbounded derived category.

Six fields of the situation play no part in this tag: separatedness of `X`, surjectivity and local
nilpotence of the transitions of rings, the second characterizing equation `transition_snd` of the
transition morphisms, flatness of `Fₙ` over the affine base at level `n`, and properness of its
support. The fields used are the system of rings, the scheme and its finite presentation, the
closed immersions `iₙ`, the transition morphisms with their equation `transition_fst`, the sheaves
`Fₙ` with their finite presentation, and the comparison isomorphisms `φₙ`. The six unused fields
are what the later tags of the section, [Stacks, Tag 0CTE] and [Stacks, Tag 0CTF], draw on; the
source states them once, in Situation [Stacks, Tag 0CTC], for the whole section.

## Implementation notes

The statements below are at the locally small model of `D(𝒪_X)`,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model the coherator vocabulary
of [Stacks, Tag 0CR2] lives at; this file declares no `HasDerivedCategory` instance of its own.
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation` is stated with no reference to a
derived category, so it is usable at that model without change.

The existence of a derived limit `K` of the system, and of the countable product it is built from,
are arguments rather than conclusions, as they are in the statements of Tag 0DIC.

## References

* [Stacks Project, Tag 0CTD](https://stacks.math.columbia.edu/tag/0CTD)
* [Stacks Project, Tag 0CTC](https://stacks.math.columbia.edu/tag/0CTC)
* [Stacks Project, Tag 0CSB](https://stacks.math.columbia.edu/tag/0CSB)
* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0DIC](https://stacks.math.columbia.edu/tag/0DIC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Opposite
open Stacks.Duality Stacks.Duality.Coherator

universe u

namespace AlgebraicGeometry.GrothendieckExistence

namespace ExistenceSituation

variable (S : ExistenceSituation.{u})

/-! ### The system of pushed-forward sheaves on `X` -/

/-- The closed immersion `iₙ : Xₙ → X` of the base change at level `n` into the scheme of the
situation. -/
abbrev closedImmersion (n : ℕ) : schemeAt S.system S.X n ⟶ S.X.left :=
  schemeProjection S.system S.X n

/-- The transition map `iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ` of the pushed-forward system.

It is the source's map, written out: the comparison isomorphism `φₙ` of the situation exhibits
`Fₙ` as the pullback of `Fₙ₊₁` along the inclusion `tₙ : Xₙ → Xₙ₊₁`, so its adjoint under
`tₙ^* ⊣ tₙ,*` is a map `Fₙ₊₁ ⟶ tₙ,* Fₙ`; pushing that forward along `iₙ₊₁` and using
`iₙ₊₁ ∘ tₙ = iₙ` gives the transition map. -/
def pushforwardTransition (n : ℕ) :
    (Scheme.Modules.pushforward (S.closedImmersion (n + 1))).obj (S.F (n + 1)) ⟶
      (Scheme.Modules.pushforward (S.closedImmersion n)).obj (S.F n) :=
  (Scheme.Modules.pushforward (S.closedImmersion (n + 1))).map
      ((Scheme.Modules.pullbackPushforwardAdjunction
          (S.transitionScheme n)).unit.app (S.F (n + 1)) ≫
        (Scheme.Modules.pushforward (S.transitionScheme n)).map (S.φ n).hom) ≫
    (Scheme.Modules.pushforwardComp (S.transitionScheme n)
        (S.closedImmersion (n + 1))).hom.app (S.F n) ≫
    (Scheme.Modules.pushforwardCongr (S.transition_fst n)).hom.app (S.F n)

/-- **The inverse system `(iₙ,* Fₙ)` of `𝒪_X`-modules attached to Situation [Stacks, Tag 0CTC].**
This is the system whose derived limit is the object `K` of [Stacks, Tag 0CTD]; the source writes
it simply `(Fₙ)`, identifying `Fₙ` with its pushforward along the closed immersion
`iₙ : Xₙ → X`. -/
def pushforwardSystem : ℕᵒᵖ ⥤ S.X.left.Modules :=
  Functor.ofOpSequence
    (X := fun n => (Scheme.Modules.pushforward (S.closedImmersion n)).obj (S.F n))
    S.pushforwardTransition

/-- The `n`-th term of `pushforwardSystem` is `iₙ,* Fₙ`. -/
@[simp]
lemma pushforwardSystem_obj (n : ℕ) :
    S.pushforwardSystem.obj (op n) =
      (Scheme.Modules.pushforward (S.closedImmersion n)).obj (S.F n) :=
  rfl

/-- The map `iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ` of `pushforwardSystem` is `pushforwardTransition n`. -/
@[simp]
lemma pushforwardSystem_map_succ (n : ℕ) :
    S.pushforwardSystem.map (homOfLE (Nat.le_succ n)).op = S.pushforwardTransition n := by
  apply Functor.ofOpSequence_map_homOfLE_succ

/-- **The pushed-forward sheaves are quasi-coherent.** The sheaf `Fₙ` is of finite presentation,
hence quasi-coherent, and the projection `iₙ : Xₙ → X` is a closed immersion, hence an affine
morphism; the direct image of a quasi-coherent module along an affine morphism is quasi-coherent,
[Stacks, Tag 02KG]. -/
instance isQuasicoherent_pushforwardSystem_obj (n : ℕ) :
    (S.pushforwardSystem.obj (op n)).IsQuasicoherent :=
  have : IsClosedImmersion (S.closedImmersion n) := S.closedSchemeProjection n
  have := S.finitelyPresented n
  have : (S.F n).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (S.F n)).choose.isQuasicoherent
  Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
    (S.closedImmersion n) (S.F n)

/-- **The inverse system `(iₙ,* Fₙ)` read in `D(𝒪_X)`**, each term placed in degree zero. Its
derived limit is the object `R lim_{D(𝒪_X)} Fₙ` of [Stacks, Tag 0CTD]. -/
def derivedPushforwardSystem : ℕᵒᵖ ⥤ DerivedCategory S.X.left.Modules :=
  S.pushforwardSystem ⋙ DerivedCategory.singleFunctor S.X.left.Modules 0

/-- The `n`-th term of `derivedPushforwardSystem` is `iₙ,* Fₙ` placed in degree zero. -/
@[simp]
lemma derivedPushforwardSystem_obj (n : ℕ) :
    S.derivedPushforwardSystem.obj (op n) =
      (DerivedCategory.singleFunctor S.X.left.Modules 0).obj
        ((Scheme.Modules.pushforward (S.closedImmersion n)).obj (S.F n)) :=
  rfl

/-- **The terms of the system have affine amplitude in `[0, 0]`.** Each `iₙ,* Fₙ` is a
quasi-coherent module placed in degree zero, so its hypercohomology over an affine open of `X` is
concentrated in degree zero: in negative degrees by left exactness of sections, in positive
degrees by Serre vanishing ([Stacks, Tag 01XB]). This is the hypothesis of [Stacks, Tag 0CSA] at
`a = b = 0`, which is what Example [Stacks, Tag 0CSB] feeds that tag. -/
theorem affineAmplitudeIn_derivedSystem_obj (n : ℕ) :
    AffineAmplitudeIn S.X.left 0 0 (S.derivedPushforwardSystem.obj (op n)) :=
  affineAmplitudeIn_zero_zero_single S.X.left (S.pushforwardSystem.obj (op n))

/-! ### The scheme of the situation is quasi-compact and quasi-separated -/

/-- The scheme of Situation [Stacks, Tag 0CTC] is quasi-compact: it is quasi-compact over the
affine inverse-limit base, because it is of finite presentation there. -/
lemma compactSpace : CompactSpace S.X.left :=
  have : QuasiCompact S.X.hom := S.finitePresentation.quasiCompact
  QuasiCompact.compactSpace_of_compactSpace S.X.hom

/-- The scheme of Situation [Stacks, Tag 0CTC] is quasi-separated: it is quasi-separated over the
affine inverse-limit base, because it is of finite presentation there. -/
lemma quasiSeparatedSpace : QuasiSeparatedSpace S.X.left :=
  have : QuasiSeparated S.X.hom := S.finitePresentation.quasiSeparated
  quasiSeparatedSpace_of_quasiSeparated S.X.hom

end ExistenceSituation

/-! ### The conclusions of the tag -/

section

variable (S : ExistenceSituation.{u})
  (DQ : DerivedCategory S.X.left.Modules ⥤ quasiCoherentDerivedCategory S.X.left)

/-- **[Stacks, Tag 0CTD], the displayed equality.** In Situation [Stacks, Tag 0CTC], if `K` is a
derived limit in `D(𝒪_X)` of the system `(iₙ,* Fₙ)` of
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.derivedPushforwardSystem`, then
`DQ_X(K)` is a derived limit of the system `(DQ_X(iₙ,* Fₙ))` in `D_QCoh(𝒪_X)`. This is the
equality `R lim_{D_QCoh(𝒪_X)}(Fₙ) = DQ_X(R lim_{D(𝒪_X)} Fₙ)` of the statement of the tag; the
existence of the product of the images is part of the conclusion.

The reason is the source's: `DQ_X` is a right adjoint, so it commutes with the countable product
occurring in a derived-limit triangle, and it is exact because the adjunction `ι ⊣ DQ_X` is
triangulated. -/
@[stacks 0CTD "the displayed equality only; the coherator of Stacks 0CR0 is an argument, as in \
  Stacks 0CSA and 0CR2"]
theorem isDerivedLimit_coherator_obj_pushforwardSystem (adj : quasiCoherentι S.X.left ⊣ DQ)
    [DQ.CommShift ℤ] [adj.IsTriangulated]
    [HasProduct fun n : ℕ => S.derivedPushforwardSystem.obj ⟨n⟩]
    (K : DerivedCategory S.X.left.Modules)
    (hK : IsDerivedLimit S.derivedPushforwardSystem K) :
    ∃ h : HasProduct fun n : ℕ => DQ.obj (S.derivedPushforwardSystem.obj ⟨n⟩),
      @IsDerivedLimit (quasiCoherentDerivedCategory S.X.left) _ _ _ _ _ _
        (S.derivedPushforwardSystem ⋙ DQ) h (DQ.obj K) :=
  isDerivedLimit_coherator_obj adj S.derivedPushforwardSystem K hK

end

end AlgebraicGeometry.GrothendieckExistence

end

module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.AffineGradedAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.BaseChangeGradedModule
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.CohomologyCoproduct
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedModuleFiniteType
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFiniteSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Further results on `ProperCohomologyFiniteness`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness` that need
imports beyond those of that module.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence (relativeSpec relativeSpecQcohEquivalence)
open Stacks.AffineGradedAlgebra (baseChangeModuleOfRelativeSpec gradedTildePullbackAlgebraSheaf
  pushforwardPullbackIsoIntCoprod qcohGradedTildePullbackModule)

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

/-! ### [Stacks, Tag 0897] part (1): finiteness of the graded cohomology -/

variable {X : Scheme.{u}}

/- `𝓑 = f^* B̃` is quasi-coherent as a sheaf of algebras, which is what a relative spectrum
`Spec_X(𝓑)` asks of it; the statements below name that relative spectrum. -/
attribute [local instance]
  Stacks.AffineGradedAlgebra.isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback

/-- The base change `X' = Spec(B) ×_{Spec(A)} X` along which the proof of [Stacks, Tag 0897]
runs, for an `A`-algebra `B` and a morphism `f : X ⟶ Spec A`. -/
abbrev baseChangeScheme (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (f : X ⟶ Spec (.of A)) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) f

/-- The structure morphism `f' : X' ⟶ Spec B` of `baseChangeScheme`. It is proper as soon as `f`
is, properness being stable under base change. -/
abbrev baseChangeToSpec (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (f : X ⟶ Spec (.of A)) : baseChangeScheme A B f ⟶ Spec (.of B) :=
  pullback.fst _ _

/-- **The base change `X' = Spec(B) ×_{Spec(A)} X` of [Stacks, Tag 0897] is locally
Noetherian**, for `A` Noetherian, `B` of finite type over `A` and `f` proper.

This is the second of the two inputs the coherence upgrade of [Stacks, Tag 01XZ] needs at `X'`:
a quasi-coherent module of finite type on a locally Noetherian scheme is coherent
(`Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType`), and
until now `X'` was nowhere recorded as locally Noetherian.

`B` is Noetherian because it is an algebra of finite type over the Noetherian ring `A`, so
`Spec B` is locally Noetherian; and the source of a morphism locally of finite type over a
locally Noetherian scheme is locally Noetherian ([Stacks, Tag 01T6],
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`), which is applied here to the
projection `π = pullback.snd`. Mathlib carries that composite as an instance, so only the
Noetherianness of `B` has to be supplied.

Properness of `f` is not used, only that it is locally of finite type, which properness
supplies by instance at the consumer. -/
@[ega "I 6.3.8" "special case", ega "I 6.6.7" "special case"]
theorem isLocallyNoetherian_baseChangeScheme (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian (baseChangeScheme A B f) :=
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  inferInstance

/-- **The coherent module `F'` on `X'` that the proof of [Stacks, Tag 0897] part (1) uses,
together with the identification of its direct image.** For `A` Noetherian, `B` a graded
`A`-algebra of finite type, `f` locally of finite type and `F` a graded `𝓑`-module with
quasi-coherent pieces which is of finite type on affine opens, there is a *coherent*
`𝒪_{X'}`-module whose direct image along the projection `π = pullback.snd` is the coproduct
`∐ₙ Fₙ` of the homogeneous pieces.

This is an input of [Stacks, Tag 0897] part (1), supplied here rather than carried as a hypothesis. The quasi-coherent
module together with the identification of its direct image of `𝒪_X`-modules is
`Stacks.AffineGradedAlgebra.exists_isQuasicoherent_pushforward_baseChange_iso_intCoprod`; the
finite type is
`Stacks.AffineGradedAlgebra.exists_isFiniteType_pushforward_baseChange_iso_intCoprod`, which
produces the module together with the identification in the quasi-coherent `𝓑`-modules — the
stronger one, carrying the `Γ(𝒪_{X'}, π⁻¹U)`-action over which finite type is taken. The
upgrade to coherence is then (2) ⇒ (1) of [Stacks, Tag 01XZ],
`Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType`, over the
locally Noetherian `X'` of `isLocallyNoetherian_baseChangeScheme`.

**The `𝓑`-linear identification is returned, not discarded.** Like the finite-type statement it
rests on, this one quantifies over the quasi-coherent module `𝒢` on `Spec_X(𝓑)` and over the
identification of its direct image in the quasi-coherent `𝓑`-modules, with
`F' = Stacks.AffineGradedAlgebra.baseChangeModuleOfRelativeSpec A 𝒜 f 𝒢`; the `𝒪_X`-module
identification `π_* F' ≅ ∐ₙ Fₙ` is kept as the last conjunct and is
`Stacks.AffineGradedAlgebra.pushforwardPullbackIsoIntCoprod` of the `𝓑`-linear one, so this
statement visibly implies the shape `∃ F', F'.IsCoherent ∧ Nonempty (π_* F' ≅ ∐ₙ Fₙ)` an earlier
revision concluded. That shape alone is what made the action of
`gradedCohomologySumModuleOfFiniteType` incomparable with any action defined from the graded
structure.

Properness of `f` is not used, only that it is locally of finite type. -/
theorem exists_isCoherent_pushforward_baseChange_iso_intCoprod
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) :
    ∃ (G : (_root_.SheafOfModules.isQuasicoherent
        (relativeSpec (gradedTildePullbackAlgebraSheaf A 𝒜 f)).ringCatSheaf).FullSubcategory)
      (_ : (relativeSpecQcohEquivalence
          (gradedTildePullbackAlgebraSheaf A 𝒜 f)).functor.obj G ≅
        qcohGradedTildePullbackModule A 𝒜 f F hqc),
      (baseChangeModuleOfRelativeSpec A 𝒜 f G.obj).IsCoherent ∧
      Nonempty ((Scheme.Modules.pushforward
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).obj
            (baseChangeModuleOfRelativeSpec A 𝒜 f G.obj) ≅
        ∐ fun n : ℤ => pieceModule F n) :=
  let key :=
    Stacks.AffineGradedAlgebra.exists_isFiniteType_pushforward_baseChange_iso_intCoprod A 𝒜 f F
      hqc hft
  have := isLocallyNoetherian_baseChangeScheme A B f
  have := key.choose_spec.choose_spec.1
  have := key.choose_spec.choose_spec.2.1
  ⟨key.choose, key.choose_spec.choose,
    CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType _,
    key.choose_spec.choose_spec.2.2⟩

/-- The quasi-coherent module on `Spec_X(𝓑)` that [Stacks, Tag 01SB] produces for the graded
`𝓑`-module `F`, chosen from `exists_isCoherent_pushforward_baseChange_iso_intCoprod`. The
coherent `F'` of [Stacks, Tag 0897] part (1) is its inverse image along `X' ≅ Spec_X(𝓑)`. -/
def baseChangeRelativeSpecModuleOfFiniteType
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) :
    (_root_.SheafOfModules.isQuasicoherent
      (relativeSpec (gradedTildePullbackAlgebraSheaf A 𝒜 f)).ringCatSheaf).FullSubcategory :=
  (exists_isCoherent_pushforward_baseChange_iso_intCoprod A 𝒜 f F hqc hft).choose

/-- **The identification of [Stacks, Tag 0897] part (1) in the quasi-coherent `𝓑`-modules**: the
direct image of `baseChangeRelativeSpecModuleOfFiniteType` under the equivalence of
[Stacks, Tag 01SB] is the ungraded realization of `F`.

This is the identification the `𝒪_X`-module one is built from, and the only one that records
which scalars it respects: its component over an affine open `U` of `X` is linear over
`Γ(𝓑, U)`, which is `Γ(𝒪_{X'}, π⁻¹U)` read through [Stacks, Tag 01LX] (3). -/
def baseChangeModuleAlgIsoOfFiniteType
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) :
    (relativeSpecQcohEquivalence (gradedTildePullbackAlgebraSheaf A 𝒜 f)).functor.obj
      (baseChangeRelativeSpecModuleOfFiniteType A 𝒜 f F hqc hft) ≅
      qcohGradedTildePullbackModule A 𝒜 f F hqc :=
  (exists_isCoherent_pushforward_baseChange_iso_intCoprod A 𝒜 f F hqc hft).choose_spec.choose

/-- The coherent `F'` on `X'` of [Stacks, Tag 0897] part (1): the inverse image along
`X' ≅ Spec_X(𝓑)` of the module `baseChangeRelativeSpecModuleOfFiniteType` on the relative
spectrum. -/
def baseChangeModuleOfFiniteType
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) : (baseChangeScheme A B f).Modules :=
  baseChangeModuleOfRelativeSpec A 𝒜 f
    (baseChangeRelativeSpecModuleOfFiniteType A 𝒜 f F hqc hft).obj

/-- `baseChangeModuleOfFiniteType` is coherent. -/
theorem isCoherent_baseChangeModuleOfFiniteType
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) :
    (baseChangeModuleOfFiniteType A 𝒜 f F hqc hft).IsCoherent :=
  (exists_isCoherent_pushforward_baseChange_iso_intCoprod A 𝒜 f F hqc
    hft).choose_spec.choose_spec.1

/-- The identification of the direct image of `baseChangeModuleOfFiniteType` along the
projection `π` with the coproduct of the homogeneous pieces.

It is `Stacks.AffineGradedAlgebra.pushforwardPullbackIsoIntCoprod` applied to the `𝓑`-linear
`baseChangeModuleAlgIsoOfFiniteType`, not an isomorphism chosen from a bare `Nonempty`: by
definition this identification is the direct image of a morphism of quasi-coherent `𝓑`-modules,
read through [Stacks, Tag 01SB] and [Stacks, Tag 01LX]. Which is what a comparison of the action
`gradedCohomologySumModuleOfFiniteType` carries across [Stacks, Tag 089W] with an action defined
degreewise from the graded structure would have to start from. -/
def baseChangeModuleIsoOfFiniteType
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) :
    (Scheme.Modules.pushforward
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).obj
        (baseChangeModuleOfFiniteType A 𝒜 f F hqc hft) ≅
      ∐ fun n : ℤ => pieceModule F n :=
  pushforwardPullbackIsoIntCoprod A 𝒜 f F hqc
    (baseChangeRelativeSpecModuleOfFiniteType A 𝒜 f F hqc hft)
    (baseChangeModuleAlgIsoOfFiniteType A 𝒜 f F hqc hft)

/-- **The `B`-action on `⨁ₙ H^p(X, Fₙ)` of the proof of [Stacks, Tag 0897] part (1)**, built
from the module `F'` on `X'` of that proof together with the identification
`e : π_* F' ≅ ∐ₙ Fₙ` of its direct image with the coproduct of the homogeneous pieces.

`X` is quasi-compact and quasi-separated, `f` being proper over an affine scheme, and the
projection `π : X' ⟶ X` is affine by base change from `Spec B ⟶ Spec A`, so
`coprodCohomologyModule` applies: cohomology commutes with the `ℤ`-indexed direct sum,
[Stacks, Tag 089W] along `π` identifies `H^p(X, ∐ₙ Fₙ)` with `H^p(X', F')`, and the `B`-action
on `H^p(X', F')` — restriction of scalars along `(f')^♯` — is carried across the composite. -/
@[instance_reducible]
def gradedCohomologySumModule (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (p : ℕ) (F' : (baseChangeScheme A B f).Modules) (hqc : F'.IsQuasicoherent)
    (e : (Scheme.Modules.pushforward
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).obj F' ≅
      ∐ fun n : ℤ => pieceModule F n) :
    Module B (gradedCohomologySum F p) :=
  letI := hqc
  letI : CompactSpace (X : Type u) := QuasiCompact.compactSpace_of_compactSpace f
  letI : QuasiSeparatedSpace (X : Type u) := quasiSeparatedSpace_of_quasiSeparated f
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) f :=
    ⟨fun sq H => isAffineHom_isStableUnderBaseChange.of_isPullback sq H⟩
  letI : IsAffineHom (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  coprodCohomologyModule _ (fun n : ℤ => pieceModule F n) F' p (baseChangeToSpec A B f) e

/-- **The `B`-action on `⨁ₙ H^p(X, Fₙ)` of [Stacks, Tag 0897] part (1), produced rather than
assumed.** It is `gradedCohomologySumModule` at the coherent `F'` and the identification `e`
that `exists_isCoherent_pushforward_baseChange_iso_intCoprod` produces from the finite type of
`F`.

`F'` is chosen, so the action depends on that choice. As with `gradedCohomologySumModule`, it is
the action carried across the comparison of [Stacks, Tag 089W] and is not asserted to agree with
the action the source defines degreewise from the graded module structure.

What stands in the way of that comparison is neither side. The `e` used here is
`baseChangeModuleIsoOfFiniteType`, which is by definition
`Stacks.AffineGradedAlgebra.pushforwardPullbackIsoIntCoprod` of the `𝓑`-linear
`baseChangeModuleAlgIsoOfFiniteType`, so the `Γ(𝓑, U)`-linearity is on record. The *other* side — a degreewise action on
`⨁ₙ H^p(X, Fₙ)` over the `f^* B̃` of this statement — exists too, as
`Stacks.AlgebraicGeometry.GradedProperCohomology.gradedTildeCohomologyGmodule`
(`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/GradedTildeDegreewiseAction.lean`): the
degreewise construction of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/CohomologyGradedReesFinite.lean` is stated over
an arbitrary `Stacks.Cohomology.FormalFunctions.SectionSystem`, and the section map
`𝒜 k → Γ(X, (f^* B̃)ₖ)` it needs, with its additivity, unit and multiplicativity, is
`Stacks.AffineGradedAlgebra.gradedTildePullbackSection`.

What is still missing is the comparison itself: a statement that the action carried across
[Stacks, Tag 089W] and the degreewise one agree. Reduced to a single piece of data it is the
hypothesis of
`Stacks.AlgebraicGeometry.GradedProperCohomology.moduleFinite_gradedTildeCohomologyModule`,
namely an injective `B`-linear map from the degreewise module into the module here, and proving
it is a statement about [Stacks, Tag 089W] and [Stacks, Tag 01SB] on the relative spectrum. The
direction is forced: the degreewise action shifts degrees by `k ≥ 0`, so the nonnegative-degree
module the source grades by `ℕ` is a `B`-submodule of the `ℤ`-graded module here, and the
projection the other way is not `B`-linear.

What that proof needs of [Stacks, Tag 089W] is naturality in the module, and the `e` above is
read off `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`, which is defined one
module at a time and has none. The naturality is available from the *other* Tag 089W
isomorphism in this library: `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIso` is an
isomorphism of functors, and
`Stacks.AffineCohomologyPushforward.cohomologyPushforwardModuleIso_naturality` carries it into
the module-valued model of cohomology this statement works in, after forgetting the scalars. No
lemma identifies the two isomorphisms, so a proof of the comparison would have to be assembled
over the natural one rather than over the `e` above. -/
@[instance_reducible]
def gradedCohomologySumModuleOfFiniteType
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) (p : ℕ) :
    Module B (gradedCohomologySum F p) :=
  letI := isCoherent_baseChangeModuleOfFiniteType A 𝒜 f F hqc hft
  gradedCohomologySumModule A 𝒜 f F p (baseChangeModuleOfFiniteType A 𝒜 f F hqc hft)
    (isQuasicoherent_of_isCoherent (baseChangeModuleOfFiniteType A 𝒜 f F hqc hft))
    (baseChangeModuleIsoOfFiniteType A 𝒜 f F hqc hft)

/-- **[Stacks, Tag 0897] part (1) at a given coherent `F'` and identification `e`.** For any
coherent `𝒪_{X'}`-module `F'` whose direct image along `π` is `∐ₙ Fₙ`, the graded `B`-module
`⨁ₙ H^p(X, Fₙ)` is a finite `B`-module, for the action `gradedCohomologySumModule` transports
across the comparison of [Stacks, Tag 089W].

`B` is Noetherian because it is a finitely generated algebra over the Noetherian ring `A`, and
`F'` is coherent, so `tag02O6` — [Stacks, Tag 02O6] over a ring — makes `H^p(X', F')` a finite
`B`-module, and the comparison carries that finiteness back to `⨁ₙ H^p(X, Fₙ)`. -/
theorem moduleFinite_gradedCohomologySum_of_iso
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (p : ℕ) (F' : (baseChangeScheme A B f).Modules) [F'.IsCoherent]
    (e : (Scheme.Modules.pushforward
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).obj F' ≅
      ∐ fun n : ℤ => pieceModule F n) :
    @Module.Finite B (gradedCohomologySum F p) _ _
      (gradedCohomologySumModule A 𝒜 f F p F' (isQuasicoherent_of_isCoherent F') e) := by
  let := isQuasicoherent_of_isCoherent F'
  let : CompactSpace (X : Type u) := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace (X : Type u) := quasiSeparatedSpace_of_quasiSeparated f
  let : IsAffineHom (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (.of_hasPullback _ _) inferInstance
  have hBN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact moduleFinite_coprodCohomology _ (fun n : ℤ => pieceModule F n) F' p
    (baseChangeToSpec A B f) e
    (tag02O6 B hBN (baseChangeScheme A B f) (baseChangeToSpec A B f) inferInstance F'
      inferInstance p)

/-- **[Stacks, Tag 0897] part (1), with `𝓑 = f^* B̃` and over the base change the proof
constructs.** Let `A` be a Noetherian ring, `B` a finitely generated graded `A`-algebra,
`f : X ⟶ Spec A` proper, `𝓑 = f^* B̃`, and `F` a quasi-coherent graded `𝓑`-module of finite
type. Then the graded `B`-module `⨁ₙ H^p(X, Fₙ)` is a finite `B`-module, for every `p`.

The graded algebra `𝓑` is the source's own: `B̃` is
`Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜`, the sheaf of graded `𝒪_{Spec A}`-algebras whose
degree-`n` piece is the associated sheaf `(𝒜 n)~`, and the pullback along `f` is
`Stacks.Conormal.gradedPullback`.

The base change of the source's proof is built here rather than assumed:
`baseChangeScheme A B f` is `X' = Spec(B) ×_{Spec(A)} X` and `baseChangeToSpec A B f` is its
structure morphism `f' : X' ⟶ Spec B`, which is proper because properness is stable under base
change in Mathlib. The projection `π : X' ⟶ X` is `pullback.snd`, and it is affine for the same
reason, which is what makes [Stacks, Tag 089W] applicable to it.

**Nothing is carried.** The coherent `F'` on `X'` and the identification `e : π_* F' ≅ ∐ₙ Fₙ`
of its direct image, which the source's statement does not mention, are produced by
`exists_isCoherent_pushforward_baseChange_iso_intCoprod` above, so the registration is
unconditional; the graded `B`-action on `⨁ₙ H^p(X, Fₙ)` and a `B`-linear comparison with
`H^p(X', F')` are produced from `e`, by `gradedCohomologySumModule`.

**Where the `B`-action comes from.** It is `gradedCohomologySumModuleOfFiniteType`, i.e.
`gradedCohomologySumModule` at the produced `F'` and `e`: cohomology of a quasi-compact
quasi-separated scheme commutes with the `ℤ`-indexed direct sum
(`Stacks.AlgebraicGeometry.GradedProperCohomology.cohomologyCoprodIso`, a universe
specialization of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange`
`.preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections`, which is
[Stacks, Tag 01FF] for a scheme), and [Stacks, Tag 089W] along the affine `π` identifies
`H^p(X, ∐ₙ Fₙ)` with `H^p(X', F')`
(`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`). The `B`-action on
`⨁ₙ H^p(X, Fₙ)` is the one carried across that composite; it is **not** asserted to agree with
the action the source defines degreewise from the graded module structure. That degreewise
action over the `f^* B̃` here is
`Stacks.AlgebraicGeometry.GradedProperCohomology.gradedTildeCohomologyGmodule`, which is not
restricted to the Rees algebra `⨁ₙ ℐⁿ` of an ideal sheaf. The note on `gradedCohomologySumModuleOfFiniteType` records what the comparison
of the two still needs, and `moduleFinite_gradedTildeCohomologyModule` is the finiteness it
would yield. `F'` is chosen, so the action depends on that choice.

**How `F'` and `e` are produced.** The quasi-coherent half is already available:
`Stacks.AffineGradedAlgebra.exists_isQuasicoherent_pushforward_baseChange_iso_intCoprod`
produces a quasi-coherent `𝒪_{X'}`-module whose direct image along `π` is `∐ₙ Fₙ`, from `hqc`
and nothing else — not even properness of `f`. It is the module of [Stacks, Tag 01SB] over
`Spec_X(𝓑)`
(`Stacks.RelativeSpec.exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight_of_piece`),
read as an `𝒪_X`-module through
`Stacks.AffineAlgebraEquivalence.restrictScalars_relativeSpecQcohEquivalence_functor_obj` and
`Stacks.RelativeSpec.intCoprodIsoUnderlyingModule_gradedModuleSheaf`, then transported to `X'`
along `Stacks.AffineGradedAlgebra.baseChangeIsoRelativeSpecGradedTildePullback`, which is
[Stacks, Tag 01LX] at `𝓑 = f^* B̃`.

What that statement cannot give is coherence, because it forgets the `𝓑`-action: the
isomorphism it returns is one of `𝒪_X`-modules and carries only the `Γ(X, U)`-action, while
finite type of `F'` is taken over `Γ(𝒪_{X'}, π⁻¹U)`. So the coherent `F'` is produced
*together with* the identification in the quasi-coherent `𝓑`-modules, by
`Stacks.AffineGradedAlgebra.exists_isFiniteType_pushforward_baseChange_iso_intCoprod`, whose
three transports — the span statement hidden in `Stacks.Coherent.IsFiniteTypeOnAffine`, the ring
of sections of `𝓑` over an affine open, and the linearity of the identification over it — are
the subject of
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedModuleFiniteType`. The upgrade from
finite type to coherence is then (2) ⇒ (1) of [Stacks, Tag 01XZ],
`Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType`, over the
locally Noetherian `X'` of `isLocallyNoetherian_baseChangeScheme`.

The finiteness itself: `B` is Noetherian because it is a finitely generated algebra over the
Noetherian ring `A`, and `F'` is coherent, so `tag02O6` — [Stacks, Tag 02O6] over a ring — makes
`H^p(X', F')` a finite `B`-module, and the comparison carries that finiteness back to
`⨁ₙ H^p(X, Fₙ)`. -/
@[stacks 0897 "part (1), with the graded algebra read as the source defines it, B = f^* Btilde \
for Btilde the graded algebra sheaf of B on Spec(A), and over the base change \
X' = Spec(B) ×_Spec(A) X that the proof builds: the graded B-module ⨁_n H^p(X, F_n) is a finite \
B-module, for the B-action carried across the comparison of Tag 089W rather than the one the \
source defines degreewise"]
theorem moduleFinite_gradedCohomologySum_gradedPullback
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule
      (Stacks.Conormal.gradedPullback f (Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜)))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) (p : ℕ) :
    @Module.Finite B (gradedCohomologySum F p) _ _
      (gradedCohomologySumModuleOfFiniteType A 𝒜 f F hqc hft p) :=
  let := isCoherent_baseChangeModuleOfFiniteType A 𝒜 f F hqc hft
  moduleFinite_gradedCohomologySum_of_iso A 𝒜 f F p
    (baseChangeModuleOfFiniteType A 𝒜 f F hqc hft)
    (baseChangeModuleIsoOfFiniteType A 𝒜 f F hqc hft)

end Stacks.AlgebraicGeometry.GradedProperCohomology

end

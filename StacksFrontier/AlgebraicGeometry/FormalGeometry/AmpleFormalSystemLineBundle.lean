module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentTowerSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalClosedSubschemeAlgebraization
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksCore.Tactic.StacksAttribute

/-!
# The line bundle of Grothendieck's algebraization theorem

`Stacks.AmpleFormalSystemAlgebraization.exists_isProjectiveMorphism_of_tupleTower` produces the
geometric half
of the conclusion of [Stacks, Tag 089A]: the proper morphism `fX : X ⟶ Spec A` and the morphisms
`kₙ : Xₙ ⟶ X` exhibiting each `Xₙ` as `X ×_{Spec A} Sₙ`. This file produces the remaining half,
**the invertible `𝒪_X`-module `ℒ` with `ℒₙ ≅ ℒ|_{Xₙ}` compatibly with the `φₙ`**, by algebraizing
the system `(ℒₙ, φₙ)` itself.

The source does not say how `ℒ` is obtained — its proof only ever sees `ℒₙ ^⊗ d`, and the final
appeal to [Stacks, Tag 0899] produces no module at all. The route taken here is the natural one:
the `(ℒₙ, φₙ)` are a system of coherent modules along the tower in the sense of
`Stacks.CoherentTower.ModuleSystem`, and Grothendieck existence says that restriction along the
`kₙ` is an equivalence onto such systems, so the system is `ℒ|_{Xₙ}` for a coherent `ℒ` — and the
compatibility clause the theorem asks for is *exactly* the statement that the family of
isomorphisms `ℒₙ ≅ ℒ|_{Xₙ}` is a morphism in that category.

## Main definitions

* `Stacks.AmpleFormalSystemLineBundle.ofInvertible` — the system `(ℒₙ, φₙ)` read as an object of
  `Stacks.CoherentTower.ModuleSystem`.

## Main results

* `Stacks.AmpleFormalSystemLineBundle.isClosedImmersion_of_isPullback` and
  `isLocallyNoetherian_of_isPullback` — each member of a cartesian adic tower over `X` is a
  locally Noetherian closed subscheme of `X`.
* `Stacks.AmpleFormalSystemLineBundle.isInvertibleModule_of_iso` and
  `isInvertibleModule_pullback` — invertibility transports along an isomorphism and along a
  pullback, in the `Stacks.Ample.IsInvertibleModule` spelling.
* `Stacks.AmpleFormalSystemLineBundle.exists_coherent_of_restriction_isEquivalence` — the
  algebraized module `ℒ` together with the isomorphisms `ℒₙ ≅ ℒ|_{Xₙ}` and the compatibility
  clause of [Stacks, Tag 089A].
* `Stacks.AmpleFormalSystemLineBundle.isAmple_of_exists_isAmple_tensorPowModule` —
  [Stacks, Tag 01PT] in the shape the ampleness residue needs.
* `Stacks.AmpleFormalSystemLineBundle.exists_isAmple_of_restriction_isEquivalence` — **the sheaf
  half of the conclusion of [Stacks, Tag 089A]**: the same `ℒ`, invertible and ample. The passage
  from coherent to invertible, and from invertible to ample, are the two named hypotheses
  `hinvertible` and `hample`; see below.

## The hypotheses

`hequiv`, that restriction along the tower is an equivalence, is Grothendieck existence in the
form [Stacks, Tag 088F] states it. The library carries [Stacks, Tag 088E] at
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_holds`, against the
category `Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I fX)`; the *unwinding* of that
category into systems on the adic base changes — the content [Stacks, Tag 088F] adds — is recorded
as missing in the module documentation of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicThickeningCoherentSystem.lean`, so it is not
available here and the equivalence enters as a hypothesis in the geometric form. Only *essential
surjectivity* of the restriction functor is used; the equivalence is asked for because that is the
form in which Grothendieck existence is stated.

`hinvertible` — a coherent `𝒪_X`-module whose restriction to every member of the tower is
invertible is invertible — and `hample` — an invertible `𝒪_X`-module whose restriction to the
closed member is ample is ample — are the two remaining residues. Both are statements about `X`
alone, with no reference to the system `(ℒₙ, φₙ)`, so each can be discharged once and for all.

## Implementation notes

The coherence of each `ℒₙ` is
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible`, whose Tag 01CS class is
the one `Stacks.RelativeVeryAmple.stacksIsInvertible` produces from the ampleness theory's
`Stacks.Ample.IsInvertibleModule`.

Each `Xₙ` is locally Noetherian because `kₙ : Xₙ ⟶ X` is a closed immersion, being the base change
of the closed immersion `Sₙ ⟶ S`, and `X` is locally Noetherian because `fX` is of finite type
over the Noetherian ring `A`. That instance has to be in scope before `hequiv` can even be stated,
so it is supplied by a `letI` in the binder.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.CoherentTower

universe u

namespace Stacks.AmpleFormalSystemLineBundle

variable (A : Type u) [CommRing A] (I : Ideal A)

/-! ### The tower is a tower of closed subschemes of `X` -/

variable {X : Scheme.{u}} {Xn : ℕ → Scheme.{u}}

/-- **Each member of a cartesian adic tower over `X` is a closed subscheme of `X`**, being the
base change of the closed immersion `Sₙ ⟶ S`. -/
public lemma isClosedImmersion_of_isPullback (fX : X ⟶ Spec (.of A))
    (q : ∀ n : ℕ, Xn n ⟶ adicThickening A I n) (k : ∀ n : ℕ, Xn n ⟶ X)
    (hkcart : ∀ n : ℕ, IsPullback (k n) (q n) fX (adicThickeningι A I n)) (n : ℕ) :
    IsClosedImmersion (k n) :=
  MorphismProperty.of_isPullback (hkcart n).flip
    (Stacks.AmpleFormalSystemSections.isClosedImmersion_adicThickeningι A I n)

/-- **Each member of a cartesian adic tower over `X` is locally Noetherian.** `X` is locally
Noetherian because `fX` is locally of finite type over the Noetherian ring `A`, and `Xₙ` is a
closed subscheme of `X`. -/
public lemma isLocallyNoetherian_of_isPullback [IsNoetherianRing A] (fX : X ⟶ Spec (.of A))
    [LocallyOfFiniteType fX] (q : ∀ n : ℕ, Xn n ⟶ adicThickening A I n)
    (k : ∀ n : ℕ, Xn n ⟶ X)
    (hkcart : ∀ n : ℕ, IsPullback (k n) (q n) fX (adicThickeningι A I n)) (n : ℕ) :
    IsLocallyNoetherian (Xn n) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian fX
  have := isClosedImmersion_of_isPullback A I fX q k hkcart n
  LocallyOfFiniteType.isLocallyNoetherian (k n)

/-! ### Transporting invertibility -/

/-- **Invertibility depends only on the isomorphism class**, through clause 2 of
[Stacks, Tag 0B8M]: both sides are rank-one finite local freeness, which transports along an
isomorphism. -/
public lemma isInvertibleModule_of_iso {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (h : IsInvertibleModule Y M) : IsInvertibleModule Y N :=
  (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one Y N).mpr
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff N 1).mp
      (Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso e
        ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff M 1).mpr
          ((Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
            Y M).mp h))))

/-- **The pullback of an invertible module is invertible**, [Stacks, Tag 0B8L], in the
`Scheme.Modules.pullback` spelling. -/
public lemma isInvertibleModule_pullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules)
    (h : IsInvertibleModule Z M) : IsInvertibleModule Y ((Scheme.Modules.pullback f).obj M) :=
  have := h
  Stacks.InvertiblePullback.isInvertibleModule_pullback f M

/-! ### The system of invertible modules -/

/-- **The system `(ℒₙ, φₙ)` of [Stacks, Tag 089A] as a system of coherent modules along the
tower.** An invertible module on a locally Noetherian scheme is coherent, so the only input is
[Stacks, Tag 01CS] for each `ℒₙ`. -/
public def ofInvertible [∀ n : ℕ, IsLocallyNoetherian (Xn n)]
    (i : ∀ n : ℕ, Xn n ⟶ Xn (n + 1)) (L : ∀ n : ℕ, (Xn n).Modules)
    (hL : ∀ n : ℕ, IsInvertibleModule (Xn n) (L n))
    (φ : ∀ n : ℕ, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n) :
    ModuleSystem i where
  obj := L
  isCoherent n :=
    haveI := hL n
    @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible (Xn n) _ (L n)
      (Stacks.RelativeVeryAmple.stacksIsInvertible (Xn n) (L n))
  transitionIso := φ

/-! ### The algebraization -/

/-- **The line bundle of [Stacks, Tag 089A], as a coherent module.** Let `A` be Noetherian, let
`fX : X ⟶ Spec A` be proper, let `Xₙ` be a tower over the thickenings exhibited as `X ×_S Sₙ` by
morphisms `kₙ : Xₙ ⟶ X` compatible with the transitions `iₙ`, and let `(ℒₙ, φₙ)` be a compatible
system of invertible modules on the `Xₙ`. Granted that restriction along the tower is an
equivalence onto the systems of coherent modules along it — Grothendieck existence in the form of
[Stacks, Tag 088F] — there is a coherent `𝒪_X`-module `ℒ` and isomorphisms `ℒₙ ≅ ℒ|_{Xₙ}`
satisfying the compatibility clause of the theorem's conclusion.

The compatibility clause is not checked: it *is* the statement that the family `(ℒₙ ≅ ℒ|_{Xₙ})` is
a morphism in `Stacks.CoherentTower.ModuleSystem`, which is what essential surjectivity
produces. -/
public theorem exists_coherent_of_restriction_isEquivalence [IsNoetherianRing A]
    (fX : X ⟶ Spec (.of A)) [IsProper fX]
    (q : ∀ n : ℕ, Xn n ⟶ adicThickening A I n) (i : ∀ n : ℕ, Xn n ⟶ Xn (n + 1))
    (k : ∀ n : ℕ, Xn n ⟶ X) (hk : ∀ n : ℕ, i n ≫ k (n + 1) = k n)
    (hkcart : ∀ n : ℕ, IsPullback (k n) (q n) fX (adicThickeningι A I n))
    (L : ∀ n : ℕ, (Xn n).Modules) (hL : ∀ n : ℕ, IsInvertibleModule (Xn n) (L n))
    (φ : ∀ n : ℕ, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n)
    (hequiv : letI : ∀ n : ℕ, IsLocallyNoetherian (Xn n) :=
        fun n => isLocallyNoetherian_of_isPullback A I fX q k hkcart n
      (restriction i k hk).IsEquivalence) :
    ∃ M : X.Modules, _root_.SheafOfModules.IsCoherent.{u} M ∧
      ∃ e : ∀ n : ℕ, L n ≅ (Scheme.Modules.pullback (k n)).obj M,
        ∀ n : ℕ, (φ n).hom ≫ (e n).hom =
          (Scheme.Modules.pullback (i n)).map (e (n + 1)).hom ≫
            (Scheme.Modules.pullbackComp (i n) (k (n + 1))).hom.app M ≫
              (Scheme.Modules.pullbackCongr (hk n)).hom.app M := by
  let : ∀ n : ℕ, IsLocallyNoetherian (Xn n) :=
    fun n => isLocallyNoetherian_of_isPullback A I fX q k hkcart n
  let : (restriction i k hk).IsEquivalence := hequiv
  set S : ModuleSystem i := ofInvertible i L hL φ with hS
  set F := (restriction i k hk).objPreimage S with hF
  have eS : (restriction i k hk).obj F ≅ S := (restriction i k hk).objObjPreimageIso S
  refine ⟨F.obj, F.property, fun n => ModuleSystem.isoApp eS.symm n, fun n => ?_⟩
  exact (ModuleSystem.Hom.comm eS.symm.hom n).symm

/-- **[Stacks, Tag 01PT] in the shape the ampleness residue of [Stacks, Tag 089A] needs.** An
invertible `𝒪_X`-module some positive tensor power of which is ample is itself ample.

This is recorded here because it is the form in which the hypothesis `hample` of
`Stacks.AmpleFormalSystemLineBundle.exists_isAmple_of_restriction_isEquivalence` is reachable from
the source's own argument: the proof of [Stacks, Tag 089A] embeds `X` in `ℙᴺ_S` and so identifies
`ℒ ^⊗ d`, not `ℒ`, with the pullback of the hyperplane sheaf. -/
@[ega "II 4.5.6" "(i)"]
public lemma isAmple_of_exists_isAmple_tensorPowModule (M : X.Modules)
    [IsInvertibleModule X M]
    (h : ∃ d : ℕ, 1 ≤ d ∧ IsAmple X (tensorPowModule X M (d : ℤ))) : IsAmple X M := by
  obtain ⟨d, hd, hdample⟩ := h
  exact Stacks.RelativeVeryAmple.isAmple_of_isAmple_tensorPowModule M d hd hdample

/-- **The sheaf half of the conclusion of [Stacks, Tag 089A].** In the situation of
`Stacks.AmpleFormalSystemLineBundle.exists_coherent_of_restriction_isEquivalence`, with `ℒ₁` ample,
there is an **ample invertible** `𝒪_X`-module `ℒ` with isomorphisms `ℒₙ ≅ ℒ|_{Xₙ}` satisfying the
compatibility clause of the theorem's conclusion.

Three hypotheses carry what is not available in this library.

* `hequiv` is Grothendieck existence along the tower, [Stacks, Tag 088F].
* `hinvertible` says a coherent `𝒪_X`-module whose restriction to every member of the tower is
  invertible is invertible.
* `hample` says an invertible `𝒪_X`-module whose restriction to the closed member `X₁` is ample is
  ample; `Stacks.AmpleFormalSystemLineBundle.isAmple_of_exists_isAmple_tensorPowModule` reduces it
  to the ampleness of a positive tensor power, which is the form the source's projective embedding
  delivers.

The last two speak only of `X` and the tower, with no reference to the system `(ℒₙ, φₙ)`. -/
public theorem exists_isAmple_of_restriction_isEquivalence [IsNoetherianRing A]
    (fX : X ⟶ Spec (.of A)) [IsProper fX]
    (q : ∀ n : ℕ, Xn n ⟶ adicThickening A I n) (i : ∀ n : ℕ, Xn n ⟶ Xn (n + 1))
    (k : ∀ n : ℕ, Xn n ⟶ X) (hk : ∀ n : ℕ, i n ≫ k (n + 1) = k n)
    (hkcart : ∀ n : ℕ, IsPullback (k n) (q n) fX (adicThickeningι A I n))
    (L : ∀ n : ℕ, (Xn n).Modules) (hL : ∀ n : ℕ, IsInvertibleModule (Xn n) (L n))
    (φ : ∀ n : ℕ, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n)
    (hequiv : letI : ∀ n : ℕ, IsLocallyNoetherian (Xn n) :=
        fun n => isLocallyNoetherian_of_isPullback A I fX q k hkcart n
      (restriction i k hk).IsEquivalence)
    (hinvertible : ∀ M : X.Modules, _root_.SheafOfModules.IsCoherent.{u} M →
      (∀ n : ℕ, IsInvertibleModule (Xn n) ((Scheme.Modules.pullback (k n)).obj M)) →
      IsInvertibleModule X M)
    (hample : ∀ (M : X.Modules) (hM : IsInvertibleModule X M),
      @IsAmple (Xn 0) ((Scheme.Modules.pullback (k 0)).obj M)
        (isInvertibleModule_pullback (k 0) M hM) → @IsAmple X M hM)
    (hample0 : @IsAmple (Xn 0) (L 0) (hL 0)) :
    ∃ (M : X.Modules) (hM : IsInvertibleModule X M), @IsAmple X M hM ∧
      ∃ e : ∀ n : ℕ, L n ≅ (Scheme.Modules.pullback (k n)).obj M,
        ∀ n : ℕ, (φ n).hom ≫ (e n).hom =
          (Scheme.Modules.pullback (i n)).map (e (n + 1)).hom ≫
            (Scheme.Modules.pullbackComp (i n) (k (n + 1))).hom.app M ≫
              (Scheme.Modules.pullbackCongr (hk n)).hom.app M := by
  obtain ⟨M, hcoh, e, hcomp⟩ :=
    exists_coherent_of_restriction_isEquivalence A I fX q i k hk hkcart L hL φ hequiv
  have hM : IsInvertibleModule X M :=
    hinvertible M hcoh fun n => isInvertibleModule_of_iso (e n) (hL n)
  refine ⟨M, hM, hample M hM ?_, e, hcomp⟩
  let := hL 0
  let := isInvertibleModule_pullback (k 0) M hM
  exact (Stacks.RelativeVeryAmple.isAmple_congr (L 0)
    ((Scheme.Modules.pullback (k 0)).obj M) (e 0)).mp hample0

end Stacks.AmpleFormalSystemLineBundle

end

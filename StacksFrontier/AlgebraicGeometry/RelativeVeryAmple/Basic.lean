module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.AmpleLocallyClosed.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic

/-!
# Stacks 01VN and 01VU: relative ampleness from an immersion over the base

Stacks Tag 01VN says that a relatively very ample invertible module on a quasi-compact morphism is
relatively ample, and Stacks Tag 01VU compares relative ampleness of `L` with relative very
ampleness of its high tensor powers. Both go through relative very ampleness, Stacks Tag 01VM:
`L` is `f`-very ample when there are a quasi-coherent `𝒪_S`-module `E` and an immersion
`i : X ⟶ 𝐏(E)` over `S` with `L ≅ i^* 𝒪_{𝐏(E)}(1)`.

**The projective bundle `𝐏(E)` exists over an ARBITRARY base**, unconditionally for a
quasi-coherent `E`, as `Stacks.SymGraded.schemeProjectiveBundle` together with
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`, which discharges the hypothesis
that definition carries; over an affine base it is also
`Stacks.SymGraded.qcohProjectiveBundle` (`../SheafSymmetricAlgebra/Qcoh.lean`). What is
still missing for Tag 01VM is the twist `𝒪_{𝐏(E)}(1)`, and that needs **two** inputs; see "What
is not done" for both, stated exactly. What this file does instead is prove
the *content* of Tag 01VN with the projective bundle replaced by an arbitrary `S`-scheme carrying a
relatively ample invertible module, which is the only property of `𝐏(E)` and `𝒪(1)` that the
source's argument uses:

> relative ampleness is inherited by an immersion over the base.

That statement is `Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion`. It is
strictly more general than Tag 01VN, and it specialises to Tag 01VN the moment `𝐏(E)` is built and
`𝒪(1)` is known relatively ample on it. Combined with the relative half of Stacks Tag 01PT from the
sibling file `StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPower.lean`, it gives the
implications (2) ⟹ (1) and (3) ⟹ (2) ⟹ (1) of Stacks Tag 01VU.

## The one input that is not available, and why it is a hypothesis

`Stacks.RelativeVeryAmple.AmplePullbackGap` is **Stacks Tag 0B3E**: ampleness pulls back along an
immersion with quasi-compact source. Tag 0B3E is proved in this repository as
`Stacks.AmpleLocallyClosed.isAmple_modulePullback`, but only under three premises that nothing here
supplies — clause (1) ⟹ (3) of Tag 01Q3, Tag 0H78, and the consequence of Tag 01PV that Tag 01PX
consumes. Rather than repeat those three, this file names their joint consequence once and
discharges the rest; `Stacks.RelativeVeryAmple.amplePullbackGap_of_premises` proves, by elaboration
rather than by prose, that `AmplePullbackGap` follows from exactly those three and nothing else.

## Main definitions

* `Stacks.RelativeVeryAmple.AmplePullbackGap`: **Stacks Tag 0B3E**, the single named input that is
  missing.
* `Stacks.RelativeVeryAmple.HasRelativeTwistImmersion`: the hypothesis of Stacks Tag 01VN with
  `𝐏(E)` generalised — there are an `S`-scheme `P`, a relatively ample invertible `𝒪_P`-module `M`,
  and an immersion `i : X ⟶ P` over `S` with `L ≅ i^* M`.

## Main results

* `Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion`: **the content of
  Stacks Tag 01VN.** Relative ampleness is inherited by an immersion over the base, given Tag 0B3E.
* `Stacks.RelativeVeryAmple.isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowModule`:
  **the implication (2) ⟹ (1) of Stacks Tag 01VU.**
* `isRelativelyAmple_of_eventually_hasRelativeTwistImmersion_tensorPowModule`: **the implication
  (3) ⟹ (1) of Stacks Tag 01VU**, through (3) ⟹ (2).
* `Stacks.RelativeVeryAmple.exists_one_le_and_of_eventually`: the implication (3) ⟹ (2) of Stacks
  Tag 01VU, which the source discharges with "trivially (3) implies (2)". It holds for any
  predicate on the degree, so it uses nothing about very ampleness.
* `Stacks.RelativeVeryAmple.amplePullbackGap_of_premises`: `AmplePullbackGap` is Tag 0B3E and
  nothing more.

## The route of Tag 01VN, and where it differs from the source

The source proves Tag 01VN by building the graded map
`Sym(E) ⟶ ⨁ₙ f_* L^{⊗ n}`, passing to `f^* Sym(E) ⟶ ⨁ₙ L^{⊗ n}` by adjunction, identifying the
morphism it induces with `i`, and quoting part (6) of Tag 01VJ. None of that is reachable here:
Tag 01VJ is not proved (see "What is not done" in
`StacksFrontier/AlgebraicGeometry/RelativeAmple/Basic.lean`) and neither is the graded section ring.

The argument below is the direct one against the repository's definition of relative ampleness,
which quantifies over the affine opens of the base. Fix an affine open `V ⊆ S`. Writing
`W = p⁻¹(V)` and `U = i⁻¹(W)`:

* `U` is `f⁻¹(V)` **on the nose** — `(i ≫ p) ⁻¹ᵁ V` and `i ⁻¹ᵁ (p ⁻¹ᵁ V)` are the same open by
  `rfl`. This is why the theorem is proved for `f = i ≫ p` and the general `f` is reached
  by substituting the hypothesis `i ≫ p = f`, whose left-hand side is then a variable: no transport
  across an equality of open subschemes is needed anywhere.
* `U` is quasi-compact, from quasi-compactness of `f` and affineness of `V`.
* `i ∣_ W : U ⟶ W` is an immersion, by Mathlib's instance on `morphismRestrict`, which is the base
  change of `i` along `W.ι`.
* `M` restricted to `W` is ample, which is what relative ampleness of `M` says at `V`.
* `U.ι^* L ≅ (i ∣_ W)^* (W.ι^* M)`, from `L ≅ i^* M` and
  `AlgebraicGeometry.morphismRestrict_ι : i ∣_ W ≫ W.ι = U.ι ≫ i`, read through the pullback
  pseudofunctor.

Tag 0B3E then gives ampleness of `(i ∣_ W)^* (W.ι^* M)` on `U`, and
`Stacks.RelativeVeryAmple.isAmple_congr` moves it onto `U.ι^* L`.

## Implementation notes

**The witness is an existential, not a structure, so that `i ≫ p = f` can be substituted.** The
proof opens by `subst`ing that equation, which is only possible because `f` is a variable of the
theorem; a bundled structure would make `w.over` an equation between two closed terms and force the
open-subscheme transport the previous section avoids.

**Two invertibility instances have to be supplied by hand.** `IsInvertibleModule` is
found for a single pullback `i^* L` and for a single tensor power `L ^⊗ d`, but the *nested* cases
— `tensorPowModule` of a pullback, and a pullback of a pullback — are **not** synthesized, while
the corresponding explicit applications of `Stacks.Ample.isInvertibleModule_tensorPowModule` and
`Stacks.InvertiblePullback.isInvertibleModule_pullback` typecheck immediately. The instance binders
of `Stacks.RelativeVeryAmple.isAmple_congr` are therefore named, and are passed as `(hN' := …)`
rather than by counting `@` positions.

**The composition isomorphism is the pseudofunctor's.**
`Stacks.PullbackPseudofunctor.modulePullbackCompIso f f' : (f' ≫ f)^* ≅ f^* ⋙ f'^*` is stated for
ringed spaces; `(g ≫ h).toLRSHom.toShHom = g.toLRSHom.toShHom ≫ h.toLRSHom.toShHom` holds by `rfl`
for schemes, so its components are used at the scheme spelling with no bridge. The
equality of morphisms `U.ι ≫ i = i ∣_ W ≫ W.ι` is carried by an `eqToIso` built with `congrArg`,
composed in `Iso` and never asked to convert.

## What is not done

**Stacks Tag 01VM is not stated, and what blocks it is the twist.** Its
definition quantifies over `𝐏(E)` and over `𝒪_{𝐏(E)}(1)`. The first is available: for a
quasi-coherent `E` on an arbitrary scheme, `Stacks.SymGraded.schemeProjectiveBundle` with its
hypothesis discharged by `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent` is
`Proj_S(Sym(E))` with its projection and its affine `Proj` charts, and a closed immersion into
it over the base is `AlgebraicGeometry.IsProjective`
(`StacksFrontier/AlgebraicGeometry/Morphisms/Projective/Basic.lean`), the first condition of Tag
01W8.

The second is not. The glued twist exists as
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist`, with its chart identifications,
and is conditional on one unproved statement,
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` — the cocycle for Tag 01NO's
twist comparison along a nested chain `W ⊆ W' ⊆ U` of affine opens of the base. That hypothesis is
stated **in one integer degree**, so what Tag 01VM needs is its single instance `n = 1`.

Its route is a rigidity statement applied to one leg composed with the inverse of the other, and
**multiplicativity of that composite is not needed**: relative rigidity in
degree one is available with no multiplicativity hypothesis at all, as
`Stacks.AlgebraicGeometry.TwistRigidityDegreeOne.eq_id_res`, whose only extra input is that the
graded ring of sections over the smaller affine open have a nonvanishing degree-one element at
each point of its `Proj`. In particular the transport of Tag 01MY's multiplicativity through the
four factors of `pushNested` is not needed in degree one.

The first step of the section computation **is proved**: Tag 01NO's *named* comparison
morphism on a pulled-back homogeneous global section is
`Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.projInclusionTwistMap_degreeSection`, in
`StacksFrontier/AlgebraicGeometry/ProjInclusionDegreeSection/Basic.lean`.
What is still owed on the section side is the same identity for `cmpNested`, over an open of the
relative Proj.

**Two inputs remain between here and a `𝒪_{𝐏(E)}(1)`, not one.**

* the cocycle itself, `IsNestedCocycle (Sym(E)) 1`. Its section half is the identity above read
  through `pushNested`; the structural half is to regroup `pushNested` so that Tag 01NO's twist
  comparison comes *before* the two pushforward factors, which makes the unit occurring in it the
  unit of the pullback--pushforward adjunction rather than of
  `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. The latter is built by a tactic block, so
  projecting its unit in a statement at that instance is unaffordable; see the implementation
  notes of `StacksFrontier/AlgebraicGeometry/ChartTransNonNested/RelativeProj.lean`;
* the **geometric** half, `Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne` for
  `Stacks.SymGraded.schemeSheafGradedAlgebra`, which is what supplies the nonvanishing degree-one
  element that rigidity asks for. **This half is proved** —
  `Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra`
  (`SheafSymmetricAlgebra/GeneratedInDegreeOne.lean:312`), with
  `Stacks.SymGraded.exists_degreeOne_notMem` at `:326`.
  It is not a formality, and the argument is worth recording: over an affine open `U` the
  predicate asks that `Γ(U, Sym^n E)` be generated by products of `Γ(U, E)`, and the obstacle was
  thought to be multiplicativity of the affine comparison
  `Stacks.SymGraded.AffinePieces.sheafificationIsoTilde`. It is not needed — what the argument uses
  is multiplicativity of the **sheafification unit**, which was already proved. So of the two
  blockers this file names for Tag 01VM, only the cocycle `IsNestedCocycle (Sym E) 1` remains.

`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` — Tag 01NR's full structure, which also
asks for the multiplication, the unit and the homogeneous-section map of the graded algebra
`⨁ₙ 𝒪(n)` — is owed beyond both but is not needed to state Tag 01VM.

**Tag 01VM is therefore still not stated, and it is deliberately not stated conditionally.** A
definition reading `∃ E, ∃ (hcoc : IsNestedCocycle _ 1), ∃ i, L ≅ i^* (gluedTwist _ 1 hcoc)` would
compile, would carry the tag, and would be unusable and uncheckable: a reader cannot tell whether
it is satisfiable, and the existential over `hcoc` silently makes the tag depend on an unproved
statement. The tag goes on once `𝒪_{𝐏(E)}(1)` is a term.

**Two things are not obstructions.** Tag `01I8__symmetric_power` is formalized, and the base
change of a symmetric power, `B ⊗[A] Sym^n_A M ≅ Sym^n_B (B ⊗[A] M)`, is
`SymPow.baseChangeEquiv`; its geometric form
is `Stacks.SymGraded.isBaseChange_gradedRestrictₗ_int`
(`../SheafSymmetricAlgebra/BaseChange.lean`); it is exactly what
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent` is proved from.

Defining a projective bundle with *unconstrained* fields would make relative very ampleness
satisfiable by `P = X`, `M = L`, `i = 𝟙`, which is why no such definition is introduced here: it
would be a weakening of the statement, not a generalisation of it. That is also why
`Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` is **not** offered as a reading of Tag
01VM and carries no tag of it: `Stacks.RelativeVeryAmple.hasRelativeTwistImmersion_self` shows
that every relatively ample invertible module satisfies it, so as a definition it would be that
weakening. It is used here only as a *hypothesis*, where being weaker makes Tag 01VN's content
stronger.

**The implication (1) ⟹ (3) of Stacks Tag 01VU is not proved here**; it is
`Stacks.VeryAmplePowersQuasiCompactBase.eventuallyVeryAmplePower_of_isRelativelyAmple`, and the
whole of Tag 01VU is `Stacks.VeryAmplePowersQuasiCompactBase.tfae`, both in
`StacksFrontier/AlgebraicGeometry/VeryAmplePowersQuasiCompactBase/Basic.lean`. As in the source, it
takes Tag 01VT over each member of a finite affine cover of the base and glues by Tag 01VR
(`Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_cover`).

**Tag 01VU's finite-type hypothesis is not used.** The tag states conditions (1)–(3) under
`CompactSpace S`, `LocallyOfFiniteType f` and `QuasiCompact f`. The two implications proved here
need only `QuasiCompact f`, and (2) ⟹ (1) needs nothing at all beyond the hypotheses of Tag 01VN,
so they are stated without the unused ones.

## References

* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VU](https://stacks.math.columbia.edu/tag/01VU)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [EGA II, Proposition 4.6.2]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample

universe u

namespace Stacks.RelativeVeryAmple

/-! ### Stacks Tag 0B3E as a named hypothesis -/

/-- **Stacks Tag 0B3E**, the one input the argument below needs and the repository does not have:
ampleness pulls back along an immersion with quasi-compact source. It is proved in
`StacksFrontier/AlgebraicGeometry/AmpleLocallyClosed/Basic.lean` under three premises that nothing
here supplies, and `Stacks.RelativeVeryAmple.amplePullbackGap_of_premises` shows this is their
joint consequence. -/
def AmplePullbackGap : Prop :=
  ∀ (A B : Scheme.{u}) (j : A ⟶ B) (N : B.Modules) [IsInvertibleModule B N],
    IsImmersion j → CompactSpace A → IsAmple B N →
      IsAmple A ((modulePullback j.toLRSHom.toShHom).obj N)

/-- **`Stacks.RelativeVeryAmple.AmplePullbackGap` is Stacks Tag 0B3E and nothing more.** It follows
from the three premises `Stacks.AmpleLocallyClosed.isAmple_modulePullback` is stated with — clause
(1) ⟹ (3) of Tag 01Q3, Tag 0H78, and the Tag 01PV consequence Tag 01PX consumes — each taken for
every scheme and every invertible module, and from nothing else. -/
theorem amplePullbackGap_of_premises
    (hbasis : ∀ (B : Scheme.{u}) (N : B.Modules) [IsInvertibleModule B N],
      IsAmple B N → Stacks.AmpleTheory.IsBasisNonvanishing B N)
    (hsect : ∀ (A B : Scheme.{u}) (j : A ⟶ B) (N : B.Modules) [IsInvertibleModule B N],
      ∃ φ : ∀ n : ℕ, Γ(tensorPowModule B N (n : ℤ), ⊤) →
          Γ(tensorPowModule A (Stacks.AmpleLocallyClosed.pullbackModule j N) (n : ℤ), ⊤),
        Stacks.AmpleLocallyClosed.SectionPullbackCompatible j N φ)
    (haff : ∀ (A B : Scheme.{u}) (j : A ⟶ B) (N : B.Modules) [IsInvertibleModule B N],
      Stacks.AmpleTheory.IsAffineOfLeAffine A
        (Stacks.AmpleLocallyClosed.pullbackModule j N)) :
    AmplePullbackGap.{u} := by
  intro A B j N _ hj hA hN
  obtain ⟨φ, hφ⟩ := hsect A B j N
  exact Stacks.AmpleLocallyClosed.isAmple_modulePullback j N hN (Or.inr (Or.inl ⟨hA, hj⟩))
    (hbasis B N hN) hφ (haff A B j N)

/-! ### The hypothesis of Stacks Tag 01VN, with the projective bundle generalised -/

/-- **The hypothesis of Stacks Tag 01VN with `𝐏(E)` replaced by an arbitrary `S`-scheme carrying a
relatively ample invertible module.** There are a scheme `P` over `S`, an invertible `𝒪_P`-module
`M` that is ample relative to the structure morphism of `P`, and an immersion `i : X ⟶ P` over `S`
with `L ≅ i^* M`.

Relative very ampleness, Stacks Tag 01VM, is the case `P = 𝐏(E)` and `M = 𝒪(1)`; it implies this
condition as soon as `𝒪(1)` is built and is known relatively ample on `𝐏(E)`, and those are the
only two properties of the bundle the source's argument uses. The bundle itself is available
(`Stacks.SymGraded.schemeProjectiveBundle`) but its twist is not — see the module documentation
— so this is the form in which Tag 01VN's content is proved.

This condition is *strictly weaker* than Tag 01VM, by
`Stacks.RelativeVeryAmple.hasRelativeTwistImmersion_self`, and is therefore not a reading of
that tag; it is a hypothesis, under which Tag 01VN's conclusion is proved for more than Tag
01VM's hypothesis supplies. -/
def HasRelativeTwistImmersion {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] : Prop :=
  ∃ (P : Scheme.{u}) (p : P ⟶ S) (M : P.Modules) (hM : IsInvertibleModule P M) (i : X ⟶ P),
    letI : IsInvertibleModule P M := hM
    IsImmersion i ∧ i ≫ p = f ∧ Stacks.RelativeAmple.IsRelativelyAmple p M ∧
      Nonempty (L ≅ (modulePullback i.toLRSHom.toShHom).obj M)

/-- `Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` is satisfiable: the identity immersion
exhibits a relatively ample module as one.

Recorded for two reasons. It shows the hypothesis of
`Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion` is not vacuous; and it
shows that the hypothesis is *exactly as strong as its own conclusion*, so it must not be read as
Stacks Tag 01VM — relative very ampleness does not hold of every relatively ample invertible
module, and a definition of it satisfied by `P = X`, `M = L`, `i = 𝟙` would be a weakening. The
predicate below is therefore a hypothesis and never a definition of that tag. -/
theorem hasRelativeTwistImmersion_self {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (h : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    HasRelativeTwistImmersion f L := by
  refine ⟨X, f, L, ‹IsInvertibleModule X L›, 𝟙 X, inferInstance, Category.id_comp f, h, ⟨?_⟩⟩
  exact (Stacks.PullbackPseudofunctor.modulePullbackIdIso X.toRingedSpace).symm.app L

/-! ### The content of Stacks Tag 01VN -/

/-- **The iterated module pullback along two morphisms is the pullback along their composite**,
`a^* (b^* M) ≅ (a ≫ b)^* M`. This is
`Stacks.PullbackPseudofunctor.modulePullbackCompIso` at `M`, with the identification
`(a ≫ b).toLRSHom.toShHom = a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom` — which holds by `rfl` for
schemes — done once, here, and never again. -/
def modulePullbackPairIso {A B D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D) (M : D.Modules) :
    (modulePullback a.toLRSHom.toShHom).obj ((modulePullback b.toLRSHom.toShHom).obj M) ≅
      (modulePullback (a ≫ b).toLRSHom.toShHom).obj M :=
  ((Stacks.PullbackPseudofunctor.modulePullbackCompIso b.toLRSHom.toShHom
    a.toLRSHom.toShHom).app M).symm

/-- Equal morphisms have equal module pullbacks. An `eqToIso`, only ever composed. -/
def modulePullbackEqIso {A D : Scheme.{u}} {g g' : A ⟶ D} (h : g = g') (M : D.Modules) :
    (modulePullback g.toLRSHom.toShHom).obj M ≅
      (modulePullback g'.toLRSHom.toShHom).obj M :=
  eqToIso (congrArg (fun k : A ⟶ D => (modulePullback k.toLRSHom.toShHom).obj M) h)

/-- **A commuting square of schemes gives an isomorphism of iterated module pullbacks**,
`a^* (b^* M) ≅ c^* (d^* M)` whenever `a ≫ b = c ≫ d`. Both sides are the pullback along that one
morphism.

Stated for four arbitrary morphisms, and assembled from the three isomorphisms above rather than
written as one composite, for two reasons. With the morphisms opaque every step is
immediate, whereas instantiated at `AlgebraicGeometry.morphismRestrict` the identification
`(i ∣_ W ≫ W.ι).toLRSHom.toShHom = (i ∣_ W).toLRSHom.toShHom ≫ W.ι.toLRSHom.toShHom` exhausts the
heartbeat budget, `morphismRestrict` being a composite of a pullback cone isomorphism with a
projection. And each of the three steps elaborates on its own in well under the budget while the
single composite `≪≫` chain does not, so the intermediate objects are pinned by the types of the
three declarations instead of being left to unification. -/
def pullbackSquareIso {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (hsq : a ≫ b = c ≫ d) (M : D.Modules) :
    (modulePullback a.toLRSHom.toShHom).obj ((modulePullback b.toLRSHom.toShHom).obj M) ≅
      (modulePullback c.toLRSHom.toShHom).obj ((modulePullback d.toLRSHom.toShHom).obj M) :=
  (modulePullbackPairIso a b M).trans
    ((modulePullbackEqIso hsq M).trans (modulePullbackPairIso c d M).symm)

/-- **The restriction of a pullback along an immersion is the pullback along the restricted
immersion**, `U.ι^* (i^* M) ≅ (i ∣_ W)^* (W.ι^* M)` for `U = i⁻¹(W)`. This is
`Stacks.RelativeVeryAmple.pullbackSquareIso` at the square
`AlgebraicGeometry.morphismRestrict_ι`. -/
def restrictPullbackIso {X P : Scheme.{u}} (i : X ⟶ P) (W : P.Opens) (M : P.Modules) :
    (modulePullback (i ⁻¹ᵁ W).ι.toLRSHom.toShHom).obj
        ((modulePullback i.toLRSHom.toShHom).obj M) ≅
      (modulePullback (i ∣_ W).toLRSHom.toShHom).obj
        ((modulePullback W.ι.toLRSHom.toShHom).obj M) :=
  pullbackSquareIso (i ⁻¹ᵁ W).ι i (i ∣_ W) W.ι (morphismRestrict_ι i W).symm M

/-- **The local step of Stacks Tag 01VN.** Let `i : X ⟶ P` be an immersion, `W` an open of `P` on
which an invertible `𝒪_P`-module `M` is ample, and suppose `i⁻¹(W)` is quasi-compact. Then a module
isomorphic to `i^* M` is ample on `i⁻¹(W)` after restriction.

Tag 0B3E, in the form `Stacks.RelativeVeryAmple.AmplePullbackGap`, is applied to the restricted
immersion `i ∣_ W`, which Mathlib knows is an immersion; the conclusion is moved onto the
restriction of `L` by `Stacks.RelativeVeryAmple.restrictPullbackIso` and
`Stacks.RelativeVeryAmple.isAmple_congr`. -/
theorem isAmple_restrict_of_immersion (hgap : AmplePullbackGap.{u}) {X P : Scheme.{u}}
    (i : X ⟶ P) [IsImmersion i] (W : P.Opens) (M : P.Modules) [IsInvertibleModule P M]
    (L : X.Modules) [IsInvertibleModule X L]
    (e : L ≅ (modulePullback i.toLRSHom.toShHom).obj M)
    (hW : IsAmple W.toScheme ((modulePullback W.ι.toLRSHom.toShHom).obj M))
    (hc : CompactSpace (i ⁻¹ᵁ W).toScheme) :
    IsAmple (i ⁻¹ᵁ W).toScheme
      ((modulePullback (i ⁻¹ᵁ W).ι.toLRSHom.toShHom).obj L) := by
  refine (isAmple_congr _ _
    (hN' := Stacks.InvertiblePullback.isInvertibleModule_pullback (i ∣_ W) _)
    ((modulePullback (i ⁻¹ᵁ W).ι.toLRSHom.toShHom).mapIso e ≪≫
      restrictPullbackIso i W M)).mpr ?_
  exact hgap _ _ (i ∣_ W) _ inferInstance hc hW

/-- **The content of Stacks Tag 01VN: relative ampleness is inherited by an immersion over the
base.** If `L` is isomorphic to the pullback along an immersion `i : X ⟶ P` over `S` of a module
ample relative to `P ⟶ S`, and `f` is quasi-compact, then `L` is ample relative to `f`.

Stacks Tag 01VN is the case `P = 𝐏(E)`, `M = 𝒪(1)`; the twist `𝒪(1)` has no library form, so
this is the general statement instead — see the module documentation. The hypothesis
`Stacks.RelativeVeryAmple.AmplePullbackGap` is Stacks Tag 0B3E.

Everything local to an affine open `V` of the base is
`Stacks.RelativeVeryAmple.isAmple_restrict_of_immersion` at `W = p⁻¹(V)`; what is left here is that
`i⁻¹(p⁻¹(V))` is `f⁻¹(V)` — the same open by `rfl` once `f` has been replaced by `i ≫ p` — and that
it is quasi-compact. -/
theorem isRelativelyAmple_of_hasRelativeTwistImmersion (hgap : AmplePullbackGap.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    (hf : QuasiCompact f) (h : HasRelativeTwistImmersion f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨P, p, M, hM, i, him, hover, hMample, ⟨e⟩⟩ := h
  let _ : IsInvertibleModule P M := hM
  let _ : IsImmersion i := him
  subst hover
  refine ⟨hf, fun V hV => ?_⟩
  exact isAmple_restrict_of_immersion hgap i (p ⁻¹ᵁ V) M L e (hMample.2 V hV)
    (isCompact_iff_compactSpace.mp (quasiCompact_iff_forall_isAffineOpen.mp hf V hV))

/-! ### Stacks Tag 01VU -/

/-- **The implication (3) ⟹ (2) of Stacks Tag 01VU**, which the source discharges with "trivially
(3) implies (2)": a property holding in all sufficiently high degrees holds in some positive
degree. Nothing about very ampleness enters, so it is stated for an arbitrary predicate on the
degree. -/
theorem exists_one_le_and_of_eventually {Q : ℕ → Prop} (h : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → Q d) :
    ∃ d : ℕ, 1 ≤ d ∧ Q d := by
  obtain ⟨d₀, h⟩ := h
  exact ⟨max d₀ 1, le_max_right _ _, h _ (le_max_left _ _)⟩

/-- **The implication (2) ⟹ (1) of Stacks Tag 01VU.** If some positive tensor power of `L` admits
an immersion over the base onto a relatively ample module — in particular, if it is relatively very
ample — then `L` is ample relative to `f`.

This is Tag 01VN applied to `L ^⊗ d`, which gives relative ampleness of that power, followed by the
relative half of Tag 01PT,
`Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule`.
Quasi-compactness of `f` is the only hypothesis of the source's finite-type assumption that is
used. -/
theorem isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowModule
    (hgap : AmplePullbackGap.{u}) {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d : ℕ, 1 ≤ d ∧
      HasRelativeTwistImmersion f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨d, hd, hVA⟩ := h
  exact isRelativelyAmple_of_isRelativelyAmple_tensorPowModule f L d hd
    (isRelativelyAmple_of_hasRelativeTwistImmersion hgap f _ hf hVA)

/-- **The implication (3) ⟹ (1) of Stacks Tag 01VU**, through (3) ⟹ (2): if all sufficiently high
tensor powers of `L` admit an immersion over the base onto a relatively ample module — in
particular, if all of them are relatively very ample — then `L` is ample relative to `f`. -/
theorem isRelativelyAmple_of_eventually_hasRelativeTwistImmersion_tensorPowModule
    (hgap : AmplePullbackGap.{u}) {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      HasRelativeTwistImmersion f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowModule hgap f L hf
    (exists_one_le_and_of_eventually h)

end Stacks.RelativeVeryAmple

end

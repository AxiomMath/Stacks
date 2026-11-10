module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelLimitPAdicComplete
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceLevelScalars

/-!
# Item (07JB) at the site: the module `M = lim_e Γ(T_e, ℱ)` is `p`-adically complete

`StacksFrontier/AlgebraicGeometry/Crystalline/LevelLimitPAdicComplete.lean` proves item (07JB) of
[Stacks, Lemma 60.17.3, Tag 07JG] at the level of modules:
`Crystalline.isPAdicallyComplete_invLimit_of_shift` says that the limit of a tower of `D`-modules
whose level `n` is annihilated by `p^{N + n}` is `p`-adically complete.  It assumes nothing about
the transition maps — not surjectivity, and not the crystal relation
`M_e = M_{e + 1} / p^e M_{e + 1}` the source's own proof uses.  Its module note records the two
things that stood between it and the field
`Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG.isPAdicallyComplete`, and
this module supplies both.

The first is a `D`-linear identification.  `...SmallSite.LevelScalars07JG.sections F` is the
limit `...SmallSite.levelSectionsLimit`, an `AddSubgroup` of `∏_e Γ(T_e, ℱ)` whose factors are
modules over *different* section rings, carrying the `D`-action of
`...SmallSite.instModuleLevelSectionsLimit` restricted along `...LevelScalars07JG.ringEquiv`;
`Crystalline.invLimit` is a `Submodule` of a product of `D`-modules.  Two steps bridge them.  The
factors are made `D`-modules by the reductions `D ⟶ Γ(T_e, 𝒪)` read off `ringEquiv`, which is
`...SmallSite.LevelScalars07JG.levelRingHom`; and the limit predicates are reconciled, the one of
`...SmallSite.levelSectionsLimit` quantifying over every `e ⟶ e'` of `ℕ` and the one of
`Crystalline.invLimit` only over the successors.  That is the cofinality step
`...SmallSite.mem_levelSectionsLimit_of_succ`, an induction on the number of steps between two
levels.

The second is the annihilation itself, and it is *proved* rather than assumed: the level `e` of
`...SmallSite.wholeSpaceSystem` has section ring `D(n)/(p)^{N + e}` by
`...SmallSite.wholeSpaceSystemLevelRingEquiv`, so the reduction of `p^{N + e}` to it vanishes, and
with it the action of `p^{N + e}` on the sections of *any* coefficient sheaf over that level.  The
exponent is `N + e = ...SmallSite.wholeSpaceLevelExponent hp e` with
`N = Crystalline.uniformLevel (...affineSituation S hp)`, matching the shift of
`Crystalline.isPAdicallyComplete_invLimit_of_shift` exactly; the unshifted
`Stacks.AdicCompletion.InverseLimit.invLimit_isAdicComplete` of [Stacks, Tag 0G1Q] would ask for
`p^e`, which at `e = 0` reads `Γ(T_0, ℱ) = 0`.

## Main definitions

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `LevelScalars07JG.levelRingHom` — the reduction `D ⟶ Γ(T_e, 𝒪_{T_e})` of the scalars to a
  level, read off `...LevelScalars07JG.ringEquiv`.
* `LevelScalars07JG.levelSections` — `Γ(T_e, ℱ)` as a `D`-module, by restriction of scalars
  along that reduction.
* `LevelScalars07JG.levelRestrict` — the restriction `Γ(T_{e + 1}, ℱ) ⟶ Γ(T_e, ℱ)`, which is
  `D`-linear because `D` acts through one and the same compatible family of scalars.

## Main results

* `mem_levelSectionsLimit_of_succ` — **the cofinality step**: a family of sections compatible
  with the one-step restrictions is compatible with all of them.
* `LevelScalars07JG.sectionsInvLimitEquiv` — **the `D`-linear identification**
  `M = lim_e Γ(T_e, ℱ) ≃ₗ[D] Crystalline.invLimit`, which is what item (07JB) is stated about.
* `LevelScalars07JG.isPAdicallyComplete_sections` — **item (07JB) at the site**, for an arbitrary
  system of levels whose level `e` is annihilated by `p^{N + e}`.
* `pow_smul_eq_zero_wholeSpaceLevelSections` — **the annihilation for the system of
  [Stacks, Proposition 60.21.1, Tag 07JN]**: `p^{N + e}` kills every section of every coefficient
  sheaf over the level `e`, because it already dies in the section ring `D(n)/(p)^{N + e}`.
* `isPAdicallyComplete_wholeSpaceLevelScalars_sections` — **the field
  `...SmallSite.LevelComparison07JG.isPAdicallyComplete` discharged** over
  `...SmallSite.wholeSpaceLevelScalars hp n` at `p = S.p`: every crystal in quasi-coherent
  `𝒪_{X/S}`-modules has `p`-adically complete module of sections over the system of
  [Stacks, Tag 07JN].
* `levelComparison07JGWholeSpaceOfRemaining` — the field exhibited as discharged: a
  `...SmallSite.LevelComparison07JG` over those scalars is assembled from its *other* five
  fields.

## What is and is not proved

**[Stacks, Tag 07JG] as a whole is not proved here**: the functor of the tag, which carries
`@[stacks 07JG]`, is `...SmallSite.crystalPairFunctor` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalPairFunctor07JG.lean`.  What is
proved here is its **item (07JB) for the source category the tag itself goes out of**: the
crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`.
`isPAdicallyComplete_wholeSpaceLevelScalars_sections` quantifies over
`...SmallSite.QuasiCoherentCrystal` and over nothing else — no reduction datum, no index type, no
basis — and its hypotheses are the source's own: Situation [Stacks, Tag 07MD] with `X` and `S`
affine and `p` nilpotent on `Γ(X, 𝒪_X)`.  The system of levels it takes the limit over is the one
the source's proof takes it over, the degree `n` member of `...SmallSite.wholeSpaceSystem` of
[Stacks, Tag 07JN], so the module it is about is the tag's own `M = lim_e Γ(T(n)_e, ℱ)`.

One might decline the attribute on the ground that (07JB) is a clause of the
hypothesis bundle `...SmallSite.Reduction07JG`, of which every producer in the library consumes a
datum of its own, so that a statement quantifying over one could be vacuous.  That ground applies
to statements that do quantify over such a bundle — and this one does not.  Item (07JB) is also
registered, in its purely algebraic form about `Crystalline.invLimit`, by
`Crystalline.isPAdicallyComplete_invLimit_of_shift` of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelLimitPAdicComplete.lean`; what this module adds
to the covering set is the same item with a crystal, and not a module, for its subject.

The other clauses of the tag are untouched: see the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceLevelScalars.lean`.  In particular
(07JB) here does **not** use
`...SmallSite.IsCrystalLevelQuotient`, the relation `M_e = M_{e + 1}/p^e M_{e + 1}` the source
argues through, nor surjectivity of the restriction maps.

The other five fields of `...SmallSite.LevelComparison07JG` are untouched here, and
`...SmallSite.levelComparison07JGWholeSpaceOfRemaining` carries them as hypotheses:
`comparison` and `comparison_naturality`, available at the structure sheaf by
`...SmallSite.LevelScalars07JG.comparisonUnit`, and `hasCoordinateOperators`, `isIntegrable` and
`isTopologicallyQuasiNilpotent`, which are items (07JD) and (07JE) with the non-vacuity of the
last two.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 0G1Q](https://stacks.math.columbia.edu/tag/0G1Q)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u uI

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {T : ℕ ⥤ CrystallineThickening S}
  {F : QuasiCoherentCrystal S}

/-! ### Cofinality: compatibility with the one-step restrictions suffices -/

/-- **A family of sections compatible with the one-step restrictions of the system restricts
correctly between any two levels.**  Induction on the number of steps, with
`...SmallSite.levelRestrict_comp` the single ingredient. -/
theorem levelRestrict_eq_of_succ (s : ∀ e : ℕ, F.obj.val.obj (op (T.obj e)))
    (hs : ∀ e : ℕ, F.obj.val.map (T.map (homOfLE (Nat.le_succ e))).op (s (e + 1)) = s e)
    {e e' : ℕ} (hle : e ≤ e') :
    F.obj.val.map (T.map (homOfLE hle)).op (s e') = s e := by
  induction e', hle using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl e) : e ⟶ e) = 𝟙 e from rfl, T.map_id, op_id,
      PresheafOfModules.map_id]
    rfl
  | succ e' hee' ih =>
    have hcomp := levelRestrict_comp (T := T) (F := F) (homOfLE hee')
      (homOfLE (Nat.le_succ e')) (s (e' + 1))
    rw [hs e', ih] at hcomp
    exact hcomp.symm

/-- **The cofinality step.**  `Crystalline.invLimit` asks a family to be compatible with the
one-step transition maps only, whereas
`...SmallSite.levelSectionsLimit` asks it to be compatible with every morphism `e ⟶ e'` of `ℕ`.
The two conditions agree: the successors are cofinal, by
`...SmallSite.levelRestrict_eq_of_succ`. -/
theorem mem_levelSectionsLimit_of_succ (s : ∀ e : ℕ, F.obj.val.obj (op (T.obj e)))
    (hs : ∀ e : ℕ, F.obj.val.map (T.map (homOfLE (Nat.le_succ e))).op (s (e + 1)) = s e) :
    s ∈ levelSectionsLimit S T F :=
  fun {_ _} h ↦ levelRestrict_eq_of_succ s hs (leOfHom h)

/-! ### The levels of a crystal as `D`-modules -/

namespace LevelScalars07JG

variable {D : DividedPowerRing.{u}} (L : LevelScalars07JG S D)

/-- **The reduction of `D` to the section ring of the level `e`.**  The identification `ringEquiv`
presents an element of `D` as a compatible family of sections of `𝒪_{X/S}` over the levels, and
this is its `e`-th member.  For the system of [Stacks, Tag 07JN] it is
`...SmallSite.levelReductionRingHom`, the quotient map `D(n) ⟶ D(n)/(p)^{N + e}` read through
`...SmallSite.wholeSpaceSystemLevelRingEquiv`. -/
def levelRingHom (e : ℕ) :
    (D : Type u) →+* (structureSheaf S).obj.obj (op (L.levelSystem.obj e)) :=
  ((Pi.evalRingHom
        (fun e : ℕ ↦ ((structureSheaf S).obj.obj (op (L.levelSystem.obj e)) : Type u)) e).comp
      (levelRingLimit S L.levelSystem).subtype).comp L.ringEquiv.toRingHom

/-- The reduction of `a : D` to the level `e` is the `e`-th member of the family `ringEquiv a`. -/
@[simp] theorem levelRingHom_apply (e : ℕ) (a : (D : Type u)) :
    L.levelRingHom e a = (L.ringEquiv a).val e :=
  rfl

/-- **The sections of a crystal over the level `e`, as a `D`-module.**  The sections are a module
over the section ring `Γ(T_e, 𝒪_{T_e})`, and `D` acts through
`...SmallSite.LevelScalars07JG.levelRingHom`.  This is a type synonym rather than an instance on
the sections themselves because the action depends on `ringEquiv`, which is a field.

It is *not* `...SmallSite.levelSectionsModule`, which makes the sections over one level a module
over one completed envelope `D(n)` for the system of [Stacks, Tag 07JN] specifically; here the
system of levels and the identification of `D` with the limit of its section rings are
arbitrary. -/
def levelSections (F : QuasiCoherentCrystal S) (e : ℕ) : Type u :=
  F.obj.val.obj (op (L.levelSystem.obj e))

/-- The sections `Γ(T_e, ℱ)` over the level `e` form an additive commutative group. -/
instance instAddCommGroupLevelSections (F : QuasiCoherentCrystal S) (e : ℕ) :
    AddCommGroup (L.levelSections F e) :=
  inferInstanceAs (AddCommGroup (F.obj.val.obj (op (L.levelSystem.obj e))))

/-- The sections `Γ(T_e, ℱ)` are a module over the section ring `Γ(T_e, 𝒪_{T_e})`. -/
instance instModuleSectionsLevelSections (F : QuasiCoherentCrystal S) (e : ℕ) :
    Module ((structureSheaf S).obj.obj (op (L.levelSystem.obj e))) (L.levelSections F e) :=
  inferInstanceAs
    (Module ((structureSheaf S).obj.obj (op (L.levelSystem.obj e)))
      (F.obj.val.obj (op (L.levelSystem.obj e))))

/-- The sections `Γ(T_e, ℱ)` are a `D`-module, with `D` acting through `levelRingHom e`. -/
instance instModuleLevelSections (F : QuasiCoherentCrystal S) (e : ℕ) :
    Module (D : Type u) (L.levelSections F e) :=
  Module.compHom (L.levelSections F e) (L.levelRingHom e)

/-- An element `a` of `D` acts on a section over the level `e` as the `e`-th member of the family
`ringEquiv a`. -/
theorem levelSections_smul_def (F : QuasiCoherentCrystal S) (e : ℕ) (a : (D : Type u))
    (x : L.levelSections F e) :
    a • x = (L.ringEquiv a).val e • x :=
  rfl

/-- **The restriction `Γ(T_{e + 1}, ℱ) ⟶ Γ(T_e, ℱ)` is `D`-linear.**  It is semilinear for the
restriction of the section rings by `PresheafOfModules.map_smul`, and `D` acts on the two levels
through the *same* compatible family of scalars, so the semilinearity becomes linearity. -/
def levelRestrict (F : QuasiCoherentCrystal S) (e : ℕ) :
    L.levelSections F (e + 1) →ₗ[(D : Type u)] L.levelSections F e where
  toFun x := F.obj.val.map (L.levelSystem.map (homOfLE (Nat.le_succ e))).op x
  map_add' x y := map_add _ x y
  map_smul' a x :=
    (PresheafOfModules.map_smul F.obj.val (L.levelSystem.map (homOfLE (Nat.le_succ e))).op
        ((L.ringEquiv a).val (e + 1)) x).trans
      (congrArg (· • F.obj.val.map (L.levelSystem.map (homOfLE (Nat.le_succ e))).op x)
        ((L.ringEquiv a).2 (homOfLE (Nat.le_succ e))))

/-- `levelRestrict F e` is the restriction map of `ℱ` along the morphism `T_e ⟶ T_{e + 1}`. -/
@[simp] theorem levelRestrict_apply (F : QuasiCoherentCrystal S) (e : ℕ)
    (x : L.levelSections F (e + 1)) :
    L.levelRestrict F e x =
      F.obj.val.map (L.levelSystem.map (homOfLE (Nat.le_succ e))).op x :=
  rfl

/-! ### The module of [Stacks, Tag 07JG] as an inverse limit of `D`-modules -/

/-- **The `D`-linear identification of the module `M = lim_e Γ(T_e, ℱ)` of [Stacks, Tag 07JG] with
an inverse limit of `D`-modules.**

The two sides are subobjects of the same product `∏_e Γ(T_e, ℱ)`, cut out by the same condition:
one quantified over every morphism `e ⟶ e'` of `ℕ`, the other over the successors only, which is
`...SmallSite.mem_levelSectionsLimit_of_succ`.  The `D`-action matches on the nose, both being the
level-by-level action of the compatible family `ringEquiv a`.

This is what item (07JB) — `Crystalline.isPAdicallyComplete_invLimit_of_shift` — is stated about,
and it is the identification the module note of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelLimitPAdicComplete.lean` records as missing. -/
def sectionsInvLimitEquiv (F : QuasiCoherentCrystal S) :
    L.sections F ≃ₗ[(D : Type u)] ↥(invLimit (L.levelSections F) (L.levelRestrict F)) :=
  { Equiv.subtypeEquivRight (p := fun s ↦ s ∈ levelSectionsLimit S L.levelSystem F)
      fun s ↦ ⟨fun hs n ↦ hs (homOfLE (Nat.le_succ n)),
        fun hs ↦ mem_levelSectionsLimit_of_succ s hs⟩ with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

/-- The `e`-th component of the image of `m` under `sectionsInvLimitEquiv` is the `e`-th component
of its image under `sectionsEquiv`. -/
@[simp] theorem sectionsInvLimitEquiv_apply_val (F : QuasiCoherentCrystal S) (m : L.sections F)
    (e : ℕ) :
    (L.sectionsInvLimitEquiv F m).val e = (L.sectionsEquiv F m).val e :=
  rfl

/-- **Item (07JB) of [Stacks, Lemma 60.17.3, Tag 07JG], at the site.**  If `p^{N + e}` annihilates
the sections of `ℱ` over the level `e`, for a single shift `N` and every `e`, then the module
`M = lim_e Γ(T_e, ℱ)` of the tag is `p`-adically complete.

This is `Crystalline.isPAdicallyComplete_invLimit_of_shift` carried across
`...SmallSite.LevelScalars07JG.sectionsInvLimitEquiv`.  Nothing is assumed of the restriction maps
of the system: not surjectivity, and not the relation `M_e = M_{e + 1}/p^e M_{e + 1}` the source's
proof uses. -/
theorem isPAdicallyComplete_sections (p : ℕ) (F : QuasiCoherentCrystal S) (N : ℕ)
    (hann : ∀ (e : ℕ) (x : L.levelSections F e),
      ((p : (D : Type u)) ^ (N + e)) • x = 0) :
    IsPAdicallyComplete p (D : Type u) (L.sections F) :=
  Stacks.Examples.isAdicComplete_of_linearEquiv (L.sectionsInvLimitEquiv F)
    (_root_.Crystalline.isPAdicallyComplete_invLimit_of_shift p (D : Type u)
      (L.levelSections F) (L.levelRestrict F) N fun e ↦
        (_root_.Crystalline.pAdicIdeal_pow_smul_top_eq_bot_iff p (D : Type u)
          (L.levelSections F) N (n := e)).2 (hann e))

end LevelScalars07JG

/-! ### The annihilation for the system of [Stacks, Tag 07JN] -/

section WholeSpace

variable (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp] [IsAffine S.X] [IsAffine S.S.scheme]

/-- **`p^{N + e}` dies in the section ring of the level `e` of
`...SmallSite.wholeSpaceSystem`.**  That ring is `D(n)/(p)^{N + e}` by
`...SmallSite.wholeSpaceSystemLevelRingEquiv`, and `p^{N + e}` lies in the ideal divided out.  The
exponent is `...SmallSite.wholeSpaceLevelExponent hp e`, the shift of
`Crystalline.isPAdicallyComplete_invLimit_of_shift` at `N = Crystalline.uniformLevel`. -/
theorem levelRingHom_pow_wholeSpaceLevelScalars_eq_zero (n e : ℕ) :
    (wholeSpaceLevelScalars hp n).levelRingHom e
        (((affineSituation S hp).p : ((wholeSpaceSystemEnvelope hp n).ring : Type u)) ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) = 0 := by
  have hmem : ((affineSituation S hp).p : ((wholeSpaceSystemEnvelope hp n).ring : Type u)) ^
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) ∈
      DividedPowers.pAdicIdeal (A := (wholeSpaceSystemEnvelope hp n).ring)
          (affineSituation S hp).p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) :=
    Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
  change (envelopeLevelRingLimitEquiv hp n
    (((affineSituation S hp).p : ((wholeSpaceSystemEnvelope hp n).ring : Type u)) ^
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))).val e = 0
  rw [envelopeLevelRingLimitEquiv_apply_coe, Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]

/-- **`p^{N + e}` annihilates the sections of every coefficient sheaf over the level `e` of
`...SmallSite.wholeSpaceSystem`.**  The scalars act through the section ring of the level, in which
`p^{N + e}` is already zero by
`...SmallSite.levelRingHom_pow_wholeSpaceLevelScalars_eq_zero`.  This is the hypothesis of
`...SmallSite.LevelScalars07JG.isPAdicallyComplete_sections` established rather than assumed, and
it needs nothing of the crystal: it is a property of the level alone. -/
theorem pow_smul_eq_zero_wholeSpaceLevelSections (n e : ℕ) (F : QuasiCoherentCrystal S)
    (x : (wholeSpaceLevelScalars hp n).levelSections F e) :
    (((affineSituation S hp).p : ((wholeSpaceSystemEnvelope hp n).ring : Type u)) ^
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) • x = 0 := by
  rw [LevelScalars07JG.levelSections_smul_def,
    ← LevelScalars07JG.levelRingHom_apply (wholeSpaceLevelScalars hp n) e,
    levelRingHom_pow_wholeSpaceLevelScalars_eq_zero, zero_smul]

/-- **The field `...SmallSite.LevelComparison07JG.isPAdicallyComplete` over the scalars of
[Stacks, Proposition 60.21.1, Tag 07JN].**

For every crystal `ℱ` in quasi-coherent `𝒪_{X/S}`-modules, the module
`M = lim_e Γ(T(n)_e, ℱ)` of [Stacks, Lemma 60.17.3, Tag 07JG] over the completed divided power
envelope `D(n)` of [Stacks, Tag 07J8] is `p`-adically complete.  This is item (07JB) at the
system of levels the source's proof works over, and it is a theorem: the two inputs are the
`D`-linear identification `...SmallSite.LevelScalars07JG.sectionsInvLimitEquiv` and the
annihilation `...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections`, which the structure of the
level supplies.

The `p` is forced to be `S.p`, the residue characteristic of the situation, and the shift is
`N = Crystalline.uniformLevel (...affineSituation S hp)`.

**This is item (07JB) of [Stacks, Tag 07JG] with the source category the tag gives it**, over the
object ring of the system.  The subject is a crystal in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)` — the statement quantifies over
`...SmallSite.QuasiCoherentCrystal` and over no reduction datum, no index type and no basis — and
the standing hypotheses `[IsAffine S.X]`, `[IsAffine S.S.scheme]` and `hp` are the source's own,
the section the tag belongs to opening "In Situation [Stacks, Tag 07MD].  Set `X = Spec(C)` and
`S = Spec(A)`".  The other three items are not touched here: (07JC) needs the comparison map,
which is the small-site form of
`...GlobalCrystallineSituation.FirstOrderIdealBaseChange`, and (07JD) and (07JE) need the
source's own `D(1)` and `D(2)` coefficient computations. -/
theorem isPAdicallyComplete_wholeSpaceLevelScalars_sections (n : ℕ)
    (F : QuasiCoherentCrystal S) :
    IsPAdicallyComplete S.p ((wholeSpaceSystemEnvelope hp n).ring : Type u)
      ((wholeSpaceLevelScalars hp n).sections F) :=
  (wholeSpaceLevelScalars hp n).isPAdicallyComplete_sections S.p F
    (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (pow_smul_eq_zero_wholeSpaceLevelSections hp n · F)

/-! ### What a comparison datum over those scalars still needs -/

section Comparison

variable {A : Type u} [CommRing A] (n : ℕ)
  {g : A →+* (wholeSpaceSystemEnvelope hp n).ring}
  {Omega : Type u} [AddCommGroup Omega]
  [Module (wholeSpaceSystemEnvelope hp n).ring Omega]
  [Module ((wholeSpaceSystemEnvelope hp n).ring)ᵐᵒᵖ Omega]
  [IsCentralScalar (wholeSpaceSystemEnvelope hp n).ring Omega]
  {d : DividedPowerDerivation A (wholeSpaceSystemEnvelope hp n).ring g Omega}
  {ι : Type uI} {dx : ι → Omega}

/-- **A `...SmallSite.LevelComparison07JG` over the scalars of [Stacks, Tag 07JN] needs five of
its six fields, not six.**  `isPAdicallyComplete` — item (07JB) — is supplied by
`...SmallSite.isPAdicallyComplete_wholeSpaceLevelScalars_sections`; what remains is the comparison
map with its naturality, which is the small-site form of
`...GlobalCrystallineSituation.FirstOrderIdealBaseChange` and is available at the structure sheaf
by `...SmallSite.LevelScalars07JG.comparisonUnit`, and the three clauses about the connection,
which are items (07JD) and (07JE) with the non-vacuity of the last two.

This exhibits the field as discharged rather than merely stating a theorem of the same shape.  It
is **not** a `...SmallSite.Reduction07JG` and no tag follows from it: the remaining five fields
are hypotheses here, exactly as they were before. -/
def levelComparison07JGWholeSpaceOfRemaining
    (comparison : ∀ Fr : QuasiCoherentCrystal S,
      FirstOrderComparison A (wholeSpaceSystemEnvelope hp n).ring g Omega d
        ((wholeSpaceLevelScalars hp n).sections Fr))
    (comparison_naturality : ∀ {Fr Gr : QuasiCoherentCrystal S} (psi : Fr ⟶ Gr)
      (m : (wholeSpaceLevelScalars hp n).sections Fr),
      comparison Gr ((wholeSpaceLevelScalars hp n).sectionsMap psi m) =
        LinearMap.lTensor
          (firstOrderExtension (wholeSpaceSystemEnvelope hp n).ring Omega)
          ((wholeSpaceLevelScalars hp n).sectionsMap psi) (comparison Fr m))
    (hasCoordinateOperators : ∀ Fr : QuasiCoherentCrystal S,
      ∃ theta : ι → ((wholeSpaceLevelScalars hp n).sections Fr →
          (wholeSpaceLevelScalars hp n).sections Fr),
        IsCoordinateExpansion S.p (wholeSpaceSystemEnvelope hp n).ring Omega dx
          ((comparison Fr).completedConnection S.p) theta)
    (isIntegrable : ∀ Fr : QuasiCoherentCrystal S,
      IsIntegrable S.p (wholeSpaceSystemEnvelope hp n).ring Omega dx
        ((comparison Fr).completedConnection S.p))
    (isTopologicallyQuasiNilpotent : ∀ Fr : QuasiCoherentCrystal S,
      IsTopologicallyQuasiNilpotent S.p (wholeSpaceSystemEnvelope hp n).ring Omega dx
        ((comparison Fr).completedConnection S.p)) :
    LevelComparison07JG S A (wholeSpaceSystemEnvelope hp n).ring g Omega d S.p dx
      (wholeSpaceLevelScalars hp n) where
  comparison := comparison
  comparison_naturality := comparison_naturality
  isPAdicallyComplete := isPAdicallyComplete_wholeSpaceLevelScalars_sections hp n
  hasCoordinateOperators := hasCoordinateOperators
  isIntegrable := isIntegrable
  isTopologicallyQuasiNilpotent := isTopologicallyQuasiNilpotent

end Comparison

end WholeSpace

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

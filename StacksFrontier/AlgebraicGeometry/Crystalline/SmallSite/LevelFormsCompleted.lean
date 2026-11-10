module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorFree
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelFormsUniversal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsPAdicComplete

/-!
# The differentials datum of [Stacks, Tag 07JG] at the completed module of differentials

`...SmallSite.LevelForms07JG.ofUniversal` constructs the differentials datum of
[Stacks, Lemma 60.17.3, Tag 07JG] over a system of levels from three inputs, the third of which
is that `(Ω, d)` is a **universal** divided power derivation of `D` over `A`.  The module
documentation of `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelFormsUniversal.lean`
then records what it takes to be the obstruction to using it in the tag's own situation:

> `Ω_{D(n)}` of that proposition is a `p`-adic completion, and the completion of a universal
> object is not universal. … the universal property is the one input that still has to be matched.

**The second sentence is wrong, and this module corrects it.**  The first is right: the module
`Ω_D` of [Stacks, Equation 60.17.0.2, Tag 07J9] is `lim_e Ω_{D/A,δ}/p^e Ω_{D/A,δ}`, and a
`p`-adic completion does not satisfy the universal property — a lift out of it is not determined
by its values on `d a`, because `Ω_{D/A,δ}` is not dense in it in any sense the universal
property can see.  But the datum `...SmallSite.LevelForms07JG` does not need a lift out of an
arbitrary `Ω`: it needs one into the differentials `Γ(T_e, Ω_{T_e/S,δ})` of a *level*, and those
are **annihilated by a power of `p`** — the level `T_e` of [Stacks, Proposition 60.21.1, Tag
07JN] is cut out at `(p)^{N + e}`.  A linear map out of `Ω_{D/A,δ}` into a module killed by
`(p)^k` factors through `Ω_{D/A,δ}/(p)^k Ω_{D/A,δ}`, which the completion *does* map onto, by
`AdicCompletion.eval`.  So the factorisation of the level's own derivation through `d` exists on
the completion as well, and it is still unique, because two maps out of the completion that agree
on the image of `Ω_{D/A,δ}` agree after composing with the level's cutoff.

So the datum of the tag is available at the source's own `Ω_D` and not only at the uncompleted
universal module.

## Main definitions

Everything is in the namespace `Crystalline`, except the last three which are in
`Crystalline.GlobalCrystallineSituation.SmallSite`.

* `Crystalline.DividedPowerDerivation.compLinear` — a divided power derivation pushed along a
  `D`-linear map of its target; with `AdicCompletion.of` this is the derivation
  `d : D ⟶ Ω_D` of [Stacks, Equation 60.17.0.3, Tag 07JA] built out of the uncompleted one.
* `Crystalline.completionLift` — **a linear map into a module annihilated by `I^k` extends to the
  `I`-adic completion of its source**, through the level-`k` evaluation.
* `...SmallSite.LevelForms07JG.completedOmegaMap` — the reduction of the completed module of
  differentials to the differentials of a level.
* `...SmallSite.LevelForms07JG.ofUniversalCompletion` — **the differentials datum of
  [Stacks, Tag 07JG] over a system of levels at the `p`-adic completion of a universal `(Ω, d)`**,
  which is the `Ω_D` of [Stacks, Tag 07J9].

## Main results

* `Crystalline.completionLift_of` — the extension agrees with the original map on the image of
  the source, which is what pins it.
* `Crystalline.completionLift_comp` — the compatibility that the field
  `...SmallSite.LevelForms07JG.omegaMap_restrict` is: if a linear map factors a second one through
  a third, so do their extensions, at any two cutoffs with the second no larger than the first.
* `...SmallSite.LevelForms07JG.completedOmegaMap_derivation` and
  `...completedOmegaMap_restrict` — the two defining properties of the constructed reduction.
* `...SmallSite.pow_smul_top_wholeSpaceLevelDiffSections_eq_bot` and
  `...SmallSite.monotone_uniformLevel_add` — **the family of cutoffs the construction asks for,
  proved at the system of levels of [Stacks, Proposition 60.21.1, Tag 07JN]**: the level `e` is
  cut out at `(p)^{N + e}`, so `(p)^{N + e}` annihilates its differentials.

## What is and is not proved

**No `@[stacks]` attribute is placed in this module and no tag is proved.**  What is settled is
that the input `huniv` of `...SmallSite.LevelForms07JG.ofUniversal` may be met at the *completion*
of a universal `(Ω, d)`, which is the module the tag's own situation supplies, so the differentials
datum is not an obstruction there.

What is **not** settled, and is untouched here, is the other input of the reduction that mentions
`Ω`: `...SmallSite.LevelBaseChangeData` asks for a `Module.Basis ι D Ω` on the chosen
differentials together with a matching basis of the differentials of each level.  For the
completion of a free module on an infinite index set no such basis exists, and the index set of
the presentation `Crystalline.canonicalPresentation` that [Stacks, Tag 07JN] is formalized over is
`Γ(X, 𝒪_X)` itself.  That is a separate obstruction from the one removed here and it is not
removed.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Equation 60.17.0.2, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Equation 60.17.0.3, Tag 07JA](https://stacks.math.columbia.edu/tag/07JA)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Crystalline

/-! ### A divided power derivation pushed along a linear map -/

section CompLinear

variable {A : Type u} [CommRing A] {B : DividedPowerRing.{u}} {f : A →+* (B : Type u)}
  {M : Type u} [AddCommGroup M] [Module (B : Type u) M]
  {N : Type u} [AddCommGroup N] [Module (B : Type u) N]

/-- **A divided power derivation pushed along a `B`-linear map of its target.**  All three axioms
are preserved: additivity and the Leibniz rule because the map is linear, the vanishing on the
image of `A` because it sends `0` to `0`, and the divided power chain rule because it is
homogeneous. -/
def DividedPowerDerivation.compLinear (E : DividedPowerDerivation A B f M)
    (phi : M →ₗ[(B : Type u)] N) : DividedPowerDerivation A B f N where
  toDerivation := phi.compDer E.toDerivation
  map_ringHom' a := by
    have h : (phi.compDer E.toDerivation) (f a) = phi (E.toDerivation (f a)) := rfl
    rw [h, E.map_ringHom' a]
    exact phi.map_zero
  map_dpow' n hn x hx := by
    have h1 : (phi.compDer E.toDerivation) (B.dividedPowers.dpow n x) =
        phi (E.toDerivation (B.dividedPowers.dpow n x)) := rfl
    have h2 : (phi.compDer E.toDerivation) x = phi (E.toDerivation x) := rfl
    rw [h1, h2, E.map_dpow' n hn x hx, map_smul]

/-- The derivation `E.compLinear phi` sends `x` to `phi (E x)`. -/
@[simp] theorem DividedPowerDerivation.compLinear_apply (E : DividedPowerDerivation A B f M)
    (phi : M →ₗ[(B : Type u)] N) (x : (B : Type u)) : E.compLinear phi x = phi (E x) :=
  rfl

end CompLinear

/-! ### Extending a linear map to the adic completion of its source -/

section CompletionLift

variable {R : Type u} [CommRing R] (I : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
  {N : Type u} [AddCommGroup N] [Module R N] {N' : Type u} [AddCommGroup N'] [Module R N']

/-- The level-`k` factorisation of a linear map whose target is annihilated by `I^k`. -/
def quotLift (k : ℕ) (phi : M →ₗ[R] N) (hN : I ^ k • (⊤ : Submodule R N) = ⊥) :
    (M ⧸ I ^ k • (⊤ : Submodule R M)) →ₗ[R] N :=
  Submodule.liftQ _ phi fun x hx ↦ by
    rw [LinearMap.mem_ker, ← Submodule.mem_bot R, ← hN]
    exact map_mem_pow_smul_top_of_mem I phi k hx

/-- The map `quotLift I k phi hN` sends the class of `x` to `phi x`. -/
@[simp] theorem quotLift_mk (k : ℕ) (phi : M →ₗ[R] N)
    (hN : I ^ k • (⊤ : Submodule R N) = ⊥) (x : M) :
    quotLift I k phi hN (Submodule.Quotient.mk x) = phi x :=
  rfl

/-- **A linear map into a module annihilated by `I^k` extends to the `I`-adic completion of its
source**: it factors through `M/I^k M`, onto which the completion maps by its level-`k`
evaluation. -/
def completionLift (k : ℕ) (phi : M →ₗ[R] N) (hN : I ^ k • (⊤ : Submodule R N) = ⊥) :
    AdicCompletion I M →ₗ[R] N :=
  (quotLift I k phi hN).comp (AdicCompletion.eval I M k)

/-- The extension `completionLift I k phi hN` is `quotLift I k phi hN` applied after the
level-`k` evaluation of the completion. -/
@[simp] theorem completionLift_apply (k : ℕ) (phi : M →ₗ[R] N)
    (hN : I ^ k • (⊤ : Submodule R N) = ⊥) (w : AdicCompletion I M) :
    completionLift I k phi hN w = quotLift I k phi hN (AdicCompletion.eval I M k w) :=
  rfl

/-- **The extension agrees with the original map on the image of the source.** -/
@[simp] theorem completionLift_of (k : ℕ) (phi : M →ₗ[R] N)
    (hN : I ^ k • (⊤ : Submodule R N) = ⊥) (x : M) :
    completionLift I k phi hN (AdicCompletion.of I M x) = phi x := by
  change quotLift I k phi hN (AdicCompletion.eval I M k (AdicCompletion.of I M x)) = phi x
  rw [AdicCompletion.eval_of]
  rfl

/-- The level-`j` evaluation of the completion is the level-`k` one followed by the transition
map, for `j ≤ k`. -/
theorem transitionMap_eval {j k : ℕ} (hjk : j ≤ k) (w : AdicCompletion I M) :
    AdicCompletion.transitionMap I M hjk (AdicCompletion.eval I M k w) =
      AdicCompletion.eval I M j w := by
  simp [AdicCompletion.eval, AdicCompletion.transitionMap]

/-- **The compatibility of the extensions.**  If `psi ∘ phi' = phi` then the same holds of the
extensions, the one of `phi'` taken at any cutoff at least as large as the one of `phi`.  This is
the field `...SmallSite.LevelForms07JG.omegaMap_restrict` of the datum built below: the two
extensions are maps out of one quotient of `M` that agree on the classes of elements of `M`, and
the quotient map is surjective. -/
theorem completionLift_comp {j k : ℕ} (hjk : j ≤ k) (phi : M →ₗ[R] N) (phi' : M →ₗ[R] N')
    (psi : N' →ₗ[R] N) (hfac : ∀ x : M, psi (phi' x) = phi x)
    (hN : I ^ j • (⊤ : Submodule R N) = ⊥) (hN' : I ^ k • (⊤ : Submodule R N') = ⊥)
    (w : AdicCompletion I M) :
    psi (completionLift I k phi' hN' w) = completionLift I j phi hN w := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M k w)
  rw [completionLift_apply, completionLift_apply, ← transitionMap_eval I hjk w, ← hx]
  show psi (quotLift I k phi' hN' (Submodule.Quotient.mk x)) = _
  rw [quotLift_mk, hfac]
  change _ = quotLift I j phi hN (Submodule.Quotient.mk x)
  rw [quotLift_mk]

end CompletionLift

/-! ### The right action of a commutative ring on a module -/

/-- **A module over a commutative ring is a module over the opposite ring**, through the
identification of the ring with its opposite.  `...SmallSite.LevelForms07JG` asks for this action
and for its agreement with the left one; over a commutative ring both are canonical and Mathlib
has no instance for the first, so they are supplied here as local instances, exactly as
`PresheafOfModules.moduleMulOpposite` supplies them elsewhere in this tree. -/
@[instance_reducible]
def moduleMulOppositeOfCommRing (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] : Module Rᵐᵒᵖ M :=
  Module.compHom M ((RingEquiv.toOpposite R).symm : Rᵐᵒᵖ →+* R)

attribute [local instance] moduleMulOppositeOfCommRing

/-- Over a commutative ring the canonical right action of
`Crystalline.moduleMulOppositeOfCommRing` agrees with the left action. -/
theorem isCentralScalarOfCommRing (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] : IsCentralScalar R M :=
  ⟨fun _ _ ↦ rfl⟩

attribute [local instance] isCentralScalarOfCommRing

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance] _root_.Crystalline.moduleMulOppositeOfCommRing
  _root_.Crystalline.isCentralScalarOfCommRing

namespace LevelForms07JG

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A] {D : DividedPowerRing.{u}}
  {g : A →+* D} {Omega : Type u} [AddCommGroup Omega] [Module D Omega]
  {d : DividedPowerDerivation A D g Omega}
  (L : LevelScalars07JG S D)
  (hdp : ∀ e : ℕ, DividedPowers.IsDPMorphism D.dividedPowers
    (crysDividedPowers S (L.levelSystem.obj e).obj) (L.levelCrysRingHom e))
  (hbase : ∀ (e : ℕ) (a : A), L.levelDerivationFun e (g a) = 0)
  (huniv : _root_.Crystalline.IsUniversalDividedPowerDerivation Omega d)
  (p : ℕ) (k : ℕ → ℕ)
  (hkill : ∀ e : ℕ, DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ k e •
    (⊤ : Submodule (D : Type u) (L.levelDiffSections e)) = ⊥)

/-- **The derivation `d : D ⟶ Ω_D` of [Stacks, Equation 60.17.0.3, Tag 07JA]**: the derivation of
the uncompleted module of divided power differentials followed by the canonical map to its
`p`-adic completion, which for a universal `(Ω, d)` is the module `Ω_D` of
[Stacks, Equation 60.17.0.2, Tag 07J9]. -/
def completedDerivation (e0 : DividedPowerDerivation A D g Omega) (q : ℕ) :
    DividedPowerDerivation A D g
      (AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) q) Omega) :=
  e0.compLinear
    (AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) q) Omega)

/-- The derivation `completedDerivation e0 q` sends `a` to the image of `e0 a` in the `q`-adic
completion. -/
@[simp] theorem completedDerivation_apply (e0 : DividedPowerDerivation A D g Omega) (q : ℕ)
    (a : (D : Type u)) :
    completedDerivation e0 q a =
      AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) q) Omega (e0 a) :=
  rfl

/-- **The reduction of the completed module of differentials to the differentials of a level**:
the factorisation `...SmallSite.LevelForms07JG.universalLift` of the level's own divided power
derivation through `d`, extended to the completion through the level's cutoff `k e`. -/
def completedOmegaMap (e : ℕ) :
    AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Omega →ₗ[(D : Type u)]
      L.levelDiffSections e :=
  _root_.Crystalline.completionLift _ (k e) (universalLift L hdp hbase huniv (d := d) e) (hkill e)

/-- **The reduction carries the derivation of the situation to the derivation of the level**,
which is the field `...SmallSite.LevelForms07JG.omegaMap_derivation`. -/
theorem completedOmegaMap_derivation (e : ℕ) (a : (D : Type u)) :
    completedOmegaMap L hdp hbase huniv p k hkill e (completedDerivation d p a) =
      L.levelDerivationFun e a := by
  change _root_.Crystalline.completionLift _ (k e) (universalLift L hdp hbase huniv (d := d) e)
      (hkill e) (AdicCompletion.of _ _ (d a)) = _
  rw [_root_.Crystalline.completionLift_of]
  exact universalLift_derivation L hdp hbase huniv e a

/-- **The reductions are compatible with the restrictions of the system**, which is the field
`...SmallSite.LevelForms07JG.omegaMap_restrict`.  The cutoffs `k e ≤ k (e + 1)` are different and
that is exactly what `Crystalline.completionLift_comp` allows for. -/
theorem completedOmegaMap_restrict (hmono : Monotone k) (e : ℕ)
    (w : AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Omega) :
    crysDiffSectionsMap (L.levelStep e)
        (completedOmegaMap L hdp hbase huniv p k hkill (e + 1) w) =
      completedOmegaMap L hdp hbase huniv p k hkill e w :=
  _root_.Crystalline.completionLift_comp _ (hmono (Nat.le_succ e))
    (universalLift L hdp hbase huniv (d := d) e)
    (universalLift L hdp hbase huniv (d := d) (e + 1)) (L.levelDiffRestrict e)
    (fun x ↦ congrArg (fun f : Omega →ₗ[(D : Type u)] L.levelDiffSections e ↦ f x)
      (levelDiffRestrict_universalLift L hdp hbase huniv e))
    (hkill e) (hkill (e + 1)) w

/-- `...SmallSite.LevelForms07JG.completedOmegaMap` as an additive map into the differentials of
the level in their sheaf spelling, which is the shape the field
`...SmallSite.LevelForms07JG.omegaMap` asks for. -/
def completedOmegaMapHom (e : ℕ) :
    AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Omega →+
      crysDiffSections (L.levelSystem.obj e).obj :=
  (completedOmegaMap L hdp hbase huniv p k hkill e).toAddMonoidHom

/-- The map `completedOmegaMapHom` is semilinear along `L.levelCrysRingHom e`. -/
theorem completedOmegaMapHom_smul (e : ℕ) (a : (D : Type u))
    (w : AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Omega) :
    completedOmegaMapHom L hdp hbase huniv p k hkill e (a • w) =
      L.levelCrysRingHom e a • completedOmegaMapHom L hdp hbase huniv p k hkill e w :=
  (completedOmegaMap L hdp hbase huniv p k hkill e).map_smul a w

/-- The map `completedOmegaMapHom` carries the completed derivation to the derivation of the
level. -/
theorem completedOmegaMapHom_derivation (e : ℕ) (a : (D : Type u)) :
    completedOmegaMapHom L hdp hbase huniv p k hkill e (completedDerivation d p a) =
      crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e a) :=
  completedOmegaMap_derivation L hdp hbase huniv p k hkill e a

/-- The maps `completedOmegaMapHom` commute with the restriction maps of the system. -/
theorem crysDiffSectionsMap_completedOmegaMapHom (hmono : Monotone k) (e : ℕ)
    (w : AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Omega) :
    crysDiffSectionsMap (L.levelStep e)
        (completedOmegaMapHom L hdp hbase huniv p k hkill (e + 1) w) =
      completedOmegaMapHom L hdp hbase huniv p k hkill e w :=
  completedOmegaMap_restrict L hdp hbase huniv p k hkill hmono e w

/-- **The differentials datum of [Stacks, Lemma 60.17.3, Tag 07JG] over a system of levels, at the
`p`-adic completion of a universal `(Ω, d)`** — which is the module `Ω_D` of
[Stacks, Equation 60.17.0.2, Tag 07J9] with the derivation of [Stacks, Tag 07JA].

Beyond the three inputs of `...SmallSite.LevelForms07JG.ofUniversal` what is consumed is the
family of cutoffs: a monotone `k` with `(p)^{k e}` annihilating the differentials of the level
`e`.  At the system of levels of [Stacks, Proposition 60.21.1, Tag 07JN] the level `e` is cut out
at `(p)^{N + e}`, so `k e = N + e` serves.

**No `@[stacks]` attribute is placed and no tag is proved**: this is one input of the reduction of
[Stacks, Tag 07JG]. -/
def ofUniversalCompletion (hmono : Monotone k) :
    LevelForms07JG S A D g
      (AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Omega)
      (completedDerivation d p) L where
  omegaMap e := completedOmegaMapHom L hdp hbase huniv p k hkill e
  omegaMap_smul e a w := completedOmegaMapHom_smul L hdp hbase huniv p k hkill e a w
  omegaMap_derivation e a := completedOmegaMapHom_derivation L hdp hbase huniv p k hkill e a
  omegaMap_restrict e w := by
    rw [crysSheafRingMap_siteMap_diffSection,
      crysDiffSectionsMap_completedOmegaMapHom L hdp hbase huniv p k hkill hmono e w]

end LevelForms07JG

/-! ### The cutoffs at the system of levels of [Stacks, Proposition 60.21.1, Tag 07JN] -/

section WholeSpace

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **`(p)^{N + e}` annihilates the differentials of the level `e` of
`...SmallSite.wholeSpaceSystem`.**

This is the hypothesis `hkill` of `...SmallSite.LevelForms07JG.ofUniversalCompletion` at the
source's own system of levels, proved.  The scalars act on the differentials of the level through
the reduction of `D(n)` to its section ring, and `p^{N + e}` is already zero there by
`...SmallSite.levelRingHom_pow_wholeSpaceLevelScalars_eq_zero`: the level is cut out at
`(p)^{N + e}`.  Like that theorem it is a property of the level alone and needs nothing of any
coefficient sheaf. -/
theorem pow_smul_top_wholeSpaceLevelDiffSections_eq_bot (n e : ℕ) :
    DividedPowers.pAdicIdeal (A := ((wholeSpaceSystemEnvelope hp n).ring : Type u))
          (affineSituation S hp).p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) •
      (⊤ : Submodule ((wholeSpaceSystemEnvelope hp n).ring : Type u)
        ((wholeSpaceLevelScalars hp n).levelDiffSections e)) = ⊥ := by
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have h0 : (wholeSpaceLevelScalars hp n).levelCrysRingHom e
        (((affineSituation S hp).p : ((wholeSpaceSystemEnvelope hp n).ring : Type u)) ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) = 0 :=
      levelRingHom_pow_wholeSpaceLevelScalars_eq_zero hp n e
    rw [Submodule.mem_bot, LevelScalars07JG.levelDiffSections_smul_def, map_mul, h0, zero_mul,
      zero_smul]
  · exact Submodule.add_mem _ hy hz

omit [WholeSpacePresentation S hp] [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The family of cutoffs `k e = N + e` of
`...SmallSite.pow_smul_top_wholeSpaceLevelDiffSections_eq_bot` is monotone, which is the other
hypothesis `...SmallSite.LevelForms07JG.ofUniversalCompletion` asks of it. -/
theorem monotone_uniformLevel_add :
    Monotone fun e : ℕ ↦ _root_.Crystalline.uniformLevel (affineSituation S hp) + e :=
  fun _ _ h ↦ Nat.add_le_add_left h _

end WholeSpace

end Crystalline.GlobalCrystallineSituation.SmallSite

end

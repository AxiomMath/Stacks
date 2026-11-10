module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DiffSectionsFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Universal

/-!
# The differentials datum of [Stacks, Tag 07JG] over a system of levels, constructed

`...SmallSite.LevelForms07JG` is the reduction of the module `Ω` of
[Stacks, Lemma 60.17.3, Tag 07JG] to the differentials of each level: a semilinear map
`ω_e : Ω ⟶ Γ(T_e, Ω_{T_e/S,δ})` for every `e`, carrying the divided power derivation `d` of the
situation to the universal divided power derivation of the level and compatible with the
restrictions of the system.  Its own module documentation calls it "a datum and not a
construction", and judged the map not constructible.

**That judgement is half right and is corrected here.**  For an *arbitrary* `Ω` the map does not
exist: the datum of the situation is a derivation `d : D ⟶ Ω`, which maps *into* `Ω`, and nothing
maps out of an arbitrary module.  What makes the map exist is `Ω` being **universal** — which is
what it is in the tag, `Ω = Ω_{D/A,δ}` of [Stacks, Tag 07J9] — and then the map is the unique
factorisation of the level's own derivation through `d`.

So this module

* names the universal property, `Crystalline.IsUniversalDividedPowerDerivation`, and records
  that the divided power differentials have it (`Crystalline.dividedPowerDifferentials_lift`,
  [Stacks, Tag 07HZ]), so the hypothesis is not vacuous;
* builds the divided power derivation of a level out of `D`: the universal divided power
  derivation of `T_e` precomposed with the reduction `D ⟶ Γ(T_e, 𝒪)`, which is a divided power
  derivation exactly because that reduction is a homomorphism of divided power rings and kills
  the differentials of the base;
* **constructs all four fields of `...SmallSite.LevelForms07JG`** from those two inputs.  The
  fourth, `omegaMap_restrict`, is not assumed: the restriction of the lift at `e + 1` along the
  step of the system is again a lift of the derivation at `e`, by
  `...GlobalCrystallineSituation.crysDiffSectionsMap_crysDerivation` and the compatibility of the
  reductions of `D`, so the uniqueness half of the universal property identifies it with the lift
  at `e`.

## Main definitions

* `Crystalline.IsUniversalDividedPowerDerivation` — the universal property of `(Ω, d)` over `D`.
* `...SmallSite.LevelScalars07JG.levelDiffSections` — the differentials of a level as a
  `D`-module, through the reduction of `D` to its section ring.
* `...SmallSite.LevelScalars07JG.levelDiffRestrict` — the restriction of differentials along a
  step of the system, `D`-linearly.
* `...SmallSite.LevelScalars07JG.levelDerivationFun` and
  `...SmallSite.LevelScalars07JG.levelDPDerivation` — **the divided power derivation
  `D ⟶ Γ(T_e, Ω_{T_e/S,δ})` of a level**, as a function and bundled.
* `...SmallSite.LevelForms07JG.universalLift` and
  `...SmallSite.LevelForms07JG.omegaMapOfUniversal` — the factorisation of that derivation
  through `d`, which is the field `omegaMap`.
* `...SmallSite.LevelForms07JG.ofUniversal` — **the differentials datum of
  [Stacks, Tag 07JG] over a system of levels, constructed.**

## Main results

* `Crystalline.isUniversalDividedPowerDerivation_universalDividedPowerDerivation` — the divided
  power differentials of a divided power ring are universal, so the hypothesis of
  `...ofUniversal` is satisfiable.
* `...SmallSite.LevelScalars07JG.levelCrysRingHom_restrict` — the reductions of `D` to the levels
  are a compatible family, which is the membership condition of `...SmallSite.levelRingLimit`.
* `...SmallSite.LevelScalars07JG.levelDerivationFun_add`, `..._mul` and `..._dpow` — the three
  axioms of a divided power derivation for the derivation of a level.
* `...SmallSite.LevelForms07JG.levelDiffRestrict_universalLift` — **the restriction of the
  factorisation at `e + 1` is the factorisation at `e`**, which is the field `omegaMap_restrict`.
* `...SmallSite.LevelForms07JG.ofUniversal_omegaMap_derivation` and
  `...ofUniversal_crysDiffSectionsMap` — the two defining properties of the constructed map.

## What is and is not proved

**No `@[stacks]` attribute is placed in this module and no tag is proved.**  What is settled is
that `...SmallSite.LevelForms07JG` is a construction and not a datum once `Ω` is the universal
module of divided power differentials of `D`, which is what [Stacks, Tag 07J9] makes it in the
tag.

The module `Ω_{D(n)}` of [Stacks, Proposition 60.21.1, Tag 07JN] is a `p`-adic completion, and the
completion of a universal object is not universal, so `...ofUniversal` does not apply to it
directly.  **That is not an obstruction to the datum**, and
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelFormsCompleted.lean` removes it: the
datum needs a map *into* the differentials of a level, those are annihilated by a power of `p`,
and the factorisation built here therefore descends to `Ω/(p)^k Ω`, which the completion maps
onto.  `...SmallSite.LevelForms07JG.ofUniversalCompletion` is the datum at the completion of a
universal `(Ω, d)`, with the cutoffs it asks for proved at the system of levels of that
proposition by `...SmallSite.pow_smul_top_wholeSpaceLevelDiffSections_eq_bot`.

What is **not** settled for that system are the other two hypotheses of `...ofUniversal` — that
the reduction of `D` to each level is a divided power morphism and that it kills the
differentials of `A`.  The ingredient for the first is
`...SmallSite.isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv`, stated for
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` and not for
`...SmallSite.LevelScalars07JG.levelCrysRingHom`; the second has no statement in the tree.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-! ### The universal property of a divided power derivation -/

/-- **`(Ω, d)` is a universal divided power derivation of `D` over `A`**: every divided power
derivation of `D` over `A` with values in a `D`-module factors uniquely and `D`-linearly through
`d`.

This is the property the module `Ω` of [Stacks, Lemma 60.17.3, Tag 07JG] has in the tag, where it
is `Ω_{D/A,δ}` of [Stacks, Tag 07J9]; it is stated as a predicate because the tag's `Ω` is a
parameter and the reduction datum must be buildable from whatever presents it. -/
def IsUniversalDividedPowerDerivation {A : Type u} [CommRing A] {D : DividedPowerRing.{u}}
    {g : A →+* (D : Type u)} (Omega : Type u) [AddCommGroup Omega] [Module (D : Type u) Omega]
    (d : DividedPowerDerivation A D g Omega) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
    (E : DividedPowerDerivation A D g M),
    ∃! lift : Omega →ₗ[(D : Type u)] M, ∀ b : (D : Type u), lift (d b) = E b

/-- **The divided power differentials of a divided power ring are universal**, which is
[Stacks, Tag 07HZ] in the form `Crystalline.dividedPowerDifferentials_lift`.  So the hypothesis of
`...SmallSite.LevelForms07JG.ofUniversal` is satisfiable, and the predicate above is not
vacuous. -/
theorem isUniversalDividedPowerDerivation_universalDividedPowerDerivation {A : Type u}
    [CommRing A] (D : DividedPowerRing.{u}) [Algebra A (D : Type u)] :
    IsUniversalDividedPowerDerivation
      (dividedPowerDifferentials (A := A) D.dividedPowers)
      (universalDividedPowerDerivation (A := A) (B := D)) :=
  fun _ _ _ E ↦ dividedPowerDifferentials_lift D E

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace LevelScalars07JG

variable {S : GlobalCrystallineSituation.{u}} {D : DividedPowerRing.{u}}
  (L : LevelScalars07JG S D)

/-! ### The differentials of a level as a `D`-module -/

/-- **The differentials `Γ(T_e, Ω_{T_e/S,δ})` of a level as a `D`-module**, the scalars acting
through the reduction `...SmallSite.LevelScalars07JG.levelCrysRingHom` of `D` to the section ring
of the level.  A type synonym and not an instance on `crysDiffSections` itself, because the action
depends on the field `ringEquiv`; this is the pattern of
`...SmallSite.LevelScalars07JG.levelSections`. -/
def levelDiffSections (e : ℕ) : Type u := crysDiffSections (L.levelSystem.obj e).obj

/-- The additive group structure on the differentials of a level. -/
instance instAddCommGroupLevelDiffSections (e : ℕ) : AddCommGroup (L.levelDiffSections e) :=
  inferInstanceAs (AddCommGroup (crysDiffSections (L.levelSystem.obj e).obj))

/-- The differentials of a level as a module over the section ring of the level. -/
instance instModuleCrysLevelDiffSections (e : ℕ) :
    Module (crysSheafRing S (L.levelSystem.obj e).obj) (L.levelDiffSections e) :=
  inferInstanceAs (Module (crysSheafRing S (L.levelSystem.obj e).obj)
    (crysDiffSections (L.levelSystem.obj e).obj))

/-- The differentials of a level as a `D`-module, through the reduction
`...SmallSite.LevelScalars07JG.levelCrysRingHom` of `D` to the section ring of the level. -/
instance instModuleLevelDiffSections (e : ℕ) : Module (D : Type u) (L.levelDiffSections e) :=
  Module.compHom (L.levelDiffSections e) (L.levelCrysRingHom e)

/-- An element of `D` acts on the differentials of a level as its reduction to the section ring of
the level. -/
theorem levelDiffSections_smul_def (e : ℕ) (a : (D : Type u)) (w : L.levelDiffSections e) :
    a • w = L.levelCrysRingHom e a • w :=
  rfl

/-- **The reductions of `D` to the levels are a compatible family**, which is the membership
condition of `...SmallSite.levelRingLimit` read through `ringEquiv`. -/
theorem levelCrysRingHom_restrict (e : ℕ) (a : (D : Type u)) :
    crysSheafRingMap (L.levelStep e) (L.levelCrysRingHom (e + 1) a) = L.levelCrysRingHom e a :=
  (L.ringEquiv a).2 (homOfLE (Nat.le_succ e))

/-- **The restriction of differentials along a step of the system is `D`-linear**: it is
semilinear for the restriction of the section rings by
`...GlobalCrystallineSituation.crysDiffSectionsMap_smul`, and `D` acts on the two levels through
one and the same compatible family of scalars. -/
def levelDiffRestrict (e : ℕ) :
    L.levelDiffSections (e + 1) →ₗ[(D : Type u)] L.levelDiffSections e where
  toFun w := crysDiffSectionsMap (L.levelStep e) w
  map_add' w w' := crysDiffSectionsMap_add (L.levelStep e) w w'
  map_smul' a w := by
    have h := crysDiffSectionsMap_smul (L.levelStep e) (L.levelCrysRingHom (e + 1) a) w
    rw [L.levelCrysRingHom_restrict] at h
    exact h

/-- The restriction of differentials along a step of the system is
`...GlobalCrystallineSituation.crysDiffSectionsMap`. -/
@[simp] theorem levelDiffRestrict_apply (e : ℕ) (w : L.levelDiffSections (e + 1)) :
    L.levelDiffRestrict e w = crysDiffSectionsMap (L.levelStep e) w :=
  rfl

/-! ### The divided power derivation of a level -/

variable {A : Type u} [CommRing A] {g : A →+* (D : Type u)}

/-- **The derivation of a level out of `D`**, as a bare function: the universal divided power
derivation `...GlobalCrystallineSituation.crysDerivation` of the level, precomposed with the
reduction of `D` to its section ring. -/
def levelDerivationFun (e : ℕ) (x : (D : Type u)) : L.levelDiffSections e :=
  crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e x)

/-- The derivation of a level is additive. -/
theorem levelDerivationFun_add (e : ℕ) (x y : (D : Type u)) :
    L.levelDerivationFun e (x + y) =
      L.levelDerivationFun e x + L.levelDerivationFun e y := by
  change crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e (x + y)) = _
  rw [map_add]
  exact sheafApp_add _ _ _ ⊤ _ _

/-- **The Leibniz rule for the derivation of a level**, the scalars acting through the reduction
of `D`. -/
theorem levelDerivationFun_mul (e : ℕ) (x y : (D : Type u)) :
    L.levelDerivationFun e (x * y) =
      x • L.levelDerivationFun e y + y • L.levelDerivationFun e x := by
  have h : crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e (x * y)) =
      L.levelCrysRingHom e x •
          crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e y) +
        L.levelCrysRingHom e y •
          crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e x) := by
    rw [map_mul]
    exact sheafApp_mul _ _ _ ⊤ _ _
  exact h

/-- **The divided power chain rule for the derivation of a level**, which the reduction of `D`
being a homomorphism of divided power rings transports from the level. -/
theorem levelDerivationFun_dpow (e : ℕ)
    (hdp : DividedPowers.IsDPMorphism D.dividedPowers
      (crysDividedPowers S (L.levelSystem.obj e).obj) (L.levelCrysRingHom e))
    (k : ℕ) (x : (D : Type u)) (hx : x ∈ D.ideal) :
    L.levelDerivationFun e (D.dividedPowers.dpow (k + 1) x) =
      D.dividedPowers.dpow k x • L.levelDerivationFun e x := by
  have hmem : L.levelCrysRingHom e x ∈
      (L.levelSystem.obj e).obj.thickening.target.ideal.obj (op ⊤) :=
    hdp.ideal_comp (Ideal.mem_map_of_mem (L.levelCrysRingHom e) hx)
  have hc1 : (crysDividedPowers S (L.levelSystem.obj e).obj).dpow (k + 1)
        (L.levelCrysRingHom e x) =
      L.levelCrysRingHom e (D.dividedPowers.dpow (k + 1) x) :=
    hdp.dpow_comp x hx
  have hc2 : (crysDividedPowers S (L.levelSystem.obj e).obj).dpow k
        (L.levelCrysRingHom e x) =
      L.levelCrysRingHom e (D.dividedPowers.dpow k x) :=
    hdp.dpow_comp x hx
  have h : crysDerivation (L.levelSystem.obj e).obj
        (L.levelCrysRingHom e (D.dividedPowers.dpow (k + 1) x)) =
      L.levelCrysRingHom e (D.dividedPowers.dpow k x) •
        crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e x) := by
    rw [← hc1, ← hc2]
    exact sheafApp_dpow _ _ _ ⊤ k _ hmem
  exact h

/-- **The divided power derivation `D ⟶ Γ(T_e, Ω_{T_e/S,δ})` of a level.**

Additivity and the Leibniz rule are those of the universal derivation of the level, the vanishing
on the image of `A` is the hypothesis `hbase`, and the divided power chain rule is the one of the
level transported along `hdp`. -/
def levelDPDerivation (e : ℕ)
    (hdp : DividedPowers.IsDPMorphism D.dividedPowers
      (crysDividedPowers S (L.levelSystem.obj e).obj) (L.levelCrysRingHom e))
    (hbase : ∀ a : A, L.levelDerivationFun e (g a) = 0) :
    DividedPowerDerivation A D g (L.levelDiffSections e) where
  toDerivation :=
    Derivation.mk'
      (AddMonoidHom.toIntLinearMap
        (AddMonoidHom.mk' (L.levelDerivationFun e) (L.levelDerivationFun_add e)))
      (L.levelDerivationFun_mul e)
  map_ringHom' a := hbase a
  map_dpow' n hn x hx := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact L.levelDerivationFun_dpow e hdp k x hx

/-- The divided power derivation of a level evaluates as `levelDerivationFun`. -/
@[simp] theorem levelDPDerivation_apply (e : ℕ)
    (hdp : DividedPowers.IsDPMorphism D.dividedPowers
      (crysDividedPowers S (L.levelSystem.obj e).obj) (L.levelCrysRingHom e))
    (hbase : ∀ a : A, L.levelDerivationFun e (g a) = 0) (x : (D : Type u)) :
    L.levelDPDerivation (g := g) e hdp hbase x = L.levelDerivationFun e x :=
  rfl

end LevelScalars07JG

/-! ### The differentials datum, constructed -/

namespace LevelForms07JG

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A] {D : DividedPowerRing.{u}}
  {g : A →+* D} {Omega : Type u} [AddCommGroup Omega] [Module D Omega]
  {d : DividedPowerDerivation A D g Omega}
  (L : LevelScalars07JG S D)
  (hdp : ∀ e : ℕ, DividedPowers.IsDPMorphism D.dividedPowers
    (crysDividedPowers S (L.levelSystem.obj e).obj) (L.levelCrysRingHom e))
  (hbase : ∀ (e : ℕ) (a : A), L.levelDerivationFun e (g a) = 0)
  (huniv : _root_.Crystalline.IsUniversalDividedPowerDerivation Omega d)

/-- The `D`-linear factorisation of the derivation of the level `e` through `d`, which the
universal property provides. -/
def universalLift (e : ℕ) : Omega →ₗ[(D : Type u)] L.levelDiffSections e :=
  (huniv (L.levelDiffSections e) (L.levelDPDerivation (g := g) e (hdp e) (hbase e))).choose

/-- The factorisation `universalLift` carries `d a` to the derivation of the level evaluated at
`a`. -/
theorem universalLift_derivation (e : ℕ) (a : (D : Type u)) :
    universalLift L hdp hbase huniv (d := d) e (d a) = L.levelDerivationFun e a :=
  (huniv (L.levelDiffSections e)
    (L.levelDPDerivation (g := g) e (hdp e) (hbase e))).choose_spec.1 a

/-- **The restriction of the factorisation at `e + 1` is the factorisation at `e`.**  Both are
`D`-linear maps `Ω ⟶ Γ(T_e, Ω)` carrying `d a` to the universal differential of the reduction of
`a`: the first by `...GlobalCrystallineSituation.crysDiffSectionsMap_crysDerivation` together
with the compatibility `...SmallSite.LevelScalars07JG.levelCrysRingHom_restrict` of the
reductions, the second by its own defining property.  The uniqueness half of the universal
property identifies them. -/
theorem levelDiffRestrict_universalLift (e : ℕ) :
    (L.levelDiffRestrict e).comp (universalLift L hdp hbase huniv (d := d) (e + 1)) =
      universalLift L hdp hbase huniv (d := d) e := by
  refine (huniv (L.levelDiffSections e)
    (L.levelDPDerivation (g := g) e (hdp e) (hbase e))).unique (fun a ↦ ?_) (fun a ↦ ?_)
  · change crysDiffSectionsMap (L.levelStep e)
        (universalLift L hdp hbase huniv (d := d) (e + 1) (d a)) = _
    rw [universalLift_derivation]
    change crysDiffSectionsMap (L.levelStep e)
        (crysDerivation (L.levelSystem.obj (e + 1)).obj (L.levelCrysRingHom (e + 1) a)) = _
    rw [crysDiffSectionsMap_crysDerivation, L.levelCrysRingHom_restrict]
    rfl
  · exact universalLift_derivation L hdp hbase huniv e a

/-- **The reduction of `Ω` to the differentials of a level**, the field
`...SmallSite.LevelForms07JG.omegaMap` of the datum built below: the `D`-linear factorisation
read in the sheaf spelling of the differentials of the level. -/
def omegaMapOfUniversal (e : ℕ) : Omega →+ crysDiffSections (L.levelSystem.obj e).obj :=
  (universalLift L hdp hbase huniv (d := d) e).toAddMonoidHom

/-- The reduction `omegaMapOfUniversal` carries `d a` to the universal divided power derivation of
the level evaluated at the reduction of `a`. -/
theorem omegaMapOfUniversal_derivation (e : ℕ) (a : (D : Type u)) :
    omegaMapOfUniversal L hdp hbase huniv (d := d) e (d a) =
      crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e a) :=
  universalLift_derivation L hdp hbase huniv e a

/-- The reduction `omegaMapOfUniversal` is semilinear for the reduction of `D` to the section ring
of the level. -/
theorem omegaMapOfUniversal_smul (e : ℕ) (a : (D : Type u)) (w : Omega) :
    omegaMapOfUniversal L hdp hbase huniv (d := d) e (a • w) =
      L.levelCrysRingHom e a • omegaMapOfUniversal L hdp hbase huniv (d := d) e w :=
  (universalLift L hdp hbase huniv (d := d) e).map_smul a w

/-- **The reductions are compatible with the restrictions of the system.** -/
theorem crysDiffSectionsMap_omegaMapOfUniversal (e : ℕ) (w : Omega) :
    crysDiffSectionsMap (L.levelStep e)
        (omegaMapOfUniversal L hdp hbase huniv (d := d) (e + 1) w) =
      omegaMapOfUniversal L hdp hbase huniv (d := d) e w :=
  congrArg (fun f : Omega →ₗ[(D : Type u)] L.levelDiffSections e ↦ f w)
    (levelDiffRestrict_universalLift L hdp hbase huniv e)

variable [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]

/-- **The differentials datum of [Stacks, Lemma 60.17.3, Tag 07JG] over a system of levels,
constructed** from three inputs about the scalars alone:

* each reduction `D ⟶ Γ(T_e, 𝒪_{T_e})` is a homomorphism of divided power rings;
* each reduction kills the differentials of the image of `A`;
* `(Ω, d)` is a universal divided power derivation of `D` over `A`.

The map `ω_e` is the unique `D`-linear factorisation of the level's own divided power derivation
through `d`, and the three remaining fields are its defining property, its `D`-linearity, and the
uniqueness of factorisations.

**No `@[stacks]` attribute is placed and no tag is proved**: this is one input of the reduction of
[Stacks, Tag 07JG]. -/
def ofUniversal : LevelForms07JG S A D g Omega d L where
  omegaMap e := omegaMapOfUniversal L hdp hbase huniv (d := d) e
  omegaMap_smul e a w := omegaMapOfUniversal_smul L hdp hbase huniv e a w
  omegaMap_derivation e a := omegaMapOfUniversal_derivation L hdp hbase huniv e a
  omegaMap_restrict e w := by
    rw [crysSheafRingMap_siteMap_diffSection,
      crysDiffSectionsMap_omegaMapOfUniversal L hdp hbase huniv e w]

/-- The map `omegaMap` of `ofUniversal` at the level `e` is `omegaMapOfUniversal`. -/
@[simp] theorem ofUniversal_omegaMap (e : ℕ) (w : Omega) :
    (ofUniversal L hdp hbase huniv (d := d)).omegaMap e w =
      omegaMapOfUniversal L hdp hbase huniv (d := d) e w :=
  rfl

/-- The map `omegaMap` of `ofUniversal` carries `d a` to the universal divided power derivation of
the level evaluated at the reduction of `a`. -/
theorem ofUniversal_omegaMap_derivation (e : ℕ) (a : (D : Type u)) :
    (ofUniversal L hdp hbase huniv (d := d)).omegaMap e (d a) =
      crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e a) :=
  omegaMapOfUniversal_derivation L hdp hbase huniv e a

/-- The maps `omegaMap` of `ofUniversal` are compatible with the restrictions of the system. -/
theorem ofUniversal_crysDiffSectionsMap (e : ℕ) (w : Omega) :
    crysDiffSectionsMap (L.levelStep e)
        ((ofUniversal L hdp hbase huniv (d := d)).omegaMap (e + 1) w) =
      (ofUniversal L hdp hbase huniv (d := d)).omegaMap e w :=
  crysDiffSectionsMap_omegaMapOfUniversal L hdp hbase huniv e w

end LevelForms07JG

end Crystalline.GlobalCrystallineSituation.SmallSite

end

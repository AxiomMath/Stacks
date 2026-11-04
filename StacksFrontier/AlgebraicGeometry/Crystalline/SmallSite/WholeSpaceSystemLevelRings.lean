module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs

/-!
# The section rings of the levels of the system of [Stacks, Tag 07JN]

[Stacks, Lemma 60.17.3, Tag 07JG] runs over the tower `T_0 ⟶ T_1 ⟶ ⋯` of finite levels
`T_e = Spec(D_e)` of the `p`-adically completed divided power envelope `D` of
[Stacks, Tag 07J8], and sets `M = lim_e Γ(T_e, ℱ_{T_e})` over them.  The tower itself is
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCosimplicialSystem.lean`, which is
already an object of `Cris(X/S)` in each bidegree.  What was missing, and what this module
supplies, is the *ring* of each level: nothing in the tree said what
`Γ(T_e, 𝒪_{T_e})` is.

The obstruction was that `wholeSpaceSystem` is built by transporting the affine finite levels
`D(n)/(p)^{N + e}` across the equivalence
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine` of `𝒞ᵒᵖ` with
`Cris(Γ(X, ⊤)/Γ(S, ⊤))`, and the inverse of that equivalence is a `Classical.choice`: an object
of `Cris(X/S)` isomorphic to the `Spec` of the level, not that `Spec` on the nose.  The counit
of the equivalence repairs exactly that, and it is what the identification below is built from.

## Main definitions

* `Crystalline.DividedPowerThickening.ringEquivOfIso` — an isomorphism of divided power
  thickenings of an affine crystalline situation, read as a ring isomorphism of their rings.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSiteInverseSectionsRingEquiv` — **the
  sections of `𝒪_{X/S}` over the object of `𝒞` transported back from an affine object are that
  object's ring.**  This is the bridge the equivalence's `Classical.choice` inverse hid.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystemEnvelope` and
  `...SmallSite.wholeSpaceSystemLevel` — the envelope `D(n)` of the situation's own
  presentation and its finite level `D(n)/(p)^{N + e}`, as an object of
  `Cris(Γ(X, ⊤)/Γ(S, ⊤))`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystemLevelRingEquiv` — **the
  section ring of the level `(n, e)` of [Stacks, Tag 07JN] is `D(n)/(p)^{N + e}`.**
* `Crystalline.GlobalCrystallineSituation.SmallSite.envelopeToLevelRingLimit` — the induced ring
  homomorphism `D(n) ⟶ lim_e Γ(T(n)_e, 𝒪)` into the limit of
  `Crystalline.GlobalCrystallineSituation.SmallSite.levelRingLimit`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.envelopeLevelRingLimitEquiv` — **the ring
  `D(n)` is that inverse limit**, which is the field `ringEquiv` of
  `Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG` for the system of
  [Stacks, Tag 07JN].

## Main results

* `...SmallSite.wholeSiteInverseSectionsRingEquiv_naturality` — the bridge is natural: a
  morphism of the affine site induces, on the transported objects, the restriction map of
  `𝒪_{X/S}`, read through the bridge.  This is the naturality of the counit and nothing more.
* `...SmallSite.wholeSpaceSystem_obj_eq_level` and `...SmallSite.wholeSpaceSystem_map_eq` — the
  object and the transition map of the system in bidegree `(n, e)` are the transport of the
  finite level and of the reduction `D(n)/(p)^{N + e + 1} ⟶ D(n)/(p)^{N + e}`.  Both hold by
  `rfl`; they are recorded so that the identification below can be used without unfolding the
  construction of the system.
* `...SmallSite.wholeSpaceSystemLevelRingEquiv_restrict` — **the identifications of the level
  rings are compatible with the tower**: the restriction map `Γ(T_{e'}, 𝒪) ⟶ Γ(T_e, 𝒪)` of the
  system becomes the reduction `D(n)/(p)^{N + e'} ⟶ D(n)/(p)^{N + e}`.
* `...SmallSite.envelopeToLevelRingLimit_apply_coe` — the value of the ring homomorphism at a
  level is the reduction of the element.
* `...SmallSite.injective_envelopeToLevelRingLimit` and
  `...SmallSite.surjective_envelopeToLevelRingLimit` — the comparison map is bijective, by the
  two halves of `p`-adic completeness of `D(n)`.
* `Crystalline.DividedPowerThickening.isDPMorphism_ringEquivOfIso` and
  `...isDPMorphism_ringEquivOfIso_symm` — **the ring isomorphism of an isomorphism of divided
  power thickenings is an isomorphism of divided power rings.**  `ringEquivOfIso` keeps only the
  underlying ring map of the two divided power morphisms; these recover the half it drops, in
  both directions.
* `...SmallSite.isDPMorphism_wholeSiteInverseSectionsRingEquiv` and its `_symm` — the bridge
  matches `Crystalline.GlobalCrystallineSituation.crysDividedPowers` on the sections of
  `𝒪_{X/S}` with the affine object's own divided powers.
* `...SmallSite.isDPMorphism_wholeSpaceSystemLevelRingEquiv` and its `_symm` — **the divided
  powers on `Γ(T(n)_e, 𝒪)` are `DividedPowers.quotientDividedPowers` on `D(n)/(p)^{N + e}`.**
  This is what lets `Crystalline.tensorFormsLevelEquiv` of
  `ModuleDifferentials/QuotientForms.lean`, which speaks about the quotient divided powers, be
  read at the level `T(n)_e`, where
  `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso` presents the sections
  of `Ω^i_{X/S}` through `crysDividedPowers`.  Both descriptions of each side hold by `rfl` —
  `Crystalline.levelThickening_ring` on one side and the construction of
  `Crystalline.GlobalCrystallineSituation.wholeThickeningToAffine` on the other — and what was
  missing was only that `ringEquivOfIso` had discarded the divided power structure, so nothing
  joined them.

## What is and is not proved

Everything here is proved, with no hypothesis beyond the standing `[IsAffine S.X]`,
`[IsAffine S.S.scheme]` and nilpotence of `p` that
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` itself carries.

The module note of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsQuasiCoherentToPairs.lean` said of the field
`ringEquiv` of `...SmallSite.PreReduction07JG` that it "asks for `D` to be the *limit* of the
section rings of the levels, which is exactly the identification of the completed divided power
envelope of [Stacks, Tag 07J8] that [Stacks, Tag 07JN] supplies and this library does not
have", and listed `ringEquiv` among "the fields that have no inhabitant".  **That is now out of
date**: `...SmallSite.envelopeLevelRingLimitEquiv` is that field at `D = D(n)` for the system
[Stacks, Tag 07JN] works over.  Surjectivity is the only place the shift `e ↦ N + e` costs
anything: the levels start at the uniform cutoff `N` past which the divided powers descend, so
the Cauchy sequence fed to `IsPrecomplete` is the reindexing `k ↦ f (k - N)` of the lifts.

What remains missing of
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG` is `functor` with its
`sections` clauses and the pair `baseChange`, `baseChange_tmul` — the small-site form of
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`, which is constructed only
for `ℱ = 𝒪_{X/S}`.  So no term of that bundle is produced here and **no `@[stacks 07JG]`
attribute is placed in this module**: what is here is one field of a hypothesis bundle, not a
clause of the tag's own statement, and `...CrystalsQuasiCoherentToPairs` records that no tag
may be stated against the bundle.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u v w

noncomputable section

namespace Crystalline.DividedPowerThickening

variable {s : AffineCrystallineSituation.{u, v}}

/-- **An isomorphism of divided power thickenings is a ring isomorphism of their rings.**  Both
directions are the underlying ring maps of the two divided power morphisms, and the two
round-trip identities are the two identities of the isomorphism read on rings. -/
def ringEquivOfIso {X Y : DividedPowerThickening.{u, v, w} s} (e : X ≅ Y) :
    (X.ring : Type w) ≃+* (Y.ring : Type w) where
  toFun := e.hom.hom.toRingHom
  invFun := e.inv.hom.toRingHom
  left_inv x := congrArg (fun f : X ⟶ X ↦ f.hom.toRingHom x) e.hom_inv_id
  right_inv x := congrArg (fun f : Y ⟶ Y ↦ f.hom.toRingHom x) e.inv_hom_id
  map_mul' := map_mul _
  map_add' := map_add _

/-- The ring isomorphism `ringEquivOfIso e` acts as the underlying ring map of `e.hom`. -/
@[simp]
theorem ringEquivOfIso_apply {X Y : DividedPowerThickening.{u, v, w} s} (e : X ≅ Y)
    (x : (X.ring : Type w)) : ringEquivOfIso e x = e.hom.hom.toRingHom x := rfl

/-- **The ring isomorphism attached to an isomorphism of divided power thickenings is a
morphism of divided powers.**

`Crystalline.DividedPowerThickening.ringEquivOfIso` keeps only the underlying ring map of the
two divided power morphisms and forgets that they are divided power morphisms at all; this
recovers the forgotten half.  Both clauses are already carried by the morphism `e.hom`, whose
underlying `DividedPowers.DPMorphism` has them as fields — the point is only that the ring
equivalence and that morphism have the same underlying function, so the fields transfer with no
proof obligation. -/
theorem isDPMorphism_ringEquivOfIso {X Y : DividedPowerThickening.{u, v, w} s} (e : X ≅ Y) :
    DividedPowers.IsDPMorphism X.ring.dividedPowers Y.ring.dividedPowers
      (ringEquivOfIso e : (X.ring : Type w) →+* (Y.ring : Type w)) :=
  ⟨e.hom.hom.ideal_comp, fun {_} a ha ↦ e.hom.hom.dpow_comp a ha⟩

/-- **The inverse ring isomorphism is a morphism of divided powers too**, by the same reading of
`e.inv`.  Together with `Crystalline.DividedPowerThickening.isDPMorphism_ringEquivOfIso` this
says that `ringEquivOfIso e` is an *isomorphism of divided power rings* and not merely a ring
isomorphism between two rings that happen to carry divided powers. -/
theorem isDPMorphism_ringEquivOfIso_symm {X Y : DividedPowerThickening.{u, v, w} s} (e : X ≅ Y) :
    DividedPowers.IsDPMorphism Y.ring.dividedPowers X.ring.dividedPowers
      ((ringEquivOfIso e).symm : (Y.ring : Type w) →+* (X.ring : Type w)) :=
  ⟨e.inv.hom.ideal_comp, fun {_} a ha ↦ e.inv.hom.dpow_comp a ha⟩

end Crystalline.DividedPowerThickening

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

/-! ### The sections over an object transported from the affine site -/

/-- **The sections of `𝒪_{X/S}` over the object of `𝒞` that the equivalence
`𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))` of
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine` sends an affine object back
to are that object's own ring.**

The equivalence's inverse is an essential-surjectivity choice, so the transported object is
merely *isomorphic* to the `Spec` of the affine object and its section ring is not that object's
ring on the nose.  The counit supplies the isomorphism, and this is it read on rings. -/
def wholeSiteInverseSectionsRingEquiv
    (Y : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)) :
    ((structureSheaf S).obj.obj
        (op ((wholeSiteEquivLittleAffine hp).inverse.obj Y).unop.obj) : Type u) ≃+*
      (Y.obj.ring : Type u) :=
  DividedPowerThickening.ringEquivOfIso
    ((affineIsCrystalline hp).ι.mapIso ((wholeSiteEquivLittleAffine hp).counitIso.app Y))

omit [WholeSpacePresentation S hp] in
/-- **The identification of the section rings is natural.**  A morphism `φ : Y₁ ⟶ Y₂` of
`Cris(Γ(X, ⊤)/Γ(S, ⊤))` is carried by the equivalence to a morphism of `Cris(X/S)` the other
way round, and restricting sections along it is, through the identification, the ring map of
`φ`.  The proof is the naturality of the counit and nothing else: the restriction map of
`𝒪_{X/S}` along the transported morphism *is* the affine-side ring map by construction of the
bridge `Crystalline.GlobalCrystallineSituation.wholeSiteToAffine`. -/
theorem wholeSiteInverseSectionsRingEquiv_naturality
    {Y₁ Y₂ : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)}
    (φ : Y₁ ⟶ Y₂)
    (x : (structureSheaf S).obj.obj
      (op ((wholeSiteEquivLittleAffine hp).inverse.obj Y₁).unop.obj)) :
    wholeSiteInverseSectionsRingEquiv hp Y₂
        (((structureSheaf S).obj.map
          ((wholeι S).map ((wholeSiteEquivLittleAffine hp).inverse.map φ).unop).op).hom x) =
      φ.hom.hom.toRingHom (wholeSiteInverseSectionsRingEquiv hp Y₁ x) :=
  congrArg (fun f ↦ f.hom.hom.toRingHom x)
    ((wholeSiteEquivLittleAffine hp).counitIso.hom.naturality φ)

omit [WholeSpacePresentation S hp] in
/-- **The bridge carries the divided powers of `𝒪_{X/S}` to the divided powers of the affine
object.**  The sections of `𝒪_{X/S}` over the transported object are the global sections of its
ambient divided power scheme, and the divided powers they carry are
`Crystalline.GlobalCrystallineSituation.crysDividedPowers`; the affine object carries
`Y.obj.ring.dividedPowers`.  This says the identification
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSiteInverseSectionsRingEquiv` of the two
rings matches up the two divided power structures.

Nothing is computed: the counit isomorphism of
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine` is an isomorphism of divided
power thickenings, so its underlying map already *is* a divided power morphism, and
`Crystalline.GlobalCrystallineSituation.wholeThickeningToAffine` is built so that the ring of an
affine object transported from `𝒞` is the divided power ring of global sections of its ambient
scheme, whose divided powers are `crysDividedPowers` by `rfl`.  What was missing before was only
that `ringEquivOfIso` discarded the divided power half of the counit, so the two structures could
not be compared. -/
theorem isDPMorphism_wholeSiteInverseSectionsRingEquiv
    (Y : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)) :
    DividedPowers.IsDPMorphism
      (crysDividedPowers S ((wholeSiteEquivLittleAffine hp).inverse.obj Y).unop.obj.obj)
      Y.obj.ring.dividedPowers
      (wholeSiteInverseSectionsRingEquiv hp Y :
        ((structureSheaf S).obj.obj
            (op ((wholeSiteEquivLittleAffine hp).inverse.obj Y).unop.obj) : Type u) →+*
          (Y.obj.ring : Type u)) :=
  DividedPowerThickening.isDPMorphism_ringEquivOfIso
    ((affineIsCrystalline hp).ι.mapIso ((wholeSiteEquivLittleAffine hp).counitIso.app Y))

omit [WholeSpacePresentation S hp] in
/-- **The inverse of the bridge is a divided power morphism as well**, so the identification of
the section ring with the affine object's ring is an isomorphism of divided power rings. -/
theorem isDPMorphism_wholeSiteInverseSectionsRingEquiv_symm
    (Y : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)) :
    DividedPowers.IsDPMorphism Y.obj.ring.dividedPowers
      (crysDividedPowers S ((wholeSiteEquivLittleAffine hp).inverse.obj Y).unop.obj.obj)
      ((wholeSiteInverseSectionsRingEquiv hp Y).symm :
        (Y.obj.ring : Type u) →+*
          ((structureSheaf S).obj.obj
            (op ((wholeSiteEquivLittleAffine hp).inverse.obj Y).unop.obj) : Type u)) :=
  DividedPowerThickening.isDPMorphism_ringEquivOfIso_symm
    ((affineIsCrystalline hp).ι.mapIso ((wholeSiteEquivLittleAffine hp).counitIso.app Y))

/-! ### The levels of the system of [Stacks, Tag 07JN] and their rings -/

/-- **The `p`-adically completed divided power envelope `D(n)` of [Stacks, Tag 07J8]** of the
`(n + 1)`-fold tensor power of the tautological polynomial presentation of `Γ(X, ⊤)`, as a
completed crystalline thickening of the affine situation.  This is the ring whose finite levels
are the objects of `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem`. -/
abbrev wholeSpaceSystemEnvelope (n : ℕ) :
    _root_.Crystalline.CompletedCrystallineThickening.{u, u, u} (affineSituation S hp) :=
  (_root_.Crystalline.tensorPowerEnvelopeThickening (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) n).thickening

/-- **The finite level `D(n)/(p)^{N + e}`**, as an object of the little affine crystalline
category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`.  `N` is the uniform cutoff
`Crystalline.uniformLevel` past which the divided powers descend to the quotient. -/
abbrev wholeSpaceSystemLevel (n e : ℕ) :
    _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp) :=
  _root_.Crystalline.levelThickening (wholeSpaceSystemEnvelope hp n)
    (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
    (_root_.Crystalline.isPAdicLevel_uniformLevel_add _ e)

/-- **The reduction `D(n)/(p)^{N + e'} ⟶ D(n)/(p)^{N + e}`** of the levels, for `e ≤ e'`. -/
abbrev wholeSpaceSystemLevelMap (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    wholeSpaceSystemLevel hp n e' ⟶ wholeSpaceSystemLevel hp n e :=
  _root_.Crystalline.levelThickeningMap _ _ (𝟙 (wholeSpaceSystemEnvelope hp n))
    (Nat.add_le_add_left h _)

/-- **The object of the system in bidegree `(n, e)` is the transport of the finite level.**  This
is `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem_obj_obj` written with the
level named, so that the identification of its ring below can be stated about the system. -/
theorem wholeSpaceSystem_obj_eq_level (n e : ℕ) :
    ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e =
      ((wholeSiteEquivLittleAffine hp).inverse.obj (wholeSpaceSystemLevel hp n e)).unop.obj :=
  rfl

/-- **The transition map of the system is the transport of the reduction of the levels.** -/
theorem wholeSpaceSystem_map_eq (n : ℕ) {e e' : ℕ} (h : e ⟶ e') :
    ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).map h =
      (wholeι S).map ((wholeSiteEquivLittleAffine hp).inverse.map
        (wholeSpaceSystemLevelMap hp n (leOfHom h))).unop :=
  rfl

/-- **The section ring of the level `(n, e)` of the system of [Stacks, Tag 07JN] is
`D(n)/(p)^{N + e}`.**

This is the identification that the construction of
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` left implicit: its objects
are transported across an equivalence whose inverse is an essential-surjectivity choice, so
before this nothing in the tree said what the ring of sections of a level is.  Together with
`...SmallSite.wholeSpaceSystemLevelRingEquiv_restrict` it makes the tower of section rings of
the system the tower `D(n)/(p)^{N} ← D(n)/(p)^{N+1} ← ⋯` of finite levels of the completed
envelope of [Stacks, Tag 07J8], which is the tower the source's proof of [Stacks, Tag 07JG]
takes a limit over. -/
def wholeSpaceSystemLevelRingEquiv (n e : ℕ) :
    ((structureSheaf S).obj.obj
        (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)) : Type u) ≃+*
      ((wholeSpaceSystemEnvelope hp n).ring ⧸
        DividedPowers.pAdicIdeal (A := (wholeSpaceSystemEnvelope hp n).ring)
            (affineSituation S hp).p ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) :=
  wholeSiteInverseSectionsRingEquiv hp (wholeSpaceSystemLevel hp n e)

/-- **The identifications of the level rings are compatible with the tower.**  Restricting a
section of `𝒪_{X/S}` along the transition map `T_e ⟶ T_{e'}` of the system becomes, through the
identifications, the reduction `D(n)/(p)^{N + e'} ⟶ D(n)/(p)^{N + e}`. -/
theorem wholeSpaceSystemLevelRingEquiv_restrict (n : ℕ) {e e' : ℕ} (h : e ⟶ e')
    (x : (structureSheaf S).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e'))) :
    wholeSpaceSystemLevelRingEquiv hp n e
        (((structureSheaf S).obj.map
          (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).map h).op).hom x) =
      (wholeSpaceSystemLevelMap hp n (leOfHom h)).hom.hom.toRingHom
        (wholeSpaceSystemLevelRingEquiv hp n e' x) :=
  wholeSiteInverseSectionsRingEquiv_naturality hp (wholeSpaceSystemLevelMap hp n (leOfHom h)) x

/-- **The divided powers on the sections of a level of the system of [Stacks, Tag 07JN] are the
divided powers of `D(n)/(p)^{N + e}`.**

This is the compatibility that lets `Crystalline.tensorFormsLevelEquiv` of
`ModuleDifferentials/QuotientForms.lean` be applied at the level `T(n)_e`: that statement is
about `DividedPowers.quotientDividedPowers` on `D(n)/(p)^{N + e}`, while
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso` presents the sections of
`Ω^i_{X/S}` over an affine object through
`Crystalline.GlobalCrystallineSituation.crysDividedPowers` of that object.  Before this nothing
said the two were the same divided powers, because the identification
`...SmallSite.wholeSpaceSystemLevelRingEquiv` of the two *rings* was built from a bare
`RingEquiv` that had dropped the divided power structure.

Both sides are what their constructions say they are, by `rfl`: the ring of
`Crystalline.levelThickening` is `Crystalline.dpQuotientLevelRing`, whose divided powers are
`DividedPowers.quotientDividedPowers`; and the ring of a transported object is the divided power
ring of global sections of its ambient scheme, whose divided powers are `crysDividedPowers`.  The
content is that `...SmallSite.wholeSpaceSystemLevelRingEquiv` matches them, which is
`isDPMorphism_wholeSiteInverseSectionsRingEquiv` at the level object. -/
theorem isDPMorphism_wholeSpaceSystemLevelRingEquiv (n e : ℕ) :
    DividedPowers.IsDPMorphism
      (crysDividedPowers S (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e).obj)
      (DividedPowers.quotientDividedPowers (wholeSpaceSystemEnvelope hp n).ring.ideal
        (wholeSpaceSystemEnvelope hp n).ring.dividedPowers (affineSituation S hp).p
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
        (_root_.Crystalline.isPAdicLevel_uniformLevel_add (wholeSpaceSystemEnvelope hp n) e).1
        (_root_.Crystalline.isPAdicLevel_uniformLevel_add (wholeSpaceSystemEnvelope hp n) e).2)
      (wholeSpaceSystemLevelRingEquiv hp n e :
        ((structureSheaf S).obj.obj
            (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)) : Type u) →+*
          ((wholeSpaceSystemEnvelope hp n).ring ⧸
            DividedPowers.pAdicIdeal (A := (wholeSpaceSystemEnvelope hp n).ring)
                (affineSituation S hp).p ^
              (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))) :=
  isDPMorphism_wholeSiteInverseSectionsRingEquiv hp (wholeSpaceSystemLevel hp n e)

/-- **The inverse identification is a divided power morphism too**, so the section ring of the
level `(n, e)` is `D(n)/(p)^{N + e}` *as a divided power ring*. -/
theorem isDPMorphism_wholeSpaceSystemLevelRingEquiv_symm (n e : ℕ) :
    DividedPowers.IsDPMorphism
      (DividedPowers.quotientDividedPowers (wholeSpaceSystemEnvelope hp n).ring.ideal
        (wholeSpaceSystemEnvelope hp n).ring.dividedPowers (affineSituation S hp).p
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
        (_root_.Crystalline.isPAdicLevel_uniformLevel_add (wholeSpaceSystemEnvelope hp n) e).1
        (_root_.Crystalline.isPAdicLevel_uniformLevel_add (wholeSpaceSystemEnvelope hp n) e).2)
      (crysDividedPowers S (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e).obj)
      ((wholeSpaceSystemLevelRingEquiv hp n e).symm :
        ((wholeSpaceSystemEnvelope hp n).ring ⧸
            DividedPowers.pAdicIdeal (A := (wholeSpaceSystemEnvelope hp n).ring)
                (affineSituation S hp).p ^
              (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) →+*
          ((structureSheaf S).obj.obj
            (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)) : Type u)) :=
  isDPMorphism_wholeSiteInverseSectionsRingEquiv_symm hp (wholeSpaceSystemLevel hp n e)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The reduction of the levels sends the class of `d` to the class of `d`. -/
theorem wholeSpaceSystemLevelMap_mk (n : ℕ) {e e' : ℕ} (h : e ≤ e')
    (d : (wholeSpaceSystemEnvelope hp n).ring) :
    (wholeSpaceSystemLevelMap hp n h).hom.hom.toRingHom
        (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ d :=
  rfl

/-! ### The comparison with the limit of the section rings -/

/-- **The reduction of `D(n)` to the level `e`**, as a ring homomorphism into the sections of
`𝒪_{X/S}` over that level: the quotient map `D(n) ⟶ D(n)/(p)^{N + e}` followed by the inverse
of the identification of the section ring. -/
def levelReductionRingHom (n e : ℕ) :
    ((wholeSpaceSystemEnvelope hp n).ring : Type u) →+*
      (structureSheaf S).obj.obj
        (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)) :=
  { toFun := fun d ↦ (wholeSpaceSystemLevelRingEquiv hp n e).symm (Ideal.Quotient.mk _ d)
    map_one' := by rw [map_one, map_one]
    map_mul' := fun a b ↦ by rw [map_mul, map_mul]
    map_zero' := by rw [map_zero, map_zero]
    map_add' := fun a b ↦ by rw [map_add, map_add] }

/-- The reduction of `d` to the level `e` is the image of its class modulo `(p)^{N + e}` under
the inverse identification of the section ring. -/
@[simp]
theorem levelReductionRingHom_apply (n e : ℕ) (d : (wholeSpaceSystemEnvelope hp n).ring) :
    levelReductionRingHom hp n e d =
      (wholeSpaceSystemLevelRingEquiv hp n e).symm (Ideal.Quotient.mk _ d) :=
  rfl

/-- **The reductions of `D(n)` to the levels form a compatible family**, so they define an
element of
`Crystalline.GlobalCrystallineSituation.SmallSite.levelRingLimit` of the system. -/
theorem levelReduction_mem_levelRingLimit (n : ℕ)
    (d : (wholeSpaceSystemEnvelope hp n).ring) :
    RingHom.pi (fun e ↦ levelReductionRingHom hp n e) d ∈
      levelRingLimit S ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))) := by
  intro e e' h
  refine (wholeSpaceSystemLevelRingEquiv hp n e).injective ?_
  rw [RingHom.pi_apply, RingHom.pi_apply, levelReductionRingHom_apply,
    levelReductionRingHom_apply, wholeSpaceSystemLevelRingEquiv_restrict,
    RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, wholeSpaceSystemLevelMap_mk]

/-- **The comparison map `D(n) ⟶ lim_e Γ(T(n)_e, 𝒪)`** of [Stacks, Tag 07JG]: an element of the
completed divided power envelope goes to the compatible family of its reductions to the finite
levels, read through the identification of the section rings.

The field `ringEquiv` of `Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG` is
the assertion that this map is bijective, which is `p`-adic completeness of `D(n)` read through
the shift `e ↦ N + e`. -/
def envelopeToLevelRingLimit (n : ℕ) :
    ((wholeSpaceSystemEnvelope hp n).ring : Type u) →+*
      ↥(levelRingLimit S ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n)))) :=
  RingHom.codRestrict (RingHom.pi (fun e ↦ levelReductionRingHom hp n e)) _
    (levelReduction_mem_levelRingLimit hp n)

/-- The `e`-th component of the image of `d` in the limit is the reduction of `d` to the level
`e`. -/
@[simp]
theorem envelopeToLevelRingLimit_apply_coe (n : ℕ)
    (d : (wholeSpaceSystemEnvelope hp n).ring) (e : ℕ) :
    (envelopeToLevelRingLimit hp n d).val e =
      (wholeSpaceSystemLevelRingEquiv hp n e).symm (Ideal.Quotient.mk _ d) := by
  rw [envelopeToLevelRingLimit, RingHom.codRestrict_apply, RingHom.pi_apply,
    levelReductionRingHom_apply]

/-! ### The comparison map is an isomorphism -/

section Bijective

variable (n : ℕ)

/-- Congruence modulo `I • ⊤` inside a commutative ring is equality of the classes modulo the
ideal `I`.  This is the only friction between `IsAdicComplete`, whose congruences are modulo
submodules, and the quotient rings of the levels. -/
private theorem smodEq_iff_quotient_eq {R : Type*} [CommRing R] (I : Ideal R) (x y : R) :
    x ≡ y [SMOD (I • (⊤ : Submodule R R))] ↔
      Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact SModEq.idealQuotientMk

/-- The class of `d` at the level `e` is the class of its image under the comparison map. -/
theorem mk_eq_of_envelopeToLevelRingLimit (d : (wholeSpaceSystemEnvelope hp n).ring) (e : ℕ) :
    Ideal.Quotient.mk _ d =
      wholeSpaceSystemLevelRingEquiv hp n e ((envelopeToLevelRingLimit hp n d).val e) := by
  rw [envelopeToLevelRingLimit_apply_coe, RingEquiv.apply_symm_apply]

/-- **The comparison map `D(n) ⟶ lim_e Γ(T(n)_e, 𝒪)` is injective.**  An element in the kernel
reduces to zero at every level, hence lies in `(p)^{N + e}` for every `e` and so in every power
of `(p)`, and `D(n)` is `p`-adically separated. -/
theorem injective_envelopeToLevelRingLimit :
    Function.Injective (envelopeToLevelRingLimit hp n) := by
  rw [injective_iff_map_eq_zero]
  intro d hd
  refine IsHausdorff.haus (wholeSpaceSystemEnvelope hp n).isComplete.toIsHausdorff d fun k ↦ ?_
  rw [smodEq_iff_quotient_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  have h0 : (envelopeToLevelRingLimit hp n d).val k = 0 := by rw [hd]; rfl
  have hk : Ideal.Quotient.mk
      (DividedPowers.pAdicIdeal (A := (wholeSpaceSystemEnvelope hp n).ring)
          (affineSituation S hp).p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + k)) d = 0 := by
    rw [mk_eq_of_envelopeToLevelRingLimit, h0, map_zero]
  exact Ideal.pow_le_pow_right (Nat.le_add_left k _)
    (Ideal.Quotient.eq_zero_iff_mem.mp hk)

/-- **The comparison map `D(n) ⟶ lim_e Γ(T(n)_e, 𝒪)` is surjective.**  A compatible family of
sections gives, through the identification of the level rings, a compatible family of classes
in the quotients `D(n)/(p)^{N + e}`; lifting them and reindexing by `k ↦ k - N` produces a
Cauchy sequence in `D(n)`, whose limit under `p`-adic precompleteness reduces to each of
them. -/
theorem surjective_envelopeToLevelRingLimit :
    Function.Surjective (envelopeToLevelRingLimit hp n) := by
  intro a
  set N := _root_.Crystalline.uniformLevel (affineSituation S hp) with hN
  set P : Ideal ((wholeSpaceSystemEnvelope hp n).ring : Type u) :=
    DividedPowers.pAdicIdeal (A := (wholeSpaceSystemEnvelope hp n).ring)
      (affineSituation S hp).p with hP
  choose f hf using fun e : ℕ ↦ Ideal.Quotient.mk_surjective (I := P ^ (N + e))
    (wholeSpaceSystemLevelRingEquiv hp n e (a.val e))
  have hcompat : ∀ {e e' : ℕ}, e ≤ e' →
      Ideal.Quotient.mk (P ^ (N + e)) (f e) = Ideal.Quotient.mk (P ^ (N + e)) (f e') := by
    intro e e' h
    have hres := wholeSpaceSystemLevelRingEquiv_restrict hp n (homOfLE h) (a.val e')
    rw [a.2 (homOfLE h)] at hres
    rw [hf e, hres, ← hf e', wholeSpaceSystemLevelMap_mk]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (wholeSpaceSystemEnvelope hp n).isComplete.toIsPrecomplete
    (f := fun k ↦ f (k - N)) (by
      intro m k hmk
      rw [smodEq_iff_quotient_eq, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      refine Ideal.pow_le_pow_right (show m ≤ N + (m - N) by omega) ?_
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact hcompat (Nat.sub_le_sub_right hmk N))
  refine ⟨L, Subtype.ext (funext fun e ↦ ?_)⟩
  have hLe := hL (N + e)
  rw [smodEq_iff_quotient_eq, Nat.add_sub_cancel_left] at hLe
  rw [envelopeToLevelRingLimit_apply_coe, ← hLe, hf e, RingEquiv.symm_apply_apply]

/-- **The ring `D(n)` is the inverse limit of the section rings of the levels of
[Stacks, Tag 07JN]**, which is the identification of the completed divided power envelope of
[Stacks, Tag 07J8] with `lim_e Γ(T(n)_e, 𝒪)`.

This is the field `ringEquiv` of
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG` for the system
[Stacks, Tag 07JN] works over, at `D = D(n)`. -/
def envelopeLevelRingLimitEquiv :
    ((wholeSpaceSystemEnvelope hp n).ring : Type u) ≃+*
      ↥(levelRingLimit S ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n)))) :=
  RingEquiv.ofBijective (envelopeToLevelRingLimit hp n)
    ⟨injective_envelopeToLevelRingLimit hp n, surjective_envelopeToLevelRingLimit hp n⟩

/-- The `e`-th component of the image of `d` under `envelopeLevelRingLimitEquiv` is the reduction
of `d` to the level `e`. -/
@[simp]
theorem envelopeLevelRingLimitEquiv_apply_coe (d : (wholeSpaceSystemEnvelope hp n).ring)
    (e : ℕ) :
    (envelopeLevelRingLimitEquiv hp n d).val e =
      (wholeSpaceSystemLevelRingEquiv hp n e).symm (Ideal.Quotient.mk _ d) :=
  envelopeToLevelRingLimit_apply_coe hp n d e

end Bijective

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

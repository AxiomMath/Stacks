module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealAffine
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelComparisonInterchange
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningFunctorial
public import StacksFrontier.LinearAlgebra.TensorProduct.SemilinearBasisBaseChange

/-!
# The ring map `D ⊕ Ω ⟶ Γ(T'_e, 𝒪)` of a level of [Stacks, Lemma 60.17.3, Tag 07JG]

`Crystalline.GlobalCrystallineSituation.SmallSite.LevelReduction07JG` is the datum from which the
functor of [Stacks, Lemma 60.17.3, Tag 07JG] is built, and five of its eleven fields were
constructed nowhere in the tree.  Two of them are the ring map

`ψ_e : D ⊕ Ω ⟶ Γ(T'_e, 𝒪_{T'_e})`

of the level `e` and its value on the `D` summand, the fields `thickeningRingHom` and
`thickeningRingHom_p₀`.  **This module constructs them.**

The construction is forced by the splitting `Γ(T'_e, 𝒪) = Γ(T_e, 𝒪) ⊕ Γ(T_e, Ω_{T_e/S,δ})` of
[Stacks, Tag 07J2] — on sections, `Crystalline.GlobalCrystallineSituation.siteP₀_siteι_add_diff
Section`: the pair `(a, ω)` has to go to `p₀^*(a mod the level) + ω_e(ω)`, so everything rests on
a reduction `ω_e : Ω ⟶ Γ(T_e, Ω_{T_e/S,δ})` of the differentials to the level.  That reduction is
the datum `...SmallSite.LevelForms07JG` below, and it is a datum and not a construction: the
module `Ω` of the tag is arbitrary and the tree produces no map out of it.  Given it, the ring map
exists, is multiplicative, and is pinned on both summands:

* on `p₀ : D ⟶ D ⊕ Ω` it is the reduction followed by restriction along the first projection
  (`thickeningRingHom_p₀`, the field of the bundle);
* on `p₁ : D ⟶ D ⊕ Ω` it is the reduction followed by restriction along the *second* projection
  (`thickeningRingHom_p₁`), which is where the compatibility of `ω_e` with the two divided power
  derivations is used and which is what makes the comparison datum of the level semilinear for
  `p₁`;
* restricted along the diagonal it is the reduction again (`thickeningRingHom_ι`);
* and the family is compatible with the restrictions of the system
  (`thickeningRingHom_restrict`).

The module also records the small-site twin of
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`, the base change of scalars
`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪)} Γ(T, ℱ) ⟶ Γ(T', ℱ)` for a sheaf of modules on `Cris(X/S)`, and the
basis of `Γ(T', 𝒪_{T'})` over `Γ(T, 𝒪)` that the splitting gives — the geometric twin of
`Crystalline.firstOrderExtensionBasis`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.crysDerivation` — the universal divided power derivation
  on the sections over an object of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.crysFirstOrderSectionsEquiv` — the splitting
  `Γ(T', 𝒪_{T'}) = Γ(T, 𝒪_T) ⊕ Ω_{T/S,δ}` of [Stacks, Tag 07J2] as a `Γ(T, 𝒪_T)`-linear
  equivalence, and `...crysFirstOrderSectionsBasis` the basis it carries across.
* `...SmallSite.crysExtensionSectionsMap` — the base change of scalars along `p₀` on the small
  crystalline site.
* `...SmallSite.LevelForms07JG` — **the datum**: the reduction of `Ω` to the differentials of each
  level, semilinear, compatible with the derivations and with the system.
* `...SmallSite.LevelForms07JG.thickeningRingHom` — **the ring map of the level**.

## Main results

* `...SmallSite.LevelForms07JG.thickeningRingHom_p₀`, `...thickeningRingHom_p₁`,
  `...thickeningRingHom_ι`, `...thickeningRingHom_restrict` and `...thickeningRingHom_smul` — the
  four normalisations and the semilinearity listed above.
* `...SmallSite.firstOrderExtensionBasis_inl` and `...firstOrderExtensionBasis_inr` — the two
  families of members of `Crystalline.firstOrderExtensionBasis`.

## What is and is not proved

**No `@[stacks]` attribute is placed in this module and no tag is proved.**  What is settled is
that the ring map of the level is no longer a hypothesis of
`...SmallSite.LevelReduction07JG`: it is a consequence of the reduction of the differentials to
the level, together with the splitting of [Stacks, Tag 07J2] that the tree already had on
sections.

What is **carried** is `...SmallSite.LevelForms07JG` itself.  Its four fields are a map
`Ω ⟶ Γ(T_e, Ω_{T_e/S,δ})` for each level and three compatibilities, and nothing in the tree
produces that map for the system of levels of [Stacks, Proposition 60.21.1, Tag 07JN]: in that
setting it is the reduction `Ω_D ⟶ Ω_{D_e}` of the differentials of [Stacks, Tag 07J9] to the
level, and the tree has the differentials of a *scheme* over the base
(`Crystalline.GlobalCrystallineSituation.dpDifferentialsMapSheaf`) but not the comparison of the
abstract module `Ω` of the tag with them.  Bijectivity of
`...SmallSite.crysExtensionSectionsMap` is also not proved here, and is not proved anywhere in the
tree; see
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelFirstOrderBaseChange.lean`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **The universal divided power derivation on the sections over an object of `CRIS(X/S)`**, the
map `d : Γ(T, 𝒪_T) ⟶ Γ(T, Ω_{T/S,δ})` whose square-zero inclusion is the difference of the two
projections of [Stacks, Tag 07J2]; see
`Crystalline.GlobalCrystallineSituation.crysSheafRingMap_siteP₁_sub_siteP₀`. -/
def crysDerivation (A : Thickening S) (b : crysSheafRing S A) : crysDiffSections A :=
  sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b

/-- **`p₁^* = p₀^* + d` on the sections of `𝒪_{X/S}`**, the splitting of [Stacks, Tag 07J2]
rewritten as a formula for the second projection.  This is
`Crystalline.GlobalCrystallineSituation.crysSheafRingMap_siteP₁_sub_siteP₀`. -/
theorem crysSheafRingMap_siteP₁_eq (A : Thickening S) (b : crysSheafRing S A) :
    crysSheafRingMap (firstOrderThickeningSiteP₁ S A) b =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b +
        firstOrderThickeningDiffSection A (crysDerivation A b) := by
  have h : firstOrderThickeningDiffSection A (crysDerivation A b) =
      crysSheafRingMap (firstOrderThickeningSiteP₁ S A) b -
        crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b :=
    (crysSheafRingMap_siteP₁_sub_siteP₀ A b).symm
  rw [h]
  abel

/-- **Restriction along a composite of morphisms of `CRIS(X/S)`**, on the sections of
`𝒪_{X/S}`. -/
theorem crysSheafRingMap_comp {A B C : Thickening S} (f : A ⟶ B) (h : B ⟶ C)
    (x : crysSheafRing S C) :
    crysSheafRingMap f (crysSheafRingMap h x) = crysSheafRingMap (f ≫ h) x :=
  moduleSiteRestrict_comp (SheafOfModules.unit (crystallineStructureSheaf S)) f h x

/-! ### The splitting of the sections over the first-order thickening, as a basis -/

/-- **The splitting `Γ(T', 𝒪_{T'}) = Γ(T, 𝒪_T) ⊕ Ω_{T/S,δ}` of [Stacks, Tag 07J2] as a
`Γ(T, 𝒪_T)`-linear equivalence**: the pair `(b, ω)` goes to `p₀^* b + ω`, and a section `t` goes
to the pair of its restriction along the diagonal and its differential component.

The two components are linear by
`Crystalline.GlobalCrystallineSituation.crysSheafRingMapSiteιLinear` and
`Crystalline.GlobalCrystallineSituation.crysDiffPartLinear`, and that the two maps are mutually
inverse is `Crystalline.GlobalCrystallineSituation.siteP₀_siteι_add_diffSection`. -/
def crysFirstOrderSectionsEquiv (A : Thickening S) :
    (crysSheafRing S A × crysDiffSections A) ≃ₗ[crysSheafRing S A]
      crysSheafRing S (firstOrderThickeningObject S A) where
  toFun x := crysSheafRingMap (firstOrderThickeningSiteP₀ S A) x.1 +
    firstOrderThickeningDiffSection A x.2
  invFun t := (crysSheafRingMap (firstOrderThickeningSiteι S A) t, crysDiffPart A t)
  map_add' x y := by
    change crysSheafRingMap (firstOrderThickeningSiteP₀ S A) (x.1 + y.1) +
      firstOrderThickeningDiffSection A (x.2 + y.2) = _
    rw [map_add, firstOrderThickeningDiffSection_add]
    abel
  map_smul' a x := by
    change crysSheafRingMap (firstOrderThickeningSiteP₀ S A) (a * x.1) +
      firstOrderThickeningDiffSection A (a • x.2) =
        a • (crysSheafRingMap (firstOrderThickeningSiteP₀ S A) x.1 +
          firstOrderThickeningDiffSection A x.2)
    rw [smul_add, crysSheafRing_smul_def, crysSheafRing_smul_def, map_mul,
      crysSheafRingMap_siteP₀_mul_diffSection]
  left_inv x := by
    refine Prod.ext ?_ ?_
    · change crysSheafRingMap (firstOrderThickeningSiteι S A)
        (crysSheafRingMap (firstOrderThickeningSiteP₀ S A) x.1 +
          firstOrderThickeningDiffSection A x.2) = x.1
      rw [map_add, crysSheafRingMap_siteι_siteP₀, crysSheafRingMap_siteι_diffSection, add_zero]
    · change crysDiffPart A (crysSheafRingMap (firstOrderThickeningSiteP₀ S A) x.1 +
        firstOrderThickeningDiffSection A x.2) = x.2
      rw [crysDiffPart_add, crysDiffPart_siteP₀, crysDiffPart_diffSection, zero_add]
  right_inv t := siteP₀_siteι_add_diffSection A t

/-- The splitting equivalence sends the pair `(b, ω)` to `p₀^* b + ω`. -/
@[simp] theorem crysFirstOrderSectionsEquiv_apply (A : Thickening S)
    (x : crysSheafRing S A × crysDiffSections A) :
    crysFirstOrderSectionsEquiv A x =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S A) x.1 +
        firstOrderThickeningDiffSection A x.2 :=
  rfl

/-- **A basis of `Γ(T', 𝒪_{T'})` over `Γ(T, 𝒪_T)` from a basis of the differentials**: the unit
section together with the square-zero inclusions of the given basis of `Ω_{T/S,δ}`.

This is the geometric twin of `Crystalline.firstOrderExtensionBasis`, and it is what lets the
base change of the sections of a crystal along `p₀` be compared with the algebraic base change
along `D ⊕ Ω`. -/
def crysFirstOrderSectionsBasis {K : Type uI} (A : Thickening S)
    (c : Module.Basis K (crysSheafRing S A) (crysDiffSections A)) :
    Module.Basis (Unit ⊕ K) (crysSheafRing S A)
      (crysSheafRing S (firstOrderThickeningObject S A)) :=
  ((Module.Basis.singleton Unit (crysSheafRing S A)).prod c).map (crysFirstOrderSectionsEquiv A)

/-- The basis vector indexed by the `Unit` summand is the unit section `1`. -/
@[simp] theorem crysFirstOrderSectionsBasis_inl {K : Type uI} (A : Thickening S)
    (c : Module.Basis K (crysSheafRing S A) (crysDiffSections A)) (x : Unit) :
    crysFirstOrderSectionsBasis A c (Sum.inl x) = 1 := by
  have h : ((Module.Basis.singleton Unit (crysSheafRing S A)).prod c) (Sum.inl x) =
      ((1 : crysSheafRing S A), (0 : crysDiffSections A)) :=
    Prod.ext ((Module.Basis.prod_apply_inl_fst _ c x).trans
        (Module.Basis.singleton_apply Unit (crysSheafRing S A) x))
      (Module.Basis.prod_apply_inl_snd _ c x)
  show crysFirstOrderSectionsEquiv A
      (((Module.Basis.singleton Unit (crysSheafRing S A)).prod c) (Sum.inl x)) = 1
  rw [h]
  show crysSheafRingMap (firstOrderThickeningSiteP₀ S A) 1 +
    firstOrderThickeningDiffSection A 0 = 1
  rw [map_one, firstOrderThickeningDiffSection_zero, add_zero]

/-- The basis vector indexed by `i : K` is the square-zero inclusion of the basis vector `c i` of
the differentials. -/
@[simp] theorem crysFirstOrderSectionsBasis_inr {K : Type uI} (A : Thickening S)
    (c : Module.Basis K (crysSheafRing S A) (crysDiffSections A)) (i : K) :
    crysFirstOrderSectionsBasis A c (Sum.inr i) = firstOrderThickeningDiffSection A (c i) := by
  have h : ((Module.Basis.singleton Unit (crysSheafRing S A)).prod c) (Sum.inr i) =
      ((0 : crysSheafRing S A), c i) :=
    Prod.ext (Module.Basis.prod_apply_inr_fst _ c i) (Module.Basis.prod_apply_inr_snd _ c i)
  show crysFirstOrderSectionsEquiv A
      (((Module.Basis.singleton Unit (crysSheafRing S A)).prod c) (Sum.inr i)) = _
  rw [h]
  show crysSheafRingMap (firstOrderThickeningSiteP₀ S A) 0 +
    firstOrderThickeningDiffSection A (c i) = _
  rw [map_zero, zero_add]

/-! ### The base change of the sections of a crystal along `p₀`, on the small site -/

namespace SmallSite

/-- The sections of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` over an object, as a module over
the section ring of that object written in the big-site spelling
`Crystalline.GlobalCrystallineSituation.crysSheafRing`.  The two spellings of the ring are equal,
but only the second carries a `CommRing` instance, which is what a tensor product over it
needs. -/
instance moduleCrysSheafRingSections (F : SheafOfModules.{u} (structureSheaf S))
    (B : CrystallineThickening S) :
    Module (crysSheafRing S B.obj) (F.val.obj (op B)) :=
  inferInstanceAs (Module ((structureSheaf S).obj.obj (op B)) (F.val.obj (op B)))

/-- The same for the sections over the first-order universal thickening of an object. -/
instance moduleCrysSheafRingFirstOrderSections (F : SheafOfModules.{u} (structureSheaf S))
    (B : CrystallineThickening S) :
    Module (crysSheafRing S (firstOrderThickeningObject S B.obj))
      (F.val.obj (op (firstOrderThickeningCrysObject S B))) :=
  inferInstanceAs (Module ((structureSheaf S).obj.obj (op (firstOrderThickeningCrysObject S B)))
    (F.val.obj (op (firstOrderThickeningCrysObject S B))))

/-- **The restriction of sections along the first projection `p₀ : T' ⟶ T` of
[Stacks, Tag 07J2]**, for a sheaf of modules on the small crystalline site. -/
abbrev crysSectionsP₀ (F : SheafOfModules.{u} (structureSheaf S)) (B : CrystallineThickening S) :
    F.val.obj (op B) → F.val.obj (op (firstOrderThickeningCrysObject S B)) :=
  F.val.map (firstOrderThickeningCrysP₀ S B).op

/-- Restriction along `p₀` is additive. -/
theorem crysSectionsP₀_add (F : SheafOfModules.{u} (structureSheaf S))
    (B : CrystallineThickening S) (s s' : F.val.obj (op B)) :
    crysSectionsP₀ F B (s + s') = crysSectionsP₀ F B s + crysSectionsP₀ F B s' :=
  map_add _ s s'

/-- Restriction along `p₀` is semilinear for the restriction of the section rings along `p₀`. -/
theorem crysSectionsP₀_smul (F : SheafOfModules.{u} (structureSheaf S))
    (B : CrystallineThickening S) (b : crysSheafRing S B.obj) (s : F.val.obj (op B)) :
    crysSectionsP₀ F B (b • s) =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S B.obj) b • crysSectionsP₀ F B s :=
  F.val.map_smul (firstOrderThickeningCrysP₀ S B).op b s

/-- The bilinear datum of
`Crystalline.GlobalCrystallineSituation.SmallSite.crysExtensionSectionsMap`. -/
def crysExtensionSectionsAux (F : SheafOfModules.{u} (structureSheaf S))
    (B : CrystallineThickening S) :
    crysSheafRing S (firstOrderThickeningObject S B.obj) →+
      (F.val.obj (op B) →+ F.val.obj (op (firstOrderThickeningCrysObject S B))) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk' (fun s ↦ t • crysSectionsP₀ F B s)
      fun s s' ↦ by rw [crysSectionsP₀_add, smul_add])
    fun t t' ↦ by
      refine AddMonoidHom.ext fun s ↦ ?_
      change (t + t') • crysSectionsP₀ F B s = t • crysSectionsP₀ F B s + t' • crysSectionsP₀ F B s
      rw [add_smul]

/-- **The base change of the sections of a sheaf of modules on `Cris(X/S)` along `p₀`**, the map

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ) ⟶ Γ(T', ℱ)`,  `t ⊗ s ↦ t · p₀^* s`.

This is the small-site twin of
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`, written for a sheaf of modules on
`Cris(X/S)` instead of on `CRIS(X/S)`: the same formula at the same object of the category, the
ring, its first-order thickening and the two restriction maps all being the big-site ones.

Its bijectivity is the affine input of [Stacks, Tag 07J6]; on the big site it is equivalent to
bijectivity of `Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap`, by
`...GlobalCrystallineSituation.bijective_firstOrderSectionsMap_iff_bijective_extensionSectionsMap`.
Nothing below proves it. -/
def crysExtensionSectionsMap (F : SheafOfModules.{u} (structureSheaf S))
    (B : CrystallineThickening S) :
    crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →+
      F.val.obj (op (firstOrderThickeningCrysObject S B)) :=
  TensorProduct.liftAddHom (crysExtensionSectionsAux F B) fun b t s ↦ by
    change (b • t) • crysSectionsP₀ F B s = t • crysSectionsP₀ F B (b • s)
    rw [crysSectionsP₀_smul, crysSheafRing_smul_def, smul_smul, crysSheafRing_mul_comm]

/-- The extension map sends the pure tensor `t ⊗ s` to `t • p₀^* s`. -/
@[simp] theorem crysExtensionSectionsMap_tmul (F : SheafOfModules.{u} (structureSheaf S))
    (B : CrystallineThickening S) (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (s : F.val.obj (op B)) :
    crysExtensionSectionsMap F B (t ⊗ₜ[crysSheafRing S B.obj] s) = t • crysSectionsP₀ F B s :=
  rfl

/-! ### The differentials of a level, and the ring map of the level -/

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega}

/-- **The reduction of `D` to the section ring of a level**, in the big-site spelling
`Crystalline.GlobalCrystallineSituation.crysSheafRing` of that ring.  It is
`...SmallSite.LevelScalars07JG.levelRingHom` and nothing else; the two spellings of the target
are equal, and this one carries the `CommRing` instance the tensor products below need. -/
abbrev LevelScalars07JG.levelCrysRingHom (L : LevelScalars07JG S D) (e : ℕ) :
    (D : Type u) →+* crysSheafRing S (L.levelSystem.obj e).obj :=
  L.levelRingHom e

/-- **One step `T_e ⟶ T_{e + 1}` of a system of levels**, as a morphism of `CRIS(X/S)` between
the ambient objects.  The type ascription is what keeps the two spellings of the objects of
`Cris(X/S)` apart from one another in the statements below. -/
abbrev LevelScalars07JG.levelStep (L : LevelScalars07JG S D) (e : ℕ) :
    (L.levelSystem.obj e).obj ⟶ (L.levelSystem.obj (e + 1)).obj :=
  (CrystallineThickening.ι S).map (L.levelSystem.map (homOfLE (Nat.le_succ e)))

/-- **The differentials of the levels, as a compatible family of semilinear maps out of `Ω`.**

The datum is a map `Ω ⟶ Γ(T_e, Ω_{T_e/S,δ})` for each level `e`, semilinear for the reduction
`D ⟶ Γ(T_e, 𝒪_{T_e})` of `...SmallSite.LevelScalars07JG.levelRingHom`, carrying the divided power
derivation `d : D ⟶ Ω` of the situation to the universal divided power derivation of the level,
and compatible with the restrictions of the system.  In the setting of
[Stacks, Proposition 60.21.1, Tag 07JN] it is the reduction `Ω_D ⟶ Ω_{D_e}` of the module of
divided power differentials of [Stacks, Tag 07J9] to the level.

**This is a datum and not a construction**: nothing in the tree produces the map
`Ω ⟶ Γ(T_e, Ω_{T_e/S,δ})` for the system of levels of that proposition, and nothing below claims
to.  What the module does with it is build the ring map
`...SmallSite.LevelReduction07JG.thickeningRingHom` of the level and the base change of the
sections of a crystal over the first-order thickening of the level, which were the two things
that bundle carried with no construction anywhere. -/
structure LevelForms07JG (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
    (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type u) [AddCommGroup Omega]
    [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
    (d : DividedPowerDerivation A D g Omega) (L : LevelScalars07JG S D) where
  /-- The reduction of `Ω` to the differentials of the level `e`. -/
  omegaMap : ∀ e : ℕ, Omega →+ crysDiffSections (L.levelSystem.obj e).obj
  /-- It is semilinear for the reduction of `D` to the section ring of the level. -/
  omegaMap_smul : ∀ (e : ℕ) (a : (D : Type u)) (w : Omega),
    omegaMap e (a • w) = L.levelCrysRingHom e a • omegaMap e w
  /-- It carries the divided power derivation of the situation to that of the level. -/
  omegaMap_derivation : ∀ (e : ℕ) (a : (D : Type u)),
    omegaMap e (d a) = crysDerivation (L.levelSystem.obj e).obj (L.levelCrysRingHom e a)
  /-- The reductions are compatible with the restrictions of the system, read inside the section
  rings of the first-order thickenings of the levels. -/
  omegaMap_restrict : ∀ (e : ℕ) (w : Omega),
    crysSheafRingMap (firstOrderThickeningSiteMap (L.levelStep e))
        (firstOrderThickeningDiffSection (L.levelSystem.obj (e + 1)).obj
          (omegaMap (e + 1) w)) =
      firstOrderThickeningDiffSection (L.levelSystem.obj e).obj (omegaMap e w)

namespace LevelForms07JG

variable {L : LevelScalars07JG S D} (R : LevelForms07JG S A D g Omega d L)

/-- **The ring map `D ⊕ Ω ⟶ Γ(T'_e, 𝒪_{T'_e})` of a level**, the field
`...SmallSite.LevelReduction07JG.thickeningRingHom`: a pair `(a, ω)` goes to
`p₀^*(a mod the level) + ω_e(ω)`, the second summand read inside the section ring of the
first-order thickening through the splitting `Γ(T'_e, 𝒪) = Γ(T_e, 𝒪) ⊕ Γ(T_e, Ω)` of
[Stacks, Tag 07J2].

It is multiplicative because the square-zero summand is an ideal of square zero and because
`p₀^*(b) · ω = b · ω` there, which is exactly the multiplication of the trivial square-zero
extension `D ⊕ Ω`; so this is a homomorphism of divided power thickenings and not merely an
additive map. -/
def thickeningRingHom (e : ℕ) : firstOrderExtension D Omega →+*
    crysSheafRing S (firstOrderThickeningObject S (L.levelSystem.obj e).obj) where
  toFun b := crysSheafRingMap (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj)
      (L.levelCrysRingHom e b.fst) +
    firstOrderThickeningDiffSection (L.levelSystem.obj e).obj (R.omegaMap e b.snd)
  map_one' := by
    change crysSheafRingMap (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj)
        (L.levelCrysRingHom e (1 : firstOrderExtension D Omega).fst) +
      firstOrderThickeningDiffSection (L.levelSystem.obj e).obj
        (R.omegaMap e (1 : firstOrderExtension D Omega).snd) = 1
    rw [TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, map_one, map_one, map_zero,
      firstOrderThickeningDiffSection_zero, add_zero]
  map_zero' := by
    change crysSheafRingMap (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj)
        (L.levelCrysRingHom e (0 : firstOrderExtension D Omega).fst) +
      firstOrderThickeningDiffSection (L.levelSystem.obj e).obj
        (R.omegaMap e (0 : firstOrderExtension D Omega).snd) = 0
    rw [TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, map_zero, map_zero, map_zero,
      firstOrderThickeningDiffSection_zero, add_zero]
  map_add' b b' := by
    change crysSheafRingMap (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj)
        (L.levelCrysRingHom e (b + b').fst) +
      firstOrderThickeningDiffSection (L.levelSystem.obj e).obj
        (R.omegaMap e (b + b').snd) = _
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add (L.levelCrysRingHom e),
      map_add (crysSheafRingMap (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj)),
      map_add (R.omegaMap e), firstOrderThickeningDiffSection_add]
    abel
  map_mul' b b' := by
    have h0 : firstOrderThickeningDiffSection (L.levelSystem.obj e).obj (R.omegaMap e b.snd) *
        firstOrderThickeningDiffSection (L.levelSystem.obj e).obj (R.omegaMap e b'.snd) = 0 :=
      firstOrderThickeningDiffSection_mul _ _ _
    have h1 : R.omegaMap e (b * b').snd =
        L.levelCrysRingHom e b.fst • R.omegaMap e b'.snd +
          L.levelCrysRingHom e b'.fst • R.omegaMap e b.snd := by
      rw [TrivSqZeroExt.snd_mul, op_smul_eq_smul, map_add, R.omegaMap_smul, R.omegaMap_smul]
    change crysSheafRingMap (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj)
        (L.levelCrysRingHom e (b * b').fst) +
      firstOrderThickeningDiffSection (L.levelSystem.obj e).obj
        (R.omegaMap e (b * b').snd) = _
    rw [h1, firstOrderThickeningDiffSection_add, ← crysSheafRingMap_siteP₀_mul_diffSection,
      ← crysSheafRingMap_siteP₀_mul_diffSection, TrivSqZeroExt.fst_mul, map_mul, map_mul]
    linear_combination -h0

/-- The ring map of level `e` sends `b = (a, ω)` to `p₀^*(a mod the level) + ω_e(ω)`. -/
theorem thickeningRingHom_apply (e : ℕ) (b : firstOrderExtension D Omega) :
    R.thickeningRingHom e b =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj)
          (L.levelCrysRingHom e b.fst) +
        firstOrderThickeningDiffSection (L.levelSystem.obj e).obj (R.omegaMap e b.snd) :=
  rfl

/-- **On the `D` summand the ring map of the level is the reduction followed by `p₀`**, which is
the field `...SmallSite.LevelReduction07JG.thickeningRingHom_p₀`. -/
theorem thickeningRingHom_p₀ (e : ℕ) (a : (D : Type u)) :
    R.thickeningRingHom e (firstOrderP₀ D Omega a) =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj)
        (L.levelCrysRingHom e a) := by
  rw [thickeningRingHom_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, map_zero, firstOrderThickeningDiffSection_zero, add_zero]

/-- **On the shifted summand the ring map of the level is the reduction followed by `p₁`.**  This
is the one place the compatibility of the differentials with the two derivations is used, and it
is what makes the comparison map of the level a semilinear map for `p₁` rather than for `p₀`:
`p₁^* = p₀^* + d` on sections, by
`Crystalline.GlobalCrystallineSituation.crysSheafRingMap_siteP₁_sub_siteP₀`. -/
theorem thickeningRingHom_p₁ (e : ℕ) (a : (D : Type u)) :
    R.thickeningRingHom e (firstOrderP₁ A D g Omega d a) =
      crysSheafRingMap (firstOrderThickeningSiteP₁ S (L.levelSystem.obj e).obj)
        (L.levelCrysRingHom e a) := by
  rw [thickeningRingHom_apply, firstOrderP₁_fst, firstOrderP₁_snd, R.omegaMap_derivation,
    crysSheafRingMap_siteP₁_eq]

/-- **Restriction along the diagonal recovers the reduction of `D`**, the first component of the
splitting of [Stacks, Tag 07J2]: the square-zero summand dies under `i`. -/
theorem thickeningRingHom_ι (e : ℕ) (b : firstOrderExtension D Omega) :
    crysSheafRingMap (firstOrderThickeningSiteι S (L.levelSystem.obj e).obj)
        (R.thickeningRingHom e b) =
      L.levelCrysRingHom e b.fst := by
  rw [thickeningRingHom_apply, map_add, crysSheafRingMap_siteι_siteP₀,
    crysSheafRingMap_siteι_diffSection, add_zero]

/-- **The ring maps of the levels are a compatible family.**  On the `D` summand this is the
compatibility of the reductions of `D`, which is the membership condition of
`...SmallSite.levelRingLimit` read through `ringEquiv`, and on the shifted summand it is the
field `omegaMap_restrict`. -/
theorem thickeningRingHom_restrict (e : ℕ) (b : firstOrderExtension D Omega) :
    crysSheafRingMap (firstOrderThickeningSiteMap (L.levelStep e))
        (R.thickeningRingHom (e + 1) b) =
      R.thickeningRingHom e b := by
  have hP₀ := firstOrderThickeningSiteMap_comp_P₀ (L.levelStep e)
  have hring : crysSheafRingMap (L.levelStep e) (L.levelCrysRingHom (e + 1) b.fst) =
      L.levelCrysRingHom e b.fst :=
    (L.ringEquiv b.fst).2 (homOfLE (Nat.le_succ e))
  rw [thickeningRingHom_apply, thickeningRingHom_apply, map_add, R.omegaMap_restrict,
    crysSheafRingMap_comp, hP₀, ← crysSheafRingMap_comp, hring]

/-- **The ring map of the level is semilinear for the reduction of `D`**: the `D`-action on
`D ⊕ Ω` is multiplication by `p₀` of the scalar, and the `Γ(T_e, 𝒪)`-action on
`Γ(T'_e, 𝒪)` is multiplication by `p₀^*` of the scalar. -/
theorem thickeningRingHom_smul (e : ℕ) (a : (D : Type u)) (b : firstOrderExtension D Omega) :
    R.thickeningRingHom e (a • b) = L.levelCrysRingHom e a • R.thickeningRingHom e b := by
  rw [thickeningRingHom_apply, thickeningRingHom_apply, TrivSqZeroExt.fst_smul,
    TrivSqZeroExt.snd_smul, smul_eq_mul, map_mul, map_mul, R.omegaMap_smul,
    ← crysSheafRingMap_siteP₀_mul_diffSection, crysSheafRing_smul_def, mul_add]

end LevelForms07JG

/-! ### The two bases of the first-order thickening -/

/-- The first member of `Crystalline.firstOrderExtensionBasis` is the unit of `D ⊕ Ω`. -/
theorem firstOrderExtensionBasis_inl {ι : Type uI} (b : Module.Basis ι (D : Type u) Omega)
    (x : Unit) : firstOrderExtensionBasis b (Sum.inl x) = 1 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show (((Module.Basis.singleton Unit (D : Type u)).prod b) (Sum.inl x)).1 = _
    rw [Module.Basis.prod_apply_inl_fst, Module.Basis.singleton_apply, TrivSqZeroExt.fst_one]
  · show (((Module.Basis.singleton Unit (D : Type u)).prod b) (Sum.inl x)).2 = _
    rw [Module.Basis.prod_apply_inl_snd, TrivSqZeroExt.snd_one]

/-- The remaining members of `Crystalline.firstOrderExtensionBasis` are the square-zero
inclusions of the basis of `Ω`. -/
theorem firstOrderExtensionBasis_inr {ι : Type uI} (b : Module.Basis ι (D : Type u) Omega)
    (i : ι) : firstOrderExtensionBasis b (Sum.inr i) = TrivSqZeroExt.inr (b i) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show (((Module.Basis.singleton Unit (D : Type u)).prod b) (Sum.inr i)).1 = _
    rw [Module.Basis.prod_apply_inr_fst, TrivSqZeroExt.fst_inr]
  · show (((Module.Basis.singleton Unit (D : Type u)).prod b) (Sum.inr i)).2 = _
    rw [Module.Basis.prod_apply_inr_snd, TrivSqZeroExt.snd_inr]

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

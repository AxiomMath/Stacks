module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SchemeDifferentials

/-!
# Crystalline differentials and their restriction to a divided power thickening

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The *module of crystalline differentials*
`Ω_{X/S}` is the presheaf of modules on the big crystalline category `CRIS(X/S)` over the
structure presheaf `(U, T, δ) ↦ Γ(T, 𝒪_T)` whose sections at an object `(U, T, δ)` are the divided
power differentials of `Γ(T, 𝒪_T)` relative to `Γ(S, 𝒪_S)`, divided by the differentials of every
section pulled back from an open of `S`.  It carries a universal `S`-derivation `d_{X/S}` in the
sense of [Stacks, Tag 07IX], and every `S`-derivation factors uniquely through it.

An object `(U, T, δ)` of `CRIS(X/S)` restricts to each open `W` of its ambient scheme `T`, the
underlying thickening being restricted to `W` and to its preimage in `U`; these restrictions are
functorial in `W`, and the sections of `𝒪_T` over `W` are the global sections of the ambient
scheme of the restriction.  Pushing `Ω_{X/S}` forward along that functor therefore gives a
presheaf of `𝒪_T`-modules on `T`, the *restriction of `Ω_{X/S}` to `T`*.

Over an open `W` of `T` both that restriction and the presheaf of divided power differentials of
`T` over `S` of [Stacks, Tag 07IY] are the divided power differentials of the same ring modulo
the differentials of the same set of base sections, read through the two mutually inverse
identifications `Γ(W, 𝒪_T) ≅ Γ(W, 𝒪_W)`.  Hence they are isomorphic as presheaves of
`𝒪_T`-modules, compatibly with the universal differentials, and the sheaf `Ω_{T/S,δ}` is the
sheaf associated with the restriction of `Ω_{X/S}`.  This presheaf-level comparison is the input
of [Stacks, Tag 07IZ], which is stated and proved for the *sheaf* `Ω_{X/S}` on the small
crystalline site in `SmallSite/CrystallineDifferentialsSheaf.lean`
(`Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialsSheafRestrictionIso` and
`...SmallSite.crysDifferentialsSheafRestrictionIso_hom_app_d`).

## Main definitions

* `Crystalline.openTopRes` — the identification of the sections of `𝒪_X` over an open `W` with
  the global sections of the open subscheme `W`, and `Crystalline.openTopResInv` its inverse.
* `Crystalline.GlobalCrystallineSituation.crysDifferentials` — the presheaf of crystalline
  differentials `Ω_{X/S}` on `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.crysSDerivation` — the universal `S`-derivation
  `d_{X/S}`, as a `Crystalline.GlobalCrystallineSituation.SDerivation`.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLE` and
  `Thickening.restrictOpenFunctor` — the restrictions of an object of `CRIS(X/S)` to the opens of
  its ambient scheme, as a functor, and `Thickening.restrictOpenRingHom` the comparison of
  structure sheaves along it.
* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentials` — the restriction of
  `Ω_{X/S}` to the ambient scheme of an object of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.comparisonHom` — the comparison morphism from the
  presheaf of divided power differentials of `T` over `S` to that restriction, and
  `comparisonAppInv` the inverse on sections.
* `Crystalline.GlobalCrystallineSituation.restrictedToSheaf` — the restriction of `Ω_{X/S}`
  mapped into the sheaf `Ω_{T/S,δ}`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SDerivation.leibniz`, `SDerivation.app_appLE` and
  `SDerivation.app_dpow` — the Leibniz rule, the vanishing on sections pulled back from the base
  and the divided power chain rule for an `S`-derivation, on sections.
* `Crystalline.GlobalCrystallineSituation.crysSDerivation_isUniversal` — `d_{X/S}` is universal:
  every `S`-derivation of the structure presheaf of `CRIS(X/S)` is obtained from it by a unique
  map of presheaves of modules.
* `Crystalline.GlobalCrystallineSituation.comparisonIso` — the restriction of the presheaf
  `Ω_{X/S}` to the ambient scheme of `(U, T, δ)` is isomorphic, as a presheaf of `𝒪_T`-modules,
  to the presheaf of divided power differentials of `T` over `S`; the presheaf-level input of
  [Stacks, Tag 07IZ].
* `Crystalline.GlobalCrystallineSituation.comparisonHom_app_d` and
  `restrictedToSheaf_app_d` — the comparison carries `d_{T/S,δ}` to the restriction of `d_{X/S}`,
  before and after sheafification.

## Implementation notes

The open `V` of the divided power base stays universally quantified throughout, as in the source.
Both `Crystalline.GlobalCrystallineSituation.SDerivation` and
`Crystalline.DividedPowerSchemeDerivation` require the map on sections to be a divided power
`Γ(V, 𝒪_S)`-derivation for *every* open `V` of `S` receiving the ambient scheme, not for one
chosen such open, and the construction of `Ω_{X/S}` honours that by dividing out the differentials
of `Crystalline.GlobalCrystallineSituation.crysBaseSections`, the sections pulled back from *some*
open of `S`.  Fixing `V = ⊤` would give the wrong object: already for `T = Y` a scheme with
nonconstant rational functions and `f = 𝟙`, taking `V = W` forces the universal object to vanish
while the `V = ⊤` object does not.  The base ring of the ring-level construction has to be a fixed
ring, and `Γ(S, 𝒪_S)` is used for that; the `V` quantifier is carried entirely by the set of
constants that is divided out.

The object `crysDifferentials` here is the *presheaf* `(U, T, δ) ↦ Ω_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ}`,
not the sheaf `Ω_{X/S}` of [Stacks, Section 60.12]: over an object whose ambient scheme is not
affine its sections are the divided power differentials of the global functions, which in
general is a strictly smaller group than the global sections of the sheaf.  So the comparison
results of this file are statements about presheaves of `𝒪_T`-modules: `comparisonIso`
identifies the restriction of the presheaf `Ω_{X/S}` to `T` with the presheaf whose
sheafification is `Ω_{T/S,δ}`, and `restrictedToSheaf_app_d` says that the induced map into
`Ω_{T/S,δ}` carries the restriction of the presheaf-level `d_{X/S}` to `d_{T/S,δ}`.  They are the
input of [Stacks, Tag 07IZ], whose statement is about the sheaf `Ω_{X/S}` on the small site
`Cris(X/S)` and is proved, from these results, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystallineDifferentialsSheaf.lean`: there
`Ω_{X/S}` is the sheaf associated with the presheaf of this file, with its universal
`S`-derivation, and its restriction to `T_Zar` is shown to be isomorphic to `Ω_{T/S,δ}` as a
sheaf of `𝒪_T`-modules, compatibly with the universal derivations.  No part of the statements
here refers to the topology.

Three spellings have to be managed by hand.  The ring `Γ(W, 𝒪_T)` of sections over an open and
the ring `Γ(⊤, 𝒪_W)` of global sections of the open subscheme are the same ring presented
differently; `Crystalline.openTopRes` and `Crystalline.openTopResInv` are the two restriction maps
between them, used as the semilinearity along which the comparison maps go.  The module structures
on the sections of a presheaf of modules, and on a restriction of scalars along those maps, are
supplied by name, because a presheaf of modules is indexed by the structure presheaf in its
`RingCat`-valued form.  And goals mentioning such objects are not type-correct at `implicit`
transparency, so the proofs are written in term mode rather than with `rw` and `simp`.

## References

* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07HR](https://stacks.math.columbia.edu/tag/07HR)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG) — the small crystalline
  site, on which the sheaf `Ω_{X/S}` is built in `SmallSite/CrystallineDifferentialsSheaf.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-- The map on sections over the whole space induced by a morphism of schemes is the map on
global sections. -/
theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) : f.appLE ⊤ ⊤ h = f.appTop :=
  (congrArg (fun φ : Γ(X, f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ Γ(X, ⊤) ↦ f.app ⊤ ≫ φ)
      (X.presheaf.map_id (op (⊤ : X.Opens)))).trans (Category.comp_id (f.app ⊤))

/-- Equal morphisms of schemes have equal maps on sections between a fixed pair of opens. -/
theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst hfg
  rfl

/-- The identification of the sections of `𝒪_X` over an open `W` with the global sections of the
open subscheme `W`, as the map on sections of the open immersion of `W`. -/
def openTopRes {X : Scheme.{u}} (W : X.Opens) : Γ(X, W) ⟶ Γ(W.toScheme, ⊤) :=
  W.ι.appLE W ⊤ W.ι_preimage_self.ge

/-- The identification of sections is a restriction map of the structure sheaf, along the equality
`W.ι ''ᵁ ⊤ = W`. -/
theorem openTopRes_eq {X : Scheme.{u}} (W : X.Opens) :
    openTopRes W = X.presheaf.map (homOfLE (W.ι_image_le ⊤)).op := by
  rw [openTopRes, Scheme.Opens.ι_appLE]

/-- The inverse of the identification of sections, as the restriction map along `W ≤ W.ι ''ᵁ ⊤`. -/
def openTopResInv {X : Scheme.{u}} (W : X.Opens) : Γ(W.toScheme, ⊤) ⟶ Γ(X, W) :=
  X.presheaf.map (homOfLE W.ι_image_top.ge).op

theorem openTopRes_openTopResInv {X : Scheme.{u}} (W : X.Opens) :
    openTopRes W ≫ openTopResInv W = 𝟙 Γ(X, W) :=
  (congrArg (fun φ : Γ(X, W) ⟶ Γ(W.toScheme, ⊤) ↦ φ ≫ openTopResInv W)
      (openTopRes_eq W)).trans
    ((X.presheaf.map_comp (homOfLE (W.ι_image_le ⊤)).op
      (homOfLE W.ι_image_top.ge).op).symm.trans (X.presheaf.map_id (op W)))

theorem openTopResInv_openTopRes {X : Scheme.{u}} (W : X.Opens) :
    openTopResInv W ≫ openTopRes W = 𝟙 Γ(W.toScheme, ⊤) :=
  (congrArg (fun φ : Γ(X, W) ⟶ Γ(W.toScheme, ⊤) ↦ openTopResInv W ≫ φ)
      (openTopRes_eq W)).trans
    ((X.presheaf.map_comp (homOfLE W.ι_image_top.ge).op
        (homOfLE (W.ι_image_le ⊤)).op).symm.trans
      (X.presheaf.map_id (op (W.ι ''ᵁ (⊤ : W.toScheme.Opens)))))

@[simp]
theorem openTopResInv_openTopRes_apply {X : Scheme.{u}} (W : X.Opens) (x : Γ(X, W)) :
    openTopResInv W (openTopRes W x) = x :=
  (CommRingCat.comp_apply (openTopRes W) (openTopResInv W) x).symm.trans
    (congrArg (fun φ : Γ(X, W) ⟶ Γ(X, W) ↦ φ x) (openTopRes_openTopResInv W))

@[simp]
theorem openTopRes_openTopResInv_apply {X : Scheme.{u}} (W : X.Opens) (x : Γ(W.toScheme, ⊤)) :
    openTopRes W (openTopResInv W x) = x :=
  (CommRingCat.comp_apply (openTopResInv W) (openTopRes W) x).symm.trans
    (congrArg (fun φ : Γ(W.toScheme, ⊤) ⟶ Γ(W.toScheme, ⊤) ↦ φ x) (openTopResInv_openTopRes W))

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- The map from the global sections of the divided power base to the global sections of the
ambient divided power scheme of an object of `CRIS(X/S)`. -/
abbrev crysBaseAppLE (A : Thickening S) :
    Γ(S.S.scheme, ⊤) ⟶ Γ(A.thickening.target.scheme, ⊤) :=
  baseAppLE A.thickening.target S.S.scheme A.toBase.hom ⊤

/-- The global sections of the ambient divided power scheme of an object of `CRIS(X/S)` that are
pulled back from some open of the divided power base. -/
abbrev crysBaseSections (A : Thickening S) : Set Γ(A.thickening.target.scheme, ⊤) :=
  baseSections A.thickening.target S.S.scheme A.toBase.hom ⊤

/-- The base maps are compatible with the transition maps of `CRIS(X/S)`. -/
theorem crysBaseAppLE_fac {A B : Thickening S} (k : A ⟶ B) :
    (𝟙 Γ(S.S.scheme, ⊤)) ≫ crysBaseAppLE S A =
      crysBaseAppLE S B ≫ k.targetHom.hom.appTop := by
  have hb : A.toBase.hom = k.targetHom.hom ≫ B.toBase.hom := by
    rw [← DividedPowerScheme.Hom.comp_hom, k.base_naturality]
  rw [Category.id_comp]
  change baseAppLE _ _ A.toBase.hom ⊤ = baseAppLE _ _ B.toBase.hom ⊤ ≫ _
  rw [baseAppLE, baseAppLE, appLE_top_top, appLE_top_top, hb, Scheme.Hom.comp_appTop]

/-- A section pulled back from the divided power base stays pulled back from the base along the
transition maps of `CRIS(X/S)`. -/
theorem map_mem_crysBaseSections {A B : Thickening S} (k : A ⟶ B)
    {s : Γ(B.thickening.target.scheme, ⊤)} (hs : s ∈ crysBaseSections S B) :
    k.targetHom.hom.appTop s ∈ crysBaseSections S A := by
  obtain ⟨V, h, a, rfl⟩ := hs
  change _ ∈ baseSections A.thickening.target S.S.scheme A.toBase.hom ⊤
  rw [← k.base_naturality]
  refine ⟨V, ?_, a, ?_⟩
  · rw [DividedPowerScheme.Hom.comp_hom, Scheme.Hom.comp_preimage, top_le_iff.mp h]
    simp
  · have e1 := Scheme.Hom.appLE_comp_appLE k.targetHom.hom B.toBase.hom V ⊤ ⊤ h
      (le_preimage_top k.targetHom.hom (⊤ : A.thickening.target.scheme.Opens))
    rw [appLE_top_top] at e1
    exact (congrArg (fun φ : Γ(S.S.scheme, V) ⟶ Γ(A.thickening.target.scheme, ⊤) ↦ φ a) e1).symm

/-- The divided powers on the global sections of the ambient divided power scheme of an object of
`CRIS(X/S)`. -/
abbrev crysDividedPowers (A : Thickening S) :=
  A.thickening.target.dividedPowers.dividedPowers (op (⊤ : A.thickening.target.scheme.Opens))

/-- The sections of `Ω_{X/S}` over an object of `CRIS(X/S)`: the divided power differentials of
`Γ(T, 𝒪_T)` over `Γ(S, 𝒪_S)` modulo the differentials of every section pulled back from the
divided power base. -/
abbrev crysDifferentialsObj (A : Thickening S) :
    ModuleCat.{u} Γ(A.thickening.target.scheme, ⊤) :=
  dpConstDifferentials (crysBaseAppLE S A) (crysDividedPowers S A) (crysBaseSections S A)

/-- The universal differential on the sections of `Ω_{X/S}` over an object of `CRIS(X/S)`. -/
abbrev crysDifferentialsD (A : Thickening S) :
    (crysDifferentialsObj S A).Derivation (crysBaseAppLE S A) :=
  dpConstD (crysBaseAppLE S A) (crysDividedPowers S A) (crysBaseSections S A)

/-- The transition map of `Ω_{X/S}` along a morphism of `CRIS(X/S)`. -/
def crysDifferentialsMap {A B : Thickening S} (k : A ⟶ B) :
    crysDifferentialsObj S B ⟶
      (ModuleCat.restrictScalars k.targetHom.hom.appTop.hom).obj (crysDifferentialsObj S A) :=
  dpConstMap (crysBaseAppLE_fac S k) (crysDividedPowers S B) (crysDividedPowers S A)
    (k.targetHom.compatible ⊤) (crysBaseSections S B) (crysBaseSections S A)
    (fun _ hs ↦ map_mem_crysBaseSections S k hs)

@[simp]
theorem crysDifferentialsMap_d {A B : Thickening S} (k : A ⟶ B)
    (b : Γ(B.thickening.target.scheme, ⊤)) :
    crysDifferentialsMap S k ((crysDifferentialsD S B).d b) =
      (crysDifferentialsD S A).d (k.targetHom.hom.appTop b) :=
  dpConstMap_d _ _ _ _ _ _ _ b

/-- **The presheaf of crystalline differentials `Ω_{X/S}`.**  Over an object `(U, T, δ)` of
`CRIS(X/S)` its sections are the divided power differentials of `Γ(T, 𝒪_T)` relative to
`Γ(S, 𝒪_S)` modulo the differentials of all sections pulled back from the divided power base, and
the transition maps are induced by the maps on sections, which are homomorphisms of divided power
rings. -/
def crysDifferentials : PresheafOfModules.{u} (structureRingCatPresheaf S) where
  obj A := crysDifferentialsObj S A.unop
  map {_ _} i := crysDifferentialsMap S i.unop
  map_id := fun A ↦ by
    refine dpConstDifferentials_ext fun b ↦ ?_
    have hb : ((𝟙 A.unop : A.unop ⟶ A.unop).targetHom.hom).appTop b = b := by simp
    exact (crysDifferentialsMap_d S (𝟙 A.unop) b).trans
      (congrArg (fun x ↦ (crysDifferentialsD S A.unop).d x) hb)
  map_comp := fun {A B C} i j ↦ by
    refine dpConstDifferentials_ext fun b ↦ ?_
    have hb : ((j.unop ≫ i.unop).targetHom.hom).appTop b =
        j.unop.targetHom.hom.appTop (i.unop.targetHom.hom.appTop b) :=
      (congrArg (fun φ : Γ(A.unop.thickening.target.scheme, ⊤) ⟶
            Γ(C.unop.thickening.target.scheme, ⊤) ↦ φ b)
          (Scheme.Hom.comp_appTop j.unop.targetHom.hom i.unop.targetHom.hom)).trans
        (CommRingCat.comp_apply _ _ b)
    exact (crysDifferentialsMap_d S (j.unop ≫ i.unop) b).trans
      ((congrArg (fun x ↦ (crysDifferentialsD S C.unop).d x) hb).trans
        ((crysDifferentialsMap_d S j.unop (i.unop.targetHom.hom.appTop b)).symm.trans
          (congrArg (ConcreteCategory.hom (crysDifferentialsMap S j.unop))
            (crysDifferentialsMap_d S i.unop b)).symm))

@[simp]
theorem crysDifferentials_obj (A : Thickening S) :
    (crysDifferentials S).obj (op A) = crysDifferentialsObj S A := rfl

@[simp]
theorem crysDifferentials_map {A B : Thickening S} (k : A ⟶ B) :
    (crysDifferentials S).map k.op = crysDifferentialsMap S k := rfl

/-- The sections of `Ω_{X/S}` over an object of `CRIS(X/S)` as a module over the divided power
ring of global sections of the ambient divided power scheme; the two rings are the same, but the
divided power ring is a bundled object, so the instance is supplied by name. -/
instance crysDifferentialsObjModule (A : Thickening S) :
    Module ↥(A.thickening.target.dividedPowers.toDividedPowerRing
        (op (⊤ : A.thickening.target.scheme.Opens))) ↥(crysDifferentialsObj S A) :=
  inferInstanceAs (Module Γ(A.thickening.target.scheme, ⊤) ↥(crysDifferentialsObj S A))

/-- **The universal differential of `Ω_{X/S}` at an object, relative to an open of the base.**
For every open `V` of the divided power base through which the structure morphism of `(U, T, δ)`
factors, the universal differential is a divided power `Γ(V, 𝒪_S)`-derivation, because the
differentials of all sections pulled back from the base have been killed. -/
def crysDerivationAt (A : Thickening S) (V : S.S.scheme.Opens)
    (h : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V) :
    DividedPowerDerivation Γ(S.S.scheme, V)
      (A.thickening.target.dividedPowers.toDividedPowerRing
        (op (⊤ : A.thickening.target.scheme.Opens)))
      (A.toBase.hom.appLE V ⊤ h).hom (crysDifferentialsObj S A) where
  toDerivation :=
    Derivation.mk'
      (AddMonoidHom.toIntLinearMap
        (AddMonoidHom.mk' (fun x ↦ (crysDifferentialsD S A).d x)
          (ModuleCat.Derivation.d_add (crysDifferentialsD S A))))
      (ModuleCat.Derivation.d_mul (crysDifferentialsD S A))
  map_ringHom' a := dpConstD_base (crysBaseAppLE S A) (crysDividedPowers S A)
    (appLE_mem_baseSections A.thickening.target S.S.scheme A.toBase.hom ⊤ V h a)
  map_dpow' n hn x hx := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact dpConstD_dpow (crysBaseAppLE S A) (crysDividedPowers S A) (crysBaseSections S A) k x hx

/-- **The universal `S`-derivation `d_{X/S}` of the structure presheaf of `CRIS(X/S)`**, with
values in the presheaf of crystalline differentials. -/
def crysSDerivation : SDerivation S (crysDifferentials S) where
  app A x := (crysDifferentialsD S A).d x
  naturality k x := crysDifferentialsMap_d S k x
  dividedPowerDerivation A V h := crysDerivationAt S A V h
  dividedPowerDerivation_apply _ _ _ _ := rfl

@[simp]
theorem crysSDerivation_app (A : Thickening S) (x : Γ(A.thickening.target.scheme, ⊤)) :
    (crysSDerivation S).app A x = (crysDifferentialsD S A).d x := rfl

/-! ### The universal property of `Ω_{X/S}` -/

/-- The sections of a presheaf of modules over the structure presheaf of `CRIS(X/S)` at an object,
as a module over the ring of global sections of the ambient divided power scheme; the two rings
are the same, but a presheaf of modules is indexed by the structure presheaf in its
`RingCat`-valued form, so the instance is supplied by name. -/
instance moduleObjGlobalSections (F : PresheafOfModules.{u} (structureRingCatPresheaf S))
    (A : Thickening S) : Module Γ(A.thickening.target.scheme, ⊤) ↥(F.obj (op A)) :=
  inferInstanceAs (Module ((structureRingPresheaf S).obj (op A)) ↥(F.obj (op A)))

namespace SDerivation

variable {S} {F : PresheafOfModules.{u} (structureRingCatPresheaf S)}

/-- The Leibniz rule for an `S`-derivation, on sections. -/
theorem leibniz (D : SDerivation S F) (A : Thickening S)
    (x y : Γ(A.thickening.target.scheme, ⊤)) :
    D.app A (x * y) = x • D.app A y + y • D.app A x := by
  simp only [← D.dividedPowerDerivation_apply A ⊤ (le_preimage_top A.toBase.hom ⊤)]
  exact (D.dividedPowerDerivation A ⊤ (le_preimage_top A.toBase.hom ⊤)).leibniz x y

/-- An `S`-derivation kills every section pulled back from the divided power base. -/
@[simp]
theorem app_appLE (D : SDerivation S F) (A : Thickening S) (V : S.S.scheme.Opens)
    (h : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V) (a : Γ(S.S.scheme, V)) :
    D.app A (A.toBase.hom.appLE V ⊤ h a) = 0 := by
  rw [← D.dividedPowerDerivation_apply A V h]
  exact (D.dividedPowerDerivation A V h).map_ringHom a

/-- The divided power chain rule for an `S`-derivation, on sections. -/
theorem app_dpow (D : SDerivation S F) (A : Thickening S) (n : ℕ) (hn : 0 < n)
    (x : Γ(A.thickening.target.scheme, ⊤))
    (hx : x ∈ A.thickening.target.ideal.obj (op (⊤ : A.thickening.target.scheme.Opens))) :
    D.app A ((A.thickening.target.dividedPowers.toDividedPowerRing
          (op (⊤ : A.thickening.target.scheme.Opens))).dividedPowers.dpow n x) =
      (A.thickening.target.dividedPowers.toDividedPowerRing
        (op (⊤ : A.thickening.target.scheme.Opens))).dividedPowers.dpow (n - 1) x • D.app A x :=
  (D.dividedPowerDerivation_apply A ⊤ (le_preimage_top A.toBase.hom ⊤) _).symm.trans
    (((D.dividedPowerDerivation A ⊤ (le_preimage_top A.toBase.hom ⊤)).map_dpow n hn x hx).trans
      (congrArg
        (fun m ↦ (A.thickening.target.dividedPowers.toDividedPowerRing
          (op (⊤ : A.thickening.target.scheme.Opens))).dividedPowers.dpow (n - 1) x • m)
        (D.dividedPowerDerivation_apply A ⊤ (le_preimage_top A.toBase.hom ⊤) x)))

end SDerivation

section Universal

variable {S} {G : PresheafOfModules.{u} (structureRingCatPresheaf S)} (E : SDerivation S G)

/-- An `S`-derivation into `G`, read on the global sections at an object of `CRIS(X/S)` as a
derivation relative to the global sections of the divided power base. -/
def crysDescDerivation (A : Thickening S) :
    (G.obj (op A)).Derivation (crysBaseAppLE S A) :=
  ModuleCat.Derivation.mk (E.app A) (E.app_add A) (E.leibniz A)
    (fun a ↦ E.app_appLE A ⊤ (le_preimage_top A.toBase.hom ⊤) a)

/-- The map on sections at an object of `CRIS(X/S)` through which an `S`-derivation factors. -/
def crysDescApp (A : Thickening S) :
    (crysDifferentials S).obj (op A) ⟶ G.obj (op A) :=
  dpConstDesc (crysDescDerivation E A)
    (fun n x hx ↦ E.app_dpow A (n + 1) (Nat.succ_pos n) x hx)
    (fun _ hs ↦ by
      obtain ⟨V, h, a, rfl⟩ := hs
      exact E.app_appLE A V h a)

@[simp]
theorem crysDescApp_d (A : Thickening S) (x : Γ(A.thickening.target.scheme, ⊤)) :
    crysDescApp E A ((crysDifferentialsD S A).d x) = E.app A x :=
  dpConstDesc_d _ _ _ x

/-- **The factorization of an `S`-derivation through the presheaf of crystalline
differentials.** -/
def crysDescHom : crysDifferentials S ⟶ G where
  app X := crysDescApp E X.unop
  naturality {X Y} i := by
    refine dpConstDifferentials_ext fun b ↦ ?_
    have h1 := crysDifferentialsMap_d S i.unop b
    have h2 := crysDescApp_d E Y.unop (i.unop.targetHom.hom.appTop b)
    have h3 := crysDescApp_d E X.unop b
    have h4 := E.naturality i.unop b
    exact ((congrArg (fun z ↦ crysDescApp E Y.unop z) h1).trans h2).trans
      (h4.symm.trans (congrArg (fun z ↦ G.map i z) h3).symm)

@[simp]
theorem crysDescHom_app_d (A : Thickening S) (x : Γ(A.thickening.target.scheme, ⊤)) :
    (crysDescHom E).app (op A) ((crysDifferentialsD S A).d x) = E.app A x :=
  crysDescApp_d E A x

/-- The factorization through the presheaf of crystalline differentials is the only one. -/
theorem crysDescHom_unique (χ : crysDifferentials S ⟶ G)
    (hχ : ∀ (A : Thickening S) (x : Γ(A.thickening.target.scheme, ⊤)),
      χ.app (op A) ((crysDifferentialsD S A).d x) = E.app A x) :
    χ = crysDescHom E := by
  refine PresheafOfModules.hom_ext fun X ↦ ?_
  refine dpConstDifferentials_ext fun b ↦ ?_
  exact (hχ X.unop b).trans (crysDescApp_d E X.unop b).symm

end Universal

/-- **The universal property of the presheaf of crystalline differentials.**  Every
`S`-derivation of the structure presheaf of `CRIS(X/S)` factors uniquely through `d_{X/S}`. -/
theorem crysSDerivation_isUniversal : (crysSDerivation S).IsUniversal := fun _ E ↦
  ⟨crysDescHom E, fun A x ↦ crysDescApp_d E A x, fun _ hχ ↦ crysDescHom_unique E _ hχ⟩

/-! ### The restrictions of an object of `CRIS(X/S)` to the opens of its ambient scheme -/

namespace Thickening

variable {S}

/-- **The transition morphism between the restrictions of an object of `CRIS(X/S)` to two nested
opens of its ambient scheme.**  On ambient schemes it is the inclusion of open subschemes, and on
thickened schemes the inclusion of the preimages. -/
def restrictOpenLE (A : Thickening S) {W W' : A.thickening.target.scheme.Opens} (h : W ≤ W') :
    A.restrictOpen W ⟶ A.restrictOpen W' where
  sourceHom := A.thickening.source.homOfLE (A.thickening.immersion.preimage_mono h)
  targetHom := A.thickening.target.restrictLE h
  immersion_naturality := morphismRestrict_homOfLE A.thickening.immersion W W' h
  base_naturality := by
    change A.thickening.target.restrictLE h ≫
      (A.thickening.target.restrictι W' ≫ A.toBase) = _
    rw [← Category.assoc, DividedPowerScheme.restrictLE_restrictι]
    rfl
  toX_naturality := by
    change A.thickening.source.homOfLE _ ≫
      ((A.thickening.immersion ⁻¹ᵁ W').ι ≫ A.toX) = _
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl

@[simp]
theorem restrictOpenLE_targetHom (A : Thickening S) {W W' : A.thickening.target.scheme.Opens}
    (h : W ≤ W') : (A.restrictOpenLE h).targetHom = A.thickening.target.restrictLE h := rfl

@[simp]
theorem restrictOpenLE_sourceHom (A : Thickening S) {W W' : A.thickening.target.scheme.Opens}
    (h : W ≤ W') : (A.restrictOpenLE h).sourceHom =
      A.thickening.source.homOfLE (A.thickening.immersion.preimage_mono h) := rfl

/-- **The restrictions of an object of `CRIS(X/S)`, as a functor from the opens of its ambient
scheme to `CRIS(X/S)`.** -/
def restrictOpenFunctor (A : Thickening S) :
    A.thickening.target.scheme.Opens ⥤ Thickening S where
  obj W := A.restrictOpen W
  map i := A.restrictOpenLE i.le
  map_id _W :=
    Hom.ext (Scheme.homOfLE_rfl _ _)
      (DividedPowerScheme.Hom.ext (Scheme.homOfLE_rfl _ _))
  map_comp i j :=
    Hom.ext
      (Scheme.homOfLE_homOfLE A.thickening.source
        (A.thickening.immersion.preimage_mono i.le)
        (A.thickening.immersion.preimage_mono j.le)).symm
      (DividedPowerScheme.Hom.ext
        (Scheme.homOfLE_homOfLE A.thickening.target.scheme i.le j.le).symm)

@[simp]
theorem restrictOpenFunctor_obj (A : Thickening S) (W : A.thickening.target.scheme.Opens) :
    (A.restrictOpenFunctor).obj W = A.restrictOpen W := rfl

/-- The sections of `𝒪_T` over an open `W` are the global sections of the ambient scheme of the
restriction of `A` to `W`, compatibly with restriction. -/
theorem openTopRes_naturality (A : Thickening S)
    {W W' : (A.thickening.target.scheme.Opens)ᵒᵖ} (i : W ⟶ W') :
    A.thickening.target.scheme.presheaf.map i ≫ openTopRes W'.unop =
      openTopRes W.unop ≫
        (A.thickening.target.scheme.homOfLE i.unop.le).appTop := by
  have hL := Scheme.Hom.map_appLE W'.unop.ι W'.unop.ι_preimage_self.ge i
  have hR := Scheme.Hom.appLE_comp_appLE (A.thickening.target.scheme.homOfLE i.unop.le)
    W.unop.ι W.unop ⊤ ⊤ W.unop.ι_preimage_self.ge
    (le_preimage_top (A.thickening.target.scheme.homOfLE i.unop.le) ⊤)
  rw [appLE_top_top] at hR
  have hM := appLE_congr_hom (Scheme.homOfLE_ι A.thickening.target.scheme i.unop.le)
    W.unop (⊤ : W'.unop.toScheme.Opens)
    (le_of_le_of_eq (fun x _ ↦ i.unop.le x.2)
      (congrArg (fun g : W'.unop.toScheme ⟶ A.thickening.target.scheme ↦ g ⁻¹ᵁ W.unop)
        (Scheme.homOfLE_ι A.thickening.target.scheme i.unop.le).symm))
    (fun x _ ↦ i.unop.le x.2)
  exact hL.trans (hM.symm.trans hR.symm)

/-- **The comparison of the structure sheaf of the ambient scheme of `A` with the structure
presheaf of `CRIS(X/S)` pulled back along the restrictions of `A`.** -/
def restrictOpenRingHom (A : Thickening S) :
    A.thickening.target.scheme.ringCatSheaf.obj ⟶
      (A.restrictOpenFunctor).op ⋙ structureRingCatPresheaf S where
  app W := (forget₂ CommRingCat.{u} RingCat.{u}).map (openTopRes W.unop)
  naturality {W W'} i :=
    ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp
          (A.thickening.target.scheme.presheaf.map i) (openTopRes W'.unop)).symm.trans
      ((congrArg ((forget₂ CommRingCat.{u} RingCat.{u}).map) (openTopRes_naturality A i)).trans
        ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp (openTopRes W.unop)
          ((A.thickening.target.scheme.homOfLE i.unop.le).appTop)))

end Thickening

/-- **The restriction of `Ω_{X/S}` to the ambient scheme of an object of `CRIS(X/S)`.**  Its
sections over an open `W` of `T` are the sections of `Ω_{X/S}` over the restriction of `(U, T, δ)`
to `W`, viewed as a module over `Γ(W, 𝒪_T)`. -/
def restrictedCrysDifferentials (A : Thickening S) :
    A.thickening.target.scheme.PresheafOfModules :=
  (PresheafOfModules.pushforward (A.restrictOpenRingHom)).obj (crysDifferentials S)

/-! ### Comparison with the divided power differentials of the ambient scheme -/

section Comparison

variable {S} (A : Thickening S)

/-- The structure morphism of the restriction of `A` to an open is the open immersion followed by
the structure morphism of `A`. -/
theorem restrictOpen_toBase_hom (W : A.thickening.target.scheme.Opens) :
    (A.restrictOpen W).toBase.hom = W.ι ≫ A.toBase.hom := rfl

/-- The base map of the restriction of `A` to `W` is the base map over `W` followed by the
identification of sections. -/
theorem crysBaseAppLE_restrictOpen (W : A.thickening.target.scheme.Opens) :
    baseAppLE A.thickening.target S.S.scheme A.toBase.hom W ≫ openTopRes W =
      crysBaseAppLE S (A.restrictOpen W) :=
  Scheme.Hom.appLE_comp_appLE W.ι A.toBase.hom ⊤ W ⊤
    (le_preimage_top A.toBase.hom W) W.ι_preimage_self.ge

theorem comparisonFac (W : A.thickening.target.scheme.Opens) :
    (𝟙 Γ(S.S.scheme, ⊤)) ≫ crysBaseAppLE S (A.restrictOpen W) =
      baseAppLE A.thickening.target S.S.scheme A.toBase.hom W ≫ openTopRes W :=
  (Category.id_comp _).trans (crysBaseAppLE_restrictOpen A W).symm

theorem comparisonFacInv (W : A.thickening.target.scheme.Opens) :
    (𝟙 Γ(S.S.scheme, ⊤)) ≫ baseAppLE A.thickening.target S.S.scheme A.toBase.hom W =
      crysBaseAppLE S (A.restrictOpen W) ≫ openTopResInv W :=
  (Category.id_comp _).trans
    (((Category.assoc (baseAppLE A.thickening.target S.S.scheme A.toBase.hom W)
          (openTopRes W) (openTopResInv W)).trans
        ((congrArg (fun φ : Γ(A.thickening.target.scheme, W) ⟶
              Γ(A.thickening.target.scheme, W) ↦
            baseAppLE A.thickening.target S.S.scheme A.toBase.hom W ≫ φ)
          (openTopRes_openTopResInv W)).trans (Category.comp_id _))).symm.trans
      (congrArg (fun φ : Γ(S.S.scheme, ⊤) ⟶ Γ(W.toScheme, ⊤) ↦ φ ≫ openTopResInv W)
        (crysBaseAppLE_restrictOpen A W)))

/-- The identification of sections is a homomorphism of divided power rings. -/
theorem isDPMorphism_openTopRes (W : A.thickening.target.scheme.Opens) :
    DividedPowers.IsDPMorphism
      (A.thickening.target.dividedPowers.dividedPowers (op W))
      (crysDividedPowers S (A.restrictOpen W)) (openTopRes W).hom := by
  rw [openTopRes_eq]
  exact A.thickening.target.dividedPowers.naturality _

/-- The inverse identification of sections is a homomorphism of divided power rings. -/
theorem isDPMorphism_openTopResInv (W : A.thickening.target.scheme.Opens) :
    DividedPowers.IsDPMorphism (crysDividedPowers S (A.restrictOpen W))
      (A.thickening.target.dividedPowers.dividedPowers (op W)) (openTopResInv W).hom :=
  A.thickening.target.dividedPowers.naturality _

/-- The identification of sections carries a section pulled back from the base to the
corresponding section of the restriction. -/
theorem openTopRes_appLE (W : A.thickening.target.scheme.Opens) (V : S.S.scheme.Opens)
    (h : W ≤ A.toBase.hom ⁻¹ᵁ V)
    (e : (⊤ : (A.restrictOpen W).thickening.target.scheme.Opens) ≤
      (A.restrictOpen W).toBase.hom ⁻¹ᵁ V) (a : Γ(S.S.scheme, V)) :
    openTopRes W (A.toBase.hom.appLE V W h a) =
      (A.restrictOpen W).toBase.hom.appLE V ⊤ e a :=
  congrArg
    (fun φ : Γ(S.S.scheme, V) ⟶ Γ((A.restrictOpen W).thickening.target.scheme, ⊤) ↦ φ a)
    (Scheme.Hom.appLE_comp_appLE W.ι A.toBase.hom V W ⊤ h W.ι_preimage_self.ge)

theorem openTopRes_mem_crysBaseSections (W : A.thickening.target.scheme.Opens)
    {s : Γ(A.thickening.target.scheme, W)}
    (hs : s ∈ baseSections A.thickening.target S.S.scheme A.toBase.hom W) :
    openTopRes W s ∈ crysBaseSections S (A.restrictOpen W) := by
  obtain ⟨V, h, a, rfl⟩ := hs
  exact ⟨V, fun x _ ↦ h x.2, a, (openTopRes_appLE A W V h _ a).symm⟩

theorem openTopResInv_mem_baseSections (W : A.thickening.target.scheme.Opens)
    {s : Γ((A.restrictOpen W).thickening.target.scheme, ⊤)}
    (hs : s ∈ crysBaseSections S (A.restrictOpen W)) :
    openTopResInv W s ∈ baseSections A.thickening.target S.S.scheme A.toBase.hom W := by
  obtain ⟨V, e, a, rfl⟩ := hs
  have h : W ≤ A.toBase.hom ⁻¹ᵁ V := fun y hy ↦ e (x := ⟨y, hy⟩) trivial
  exact ⟨V, h, a, (openTopResInv_openTopRes_apply W (A.toBase.hom.appLE V W h a)).symm.trans
    (congrArg (fun z ↦ openTopResInv W z) (openTopRes_appLE A W V h e a))⟩

/-- **The comparison map from the divided power differentials of the ambient scheme to the
restriction of `Ω_{X/S}`**, over an open of the ambient scheme. -/
def comparisonApp (W : A.thickening.target.scheme.Opens) :
    (dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj (op W) ⟶
      (restrictedCrysDifferentials S A).obj (op W) :=
  dpConstMap (comparisonFac A W) _ _ (isDPMorphism_openTopRes A W) _ _
    (fun _ hs ↦ openTopRes_mem_crysBaseSections A W hs)

@[simp]
theorem comparisonApp_d (W : A.thickening.target.scheme.Opens)
    (b : Γ(A.thickening.target.scheme, W)) :
    (comparisonApp A W).hom ((presheafD A.thickening.target S.S.scheme A.toBase.hom W).d b) =
      (crysDifferentialsD S (A.restrictOpen W)).d (openTopRes W b) :=
  dpConstMap_d _ _ _ _ _ _ _ b

/-- The identification of sections commutes with restriction, on sections. -/
theorem openTopRes_naturality_apply
    {W W' : (A.thickening.target.scheme.Opens)ᵒᵖ} (i : W ⟶ W')
    (b : Γ(A.thickening.target.scheme, W.unop)) :
    openTopRes W'.unop (A.thickening.target.scheme.presheaf.map i b) =
      (A.thickening.target.scheme.homOfLE i.unop.le).appTop (openTopRes W.unop b) :=
  (CommRingCat.comp_apply _ _ b).symm.trans
    ((congrArg (fun φ : Γ(A.thickening.target.scheme, W.unop) ⟶ Γ(W'.unop.toScheme, ⊤) ↦ φ b)
        (Thickening.openTopRes_naturality A i)).trans (CommRingCat.comp_apply _ _ b))

/-- **The comparison morphism, input of [Stacks, Tag 07IZ].**  The universal property of the
presheaf of divided power differentials of `T` over `S` applied to the restriction of `d_{X/S}`:
a morphism of presheaves of `𝒪_T`-modules from `Ω_{T/S,δ}` before sheafification to the
restriction of `Ω_{X/S}`, carrying `d_{T/S,δ}` to the restriction of `d_{X/S}`. -/
def comparisonHom (A : Thickening S) :
    dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom ⟶
      restrictedCrysDifferentials S A where
  app W := comparisonApp A W.unop
  naturality {W W'} i := by
    refine dpConstDifferentials_ext fun b ↦ ?_
    have h1 := dpDifferentialsPresheaf_map A.thickening.target S.S.scheme A.toBase.hom i b
    have h2 := comparisonApp_d A W'.unop (A.thickening.target.scheme.presheaf.map i b)
    have h3 := comparisonApp_d A W.unop b
    have h4 := crysDifferentialsMap_d S (A.restrictOpenLE i.unop.le) (openTopRes W.unop b)
    have h5 := openTopRes_naturality_apply A i b
    exact ((congrArg (fun z ↦ (comparisonApp A W'.unop).hom z) h1).trans
      (h2.trans ((congrArg (fun z ↦ (crysDifferentialsD S (A.restrictOpen W'.unop)).d z)
        h5).trans h4.symm))).trans
          (congrArg (fun z ↦ (crysDifferentialsMap S (A.restrictOpenLE i.unop.le)).hom z)
            h3).symm

@[simp]
theorem comparisonHom_app_d (A : Thickening S) (W : A.thickening.target.scheme.Opens)
    (b : Γ(A.thickening.target.scheme, W)) :
    ((comparisonHom A).app (op W)).hom
        ((presheafD A.thickening.target S.S.scheme A.toBase.hom W).d b) =
      (crysSDerivation S).app (A.restrictOpen W) (openTopRes W b) :=
  comparisonApp_d A W b

/-- The comparison map in the other direction, semilinear along the inverse identification of
sections. -/
def comparisonAppInv₀ (W : A.thickening.target.scheme.Opens) :
    crysDifferentialsObj S (A.restrictOpen W) ⟶
      (ModuleCat.restrictScalars (openTopResInv W).hom).obj
        ((dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj (op W)) :=
  dpConstMap (comparisonFacInv A W) _ _ (isDPMorphism_openTopResInv A W) _ _
    (fun _ hs ↦ openTopResInv_mem_baseSections A W hs)

@[simp]
theorem comparisonAppInv₀_d (W : A.thickening.target.scheme.Opens)
    (b : Γ((A.restrictOpen W).thickening.target.scheme, ⊤)) :
    (comparisonAppInv₀ A W).hom ((crysDifferentialsD S (A.restrictOpen W)).d b) =
      (presheafD A.thickening.target S.S.scheme A.toBase.hom W).d (openTopResInv W b) :=
  dpConstMap_d _ _ _ _ _ _ _ b

/-- The sections of the restriction of `Ω_{X/S}` over an open `W`, as a module over the global
sections of the ambient scheme of the restricted object; the two rings are the same, but the
restriction of scalars spells the scalars differently, so the instance is supplied by name. -/
instance restrictedCrysDifferentialsModule (W : A.thickening.target.scheme.Opens) :
    Module Γ((A.restrictOpen W).thickening.target.scheme, ⊤)
      ↥((restrictedCrysDifferentials S A).obj (op W)) :=
  inferInstanceAs (Module Γ((A.restrictOpen W).thickening.target.scheme, ⊤)
    ↥(crysDifferentialsObj S (A.restrictOpen W)))

/-- The sections of the presheaf of divided power differentials over `W`, as a module over the
global sections of the ambient scheme of the restricted object along the inverse identification of
sections. -/
instance restrictScalarsDpDifferentialsModule (W : A.thickening.target.scheme.Opens) :
    Module Γ((A.restrictOpen W).thickening.target.scheme, ⊤)
      ↥((ModuleCat.restrictScalars (openTopResInv W).hom).obj
        ((dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj (op W))) :=
  ((ModuleCat.restrictScalars (openTopResInv W).hom).obj
    ((dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj (op W))).isModule

/-- The sections of the presheaf of divided power differentials over `W`, as a module over
`Γ(W, 𝒪_T)` through the restriction of scalars along the inverse identification of sections; the
underlying module is the one of the presheaf itself. -/
instance dpDifferentialsRestrictScalarsModule (W : A.thickening.target.scheme.Opens) :
    Module Γ(A.thickening.target.scheme, W)
      ↥((ModuleCat.restrictScalars (openTopResInv W).hom).obj
        ((dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj (op W))) :=
  inferInstanceAs (Module Γ(A.thickening.target.scheme, W)
    ↥((dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj (op W)))

/-- **The inverse comparison map**, read as a map of `Γ(W, 𝒪_T)`-modules: the semilinearity of
`comparisonAppInv₀` along the inverse identification cancels the semilinearity built into the
restriction of `Ω_{X/S}`. -/
def comparisonAppInv (W : A.thickening.target.scheme.Opens) :
    (restrictedCrysDifferentials S A).obj (op W) ⟶
      (dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj (op W) :=
  ModuleCat.ofHom
    (X := (restrictedCrysDifferentials S A).obj (op W))
    (Y := (dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj (op W))
    { (comparisonAppInv₀ A W).hom with
      map_smul' := fun r m ↦
        ((comparisonAppInv₀ A W).hom.map_smul (openTopRes W r) m).trans
          (congrArg (fun z : Γ(A.thickening.target.scheme, W) ↦
              z • (comparisonAppInv₀ A W).hom m)
            (openTopResInv_openTopRes_apply W r)) }

/-- The round trip through the two comparison maps on the restriction of `Ω_{X/S}`. -/
def comparisonRoundTrip (W : A.thickening.target.scheme.Opens) :
    crysDifferentialsObj S (A.restrictOpen W) ⟶ crysDifferentialsObj S (A.restrictOpen W) :=
  ModuleCat.ofHom
    (X := crysDifferentialsObj S (A.restrictOpen W))
    (Y := crysDifferentialsObj S (A.restrictOpen W))
    { toFun := fun m ↦ (comparisonApp A W).hom ((comparisonAppInv₀ A W).hom m)
      map_add' := fun m m' ↦
        (congrArg (fun z ↦ (comparisonApp A W).hom z)
            ((comparisonAppInv₀ A W).hom.map_add m m')).trans
          ((comparisonApp A W).hom.map_add _ _)
      map_smul' := fun s m ↦
        ((congrArg (fun z ↦ (comparisonApp A W).hom z)
              ((comparisonAppInv₀ A W).hom.map_smul s m)).trans
            ((comparisonApp A W).hom.map_smul (openTopResInv W s) _)).trans
          (congrArg (fun z : Γ((A.restrictOpen W).thickening.target.scheme, ⊤) ↦
              z • (comparisonApp A W).hom ((comparisonAppInv₀ A W).hom m))
            (openTopRes_openTopResInv_apply W s)) }

theorem comparisonRoundTrip_eq_id (W : A.thickening.target.scheme.Opens) :
    comparisonRoundTrip A W = 𝟙 _ :=
  dpConstDifferentials_ext fun b ↦
    (congrArg (fun z ↦ (comparisonApp A W).hom z) (comparisonAppInv₀_d A W b)).trans
      ((comparisonApp_d A W (openTopResInv W b)).trans
        (congrArg (fun z ↦ (crysDifferentialsD S (A.restrictOpen W)).d z)
          (openTopRes_openTopResInv_apply W b)))

theorem comparisonApp_comparisonAppInv₀ (W : A.thickening.target.scheme.Opens)
    (m : crysDifferentialsObj S (A.restrictOpen W)) :
    (comparisonApp A W).hom ((comparisonAppInv₀ A W).hom m) = m :=
  congrArg
    (fun φ : crysDifferentialsObj S (A.restrictOpen W) ⟶
      crysDifferentialsObj S (A.restrictOpen W) ↦ φ.hom m) (comparisonRoundTrip_eq_id A W)

/-- **The comparison isomorphism over an open of the ambient scheme.**  Both sides are the divided
power differentials of the same ring modulo the differentials of the same set of base sections, so
the two identifications of sections induce mutually inverse maps. -/
def comparisonIsoApp (W : A.thickening.target.scheme.Opens) :
    (dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj (op W) ≅
      (restrictedCrysDifferentials S A).obj (op W) where
  hom := comparisonApp A W
  inv := comparisonAppInv A W
  hom_inv_id := dpConstDifferentials_ext fun b ↦
    (congrArg (fun z ↦ (comparisonAppInv₀ A W).hom z) (comparisonApp_d A W b)).trans
      ((comparisonAppInv₀_d A W (openTopRes W b)).trans
        (congrArg (fun z ↦ (presheafD A.thickening.target S.S.scheme A.toBase.hom W).d z)
          (openTopResInv_openTopRes_apply W b)))
  inv_hom_id :=
    ModuleCat.hom_ext (LinearMap.ext fun m ↦ comparisonApp_comparisonAppInv₀ A W m)

/-- **The restriction of the presheaf `Ω_{X/S}` to the ambient scheme of an object `(U, T, δ)` of
`CRIS(X/S)` is the presheaf of divided power differentials of `T` over `S`**, as presheaves of
`𝒪_T`-modules, and the isomorphism carries the presheaf-level `d_{T/S,δ}` to the restriction of
`d_{X/S}` (`comparisonHom_app_d`).  This is an identification of presheaves; [Stacks, Tag 07IZ],
about the sheaf `Ω_{X/S}`, is
`Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialsSheafRestrictionIso`, which is
deduced from it. -/
def comparisonIso (A : Thickening S) :
    dpDifferentialsPresheaf A.thickening.target S.S.scheme A.toBase.hom ≅
      restrictedCrysDifferentials S A :=
  PresheafOfModules.isoMk (fun W ↦ comparisonIsoApp A W.unop)
    (fun {_ _} i ↦ (comparisonHom A).naturality i)

@[simp]
theorem comparisonIso_hom (A : Thickening S) :
    (comparisonIso A).hom = comparisonHom A := rfl

/-- **The restriction of the presheaf `Ω_{X/S}` to `T`, mapped into the sheaf `Ω_{T/S,δ}`**,
through the comparison isomorphism followed by the unit of the sheafification; so `Ω_{T/S,δ}` is
the sheaf associated with the restriction of the presheaf `Ω_{X/S}`.  This is only a morphism of
presheaves of `𝒪_T`-modules; the isomorphism of sheaves of [Stacks, Tag 07IZ] is
`Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialsSheafRestrictionIso`. -/
def restrictedToSheaf (A : Thickening S) :
    restrictedCrysDifferentials S A ⟶
      (Scheme.Modules.toPresheafOfModules A.thickening.target.scheme).obj
        (dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom) :=
  (comparisonIso A).inv ≫ dpDifferentialsToSheaf A.thickening.target S.S.scheme A.toBase.hom

/-- **The comparison carries the restriction of the presheaf-level `d_{X/S}` to `d_{T/S,δ}`**: the
section of the restriction of the presheaf `Ω_{X/S}` over `W` given by the restricted universal
`S`-derivation of a section `b` is sent to `d_{T/S,δ} b`.  The corresponding statement for the
sheaf `Ω_{X/S}`, part of [Stacks, Tag 07IZ], is
`Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialsSheafRestrictionIso_hom_app_d`.
-/
@[simp]
theorem restrictedToSheaf_app_d (A : Thickening S) (W : A.thickening.target.scheme.Opens)
    (b : Γ(A.thickening.target.scheme, W)) :
    ((restrictedToSheaf A).app (op W)).hom
        ((crysSDerivation S).app (A.restrictOpen W) (openTopRes W b)) =
      (universalDPSchemeDerivation A.thickening.target S.S.scheme A.toBase.hom).app W b :=
  congrArg
    (fun z ↦ (dpDifferentialsToSheaf A.thickening.target S.S.scheme A.toBase.hom).app (op W) z)
    ((comparisonAppInv₀_d A W (openTopRes W b)).trans
      (congrArg (fun z ↦ (presheafD A.thickening.target S.S.scheme A.toBase.hom W).d z)
        (openTopResInv_openTopRes_apply W b)))

end Comparison

end GlobalCrystallineSituation

end Crystalline

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantSequenceDatum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.TopDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Frobenius comparison for the étale cohomology of `𝐆_a`

Let `X` be a scheme over a field `k` of characteristic `p`. This file constructs the datum
`Stacks.ArtinSchreier.TopDegreeFrobeniusComparison` in every degree `n`. The étale cohomology
`Hⁿ(X_étale, 𝐆_a)` is identified with `Hⁿ(X, 𝒪_X)`, which is [Stacks, Tag 03P2] for
`𝐆_a = (𝒪_X)ᵃ` ([Stacks, Tag 03P6]). Under this identification the Artin–Schreier map
`x ↦ x ^ p - x` becomes `F - 1`, where `F` is the map induced on cohomology by the absolute
Frobenius `x ↦ x ^ p` of `𝒪_X`, and `F` is Frobenius-semilinear over `k`.

The comparison is built from maps that are each natural in the sheaf:
* forgetting the module structure, and [Stacks, Tag 03FD], natural in `𝒪_X`-modules
  (`moduleCohomologyIsoAbelian`);
* the isomorphism `𝒪_X ≅ ε_* 𝐆_a` of abelian sheaves on the Zariski site, which is a ring map on
  sections (`unitToPushforwardAdditiveSheafBase`);
* the edge morphism of the Leray collapse along `ε : X_étale ⟶ X_Zar`, read as
  `CategoryTheory.Sheaf.H`. This is a natural transformation (`etaleZariskiComparison`), and it is
  invertible at `𝐆_a` because the higher direct images of `𝐆_a` along `ε` vanish;
* the change of coefficient universe and of `Ext` universe.

Because each step is natural, the Frobenius of `𝐆_a` is carried to the absolute Frobenius of
`𝒪_X`, and multiplication by a scalar is carried to the module structure of `Hⁿ(X, 𝒪_X)`
(`AlgebraicGeometry.cohomologyOverFieldMap_globalSmul`).

## Main definitions

* `Stacks.ArtinSchreier.frobeniusZariski`: the absolute Frobenius of `𝒪_X` as a map of abelian
  sheaves.
* `Stacks.ArtinSchreier.etaleZariskiComparison`: `Hⁿ(X_Zar, ε_* G) ⟶ Hⁿ(X_étale, G)`, natural
  in `G`.
* `Stacks.ArtinSchreier.etaleHAdditiveSheafAddEquiv`: `Hⁿ(X_étale, 𝐆_a) ≃+ Hⁿ(X, 𝒪_X)`.
* `Stacks.ArtinSchreier.frobeniusOverField`: the Frobenius `F` on `Hⁿ(X, 𝒪_X)`.
* `Stacks.ArtinSchreier.topDegreeFrobeniusComparison`: the comparison datum, with no hypothesis
  on `X`.

## Main results

* `Stacks.ArtinSchreier.frobeniusOverField_smul`: `F (a • v) = a ^ p • F v`.
* `Stacks.ArtinSchreier.etaleHAdditiveSheafAddEquiv_artinSchreierMap`: the Artin–Schreier map
  becomes `F - 1`.

## Implementation notes

The Leray collapse and [Stacks, Tag 03P2] live at the coefficient universe `u`, which is the
morphism universe of the small étale site. So `𝐆_a` is taken there as
`AlgebraicGeometry.additiveSheafBase`, together with its own Frobenius
`Stacks.ArtinSchreier.frobeniusMapBase`. The result is then moved to `𝐆_a` at `u + 1` along
`AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`, whose naturality is
`Stacks.ArtinSchreier.smallEtaleSheafHUliftAddEquiv_map`. Instances for the small étale site are
pinned locally to the universe each step needs, because the general instances are indexed by
`max (u + 1) v`.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03P6](https://stacks.math.columbia.edu/tag/03P6)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J)
* [Stacks Project, Tag 0A3N](https://stacks.math.columbia.edu/tag/0A3N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w u v

namespace Stacks.ArtinSchreier

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt

/-- Abelian sheaves on the small étale site with coefficients at its morphism universe form a
Grothendieck abelian category, with the universe pinned so that instance search need not solve
for it. -/
local instance (priority := 3000) isGrothendieckAbelian_smallEtale_morphismUniverse
    (Y : Scheme.{u}) : IsGrothendieckAbelian.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
  Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology Y AddCommGrpCat.{u}

/-- Enough injectives for abelian sheaves on the small étale site at its morphism universe. -/
local instance (priority := 3000) enoughInjectives_smallEtale_morphismUniverse
    (Y : Scheme.{u}) : EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
  AlgebraicGeometry.enoughInjectives_sheaf_smallEtaleTopology Y

/-- `Ext` of abelian sheaves on the small étale site at its morphism universe. -/
local instance (priority := 3000) hasExt_smallEtale_morphismUniverse
    (Y : Scheme.{u}) : HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- The universe lift of the coefficients of the small étale site, from its morphism universe to
its object universe, is compatible with sheafification. -/
local instance preservesSheafification_uliftFunctor_smallEtale (Y : Scheme.{u}) :
    Y.smallEtaleTopology.PreservesSheafification AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  (etaleUlift_properties.{u, u, u + 1} Y).1

/-- The universe lift of abelian sheaves on the small étale site is additive. -/
local instance additive_uliftSheafCompose_smallEtale (Y : Scheme.{u}) :
    (sheafCompose Y.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).Additive :=
  ⟨by intros; rfl⟩

/-- The universe lift of abelian sheaves on the small étale site preserves finite limits. -/
local instance preservesFiniteLimits_uliftSheafCompose_smallEtale (Y : Scheme.{u}) :
    PreservesFiniteLimits
      (sheafCompose Y.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
  Stacks.Cohomology.CoefficientLift.uliftSheafCompose_preservesFiniteLimits.{u, u + 1} _

/-- The universe lift of abelian sheaves on the small étale site preserves finite colimits. -/
local instance preservesFiniteColimits_uliftSheafCompose_smallEtale (Y : Scheme.{u}) :
    PreservesFiniteColimits
      (sheafCompose Y.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
  Stacks.Cohomology.CoefficientLift.uliftSheafCompose_preservesFiniteColimits.{u, u + 1} _

/-- `Ext` of abelian sheaves on the small étale site at its object universe. -/
local instance (priority := 3000) hasExt_smallEtale_objectUniverse
    (Y : Scheme.{u}) : HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI : IsGrothendieckAbelian.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Y
  CategoryTheory.IsGrothendieckAbelian.hasExt _


/-! ### The structure sheaf as the direct image of `𝐆_a` -/

/-- Two composites of restriction maps of the structure sheaf between the same two opens agree,
the category of opens being a partial order. -/
theorem presheaf_map_map_eq {X : Scheme.{u}} {A B C D : (X.Opens)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (x : X.presheaf.obj A) :
    X.presheaf.map b (X.presheaf.map a x) = X.presheaf.map d (X.presheaf.map c x) := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← CommRingCat.comp_apply,
    ← Functor.map_comp, Subsingleton.elim (a ≫ b) (c ≫ d)]

/-- A composite of two restriction maps of the structure sheaf is the restriction map between
the outer two opens. -/
theorem presheaf_map_map_eq_map {X : Scheme.{u}} {A B D : (X.Opens)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ D)
    (d : A ⟶ D) (x : X.presheaf.obj A) :
    X.presheaf.map b (X.presheaf.map a x) = X.presheaf.map d x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (a ≫ b) d]

/-- **Sections of the structure sheaf over an open `V` are global functions on the open
subscheme `V`**, as a morphism from the abelian sheaf underlying `𝒪_X` to the direct image along
`ε : X_étale ⟶ X_Zar` of `𝐆_a`. Its component at `V` is `V.ι.appLE V ⊤`. -/
def unitToPushforwardAdditiveSheafBase (X : Scheme.{u}) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (smallEtaleZariskiPushforward X).obj (additiveSheafBase X) :=
  ⟨{ app V := AddCommGrpCat.ofHom
        (X := ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (SheafOfModules.unit X.ringCatSheaf)).obj.obj V)
        (Y := ((smallEtaleZariskiPushforward X).obj (additiveSheafBase X)).obj.obj V)
        (((Scheme.Opens.ι V.unop).appLE V.unop ⊤
            (Scheme.Opens.ι_preimage_self V.unop).ge).hom.toAddMonoidHom :
          Γ(X, V.unop) →+ Γ(Scheme.Opens.toScheme V.unop, ⊤))
     naturality V W h := by
      ext (x : Γ(X, V.unop))
      change (Scheme.Opens.ι W.unop).appLE W.unop ⊤ (Scheme.Opens.ι_preimage_self W.unop).ge
          (X.presheaf.map h x) =
        (X.homOfLE (leOfHom h.unop)).appTop
          ((Scheme.Opens.ι V.unop).appLE V.unop ⊤ (Scheme.Opens.ι_preimage_self V.unop).ge x)
      simp only [Scheme.Opens.ι_appLE, Scheme.homOfLE_appTop]
      exact presheaf_map_map_eq _ _ _ _ x }⟩

/-- The comparison `𝒪_X ⟶ ε_* 𝐆_a` is an isomorphism: each component `V.ι.appLE V ⊤` is the
identification of the sections of `𝒪_X` over `V` with the global functions on `V`. -/
instance isIso_unitToPushforwardAdditiveSheafBase (X : Scheme.{u}) :
    IsIso (unitToPushforwardAdditiveSheafBase X) := by
  have : IsIso ((sheafToPresheaf _ _).map (unitToPushforwardAdditiveSheafBase X)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    change IsIso ((forget₂ RingCat AddCommGrpCat).map ((forget₂ CommRingCat RingCat).map
      ((Scheme.Opens.ι V.unop).appLE V.unop ⊤ (Scheme.Opens.ι_preimage_self V.unop).ge)))
    infer_instance
  exact isIso_of_fully_faithful (sheafToPresheaf _ _) _

/-! ### The Frobenius on both sides -/

/-- If `p` vanishes on `X` then it vanishes on every open of `X`. -/
theorem natCast_eq_zero_of_opens (X : Scheme.{u}) {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0)
    (V : X.Opens) : (p : Γ(X, V)) = 0 :=
  (map_natCast (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom p).symm.trans
    ((congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom hX).trans (map_zero _))

/-- **The absolute Frobenius of `𝒪_X`**, `x ↦ x ^ p`, as an endomorphism of the abelian sheaf
underlying the structure sheaf of a scheme on which the prime `p` vanishes. It is not
`𝒪_X`-linear, only additive, which is why it lives on the abelian sheaf. -/
@[sga "3 VIIA 4.3.3" "partial", sga "7 XXI 1.0"]
def frobeniusZariski (X : Scheme.{u}) {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨{ app V := AddCommGrpCat.ofHom
        (X := ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (SheafOfModules.unit X.ringCatSheaf)).obj.obj V)
        (Y := ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (SheafOfModules.unit X.ringCatSheaf)).obj.obj V)
        ((frobeniusRingHom Γ(X, V.unop) hp (natCast_eq_zero_of_opens X hX V.unop)).toAddMonoidHom :
          Γ(X, V.unop) →+ Γ(X, V.unop))
     naturality V W h := by
      ext (x : Γ(X, V.unop))
      change (X.presheaf.map h x) ^ p = X.presheaf.map h (x ^ p)
      exact (map_pow _ x p).symm }⟩

/-- The absolute Frobenius of `𝒪_X` is `x ↦ x ^ p` on sections. -/
theorem frobeniusZariski_app (X : Scheme.{u}) {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (V : X.Opens) (x : Γ(X, V)) :
    (frobeniusZariski X hp hX).hom.app (op V) x = x ^ p :=
  rfl

/-- **The absolute Frobenius of `𝒪_X` is Frobenius-semilinear**: it carries multiplication by a
global function `c` to multiplication by `c ^ p`. -/
theorem toSheaf_map_globalSmul_comp_frobeniusZariski (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (c : Γ(X, ⊤)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map
        (globalSmul c (SheafOfModules.unit X.ringCatSheaf)) ≫ frobeniusZariski X hp hX =
      frobeniusZariski X hp hX ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map
        (globalSmul (c ^ p) (SheafOfModules.unit X.ringCatSheaf)) := by
  ext V (x : Γ(X, V.unop))
  have h1 : (globalSmul c (SheafOfModules.unit X.ringCatSheaf)).app V.unop x =
      restrictTop c V.unop * x :=
    globalSmul_app c (SheafOfModules.unit X.ringCatSheaf) V.unop x
  have h0 := natCast_eq_zero_of_opens X hX V.unop
  have h2 : (globalSmul (c ^ p) (SheafOfModules.unit X.ringCatSheaf)).app V.unop
      (frobeniusRingHom Γ(X, V.unop) hp h0 x) =
        restrictTop (c ^ p) V.unop * frobeniusRingHom Γ(X, V.unop) hp h0 x :=
    globalSmul_app (c ^ p) (SheafOfModules.unit X.ringCatSheaf) V.unop _
  change frobeniusRingHom Γ(X, V.unop) hp h0
      ((globalSmul c (SheafOfModules.unit X.ringCatSheaf)).app V.unop x) =
    (globalSmul (c ^ p) (SheafOfModules.unit X.ringCatSheaf)).app V.unop
      (frobeniusRingHom Γ(X, V.unop) hp h0 x)
  rw [h1, h2]
  change (restrictTop c V.unop * x) ^ p = restrictTop (c ^ p) V.unop * x ^ p
  rw [mul_pow, restrictTop, restrictTop, map_pow]

/-- **The Frobenius of `𝐆_a` at coefficients `AddCommGrpCat.{u}`**, `x ↦ x ^ p`. -/
def frobeniusMapBase (X : Scheme.{u}) {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) :
    additiveSheafBase X ⟶ additiveSheafBase X :=
  ⟨Functor.whiskerRight (frobeniusGlobalFunctions X hp hX)
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)⟩

/-- **The Artin–Schreier map of `𝐆_a` at coefficients `AddCommGrpCat.{u}`**, `x ↦ x ^ p - x`. -/
def artinSchreierMapBase (X : Scheme.{u}) {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) :
    additiveSheafBase X ⟶ additiveSheafBase X :=
  frobeniusMapBase X hp hX - 𝟙 _

/-- **Raising the coefficients of the Artin–Schreier map of `𝐆_a` at `AddCommGrpCat.{u}` gives
`Stacks.ArtinSchreier.artinSchreierMap`**, through
`AlgebraicGeometry.additiveSheafBaseUliftIso`. -/
theorem additiveSheafBaseUliftIso_hom_comp_artinSchreierMap (X : Scheme.{u}) {p : ℕ}
    (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) :
    (additiveSheafBaseUliftIso X).hom ≫ artinSchreierMap.{u, u + 1} X hp hX =
      (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        (artinSchreierMapBase X hp hX) ≫ (additiveSheafBaseUliftIso X).hom := by
  ext U x
  rfl

/-- **The comparison `𝒪_X ≅ ε_* 𝐆_a` intertwines the two Frobenius maps**: a ring homomorphism
commutes with `p`-th powers. -/
theorem unitToPushforwardAdditiveSheafBase_comp_frobeniusMapBase (X : Scheme.{u}) {p : ℕ}
    (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) :
    unitToPushforwardAdditiveSheafBase X ≫
        (smallEtaleZariskiPushforward X).map (frobeniusMapBase X hp hX) =
      frobeniusZariski X hp hX ≫ unitToPushforwardAdditiveSheafBase X := by
  ext V (x : Γ(X, V.unop))
  change ((Scheme.Opens.ι V.unop).appLE V.unop ⊤ (Scheme.Opens.ι_preimage_self V.unop).ge x) ^ p =
    (Scheme.Opens.ι V.unop).appLE V.unop ⊤ (Scheme.Opens.ι_preimage_self V.unop).ge (x ^ p)
  exact (map_pow _ x p).symm

/-- **The comparison `𝒪_X ≅ ε_* 𝐆_a` carries `F - 1` to the Artin–Schreier map.** -/
theorem unitToPushforwardAdditiveSheafBase_comp_artinSchreierMapBase (X : Scheme.{u}) {p : ℕ}
    (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) :
    unitToPushforwardAdditiveSheafBase X ≫
        (smallEtaleZariskiPushforward X).map (artinSchreierMapBase X hp hX) =
      (frobeniusZariski X hp hX - 𝟙 _) ≫ unitToPushforwardAdditiveSheafBase X := by
  rw [artinSchreierMapBase, Functor.map_sub, CategoryTheory.Functor.map_id, Preadditive.comp_sub,
    Preadditive.sub_comp, unitToPushforwardAdditiveSheafBase_comp_frobeniusMapBase,
    Category.comp_id, Category.id_comp]

/-! ### Naturality of the change-of-universe comparisons of cohomology -/

section ExtUniverse

variable {C : Type*} [Category* C] [Abelian C]

/-- Changing the universe of an `Ext` group is additive. -/
theorem ext_chgUniv_add [HasExt.{w} C] [HasExt.{v} C] {A B : C} {n : ℕ} (x y : Ext.{w} A B n) :
    Ext.chgUniv.{v} (x + y) = Ext.chgUniv.{v} x + Ext.chgUniv.{v} y := by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.homEquiv_chgUniv, Ext.add_hom]

/-- Changing the universe of an `Ext` group commutes with postcomposition by a morphism. -/
theorem ext_chgUniv_comp_mk₀ [HasExt.{w} C] [HasExt.{v} C] {A B D : C} {n : ℕ}
    (x : Ext.{w} A B n) (g : B ⟶ D) :
    Ext.chgUniv.{v} (x.comp (Ext.mk₀ g) (add_zero n)) =
      (Ext.chgUniv.{v} x).comp (Ext.mk₀ g) (add_zero n) := by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.homEquiv_chgUniv, Ext.comp_hom, Ext.mk₀_hom]

/-- **Changing the universe of an `Ext` group**, as an additive equivalence. -/
def extChgUnivAddEquiv [HasExt.{w} C] [HasExt.{v} C] (A B : C) (n : ℕ) :
    Ext.{w} A B n ≃+ Ext.{v} A B n where
  __ := Ext.chgUniv.{v}
  map_add' := ext_chgUniv_add

end ExtUniverse

/-- **Transport of cohomology along an isomorphism of sheaves is natural**: if `e : F ≅ G`
intertwines the endomorphisms `fF` and `fG`, then so does
`Stacks.Cohomology.CoefficientLift.sheafHIsoCongr e`. -/
theorem sheafHIsoCongr_map {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    {F G : Sheaf J AddCommGrpCat.{v}} (e : F ≅ G) {fF : F ⟶ F} {fG : G ⟶ G}
    (h : e.hom ≫ fG = fF ≫ e.hom) (n : ℕ) (x : Sheaf.H.{w} F n) :
    Stacks.Cohomology.CoefficientLift.sheafHIsoCongr e n (Sheaf.H.map fF n x) =
      Sheaf.H.map fG n (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr e n x) := by
  change (x.comp (Ext.mk₀ fF) (add_zero n)).comp (Ext.mk₀ e.hom) (add_zero n) =
    (x.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ fG) (add_zero n)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀, h]

/-- **Raising the coefficient universe of étale cohomology is natural in the sheaf.** -/
theorem smallEtaleSheafHUliftAddEquiv_map (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (g : F ⟶ G) (n : ℕ)
    (x : Sheaf.H.{u, u} F n) :
    smallEtaleSheafHUliftAddEquiv X G n (Sheaf.H.map g n x) =
      Sheaf.H.map ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map g)
        n (smallEtaleSheafHUliftAddEquiv X F n x) := by
  have hE : ∀ (F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (y : Sheaf.H.{u, u} F' n),
      smallEtaleSheafHUliftAddEquiv X F' n y =
        (Ext.mk₀ (Stacks.Cohomology.CoefficientLift.constantSheafUliftIso.{u, u + 1}
          X.smallEtaleTopology).hom).comp
          (y.mapExactFunctor (sheafCompose X.smallEtaleTopology
            AddCommGrpCat.uliftFunctor.{u + 1, u})) (zero_add n) :=
    fun _ _ => rfl
  rw [hE, hE, Sheaf.H.map_apply, Sheaf.H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- **A commuting square of isomorphisms composes**: if `e₁` and `e₂` intertwine the
endomorphisms `fA, fB` and `fB, fC` respectively, then `e₁ ≪≫ e₂` intertwines `fA` and `fC`. -/
theorem iso_trans_hom_comp_eq {C : Type*} [Category* C] {A B D : C} (e₁ : A ≅ B) (e₂ : B ≅ D)
    {fA : A ⟶ A} {fB : B ⟶ B} {fC : D ⟶ D} (h₁ : e₁.hom ≫ fB = fA ≫ e₁.hom)
    (h₂ : e₂.hom ≫ fC = fB ≫ e₂.hom) :
    (e₁ ≪≫ e₂).hom ≫ fC = fA ≫ (e₁ ≪≫ e₂).hom := by
  rw [Iso.trans_hom, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

section Comparison

variable (X : Scheme.{u})

/-- **The higher direct images of `𝐆_a` along `ε : X_étale ⟶ X_Zar` vanish.** This is
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale` for the structure module,
transported along the identification `𝐆_a ≅ (𝒪_X)ᵃ` of [Stacks, Tag 03P6]. -/
theorem isZero_rightDerived_pushforward_additiveSheafBase (q : ℕ) (hq : 0 < q) :
    IsZero (((smallEtaleZariskiPushforward X).rightDerived q).obj (additiveSheafBase X)) :=
  (isZero_rightDerived_pushforward_opensToEtale X (Scheme.unitModule X) q hq).of_iso
    (((smallEtaleZariskiPushforward X).rightDerived q).mapIso
      (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X))

/-- The final object `ε(X)` of the small étale site, the open subscheme `X ⊆ X`. -/
abbrev etaleFinal : X.Etale := (opensToEtale X).obj ⊤

open Stacks.Cohomology.FreeYonedaUnivLE in
/-- **Derived global sections over the final object are `CategoryTheory.Sheaf.H`**, as an
isomorphism of functors on abelian sheaves on the small étale site at the morphism universe. It is
`Cohomology.FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives`
read through the two identifications of the free abelian sheaf on the final object with the
constant sheaf `ULift ℤ`. -/
def rightDerivedFinalSectionsIsoExt (n : ℕ) :
    ((sheafSections (Scheme.smallEtaleTopology X) AddCommGrpCat.{u}).obj
        (op (etaleFinal X))).rightDerived n ≅
      extFunctorObj ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))) n :=
  (nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives.{u}
      (Scheme.smallEtaleTopology X) (etaleFinal X) n).some.symm ≪≫
    (extFunctor n).mapIso ((Stacks.Cohomology.FreeYonedaUnivLE.freeYonedaIso.{u}
      (Scheme.smallEtaleTopology X)).app (etaleFinal X)).symm.op ≪≫
    (extFunctor n).mapIso (Stacks.Cohomology.TerminalCohomology.freeOfTerminalIsoConstantSheaf
      (Scheme.smallEtaleTopology X) (etaleFinal X) (isTerminal_opensToEtale_top X)).symm.op

/-- **The étale-to-Zariski comparison, as a natural transformation.** For an abelian sheaf `G` on
the small étale site of `X`, at the morphism universe `u`, this is the map
`Hⁿ(X_Zar, ε_* G) ⟶ Hⁿ(X_étale, G)`: the edge morphism of the Leray collapse along
`ε : X_étale ⟶ X_Zar` followed by `rightDerivedFinalSectionsIsoExt`.

It is natural in `G` by construction, and it is an isomorphism at every `G` whose higher direct
images along `ε` vanish up to degree `n` (`isIso_etaleZariskiComparison_app`). -/
def etaleZariskiComparison (n : ℕ) :
    smallEtaleZariskiPushforward X ⋙
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op (⊤ : X.Opens))).rightDerived n ⟶
      extFunctorObj ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))) n :=
  Stacks.Cohomology.RightDerivedEdge.edge (smallEtaleZariskiPushforward X)
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : X.Opens))) n ≫ (rightDerivedFinalSectionsIsoExt X n).hom

/-- **The étale-to-Zariski comparison is an isomorphism at a sheaf whose higher direct images
vanish**, by `Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app`. -/
theorem isIso_etaleZariskiComparison_app (n : ℕ)
    (G : Sheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u})
    (hG : ∀ q, 1 ≤ q → q ≤ n →
      IsZero (((smallEtaleZariskiPushforward X).rightDerived q).obj G)) :
    IsIso ((etaleZariskiComparison X n).app G) := by
  have := Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app (smallEtaleZariskiPushforward X)
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : X.Opens))) G n hG
  exact IsIso.comp_isIso' this (Iso.isIso_hom ((rightDerivedFinalSectionsIsoExt X n).app G))

/-- **[Stacks, Tag 03P2] for the structure sheaf, on the Zariski side**: the abelian group
underlying the cohomology module `Hⁿ(X, ℳ)` is the `n`-th right derived functor of global
sections of the abelian sheaf underlying `ℳ`, naturally in morphisms of `𝒪_X`-modules. This is
the composite of `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` and
[Stacks, Tag 03FD] (`Stacks.Cohomology.ModuleComparison.underlyingSectionsIso`). -/
def moduleCohomologyIsoAbelian (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (((moduleGlobalSections X).rightDerived n).obj M) ≅
      (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : X.Opens))).rightDerived n).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
  (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤ n).app M ≪≫
    (Stacks.Cohomology.ModuleComparison.underlyingSectionsIso X.ringCatSheaf ⊤ n).app M

/-- **`moduleCohomologyIsoAbelian` is natural** in endomorphisms of `𝒪_X`-modules. -/
theorem moduleCohomologyIsoAbelian_hom_naturality {M : X.Modules} (φ : M ⟶ M) (n : ℕ) :
    (moduleCohomologyIsoAbelian X M n).hom ≫
      (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : X.Opens))).rightDerived n).map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) =
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
        (((moduleGlobalSections X).rightDerived n).map φ) ≫
      (moduleCohomologyIsoAbelian X M n).hom :=
  iso_trans_hom_comp_eq _ _
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
      n).hom.naturality φ).symm
    ((Stacks.Cohomology.ModuleComparison.underlyingSectionsIso X.ringCatSheaf ⊤
      n).hom.naturality φ).symm

/-- **[Stacks, Tag 03P2] for `𝐆_a`, on the étale side**: global sections cohomology of the
abelian sheaf `𝒪_X` on the Zariski site is the étale cohomology of `𝐆_a`, at coefficients
`AddCommGrpCat.{u}`. It is `𝒪_X ≅ ε_* 𝐆_a` followed by `etaleZariskiComparison`, an isomorphism
because the higher direct images of `𝐆_a` along `ε` vanish. -/
def abelianCohomologyIsoEtaleH (n : ℕ) :
    (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : X.Opens))).rightDerived n).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      AddCommGrpCat.of (Sheaf.H.{u, u} (additiveSheafBase X) n) :=
  (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : X.Opens))).rightDerived n).mapIso (asIso (unitToPushforwardAdditiveSheafBase X)) ≪≫
    @asIso _ _ _ _ ((etaleZariskiComparison X n).app (additiveSheafBase X))
      (isIso_etaleZariskiComparison_app X n _
        (fun q hq _ ↦ isZero_rightDerived_pushforward_additiveSheafBase X q hq))

/-- **`abelianCohomologyIsoEtaleH` is natural for maps coming from the Zariski side**: if an
endomorphism `ψ` of the abelian sheaf `𝒪_X` corresponds under `𝒪_X ≅ ε_* 𝐆_a` to the direct
image of an endomorphism `m` of `𝐆_a`, then the comparison carries the map induced by `ψ` on
Zariski cohomology to the map induced by `m` on étale cohomology. -/
theorem abelianCohomologyIsoEtaleH_hom_naturality
    (ψ : (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf))
    (m : additiveSheafBase X ⟶ additiveSheafBase X)
    (h : unitToPushforwardAdditiveSheafBase X ≫ (smallEtaleZariskiPushforward X).map m =
      ψ ≫ unitToPushforwardAdditiveSheafBase X) (n : ℕ) :
    (abelianCohomologyIsoEtaleH X n).hom ≫ AddCommGrpCat.ofHom (Sheaf.H.map m n) =
      (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : X.Opens))).rightDerived n).map ψ ≫ (abelianCohomologyIsoEtaleH X n).hom := by
  refine iso_trans_hom_comp_eq _ _ ?_ ((etaleZariskiComparison X n).naturality m).symm
  change (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : X.Opens))).rightDerived n).map (unitToPushforwardAdditiveSheafBase X) ≫
      (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : X.Opens))).rightDerived n).map ((smallEtaleZariskiPushforward X).map m) = _
  rw [← Functor.map_comp, h, Functor.map_comp]
  rfl

/-! ### The comparison and the Frobenius on the cohomology of the structure sheaf -/

/-- **The étale cohomology of `𝐆_a` is the cohomology of the structure sheaf**, at coefficients
`AddCommGrpCat.{u + 1}`, in every degree and at the `Ext` universe `u + 1`: the comparison of
[Stacks, Tag 03P2] for `𝐆_a = (𝒪_X)ᵃ` ([Stacks, Tag 03P6]).

It is `abelianCohomologyIsoEtaleH` and `moduleCohomologyIsoAbelian`, read through the
coefficient-universe lift `AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`, the identification
`AlgebraicGeometry.additiveSheafBaseUliftIso` of the lift of `𝐆_a` with `𝐆_a`. -/
def etaleHAdditiveSheafAddEquivObjectUniverse (n : ℕ) :
    Sheaf.H.{u + 1, u + 1} (additiveSheaf.{u, u + 1} X) n ≃+
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (((moduleGlobalSections X).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
      (additiveSheafBaseUliftIso X) n).symm.trans <|
    (smallEtaleSheafHUliftAddEquiv X (additiveSheafBase X) n).symm.trans <|
      ((abelianCohomologyIsoEtaleH X n).symm ≪≫
        (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).symm
        ).addCommGroupIsoToAddEquiv

/-- **The étale cohomology of `𝐆_a` is the cohomology of the structure sheaf**, in an arbitrary
`Ext` universe: `etaleHAdditiveSheafAddEquivObjectUniverse` after a change of `Ext` universe. -/
def etaleHAdditiveSheafAddEquiv [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (n : ℕ) :
    Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) n ≃+
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (((moduleGlobalSections X).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  (extChgUnivAddEquiv.{w, u + 1} _ _ n).trans (etaleHAdditiveSheafAddEquivObjectUniverse X n)

/-- **The Frobenius `F` on `Hⁿ(X, 𝒪_X)`**: the map induced on cohomology by the absolute
Frobenius `x ↦ x ^ p` of the structure sheaf, a map of abelian sheaves, read on the cohomology
module through [Stacks, Tag 03FD] (`moduleCohomologyIsoAbelian`). -/
def frobeniusCohomology {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (((moduleGlobalSections X).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf)) →+
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (((moduleGlobalSections X).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  ((moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).hom ≫
    (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : X.Opens))).rightDerived n).map (frobeniusZariski X hp hX) ≫
    (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv).hom

/-- **The Frobenius on `Hⁿ(X, 𝒪_X)` is semilinear for global functions**: it carries the map
induced by multiplication by `a ∈ Γ(X, 𝒪_X)` to the map induced by multiplication by `a ^ p`. -/
theorem frobeniusCohomology_globalSmul {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (n : ℕ) (a : Γ(X, ⊤))
    (z : (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (((moduleGlobalSections X).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf))) :
    frobeniusCohomology X hp hX n ((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
        (((moduleGlobalSections X).rightDerived n).map
          (globalSmul a (SheafOfModules.unit X.ringCatSheaf))) z) =
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
        (((moduleGlobalSections X).rightDerived n).map
          (globalSmul (a ^ p) (SheafOfModules.unit X.ringCatSheaf)))
        (frobeniusCohomology X hp hX n z) := by
  set R := ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op (⊤ : X.Opens))).rightDerived n
  set e := moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n
  have hnat := fun b : Γ(X, ⊤) =>
    moduleCohomologyIsoAbelian_hom_naturality X
      (globalSmul b (SheafOfModules.unit X.ringCatSheaf)) n
  have hinv := fun b : Γ(X, ⊤) => (CommSq.horiz_inv ⟨hnat b⟩).w.symm
  have key : (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
        (((moduleGlobalSections X).rightDerived n).map
          (globalSmul a (SheafOfModules.unit X.ringCatSheaf))) ≫
        (e.hom ≫ R.map (frobeniusZariski X hp hX) ≫ e.inv) =
      (e.hom ≫ R.map (frobeniusZariski X hp hX) ≫ e.inv) ≫
        (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
          (((moduleGlobalSections X).rightDerived n).map
            (globalSmul (a ^ p) (SheafOfModules.unit X.ringCatSheaf))) := by
    rw [← Category.assoc, ← hnat a, Category.assoc, ← Category.assoc (R.map _),
      ← Functor.map_comp, toSheaf_map_globalSmul_comp_frobeniusZariski, Functor.map_comp,
      Category.assoc, hinv, Category.assoc, Category.assoc]
  exact ConcreteCategory.congr_hom key z

/-- **Under the comparison of [Stacks, Tag 03P2], the Artin–Schreier map becomes `F - 1`.** -/
theorem etaleHAdditiveSheafAddEquivObjectUniverse_artinSchreierMap {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} (additiveSheaf.{u, u + 1} X) n) :
    etaleHAdditiveSheafAddEquivObjectUniverse X n
        (Sheaf.H.map (artinSchreierMap.{u, u + 1} X hp hX) n x) =
      frobeniusCohomology X hp hX n (etaleHAdditiveSheafAddEquivObjectUniverse X n x) -
        etaleHAdditiveSheafAddEquivObjectUniverse X n x := by
  have h2 := Function.Semiconj.inverse_left
    (sheafHIsoCongr_map _ (additiveSheafBaseUliftIso_hom_comp_artinSchreierMap X hp hX) n)
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr _ n).symm_apply_apply
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr _ n).apply_symm_apply
  have h3 := Function.Semiconj.inverse_left
    (smallEtaleSheafHUliftAddEquiv_map X (artinSchreierMapBase X hp hX) n)
    (smallEtaleSheafHUliftAddEquiv X _ n).symm_apply_apply
    (smallEtaleSheafHUliftAddEquiv X _ n).apply_symm_apply
  have hn := abelianCohomologyIsoEtaleH_hom_naturality X (frobeniusZariski X hp hX - 𝟙 _)
    (artinSchreierMapBase X hp hX)
    (unitToPushforwardAdditiveSheafBase_comp_artinSchreierMapBase X hp hX) n
  have h4 := (CommSq.horiz_inv ⟨hn⟩).w
  have := Stacks.DerivedLinear.rightDerived_additive
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : X.Opens))) n
  have h5 : ∀ y, (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv
      ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : X.Opens))).rightDerived n).map (frobeniusZariski X hp hX - 𝟙 _) y) =
      frobeniusCohomology X hp hX n
        ((moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv y) -
      (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv y := by
    intro y
    rw [Functor.map_sub, CategoryTheory.Functor.map_id]
    change (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv
      ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : X.Opens))).rightDerived n).map (frobeniusZariski X hp hX) y - y) = _
    rw [map_sub]
    congr 1
    change _ = (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv
      ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : X.Opens))).rightDerived n).map (frobeniusZariski X hp hX)
        ((moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).hom
          ((moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv y)))
    rw [Iso.inv_hom_id_apply]
  change (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv
    ((abelianCohomologyIsoEtaleH X n).inv
      ((smallEtaleSheafHUliftAddEquiv X (additiveSheafBase X) n).symm
      ((Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
        (additiveSheafBaseUliftIso X) n).symm
          (Sheaf.H.map (artinSchreierMap.{u, u + 1} X hp hX) n x)))) = _
  rw [h2, h3]
  set z := (smallEtaleSheafHUliftAddEquiv X (additiveSheafBase X) n).symm
    ((Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
      (additiveSheafBaseUliftIso X) n).symm x)
  have h4' := ConcreteCategory.congr_hom h4 z
  change (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv
    ((AddCommGrpCat.ofHom (Sheaf.H.map (artinSchreierMapBase X hp hX) n) ≫
    (abelianCohomologyIsoEtaleH X n).inv) z) = _
  rw [← h4']
  change (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv
    ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : X.Opens))).rightDerived n).map (frobeniusZariski X hp hX - 𝟙 _)
      ((abelianCohomologyIsoEtaleH X n).inv z)) = _
  rw [h5]
  rfl

/-- **Under the comparison of [Stacks, Tag 03P2], the Artin–Schreier map becomes `F - 1`**, in
an arbitrary `Ext` universe. -/
theorem etaleHAdditiveSheafAddEquiv_artinSchreierMap
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) (x : Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) n) :
    etaleHAdditiveSheafAddEquiv X n (Sheaf.H.map (artinSchreierMap.{u, u + 1} X hp hX) n x) =
      frobeniusCohomology X hp hX n (etaleHAdditiveSheafAddEquiv X n x) -
        etaleHAdditiveSheafAddEquiv X n x := by
  have h1 : extChgUnivAddEquiv.{w, u + 1} _ _ n
      (Sheaf.H.map (artinSchreierMap.{u, u + 1} X hp hX) n x) =
      (extChgUnivAddEquiv.{w, u + 1} _ _ n x).comp
        (Ext.mk₀ (artinSchreierMap.{u, u + 1} X hp hX)) (add_zero n) :=
    @ext_chgUniv_comp_mk₀ _ _ _ _ (hasExt_smallEtale_objectUniverse X) _ _ _ _ x _
  change etaleHAdditiveSheafAddEquivObjectUniverse X n (extChgUnivAddEquiv.{w, u + 1} _ _ n
    (Sheaf.H.map (artinSchreierMap.{u, u + 1} X hp hX) n x)) = _
  rw [h1]
  exact etaleHAdditiveSheafAddEquivObjectUniverse_artinSchreierMap X hp hX n _

end Comparison

/-! ### The Frobenius comparison over a field -/

section OverField

variable {p : ℕ} (hp : p.Prime) (k : Type u) [Field k] [CharP k p] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- **The Frobenius `F` on the `k`-vector space `Hⁿ(X, 𝒪_X)`**: `frobeniusCohomology`, the map
induced by the absolute Frobenius of `𝒪_X`, on `AlgebraicGeometry.cohomologyOverField`. -/
def frobeniusOverField (n : ℕ) :
    cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n →+
      cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n :=
  frobeniusCohomology X hp (natCast_eq_zero_of_charP k p f) n

/-- **The Frobenius on `Hⁿ(X, 𝒪_X)` is Frobenius-semilinear over `k`**: `F (a • v) = a ^ p • F v`.
Multiplication by `a ∈ k` on cohomology is the map induced by multiplication by its image in
`Γ(X, 𝒪_X)` (`AlgebraicGeometry.cohomologyOverFieldMap_globalSmul`), and the absolute Frobenius
of `𝒪_X` carries multiplication by a function to multiplication by its `p`-th power. -/
theorem frobeniusOverField_smul (n : ℕ) (a : k)
    (v : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) :
    frobeniusOverField hp k f n (a • v) = a ^ p • frobeniusOverField hp k f n v := by
  have h1 := cohomologyOverFieldMap_globalSmul k f a (SheafOfModules.unit X.ringCatSheaf) n v
  have h2 := cohomologyOverFieldMap_globalSmul k f (a ^ p) (SheafOfModules.unit X.ringCatSheaf) n
    (frobeniusOverField hp k f n v)
  have h3 : baseScalarSection k f (a ^ p) = baseScalarSection k f a ^ p := map_pow _ a p
  rw [← h1, ← h2, h3]
  with_unfolding_all exact (frobeniusCohomology_globalSmul X hp (natCast_eq_zero_of_charP k p f)
    n (baseScalarSection k f a) v)

/-- **The Frobenius comparison for the Artin–Schreier sequence, constructed.** For a scheme `X`
over a field `k` of characteristic `p` and every degree `n`, the étale cohomology
`Hⁿ(X_étale, 𝐆_a)` is identified with `Hⁿ(X, 𝒪_X)` ([Stacks, Tag 03P2] for `𝐆_a = (𝒪_X)ᵃ`) so
that the Artin–Schreier map `x ↦ x ^ p - x` becomes `F - 1`, where `F` is the map induced on
cohomology by the absolute Frobenius of `𝒪_X`, which is Frobenius-semilinear over `k`.

No hypothesis on `X` beyond the structure morphism is needed. This is the datum
`Stacks.ArtinSchreier.TopDegreeFrobeniusComparison` carried by [Stacks, Tag 0A3N] and
[Stacks, Tag 0A3P]. -/
def topDegreeFrobeniusComparison [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (n : ℕ) :
    TopDegreeFrobeniusComparison.{w} p k f (additiveSheaf.{u, u + 1} X)
      (artinSchreierMap.{u, u + 1} X hp (natCast_eq_zero_of_charP k p f)) n where
  equiv := etaleHAdditiveSheafAddEquiv X n
  frobenius := frobeniusOverField hp k f n
  frobenius_smul := frobeniusOverField_smul hp k f n
  equiv_map := etaleHAdditiveSheafAddEquiv_artinSchreierMap X hp (natCast_eq_zero_of_charP k p f) n

/-- The Frobenius of the constructed comparison is the map induced by the absolute Frobenius of
`𝒪_X`. -/
@[simp]
theorem topDegreeFrobeniusComparison_frobenius
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] (n : ℕ) :
    (topDegreeFrobeniusComparison.{w} hp k f n).frobenius = frobeniusOverField hp k f n :=
  rfl

/-- The constructed comparison, for the Artin–Schreier sequence datum
`Stacks.ArtinSchreier.constantArtinSchreierSequenceDatum`, whose middle term is `𝐆_a`. -/
def constantSequenceFrobeniusComparison
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] (n : ℕ) :
    TopDegreeFrobeniusComparison.{w} p k f
      (constantArtinSchreierSequenceDatum X hp (natCast_eq_zero_of_charP k p f)).Ga
      (constantArtinSchreierSequenceDatum X hp (natCast_eq_zero_of_charP k p f)).φ n :=
  topDegreeFrobeniusComparison hp k f n

end OverField

end Stacks.ArtinSchreier

end

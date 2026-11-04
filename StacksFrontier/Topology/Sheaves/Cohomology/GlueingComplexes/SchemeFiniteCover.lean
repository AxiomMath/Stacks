module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentMayerVietoris
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectUnion
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.Pullback

/-!
# Glueing morphisms of the derived category over a finite open cover of a scheme

Let `X` be a scheme, `K` and `E` objects of `D(𝒪_X)` and `X = U_1 ∪ … ∪ U_n` a finite open
cover such that `Ext^{-1}(K|_W, E|_W) = 0` for every open `W` contained in some `U_i`. Then a
family of morphisms `a_i : K|_{U_i} ⟶ E|_{U_i}` agreeing on the overlaps comes from a unique
morphism `K ⟶ E`. This is the sheaf property of `W ↦ Hom(K|_W, E|_W)` for finite covers, obtained
by induction on `n` from the Mayer--Vietoris statements of [Stacks, Tag 08DG] for two opens
(`Stacks.Cohomology.GlueingComplexes.exists_hom_of_compatible` and
`Stacks.Cohomology.GlueingComplexes.eq_zero_of_restrict_eq_zero`).

Restriction from `U` to `W ≤ U` on derived morphism sets is
`Stacks.DerivedPullback.schemeFactorHom` along `W ⟶ U ⟶ X`; its compatibility with composition is
the associativity coherence of [Stacks, Tag 0D5S] (`Stacks.DerivedPullback.schemeFactorHom_comp`).

## Main results

* `Stacks.Cohomology.GlueingComplexes.exists_restrictHom_eq_of_le_sup`: glueing along two opens.
* `Stacks.Cohomology.GlueingComplexes.eq_of_restrictHom_eq_of_le_sup`: uniqueness along two opens.
* `Stacks.Cohomology.GlueingComplexes.existsUnique_map_eq_of_iSup_eq_top`: glueing along a
  finite open cover.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback (factorIso factorIso_assoc schemeFactorIso schemeFactorHom
  schemeFactorHom_comp schemeFactorHom_id schemeFactorHom_add)

namespace Stacks.Cohomology.GlueingComplexes

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived category of an empty scheme is trivial**: any two morphisms agree. -/
theorem subsingleton_hom_derivedCategory_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y]
    (A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :
    Subsingleton (A ⟶ B) := by
  have hC : ∀ C : CochainComplex (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ℤ,
      IsZero C := fun C => by
    rw [IsZero.iff_id_eq_zero]
    ext n : 1
    exact (subsingleton_hom_of_isEmpty (Y := Y) (C.X n) (C.X n)).elim _ _
  have hA : IsZero A :=
    IsZero.of_iso (DerivedCategory.Q.map_isZero (hC _))
      (DerivedCategory.Q.objObjPreimageIso A).symm
  exact ⟨fun f g => hA.eq_of_src f g⟩

/-- The empty open of a scheme is an empty scheme. -/
instance isEmpty_bot_toScheme {X : Scheme.{u}} : IsEmpty (⊥ : X.Opens).toScheme :=
  ⟨fun x => by simpa using x.2⟩

variable {X : Scheme.{u}}
  (K E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

/-- The derived morphism set `Hom(K|_W, E|_W)` over an open `W` of `X`, restriction being derived
pullback along `W ⟶ X`. -/
abbrev OpenHom (W : X.Opens) : Type (u + 1) :=
  (derivedPullback W.ι.toLRSHom.toShHom).obj K ⟶ (derivedPullback W.ι.toLRSHom.toShHom).obj E

/-- Restriction of derived morphisms from an open `U` to an open `W ≤ U`. -/
abbrev restrictHom {W U : X.Opens} (h : W ≤ U) (φ : OpenHom K E U) : OpenHom K E W :=
  schemeFactorHom (X.homOfLE h) U.ι W.ι (X.homOfLE_ι h) K E φ

/-- Restricting from `U` to `W` and then to `W' ≤ W` is restricting from `U` to `W'`. -/
theorem restrictHom_restrictHom {W' W U : X.Opens} (h' : W' ≤ W) (h : W ≤ U)
    (φ : OpenHom K E U) :
    restrictHom K E h' (restrictHom K E h φ) = restrictHom K E (h'.trans h) φ :=
  schemeFactorHom_comp (X.homOfLE h') (X.homOfLE h) U.ι W.ι (X.homOfLE (h'.trans h)) W'.ι
    (X.homOfLE_ι h) (X.homOfLE_homOfLE h' h) (X.homOfLE_ι _) (X.homOfLE_ι h') K E φ

/-- Restriction from `U` to itself is the identity. -/
theorem restrictHom_refl (U : X.Opens) (φ : OpenHom K E U) :
    restrictHom K E (le_refl U) φ = φ :=
  schemeFactorHom_id (X.homOfLE_rfl U) U.ι (X.homOfLE_ι _) K E φ

/-- Restriction of derived morphisms commutes with subtraction. -/
theorem restrictHom_sub {W U : X.Opens} (h : W ≤ U) (φ ψ : OpenHom K E U) :
    restrictHom K E h (φ - ψ) = restrictHom K E h φ - restrictHom K E h ψ := by
  refine eq_sub_of_add_eq ?_
  rw [← schemeFactorHom_add, sub_add_cancel]

/-- Restricting the pullback of a global morphism `φ : K ⟶ E` from `U` to `W` gives the pullback
of `φ` to `W`. -/
theorem restrictHom_map {W U : X.Opens} (h : W ≤ U) (φ : K ⟶ E) :
    restrictHom K E h ((derivedPullback U.ι.toLRSHom.toShHom).map φ) =
      (derivedPullback W.ι.toLRSHom.toShHom).map φ := by
  have nat := (schemeFactorIso (X.homOfLE h) U.ι W.ι (X.homOfLE_ι h)).hom.naturality φ
  simp only [Functor.comp_map] at nat
  simp only [restrictHom, schemeFactorHom, Iso.homCongr_apply, Iso.app_inv, Iso.app_hom]
  rw [nat, Iso.inv_hom_id_app_assoc]

section Coherence

variable {Y U V W Z : RingedSpace.{u, u}}

/-- **The comparison on an intersection, against the comparisons with the ambient restriction.**
For opens `U`, `V` of `Y` with intersection `W`, all mapping to `Z` compatibly, the canonical
comparison `Li_U^* Lj_U^* ≅ Li_V^* Lj_V^*` on `W` is the one through `L(W → Z)^*`. -/
theorem overlapIso_hom_app_comp_factorIso (jU : U ⟶ Y) (jV : V ⟶ Y) (iU : W ⟶ U) (iV : W ⟶ V)
    (h : iU ≫ jU = iV ≫ jV) (ιY : Y ⟶ Z) (ιU : U ⟶ Z) (ιV : V ⟶ Z) (ιW : W ⟶ Z)
    (hU : jU ≫ ιY = ιU) (hV : jV ≫ ιY = ιV) (hWU : iU ≫ ιU = ιW) (hWV : iV ≫ ιV = ιW)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    (overlapIso jU jV iU iV h).hom.app ((derivedRestrict ιY).obj M) ≫
        (derivedRestrict iV).map ((factorIso jV ιY ιV hV).hom.app M) ≫
          (factorIso iV ιV ιW hWV).hom.app M =
      (derivedRestrict iU).map ((factorIso jU ιY ιU hU).hom.app M) ≫
        (factorIso iU ιU ιW hWU).hom.app M := by
  have hκ : (iU ≫ jU) ≫ ιY = ιW := by rw [Category.assoc, hU, hWU]
  have e₁ := congrArg Iso.hom
    (pathIsoInner_eq_pathIsoOuter iU jU ιY ιU hU (iU ≫ jU) rfl ιW hWU hκ M)
  have e₂ := congrArg Iso.hom
    (pathIsoInner_eq_pathIsoOuter iV jV ιY ιV hV (iU ≫ jU) h.symm ιW hWV hκ M)
  have e₃ := squareIso_app_comp_pathIsoOuter iU jU iV jV ιY h (iU ≫ jU) rfl h.symm ιW hκ M
  simp only [pathIsoInner, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at e₁ e₂
  rw [overlapIso_eq_derivedRestrictSquareIso, e₁, e₂]
  exact e₃

end Coherence

section TwoOpensRingedSpace

private theorem glue_chase {C : Type*} [Category C] {P Q A B T P' Q' A' B' T' : C}
    (uK : P ≅ A) (vK : Q ≅ B) (wUK : A ≅ T) (wVK : B ≅ T) (uE : P' ≅ A') (vE : Q' ≅ B')
    (wUE : A' ≅ T') (wVE : B' ≅ T') (ovK : P ⟶ Q) (ovE : P' ⟶ Q') (α : A ⟶ A') (β : B ⟶ B')
    (cK : ovK ≫ vK.hom ≫ wVK.hom = uK.hom ≫ wUK.hom)
    (cE : ovE ≫ vE.hom ≫ wVE.hom = uE.hom ≫ wUE.hom)
    (hab : wUK.inv ≫ α ≫ wUE.hom = wVK.inv ≫ β ≫ wVE.hom) :
    (uK.hom ≫ α ≫ uE.inv) ≫ ovE = ovK ≫ vK.hom ≫ β ≫ vE.inv := by
  have eE : ovE = uE.hom ≫ wUE.hom ≫ wVE.inv ≫ vE.inv := by
    rw [← reassoc_of% cE]; simp
  have eα : α ≫ wUE.hom = wUK.hom ≫ wVK.inv ≫ β ≫ wVE.hom := by
    rw [← hab]; simp
  have eK : uK.hom ≫ wUK.hom ≫ wVK.inv = ovK ≫ vK.hom := by
    rw [← reassoc_of% cK]; simp
  rw [eE]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% eα]
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% eK]

open Stacks.DerivedPullback (factorHom)

variable {Y U V W Z : RingedSpace.{u, u}}

/-- **Glueing derived morphisms along two opens covering a ringed space.** Let `U`, `V` be open
in `Y` with intersection `W` and covering `Y`. Two morphisms `a : K|_U ⟶ E|_U`, `b : K|_V ⟶ E|_V`
agreeing on `W` are the restrictions of a morphism `K ⟶ E`. -/
theorem exists_map_eq_of_compatible (jU : U ⟶ Y) (jV : V ⟶ Y) (iU : W ⟶ U) (iV : W ⟶ V)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (hpb : IsPullback iU iV jU jV)
    (cover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    (K E : DerivedModules Y) (a : (derivedRestrict jU).obj K ⟶ (derivedRestrict jU).obj E)
    (b : (derivedRestrict jV).obj K ⟶ (derivedRestrict jV).obj E)
    (hab : (derivedRestrict iU).map a ≫ (overlapIso jU jV iU iV hpb.w).hom.app E =
      (overlapIso jU jV iU iV hpb.w).hom.app K ≫ (derivedRestrict iV).map b) :
    ∃ φ : K ⟶ E, (derivedRestrict jU).map φ = a ∧ (derivedRestrict jV).map φ = b := by
  let G : Glueing jU jV iU iV hpb.w ((derivedRestrict jU).obj K) ((derivedRestrict jV).obj K)
      ((overlapIso jU jV iU iV hpb.w).app K) :=
    ⟨K, Iso.refl _, Iso.refl _, by
      simp only [CompatibleOnOverlap, Iso.refl_hom, Iso.app_hom]
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
      exact (Category.comp_id _).symm⟩
  obtain ⟨φ, hφU, hφV⟩ := exists_hom_of_compatible jU jV iU iV hpb cover G E a b hab
  exact ⟨φ, hφU.trans (Category.id_comp a), hφV.trans (Category.id_comp b)⟩

/-- **Glueing derived morphisms along two opens, against an ambient restriction.** Let `U`, `V`
be open in `Y` with intersection `W`, covering `Y`, all mapping to `Z` compatibly. Two morphisms
`a : K|_U ⟶ E|_U`, `b : K|_V ⟶ E|_V` agreeing on `W` are the restrictions of a morphism
`K|_Y ⟶ E|_Y`; here `K|_T` is the derived pullback along `T ⟶ Z`. -/
theorem exists_factorHom_eq_of_isPullback (jU : U ⟶ Y) (jV : V ⟶ Y) (iU : W ⟶ U) (iV : W ⟶ V)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (hpb : IsPullback iU iV jU jV)
    (cover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    (ιY : Y ⟶ Z) (ιU : U ⟶ Z) (ιV : V ⟶ Z) (ιW : W ⟶ Z)
    (hU : jU ≫ ιY = ιU) (hV : jV ≫ ιY = ιV) (hWU : iU ≫ ιU = ιW) (hWV : iV ≫ ιV = ιW)
    (K E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (a : (derivedRestrict ιU).obj K ⟶ (derivedRestrict ιU).obj E)
    (b : (derivedRestrict ιV).obj K ⟶ (derivedRestrict ιV).obj E)
    (hab : factorHom iU ιU ιW hWU K E a = factorHom iV ιV ιW hWV K E b) :
    ∃ φ : (derivedRestrict ιY).obj K ⟶ (derivedRestrict ιY).obj E,
      factorHom jU ιY ιU hU K E φ = a ∧ factorHom jV ιY ιV hV K E φ = b := by
  have cK := overlapIso_hom_app_comp_factorIso jU jV iU iV hpb.w ιY ιU ιV ιW hU hV hWU hWV K
  have cE := overlapIso_hom_app_comp_factorIso jU jV iU iV hpb.w ιY ιU ιV ιW hU hV hWU hWV E
  simp only [factorHom, Iso.homCongr_apply, Iso.app_inv, Iso.app_hom] at hab
  obtain ⟨φ, hφU, hφV⟩ := exists_map_eq_of_compatible jU jV iU iV hpb cover
    ((derivedRestrict ιY).obj K) ((derivedRestrict ιY).obj E)
    ((factorIso jU ιY ιU hU).hom.app K ≫ a ≫ (factorIso jU ιY ιU hU).inv.app E)
    ((factorIso jV ιY ιV hV).hom.app K ≫ b ≫ (factorIso jV ιY ιV hV).inv.app E) (by
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
      exact glue_chase ((derivedRestrict iU).mapIso ((factorIso jU ιY ιU hU).app K))
        ((derivedRestrict iV).mapIso ((factorIso jV ιY ιV hV).app K))
        ((factorIso iU ιU ιW hWU).app K) ((factorIso iV ιV ιW hWV).app K)
        ((derivedRestrict iU).mapIso ((factorIso jU ιY ιU hU).app E))
        ((derivedRestrict iV).mapIso ((factorIso jV ιY ιV hV).app E))
        ((factorIso iU ιU ιW hWU).app E) ((factorIso iV ιV ιW hWV).app E) _ _ _ _ cK cE hab)
  exact ⟨φ, by simp [factorHom, hφU], by simp [factorHom, hφV]⟩

/-- **Uniqueness of the glued derived morphism along two opens** ([Stacks, Tag 08DG]). With
`U`, `V`, `W`, `Y`, `Z` as in `exists_factorHom_eq_of_isPullback`, if
`Ext^{-1}(K|_W, E|_W) = 0`, two morphisms `K|_Y ⟶ E|_Y` with the same restrictions to `U` and to
`V` are equal. -/
theorem eq_of_factorHom_eq_of_isPullback (jU : U ⟶ Y) (jV : V ⟶ Y) (iU : W ⟶ U) (iV : W ⟶ V)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (hpb : IsPullback iU iV jU jV)
    (cover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    (ιY : Y ⟶ Z) (ιU : U ⟶ Z) (ιV : V ⟶ Z) (ιW : W ⟶ Z)
    (hU : jU ≫ ιY = ιU) (hV : jV ≫ ιY = ιV) (hWV : iV ≫ ιV = ιW)
    (K E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (hW : ∀ g : ((derivedRestrict ιW).obj K)⟦(1 : ℤ)⟧ ⟶ (derivedRestrict ιW).obj E, g = 0)
    (φ ψ : (derivedRestrict ιY).obj K ⟶ (derivedRestrict ιY).obj E)
    (h₁ : factorHom jU ιY ιU hU K E φ = factorHom jU ιY ιU hU K E ψ)
    (h₂ : factorHom jV ιY ιV hV K E φ = factorHom jV ιY ιV hV K E ψ) : φ = ψ := by
  have : (derivedRestrict jU).Additive := inferInstance
  have : (derivedRestrict jV).Additive := inferInstance
  have e₁ : (derivedRestrict jU).map φ = (derivedRestrict jU).map ψ :=
    (Stacks.DerivedPullback.factorEquiv jU ιY ιU hU K E).injective h₁
  have e₂ : (derivedRestrict jV).map φ = (derivedRestrict jV).map ψ :=
    (Stacks.DerivedPullback.factorEquiv jV ιY ιV hV K E).injective h₂
  have hc : (iV ≫ jV) ≫ ιY = ιW := by rw [Category.assoc, hV, hWV]
  let S : (derivedRestrict (iV ≫ jV)).obj (((derivedRestrict ιY).obj K)⟦(1 : ℤ)⟧) ≅
      ((derivedRestrict ιW).obj K)⟦(1 : ℤ)⟧ :=
    ((derivedRestrict (iV ≫ jV)).commShiftIso (1 : ℤ)).app ((derivedRestrict ιY).obj K) ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso ((factorIso (iV ≫ jV) ιY ιW hc).app K)
  let T : (derivedRestrict iV).obj ((derivedRestrict jV).obj ((derivedRestrict ιY).obj E)) ≅
      (derivedRestrict ιW).obj E :=
    (derivedRestrict iV).mapIso ((factorIso jV ιY ιV hV).app E) ≪≫
      (factorIso iV ιV ιW hWV).app E
  rw [← sub_eq_zero]
  refine eq_zero_of_restrict_eq_zero jU jV iU iV hpb cover (φ - ψ)
    (by rw [Functor.map_sub, e₁, sub_self]) (by rw [Functor.map_sub, e₂, sub_self]) fun g => ?_
  have h0 := hW (S.inv ≫ g ≫ T.hom)
  calc g = S.hom ≫ (S.inv ≫ g ≫ T.hom) ≫ T.inv := by simp
    _ = 0 := by rw [h0, zero_comp, comp_zero]

end TwoOpensRingedSpace

/-! ### Finite covers, for a presheaf with binary glueing -/

section Abstract

variable {α : Type*} [Order.Frame α] (P : α → Type*) (res : ∀ {a b : α}, a ≤ b → P b → P a)
  (res_res : ∀ {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) (x : P c),
    res h₁ (res h₂ x) = res (h₁.trans h₂) x)
  (res_refl : ∀ (a : α) (x : P a), res (le_refl a) x = x)
  (Good : α → Prop)
  (glue : ∀ {u v y : α} (hu : u ≤ y) (hv : v ≤ y), y ≤ u ⊔ v → ∀ (a : P u) (b : P v),
    res (inf_le_left : u ⊓ v ≤ u) a = res (inf_le_right : u ⊓ v ≤ v) b →
      ∃ φ : P y, res hu φ = a ∧ res hv φ = b)
  (uniq : ∀ {u v y : α} (hu : u ≤ y) (hv : v ≤ y), y ≤ u ⊔ v → Good (u ⊓ v) →
    ∀ φ ψ : P y, res hu φ = res hu ψ → res hv φ = res hv ψ → φ = ψ)
  (hbot : ∀ b : α, b = ⊥ → Nonempty (P b) ∧ Subsingleton (P b))

include res_res res_refl in
private theorem res_injective {a b : α} (h : a ≤ b) (h' : b ≤ a) (x y : P b)
    (e : res h x = res h y) : x = y := by
  rw [← res_refl b x, ← res_refl b y]
  have e' := congrArg (res h') e
  rwa [res_res, res_res] at e'

include res_res res_refl glue uniq hbot in
/-- **Glueing over a finite family of opens**, for a presheaf on a frame which glues along two
members, uniquely when their intersection is good. -/
theorem existsUnique_res_eq_of_finset {ι : Type*} (s : Finset ι) (V : ι → α)
    (hGood : ∀ w, (∃ i ∈ s, w ≤ V i) → Good w) (a : ∀ i, P (V i))
    (ha : ∀ i ∈ s, ∀ j ∈ s, res (inf_le_left : V i ⊓ V j ≤ V i) (a i) =
      res (inf_le_right : V i ⊓ V j ≤ V j) (a j)) :
    ∃! φ : P (s.sup V), ∀ i (hi : i ∈ s), res (Finset.le_sup hi) φ = a i := by
  classical
  induction s using Finset.induction_on generalizing V a with
  | empty =>
    obtain ⟨⟨z⟩, hz⟩ := hbot _ Finset.sup_empty
    exact ⟨z, fun i hi => absurd hi (Finset.notMem_empty i), fun y _ => hz.elim _ _⟩
  | @insert j s hj ih =>
    have hjY : V j ≤ (insert j s).sup V := Finset.le_sup (Finset.mem_insert_self j s)
    have hsY : s.sup V ≤ (insert j s).sup V := Finset.sup_mono (Finset.subset_insert j s)
    have hYle : (insert j s).sup V ≤ s.sup V ⊔ V j := by
      rw [Finset.sup_insert, sup_comm]
    obtain ⟨φs, hφs, hus⟩ := ih V
      (fun w ⟨i, hi, hw⟩ => hGood w ⟨i, Finset.mem_insert_of_mem hi, hw⟩) a
      (fun i hi k hk => ha i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk))
    have hcompat : res (inf_le_left : s.sup V ⊓ V j ≤ s.sup V) φs =
        res (inf_le_right : s.sup V ⊓ V j ≤ V j) (a j) := by
      have hm : s.sup (fun i => V i ⊓ V j) = s.sup V ⊓ V j :=
        (Finset.sup_inf_distrib_right s V (V j)).symm
      obtain ⟨_, _, hu'⟩ := ih (fun i => V i ⊓ V j)
        (fun w ⟨i, hi, hw⟩ => hGood w ⟨i, Finset.mem_insert_of_mem hi, hw.trans inf_le_left⟩)
        (fun i => res (inf_le_left : V i ⊓ V j ≤ V i) (a i))
        (fun i hi k hk => by
          have e := congrArg (res (show (V i ⊓ V j) ⊓ (V k ⊓ V j) ≤ V i ⊓ V k from
            inf_le_inf inf_le_left inf_le_left))
            (ha i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk))
          simp only [res_res] at e ⊢
          exact e)
      refine res_injective P res res_res res_refl hm.le hm.ge _ _ ?_
      refine (hu' _ fun i hi => ?_).trans (hu' _ fun i hi => ?_).symm
      · rw [res_res, res_res, ← hφs i hi, res_res]
      · rw [res_res, res_res, ← ha i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_self j s)]
    obtain ⟨φ, hφ₁, hφ₂⟩ := glue hsY hjY hYle φs (a j) hcompat
    refine ⟨φ, fun i hi => ?_, fun ψ hψ => ?_⟩
    · rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact hφ₂
      · rw [← hφs i hi', ← hφ₁, res_res]
    · refine uniq hsY hjY hYle
        (hGood _ ⟨j, Finset.mem_insert_self j s, inf_le_right⟩) ψ φ ?_ ?_
      · rw [hφ₁]
        refine hus _ fun i hi => ?_
        rw [res_res]
        exact hψ i (Finset.mem_insert_of_mem hi)
      · rw [hφ₂]
        exact hψ j (Finset.mem_insert_self j s)

end Abstract

section TwoOpens

variable {X : Scheme.{u}}

/-- If opens `U, V ≤ Y` satisfy `Y ≤ U ⊔ V`, then the images of the inclusions of `U` and `V`
into `Y` cover `Y`. -/
theorem range_homOfLE_union {U V Y : X.Opens} (hU : U ≤ Y) (hV : V ≤ Y) (hY : Y ≤ U ⊔ V) :
    Set.range (X.homOfLE hU).toLRSHom.toShHom.hom.base ∪
      Set.range (X.homOfLE hV).toLRSHom.toShHom.hom.base = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨x, hx⟩ := y
  have hx' : x ∈ U ⊔ V := hY hx
  simp only [TopologicalSpace.Opens.mem_sup] at hx'
  rcases hx' with hxU | hxV
  · exact Or.inl ⟨⟨x, hxU⟩, Subtype.ext (Scheme.homOfLE_apply hU ⟨x, hxU⟩)⟩
  · exact Or.inr ⟨⟨x, hxV⟩, Subtype.ext (Scheme.homOfLE_apply hV ⟨x, hxV⟩)⟩

variable (K E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

/-- **Glueing derived morphisms along two opens** ([Stacks, Tag 08DG]). If `U ∪ V ⊇ Y` and
morphisms `a : K|_U ⟶ E|_U`, `b : K|_V ⟶ E|_V` agree on `U ∩ V`, they are the restrictions of a
morphism `K|_Y ⟶ E|_Y`. -/
theorem exists_restrictHom_eq_of_le_sup {U V Y : X.Opens} (hU : U ≤ Y) (hV : V ≤ Y)
    (hY : Y ≤ U ⊔ V) (a : OpenHom K E U) (b : OpenHom K E V)
    (hab : restrictHom K E (inf_le_left : U ⊓ V ≤ U) a =
      restrictHom K E (inf_le_right : U ⊓ V ≤ V) b) :
    ∃ φ : OpenHom K E Y, restrictHom K E hU φ = a ∧ restrictHom K E hV φ = b :=
  exists_factorHom_eq_of_isPullback _ _ _ _
    (Scheme.isPullback_toShHom (isPullback_opens_inf_le hU hV)) (range_homOfLE_union hU hV hY)
    Y.ι.toLRSHom.toShHom U.ι.toLRSHom.toShHom V.ι.toLRSHom.toShHom (U ⊓ V).ι.toLRSHom.toShHom
    _ _ _ _ K E a b hab

/-- **Uniqueness of glued derived morphisms along two opens** ([Stacks, Tag 08DG]). If
`U ∪ V ⊇ Y` and `Ext^{-1}(K|_{U ∩ V}, E|_{U ∩ V}) = 0`, two morphisms `K|_Y ⟶ E|_Y` with the
same restrictions to `U` and to `V` are equal. -/
theorem eq_of_restrictHom_eq_of_le_sup {U V Y : X.Opens} (hU : U ≤ Y) (hV : V ≤ Y)
    (hY : Y ≤ U ⊔ V)
    (hW : ∀ g : ((derivedPullback (U ⊓ V).ι.toLRSHom.toShHom).obj K)⟦(1 : ℤ)⟧ ⟶
      (derivedPullback (U ⊓ V).ι.toLRSHom.toShHom).obj E, g = 0)
    (φ ψ : OpenHom K E Y) (h₁ : restrictHom K E hU φ = restrictHom K E hU ψ)
    (h₂ : restrictHom K E hV φ = restrictHom K E hV ψ) : φ = ψ :=
  eq_of_factorHom_eq_of_isPullback _ _ _ _
    (Scheme.isPullback_toShHom (isPullback_opens_inf_le hU hV)) (range_homOfLE_union hU hV hY)
    Y.ι.toLRSHom.toShHom U.ι.toLRSHom.toShHom V.ι.toLRSHom.toShHom (U ⊓ V).ι.toLRSHom.toShHom
    _ _ (congrArg (fun m : (U ⊓ V).toScheme ⟶ X ↦ m.toLRSHom.toShHom)
      (X.homOfLE_ι (inf_le_right : U ⊓ V ≤ V))) K E hW φ ψ h₁ h₂

end TwoOpens

section FiniteCover

variable {X : Scheme.{u}}
  (K E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

/-- Restriction to the open `⊤` is bijective on derived morphism sets. -/
theorem bijective_map_top :
    Function.Bijective ((derivedPullback (⊤ : X.Opens).ι.toLRSHom.toShHom).map :
      (K ⟶ E) → OpenHom K E ⊤) :=
  Stacks.DerivedPullback.bijective_derivedPullback_map _ X.topIso.inv.toLRSHom.toShHom
    (congrArg (fun m : (⊤ : X.Opens).toScheme ⟶ (⊤ : X.Opens).toScheme ↦ m.toLRSHom.toShHom)
      (show (⊤ : X.Opens).ι ≫ X.topIso.inv = 𝟙 _ by rw [← Scheme.topIso_hom, Iso.hom_inv_id]))
    (congrArg (fun m : X ⟶ X ↦ m.toLRSHom.toShHom)
      (show X.topIso.inv ≫ (⊤ : X.Opens).ι = 𝟙 _ by rw [← Scheme.topIso_hom, Iso.inv_hom_id]))
    K E

/-- **Glueing derived morphisms along a finite open cover.** Let `X = ⋃ U_i` be a finite open
cover and `K`, `E` objects of `D(𝒪_X)` with `Ext^{-1}(K|_W, E|_W) = 0` for every open `W`
contained in some `U_i`. A family of morphisms `a_i : K|_{U_i} ⟶ E|_{U_i}` agreeing on the
overlaps `U_i ∩ U_j` is the family of restrictions of a unique morphism `K ⟶ E`. -/
theorem existsUnique_map_eq_of_iSup_eq_top {ι : Type*} [Finite ι] (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤)
    (hExt : ∀ W : X.Opens, (∃ i, W ≤ U i) →
      ∀ g : ((derivedPullback W.ι.toLRSHom.toShHom).obj K)⟦(1 : ℤ)⟧ ⟶
        (derivedPullback W.ι.toLRSHom.toShHom).obj E, g = 0)
    (a : ∀ i, OpenHom K E (U i))
    (ha : ∀ i j, restrictHom K E (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
      restrictHom K E (inf_le_right : U i ⊓ U j ≤ U j) (a j)) :
    ∃! φ : K ⟶ E, ∀ i, (derivedPullback (U i).ι.toLRSHom.toShHom).map φ = a i := by
  classical
  have := Fintype.ofFinite ι
  have hT : (Finset.univ : Finset ι).sup U = ⊤ := by
    rw [Finset.sup_univ_eq_iSup, hU]
  obtain ⟨ψ, hψ, hu⟩ := existsUnique_res_eq_of_finset (OpenHom K E)
    (fun h => restrictHom K E h) (fun h₁ h₂ x => restrictHom_restrictHom K E h₁ h₂ x)
    (fun a x => restrictHom_refl K E a x)
    (fun W => ∀ g : ((derivedPullback W.ι.toLRSHom.toShHom).obj K)⟦(1 : ℤ)⟧ ⟶
        (derivedPullback W.ι.toLRSHom.toShHom).obj E, g = 0)
    (fun hu hv hy a b hab => exists_restrictHom_eq_of_le_sup K E hu hv hy a b hab)
    (fun hu hv hy hW φ ψ h₁ h₂ => eq_of_restrictHom_eq_of_le_sup K E hu hv hy hW φ ψ h₁ h₂)
    (fun b hb => by
      subst hb
      exact ⟨⟨0⟩, subsingleton_hom_derivedCategory_of_isEmpty _ _⟩)
    Finset.univ U (fun w ⟨i, _, hw⟩ => hExt w ⟨i, hw⟩) a (fun i _ j _ => ha i j)
  have hTle : (⊤ : X.Opens) ≤ (Finset.univ : Finset ι).sup U := hT.ge
  obtain ⟨φ, hφ⟩ := (bijective_map_top K E).2 (restrictHom K E hTle ψ)
  have key : ∀ φ' : K ⟶ E, (∀ i, (derivedPullback (U i).ι.toLRSHom.toShHom).map φ' = a i) →
      (derivedPullback (⊤ : X.Opens).ι.toLRSHom.toShHom).map φ' = restrictHom K E hTle ψ := by
    intro φ' h'
    rw [← restrictHom_map K E hTle φ']
    congr 1
    refine hu _ fun i _ => ?_
    rw [restrictHom_map]
    exact h' i
  refine ⟨φ, fun i => ?_, fun φ' h' => ?_⟩
  · rw [← restrictHom_map K E (le_top : U i ≤ ⊤), hφ, restrictHom_restrictHom]
    exact hψ i (Finset.mem_univ i)
  · exact (bijective_map_top K E).1 ((key φ' h').trans hφ.symm)

end FiniteCover

end Stacks.Cohomology.GlueingComplexes

end

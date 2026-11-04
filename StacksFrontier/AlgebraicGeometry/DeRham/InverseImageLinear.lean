module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.MateStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.MorphismGluing
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianFractionFunctoriality
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DeRhamComplexLogPoles
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormCalculus
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafAffine

/-!
# Additive maps of `𝒪_X`-modules that are `f^{-1}𝒪_S`-linear

Let `f : X ⟶ S` be a morphism of schemes. The relative de Rham complex `Ω^•_{X/S}` and every
complex built from it — the weight-zero forms of a line bundle of Tag 0FUF, the forms with
logarithmic poles of Tag 0FMW, the pushed-forward forms of a closed subscheme — have terms which
are `𝒪_X`-modules and differentials which are only additive. The category those complexes live in
is that of sheaves of `f^{-1}𝒪_S`-modules, the `D(X, f^{-1}𝒪_S)` of the source, and a differential
belongs to that category exactly when it commutes with the action of `f^{-1}𝒪_S`.

This file reduces that linearity to the sections coming from the base: an additive map commuting
with multiplication by `f^♯ s` for every local section `s` of `𝒪_S` commutes with the action of
every local section of `f^{-1}𝒪_S`, because those are locally of the form `f^♯ s`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.toBaseModules`: an `𝒪_X`-module read as an `f^{-1}𝒪_S`-module.
* `AlgebraicGeometry.Scheme.Hom.baseLinearHom`: **an additive map of `𝒪_X`-modules commuting with
  `f^♯` of the local sections of `𝒪_S`, as a morphism of `f^{-1}𝒪_S`-modules.**

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_eq_baseUnitSection`: a local section of `f^{-1}𝒪_S` is,
  near every point, the image of a local section of `𝒪_S`.
* `AlgebraicGeometry.Scheme.Hom.map_smul_of_appLE`: the reduction of linearity to the base.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **An `𝒪_X`-module read as an `f^{-1}𝒪_S`-module**, by restriction of scalars along the
structural map `f^{-1}𝒪_S ⟶ 𝒪_X`. This is how the terms of the relative de Rham complex are read
(`AlgebraicGeometry.Scheme.Hom.deRhamComplex_X`). -/
abbrev toBaseModules : X.Modules ⥤ _root_.SheafOfModules.{u} (baseRingSheaf f) :=
  _root_.SheafOfModules.restrictScalars (baseRingHom f)

/-- Restriction of scalars to `f^{-1}𝒪_S` is additive: Mathlib's instance, restated through
`AlgebraicGeometry.Scheme.Hom.toBaseModules`. -/
instance additive_toBaseModules : (toBaseModules f).Additive :=
  inferInstanceAs (_root_.SheafOfModules.restrictScalars (baseRingHom f)).Additive

/-- The unit section of `f^{-1}𝒪_S` over `f⁻¹V` attached to a section of `𝒪_S` over `V`. -/
abbrev baseUnitSection (V : S.Opens) (s : Γ(S, V)) :
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.obj (op (f ⁻¹ᵁ V)) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
    S.sheaf).hom.app (op V)).hom s

/-- **A local section of `f^{-1}𝒪_S` is, near every point, the image of a local section of
`𝒪_S`**: the stalk of `f^{-1}𝒪_S` at `x` is the stalk of `𝒪_S` at `f x`. -/
theorem exists_eq_baseUnitSection {U : X.Opens}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.obj (op U))
    {x : X} (hx : x ∈ U) :
    ∃ (V : S.Opens) (s : Γ(S, V)) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ f ⁻¹ᵁ V), x ∈ W ∧
      (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.map (homOfLE hWU).op).hom
          a =
        (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.map
          (homOfLE hWV).op).hom (baseUnitSection f V s) := by
  let e := (Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso CommRingCat.{u} f.base
    x).app S.sheaf
  obtain ⟨V, hV, s, hs⟩ := TopCat.Presheaf.exists_germ_eq S.sheaf.presheaf (x := f.base x)
    (e.inv.hom
      (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.germ U x hx a))
  have h1 : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.germ U x hx a =
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.germ (f ⁻¹ᵁ V) x hV
        (baseUnitSection f V s) := by
    have h2 := congrArg (fun φ => φ.hom s)
      (Stacks.AlgebraPullbackQcoh.germ_stalkSheafPullbackMateNatIso
        (A := CommRingCat.{u}) f.base x S.sheaf V hV)
    have h3 : e.hom.hom (S.sheaf.presheaf.germ V (f.base x) hV s) =
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.germ U x hx a := by
      rw [hs]
      exact congrArg (fun φ => φ.hom
        (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.germ U x hx a))
        e.inv_hom_id
    exact h3.symm.trans h2
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hx hV _ _ h1
  exact ⟨V, s, W, leOfHom iU, leOfHom iV, hxW, hW⟩

/-- **The structural map sends the unit section of `s` to `f^♯ s`**: restricted to an open `W`
with `f(W) ⊆ V`, the unit section attached to a section `s` of `𝒪_S` over `V` is carried by
`f^{-1}𝒪_S ⟶ 𝒪_X` to the image of `s` under `f.appLE V W`. -/
theorem inverseImageStructureMap_baseUnitSection (V : S.Opens) (W : X.Opens)
    (hWV : W ≤ f ⁻¹ᵁ V) (s : Γ(S, V)) :
    ((inverseImageStructureMap f).hom.app (op W)).hom
        ((((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.map
          (homOfLE hWV).op).hom (baseUnitSection f V s)) = (f.appLE V W hWV).hom s :=
  Stacks.Smooth.inverseImageStructureMap_inverseImageSection f W hWV s

/-- **Linearity over `f^{-1}𝒪_S` reduces to linearity over the base.** A morphism of the
underlying abelian presheaves of two `𝒪_X`-modules which commutes with multiplication by
`f^♯ s = f.appLE V W s` for every local section `s` of `𝒪_S` commutes with multiplication by the
image of every local section of `f^{-1}𝒪_S`. -/
theorem map_smul_of_appLE {M N : X.Modules}
    (ψ : Scheme.Modules.presheaf M ⟶ Scheme.Modules.presheaf N)
    (hψ : ∀ (V : S.Opens) (W : X.Opens) (hWV : W ≤ f ⁻¹ᵁ V) (s : Γ(S, V)) (m : Γ(M, W)),
      ψ.app (op W) ((f.appLE V W hWV).hom s • m) = (f.appLE V W hWV).hom s • ψ.app (op W) m)
    (U : X.Opens) (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.obj (op U))
    (m : Γ(M, U)) :
    ψ.app (op U) (baseFn f a • m) = baseFn f a • ψ.app (op U) m := by
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq N U _ _ fun x hx => ?_
  obtain ⟨V, s, W, hWU, hWV, hxW, hW⟩ := exists_eq_baseUnitSection f a hx
  refine ⟨W, hWU, hxW, ?_⟩
  have hφ : (X.presheaf.map (homOfLE hWU).op).hom (baseFn f a) =
        (f.appLE V W hWV).hom s := by
    have h := congrArg (fun φ => φ.hom a)
      ((inverseImageStructureMap f).hom.naturality (homOfLE hWU).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    refine h.symm.trans ?_
    rw [hW]
    exact inverseImageStructureMap_baseUnitSection f V W hWV s
  have nat : ∀ (y : Γ(M, U)), (Scheme.Modules.presheaf N).map (homOfLE hWU).op (ψ.app (op U) y) =
      ψ.app (op W) ((Scheme.Modules.presheaf M).map (homOfLE hWU).op y) := fun y =>
    (ConcreteCategory.congr_hom (ψ.naturality (homOfLE hWU).op) y).symm
  rw [nat, Scheme.Modules.map_smul, Scheme.Modules.map_smul, hφ, hψ, nat]

/-- **An additive map of `𝒪_X`-modules commuting with `f^♯` of the local sections of `𝒪_S`, as
a morphism of sheaves of `f^{-1}𝒪_S`-modules** between the two modules read over `f^{-1}𝒪_S`. -/
def baseLinearHom {M N : X.Modules}
    (ψ : Scheme.Modules.presheaf M ⟶ Scheme.Modules.presheaf N)
    (hψ : ∀ (V : S.Opens) (W : X.Opens) (hWV : W ≤ f ⁻¹ᵁ V) (s : Γ(S, V)) (m : Γ(M, W)),
      ψ.app (op W) ((f.appLE V W hWV).hom s • m) = (f.appLE V W hWV).hom s • ψ.app (op W) m) :
    (toBaseModules f).obj M ⟶ (toBaseModules f).obj N :=
  ⟨PresheafOfModules.homMk ψ fun U a m => map_smul_of_appLE f ψ hψ U.unop a m⟩

/-- On sections, the lifted morphism is the given additive map. -/
theorem baseLinearHom_app {M N : X.Modules}
    (ψ : Scheme.Modules.presheaf M ⟶ Scheme.Modules.presheaf N)
    (hψ : ∀ (V : S.Opens) (W : X.Opens) (hWV : W ≤ f ⁻¹ᵁ V) (s : Γ(S, V)) (m : Γ(M, W)),
      ψ.app (op W) ((f.appLE V W hWV).hom s • m) = (f.appLE V W hWV).hom s • ψ.app (op W) m)
    (U : X.Opens) (m : Γ(M, U)) :
    (baseLinearHom f ψ hψ).val.app (op U) m = ψ.app (op U) m :=
  rfl

/-- **The underlying morphism of abelian sheaves of the lifted morphism is the given one.** -/
theorem toSheaf_map_baseLinearHom {M N : X.Modules}
    (ψ : Scheme.Modules.presheaf M ⟶ Scheme.Modules.presheaf N)
    (hψ : ∀ (V : S.Opens) (W : X.Opens) (hWV : W ≤ f ⁻¹ᵁ V) (s : Γ(S, V)) (m : Γ(M, W)),
      ψ.app (op W) ((f.appLE V W hWV).hom s • m) = (f.appLE V W hWV).hom s • ψ.app (op W) m) :
    (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).map (baseLinearHom f ψ hψ) =
      Stacks.Perfect.AbelianFraction.abHom ψ :=
  rfl

/-- **The underlying abelian sheaf of an `𝒪_X`-module read over `f^{-1}𝒪_S` is its underlying
abelian sheaf.** -/
theorem toSheaf_toBaseModules (M : X.Modules) :
    (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).obj ((toBaseModules f).obj M) =
      (Stacks.Perfect.AbelianFraction.abelianSheaf X).obj M :=
  rfl

/-- Restriction of scalars to `f^{-1}𝒪_S` does not change the underlying morphism of abelian
sheaves. -/
theorem toSheaf_map_toBaseModules {M N : X.Modules} (φ : M ⟶ N) :
    (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).map ((toBaseModules f).map φ) =
      (Stacks.Perfect.AbelianFraction.abelianSheaf X).map φ :=
  rfl

/-- The underlying morphism of abelian sheaves of the relative de Rham differential is
`AlgebraicGeometry.Scheme.Hom.deRhamDifferentialAbHom`. -/
theorem toSheaf_map_deRhamComplex_d (p : ℕ) :
    (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).map ((deRhamComplex f).d p (p + 1)) =
      deRhamDifferentialAbHom f p :=
  rfl

/-! ### The relative de Rham differential and its direct images -/

/-- **The relative de Rham differential is linear over the base**: it commutes with
multiplication by `h^♯ s` for a local section `s` of `𝒪_S`. -/
theorem deRhamD_appLE_smul {T : Scheme.{u}} (h : T ⟶ S) (p : ℕ) (V : S.Opens) (W : T.Opens)
    (hWV : W ≤ h ⁻¹ᵁ V) (s : Γ(S, V)) (ω : Γ(relativeDifferentialForms h (p : ℤ), W)) :
    deRhamD h p W ((h.appLE V W hWV).hom s • ω) = (h.appLE V W hWV).hom s • deRhamD h p W ω := by
  rw [← inverseImageStructureMap_baseUnitSection h V W hWV s]
  exact (((deRhamComplex h).d p (p + 1)).val.app (op W)).hom.map_smul _ ω

/-- **The direct image of the relative de Rham differential of `T/S` along `g : T ⟶ X` is linear
over `f^{-1}𝒪_S`**, for `f : X ⟶ S`: it commutes with multiplication by `f^♯ s`. -/
theorem pushforwardDeRham_appLE_smul {T : Scheme.{u}} (g : T ⟶ X) (p : ℕ) (V : S.Opens)
    (W : X.Opens) (hWV : W ≤ f ⁻¹ᵁ V) (s : Γ(S, V))
    (ω : Γ((Scheme.Modules.pushforward g).obj (relativeDifferentialForms (g ≫ f) (p : ℤ)), W)) :
    (pushforwardDeRhamDifferentialPresheafHom g f p).app (op W) ((f.appLE V W hWV).hom s • ω) =
      (f.appLE V W hWV).hom s • (pushforwardDeRhamDifferentialPresheafHom g f p).app (op W) ω := by
  have hle : g ⁻¹ᵁ W ≤ (g ≫ f) ⁻¹ᵁ V := fun x hx => hWV hx
  have key : (g.app W).hom ((f.appLE V W hWV).hom s) = ((g ≫ f).appLE V (g ⁻¹ᵁ W) hle).hom s := by
    rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE]
    rfl
  let ω' : Γ(relativeDifferentialForms (g ≫ f) (p : ℤ), g ⁻¹ᵁ W) := ω
  show deRhamD (g ≫ f) p (g ⁻¹ᵁ W) ((g.app W).hom ((f.appLE V W hWV).hom s) • ω') =
    (g.app W).hom ((f.appLE V W hWV).hom s) • deRhamD (g ≫ f) p (g ⁻¹ᵁ W) ω'
  rw [key]
  exact deRhamD_appLE_smul (g ≫ f) p V (g ⁻¹ᵁ W) hle s ω'

end AlgebraicGeometry.Scheme.Hom

module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictSheafification

/-!
# The crystalline differentials of a restricted situation

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], an open `W` of `S`
and an open `V` of `X` whose image lies in `W`.  This file proves that `Ω_{V/S|_W}` is the
restriction of `Ω_{X/S}` along `smallExtend`.

## Main definitions

* `Crystalline.dpConstDifferentialsCongrBase`: the divided power differentials killing a set of
  constants do not depend on the base map whose image lies among those constants.
* `Crystalline.GlobalCrystallineSituation.SmallSite.smallExtendCrysDifferentialsIso`: the
  restriction of `Ω_{X/S}` along `smallExtend` is isomorphic to `Ω_{V/S|_W}`.

## References

* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline

/-! ### Divided power differentials over two base maps with the same constants -/

section ConstBase

variable {A A' B : CommRingCat.{u}} {J : Ideal B}

/-- The universal divided power differential killing a set of constants, read as a derivation
over another base map whose image is among those constants. -/
def dpConstDOfBase (f : A ⟶ B) (f' : A' ⟶ B) (hJ : DividedPowers J) (Z' : Set B)
    (hf : ∀ a, f a ∈ Z') : (dpConstDifferentials f' hJ Z').Derivation f :=
  ModuleCat.Derivation.mk (fun b ↦ (dpConstD f' hJ Z').d b)
    (fun b b' ↦ ModuleCat.Derivation.d_add _ b b')
    (fun b b' ↦ ModuleCat.Derivation.d_mul _ b b')
    (fun a ↦ dpConstD_base f' hJ (hf a))

/-- The derivation `dpConstDOfBase f f' hJ Z' hf` sends `b` to `d b`. -/
@[simp]
theorem dpConstDOfBase_d (f : A ⟶ B) (f' : A' ⟶ B) (hJ : DividedPowers J) (Z' : Set B)
    (hf : ∀ a, f a ∈ Z') (b : B) :
    (dpConstDOfBase f f' hJ Z' hf).d b = (dpConstD f' hJ Z').d b := rfl

/-- The comparison map between the divided power differentials killing one set of constants over
one base map and those killing another set over another base map. -/
def dpConstDifferentialsCongrHom (f : A ⟶ B) (f' : A' ⟶ B) (hJ : DividedPowers J) (Z Z' : Set B)
    (hZ : Z ⊆ Z') (hf : ∀ a, f a ∈ Z') :
    dpConstDifferentials f hJ Z ⟶ dpConstDifferentials f' hJ Z' :=
  dpConstDesc (dpConstDOfBase f f' hJ Z' hf)
    (fun n x hx ↦ dpConstD_dpow f' hJ Z' n x hx)
    (fun _ hs ↦ dpConstD_base f' hJ (hZ hs))

/-- The comparison map `dpConstDifferentialsCongrHom` sends `d b` to `d b`. -/
@[simp]
theorem dpConstDifferentialsCongrHom_d (f : A ⟶ B) (f' : A' ⟶ B) (hJ : DividedPowers J)
    (Z Z' : Set B) (hZ : Z ⊆ Z') (hf : ∀ a, f a ∈ Z') (b : B) :
    dpConstDifferentialsCongrHom f f' hJ Z Z' hZ hf ((dpConstD f hJ Z).d b) =
      (dpConstD f' hJ Z').d b :=
  dpConstDesc_d _ _ _ b

/-- **Divided power differentials depend only on the set of constants killed.**  If two base maps
`f : A ⟶ B` and `f' : A' ⟶ B` have their images inside two sets of constants that coincide, the
two modules of divided power differentials killing those constants agree. -/
def dpConstDifferentialsCongrBase (f : A ⟶ B) (f' : A' ⟶ B) (hJ : DividedPowers J) (Z Z' : Set B)
    (hZ : Z ⊆ Z') (hZ' : Z' ⊆ Z) (hf : ∀ a, f a ∈ Z') (hf' : ∀ a', f' a' ∈ Z) :
    dpConstDifferentials f hJ Z ≅ dpConstDifferentials f' hJ Z' where
  hom := dpConstDifferentialsCongrHom f f' hJ Z Z' hZ hf
  inv := dpConstDifferentialsCongrHom f' f hJ Z' Z hZ' hf'
  hom_inv_id := by
    refine dpConstDifferentials_ext fun b ↦ ?_
    rw [ModuleCat.comp_apply, dpConstDifferentialsCongrHom_d,
      dpConstDifferentialsCongrHom_d, ModuleCat.id_apply]
  inv_hom_id := by
    refine dpConstDifferentials_ext fun b ↦ ?_
    rw [ModuleCat.comp_apply, dpConstDifferentialsCongrHom_d,
      dpConstDifferentialsCongrHom_d, ModuleCat.id_apply]

/-- **The comparison of divided power differentials over different base maps is compatible with
the restriction maps along a homomorphism of divided power rings.** -/
theorem dpConstMap_dpConstDifferentialsCongrHom {A₁ A₂ E₁ E₂ D D' : CommRingCat.{u}}
    {K : Ideal D} {K' : Ideal D'} {f₁ : A₁ ⟶ D} {f₂ : A₂ ⟶ D'} {e₁ : E₁ ⟶ D} {e₂ : E₂ ⟶ D'}
    {g : A₁ ⟶ A₂} {h : E₁ ⟶ E₂} {φ : D ⟶ D'}
    (fac : g ≫ f₂ = f₁ ≫ φ) (fac' : h ≫ e₂ = e₁ ≫ φ)
    (hK : DividedPowers K) (hK' : DividedPowers K')
    (hφ : DividedPowers.IsDPMorphism hK hK' φ.hom)
    (Z : Set D) (Z' : Set D') (hZ : ∀ s ∈ Z, φ s ∈ Z')
    (Y : Set D) (Y' : Set D') (hY : ∀ s ∈ Y, φ s ∈ Y')
    (hZY : Z ⊆ Y) (hf : ∀ a, f₁ a ∈ Y) (hZY' : Z' ⊆ Y') (hf' : ∀ a, f₂ a ∈ Y') :
    dpConstMap fac hK hK' hφ Z Z' hZ ≫
        (ModuleCat.restrictScalars φ.hom).map
          (dpConstDifferentialsCongrHom f₂ e₂ hK' Z' Y' hZY' hf') =
      dpConstDifferentialsCongrHom f₁ e₁ hK Z Y hZY hf ≫
        dpConstMap fac' hK hK' hφ Y Y' hY := by
  refine dpConstDifferentials_ext fun b ↦ ?_
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, dpConstMap_d,
    dpConstDifferentialsCongrHom_d, dpConstMap_d]
  exact dpConstDifferentialsCongrHom_d f₂ e₂ hK' Z' Y' hZY' hf' (φ b)

end ConstBase

/-! ### The sections pulled back from an open subscheme of the base -/

/-- **The sections pulled back from the base do not change when the base is replaced by an open
subscheme through which the structure morphism factors.** -/
theorem baseSections_comp_of_isOpenImmersion (T : DividedPowerScheme.{u}) {Y' Y : Scheme.{u}}
    (f' : T.scheme ⟶ Y') (j : Y' ⟶ Y) [IsOpenImmersion j] (Wo : T.scheme.Opens) :
    baseSections T Y (f' ≫ j) Wo = baseSections T Y' f' Wo := by
  ext b
  constructor
  · rintro ⟨N, h, a, rfl⟩
    have h' : Wo ≤ f' ⁻¹ᵁ (j ⁻¹ᵁ N) := by rwa [← Scheme.Hom.comp_preimage]
    refine ⟨j ⁻¹ᵁ N, h', j.appLE N (j ⁻¹ᵁ N) le_rfl a, ?_⟩
    exact (CommRingCat.comp_apply _ _ a).symm.trans
      (congrArg (fun φ : Γ(Y, N) ⟶ Γ(T.scheme, Wo) ↦ φ a)
        (Scheme.Hom.appLE_comp_appLE f' j N (j ⁻¹ᵁ N) Wo le_rfl h'))
  · rintro ⟨N', h, a, rfl⟩
    have h2 : Wo ≤ (f' ≫ j) ⁻¹ᵁ (j ''ᵁ N') := by
      rwa [Scheme.Hom.comp_preimage, j.preimage_image_eq]
    refine ⟨j ''ᵁ N', h2, (j.appIso N').inv a, ?_⟩
    have key : (j.appIso N').inv ≫ (f' ≫ j).appLE (j ''ᵁ N') Wo h2 = f'.appLE N' Wo h := by
      rw [← Scheme.Hom.appLE_comp_appLE f' j (j ''ᵁ N') N' Wo
        (j.preimage_image_eq N').ge h, ← Category.assoc, Scheme.Hom.appIso_inv_appLE]
      simp
    exact (CommRingCat.comp_apply _ _ a).symm.trans
      (congrArg (fun φ : Γ(Y', N') ⟶ Γ(T.scheme, Wo) ↦ φ a) key)

/-! ### `Ω_{V/S|_W}` is the restriction of `Ω_{X/S}` -/

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-- **The sections pulled back from the divided power base are the same for an object of
`Cris(V/S|_W)` and for its extension to `Cris(X/S)`.** -/
theorem crysBaseSections_extend (A : Thickening (restrict S W V hVW)) :
    crysBaseSections S ((extend S W V hVW).obj A) =
      crysBaseSections (restrict S W V hVW) A := by
  have h : ((extend S W V hVW).obj A).toBase.hom =
      A.toBase.hom ≫ (restrictSι S W V hVW).hom :=
    DividedPowerScheme.Hom.comp_hom _ _
  rw [show crysBaseSections S ((extend S W V hVW).obj A) =
      baseSections A.thickening.target S.S.scheme
        (A.toBase.hom ≫ (restrictSι S W V hVW).hom) ⊤ from h ▸ rfl]
  exact baseSections_comp_of_isOpenImmersion _ _ _ _

namespace SmallSite

/-- For an object `A` of `Cris(V/S|_W)`, the image of a global section of `S` in the global
sections of the extension of `A` to `Cris(X/S)` lies among the sections of `A` pulled back from the
base `S|_W`. -/
theorem crysBaseAppLE_mem_crysBaseSections_extend
    (A : CrystallineThickening (restrict S W V hVW))
    (a : Γ(S.S.scheme, ⊤)) :
    GlobalCrystallineSituation.crysBaseAppLE S ((smallExtend S W V hVW).obj A).obj a ∈
      GlobalCrystallineSituation.crysBaseSections (restrict S W V hVW) A.obj :=
  (crysBaseSections_extend S W V hVW A.obj) ▸ appLE_mem_baseSections _ _ _ ⊤ ⊤ _ a

/-- For an object `A` of `Cris(V/S|_W)`, the image of a global section of `S|_W` in the global
sections of `A` lies among the sections of the extension of `A` to `Cris(X/S)` pulled back from
the base `S`. -/
theorem crysBaseAppLE_mem_crysBaseSections_restrict
    (A : CrystallineThickening (restrict S W V hVW))
    (a : Γ((restrict S W V hVW).S.scheme, ⊤)) :
    GlobalCrystallineSituation.crysBaseAppLE (restrict S W V hVW) A.obj a ∈
      GlobalCrystallineSituation.crysBaseSections S
        ((smallExtend S W V hVW).obj A).obj :=
  (crysBaseSections_extend S W V hVW A.obj).symm ▸ appLE_mem_baseSections _ _ _ ⊤ ⊤ _ a

/-- For an object `A` of `Cris(V/S|_W)`, the crystalline differentials of the extension of `A` to
`Cris(X/S)` are isomorphic to the crystalline differentials of `A`. -/
def smallExtendCrysDifferentialsObjIso (A : CrystallineThickening (restrict S W V hVW)) :
    GlobalCrystallineSituation.crysDifferentialsObj S
        ((smallExtend S W V hVW).obj A).obj ≅
      GlobalCrystallineSituation.crysDifferentialsObj (restrict S W V hVW) A.obj :=
  dpConstDifferentialsCongrBase _ _ _ _ _
    (le_of_eq (crysBaseSections_extend S W V hVW A.obj))
    (le_of_eq (crysBaseSections_extend S W V hVW A.obj).symm)
    (crysBaseAppLE_mem_crysBaseSections_extend S W V hVW A)
    (crysBaseAppLE_mem_crysBaseSections_restrict S W V hVW A)

/-- **The object-wise comparison is compatible with the transition maps.** -/
theorem crysDifferentialsMap_smallExtendCrysDifferentialsObjIso
    {P Q : CrystallineThickening (restrict S W V hVW)} (k : Q ⟶ P) :
    GlobalCrystallineSituation.crysDifferentialsMap S ((smallExtend S W V hVW).map k).hom ≫
        (ModuleCat.restrictScalars (k.hom.targetHom.hom.appTop).hom).map
          (smallExtendCrysDifferentialsObjIso S W V hVW Q).hom =
      (smallExtendCrysDifferentialsObjIso S W V hVW P).hom ≫
        GlobalCrystallineSituation.crysDifferentialsMap (restrict S W V hVW) k.hom :=
  dpConstMap_dpConstDifferentialsCongrHom _ _ _ _ _ _ _ _ _ _ _
    (le_of_eq (crysBaseSections_extend S W V hVW P.obj))
    (crysBaseAppLE_mem_crysBaseSections_extend S W V hVW P)
    (le_of_eq (crysBaseSections_extend S W V hVW Q.obj))
    (crysBaseAppLE_mem_crysBaseSections_extend S W V hVW Q)

/-- **`Ω_{V/S|_W}` is the restriction of `Ω_{X/S}` along `smallExtend`.** -/
def smallExtendCrysDifferentialsIso :
    (smallExtendModuleRestriction S W V hVW).obj (crysDifferentials S) ≅
      crysDifferentials (restrict S W V hVW) :=
  PresheafOfModules.isoMk (fun A ↦ smallExtendCrysDifferentialsObjIso S W V hVW A.unop)
    (fun {_ _} f ↦ crysDifferentialsMap_smallExtendCrysDifferentialsObjIso S W V hVW f.unop)

end SmallSite

end GlobalCrystallineSituation

end Crystalline

end

end

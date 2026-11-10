module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelBridge07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechFunctorialRing07Q9

/-!
# The morphism of Čech systems over `f : X' ⟶ X`

Fix a global crystalline situation `(p, (S, I, γ), X)`, affine opens `V ⊆ S` and `W ⊆ X` with `W`
mapping into `V`, a morphism `f : X' ⟶ X` with `W' = f⁻¹(W)` affine, surjective polynomial
presentations `P → Γ(W, ⊤)` and `P' → Γ(W', ⊤)` over `Γ(V, ⊤)`, and a morphism of presentations
`r : P → P'` compatible with `f^♯`.  Let `T` and `T'` be the Čech systems `openSystem07Q9` of the
two presentations, in `Cris(X/S)` and in `Cris(X'/S)` (the situation `X'/S` over the same divided
power base being `overSituation S f`).

This file builds the morphism of systems over `f`: for all `n` and `e` a morphism

`τ n e : f_*(T'(n)_e) ⟶ T(n)_{e + N'}`

of `CRIS(X/S)`, where `f_*` is change of base along `(𝟙, f)` and `N'` is the uniform cutoff of the
levels of `T'`, and proves that it is natural in `n` (the simplicial structure) and in `e` (the
tower maps).  On rings `τ n e` is the map of finite levels
`D(n)/(p)^{N + e + N'} → D'(n)/(p)^{N' + e}` induced by the divided power morphism
`D(n) ⟶ D'(n)` of `envelopeRingMap07Q9`; the shift `N'` is what makes that map exist,
`p^{N' + e}` being zero in the target.

## Main definitions

* `openSystemShift07Q9` — the shift `N'`.
* `openSystemMap07Q9` — the morphism `τ n e`.

## Main results

* `openSystemMap07Q9_naturality_tower` — naturality in the tower direction.
* `openSystemMap07Q9_naturality_simplicial` — naturality in the simplicial direction.

## References

* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)
  {X' : Scheme.{u}} (f : X' ⟶ S.X)

/-! ### Change of base between the two restricted situations -/

/-- **The restriction of `f` is a morphism of the restricted situations** over the identity of
`S|_V`: the compatibility datum of change of base. -/
theorem restrictMap07Q9_condition :
    (restrict (overSituation S f) V (f ⁻¹ᵁ W)
        (preimage_le_overSituation07Q9 S hVW f)).toClosedFiber ≫
        DividedPowerScheme.closedFiberMap (𝟙 (S.S.restrict V)) =
      restrictMap07Q9 S hVW f ≫ (restrict S V W hVW).toClosedFiber := by
  have h1 : DividedPowerScheme.closedFiberMap (𝟙 (S.S.restrict V)) = 𝟙 _ :=
    DividedPowerScheme.closedFiberFunctor.map_id _
  refine (congrArg (_ ≫ ·) h1).trans ((Category.comp_id _).trans ?_)
  refine (cancel_mono (DividedPowerScheme.closedFiberι (S.S.restrict V))).mp ?_
  exact (sourceToBase_restrict_overSituation07Q9 S hVW f).trans (Category.assoc _ _ _).symm

/-- **Change of base from the restricted situation of `X'/S` to the restricted situation of
`X/S`**, along the identity of `S|_V` and the restriction `f⁻¹(W) ⟶ W` of `f`. -/
abbrev restrictChangeBase07Q9 :
    Thickening (restrict (overSituation S f) V (f ⁻¹ᵁ W) (preimage_le_overSituation07Q9 S hVW f)) ⥤
      Thickening (restrict S V W hVW) :=
  changeBase _ _ (𝟙 (S.S.restrict V)) (restrictMap07Q9 S hVW f)
    (restrictMap07Q9_condition S hVW f)

/-- **The two ways from the restricted situation of `X'/S` to `X/S` agree**: extending to `X'/S`
and changing base along `f`, or changing base to the restricted situation of `X/S` and extending.
The two objects have the same thickening and equal structure morphisms, and this is the
comparison morphism with identity components. -/
def extendChangeBaseHom07Q9
    (Y : Thickening (restrict (overSituation S f) V (f ⁻¹ᵁ W)
      (preimage_le_overSituation07Q9 S hVW f))) :
    (changeBase (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)).obj
        ((extend (overSituation S f) V (f ⁻¹ᵁ W) (preimage_le_overSituation07Q9 S hVW f)).obj Y) ⟶
      (extend S V W hVW).obj ((restrictChangeBase07Q9 S hVW f).obj Y) where
  sourceHom := 𝟙 _
  targetHom := 𝟙 _
  immersion_naturality := (Category.comp_id _).trans (Category.id_comp _).symm
  base_naturality := by
    change 𝟙 _ ≫ ((Y.toBase ≫ 𝟙 _) ≫ S.S.restrictι V) = (Y.toBase ≫ S.S.restrictι V) ≫ 𝟙 S.S
    simp only [Category.id_comp, Category.comp_id]
  toX_naturality := by
    change 𝟙 _ ≫ ((Y.toX ≫ restrictMap07Q9 S hVW f) ≫ restrictXι S V W hVW) =
      (Y.toX ≫ restrictXι (overSituation S f) V (f ⁻¹ᵁ W)
        (preimage_le_overSituation07Q9 S hVW f)) ≫ f
    rw [Category.id_comp, Category.assoc, restrictMap07Q9_comp_restrictXι, Category.assoc]

/-- The comparison morphism is natural. -/
theorem extendChangeBaseHom07Q9_naturality
    {Y Y' : Thickening (restrict (overSituation S f) V (f ⁻¹ᵁ W)
      (preimage_le_overSituation07Q9 S hVW f))} (y : Y ⟶ Y') :
    (changeBase (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)).map
        ((extend (overSituation S f) V (f ⁻¹ᵁ W) (preimage_le_overSituation07Q9 S hVW f)).map y) ≫
        extendChangeBaseHom07Q9 S hVW f Y' =
      extendChangeBaseHom07Q9 S hVW f Y ≫
        (extend S V W hVW).map ((restrictChangeBase07Q9 S hVW f).map y) :=
  Thickening.Hom.ext ((Category.comp_id y.sourceHom).trans (Category.id_comp y.sourceHom).symm)
    ((Category.comp_id y.targetHom).trans (Category.id_comp y.targetHom).symm)

/-! ### The morphisms of the restricted systems -/

variable (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {ι κ : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A
    →ₐ[(openAffineSituation07Q9 S hW hVW).A] (openAffineSituation07Q9 S hW hVW).C)
  (hg : Function.Surjective g)
  (g₂ : MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A
    →ₐ[(openAffineSituation₂07Q9 S hVW f hW₂).A] (openAffineSituation₂07Q9 S hVW f hW₂).C)
  (hg₂ : Function.Surjective g₂)
  (r : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →+*
    MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A)
  (hr : g₂.toRingHom.comp r = (restrictMap07Q9 S hVW f).appTop.hom.comp g.toRingHom)

/-- **The shift of the levels**: the uniform cutoff of the levels of the system of `X'/S`. -/
abbrev openSystemShift07Q9 : ℕ := uniformLevel (openAffineSituation₂07Q9 S hVW f hW₂)

/-- The finite level `D(n)/(p)^{N + e}` of the system of `X/S`. -/
abbrev levelObj07Q9 (n e : ℕ) :
    _root_.Crystalline.CrystallineThickening.{u, u, u} (openAffineSituation07Q9 S hW hVW) :=
  ((affineLevelSystem _ g hg).obj ⦋n⦌).obj (op e)

/-- The finite level `D'(n)/(p)^{N' + e}` of the system of `X'/S`. -/
abbrev levelObj₂07Q9 (n e : ℕ) :
    _root_.Crystalline.CrystallineThickening.{u, u, u} (openAffineSituation₂07Q9 S hVW f hW₂) :=
  ((affineLevelSystem _ g₂ hg₂).obj ⦋n⦌).obj (op e)

/-- **The map of finite levels `D(n)/(p)^{N + e + N'} ⟶ D'(n)/(p)^{N' + e}`** induced by the
divided power morphism `D(n) ⟶ D'(n)`. -/
def levelRingMap07Q9 (n e : ℕ) :
    (levelObj07Q9 S hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂)).obj.ring ⟶
      (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ n e).obj.ring :=
  levelHom S.p
    (isPAdicLevel_uniformLevel_add (tensorPowerEnvelopeThickening _ g hg n).thickening
      (e + openSystemShift07Q9 S hVW f hW₂))
    (isPAdicLevel_uniformLevel_add (tensorPowerEnvelopeThickening _ g₂ hg₂ n).thickening e)
    (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n)
    ((Nat.add_comm _ _).le.trans (Nat.le_add_left _ _))

/-- The maps of finite levels commute with the level drops. -/
theorem levelRingMap07Q9_tower (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    (((affineLevelSystem _ g hg).obj ⦋n⦌).map
        (homOfLE (Nat.add_le_add_right h (openSystemShift07Q9 S hVW f hW₂))).op).hom.hom ≫
        levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e =
      levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e' ≫
        (((affineLevelSystem _ g₂ hg₂).obj ⦋n⦌).map (homOfLE h).op).hom.hom := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The maps of finite levels commute with the cosimplicial structure maps. -/
theorem levelRingMap07Q9_simplicial {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (e : ℕ) :
    (((affineLevelSystem _ g hg).map φ).app
        (op (e + openSystemShift07Q9 S hVW f hW₂))).hom.hom ≫
        levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr m e =
      levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e ≫
        (((affineLevelSystem _ g₂ hg₂).map φ).app (op e)).hom.hom := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (Ideal.Quotient.mk _) (congrArg (fun q : DividedPowers.DPMorphism _ _ ↦ q a)
    (envelopeRingMap07Q9_comp_map S hW hVW f hW₂ g hg g₂ hg₂ r hr φ))

/-! ### The morphisms of the restricted systems -/

/-- The level `e` in degree `n` of the restricted system of `X'/S`, read in `CRIS(W/S|_V)` by
change of base along the restriction of `f`. -/
abbrev sourceObj07Q9 (n e : ℕ) : Thickening (restrict S V W hVW) :=
  (restrictChangeBase07Q9 S hVW f).obj ((CrystallineThickening.ι _).obj
    (((openLocalSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
      g₂ hg₂).obj (op ⦋n⦌)).obj e))

/-- The thickened scheme of `sourceObj07Q9` is affine, being isomorphic to `f⁻¹(W)`. -/
theorem isAffine_sourceObj07Q9 (n e : ℕ) :
    IsAffine (sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e).thickening.source :=
  @IsAffine.of_isIso _ _ (((openLocalSystem07Q9 (overSituation S f) hV hW₂
    (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).obj (op ⦋n⦌)).obj e).obj.toX
    (isIso_toX_openLocalSystem07Q9 (overSituation S f) hV hW₂
      (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂ n e)
    (isAffine_restrictX07Q9 (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f))

/-- The counit of the equivalence of the restricted situation of `X'/S` at a finite level. -/
abbrev levelCounit₂07Q9 (n e : ℕ) :
    haveI : IsAffine ((CrystallineThickening.ι _).obj
        (((openLocalSystem07Q9 (overSituation S f) hV hW₂
          (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).obj (op ⦋n⦌)).obj e)).thickening.source :=
      isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e
    (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ n e).obj ⟶
      wholeThickeningToAffine (isNilpotent_prime_openSituation07Q9 (overSituation S f) hW₂
        (preimage_le_overSituation07Q9 S hVW f)) ((CrystallineThickening.ι _).obj
          (((openLocalSystem07Q9 (overSituation S f) hV hW₂
            (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).obj (op ⦋n⦌)).obj e)) :=
  haveI := isAffine_restrictX07Q9 (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f)
  haveI := isAffine_restrictS07Q9 (overSituation S f) hV (preimage_le_overSituation07Q9 S hVW f)
  ((wholeSiteEquivLittleAffine (isNilpotent_prime_openSituation07Q9 (overSituation S f) hW₂
    (preimage_le_overSituation07Q9 S hVW f))).counitIso.inv.app
      (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ n e)).hom

/-- **The morphism of `CRIS(Γ(W, ⊤)/Γ(V, ⊤))` out of the level `D(n)/(p)^{N + e + N'}` into the
global sections of `sourceObj07Q9`**: the map of finite levels followed by the identification of
`D'(n)/(p)^{N' + e}` with the global sections of the corresponding object of `CRIS(f⁻¹(W)/S|_V)`.
It is over `Γ(V, ⊤)`, and compatible with the structural maps out of `Γ(W, ⊤)` because the map
of finite levels is compatible with `f^♯`. -/
def levelAffineHom07Q9 (n e : ℕ) :
    (levelObj07Q9 S hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂)).obj ⟶
      @wholeThickeningToAffine _ (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e)
        (isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e) :=
  { hom := levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e ≫
      (levelCounit₂07Q9 S hV hVW f hW₂ g₂ hg₂ n e).hom
    fromBase_comp := by
      apply DividedPowers.DPMorphism.ext
      funext a
      have h1 : levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e
          ((levelObj07Q9 S hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂)).obj.fromBase a) =
          (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ n e).obj.fromBase a := by
        change Ideal.Quotient.mk _ (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n
            ((tensorPowerEnvelopeThickening _ g hg n).thickening.fromBase a)) =
          Ideal.Quotient.mk _ ((tensorPowerEnvelopeThickening _ g₂ hg₂ n).thickening.fromBase a)
        rw [envelopeRingMap07Q9_fromBase]
      change (levelCounit₂07Q9 S hV hVW f hW₂ g₂ hg₂ n e).hom
          (levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e
            ((levelObj07Q9 S hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂)).obj.fromBase
              a)) =
        globalSectionsDPMorphism (((CrystallineThickening.ι _).obj
          (((openLocalSystem07Q9 (overSituation S f) hV hW₂
            (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).obj (op ⦋n⦌)).obj e)).toBase ≫
              𝟙 _) a
      rw [h1, Category.comp_id]
      exact congrArg (fun q : DividedPowers.DPMorphism _ _ ↦ q a)
        (levelCounit₂07Q9 S hV hVW f hW₂ g₂ hg₂ n e).fromBase_comp
    toQuotient_comp := by
      refine RingHom.ext fun x ↦ ?_
      obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective
        ((tensorPowerEnvelopeThickening _ g hg n).thickening.toQuotient x)
      have key : (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ n e).obj.toQuotient
          ((restrictMap07Q9 S hVW f).appTop.hom x) =
          Ideal.Quotient.mk _ (levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e
            (Ideal.Quotient.mk _ d)) := by
        change levelQuotientMap _ _ _ _
          ((tensorPowerEnvelopeThickening _ g₂ hg₂ n).thickening.toQuotient
            ((restrictMap07Q9 S hVW f).appTop.hom x)) = _
        rw [← envelopeRingMap07Q9_toQuotient, ← hd, DividedPowerRing.quotientRingHom_mk,
          levelQuotientMap_mk]
        rfl
      have hc := RingHom.congr_fun (levelCounit₂07Q9 S hV hVW f hW₂ g₂ hg₂ n e).toQuotient_comp
        ((restrictMap07Q9 S hVW f).appTop.hom x)
      change DividedPowerRing.quotientRingHom _ (levelQuotientMap _ _ _ _
          ((tensorPowerEnvelopeThickening _ g hg n).thickening.toQuotient x)) = _
      rw [← hd, levelQuotientMap_mk]
      exact (DividedPowerRing.quotientRingHom_mk _ _).trans
        (((DividedPowerRing.quotientRingHom_mk _ _).symm.trans (congrArg _ key.symm)).trans hc) }

/-- **The morphism of the restricted systems in `CRIS(W/S|_V)`**: the morphism from the level `e`
in degree `n` of the restricted system of `X'/S`, read by change of base along the restriction of
`f`, into the level `e + N'` in degree `n` of the restricted system of `X/S`, whose map on global
sections is `levelAffineHom07Q9`. -/
def localSystemMap07Q9 (n e : ℕ) :
    sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e ⟶
      (CrystallineThickening.ι _).obj (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj
        (e + openSystemShift07Q9 S hVW f hW₂)) :=
  (@exists_levelBridge_eq (restrict S V W hVW) (isAffine_restrictX07Q9 S hW hVW)
    (isAffine_restrictS07Q9 S hV hVW) (isNilpotent_prime_openSituation07Q9 S hW hVW) _
    (isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e) _
    (levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e)).choose

/-- `localSystemMap07Q9` induces `levelAffineHom07Q9` on global sections. -/
theorem levelBridge_localSystemMap07Q9 (n e : ℕ) :
    @levelBridge (restrict S V W hVW) (isAffine_restrictX07Q9 S hW hVW)
      (isAffine_restrictS07Q9 S hV hVW) (isNilpotent_prime_openSituation07Q9 S hW hVW) _
      (isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e) _
      (localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e) =
      levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e :=
  (@exists_levelBridge_eq (restrict S V W hVW) (isAffine_restrictX07Q9 S hW hVW)
    (isAffine_restrictS07Q9 S hV hVW) (isNilpotent_prime_openSituation07Q9 S hW hVW) _
    (isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e) _
    (levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e)).choose_spec

/-- **Naturality of `localSystemMap07Q9` in the tower direction.** -/
theorem localSystemMap07Q9_tower (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    (restrictChangeBase07Q9 S hVW f).map ((CrystallineThickening.ι _).map
        (((openLocalSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
          g₂ hg₂).obj (op ⦋n⦌)).map (homOfLE h))) ≫
        localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e' =
      localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e ≫
        (CrystallineThickening.ι _).map (((openLocalSystem07Q9 S hV hW hVW g hg).obj
          (op ⦋n⦌)).map (homOfLE (Nat.add_le_add_right h (openSystemShift07Q9 S hVW f hW₂)))) := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  have := isAffine_restrictX07Q9 (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f)
  have := isAffine_restrictS07Q9 (overSituation S f) hV (preimage_le_overSituation07Q9 S hVW f)
  have := isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e
  have := isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e'
  let hp := isNilpotent_prime_openSituation07Q9 S hW hVW
  let hp₂ := isNilpotent_prime_openSituation07Q9 (overSituation S f) hW₂
    (preimage_le_overSituation07Q9 S hVW f)
  let ψ := ((affineLevelSystem _ g hg).obj ⦋n⦌).map
    (homOfLE (Nat.add_le_add_right h (openSystemShift07Q9 S hVW f hW₂))).op
  let ψ₂ := ((affineLevelSystem _ g₂ hg₂).obj ⦋n⦌).map (homOfLE h).op
  let x := (CrystallineThickening.ι _).map
    (((openLocalSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
      g₂ hg₂).obj (op ⦋n⦌)).map (homOfLE h))
  have e1 : levelBridge hp _ _ ((restrictChangeBase07Q9 S hVW f).map x ≫
      localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e') =
      levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e' ≫
        wholeHomToAffine hp ((restrictChangeBase07Q9 S hVW f).map x) :=
    (levelBridge_comp _ _).trans
      (congrArg (· ≫ _)
        (levelBridge_localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e'))
  have e2 : levelBridge hp _ _ (localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e ≫
      (CrystallineThickening.ι _).map (((openLocalSystem07Q9 S hV hW hVW g hg).obj
        (op ⦋n⦌)).map (homOfLE (Nat.add_le_add_right h (openSystemShift07Q9 S hVW f hW₂))))) =
      ψ.hom ≫ levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e :=
    (levelBridge_comp_inverse_map _ ψ).trans
      (congrArg (ψ.hom ≫ ·)
        (levelBridge_localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e))
  have hn := congrArg (fun y ↦ y.hom.hom)
    ((wholeSiteEquivLittleAffine hp₂).counitIso.inv.naturality ψ₂)
  have e3 : levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e' ≫
        wholeHomToAffine hp ((restrictChangeBase07Q9 S hVW f).map x) =
      ψ.hom ≫ levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e := by
    apply DividedPowerThickening.Hom.ext
    change (levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e' ≫
        (levelCounit₂07Q9 S hV hVW f hW₂ g₂ hg₂ n e').hom) ≫
          ((wholeSiteEquivLittleAffine hp₂).functor.map
            ((wholeSiteEquivLittleAffine hp₂).inverse.map ψ₂)).hom.hom =
      ψ.hom.hom ≫ (levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e ≫
        (levelCounit₂07Q9 S hV hVW f hW₂ g₂ hg₂ n e).hom)
    exact (Category.assoc _ _ _).trans ((congrArg _ hn.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (levelRingMap07Q9_tower S hW hVW f hW₂ g hg g₂ hg₂ r hr n h).symm).trans
          (Category.assoc _ _ _))))
  exact levelBridge_injective (hp := hp) _ _ (e1.trans (e3.trans e2.symm))

/-- **Naturality of `localSystemMap07Q9` in the simplicial direction.** -/
theorem localSystemMap07Q9_simplicial {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (e : ℕ) :
    (restrictChangeBase07Q9 S hVW f).map ((CrystallineThickening.ι _).map
        (((openLocalSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
          g₂ hg₂).map φ.op).app e)) ≫
        localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e =
      localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr m e ≫
        (CrystallineThickening.ι _).map (((openLocalSystem07Q9 S hV hW hVW g hg).map φ.op).app
          (e + openSystemShift07Q9 S hVW f hW₂)) := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  have := isAffine_restrictX07Q9 (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f)
  have := isAffine_restrictS07Q9 (overSituation S f) hV (preimage_le_overSituation07Q9 S hVW f)
  have := isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e
  have := isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ m e
  let hp := isNilpotent_prime_openSituation07Q9 S hW hVW
  let hp₂ := isNilpotent_prime_openSituation07Q9 (overSituation S f) hW₂
    (preimage_le_overSituation07Q9 S hVW f)
  let ψ := ((affineLevelSystem _ g hg).map φ).app (op (e + openSystemShift07Q9 S hVW f hW₂))
  let ψ₂ := ((affineLevelSystem _ g₂ hg₂).map φ).app (op e)
  let x := (CrystallineThickening.ι _).map
    (((openLocalSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
      g₂ hg₂).map φ.op).app e)
  have e1 : levelBridge hp _ _ ((restrictChangeBase07Q9 S hVW f).map x ≫
      localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e) =
      levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e ≫
        wholeHomToAffine hp ((restrictChangeBase07Q9 S hVW f).map x) :=
    (levelBridge_comp _ _).trans
      (congrArg (· ≫ _) (levelBridge_localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e))
  have e2 : levelBridge hp _ _ (localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr m e ≫
      (CrystallineThickening.ι _).map (((openLocalSystem07Q9 S hV hW hVW g hg).map φ.op).app
        (e + openSystemShift07Q9 S hVW f hW₂))) =
      ψ.hom ≫ levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr m e :=
    (levelBridge_comp_inverse_map _ ψ).trans
      (congrArg (ψ.hom ≫ ·)
        (levelBridge_localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr m e))
  have hn := congrArg (fun y ↦ y.hom.hom)
    ((wholeSiteEquivLittleAffine hp₂).counitIso.inv.naturality ψ₂)
  have e3 : levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e ≫
        wholeHomToAffine hp ((restrictChangeBase07Q9 S hVW f).map x) =
      ψ.hom ≫ levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr m e := by
    apply DividedPowerThickening.Hom.ext
    change (levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e ≫
        (levelCounit₂07Q9 S hV hVW f hW₂ g₂ hg₂ n e).hom) ≫
          ((wholeSiteEquivLittleAffine hp₂).functor.map
            ((wholeSiteEquivLittleAffine hp₂).inverse.map ψ₂)).hom.hom =
      ψ.hom.hom ≫ (levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr m e ≫
        (levelCounit₂07Q9 S hV hVW f hW₂ g₂ hg₂ m e).hom)
    exact (Category.assoc _ _ _).trans ((congrArg _ hn.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (levelRingMap07Q9_simplicial S hW hVW f hW₂ g hg g₂ hg₂ r hr φ e).symm).trans
          (Category.assoc _ _ _))))
  exact levelBridge_injective (hp := hp) _ _ (e1.trans (e3.trans e2.symm))

/-! ### The morphism of systems over `f` -/

/-- **The morphism of Čech systems over `f : X' ⟶ X`.**  For all `n` and `e`, the morphism of
`CRIS(X/S)` from the change of base along `(𝟙, f)` of the level `e` in degree `n` of the system of
`X'/S` into the level `e + N'` in degree `n` of the system of `X/S`.  On rings it is the map of
finite levels `D(n)/(p)^{N + e + N'} → D'(n)/(p)^{N' + e}` induced by the divided power morphism
`D(n) ⟶ D'(n)` of the morphism of presentations; `N'` is `openSystemShift07Q9`. -/
def openSystemMap07Q9 (n e : ℕ) :
    (changeBase (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)).obj
        ((CrystallineThickening.ι (overSituation S f)).obj
          (((openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
            g₂ hg₂).obj (op ⦋n⦌)).obj e)) ⟶
      (CrystallineThickening.ι S).obj (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj
        (e + openSystemShift07Q9 S hVW f hW₂)) :=
  extendChangeBaseHom07Q9 S hVW f _ ≫
    (extend S V W hVW).map (localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e)

/-- **Naturality of the morphism of systems in the tower direction**: it commutes with the tower
maps `T'(n)_e ⟶ T'(n)_{e'}` and `T(n)_{e + N'} ⟶ T(n)_{e' + N'}`. -/
theorem openSystemMap07Q9_naturality_tower (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    (changeBase (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)).map
        ((CrystallineThickening.ι (overSituation S f)).map
          (((openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
            g₂ hg₂).obj (op ⦋n⦌)).map (homOfLE h))) ≫
        openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e' =
      openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e ≫
        (CrystallineThickening.ι S).map (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).map
          (homOfLE (Nat.add_le_add_right h (openSystemShift07Q9 S hVW f hW₂)))) := by
  have h1 := extendChangeBaseHom07Q9_naturality S hVW f ((CrystallineThickening.ι _).map
    (((openLocalSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
      g₂ hg₂).obj (op ⦋n⦌)).map (homOfLE h)))
  have h2 := congrArg (extend S V W hVW).map
    (localSystemMap07Q9_tower S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n h)
  rw [Functor.map_comp, Functor.map_comp] at h2
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

/-- **Naturality of the morphism of systems in the simplicial direction**: it commutes with the
simplicial structure maps `T'(m)_e ⟶ T'(n)_e` and `T(m)_{e + N'} ⟶ T(n)_{e + N'}` of a map
`⦋n⦌ ⟶ ⦋m⦌` of the simplex category. -/
theorem openSystemMap07Q9_naturality_simplicial {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (e : ℕ) :
    (changeBase (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)).map
        ((CrystallineThickening.ι (overSituation S f)).map
          (((openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
            g₂ hg₂).map φ.op).app e)) ≫
        openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e =
      openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr m e ≫
        (CrystallineThickening.ι S).map (((openSystem07Q9 S hV hW hVW g hg).map φ.op).app
          (e + openSystemShift07Q9 S hVW f hW₂)) := by
  have h1 := extendChangeBaseHom07Q9_naturality S hVW f ((CrystallineThickening.ι _).map
    (((openLocalSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
      g₂ hg₂).map φ.op).app e))
  have h2 := congrArg (extend S V W hVW).map
    (localSystemMap07Q9_simplicial S hV hW hVW f hW₂ g hg g₂ hg₂ r hr φ e)
  rw [Functor.map_comp, Functor.map_comp] at h2
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

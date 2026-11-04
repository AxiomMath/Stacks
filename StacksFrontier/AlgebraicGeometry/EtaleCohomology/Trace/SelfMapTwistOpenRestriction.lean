module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapTwistInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralExtensionByZeroRing

/-!
# Restricting a self-map twist to an open subscheme

Consider a commutative square of schemes `p ≫ m = g ≫ q` with `g : U ⟶ Y` an étale monomorphism
(an open immersion, say), an endomorphism `φ` of `Y` over `S` and an endomorphism `φ_U` of `U`
over `V`, such that `φ_U ≫ g = g ≫ φ` is cartesian.  For a sheaf `M` of `Λ`-modules on `S` with
an isomorphism `ν : m^{-1} M ≅ F` (for `m` an étale monomorphism and `M = m_! F`, the inverse of
the unit, `Stacks.EtaleCohomology.inverseImageExtensionByZeroIso`), `g^{-1} q^{-1} M ≅ p^{-1} F`
canonically (`Stacks.EtaleCohomology.selfMapTwistOpenRestrictionIso`:
`g^{-1} q^{-1} ≅ (p ≫ m)^{-1} ≅ p^{-1} m^{-1}` and `p^{-1}(ν)`), and under it the restriction to
`U` of the self-map twist of `q^{-1} M` along `φ`, read through `g^{-1} φ_* ≅ φ_{U,*} g^{-1}`
(`Stacks.EtaleCohomology.restrictionIntegralDirectImageIso`), is the self-map twist of
`p^{-1} F` along `φ_U` (`Stacks.EtaleCohomology.selfMapTwistOpenRestrictionIso_selfMapTwist`).

## Main definitions

* `Stacks.EtaleCohomology.inverseImageExtensionByZeroIso`.
* `Stacks.EtaleCohomology.selfMapTwistOpenInverseImageIso`.
* `Stacks.EtaleCohomology.selfMapTwistOpenRestrictionIso`.

## Main results

* `Stacks.EtaleCohomology.restrictionIntegralDirectImageIso_inv`.
* `Stacks.EtaleCohomology.selfMapTwistOpenInverseImageIso_selfMapTwist`.
* `Stacks.EtaleCohomology.selfMapTwistOpenRestrictionIso_selfMapTwist`.

## Implementation notes

Everything is stated for `Λ : Type`, the universe of `restrictionIntegralDirectImageIso`, and the
composite isomorphisms are typed through the composite functor `q^{-1} ⋙ g^{-1}` and assembled by
lemmas about abstract functors (`Stacks.EtaleCohomology.twist_chase_of_comp`,
`Stacks.EtaleCohomology.restriction_chase_of_iso`).  Instantiating a universe-polymorphic
statement at `Λ : Type` and comparing it with one elaborated at `Λ : Type` spells the universe
levels differently, and comparing `g^{-1}(q^{-1} M)` with `(q^{-1} ⋙ g^{-1}) M` for the heavy
inverse image functors makes the kernel unfold them: either one alone causes deterministic kernel
timeouts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-! ### Two diagram chases, for abstract functors -/

section Chase

variable {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
  (Iq : 𝒜 ⥤ ℬ) (Ig : ℬ ⥤ 𝒞) (IfU : 𝒜 ⥤ 𝒞) (Im : 𝒜 ⥤ 𝒟) (Ip : 𝒟 ⥤ 𝒞) (Dφ : ℬ ⥤ ℬ)
  (DU : 𝒞 ⥤ 𝒞) (e₁ : Iq ⋙ Ig ≅ IfU) (e₂ : Im ⋙ Ip ≅ IfU)

/-- The forward map of `e₁ ≪≫ e₂⁻¹ ≪≫ Ip(ν)` at an object. -/
public lemma iso_trans_symm_mapIso_hom (M : 𝒜) {F : 𝒟} (ν : Im.obj M ≅ F) :
    (e₁.app M ≪≫ (e₂.app M).symm ≪≫ Ip.mapIso ν).hom =
      e₁.hom.app M ≫ e₂.inv.app M ≫ Ip.map ν.hom :=
  rfl

/-- **The twist chase**: from `Ig(τ_q) ≫ β ≫ DU(e₁) = e₁ ≫ τ_U` and
`τ_p ≫ DU(e₂) = e₂ ≫ τ_U`, the twist `Ig(τ_q) ≫ β` is carried by `e₁ ≪≫ e₂⁻¹ ≪≫ Ip(ν)` to
`τ_p`. -/
public lemma twist_chase_of_comp (τq : Iq ⟶ Iq ⋙ Dφ) (β : Dφ ⋙ Ig ⟶ Ig ⋙ DU)
    (τU : IfU ⟶ IfU ⋙ DU) (τp : Ip ⟶ Ip ⋙ DU) (M : 𝒜) {F : 𝒟} (ν : Im.obj M ≅ F)
    (h₁ : Ig.map (τq.app M) ≫ β.app (Iq.obj M) ≫ DU.map (e₁.hom.app M) =
      e₁.hom.app M ≫ τU.app M)
    (h₂ : τp.app (Im.obj M) ≫ DU.map (e₂.hom.app M) = e₂.hom.app M ≫ τU.app M) :
    Ig.map (τq.app M) ≫ β.app (Iq.obj M) ≫
        DU.map (e₁.app M ≪≫ (e₂.app M).symm ≪≫ Ip.mapIso ν).hom =
      (e₁.app M ≪≫ (e₂.app M).symm ≪≫ Ip.mapIso ν).hom ≫ τp.app F := by
  have h₂' : e₂.inv.app M ≫ τp.app (Im.obj M) = τU.app M ≫ DU.map (e₂.inv.app M) := by
    rw [← cancel_epi (e₂.hom.app M), Iso.hom_inv_id_app_assoc, ← reassoc_of% h₂,
      ← DU.map_comp, Iso.hom_inv_id_app]
    simp
  have h₃ := τp.naturality ν.hom
  dsimp only [Functor.comp_obj, Functor.comp_map] at h₃
  rw [iso_trans_symm_mapIso_hom]
  simp only [DU.map_comp, Category.assoc]
  rw [reassoc_of% h₁, ← reassoc_of% h₂', ← h₃]

/-- The isomorphism `R(Iq M) ≅ Ig(Iq M) ≅ E` through a component of `ε : Ig ≅ R`. -/
public def restrictionCompIso (R : ℬ ⥤ 𝒞) (ε : Ig ≅ R) (M : 𝒜) {E : 𝒞}
    (lam : (Iq ⋙ Ig).obj M ≅ E) : R.obj (Iq.obj M) ≅ E :=
  (ε.app (Iq.obj M)).symm ≪≫ lam

/-- The forward map of `Stacks.EtaleCohomology.restrictionCompIso`. -/
public lemma restrictionCompIso_hom (R : ℬ ⥤ 𝒞) (ε : Ig ≅ R) (M : 𝒜) {E : 𝒞}
    (lam : (Iq ⋙ Ig).obj M ≅ E) :
    (restrictionCompIso Iq Ig R ε M lam).hom = ε.inv.app (Iq.obj M) ≫ lam.hom :=
  rfl

/-- **The restriction chase**: transporting along a component of a natural isomorphism
`ε : Ig ≅ R`. -/
public lemma restriction_chase_of_iso (R : ℬ ⥤ 𝒞) (ε : Ig ≅ R) (ρ : Dφ ⋙ R ⟶ R ⋙ DU)
    (β : Dφ ⋙ Ig ⟶ Ig ⋙ DU)
    (hρ : ρ = Functor.whiskerLeft Dφ ε.inv ≫ β ≫ Functor.whiskerRight ε.hom DU)
    (τq : Iq ⟶ Iq ⋙ Dφ) (M : 𝒜) {E : 𝒞} (lam : (Iq ⋙ Ig).obj M ≅ E) (τE : E ⟶ DU.obj E)
    (hl : Ig.map (τq.app M) ≫ β.app (Iq.obj M) ≫ DU.map lam.hom = lam.hom ≫ τE) :
    R.map (τq.app M) ≫ ρ.app (Iq.obj M) ≫ DU.map (restrictionCompIso Iq Ig R ε M lam).hom =
      (restrictionCompIso Iq Ig R ε M lam).hom ≫ τE := by
  subst hρ
  have hn := ε.inv.naturality (τq.app M)
  rw [restrictionCompIso_hom]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    DU.map_comp, Category.assoc]
  rw [← DU.map_comp_assoc, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hn, hl]

end Chase

section Unfold

variable (Λ : Type) [Ring Λ]

variable {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [Etale j] [Mono j]
  (j' : V ⟶ Vb) [Etale j'] [Mono j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb)

omit [Mono j] [Mono j'] in
/-- `Stacks.EtaleCohomology.restrictionIntegralDirectImageIso`, inverse, unfolded: the comparison
of restriction with inverse image around the base change map. -/
public theorem restrictionIntegralDirectImageIso_inv :
    (restrictionIntegralDirectImageIso Λ j j' f fb sq).inv =
      Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ fb)
          (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).inv ≫
        etaleModuleBaseChange Λ fb f j j' sq.w ≫
        Functor.whiskerRight (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j').hom
          (etaleModuleDirectImage.{u, 0} Λ f) := by
  rw [restrictionIntegralDirectImageIso, Iso.trans_inv, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Iso.symm_inv, asIso_hom, Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc]

end Unfold

section ExtensionByZero

variable (Λ : Type) [Ring Λ]

/-- `m^{-1} m_! F ≅ F` for an étale monomorphism `m`, with `m^{-1}` the inverse image: the
comparison of the inverse image with the restriction, and the inverse of the unit of
`m_! ⊣ m^{-1}`. -/
public def inverseImageExtensionByZeroIso {V S : Scheme.{u}} (m : V ⟶ S) [Etale m] [Mono m]
    (F : EtaleModules.{u, 0} Λ V) :
    (etaleModuleInverseImage.{u, 0} Λ m).obj ((etaleModuleExtensionByZero.{u, 0} Λ m).obj F) ≅ F :=
  (etaleModuleInverseImageRestrictionIso.{u, 0} Λ m).app _ ≪≫
    (asIso (etaleModuleExtensionByZeroAdj.{u, 0} Λ m).unit).symm.app F

end ExtensionByZero

section Square

variable (Λ : Type) [Ring Λ] {U Y S V : Scheme.{u}} (g : U ⟶ Y) [Etale g] [Mono g] (q : Y ⟶ S)
  (p : U ⟶ V) (m : V ⟶ S) (h : p ≫ m = g ≫ q) (M : EtaleModules.{u, 0} Λ S)
  {F : EtaleModules.{u, 0} Λ V} (ν : (etaleModuleInverseImage.{u, 0} Λ m).obj M ≅ F)

/-- **`g^{-1} q^{-1} M ≅ p^{-1} F`** for `ν : m^{-1} M ≅ F`, with `g^{-1}` the inverse image:
`g^{-1} q^{-1} ≅ (p ≫ m)^{-1} ≅ p^{-1} m^{-1}` and `p^{-1}(ν)`. -/
public def selfMapTwistOpenInverseImageIso :
    (etaleModuleInverseImage.{u, 0} Λ q ⋙ etaleModuleInverseImage.{u, 0} Λ g).obj M ≅
      (etaleModuleInverseImage.{u, 0} Λ p).obj F :=
  (selfMapRestrictionIso.{u, 0} Λ q g (p ≫ m) h).app _ ≪≫
    ((selfMapRestrictionIso.{u, 0} Λ m p (p ≫ m) rfl).app _).symm ≪≫
    (etaleModuleInverseImage.{u, 0} Λ p).mapIso ν

/-- **`g^{-1} q^{-1} M ≅ p^{-1} F`** for `ν : m^{-1} M ≅ F`, with `g^{-1}` the restriction along
the étale monomorphism `g`: `Stacks.EtaleCohomology.selfMapTwistOpenInverseImageIso` read through
the comparison of restriction with inverse image. -/
public def selfMapTwistOpenRestrictionIso :
    (etaleModuleRestriction.{u, 0} Λ g).obj ((etaleModuleInverseImage.{u, 0} Λ q).obj M) ≅
      (etaleModuleInverseImage.{u, 0} Λ p).obj F :=
  restrictionCompIso (etaleModuleInverseImage.{u, 0} Λ q) (etaleModuleInverseImage.{u, 0} Λ g)
    (etaleModuleRestriction.{u, 0} Λ g) (etaleModuleInverseImageRestrictionIso.{u, 0} Λ g)
    M (selfMapTwistOpenInverseImageIso Λ g q p m h M ν)

variable (φ : Y ⟶ Y) (w : φ ≫ q = q) (φU : U ⟶ U) (wp : φU ≫ p = p)
  (hi : φU ≫ g = g ≫ φ)

omit [Etale g] [Mono g] in
include hi in
/-- **The restriction of the twist is the twist**, inverse image form: `g^{-1}` of the self-map
twist of `q^{-1} M` along `φ`, followed by the base change map `g^{-1} φ_* ⟶ φ_{U,*} g^{-1}`, is,
through `Stacks.EtaleCohomology.selfMapTwistOpenInverseImageIso`, the self-map twist of `p^{-1} F`
along `φ_U`. -/
public theorem selfMapTwistOpenInverseImageIso_selfMapTwist :
    (etaleModuleInverseImage.{u, 0} Λ g).map ((selfMapTwist.{u, 0} Λ q φ w).app M) ≫
      (etaleModuleBaseChange Λ φ φU g g hi).app ((etaleModuleInverseImage.{u, 0} Λ q).obj M) ≫
      (etaleModuleDirectImage.{u, 0} Λ φU).map
        (selfMapTwistOpenInverseImageIso Λ g q p m h M ν).hom =
    (selfMapTwistOpenInverseImageIso Λ g q p m h M ν).hom ≫
      (selfMapTwist.{u, 0} Λ p φU wp).app F := by
  have wU : φU ≫ p ≫ m = p ≫ m := by rw [← Category.assoc, wp]
  have h1 := inverseImage_map_selfMapTwist_comp_baseChange Λ q g (p ≫ m) h φ w φU wU hi M
  have h2 := selfMapTwist_comp_selfMapRestrictionIso Λ φU p m (p ≫ m) rfl wp wU M
  exact twist_chase_of_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2

omit [Mono g] in
include hi in
/-- `Stacks.EtaleCohomology.selfMapTwistOpenRestrictionIso_selfMapTwist` with the comparison
`g^{-1} φ_* ≅ φ_{U,*} g^{-1}` written out through the base change map. -/
public theorem selfMapTwistOpenRestrictionIso_selfMapTwist_baseChange :
    (etaleModuleRestriction.{u, 0} Λ g).map ((selfMapTwist.{u, 0} Λ q φ w).app M) ≫
      (Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ φ)
          (etaleModuleInverseImageRestrictionIso.{u, 0} Λ g).inv ≫
        etaleModuleBaseChange Λ φ φU g g hi ≫
        Functor.whiskerRight (etaleModuleInverseImageRestrictionIso.{u, 0} Λ g).hom
          (etaleModuleDirectImage.{u, 0} Λ φU)).app ((etaleModuleInverseImage.{u, 0} Λ q).obj M) ≫
      (etaleModuleDirectImage.{u, 0} Λ φU).map
        (selfMapTwistOpenRestrictionIso Λ g q p m h M ν).hom =
    (selfMapTwistOpenRestrictionIso Λ g q p m h M ν).hom ≫
      (selfMapTwist.{u, 0} Λ p φU wp).app F :=
  restriction_chase_of_iso _ _ _ _ _ (etaleModuleInverseImageRestrictionIso.{u, 0} Λ g) _ _ rfl
    _ _ _ _ (selfMapTwistOpenInverseImageIso_selfMapTwist Λ g q p m h M ν φ w φU wp hi)

omit [Mono g] in
/-- **The restriction of the twist is the twist**: `g^{-1}` of the self-map twist of `q^{-1} M`
along `φ`, followed by `g^{-1} φ_* ≅ φ_{U,*} g^{-1}`
(`Stacks.EtaleCohomology.restrictionIntegralDirectImageIso` on the cartesian square
`φ_U ≫ g = g ≫ φ`), is, through `Stacks.EtaleCohomology.selfMapTwistOpenRestrictionIso`, the
self-map twist of `p^{-1} F` along `φ_U`. -/
public theorem selfMapTwistOpenRestrictionIso_selfMapTwist [IsIntegralHom φ]
    (sq : IsPullback φU g g φ) :
    (etaleModuleRestriction.{u, 0} Λ g).map ((selfMapTwist.{u, 0} Λ q φ w).app M) ≫
      (restrictionIntegralDirectImageIso Λ g g φU φ sq).inv.app
        ((etaleModuleInverseImage.{u, 0} Λ q).obj M) ≫
      (etaleModuleDirectImage.{u, 0} Λ φU).map
        (selfMapTwistOpenRestrictionIso Λ g q p m h M ν).hom =
    (selfMapTwistOpenRestrictionIso Λ g q p m h M ν).hom ≫
      (selfMapTwist.{u, 0} Λ p φU wp).app F := by
  rw [restrictionIntegralDirectImageIso_inv]
  exact selfMapTwistOpenRestrictionIso_selfMapTwist_baseChange Λ g q p m h M ν φ w φU wp sq.w

end Square

end Stacks.EtaleCohomology

end

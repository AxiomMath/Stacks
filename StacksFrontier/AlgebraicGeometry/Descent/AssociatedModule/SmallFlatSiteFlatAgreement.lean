module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSiteFlatAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteRingedSite
import StacksCore.Tactic.StacksAttribute

/-! # Descent, Lemma 05VG for flatness on the small smooth, syntomic and fppf sites

Let `S` be a scheme of a big fppf site and `τ ∈ {smooth, syntomic, fppf}`, and let `S_τ` be the
small `τ`-site of `S` (`AlgebraicGeometry.SmallFlatSite`), which extends the source's small sites
to these three topologies.  This file proves the clause of Descent, Lemma 05VG for Modules on
Sites, Definition 03ER (3), flatness, on `S_τ`:

    `𝓗` flat on `S_Zar`  ↔  `𝓗ᵃ` flat on `S_τ`,  for a quasi-coherent `𝒪_S`-module `𝓗`.

Both halves run through the criterion of Stacks 08FC: a sheaf of modules is flat exactly when
every relation among finitely many of its sections admits, locally, a finite free factorization.

* **The forward half.**  `𝓗ᵃ` on `S_τ` is the restriction of `𝓗ᵃ` on the big site `(Sch/S)_τ`
  (`AlgebraicGeometry.SmallFlatSite.associatedModuleIsoRestriction`), which is flat by the
  big-site clause.  A relation among sections over an object `U` of `S_τ` is a relation over `U`
  on the big site; it factors on a covering sieve of the big site, and the sieve it pulls back to
  covers `U` in `S_τ`, the inclusion being cocontinuous.  So restriction to `S_τ` keeps the
  factorizations of 08FC.
* **The converse half** is the local equational criterion, as on the big site: a relation among
  germs of `𝓗` at `x` is the germ of a relation among sections over an open `U ∋ x`; read at the
  object `U → S` of `S_τ`, flatness of `𝓗ᵃ` factors it on a covering sieve of `S_τ`, a member
  `T → U` of which passes through `x`; `T → S` is flat, because it is smooth, syntomic,
  respectively flat by definition of `S_τ`; and vanishing trivially descends along the faithfully
  flat stalk map at a point of `T` over `x`.  This last step is
  `AlgebraicGeometry.isFlat_of_forall_relation`, which isolates the descent from the site.

## Main results

* `AlgebraicGeometry.isFlat_of_forall_relation`: an `𝒪_S`-module is flat as soon as every relation
  among its sections over an open `U ∋ x` factors through a finite free module after pullback to a
  flat `T → S` reaching `x` and landing in `U`.
* `AlgebraicGeometry.SmallFlatSite.isFlat_associatedModule_iff`: **Descent, Lemma 05VG for 03ER
  (3), on the small `τ`-site, for every `τ ∈ {smooth, syntomic, fppf}`.**

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The germ of a finite sum `∑ bₖ • tₖ` of sections of a presheaf of modules is the sum of the
products of the germs. -/
private theorem germ_sum_smul {X : Scheme.{u}}
    (M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : X)
    (U : X.Opens) (hx : x ∈ U) {k : ℕ} (b : Fin k → ToType (X.presheaf.obj (op U)))
    (t : Fin k → ToType (M.obj (op U))) :
    TopCat.Presheaf.germ M.presheaf U x hx (∑ κ, b κ • t κ)
      = ∑ κ, X.presheaf.germ U x hx (b κ) • TopCat.Presheaf.germ M.presheaf U x hx (t κ) :=
  (map_sum (TopCat.Presheaf.germ M.presheaf U x hx).hom (fun κ ↦ b κ • t κ) Finset.univ).trans
    (Finset.sum_congr rfl fun κ _ ↦ PresheafOfModules.germ_smul M x U hx (b κ) (t κ))

/-- **Flatness from local factorizations of relations on flat covers.**  Let `𝓗` be an
`𝒪_S`-module such that, for every point `x`, every open `U ∋ x` and every relation
`∑ᵢ aᵢ • sᵢ = 0` among sections of `𝓗` over `U`, there are a flat morphism `g : T → S` landing in
`U`, a point `y` of `T` over `x`, and a factorization of the pulled-back sections through a finite
free module by a matrix annihilating the pulled-back relation.  Then `𝓗` is flat.

By Stacks 05NE flatness of `𝓗` is flatness of its stalks, and by the equational criterion that is
the triviality of every relation among germs.  A relation among germs at `x` is the germ of a
relation among sections over an open `U ∋ x`; the stalk of `g^*𝓗` at `y` is the base change of
the stalk of `𝓗` at `x` along the faithfully flat local homomorphism `𝒪_{S,x} → 𝒪_{T,y}`
(Stacks 0098), where the factorization makes the relation vanish trivially; and vanishing
trivially descends along a faithfully flat base change. -/
theorem isFlat_of_forall_relation {S : Scheme.{u}} (𝓗 : S.Modules)
    (H : ∀ (x : ↥S) (U : S.Opens) (_ : x ∈ U) (l : ℕ) (a : Fin l → Γ(S, U))
      (s : Fin l → Γ(𝓗, U)), ∑ i, a i • s i = 0 →
      ∃ (T : Scheme.{u}) (g : T ⟶ S) (_ : Flat g) (y : ↥T) (_ : g.base y = x)
        (hgle : (⊤ : T.Opens) ≤ g ⁻¹ᵁ U) (k : ℕ)
        (t : Fin k → Γ((Scheme.Modules.pullback g).obj 𝓗, ⊤)) (Bm : Fin k → Fin l → Γ(T, ⊤)),
        (∀ i, pullbackSectionHom g 𝓗 U ⊤ hgle (s i) = ∑ κ, Bm κ i • t κ) ∧
        (∀ κ, ∑ i, Bm κ i * Scheme.Hom.appLE g U ⊤ hgle (a i) = 0)) :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓗 := by
  classical
  suffices key : ∀ (x : ↥S) {l : ℕ} (φ : Fin l → ToType (S.presheaf.stalk x))
      (σ : Fin l → ToType (TopCat.Presheaf.stalk 𝓗.val.presheaf x)), ∑ i, φ i • σ i = 0 →
      TensorProduct.VanishesTrivially (ToType (S.presheaf.stalk x)) φ σ by
    have hflat : ∀ x : ↥S, Module.Flat (ToType (S.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk 𝓗.val.presheaf x)) := fun x ↦
      Module.Flat.of_forall_isTrivialRelation fun {_} {φ} {σ} hrel ↦
        Module.isTrivialRelation_iff_vanishesTrivially.2 (key x φ σ hrel)
    exact (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat S.sheaf 𝓗).2 hflat
  intro x l φ σ hrel
  -- a relation among germs is the germ of a relation among sections over an open
  let M : PresheafOfModules.{u} (S.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := 𝓗.val
  choose V hV s₀ hs₀ using fun i : Fin l ↦ TopCat.Presheaf.exists_germ_eq M.presheaf (σ i)
  choose W hW a₀ ha₀ using fun i : Fin l ↦ TopCat.Presheaf.exists_germ_eq S.presheaf (φ i)
  obtain ⟨U₀, hxU₀, hle⟩ := Stacks.SheafOfModules.exists_nbhd_le x
    (fun j : Fin l ⊕ Fin l ↦ j.elim V W)
    (by rintro (i | i) <;> [exact hV i; exact hW i])
  set a₁ : Fin l → ToType (S.presheaf.obj (op U₀)) := fun i ↦
    S.presheaf.map (homOfLE (hle (Sum.inr i))).op (a₀ i) with ha₁
  set s₁ : Fin l → ToType (M.obj (op U₀)) := fun i ↦
    M.restrictₛₗ (homOfLE (hle (Sum.inl i))).op (s₀ i) with hs₁
  have hga : ∀ i, S.presheaf.germ U₀ x hxU₀ (a₁ i) = φ i := fun i ↦
    (TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE (hle (Sum.inr i))) x hxU₀
      (a₀ i)).trans (ha₀ i)
  have hgs : ∀ i, TopCat.Presheaf.germ M.presheaf U₀ x hxU₀ (s₁ i) = σ i := fun i ↦
    (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (hle (Sum.inl i))) x hxU₀
      (s₀ i)).trans (hs₀ i)
  have hz : TopCat.Presheaf.germ M.presheaf U₀ x hxU₀ (∑ i, a₁ i • s₁ i) = 0 :=
    (germ_sum_smul M x U₀ hxU₀ a₁ s₁).trans
      ((Finset.sum_congr rfl fun i _ ↦ by rw [hga i, hgs i]; rfl).trans hrel)
  obtain ⟨U, hxU, i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq M.presheaf x hxU₀ hxU₀
    (∑ i, a₁ i • s₁ i) 0
    (hz.trans (map_zero (TopCat.Presheaf.germ M.presheaf U₀ x hxU₀).hom).symm)
  let a : Fin l → Γ(S, U) := fun i ↦ S.presheaf.map i₁.op (a₁ i)
  let s : Fin l → Γ(𝓗, U) := fun i ↦ M.restrictₛₗ i₁.op (s₁ i)
  have hga' : ∀ i, S.presheaf.germ U x hxU (a i) = φ i := fun i ↦
    (TopCat.Presheaf.germ_res_apply S.presheaf i₁ x hxU (a₁ i)).trans (hga i)
  have hgs' : ∀ i, TopCat.Presheaf.germ 𝓗.val.presheaf U x hxU (s i) = σ i := fun i ↦
    (TopCat.Presheaf.germ_res_apply M.presheaf i₁ x hxU (s₁ i)).trans (hgs i)
  have hrelU : ∑ i, a i • s i = 0 := by
    refine Eq.trans (Eq.symm (Eq.trans (map_sum (M.restrictₛₗ i₁.op)
      (fun i ↦ a₁ i • s₁ i) Finset.univ)
      (Finset.sum_congr rfl fun i _ ↦ (M.restrictₛₗ i₁.op).map_smulₛₗ (a₁ i) (s₁ i)))) ?_
    exact he.trans (map_zero (M.presheaf.map i₂.op).hom)
  -- the factorization on a flat cover, and its descent at a point over `x`
  obtain ⟨T, g, hg, y, rfl, hgle, k, t, Bm, h1, h2⟩ := H x U hxU l a s hrelU
  let : Algebra (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) :=
    (g.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap y).hom)
  have : Module.Flat (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) := Flat.stalkMap g y
  have : Module.FaithfullyFlat (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨e₀, he₀⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    g.toLRSHom.toShHom 𝓗 y
  let e : ToType (TopCat.Presheaf.stalk ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf y)
      ≃ₗ[T.presheaf.stalk y]
      TensorProduct (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y)
        (ToType (TopCat.Presheaf.stalk 𝓗.val.presheaf (g.base y))) := e₀
  have he' : ∀ (V : S.Opens) (hv : g.base y ∈ V) (hvle : (⊤ : T.Opens) ≤ g ⁻¹ᵁ V)
      (tt : Γ(𝓗, V)),
      e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf ⊤ y trivial
          (pullbackSectionHom g 𝓗 V ⊤ hvle tt))
        = (1 : T.presheaf.stalk y) ⊗ₜ
            TopCat.Presheaf.germ 𝓗.val.presheaf V (g.base y) hv tt := fun V hv hvle tt ↦
    (congrArg e (TopCat.Presheaf.germ_res_apply _ (homOfLE hvle) y trivial _)).trans
      (he₀ V hv tt)
  refine Stacks.FlatDescent.vanishesTrivially_of_baseChange (B := T.presheaf.stalk y) ?_
  refine TensorProduct.VanishesTrivially.of_fintype
    (fun i κ ↦ T.presheaf.germ ⊤ y trivial (Bm κ i))
    (fun κ ↦ e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf
      ⊤ y trivial (t κ))) ?_ ?_
  · intro i
    calc (1 : T.presheaf.stalk y) ⊗ₜ σ i
        = e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf ⊤ y trivial
            (pullbackSectionHom g 𝓗 U ⊤ hgle (s i))) := by
          rw [← hgs' i, he' U hxU hgle (s i)]
      _ = e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf ⊤ y trivial
            (∑ κ, Bm κ i • t κ)) :=
          congrArg (fun z ↦ e (TopCat.Presheaf.germ
            ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf ⊤ y trivial z)) (h1 i)
      _ = ∑ κ, T.presheaf.germ ⊤ y trivial (Bm κ i) •
            e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf
              ⊤ y trivial (t κ)) := by
          refine (congrArg e (germ_sum_smul (((Scheme.Modules.pullback g).obj 𝓗).val :
            PresheafOfModules.{u} (T.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
              y ⊤ trivial (fun κ ↦ Bm κ i) t)).trans ((map_sum e _ _).trans ?_)
          exact Finset.sum_congr rfl fun κ _ ↦ e.map_smul _ _
  · intro κ
    have hgr : ∀ i, T.presheaf.germ ⊤ y trivial (Scheme.Hom.appLE g U ⊤ hgle (a i))
        = algebraMap (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) (φ i) := fun i ↦ by
      rw [RingHom.algebraMap_toAlgebra, ← hga' i]
      exact (TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hgle) y trivial _).trans
        (Scheme.Hom.germ_stalkMap_apply g U y hxU (a i)).symm
    calc ∑ i, T.presheaf.germ ⊤ y trivial (Bm κ i) •
            algebraMap (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) (φ i)
        = T.presheaf.germ ⊤ y trivial (∑ i, Bm κ i * Scheme.Hom.appLE g U ⊤ hgle (a i)) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, hgr i, smul_eq_mul]
      _ = 0 := by rw [h2 κ, map_zero]

/-- **Global functions through a morphism into an open.**  If `g : T ⟶ S` factors as `h` followed
by the inclusion of an open `U`, the image under `g` of a function on `U` is the image under `h` of
its restriction to the open subscheme `U`. -/
theorem appLE_comp_ι_eq {S T : Scheme.{u}} {U : S.Opens} (h : T ⟶ U.toScheme)
    (hle : (⊤ : T.Opens) ≤ (h ≫ U.ι) ⁻¹ᵁ U) (hU : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U)
    (r : Γ(S, U)) :
    Scheme.Hom.appLE (h ≫ U.ι) U ⊤ hle r = h.app ⊤ (Scheme.Hom.appLE U.ι U ⊤ hU r) := by
  have hb : Scheme.Hom.appLE h (⊤ : U.toScheme.Opens) (⊤ : T.Opens) le_rfl = h.app ⊤ :=
    Scheme.Hom.appLE_preimage_self h ⊤
  rw [← hb]
  exact (congrArg (fun k : Γ(S, U) ⟶ Γ(T, ⊤) ↦ ConcreteCategory.hom k r)
    (Scheme.Hom.appLE_comp_appLE h U.ι U ⊤ ⊤ hU le_rfl)).symm

namespace SmallFlatSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-- Presheaves of types in the universe of the sections sheafify on the small `τ`-site, which is
essentially small. -/
theorem hasSheafify_type : HasSheafify (topology B S hS κ) (Type u) :=
  hasSheafifyEssentiallySmallSite.{u} _ _

attribute [local instance] BigFppfOver.hasSheafify_type_baseOver hasSheafify_type

/-- **Restriction to the small `τ`-site keeps the local factorizations of Stacks 08FC.**  A
relation among sections over an object `U` of the small site is one over `U` on the big site; it
factors on a covering sieve of the big site, and the sieve this pulls back to covers `U` in the
small site, the inclusion being cocontinuous. -/
theorem hasLocalSingleRelationFactorizations_restriction
    (𝓜 : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind))
    (h : Stacks.SheafOfModules.HasLocalSingleRelationFactorizations.{u, u, u + 1}
      (BigFppfOver.baseRingedSite B S hS κ.toSiteKind).O 𝓜) :
    Stacks.SheafOfModules.HasLocalSingleRelationFactorizations.{u, u, u + 1} (ringedSite B S hS κ).O
      ((restriction B S hS κ).obj 𝓜) := by
  intro U n a s hrel
  obtain ⟨T, hT, hfac⟩ := h ((inclusion B S hS κ).obj U) n a s hrel
  exact ⟨T.functorPullback (inclusion B S hS κ),
    (inclusion B S hS κ).cover_lift (topology B S hS κ)
      (BigFppfOver.baseOverTopology B S hS κ.toSiteKind) hT,
    fun {_} f hf ↦ hfac ((inclusion B S hS κ).map f) hf⟩

variable (𝓗 : S.Modules) [𝓗.IsQuasicoherent]

/-- The associated module of the small `τ`-site is the restriction of the pullback-sections sheaf
of the big `τ`-site. -/
noncomputable def associatedModuleIsoRestrictionSectionsSheaf :
    (associatedModule B S hS κ).obj 𝓗 ≅
      (restriction B S hS κ).obj (BigFppfOver.sectionsSheafOfModules B S hS κ.toSiteKind 𝓗) :=
  (associatedModuleIsoRestriction B S hS κ).app 𝓗 ≪≫
    (restriction B S hS κ).mapIso
      (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B S hS κ.toSiteKind 𝓗)

/-- **The forward half of Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), on the
small `τ`-site.**  If `𝓗` is flat, so is `𝓗ᵃ` on `S_τ`: it is flat on the big site, and
restriction to the small site keeps the criterion of Stacks 08FC. -/
theorem isFlat_associatedModule_of_isFlat
    (h𝓗 : Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓗) :
    Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (ringedSite B S hS κ).O)
      ((associatedModule B S hS κ).obj 𝓗) := by
  have hbig := (BigFppfOver.isFlat_baseAssociatedModule_iff B S hS κ.toSiteKind 𝓗).1 h𝓗
  have hbig' : Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (BigFppfOver.baseRingedSite B S hS κ.toSiteKind).O)
      (BigFppfOver.sectionsSheafOfModules B S hS κ.toSiteKind 𝓗) :=
    Stacks.ModuleUp.isFlat_of_iso_anySite
      (O := (BigFppfOver.baseRingedSite B S hS κ.toSiteKind).O)
      (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B S hS κ.toSiteKind 𝓗) hbig
  refine Stacks.ModuleUp.isFlat_of_iso_anySite (O := (ringedSite B S hS κ).O)
    (associatedModuleIsoRestrictionSectionsSheaf B S hS κ 𝓗).symm ?_
  refine (Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse
    (ringedSite B S hS κ).O _).2 ?_
  exact hasLocalSingleRelationFactorizations_restriction B S hS κ _
    ((Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse
      (BigFppfOver.baseRingedSite B S hS κ.toSiteKind).O _).1 hbig')

/-- **The converse half of Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), on the
small `τ`-site.**  If `𝓗ᵃ` is flat on `S_τ`, then the quasi-coherent `𝒪_S`-module `𝓗` is flat.

A relation among sections of `𝓗` over an open `U ∋ x` is read at the object `U → S` of `S_τ`,
where the sections of `𝓗ᵃ` are those of the pullback of `𝓗`; Stacks 08FC factors it on a covering
sieve of `S_τ`; that sieve generates a covering sieve of the big site, an arrow of which passes
through `x` (`AlgebraicGeometry.BigFppfOver.exists_mem_of_mem_topology`) and factors through a
member `W → U` of the given sieve; and `W → S` is flat by the definition of `S_τ`.
`AlgebraicGeometry.isFlat_of_forall_relation` then descends the factorization. -/
theorem isFlat_of_isFlat_associatedModule
    (hflat : Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (ringedSite B S hS κ).O)
      ((associatedModule B S hS κ).obj 𝓗)) :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓗 := by
  classical
  have hflat' : Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (ringedSite B S hS κ).O)
      ((restriction B S hS κ).obj (BigFppfOver.sectionsSheafOfModules B S hS κ.toSiteKind 𝓗)) :=
    Stacks.ModuleUp.isFlat_of_iso_anySite (O := (ringedSite B S hS κ).O)
      (associatedModuleIsoRestrictionSectionsSheaf B S hS κ 𝓗) hflat
  have H := (Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse
    (ringedSite B S hS κ).O _).1 hflat'
  refine isFlat_of_forall_relation 𝓗 fun x U hxU l a s hrelU ↦ ?_
  have hUle : (⊤ : (Scheme.Opens.toScheme U).Opens) ≤ Scheme.Opens.ι U ⁻¹ᵁ U :=
    Scheme.Opens.top_le_ι_preimage (le_refl U)
  have hrel' : ∑ i, (Scheme.Hom.appLE (Scheme.Opens.ι U) U ⊤ hUle (a i) :
        ToType (Γ(Scheme.Opens.toScheme U, ⊤))) •
      (pullbackSectionHom (Scheme.Opens.ι U) 𝓗 U ⊤ hUle (s i) :
        ToType (Γ((Scheme.Modules.pullback (Scheme.Opens.ι U)).obj 𝓗, ⊤))) = 0 := by
    refine Eq.trans (Eq.symm (Eq.trans
      (map_sum (pullbackSectionHom (Scheme.Opens.ι U) 𝓗 U ⊤ hUle).hom
        (fun i ↦ a i • s i) Finset.univ)
      (Finset.sum_congr rfl fun i _ ↦
        pullbackSectionHom_smul (Scheme.Opens.ι U) 𝓗 U ⊤ hUle (a i) (s i)))) ?_
    rw [hrelU]
    exact map_zero (pullbackSectionHom (Scheme.Opens.ι U) 𝓗 U ⊤ hUle).hom
  obtain ⟨Rv, hRv, hfac⟩ := H ((opensToSmall B S hS κ).obj U) l
    (fun i ↦ Scheme.Hom.appLE (Scheme.Opens.ι U) U ⊤ hUle (a i))
    (fun i ↦ pullbackSectionHom (Scheme.Opens.ι U) 𝓗 U ⊤ hUle (s i)) hrel'
  obtain ⟨c, q', hq', -, -, y, hy⟩ := BigFppfOver.exists_mem_of_mem_topology B S hS
    (BigFppfOver.baseOverTopology_le_fppf B S hS κ.toSiteKind _
      ((mem_topology_iff B S hS κ _).1 hRv)) (⟨x, hxU⟩ : ↥(Scheme.Opens.toScheme U))
  obtain ⟨W, q, h, hq, rfl⟩ := hq'
  obtain ⟨k, t, Bm, hfac1, hfac2⟩ := hfac q hq
  have hcq : W.obj.hom.hom =
      (BigFppfOver.toScheme B S hS).map ((inclusion B S hS κ).map q) ≫ Scheme.Opens.ι U :=
    BigFppfOver.hom_hom_eq B S hS ((inclusion B S hS κ).map q)
  have hgle : (⊤ : ((BigFppfOver.toScheme B S hS).obj W.obj).Opens) ≤ W.obj.hom.hom ⁻¹ᵁ U := by
    rw [hcq]
    exact fun z _ ↦ hUle trivial
  refine ⟨_, W.obj.hom.hom, κ.flat_of_morphismProperty W.property,
    ((BigFppfOver.toScheme B S hS).map h).base y, ?_, hgle, k, t, Bm, fun i ↦ ?_, fun κ' ↦ ?_⟩
  · rw [hcq]
    exact congrArg (fun z ↦ (Scheme.Opens.ι U).base z) hy
  · exact (pullbackSectionsMap_pullbackSectionHom 𝓗
      ((Over.post (X := B.obj hS) B.inclusion).map ((inclusion B S hS κ).map q)) U hUle hgle
      (s i)).symm.trans (hfac1 i)
  · refine Eq.trans ?_ (hfac2 κ' 0)
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine congrArg _ ?_
    revert hgle
    rw [hcq]
    intro hgle
    exact appLE_comp_ι_eq ((BigFppfOver.toScheme B S hS).map ((inclusion B S hS κ).map q)) hgle
      hUle (a i)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module `𝓗` is flat if and only if
`𝓗ᵃ` is flat as an `𝒪`-module on `S_τ`.

The `only if` half is `AlgebraicGeometry.SmallFlatSite.isFlat_associatedModule_of_isFlat`, the
`if` half `AlgebraicGeometry.SmallFlatSite.isFlat_of_isFlat_associatedModule`. -/
@[stacks 05VG "flat (03ER (3)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ {smooth, syntomic, fppf} \
(the small sites extending the source's)"]
theorem isFlat_associatedModule_iff :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓗 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (ringedSite B S hS κ).O)
        ((associatedModule B S hS κ).obj 𝓗) :=
  ⟨isFlat_associatedModule_of_isFlat B S hS κ 𝓗, isFlat_of_isFlat_associatedModule B S hS κ 𝓗⟩

end SmallFlatSite

end AlgebraicGeometry

end

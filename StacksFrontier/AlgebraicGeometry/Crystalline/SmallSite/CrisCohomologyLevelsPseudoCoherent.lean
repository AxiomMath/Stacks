module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelBase
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeNilpotentSmooth
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelCohomologyPseudoCoherent
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent

/-!
# The finite levels of `RΓ(CRIS(X/S), N)`: the derived inverse limit of [Stacks, Tag 07MV]

Let `X/S` be a global crystalline situation with affine base, `A = Γ(S, ⊤)` `p`-adically complete,
and `N₀` a finite divided power level (`(p^{N₀}) ⊆ I` preserved by `γ`).  The exponents
`N₀, 2N₀, 3N₀, …` are again levels (`Crystalline.IsPAdicLevel.mul`), and the rings
`Γ(S_{N₀(n+1)}, ⊤) ≅ A ⧸ p^{N₀(n+1)}A` (`levelSectionsEquiv`) form an inverse system with
surjective transitions of square-zero kernel whose limit is `A`
(`isLimitLevelRingCone`, from `IsAdicComplete.StrictMono.liftRingHom`).

On this tower the derived-limit theorem [Stacks, Tag 0CQF]
(`StacksDraft.DerivedInverseLimit.derivedLimit_isPseudoCoherent_and_baseChange_iso`) is applied
to `K = RΓ(CRIS(X/S), N)` and the terms `K_n = RΓ(CRIS(X/S_{N₀(n+1)}), N_{N₀(n+1)})`, with the
transitions the change-of-base comparisons of the chapter.  Given the Milnor triangle of `K` over
the levels, the base change isomorphisms of the tower and the pseudo-coherence of `K_0`, it yields
(`SmallSite.levels_isPseudoCoherent_and_isIso`) that `K` is pseudo-coherent and that the
transposes `K ⊗^L_A Γ(S_{N₀(n+1)}, ⊤) ⟶ K_n` of the change-of-base comparisons are isomorphisms;
the case `n = 0` is the level `N₀` itself.

The derived-limit theorem is proved in the standard models of the derived categories of modules,
and this file is stated in them.

## Main results

* `Crystalline.IsPAdicLevel.mul` — multiples of a level are levels.
* `GlobalCrystallineSituation.isLimitLevelRingCone` — `A = lim Γ(S_{N₀(n+1)}, ⊤)`.
* `GlobalCrystallineSituation.SmallSite.levels_isPseudoCoherent_and_isIso` — **the assembly.**
* `StacksDraft.DerivedInverseLimit.ι_map_app_eq_derivedRestrictScalarsComp_hom_app` — a
  transformation of restrictions of scalars on `D⁺` induced by `restrictScalarsComp'` is
  `derivedRestrictScalarsComp` on `D`.

## References

* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 0CQF](https://stacks.math.columbia.edu/tag/0CQF)
* [Stacks Project, Tag 09AV](https://stacks.math.columbia.edu/tag/09AV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u v

namespace CategoryTheory.Functor

/-- For an exact functor `E`, the inverse of `Qh ∘ E ≅ E ∘ Qh` at `K` followed by `E` of
`Qh(K) ≅ Q(K)` is `Qh(E K) ≅ Q(E K)` followed by the inverse of `Q ∘ E ≅ E ∘ Q`. -/
theorem mapDerivedCategoryFactorsh_inv_app_comp_map_quotientCompQhIso_hom
    {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    {ℬ : Type*} [Category* ℬ] [Abelian ℬ] [HasDerivedCategory ℬ]
    (E : 𝒜 ⥤ ℬ) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (K : CochainComplex 𝒜 ℤ) :
    E.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K) ≫
        E.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜).hom.app K) =
      (DerivedCategory.quotientCompQhIso ℬ).hom.app _ ≫ E.mapDerivedCategoryFactors.inv.app K := by
  have h1 := E.quotientCompQhIso_inv_app_comp_Qh_map_comp_mapDerivedCategory_map
    (𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  have e1 : DerivedCategory.Qh.map ((HomotopyCategory.quotient ℬ (ComplexShape.up ℤ)).map
      (𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) = 𝟙 _ :=
    (congrArg DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map_id _)).trans
      (DerivedCategory.Qh.map_id _)
  have e2 : DerivedCategory.Q.map (𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      𝟙 _ := DerivedCategory.Q.map_id _
  refine (Iso.inv_comp_eq ((DerivedCategory.quotientCompQhIso ℬ).app _)).1
    (Eq.trans ?_ (h1.trans ((congrArg (· ≫ _) e2).trans (Category.id_comp _))))
  exact congrArg (_ ≫ ·) ((congrArg (· ≫ _) e1).trans (Category.id_comp _)).symm

end CategoryTheory.Functor

namespace StacksDraft.DerivedInverseLimit

section RestrictComposition

attribute [local instance 1100] HasDerivedCategory.standard

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T) (h : R →+* T) (w : h = g.comp f)

/-- **The derived comparison of restrictions of scalars along a composite is determined by its
values on complexes.** For ring maps `f : R ⟶ S`, `g : S ⟶ T` and `h = g ∘ f`, any transformation
`ρ : res_f ∘ res_g ⟶ res_h` of the induced functors on `D⁺` which is induced by
`ModuleCat.restrictScalarsComp'` on bounded below complexes (the compatibility `hρ`) is, read in
the unbounded derived category, the comparison `derivedRestrictScalarsComp` of [Stacks, Tag 0CQF].
-/
theorem ι_map_app_eq_derivedRestrictScalarsComp_hom_app
    (ρ : (ModuleCat.restrictScalars.{max u v} g).mapDerivedCategoryPlus ⋙
        (ModuleCat.restrictScalars.{max u v} f).mapDerivedCategoryPlus ⟶
      (ModuleCat.restrictScalars.{max u v} h).mapDerivedCategoryPlus)
    (hρ : ∀ L : HomotopyCategory.Plus (ModuleCat.{max u v} T),
      (ModuleCat.restrictScalars.{max u v} f).mapDerivedCategoryPlusFactorsh.inv.app
          ((ModuleCat.restrictScalars.{max u v} g).mapHomotopyCategoryPlus.obj L) ≫
        (ModuleCat.restrictScalars.{max u v} f).mapDerivedCategoryPlus.map
          ((ModuleCat.restrictScalars.{max u v} g).mapDerivedCategoryPlusFactorsh.inv.app L) ≫
          ρ.app (DerivedCategory.Plus.Qh.obj L) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans
          (ModuleCat.restrictScalarsComp'.{max u v} f g h w).inv).app L) ≫
        (ModuleCat.restrictScalars.{max u v} h).mapDerivedCategoryPlusFactorsh.inv.app L)
    (Y : DerivedCategory.Plus (ModuleCat.{max u v} T)) :
    DerivedCategory.Plus.ι.map (ρ.app Y) =
      (derivedRestrictScalarsComp.{u, v} f g h w).hom.app (DerivedCategory.Plus.ι.obj Y) := by
  let Fg := ModuleCat.restrictScalars.{max u v} g
  let Ff := ModuleCat.restrictScalars.{max u v} f
  let Fh := ModuleCat.restrictScalars.{max u v} h
  suffices H : (Functor.whiskerRight ρ DerivedCategory.Plus.ι :
        (Fg.mapDerivedCategoryPlus ⋙ Ff.mapDerivedCategoryPlus) ⋙ DerivedCategory.Plus.ι ⟶
          Fh.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι) =
      (Functor.whiskerLeft DerivedCategory.Plus.ι (derivedRestrictScalarsComp.{u, v} f g h w).hom :
        (Fg.mapDerivedCategoryPlus ⋙ Ff.mapDerivedCategoryPlus) ⋙ DerivedCategory.Plus.ι ⟶
          Fh.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι) from
    NatTrans.congr_app H Y
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{max u v} T)) (fun L ↦ ?_)
  obtain ⟨L, hL⟩ := L
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  have e1 := congrArg DerivedCategory.Plus.ι.map (hρ ⟨(HomotopyCategory.quotient _ _).obj K, hL⟩)
  simp only [Functor.map_comp] at e1
  change DerivedCategory.Plus.ι.map (ρ.app (DerivedCategory.Plus.Qh.obj ⟨_, hL⟩)) =
    (derivedRestrictScalarsComp.{u, v} f g h w).hom.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))
  let c := (NatTrans.mapHomologicalComplex (ModuleCat.restrictScalarsComp'.{max u v} f g h w).inv
    (ComplexShape.up ℤ)).app K
  have e1' : Ff.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ _).obj
          ((Fg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      Ff.mapDerivedCategory.map
        (Fg.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K)) ≫
        DerivedCategory.Plus.ι.map (ρ.app (DerivedCategory.Plus.Qh.obj ⟨_, hL⟩)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map c) ≫
        Fh.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K) :=
    e1.trans (DerivedCategory.Plus.ι.map_comp _ _)
  have hn := (derivedRestrictScalarsComp.{u, v} f g h w).hom.naturality
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} T)).hom.app K)
  have hFg := Fg.mapDerivedCategoryFactorsh_inv_app_comp_map_quotientCompQhIso_hom K
  have hFf := Ff.mapDerivedCategoryFactorsh_inv_app_comp_map_quotientCompQhIso_hom
    ((Fg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have hD := derivedRestrictScalarsComp_factors.{u, v} f g h w K
  have hU := Fh.quotientCompQhIso_inv_app_comp_Qh_map_comp_mapDerivedCategory_map c
  have e2 : Ff.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ _).obj
          ((Fg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      Ff.mapDerivedCategory.map
        (Fg.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K)) ≫
        (derivedRestrictScalarsComp.{u, v} f g h w).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map c) ≫
        Fh.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K) := by
    refine (Iso.cancel_iso_inv_left ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).app
      ((Ff.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Fg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) _ _).1
      ((cancel_mono (Fh.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} T)).hom.app K))).1 ?_)
    refine Eq.trans ?_ (((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans hU).symm
    have hB := (Ff.mapDerivedCategory.map_comp _ _).symm.trans
      ((congrArg Ff.mapDerivedCategory.map hFg).trans (Ff.mapDerivedCategory.map_comp _ _))
    refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _))))).trans ?_
    refine (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) hn.symm).trans
      ((reassoc_of% hB) _))).trans ((reassoc_of% hFf) _))).trans ?_
    rw [Iso.app_inv, Iso.inv_hom_id_app_assoc]
    exact hD
  exact (Iso.cancel_iso_inv_left (Ff.mapDerivedCategory.mapIso
      (Fg.mapDerivedCategoryFactorsh.app _)) _ _).1
    ((Iso.cancel_iso_inv_left (Ff.mapDerivedCategoryFactorsh.app _) _ _).1 (e1'.trans e2.symm))

end RestrictComposition

end StacksDraft.DerivedInverseLimit

namespace Crystalline

namespace IsPAdicLevel

variable {A : Type u} [CommRing A] {I : Ideal A} {γ : DividedPowers I} {p e : ℕ}

/-- The powers of `(p)` are principal. -/
theorem pAdicIdeal_pow_eq (m : ℕ) :
    DividedPowers.pAdicIdeal (A := A) p ^ m = Ideal.span {((p : ℕ) : A) ^ m} := by
  rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow]

/-- A multiple of a finite divided power level is a finite divided power level. -/
theorem mul (he : IsPAdicLevel I γ p e) (k : ℕ) : IsPAdicLevel I γ p (e * (k + 1)) := by
  have hmem : ((p : ℕ) : A) ^ e ∈ DividedPowers.pAdicIdeal p ^ e := by
    rw [pAdicIdeal_pow_eq]; exact Ideal.subset_span rfl
  have hpe : ((p : ℕ) : A) ^ e ∈ I := he.1 hmem
  have hfac : ((p : ℕ) : A) ^ (e * (k + 1)) = ((p : ℕ) : A) ^ (e * k) * ((p : ℕ) : A) ^ e := by
    ring
  refine ⟨(Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right e (Nat.succ_pos k))).trans he.1, ?_⟩
  rw [pAdicIdeal_pow_eq]
  refine (DividedPowers.span_isSubDPIdeal_iff ?_).mpr ?_
  · rintro _ rfl
    rw [hfac]
    exact I.mul_mem_left _ hpe
  · rintro n hn _ rfl
    rw [hfac, γ.dpow_mul hpe]
    have h2 : γ.dpow n (((p : ℕ) : A) ^ e) ∈ Ideal.span {((p : ℕ) : A) ^ e} := by
      have := he.2.dpow_mem n hn hmem
      rwa [pAdicIdeal_pow_eq] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h2
    rw [Ideal.mem_span_singleton, hc]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨(((p : ℕ) : A) ^ (e * k)) ^ m * c, by ring⟩

end IsPAdicLevel

namespace GlobalCrystallineSituation

open DividedPowerScheme SmallSite

/-- `Spec` of a ring map, read on global sections through `Γ(Spec R, ⊤) ≅ R`. -/
theorem ΓSpecIso_hom_specMap_appTop {R T : CommRingCat.{u}} (f : R ⟶ T) (x : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso T).hom.hom ((Spec.map f).appTop.hom x) =
      f.hom ((Scheme.ΓSpecIso R).hom.hom x) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality f) x

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme]

/-- The ring `A ⧸ p^e A` of a finite level. -/
abbrev levelQuotient (e : ℕ) : Type u :=
  Γ(S.S.scheme, ⊤) ⧸ DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p ^ e

/-- **The global sections of `S_e` are `A ⧸ p^e A`.** -/
def levelSectionsEquiv {e : ℕ} (he : S.IsLevel e) :
    Γ((S.levelSituation he).S.scheme, ⊤) ≃+* S.levelQuotient e :=
  (Scheme.ΓSpecIso (CommRingCat.of (pAdicLevelRing S.baseIdeal S.baseDividedPowers S.p he)))
    |>.commRingCatIsoToRingEquiv

/-- Through `Γ(S_e, ⊤) ≅ A ⧸ p^eA`, the projection `A → Γ(S_e, ⊤)` is the quotient map. -/
theorem levelSectionsEquiv_baseChangeRingHom_levelProj {e : ℕ} (he : S.IsLevel e)
    (a : Γ(S.S.scheme, ⊤)) :
    S.levelSectionsEquiv he (baseChangeRingHom (S.levelProj he) a) = Ideal.Quotient.mk _ a := by
  change (Scheme.ΓSpecIso _).hom.hom
    ((Spec.map (CommRingCat.ofHom (pAdicLevelProj S.baseIdeal S.baseDividedPowers S.p he
      ).toRingHom)).appTop.hom (S.S.scheme.isoSpec.inv.appTop.hom a)) = _
  rw [ΓSpecIso_hom_specMap_appTop, isoSpec_inv_appTop_eq_ΓSpecIso_inv]
  exact congrArg _ (ConcreteCategory.congr_hom (Scheme.ΓSpecIso Γ(S.S.scheme, ⊤)).inv_hom_id a)

/-- Through `Γ(S_e, ⊤) ≅ A ⧸ p^eA`, the transitions of the levels are the canonical surjections. -/
theorem levelSectionsEquiv_baseChangeRingHom_levelTransition {m e : ℕ} (hm : S.IsLevel m)
    (he : S.IsLevel e) (hme : m ≤ e) (x : Γ((S.levelSituation he).S.scheme, ⊤)) :
    S.levelSectionsEquiv hm (baseChangeRingHom (S.levelTransition hm he hme) x) =
      Ideal.Quotient.factorPow _ hme (S.levelSectionsEquiv he x) :=
  ΓSpecIso_hom_specMap_appTop _ x

omit [IsAffine S.S.scheme] in
/-- `baseChangeRingHom` is contravariantly functorial. -/
theorem baseChangeRingHom_comp_apply {S₁ S₂ S₃ : GlobalCrystallineSituation.{u}} (f : S₁.S ⟶ S₂.S)
    (g : S₂.S ⟶ S₃.S) (x : Γ(S₃.S.scheme, ⊤)) :
    baseChangeRingHom (S := S₁) (S' := S₃) (f ≫ g) x =
      baseChangeRingHom f (baseChangeRingHom g x) := by
  simp only [baseChangeRingHom_apply, DividedPowerScheme.Hom.comp_hom, op_comp,
    Functor.map_comp, CommRingCat.hom_comp]
  rfl

variable {N₀ : ℕ} (h₀ : S.IsLevel N₀)

/-- The exponents `N₀(n+1)` increase with `n`. -/
theorem tower_le {m n : ℕ} (h : m ≤ n) : N₀ * (m + 1) ≤ N₀ * (n + 1) :=
  Nat.mul_le_mul_left _ (by omega)

/-- **The tower of rings `Γ(S_{N₀(n+1)}, ⊤)`** of the finite levels `N₀, 2N₀, 3N₀, …`. -/
def levelRingTower : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := Γ((S.levelSituation (h₀.mul n.unop)).S.scheme, ⊤)
  map {m n} f := Scheme.Γ.map (S.levelTransition (h₀.mul n.unop)
    (h₀.mul m.unop) (tower_le (leOfHom f.unop))).hom.op
  map_id n := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    change baseChangeRingHom (S.levelTransition (h₀.mul n.unop) (h₀.mul n.unop) le_rfl) x = x
    rw [levelTransition_self]
    exact RingHom.congr_fun (baseChangeRingHom_id (S.levelSituation (h₀.mul n.unop))) x
  map_comp {k m n} f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    exact (congrArg (fun φ ↦ baseChangeRingHom φ x) (S.levelTransition_comp (h₀.mul n.unop)
      (h₀.mul m.unop) (h₀.mul k.unop) (tower_le (leOfHom g.unop))
      (tower_le (leOfHom f.unop)))).symm.trans
      (baseChangeRingHom_comp_apply (S₁ := S.levelSituation (h₀.mul n.unop))
        (S₂ := S.levelSituation (h₀.mul m.unop)) (S₃ := S.levelSituation (h₀.mul k.unop)) _ _ x)

/-- The cone of the projections `A ⟶ Γ(S_{N₀(n+1)}, ⊤)`. -/
def levelRingCone : Cone (S.levelRingTower h₀) where
  pt := Γ(S.S.scheme, ⊤)
  π :=
    { app n := Scheme.Γ.map (S.levelProj (h₀.mul n.unop)).hom.op
      naturality {m n} f := by
        refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        exact (congrArg (fun φ ↦ baseChangeRingHom φ x) (S.levelTransition_comp_levelProj
          (h₀.mul n.unop) (h₀.mul m.unop) (tower_le (leOfHom f.unop)))).symm.trans
          (baseChangeRingHom_comp_apply (S₁ := S.levelSituation (h₀.mul n.unop))
            (S₂ := S.levelSituation (h₀.mul m.unop)) (S₃ := S) _ _ x) }

/-- The exponents `N₀(n+1)` are strictly increasing for `N₀ > 0`. -/
theorem strictMono_tower (hN₀ : 0 < N₀) : StrictMono fun n : ℕ ↦ N₀ * (n + 1) :=
  fun m n h ↦ Nat.mul_lt_mul_of_pos_left (by omega) hN₀

/-- **`A` is the limit of the tower `Γ(S_{N₀(n+1)}, ⊤)`**, `A` being `p`-adically complete. -/
def isLimitLevelRingCone [IsAdicComplete (DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p)
    Γ(S.S.scheme, ⊤)] (hN₀ : 0 < N₀) : IsLimit (S.levelRingCone h₀) := by
  let I := DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p
  have ha := strictMono_tower hN₀
  let fam : ∀ s : Cone (S.levelRingTower h₀), ∀ n : ℕ,
      s.pt →+* Γ(S.S.scheme, ⊤) ⧸ I ^ (N₀ * (n + 1)) :=
    fun s n ↦ (S.levelSectionsEquiv (h₀.mul n)).toRingHom.comp (s.π.app (op n)).hom
  have hfam : ∀ s : Cone (S.levelRingTower h₀), ∀ {m : ℕ},
      (Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp (fam s (m + 1)) = fam s m := by
    intro s m
    refine RingHom.ext fun x ↦ ?_
    refine (S.levelSectionsEquiv_baseChangeRingHom_levelTransition (h₀.mul m) (h₀.mul (m + 1))
      (tower_le m.le_succ) _).symm.trans ?_
    exact congrArg (S.levelSectionsEquiv (h₀.mul m))
      (ConcreteCategory.congr_hom (s.w (homOfLE (Nat.le_succ m)).op) x)
  refine
    { lift := fun s ↦ CommRingCat.ofHom (IsAdicComplete.StrictMono.liftRingHom I ha (fam s)
        (hfam s))
      fac := fun s n ↦ CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
      uniq := fun s g hg ↦ CommRingCat.hom_ext ?_ }
  · refine (S.levelSectionsEquiv (h₀.mul n.unop)).injective ?_
    refine (S.levelSectionsEquiv_baseChangeRingHom_levelProj (h₀.mul n.unop) _).trans ?_
    exact IsAdicComplete.StrictMono.mk_liftRingHom I ha (fam s) (hfam s) x
  · refine IsAdicComplete.StrictMono.eq_liftRingHom I ha (fam s) (hfam s) fun n ↦
      RingHom.ext fun x ↦ ?_
    refine (S.levelSectionsEquiv_baseChangeRingHom_levelProj (h₀.mul n) _).symm.trans ?_
    exact congrArg (S.levelSectionsEquiv (h₀.mul n)) (ConcreteCategory.congr_hom (hg (op n)) x)

/-- The transitions `Γ(S_e, ⊤) → Γ(S_m, ⊤)` are surjective. -/
theorem surjective_baseChangeRingHom_levelTransition {m e : ℕ} (hm : S.IsLevel m)
    (he : S.IsLevel e) (hme : m ≤ e) :
    Function.Surjective (baseChangeRingHom (S.levelTransition hm he hme)) := by
  intro y
  obtain ⟨z, hz⟩ := Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (I := DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p) hme)
    (S.levelSectionsEquiv hm y)
  refine ⟨(S.levelSectionsEquiv he).symm z, (S.levelSectionsEquiv hm).injective ?_⟩
  rwa [levelSectionsEquiv_baseChangeRingHom_levelTransition, RingEquiv.apply_symm_apply]

/-- The kernel of `Γ(S_e, ⊤) → Γ(S_m, ⊤)` squares to zero when `e ≤ 2m`. -/
theorem isNilpotent_ker_baseChangeRingHom_levelTransition {m e : ℕ} (hm : S.IsLevel m)
    (he : S.IsLevel e) (hme : m ≤ e) (h2 : e ≤ 2 * m) :
    IsNilpotent (RingHom.ker (baseChangeRingHom (S.levelTransition hm he hme))) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  refine (S.levelSectionsEquiv he).injective ?_
  rw [map_mul, map_zero]
  have hA : ∀ x ∈ RingHom.ker (baseChangeRingHom (S.levelTransition hm he hme)),
      ∃ y ∈ DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p ^ m,
        S.levelSectionsEquiv he x = Ideal.Quotient.mk _ y := by
    intro x hx
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (S.levelSectionsEquiv he x)
    refine ⟨y, ?_, hy.symm⟩
    have h := congrArg (S.levelSectionsEquiv hm) (RingHom.mem_ker.mp hx)
    rw [levelSectionsEquiv_baseChangeRingHom_levelTransition, map_zero, ← hy] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  obtain ⟨y, hy, hya⟩ := hA a ha
  obtain ⟨z, hz, hzb⟩ := hA b hb
  rw [hya, hzb, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_le_pow_right h2 (by rw [two_mul, pow_add]; exact Ideal.mul_mem_mul hy hz)

end GlobalCrystallineSituation

namespace GlobalCrystallineSituation.SmallSite

section LevelTransition

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme]

/-- The map on closed fibres of `S_e ⟶ S` is an isomorphism. -/
instance isIso_closedFiberMap_levelProj_of_trivial {e : ℕ} (he : S.IsLevel e) :
    IsIso (DividedPowerScheme.closedFiberMap (S.levelProj he)) := by
  have h : DividedPowerScheme.closedFiberMap (trivialBaseToLevel he) ≫
      DividedPowerScheme.closedFiberMap (S.levelProj he) =
        (trivialClosedFiberIso (DividedPowerScheme.closedFiber S.S)).hom := by
    rw [← DividedPowerScheme.closedFiberMap_comp, trivialBaseToLevel_comp_levelProj,
      closedFiberMap_closedFiberToBaseHom]
  have : IsIso (DividedPowerScheme.closedFiberMap (trivialBaseToLevel he) ≫
      DividedPowerScheme.closedFiberMap (S.levelProj he)) := by
    rw [h]
    exact Iso.isIso_hom _
  exact IsIso.of_isIso_comp_left (DividedPowerScheme.closedFiberMap (trivialBaseToLevel he)) _

/-- The map on closed fibres of a transition `S_m ⟶ S_e` is an isomorphism. -/
instance isIso_closedFiberMap_levelTransition {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e)
    (hme : m ≤ e) : IsIso (DividedPowerScheme.closedFiberMap (S.levelTransition hm he hme)) := by
  have h : DividedPowerScheme.closedFiberMap (S.levelTransition hm he hme) ≫
      DividedPowerScheme.closedFiberMap (S.levelProj he) =
        DividedPowerScheme.closedFiberMap (S.levelProj hm) := by
    rw [← DividedPowerScheme.closedFiberMap_comp, levelTransition_comp_levelProj]
  have : IsIso (DividedPowerScheme.closedFiberMap (S.levelTransition hm he hme) ≫
      DividedPowerScheme.closedFiberMap (S.levelProj he)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (DividedPowerScheme.closedFiberMap (S.levelProj he))

/-- **The square of closed fibres of `(S_m ⟶ S_e, 𝟙_X)` is a pullback square.** -/
theorem isPullback_levelTransition {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e)
    (hme : m ≤ e) :
    IsPullback (𝟙 S.X) (S.levelSituation hm).toClosedFiber (S.levelSituation he).toClosedFiber
      (DividedPowerScheme.closedFiberMap (S.levelTransition hm he hme)) :=
  IsPullback.of_horiz_isIso ⟨by rw [S.levelTransition_condition hm he hme]⟩

/-- **`p` is nilpotent on the level `S_e`.** -/
theorem isNilpotent_prime_level {e : ℕ} (he : S.IsLevel e) :
    IsNilpotent ((S.levelSituation he).p : Γ((S.levelSituation he).S.scheme, ⊤)) :=
  ⟨e, natCast_pow_eq_zero_level S he⟩

end LevelTransition

open DerivedCategory StacksDraft.DerivedInverseLimit

/-- The adjoint transposes of a morphism under two adjunctions with the same right adjoint are
isomorphisms together. -/
theorem isIso_adjTranspose_iff {C D : Type*} [Category* C] [Category* D] {F F' : C ⥤ D}
    {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) {X : C} {Y : D} (g : X ⟶ G.obj Y) :
    IsIso ((adj1.homEquiv X Y).symm g) ↔ IsIso ((adj2.homEquiv X Y).symm g) := by
  have h : (adj1.homEquiv X Y).symm g =
      (Adjunction.leftAdjointUniq adj1 adj2).hom.app X ≫ (adj2.homEquiv X Y).symm g := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, ← Category.assoc,
      ← (Adjunction.leftAdjointUniq adj1 adj2).hom.naturality, Category.assoc,
      Adjunction.leftAdjointUniq_hom_app_counit]
  rw [h]
  exact isIso_comp_left_iff _ _

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance 1100] HasDerivedCategory.standard

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme] {N₀ : ℕ} (h₀ : S.IsLevel N₀)
  (N : BigModuleSheaf S)

/-- `K = RΓ(CRIS(X/S), N)` in `D(Mod_A)`. -/
abbrev levelK : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  Plus.ι.obj ((derivedBigModuleGlobalSections S).obj N)

/-- `K_n = RΓ(CRIS(X/S_{N₀(n+1)}), N_{N₀(n+1)})`. -/
abbrev levelKn (n : ℕ) :
    DerivedCategory (ModuleCat.{u + 1} ((S.levelRingTower h₀).obj (op n))) :=
  Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).obj
    ((S.levelPullback (h₀.mul n)).obj N))

/-- The transition `K_{n+1} ⟶ res K_n`. -/
def levelPhi (n : ℕ) : levelKn S h₀ N (n + 1) ⟶
    (ModuleCat.restrictScalars ((S.levelRingTower h₀).map (homOfLE (Nat.le_succ n)).op).hom
      ).mapDerivedCategory.obj (levelKn S h₀ N n) :=
  Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
      (S.levelTransition (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)) (𝟙 S.X)
      (S.levelTransition_condition _ _ _) ((S.levelPullback (h₀.mul (n + 1))).obj N)) ≫
    Plus.ι.map ((ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom
      (S.levelTransition (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ))
        )).mapDerivedCategoryPlus.map
      ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).map
        ((S.levelPullbackCompIso (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)).hom.app N)))

/-- The comparison `K ⟶ res K_n`. -/
def levelC (n : ℕ) : levelK S N ⟶
    (ModuleCat.restrictScalars ((S.levelRingCone h₀).π.app (op n)).hom).mapDerivedCategory.obj
      (levelKn S h₀ N n) :=
  Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap (S.levelProj (h₀.mul n)) (𝟙 S.X)
    (S.levelProj_condition _) N)

/-- The transpose of [Stacks, Tag 0CQF] and the chapter's transpose (under `- ⊗^L_{A'} A ⊣ res`)
are isomorphisms together: the two adjunctions share their right adjoint. -/
theorem isIso_derivedBaseChangeComparison_iff {S' S'' : GlobalCrystallineSituation.{u}}
    (f : S'.S ⟶ S''.S) {X : DerivedCategory (ModuleCat.{u + 1} Γ(S''.S.scheme, ⊤))}
    {Y : DerivedCategory (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))}
    (g : X ⟶ (ModuleCat.restrictScalars (baseChangeRingHom f)).mapDerivedCategory.obj Y) :
    IsIso (derivedBaseChangeComparison.{u, u + 1, u} (baseChangeRingHom f) g) ↔
      IsIso (((derivedBaseChangeTensorAdjunction f).homEquiv X Y).symm g) :=
  isIso_adjTranspose_iff _ _ g

/-- The terms `res K_n` of the tower in `D(Mod_A)`. -/
abbrev levelX (n : ℕ) : DerivedCategory (ModuleCat.{u + 1} (S.levelRingCone h₀).pt) :=
  (ModuleCat.restrictScalars ((S.levelRingCone h₀).π.app (op n)).hom).mapDerivedCategory.obj
    (levelKn S h₀ N n)

/-- The transitions `res K_{n+1} ⟶ res K_n` of the tower in `D(Mod_A)`. -/
abbrev levelT (n : ℕ) : levelX S h₀ N (n + 1) ⟶ levelX S h₀ N n :=
  (ModuleCat.restrictScalars ((S.levelRingCone h₀).π.app (op (n + 1))).hom).mapDerivedCategory.map
      (levelPhi S h₀ N n) ≫
    (derivedRestrictScalarsComp.{u, u + 1} ((S.levelRingCone h₀).π.app (op (n + 1))).hom
      ((S.levelRingTower h₀).map (homOfLE (Nat.le_succ n)).op).hom
      ((S.levelRingCone h₀).π.app (op n)).hom
      (congrArg CommRingCat.Hom.hom
        ((S.levelRingCone h₀).w (homOfLE (Nat.le_succ n)).op)).symm).hom.app
        (levelKn S h₀ N n)

/-- The transition `levelT` is the comparison along `S_{N₀(n+1)} ⟶ S_{N₀(n+2)}`, read in
`D(Mod_A)`, followed by the comparison of the two restrictions of scalars to `A` and the
identification of the restriction of `N_{N₀(n+2)}` with `N_{N₀(n+1)}`. -/
theorem levelT_eq (n : ℕ) :
    levelT S h₀ N n =
      (ModuleCat.restrictScalars ((S.levelRingCone h₀).π.app (op (n + 1))).hom
          ).mapDerivedCategory.map (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
            (S.levelTransition (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)) (𝟙 S.X)
            (S.levelTransition_condition _ _ _) ((S.levelPullback (h₀.mul (n + 1))).obj N))) ≫
        (derivedRestrictScalarsComp.{u, u + 1} ((S.levelRingCone h₀).π.app (op (n + 1))).hom
          ((S.levelRingTower h₀).map (homOfLE (Nat.le_succ n)).op).hom
          ((S.levelRingCone h₀).π.app (op n)).hom
          (congrArg CommRingCat.Hom.hom
            ((S.levelRingCone h₀).w (homOfLE (Nat.le_succ n)).op)).symm).hom.app
          (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).obj
            ((S.levelStepPullback (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)).obj
              ((S.levelPullback (h₀.mul (n + 1))).obj N)))) ≫
        (ModuleCat.restrictScalars ((S.levelRingCone h₀).π.app (op n)).hom
          ).mapDerivedCategory.map (Plus.ι.map
            ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).map
              ((S.levelPullbackCompIso (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)).hom.app
                N))) := by
  refine ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _)).trans
    (congrArg (_ ≫ ·) ?_)
  exact ((derivedRestrictScalarsComp.{u, u + 1} ((S.levelRingCone h₀).π.app (op (n + 1))).hom
    ((S.levelRingTower h₀).map (homOfLE (Nat.le_succ n)).op).hom
    ((S.levelRingCone h₀).π.app (op n)).hom
    (congrArg CommRingCat.Hom.hom
      ((S.levelRingCone h₀).w (homOfLE (Nat.le_succ n)).op)).symm).hom.naturality
    (Plus.ι.map ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).map
      ((S.levelPullbackCompIso (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)).hom.app
        N))))

/-- **The levels assembly, in the standard models.**  Given the Milnor triangle of
`K = RΓ(CRIS(X/S), N)` over the levels `S_{N₀(n+1)}`, the base change isomorphisms of the tower,
and the pseudo-coherence of `K_0 = RΓ(CRIS(X/S_{N₀}), N_{N₀})`, the complex `K` is pseudo-coherent
and every transpose `K ⊗^L_A Γ(S_{N₀(n+1)}, ⊤) ⟶ K_n` of the change-of-base comparison is an
isomorphism ([Stacks, Tag 0CQF] on the tower of `isLimitLevelRingCone`). -/
theorem levels_isPseudoCoherent_and_isIso
    [IsAdicComplete (DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p) Γ(S.S.scheme, ⊤)]
    (hN₀ : 0 < N₀)
    (hBC : ∀ n : ℕ, IsIso (((derivedBaseChangeTensorAdjunction (S.levelTransition (h₀.mul n)
      (h₀.mul (n + 1)) (tower_le n.le_succ))).homEquiv
        (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul (n + 1)))).obj
          ((S.levelPullback (h₀.mul (n + 1))).obj N)))
        (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).obj
          ((S.levelStepPullback (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)).obj
            ((S.levelPullback (h₀.mul (n + 1))).obj N))))).symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
          (S.levelTransition (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)) (𝟙 S.X)
          (S.levelTransition_condition _ _ _) ((S.levelPullback (h₀.mul (n + 1))).obj N)))))
    (hPC : PseudoCoherence.IsPseudoCoherent (levelKn S h₀ N 0))
    [HasProduct (levelX S h₀ N)] (δ : ∏ᶜ levelX S h₀ N ⟶ (levelK S N)⟦(1 : ℤ)⟧)
    (hTri : Pretriangulated.Triangle.mk (Pi.lift (levelC S h₀ N))
      (Pi.lift fun n : ℕ ↦ Pi.π (levelX S h₀ N) n - Pi.π (levelX S h₀ N) (n + 1) ≫
        levelT S h₀ N n) δ ∈
          distTriang (DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)))) :
    PseudoCoherence.IsPseudoCoherent (levelK S N) ∧ ∀ n : ℕ,
      IsIso (((derivedBaseChangeTensorAdjunction (S.levelProj (h₀.mul n))).homEquiv
        (levelK S N) (levelKn S h₀ N n)).symm (levelC S h₀ N n)) := by
  have h2n : ∀ n : ℕ, N₀ * (n + 1 + 1) ≤ 2 * (N₀ * (n + 1)) := fun n ↦ by
    have := Nat.mul_le_mul_left N₀ (show n + 1 + 1 ≤ 2 * (n + 1) by omega)
    linarith
  have hSurj : ∀ n : ℕ,
      Function.Surjective ((S.levelRingTower h₀).map (homOfLE (Nat.le_succ n)).op).hom :=
    fun n ↦ S.surjective_baseChangeRingHom_levelTransition _ _ _
  have hNil : ∀ n : ℕ,
      IsNilpotent (RingHom.ker ((S.levelRingTower h₀).map (homOfLE (Nat.le_succ n)).op).hom) :=
    fun n ↦ S.isNilpotent_ker_baseChangeRingHom_levelTransition _ _ _ (h2n n)
  have hBC' : ∀ n : ℕ, IsIso (derivedBaseChangeComparison.{u, u + 1, u}
      ((S.levelRingTower h₀).map (homOfLE (Nat.le_succ n)).op).hom (levelPhi S h₀ N n)) := by
    intro n
    refine (isIso_derivedBaseChangeComparison_iff (S.levelTransition (h₀.mul n) (h₀.mul (n + 1))
      (tower_le n.le_succ)) (levelPhi S h₀ N n)).mpr ?_
    have h := (derivedBaseChangeTensorAdjunction (S.levelTransition (h₀.mul n)
      (h₀.mul (n + 1)) (tower_le n.le_succ))).homEquiv_naturality_right_symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
          (S.levelTransition (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)) (𝟙 S.X)
          (S.levelTransition_condition _ _ _) ((S.levelPullback (h₀.mul (n + 1))).obj N)))
        (Plus.ι.map ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).map
            ((S.levelPullbackCompIso (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)).hom.app
              N)))
    have hI' : IsIso ((((derivedBaseChangeTensorAdjunction (S.levelTransition (h₀.mul n)
      (h₀.mul (n + 1)) (tower_le n.le_succ))).homEquiv _ _).symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
          (S.levelTransition (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)) (𝟙 S.X)
          (S.levelTransition_condition _ _ _) ((S.levelPullback (h₀.mul (n + 1))).obj N)))) ≫
        (Plus.ι.map ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).map
            ((S.levelPullbackCompIso (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)).hom.app
              N)))) := IsIso.comp_isIso' (hBC n) (by infer_instance)
    rwa [← h] at hI'
  have hMain := derivedLimit_isPseudoCoherent_and_baseChange_iso.{u, u + 1} (S.levelRingTower h₀)
    (S.levelRingCone h₀) (S.isLimitLevelRingCone h₀ hN₀) (levelKn S h₀ N) (levelPhi S h₀ N) hSurj
    (fun n ↦ isLocallyNilpotent_of_isNilpotent _ (hNil n))
    (Or.inr ⟨0, hPC, fun n _ ↦ hNil n⟩) hBC'
  have h4 := hMain (levelK S N) (Pi.lift (levelC S h₀ N)) δ hTri
  refine ⟨h4.1, fun n ↦ ?_⟩
  have h' : IsIso (derivedBaseChangeComparison.{u, u + 1, u}
      (baseChangeRingHom (S.levelProj (h₀.mul n))) (levelC S h₀ N n)) := by
    exact (Pi.lift_comp_π (levelC S h₀ N) n) ▸ h4.2 n
  exact (isIso_derivedBaseChangeComparison_iff (S.levelProj (h₀.mul n)) (levelC S h₀ N n)).mp h'

/-- The transpose of the comparison at a level only depends on the exponent. -/
theorem isIso_transpose_levelProj_congr {e e' : ℕ} (h : e = e') (he : S.IsLevel e)
    (he' : S.IsLevel e') :
    IsIso (((derivedBaseChangeTensorAdjunction (S.levelProj he)).homEquiv (levelK S N)
        (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation he)).obj
          ((S.levelPullback he).obj N)))).symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap (S.levelProj he) (𝟙 S.X)
          (S.levelProj_condition _) N))) ↔
      IsIso (((derivedBaseChangeTensorAdjunction (S.levelProj he')).homEquiv (levelK S N)
        (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation he')).obj
          ((S.levelPullback he').obj N)))).symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap (S.levelProj he') (𝟙 S.X)
          (S.levelProj_condition _) N))) := by
  subst h
  rfl

/-- **The levels assembly at the level `N₀` itself**, in the standard models: `K` is
pseudo-coherent and `K ⊗^L_A Γ(S_{N₀}, ⊤) ⟶ RΓ(CRIS(X/S_{N₀}), N_{N₀})` is an isomorphism. -/
theorem levels_isPseudoCoherentIn_and_isIso_levelProj
    [IsAdicComplete (DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p) Γ(S.S.scheme, ⊤)]
    (hN₀ : 0 < N₀)
    (hBC : ∀ n : ℕ, IsIso (((derivedBaseChangeTensorAdjunction (S.levelTransition (h₀.mul n)
      (h₀.mul (n + 1)) (tower_le n.le_succ))).homEquiv
        (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul (n + 1)))).obj
          ((S.levelPullback (h₀.mul (n + 1))).obj N)))
        (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).obj
          ((S.levelStepPullback (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)).obj
            ((S.levelPullback (h₀.mul (n + 1))).obj N))))).symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
          (S.levelTransition (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)) (𝟙 S.X)
          (S.levelTransition_condition _ _ _) ((S.levelPullback (h₀.mul (n + 1))).obj N)))))
    (hPC : StacksDraft.PseudoCoherence.IsPseudoCoherentIn (levelKn S h₀ N 0))
    [HasProduct (levelX S h₀ N)] (δ : ∏ᶜ levelX S h₀ N ⟶ (levelK S N)⟦(1 : ℤ)⟧)
    (hTri : Pretriangulated.Triangle.mk (Pi.lift (levelC S h₀ N))
      (Pi.lift fun n : ℕ ↦ Pi.π (levelX S h₀ N) n - Pi.π (levelX S h₀ N) (n + 1) ≫
        levelT S h₀ N n) δ ∈
          distTriang (DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentIn (levelK S N) ∧
      IsIso (((derivedBaseChangeTensorAdjunction (S.levelProj h₀)).homEquiv (levelK S N)
        (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation h₀)).obj
          ((S.levelPullback h₀).obj N)))).symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap (S.levelProj h₀) (𝟙 S.X)
          (S.levelProj_condition _) N))) := by
  obtain ⟨h1, h2⟩ := levels_isPseudoCoherent_and_isIso S h₀ N hN₀ hBC hPC δ hTri
  exact ⟨h1, (isIso_transpose_levelProj_congr S N (Nat.mul_one N₀) (h₀.mul 0) h₀).mp (h2 0)⟩

end GlobalCrystallineSituation.SmallSite

end Crystalline

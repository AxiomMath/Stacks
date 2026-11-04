module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportLevelComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Transition

/-!
# The tower `Kₙ = RΓ_c(X_k̄, Fₙ)` of an ℓ-adic sheaf with flat levels

Let `F = {Fₙ}` be an ℓ-adic sheaf on `X` whose levels are flat (pow-exact) and whose
compactly supported cohomologies `RΓ_c(X_k̄, Fₙ)` are perfect.  The complexes
`Kₙ = RΓ_c(X_k̄, Fₙ) ∈ D(ℤ/ℓⁿ⁺¹ℤ)`, with the canonical geometric Frobenius `π_X^*` and the
transitions induced by those of `F`, form a tower of perfect complexes in the sense of
[Tag 03V4](https://stacks.math.columbia.edu/tag/03V4).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.etaleLevel`: the level `Fₙ` read on Mathlib's small étale
  site.
* `Stacks.EtaleCohomology.LAdicSheaf.etaleTransition`: the transition `Fₙ₊₁ ⟶ Fₙ` there.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricPerfectTower`: the tower.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 03V4](https://stacks.math.columbia.edu/tag/03V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Transport

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- Restriction of scalars commutes with reading sheaves on the small étale site of Stacks 021B
from Mathlib's: pushing forward along the embedding of sites commutes with composing with a
functor of coefficients. -/
def sheafEquivInverseRestrictScalarsIso :
    (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ')).inverse ⋙
        sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ) ≅
      etaleModuleRestrictScalars ρ S ⋙
        (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse :=
  Iso.refl _

/-- **Restriction of scalars commutes with reading sheaves of Stacks 021B on Mathlib's small
étale site.** -/
def sheafEquivRestrictScalarsIso :
    (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ')).functor ⋙ etaleModuleRestrictScalars ρ S ≅
      sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ) ⋙
        (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).functor :=
  (CatCommSq.hInv (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ')).symm
    (etaleModuleRestrictScalars ρ S)
    (sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ))
    (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).symm
    ⟨sheafEquivInverseRestrictScalarsIso B S hS ρ⟩).iso

end Transport

section CokernelSingle

variable {C : Type*} [Category* C] [Abelian C]

/-- A cokernel cofork between zero objects is a colimit. -/
def isColimitCokernelCoforkOfIsZero {X Y : C} (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ X)
    (g : X ⟶ Y) (w : f ≫ g = 0) : IsColimit (CokernelCofork.ofπ g w) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun _ _ => 0) (fun _ _ => hX.eq_of_src _ _)
    (fun _ _ _ _ => hY.eq_of_src _ _)

/-- If `f ≫ g = 0` and `f'` is conjugate to `f` by `e₁`, then `f'` composed with
`e₁.hom ≫ g ≫ e₂.hom` is zero. -/
theorem conj_cokernel_condition {X X' Y Y' : C} (f : X ⟶ X) (g : X ⟶ Y) (w : f ≫ g = 0)
    (e₁ : X' ≅ X) (e₂ : Y ≅ Y') (f' : X' ⟶ X') (hf : f' ≫ e₁.hom = e₁.hom ≫ f) :
    f' ≫ e₁.hom ≫ g ≫ e₂.hom = 0 := by
  rw [← Category.assoc, hf, Category.assoc, ← Category.assoc f g, w, zero_comp, comp_zero]

/-- A cokernel of `f`, conjugated by isomorphisms, is a cokernel of the conjugate of `f`. -/
def isColimitCokernelCoforkConj {X X' Y Y' : C} (f : X ⟶ X) (g : X ⟶ Y) (w : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ g w)) (e₁ : X' ≅ X) (e₂ : Y ≅ Y') (f' : X' ⟶ X')
    (hf : f' ≫ e₁.hom = e₁.hom ≫ f) (w' : f' ≫ e₁.hom ≫ g ≫ e₂.hom = 0) :
    IsColimit (CokernelCofork.ofπ (e₁.hom ≫ g ≫ e₂.hom) w') := by
  have hd : ∀ {Z : C} (g' : X' ⟶ Z), f' ≫ g' = 0 → f ≫ e₁.inv ≫ g' = 0 ≫ e₁.inv ≫ g' :=
    fun g' hg' => by
      rw [zero_comp, ← cancel_epi e₁.hom, comp_zero, ← Category.assoc, ← hf, Category.assoc,
        e₁.hom_inv_id_assoc, hg']
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun g' hg' => e₂.inv ≫ Cofork.IsColimit.desc h (e₁.inv ≫ g') (hd g' hg'))
    (fun g' hg' => ?_) (fun g' hg' m hm => ?_)
  · have hfac : g ≫ Cofork.IsColimit.desc h (e₁.inv ≫ g') (hd g' hg') = e₁.inv ≫ g' :=
      Cofork.IsColimit.π_desc' h _ (hd g' hg')
    simp only [Category.assoc, e₂.hom_inv_id_assoc]
    rw [hfac, e₁.hom_inv_id_assoc]
  · have hfac : g ≫ Cofork.IsColimit.desc h (e₁.inv ≫ g') (hd g' hg') = e₁.inv ≫ g' :=
      Cofork.IsColimit.π_desc' h _ (hd g' hg')
    rw [← cancel_epi e₂.hom, e₂.hom_inv_id_assoc]
    refine Cofork.IsColimit.hom_ext h ?_
    change g ≫ e₂.hom ≫ m = g ≫ _
    rw [hfac, ← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← hm, Category.assoc, Category.assoc]

end CokernelSingle

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Levels

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-- The level `Fₙ` of an ℓ-adic sheaf, read on Mathlib's small étale site. -/
abbrev LAdicSheaf.etaleLevel (F : LAdicSheaf B X ℓ) (n : ℕ) :
    EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) X.1 :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.obj
    (F.level n)

/-- The transition `Fₙ₊₁ ⟶ Fₙ` of an ℓ-adic sheaf, read on Mathlib's small étale site. -/
def LAdicSheaf.etaleTransition (F : LAdicSheaf B X ℓ) (n : ℕ) :
    LAdicSheaf.etaleLevel B X ℓ F (n + 1) ⟶
      (etaleModuleRestrictScalars (levelCast ℓ n) X.1).obj (LAdicSheaf.etaleLevel B X ℓ F n) :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).functor.map
      (F.transition n) ≫
    (sheafEquivRestrictScalarsIso B X.1 X.property (levelCast ℓ n)).inv.app (F.level n)

/-- An additive functor preserves the vanishing of `(m • 𝟙) ≫ g`. -/
private theorem map_nsmul_id_comp_map_eq_zero {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive] (m : ℕ) {X Y : C} (g : X ⟶ Y)
    (h : (m • 𝟙 X) ≫ g = 0) : (m • 𝟙 (G.obj X)) ≫ G.map g = 0 := by
  rw [← G.map_id, ← G.map_nsmul, ← G.map_comp, h, G.map_zero]

/-- `ℓⁿ⁺¹` kills the transition. -/
theorem LAdicSheaf.etaleTransition_condition (F : LAdicSheaf B X ℓ) (n : ℕ) :
    ((ℓ ^ (n + 1)) • 𝟙 (LAdicSheaf.etaleLevel B X ℓ F (n + 1))) ≫
      LAdicSheaf.etaleTransition B X ℓ F n = 0 := by
  let e := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  rw [LAdicSheaf.etaleTransition, ← Category.assoc,
    map_nsmul_id_comp_map_eq_zero e.functor _ _ (transition_condition F n), zero_comp]

/-- **The transition exhibits `Fₙ` as `Fₙ₊₁ / ℓⁿ⁺¹ Fₙ₊₁`.** -/
def LAdicSheaf.etaleTransitionIsCokernel (F : LAdicSheaf B X ℓ) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (LAdicSheaf.etaleTransition B X ℓ F n)
      (LAdicSheaf.etaleTransition_condition B X ℓ F n)) := by
  let e := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h₁ := isColimitCoforkMapOfIsColimit' e.functor (transition_condition F n)
    (transition_isCokernel F n)
  have hf : e.functor.map ((ℓ ^ (n + 1)) • 𝟙 (F.level (n + 1))) =
      (ℓ ^ (n + 1)) • 𝟙 (LAdicSheaf.etaleLevel B X ℓ F (n + 1)) := by
    rw [e.functor.map_nsmul, e.functor.map_id]
  exact isColimitCokernelCoforkCompIso _ (isColimitCokernelCoforkOfEq hf _ h₁)
    (e := (sheafEquivRestrictScalarsIso B X.1 X.property (levelCast ℓ n)).inv.app (F.level n))
    inferInstance

/-- The level `Fₙ`, as a bounded below complex concentrated in degree `0`. -/
abbrev LAdicSheaf.levelComplex (F : LAdicSheaf B X ℓ) (n : ℕ) :
    CochainComplex.Plus (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) X.1) :=
  ⟨(CochainComplex.singleFunctor _ 0).obj (LAdicSheaf.etaleLevel B X ℓ F n),
    CochainComplex.plus_singleFunctor_obj _⟩

/-- The transition of an ℓ-adic sheaf, on the complexes concentrated in degree `0`. -/
def LAdicSheaf.levelComplexTransition (F : LAdicSheaf B X ℓ) (n : ℕ) :
    LAdicSheaf.levelComplex B X ℓ F (n + 1) ⟶
      (etaleModuleRestrictScalars (levelCast ℓ n) X.1).mapCochainComplexPlus.obj
        (LAdicSheaf.levelComplex B X ℓ F n) :=
  ObjectProperty.homMk ((CochainComplex.singleFunctor _ 0).map
      (LAdicSheaf.etaleTransition B X ℓ F n) ≫
    (HomologicalComplex.singleMapHomologicalComplex (etaleModuleRestrictScalars (levelCast ℓ n) X.1)
      (ComplexShape.up ℤ) 0).inv.app (LAdicSheaf.etaleLevel B X ℓ F n))

/-- In each degree, multiplication by `ℓⁿ⁺¹` on the level complex of `Fₙ₊₁` composed with the
transition to the level complex of `Fₙ` is zero. -/
theorem LAdicSheaf.levelComplexTransition_condition (F : LAdicSheaf B X ℓ) (n : ℕ) (i : ℤ) :
    ((ℓ ^ (n + 1)) • 𝟙 ((LAdicSheaf.levelComplex B X ℓ F (n + 1)).obj.X i)) ≫
      (LAdicSheaf.levelComplexTransition B X ℓ F n).hom.f i = 0 := by
  let sg := HomologicalComplex.single (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) X.1)
    (ComplexShape.up ℤ) 0
  have h₁ := map_nsmul_id_comp_map_eq_zero sg (ℓ ^ (n + 1)) (LAdicSheaf.etaleTransition B X ℓ F n)
    (LAdicSheaf.etaleTransition_condition B X ℓ F n)
  have h₂ := HomologicalComplex.congr_hom h₁ i
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, HomologicalComplex.nsmul_f_apply,
    HomologicalComplex.id_f] at h₂
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans zero_comp)

/-- **The transition is termwise a cokernel of `ℓⁿ⁺¹`.** -/
def LAdicSheaf.levelComplexTransitionIsCokernel (F : LAdicSheaf B X ℓ) (n : ℕ) (i : ℤ) :
    IsColimit (CokernelCofork.ofπ ((LAdicSheaf.levelComplexTransition B X ℓ F n).hom.f i)
      (LAdicSheaf.levelComplexTransition_condition B X ℓ F n i)) := by
  by_cases hi : i = 0
  · subst hi
    let rX := etaleModuleRestrictScalars (levelCast ℓ n) X.1
    let sg := HomologicalComplex.single (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) X.1)
      (ComplexShape.up ℤ) 0
    let e₁ := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (LAdicSheaf.etaleLevel B X ℓ F (n + 1))
    let e₂ := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (rX.obj (LAdicSheaf.etaleLevel B X ℓ F n))).symm
    let ι₀ := ((HomologicalComplex.singleMapHomologicalComplex rX (ComplexShape.up ℤ) 0).inv.app
      (LAdicSheaf.etaleLevel B X ℓ F n)).f 0
    have hι₀ : IsIso ι₀ := by
      dsimp only [ι₀]
      infer_instance
    have hc := isColimitCokernelCoforkConj _ _ _ (LAdicSheaf.etaleTransitionIsCokernel B X ℓ F n)
      e₁ e₂ ((ℓ ^ (n + 1)) • 𝟙 (sg.obj (LAdicSheaf.etaleLevel B X ℓ F (n + 1))).X 0)
      (nsmul_id_comp e₁.hom _) (conj_cokernel_condition ((ℓ ^ (n + 1)) • 𝟙 _) _
        (LAdicSheaf.etaleTransition_condition B X ℓ F n) e₁ e₂ _ (nsmul_id_comp e₁.hom _))
    have h₁ := isColimitCokernelCoforkOfEqπ
      (HomologicalComplex.single_map_f_self (V := EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) X.1)
        (c := ComplexShape.up ℤ) 0 (LAdicSheaf.etaleTransition B X ℓ F n)).symm _ hc
    exact isColimitCokernelCoforkCompIso _ h₁ hι₀
  · exact isColimitCokernelCoforkOfIsZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i hi)
      ((etaleModuleRestrictScalars (levelCast ℓ n) X.1).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i hi)) _ _ _

/-- If `t` intertwines `fa` with `fb` and `θ` intertwines `fb'` with `fb`, then `t ≫ θ.inv`
intertwines `fa` with `fb'`. -/
theorem tower_endo_aux {C : Type*} [Category* C] {A B B' : C} (fa : A ⟶ A) (t : A ⟶ B)
    (fb : B ⟶ B) (θ : B' ≅ B) (fb' : B' ⟶ B') (h₁ : t ≫ fb = fa ≫ t)
    (h₂ : fb' ≫ θ.hom = θ.hom ≫ fb) : fa ≫ t ≫ θ.inv = (t ≫ θ.inv) ≫ fb' := by
  have h₃ : fb ≫ θ.inv = θ.inv ≫ fb' := by
    rw [Iso.comp_inv_eq, Category.assoc, h₂, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← h₁, Category.assoc, h₃, Category.assoc]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The tower `Kₙ = RΓ_c(X_k̄, Fₙ)` of an ℓ-adic sheaf with flat levels**, with the canonical
geometric Frobenius `π_X^*` and the transitions induced by those of `F`, given that every `Kₙ` is
perfect: a tower of perfect complexes in the sense of
[Tag 03V4](https://stacks.math.columbia.edu/tag/03V4). -/
def LAdicSheaf.geometricPerfectTower (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) :
    PerfectTower.{u + 1} ℓ where
  obj n := DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1)))
    f j kbar (LAdicSheaf.levelComplex B X ℓ F n))
  isPerfect := hP
  endo n := DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} _ f j kbar p q hcard
    (LAdicSheaf.levelComplex B X ℓ F n))
  transition n := DerivedCategory.Plus.ι.map
    ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map
        (LAdicSheaf.levelComplexTransition B X ℓ F n) ≫
      (compactSupportFrobeniusCohomologyRestrictScalarsIso (levelCast ℓ n) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)).inv)
  comparison_isIso n := isIso_levelAdjunction_homEquiv_symm_compactSupport n f j kbar _ _ _
    (fun i => powExact_single_X (hF (n + 1)) i) _
    (LAdicSheaf.levelComplexTransitionIsCokernel B X ℓ F n) (hP (n + 1))
  endo_compatible n := by
    have h₁ := (canonicalCompactSupportFrobeniusNatTrans.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) f j kbar
      p q hcard).naturality (LAdicSheaf.levelComplexTransition B X ℓ F n)
    have h₂ := restrictScalars_canonicalCompactSupportFrobenius (levelCast ℓ n) f j kbar p q hcard
      (LAdicSheaf.levelComplex B X ℓ F n)
    exact (DerivedCategory.Plus.ι.map_comp _ _).symm.trans ((congrArg DerivedCategory.Plus.ι.map
      (tower_endo_aux _ _ _ _ _ h₁ h₂)).trans (DerivedCategory.Plus.ι.map_comp _ _))

end Levels

end Stacks.EtaleCohomology

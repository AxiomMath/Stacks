module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.DerivedModuleCorrespondence
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ActionTotalComplexUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ActionWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.HypercohomologyBridge
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism `ξ' : Ω^• ⟶ Ω^•[n]` acts on cohomology by cup product

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex. Remark 0FU7 attaches to `ξ ∈ H^n_{dR}` a morphism
`ξ' : Ω^• ⟶ Ω^•[n]` of `D(A)`, and its property (3) says that `ξ'` sends `η ∈ H^m_{dR}` to
`ξ ∪ η ∈ H^{n + m}_{dR}`.

The argument is the one of Differential Graded Sheaves, Section 0FU3. Represent the morphism of
`D(Ω^•, d)` underlying `ξ'` by a roof `Ω^• ⟶ I ⟵ Ω^•[n]` of maps of right differential graded
modules, the second a quasi-isomorphism. A map of right differential graded modules out of the
regular module is right multiplication by its value at `1`, and right multiplication is the
action `Tot(I ⊗ Ω^•) ⟶ I`; the unit law of the cup product and its naturality then show that
the map induced on `H^m` is the cup product with the class of the value at `1`, read through the
action. Pulling this back along the quasi-isomorphism, moving the shift out of the first factor
(no sign: `totalCupPairing_shift₁`), and identifying the action of `Ω^•` on itself with the
wedge product of Tag 0FM2 gives the cup product of Tag 0FM3.

Everything is first done for an arbitrary sheaf of differential graded algebras `𝒜` over
`(X, A)` whose underlying complex is bounded below.

## Main results

* `AlgebraicGeometry.SheafOfModules.dgaClassMorphism_cup`: for `ξ ∈ H^n(X, 𝒜)` and
  `η ∈ H^m(X, 𝒜)`, `ξ'` sends `η` to the cup product of `ξ` and `η` along the multiplication of
  `𝒜`.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_eq_deRhamClassMorphism`: **Remark 0FU7,
  property (3)**, `ξ ∪ η = ξ'(η)`.

## References

* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The cancellations behind `exists_derivedForgetShiftedHom_comp_eq`, with every object and
morphism a variable. -/
theorem roof_paste {C : Type*} [Category* C] {P Q Q' R T : C} (a : P ⟶ Q) (e₁ : Q = Q')
    (c : Q' ⟶ R) (c' : R ⟶ Q') (e₂ : Q' = Q) (q : Q ⟶ T) (hc : c ≫ c' = 𝟙 _) :
    (a ≫ eqToHom e₁ ≫ c) ≫ c' ≫ eqToHom e₂ ≫ q = a ≫ q := by
  simp only [Category.assoc]
  rw [reassoc_of% hc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **A morphism `A ⟶ A[n]` of `D(A, d)` is a roof.** Its underlying morphism of `D(O)`, followed
by the identification of `A[n]` with the complex of the translate `A[n]` of the regular module and
by a quasi-isomorphism `b` from that translate into a graded injective K-injective module `I`, is
the underlying morphism of a map `x : A ⟶ I` of right differential graded modules. -/
theorem exists_derivedForgetShiftedHom_comp_eq (n : ℤ)
    (g : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj
          (regularModule A)))⟦n⟧) :
    ∃ (I : DifferentialGradedModule.{u, u, u} A) (x : regularModule A ⟶ I)
      (b : shiftedModule A (regularModule A) n ⟶ I), QuasiIso b.toHomologicalComplex ∧
      derivedForgetShiftedHom A (regularModule A) n g ≫
          (DerivedCategory.Q.commShiftIso n).inv.app (regularModule A).complex ≫
          eqToHom (congrArg DerivedCategory.Q.obj
            (HomotopyCategory.shiftFunctor_obj_complex A n (regularModule A)).symm) ≫
          DerivedCategory.Q.map b.toHomologicalComplex =
        DerivedCategory.Q.map x.toHomologicalComplex := by
  obtain ⟨I, b, hb, hGI, hKI⟩ := hasKInjectiveResolutions_dg.{u, u, u} A
    (shiftedModule A (regularModule A) n)
  let e := derivedHomEquivHomotopyHomOfKInjective (M := regularModule A) hKI hGI hb
  let g' := g ≫ ((toDerivedCategory.{u, u, u} A).commShiftIso n).inv.app
    ((HomotopyCategory.quotient A).obj (regularModule A))
  obtain ⟨x, hx⟩ := (HomotopyCategory.quotient A).map_surjective (e g')
  refine ⟨I, x, b, hb, ?_⟩
  have hg' : g' = (toDerivedCategory.{u, u, u} A).map ((HomotopyCategory.quotient A).map x) ≫
      (toDerivedCategoryIso b hb).inv := by
    rw [hx, ← derivedHomEquivHomotopyHomOfKInjective_symm_apply hKI hGI hb]
    exact (e.symm_apply_apply g').symm
  have hhom : ((derivedForget A).mapIso (toDerivedCategoryIso b hb)).hom =
      DerivedCategory.Q.map b.toHomologicalComplex :=
    derivedForget_map_toDerivedCategory_map A _
  have hF : (derivedForget A).map g' = DerivedCategory.Q.map x.toHomologicalComplex ≫
      ((derivedForget A).mapIso (toDerivedCategoryIso b hb)).inv := by
    rw [hg', Functor.map_comp, derivedForget_map_toDerivedCategory_map, homotopyForget_quotient_map]
    rfl
  unfold derivedForgetShiftedHom
  refine (roof_paste (C := DerivedCategory (_root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) _ _ _ _ _ _
    (Iso.hom_inv_id_app (DerivedCategory.Q.commShiftIso n) (regularModule A).complex)).trans ?_
  change (derivedForget A).map g' ≫ _ = _
  rw [hF]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) hhom.symm).trans
    (Iso.inv_hom_id _))).trans (Category.comp_id _))

/-- A heterogeneous equality of biadditive maps with targets in two equal degrees of a graded
family gives one of their values. -/
theorem heq_addMonoidHom₂_apply {P Q : Type*} [AddCommGroup P] [AddCommGroup Q] (F : ℤ → Type*)
    [∀ d, AddCommGroup (F d)] {d d' : ℤ} (h : d = d') (f : P →+ Q →+ F d) (f' : P →+ Q →+ F d')
    (hf : HEq f f') (x : P) (y : Q) : HEq (f x y) (f' x y) := by
  subst h
  cases hf
  rfl

/-- A right differential graded module whose underlying complex is `M[k]` and whose action is that
of `M` read in the shifted degree, in the form of
`AlgebraicGeometry.SheafOfModules.dgAction_shift`: the action on a local section is the action of
`M` on the same section. -/
theorem mul_heq_of_shift {M N : DifferentialGradedModule.{u, u, u} A} (k : ℤ)
    (hc : N.complex = M.complex⟦k⟧)
    (hact : ∀ (p q : ℤ) (U : X.Cᵒᵖ), HEq ((N.mul p q).app U) ((M.mul (p + k) q).app U))
    (p q : ℤ) (U : X.Cᵒᵖ) (x : (N.complex.X p).val.obj U) (x' : (M.complex.X (p + k)).val.obj U)
    (y : (A.complex.X q).val.obj U) (hx : HEq x x') :
    HEq ((N.mul p q).app U x y) ((M.mul (p + k) q).app U x' y) := by
  obtain ⟨Nc, Nmul, h₁, h₂, h₃⟩ := N
  dsimp only at hc hact x hx ⊢
  subst hc
  obtain rfl := eq_of_heq hx
  exact heq_addMonoidHom₂_apply (fun d => (M.complex.X d).val.obj U)
    (show p + q + k = p + k + q by omega) _ _ (hact p q U) x y

/-- **The action on the translate `M[k]` is that of `M`, read in the shifted degree**, on local
sections. -/
theorem shiftedModule_mul_heq (M : DifferentialGradedModule.{u, u, u} A) (k p q : ℤ)
    (U : X.Cᵒᵖ) (x : ((shiftedModule A M k).complex.X p).val.obj U)
    (x' : (M.complex.X (p + k)).val.obj U) (y : (A.complex.X q).val.obj U) (hx : HEq x x') :
    HEq (((shiftedModule A M k).mul p q).app U x y) ((M.mul (p + k) q).app U x' y) := by
  refine mul_heq_of_shift A k (HomotopyCategory.shiftFunctor_obj_complex A k M) (fun p q U => ?_)
    p q U x x' y hx
  have e : shiftedModule A M k = asModule A ((dgShiftFunctor.{u, u, u} A k).obj (asObject A M)) :=
    congrArg (fun Y => Y.as) (HomotopyCategory.shiftFunctor_obj_eq A k M)
  have key : ∀ (N : DifferentialGradedModule.{u, u, u} A)
      (_ : N = asModule A ((dgShiftFunctor.{u, u, u} A k).obj (asObject A M))),
      HEq ((N.mul p q).app U) ((M.mul (p + k) q).app U) := fun N hN => by
    subst hN
    exact dgShiftFunctor_action A k M p q U
  exact key _ e

end SheafOfModules.DifferentialGradedModule

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}
  (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf A))

/-- `shiftCohomologyIsoR` is `shiftCohomologyIso`, as `shiftBridge` is the identity. -/
private theorem shiftCohomologyIsoR_hom_eq {S : RingedSpace.{u, u}}
    (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (n m k : ℤ) (h : n + m = k) :
    (shiftCohomologyIsoR (S := S) K n m k h).hom = (shiftCohomologyIso (S := S) K n m k h).hom := by
  have hb : (shiftBridge (S := S) K n).hom = 𝟙 _ := by
    ext k
    rfl
  have e : (shiftCohomologyIsoR (S := S) K n m k h).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
        ((baseSections S).map (DerivedCategory.Q.map (shiftBridge (S := S) K n).hom)) ≫
        (shiftCohomologyIso (S := S) K n m k h).hom := rfl
  refine e.trans ((congrArg (· ≫ _) ((congrArg (fun f =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
      ((baseSections S).map (DerivedCategory.Q.map f))) hb).trans
        (homology_map_Q_id _ _))).trans (Category.id_comp _))

/-- **The two identifications `Hᵐ(X, 𝒜[n]) ≅ Hⁿ⁺ᵐ(X, 𝒜)` agree**: `dgaShiftHomologyIso`, the
commutation of `RΓ(X, -)` on `D(A)` with the translation, preceded by the commutation of the
localization with the translation, is the identification `shiftCohomologyIsoR` of the cup product
of Section 0FKU. -/
theorem homology_map_commShiftIso_dgaShiftHomologyIso (n m k : ℤ) (h : n + m = k) :
    (DerivedCategory.homologyFunctor _ m).map ((derivedSectionsBase A).map
      ((DerivedCategory.Q.commShiftIso n).hom.app 𝒜.complex)) ≫
        (dgaShiftHomologyIso 𝒜 n m k h).hom =
      (shiftCohomologyIsoR (S := baseRingedSpace A) 𝒜.complex n m k h).hom := by
  refine Eq.trans ?_ (shiftCohomologyIsoR_hom_eq (S := baseRingedSpace A) _ n m k h).symm
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Functor.map_comp _ _ _).symm)

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

section Generic

variable {S : RingedSpace.{u, u}}
  (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf S.sheaf))

/-- The algebra of `cohomologyModuleMap_regularHom`, with every object and morphism a variable. -/
theorem regularHom_paste {C : Type*} [Category* C] {P P' Q₀ R₀ R₁ R₂ W₀ W₁ Q₁' : C}
    (L : P ⟶ P') (x : P' ⟶ Q₀) (c : Q₀ ⟶ R₀) (lh : R₀ ⟶ R₁) (η : P ⟶ W₀) (E : W₀ ⟶ R₁)
    (li : R₁ ⟶ R₀) (t : R₀ ⟶ R₂) (act : R₂ ⟶ W₁) (z : P' ⟶ Q₁') (c' : Q₁' ⟶ R₂) {mx : R₁ ⟶ W₁}
    (h₁ : η ≫ E = L ≫ x ≫ c ≫ lh) (h₂ : mx = li ≫ t ≫ act) (h₃ : lh ≫ li = 𝟙 _)
    (h₄ : L ≫ x ≫ c ≫ t = L ≫ z ≫ c') : (η ≫ E) ≫ mx = L ≫ z ≫ c' ≫ act := by
  rw [h₁, h₂]
  simp only [Category.assoc]
  rw [reassoc_of% h₃]
  simp only [← Category.assoc] at h₄ ⊢
  rw [h₄]

/-- `totalCupPairing_naturality'` for a map in the first factor only. -/
private theorem totalCupPairing_naturality_id_right {K K' M : CochainComplex
    (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} (f : K ⟶ K') (i j : ℤ)
    (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫ totalCupPairing K M i j ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          ((baseSections S).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f
            (𝟙 M) (sheafTensor S.sheaf) (ComplexShape.up ℤ)))) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((ξ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
          ((baseSections S).map (DerivedCategory.Q.map f))) ⊗ₘ η) ≫ totalCupPairing K' M i j := by
  simpa only [homology_map_Q_id, Category.comp_id] using
    totalCupPairing_naturality' (S := S) f (𝟙 M) i j ξ η

/-- **A map of right differential graded modules out of the regular module, on cohomology.** For
`x : 𝒜 ⟶ N`, the map `x` induces on `Hᵐ` sends `η` to the cup product of the class of `x(1)` with
`η`, followed by the action `Tot(N ⊗ 𝒜) ⟶ N`. Classes are families parametrized by the free module
of rank one, and `0 + m` is identified with `m`. -/
theorem cohomologyMap_regularHom
    {N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜}
    (x : _root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜 ⟶ N) (m : ℤ)
    (η : (ModuleCat.of (baseRing S) (baseRing S)) ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj 𝒜.complex) m) :
    η ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map (DerivedCategory.Q.map (x.toHomologicalComplex))) ≫
        eqToHom (congrArg (cohomologyModule (S := S) (DerivedCategory.Q.obj N.complex))
          (zero_add m).symm) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ((globalCycleClass (unitCycleHom S) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map
            (DerivedCategory.Q.map ((dgUnitComplexHom 𝒜 ≫ x.toHomologicalComplex))))) ⊗ₘ η) ≫
        totalCupPairing (S := S) N.complex 𝒜.complex 0 m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map ((dgAction N)))) := by
  have hunit := totalCupPairing_unit_left (S := S) 𝒜.complex m η
  have hx := dgAction_regularHom_eq 𝒜 x
  have e1 : η ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map (DerivedCategory.Q.map (x.toHomologicalComplex))) ≫
      eqToHom (congrArg (cohomologyModule (S := S) (DerivedCategory.Q.obj N.complex))
        (zero_add m).symm) =
      (η ≫ eqToHom (congrArg (cohomologyModule (S := S)
        (DerivedCategory.Q.obj 𝒜.complex)) (zero_add m).symm)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map (x.toHomologicalComplex))) :=
    (congrArg (η ≫ ·) (eqToHom_comp_cohomologyModule_map
      (DerivedCategory.Q.map x.toHomologicalComplex)
      (zero_add m).symm).symm).trans (Category.assoc _ _ _).symm
  have e2 : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map (x.toHomologicalComplex))) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map
            (DerivedCategory.Q.map ((unitTensorLeftIso (S := S) 𝒜.complex).inv))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map ((HomologicalComplex.mapBifunctorMap
          (dgUnitComplexHom 𝒜 ≫ x.toHomologicalComplex) (𝟙 𝒜.complex) (sheafTensor S.sheaf)
          (ComplexShape.up ℤ))))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map ((dgAction N)))) :=
    (congrArg (fun f => (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map (f)))) hx).trans
      ((homology_map_Q_comp _ _ _).trans (congrArg (_ ≫ ·) (homology_map_Q_comp _ _ _)))
  have hlu : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map
            (DerivedCategory.Q.map ((unitTensorLeftIso (S := S) 𝒜.complex).hom))) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map
            (DerivedCategory.Q.map ((unitTensorLeftIso (S := S) 𝒜.complex).inv))) = 𝟙 _ :=
    (homology_map_Q_comp _ _ _).symm.trans ((congrArg (fun f =>
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map (f))))
      (Iso.hom_inv_id _)).trans (homology_map_Q_id _ _))
  have n₂ := totalCupPairing_naturality_id_right (S := S) (M := 𝒜.complex)
    (dgUnitComplexHom 𝒜 ≫ x.toHomologicalComplex) 0 m (globalCycleClass (unitCycleHom S)) η
  exact e1.trans (regularHom_paste _ _ _ _ _ _ _ _ _ _ _ hunit.symm e2 hlu n₂)

/-- The pasting behind `totalCupPairing_dgAction_shift`, with every object and morphism a
variable. -/
theorem shift_paste {C : Type*} [Category* C] {P P' Q R₀ R₁ R₂ W₁ W₂ W₃ Q' : C}
    (L : P ⟶ P') (y : P' ⟶ Q) (c : Q ⟶ R₀) (s₁ : R₀ ⟶ R₁) (a : R₁ ⟶ R₂) (e : R₂ ⟶ W₁)
    (σ : W₁ ⟶ W₂) (σ' : R₂ ⟶ W₂) (σT : R₁ ⟶ W₃) (a' : W₃ ⟶ W₂) (y' : P' ⟶ Q') (c' : Q' ⟶ W₃)
    {A : R₀ ⟶ R₂} (hA : A = s₁ ≫ a)
    (h₁ : e ≫ σ = σ') (h₂ : a ≫ σ' = σT ≫ a') (h₃ : L ≫ y ≫ c ≫ s₁ ≫ σT = L ≫ y' ≫ c') :
    (L ≫ y ≫ c ≫ A) ≫ e ≫ σ = L ≫ y' ≫ c' ≫ a' := by
  subst hA
  simp only [Category.assoc]
  rw [h₁, h₂]
  simp only [← Category.assoc] at h₃ ⊢
  rw [h₃]

/-- Moving the degree of `shiftCohomologyIsoR` along an equality of degrees. -/
theorem eqToHom_comp_shiftCohomologyIsoR
    (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (n : ℤ)
    {a b : ℤ} (e : a = b) (c : ℤ) (h : n + b = c) :
    eqToHom (congrArg (cohomologyModule (S := S) (DerivedCategory.Q.obj (shiftR K n))) e) ≫
        (shiftCohomologyIsoR K n b c h).hom = (shiftCohomologyIsoR K n a c (e ▸ h)).hom := by
  subst e
  exact Category.id_comp _

/-- `totalCupPairing_dgAction_shift` with the action of the translate a variable. -/
theorem totalCupPairing_dgAction_shift_aux (h𝒜 : ∃ k : ℤ, 𝒜.complex.IsStrictlyGE k) (n m : ℤ)
    (act : HomologicalComplex.mapBifunctor (𝒜.complex⟦n⟧) 𝒜.complex (sheafTensor S.sheaf)
      (ComplexShape.up ℤ) ⟶ 𝒜.complex⟦n⟧)
    (hact : act = (CochainComplex.mapBifunctorShift₁Iso 𝒜.complex 𝒜.complex (sheafTensor S.sheaf)
      n).hom ≫ (dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))⟦n⟧')
    (y₀ : (ModuleCat.of (baseRing S) (baseRing S)) ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj (𝒜.complex⟦n⟧)) 0)
    (η : (ModuleCat.of (baseRing S) (baseRing S)) ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj 𝒜.complex) m) :
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (y₀ ⊗ₘ η) ≫
        totalCupPairing (S := S) (𝒜.complex⟦n⟧) 𝒜.complex 0 m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map ((act))))) ≫
        eqToHom (congrArg (cohomologyModule (S := S) (DerivedCategory.Q.obj (𝒜.complex⟦n⟧)))
          (zero_add m)) ≫
        (shiftCohomologyIsoR (S := S) 𝒜.complex n m (n + m) rfl).hom =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((y₀ ≫ (shiftCohomologyIsoR (S := S) 𝒜.complex n 0 n (add_zero n)).hom) ⊗ₘ η) ≫
        totalCupPairing (S := S) 𝒜.complex 𝒜.complex n m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (n + m)).map
          ((baseSections S).map (DerivedCategory.Q.map
            ((dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))))) := by
  subst hact
  exact shift_paste _ _ _ _ _ _ _ _ _ _ _ _ (homology_map_Q_comp _ _ _)
    (eqToHom_comp_shiftCohomologyIsoR 𝒜.complex n (zero_add m) (n + m) rfl)
    (shiftCohomologyIsoR_naturality _ n (0 + m) (n + m) (by omega))
    (totalCupPairing_shift₁_of_eq 𝒜.complex 𝒜.complex h𝒜 h𝒜 n 0 n m (add_zero n) y₀ η)

/-- **The action on a translate and the cup product.** Let `N` be a right differential graded
`𝒜`-module whose underlying complex is `𝒜[n]`, with the action of `𝒜` on itself read in the shifted
degree (as for the translate of Differential Graded Sheaves, Section 0FRY). For classes
`y ∈ H⁰(X, N)` and `η ∈ Hᵐ(X, 𝒜)`, the cup product of `y` and `η` followed by the action of `N`,
read in `Hⁿ⁺ᵐ(X, 𝒜)` through `Hᵐ(X, 𝒜[n]) = Hⁿ⁺ᵐ(X, 𝒜)`, is the cup product of `y`, read in
`Hⁿ(X, 𝒜)`, with `η`, followed by the multiplication of `𝒜`. There is no sign. -/
theorem totalCupPairing_dgAction_shift (h𝒜 : ∃ k : ℤ, 𝒜.complex.IsStrictlyGE k) (n m : ℤ)
    (N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜) (hN : N.complex = 𝒜.complex⟦n⟧)
    (hmul : ∀ (p q : ℤ) (U : (Opens S.carrier)ᵒᵖ) (x : (N.complex.X p).val.obj U)
      (x' : (𝒜.complex.X (p + n)).val.obj U) (y : (𝒜.complex.X q).val.obj U), HEq x x' →
        HEq ((N.mul p q).app U x y)
          (((_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜).mul (p + n) q).app U
            x' y))
    (y₀ : (ModuleCat.of (baseRing S) (baseRing S)) ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj N.complex) 0)
    (η : (ModuleCat.of (baseRing S) (baseRing S)) ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj 𝒜.complex) m) :
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (y₀ ⊗ₘ η) ≫
        totalCupPairing (S := S) N.complex 𝒜.complex 0 m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map ((dgAction N))))) ≫
        eqToHom (congrArg (cohomologyModule (S := S) (DerivedCategory.Q.obj N.complex))
          (zero_add m)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
          ((baseSections S).map (eqToHom (congrArg DerivedCategory.Q.obj hN))) ≫
        (shiftCohomologyIsoR (S := S) 𝒜.complex n m (n + m) rfl).hom =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((y₀ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) 0).map
          ((baseSections S).map (eqToHom (congrArg DerivedCategory.Q.obj hN))) ≫
          (shiftCohomologyIsoR (S := S) 𝒜.complex n 0 n (add_zero n)).hom) ⊗ₘ η) ≫
        totalCupPairing (S := S) 𝒜.complex 𝒜.complex n m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (n + m)).map
          ((baseSections S).map (DerivedCategory.Q.map
            ((dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))))) := by
  obtain ⟨Nc, Nmul, h₁, h₂, h₃⟩ := N
  dsimp only at hN hmul y₀ ⊢
  subst hN
  have hact := dgAction_shift (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n
    ⟨_, Nmul, h₁, h₂, h₃⟩ rfl hmul
  simp only at hact
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  exact totalCupPairing_dgAction_shift_aux 𝒜 h𝒜 n m _ hact y₀ η

/-- The pasting behind `totalCupPairing_dgAction_naturality`, with every object and morphism a
variable. -/
theorem action_naturality_paste {C : Type*} [Category* C] {P P' Q R₀ R₁ W₀ W₁ Q' : C}
    (L : P ⟶ P') (x : P' ⟶ Q) (c : Q ⟶ R₀) (t : R₀ ⟶ R₁) (aN : R₁ ⟶ W₁) (aM : R₀ ⟶ W₀)
    (f : W₀ ⟶ W₁) (x' : P' ⟶ Q') (c' : Q' ⟶ R₁) (h₁ : L ≫ x ≫ c ≫ t = L ≫ x' ≫ c')
    (h₂ : t ≫ aN = aM ≫ f) : L ≫ x' ≫ c' ≫ aN = L ≫ x ≫ c ≫ aM ≫ f := by
  simp only [← Category.assoc] at h₁ ⊢
  rw [← h₁]
  simp only [Category.assoc]
  rw [h₂]

/-- **The action and the cup product are natural along maps of right differential graded
modules.** For `f : M ⟶ N`, `u ∈ Hᵃ(X, M)` and `v ∈ Hᵇ(X, 𝒜)`, the cup product of `f(u)` with `v`
followed by the action of `N` is `f` of the cup product of `u` with `v` followed by the action of
`M`. -/
theorem totalCupPairing_dgAction_naturality
    {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜} (f : M ⟶ N) (a b : ℤ)
    (u : (ModuleCat.of (baseRing S) (baseRing S)) ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj M.complex) a)
    (v : (ModuleCat.of (baseRing S) (baseRing S)) ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj 𝒜.complex) b) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((u ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (a)).map
          ((baseSections S).map (DerivedCategory.Q.map ((f.toHomologicalComplex))))) ⊗ₘ v) ≫
        totalCupPairing (S := S) N.complex 𝒜.complex a b ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (a + b)).map
          ((baseSections S).map (DerivedCategory.Q.map ((dgAction N)))) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (u ⊗ₘ v) ≫
        totalCupPairing (S := S) M.complex 𝒜.complex a b ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (a + b)).map
          ((baseSections S).map (DerivedCategory.Q.map ((dgAction M)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (a + b)).map
          ((baseSections S).map (DerivedCategory.Q.map ((f.toHomologicalComplex)))) := by
  have n₂ := totalCupPairing_naturality_id_right (S := S) (M := 𝒜.complex)
    f.toHomologicalComplex a b u v
  have hn := dgAction_naturality f
  exact action_naturality_paste _ _ _ _ _ _ _ _ _ n₂ ((homology_map_Q_comp _ _ _).symm.trans
    ((congrArg (fun g => (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (a + b)).map
          ((baseSections S).map (DerivedCategory.Q.map (g)))) hn).trans
      (homology_map_Q_comp _ _ _)))

/-- **The two identifications `Hᵐ(X, K[n]) ≅ Hⁿ⁺ᵐ(X, K)` agree**: the commutation of `RΓ(X, -)` on
`D(𝒪_X)` with the translation, preceded by the commutation of the localization with the
translation, is the identification `shiftCohomologyIsoR` of the cup product of Section 0FKU. -/
theorem homology_map_commShiftIso_shiftHomologyIsoU
    (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (n m k : ℤ) (h : n + m = k) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map (((DerivedCategory.Q.commShiftIso n).hom.app K))) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU (baseSections S)
          (DerivedCategory.Q.obj K) n m k h).hom =
      (shiftCohomologyIsoR (S := S) K n m k h).hom := by
  refine Eq.trans ?_ (shiftCohomologyIsoR_hom_eq _ n m k h).symm
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Functor.map_comp _ _ _).symm)

/-- `Hᵏ(RΓ(X, -))` of a composite of morphisms of `D(𝒪_X)`. -/
theorem homology_map_comp_D (k : ℤ)
    {K L M : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing S))}
    (f : K ⟶ L) (g : L ⟶ M) : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (k)).map
          ((baseSections S).map ((f ≫ g))) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (k)).map
          ((baseSections S).map ((f))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (k)).map
          ((baseSections S).map ((g))) := by
  rw [Functor.map_comp, Functor.map_comp]

/-- A morphism into `K[n]` which is `Φ` followed by the commutation with the translation induces
the same map on `Hᵏ` as `Φ`, through the two identifications of `Hᵏ(K[n])` with `Hⁿ⁺ᵏ(K)`. -/
private theorem homology_map_shiftHomologyIsoU_of_eq
    (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (n k k' : ℤ) (h : n + k = k')
    {Z : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing S))}
    (F : Z ⟶ (DerivedCategory.Q.obj K)⟦n⟧) (Φ : Z ⟶ DerivedCategory.Q.obj (K⟦n⟧))
    (hF : F = Φ ≫ (DerivedCategory.Q.commShiftIso n).hom.app K) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
          ((baseSections S).map F) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU (baseSections S)
          (DerivedCategory.Q.obj K) n k k' h).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
          ((baseSections S).map Φ) ≫ (shiftCohomologyIsoR (S := S) K n k k' h).hom := by
  subst hF
  refine (congrArg (· ≫ _) ((congrArg (DerivedCategory.homologyFunctor _ k).map
    ((baseSections S).map_comp _ _)).trans (Functor.map_comp _ _ _))).trans ?_
  exact (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (homology_map_commShiftIso_shiftHomologyIsoU K n k k' h))

/-- The step of `roof_cup` moving the quasi-isomorphism across the cup product, with every object
and morphism a variable. -/
theorem star_paste {C : Type*} [Category* C] {P W₀ W₁ W₂ W₃ W₄ P' Q R : C} (η : P ⟶ W₀)
    (Φ : W₀ ⟶ W₁) (E : W₁ ⟶ W₂) (Hb : W₂ ⟶ W₃) (Hb' : W₁ ⟶ W₄) (E' : W₄ ⟶ W₃) (L : P ⟶ P')
    (x : P' ⟶ Q) (c : Q ⟶ R) (a : R ⟶ W₂) (X : P ⟶ W₃) {X₀ : W₀ ⟶ W₄}
    (heq : E ≫ Hb = Hb' ≫ E') (hB : η ≫ X₀ ≫ E' = X) (hX₀ : X₀ = Φ ≫ Hb')
    (hN : X = L ≫ x ≫ c ≫ a ≫ Hb) :
    (η ≫ Φ ≫ E) ≫ Hb = (L ≫ x ≫ c ≫ a) ≫ Hb := by
  subst hX₀
  simp only [Category.assoc] at hB ⊢
  rw [heq, hB, hN]

/-- The cancellation behind `roof_cup`, with every object and morphism a variable. -/
theorem roof_cup_paste {C : Type*} [Category* C] {P W₀ W₁ W₂ W₃ : C} (η : P ⟶ W₀)
    (φ : W₀ ⟶ W₁) (E : W₁ ⟶ W₂) (E' : W₂ ⟶ W₁) (σ : W₁ ⟶ W₃) (X : P ⟶ W₂) (Y : P ⟶ W₃)
    (hE : E ≫ E' = 𝟙 _) (h₁ : η ≫ φ ≫ E = X) (h₂ : X ≫ E' ≫ σ = Y) : η ≫ φ ≫ σ = Y := by
  rw [← h₂, ← h₁]
  simp only [Category.assoc]
  rw [reassoc_of% hE]

/-- **A roof acts on cohomology by cup product with its value at `1`.** Let `F : 𝒜 ⟶ 𝒜[n]` be a
morphism of `D(𝒪_X)` such that `F` followed by a quasi-isomorphism `b : N ⟶ I` of right
differential graded modules, out of a module `N` whose underlying complex is `𝒜[n]` with the
shifted action, is a map `x : 𝒜 ⟶ I` of right differential graded modules. Then `F` sends
`η ∈ Hᵐ(X, 𝒜)` to the cup product of `F(1) ∈ Hⁿ(X, 𝒜)` with `η`, followed by the multiplication of
`𝒜`. -/
theorem roof_cup (h𝒜 : ∃ k : ℤ, 𝒜.complex.IsStrictlyGE k) (n m : ℤ)
    (F : DerivedCategory.Q.obj 𝒜.complex ⟶ (DerivedCategory.Q.obj 𝒜.complex)⟦n⟧)
    {I N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜}
    (x : _root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜 ⟶ I) (b : N ⟶ I)
    (hb : QuasiIso b.toHomologicalComplex) (hN : N.complex = 𝒜.complex⟦n⟧)
    (hmul : ∀ (p q : ℤ) (U : (Opens S.carrier)ᵒᵖ) (x : (N.complex.X p).val.obj U)
      (x' : (𝒜.complex.X (p + n)).val.obj U) (y : (𝒜.complex.X q).val.obj U), HEq x x' →
        HEq ((N.mul p q).app U x y)
          (((_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜).mul (p + n) q).app U
            x' y))
    (hroof : F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex ≫
      eqToHom (congrArg DerivedCategory.Q.obj hN.symm) ≫
      DerivedCategory.Q.map b.toHomologicalComplex =
        DerivedCategory.Q.map x.toHomologicalComplex)
    (η : (ModuleCat.of (baseRing S) (baseRing S)) ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj 𝒜.complex) m) :
    η ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map ((F))) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU (baseSections S)
          (DerivedCategory.Q.obj 𝒜.complex) n m (n + m) rfl).hom =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ((globalCycleClass (unitCycleHom S) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((DerivedCategory.Q.map (dgUnitComplexHom 𝒜) ≫ F))) ≫
          (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU (baseSections S)
            (DerivedCategory.Q.obj 𝒜.complex) n 0 n (add_zero n)).hom) ⊗ₘ η) ≫
        totalCupPairing (S := S) 𝒜.complex 𝒜.complex n m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (n + m)).map
          ((baseSections S).map (DerivedCategory.Q.map
            ((dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))))) := by
  obtain ⟨Nc, Nmul, h₁, h₂, h₃⟩ := N
  dsimp only at hN hmul b hb hroof ⊢
  subst hN
  simp only [eqToHom_refl, Category.id_comp] at hroof
  let Φ := F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex
  have hact := dgAction_shift (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n
    ⟨_, Nmul, h₁, h₂, h₃⟩ rfl hmul
  simp only at hact
  have hQx : DerivedCategory.Q.map x.toHomologicalComplex =
      Φ ≫ DerivedCategory.Q.map b.toHomologicalComplex :=
    hroof.symm.trans (Category.assoc _ _ _).symm
  have hxm : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map (DerivedCategory.Q.map ((x.toHomologicalComplex)))) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map ((Φ))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map (DerivedCategory.Q.map ((b.toHomologicalComplex)))) := by
    exact (congrArg (fun f => (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map ((f)))) hQx).trans (homology_map_comp_D _ _ _)
  have hux : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map
            (DerivedCategory.Q.map ((dgUnitComplexHom 𝒜 ≫ x.toHomologicalComplex)))) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((DerivedCategory.Q.map (dgUnitComplexHom 𝒜) ≫ Φ))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map (DerivedCategory.Q.map ((b.toHomologicalComplex)))) := by
    exact (congrArg (fun f => (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((f)))) ((DerivedCategory.Q.map_comp _ _).trans
      ((congrArg (_ ≫ ·) hQx).trans (Category.assoc _ _ _).symm))).trans
        (homology_map_comp_D _ _ _)
  have hB := cohomologyMap_regularHom 𝒜 x m η
  simp only [hux] at hB
  have hN2 := totalCupPairing_dgAction_naturality 𝒜 b 0 m
    (globalCycleClass (unitCycleHom S) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((DerivedCategory.Q.map (dgUnitComplexHom 𝒜) ≫ Φ)))) η
  have heq := eqToHom_comp_cohomologyModule_map (S := S)
    (DerivedCategory.Q.map b.toHomologicalComplex) (zero_add m).symm
  have hQb : IsIso (DerivedCategory.Q.map b.toHomologicalComplex) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hb
  have hRb : IsIso ((baseSections S).map (DerivedCategory.Q.map b.toHomologicalComplex)) :=
    (Functor.mapIso (baseSections S)
      (@asIso _ _ _ _ (DerivedCategory.Q.map b.toHomologicalComplex) hQb)).isIso_hom
  have hHb : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map ((b.toHomologicalComplex))))) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).mapIso
      (@asIso _ _ _ _ ((baseSections S).map (DerivedCategory.Q.map b.toHomologicalComplex))
        hRb)).isIso_hom
  have hstar : η ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map ((Φ))) ≫ eqToHom (congrArg (cohomologyModule (S := S)
        (DerivedCategory.Q.obj (𝒜.complex⟦n⟧))) (zero_add m).symm) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ((globalCycleClass (unitCycleHom S) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((DerivedCategory.Q.map (dgUnitComplexHom 𝒜) ≫ Φ)))) ⊗ₘ η) ≫
        totalCupPairing (S := S) (𝒜.complex⟦n⟧) 𝒜.complex 0 m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + m)).map
          ((baseSections S).map (DerivedCategory.Q.map ((dgAction ⟨_, Nmul, h₁, h₂, h₃⟩)))) := by
    refine (@cancel_mono _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hHb) _ _).1 ?_
    simp only [Category.assoc] at hN2
    exact star_paste _ _ _ _ _ _ _ _ _ _ _ heq hB hxm hN2
  have aux := totalCupPairing_dgAction_shift_aux 𝒜 h𝒜 n m (dgAction ⟨_, Nmul, h₁, h₂, h₃⟩) hact
    (globalCycleClass (unitCycleHom S) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((DerivedCategory.Q.map (dgUnitComplexHom 𝒜) ≫ Φ)))) η
  have hF : F = Φ ≫ (DerivedCategory.Q.commShiftIso n).hom.app 𝒜.complex :=
    ((Category.comp_id F).symm.trans (congrArg (F ≫ ·)
      (Iso.inv_hom_id_app (DerivedCategory.Q.commShiftIso n) 𝒜.complex).symm)).trans
      (Category.assoc _ _ _).symm
  have P1 := homology_map_shiftHomologyIsoU_of_eq 𝒜.complex n m (n + m) rfl F Φ hF
  have P2 : globalCycleClass (unitCycleHom S) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((DerivedCategory.Q.map (dgUnitComplexHom 𝒜) ≫ F))) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU (baseSections S)
          (DerivedCategory.Q.obj 𝒜.complex) n 0 n (add_zero n)).hom =
      (globalCycleClass (unitCycleHom S) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((DerivedCategory.Q.map (dgUnitComplexHom 𝒜) ≫ Φ)))) ≫
        (shiftCohomologyIsoR (S := S) 𝒜.complex n 0 n (add_zero n)).hom := by
    exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      ((congrArg (globalCycleClass (unitCycleHom S) ≫ ·)
        (homology_map_shiftHomologyIsoU_of_eq 𝒜.complex n 0 n (add_zero n) _
          (DerivedCategory.Q.map (dgUnitComplexHom 𝒜) ≫ Φ) ((congrArg (_ ≫ ·) hF).trans
            (Category.assoc _ _ _).symm))).trans (Category.assoc _ _ _).symm)
  refine (congrArg (η ≫ ·) P1).trans (Eq.trans ?_
    (congrArg (fun t => (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (t ⊗ₘ η) ≫ _) P2.symm))
  exact roof_cup_paste _ _ _ _ _ _ _ ((eqToHom_trans _ _).trans (eqToHom_refl _ _)) hstar aux

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- The translation functors of `D(𝒜, d)`. -/
noncomputable local instance :
    HasShift (_root_.SheafOfModules.DifferentialGradedModule.derivedCategory.{u, u, u} 𝒜) ℤ :=
  _root_.SheafOfModules.DifferentialGradedModule.derivedCategoryHasShift
    (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **A morphism `𝒜 ⟶ 𝒜[n]` of `D(𝒜, d)` acts on cohomology by cup product with its value at
`1`.** For `g : 𝒜 ⟶ 𝒜[n]` in `D(𝒜, d)` with underlying morphism `g'` of `D(𝒪_X)`, and
`η ∈ Hᵐ(X, 𝒜)`, the image of `η` under `g'`, read in `Hⁿ⁺ᵐ(X, 𝒜)`, is the cup product of
`g'(1) ∈ Hⁿ(X, 𝒜)` with `η`, followed by the multiplication of `𝒜`. -/
theorem derivedForgetShiftedHom_cup (h𝒜 : ∃ k : ℤ, 𝒜.complex.IsStrictlyGE k) (n m : ℤ)
    (g : (_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u} 𝒜).obj
        ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient 𝒜).obj
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)) ⟶
      ((_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u} 𝒜).obj
        ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient 𝒜).obj
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)))⟦n⟧)
    (η : (ModuleCat.of (baseRing S) (baseRing S)) ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj 𝒜.complex) m) :
    η ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (m)).map
          ((baseSections S).map
            ((_root_.SheafOfModules.DifferentialGradedModule.derivedForgetShiftedHom
              (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜
              (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n g))) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU (baseSections S)
          (DerivedCategory.Q.obj 𝒜.complex) n m (n + m) rfl).hom =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ((globalCycleClass (unitCycleHom S) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((DerivedCategory.Q.map (dgUnitComplexHom 𝒜) ≫
            _root_.SheafOfModules.DifferentialGradedModule.derivedForgetShiftedHom
              (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜
              (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n g))) ≫
          (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU (baseSections S)
            (DerivedCategory.Q.obj 𝒜.complex) n 0 n (add_zero n)).hom) ⊗ₘ η) ≫
        totalCupPairing (S := S) 𝒜.complex 𝒜.complex n m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (n + m)).map
          ((baseSections S).map (DerivedCategory.Q.map
            ((dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))))) := by
  obtain ⟨I, x, b, hb, hroof⟩ :=
    _root_.SheafOfModules.DifferentialGradedModule.exists_derivedForgetShiftedHom_comp_eq
      (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜 n g
  exact roof_cup 𝒜 h𝒜 n m _ x b hb
    (_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.shiftFunctor_obj_complex
      (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜 n
      (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))
    (fun p q U x x' y hx => _root_.SheafOfModules.DifferentialGradedModule.shiftedModule_mul_heq
      (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜
      (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n p q U x x' y hx)
    hroof η

/-- The value at `1` of the class of `1` followed by `Hᵏ` of two composable morphisms of `D(𝒪_X)`
and an identification. -/
theorem globalCycleClass_unitCycleHom_comp_apply
    {K L : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing S))}
    (f : DerivedCategory.Q.obj (unitComplexR S) ⟶ K) (g : K ⟶ L) {T : ModuleCat.{u} (baseRing S)}
    (σ : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) 0).obj
      ((baseSections S).obj L) ⟶ T) :
    (globalCycleClass (unitCycleHom S) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((f ≫ g))) ≫ σ).hom 1 =
      σ.hom (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((g)))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((f)))).hom (unitCycleClass S 0))) := by
  refine (congrArg σ.hom (ConcreteCategory.congr_hom
    ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) 0).map
      ((baseSections S).map_comp f g)).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) 0).map_comp _ _))
    ((globalCycleClass (unitCycleHom S)).hom 1))).trans ?_
  exact congrArg (fun t => σ.hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((g)))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0)).map
          ((baseSections S).map ((f)))).hom t)))
    (congrArg (globalClass (unitComplex S 0) 0) (one_smul _ _))

end Generic

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

open scoped TensorProduct

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **Stacks Project, Tag 0FU7, property (3).** The morphism `ξ' : Ω^• ⟶ Ω^•[n]` attached to
`ξ ∈ H^n_{dR}(X/S)` sends `η ∈ H^m_{dR}(X/S)` to `ξ ∪ η ∈ H^{n + m}_{dR}(X/S)`: the map `ξ'`
induces on `H^m(X, -)`, read through `H^m(X, Ω^•[n]) = H^{n + m}_{dR}(X/S)`, is left cup product
with `ξ` (the cup product of Tag 0FM3). -/
@[stacks 0FU7 "property (3): the morphism xi' sends eta in H^m_dR to the cup product xi cup eta in
  H^{n+m}_dR, read through H^m(X, Omega^bullet[n]) = H^{n+m}_dR"]
theorem deRhamCohomologyCup_eq_deRhamClassMorphism (n m : ℤ) (ξ : deRhamCohomology B D n)
    (η : deRhamCohomology B D m) :
    deRhamCohomologyCup B D n m ξ η =
      (deRhamShiftHomologyIso B D n m (n + m) rfl).hom
        ((DerivedCategory.homologyFunctor _ m).map
          ((derivedSectionsBase A).map (deRhamClassMorphism B D n ξ)) η) := by
  let 𝒜 := deRhamDifferentialGradedAlgebra B D
  have G1 := ConcreteCategory.congr_hom
    (derivedForgetShiftedHom_cup (S := baseRingedSpace A) 𝒜
      ⟨0, isStrictlyGE_deRhamComplexInt B D⟩ n m
      (deRhamClassDerivedEquiv B D n ξ)
      (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (deRhamCohomologyToModule B D m η)))) 1
  have hcup : deRhamCohomologyCup B D n m ξ η =
      (totalCupPairing (S := baseRingedSpace A) (deRhamComplexInt (X := X) (A := A) (φ := φ) B D)
        (deRhamComplexInt (X := X) (A := A) (φ := φ) B D) n m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) (n + m)).map
          ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map
            ((dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)))))).hom
          (deRhamCohomologyToModule B D n ξ ⊗ₜ deRhamCohomologyToModule B D m η) := by
    rw [dgAction_regular_deRham]
    exact congrArg
      (fun f => f.hom (deRhamCohomologyToModule B D n ξ ⊗ₜ deRhamCohomologyToModule B D m η))
      (canonicalPairingModule_eq (wedgeProduct B D) n m)
  have hξ := (globalCycleClass_unitCycleHom_comp_apply (S := baseRingedSpace A)
    (DerivedCategory.Q.map (dgUnitComplexHom 𝒜)) (deRhamClassMorphism B D n ξ)
    (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU (baseSections (baseRingedSpace A))
      (DerivedCategory.Q.obj 𝒜.complex) n 0 n (add_zero n)).hom).trans
    (deRhamEvalOne_deRhamClassMorphism B D n ξ)
  have hη : (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing (baseRingedSpace A)) _
      (deRhamCohomologyToModule B D m η))).hom 1 = deRhamCohomologyToModule B D m η :=
    one_smul _ _
  refine hcup.trans (Eq.trans ?_ (G1.symm.trans ?_))
  · exact congrArg₂ (fun s t => (totalCupPairing (S := baseRingedSpace A)
        (deRhamComplexInt (X := X) (A := A) (φ := φ) B D)
        (deRhamComplexInt (X := X) (A := A) (φ := φ) B D) n m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) (n + m)).map
          ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map
            (dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))))).hom
          (s ⊗ₜ t)) hξ.symm hη.symm
  · exact congrArg (fun t => (deRhamShiftHomologyIso B D n m (n + m) rfl).hom.hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) (m)).map
          ((baseSections (baseRingedSpace A)).map ((deRhamClassMorphism B D n ξ)))).hom t)) hη

end AlgebraicGeometry.SheafOfModules

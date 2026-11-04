module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.Statements
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealLattice

/-!
# Closed subspaces from a compatible tower, given Grothendieck's existence theorem

In Situation 08B7 (`A` Noetherian and `I`-adically complete, `X` separated of finite type over
`V = Spec A`), let `Z_n ⊆ X_n = X ×_V Spec (A / Iⁿ)` be closed subspaces with
`Z_n = Z_{n+1} ∩ X_n` and `Z_1` proper over `V`.  Stacks 08BG produces a closed subspace
`Z ⊆ X`, proper over `V`, with `Z ∩ X_n = Z_n`.  This file proves it from Grothendieck's
existence theorem (Stacks 08BE) and full faithfulness of completion (Stacks 08B9), taken as the
propositions `AlgebraicGeometry.Space.CompletionProperOverIsEquivalence` and
`AlgebraicGeometry.Space.CompletionBijectiveOnHoms`; nothing is registered here.

## Main definitions

* `AlgebraicGeometry.Space.towerSystem`: the inverse system `(𝒪_X / 𝓘_{Z_{k+1}})_k`.
* `AlgebraicGeometry.Space.towerProjection`: the projections `𝒪_X^∧ ⟶ (𝒪_X / 𝓘_{Z_{k+1}})_k`.

## Main results

* `AlgebraicGeometry.Space.isCoherentAdicSystem_towerSystem`: the tower is an object of
  `Coh(X, I 𝒪_X)`, and `hasProperSupport_cokernel_definingIdealSheaf` gives its support
  condition.
* `AlgebraicGeometry.Space.ker_comp_cokernel_π_idealPowerMultiple`: for an epimorphism
  `a : M ⟶ N`, the kernel of `M ⟶ N / 𝓘ⁿ N` is `ker a + 𝓘ⁿ M`.
* `AlgebraicGeometry.Space.closedSubspaceTowerAlgebraizes_of_existence`: **Stacks 08BG**, from
  Stacks 08BE and Stacks 08B9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

section Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The inclusion of a join of two submodules is killed by a morphism exactly when both
inclusions are. -/
theorem sup_ι_comp_eq_zero_iff {M N : Modules.{u, u} B S hS F hF} (P Q : M.Submodule)
    (g : M ⟶ N) : (P ⊔ Q).ι ≫ g = 0 ↔ P.ι ≫ g = 0 ∧ Q.ι ≫ g = 0 := by
  simp only [← le_ker_iff_ι_comp_eq_zero, sup_le_iff]

/-- The inclusion of a submodule is killed by the quotient map onto a larger quotient. -/
private theorem ι_comp_cokernel_π_eq_zero_of_le {M : Modules.{u, u} B S hS F hF}
    {P P' : M.Submodule} (h : P ≤ P') : P.ι ≫ cokernel.π P'.ι = 0 :=
  (le_ker_iff_ι_comp_eq_zero B S hS F hF P _).1 (h.trans (le_ker_cokernel_π_ι B S hS F hF P'))

/-- The projection `M / P ⟶ M / P'` for submodules `P ≤ P'`. -/
def submoduleQuotientMapOfLE {M : Modules.{u, u} B S hS F hF} {P P' : M.Submodule} (h : P ≤ P') :
    cokernel P.ι ⟶ cokernel P'.ι :=
  cokernel.desc _ (cokernel.π P'.ι)
    ((le_ker_iff_ι_comp_eq_zero B S hS F hF P _).1
      (h.trans (le_ker_cokernel_π_ι B S hS F hF P')))

/-- The projection `M / P ⟶ M / P'` commutes with the quotient maps from `M`. -/
@[reassoc (attr := simp)]
theorem π_submoduleQuotientMapOfLE {M : Modules.{u, u} B S hS F hF} {P P' : M.Submodule}
    (h : P ≤ P') : cokernel.π P.ι ≫ submoduleQuotientMapOfLE h = cokernel.π P'.ι :=
  cokernel.π_desc _ _ _

/-- The projection `M / P ⟶ M / P` is the identity. -/
theorem submoduleQuotientMapOfLE_refl {M : Modules.{u, u} B S hS F hF} {P : M.Submodule}
    (h : P ≤ P) : submoduleQuotientMapOfLE h = 𝟙 _ :=
  (cancel_epi (cokernel.π P.ι)).1 (by simp)

/-- The projections `M / P ⟶ M / P' ⟶ M / P''` compose to the projection `M / P ⟶ M / P''`. -/
theorem submoduleQuotientMapOfLE_comp {M : Modules.{u, u} B S hS F hF} {P P' P'' : M.Submodule}
    (h : P ≤ P') (h' : P' ≤ P'') :
    submoduleQuotientMapOfLE h ≫ submoduleQuotientMapOfLE h' =
      submoduleQuotientMapOfLE (h.trans h') :=
  (cancel_epi (cokernel.π P.ι)).1 (by simp)

/-- The projection `M / P ⟶ M / P'` is an epimorphism. -/
instance {M : Modules.{u, u} B S hS F hF} {P P' : M.Submodule} (h : P ≤ P') :
    Epi (submoduleQuotientMapOfLE h) :=
  epi_of_epi_fac (π_submoduleQuotientMapOfLE h)

/-- The kernel of a composite contains the kernel of the first factor. -/
theorem submoduleKer_le_ker_comp {M N T : Modules.{u, u} B S hS F hF} (g : M ⟶ N) (h : N ⟶ T) :
    SheafOfModules.Submodule.ker g ≤ SheafOfModules.Submodule.ker (g ≫ h) := by
  intro U x hx
  refine (SheafOfModules.Submodule.mem_ker _ U x).2 ?_
  change h.val.app U (g.val.app U x) = 0
  rw [(SheafOfModules.Submodule.mem_ker g U x).1 hx, map_zero]

/-- The kernel of a composite with a split monomorphism is the kernel of the first factor. -/
theorem submoduleKer_comp_of_comp_eq_id {M N T : Modules.{u, u} B S hS F hF} (g : M ⟶ N) (h : N ⟶ T)
    (h' : T ⟶ N) (hh : h ≫ h' = 𝟙 N) :
    SheafOfModules.Submodule.ker (g ≫ h) = SheafOfModules.Submodule.ker g := by
  refine le_antisymm (fun U x hx => ?_) (submoduleKer_le_ker_comp g h)
  refine (SheafOfModules.Submodule.mem_ker _ U x).2 ?_
  have h1 : h'.val.app U (h.val.app U (g.val.app U x)) = g.val.app U x :=
    congrArg (fun φ : N ⟶ N => φ.val.app U (g.val.app U x)) hh
  have h2 : h.val.app U (g.val.app U x) = 0 := (SheafOfModules.Submodule.mem_ker _ U x).1 hx
  rw [← h1, h2, map_zero]

/-- The map `M / A ⟶ M / P` induced by the quotient map onto `M / P` is an epimorphism. -/
instance epi_cokernel_desc_cokernel_π {M : Modules.{u, u} B S hS F hF} (A P : M.Submodule)
    (h : A.ι ≫ cokernel.π P.ι = 0) : Epi (cokernel.desc A.ι (cokernel.π P.ι) h) :=
  epi_of_epi_fac (cokernel.π_desc _ _ _)

variable (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- A morphism carries `𝓘ᵏ M` into `𝓘ᵏ N`: a morphism killing `𝓘ᵏ N` kills the image of `𝓘ᵏ M`. -/
theorem idealPowerMultiple_ι_comp_comp_eq_zero_of_hom (k : ℕ) {M N T : Modules.{u, u} B S hS F hF}
    (p : M ⟶ N) (g : N ⟶ T) (h : (idealPowerMultiple B S hS F hF 𝓘 k N).ι ≫ g = 0) :
    (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫ p ≫ g = 0 := by
  have h' := (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k g).1 h
  refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k (p ≫ g)).2 fun U r hr x => ?_
  change g.val.app (op U) (p.val.app (op U) (r • x)) = 0
  rw [show p.val.app (op U) (r • x) = r • p.val.app (op U) x from
    (p.val.app (op U)).hom.map_smul r x]
  exact h' U r hr _

/-- `𝓘ᵏ` annihilates a quotient `Q` of `M` as soon as the projection kills `𝓘ᵏ M`. -/
theorem idealPowerMultiple_eq_bot_of_epi (k : ℕ) {M Q : Modules.{u, u} B S hS F hF}
    (π : M ⟶ Q) [Epi π] (h : (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫ π = 0) :
    idealPowerMultiple B S hS F hF 𝓘 k Q = ⊥ := by
  refine (submodule_ι_eq_zero_iff B S hS F hF _).1 ?_
  have h' := idealPowerMultiple_ι_comp_eq_zero_of_epi B S hS F hF 𝓘 k π (𝟙 Q)
    (by rwa [Category.comp_id])
  rwa [Category.comp_id] at h'

/-- **The kernel of `M ⟶ N ⟶ N / 𝓘ⁿ N`** for an epimorphism `M ⟶ N` is `ker + 𝓘ⁿ M`. -/
theorem ker_comp_cokernel_π_idealPowerMultiple {M N : Modules.{u, u} B S hS F hF} (a : M ⟶ N)
    [Epi a] (n : ℕ) :
    SheafOfModules.Submodule.ker (a ≫ cokernel.π (idealPowerMultiple B S hS F hF 𝓘 n N).ι) =
      SheafOfModules.Submodule.ker a ⊔ idealPowerMultiple B S hS F hF 𝓘 n M := by
  set P := SheafOfModules.Submodule.ker a ⊔ idealPowerMultiple B S hS F hF 𝓘 n M with hP
  refine le_antisymm ?_ (sup_le (submoduleKer_le_ker_comp _ _) ?_)
  · have hkP : (SheafOfModules.Submodule.ker a).ι ≫ cokernel.π P.ι = 0 :=
      ι_comp_cokernel_π_eq_zero_of_le le_sup_left
    have hz : kernel.ι a ≫ cokernel.π P.ι = 0 := by
      rw [← SheafOfModules.Submodule.kerIsoKernel_hom_comp_ι a] at hkP
      have := congrArg (fun φ => (SheafOfModules.Submodule.kerIsoKernel a).inv ≫ φ) hkP
      simpa using this
    have hg₁ : a ≫ Abelian.epiDesc a (cokernel.π P.ι) hz = cokernel.π P.ι :=
      Abelian.comp_epiDesc _ _ _
    have h2 : (idealPowerMultiple B S hS F hF 𝓘 n N).ι ≫ Abelian.epiDesc a (cokernel.π P.ι) hz =
        0 := by
      refine idealPowerMultiple_ι_comp_eq_zero_of_epi B S hS F hF 𝓘 n a _ ?_
      rw [hg₁]
      exact ι_comp_cokernel_π_eq_zero_of_le le_sup_right
    calc SheafOfModules.Submodule.ker (a ≫ cokernel.π (idealPowerMultiple B S hS F hF 𝓘 n N).ι)
        ≤ SheafOfModules.Submodule.ker ((a ≫ cokernel.π (idealPowerMultiple B S hS F hF 𝓘 n N).ι)
          ≫ cokernel.desc _ _ h2) := submoduleKer_le_ker_comp _ _
      _ = P := by rw [Category.assoc, cokernel.π_desc, hg₁, ker_cokernel_π_ι]
  · exact (le_ker_iff_ι_comp_eq_zero B S hS F hF _ _).2
      (idealPowerMultiple_ι_comp_comp_eq_zero_of_hom _ n _ _ (cokernel.condition _))

end Generic

section Subspaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)

/-- The annihilator of a module `N` lies in the kernel of every map `𝒪_X ⟶ N`. -/
theorem annihilatorIdealSheaf_le_ker {N : Modules.{u, u} B S hS X.1 X.2}
    (a : structureSheafModule B S hS X ⟶ N) :
    annihilatorIdealSheaf B S hS X N ≤ SheafOfModules.Submodule.ker a := by
  intro U r hr
  refine (SheafOfModules.Submodule.mem_ker a U r).2 ?_
  let one : (structureSheafModule B S hS X).val.obj U :=
    (1 : ToType ((structureRingSheaf B S hS X).obj.obj U))
  have h1 := hr U (𝟙 U) (a.val.app U one)
  have h0 := congrArg (fun φ => (RingCat.Hom.hom φ) r)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map_id U)
  let R := ToType
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U)
  let r' : R := r
  let : Module R ((structureSheafModule B S hS X).val.obj U) :=
    ((structureSheafModule B S hS X).val.obj U).isModule
  have h2 : r = r' • one := (mul_one r').symm
  rw [h2, (a.val.app U).hom.map_smul]
  convert h1 using 2
  exact h0.symm

/-- **Properness of closed subspaces is monotone in the defining ideal.** -/
theorem isProper_of_definingIdealSheaf_le {Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (hg : IsLocallyOfFiniteType B S hS g.hom) (Z Z' : ClosedSubspaces B S hS X.1)
    (h : definingIdealSheaf B S hS X Z' ≤ definingIdealSheaf B S hS X Z)
    (hZ' : IsProper B S hS (Z'.1.ι ≫ g.hom)) : IsProper B S hS (Z.1.ι ≫ g.hom) := by
  have hsub : Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ⊆
      Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι) := by
    rw [range_pointsMap_ι_eq_idealZeroLocus B S hS X Z,
      range_pointsMap_ι_eq_idealZeroLocus B S hS X Z']
    exact idealZeroLocus_antitone B S hS X h
  have hcl := isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 Z.1.ι Z.2.2
  have hp := isProperOver_of_subset B S hS X.2 Y.2 g.hom hg _ _ hcl
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 Z'.1.ι Z'.2.2) hsub
    (isProperOver_range_pointsMap_of_isProper B S hS X Y g.hom hg Z' hZ')
  exact (exists_isProper_closedSubspace_iff_forall B S hS X.2 Y.2 g.hom hg _ hcl).1
    ((isProper_reducedClosedSubspace_iff_exists B S hS X.2 Y.2 g.hom hg _ hcl).1 hp) Z.1 Z.2 rfl

end Subspaces

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ schemeSpace V)

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- `(I 𝒪_X)ⁿ 𝒪_X` is the ideal of the thickening `X_n = X ×_V Spec (A / Iⁿ)`. -/
theorem idealPowerMultiple_structureSheafModule_eq_definingIdealSheaf (n : ℕ) :
    idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) n
        (structureSheafModule B S hS X) =
      definingIdealSheaf B S hS X (thickeningSubspace V I f n) := by
  rw [idealPowerMultiple_idealKernel_eq_ker, definingIdealSheaf_fibreThickening]
  rfl

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- In a compatible tower `Z_n = Z_{n+1} ∩ X_n` the closed subspaces increase. -/
theorem towerSubspace_mono (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZeq : ∀ n, 1 ≤ n → (Z n).1 = (Z (n + 1)).1 ⊓ (thickeningSubspace V I f n).1)
    {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) : (Z m).1 ≤ (Z n).1 := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact ih.trans ((hZeq n (hm.trans hmn)).le.trans inf_le_left)

/-- **The inverse system `(𝒪_X / 𝓘_{Z_{k+1}})_k`** of the structure sheaves of a compatible tower
of closed subspaces, zero-indexed. -/
def towerSystem (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZeq : ∀ n, 1 ≤ n → (Z n).1 = (Z (n + 1)).1 ⊓ (thickeningSubspace V I f n).1) :
    ℕᵒᵖ ⥤ Modules.{u, u} B S hS X.1 X.2 where
  obj k := cokernel (definingIdealSheaf B S hS X (Z (k.unop + 1))).ι
  map {_k _l} h := submoduleQuotientMapOfLE (definingIdealSheaf_antitone B S hS X _ _
    (towerSubspace_mono V I f Z hZeq (Nat.le_add_left 1 _)
      (Nat.add_le_add_right (leOfHom h.unop) 1)))
  map_id _ := submoduleQuotientMapOfLE_refl _
  map_comp _ _ := (submoduleQuotientMapOfLE_comp _ _).symm

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- `(I 𝒪_X)ⁿ 𝒪_X` lies in the ideal of `Z_n` when `Z_n ⊆ X_n`. -/
theorem idealPowerMultiple_le_definingIdealSheaf_of_le (Z : ClosedSubspaces B S hS X.1) (n : ℕ)
    (hZ : Z.1 ≤ (thickeningSubspace V I f n).1) :
    idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) n
        (structureSheafModule B S hS X) ≤ definingIdealSheaf B S hS X Z :=
  (idealPowerMultiple_structureSheafModule_eq_definingIdealSheaf V I f n).le.trans
    (definingIdealSheaf_antitone B S hS X Z _ hZ)

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- `(I 𝒪_X)ⁿ` annihilates `𝒪_X / 𝓘_Z` when `Z ⊆ X_n`. -/
theorem idealPowerMultiple_cokernel_definingIdealSheaf_eq_bot (Z : ClosedSubspaces B S hS X.1)
    (n : ℕ) (hZ : Z.1 ≤ (thickeningSubspace V I f n).1) :
    idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) n
        (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι) = ⊥ := by
  have h0 : (idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) n
      (structureSheafModule B S hS X)).ι ≫
        cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι = 0 :=
    ι_comp_cokernel_π_eq_zero_of_le (idealPowerMultiple_le_definingIdealSheaf_of_le V I f Z n hZ)
  have : Epi (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι) :=
    coequalizer.π_epi
  exact idealPowerMultiple_eq_bot_of_epi _ n
    (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι) h0

/-- **The quotient of `𝒪_X / 𝓘_P` by `(I 𝒪_X)ⁿ` is `𝒪_X / 𝓘_Q`** when `𝓘_Q = 𝓘_P ⊔ (I 𝒪_X)ⁿ 𝒪_X`,
compatibly with the projections. -/
def idealPowerQuotientCokernelIso (n : ℕ) (P Q : (structureSheafModule B S hS X).Submodule)
    (hPQ : Q = P ⊔ idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) n
        (structureSheafModule B S hS X)) :
    idealPowerQuotient B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) n
        (cokernel (C := Modules.{u, u} B S hS X.1 X.2) P.ι) ≅
      cokernel (C := Modules.{u, u} B S hS X.1 X.2) Q.ι where
  hom := cokernel.desc _ (submoduleQuotientMapOfLE (hPQ ▸ le_sup_left)) (by
    refine idealPowerMultiple_ι_comp_eq_zero_of_epi B S hS X.1 X.2 _ n
      (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) P.ι) _ ?_
    rw [π_submoduleQuotientMapOfLE]
    exact (le_ker_iff_ι_comp_eq_zero B S hS X.1 X.2 _ _).1
      ((hPQ ▸ le_sup_right).trans (le_ker_cokernel_π_ι B S hS X.1 X.2 _)))
  inv := cokernel.desc _ (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) P.ι ≫
      cokernel.π (idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) n
        (cokernel (C := Modules.{u, u} B S hS X.1 X.2) P.ι)).ι) (by
    subst hPQ
    refine (sup_ι_comp_eq_zero_iff _ _ _).2 ⟨?_, ?_⟩
    · rw [← Category.assoc, cokernel.condition, zero_comp]
    · exact idealPowerMultiple_ι_comp_comp_eq_zero_of_hom _ n _ _ (cokernel.condition _))
  hom_inv_id := by
    refine (cancel_epi (cokernel.π _)).1 ?_
    refine (cancel_epi (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) P.ι)).1 ?_
    simp
  inv_hom_id := by
    refine (cancel_epi (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) Q.ι)).1 ?_
    simp

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- Precomposed with the quotient map from `𝒪_X / P`, `idealPowerQuotientCokernelIso` is the
projection `𝒪_X / P ⟶ 𝒪_X / Q`. -/
@[reassoc (attr := simp)]
theorem π_idealPowerQuotientCokernelIso_hom (n : ℕ)
    (P Q : (structureSheafModule B S hS X).Submodule)
    (hPQ : Q = P ⊔ idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) n
        (structureSheafModule B S hS X)) :
    cokernel.π _ ≫ (idealPowerQuotientCokernelIso V I f n P Q hPQ).hom =
      submoduleQuotientMapOfLE (hPQ ▸ le_sup_left) :=
  cokernel.π_desc _ _ _

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- In a compatible tower, `𝓘_{Z_n} = 𝓘_{Z_{n+1}} ⊔ (I 𝒪_X)ⁿ 𝒪_X`. -/
theorem definingIdealSheaf_tower_eq_sup (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZeq : ∀ n, 1 ≤ n → (Z n).1 = (Z (n + 1)).1 ⊓ (thickeningSubspace V I f n).1)
    (n : ℕ) (hn : 1 ≤ n) :
    definingIdealSheaf B S hS X (Z n) = definingIdealSheaf B S hS X (Z (n + 1)) ⊔
      idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) n
        (structureSheafModule B S hS X) := by
  have hZ : Z n = schemeTheoreticIntersection B S hS X.1 X.2 (Z (n + 1))
      (thickeningSubspace V I f n) := Subtype.ext (hZeq n hn)
  rw [hZ, definingIdealSheaf_schemeTheoreticIntersection,
    idealPowerMultiple_structureSheafModule_eq_definingIdealSheaf]

/-- `𝒪_X / 𝓘_Z` is coherent for every closed subspace `Z`. -/
private theorem isCoherent_cokernel_definingIdealSheaf (hft : IsLocallyOfFiniteType B S hS f.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    IsCoherent B S hS X.1 X.2
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι) := by
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_schemeSpace V f hft
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T)) := ⟨hN⟩
  exact isCoherent_cokernel B S hS X.1 X.2
    (isCoherent_quasicoherentIdeal B S hS X hN
      ⟨_, isQuasicoherentOnSite_definingIdealSheaf B S hS X Z⟩)
    (isCoherent_structureSheaf B S hS X.1 X.2) _

/-- **The tower `(𝒪_X / 𝓘_{Z_{k+1}})_k` is a coherent adic system along `I 𝒪_X`.** -/
theorem isCoherentAdicSystem_towerSystem (hft : IsLocallyOfFiniteType B S hS f.hom)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZle : ∀ n, 1 ≤ n → (Z n).1 ≤ (thickeningSubspace V I f n).1)
    (hZeq : ∀ n, 1 ≤ n → (Z n).1 = (Z (n + 1)).1 ⊓ (thickeningSubspace V I f n).1) :
    IsCoherentAdicSystem B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I)
      (towerSystem V I f Z hZeq) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · exact isCoherent_cokernel_definingIdealSheaf V f hft _
  · exact idealPowerMultiple_cokernel_definingIdealSheaf_eq_bot V I f _ _ (hZle _ (by omega))
  · refine ⟨idealPowerQuotientCokernelIso V I f (n + 1) _ _
      (definingIdealSheaf_tower_eq_sup V I f Z hZeq (n + 1) (by omega)), ?_⟩
    exact π_idealPowerQuotientCokernelIso_hom V I f (n + 1) _ _ _

/-- **`𝒪_X / 𝓘_Z` has support proper over `V`** when `Z` is proper over `V`: it is the direct
image of `𝒪_Z`, so its support lies in `|Z|`. -/
theorem hasProperSupport_cokernel_definingIdealSheaf (hft : IsLocallyOfFiniteType B S hS f.hom)
    (Z : ClosedSubspaces B S hS X.1)
    (hZp : IsProper B S hS (subspaceInclusion B S hS X Z ≫ f).hom) :
    HasProperSupport B S hS X.2 (schemeSpace V).2 f.hom hft
      ((SheafOfModules.toSheaf _).obj
        (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι)) := by
  have hcoh := isCoherent_cokernel_definingIdealSheaf V f hft Z
  have : SheafOfModules.IsCoherentOnSite
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι) :=
    hcoh.toIsCoherentOnSite
  have : SheafOfModules.IsFiniteTypeOnSite
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι) :=
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS X _
  have hcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2
    (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι)
  refine ⟨hcl, isProperOver_of_subset B S hS X.2 (schemeSpace V).2 f.hom hft _ _ hcl
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 Z.1.ι Z.2.2)
    (supportOfSheaf_subset_range_pointsMap_of_annihilatedByKerIdeal B S hS X _ Z
      (annihilatedByKerIdeal_of_essImage_modulePushforward B S hS
        (closedSubspaceInclusion B S hS X Z)
        ⟨_, ⟨(cokernelIsoPushforwardOfDefiningIdealSheafEq Z _ rfl).symm⟩⟩))
    (isProperOver_range_pointsMap_of_isProper B S hS X (schemeSpace V) f.hom hft Z hZp)⟩

/-- The projections `𝒪_X / (I 𝒪_X)^{k+1} ⟶ 𝒪_X / 𝓘_{Z_{k+1}}`, a morphism from the completion of
`𝒪_X` to the tower. -/
def towerProjection (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZle : ∀ n, 1 ≤ n → (Z n).1 ≤ (thickeningSubspace V I f n).1)
    (hZeq : ∀ n, 1 ≤ n → (Z n).1 = (Z (n + 1)).1 ⊓ (thickeningSubspace V I f n).1) :
    adicQuotientSystem B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I)
        (structureSheafModule B S hS X) ⟶ towerSystem V I f Z hZeq where
  app k := cokernel.desc (idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I)
      (k.unop + 1) (structureSheafModule B S hS X)).ι
      (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2)
        (definingIdealSheaf B S hS X (Z (k.unop + 1))).ι)
    ((le_ker_iff_ι_comp_eq_zero B S hS X.1 X.2 _ _).1
      ((idealPowerMultiple_le_definingIdealSheaf_of_le V I f _ _ (hZle _ (by omega))).trans
        (le_ker_cokernel_π_ι B S hS X.1 X.2 _)))
  naturality {k l} h := by
    refine (cancel_epi (cokernel.π _)).1 ?_
    dsimp only [towerSystem, adicQuotientSystem]
    rw [← Category.assoc, π_comp_idealPowerQuotientMapOfLE]
    exact (cokernel.π_desc _ _ _).trans ((π_submoduleQuotientMapOfLE _).symm.trans
      ((congrArg (· ≫ submoduleQuotientMapOfLE _) (cokernel.π_desc _ _ _).symm).trans
        (Category.assoc _ _ _)))

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The `k`-th component of `towerProjection`, precomposed with the quotient map from the
structure sheaf, is the quotient map onto the structure sheaf of `Z (k + 1)`. -/
theorem π_towerProjection_app (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZle : ∀ n, 1 ≤ n → (Z n).1 ≤ (thickeningSubspace V I f n).1)
    (hZeq : ∀ n, 1 ≤ n → (Z n).1 = (Z (n + 1)).1 ⊓ (thickeningSubspace V I f n).1) (k : ℕ) :
    cokernel.π (idealPowerMultiple B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I)
      (k + 1) (structureSheafModule B S hS X)).ι ≫ (towerProjection V I f Z hZle hZeq).app (op k) =
      cokernel.π (C := Modules.{u, u} B S hS X.1 X.2)
        (definingIdealSheaf B S hS X (Z (k + 1))).ι :=
  cokernel.π_desc _ _ _

/-- Completion is bijective on morphisms into a coherent module with support proper over `V`,
given Stacks 08B9. -/
theorem completion_bijective_of_hasProperSupport (h08B9 : CompletionBijectiveOnHoms V I f)
    (hcomp : IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hsep : IsSeparated B S hS f.hom) (hft : IsFiniteType B S hS f.hom)
    (M N : CoherentModules.{u, u} B S hS X.1 X.2)
    (hN : HasProperSupport B S hS X.2 (schemeSpace V).2 f.hom hft.1
      ((SheafOfModules.toSheaf _).obj N.obj)) :
    Function.Bijective (fun a : M ⟶ N => (completionFunctorOver V I f hft.1).map a) := by
  obtain ⟨hNcl, hNp⟩ := hN
  have : SheafOfModules.IsCoherentOnSite M.obj := M.property.toIsCoherentOnSite
  have : SheafOfModules.IsFiniteTypeOnSite M.obj :=
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS X _
  have hMcl : IsClosed (coherentSupport M) :=
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 M.obj
  exact h08B9 hcomp hsep hft M N (hMcl.inter hNcl)
    (isProperOver_of_subset B S hS X.2 (schemeSpace V).2 f.hom hft.1 _ _ (hMcl.inter hNcl) hNcl
      Set.inter_subset_right hNp)

/-- **Stacks 08BG from Stacks 08BE and 08B9.** In Situation 08B7, a compatible tower of closed
subspaces `Z_n ⊆ X_n` with `Z_1` proper over `V` is the tower of thickenings of a closed subspace
`Z ⊆ X` proper over `V`.

The structure sheaves `𝒪_{Z_n}` form an object of `Coh_{support proper over A}(X, I 𝒪_X)`;
Grothendieck's existence theorem algebraizes it to a coherent `𝓕`, and full faithfulness lifts the
projections `𝒪_X^∧ ⟶ (𝒪_{Z_n})` to `a : 𝒪_X ⟶ 𝓕`.  Completion is faithful on morphisms into
modules with proper support, so `a` is surjective, and `Z = V(ker a)`. -/
theorem closedSubspaceTowerAlgebraizes_of_existence (h08B9 : CompletionBijectiveOnHoms V I f)
    (h08BE : CompletionProperOverIsEquivalence V I f) : ClosedSubspaceTowerAlgebraizes V I f := by
  intro hcomp hsep hft Z hZle hZeq hZ1
  have hN :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_schemeSpace V f hft.1
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T)) := ⟨hN⟩
  have := h08BE hcomp hsep hft
  let E : CoherentAdicSystems B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) :=
    ⟨towerSystem V I f Z hZeq, isCoherentAdicSystem_towerSystem V I f hft.1 Z hZle hZeq⟩
  let E' : CoherentAdicSystemsProperOver B S hS X.2 (schemeSpace V).2 f.hom hft.1
      (idealKernel (pullbackRingHom B V f) I) :=
    ⟨E, hasProperSupport_cokernel_definingIdealSheaf V f hft.1 (Z 1) hZ1⟩
  let M := (completionFunctorProperOverBase V I f hft.1).objPreimage E'
  let e := (completionFunctorProperOverBase V I f hft.1).objObjPreimageIso E'
  let O : CoherentModules.{u, u} B S hS X.1 X.2 :=
    ⟨structureSheafModule B S hS X, isCoherent_structureSheaf B S hS X.1 X.2⟩
  let q : (completionFunctorOver V I f hft.1).obj O ⟶ E :=
    ObjectProperty.homMk (towerProjection V I f Z hZle hZeq)
  have hq : Epi q := epi_of_epi_app_zero B S hS X.1 X.2 _ q
    (epi_cokernel_desc_cokernel_π _ _ _)
  have : IsIso e.inv.hom := (ObjectProperty.ι _).map_isIso e.inv
  obtain ⟨a, ha⟩ := (completion_bijective_of_hasProperSupport V I f h08B9 hcomp hsep hft O M.obj
    M.property).2 (q ≫ e.inv.hom)
  -- `a` is an epimorphism
  let C : CoherentModules.{u, u} B S hS X.1 X.2 :=
    ⟨cokernel a.hom, isCoherent_cokernel B S hS X.1 X.2 O.property M.obj.property a.hom⟩
  let p : M.obj ⟶ C := ObjectProperty.homMk (cokernel.π a.hom)
  have : SheafOfModules.IsCoherentOnSite M.obj.obj := M.obj.property.toIsCoherentOnSite
  have hMft : SheafOfModules.IsFiniteTypeOnSite M.obj.obj :=
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS X _
  have hC : HasProperSupport B S hS X.2 (schemeSpace V).2 f.hom hft.1
      ((SheafOfModules.toSheaf _).obj C.obj) :=
    hasProperSupport_of_epi B S hS X.2 (schemeSpace V).2 f.hom hft.1 (cokernel.π a.hom) hMft
      M.property
  have hap : a ≫ p = a ≫ 0 := ObjectProperty.hom_ext _ (by
    change a.hom ≫ cokernel.π a.hom = a.hom ≫ 0
    rw [cokernel.condition, comp_zero])
  have hp : p = 0 := by
    refine (completion_bijective_of_hasProperSupport V I f h08B9 hcomp hsep hft M.obj C hC).1 ?_
    have h1 := congrArg (fun φ => (completionFunctorOver V I f hft.1).map φ) hap
    simp only [Functor.map_comp, ha] at h1
    exact (cancel_epi e.inv.hom).1 ((cancel_epi q).1 h1)
  have : Epi a.hom := Abelian.epi_of_cokernel_π_eq_zero _
    (congrArg (fun φ : M.obj ⟶ C => φ.hom) hp)
  -- the closed subspace
  have hJk : (SheafOfModules.Submodule.ker a.hom).toSheafOfModules.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso (SheafOfModules.Submodule.kerIsoKernel a.hom).symm
      (isCoherent_kernel B S hS X.1 X.2 O.property M.obj.property a.hom).toIsQuasicoherentOnSite
  obtain ⟨Z', hZ'⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X
    (SheafOfModules.Submodule.ker a.hom) hJk
  refine ⟨Z', ?_, fun n hn => ?_⟩
  · -- properness, through the closed subspace carrying `M` given by Stacks 0CZI
    obtain ⟨Z'', G, -, -, hZ''p, ⟨eG⟩⟩ := ((hasProperSupport_tfae B S hS X (schemeSpace V) f.hom
      hft.1 M.obj.obj M.obj.property.toIsQuasicoherentOnSite hMft
      (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _ hMft)).out 1 3).1
      M.property
    have hann := annihilatedByKerIdeal_of_essImage_modulePushforward B S hS
      (closedSubspaceInclusion B S hS X Z'') ⟨G, ⟨eG⟩⟩
    have hle : definingIdealSheaf B S hS X Z'' ≤ definingIdealSheaf B S hS X Z' := by
      rw [hZ']
      exact (definingIdealSheaf_le_annihilatorIdealSheaf B S hS X _ Z'' hann).trans
        (annihilatorIdealSheaf_le_ker X a.hom)
    exact isProper_of_definingIdealSheaf_le X f hft.1 Z' Z'' hle hZ''p
  · -- the thickenings
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hlev : idealPowerQuotientMapOfHom B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I)
        (k + 1) a.hom = (towerProjection V I f Z hZle hZeq).app (op k) ≫
          e.inv.hom.hom.app (op k) :=
      congrArg (fun φ => φ.hom.app (op k)) ha
    have hcompa : a.hom ≫ cokernel.π (idealPowerMultiple B S hS X.1 X.2
        (idealKernel (pullbackRingHom B V f) I) (k + 1) M.obj.obj).ι =
        cokernel.π (C := Modules.{u, u} B S hS X.1 X.2)
          (definingIdealSheaf B S hS X (Z (k + 1))).ι ≫ e.inv.hom.hom.app (op k) :=
      ((π_comp_idealPowerQuotientMapOfHom _ _ _ _ _ _ _ _).symm.trans (congrArg _ hlev)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ e.inv.hom.hom.app (op k)) (π_towerProjection_app V I f Z hZle hZeq k)))
    have hinv : e.inv.hom.hom.app (op k) ≫ e.hom.hom.hom.app (op k) = 𝟙 _ :=
      congrArg (fun φ => φ.hom.hom.app (op k)) e.inv_hom_id
    have h1 : SheafOfModules.Submodule.ker (a.hom ≫ cokernel.π (idealPowerMultiple B S hS X.1 X.2
        (idealKernel (pullbackRingHom B V f) I) (k + 1) M.obj.obj).ι) =
        definingIdealSheaf B S hS X (Z (k + 1)) :=
      (congrArg SheafOfModules.Submodule.ker hcompa).trans
        ((submoduleKer_comp_of_comp_eq_id _ _ _ hinv).trans (ker_cokernel_π_ι B S hS X.1 X.2 _))
    have hker := ker_comp_cokernel_π_idealPowerMultiple (idealKernel (pullbackRingHom B V f) I)
      a.hom (k + 1)
    have h2 : definingIdealSheaf B S hS X (Z (k + 1)) = definingIdealSheaf B S hS X
        (schemeTheoreticIntersection B S hS X.1 X.2 Z' (thickeningSubspace V I f (k + 1))) := by
      rw [definingIdealSheaf_schemeTheoreticIntersection, hZ',
        ← idealPowerMultiple_structureSheafModule_eq_definingIdealSheaf]
      exact h1.symm.trans hker
    exact congrArg Subtype.val (definingIdealSheaf_injective B S hS X h2).symm

end Tower

end AlgebraicGeometry.Space

end

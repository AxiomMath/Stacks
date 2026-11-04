module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent

/-!
# The completion functor `Coh(𝒪_F) ⟶ Coh(F, 𝓘)` on an algebraic space

Let `F` be an algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a quasi-coherent sheaf of
ideals on its small étale ringed site. This file constructs the completion functor
`𝓖 ↦ 𝓖^∧ = (𝓖 / 𝓘 ^ (n + 1) 𝓖)_n` from coherent `𝒪_F`-modules to the category `Coh(F, 𝓘)` of
coherent `𝓘`-adic systems.

## Main definitions

* `AlgebraicGeometry.Space.idealPowerQuotientMapOfLE`: the projection
  `𝓖 / 𝓘 ^ l 𝓖 ⟶ 𝓖 / 𝓘 ^ k 𝓖` for `k ≤ l`, and the transition map of the system.
* `AlgebraicGeometry.Space.idealPowerQuotientMapOfHom`: the map `𝓖 / 𝓘 ^ k 𝓖 ⟶ 𝓗 / 𝓘 ^ k 𝓗`
  induced by a morphism `𝓖 ⟶ 𝓗`.
* `AlgebraicGeometry.Space.adicQuotientSystem`: the inverse system `(𝓖 / 𝓘 ^ (n + 1) 𝓖)_n`.
* `AlgebraicGeometry.Space.adicQuotientFunctor`: the completion along `𝓘`, as a functor to inverse
  systems of `𝒪_F`-modules.
* `AlgebraicGeometry.Space.idealPowerQuotientQuotientIso`: the isomorphism
  `(𝓖 / 𝓘 ^ l 𝓖) / 𝓘 ^ k (𝓖 / 𝓘 ^ l 𝓖) ≅ 𝓖 / 𝓘 ^ k 𝓖` for `k ≤ l`.
* `AlgebraicGeometry.Space.completionFunctor`: the functor `Coh(𝒪_F) ⟶ Coh(F, 𝓘)`.

## Main results

* `AlgebraicGeometry.Space.isPowAnnihilated_idealPowerQuotient` and
  `AlgebraicGeometry.Space.idealPowerMultiple_idealPowerQuotient_eq_bot`: `𝓘 ^ k` annihilates
  `𝓖 / 𝓘 ^ k 𝓖`, equivalently `𝓘 ^ k (𝓖 / 𝓘 ^ k 𝓖) = 0`.
* `AlgebraicGeometry.Space.isCoherentAdicSystem_adicQuotientSystem`: the completion of a
  coherent module is an object of `Coh(F, 𝓘)`.

## References

* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### The subsheaves `𝓘 ^ n M` decrease -/

/-- The subsheaves `𝓘 ^ n M` decrease as the exponent grows. -/
theorem idealPowerMultiple_antitone {k l : ℕ} (h : k ≤ l) (M : Modules.{u, u} B S hS F hF) :
    idealPowerMultiple B S hS F hF 𝓘 l M ≤ idealPowerMultiple B S hS F hF 𝓘 k M := by
  rw [idealPowerMultiple_le_iff]
  refine fun U => le_trans (Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl)
    (le_idealPowerMultiple_obj B S hS F hF 𝓘 k M U)

/-! ### The transition maps of the tower of quotients -/

/-- The projection `M / 𝓘 ^ l M ⟶ M / 𝓘 ^ k M` for `k ≤ l`. -/
def idealPowerQuotientMapOfLE {k l : ℕ} (h : k ≤ l) (M : Modules.{u, u} B S hS F hF) :
    idealPowerQuotient B S hS F hF 𝓘 l M ⟶ idealPowerQuotient B S hS F hF 𝓘 k M :=
  cokernel.desc _ (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι) (by
    rw [← Stacks.SheafOfModules.Submodule.homOfLE_comp_ι
      (idealPowerMultiple_antitone B S hS F hF 𝓘 h M), Category.assoc, cokernel.condition,
      comp_zero])

/-- The projection `M / 𝓘 ^ l M ⟶ M / 𝓘 ^ k M` is compatible with the quotient projections out
of `M`. -/
@[simp]
theorem π_comp_idealPowerQuotientMapOfLE {k l : ℕ} (h : k ≤ l)
    (M : Modules.{u, u} B S hS F hF) :
    cokernel.π (idealPowerMultiple B S hS F hF 𝓘 l M).ι ≫
        idealPowerQuotientMapOfLE B S hS F hF 𝓘 h M =
      cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι :=
  cokernel.π_desc _ _ _

/-- The projection of `M / 𝓘 ^ k M` onto itself is the identity. -/
theorem idealPowerQuotientMapOfLE_refl {k : ℕ} (h : k ≤ k)
    (M : Modules.{u, u} B S hS F hF) :
    idealPowerQuotientMapOfLE B S hS F hF 𝓘 h M = 𝟙 _ := by
  apply (cancel_epi (cokernel.π _)).mp
  rw [π_comp_idealPowerQuotientMapOfLE, Category.comp_id]

/-- The projections of the tower of quotients compose. -/
theorem idealPowerQuotientMapOfLE_comp {j k l : ℕ} (h₁ : j ≤ k) (h₂ : k ≤ l)
    (M : Modules.{u, u} B S hS F hF) :
    idealPowerQuotientMapOfLE B S hS F hF 𝓘 h₂ M ≫
        idealPowerQuotientMapOfLE B S hS F hF 𝓘 h₁ M =
      idealPowerQuotientMapOfLE B S hS F hF 𝓘 (h₁.trans h₂) M := by
  apply (cancel_epi (cokernel.π _)).mp
  rw [← Category.assoc, π_comp_idealPowerQuotientMapOfLE,
    π_comp_idealPowerQuotientMapOfLE, π_comp_idealPowerQuotientMapOfLE]

/-- The inverse system `(M / 𝓘 ^ (n + 1) M)_n` of `𝒪_F`-modules, the completion of `M` along `𝓘`,
with the projections of the tower of quotients as transition maps. -/
def adicQuotientSystem (M : Modules.{u, u} B S hS F hF) :
    ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF where
  obj n := idealPowerQuotient B S hS F hF 𝓘 (n.unop + 1) M
  map {_ _} f := idealPowerQuotientMapOfLE B S hS F hF 𝓘
    (Nat.add_le_add_right (leOfHom f.unop) 1) M
  map_id _ := idealPowerQuotientMapOfLE_refl B S hS F hF 𝓘 _ M
  map_comp _ _ := (idealPowerQuotientMapOfLE_comp B S hS F hF 𝓘 _ _ M).symm

/-- The transition map of the system `(M / 𝓘 ^ (n + 1) M)_n` is the projection of the tower. -/
theorem adicQuotientSystem_map (M : Modules.{u, u} B S hS F hF) {i j : ℕ} (h : j ≤ i) :
    (adicQuotientSystem B S hS F hF 𝓘 M).map (homOfLE h).op =
      idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right h 1) M :=
  rfl

/-! ### `𝓘 ^ k` annihilates `M / 𝓘 ^ k M` -/

/-- The ideal `𝓘 ^ k` annihilates `M / 𝓘 ^ k M`. -/
theorem isPowAnnihilated_idealPowerQuotient (k : ℕ) (M : Modules.{u, u} B S hS F hF) :
    IsPowAnnihilated B S hS F hF 𝓘 k (idealPowerQuotient B S hS F hF 𝓘 k M) := by
  have hz : cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫
      cokernel.π (powAnnihilator B S hS F hF 𝓘 k
        (idealPowerQuotient B S hS F hF 𝓘 k M)).ι = 0 := by
    ext X y
    show (cokernel.π (powAnnihilator B S hS F hF 𝓘 k
        (idealPowerQuotient B S hS F hF 𝓘 k M)).ι).val.app X
      ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app X y) = 0
    refine (cokernel_π_app_eq_zero_iff B S hS F hF _ X _).mpr ?_
    intro V g r hr
    have h1 : (idealPowerQuotient B S hS F hF 𝓘 k M).val.restrictₛₗ g
          ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app X y)
        = (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op V)
          (M.val.restrictₛₗ g y) :=
      (PresheafOfModules.naturality_apply
        (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val g y).symm
    have h2 : r • (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op V)
          (M.val.restrictₛₗ g y)
        = (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op V)
          (r • M.val.restrictₛₗ g y) :=
      (((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app
        (op V)).hom.map_smul r _).symm
    rw [h1, h2]
    refine (cokernel_π_app_eq_zero_iff B S hS F hF _ (op V) _).mpr ?_
    exact le_idealPowerMultiple_obj B S hS F hF 𝓘 k M V
      (Submodule.smul_mem_smul hr Submodule.mem_top)
  have h0 : cokernel.π (powAnnihilator B S hS F hF 𝓘 k
      (idealPowerQuotient B S hS F hF 𝓘 k M)).ι = 0 :=
    (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι)).mp
      (by rw [hz, comp_zero])
  refine isPowAnnihilated_of_mem_powAnnihilator B S hS F hF 𝓘 k _ fun U x => ?_
  refine (cokernel_π_app_eq_zero_iff B S hS F hF _ (op U) x).mp ?_
  rw [h0]
  rfl

/-- The submodule `𝓘 ^ k (M / 𝓘 ^ k M)` of `M / 𝓘 ^ k M` is zero. -/
theorem idealPowerMultiple_idealPowerQuotient_eq_bot (k : ℕ)
    (M : Modules.{u, u} B S hS F hF) :
    idealPowerMultiple B S hS F hF 𝓘 k (idealPowerQuotient B S hS F hF 𝓘 k M) = ⊥ :=
  (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k _).mpr
    (isPowAnnihilated_idealPowerQuotient B S hS F hF 𝓘 k M)

/-! ### The transition isomorphism -/

/-- For `k ≤ l`, the projection `M / 𝓘 ^ l M ⟶ M / 𝓘 ^ k M` vanishes on
`𝓘 ^ k (M / 𝓘 ^ l M)`. -/
theorem idealPowerMultiple_ι_comp_idealPowerQuotientMapOfLE {k l : ℕ} (h : k ≤ l)
    (M : Modules.{u, u} B S hS F hF) :
    (idealPowerMultiple B S hS F hF 𝓘 k
          (idealPowerQuotient B S hS F hF 𝓘 l M)).ι ≫
        idealPowerQuotientMapOfLE B S hS F hF 𝓘 h M = 0 := by
  refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k
    (idealPowerQuotientMapOfLE B S hS F hF 𝓘 h M)).mpr fun U r hr x => ?_
  rw [((idealPowerQuotientMapOfLE B S hS F hF 𝓘 h M).val.app (op U)).hom.map_smul r x]
  exact isPowAnnihilated_idealPowerQuotient B S hS F hF 𝓘 k M U r hr _

/-- The map `M / 𝓘 ^ k M ⟶ (M / 𝓘 ^ l M) / 𝓘 ^ k (M / 𝓘 ^ l M)` induced by the two quotient
projections. -/
def idealPowerQuotientQuotientInv (k l : ℕ) (M : Modules.{u, u} B S hS F hF) :
    idealPowerQuotient B S hS F hF 𝓘 k M ⟶
      idealPowerQuotient B S hS F hF 𝓘 k (idealPowerQuotient B S hS F hF 𝓘 l M) :=
  cokernel.desc _ (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 l M).ι ≫
      cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k
        (idealPowerQuotient B S hS F hF 𝓘 l M)).ι) (by
    refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k _).mpr fun U r x => ?_
    intro y
    change (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k
        (idealPowerQuotient B S hS F hF 𝓘 l M)).ι).val.app (op U)
      ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 l M).ι).val.app (op U) (r • y)) = 0
    rw [((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 l M).ι).val.app (op U)).hom.map_smul r y]
    refine (cokernel_π_app_eq_zero_iff B S hS F hF _ (op U) _).mpr ?_
    exact le_idealPowerMultiple_obj B S hS F hF 𝓘 k _ U
      (Submodule.smul_mem_smul x Submodule.mem_top))

/-- The comparison `M / 𝓘 ^ k M ⟶ (M / 𝓘 ^ l M) / 𝓘 ^ k (M / 𝓘 ^ l M)` is the composite of the
two quotient projections. -/
@[simp]
theorem π_comp_idealPowerQuotientQuotientInv (k l : ℕ) (M : Modules.{u, u} B S hS F hF) :
    cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫
        idealPowerQuotientQuotientInv B S hS F hF 𝓘 k l M =
      cokernel.π (idealPowerMultiple B S hS F hF 𝓘 l M).ι ≫
        cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k
          (idealPowerQuotient B S hS F hF 𝓘 l M)).ι :=
  cokernel.π_desc _ _ _

/-- The transition isomorphism `(M / 𝓘 ^ l M) / 𝓘 ^ k (M / 𝓘 ^ l M) ≅ M / 𝓘 ^ k M` for `k ≤ l`,
induced by the projection `M / 𝓘 ^ l M ⟶ M / 𝓘 ^ k M`. -/
def idealPowerQuotientQuotientIso {k l : ℕ} (h : k ≤ l) (M : Modules.{u, u} B S hS F hF) :
    idealPowerQuotient B S hS F hF 𝓘 k (idealPowerQuotient B S hS F hF 𝓘 l M) ≅
      idealPowerQuotient B S hS F hF 𝓘 k M where
  hom := cokernel.desc _ (idealPowerQuotientMapOfLE B S hS F hF 𝓘 h M)
    (idealPowerMultiple_ι_comp_idealPowerQuotientMapOfLE B S hS F hF 𝓘 h M)
  inv := idealPowerQuotientQuotientInv B S hS F hF 𝓘 k l M
  hom_inv_id := by
    refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k
      (idealPowerQuotient B S hS F hF 𝓘 l M)).ι)).mp ?_
    rw [← Category.assoc, cokernel.π_desc, Category.comp_id]
    refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 l M).ι)).mp ?_
    rw [← Category.assoc, π_comp_idealPowerQuotientMapOfLE]
    exact cokernel.π_desc _ _ _
  inv_hom_id := by
    refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι)).mp ?_
    rw [← Category.assoc, π_comp_idealPowerQuotientQuotientInv, Category.comp_id,
      Category.assoc, cokernel.π_desc, π_comp_idealPowerQuotientMapOfLE]

/-- The transition isomorphism intertwines the quotient projection with the transition map of the
system. -/
theorem π_comp_idealPowerQuotientQuotientIso_hom {k l : ℕ} (h : k ≤ l)
    (M : Modules.{u, u} B S hS F hF) :
    cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k
          (idealPowerQuotient B S hS F hF 𝓘 l M)).ι ≫
        (idealPowerQuotientQuotientIso B S hS F hF 𝓘 h M).hom =
      idealPowerQuotientMapOfLE B S hS F hF 𝓘 h M :=
  cokernel.π_desc _ _ _

/-! ### Functoriality in the module -/

/-- The map `M / 𝓘 ^ k M ⟶ N / 𝓘 ^ k N` induced by a morphism `M ⟶ N`. -/
def idealPowerQuotientMapOfHom (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N) :
    idealPowerQuotient B S hS F hF 𝓘 k M ⟶ idealPowerQuotient B S hS F hF 𝓘 k N :=
  cokernel.desc _ (f ≫ cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k N).ι) (by
    refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k _).mpr fun U r hr x => ?_
    change (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k N).ι).val.app (op U)
      (f.val.app (op U) (r • x)) = 0
    rw [(f.val.app (op U)).hom.map_smul r x]
    refine (cokernel_π_app_eq_zero_iff B S hS F hF _ (op U) _).mpr ?_
    exact le_idealPowerMultiple_obj B S hS F hF 𝓘 k N U
      (Submodule.smul_mem_smul hr Submodule.mem_top))

/-- The induced map on quotients is compatible with the quotient projections. -/
@[simp]
theorem π_comp_idealPowerQuotientMapOfHom (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N) :
    cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫
        idealPowerQuotientMapOfHom B S hS F hF 𝓘 k f =
      f ≫ cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k N).ι :=
  cokernel.π_desc _ _ _

/-- The identity induces the identity on quotients. -/
theorem idealPowerQuotientMapOfHom_id (k : ℕ) (M : Modules.{u, u} B S hS F hF) :
    idealPowerQuotientMapOfHom B S hS F hF 𝓘 k (𝟙 M) = 𝟙 _ := by
  apply (cancel_epi (cokernel.π _)).mp
  rw [π_comp_idealPowerQuotientMapOfHom, Category.id_comp, Category.comp_id]

/-- The induced maps on quotients compose. -/
theorem idealPowerQuotientMapOfHom_comp (k : ℕ) {M N P : Modules.{u, u} B S hS F hF}
    (f : M ⟶ N) (g : N ⟶ P) :
    idealPowerQuotientMapOfHom B S hS F hF 𝓘 k (f ≫ g) =
      idealPowerQuotientMapOfHom B S hS F hF 𝓘 k f ≫
        idealPowerQuotientMapOfHom B S hS F hF 𝓘 k g := by
  apply (cancel_epi (cokernel.π _)).mp
  rw [π_comp_idealPowerQuotientMapOfHom, ← Category.assoc,
    π_comp_idealPowerQuotientMapOfHom, Category.assoc, Category.assoc,
    π_comp_idealPowerQuotientMapOfHom]

/-- The induced map on quotients commutes with the projections of the tower. -/
theorem idealPowerQuotientMapOfLE_comp_idealPowerQuotientMapOfHom {k l : ℕ} (h : k ≤ l)
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N) :
    idealPowerQuotientMapOfLE B S hS F hF 𝓘 h M ≫
        idealPowerQuotientMapOfHom B S hS F hF 𝓘 k f =
      idealPowerQuotientMapOfHom B S hS F hF 𝓘 l f ≫
        idealPowerQuotientMapOfLE B S hS F hF 𝓘 h N := by
  apply (cancel_epi (cokernel.π _)).mp
  rw [← Category.assoc, π_comp_idealPowerQuotientMapOfLE,
    π_comp_idealPowerQuotientMapOfHom, ← Category.assoc,
    π_comp_idealPowerQuotientMapOfHom, Category.assoc,
    π_comp_idealPowerQuotientMapOfLE]

/-- The morphism of inverse systems `(M / 𝓘 ^ (n + 1) M)_n ⟶ (N / 𝓘 ^ (n + 1) N)_n` induced by a
morphism `M ⟶ N`. -/
def adicQuotientSystemMap {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N) :
    adicQuotientSystem B S hS F hF 𝓘 M ⟶ adicQuotientSystem B S hS F hF 𝓘 N where
  app n := idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n.unop + 1) f
  naturality _ _ g :=
    idealPowerQuotientMapOfLE_comp_idealPowerQuotientMapOfHom B S hS F hF 𝓘
      (Nat.add_le_add_right (leOfHom g.unop) 1) f

/-- The completion along `𝓘`, as a functor from `𝒪_F`-modules to inverse systems of `𝒪_F`-modules,
sending `M` to `(M / 𝓘 ^ (n + 1) M)_n`. -/
def adicQuotientFunctor :
    Modules.{u, u} B S hS F hF ⥤ (ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) where
  obj M := adicQuotientSystem B S hS F hF 𝓘 M
  map f := adicQuotientSystemMap B S hS F hF 𝓘 f
  map_id M := NatTrans.ext (funext fun n =>
    idealPowerQuotientMapOfHom_id B S hS F hF 𝓘 (n.unop + 1) M)
  map_comp f g := NatTrans.ext (funext fun n =>
    idealPowerQuotientMapOfHom_comp B S hS F hF 𝓘 (n.unop + 1) f g)

/-! ### The completion of a coherent module is a coherent adic system -/

/-- On a locally Noetherian algebraic space, the completion of a coherent module along a
quasi-coherent sheaf of ideals `𝓘` is a coherent `𝓘`-adic system. -/
theorem isCoherentAdicSystem_adicQuotientSystem
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (M : Modules.{u, u} B S hS F hF)
    (hM : IsCoherent B S hS F hF M) :
    IsCoherentAdicSystem B S hS F hF 𝓘 (adicQuotientSystem B S hS F hF 𝓘 M) :=
  ⟨fun n => isCoherent_idealPowerQuotient B S hS F hF 𝓘 hI M hM (n + 1),
    fun n => idealPowerMultiple_idealPowerQuotient_eq_bot B S hS F hF 𝓘 (n + 1) M,
    fun n => ⟨idealPowerQuotientQuotientIso B S hS F hF 𝓘 (Nat.le_succ (n + 1)) M,
      π_comp_idealPowerQuotientQuotientIso_hom B S hS F hF 𝓘 (Nat.le_succ (n + 1)) M⟩⟩

/-- The completion functor `Coh(𝒪_F) ⟶ Coh(F, 𝓘)` on a locally Noetherian algebraic space, for a
quasi-coherent sheaf of ideals `𝓘`, sending a coherent `𝒪_F`-module `𝓖` to the coherent `𝓘`-adic
system `𝓖^∧ = (𝓖 / 𝓘 ^ (n + 1) 𝓖)_n`. -/
@[stacks 08B4]
def completionFunctor
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) :
    CoherentModules.{u, u} B S hS F hF ⥤ CoherentAdicSystems B S hS F hF 𝓘 :=
  ObjectProperty.lift (IsCoherentAdicSystem B S hS F hF 𝓘 :
      ObjectProperty (ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF))
    (ObjectProperty.ι (isCoherent.{u, u} B S hS F hF) ⋙
      adicQuotientFunctor B S hS F hF 𝓘)
    fun G => isCoherentAdicSystem_adicQuotientSystem B S hS F hF 𝓘 hI G.obj G.property

end AlgebraicGeometry.Space

end

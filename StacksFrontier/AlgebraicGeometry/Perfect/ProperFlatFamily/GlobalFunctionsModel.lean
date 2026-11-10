module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsKernelModel
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSectionTransfer
public import StacksFrontier.RingTheory.Etale.FiniteFreeFibrewise

/-!
# The kernel model on global functions

Let `f : X ⟶ Spec A` be separated with a finite affine open cover, and let `u : P ⟶ Č ⊗_A R` be a
chain-level model over an `A`-algebra `R` of the `A`-linear Čech complex `Č` of the structure
sheaf, vanishing in degree `-1`, with first differential the matrix `M`. The kernel model of
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsKernelModel.lean` identifies,
for every `R`-algebra `B` and every base change `X'` of `X` to `B`, the kernel of `M ⊗ B` with the
sections of the pullback of `𝒪_X` to `X'`. Reading those sections as the global functions of `X'`
through the canonical identification `g'^* 𝒪_X ≅ 𝒪_{X'}`, this file gives

* `kernelFunctionsEquiv`: the `B`-linear identification `ker (M ⊗ B) ≅ Γ(X', 𝒪_{X'})`, where
  `Γ(X', 𝒪_{X'})` is a `B`-module through the structure morphism; and
* `appTop_kernelFunctionsEquiv`: its naturality — pulling a global function back along a further
  base change `X'' ⟶ X'` over `B ⟶ B'` is, in coordinates, `v ↦ ψ' ∘ v`.

When `M ⊗ B` vanishes the kernel is all of `B^r`, so `Γ(X', 𝒪_{X'})` is free of rank `r` over `B`
and, by `Algebra.TensorProduct.bijective_lift_of_coordinates`, its formation commutes with every
further base change (`bijective_lift_appTop_of_matrix_map_eq_zero`).

## Implementation notes

The identification `g'^* 𝒪_X ≅ 𝒪_{X'}` is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. It
is linear over `Γ(X', ⊤)`, and the `B`-module structure that the kernel model puts on the sections
of `g'^* 𝒪_X` is restriction of scalars along `Stacks.Cech.baseRingHom f' ⊤`, which is
`Stacks.Cech.globalRingHom f'` followed by the restriction along `⊤ ≤ ⊤`; so it is `B`-linear for
the algebra structure of `Γ(X', ⊤)` along `Stacks.Cech.globalRingHom f'`. Naturality combines the
naturality of the kernel model (`kernelModelEquiv_comp`), the compatibility of `pullbackUnitIso`
with composition (`Scheme.Modules.pullbackUnitIso_comp`), the naturality of pulling sections back
in the module (`pullbackSectionHom_naturality`), and the fact that pulling a function back as a
section of `g''^* 𝒪_{X'}` is pulling it back as a function (`pullbackUnitIso_unit`).

## References

* [Stacks Project, Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

/-! ### Global functions as sections of the pulled-back structure sheaf -/

section UnitSections

variable {B : Type u} [CommRing B] {X X' : Scheme.{u}} (f' : X' ⟶ Spec (.of B)) (g' : X' ⟶ X)

/-- The structural ring map `B ⟶ Γ(X', ⊤)` restricted along `⊤ ≤ ⊤` is itself. -/
theorem baseRingHom_top : Stacks.Cech.baseRingHom f' ⊤ = Stacks.Cech.globalRingHom f' := by
  rw [Stacks.Cech.baseRingHom, show (homOfLE (le_top (a := (⊤ : X'.Opens)))).op = 𝟙 _ from
    Subsingleton.elim _ _, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The sections of `g'^* 𝒪_X` over `X'` are the global functions of `X'`**: the
identification `g'^* 𝒪_X ≅ 𝒪_{X'}` on global sections. -/
def unitSectionsEquiv :
    Γ((Scheme.Modules.pullback g').obj (Scheme.unitModule X), ⊤) ≃+ Γ(X', ⊤) where
  toFun s := (Scheme.Modules.pullbackUnitIso g').hom.app ⊤ s
  invFun s := (Scheme.Modules.pullbackUnitIso g').inv.app ⊤ s
  left_inv s := by
    change ((Scheme.Modules.pullbackUnitIso g').hom ≫
      (Scheme.Modules.pullbackUnitIso g').inv).app ⊤ s = s
    rw [Iso.hom_inv_id]
    rfl
  right_inv s := by
    change ((Scheme.Modules.pullbackUnitIso g').inv ≫
      (Scheme.Modules.pullbackUnitIso g').hom).app ⊤ s = s
    rw [Iso.inv_hom_id]
    rfl
  map_add' s t := map_add _ s t

/-- `unitSectionsEquiv` carries the action of `B` through `Stacks.Cech.baseRingHom f' ⊤` to
multiplication by the image under `Stacks.Cech.globalRingHom f'`. -/
theorem unitSectionsEquiv_smul (c : B)
    (s : Γ((Scheme.Modules.pullback g').obj (Scheme.unitModule X), ⊤)) :
    unitSectionsEquiv g' ((Stacks.Cech.baseRingHom f' ⊤ c) • s) =
      Stacks.Cech.globalRingHom f' c * unitSectionsEquiv g' s := by
  change (Scheme.Modules.pullbackUnitIso g').hom.app ⊤ ((Stacks.Cech.baseRingHom f' ⊤ c) • s) = _
  rw [baseRingHom_top, Scheme.Modules.Hom.app_smul]
  rfl

/-- **The `B`-linear form of `unitSectionsEquiv`**, for the module structures of the kernel model
on the source and of the structure morphism on the target. -/
def unitSectionsLinearEquiv :
    letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤
    letI : Algebra B Γ(X', ⊤) :=
      ((Stacks.Cech.globalRingHom f').hom : B →+* Γ(X', ⊤)).toAlgebra
    Γ((Scheme.Modules.pullback g').obj (Scheme.unitModule X), ⊤) ≃ₗ[B] Γ(X', ⊤) :=
  letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤
  letI : Algebra B Γ(X', ⊤) :=
    ((Stacks.Cech.globalRingHom f').hom : B →+* Γ(X', ⊤)).toAlgebra
  { unitSectionsEquiv g' with
    map_smul' := unitSectionsEquiv_smul f' g' }

/-- `unitSectionsEquiv` on the pullback of a global function is the pullback of the function. -/
theorem unitSectionsEquiv_pullbackSectionHom {X'' : Scheme.{u}} (g'' : X'' ⟶ X')
    (a : Γ(X', ⊤)) :
    unitSectionsEquiv (g'' ≫ g') (((Scheme.Modules.pullbackComp g'' g').hom.app
        (Scheme.unitModule X)).app ⊤ (pullbackSectionHom g''
          ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤ ⊤ (by simp)
          ((Scheme.Modules.pullbackUnitIso g').inv.app ⊤ a))) =
      g''.appTop a := by
  set t := (Scheme.Modules.pullbackUnitIso g').hom
  have h1 : ((Scheme.Modules.pullbackComp g'' g').hom.app (Scheme.unitModule X)) ≫
      (Scheme.Modules.pullbackUnitIso (g'' ≫ g')).hom =
      (Scheme.Modules.pullback g'').map t ≫ (Scheme.Modules.pullbackUnitIso g'').hom := by
    rw [← Scheme.Modules.pullbackUnitIso_comp g'' g', ← Category.assoc, ← Category.assoc,
      ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app, Category.id_comp]
  have hle : (⊤ : X''.Opens) ≤ g'' ⁻¹ᵁ ⊤ := by simp
  have h2 : pullbackSectionHom g'' ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤ ⊤
      hle ≫ ((Scheme.Modules.pullback g'').map t ≫ (Scheme.Modules.pullbackUnitIso g'').hom).app ⊤ =
      t.app ⊤ ≫ pullbackSectionHom g'' (Scheme.unitModule X') ⊤ ⊤ hle ≫
        (Scheme.Modules.pullbackUnitIso g'').hom.app ⊤ := by
    rw [Scheme.Modules.Hom.comp_app, ← Category.assoc, pullbackSectionHom_naturality,
      Category.assoc]
  have h3 : t.app ⊤ ((Scheme.Modules.pullbackUnitIso g').inv.app ⊤ a) = a :=
    (unitSectionsEquiv g').apply_symm_apply a
  have h4 : pullbackSectionHom g'' (Scheme.unitModule X') ⊤ ⊤ hle =
      pullbackGlobalSections g'' (Scheme.unitModule X') := by
    unfold pullbackSectionHom pullbackGlobalSections
    congr 2
  change ((((Scheme.Modules.pullbackComp g'' g').hom.app (Scheme.unitModule X)) ≫
      (Scheme.Modules.pullbackUnitIso (g'' ≫ g')).hom).app ⊤)
      (pullbackSectionHom g'' ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤ ⊤ hle
        ((Scheme.Modules.pullbackUnitIso g').inv.app ⊤ a)) = g''.appTop a
  rw [h1, ← ConcreteCategory.comp_apply, h2, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, h3, h4]
  exact SectionsEqualizer.pullbackUnitIso_unit g'' a

end UnitSections

/-! ### The structure maps of a base change -/

/-- **The structure maps on global functions are compatible with a commutative square** over
`Spec B' ⟶ Spec B`. -/
theorem globalRingHom_naturality {B B' : Type u} [CommRing B] [CommRing B'] (ψ' : B →+* B')
    {X' X'' : Scheme.{u}} (f' : X' ⟶ Spec (.of B)) (f'' : X'' ⟶ Spec (.of B')) (g'' : X'' ⟶ X')
    (w : g'' ≫ f' = f'' ≫ Spec.map (CommRingCat.ofHom ψ')) (c : B) :
    Stacks.Cech.globalRingHom f'' (ψ' c) = g''.appTop (Stacks.Cech.globalRingHom f' c) := by
  have h : CommRingCat.ofHom ψ' ≫ Stacks.Cech.globalRingHom f'' =
      Stacks.Cech.globalRingHom f' ≫ g''.appTop := by
    change CommRingCat.ofHom ψ' ≫ (Scheme.ΓSpecIso (.of B')).inv ≫ f''.appTop =
      ((Scheme.ΓSpecIso (.of B)).inv ≫ f'.appTop) ≫ g''.appTop
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, w]
  exact congr($h c)

/-! ### The kernel model on global functions -/

section Coordinates

open scoped Matrix

variable {A R : Type u} [CommRing A] [CommRing R] (α : A →+* R)
  {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f]
  {I : Type u} [Fintype I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))
  (hflat : IsFlatOver f.toLRSHom.toShHom (Scheme.unitModule X))
  {P : CochainComplex (ModuleCat.{u} R) ℤ}
  (u : P ⟶ extendScalarsComplex α (baseAlternatingCechComplex f U hU (Scheme.unitModule X)))
  [QuasiIso u] [∀ n : ℤ, Module.Flat R (P.X n)] (b : ℤ) [P.IsStrictlyLE b]
  (hP : IsZero (P.X (-1)))
  {r β : ℕ} (e₀ : P.X 0 ≅ ModuleCat.of R (Fin r → R)) (e₁ : P.X 1 ≅ ModuleCat.of R (Fin β → R))
  (M : Matrix (Fin β) (Fin r) R) (hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv)

/-- **The kernel model on global functions.** For an `R`-algebra `B` and a cartesian square
exhibiting `X'` as the base change of `X` to `B`, the kernel of `M ⊗ B` is `Γ(X', 𝒪_{X'})`,
`B`-linearly for the module structure of the structure morphism. -/
def kernelFunctionsEquiv {B : Type u} [CommRing B] (ψ : R →+* B) {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α)))) :
    letI : Algebra B Γ(X', ⊤) :=
      ((Stacks.Cech.globalRingHom f').hom : B →+* Γ(X', ⊤)).toAlgebra
    LinearMap.ker (M.map ψ).mulVecLin ≃ₗ[B] Γ(X', ⊤) :=
  (kernelModelEquiv α (Scheme.unitModule X) U hU hUaff hflat u b hP e₀ e₁ M hM ψ hsq).trans
    (unitSectionsLinearEquiv f' g')

/-- **The kernel model on global functions is natural.** Pulling a global function back along a
further base change `X'' ⟶ X'` over `ψ' : B ⟶ B'` is, in coordinates, `v ↦ ψ' ∘ v`. -/
theorem appTop_kernelFunctionsEquiv {B B' : Type u} [CommRing B] [CommRing B'] (ψ : R →+* B)
    (ψ' : B →+* B') {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)}
    {f'' : X'' ⟶ Spec (.of B')} {g' : X' ⟶ X} {g'' : X'' ⟶ X'}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α))))
    (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom ψ')))
    (hsq'' : IsPullback (g'' ≫ g') f'' f (Spec.map (CommRingCat.ofHom ((ψ'.comp ψ).comp α))))
    (v : LinearMap.ker (M.map ψ).mulVecLin)
    (hv : ψ' ∘ (v : Fin r → B) ∈ LinearMap.ker (M.map (ψ'.comp ψ)).mulVecLin) :
    g''.appTop (kernelFunctionsEquiv α U hU hUaff hflat u b hP e₀ e₁ M hM ψ hsq v) =
      kernelFunctionsEquiv α U hU hUaff hflat u b hP e₀ e₁ M hM (ψ'.comp ψ) hsq''
        ⟨ψ' ∘ (v : Fin r → B), hv⟩ := by
  have key := kernelModelEquiv_comp α (Scheme.unitModule X) U hU hUaff hflat u b hP e₀ e₁ M hM ψ ψ'
    hsq hsq' hsq'' v hv
  set y := kernelModelEquiv α (Scheme.unitModule X) U hU hUaff hflat u b hP e₀ e₁ M hM ψ hsq v
  change g''.appTop (unitSectionsEquiv g' y) = unitSectionsEquiv (g'' ≫ g') _
  refine Eq.trans ?_ (congrArg (unitSectionsEquiv (g'' ≫ g')) key)
  have h := unitSectionsEquiv_pullbackSectionHom g' g'' (unitSectionsEquiv g' y)
  have e : (Scheme.Modules.pullbackUnitIso g').inv.app ⊤ (unitSectionsEquiv g' y) = y :=
    (unitSectionsEquiv g').symm_apply_apply y
  rw [e] at h
  exact h.symm

/-- When `M ⊗ B` vanishes its kernel is everything. -/
theorem ker_mulVecLin_map_eq_top {B : Type u} [CommRing B] (ψ : R →+* B) (hψ : M.map ψ = 0) :
    LinearMap.ker (M.map ψ).mulVecLin = ⊤ := by
  rw [hψ, eq_top_iff]
  intro v _
  simp

omit [IsSeparated f] [Fintype I] [QuasiIso u] [∀ n : ℤ, Module.Flat R (P.X n)] [P.IsStrictlyLE b] in
/-- If `M ⊗ B` vanishes, so does `M ⊗ B'` for every `B`-algebra `B'`. -/
theorem matrix_map_comp_eq_zero {B B' : Type u} [CommRing B] [CommRing B'] (ψ : R →+* B)
    (hψ : M.map ψ = 0) (ψ' : B →+* B') : M.map (ψ'.comp ψ) = 0 := by
  rw [RingHom.coe_comp, ← Matrix.map_map, hψ, Matrix.map_zero _ (map_zero ψ')]

/-- **When `M ⊗ B` vanishes, the global functions of `X'` are free of rank `r` over `B`.** -/
def freeFunctionsEquiv {B : Type u} [CommRing B] (ψ : R →+* B) (hψ : M.map ψ = 0) {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α)))) :
    letI : Algebra B Γ(X', ⊤) :=
      ((Stacks.Cech.globalRingHom f').hom : B →+* Γ(X', ⊤)).toAlgebra
    (Fin r → B) ≃ₗ[B] Γ(X', ⊤) :=
  (LinearEquiv.ofTop _ (ker_mulVecLin_map_eq_top M ψ hψ)).symm.trans
    (kernelFunctionsEquiv α U hU hUaff hflat u b hP e₀ e₁ M hM ψ hsq)

/-- The coordinates of `freeFunctionsEquiv` are natural in the algebra. -/
theorem appTop_freeFunctionsEquiv {B B' : Type u} [CommRing B] [CommRing B'] (ψ : R →+* B)
    (hψ : M.map ψ = 0) (ψ' : B →+* B') {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)}
    {f'' : X'' ⟶ Spec (.of B')} {g' : X' ⟶ X} {g'' : X'' ⟶ X'}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α))))
    (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom ψ')))
    (hsq'' : IsPullback (g'' ≫ g') f'' f (Spec.map (CommRingCat.ofHom ((ψ'.comp ψ).comp α))))
    (v : Fin r → B) :
    g''.appTop (freeFunctionsEquiv α U hU hUaff hflat u b hP e₀ e₁ M hM ψ hψ hsq v) =
      freeFunctionsEquiv α U hU hUaff hflat u b hP e₀ e₁ M hM (ψ'.comp ψ)
        (matrix_map_comp_eq_zero M ψ hψ ψ') hsq'' (ψ' ∘ v) :=
  appTop_kernelFunctionsEquiv α U hU hUaff hflat u b hP e₀ e₁ M hM ψ ψ' hsq hsq' hsq''
    ⟨v, by rw [ker_mulVecLin_map_eq_top M ψ hψ]; trivial⟩ _

omit [Fintype I] in
include U hU hUaff hflat u b hP e₀ e₁ hM in
/-- **When `M ⊗ B` vanishes, the formation of the global functions commutes with every further
base change**: for a `B`-algebra `B'` and a cartesian square exhibiting `X''` as the base change
of `X'` to `B'`, the map `B' ⊗_B Γ(X', 𝒪_{X'}) ⟶ Γ(X'', 𝒪_{X''})`, `b' ⊗ a ↦ b' · g''^* a`, is
bijective. -/
theorem bijective_lift_appTop_of_matrix_map_eq_zero [Finite I] {B B' : Type u} [CommRing B]
    [CommRing B'] [Algebra B B'] (ψ : R →+* B) (hψ : M.map ψ = 0) {X' X'' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of B)} {f'' : X'' ⟶ Spec (.of B')} {g' : X' ⟶ X} {g'' : X'' ⟶ X'}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α))))
    (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom (algebraMap B B'))))
    (hsq'' : IsPullback (g'' ≫ g') f'' f
      (Spec.map (CommRingCat.ofHom (((algebraMap B B').comp ψ).comp α)))) :
    letI : Algebra B Γ(X', ⊤) :=
      ((Stacks.Cech.globalRingHom f').hom : B →+* Γ(X', ⊤)).toAlgebra
    letI : Algebra B' Γ(X'', ⊤) :=
      ((Stacks.Cech.globalRingHom f'').hom : B' →+* Γ(X'', ⊤)).toAlgebra
    letI : Algebra B Γ(X'', ⊤) := ((algebraMap B' Γ(X'', ⊤)).comp (algebraMap B B')).toAlgebra
    letI : IsScalarTower B B' Γ(X'', ⊤) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId B' Γ(X'', ⊤))
      (Algebra.TensorProduct.algHomOfLiesOver (B := B) (B' := B') g''.appTop.hom
        (fun c => (globalRingHom_naturality (algebraMap B B') f' f'' g'' hsq'.w c).symm))
      fun _ _ => Commute.all _ _) := by
  have := Fintype.ofFinite I
  let : Algebra B Γ(X', ⊤) :=
    ((Stacks.Cech.globalRingHom f').hom : B →+* Γ(X', ⊤)).toAlgebra
  let : Algebra B' Γ(X'', ⊤) :=
    ((Stacks.Cech.globalRingHom f'').hom : B' →+* Γ(X'', ⊤)).toAlgebra
  let θ := freeFunctionsEquiv α U hU hUaff hflat u b hP e₀ e₁ M hM ψ hψ hsq
  let θ' := freeFunctionsEquiv α U hU hUaff hflat u b hP e₀ e₁ M hM ((algebraMap B B').comp ψ)
    (matrix_map_comp_eq_zero M ψ hψ _) hsq''
  exact Algebra.TensorProduct.bijective_lift_of_coordinates (B := B) (B' := B') g''.appTop.hom
    (fun c => (globalRingHom_naturality (algebraMap B B') f' f'' g'' hsq'.w c).symm) θ θ'
    fun v => appTop_freeFunctionsEquiv α U hU hUaff hflat u b hP e₀ e₁ M hM ψ hψ (algebraMap B B')
      hsq hsq' hsq'' v

end Coordinates

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end

module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.GradedPiece
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative

/-!
# One step of the thickening induction

Let `g : X ⟶ Spec R`, `I ⊆ R` and `ℱ` quasi-coherent on `X` with `R`-flat sections over affine
opens. A *face* is a closed immersion `j : F ⟶ X`, a quasi-coherent `𝒪_F`-module `ℱ'` with
`R`-flat sections, and an `𝒪_X`-linear map `u : ℱ ⟶ j_* ℱ'` (in the application, `ℱ' = j^* ℱ`
and `u` is the adjunction unit).

If `Γ(F, ℱ' / Iⁿ⁺²ℱ') → Γ(F, ℱ' / Iⁿ⁺¹ℱ')` is surjective for every face and the maps
`H¹(X, ℱ / Iℱ) → H¹(X, j_* (ℱ' / Iℱ'))` are jointly injective, then
`Γ(X, ℱ / Iⁿ⁺²ℱ) → Γ(X, ℱ / Iⁿ⁺¹ℱ)` is surjective. This is step 1(a) of the cube proof
in abstract form: the obstruction to lifting a section lies in
`H¹(X, Iⁿ⁺¹ℱ / Iⁿ⁺²ℱ) = H¹(X, ℱ / Iℱ)ᵈ`, and it restricts on each face to the obstruction there.

## Main definitions

* `Stacks.CubeOpenAtUnit.Face`: the data of a face.
* `Stacks.CubeOpenAtUnit.Face.quoMap`: the induced `ℱ / Iᵐℱ ⟶ j_* (ℱ' / Iᵐℱ')`.

## Main results

* `Stacks.CubeOpenAtUnit.surjective_quoDrop_app_top`: the lifting step.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open Stacks.Coherent (baseSectionHom baseIdealSheaf_ideal_eq_map)

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

universe u

namespace Stacks.CubeOpenAtUnit

/-- The category of `𝒪_X`-modules has finite biproducts. -/
local instance hasFiniteBiproducts_modules' (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (.of R)) (I : Ideal R)

/-! ### Base ring maps along a morphism -/

/-- The structure map `R → Γ(F, j⁻¹ U)` of `j ≫ g` is that of `g` on `U` followed by `j.app U`. -/
theorem baseSectionHom_comp {F : Scheme.{u}} (j : F ⟶ X) (U : X.Opens) :
    baseSectionHom R (j ≫ g) (j ⁻¹ᵁ U) = (j.app U).hom.comp (baseSectionHom R g U) := by
  have h : ((Scheme.ΓSpecIso (.of R)).inv ≫ (j ≫ g).appTop) ≫
        F.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ U ≤ ⊤)).op =
      (((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop) ≫
        X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ≫ j.app U := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      Scheme.Hom.naturality]
    rfl
  ext a
  exact congrArg (fun φ => φ.hom a) h

/-- The global function on `F` given by `a : R` along `j ≫ g` is the image under `j.appTop` of
the global function on `X` given by `a` along `g`. -/
theorem baseTop_comp {F : Scheme.{u}} (j : F ⟶ X) (a : R) :
    baseTop (j ≫ g) a = j.appTop (baseTop g a) := by
  show ((Scheme.ΓSpecIso (.of R)).inv ≫ (j ≫ g).appTop).hom a = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Pushing forward multiplication by a function from the base is multiplication by it. -/
theorem pushforward_map_globalSmul {F : Scheme.{u}} (j : F ⟶ X) (M : F.Modules) (a : R) :
    (Scheme.Modules.pushforward j).map (AlgebraicGeometry.globalSmul (baseTop (j ≫ g) a) M) =
      AlgebraicGeometry.globalSmul (baseTop g a) ((Scheme.Modules.pushforward j).obj M) := by
  ext U x
  have e : AlgebraicGeometry.restrictTop (baseTop (j ≫ g) a) (j ⁻¹ᵁ U) =
      (j.app U).hom (AlgebraicGeometry.restrictTop (baseTop g a) U) := by
    rw [restrictTop_baseTop, restrictTop_baseTop, baseSectionHom_comp]
    rfl
  have h1 := AlgebraicGeometry.globalSmul_app (baseTop (j ≫ g) a) M (j ⁻¹ᵁ U) x
  have h2 := AlgebraicGeometry.globalSmul_app (baseTop g a) ((Scheme.Modules.pushforward j).obj M)
    U x
  rw [e] at h1
  exact h1.trans h2.symm

/-! ### Faces -/

variable (G : X.Modules)

/-- A *face* of `(X, ℱ)`: a closed immersion `j : F ⟶ X`, a quasi-coherent `𝒪_F`-module `ℱ'` and
an `𝒪_X`-linear map `u : ℱ ⟶ j_* ℱ'`. -/
structure Face where
  /-- The source of the face. -/
  F : Scheme.{u}
  /-- The closed immersion. -/
  j : F ⟶ X
  [isClosedImmersion : IsClosedImmersion j]
  /-- The module on the face. -/
  G' : F.Modules
  [isQuasicoherent : G'.IsQuasicoherent]
  /-- The comparison map. -/
  u : G ⟶ (Scheme.Modules.pushforward j).obj G'

attribute [instance] Face.isClosedImmersion Face.isQuasicoherent

namespace Face

variable {g I G} (φ : Face G)

/-- The map `ℱ / Iᵐℱ ⟶ j_* (ℱ' / Iᵐℱ')` induced by `u`. -/
def quoMap (m : ℕ) : quo g I G m ⟶
    (Scheme.Modules.pushforward φ.j).obj (quo (φ.j ≫ g) I φ.G' m) :=
  cokernel.desc (C := X.Modules) (idealPowerMultiple (baseIdealSheaf R I g) m G).ι
    (φ.u ≫ (Scheme.Modules.pushforward φ.j).map (quoπ (φ.j ≫ g) I φ.G' m)) (by
      refine Stacks.Coherent.idealPowerMultiple_ι_comp_eq_zero_of_app_smul _ _ _
        fun U b hb y => ?_
      change (quoπ (φ.j ≫ g) I φ.G' m).app (φ.j ⁻¹ᵁ U.1) (φ.u.app U.1 (b • y)) = 0
      rw [Scheme.Modules.Hom.app_smul]
      let V : (φ.F).affineOpens := ⟨φ.j ⁻¹ᵁ U.1, U.2.preimage φ.j⟩
      change (quoπ (φ.j ≫ g) I φ.G' m).app V.1
        ((φ.j.app U.1).hom b • (show Γ(φ.G', φ.j ⁻¹ᵁ U.1) from φ.u.app U.1 y)) = 0
      rw [quoπ_app_eq_zero_iff]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [baseIdealSheaf_ideal_eq_map, ← Ideal.map_pow] at hb
      have := Ideal.mem_map_of_mem (φ.j.app U.1).hom hb
      rwa [Ideal.map_map, ← baseSectionHom_comp, Ideal.map_pow] at this)

/-- The map `ℱ / Iᵐℱ ⟶ j_* (ℱ' / Iᵐℱ')` composed with the quotient map `ℱ ⟶ ℱ / Iᵐℱ` is `u`
followed by the pushforward of the quotient map `ℱ' ⟶ ℱ' / Iᵐℱ'`. -/
@[reassoc]
theorem quoπ_quoMap (m : ℕ) :
    quoπ g I G m ≫ φ.quoMap m =
      φ.u ≫ (Scheme.Modules.pushforward φ.j).map (quoπ (φ.j ≫ g) I φ.G' m) :=
  cokernel.π_desc _ _ _

end Face

/-! ### The graded short exact sequence -/

/-- The map `ℱ / Iᵏ⁺¹ℱ ⟶ ℱ / Iᵏℱ` is an epimorphism. -/
instance epi_quoDrop (k : ℕ) : Epi (quoDrop g I G k) :=
  epi_of_epi_fac (quoπ_quoDrop g I G k)

variable [G.IsQuasicoherent] {n : ℕ} {d : ℕ} (r : Fin d → R) (hr : ∀ k, r k ∈ I ^ (n + 1))

/-- The sequence `0 → (ℱ / Iℱ)ᵈ → ℱ / Iⁿ⁺²ℱ → ℱ / Iⁿ⁺¹ℱ → 0`. -/
def gradedSC : ShortComplex X.Modules :=
  ShortComplex.mk (gradedDesc g I G r hr ≫ kernel.ι (C := X.Modules) _) (quoDrop g I G (n + 1))
    (by rw [Category.assoc, kernel.condition, comp_zero])

/-- If `R → Γ(X, U)` and `Γ(X, U) → Γ(ℱ, U)` are flat for every affine open `U` and the
`rₖ ∈ Iⁿ⁺¹` form a basis of `Iⁿ⁺¹ / Iⁿ⁺²` over `R / I`, then
`0 → (ℱ / Iℱ)ᵈ → ℱ / Iⁿ⁺²ℱ → ℱ / Iⁿ⁺¹ℱ → 0` is short exact. -/
theorem gradedSC_shortExact
    (hflat : ∀ U : X.affineOpens, (baseSectionHom R g U.1).Flat ∧
      Module.Flat Γ(X, U.1) Γ(G, U.1))
    (hspan : I ^ (n + 1) ≤ Ideal.span (Set.range r) ⊔ I ^ (n + 2))
    (hind : ∀ a : Fin d → R, ∑ k, a k * r k ∈ I ^ (n + 2) → ∀ k, a k ∈ I) :
    (gradedSC g I G r hr).ShortExact := by
  have := isIso_gradedDesc g I G r hr hflat hspan hind
  refine ShortComplex.shortExact_of_iso ?_
    (ShortComplex.shortExact_mk_kernel_ι (quoDrop g I G (n + 1)))
  refine ShortComplex.isoMk (asIso (gradedDesc g I G r hr)).symm (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [gradedSC]
  · simp [gradedSC]

/-- On the `k`-th summand, the map `(ℱ / Iℱ)ᵈ ⟶ ℱ / Iⁿ⁺²ℱ` is multiplication by `rₖ`. -/
@[reassoc]
theorem ι_gradedDesc_kernelι (k : Fin d) :
    biproduct.ι (fun _ : Fin d => quo g I G 1) k ≫ gradedDesc g I G r hr ≫
        kernel.ι (C := X.Modules) (quoDrop g I G (n + 1)) = mulMap g I G (hr k) := by
  rw [gradedDesc, biproduct.ι_desc_assoc, mulKer_ι]

variable {g I G}

/-- The first component of `Stacks.CubeOpenAtUnit.Face.gradedSCMap`. -/
def Face.gradedτ₁ (φ : Face G) : (⨁ fun _ : Fin d => quo g I G 1) ⟶
    (Scheme.Modules.pushforward φ.j).obj (⨁ fun _ : Fin d => quo (φ.j ≫ g) I φ.G' 1) :=
  biproduct.desc fun k =>
    φ.quoMap 1 ≫ (Scheme.Modules.pushforward φ.j).map
      (biproduct.ι (fun _ : Fin d => quo (φ.j ≫ g) I φ.G' 1) k)

omit [SheafOfModules.IsQuasicoherent G] in
/-- On the `k`-th summand, `Stacks.CubeOpenAtUnit.Face.gradedτ₁` is `quoMap 1` followed by the
pushforward of the `k`-th inclusion. -/
@[reassoc]
theorem Face.ι_gradedτ₁ (φ : Face G) (k : Fin d) :
    biproduct.ι (fun _ : Fin d => quo g I G 1) k ≫ φ.gradedτ₁ =
      φ.quoMap 1 ≫ (Scheme.Modules.pushforward φ.j).map
        (biproduct.ι (fun _ : Fin d => quo (φ.j ≫ g) I φ.G' 1) k) :=
  biproduct.ι_desc _ _

omit [SheafOfModules.IsQuasicoherent G] in
/-- `Stacks.CubeOpenAtUnit.Face.gradedτ₁` followed by the pushforward of the `j`-th projection is
the `j`-th projection followed by `quoMap 1`. -/
theorem Face.gradedτ₁_π (φ : Face G) (j : Fin d) :
    φ.gradedτ₁ ≫ (Scheme.Modules.pushforward φ.j).map
        (biproduct.π (fun _ : Fin d => quo (φ.j ≫ g) I φ.G' 1) j) =
      biproduct.π (fun _ : Fin d => quo g I G 1) j ≫ φ.quoMap 1 := by
  refine biproduct.hom_ext' _ _ fun k => ?_
  rw [φ.ι_gradedτ₁_assoc, ← Functor.map_comp]
  by_cases hkj : k = j
  · subst hkj
    rw [biproduct.ι_π_self, biproduct.ι_π_self_assoc, CategoryTheory.Functor.map_id,
      Category.comp_id]
  · rw [biproduct.ι_π_ne _ hkj, ← Category.assoc, biproduct.ι_π_ne _ hkj, Functor.map_zero,
      comp_zero, zero_comp]

/-- The morphism from the graded sequence of `ℱ` to the pushforward of the graded sequence of
`ℱ'`, along a face. -/
def Face.gradedSCMap (φ : Face G) :
    gradedSC g I G r hr ⟶
      (gradedSC (φ.j ≫ g) I φ.G' r hr).map (Scheme.Modules.pushforward φ.j) where
  τ₁ := φ.gradedτ₁
  τ₂ := φ.quoMap (n + 2)
  τ₃ := φ.quoMap (n + 1)
  comm₁₂ := by
    refine biproduct.hom_ext' _ _ fun k => ?_
    change biproduct.ι _ k ≫ φ.gradedτ₁ ≫
        (Scheme.Modules.pushforward φ.j).map (gradedDesc (φ.j ≫ g) I φ.G' r hr ≫
          kernel.ι (C := φ.F.Modules) (quoDrop (φ.j ≫ g) I φ.G' (n + 1))) =
      biproduct.ι _ k ≫ (gradedDesc g I G r hr ≫
        kernel.ι (C := X.Modules) (quoDrop g I G (n + 1))) ≫ φ.quoMap (n + 2)
    rw [φ.ι_gradedτ₁_assoc, ← Functor.map_comp, ι_gradedDesc_kernelι]
    simp only [Category.assoc]
    rw [ι_gradedDesc_kernelι_assoc]
    refine (cancel_epi (quoπ g I G 1)).1 ?_
    have hF := quoπ_mulMap (φ.j ≫ g) I φ.G' (hr k)
    rw [φ.quoπ_quoMap_assoc, quoπ_mulMap_assoc, φ.quoπ_quoMap, ← Functor.map_comp, hF,
      Functor.map_comp, pushforward_map_globalSmul, ← Category.assoc,
      AlgebraicGeometry.comp_globalSmul, Category.assoc]
  comm₂₃ := by
    simp only [gradedSC, ShortComplex.map_g]
    refine (cancel_epi (quoπ g I G (n + 2))).1 ?_
    rw [φ.quoπ_quoMap_assoc, ← Functor.map_comp, quoπ_quoDrop, quoπ_quoDrop_assoc,
      φ.quoπ_quoMap]

include hr in
/-- **The lifting step.** Let `ℱ` and the modules `ℱ'` of a family of faces have `R`-flat
sections over affine opens, and let the `rₖ ∈ Iⁿ⁺¹` form a basis of `Iⁿ⁺¹ / Iⁿ⁺²` over `R / I`.
If `Γ(F, ℱ' / Iⁿ⁺²ℱ') → Γ(F, ℱ' / Iⁿ⁺¹ℱ')` is surjective on every face and the maps
`H¹(X, ℱ / Iℱ) → H¹(X, j_* (ℱ' / Iℱ'))` induced by the faces are jointly injective, then
`Γ(X, ℱ / Iⁿ⁺²ℱ) → Γ(X, ℱ / Iⁿ⁺¹ℱ)` is surjective. -/
theorem surjective_quoDrop_app_top
    (hflat : ∀ U : X.affineOpens, (baseSectionHom R g U.1).Flat ∧
      Module.Flat Γ(X, U.1) Γ(G, U.1))
    (hspan : I ^ (n + 1) ≤ Ideal.span (Set.range r) ⊔ I ^ (n + 2))
    (hind : ∀ a : Fin d → R, ∑ k, a k * r k ∈ I ^ (n + 2) → ∀ k, a k ∈ I)
    {ι : Type*} (φ : ι → Face G)
    (hflatF : ∀ i, ∀ U : (φ i).F.affineOpens, (baseSectionHom R ((φ i).j ≫ g) U.1).Flat ∧
      Module.Flat Γ((φ i).F, U.1) Γ((φ i).G', U.1))
    (hsurj : ∀ i, Function.Surjective ((quoDrop ((φ i).j ≫ g) I (φ i).G' (n + 1)).app ⊤))
    (hinj : ∀ c : (H X 1).obj (quo g I G 1),
      (∀ i, ((H X 1).map ((φ i).quoMap 1)).hom c = 0) → c = 0) :
    Function.Surjective ((quoDrop g I G (n + 1)).app ⊤) := by
  refine (surjective_H0_map_iff _).1 ?_
  refine surjective_H0_of_faces (gradedSC_shortExact g I G r hr hflat hspan hind)
    (T := fun i => (gradedSC ((φ i).j ≫ g) I (φ i).G' r hr).map
      (Scheme.Modules.pushforward (φ i).j))
    (fun i => (gradedSC_shortExact _ I _ r hr (hflatF i) hspan hind).map_of_exact _)
    (fun i => (φ i).gradedSCMap r hr) (fun i => (surjective_H0_map_iff _).2 (hsurj i)) ?_
  intro c hc
  exact jointlyInjective_H1_of_decomposition
    (fun j => biproduct.π (fun _ : Fin d => quo g I G 1) j)
    (fun j => biproduct.ι (fun _ : Fin d => quo g I G 1) j) biproduct.total
    (fun i => ((φ i).gradedSCMap r hr).τ₁) (fun i => (φ i).quoMap 1)
    (fun i j => (Scheme.Modules.pushforward (φ i).j).map
      (biproduct.π (fun _ : Fin d => quo ((φ i).j ≫ g) I (φ i).G' 1) j))
    (fun i j => (φ i).gradedτ₁_π j) hinj c hc

end Stacks.CubeOpenAtUnit

end

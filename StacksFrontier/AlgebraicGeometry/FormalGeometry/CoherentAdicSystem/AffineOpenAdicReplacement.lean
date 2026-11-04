module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineAdicReplacement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.BaseAdicCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantNoetherianCompletion
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving

/-!
# Adic replacement over an affine open

Let `X` be a Noetherian scheme, `𝒥` an ideal sheaf on `X`, `(ℱₙ)` an object of `Coh(X, 𝒥)`,
`(Pₙ)` an inverse system of coherent modules with a map `τ : (ℱₙ) → (Pₙ)`, and `U ⊆ X` an affine
open with ideal `I₀ = 𝒥(U) ⊆ Γ(X, U)`. Suppose the sections over `U` of `(Pₙ)` are
pro-isomorphic to the adic tower `(M/I₀^{n+1}M)` of a `Γ(X, U)`-module `M`, compatibly with a map
`σ₀ : (Γ(U, ℱₙ)) → (M/I₀^{n+1}M)`. Then on the open subscheme `U` there are an object `(𝒩ₙ)` of
`Coh(U, 𝒥|_U)`, a pro-isomorphism `(Pₙ|_U) ≅ (𝒩ₙ)` and a morphism `σ : (ℱₙ|_U) → (𝒩ₙ)`
compatible with `τ`, whose kernel and cokernel are annihilated by `𝒥|_U^c` as soon as those of
`σ₀` are annihilated by `I₀^c`.

This is `Stacks.Coherent.exists_coherentAdicSystem_of_affineAdicReplacement` on the affine scheme
`U`, transported along the identification of global sections on `U` with sections over `U` on `X`:
`Γ(ℱ|_U, ⊤) = Γ(ℱ, U)` with the scalars of `Γ(U, ⊤)` acting through `Γ(U, ⊤) ≅ Γ(X, U)`, and the
global ideal of `𝒥|_U` corresponding to `I₀` under that isomorphism.

## Main results

* `Stacks.Coherent.exists_coherentAdicSystem_of_affineOpenAdicReplacement` — the statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open InverseSequence Stacks.AdicSystem Stacks.Algebraization
open scoped Pointwise

universe u

namespace Stacks.Coherent

/-! ### Changing the ring of an adic tower along an isomorphism -/

section RingChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (hsurj : Function.Surjective (algebraMap A B)) (I₀ : Ideal B)
  (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

include hsurj in
/-- Along a surjective ring map `A → B`, the submodule `(I₀ ∩ A)^k M` of a `B`-module `M`, read as
an `A`-module, is `I₀^k M`. -/
theorem comap_pow_smul_top_eq_restrictScalars (k : ℕ) :
    (I₀.comap (algebraMap A B)) ^ k • (⊤ : Submodule A M) =
      (I₀ ^ k • (⊤ : Submodule B M)).restrictScalars A := by
  have hmap : ((I₀.comap (algebraMap A B)) ^ k).map (algebraMap A B) = I₀ ^ k := by
    rw [Ideal.map_pow, Ideal.map_comap_of_surjective _ hsurj I₀]
  rw [← hmap, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

/-- **The adic tower of `M` over `A` is the adic tower over `B`, read over `A`**, for a
surjective ring map `A → B` and the ideal `I₀ ∩ A`. -/
def adicQuotientTowerComapIso :
    adicQuotientTower (I₀.comap (algebraMap A B)) M ≅
      adicQuotientTower I₀ M ⋙ ModuleCat.restrictScalars (algebraMap A B) :=
  NatIso.ofComponents
    (fun n => LinearEquiv.toModuleIso
      ({ QuotientAddGroup.quotientAddEquivOfEq
          (congrArg Submodule.toAddSubgroup
            (comap_pow_smul_top_eq_restrictScalars hsurj I₀ M (n.unop + 1))) with
        map_smul' := fun r x => by
          induction x using Submodule.Quotient.induction_on with
          | H m =>
            change Submodule.Quotient.mk (r • m) =
              (Submodule.Quotient.mk (algebraMap A B r • m) :
                M ⧸ (I₀ ^ (n.unop + 1) • (⊤ : Submodule B M)))
            rw [algebraMap_smul] } :
        (M ⧸ ((I₀.comap (algebraMap A B)) ^ (n.unop + 1) • (⊤ : Submodule A M))) ≃ₗ[A]
          ((ModuleCat.restrictScalars (algebraMap A B)).obj
            ((adicQuotientTower I₀ M).obj n))))
    (fun {m n} g => by
      apply ModuleCat.hom_ext
      apply Submodule.linearMap_qext
      ext x
      rfl)

end RingChange


/-! ### Kernel and cokernel conditions along a change of rings -/

section Transfer

variable {J : Type*} [Category J] {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
  {S T : J ⥤ ModuleCat.{u} B} {S' T' : J ⥤ ModuleCat.{u} A}
  (γ : S' ≅ S ⋙ ModuleCat.restrictScalars φ) (ι : T' ≅ T ⋙ ModuleCat.restrictScalars φ)
  (σ : S ⟶ T) (I₀ : Ideal B) (c : ℕ) (j : J)

/-- If `I₀^c` kills the kernel of `σ_j`, then `(φ⁻¹I₀)^c` kills the kernel of the map
`γ ≫ σ ≫ ι⁻¹` read over `A`. -/
theorem smul_eq_zero_of_restrictScalars_comp_eq_zero (σ' : S' ⟶ T')
    (hσ' : σ' = γ.hom ≫ Functor.whiskerRight σ (ModuleCat.restrictScalars φ) ≫ ι.inv)
    (h : ∀ b ∈ I₀ ^ c, ∀ q : S.obj j, (σ.app j).hom q = 0 → b • q = 0) :
    ∀ a ∈ (I₀.comap φ) ^ c, ∀ q : S'.obj j, (σ'.app j).hom q = 0 → a • q = 0 := by
  subst hσ'
  intro a ha q hq
  have ha' : φ a ∈ I₀ ^ c := Ideal.le_comap_pow _ _ ha
  have hι : ∀ y, (ι.hom.app j).hom ((ι.inv.app j).hom y) = y := fun y =>
    congrArg (fun f => ModuleCat.Hom.hom f y) (ι.inv_hom_id_app j)
  have hγi : ∀ y, (γ.inv.app j).hom ((γ.hom.app j).hom y) = y := fun y =>
    congrArg (fun f => ModuleCat.Hom.hom f y) (γ.hom_inv_id_app j)
  set x : S.obj j := (γ.hom.app j).hom q with hx
  have h0 : (ι.inv.app j).hom ((σ.app j).hom x) = 0 := hq
  have hσx : (σ.app j).hom x = 0 := by
    have h1 := hι ((σ.app j).hom x)
    rw [h0, map_zero] at h1
    exact h1.symm
  have hγ : (γ.hom.app j).hom (a • q) = 0 := by
    rw [map_smul]
    exact h (φ a) ha' x hσx
  have h1 := hγi (a • q)
  rw [hγ, map_zero] at h1
  exact h1.symm

/-- If `I₀^c` maps the target of `σ_j` into its image, then `(φ⁻¹I₀)^c` maps the target of
`γ ≫ σ ≫ ι⁻¹` into its image, over `A`. -/
theorem smul_mem_range_restrictScalars_comp (σ' : S' ⟶ T')
    (hσ' : σ' = γ.hom ≫ Functor.whiskerRight σ (ModuleCat.restrictScalars φ) ≫ ι.inv)
    (h : ∀ b ∈ I₀ ^ c, ∀ q : T.obj j, b • q ∈ LinearMap.range (σ.app j).hom) :
    ∀ a ∈ (I₀.comap φ) ^ c, ∀ q : T'.obj j, a • q ∈ LinearMap.range (σ'.app j).hom := by
  subst hσ'
  intro a ha q
  have ha' : φ a ∈ I₀ ^ c := Ideal.le_comap_pow _ _ ha
  have hιi : ∀ y, (ι.inv.app j).hom ((ι.hom.app j).hom y) = y := fun y =>
    congrArg (fun f => ModuleCat.Hom.hom f y) (ι.hom_inv_id_app j)
  have hγ : ∀ y, (γ.hom.app j).hom ((γ.inv.app j).hom y) = y := fun y =>
    congrArg (fun f => ModuleCat.Hom.hom f y) (γ.inv_hom_id_app j)
  obtain ⟨p, hp⟩ := h (φ a) ha' ((ι.hom.app j).hom q)
  refine ⟨(γ.inv.app j).hom (show (S ⋙ ModuleCat.restrictScalars φ).obj j from p), ?_⟩
  change (ι.inv.app j).hom ((σ.app j).hom ((γ.hom.app j).hom ((γ.inv.app j).hom
    (show (S ⋙ ModuleCat.restrictScalars φ).obj j from p)))) = a • q
  rw [hγ]
  change (ι.inv.app j).hom ((σ.app j).hom p) = a • q
  rw [hp]
  change (ι.inv.app j).hom (a • (ι.hom.app j).hom q) = a • q
  rw [map_smul, hιi]

end Transfer

/-! ### The affine-open form -/

/-- Global sections on an open subscheme `U` of the restriction of a module are its sections over
the image `U.ι ''ᵁ ⊤`, with the scalars of `Γ(U, ⊤)` acting through `Γ(U, ⊤) ≅ Γ(X, U.ι ''ᵁ ⊤)`. -/
def restrictModuleGlobalSectionsIso {X : Scheme.{u}} (U : X.Opens) :
    Scheme.Modules.restrictFunctor U.ι ⋙ moduleGlobalSections U.toScheme ≅
      sectionsOn X (U.ι ''ᵁ ⊤) ⋙ ModuleCat.restrictScalars (U.ι.appIso ⊤).inv.hom :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

section AffineOpen

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (F : CoherentAdicSystems I)
  (P : ℕᵒᵖ ⥤ X.Modules) [∀ n, (P.obj n).IsCoherent] (τ : F.obj ⟶ P)

/-- The statement of `Stacks.Coherent.exists_coherentAdicSystem_of_affineOpenAdicReplacement`, with
the open over which sections are taken written `V` and identified with the image of the open
subscheme `U`. -/
theorem exists_coherentAdicSystem_of_affineOpenAdicReplacement_of_image_eq (U : X.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hUV : U.ι ''ᵁ ⊤ = V)
    (M : Type u) [AddCommGroup M] [Module Γ(X, V) M]
    (hfin : ∀ n : ℕ, Module.Finite Γ(X, V)
      (M ⧸ (I.ideal ⟨V, hV⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, V) M))))
    (e₀ : ProIso (P ⋙ sectionsOn X V) (adicQuotientTower (I.ideal ⟨V, hV⟩) M))
    (σ₀ : F.obj ⋙ sectionsOn X V ⟶ adicQuotientTower (I.ideal ⟨V, hV⟩) M)
    (hσ₀ : ∀ n : ℕ, (sectionsOn X V).map (τ.app (op (e₀.α n))) ≫ e₀.φ n =
      (sectionsOn X V).map (F.obj.map (homOfLE (e₀.αle n)).op) ≫ σ₀.app (op n)) :
    ∃ (N : CoherentAdicSystems (I.comap U.ι))
      (e : ProIso (P ⋙ Scheme.Modules.restrictFunctor U.ι) N.obj)
      (σ : (restrictFunctor I U.ι).obj F ⟶ N),
      (∀ n : ℕ, (Functor.whiskerRight τ (Scheme.Modules.restrictFunctor U.ι)).app (op (e.α n)) ≫
          e.φ n = ((restrictFunctor I U.ι).obj F).obj.map (homOfLE (e.αle n)).op ≫
            σ.hom.app (op n)) ∧
      (∀ c : ℕ, (∀ (n : ℕ) (a : Γ(X, V)), a ∈ I.ideal ⟨V, hV⟩ ^ c →
          ∀ q : Γ(F.obj.obj (op n), V), (σ₀.app (op n)).hom q = 0 → a • q = 0) →
        ∀ n : ℕ, idealPowerMultiple (I.comap U.ι) c ((kernel σ).obj.obj (op n)) = ⊥) ∧
      (∀ c : ℕ, (∀ (n : ℕ) (a : Γ(X, V)), a ∈ I.ideal ⟨V, hV⟩ ^ c →
          ∀ q : (adicQuotientTower (I.ideal ⟨V, hV⟩) M).obj (op n),
            a • q ∈ LinearMap.range (σ₀.app (op n)).hom) →
        ∀ n : ℕ, idealPowerMultiple (I.comap U.ι) c ((cokernel σ).obj.obj (op n)) = ⊥) := by
  subst hUV
  have : IsAffine U.toScheme := hU
  let I₀ := I.ideal ⟨U.ι ''ᵁ ⊤, hV⟩
  let ψ : Γ(U.toScheme, ⊤) →+* Γ(X, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv.hom
  have hψ : Function.Bijective ψ := ConcreteCategory.bijective_of_isIso (U.ι.appIso ⊤).inv
  let : Algebra Γ(U.toScheme, ⊤) Γ(X, U.ι ''ᵁ ⊤) := ψ.toAlgebra
  let : Module Γ(U.toScheme, ⊤) M := Module.compHom M ψ
  have : IsScalarTower Γ(U.toScheme, ⊤) Γ(X, U.ι ''ᵁ ⊤) M :=
    IsScalarTower.of_compHom _ _ M
  have hJ : (I.comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩ =
      I₀.comap (algebraMap Γ(U.toScheme, ⊤) Γ(X, U.ι ''ᵁ ⊤)) :=
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I U.ι ⟨⊤, isAffineOpen_top U.toScheme⟩
  let R := ModuleCat.restrictScalars ψ
  have iso : adicQuotientTower ((I.comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩) M ≅
      adicQuotientTower I₀ M ⋙ R :=
    eqToIso (by rw [hJ]) ≪≫ adicQuotientTowerComapIso hψ.2 I₀ M
  have γ := restrictModuleGlobalSectionsIso U
  let e₀' : ProIso (P ⋙ Scheme.Modules.restrictFunctor U.ι ⋙ moduleGlobalSections U.toScheme)
      (adicQuotientTower ((I.comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩) M) :=
    (ProIso.ofNatIso (Functor.isoWhiskerLeft P γ)).trans
      ((e₀.whiskerRight R).trans (ProIso.ofNatIso iso.symm))
  let γF : ((restrictFunctor I U.ι).obj F).obj ⋙ moduleGlobalSections U.toScheme ≅
      (F.obj ⋙ sectionsOn X (U.ι ''ᵁ ⊤)) ⋙ R :=
    Functor.isoWhiskerRight ((restrictFunctorCompιIso I U.ι).app F)
      (moduleGlobalSections U.toScheme) ≪≫ Functor.isoWhiskerLeft F.obj γ
  obtain ⟨σ₀', hσ₀'def⟩ : ∃ σ' : ((restrictFunctor I U.ι).obj F).obj ⋙
      moduleGlobalSections U.toScheme ⟶
      adicQuotientTower ((I.comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩) M,
      σ' = γF.hom ≫ Functor.whiskerRight σ₀ R ≫ iso.inv := ⟨_, rfl⟩
  have hfin' : ∀ n : ℕ, Module.Finite Γ(U.toScheme, ⊤)
      (M ⧸ ((I.comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩ ^ (n + 1) •
        (⊤ : Submodule Γ(U.toScheme, ⊤) M))) := by
    intro n
    have hf : Module.Finite Γ(U.toScheme, ⊤) ((R.obj ((adicQuotientTower I₀ M).obj (op n)))) := by
      have := hfin n
      obtain ⟨s, hs⟩ := (Module.finite_def).1 this
      refine ⟨⟨s, ?_⟩⟩
      have h := Submodule.restrictScalars_span Γ(U.toScheme, ⊤) Γ(X, U.ι ''ᵁ ⊤) hψ.2
        (s : Set (M ⧸ (I₀ ^ (n + 1) • (⊤ : Submodule Γ(X, U.ι ''ᵁ ⊤) M))))
      rw [hs, Submodule.restrictScalars_top] at h
      exact h.symm
    have : Module.Finite Γ(U.toScheme, ⊤) ((adicQuotientTower I₀ M ⋙ R).obj (op n)) := hf
    exact Module.Finite.equiv (iso.app (op n)).symm.toLinearEquiv
  have hσ₀' : ∀ n : ℕ, (moduleGlobalSections U.toScheme).map
      ((Functor.whiskerRight τ (Scheme.Modules.restrictFunctor U.ι)).app (op (e₀'.α n))) ≫
        e₀'.φ n = (moduleGlobalSections U.toScheme).map
          (((restrictFunctor I U.ι).obj F).obj.map (homOfLE (e₀'.αle n)).op) ≫ σ₀'.app (op n) := by
    intro n
    rw [hσ₀'def]
    have h := congrArg R.map (hσ₀ n)
    rw [R.map_comp, R.map_comp] at h
    have n1 := γ.hom.naturality (τ.app (op (e₀.α n)))
    have n2 := γ.hom.naturality (F.obj.map (homOfLE (e₀.αle n)).op)
    simp only [Functor.comp_map] at n1 n2
    change (moduleGlobalSections U.toScheme).map
          ((Scheme.Modules.restrictFunctor U.ι).map (τ.app (op (e₀.α n)))) ≫
        (γ.hom.app (P.obj (op (e₀.α n))) ≫ (R.map (e₀.φ n) ≫ iso.inv.app (op n))) =
      (moduleGlobalSections U.toScheme).map
          ((Scheme.Modules.restrictFunctor U.ι).map (F.obj.map (homOfLE (e₀.αle n)).op)) ≫
        (γ.hom.app (F.obj.obj (op n)) ≫ R.map (σ₀.app (op n)) ≫ iso.inv.app (op n))
    rw [reassoc_of% n1, reassoc_of% n2, reassoc_of% h]
  have : ∀ n, ((P ⋙ Scheme.Modules.restrictFunctor U.ι).obj n).IsCoherent := fun n =>
    @isCoherent_restrict_of_isOpenImmersion X U.toScheme U.ι _ _ (P.obj n) inferInstance
  obtain ⟨N, e, σ, hcompat, hker, hcok⟩ :=
    exists_coherentAdicSystem_of_affineAdicReplacement (I.comap U.ι) ((restrictFunctor I U.ι).obj F)
      (P ⋙ Scheme.Modules.restrictFunctor U.ι) (Functor.whiskerRight τ _) M hfin' e₀' σ₀' hσ₀'
  have hJ' : (I.comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩ = I₀.comap ψ := hJ
  refine ⟨N, e, σ, hcompat, fun c hc => hker c fun n a ha => ?_,
    fun c hc => hcok c fun n a ha => ?_⟩
  · intro q hq
    exact smul_eq_zero_of_restrictScalars_comp_eq_zero ψ γF iso σ₀
      I₀ c (op n) σ₀' hσ₀'def (fun b hb q' hq' => hc n b hb q' hq') a (hJ' ▸ ha) q hq
  · intro q
    exact smul_mem_range_restrictScalars_comp ψ γF iso σ₀
      I₀ c (op n) σ₀' hσ₀'def (fun b hb q' => hc n b hb q') a (hJ' ▸ ha) q

/-- **Adic replacement over an affine open.** Let `X` be a Noetherian scheme, `𝒥` an ideal sheaf,
`(ℱₙ)` an object of `Coh(X, 𝒥)`, `(Pₙ)` an inverse system of coherent modules with
`τ : (ℱₙ) → (Pₙ)`, and `U` an affine open with `I₀ = 𝒥(U)`. Let `M` be a `Γ(X, U)`-module with
`M/I₀^{n+1}M` finite, `e₀` a pro-isomorphism from the sections over `U` of `(Pₙ)` to
`(M/I₀^{n+1}M)` and `σ₀ : (Γ(U, ℱₙ)) → (M/I₀^{n+1}M)` compatible with `τ`. Then there are an
object `(𝒩ₙ)` of `Coh(U, 𝒥|_U)`, a pro-isomorphism `(Pₙ|_U) ≅ (𝒩ₙ)` and a morphism
`σ : (ℱₙ|_U) → (𝒩ₙ)` compatible with `τ`, such that for every `c`, if `I₀^c` kills the kernels
of the `σ₀ n` then `(𝒥|_U)^c` kills the terms of `ker σ`, and if `I₀^c` maps the
`M/I₀^{n+1}M` into the images of the `σ₀ n` then `(𝒥|_U)^c` kills the terms of `coker σ`. -/
theorem exists_coherentAdicSystem_of_affineOpenAdicReplacement (U : X.Opens)
    (hU : IsAffineOpen U) (M : Type u) [AddCommGroup M] [Module Γ(X, U) M]
    (hfin : ∀ n : ℕ, Module.Finite Γ(X, U)
      (M ⧸ (I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) M))))
    (e₀ : ProIso (P ⋙ sectionsOn X U) (adicQuotientTower (I.ideal ⟨U, hU⟩) M))
    (σ₀ : F.obj ⋙ sectionsOn X U ⟶ adicQuotientTower (I.ideal ⟨U, hU⟩) M)
    (hσ₀ : ∀ n : ℕ, (sectionsOn X U).map (τ.app (op (e₀.α n))) ≫ e₀.φ n =
      (sectionsOn X U).map (F.obj.map (homOfLE (e₀.αle n)).op) ≫ σ₀.app (op n)) :
    ∃ (N : CoherentAdicSystems (I.comap U.ι))
      (e : ProIso (P ⋙ Scheme.Modules.restrictFunctor U.ι) N.obj)
      (σ : (restrictFunctor I U.ι).obj F ⟶ N),
      (∀ n : ℕ, (Functor.whiskerRight τ (Scheme.Modules.restrictFunctor U.ι)).app (op (e.α n)) ≫
          e.φ n = ((restrictFunctor I U.ι).obj F).obj.map (homOfLE (e.αle n)).op ≫
            σ.hom.app (op n)) ∧
      (∀ c : ℕ, (∀ (n : ℕ) (a : Γ(X, U)), a ∈ I.ideal ⟨U, hU⟩ ^ c →
          ∀ q : Γ(F.obj.obj (op n), U), (σ₀.app (op n)).hom q = 0 → a • q = 0) →
        ∀ n : ℕ, idealPowerMultiple (I.comap U.ι) c ((kernel σ).obj.obj (op n)) = ⊥) ∧
      (∀ c : ℕ, (∀ (n : ℕ) (a : Γ(X, U)), a ∈ I.ideal ⟨U, hU⟩ ^ c →
          ∀ q : (adicQuotientTower (I.ideal ⟨U, hU⟩) M).obj (op n),
            a • q ∈ LinearMap.range (σ₀.app (op n)).hom) →
        ∀ n : ℕ, idealPowerMultiple (I.comap U.ι) c ((cokernel σ).obj.obj (op n)) = ⊥) :=
  exists_coherentAdicSystem_of_affineOpenAdicReplacement_of_image_eq I F P τ U hU U hU
    U.ι_image_top M hfin e₀ σ₀ hσ₀

end AffineOpen

end Stacks.Coherent

end

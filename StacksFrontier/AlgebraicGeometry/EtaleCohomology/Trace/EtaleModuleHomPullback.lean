module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomAcyclic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero

/-!
# `Hom_R(N, -)` commutes with inverse image and extension by zero

Let `A` be a commutative ring, `R` an `A`-algebra and `N` a finite `R`-module, `R` being left
Noetherian. The functors `Hom_R(N, -)` from sheaves of `R`-modules to sheaves of `A`-modules on
small étale sites commute on the nose with every direct image along a functor of sites, both
being computed on sections. The mate of this identity with respect to the adjunctions
`L ⊣ P` (inverse image and direct image, or extension by zero and restriction) is a comparison
`L(Hom_R(N, G)) ⟶ Hom_R(N, L G)`, and it is an isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.strictMate`: the mate of a commuting square of right adjoints.
* `Stacks.EtaleCohomology.coefficientMate`: the comparison `L(Φ G) ⟶ Φ(L G)` for a change of
  coefficients `Φ` applied sectionwise.

## Main results

* `Stacks.EtaleCohomology.strictMate_naturality`: the mate is natural in the commuting square.
* `Stacks.EtaleCohomology.isIso_coefficientMate_of_finite`: for an exact left adjoint `L`, the
  comparison `L(Hom_R(N, G)) ⟶ Hom_R(N, L G)` is invertible for every finite `R`-module `N` as
  soon as it is for `N = R`.
* `Stacks.EtaleCohomology.isIso_coefficientMate_inverseImage`:
  `f^{-1} Hom_R(N, G) ≅ Hom_R(N, f^{-1} G)`.
* `Stacks.EtaleCohomology.isIso_coefficientMate_extensionByZero`:
  `j_! Hom_R(N, G) ≅ Hom_R(N, j_! G)`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology

/-! ### Mates of commuting squares of right adjoints -/

section Mate

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {L₁ : C₁ ⥤ C₂} {P₁ : C₂ ⥤ C₁} (adj₁ : L₁ ⊣ P₁) {L₂ : D₁ ⥤ D₂} {P₂ : D₂ ⥤ D₁} (adj₂ : L₂ ⊣ P₂)

/-- The mate `Ψ₁ ⋙ L₂ ⟶ L₁ ⋙ Ψ₂` of a square `β : P₁ ⋙ Ψ₁ ⟶ Ψ₂ ⋙ P₂`. -/
def strictMate {Ψ₁ : C₁ ⥤ D₁} {Ψ₂ : C₂ ⥤ D₂} (β : P₁ ⋙ Ψ₁ ⟶ Ψ₂ ⋙ P₂) :
    Ψ₁ ⋙ L₂ ⟶ L₁ ⋙ Ψ₂ :=
  ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ β)).natTrans

/-- The components of `strictMate` in terms of the unit of `adj₁` and the counit of `adj₂`. -/
lemma strictMate_app {Ψ₁ : C₁ ⥤ D₁} {Ψ₂ : C₂ ⥤ D₂} (β : P₁ ⋙ Ψ₁ ⟶ Ψ₂ ⋙ P₂) (X : C₁) :
    (strictMate adj₁ adj₂ β).app X =
      L₂.map (Ψ₁.map (adj₁.unit.app X)) ≫ L₂.map (β.app (L₁.obj X)) ≫
        adj₂.counit.app (Ψ₂.obj (L₁.obj X)) := by
  simp [strictMate, mateEquiv]

/-- The mate is natural in the commuting square. -/
lemma strictMate_naturality {Ψ₁ Ψ₁' : C₁ ⥤ D₁} {Ψ₂ Ψ₂' : C₂ ⥤ D₂} (β : P₁ ⋙ Ψ₁ ⟶ Ψ₂ ⋙ P₂)
    (β' : P₁ ⋙ Ψ₁' ⟶ Ψ₂' ⋙ P₂) (θ₁ : Ψ₁ ⟶ Ψ₁') (θ₂ : Ψ₂ ⟶ Ψ₂')
    (h : ∀ Z : C₂, β.app Z ≫ P₂.map (θ₂.app Z) = θ₁.app (P₁.obj Z) ≫ β'.app Z) (X : C₁) :
    L₂.map (θ₁.app X) ≫ (strictMate adj₁ adj₂ β').app X =
      (strictMate adj₁ adj₂ β).app X ≫ θ₂.app (L₁.obj X) := by
  have h1 : θ₁.app X ≫ Ψ₁'.map (adj₁.unit.app X) =
      Ψ₁.map (adj₁.unit.app X) ≫ θ₁.app (P₁.obj (L₁.obj X)) :=
    (θ₁.naturality (adj₁.unit.app X)).symm
  have h3 : L₂.map (P₂.map (θ₂.app (L₁.obj X))) ≫ adj₂.counit.app (Ψ₂'.obj (L₁.obj X)) =
      adj₂.counit.app (Ψ₂.obj (L₁.obj X)) ≫ θ₂.app (L₁.obj X) :=
    adj₂.counit.naturality (θ₂.app (L₁.obj X))
  rw [strictMate_app, strictMate_app, ← L₂.map_comp_assoc, h1, L₂.map_comp, Category.assoc,
    ← L₂.map_comp_assoc (θ₁.app _), ← h, L₂.map_comp, Category.assoc, h3]
  simp only [Category.assoc]

/-- The mate of a square is invertible as soon as the mate of an isomorphic square is. -/
lemma isIso_strictMate_of_iso {Ψ₁ Ψ₁' : C₁ ⥤ D₁} {Ψ₂ Ψ₂' : C₂ ⥤ D₂} (β : P₁ ⋙ Ψ₁ ⟶ Ψ₂ ⋙ P₂)
    (β' : P₁ ⋙ Ψ₁' ⟶ Ψ₂' ⋙ P₂) (θ₁ : Ψ₁ ≅ Ψ₁') (θ₂ : Ψ₂ ≅ Ψ₂')
    (h : ∀ Z : C₂, β.app Z ≫ P₂.map (θ₂.hom.app Z) = θ₁.hom.app (P₁.obj Z) ≫ β'.app Z) (X : C₁)
    [IsIso ((strictMate adj₁ adj₂ β').app X)] : IsIso ((strictMate adj₁ adj₂ β).app X) := by
  have e := strictMate_naturality adj₁ adj₂ β β' θ₁.hom θ₂.hom h X
  have : (strictMate adj₁ adj₂ β).app X =
      L₂.map (θ₁.hom.app X) ≫ (strictMate adj₁ adj₂ β').app X ≫ θ₂.inv.app (L₁.obj X) := by
    rw [reassoc_of% e, Iso.hom_inv_id_app, Category.comp_id]
  rw [this]
  infer_instance

end Mate

/-! ### The comparison for `Hom_R(N, -)` -/

section Comparison

variable {A : Type} [CommRing A] {R : Type} [Ring R] [Algebra A R]
  {S T : Scheme.{u}} (uf : S.Etale ⥤ T.Etale)
  [uf.IsContinuous S.smallEtaleTopology T.smallEtaleTopology]
  {L_R : EtaleModules.{u, 0} R S ⥤ EtaleModules.{u, 0} R T}
  (adj_R : L_R ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} R) S.smallEtaleTopology
    T.smallEtaleTopology)
  {L_A : EtaleModules.{u, 0} A S ⥤ EtaleModules.{u, 0} A T}
  (adj_A : L_A ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.smallEtaleTopology
    T.smallEtaleTopology)

variable {B : Type} [Ring B]

/-- The comparison `L(Φ G) ⟶ Φ(L G)` for a change of coefficients `Φ` applied sectionwise: the
mate of the identity `P ∘ Φ = Φ ∘ P` for a direct image `P` with left adjoint `L`. -/
def coefficientMate (L_B : EtaleModules.{u, 0} B S ⥤ EtaleModules.{u, 0} B T)
    (adj_B : L_B ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} B) S.smallEtaleTopology
      T.smallEtaleTopology)
    (Φ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} B) [S.smallEtaleTopology.HasSheafCompose Φ]
    [T.smallEtaleTopology.HasSheafCompose Φ] :
    sheafCompose S.smallEtaleTopology Φ ⋙ L_B ⟶ L_R ⋙ sheafCompose T.smallEtaleTopology Φ :=
  strictMate adj_R adj_B (𝟙 _)

/-- The comparison is natural in the change of coefficients. -/
lemma coefficientMate_naturality (L_B : EtaleModules.{u, 0} B S ⥤ EtaleModules.{u, 0} B T)
    (adj_B : L_B ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} B) S.smallEtaleTopology
      T.smallEtaleTopology)
    {Φ Φ' : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} B} [S.smallEtaleTopology.HasSheafCompose Φ]
    [T.smallEtaleTopology.HasSheafCompose Φ] [S.smallEtaleTopology.HasSheafCompose Φ']
    [T.smallEtaleTopology.HasSheafCompose Φ'] (θ : Φ ⟶ Φ') (G : EtaleModules.{u, 0} R S) :
    L_B.map ((sheafCompose_map S.smallEtaleTopology θ).app G) ≫
        (coefficientMate uf adj_R L_B adj_B Φ').app G =
      (coefficientMate uf adj_R L_B adj_B Φ).app G ≫
        (sheafCompose_map T.smallEtaleTopology θ).app (L_R.obj G) :=
  strictMate_naturality (Ψ₁ := sheafCompose S.smallEtaleTopology Φ)
    (Ψ₂ := sheafCompose T.smallEtaleTopology Φ) (Ψ₁' := sheafCompose S.smallEtaleTopology Φ')
    (Ψ₂' := sheafCompose T.smallEtaleTopology Φ') adj_R adj_B (𝟙 _) (𝟙 _)
    (sheafCompose_map S.smallEtaleTopology θ) (sheafCompose_map T.smallEtaleTopology θ) (fun Z => by
      apply Sheaf.hom_ext
      ext U x
      rfl) G

/-- The isomorphism of sheaf-valued functors induced by an isomorphism of changes of
coefficients. -/
def sheafComposeIso (X : Scheme.{u}) {Φ Φ' : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} B}
    [X.smallEtaleTopology.HasSheafCompose Φ] [X.smallEtaleTopology.HasSheafCompose Φ']
    (θ : Φ ≅ Φ') : sheafCompose X.smallEtaleTopology Φ ≅ sheafCompose X.smallEtaleTopology Φ' where
  hom := sheafCompose_map X.smallEtaleTopology θ.hom
  inv := sheafCompose_map X.smallEtaleTopology θ.inv
  hom_inv_id := by
    ext G : 2
    apply Sheaf.hom_ext
    ext U : 2
    exact θ.hom_inv_id_app _
  inv_hom_id := by
    ext G : 2
    apply Sheaf.hom_ext
    ext U : 2
    exact θ.inv_hom_id_app _

/-- The comparison is invertible for `Φ` as soon as it is for an isomorphic change of
coefficients. -/
lemma isIso_coefficientMate_of_iso (L_B : EtaleModules.{u, 0} B S ⥤ EtaleModules.{u, 0} B T)
    (adj_B : L_B ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} B) S.smallEtaleTopology
      T.smallEtaleTopology)
    {Φ Φ' : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} B} [S.smallEtaleTopology.HasSheafCompose Φ]
    [T.smallEtaleTopology.HasSheafCompose Φ] [S.smallEtaleTopology.HasSheafCompose Φ']
    [T.smallEtaleTopology.HasSheafCompose Φ'] (θ : Φ ≅ Φ') (G : EtaleModules.{u, 0} R S)
    [IsIso ((coefficientMate uf adj_R L_B adj_B Φ').app G)] :
    IsIso ((coefficientMate uf adj_R L_B adj_B Φ).app G) :=
  have : IsIso ((strictMate adj_R adj_B (Ψ₁ := sheafCompose S.smallEtaleTopology Φ')
      (Ψ₂ := sheafCompose T.smallEtaleTopology Φ') (𝟙 _)).app G) :=
    ‹IsIso ((coefficientMate uf adj_R L_B adj_B Φ').app G)›
  isIso_strictMate_of_iso (Ψ₁ := sheafCompose S.smallEtaleTopology Φ)
    (Ψ₂ := sheafCompose T.smallEtaleTopology Φ) (Ψ₁' := sheafCompose S.smallEtaleTopology Φ')
    (Ψ₂' := sheafCompose T.smallEtaleTopology Φ') adj_R adj_B (𝟙 _) (𝟙 _)
    (sheafComposeIso S θ) (sheafComposeIso T θ) (fun Z => by
      apply Sheaf.hom_ext
      ext U x
      rfl) G

/-- The comparison for `Hom_R(R, -)` is invertible as soon as it is for restriction of scalars. -/
private lemma isIso_coefficientMate_regular
    (hres : ∀ H, IsIso ((coefficientMate uf adj_R L_A adj_A
      (ModuleCat.restrictScalars.{u + 1} (algebraMap A R))).app H)) (H : EtaleModules.{u, 0} R S) :
    IsIso ((coefficientMate uf adj_R L_A adj_A
      (homFunctor (regularModuleU.{u} R)
        (centralScalars (A := A) (regularModuleU.{u} R)))).app H) :=
  have := hres H
  isIso_coefficientMate_of_iso uf adj_R L_A adj_A homFunctorRegularIso H

/-- The comparison for `Hom_R(R^k, -)` is invertible as soon as the one for `Hom_R(R, -)` is. -/
lemma isIso_coefficientMate_free
    (hreg : ∀ G, IsIso ((coefficientMate uf adj_R L_A adj_A
      (homFunctor (regularModuleU.{u} R) (centralScalars (A := A) (regularModuleU.{u} R)))).app G))
    (k : ℕ) (G : EtaleModules.{u, 0} R S) :
    IsIso ((coefficientMate uf adj_R L_A adj_A
      (homFunctor (freeModuleU.{u} R k)
        (centralScalars (A := A) (freeModuleU.{u} R k)))).app G) := by
  obtain ⟨cRinv, hcR1, hcR2⟩ := (hreg G).out
  have : (uf.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.smallEtaleTopology
      T.smallEtaleTopology).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have : L_A.Additive := adj_A.left_adjoint_additive
  set cF := (coefficientMate uf adj_R L_A adj_A
    (homFunctor (freeModuleU.{u} R k) (centralScalars (A := A) (freeModuleU.{u} R k)))).app G
    with hcF
  set cR := (coefficientMate uf adj_R L_A adj_A
    (homFunctor (regularModuleU.{u} R) (centralScalars (A := A) (regularModuleU.{u} R)))).app G
    with hcR
  let θ := fun {N₁ N₂ : ModuleCat.{u + 1} R} (v : N₁ ⟶ N₂) (X : Scheme.{u})
      (H : EtaleModules.{u, 0} R X) =>
    (sheafCompose_map X.smallEtaleTopology (homFunctorPrecomp (A := A) v)).app H
  have hι : ∀ j, cF ≫ θ (freeModuleι k j) T (L_R.obj G) =
      L_A.map (θ (freeModuleι k j) S G) ≫ cR := fun j =>
    (coefficientMate_naturality uf adj_R L_A adj_A
      (homFunctorPrecomp (A := A) (freeModuleι k j)) G).symm
  have hπ : ∀ j, L_A.map (θ (freeModuleπ k j) S G) ≫ cF =
      cR ≫ θ (freeModuleπ k j) T (L_R.obj G) := fun j =>
    coefficientMate_naturality uf adj_R L_A adj_A (homFunctorPrecomp (A := A) (freeModuleπ k j)) G
  have hsum : ∀ (X : Scheme.{u}) (H : EtaleModules.{u, 0} R X),
      ∑ j, θ (freeModuleι k j) X H ≫ θ (freeModuleπ k j) X H = 𝟙 _ := fun X H => by
    exact show ∑ j, homPrecompApp (A := A) (freeModuleι k j) H ≫
        homPrecompApp (freeModuleπ k j) H = 𝟙 _ by
      simp only [← homPrecompApp_comp, ← homPrecompApp_sum, sum_freeModuleπ_comp_ι,
        homPrecompApp_id]
  refine ⟨∑ j, θ (freeModuleι k j) T (L_R.obj G) ≫ cRinv ≫ L_A.map (θ (freeModuleπ k j) S G),
    ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    have : ∀ j, cF ≫ θ (freeModuleι k j) T (L_R.obj G) ≫ cRinv ≫ L_A.map (θ (freeModuleπ k j) S G) =
        L_A.map (θ (freeModuleι k j) S G ≫ θ (freeModuleπ k j) S G) := fun j => by
      rw [← Category.assoc, hι j, Category.assoc, reassoc_of% hcR1, Functor.map_comp]
    rw [Finset.sum_congr rfl fun j _ => this j, ← Functor.map_sum, hsum,
      CategoryTheory.Functor.map_id]
    rfl
  · rw [Preadditive.sum_comp]
    have : ∀ j, (θ (freeModuleι k j) T (L_R.obj G) ≫ cRinv ≫ L_A.map (θ (freeModuleπ k j) S G)) ≫
        cF = θ (freeModuleι k j) T (L_R.obj G) ≫ θ (freeModuleπ k j) T (L_R.obj G) := fun j => by
      rw [Category.assoc, Category.assoc, hπ j, reassoc_of% hcR2]
    rw [Finset.sum_congr rfl fun j _ => this j, hsum]
    rfl

/-- `Hom_R(-, G)` is left exact: for an epimorphism `g : F ⟶ N` with kernel `K`, the sequence
`0 → Hom_R(N, G) → Hom_R(F, G) → Hom_R(K, G)` of sheaves is exact. -/
lemma exact_sheafCompose_homFunctorPrecomp {X : Scheme.{u}} {F N : ModuleCat.{u + 1} R}
    (g : F ⟶ N) [Epi g] (H : EtaleModules.{u, 0} R X) :
    (ShortComplex.mk ((sheafCompose_map X.smallEtaleTopology (homFunctorPrecomp (A := A) g)).app H)
      ((sheafCompose_map X.smallEtaleTopology (homFunctorPrecomp (A := A) (kernel.ι g))).app H)
      (by
        apply Sheaf.hom_ext
        ext U f
        change kernel.ι g ≫ g ≫ (show N ⟶ H.obj.obj U from f) = 0
        rw [kernel.condition_assoc, zero_comp])).Exact ∧
      Mono ((sheafCompose_map X.smallEtaleTopology (homFunctorPrecomp (A := A) g)).app H) := by
  have hcok := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel g)
  refine ⟨shortComplex_exact_of_sections _ fun U x hx => ?_, ?_⟩
  · have hx' : kernel.ι g ≫ (show F ⟶ H.obj.obj U from x) = 0 := hx
    exact ⟨hcok.desc (CokernelCofork.ofπ _ hx'), hcok.fac _ WalkingParallelPair.one⟩
  · refine (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mono_of_mono_map ?_
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun U => ?_
    rw [ModuleCat.mono_iff_injective]
    intro a b hab
    exact (cancel_epi g).1 hab

/-- For an exact left adjoint `L`, the comparison `L(Hom_R(N, G)) ⟶ Hom_R(N, L G)` is invertible
for every finite module `N` as soon as it is for `R`. -/
theorem isIso_coefficientMate_of_finite [IsNoetherianRing R]
    [L_A.Additive] [L_A.PreservesMonomorphisms] [L_A.PreservesHomology]
    (hreg : ∀ G, IsIso ((coefficientMate uf adj_R L_A adj_A
      (homFunctor (regularModuleU.{u} R) (centralScalars (A := A) (regularModuleU.{u} R)))).app G))
    (N : ModuleCat.{u + 1} R) [Module.Finite R N] (G : EtaleModules.{u, 0} R S) :
    IsIso ((coefficientMate uf adj_R L_A adj_A
      (homFunctor N (centralScalars (A := A) N))).app G) := by
  have hfree := isIso_coefficientMate_free uf adj_R adj_A hreg
  have hsurj : ∀ (M : ModuleCat.{u + 1} R) [Module.Finite R M], ∃ (k : ℕ)
      (g : freeModuleU.{u} R k ⟶ M), Epi g := fun M _ => by
    obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R M
    exact ⟨k, ModuleCat.ofHom (π ∘ₗ (LinearEquiv.piCongrRight fun _ : Fin k =>
      ULift.moduleEquiv (R := R) (M := R)).toLinearMap),
      (ModuleCat.epi_iff_surjective _).2 (hπ.comp (LinearEquiv.surjective _))⟩
  have hmono : ∀ (M : ModuleCat.{u + 1} R) [Module.Finite R M], Mono ((coefficientMate uf adj_R
      L_A adj_A (homFunctor M (centralScalars (A := A) M))).app G) := fun M _ => by
    obtain ⟨k, g, hg⟩ := hsurj M
    have hF := hfree k G
    have e := coefficientMate_naturality uf adj_R L_A adj_A (homFunctorPrecomp (A := A) g) G
    have hm := (exact_sheafCompose_homFunctorPrecomp (A := A) g G).2
    have hmL : Mono (L_A.map ((sheafCompose_map S.smallEtaleTopology
        (homFunctorPrecomp (A := A) g)).app G)) := by
      have := hm
      exact L_A.map_mono _
    have hFm : Mono ((coefficientMate uf adj_R L_A adj_A (homFunctor (freeModuleU.{u} R k)
        (centralScalars (A := A) (freeModuleU.{u} R k)))).app G) :=
      @IsIso.mono_of_iso _ _ _ _ _ hF
    have hc : Mono ((coefficientMate uf adj_R L_A adj_A
        (homFunctor M (centralScalars (A := A) M))).app G ≫
        (sheafCompose_map T.smallEtaleTopology (homFunctorPrecomp (A := A) g)).app
          (L_R.obj G)) := by
      rw [← e]
      exact @mono_comp _ _ _ _ _ _ hmL _ hFm
    exact @mono_of_mono _ _ _ _ _ _ _ hc
  obtain ⟨k, g, hg⟩ := hsurj N
  have : IsNoetherian R (freeModuleU.{u} R k) := inferInstance
  have : Module.Finite R ↑(kernel g : ModuleCat.{u + 1} R) :=
    Module.Finite.of_injective (kernel.ι g).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have := hfree k G
  have := hmono (kernel g : ModuleCat.{u + 1} R)
  let θ := fun {N₁ N₂ : ModuleCat.{u + 1} R} (v : N₁ ⟶ N₂) (X : Scheme.{u})
      (H : EtaleModules.{u, 0} R X) =>
    (sheafCompose_map X.smallEtaleTopology (homFunctorPrecomp (A := A) v)).app H
  set cN := (coefficientMate uf adj_R L_A adj_A (homFunctor N (centralScalars (A := A) N))).app G
  set cF := (coefficientMate uf adj_R L_A adj_A
    (homFunctor (freeModuleU.{u} R k) (centralScalars (A := A) (freeModuleU.{u} R k)))).app G
  set cK := (coefficientMate uf adj_R L_A adj_A
    (homFunctor (kernel g : ModuleCat.{u + 1} R) (centralScalars (A := A) _))).app G
  have eg : L_A.map (θ g S G) ≫ cF = cN ≫ θ g T (L_R.obj G) :=
    coefficientMate_naturality uf adj_R L_A adj_A (homFunctorPrecomp (A := A) g) G
  have eι : L_A.map (θ (kernel.ι g) S G) ≫ cK = cF ≫ θ (kernel.ι g) T (L_R.obj G) :=
    coefficientMate_naturality uf adj_R L_A adj_A (homFunctorPrecomp (A := A) (kernel.ι g)) G
  obtain ⟨hex, hm⟩ := exact_sheafCompose_homFunctorPrecomp (A := A) g G
  obtain ⟨hexT, hmT⟩ := exact_sheafCompose_homFunctorPrecomp (A := A) g (L_R.obj G)
  have hexL := hex.map L_A
  have hmL : Mono (L_A.map (θ g S G)) := by
    have := hm
    exact L_A.map_mono (θ g S G)
  have hk := @ShortComplex.Exact.fIsKernel _ _ _ _ _ hexL hmL
  have hzT : θ g T (L_R.obj G) ≫ θ (kernel.ι g) T (L_R.obj G) = 0 := by
    apply Sheaf.hom_ext
    ext U f
    show kernel.ι g ≫ g ≫ (show N ⟶ (L_R.obj G).obj.obj U from f) = 0
    rw [kernel.condition_assoc, zero_comp]
  let d : (sheafCompose T.smallEtaleTopology (homFunctor N (centralScalars (A := A) N))).obj
      (L_R.obj G) ⟶ L_A.obj ((sheafCompose S.smallEtaleTopology
        (homFunctor N (centralScalars (A := A) N))).obj G) :=
    hk.lift (KernelFork.ofι (θ g T (L_R.obj G) ≫ inv cF) (by
      rw [← cancel_mono cK, zero_comp, Category.assoc, Category.assoc]
      show θ g T (L_R.obj G) ≫ inv cF ≫ L_A.map (θ (kernel.ι g) S G) ≫ cK = 0
      rw [eι, IsIso.inv_hom_id_assoc, hzT]))
  have hd : d ≫ L_A.map (θ g S G) = θ g T (L_R.obj G) ≫ inv cF :=
    hk.fac _ WalkingParallelPair.zero
  refine ⟨d, ?_, ?_⟩
  · apply Fork.IsLimit.hom_ext hk
    show (cN ≫ d) ≫ L_A.map (θ g S G) = 𝟙 _ ≫ L_A.map (θ g S G)
    rw [Category.assoc, hd, ← Category.assoc, ← eg, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · rw [← cancel_mono (θ g T (L_R.obj G)), Category.assoc, ← eg, ← Category.assoc, hd,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

end Comparison

/-! ### Inverse image and extension by zero -/

section Instances

variable {A : Type} [CommRing A] {R : Type} [Ring R] [Algebra A R] [IsNoetherianRing R]

/-- `Hom_R(N, -)` commutes with inverse image: `f^{-1} Hom_R(N, G) ≅ Hom_R(N, f^{-1} G)` for a
finite `R`-module `N`. -/
theorem isIso_coefficientMate_inverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ModuleCat.{u + 1} R) [Module.Finite R N] (G : EtaleModules.{u, 0} R Y) :
    IsIso ((coefficientMate (smallEtaleBaseChange f) (etaleModuleInverseImageAdj.{u, 0} R f)
      (etaleModuleInverseImage.{u, 0} A f) (etaleModuleInverseImageAdj.{u, 0} A f)
      (homFunctor N (centralScalars (A := A) N))).app G) := by
  have hres : ∀ H : EtaleModules.{u, 0} R Y, IsIso ((coefficientMate (smallEtaleBaseChange f)
      (etaleModuleInverseImageAdj.{u, 0} R f) (etaleModuleInverseImage.{u, 0} A f)
      (etaleModuleInverseImageAdj.{u, 0} A f)
      (ModuleCat.restrictScalars.{u + 1} (algebraMap A R))).app H) := fun H =>
    (inferInstance : IsIso ((etaleModuleInverseImageRestrictScalars (algebraMap A R) f).hom.app H))
  have : (etaleModuleInverseImage.{u, 0} A f).Additive :=
    (etaleModuleInverseImageAdj.{u, 0} A f).left_adjoint_additive
  have : PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} A f) :=
    etaleModuleInverseImage_preservesFiniteLimits.{u, 0} A f
  have : PreservesFiniteColimits (etaleModuleInverseImage.{u, 0} A f) :=
    have := (etaleModuleInverseImageAdj.{u, 0} A f).isLeftAdjoint
    inferInstance
  exact isIso_coefficientMate_of_finite _ _ _ (isIso_coefficientMate_regular _ _ _ hres) N G

/-- `Hom_R(N, -)` commutes with extension by zero: `j_! Hom_R(N, G) ≅ Hom_R(N, j_! G)` for a
finite `R`-module `N` and an étale `j`. -/
theorem isIso_coefficientMate_extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (N : ModuleCat.{u + 1} R) [Module.Finite R N] (G : EtaleModules.{u, 0} R U) :
    IsIso ((coefficientMate (Scheme.Etale.smallEtaleCompose j)
      (etaleModuleExtensionByZeroAdj.{u, 0} R j) (etaleModuleExtensionByZero.{u, 0} A j)
      (etaleModuleExtensionByZeroAdj.{u, 0} A j)
      (homFunctor N (centralScalars (A := A) N))).app G) := by
  have hres : ∀ H : EtaleModules.{u, 0} R U, IsIso ((coefficientMate
      (Scheme.Etale.smallEtaleCompose j) (etaleModuleExtensionByZeroAdj.{u, 0} R j)
      (etaleModuleExtensionByZero.{u, 0} A j) (etaleModuleExtensionByZeroAdj.{u, 0} A j)
      (ModuleCat.restrictScalars.{u + 1} (algebraMap A R))).app H) := fun H =>
    (inferInstance :
      IsIso ((etaleModuleExtensionByZeroRestrictScalars (algebraMap A R) j).hom.app H))
  have : PreservesFiniteColimits (etaleModuleExtensionByZero.{u, 0} A j) :=
    have := (etaleModuleExtensionByZeroAdj.{u, 0} A j).isLeftAdjoint
    inferInstance
  exact isIso_coefficientMate_of_finite _ _ _ (isIso_coefficientMate_regular _ _ _ hres) N G

end Instances

end Stacks.EtaleCohomology

module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Module.Projective
public import StacksFrontier.Homology.KFlat.BifunctorKInjective
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact
public import StacksFrontier.Algebra.Homology.HomotopyCategory.KInjectiveClosure

/-!
# Tensoring a sheaf with a finitely generated projective module

For a finitely generated projective `Λ`-module `Q` and a sheaf `S` of `Λ`-modules, the presheaf
`U ↦ Q ⊗_Λ S(U)` is already a sheaf: `Q` is a direct summand of `Λⁿ`, the presheaf is a
retract of `U ↦ S(U)ⁿ`, and a retract of a sheaf is a sheaf. Hence `S ⊗_Λ Q` needs no
sheafification, and its sections over every object are `Q ⊗_Λ S(U)`.

## Main results

* `Stacks.ConstantModuleTensor.isSheaf_of_retract`: a retract of a sheaf is a sheaf.
* `Stacks.ConstantModuleTensor.isSheaf_comp_tensorLeft`: `S ⋙ (Q ⊗ -)` is a sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe w v₁ u₁ t

namespace Stacks.ConstantModuleTensor

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- A retract of a sheaf of types is a sheaf. -/
theorem _root_.CategoryTheory.Presieve.isSheaf_of_retract {P G : Cᵒᵖ ⥤ Type t} (i : P ⟶ G)
    (r : G ⟶ P) (h : i ≫ r = 𝟙 P) (hG : Presieve.IsSheaf J G) : Presieve.IsSheaf J P := by
  intro X S hS x hx
  obtain ⟨t, ht, -⟩ := hG S hS (x.map i) (hx.map i)
  refine ⟨r.app _ t, ?_, fun s hs => ?_⟩
  · have := ht.map r
    rwa [Presieve.FamilyOfElements.map_comp, h, Presieve.FamilyOfElements.map_id] at this
  · have h1 := (hG S hS (x.map i) (hx.map i)).unique (hs.map i) ht
    have h2 := congrArg (r.app _) h1
    rwa [← types_comp_apply (i.app _) (r.app _), ← NatTrans.comp_app, h, NatTrans.id_app,
      types_id_apply] at h2

variable (Λ : Type w) [CommRing Λ]

/-- A retract of a sheaf of `Λ`-modules is a sheaf. -/
theorem isSheaf_of_retract {P G : Cᵒᵖ ⥤ ModuleCat.{w} Λ} (i : P ⟶ G) (r : G ⟶ P)
    (h : i ≫ r = 𝟙 P) (hG : Presheaf.IsSheaf J G) : Presheaf.IsSheaf J P := fun E =>
  Presieve.isSheaf_of_retract J (Functor.whiskerRight i (coyoneda.obj (op E)))
    (Functor.whiskerRight r (coyoneda.obj (op E)))
    (by rw [← Functor.whiskerRight_comp, h, Functor.whiskerRight_id']) (hG E)

/-- The pairing `Λⁿ ⟶ Λ`, `v ↦ ∑ⱼ vⱼ cⱼ`, attached to `c : Λⁿ`. -/
def pairing {n : ℕ} (c : Fin n → Λ) : (Fin n → Λ) →ₗ[Λ] Λ :=
  ∑ j, c j • LinearMap.proj j

omit [CommRing Λ] in
/-- `pairing c v = ∑ⱼ cⱼ vⱼ`. -/
theorem pairing_apply [CommRing Λ] {n : ℕ} (c v : Fin n → Λ) :
    pairing Λ c v = ∑ j, c j * v j := by
  simp [pairing]

/-- For a map `s : Q ⟶ Λⁿ`, the map `Q ⊗ X ⟶ Hom(Λⁿ, X)`, `q ⊗ x ↦ (v ↦ ⟨s q, v⟩ • x)`,
natural in `X`. -/
def tensorToHom {Q : ModuleCat.{w} Λ} {n : ℕ} (s : Q →ₗ[Λ] (Fin n → Λ)) :
    tensorLeft Q ⟶ ihom (ModuleCat.of Λ (Fin n → Λ)) where
  app X := ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ Λ
    (fun (q : Q) (x : X) => (ModuleCat.ofHom ((pairing Λ (s q)).smulRight x) :
      ModuleCat.of Λ (Fin n → Λ) ⟶ X))
    (fun q q' x => by ext v; simp [pairing_apply, add_mul, Finset.sum_add_distrib, add_smul])
    (fun a q x => by ext v; simp [pairing_apply, mul_assoc, Finset.mul_sum, smul_smul])
    (fun q x x' => by ext v; simp)
    (fun a q x => by ext v; simp [smul_comm a])))
  naturality X Y g := by
    ext1
    apply TensorProduct.ext'
    intro q x
    apply ModuleCat.hom_ext
    ext v
    change (pairing Λ (s q) _) • g x = g ((pairing Λ (s q) _) • x)
    rw [map_smul]

/-- For a map `π : Λⁿ ⟶ Q`, the map `Hom(Λⁿ, X) ⟶ Q ⊗ X`, `φ ↦ ∑ⱼ π(eⱼ) ⊗ φ(eⱼ)`, natural in
`X`. -/
def homToTensor {Q : ModuleCat.{w} Λ} {n : ℕ} (π : (Fin n → Λ) →ₗ[Λ] Q) :
    ihom (ModuleCat.of Λ (Fin n → Λ)) ⟶ tensorLeft Q where
  app X := ModuleCat.ofHom
    { toFun φ := ∑ j, π (Pi.single j 1) ⊗ₜ[Λ] φ.hom (Pi.single j 1)
      map_add' φ φ' := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
      map_smul' a φ := by simp [Finset.smul_sum, TensorProduct.tmul_smul] }
  naturality X Y g := by
    apply ModuleCat.hom_ext
    ext φ
    change ∑ j, π (Pi.single j 1) ⊗ₜ[Λ] g.hom (φ.hom (Pi.single j 1)) =
      (Q ◁ g).hom (∑ j, π (Pi.single j 1) ⊗ₜ[Λ] φ.hom (Pi.single j 1))
    simp [map_sum]

/-- The composite `Q ⊗ X ⟶ Hom(Λⁿ, X) ⟶ Q ⊗ X` is the identity when `π ∘ s = id`. -/
theorem tensorToHom_comp_homToTensor {Q : ModuleCat.{w} Λ} {n : ℕ} (s : Q →ₗ[Λ] (Fin n → Λ))
    (π : (Fin n → Λ) →ₗ[Λ] Q) (h : π.comp s = LinearMap.id) :
    tensorToHom Λ s ≫ homToTensor Λ π = 𝟙 _ := by
  ext X : 2
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro q x
  change ∑ j, π (Pi.single j 1) ⊗ₜ[Λ] ((pairing Λ (s q) (Pi.single j 1)) • x) = q ⊗ₜ[Λ] x
  have hq : ∑ j, s q j • π (Pi.single j 1) = q := by
    have h1 := congrArg (fun f => f q) h
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    have h2 : s q = ∑ j, s q j • (Pi.single j 1 : Fin n → Λ) := by
      ext i
      simp [Pi.single_apply]
    conv_rhs => rw [← h1, h2]
    simp [map_sum, map_smul]
  have hp : ∀ j, pairing Λ (s q) (Pi.single j 1) = s q j := fun j => by
    simp [pairing_apply, Pi.single_apply]
  calc ∑ j, π (Pi.single j 1) ⊗ₜ[Λ] ((pairing Λ (s q) (Pi.single j 1)) • x)
      = ∑ j, (s q j • π (Pi.single j 1)) ⊗ₜ[Λ] x := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hp, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    _ = q ⊗ₜ[Λ] x := by rw [← TensorProduct.sum_tmul, hq]

variable {Λ}

/-- **`Q ⊗ S` is a sheaf** for a finitely generated projective module `Q` and a sheaf `S`. -/
theorem isSheaf_comp_tensorLeft (Q : ModuleCat.{w} Λ) [Module.Finite Λ Q] [Module.Projective Λ Q]
    (S : Sheaf J (ModuleCat.{w} Λ)) : Presheaf.IsSheaf J (S.obj ⋙ tensorLeft Q) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Λ Q
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  exact isSheaf_of_retract J Λ (Functor.whiskerLeft S.obj (tensorToHom Λ s))
    (Functor.whiskerLeft S.obj (homToTensor Λ π))
    (by rw [← Functor.whiskerLeft_comp, tensorToHom_comp_homToTensor Λ s π hs,
      Functor.whiskerLeft_id'])
    ((sheafCompose J (ihom (ModuleCat.of Λ (Fin n → Λ)))).obj S).property

/-- `S ↦ Q ⊗ S` without sheafification, for a finitely generated projective module `Q`. -/
@[simps]
def tensorProjectiveFunctor (Q : ModuleCat.{w} Λ) [Module.Finite Λ Q] [Module.Projective Λ Q] :
    Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} Λ) where
  obj S := ⟨S.obj ⋙ tensorLeft Q, isSheaf_comp_tensorLeft J Q S⟩
  map f := ObjectProperty.homMk (Functor.whiskerRight f.hom (tensorLeft Q))
  map_id S := by ext1; simp
  map_comp f g := by ext1; simp

/-- The functor `S ↦ Q ⊗ S` on sheaves of `Λ`-modules is additive. -/
instance additive_tensorProjectiveFunctor (Q : ModuleCat.{w} Λ) [Module.Finite Λ Q]
    [Module.Projective Λ Q] : (tensorProjectiveFunctor J Q).Additive where
  map_add {_ _} f g := by
    ext1; ext U : 2
    simp [MonoidalPreadditive.whiskerLeft_add]
    rfl

/-- Postcomposition with `Hom(N, -)` on sheaves of `Λ`-modules is additive. -/
instance additive_sheafCompose_ihom (N : ModuleCat.{w} Λ) : (sheafCompose J (ihom N)).Additive where
  map_add {_ _} f g := by
    ext1; ext U : 2
    simp only [sheafCompose_map_hom, Functor.whiskerRight_app, Sheaf.Hom.add_app]
    apply ModuleCat.hom_ext; ext φ : 1
    change φ ≫ (f.hom.app U + g.hom.app U) = φ ≫ f.hom.app U + φ ≫ g.hom.app U
    exact Preadditive.comp_add _ _ _ _ _ _

section Sheafify

variable [HasSheafify J (ModuleCat.{w} Λ)]

/-- The functor `S ↦ S ⊗_Λ N` on sheaves of `Λ`-modules is additive. -/
instance additive_flipObj_sheafTensor (N : ModuleCat.{w} Λ) :
    ((sheafTensor J Λ).flip.obj N).Additive where
  map_add {_ _} f g := by
    simp only [Functor.flip_obj_map, Functor.map_add, NatTrans.app_add]

/-- `S ⊗_Λ Q` needs no sheafification for `Q` finitely generated projective. -/
def flipObjIsoTensorProjectiveFunctor (Q : ModuleCat.{w} Λ) [Module.Finite Λ Q]
    [Module.Projective Λ Q] :
    (sheafTensor J Λ).flip.obj Q ≅ tensorProjectiveFunctor J Q :=
  NatIso.ofComponents
    (fun S => (asIso (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit).app
      ((tensorProjectiveFunctor J Q).obj S))
    (fun {_ _} f => (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.naturality
      ((tensorProjectiveFunctor J Q).map f))

/-- The complex `p ↦ Kᵖ ⊗_Λ Q` is K-injective for `K` K-injective and `Q` finitely generated
projective: it is a retract of `p ↦ Hom(Λⁿ, Kᵖ)`, and `Hom(Λⁿ, -)` is right adjoint to the exact
functor `Λⁿ ⊗ -`. -/
theorem isKInjective_rowComplex (Q : ModuleCat.{w} Λ) [Module.Finite Λ Q] [Module.Projective Λ Q]
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) [K.IsKInjective] :
    CochainComplex.IsKInjective
      (CochainComplex.KFlatBifunctor.rowComplex (sheafTensor J Λ) K Q) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Λ Q
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let N := ModuleCat.of Λ (Fin n → Λ)
  have : (Sheaf.composeAndSheafify J (tensorLeft N)).Additive :=
    Functor.additive_of_iso (flipObjIso J Λ N)
  have : PreservesFiniteLimits (Sheaf.composeAndSheafify J (tensorLeft N)) :=
    preservesFiniteLimits_of_natIso (flipObjIso J Λ N)
  have : PreservesFiniteColimits (Sheaf.composeAndSheafify J (tensorLeft N)) :=
    preservesFiniteColimits_of_natIso (flipObjIso J Λ N)
  have hI := Stacks.Injectives.isKInjective_mapHomologicalComplex_of_adjunction
    (sheafCompose J (ihom N)) (Sheaf.composeAndSheafify J (tensorLeft N))
    (Sheaf.adjunction J (ihom.adjunction N)) K
  let ι : tensorProjectiveFunctor J Q ⟶ sheafCompose J (ihom N) :=
    { app S := ObjectProperty.homMk (Functor.whiskerLeft S.obj (tensorToHom Λ s))
      naturality _ _ f := by ext1; ext U : 2; exact (tensorToHom Λ s).naturality _ }
  let ρ : sheafCompose J (ihom N) ⟶ tensorProjectiveFunctor J Q :=
    { app S := ObjectProperty.homMk (Functor.whiskerLeft S.obj (homToTensor Λ π))
      naturality _ _ f := by ext1; ext U : 2; exact (homToTensor Λ π).naturality _ }
  have hιρ : ι ≫ ρ = 𝟙 _ := by
    ext S : 2; ext1; ext U : 2
    exact congrArg (fun t => NatTrans.app t (S.obj.obj U)) (tensorToHom_comp_homToTensor Λ s π hs)
  have hK := CochainComplex.isKInjective_of_retract
    ⟨(NatTrans.mapHomologicalComplex ι (ComplexShape.up ℤ)).app K,
      (NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ)).app K,
      by rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, hιρ,
        NatTrans.mapHomologicalComplex_id, NatTrans.id_app]⟩
  exact CochainComplex.isKInjective_of_iso
    (((NatIso.mapHomologicalComplex (flipObjIsoTensorProjectiveFunctor J Q)
      (ComplexShape.up ℤ)).app K).symm ≪≫ HomologicalComplex.Hom.isoOfComponents
        (fun _ => Iso.refl _) (fun i j _ => by
          simp only [Iso.refl_hom]
          rfl))

/-- **`Tot(K ⊗_Λ P)` is K-injective** for `K` K-injective and `P` a bounded complex of finitely
generated projective `Λ`-modules. -/
theorem isKInjective_totalComplex (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    [K.IsKInjective] (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (a b : ℤ) [P.IsStrictlyLE b]
    [P.IsStrictlyGE a] (hP : ∀ q, Module.Finite Λ (P.X q) ∧ Module.Projective Λ (P.X q)) :
    CochainComplex.IsKInjective
      (CochainComplex.KFlatBifunctor.totalComplex (sheafTensor J Λ) K P) :=
  CochainComplex.KFlatBifunctor.isKInjective_totalComplex_of_isStrictlyLE_of_isStrictlyGE
    (sheafTensor J Λ) K P b a fun q => by
      have := (hP q).1
      have := (hP q).2
      exact CochainComplex.KFlatBifunctor.totIsKInjective_single _ K _ q
        (isKInjective_rowComplex J (P.X q) K)

/-- The identification `S ⊗_Λ Q ≅ Q ⊗ S` (no sheafification) is natural in `Q`. -/
theorem flipObjIsoTensorProjectiveFunctor_naturality_right {Q Q' : ModuleCat.{w} Λ}
    [Module.Finite Λ Q] [Module.Projective Λ Q] [Module.Finite Λ Q'] [Module.Projective Λ Q']
    (g : Q ⟶ Q') (S : Sheaf J (ModuleCat.{w} Λ)) :
    ((sheafTensor J Λ).obj S).map g ≫ ((flipObjIsoTensorProjectiveFunctor J Q').hom.app S) =
      ((flipObjIsoTensorProjectiveFunctor J Q).hom.app S) ≫
        ObjectProperty.homMk (X := (tensorProjectiveFunctor J Q).obj S)
          (Y := (tensorProjectiveFunctor J Q').obj S)
          (Functor.whiskerLeft S.obj ((curriedTensor (ModuleCat.{w} Λ)).map g)) :=
  (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.naturality
    (X := (tensorProjectiveFunctor J Q).obj S) (Y := (tensorProjectiveFunctor J Q').obj S)
    (ObjectProperty.homMk (Functor.whiskerLeft S.obj ((curriedTensor (ModuleCat.{w} Λ)).map g)))

end Sheafify

end Stacks.ConstantModuleTensor

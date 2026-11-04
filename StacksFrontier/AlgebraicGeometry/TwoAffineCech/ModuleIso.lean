module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.Family
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor

/-!
# The two-term Čech complex of isomorphic modules

An isomorphism `e : F ≅ F'` of `𝒪_X`-modules on a scheme over `Spec A` induces `A`-linear
equivalences of the alternating Čech complexes, compatible with the differentials.

## Main definitions

* `Stacks.Cech.alternatingCechModuleObjCongr`: the degreewise equivalence.

## Main results

* `Stacks.TwoAffineCech.cechD_congr`: the two-term Čech differential is invariant under
  isomorphism of the module.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I : Type u}
  (U : I → X.Opens) {F F' : X.Modules}

/-- A morphism of modules acts `A`-linearly on alternating Čech cochains. -/
def alternatingCechModuleObjLinearMap (φ : F ⟶ F') (p : ℕ) :
    alternatingCechModuleObj f U F p →ₗ[A] alternatingCechModuleObj f U F' p :=
  letI := cochainModule f U F p
  letI := cochainModule f U F' p
  { toFun := fun s => ⟨cochainMap U φ.mapPresheaf p s.1,
      cochainMap_isAlternating U φ.mapPresheaf p s.2⟩
    map_add' := fun s t => Subtype.ext (map_add (cochainMap U φ.mapPresheaf p) s.1 t.1)
    map_smul' := fun a s => Subtype.ext (by
      funext i
      change φ.app _ ((baseRingHom f (CechCochains.inter U i)).hom a • s.1 i) =
        (baseRingHom f (CechCochains.inter U i)).hom a • φ.app _ (s.1 i)
      exact Scheme.Modules.Hom.app_smul φ _ _) }

/-- The cochain `alternatingCechModuleObjLinearMap f U φ p s` has component `φ.app _ (s.1 i)` at
`i`. -/
theorem alternatingCechModuleObjLinearMap_apply (φ : F ⟶ F') (p : ℕ)
    (s : alternatingCechModuleObj f U F p) (i : Fin (p + 1) → I) :
    (alternatingCechModuleObjLinearMap f U φ p s).1 i = φ.app _ (s.1 i) :=
  rfl

/-- The action of `φ ≫ ψ` on alternating Čech cochains is the action of `φ` followed by that of
`ψ`. -/
theorem alternatingCechModuleObjLinearMap_comp {F'' : X.Modules} (φ : F ⟶ F') (ψ : F' ⟶ F'')
    (p : ℕ) (s : alternatingCechModuleObj f U F p) :
    alternatingCechModuleObjLinearMap f U ψ p (alternatingCechModuleObjLinearMap f U φ p s) =
      alternatingCechModuleObjLinearMap f U (φ ≫ ψ) p s :=
  Subtype.ext (funext fun _ => rfl)

/-- The identity morphism of a module acts as the identity on alternating Čech cochains. -/
theorem alternatingCechModuleObjLinearMap_id (p : ℕ) (s : alternatingCechModuleObj f U F p) :
    alternatingCechModuleObjLinearMap f U (𝟙 F) p s = s :=
  Subtype.ext (funext fun _ => rfl)

/-- **An isomorphism of modules induces an `A`-linear equivalence of alternating Čech
cochains.** -/
def alternatingCechModuleObjCongr (e : F ≅ F') (p : ℕ) :
    alternatingCechModuleObj f U F p ≃ₗ[A] alternatingCechModuleObj f U F' p :=
  { alternatingCechModuleObjLinearMap f U e.hom p with
    invFun := alternatingCechModuleObjLinearMap f U e.inv p
    left_inv := fun s => by
      change alternatingCechModuleObjLinearMap f U e.inv p
        (alternatingCechModuleObjLinearMap f U e.hom p s) = s
      rw [alternatingCechModuleObjLinearMap_comp, e.hom_inv_id,
        alternatingCechModuleObjLinearMap_id]
    right_inv := fun s => by
      change alternatingCechModuleObjLinearMap f U e.hom p
        (alternatingCechModuleObjLinearMap f U e.inv p s) = s
      rw [alternatingCechModuleObjLinearMap_comp, e.inv_hom_id,
        alternatingCechModuleObjLinearMap_id] }

/-- The action of a morphism of modules commutes with the alternating Čech differential. -/
theorem alternatingCechModuleObjLinearMap_d (φ : F ⟶ F') (p : ℕ)
    (s : alternatingCechModuleObj f U F p) :
    alternatingCechModuleObjLinearMap f U φ (p + 1) (alternatingCechModuleD f U F p s) =
      alternatingCechModuleD f U F' p (alternatingCechModuleObjLinearMap f U φ p s) :=
  Subtype.ext (cochainMap_cechD U φ.mapPresheaf p s.1)

end Stacks.Cech

namespace Stacks.TwoAffineCech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (U : Cover.{u} → X.Opens) {F F' : X.Modules}

/-- **The two-term Čech differential is invariant under isomorphism of the module.** -/
theorem cechD_congr (e : F ≅ F') :
    (Stacks.Cech.alternatingCechModuleObjCongr f U e 1).toLinearMap ∘ₗ cechD f U F =
      cechD f U F' ∘ₗ (Stacks.Cech.alternatingCechModuleObjCongr f U e 0).toLinearMap := by
  ext s
  exact Stacks.Cech.alternatingCechModuleObjLinearMap_d f U e.hom 0 s

end Stacks.TwoAffineCech

namespace Stacks.TwoAffineCech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (U : Cover.{u} → X.Opens) (F : X.Modules) [IsSeparated f] [F.IsQuasicoherent]
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- **Global sections are the kernel of the two-term Čech differential**, `A`-linearly. -/
noncomputable def globalSectionsIsoKer :
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        ((AlgebraicGeometry.moduleGlobalSections X).obj F) ≅
      ModuleCat.of A (LinearMap.ker (cechD f U F)) :=
  (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapIso
      ((AlgebraicGeometry.moduleGlobalSections X).rightDerivedZeroIsoSelf.app F).symm ≪≫
    cohomologyZeroIso f U F hU hUaff

end Stacks.TwoAffineCech

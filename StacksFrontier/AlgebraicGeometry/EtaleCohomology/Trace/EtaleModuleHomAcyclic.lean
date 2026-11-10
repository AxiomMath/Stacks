module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# `Hom_R(N, I)` is acyclic for an injective sheaf `I`

Let `A` be a commutative ring and `R` an `A`-algebra, left Noetherian, and let `I` be an injective
sheaf of `R`-modules on the small étale site of a scheme. For every finite `R`-module `N`, the
sheaf of `A`-modules `Hom_R(N, I)` is acyclic for the sections over every object `U`.

## Main results

* `Stacks.EtaleCohomology.rightAcyclic_sections_iff_ext_eq_zero`: acyclicity over `U` is the
  vanishing of `Ext^{n+1}(A_U, -)`.
* `CategoryTheory.Abelian.ext_eq_zero_of_dimensionShift`: the abstract dimension shift.
* `Stacks.EtaleCohomology.isAcyclicEverywhere_etaleModuleHom_of_injective`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

/-! ### The abstract dimension shift -/

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]

/-- Transport of a vanishing statement for `Ext` along an isomorphism of the second argument. -/
lemma ext_eq_zero_of_iso {P Y Y' : C} (e : Y ≅ Y') {n : ℕ}
    (h : ∀ z : Ext.{w} P Y' n, z = 0) (z : Ext.{w} P Y n) : z = 0 := by
  have : z = (z.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ e.inv) (add_zero n) := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.comp_mk₀_id]
  rw [this, h (z.comp (Ext.mk₀ e.hom) (add_zero n)), Ext.zero_comp]

/-- **The abstract dimension shift.** Let `Y : ι → C` be a family of objects such that every
`Y x` is the kernel of an epimorphism `X₂ ⟶ Y y` in a short exact sequence whose middle term has
no higher `Ext(P, -)`, and such that every morphism `P ⟶ Y y` lifts to `X₂`. Then no `Y x` has
higher `Ext(P, -)`. -/
theorem ext_eq_zero_of_dimensionShift {ι : Type*} (P : C) (Y : ι → C)
    (h : ∀ x, ∃ (S : ShortComplex C) (_ : S.ShortExact) (y : ι) (_ : S.X₁ ≅ Y x)
      (_ : S.X₃ ≅ Y y), (∀ (n : ℕ) (z : Ext.{w} P S.X₂ (n + 1)), z = 0) ∧
        ∀ f : P ⟶ S.X₃, ∃ g : P ⟶ S.X₂, g ≫ S.g = f) :
    ∀ (n : ℕ) (x : ι) (z : Ext.{w} P (Y x) (n + 1)), z = 0 := by
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro x
    obtain ⟨S, hS, y, e₁, e₃, h₂, hlift⟩ := h x
    refine ext_eq_zero_of_iso e₁.symm fun z => ?_
  · obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ P hS z (h₂ 0 _) (zero_add 1)
    obtain ⟨g, hg⟩ := hlift (Ext.homEquiv₀ x₃)
    rw [← Ext.mk₀_homEquiv₀_apply x₃, ← hg] at hx₃
    rw [← hx₃, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Ext.comp_zero]
  · obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ P hS z (h₂ (n + 1) _) rfl
    rw [← hx₃, ext_eq_zero_of_iso e₃ (ih y) x₃, Ext.zero_comp]

end CategoryTheory.Abelian

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Acyclicity over an object and `Ext` out of the corepresenting sheaf -/

section Corepresentation

variable {Λ : Type} [CommRing Λ] {X : Scheme.{u}}

/-- **Acyclicity for the sections over `U` is the vanishing of the higher `Ext` out of the
sheafified free module `Λ_U`** that corepresents them. -/
theorem rightAcyclic_sections_iff_ext_eq_zero (G : EtaleModules.{u, 0} Λ X) (U : X.Etale) :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U)).rightAcyclic G ↔
      ∀ (n : ℕ) (e : Ext.{u + 1} (freeYonedaSheaf (Λ := Λ) U) G (n + 1)), e = 0 := by
  let Γ := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U)
  have key : ∀ n : ℕ, IsZero ((Γ.rightDerived (n + 1)).obj G) ↔
      ∀ e : Ext.{u + 1} (freeYonedaSheaf (Λ := Λ) U) G (n + 1), e = 0 := fun n => by
    have e₀ := (Stacks.Cohomology.DerivedForget.rightDerivedCompIso Γ
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) (n + 1)).app G
    have e₁ := (ModuleSheafCohomology.rightDerivedIso
      (freeYonedaSheafSectionsCorepresentation U) (n + 1)).app G ≪≫
        (ModuleSheafCohomology.rightDerivedCoyonedaSuccIso _ n).app G
    constructor
    · intro hz e
      have h1 : IsZero (((Γ ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).rightDerived
          (n + 1)).obj G) :=
        ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map_isZero hz).of_iso e₀.symm
      have h2 := h1.of_iso e₁.symm
      rw [AddCommGrpCat.isZero_iff_subsingleton] at h2
      exact @Subsingleton.elim _ h2 _ _
    · intro hv
      have h2 : IsZero ((extFunctorObj (freeYonedaSheaf (Λ := Λ) U) (n + 1)).obj G) := by
        rw [AddCommGrpCat.isZero_iff_subsingleton]
        exact ⟨fun a b => (hv a).trans (hv b).symm⟩
      have h' := (h2.of_iso e₁).of_iso e₀
      rw [IsZero.iff_id_eq_zero] at h' ⊢
      exact (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map_injective
        (by rw [CategoryTheory.Functor.map_id, Functor.map_zero]; exact h')
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  constructor
  · intro h n
    exact (key n).1 (h (n + 1) (Nat.succ_pos n))
  · intro h p hp
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by lia⟩
    exact (key n).2 (h n)

end Corepresentation

/-! ### `Hom_R(N, I)` for an injective sheaf `I` -/

section HomAcyclic

variable {A : Type} [CommRing A] {R : Type} [Ring R] [Algebra A R] {X : Scheme.{u}}

/-- The regular module `R` in the universe of the sections of sheaves on `X_étale`. -/
abbrev regularModuleU (R : Type) [Ring R] : ModuleCat.{u + 1} R :=
  ModuleCat.of R (ULift.{u + 1} R)

/-- `Hom_R(R, P) ≅ P` as `A`-modules: `f ↦ f(1)`. -/
def homRegularLinearEquiv (P : ModuleCat.{u + 1} R) :
    ↑((homFunctor (regularModuleU.{u} R)
        (centralScalars (A := A) (regularModuleU.{u} R))).obj P) ≃ₗ[A]
      ↑((ModuleCat.restrictScalars.{u + 1} (algebraMap A R)).obj P) where
  toFun f := (show regularModuleU.{u} R ⟶ P from f).hom ⟨1⟩
  invFun p := (ModuleCat.ofHom (LinearMap.toSpanSingleton R P p ∘ₗ
    (ULift.moduleEquiv (R := R) (M := R)).toLinearMap) : regularModuleU.{u} R ⟶ P)
  map_add' f g := rfl
  map_smul' a f := by
    change (show regularModuleU.{u} R ⟶ P from f).hom (algebraMap A R a • (⟨1⟩ : ULift.{u + 1} R)) =
      algebraMap A R a • (show regularModuleU.{u} R ⟶ P from f).hom ⟨1⟩
    rw [← map_smul]
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    change x • (show regularModuleU.{u} R ⟶ P from f).hom ⟨1⟩ =
      (show regularModuleU.{u} R ⟶ P from f).hom ⟨x⟩
    rw [← map_smul]
    congr 1
    exact ULift.ext (mul_one x)
  right_inv p := by
    change (1 : R) • p = p
    rw [one_smul]

/-- **`Hom_R(R, -)` is restriction of scalars to `A`**: `f ↦ f(1)`. -/
def homFunctorRegularIso :
    homFunctor (regularModuleU.{u} R) (centralScalars (A := A) (regularModuleU.{u} R)) ≅
      ModuleCat.restrictScalars.{u + 1} (algebraMap A R) :=
  NatIso.ofComponents (fun P => (homRegularLinearEquiv P).toModuleIso) (fun {P Q} g => by
    ext f
    rfl)

/-- `Hom_R(R, I)` is the sheaf `I` read over `A`. -/
def etaleModuleHomRegularIso (X : Scheme.{u}) :
    etaleModuleHom (regularModuleU.{u} R) (centralScalars (A := A) (regularModuleU.{u} R)) X ≅
      etaleModuleRestrictScalars (algebraMap A R) X where
  hom := sheafCompose_map X.smallEtaleTopology homFunctorRegularIso.hom
  inv := sheafCompose_map X.smallEtaleTopology homFunctorRegularIso.inv
  hom_inv_id := by
    ext G : 2
    apply Sheaf.hom_ext
    ext U : 2
    exact homFunctorRegularIso.hom_inv_id_app _
  inv_hom_id := by
    ext G : 2
    apply Sheaf.hom_ext
    ext U : 2
    exact homFunctorRegularIso.inv_hom_id_app _

/-- The map `Hom_R(N₂, G) ⟶ Hom_R(N₁, G)` induced by `u : N₁ ⟶ N₂`. -/
abbrev homPrecompApp {N₁ N₂ : ModuleCat.{u + 1} R} (u : N₁ ⟶ N₂) (G : EtaleModules.{u, 0} R X) :
    (etaleModuleHom N₂ (centralScalars (A := A) N₂) X).obj G ⟶
      (etaleModuleHom N₁ (centralScalars (A := A) N₁) X).obj G :=
  (etaleModuleHomPrecomp u X).app G

/-- `homPrecompApp` sends the identity of `N` to the identity. -/
lemma homPrecompApp_id (N : ModuleCat.{u + 1} R) (G : EtaleModules.{u, 0} R X) :
    homPrecompApp (A := A) (𝟙 N) G = 𝟙 _ := by
  apply Sheaf.hom_ext
  ext U f
  exact Category.id_comp (show N ⟶ G.obj.obj U from f)

/-- `homPrecompApp` is contravariant: it sends `u ≫ v` to the composite in the opposite order. -/
lemma homPrecompApp_comp {N₁ N₂ N₃ : ModuleCat.{u + 1} R} (u : N₁ ⟶ N₂) (v : N₂ ⟶ N₃)
    (G : EtaleModules.{u, 0} R X) :
    homPrecompApp (A := A) (u ≫ v) G = homPrecompApp v G ≫ homPrecompApp u G := by
  apply Sheaf.hom_ext
  ext U f
  exact Category.assoc u v (show N₃ ⟶ G.obj.obj U from f)

/-- `homPrecompApp` is additive in the morphism `u`. -/
lemma homPrecompApp_add {N₁ N₂ : ModuleCat.{u + 1} R} (u v : N₁ ⟶ N₂)
    (G : EtaleModules.{u, 0} R X) :
    homPrecompApp (A := A) (u + v) G = homPrecompApp u G + homPrecompApp v G := by
  apply Sheaf.hom_ext
  ext U f
  exact Preadditive.add_comp _ _ _ u v (show N₂ ⟶ G.obj.obj U from f)

/-- `homPrecompApp` sends the zero morphism to zero. -/
lemma homPrecompApp_zero (N₁ N₂ : ModuleCat.{u + 1} R) (G : EtaleModules.{u, 0} R X) :
    homPrecompApp (A := A) (0 : N₁ ⟶ N₂) G = 0 := by
  have h := homPrecompApp_add (A := A) (0 : N₁ ⟶ N₂) 0 G
  rw [add_zero] at h
  exact add_left_cancel (a := homPrecompApp (A := A) (0 : N₁ ⟶ N₂) G) (by rw [← h, add_zero])

/-- `homPrecompApp` commutes with finite sums of morphisms. -/
lemma homPrecompApp_sum {N₁ N₂ : ModuleCat.{u + 1} R} {J : Type*} (s : Finset J)
    (u : J → (N₁ ⟶ N₂)) (G : EtaleModules.{u, 0} R X) :
    homPrecompApp (A := A) (∑ j ∈ s, u j) G = ∑ j ∈ s, homPrecompApp (u j) G :=
  map_sum (AddMonoidHom.mk' (fun u : N₁ ⟶ N₂ => homPrecompApp (A := A) u G)
    (fun u v => homPrecompApp_add u v G)) u s

/-- `Ext` composed with a sum of morphisms of degree `0`. -/
lemma ext_comp_mk₀_finsetSum {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C] {P Y Z : C}
    {n : ℕ} (e : Ext.{w} P Y n) {J : Type*} (s : Finset J) (a : J → (Y ⟶ Z)) :
    e.comp (Ext.mk₀ (∑ j ∈ s, a j)) (add_zero n) = ∑ j ∈ s, e.comp (Ext.mk₀ (a j)) (add_zero n) :=
  map_sum (AddMonoidHom.mk' (fun a : Y ⟶ Z => e.comp (Ext.mk₀ a) (add_zero n))
    (fun a b => by rw [Ext.mk₀_add, Ext.comp_add])) a s

/-- **`Ext^{n+1}(A_U, Hom_R(R, I)) = 0`** for an injective sheaf `I`. -/
lemma ext_eq_zero_homRegular (I : EtaleModules.{u, 0} R X) [Injective I] (U : X.Etale) (n : ℕ)
    (e : Ext.{u + 1} (freeYonedaSheaf (Λ := A) U)
      ((etaleModuleHom (regularModuleU.{u} R) (centralScalars (A := A) (regularModuleU.{u} R))
        X).obj I) (n + 1)) : e = 0 :=
  ext_eq_zero_of_iso ((etaleModuleHomRegularIso (A := A) X).app I)
    ((rightAcyclic_sections_iff_ext_eq_zero _ U).1
      (isAcyclicEverywhere_restrictScalars' (algebraMap A R) I U) n) e

/-- The free module `R^k` in the universe of the sections. -/
abbrev freeModuleU (R : Type) [Ring R] (k : ℕ) : ModuleCat.{u + 1} R :=
  ModuleCat.of R (Fin k → ULift.{u + 1} R)

/-- The inclusion of the `j`-th summand of `R^k`. -/
def freeModuleι (k : ℕ) (j : Fin k) : regularModuleU.{u} R ⟶ freeModuleU.{u} R k :=
  ModuleCat.ofHom (LinearMap.single R (fun _ : Fin k => ULift.{u + 1} R) j)

/-- The projection of `R^k` to its `j`-th summand. -/
def freeModuleπ (k : ℕ) (j : Fin k) : freeModuleU.{u} R k ⟶ regularModuleU.{u} R :=
  ModuleCat.ofHom (LinearMap.proj j)

/-- The projections and inclusions of the summands of `R^k` sum to the identity. -/
lemma sum_freeModuleπ_comp_ι (k : ℕ) :
    ∑ j, freeModuleπ.{u} (R := R) k j ≫ freeModuleι k j = 𝟙 _ := by
  classical
  refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun j' => ?_)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.id_apply]
  rw [LinearMap.sum_apply, Finset.sum_apply]
  change ∑ j, (Pi.single j (x j) : Fin k → ULift.{u + 1} R) j' = x j'
  simp [Pi.single_apply]

/-- **`Ext^{n+1}(A_U, Hom_R(R^k, I)) = 0`** for an injective sheaf `I`. -/
lemma ext_eq_zero_homFree (I : EtaleModules.{u, 0} R X) [Injective I] (U : X.Etale) (n k : ℕ)
    (e : Ext.{u + 1} (freeYonedaSheaf (Λ := A) U)
      ((etaleModuleHom (freeModuleU.{u} R k) (centralScalars (A := A) (freeModuleU.{u} R k))
        X).obj I) (n + 1)) : e = 0 := by
  have h1 : e = e.comp (Ext.mk₀ (homPrecompApp (A := A) (𝟙 (freeModuleU.{u} R k)) I))
      (add_zero _) := by
    rw [homPrecompApp_id, Ext.comp_mk₀_id]
  rw [h1, ← sum_freeModuleπ_comp_ι, homPrecompApp_sum, ext_comp_mk₀_finsetSum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [homPrecompApp_comp, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    ext_eq_zero_homRegular I U n (e.comp (Ext.mk₀ (homPrecompApp (freeModuleι k j) I)) _),
    Ext.zero_comp]

variable [IsNoetherianRing R]

/-- **`Ext^{n+1}(A_U, Hom_R(N, I)) = 0`** for an injective sheaf `I` of `R`-modules and every
finite `R`-module `N`. -/
theorem ext_eq_zero_etaleModuleHom_of_injective (I : EtaleModules.{u, 0} R X) [Injective I]
    (U : X.Etale) (n : ℕ) (N : ModuleCat.{u + 1} R) [Module.Finite R N]
    (e : Ext.{u + 1} (freeYonedaSheaf (Λ := A) U)
      ((etaleModuleHom N (centralScalars (A := A) N) X).obj I) (n + 1)) : e = 0 := by
  let corep := freeYonedaSheafSectionsCorepresentation (Λ := A) U
  refine ext_eq_zero_of_dimensionShift (freeYonedaSheaf (Λ := A) U)
    (fun x : {N : ModuleCat.{u + 1} R // Module.Finite R N} =>
      (etaleModuleHom x.1 (centralScalars (A := A) x.1) X).obj I) (fun ⟨N, hN⟩ => ?_) n ⟨N, ‹_›⟩ e
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R N
  let g : freeModuleU.{u} R k ⟶ N := ModuleCat.ofHom (π ∘ₗ
    (LinearEquiv.piCongrRight fun _ : Fin k => ULift.moduleEquiv (R := R) (M := R)).toLinearMap)
  have hg : Epi g := (ModuleCat.epi_iff_surjective _).2 (hπ.comp (LinearEquiv.surjective _))
  let SR : ShortComplex (ModuleCat.{u + 1} R) := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hSR : SR.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel g) }
  have : IsNoetherian R (freeModuleU.{u} R k) := inferInstance
  have hK : Module.Finite R ↑(kernel g : ModuleCat.{u + 1} R) :=
    Module.Finite.of_injective (kernel.ι g).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have hinj : ∀ V : X.Etale, Injective (I.obj.obj (op V)) := fun V =>
    injective_obj_obj_of_injective I V
  refine ⟨_, shortExact_etaleModuleHom_of_injective SR hSR I hinj,
    ⟨(kernel g : ModuleCat.{u + 1} R), hK⟩, Iso.refl _, Iso.refl _,
    fun n e => ext_eq_zero_homFree I U n k e, fun f => ?_⟩
  let s : (kernel g : ModuleCat.{u + 1} R) ⟶ I.obj.obj (op U) := (corep.inv.app _).hom f
  have := hinj U
  let t : freeModuleU.{u} R k ⟶ I.obj.obj (op U) := Injective.factorThru s (kernel.ι g)
  let G₂ := (etaleModuleHom (freeModuleU.{u} R k) (centralScalars (A := A) (freeModuleU.{u} R k))
    X).obj I
  let G₃ := (etaleModuleHom (kernel g : ModuleCat.{u + 1} R) (centralScalars (A := A) _) X).obj I
  refine ⟨(corep.hom.app G₂).hom t, ?_⟩
  have hnat := congrArg (fun φ => φ.hom t) (corep.hom.naturality
    ((etaleModuleHomPrecomp (A := A) (kernel.ι g) X).app I))
  change (corep.hom.app G₃).hom (kernel.ι g ≫ t) =
    (corep.hom.app G₂).hom t ≫ (etaleModuleHomPrecomp (A := A) (kernel.ι g) X).app I at hnat
  change (corep.hom.app G₂).hom t ≫ (etaleModuleHomPrecomp (A := A) (kernel.ι g) X).app I = f
  have ht : kernel.ι g ≫ t = s := Injective.comp_factorThru s (kernel.ι g)
  rw [← hnat, ht]
  exact congrArg (fun φ => φ.hom f) (corep.inv_hom_id_app _)

/-- **`Hom_R(N, I)` is acyclic everywhere**, for an injective sheaf `I` and a finite module `N`. -/
theorem isAcyclicEverywhere_etaleModuleHom_of_injective (I : EtaleModules.{u, 0} R X)
    [Injective I] (N : ModuleCat.{u + 1} R) [Module.Finite R N] :
    IsAcyclicEverywhere ((etaleModuleHom N (centralScalars (A := A) N) X).obj I) := fun U =>
  (rightAcyclic_sections_iff_ext_eq_zero _ U).2 fun n e =>
    ext_eq_zero_etaleModuleHom_of_injective I U n N e

end HomAcyclic

end Stacks.EtaleCohomology

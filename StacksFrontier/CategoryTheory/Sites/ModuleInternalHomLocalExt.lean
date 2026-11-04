module

public import StacksFrontier.CategoryTheory.Sites.ModuleInternalHomTensor
public import StacksFrontier.Algebra.Homology.QuasiIsoSingleLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.LeftExact

/-!
# Local `Ext` of a locally constant sheaf of `A`-modules into a locally injective one

Let `(C, K)` be a site, `A` a commutative noetherian ring, `G` a sheaf of `A`-modules which is
locally constant with finitely presented values, and `ω` a sheaf of `A`-modules which is locally
isomorphic to the constant sheaf of an injective `A`-module. If `ω ⟶ J` is a resolution by
sheaves whose modules of sections are injective (for instance an injective resolution), then
`ℋom_A(G, J)` is a resolution of `ℋom_A(G, ω)`: the local `Ext` sheaves `ℰxtⁱ_A(G, ω)` vanish
for `i > 0`.

The proof is local, which reduces it to a constant sheaf `M̲` with `M` finitely presented and to
`ω` constant. There `ℋom_A(N̲, F)` has sections `Hom_A(N, F(-))`, so a presentation
`0 → K → A^b → M → 0` gives a short exact sequence of complexes `ℋom_A(-, J)`, the sections of
`J` being injective; `ℋom_A(A̲, -)` is the identity, and the cohomology in degree one is the
cokernel of `ℋom_A(A̲^b, E̲) ⟶ ℋom_A(K̲, E̲)`, which is the constant sheaf on the cokernel of
`Hom_A(A^b, E) ⟶ Hom_A(K, E)` (Tag 093T (1)), zero since `E` is injective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe w v u

namespace Stacks.ModuleInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (A : Type w) [CommRing A]

section Lcomp

universe t

variable {A}

/-- A short complex of `A`-modules is exact if and only if its underlying linear maps are exact. -/
lemma moduleCat_exact_iff_function_exact' (S : ShortComplex (ModuleCat.{t} A)) :
    S.Exact ↔ Function.Exact S.f.hom S.g.hom := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker, LinearMap.exact_iff, eq_comm]

/-- `Hom_A(-, M)` applied to a short complex of `A`-modules. -/
def lcompShortComplex (S : ShortComplex (ModuleCat.{t} A)) (M : ModuleCat.{t} A) :
    ShortComplex (ModuleCat.{t} A) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.lcomp A M S.g.hom))
    (ModuleCat.ofHom (LinearMap.lcomp A M S.f.hom)) (by
      refine ModuleCat.hom_ext (LinearMap.ext fun φ => LinearMap.ext fun x => ?_)
      change φ (S.g.hom (S.f.hom x)) = 0
      rw [← LinearMap.comp_apply S.g.hom S.f.hom, ← ModuleCat.hom_comp, S.zero]
      exact φ.map_zero)

/-- **`Hom_A(-, M)` is exact for an injective module `M`.** -/
lemma lcompShortComplex_shortExact {S : ShortComplex (ModuleCat.{t} A)}
    (hS : S.ShortExact) (M : ModuleCat.{t} A) [Module.Injective A M] :
    (lcompShortComplex S M).ShortExact := by
  have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective _).1 hS.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [moduleCat_exact_iff_function_exact']
    exact LinearMap.exact_lcomp_of_exact_of_surjective M
      ((moduleCat_exact_iff_function_exact' _).1 hS.exact) hg
  · rw [ModuleCat.mono_iff_injective]
    exact LinearMap.lcomp_injective_of_surjective _ hg
  · rw [ModuleCat.epi_iff_surjective]
    intro ψ
    obtain ⟨φ, hφ⟩ := Module.Injective.out S.f.hom
      ((ModuleCat.mono_iff_injective _).1 hS.mono_f) ψ
    exact ⟨φ, LinearMap.ext hφ⟩

variable (A) in
/-- The `A`-module `A`, shrunk to the universe `t`. -/
abbrev unitModule [Small.{t} A] : ModuleCat.{t} A := ModuleCat.of A (Shrink.{t} A)

/-- Evaluation at `1`: `Hom_A(A, M) ≃ M`, for `A` shrunk to the universe of `M`. -/
def evalOneEquiv [Small.{t} A] (M : ModuleCat.{t} A) : (Shrink.{t} A →ₗ[A] M) ≃ₗ[A] M where
  toFun φ := φ ((Shrink.linearEquiv A A).symm 1)
  invFun m := (LinearMap.toSpanSingleton A M m).comp (Shrink.linearEquiv A A).toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := by
    ext x
    change (Shrink.linearEquiv A A x) • φ ((Shrink.linearEquiv A A).symm 1) = φ x
    rw [← φ.map_smul, ← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  right_inv m := by
    change (Shrink.linearEquiv A A ((Shrink.linearEquiv A A).symm 1)) • m = m
    rw [LinearEquiv.apply_symm_apply, one_smul]

variable (A) in
/-- The free module `A^b`, shrunk to the universe `t`. -/
abbrev freeModule [Small.{t} A] (b : ℕ) : ModuleCat.{t} A :=
  ModuleCat.of A (Fin b → Shrink.{t} A)

variable (A) in
/-- The split short exact sequence `0 → A → A^(b+1) → A^b → 0`. -/
def freeSuccShortComplex [Small.{t} A] (b : ℕ) : ShortComplex (ModuleCat.{t} A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.single A (fun _ : Fin (b + 1) => Shrink.{t} A) 0) :
      unitModule A ⟶ freeModule A (b + 1))
    (ModuleCat.ofHom (LinearMap.funLeft A (Shrink.{t} A) Fin.succ) :
      freeModule A (b + 1) ⟶ freeModule A b)
    (by
      refine ModuleCat.hom_ext (LinearMap.ext fun (x : Shrink.{t} A) => funext fun i => ?_)
      change @Pi.single (Fin (b + 1)) (fun _ => Shrink.{t} A) _ _ 0 x i.succ = 0
      exact Pi.single_eq_of_ne (Fin.succ_ne_zero i) x)

/-- The sequence `0 → A → A^(b+1) → A^b → 0` is short exact. -/
lemma freeSuccShortComplex_shortExact [Small.{t} A] (b : ℕ) :
    (freeSuccShortComplex A b : ShortComplex (ModuleCat.{t} A)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [moduleCat_exact_iff_function_exact']
    intro (v : Fin (b + 1) → Shrink.{t} A)
    refine ⟨fun hv => ⟨v 0, funext fun j => ?_⟩, ?_⟩
    · show @Pi.single (Fin (b + 1)) (fun _ => Shrink.{t} A) _ _ 0 (v 0) j = v j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact Pi.single_eq_same _ _
      · rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i)]
        exact (congrFun hv i).symm
    · rintro ⟨(x : Shrink.{t} A), rfl⟩
      refine funext fun i => ?_
      show @Pi.single (Fin (b + 1)) (fun _ => Shrink.{t} A) _ _ 0 x i.succ = 0
      exact Pi.single_eq_of_ne (Fin.succ_ne_zero i) x
  · rw [ModuleCat.mono_iff_injective]
    intro (a : Shrink.{t} A) (a' : Shrink.{t} A) h
    have h0 := congrFun h 0
    change @Pi.single (Fin (b + 1)) (fun _ => Shrink.{t} A) _ _ 0 a 0 =
      @Pi.single (Fin (b + 1)) (fun _ => Shrink.{t} A) _ _ 0 a' 0 at h0
    rwa [Pi.single_eq_same, Pi.single_eq_same] at h0
  · rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective b)

variable (A) in
/-- Precomposition with `i : N₂ ⟶ N₁` on `Hom_A(-, E)`, as a map of `A`-modules. -/
def precompHom {N₁ N₂ : ModuleCat.{t} A} (i : N₂ ⟶ N₁) (E : ModuleCat.{t} A) :
    ModuleCat.of A (N₁ ⟶ E) ⟶ ModuleCat.of A (N₂ ⟶ E) :=
  ModuleCat.ofHom
    { toFun := fun h => i ≫ h
      map_add' := fun _ _ => Preadditive.comp_add _ _ _ _ _ _
      map_smul' := fun _ _ => Linear.comp_smul _ _ _ _ _ _ }

/-- **A finite module over a noetherian ring has a presentation**
`0 → K → A^b → N → 0` with `K` finite. -/
lemma exists_presentation [Small.{t} A] [IsNoetherianRing A] (N : ModuleCat.{t} A)
    [Module.Finite A N] :
    ∃ (b : ℕ) (S : ShortComplex (ModuleCat.{t} A)) (_ : S.ShortExact) (_ : Module.Finite A S.X₁)
      (_ : Module.Finite A S.X₂), S.X₂ = freeModule A b ∧ S.X₃ = N := by
  obtain ⟨b, f, hf⟩ := Module.Finite.exists_fin' A N
  let π : (Fin b → Shrink.{t} A) →ₗ[A] N :=
    f ∘ₗ (LinearEquiv.piCongrRight fun _ => Shrink.linearEquiv A A).toLinearMap
  let S : ShortComplex (ModuleCat.{t} A) :=
    ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker π).subtype :
        ModuleCat.of A (LinearMap.ker π) ⟶ freeModule A b)
      (ModuleCat.ofHom π : freeModule A b ⟶ N) (ModuleCat.hom_ext (LinearMap.ext fun x => x.2))
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [moduleCat_exact_iff_function_exact']
      intro x
      exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
    · rw [ModuleCat.mono_iff_injective]
      exact Subtype.val_injective
    · rw [ModuleCat.epi_iff_surjective]
      exact hf.comp (LinearEquiv.piCongrRight fun _ => Shrink.linearEquiv A A).surjective
  have : Module.Finite A (Fin b → Shrink.{t} A) :=
    Module.Finite.equiv (LinearEquiv.piCongrRight fun _ => Shrink.linearEquiv A A).symm
  exact ⟨b, S, hS, inferInstanceAs (Module.Finite A (LinearMap.ker π)),
    inferInstanceAs (Module.Finite A (Fin b → Shrink.{t} A)), rfl, rfl⟩

end Lcomp

section Functors

/-- **The internal Hom `ℋom_A(G, -)`** of sheaves of `A`-modules, as a functor of its second
variable. -/
@[simps obj]
def homFunctor (G : Sheaf K (ModuleCat.{max u v} A)) :
    Sheaf K (ModuleCat.{max u v} A) ⥤ Sheaf K (ModuleCat.{max u v} A) where
  obj F := moduleSheafHom K A G F
  map g := moduleSheafHomMap K A (𝟙 G) g
  map_id I := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext
      fun (α : (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
        (K.overPullback (ModuleCat.{max u v} A) U.unop).obj I) => ?_)))
    change (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 I) = α
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
  map_comp {I₁ I₂ I₃} f g := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext
      fun (α : (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
        (K.overPullback (ModuleCat.{max u v} A) U.unop).obj I₁) => ?_)))
    change (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
        (K.overPullback (ModuleCat.{max u v} A) U.unop).map (f ≫ g) =
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫
        ((K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
          (K.overPullback (ModuleCat.{max u v} A) U.unop).map f) ≫
        (K.overPullback (ModuleCat.{max u v} A) U.unop).map g
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp, Category.assoc]

/-- The functor `ℋom_A(G, -)` is additive. -/
instance homFunctor_additive (G : Sheaf K (ModuleCat.{max u v} A)) :
    (homFunctor K A G).Additive where
  map_add {F F'} f g := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext
      fun (α : (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
        (K.overPullback (ModuleCat.{max u v} A) U.unop).obj F) => ?_)))
    change (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
        (K.overPullback (ModuleCat.{max u v} A) U.unop).map (f + g) =
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
          (K.overPullback (ModuleCat.{max u v} A) U.unop).map f +
        (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
          (K.overPullback (ModuleCat.{max u v} A) U.unop).map g
    have : (K.overPullback (ModuleCat.{max u v} A) U.unop).Additive :=
      Functor.additive_of_preserves_binary_products _
    rw [Functor.map_add, Preadditive.comp_add, Preadditive.comp_add]

/-- The abelian sheaf underlying `ℋom_A(G, -)` is `homAbFunctor`. -/
lemma homFunctor_comp_forget (G : Sheaf K (ModuleCat.{max u v} A)) :
    homFunctor K A G ⋙ sheafCompose K (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}) =
      homAbFunctor A K G := rfl

end Functors

section Exactness

/-- **A short complex of sheaves of modules which is short exact on every module of sections is
short exact.** -/
lemma shortExact_of_sectionwise (S : ShortComplex (Sheaf K (ModuleCat.{max u v} A)))
    (h : ∀ X : Cᵒᵖ, (S.map ((sheafSections K (ModuleCat.{max u v} A)).obj X)).ShortExact) :
    S.ShortExact := by
  have hmono : Mono S.f := by
    have : ∀ X, Mono (((sheafToPresheaf K (ModuleCat.{max u v} A)).map S.f).app X) :=
      fun X => (h X).mono_f
    have : Mono ((sheafToPresheaf K (ModuleCat.{max u v} A)).map S.f) :=
      NatTrans.mono_of_mono_app _
    exact (sheafToPresheaf K _).mono_of_mono_map this
  have hepi : Epi S.g := by
    have : Presheaf.IsLocallySurjective K S.g.hom :=
      Presheaf.isLocallySurjective_of_surjective K S.g.hom fun X =>
        (ModuleCat.epi_iff_surjective _).1 (h X).epi_g
    exact Sheaf.epi_of_isLocallySurjective S.g
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.exact_iff_epi_toCycles]
  have hi : ∀ X : Cᵒᵖ, Function.Injective (S.iCycles.hom.app X).hom := fun X => by
    have : Mono ((sheafToPresheaf K (ModuleCat.{max u v} A)).map S.iCycles) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this X)
  have : Presheaf.IsLocallySurjective K S.toCycles.hom :=
    Presheaf.isLocallySurjective_of_surjective K S.toCycles.hom fun X c => by
      obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1 (h X).exact
        ((S.iCycles.hom.app X).hom c) (by
          show ((S.iCycles ≫ S.g).hom.app X).hom c = 0
          rw [S.iCycles_g]
          rfl)
      refine ⟨x, hi X ?_⟩
      show ((S.toCycles ≫ S.iCycles).hom.app X).hom x = _
      rw [S.toCycles_i]
      exact hx
  exact Sheaf.epi_of_isLocallySurjective S.toCycles

end Exactness

section Complexes

variable (J : CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ)

/-- **The complex `ℋom_A(G, J)`**. -/
abbrev homComplex (G : Sheaf K (ModuleCat.{max u v} A)) :
    CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ :=
  ((homFunctor K A G).mapHomologicalComplex (ComplexShape.up ℤ)).obj J

/-- Two maps out of `ℋom_A(G, F)` are equal if they agree on every section over an object
of `C`, i.e. on every map `G|ᵤ ⟶ F|ᵤ` of restrictions to an object `U`. -/
private lemma moduleSheafHom_hom_ext {G F H : Sheaf K (ModuleCat.{max u v} A)}
    {f g : moduleSheafHom K A G F ⟶ H}
    (h : ∀ (U : Cᵒᵖ) (α : (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
      (K.overPullback (ModuleCat.{max u v} A) U.unop).obj F),
      (f.hom.app U).hom α = (g.hom.app U).hom α) :
    f = g :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext (h U))))

/-- For `f : G₁ ⟶ G₂` and `g : F₁ ⟶ F₂`, precomposition with `f` and postcomposition with `g`
commute as maps `ℋom_A(G₂, F₁) ⟶ ℋom_A(G₁, F₂)`. -/
lemma moduleSheafHomMap_comp_moduleSheafHomMap {G₁ G₂ F₁ F₂ : Sheaf K (ModuleCat.{max u v} A)}
    (f : G₁ ⟶ G₂) (g : F₁ ⟶ F₂) :
    moduleSheafHomMap K A f (𝟙 F₁) ≫ moduleSheafHomMap K A (𝟙 G₁) g =
      moduleSheafHomMap K A (𝟙 G₂) g ≫ moduleSheafHomMap K A f (𝟙 F₂) := by
  refine moduleSheafHom_hom_ext K A fun U α => ?_
  show (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G₁) ≫
      ((K.overPullback (ModuleCat.{max u v} A) U.unop).map f ≫ α ≫
        (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 F₁)) ≫
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map g =
    (K.overPullback (ModuleCat.{max u v} A) U.unop).map f ≫
      ((K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G₂) ≫ α ≫
        (K.overPullback (ModuleCat.{max u v} A) U.unop).map g) ≫
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 F₂)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]

/-- Precomposition with `f : G₁ ⟶ G₂`, as a map of complexes `ℋom_A(G₂, J) ⟶ ℋom_A(G₁, J)`. -/
def homComplexMap {G₁ G₂ : Sheaf K (ModuleCat.{max u v} A)} (f : G₁ ⟶ G₂) :
    homComplex K A J G₂ ⟶ homComplex K A J G₁ where
  f n := moduleSheafHomMap K A f (𝟙 (J.X n))
  comm' i j _ := (moduleSheafHomMap_comp_moduleSheafHomMap K A f (J.d i j)).symm

/-- In degree `n`, `homComplexMap J f` is precomposition with `f` on `ℋom_A(-, J.X n)`. -/
lemma homComplexMap_f {G₁ G₂ : Sheaf K (ModuleCat.{max u v} A)} (f : G₁ ⟶ G₂) (n : ℤ) :
    (homComplexMap K A J f).f n = moduleSheafHomMap K A f (𝟙 (J.X n)) := rfl

/-- `homComplexMap` takes `f ≫ g` to the composite of `homComplexMap g` and `homComplexMap f`. -/
lemma homComplexMap_comp {G₁ G₂ G₃ : Sheaf K (ModuleCat.{max u v} A)} (f : G₁ ⟶ G₂)
    (g : G₂ ⟶ G₃) :
    homComplexMap K A J (f ≫ g) = homComplexMap K A J g ≫ homComplexMap K A J f := by
  refine HomologicalComplex.hom_ext _ _ fun n => moduleSheafHom_hom_ext K A fun U α => ?_
  show (K.overPullback (ModuleCat.{max u v} A) U.unop).map (f ≫ g) ≫ α ≫
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 (J.X n)) =
    (K.overPullback (ModuleCat.{max u v} A) U.unop).map f ≫
      ((K.overPullback (ModuleCat.{max u v} A) U.unop).map g ≫ α ≫
        (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 (J.X n))) ≫
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 (J.X n))
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Functor.map_comp, Category.assoc]

/-- `homComplexMap` takes the identity of `G` to the identity of `ℋom_A(G, J)`. -/
lemma homComplexMap_id (G : Sheaf K (ModuleCat.{max u v} A)) :
    homComplexMap K A J (𝟙 G) = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n => moduleSheafHom_hom_ext K A fun U α => ?_
  show (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 (J.X n)) = α
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- An isomorphism `G₁ ≅ G₂` induces `ℋom_A(G₂, J) ≅ ℋom_A(G₁, J)`. -/
def homComplexIso {G₁ G₂ : Sheaf K (ModuleCat.{max u v} A)} (e : G₁ ≅ G₂) :
    homComplex K A J G₂ ≅ homComplex K A J G₁ where
  hom := homComplexMap K A J e.hom
  inv := homComplexMap K A J e.inv
  hom_inv_id := by rw [← homComplexMap_comp, e.inv_hom_id, homComplexMap_id]
  inv_hom_id := by rw [← homComplexMap_comp, e.hom_inv_id, homComplexMap_id]

/-- For a short complex `S`, the composite `ℋom_A(S.X₃, J) ⟶ ℋom_A(S.X₂, J) ⟶ ℋom_A(S.X₁, J)`
is zero. -/
lemma homComplexMap_comp_eq_zero (S : ShortComplex (Sheaf K (ModuleCat.{max u v} A))) :
    homComplexMap K A J S.g ≫ homComplexMap K A J S.f = 0 := by
  rw [← homComplexMap_comp, S.zero]
  refine HomologicalComplex.hom_ext _ _ fun n => moduleSheafHom_hom_ext K A fun U α => ?_
  show (K.overPullback (ModuleCat.{max u v} A) U.unop).map 0 ≫ α ≫
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 (J.X n)) = 0
  rw [Functor.map_zero, Limits.zero_comp]

/-- The short complex of complexes `ℋom_A(S.X₃, J) ⟶ ℋom_A(S.X₂, J) ⟶ ℋom_A(S.X₁, J)`. -/
abbrev homComplexShortComplex (S : ShortComplex (Sheaf K (ModuleCat.{max u v} A))) :
    ShortComplex (CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ) :=
  ShortComplex.mk (homComplexMap K A J S.g) (homComplexMap K A J S.f)
    (homComplexMap_comp_eq_zero K A J S)

/-- Evaluation of a section of `ℋom_A(N̲, F)` over `X`, as a map to `Hom_A(N, F(X))`; it is
bijective (`Stacks.ConstantSheaf.bijective_sheafHomEval_app`). -/
abbrev constantHomEval (N : ModuleCat.{max u v} A) (F : Sheaf K (ModuleCat.{max u v} A))
    (X : Cᵒᵖ) :=
  (sheafHomEval K A N (G := F) (constantUnit K A N)).app X

/-- The evaluation `ℋom_A(N̲, F)(X) ⟶ Hom_A(N, F(X))` is an isomorphism. -/
instance isIso_constantHomEval (N : ModuleCat.{max u v} A) (F : Sheaf K (ModuleCat.{max u v} A))
    (X : Cᵒᵖ) : IsIso (constantHomEval K A N F X) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_sheafHomEval_app K A N F X

/-- The evaluation of `ℋom_A(N̲, F)` is natural in `N`. -/
lemma constantHomEval_naturality {N₁ N₂ : ModuleCat.{max u v} A} (f : N₁ ⟶ N₂)
    (F : Sheaf K (ModuleCat.{max u v} A)) (X : Cᵒᵖ) :
    (moduleSheafHomMap K A ((constantSheaf K (ModuleCat.{max u v} A)).map f) (𝟙 F)).hom.app X ≫
        constantHomEval K A N₁ F X =
      constantHomEval K A N₂ F X ≫ ModuleCat.ofHom (LinearMap.lcomp A (F.obj.obj X) f.hom) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun (α : (K.overPullback (ModuleCat.{max u v} A)
    X.unop).obj ((constantSheaf K (ModuleCat.{max u v} A)).obj N₂) ⟶
      (K.overPullback (ModuleCat.{max u v} A) X.unop).obj F) => LinearMap.ext fun m => ?_)
  show (((K.overPullback (ModuleCat.{max u v} A) X.unop).map
      ((constantSheaf K (ModuleCat.{max u v} A)).map f) ≫ α ≫
        (K.overPullback (ModuleCat.{max u v} A) X.unop).map (𝟙 F)).hom.app
          (op (Over.mk (𝟙 X.unop)))).hom (((constantUnit K A N₁).app X).hom m) =
    (α.hom.app (op (Over.mk (𝟙 X.unop)))).hom (((constantUnit K A N₂).app X).hom (f.hom m))
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  show (α.hom.app (op (Over.mk (𝟙 X.unop)))).hom
      ((((constantSheaf K (ModuleCat.{max u v} A)).map f).hom.app X).hom
        (((constantUnit K A N₁).app X).hom m)) = _
  exact congrArg (fun z => (α.hom.app (op (Over.mk (𝟙 X.unop)))).hom z)
    (ConcreteCategory.congr_hom
      (toSheafify_const_naturality_app K (ModuleCat.{max u v} A) f X) m).symm

variable (hJ : ∀ (n : ℤ) (X : Cᵒᵖ), Module.Injective A ((J.X n).obj.obj X))
include hJ

/-- **`ℋom_A(-, J)` takes a short exact sequence of constant sheaves to a short exact sequence
of complexes**, the modules of sections of `J` being injective. -/
lemma shortExact_homComplexShortComplex_constant {S : ShortComplex (ModuleCat.{max u v} A)}
    (hS : S.ShortExact) :
    (homComplexShortComplex K A J
      (S.map (constantSheaf K (ModuleCat.{max u v} A)))).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    shortExact_of_sectionwise K A _ fun X => ?_
  have := hJ n X
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk
    (@asIso _ _ _ _ _ (isIso_constantHomEval K A S.X₃ (J.X n) X))
    (@asIso _ _ _ _ _ (isIso_constantHomEval K A S.X₂ (J.X n) X))
    (@asIso _ _ _ _ _ (isIso_constantHomEval K A S.X₁ (J.X n) X))
    (constantHomEval_naturality K A S.g (J.X n) X).symm
    (constantHomEval_naturality K A S.f (J.X n) X).symm).symm
    (lcompShortComplex_shortExact hS ((J.X n).obj.obj X))

end Complexes

section Unit

variable [Small.{max u v} A]

/-- The constant sheaf `A̲`. -/
abbrev unitSheaf : Sheaf K (ModuleCat.{max u v} A) :=
  (constantSheaf K (ModuleCat.{max u v} A)).obj ((unitModule A : ModuleCat.{max u v} A))

/-- `ℋom_A(A̲, F) ≅ F` on presheaves: a section is sent to its value at `1`. -/
def unitPresheafIso (F : Sheaf K (ModuleCat.{max u v} A)) :
    (moduleSheafHom K A (unitSheaf K A) F).obj ≅ F.obj :=
  NatIso.ofComponents
    (fun X => @asIso _ _ _ _ _
        (isIso_constantHomEval K A ((unitModule A : ModuleCat.{max u v} A)) F X) ≪≫
      (evalOneEquiv (F.obj.obj X)).toModuleIso)
    (fun {X Y} f => by
      refine ModuleCat.hom_ext (LinearMap.ext fun α => ?_)
      have h := ConcreteCategory.congr_hom ((sheafHomEval K A (unitModule A : ModuleCat.{max u v} A)
        (G := F) (constantUnit K A (unitModule A : ModuleCat.{max u v} A))).naturality f) α
      exact congrArg (evalOneEquiv (F.obj.obj Y)) h)

/-- **`ℋom_A(A̲, F) ≅ F`**, evaluation at `1`. -/
def unitIso (F : Sheaf K (ModuleCat.{max u v} A)) : moduleSheafHom K A (unitSheaf K A) F ≅ F :=
  ObjectProperty.isoMk _ (unitPresheafIso K A F)

/-- **`ℋom_A(A̲, -)` is the identity functor.** -/
def homFunctorUnitIso : homFunctor K A (unitSheaf K A) ≅ 𝟭 _ :=
  NatIso.ofComponents (unitIso K A) (fun {F F'} g => by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun X => ModuleCat.hom_ext (LinearMap.ext
      fun (α : (K.overPullback (ModuleCat.{max u v} A) X.unop).obj (unitSheaf K A) ⟶
        (K.overPullback (ModuleCat.{max u v} A) X.unop).obj F) => ?_)))
    rfl)

variable (J : CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ)

/-- `ℋom_A(A̲, J) ≅ J`. -/
def homComplexUnitIso : homComplex K A J (unitSheaf K A) ≅ J :=
  (NatIso.mapHomologicalComplex (homFunctorUnitIso K A) (ComplexShape.up ℤ)).app J ≪≫
    (Functor.mapHomologicalComplexIdIso _ _).app J

end Unit

section Vanishing

variable (J : CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ)

/-- The local `Ext` sheaves `ℋⁿ(ℋom_A(G, J))` vanish in positive degrees. -/
def ExtVanishes (G : Sheaf K (ModuleCat.{max u v} A)) : Prop :=
  ∀ n : ℤ, 0 < n → IsZero ((homComplex K A J G).homology n)

/-- `ℋom_A(G, F)` is zero when `G` is zero. -/
lemma isZero_moduleSheafHom_of_isZero {G : Sheaf K (ModuleCat.{max u v} A)} (hG : IsZero G)
    (F : Sheaf K (ModuleCat.{max u v} A)) : IsZero (moduleSheafHom K A G F) := by
  refine Sheaf.isZero_of_forall_isZero_sections _ fun X => ?_
  have hG' : IsZero ((K.overPullback (ModuleCat.{max u v} A) X).obj G) :=
    Sheaf.isZero_of_forall_isZero_sections _ fun W =>
      Functor.map_isZero ((sheafSections K (ModuleCat.{max u v} A)).obj (op W.left)) hG
  have : Subsingleton ((K.overPullback (ModuleCat.{max u v} A) X).obj G ⟶
      (K.overPullback (ModuleCat.{max u v} A) X).obj F) := ⟨fun a b => hG'.eq_of_src a b⟩
  have : Subsingleton ((moduleSheafHom K A G F).obj.obj (op X)) := this
  exact ModuleCat.isZero_of_subsingleton _

/-- Local `Ext` vanishes out of a zero sheaf. -/
lemma extVanishes_of_isZero {G : Sheaf K (ModuleCat.{max u v} A)} (hG : IsZero G) :
    ExtVanishes K A J G := fun _ _ =>
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_moduleSheafHom_of_isZero K A hG _)

variable (hJ : ∀ (n : ℤ) (X : Cᵒᵖ), Module.Injective A ((J.X n).obj.obj X))
include hJ

/-- For a short exact sequence `S` of `A`-modules, if local `Ext` into `J` vanishes out of the
constant sheaves on `S.X₁` and `S.X₃`, then it vanishes out of the constant sheaf on `S.X₂`. -/
lemma extVanishes_mid_constant {S : ShortComplex (ModuleCat.{max u v} A)} (hS : S.ShortExact)
    (h₁ : ExtVanishes K A J ((constantSheaf K _).obj S.X₁))
    (h₃ : ExtVanishes K A J ((constantSheaf K _).obj S.X₃)) :
    ExtVanishes K A J ((constantSheaf K _).obj S.X₂) := fun n hn =>
  ((shortExact_homComplexShortComplex_constant K A J hJ hS).homology_exact₂ n).isZero_X₂
    ((h₃ n hn).eq_of_src _ _) ((h₁ n hn).eq_of_tgt _ _)

/-- For a short exact sequence `S` of `A`-modules, if `Hⁿ` of `ℋom_A` of the constant sheaf on
`S.X₁` into `J` and `Hⁿ⁺¹` of `ℋom_A` of the constant sheaf on `S.X₂` into `J` vanish, then so
does `Hⁿ⁺¹` of `ℋom_A` of the constant sheaf on `S.X₃` into `J`. -/
lemma isZero_homology_succ_constant {S : ShortComplex (ModuleCat.{max u v} A)}
    (hS : S.ShortExact) (n : ℤ)
    (h₁ : IsZero ((homComplex K A J ((constantSheaf K _).obj S.X₁)).homology n))
    (h₂ : IsZero ((homComplex K A J ((constantSheaf K _).obj S.X₂)).homology (n + 1))) :
    IsZero ((homComplex K A J ((constantSheaf K _).obj S.X₃)).homology (n + 1)) :=
  ((shortExact_homComplexShortComplex_constant K A J hJ hS).homology_exact₁ n (n + 1) rfl).isZero_X₂
    (h₁.eq_of_src _ _) (h₂.eq_of_tgt _ _)

/-- For a short exact sequence `S` of `A`-modules, if `H¹` of `ℋom_A` of the constant sheaf on
`S.X₂` into `J` vanishes and precomposition with the constant map on `S.f` is an epimorphism on
`H⁰`, then `H¹` of `ℋom_A` of the constant sheaf on `S.X₃` into `J` vanishes. -/
lemma isZero_homology_one_constant {S : ShortComplex (ModuleCat.{max u v} A)}
    (hS : S.ShortExact)
    (h₂ : IsZero ((homComplex K A J ((constantSheaf K _).obj S.X₂)).homology (0 + 1)))
    (h0 : Epi (HomologicalComplex.homologyMap
      (homComplexMap K A J ((constantSheaf K (ModuleCat.{max u v} A)).map S.f)) 0)) :
    IsZero ((homComplex K A J ((constantSheaf K _).obj S.X₃)).homology (0 + 1)) := by
  have hT := shortExact_homComplexShortComplex_constant K A J hJ hS
  have hδ : Epi (hT.δ 0 (0 + 1) rfl) :=
    (hT.homology_exact₁ 0 (0 + 1) rfl).epi_f (h₂.eq_of_tgt _ _)
  have hcomp := (ShortComplex.mk _ _ (hT.comp_δ 0 (0 + 1) rfl)).zero
  have : Epi (HomologicalComplex.homologyMap
    (homComplexShortComplex K A J (S.map (constantSheaf K (ModuleCat.{max u v} A)))).g 0) := h0
  have hz : hT.δ 0 (0 + 1) rfl = 0 := (cancel_epi _).1 (hcomp.trans (comp_zero).symm)
  exact IsZero.of_epi_eq_zero _ hz

end Vanishing

section Free

variable [Small.{max u v} A] (J : CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ)
  {ω : Sheaf K (ModuleCat.{max u v} A)}
  (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω ⟶ J) [QuasiIso ι]

include ι in
/-- Local `Ext` into a resolution `J` of `ω` vanishes out of the constant sheaf `A̲`. -/
lemma extVanishes_unitSheaf : ExtVanishes K A J (unitSheaf K A) := fun n hn =>
  (Stacks.LeftExactHomology.isZero_homology_of_quasiIso_single ι n (ne_of_gt hn)).of_iso
    (HomologicalComplex.homologyMapIso (homComplexUnitIso K A J) n)

variable (hJ : ∀ (n : ℤ) (X : Cᵒᵖ), Module.Injective A ((J.X n).obj.obj X))
include hJ

include ι in
/-- **Local `Ext` vanishes out of a finite free constant sheaf.** -/
lemma extVanishes_freeModule (b : ℕ) :
    ExtVanishes K A J ((constantSheaf K _).obj (freeModule A b : ModuleCat.{max u v} A)) := by
  have : (constantSheaf K (ModuleCat.{max u v} A)).Additive :=
    Functor.additive_of_preserves_binary_products _
  induction b with
  | zero =>
    have : Subsingleton (freeModule A 0 : ModuleCat.{max u v} A) :=
      inferInstanceAs (Subsingleton (Fin 0 → Shrink.{max u v} A))
    exact extVanishes_of_isZero K A J (Functor.map_isZero (constantSheaf K _)
      (ModuleCat.isZero_of_subsingleton (freeModule A 0 : ModuleCat.{max u v} A)))
  | succ b ih =>
    exact extVanishes_mid_constant K A J hJ
      (S := (freeSuccShortComplex A b : ShortComplex (ModuleCat.{max u v} A)))
      (freeSuccShortComplex_shortExact b) (extVanishes_unitSheaf K A J ι) ih

end Free

section DegreeZero

/-- Forgetting the `A`-module structure of sheaves preserves finite limits. -/
lemma preservesFiniteLimits_sheafCompose_forget₂ :
    PreservesFiniteLimits
      (sheafCompose K (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v})) := by
  have : PreservesFiniteLimits (sheafCompose K (forget₂ (ModuleCat.{max u v} A)
      AddCommGrpCat.{max u v}) ⋙ sheafToPresheaf K AddCommGrpCat.{max u v}) := by
    show PreservesFiniteLimits (sheafToPresheaf K (ModuleCat.{max u v} A) ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}))
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf K AddCommGrpCat.{max u v})

/-- **`ℋom_A(G, -)` preserves finite limits**: forgetting the module structure it is a right
adjoint, and forgetting reflects limits. -/
lemma homFunctor_preservesFiniteLimits (G : Sheaf K (ModuleCat.{max u v} A)) :
    PreservesFiniteLimits (homFunctor K A G) := by
  have hF := preservesFiniteLimits_sheafCompose_forget₂ K A
  constructor
  intro J _ _
  have : ReflectsLimitsOfShape J
      (sheafCompose K (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v})) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape J (homFunctor K A G ⋙
      sheafCompose K (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v})) := by
    rw [homFunctor_comp_forget]
    have := (sheafTensorAdj A K G).rightAdjoint_preservesLimits
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafCompose K (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}))

/-- A map of complexes concentrated in degree `0` which is an epimorphism in degree `0` is an
epimorphism on `H⁰`. -/
lemma epi_homologyMap_zero_of_epi {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
    {X Y : CochainComplex 𝒜 ℤ} (φ : X ⟶ Y) (hX₁ : X.d (-1) 0 = 0) (hX₂ : X.d 0 1 = 0)
    (hY₁ : Y.d (-1) 0 = 0) (hY₂ : Y.d 0 1 = 0) [Epi (φ.f 0)] :
    Epi (HomologicalComplex.homologyMap φ 0) := by
  have : IsIso (X.homologyπ 0) := X.isIso_homologyπ (-1) 0 (by simp) hX₁
  have : IsIso (Y.homologyπ 0) := Y.isIso_homologyπ (-1) 0 (by simp) hY₁
  have : IsIso (X.iCycles 0) := X.isIso_iCycles 0 1 (by simp) hX₂
  have : IsIso (Y.iCycles 0) := Y.isIso_iCycles 0 1 (by simp) hY₂
  have hc : HomologicalComplex.cyclesMap φ 0 = X.iCycles 0 ≫ φ.f 0 ≫ inv (Y.iCycles 0) := by
    rw [← HomologicalComplex.cyclesMap_i_assoc, IsIso.hom_inv_id, Category.comp_id]
  have hh : HomologicalComplex.homologyMap φ 0 =
      inv (X.homologyπ 0) ≫ HomologicalComplex.cyclesMap φ 0 ≫ Y.homologyπ 0 := by
    rw [← HomologicalComplex.homologyπ_naturality, IsIso.inv_hom_id_assoc]
  rw [hh, hc]
  infer_instance

/-- `ℋom_A(G, F)` is zero when `F` is zero. -/
lemma isZero_moduleSheafHom_of_isZero_right (G : Sheaf K (ModuleCat.{max u v} A))
    {F : Sheaf K (ModuleCat.{max u v} A)} (hF : IsZero F) : IsZero (moduleSheafHom K A G F) :=
  have := homFunctor_preservesFiniteLimits K A G
  Functor.map_isZero (homFunctor K A G) hF

/-- Precomposition with `i` stays an epimorphism after replacing the target by an isomorphic
one. -/
lemma epi_moduleSheafHomMap_of_iso {G₁ G₂ X Y : Sheaf K (ModuleCat.{max u v} A)} (i : G₂ ⟶ G₁)
    (e : X ≅ Y) (h : Epi (moduleSheafHomMap K A i (𝟙 Y))) :
    Epi (moduleSheafHomMap K A i (𝟙 X)) := by
  have : IsIso (moduleSheafHomMap K A (𝟙 G₁) e.hom) := (homFunctor K A G₁).map_isIso e.hom
  have : IsIso (moduleSheafHomMap K A (𝟙 G₂) e.hom) := (homFunctor K A G₂).map_isIso e.hom
  rw [← epi_comp_iff_of_isIso _ (moduleSheafHomMap K A (𝟙 G₂) e.hom),
    moduleSheafHomMap_comp_moduleSheafHomMap]
  infer_instance

variable (J : CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ) [J.IsStrictlyGE 0]
  {ω : Sheaf K (ModuleCat.{max u v} A)}
  (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω ⟶ J) [QuasiIso ι]

include ι in
/-- `ℋom_A(G, -)`, being left exact, takes the resolution `ω ⟶ J` to a map which is an
isomorphism on `H⁰`. -/
lemma quasiIsoAt_zero_homFunctor_map (G : Sheaf K (ModuleCat.{max u v} A)) :
    QuasiIsoAt (((homFunctor K A G).mapHomologicalComplex (ComplexShape.up ℤ)).map ι) 0 :=
  have := homFunctor_preservesFiniteLimits K A G
  Stacks.LeftExactHomology.quasiIsoAt_zero_map_of_preservesFiniteLimits _ ι

include ι in
/-- **On `H⁰`, precomposition with `i : G₂ ⟶ G₁` is an epimorphism as soon as it is one on
`ℋom_A(-, ω)`.** -/
lemma epi_homologyMap_zero_homComplexMap {G₁ G₂ : Sheaf K (ModuleCat.{max u v} A)} (i : G₂ ⟶ G₁)
    (hi : Epi (moduleSheafHomMap K A i (𝟙 ω))) :
    Epi (HomologicalComplex.homologyMap (homComplexMap K A J i) 0) := by
  let J₀ :=
    (HomologicalComplex.single (Sheaf K (ModuleCat.{max u v} A)) (ComplexShape.up ℤ) 0).obj ω
  have hzero : ∀ (G : Sheaf K (ModuleCat.{max u v} A)) (n : ℤ), n ≠ 0 →
      IsZero ((homComplex K A J₀ G).X n) := fun G n hn =>
    isZero_moduleSheafHom_of_isZero_right K A G (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hsq : homComplexMap K A J₀ i ≫ ((homFunctor K A G₂).mapHomologicalComplex _).map ι =
      ((homFunctor K A G₁).mapHomologicalComplex _).map ι ≫ homComplexMap K A J i :=
    HomologicalComplex.hom_ext _ _ fun n => moduleSheafHomMap_comp_moduleSheafHomMap K A i (ι.f n)
  have : Epi ((homComplexMap K A J₀ i).f 0) := by
    rw [homComplexMap_f]
    exact epi_moduleSheafHomMap_of_iso K A i
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ω) hi
  have h0 : Epi (HomologicalComplex.homologyMap (homComplexMap K A J₀ i) 0) :=
    epi_homologyMap_zero_of_epi _ ((hzero G₁ (-1) (by simp)).eq_of_src _ _)
      ((hzero G₁ 1 (by simp)).eq_of_tgt _ _) ((hzero G₂ (-1) (by simp)).eq_of_src _ _)
      ((hzero G₂ 1 (by simp)).eq_of_tgt _ _)
  have : IsIso (HomologicalComplex.homologyMap
      (((homFunctor K A G₂).mapHomologicalComplex _).map ι) 0) :=
    (quasiIsoAt_iff_isIso_homologyMap _ 0).1 (quasiIsoAt_zero_homFunctor_map K A J ι G₂)
  have : Epi
      (HomologicalComplex.homologyMap (((homFunctor K A G₁).mapHomologicalComplex _).map ι) 0 ≫
        HomologicalComplex.homologyMap (homComplexMap K A J i) 0) := by
    rw [← HomologicalComplex.homologyMap_comp, ← hsq, HomologicalComplex.homologyMap_comp]
    infer_instance
  exact epi_of_epi (HomologicalComplex.homologyMap
    (((homFunctor K A G₁).mapHomologicalComplex _).map ι) 0) _

end DegreeZero

section Constant

/-- **Tag 093T (1) is natural in the first variable**: under `Hom_A(N, E)̲ ≅ ℋom_A(N̲, E̲)`,
precomposition with `i̲` is the constant sheaf on precomposition with `i`. -/
lemma constantSheafHomIsoOfHom_hom_comp_moduleSheafHomMap {N₁ N₂ : ModuleCat.{max u v} A}
    [Module.FinitePresentation A N₁] [Module.FinitePresentation A N₂] (i : N₂ ⟶ N₁)
    (E : ModuleCat.{max u v} A) :
    (constantSheafHomIsoOfHom.{u, v, w, max u v} K A N₁ E).hom ≫
        moduleSheafHomMap K A ((constantSheaf K _).map i) (𝟙 ((constantSheaf K _).obj E)) =
      (constantSheaf K (ModuleCat.{max u v} A)).map (precompHom A i E) ≫
        (constantSheafHomIsoOfHom.{u, v, w, max u v} K A N₂ E).hom := by
  refine Sheaf.hom_ext (sheafify_hom_ext K _ _
    (moduleSheafHom K A ((constantSheaf K _).obj N₂) ((constantSheaf K _).obj E)).property ?_)
  refine NatTrans.ext (funext fun X => ModuleCat.hom_ext (LinearMap.ext fun (h : N₁ ⟶ E) => ?_))
  have h₁ := constantSheafHomIso_hom_app_apply K A N₁ E (ModuleCat.of A (N₁ ⟶ E))
    (ModuleCat.homLinearEquiv (S := A)).symm X h
  have h₂ := constantSheafHomIso_hom_app_apply K A N₂ E (ModuleCat.of A (N₂ ⟶ E))
    (ModuleCat.homLinearEquiv (S := A)).symm X (i ≫ h)
  simp only [LinearEquiv.symm_apply_apply] at h₁ h₂
  have h₁' : ((constantSheafHomIsoOfHom K A N₁ E).hom.hom.app X).hom
      (((constantUnit K A (ModuleCat.of A (N₁ ⟶ E))).app X).hom h) =
        (K.overPullback (ModuleCat.{max u v} A) X.unop).map ((constantSheaf K _).map h) := h₁
  have h₂' : ((constantSheafHomIsoOfHom K A N₂ E).hom.hom.app X).hom
      (((constantUnit K A (ModuleCat.of A (N₂ ⟶ E))).app X).hom (i ≫ h)) =
        (K.overPullback (ModuleCat.{max u v} A) X.unop).map ((constantSheaf K _).map (i ≫ h)) := h₂
  have hn : (((constantSheaf K _).map (precompHom A i E)).hom.app X).hom
      (((constantUnit K A (ModuleCat.of A (N₁ ⟶ E))).app X).hom h) =
        ((constantUnit K A (ModuleCat.of A (N₂ ⟶ E))).app X).hom (i ≫ h) :=
    (ConcreteCategory.congr_hom
      (toSheafify_const_naturality_app K (ModuleCat.{max u v} A) (precompHom A i E) X) h).symm
  show (moduleSheafHomMap K A ((constantSheaf K _).map i) (𝟙 _)).hom.app X
      (((constantSheafHomIsoOfHom K A N₁ E).hom.hom.app X).hom
        (((constantUnit K A (ModuleCat.of A (N₁ ⟶ E))).app X).hom h)) =
    ((constantSheafHomIsoOfHom K A N₂ E).hom.hom.app X).hom
      ((((constantSheaf K _).map (precompHom A i E)).hom.app X).hom
        (((constantUnit K A (ModuleCat.of A (N₁ ⟶ E))).app X).hom h))
  rw [hn, h₂', h₁']
  show (K.overPullback (ModuleCat.{max u v} A) X.unop).map ((constantSheaf K _).map i) ≫
      (K.overPullback (ModuleCat.{max u v} A) X.unop).map ((constantSheaf K _).map h) ≫
      (K.overPullback (ModuleCat.{max u v} A) X.unop).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]

/-- **`ℋom_A(-, E̲)` takes an injection of finitely presented constant sheaves to an
epimorphism**, for an injective `A`-module `E`. -/
lemma epi_moduleSheafHomMap_constant {N₁ N₂ : ModuleCat.{max u v} A}
    [Module.FinitePresentation A N₁] [Module.FinitePresentation A N₂] (i : N₂ ⟶ N₁) [Mono i]
    (E : ModuleCat.{max u v} A) [Module.Injective A E] :
    Epi (moduleSheafHomMap K A ((constantSheaf K _).map i) (𝟙 ((constantSheaf K _).obj E))) := by
  have hp : Epi (precompHom A i E) := by
    rw [ModuleCat.epi_iff_surjective]
    intro ψ
    obtain ⟨φ, hφ⟩ := Module.Injective.out i.hom ((ModuleCat.mono_iff_injective i).1 inferInstance)
      ψ.hom
    exact ⟨ModuleCat.ofHom φ, ModuleCat.hom_ext (LinearMap.ext hφ)⟩
  have : PreservesColimits (constantSheaf K (ModuleCat.{max u v} A)) := by
    unfold constantSheaf; infer_instance
  have : Epi ((constantSheafHomIsoOfHom.{u, v, w, max u v} K A N₁ E).hom ≫
      moduleSheafHomMap K A ((constantSheaf K _).map i) (𝟙 ((constantSheaf K _).obj E))) := by
    rw [constantSheafHomIsoOfHom_hom_comp_moduleSheafHomMap]
    infer_instance
  exact epi_of_epi (constantSheafHomIsoOfHom.{u, v, w, max u v} K A N₁ E).hom _

end Constant

section ConstantVanishing

variable [Small.{max u v} A] [IsNoetherianRing A]
  (J : CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ) [J.IsStrictlyGE 0]
  {ω : Sheaf K (ModuleCat.{max u v} A)}
  (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω ⟶ J) [QuasiIso ι]
  (hJ : ∀ (n : ℤ) (X : Cᵒᵖ), Module.Injective A ((J.X n).obj.obj X))
  (E : ModuleCat.{max u v} A) [Module.Injective A E] (eω : ω ≅ (constantSheaf K _).obj E)

include ι hJ eω in
/-- **Local `Ext` vanishing for a constant sheaf on a finite module, into a constant sheaf on an
injective module.** -/
theorem extVanishes_constantSheaf_of_finite (N : ModuleCat.{max u v} A) [Module.Finite A N] :
    ExtVanishes K A J ((constantSheaf K (ModuleCat.{max u v} A)).obj N) := by
  have hfree₀ : ∀ (S : ShortComplex (ModuleCat.{max u v} A)) (b : ℕ), S.X₂ = freeModule A b →
      ExtVanishes K A J ((constantSheaf K (ModuleCat.{max u v} A)).obj S.X₂) :=
    fun _ b h₂ => h₂ ▸ extVanishes_freeModule K A J ι hJ b
  have key : ∀ (m : ℕ) (N : ModuleCat.{max u v} A) [Module.Finite A N],
      IsZero ((homComplex K A J ((constantSheaf K (ModuleCat.{max u v} A)).obj N)).homology
        ((m : ℤ) + 1)) := by
    intro m
    induction m with
    | zero =>
      intro N _
      obtain ⟨b, S, hS, hK, hF, h₂, rfl⟩ := exists_presentation N
      have hfree := hfree₀ S b h₂
      have : Module.FinitePresentation A S.X₁ := Module.finitePresentation_of_finite A _
      have : Module.FinitePresentation A S.X₂ := Module.finitePresentation_of_finite A _
      have : Mono S.f := hS.mono_f
      have hε := epi_moduleSheafHomMap_of_iso K A ((constantSheaf K _).map S.f) eω
        (epi_moduleSheafHomMap_constant K A S.f E)
      simpa using isZero_homology_one_constant K A J hJ hS (hfree 1 (by norm_num))
        (epi_homologyMap_zero_homComplexMap K A J ι _ hε)
    | succ m ih =>
      intro N _
      obtain ⟨b, S, hS, hK, hF, h₂, rfl⟩ := exists_presentation N
      have hfree := hfree₀ S b h₂
      simpa [add_assoc] using
        isZero_homology_succ_constant K A J hJ hS ((m : ℤ) + 1) (ih S.X₁) (hfree _ (by omega))
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  exact key m N

end ConstantVanishing

end Stacks.ModuleInternalHom

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverDerivedSquare

/-!
# The Čech map along a continuous functor, and the derived comparison of global sections

Let `F : C' ⥤ C` be a continuous functor of sites, `ψ : R' ⟶ F_* R` a morphism of sheaves of rings,
and `P = SheafOfModules.pushforward ψ` the pullback of sheaves of modules, computed by
precomposition with `F`: `(P N)(V') = N(F V')`. Let `D : ι → C` and `D' : ι' → C'` be families
covering the final objects with all finite nonempty products, and let `γ i' : F(D' i') ⟶ D (τ i')`
be morphisms over a map of indices `τ : ι' → ι`. They induce morphisms
`F(D'_{x'}) ⟶ D_{τ ∘ x'}` on the products (`cechLiftMap`), hence by restriction a map of Čech
complexes

`Č(D, N) ⟶ res_ρ Č(D', P N)`,

for ring maps `A ⟶ Γ(C, R)`, `A' ⟶ Γ(C', R')` and `ρ : A ⟶ A'` compatible with `ψ`
(`pushforwardCechMap`). This file proves that **under the Čech comparisons of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/FinalCoverDerived.lean`, the derived comparison
`CategoryTheory.Functor.derivedSquareMap α N` of the comparison of global sections
`α : Γ(C, N) ⟶ res_ρ Γ(C', P N)`, `s ↦ (V' ↦ s(F V'))`, is this Čech map**
(`cechToDerivedGlobalSections_comp_derivedSquareMap_pushforward`).

## Main definitions

* `cechLiftMap` — the morphisms `F(D'_{x'}) ⟶ D_{τ ∘ x'}` induced by the `γ i'`.
* `pushforwardCechMap` — the map of Čech complexes, natural in `N`.
* `cechIntMap` — a map of Čech complexes, extended by zero to integer degrees.

## Main results

* `augmentation_comp_pushforwardCechMap` — the Čech map is compatible with `α` in degree zero.
* `cechToDerivedGlobalSections_comp_derivedSquareMap_pushforward` — the derived comparison of
  global sections is the Čech map.

## References

* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape
open Stacks.Cohomology.SiteModules

universe w v u r uA uA' m

namespace Stacks.CechSite.FinalCover

attribute [local instance high] hasProducts_moduleCat

attribute [local instance] preservesFiniteLimits_restrictScalars
  preservesFiniteColimits_restrictScalars

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

/-! ### Maps into a restriction of scalars of a product -/

section ResPi

variable {A : Type uA} [Ring A] {A' : Type uA'} [Ring A'] (ρ : A →+* A') {κ : Type w}
  [UnivLE.{w, m}] (Z : κ → ModuleCat.{m} A')

/-- Two maps into a restriction of scalars of a product agree as soon as they agree after every
projection. -/
lemma resPi_hom_ext {T : ModuleCat.{m} A}
    {f g : T ⟶ (ModuleCat.restrictScalars.{m} ρ).obj (∏ᶜ Z)}
    (h : ∀ k, f ≫ (ModuleCat.restrictScalars ρ).map (Pi.π Z k) =
      g ≫ (ModuleCat.restrictScalars ρ).map (Pi.π Z k)) : f = g :=
  (cancel_mono (piComparison (ModuleCat.restrictScalars.{m} ρ) Z)).1
    (Pi.hom_ext _ _ fun k ↦ by rw [Category.assoc, Category.assoc, piComparison_comp_π]; exact h k)

/-- The map into a restriction of scalars of a product given by its components. -/
def resPiLift {T : ModuleCat.{m} A}
    (f : ∀ k, T ⟶ (ModuleCat.restrictScalars.{m} ρ).obj (Z k)) :
    T ⟶ (ModuleCat.restrictScalars.{m} ρ).obj (∏ᶜ Z) :=
  Pi.lift f ≫ inv (piComparison (ModuleCat.restrictScalars.{m} ρ) Z)

/-- The components of `resPiLift`. -/
@[reassoc (attr := simp)]
lemma resPiLift_comp {T : ModuleCat.{m} A}
    (f : ∀ k, T ⟶ (ModuleCat.restrictScalars.{m} ρ).obj (Z k)) (k : κ) :
    resPiLift ρ Z f ≫ (ModuleCat.restrictScalars ρ).map (Pi.π Z k) = f k := by
  rw [resPiLift, Category.assoc, inv_piComparison_comp_map_π]
  exact Pi.lift_comp_π _ _

end ResPi

/-! ### Extension by zero of a map of Čech complexes -/

section IntMap

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  {A : Type uA} [Ring A] (φ : A →+* GlobalSectionRing R) {ι : Type w} (D : ι → C)
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]
  {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'} (R' : Sheaf J' RingCat.{r})
  {A' : Type uA'} [Ring A'] (φ' : A' →+* GlobalSectionRing R') {ι' : Type w} (D' : ι' → C')
  [∀ (n : ℕ) (x : Fin (n + 1) → ι'), HasProduct (fun a ↦ D' (x a))]
  (P : SheafOfModules.{max u v w} R ⥤ SheafOfModules.{max u v w} R') (ρ : A →+* A')

omit [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]
  [∀ (n : ℕ) (x : Fin (n + 1) → ι'), HasProduct (fun a ↦ D' (x a))] in
/-- Cancelling an isomorphism against its inverse in a composite. -/
lemma cancel_iso_comp_aux {𝒦 : Type*} [Category* 𝒦] {T X Y Z W V : 𝒦} (x : T ⟶ Y) (e : X ≅ Y)
    (c : Y ⟶ Z) (eY : Z ⟶ W) (m : W ⟶ V) :
    x ≫ e.inv ≫ ((e.hom ≫ c ≫ eY) ≫ m) = x ≫ c ≫ eY ≫ m := by
  simp

/-- A map of Čech complexes, extended by zero to integer degrees. -/
def cechIntMap (c₀ : cechFunctor R φ D ⟶
    P ⋙ cechFunctor R' φ' D' ⋙ (ModuleCat.restrictScalars.{max u v w} ρ).mapHomologicalComplex
      (up ℕ)) :
    cechIntFunctor R φ D ⟶
      P ⋙ cechIntFunctor R' φ' D' ⋙
        (ModuleCat.restrictScalars.{max u v w} ρ).mapHomologicalComplex (up ℤ) :=
  Functor.whiskerRight c₀ (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{max u v w} A)) ≫
    Functor.whiskerLeft (P ⋙ cechFunctor R' φ' D')
      (Stacks.DerivedIndexing.mapExtendNatIso (ModuleCat.restrictScalars.{max u v w} ρ)
        ComplexShape.embeddingUpNat).hom

/-- **The extension by zero of a map of Čech complexes compatible in degree zero with a
comparison of global sections is compatible with it.** -/
lemma augmentationInt_comp_cechIntMap_f (c₀ : cechFunctor R φ D ⟶
      P ⋙ cechFunctor R' φ' D' ⋙ (ModuleCat.restrictScalars.{max u v w} ρ).mapHomologicalComplex
        (up ℕ))
    (α : baseGlobalSections R φ ⟶ P ⋙ baseGlobalSections R' φ' ⋙ ModuleCat.restrictScalars ρ)
    (hc₀ : ∀ N, (augmentation R φ D).app N ≫ (c₀.app N).f 0 =
      α.app N ≫ (ModuleCat.restrictScalars ρ).map ((augmentation R' φ' D').app (P.obj N)))
    (N : SheafOfModules.{max u v w} R) :
    augmentationInt R φ D N ≫ ((cechIntMap R φ D R' φ' D' P ρ c₀).app N).f 0 =
      α.app N ≫ (ModuleCat.restrictScalars ρ).map (augmentationInt R' φ' D' (P.obj N)) := by
  dsimp only [cechIntMap, augmentationInt, cechIntXIso]
  rw [NatTrans.comp_app, HomologicalComplex.comp_f, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f (c₀.app N) ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  refine (cancel_iso_comp_aux (𝒦 := ModuleCat.{max u v w} A) _ _ _ _ _).trans ?_
  have h := Stacks.DerivedIndexing.extendXIso_inv_comp_mapExtendIso_hom_f
    (ModuleCat.restrictScalars.{max u v w} ρ) ComplexShape.embeddingUpNat
    ((cechFunctor R' φ' D').obj (P.obj N)) (i := 0) (i' := 0) rfl
  refine (congrArg ((augmentation R φ D).app N ≫ (c₀.app N).f 0 ≫ ·) h).trans ?_
  rw [reassoc_of% (hc₀ N), ← Functor.map_comp]
  rfl

end IntMap

/-! ### The Čech map along a continuous functor -/

section Pushforward

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  {A : Type uA} [Ring A] (φ : A →+* GlobalSectionRing R) {ι : Type w} (D : ι → C)
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]
  {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'} (R' : Sheaf J' RingCat.{r})
  {A' : Type uA'} [Ring A'] (φ' : A' →+* GlobalSectionRing R') {ι' : Type w} (D' : ι' → C')
  [∀ (n : ℕ) (x : Fin (n + 1) → ι'), HasProduct (fun a ↦ D' (x a))]
  (F : C' ⥤ C) [F.IsContinuous J' J]
  (ψ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{r} J' J).obj R) (ρ : A →+* A')
  {τ : ι' → ι} (γ : ∀ i', F.obj (D' i') ⟶ D (τ i'))

/-- **The morphisms `F(D'_{x'}) ⟶ D_{τ ∘ x'}`** induced on the products by the
`γ i' : F(D' i') ⟶ D (τ i')`. -/
def cechLiftMap {n : ℕ} (x : Fin (n + 1) → ι') : F.obj (inter D' x) ⟶ inter D (τ ∘ x) :=
  interLift D fun a ↦ F.map (interπ D' x a) ≫ γ (x a)

/-- The components of `cechLiftMap`. -/
@[reassoc (attr := simp)]
lemma cechLiftMap_comp_interπ {n : ℕ} (x : Fin (n + 1) → ι') (a : Fin (n + 1)) :
    cechLiftMap D D' F γ x ≫ interπ D (τ ∘ x) a = F.map (interπ D' x a) ≫ γ (x a) :=
  interLift_comp_interπ D _ a

/-- `cechLiftMap` is compatible with reindexing. -/
@[reassoc]
lemma cechLiftMap_comp_interMap {n m : ℕ} (x : Fin (n + 1) → ι')
    (h : Fin (m + 1) → Fin (n + 1)) :
    cechLiftMap D D' F γ x ≫ interMap D (τ ∘ x) h =
      F.map (interMap D' x h) ≫ cechLiftMap D D' F γ (x ∘ h) :=
  inter_hom_ext D fun a ↦ by
    rw [Category.assoc, interMap_comp_interπ, cechLiftMap_comp_interπ]
    refine (congrArg (· ≫ γ (x (h a))) (congrArg F.map (interMap_comp_interπ D' x h a).symm)).trans
      ?_
    rw [F.map_comp, Category.assoc]
    exact (congrArg (F.map (interMap D' x h) ≫ ·)
      (cechLiftMap_comp_interπ D D' F γ (x ∘ h) a).symm).trans (Category.assoc _ _ _).symm

variable [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

variable (hρ : ∀ (a : A) (V' : C'ᵒᵖ),
  (ψ.hom.app V').hom ((φ' (ρ a)).1 V') = (φ a).1 (op (F.obj V'.unop)))

include hρ in
/-- The sections of `N` over `F V'` are, as `A`-modules, the sections of the pullback `P N` over
`V'` with their scalars restricted along `ρ`: the identity of the underlying groups. -/
def pushforwardSectionsHom (N : SheafOfModules.{max u v w} R) (V' : C') :
    ((basePresheaf R φ).obj N).obj (op (F.obj V')) ⟶
      (ModuleCat.restrictScalars.{max u v w} ρ).obj
        (((basePresheaf R' φ').obj ((SheafOfModules.pushforward.{max u v w} ψ).obj N)).obj
          (op V')) :=
  ModuleCat.ofHom
    (X := ((basePresheaf R φ).obj N).obj (op (F.obj V')))
    (Y := (ModuleCat.restrictScalars.{max u v w} ρ).obj
        (((basePresheaf R' φ').obj ((SheafOfModules.pushforward.{max u v w} ψ).obj N)).obj
          (op V')))
    { toFun := fun x ↦ (x : N.val.obj (op (F.obj V')))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change (φ a).1 (op (F.obj V')) • (show N.val.obj (op (F.obj V')) from x) =
          (show R.obj.obj (op (F.obj V')) from (ψ.hom.app (op V')).hom ((φ' (ρ a)).1 (op V'))) •
            (show N.val.obj (op (F.obj V')) from x)
        rw [hρ a (op V')] }

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- `pushforwardSectionsHom` is natural in the object of `C'`. -/
@[reassoc]
lemma pushforwardSectionsHom_naturality (N : SheafOfModules.{max u v w} R) {V V' : C'}
    (f : V ⟶ V') :
    ((basePresheaf R φ).obj N).map (F.map f).op ≫ pushforwardSectionsHom R φ R' φ' F ψ ρ hρ N V =
      pushforwardSectionsHom R φ R' φ' F ψ ρ hρ N V' ≫
        (ModuleCat.restrictScalars.{max u v w} ρ).map
          (((basePresheaf R' φ').obj ((SheafOfModules.pushforward.{max u v w} ψ).obj N)).map
            f.op) :=
  rfl

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- `pushforwardSectionsHom` is natural in the sheaf of modules. -/
@[reassoc]
lemma pushforwardSectionsHom_naturality_left {N N' : SheafOfModules.{max u v w} R} (g : N ⟶ N')
    (V : C') :
    ((basePresheaf R φ).map g).app (op (F.obj V)) ≫ pushforwardSectionsHom R φ R' φ' F ψ ρ hρ N' V =
      pushforwardSectionsHom R φ R' φ' F ψ ρ hρ N V ≫
        (ModuleCat.restrictScalars.{max u v w} ρ).map
          (((basePresheaf R' φ').map ((SheafOfModules.pushforward.{max u v w} ψ).map g)).app
            (op V)) :=
  rfl

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))] in
/-- Two maps into a restriction of scalars of a Čech term agree as soon as they agree after every
projection. -/
lemma resCech_hom_ext (M : SheafOfModules.{max u v w} R') {n : ℕ} {T : ModuleCat.{max u v w} A}
    {f g : T ⟶ (ModuleCat.restrictScalars.{max u v w} ρ).obj (((cechFunctor R' φ' D').obj M).X n)}
    (h : ∀ x, f ≫ (ModuleCat.restrictScalars ρ).map (π D' ((basePresheaf R' φ').obj M) n x) =
      g ≫ (ModuleCat.restrictScalars ρ).map (π D' ((basePresheaf R' φ').obj M) n x)) : f = g :=
  resPi_hom_ext ρ (fun x : Fin (n + 1) → ι' ↦ ((basePresheaf R' φ').obj M).obj (op (inter D' x)))
    h

/-- The component of the Čech map at a tuple `x'`: restriction along
`cechLiftMap : F(D'_{x'}) ⟶ D_{τ ∘ x'}`. -/
def pushforwardCechComponent (N : SheafOfModules.{max u v w} R) {n : ℕ} (x : Fin (n + 1) → ι') :
    ((cechFunctor R φ D).obj N).X n ⟶
      (ModuleCat.restrictScalars.{max u v w} ρ).obj
        (((basePresheaf R' φ').obj ((SheafOfModules.pushforward.{max u v w} ψ).obj N)).obj
          (op (inter D' x))) :=
  π D ((basePresheaf R φ).obj N) n (τ ∘ x) ≫
    ((basePresheaf R φ).obj N).map (cechLiftMap D D' F γ x).op ≫
    pushforwardSectionsHom R φ R' φ' F ψ ρ hρ N (inter D' x)

/-- **The Čech map `Č(D, N) ⟶ res_ρ Č(D', P N)` in degree `n`**: on the factor indexed by
`x' : Fin (n + 1) → ι'` it is the factor indexed by `τ ∘ x'`, restricted along
`F(D'_{x'}) ⟶ D_{τ ∘ x'}`. -/
def pushforwardCechMapF (N : SheafOfModules.{max u v w} R) (n : ℕ) :
    ((cechFunctor R φ D).obj N).X n ⟶
      (ModuleCat.restrictScalars.{max u v w} ρ).obj
        (((cechFunctor R' φ' D').obj ((SheafOfModules.pushforward.{max u v w} ψ).obj N)).X n) :=
  resPiLift ρ (fun x : Fin (n + 1) → ι' ↦
      ((basePresheaf R' φ').obj ((SheafOfModules.pushforward.{max u v w} ψ).obj N)).obj
        (op (inter D' x)))
    fun x ↦ pushforwardCechComponent R φ D R' φ' D' F ψ ρ γ hρ N x

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The components of `pushforwardCechMapF`. -/
@[reassoc (attr := simp)]
lemma pushforwardCechMapF_comp (N : SheafOfModules.{max u v w} R) (n : ℕ)
    (x : Fin (n + 1) → ι') :
    pushforwardCechMapF R φ D R' φ' D' F ψ ρ γ hρ N n ≫
        (ModuleCat.restrictScalars.{max u v w} ρ).map
          (π D' ((basePresheaf R' φ').obj ((SheafOfModules.pushforward.{max u v w} ψ).obj N))
            n x) =
      pushforwardCechComponent R φ D R' φ' D' F ψ ρ γ hρ N x :=
  resPiLift_comp ρ _ _ x

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- **The Čech map commutes with the differentials.** -/
lemma pushforwardCechMapF_comm (N : SheafOfModules.{max u v w} R) (n : ℕ) :
    ((cechFunctor R φ D).obj N).d n (n + 1) ≫
        pushforwardCechMapF R φ D R' φ' D' F ψ ρ γ hρ N (n + 1) =
      pushforwardCechMapF R φ D R' φ' D' F ψ ρ γ hρ N n ≫
        (ModuleCat.restrictScalars.{max u v w} ρ).map
          (((cechFunctor R' φ' D').obj ((SheafOfModules.pushforward.{max u v w} ψ).obj N)).d n
            (n + 1)) := by
  refine resCech_hom_ext R' φ' D' ρ _ fun y ↦ ?_
  have hd := d_comp_π D ((basePresheaf R φ).obj N) n (τ ∘ y)
  have hd' := d_comp_π D' ((basePresheaf R' φ').obj
    ((SheafOfModules.pushforward.{max u v w} ψ).obj N)) n y
  rw [Category.assoc, pushforwardCechMapF_comp, Category.assoc, ← Functor.map_comp,
    show ((cechFunctor R' φ' D').obj ((SheafOfModules.pushforward.{max u v w} ψ).obj N)).d n
        (n + 1) ≫ π D' _ (n + 1) y = _ from hd',
    Functor.map_sum, Preadditive.comp_sum]
  dsimp only [pushforwardCechComponent]
  rw [← Category.assoc,
    show ((cechFunctor R φ D).obj N).d n (n + 1) ≫ π D _ (n + 1) (τ ∘ y) = _ from hd,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp, Functor.map_zsmul, Preadditive.comp_zsmul]
  congr 1
  rw [Functor.map_comp]
  refine Eq.trans ?_ ((reassoc_of% (pushforwardCechMapF_comp R φ D R' φ' D' F ψ ρ γ hρ N n
    (y ∘ i.succAbove))) _).symm
  dsimp only [pushforwardCechComponent]
  simp only [Category.assoc]
  rw [← pushforwardSectionsHom_naturality, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← op_comp, ← op_comp, cechLiftMap_comp_interMap]
  rfl

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- **The Čech map is natural in the sheaf of modules.** -/
lemma pushforwardCechMapF_naturality {N N' : SheafOfModules.{max u v w} R} (g : N ⟶ N') (n : ℕ) :
    ((cechFunctor R φ D).map g).f n ≫ pushforwardCechMapF R φ D R' φ' D' F ψ ρ γ hρ N' n =
      pushforwardCechMapF R φ D R' φ' D' F ψ ρ γ hρ N n ≫
        (ModuleCat.restrictScalars.{max u v w} ρ).map
          (((cechFunctor R' φ' D').map
            ((SheafOfModules.pushforward.{max u v w} ψ).map g)).f n) := by
  refine resCech_hom_ext R' φ' D' ρ _ fun x ↦ ?_
  rw [Category.assoc, pushforwardCechMapF_comp, Category.assoc, ← Functor.map_comp]
  refine Eq.trans ?_ (congrArg (pushforwardCechMapF R φ D R' φ' D' F ψ ρ γ hρ N n ≫ ·)
    (congrArg (ModuleCat.restrictScalars.{max u v w} ρ).map (map_f_π D' _ n x).symm))
  rw [Functor.map_comp]
  refine Eq.trans ?_ ((reassoc_of% (pushforwardCechMapF_comp R φ D R' φ' D' F ψ ρ γ hρ N n x))
    _).symm
  dsimp only [pushforwardCechComponent]
  rw [← Category.assoc, show ((cechFunctor R φ D).map g).f n ≫ π D _ n (τ ∘ x) = _ from
    map_f_π D ((basePresheaf R φ).map g) n (τ ∘ x), Category.assoc, Category.assoc]
  refine congrArg (π D ((basePresheaf R φ).obj N) n (τ ∘ x) ≫ ·) ?_
  rw [← Category.assoc, ← NatTrans.naturality, Category.assoc,
    pushforwardSectionsHom_naturality_left]
  rfl

/-- **The map of Čech complexes `Č(D, -) ⟶ P ⋙ res_ρ Č(D', -)` induced by the
`γ i' : F(D' i') ⟶ D (τ i')`**, for the pullback `P` of sheaves of modules along `F`. -/
def pushforwardCechMap :
    cechFunctor R φ D ⟶ SheafOfModules.pushforward.{max u v w} ψ ⋙ cechFunctor R' φ' D' ⋙
      (ModuleCat.restrictScalars.{max u v w} ρ).mapHomologicalComplex (up ℕ) where
  app N :=
    { f n := pushforwardCechMapF R φ D R' φ' D' F ψ ρ γ hρ N n
      comm' n m hnm := by
        obtain rfl : n + 1 = m := hnm
        exact (pushforwardCechMapF_comm R φ D R' φ' D' F ψ ρ γ hρ N n).symm }
  naturality N N' g := HomologicalComplex.hom_ext _ _ fun n ↦
    pushforwardCechMapF_naturality R φ D R' φ' D' F ψ ρ γ hρ g n

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The components of `pushforwardCechMap`. -/
lemma pushforwardCechMap_app_f (N : SheafOfModules.{max u v w} R) (n : ℕ) :
    ((pushforwardCechMap R φ D R' φ' D' F ψ ρ γ hρ).app N).f n =
      pushforwardCechMapF R φ D R' φ' D' F ψ ρ γ hρ N n :=
  rfl

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- **The Čech map is compatible in degree zero with the comparison of global sections**
`α : Γ(C, N) ⟶ res_ρ Γ(C', P N)` reading a global section at the images `F V'`. -/
lemma augmentation_comp_pushforwardCechMap
    (α : baseGlobalSections R φ ⟶ SheafOfModules.pushforward.{max u v w} ψ ⋙
      baseGlobalSections R' φ' ⋙ ModuleCat.restrictScalars ρ)
    (hα : ∀ (N : SheafOfModules.{max u v w} R) (s : N.sections) (V : C'),
      ((α.app N).hom s).val (op V) = s.val (op (F.obj V)))
    (N : SheafOfModules.{max u v w} R) :
    (augmentation R φ D).app N ≫ ((pushforwardCechMap R φ D R' φ' D' F ψ ρ γ hρ).app N).f 0 =
      α.app N ≫ (ModuleCat.restrictScalars.{max u v w} ρ).map
        ((augmentation R' φ' D').app ((SheafOfModules.pushforward.{max u v w} ψ).obj N)) := by
  refine resCech_hom_ext R' φ' D' ρ _ fun x ↦ ?_
  rw [pushforwardCechMap_app_f, Category.assoc, pushforwardCechMapF_comp, Category.assoc,
    ← Functor.map_comp, augmentation_app_π]
  dsimp only [pushforwardCechComponent]
  refine ((reassoc_of% (augmentation_app_π R φ D N (τ ∘ x))) _).trans ?_
  ext s
  exact ((s : N.sections).2 (cechLiftMap D D' F γ x).op).trans (hα N s (inter D' x)).symm

variable [EnoughInjectives (SheafOfModules.{max u v w} R)]
  [HasSheafify J' AddCommGrpCat.{max u v w}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (SheafOfModules.{max u v w} R')]
  [HasDerivedCategory (SheafOfModules.{max u v w} R)]
  [HasDerivedCategory (ModuleCat.{max u v w} A)]
  [HasDerivedCategory (SheafOfModules.{max u v w} R')]
  [HasDerivedCategory (ModuleCat.{max u v w} A')] [EnoughInjectives (ModuleCat.{max u v w} A')]
  [(SheafOfModules.pushforward.{max u v w} ψ).Additive]
  [PreservesFiniteLimits (SheafOfModules.pushforward.{max u v w} ψ)]
  [PreservesFiniteColimits (SheafOfModules.pushforward.{max u v w} ψ)]

/-- **The derived comparison of global sections along a continuous functor is the Čech map.**
Let `F : C' ⥤ C` be a continuous functor, `ψ : R' ⟶ F_* R` a morphism of sheaves of rings whose
pullback of sheaves of modules `P = SheafOfModules.pushforward ψ` is exact, `ρ : A ⟶ A'` a ring
map compatible with `ψ` and the ring maps to the global sections (`hρ`), and
`α : Γ(C, N) ⟶ res_ρ Γ(C', P N)` the comparison of global sections reading a section at the
images `F V'` (`hα`). Let `D` and `D'` be families covering the final objects of `C` and `C'`
with all finite nonempty products, and `γ i' : F(D' i') ⟶ D (τ i')`. Then for every sheaf of
`R`-modules `N`, the Čech comparison `Č(D, N) ⟶ RΓ(C, N)` followed by
`CategoryTheory.Functor.derivedSquareMap α N : RΓ(C, N) ⟶ res_ρ RΓ(C', P N)` is the class of the
Čech map `Č(D, N) ⟶ res_ρ Č(D', P N)` induced by the `γ` (`pushforwardCechMap`), followed by
`res_ρ` of the Čech comparison `Č(D', P N) ⟶ RΓ(C', P N)`. -/
theorem cechToDerivedGlobalSections_comp_derivedSquareMap_pushforward (hD : J.CoversTop D)
    (hD' : J'.CoversTop D')
    (α : baseGlobalSections R φ ⟶ SheafOfModules.pushforward.{max u v w} ψ ⋙
      baseGlobalSections R' φ' ⋙ ModuleCat.restrictScalars ρ)
    (hα : ∀ (N : SheafOfModules.{max u v w} R) (s : N.sections) (V : C'),
      ((α.app N).hom s).val (op V) = s.val (op (F.obj V)))
    (N : SheafOfModules.{max u v w} R) :
    (cechToDerivedGlobalSections R φ D hD).app N ≫ Functor.derivedSquareMap α N =
      (DerivedCategory.Plus.qhQIso ((cechPlusFunctor R φ D).obj N)).inv ≫
        DerivedCategory.Plus.Qh.map (cechMapPlus R φ D R' φ' D'
          (SheafOfModules.pushforward.{max u v w} ψ) ρ
          (cechIntMap R φ D R' φ' D' (SheafOfModules.pushforward.{max u v w} ψ) ρ
            (pushforwardCechMap R φ D R' φ' D' F ψ ρ γ hρ)) N) ≫
        (ModuleCat.restrictScalars.{max u v w} ρ).mapDerivedCategoryPlusFactorsh.inv.app _ ≫
        (ModuleCat.restrictScalars.{max u v w} ρ).mapDerivedCategoryPlus.map
          ((DerivedCategory.Plus.qhQIso ((cechPlusFunctor R' φ' D').obj
              ((SheafOfModules.pushforward.{max u v w} ψ).obj N))).hom ≫
            (cechToDerivedGlobalSections R' φ' D' hD').app
              ((SheafOfModules.pushforward.{max u v w} ψ).obj N)) :=
  cechToDerivedGlobalSections_comp_derivedSquareMap R φ D R' φ' D'
    (SheafOfModules.pushforward.{max u v w} ψ) ρ α _ hD hD'
    (augmentationInt_comp_cechIntMap_f R φ D R' φ' D' _ ρ _ α
      (augmentation_comp_pushforwardCechMap R φ D R' φ' D' F ψ ρ γ hρ α hα)) N

end Pushforward

end Stacks.CechSite.FinalCover

end

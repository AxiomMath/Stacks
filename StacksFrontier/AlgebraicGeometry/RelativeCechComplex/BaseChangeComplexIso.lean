module

public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.BaseChangeComplex
public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Basic
public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# The base change map of the coefficient presheaves is the affine base change morphism

The component of `coefficientPullback` at an object `A` of `Over X` is the base change morphism of
[Stacks, Tag 02KG] for the cartesian square over `A` (`coefficientPullback_app`).  The file also
builds isomorphisms of Čech complexes from isomorphisms of the coefficients at the finite
intersections (`cechIsoOfComponents`), and identifies the Čech complex of the coefficient presheaf
of [Stacks, Tag 01XL] with that of the presheaf of monads followed by the pushforward
(`cechRelativeCechPresheafIso`).
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechBaseChange

open Stacks.AlgebraicGeometry.RelativeCech

variable {X X' : Scheme.{u}}

section Components

variable {S S' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

open Stacks.AlgebraicGeometry.AffinePushforward

/-- The restriction maps of the presheaf of monads followed by a pushforward, at the opposite of
a morphism of `Over X`. -/
theorem flip_comp_pushforward_map_op {Y : Scheme.{u}} (k : X ⟶ Y) (N : X.Modules)
    {B C : Over X} (ψ : C ⟶ B) :
    ((relativeMonad X).flip.obj N ⋙ pushforward k).map ψ.op =
      (pushforward k).map ((relativeUnit' ψ.left B.hom C.hom (Over.w ψ)).app N) := by
  rw [Functor.comp_map, Functor.flip_obj_map]
  exact congrArg (fun t ↦ (pushforward k).map (NatTrans.app t N)) (relativeMonad_map X ψ)

/-- The components of `coefficientMapIso`. -/
theorem coefficientMapIso_hom_app (w : g' ≫ f = f' ≫ g) (M : X.Modules) (B : Over X') :
    (coefficientMapIso w M).hom.app (op B) =
      (pushforward f).map ((pushforward (B.hom ≫ g')).map ((pullbackComp B.hom g').inv.app M)) ≫
        (pushforwardSquareIso w).hom.app ((pushforward B.hom).obj
          ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback B.hom).obj M)) := rfl

/-- The components of `restrictCounit` at the opposite of an object. -/
theorem restrictCounit_app_op {C : Type*} [Category* C] (g' : X' ⟶ X)
    {G : Over X ⥤ Over X'} (ε : G ⋙ Over.map g' ⟶ 𝟭 _)
    (P : (Over X)ᵒᵖ ⥤ C) (R : (Over X')ᵒᵖ ⥤ C) (θ : (Over.map g').op ⋙ P ⟶ R) (A : Over X) :
    (restrictCounit g' ε P R θ).app (op A) = P.map (ε.app A).op ≫ θ.app (op (G.obj A)) := rfl

/-- The restriction map along a component of `ε : G ⋙ Over.map g' ⟶ 𝟭`, with the source and the
target of the component spelled through `G`. -/
theorem relativeUnit'_counit (g' : X' ⟶ X) {G : Over X ⥤ Over X'} (ε : G ⋙ Over.map g' ⟶ 𝟭 _)
    (A : Over X) :
    relativeUnit' (ε.app A).left ((𝟭 (Over X)).obj A).hom ((G ⋙ Over.map g').obj A).hom
        (Over.w (ε.app A)) =
      relativeUnit' (ε.app A).left A.hom ((G.obj A).hom ≫ g') (Over.w (ε.app A)) := rfl

/-- The components of `coefficientBaseChange`. -/
theorem coefficientBaseChange_app (w : g' ≫ f = f' ≫ g) {G : Over X ⥤ Over X'}
    (ε : G ⋙ Over.map g' ⟶ 𝟭 _) (M : X.Modules) (A : Over X) :
    (coefficientBaseChange w ε M).app (op A) =
      (pushforward f).map ((relativeUnit' (ε.app A).left A.hom ((G.obj A).hom ≫ g')
          (Over.w (ε.app A))).app M) ≫
        ((pushforward f).map ((pushforward ((G.obj A).hom ≫ g')).map
            ((pullbackComp (G.obj A).hom g').inv.app M)) ≫
          (pushforwardSquareIso w).hom.app ((pushforward (G.obj A).hom).obj
            ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback (G.obj A).hom).obj M))) := by
  rw [coefficientBaseChange, restrictCounit_app_op, flip_comp_pushforward_map_op f M (ε.app A),
    coefficientMapIso_hom_app, relativeUnit'_counit g' ε A]
  rfl

/-- The value of the presheaf of monads at `a : A ⟶ X` is the monad `a_* a^*`. -/
theorem relativeMonad_obj (A : (Over X)ᵒᵖ) :
    (relativeMonad X).obj A = Scheme.Modules.pullback A.unop.hom ⋙ pushforward A.unop.hom := rfl

/-- The pushforward along `u ≫ b` of a module is the pushforward along `b` of its pushforward
along `u`. -/
theorem pushforward_comp_obj {Y Z W : Scheme.{u}} (u : Y ⟶ Z) (b : Z ⟶ W) (N : Y.Modules) :
    (pushforward (u ≫ b)).obj N = (pushforward b).obj ((pushforward u).obj N) := rfl

/-- A morphism is the transpose of `γ` at `j` as soon as `γ_j` is its image under the unit. -/
theorem transposeNatTrans_app_eq {J C D : Type*} [Category* J] [Category* C] [Category* D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) {P : J ⥤ C} {Q : J ⥤ D} (γ : P ⟶ Q ⋙ G) (j : J)
    (β : L.obj (P.obj j) ⟶ Q.obj j) (h : γ.app j = adj.unit.app (P.obj j) ≫ G.map β) :
    (transposeNatTrans adj γ).app j = β := by
  rw [transposeNatTrans_app, Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
  exact h

open Stacks.AlgebraicGeometry.AffinePushforward in
/-- `square_identity`, with the transpose written through the unit of `g^* ⊣ g_*`. -/
theorem square_identity_unit {A A' : Scheme.{u}} (h : A' ⟶ A) (a : A ⟶ X) (a' : A' ⟶ X')
    (hk : h ≫ a = a' ≫ g') (w : g' ≫ f = f' ≫ g) (hm : (a' ≫ g') ≫ f = (a' ≫ f') ≫ g)
    (wA : h ≫ a ≫ f = (a' ≫ f') ≫ g) (M : X.Modules) :
    (pushforward f).map ((relativeUnit' h a (a' ≫ g') hk).app M) ≫
        ((pushforward f).map ((pushforward (a' ≫ g')).map ((pullbackComp a' g').inv.app M)) ≫
          (pushforwardSquareIso w).hom.app ((pushforward a').obj
            ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback a').obj M))) =
      (pullbackPushforwardAdjunction g).unit.app ((pushforward (a ≫ f)).obj
          ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforward g).map ((baseChangeNatTrans wA).app ((Scheme.Modules.pullback a).obj M) ≫
          (pushforward (a' ≫ f')).map ((pullbackComp h a).hom.app M ≫
            (pullbackCongr hk).hom.app M ≫ (pullbackComp a' g').inv.app M)) :=
  (square_identity h a a' hk w hm wA M).trans (Adjunction.homEquiv_unit _ _ _ _)

/-- **The base change map of coefficient presheaves is the affine base change morphism.**  At
`A : Over X`, `coefficientPullback` is the base change morphism of [Stacks, Tag 02KG] for the
square `ε_A : G(A) ⟶ A` over `g : S' ⟶ S`, followed by the identification
`ε_A^* a^* M ≅ a'^* (g')^* M`. -/
theorem coefficientPullback_app (w : g' ≫ f = f' ≫ g) {G : Over X ⥤ Over X'}
    (ε : G ⋙ Over.map g' ⟶ 𝟭 _) (M : X.Modules) (A : Over X)
    (hm : ((G.obj A).hom ≫ g') ≫ f = ((G.obj A).hom ≫ f') ≫ g)
    (wA : (ε.app A).left ≫ A.hom ≫ f = ((G.obj A).hom ≫ f') ≫ g) :
    (coefficientPullback w ε M).app (op A) =
      (baseChangeNatTrans wA).app ((Scheme.Modules.pullback A.hom).obj M) ≫
        (pushforward ((G.obj A).hom ≫ f')).map ((pullbackComp (ε.app A).left A.hom).hom.app M ≫
          (pullbackCongr (Over.w (ε.app A) :
            (ε.app A).left ≫ A.hom = (G.obj A).hom ≫ g')).hom.app M ≫
            (pullbackComp (G.obj A).hom g').inv.app M) := by
  refine transposeNatTrans_app_eq _ _ _ _ ?_
  rw [coefficientBaseChange_app]
  refine (square_identity_unit (g' := g') (ε.app A).left A.hom (G.obj A).hom
    (Over.w (ε.app A) : (ε.app A).left ≫ A.hom = (G.obj A).hom ≫ g') w hm wA M).trans ?_
  dsimp only [Functor.comp_obj, Functor.flip_obj_obj, relativeMonad_obj, Functor.op_obj,
    Opposite.unop_op, pushforward_comp_obj]

/-- The base change map of coefficient presheaves is invertible at `A` as soon as the base change
morphism of the square `ε_A : G(A) ⟶ A` over `g : S' ⟶ S` is invertible at `a^* M`. -/
theorem isIso_coefficientPullback_app_of (w : g' ≫ f = f' ≫ g) {G : Over X ⥤ Over X'}
    (ε : G ⋙ Over.map g' ⟶ 𝟭 _) (M : X.Modules) (A : Over X)
    (hm : ((G.obj A).hom ≫ g') ≫ f = ((G.obj A).hom ≫ f') ≫ g)
    (wA : (ε.app A).left ≫ A.hom ≫ f = ((G.obj A).hom ≫ f') ≫ g)
    (h : IsIso ((baseChangeNatTrans wA).app ((Scheme.Modules.pullback A.hom).obj M))) :
    IsIso ((coefficientPullback w ε M).app (op A)) := by
  rw [coefficientPullback_app w ε M A hm wA]
  have hiso : IsIso ((pushforward ((G.obj A).hom ≫ f')).map
      ((pullbackComp (ε.app A).left A.hom).hom.app M ≫
        (pullbackCongr (Over.w (ε.app A) :
          (ε.app A).left ≫ A.hom = (G.obj A).hom ≫ g')).hom.app M ≫
          (pullbackComp (G.obj A).hom g').inv.app M)) :=
    Iso.isIso_hom ((pushforward ((G.obj A).hom ≫ f')).mapIso
      ((pullbackComp (ε.app A).left A.hom).app M ≪≫
        (pullbackCongr (Over.w (ε.app A) :
          (ε.app A).left ≫ A.hom = (G.obj A).hom ≫ g')).app M ≪≫
          ((pullbackComp (G.obj A).hom g').app M).symm))
  have := IsIso.comp_isIso' h hiso
  exact this

end Components


/-! ### Products in `Over X` and in `X.Modules` -/

/-- Finite products in `Over Y`. -/
scoped instance (priority := high) hasFiniteProducts_over (Y : Scheme.{u}) :
    Limits.HasFiniteProducts (Over Y) :=
  inferInstance

/-- Products in `Y.Modules`. -/
scoped instance (priority := high) hasProducts_modules (Y : Scheme.{u}) :
    Limits.HasProducts.{u} Y.Modules :=
  inferInstance

/-! ### Isomorphisms of Čech complexes -/

section CechIso

open CategoryTheory.Limits

variable {C A : Type*} [Category* C] [HasFiniteProducts C] [Category* A] [Preadditive A]
  {ι : Type u} [HasProducts.{u} A] (U : ι → C)

/-- A morphism of presheaves which is invertible at every finite intersection of the members of a
family induces an isomorphism of Čech complexes. -/
theorem isIso_cechComplexFunctor_map {P Q : Cᵒᵖ ⥤ A} (θ : P ⟶ Q)
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsIso (θ.app (op (∏ᶜ fun a ↦ U (x a))))) :
    IsIso ((cechComplexFunctor U).map θ) := by
  have (n : ℕ) : IsIso (((cechComplexFunctor U).map θ).f n) := by
    have := h n
    exact inferInstanceAs
      (IsIso (Limits.Pi.map fun x : Fin (n + 1) → ι ↦ θ.app (op (∏ᶜ fun a ↦ U (x a)))))
  exact HomologicalComplex.Hom.isIso_of_components _

open Stacks.CategoryTheory.CechComplex in
/-- The degreewise isomorphism of Čech complexes induced by isomorphisms of the values at the
finite intersections. -/
noncomputable def cechXIsoOfComponents {P Q : Cᵒᵖ ⥤ A}
    (e : ∀ {m : ℕ} (x : Fin m → ι), P.obj (op (inter U x)) ≅ Q.obj (op (inter U x))) (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ≅ ((cechComplexFunctor U).obj Q).X n :=
  Limits.Pi.mapIso fun x : Fin (n + 1) → ι ↦ e x

open Stacks.CategoryTheory.CechComplex in
/-- The component of `cechXIsoOfComponents` at the intersection indexed by `x` is `e x`. -/
theorem cechXIsoOfComponents_hom_π {P Q : Cᵒᵖ ⥤ A}
    (e : ∀ {m : ℕ} (x : Fin m → ι), P.obj (op (inter U x)) ≅ Q.obj (op (inter U x))) (n : ℕ)
    (x : Fin (n + 1) → ι) :
    (cechXIsoOfComponents U e n).hom ≫ π U Q n x = π U P n x ≫ (e x).hom :=
  Limits.Pi.map_π (fun x : Fin (n + 1) → ι ↦ (e x).hom) x

open Stacks.CategoryTheory.CechComplex in
/-- **An isomorphism of Čech complexes from isomorphisms of the values at the finite
intersections**, compatible with the restriction maps between intersections. -/
noncomputable def cechIsoOfComponents {P Q : Cᵒᵖ ⥤ A}
    (e : ∀ {m : ℕ} (x : Fin m → ι), P.obj (op (inter U x)) ≅ Q.obj (op (inter U x)))
    (he : ∀ {m m' : ℕ} (x : Fin m → ι) (h : Fin m' → Fin m),
      P.map (interMap U x h).op ≫ (e x).hom = (e (x ∘ h)).hom ≫ Q.map (interMap U x h).op) :
    (cechComplexFunctor U).obj P ≅ (cechComplexFunctor U).obj Q :=
  HomologicalComplex.Hom.isoOfComponents (cechXIsoOfComponents U e) (by
    rintro n _ rfl
    refine hom_ext U Q fun y ↦ ?_
    rw [Category.assoc, Category.assoc, cechXIsoOfComponents_hom_π, d_comp_π,
      ← Category.assoc, d_comp_π, Preadditive.comp_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc, he,
      ← Category.assoc, ← Category.assoc, cechXIsoOfComponents_hom_π])

open Stacks.CategoryTheory.CechComplex in
/-- `cechIsoOfComponents`, for a family of isomorphisms with an explicit length argument. -/
noncomputable def cechIsoOfComponents' {P Q : Cᵒᵖ ⥤ A}
    (e : ∀ (m : ℕ) (x : Fin m → ι), P.obj (op (inter U x)) ≅ Q.obj (op (inter U x)))
    (he : ∀ {m m' : ℕ} (x : Fin m → ι) (h : Fin m' → Fin m),
      P.map (interMap U x h).op ≫ (e m x).hom = (e m' (x ∘ h)).hom ≫ Q.map (interMap U x h).op) :
    (cechComplexFunctor U).obj P ≅ (cechComplexFunctor U).obj Q :=
  cechIsoOfComponents U (fun x ↦ e _ x) (fun x h ↦ he x h)

/-- The change-of-site isomorphism of Čech complexes, at one presheaf. -/
noncomputable def cechSiteIsoObj {D : Type*} [Category* D] [HasFiniteProducts D]
    (Φ : C ⥤ D) [PreservesFiniteProducts Φ] (Q : Dᵒᵖ ⥤ A) :
    (cechComplexFunctor (A := A) fun i ↦ Φ.obj (U i)).obj Q ≅
      (cechComplexFunctor (A := A) U).obj (Φ.op ⋙ Q) :=
  (Stacks.CechSiteChange.cechComplexFunctorSiteIso Φ U).app Q

end CechIso

/-! ### The coefficient presheaf of [Stacks, Tag 01XL] -/

section RelativeCechPresheaf

/-- The underlying `𝒪_Y`-module of a quasi-coherent module. -/
noncomputable def qcohModule {Y : Scheme.{u}}
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) : Y.Modules :=
  G.obj

/-- The coefficient presheaf of the presheaf of monads followed by a pushforward, at an object. -/
theorem flip_comp_pushforward_obj {Y Z : Scheme.{u}} (k : Y ⟶ Z) (N : Y.Modules) (A : Over Y) :
    ((relativeMonad Y).flip.obj N ⋙ Scheme.Modules.pushforward k).obj (op A) =
      (Scheme.Modules.pushforward (A.hom ≫ k)).obj ((Scheme.Modules.pullback A.hom).obj N) := rfl

/-- The values of the coefficient presheaf of [Stacks, Tag 01XL] are those of the presheaf of
monads followed by the pushforward. -/
theorem relativeCechPresheaf_obj_op {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) (A : Over Y) :
    ((relativeCechPresheaf k).obj G).obj (op A) =
      ((relativeMonad Y).flip.obj (qcohModule G) ⋙ Scheme.Modules.pushforward k).obj (op A) :=
  (relativeCechPresheaf_obj_obj k G A).trans (flip_comp_pushforward_obj k (qcohModule G) A).symm

/-- The restriction maps of the coefficient presheaf of [Stacks, Tag 01XL] are those of the
presheaf of monads followed by the pushforward. -/
theorem relativeCechPresheaf_map_op {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) {A B : Over Y}
    (h : A ⟶ B) :
    ((relativeCechPresheaf k).obj G).map h.op =
      ((relativeMonad Y).flip.obj (qcohModule G) ⋙ Scheme.Modules.pushforward k).map h.op :=
  (relativeCechPresheaf_obj_map k G h).trans (flip_comp_pushforward_map_op k (qcohModule G) h).symm

/-- A transport along an equality of an object with itself commutes with every morphism. -/
theorem comp_eqToHom_eq_eqToHom_comp {C : Type*} [Category* C] {X₁ Y₁ : C} (x : X₁ ⟶ Y₁)
    (h₁ : X₁ = X₁) (h₂ : Y₁ = Y₁) : x ≫ eqToHom h₂ = eqToHom h₁ ≫ x := by
  simp

/-- The comparison of the restriction maps of `relativeCechPresheaf_map_op`, through the
identifications of the values. -/
theorem relativeCechPresheaf_map_op_eqToHom {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) {A B : Over Y}
    (h : A ⟶ B) :
    ((relativeCechPresheaf k).obj G).map h.op ≫ eqToHom (relativeCechPresheaf_obj_op k G A) =
      eqToHom (relativeCechPresheaf_obj_op k G B) ≫
        ((relativeMonad Y).flip.obj (qcohModule G) ⋙ Scheme.Modules.pushforward k).map h.op := by
  rw [relativeCechPresheaf_map_op k G h]
  exact comp_eqToHom_eq_eqToHom_comp _ _ _

/-- The identification of the values of the coefficient presheaf of [Stacks, Tag 01XL] with those
of the presheaf of monads followed by the pushforward. -/
noncomputable def relativeCechPresheafObjIso {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) (A : Over Y) :
    ((relativeCechPresheaf k).obj G).obj (op A) ≅
      ((relativeMonad Y).flip.obj (qcohModule G) ⋙ Scheme.Modules.pushforward k).obj (op A) :=
  eqToIso (relativeCechPresheaf_obj_op k G A)

/-- Naturality of `relativeCechPresheafObjIso`. -/
theorem relativeCechPresheafObjIso_naturality {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) {A B : Over Y}
    (h : A ⟶ B) :
    ((relativeCechPresheaf k).obj G).map h.op ≫ (relativeCechPresheafObjIso k G A).hom =
      (relativeCechPresheafObjIso k G B).hom ≫
        ((relativeMonad Y).flip.obj (qcohModule G) ⋙ Scheme.Modules.pushforward k).map h.op :=
  relativeCechPresheaf_map_op_eqToHom k G h

open Stacks.CategoryTheory.CechComplex in
/-- `relativeCechPresheafObjIso` at the finite intersections of the members of a family. -/
noncomputable def relativeCechPresheafInterIso {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) {ι : Type u}
    (V : ι → Over Y) (m : ℕ) (x : Fin m → ι) :
    ((relativeCechPresheaf k).obj G).obj (op (inter V x)) ≅
      ((relativeMonad Y).flip.obj (qcohModule G) ⋙ Scheme.Modules.pushforward k).obj
        (op (inter V x)) :=
  relativeCechPresheafObjIso k G (inter V x)

open Stacks.CategoryTheory.CechComplex in
/-- Naturality of `relativeCechPresheafInterIso`. -/
theorem relativeCechPresheafInterIso_naturality {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) {ι : Type u}
    (V : ι → Over Y) {m m' : ℕ} (x : Fin m → ι) (h : Fin m' → Fin m) :
    ((relativeCechPresheaf k).obj G).map (interMap V x h).op ≫
        (relativeCechPresheafInterIso k G V m x).hom =
      (relativeCechPresheafInterIso k G V m' (x ∘ h)).hom ≫
        ((relativeMonad Y).flip.obj (qcohModule G) ⋙ Scheme.Modules.pushforward k).map
          (interMap V x h).op :=
  relativeCechPresheafObjIso_naturality k G (interMap V x h)

/-- **The Čech complex of the coefficient presheaf of [Stacks, Tag 01XL] is the Čech complex of
the presheaf of monads followed by the pushforward.** -/
noncomputable def cechRelativeCechPresheafIso {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) {ι : Type u}
    (V : ι → Over Y) :
    (cechComplexFunctor V).obj ((relativeCechPresheaf k).obj G) ≅
      (cechComplexFunctor V).obj
        ((relativeMonad Y).flip.obj (qcohModule G) ⋙ Scheme.Modules.pushforward k) :=
  cechIsoOfComponents' V (relativeCechPresheafInterIso k G V)
    (relativeCechPresheafInterIso_naturality k G V)

/-- `cechRelativeCechPresheafIso`, for a module equal to the underlying module. -/
noncomputable def cechRelativeCechPresheafIsoOfEq {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) {ι : Type u}
    (V : ι → Over Y) (N : Y.Modules) (hN : qcohModule G = N) :
    (cechComplexFunctor V).obj ((relativeCechPresheaf k).obj G) ≅
      (cechComplexFunctor V).obj ((relativeMonad Y).flip.obj N ⋙ Scheme.Modules.pushforward k) := by
  subst hN
  exact cechRelativeCechPresheafIso k G V

end RelativeCechPresheaf

end Stacks.AlgebraicGeometry.RelativeCechBaseChange

end

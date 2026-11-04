module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.CategoryTheory.Preadditive.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BandedSheaf
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentDataEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Existence of an object of a gerbe with abelian automorphism sheaves

Let `p : 𝒮 ⥤ 𝒞` be a gerbe over the site `(𝒞, J)` whose automorphism sheaves are abelian and let
`𝒢` be the sheaf of abelian groups that Stacks 0CJY builds out of them. Stacks 0CK0 says that an
object `U` of `𝒞` carries an object of `𝒮` as soon as

1. there is a cofinal system of coverings `{U_i → U}` of `U` with `H¹(U_i, 𝒢) = 0` and
   `H¹(U_i ×_U U_j, 𝒢) = 0` for all `i`, `j`, and
2. `H²(U, 𝒢) = 0`.

The proof is the source's. A covering of `U` with objects `x_i` over its members exists because a
gerbe is locally nonempty, and (1) refines it inside the cofinal system. The sheaf
`Isom(x_i|, x_j|)` on `𝒞/U_ij` is a torsor under `𝒢|_{U_ij} = Aut(x_i|_{U_ij})`, trivial because
`H¹(U_ij, 𝒢) = 0` (Stacks 03AJ and 03AI), so there are isomorphisms
`φ_ij : x_i|_{U_ij} → x_j|_{U_ij}`. Their failure to satisfy the cocycle condition is a Čech
`2`-cocycle `g_ijk` with values in `𝒢`, and it is a coboundary because `H²(U, 𝒢) = 0` while
`H¹(U_i, 𝒢) = 0` keeps the Čech class from dying on the way to `H²(U, 𝒢)`. Correcting `φ_ij` by
that coboundary gives a descent datum, which is effective because `p` is a stack.

## Main results

* `CategoryTheory.Gerbe.nonempty_fiber_of_cohomology_vanishing`: Stacks 0CK0 for a sheaf `𝒢`
  given together with the comparisons `𝒢|_V ≅ Aut(y)` of Stacks 0CJY, which is what "the sheaf
  constructed in Stacks 0CJY" names.
* `CategoryTheory.Gerbe.exists_band_nonempty_fiber_of_cohomology_vanishing`: the same with
  nothing assumed — the sheaf `𝒢` and its comparisons are produced here, by Stacks 0CJY, so no
  hypothesis of this statement is the conclusion of another tag.

## Implementation notes

`𝒢` is an additive sheaf given with the multiplicative comparison with each automorphism
presheaf, including compatibility with conjugation and with base change, as Stacks 0CJY supplies
them; the base-change clause identifies the comparison at a pullback with the comparison at the
original object, so the comparisons cannot vary independently over different base objects.
Covering families are pre-zero-hypercovers and cofinality is refinement of covering sieves.
`H^n(V, 𝒢) = 0` is `Subsingleton (Sheaf.H (𝒢.over V) n)`, the cohomology of the restriction of
`𝒢` to the slice site `𝒞/V` at the terminal object of that site. This formulation keeps the
coefficient universe independent of the morphism universe of the site.

Stacks 0CJY is valued in `CommGrpCat` while `Sheaf.H` takes coefficients in `AddCommGrpCat`; the
two are carried into one another by `commGroupAddCommGroupEquivalence`, whose unit and counit are
`Iso.refl`, and that is what lets the second statement below instantiate the first at the band.

## References

* [Stacks 0CK0](https://stacks.math.columbia.edu/tag/0CK0)
* [Stacks 0CJY](https://stacks.math.columbia.edu/tag/0CJY)
* [Stacks 06NZ](https://stacks.math.columbia.edu/tag/06NZ)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.Torsors

universe x w w' v₁ u₁ v₂ u₂

namespace CategoryTheory.Gerbe

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

private noncomputable def bandEndEquiv
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{max w v₂}) {U : C} (y : p.Fiber U)
    (θ : (Over.forget U).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp ⋙ forget CommGrpCat ≅
      p.morPresheaf y y ⋙ uliftFunctor.{w, v₂}) :
    G.obj.obj (op U) ≃ (y ⟶ y) :=
  ((θ.app (op (Over.mk (𝟙 U)))).toEquiv.trans Equiv.ulift).trans
    (Iso.homCongr (Functor.pullbackFiberIdIso y) (Functor.pullbackFiberIdIso y))

private lemma bandEndEquiv_apply
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{max w v₂}) {U : C} (y : p.Fiber U)
    (θ : (Over.forget U).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp ⋙ forget CommGrpCat ≅
      p.morPresheaf y y ⋙ uliftFunctor.{w, v₂}) (a : G.obj.obj (op U)) :
    bandEndEquiv p G y θ a = (Functor.pullbackFiberIdIso y).inv ≫
      (θ.hom.app (op (Over.mk (𝟙 U))) (Multiplicative.ofAdd a)).down ≫
        (Functor.pullbackFiberIdIso y).hom := rfl

private lemma pullbackFiberHom_pullbackFiberIdIso_hom
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {V W : C} (y : p.Fiber V) (f : W ⟶ V) :
    Functor.pullbackFiberHom (Functor.pullbackFiberIdIso y).hom f =
      (Functor.pullbackFiberCompIso' y (𝟙 V) f f (Category.comp_id f)).hom := by
  apply (cancel_epi
    (Functor.pullbackFiberCompIso' y (𝟙 V) f f (Category.comp_id f)).inv).mp
  rw [← Functor.pullbackFiberHom_pullbackFiberIdIso_inv_eq,
    ← Functor.pullbackFiberHom_comp, Iso.inv_hom_id, Functor.pullbackFiberHom_id,
    Functor.pullbackFiberHom_pullbackFiberIdIso_inv_eq, Iso.inv_hom_id]

private lemma bandEndEquiv_restrict
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{max w v₂}) {V W : C} (y : p.Fiber V)
    (θ : (Over.forget V).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp ⋙ forget CommGrpCat ≅
      p.morPresheaf y y ⋙ uliftFunctor.{w, v₂})
    (f : W ⟶ V) (a : G.obj.obj (op V)) :
    (θ.hom.app (op (Over.mk f)) (Multiplicative.ofAdd (G.obj.map f.op a))).down =
      Functor.pullbackFiberHom (bandEndEquiv p G y θ a) f := by
  let k : Over.mk f ⟶ Over.mk (𝟙 V) := Over.homMk f (Category.comp_id f)
  have hn := congrArg (fun t => (t (Multiplicative.ofAdd a)).down)
    (θ.hom.naturality k.op)
  change (θ.hom.app (op (Over.mk f))
      (Multiplicative.ofAdd (G.obj.map f.op a))).down =
    p.morRestrict y y k
      ((θ.hom.app (op (Over.mk (𝟙 V))) (Multiplicative.ofAdd a)).down) at hn
  rw [hn, Functor.morRestrict_eq_pullbackFiberHom, bandEndEquiv_apply,
    Functor.pullbackFiberHom_comp, Functor.pullbackFiberHom_comp,
    Functor.pullbackFiberHom_pullbackFiberIdIso_inv_eq,
    pullbackFiberHom_pullbackFiberIdIso_hom]
  rfl

private lemma bandEndEquiv_add
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{max w v₂}) {U : C} (y : p.Fiber U)
    (θ : (Over.forget U).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp ⋙ forget CommGrpCat ≅
      p.morPresheaf y y ⋙ uliftFunctor.{w, v₂})
    (hθ : ∀ a b : G.obj.obj (op U),
      (θ.hom.app (op (Over.mk (𝟙 U))) (Multiplicative.ofAdd (a + b))).down =
        (θ.hom.app (op (Over.mk (𝟙 U))) (Multiplicative.ofAdd a)).down ≫
          (θ.hom.app (op (Over.mk (𝟙 U))) (Multiplicative.ofAdd b)).down)
    (a b : G.obj.obj (op U)) :
    bandEndEquiv p G y θ (a + b) = bandEndEquiv p G y θ a ≫ bandEndEquiv p G y θ b := by
  simp only [bandEndEquiv_apply, hθ, Category.assoc, Iso.hom_inv_id_assoc]

private lemma pullbackFiberHom_id_base
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {U : C} {y z : p.Fiber U} (φ : y ⟶ z) :
    Functor.pullbackFiberHom φ (𝟙 U) ≫ (Functor.pullbackFiberIdIso z).hom =
      (Functor.pullbackFiberIdIso y).hom ≫ φ := by
  apply Functor.Fiber.hom_ext
  rw [Functor.map_comp, Functor.map_comp, Functor.pullbackFiberIdIso_hom_fac,
    Functor.pullbackFiberIdIso_hom_fac, Functor.pullbackFiberHom_fac]

private lemma bandEndEquiv_pullback_of_coherence
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{max w v₂}) {V W : C} (y : p.Fiber V)
    (f : W ⟶ V)
    (θ : (Over.forget V).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp ⋙ forget CommGrpCat ≅
      p.morPresheaf y y ⋙ uliftFunctor.{w, v₂})
    (η : (Over.forget W).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp ⋙ forget CommGrpCat ≅
      p.morPresheaf (p.pullbackFiber y f) (p.pullbackFiber y f) ⋙ uliftFunctor.{w, v₂})
    (hcoh : ∀ b : G.obj.obj (op W),
      (θ.hom.app (op (Over.mk f)) (Multiplicative.ofAdd b)).down =
        (Functor.pullbackFiberIdIso (p.pullbackFiber y f)).inv ≫
          (η.hom.app (op (Over.mk (𝟙 W))) (Multiplicative.ofAdd b)).down ≫
            (Functor.pullbackFiberIdIso (p.pullbackFiber y f)).hom)
    (a : G.obj.obj (op V)) :
    bandEndEquiv p G (p.pullbackFiber y f) η (G.obj.map f.op a) =
      Functor.pullbackFiberHom (bandEndEquiv p G y θ a) f := by
  rw [bandEndEquiv_apply, ← hcoh]
  exact bandEndEquiv_restrict p G y θ f a

private lemma bandEndEquiv_conj
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{max w v₂}) {U : C} (y z : p.Fiber U)
    (φ : y ⟶ z) [IsIso φ]
    (θy : (Over.forget U).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp ⋙ forget CommGrpCat ≅
      p.morPresheaf y y ⋙ uliftFunctor.{w, v₂})
    (θz : (Over.forget U).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp ⋙ forget CommGrpCat ≅
      p.morPresheaf z z ⋙ uliftFunctor.{w, v₂})
    (hθ : ∀ a : G.obj.obj (op U),
      (θz.hom.app (op (Over.mk (𝟙 U))) (Multiplicative.ofAdd a)).down =
        Functor.pullbackFiberHom (inv φ) (𝟙 U) ≫
          (θy.hom.app (op (Over.mk (𝟙 U))) (Multiplicative.ofAdd a)).down ≫
            Functor.pullbackFiberHom φ (𝟙 U))
    (a : G.obj.obj (op U)) :
    bandEndEquiv p G z θz a = inv φ ≫ bandEndEquiv p G y θy a ≫ φ := by
  have hi : (Functor.pullbackFiberIdIso z).inv ≫
      Functor.pullbackFiberHom (inv φ) (𝟙 U) =
        inv φ ≫ (Functor.pullbackFiberIdIso y).inv := by
    apply (cancel_mono (Functor.pullbackFiberIdIso y).hom).mp
    simp only [Category.assoc, pullbackFiberHom_id_base,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [bandEndEquiv_apply, hθ, Category.assoc, pullbackFiberHom_id_base]
  rw [← Category.assoc, hi]
  simp only [Category.assoc]

private lemma iso_defect_cocycle
    {D : Type*} [Category D] {X₀ X₁ X₂ X₃ : D}
    (e₀₁ : X₀ ≅ X₁) (e₀₂ : X₀ ≅ X₂) (e₀₃ : X₀ ≅ X₃)
    (e₁₂ : X₁ ≅ X₂) (e₁₃ : X₁ ≅ X₃) (e₂₃ : X₂ ≅ X₃) :
    (e₀₁.hom ≫ (e₁₂.hom ≫ e₂₃.hom ≫ e₁₃.inv) ≫ e₀₁.inv) ≫
        (e₀₁.hom ≫ e₁₃.hom ≫ e₀₃.inv) =
      (e₀₁.hom ≫ e₁₂.hom ≫ e₀₂.inv) ≫ (e₀₂.hom ≫ e₂₃.hom ≫ e₀₃.inv) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private lemma additive_iso_defect_cocycle
    {D : Type*} [Category D] {A : Type*} [AddCommGroup A]
    {X₀ X₁ X₂ X₃ : D}
    (e₀₁ : X₀ ≅ X₁) (e₀₂ : X₀ ≅ X₂) (e₀₃ : X₀ ≅ X₃)
    (e₁₂ : X₁ ≅ X₂) (e₁₃ : X₁ ≅ X₃) (e₂₃ : X₂ ≅ X₃)
    (θ₀ : A → (X₀ ⟶ X₀)) (θ₁ : A → (X₁ ⟶ X₁))
    (hθ₀ : Function.Injective θ₀)
    (hadd : ∀ a b, θ₀ (a + b) = θ₀ a ≫ θ₀ b)
    (hconj : ∀ a, θ₀ a = e₀₁.hom ≫ θ₁ a ≫ e₀₁.inv)
    (a₀₁₂ a₀₁₃ a₀₂₃ a₁₂₃ : A)
    (h₀₁₂ : θ₀ a₀₁₂ = e₀₁.hom ≫ e₁₂.hom ≫ e₀₂.inv)
    (h₀₁₃ : θ₀ a₀₁₃ = e₀₁.hom ≫ e₁₃.hom ≫ e₀₃.inv)
    (h₀₂₃ : θ₀ a₀₂₃ = e₀₂.hom ≫ e₂₃.hom ≫ e₀₃.inv)
    (h₁₂₃ : θ₁ a₁₂₃ = e₁₂.hom ≫ e₂₃.hom ≫ e₁₃.inv) :
    a₁₂₃ - a₀₂₃ + a₀₁₃ - a₀₁₂ = 0 := by
  have h : a₁₂₃ + a₀₁₃ = a₀₁₂ + a₀₂₃ := by
    apply hθ₀
    rw [hadd, hadd, hconj a₁₂₃, h₁₂₃, h₀₁₃, h₀₁₂, h₀₂₃]
    exact iso_defect_cocycle e₀₁ e₀₂ e₀₃ e₁₂ e₁₃ e₂₃
  rw [show a₁₂₃ - a₀₂₃ + a₀₁₃ - a₀₁₂ = (a₁₂₃ + a₀₁₃) - (a₀₁₂ + a₀₂₃) by abel, h, sub_self]

private lemma iso_cocycle_of_defect_eq_coboundary
    {D : Type*} [Category D] {A : Type*} [AddCommGroup A]
    {X₀ X₁ X₂ : D} (e₀₁ : X₀ ≅ X₁) (e₀₂ : X₀ ≅ X₂) (e₁₂ : X₁ ≅ X₂)
    (θ₀ : A → (X₀ ⟶ X₀)) (θ₁ : A → (X₁ ⟶ X₁))
    (hadd : ∀ a b, θ₀ (a + b) = θ₀ a ≫ θ₀ b)
    (hconj : ∀ a, θ₀ a ≫ e₀₁.hom = e₀₁.hom ≫ θ₁ a)
    (b₀₁ b₀₂ b₁₂ : A)
    (hdefect : θ₀ (b₀₁ + b₁₂ - b₀₂) = e₀₁.hom ≫ e₁₂.hom ≫ e₀₂.inv) :
    (θ₀ (-b₀₁) ≫ e₀₁.hom) ≫ (θ₁ (-b₁₂) ≫ e₁₂.hom) =
      θ₀ (-b₀₂) ≫ e₀₂.hom := by
  have hpair : e₀₁.hom ≫ e₁₂.hom = θ₀ (b₀₁ + b₁₂ - b₀₂) ≫ e₀₂.hom := by
    rw [hdefect]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    (θ₀ (-b₀₁) ≫ e₀₁.hom) ≫ (θ₁ (-b₁₂) ≫ e₁₂.hom) =
        θ₀ (-b₀₁) ≫ (e₀₁.hom ≫ θ₁ (-b₁₂)) ≫ e₁₂.hom := by
      simp only [Category.assoc]
    _ = θ₀ (-b₀₁) ≫ (θ₀ (-b₁₂) ≫ e₀₁.hom) ≫ e₁₂.hom := by
      rw [hconj]
    _ = (θ₀ (-b₀₁) ≫ θ₀ (-b₁₂)) ≫ (e₀₁.hom ≫ e₁₂.hom) := by
      simp only [Category.assoc]
    _ = θ₀ (-b₀₁ + -b₁₂) ≫ (θ₀ (b₀₁ + b₁₂ - b₀₂) ≫ e₀₂.hom) := by
      rw [← hadd, hpair]
    _ = θ₀ ((-b₀₁ + -b₁₂) + (b₀₁ + b₁₂ - b₀₂)) ≫ e₀₂.hom := by
      simp only [hadd, Category.assoc]
    _ = θ₀ (-b₀₂) ≫ e₀₂.hom := by
      congr 2
      abel

private theorem torsor_has_global_section_of_subsingleton_H1
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w'}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{w'})]
    (H : Sheaf J AddCommGrpCat.{w'}) (F : AbelianTorsor H)
    (hH1 : Subsingleton (Sheaf.H H 1)) :
    Nonempty (GlobalSections F.1.presheaf) :=
  (torsor_class_eq_trivial_iff H F).mp ((torsorIsoClassesEquivH1 H).injective (hH1.elim _ _))

private noncomputable def morPseudoTorsor
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    {J : GrothendieckTopology C} (p : S ⥤ C) [p.IsFibered]
    [∀ V : C, IsGroupoid (p.Fiber V)]
    {U : C} (a b : p.Fiber U)
    (H : Sheaf (J.over U) AddCommGrpCat.{max w' v₂})
    (hSheaf : p.IsMorSheaf J U a b)
    (θ : (abelianSheafAsGroupSheaf H).presheaf ≅
      p.morPresheaf a a ⋙ uliftFunctor.{w', v₂})
    (hθ : ∀ (V : (Over U)ᵒᵖ) (g h : H.obj.obj V),
      (θ.hom.app V (Multiplicative.ofAdd (g + h))).down =
      (θ.hom.app V (Multiplicative.ofAdd g)).down ≫
      (θ.hom.app V (Multiplicative.ofAdd h)).down) :
    PseudoTorsor (abelianSheafAsGroupSheaf H) where
  presheaf := p.morPresheaf a b ⋙ uliftFunctor.{w', v₂}
  isSheaf := Presheaf.isSheaf_comp_of_isSheaf _ _ _ hSheaf
  act V g s := ⟨(θ.hom.app V g).down ≫ s.down⟩
  one_act V s := by
    apply ULift.ext
    have he : (θ.hom.app V (Multiplicative.ofAdd (0 : H.obj.obj V))).down = 𝟙 _ := by
      have h := hθ V 0 0
      rw [zero_add] at h
      exact (cancel_epi _).mp (by simpa using h.symm)
    change (θ.hom.app V (Multiplicative.ofAdd (0 : H.obj.obj V))).down ≫ s.down = s.down
    rw [he, Category.id_comp]
  mul_act V g h s := by
    change Multiplicative (H.obj.obj V) at g h
    apply ULift.ext
    change (θ.hom.app V (Multiplicative.ofAdd (g.toAdd + h.toAdd))).down ≫ s.down = _
    rw [hθ, Category.assoc]
    rfl
  naturality f g s := by
    apply ULift.ext
    change Functor.morRestrict p a b f.unop ((θ.hom.app _ g).down ≫ s.down) = _
    rw [Functor.morRestrict_comp_hom]
    have h := congrArg (fun k => (k g).down) (θ.hom.naturality f)
    change (θ.hom.app _ ((abelianSheafAsGroupSheaf H).presheaf.map f g)).down =
      Functor.morRestrict p a a f.unop ((θ.hom.app _ g).down) at h
    rw [← h]
    rfl
  simplyTransitive V _ s r := by
    let α : Functor.pullbackFiber p a V.unop.hom ⟶ Functor.pullbackFiber p a V.unop.hom :=
      r.down ≫ inv s.down
    let g := θ.inv.app V (ULift.up α)
    have hg : (θ.hom.app V g).down = α :=
      congrArg (fun k => (k (ULift.up α)).down) (θ.inv_hom_id_app V)
    refine ⟨g, ?_, ?_⟩
    · apply ULift.ext
      change (θ.hom.app V g).down ≫ s.down = r.down
      rw [hg]
      dsimp [α]
      simp
    · intro h hh
      apply (CategoryTheory.injective_of_mono (θ.hom.app V))
      apply ULift.ext
      rw [hg]
      have hh' := congrArg ULift.down hh
      change (θ.hom.app V h).down ≫ s.down = r.down at hh'
      dsimp [α]
      rw [← hh']
      simp

private lemma locally_nonempty_morPresheaf
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    {J : GrothendieckTopology C} (p : S ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hlc : p.LocallyConnected J)
    {U : C} (a b : p.Fiber U) :
    haveI : p.IsFibered := hp.isFibered
    ∀ V : Over U, ∃ R ∈ (J.over U) V,
      ∀ ⦃W : Over U⦄ ⦃f : W ⟶ V⦄, R f →
        Nonempty ((p.morPresheaf a b ⋙ uliftFunctor.{w', v₂}).obj (op W)) := by
  let : p.IsFibered := hp.isFibered
  intro V
  let a' := p.pullbackFiber a V.hom
  let b' := p.pullbackFiber b V.hom
  obtain ⟨R, hR, hloc⟩ := hlc a'.1 b'.1 a'.2 b'.2
  refine ⟨(Sieve.overEquiv V).symm R, J.overEquiv_symm_mem_over V R hR, ?_⟩
  intro W f hf
  obtain ⟨x, y, ξ, υ, e, hξ, hυ, he⟩ := hloc f.left hf
  have := hξ
  have := hυ
  have hξc : p.IsStronglyCartesian f.left ξ := hp.isStronglyCartesian_homLift f.left ξ
  have hυc : p.IsStronglyCartesian f.left υ := hp.isStronglyCartesian_homLift f.left υ
  have hξcart : p.IsCartesian f.left ξ :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p f.left ξ
  have hυcart : p.IsCartesian f.left υ :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p f.left υ
  let i₁ : p.pullbackFiber a' f.left ≅
      (Functor.Fiber.mk (IsHomLift.domain_eq p f.left ξ) : p.Fiber W.left) :=
    Functor.fiberIsoOfCartesian f.left (Functor.IsPreFibered.pullbackMap a'.2 f.left) ξ
      (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) hξcart
  let i₂ : (Functor.Fiber.mk (IsHomLift.domain_eq p f.left υ) : p.Fiber W.left) ≅
      p.pullbackFiber b' f.left :=
    Functor.fiberIsoOfCartesian f.left υ (Functor.IsPreFibered.pullbackMap b'.2 f.left)
      hυcart (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
  let e' : (Functor.Fiber.mk (IsHomLift.domain_eq p f.left ξ) : p.Fiber W.left) ≅
      (Functor.Fiber.mk (IsHomLift.domain_eq p f.left υ) : p.Fiber W.left) :=
    Functor.Fiber.isoMk e he
  let i : p.pullbackFiber a (f.left ≫ V.hom) ≅ p.pullbackFiber b (f.left ≫ V.hom) :=
    (Functor.pullbackFiberCompIso a V.hom f.left).symm ≪≫ i₁ ≪≫ e' ≪≫ i₂ ≪≫
      Functor.pullbackFiberCompIso b V.hom f.left
  rw [Over.w f] at i
  exact ⟨ULift.up i.hom⟩

private theorem nonempty_fiberIso_of_subsingleton_H1
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
    {J : GrothendieckTopology C} (p : S ⥤ C) [p.IsFibered]
    [∀ V : C, IsGroupoid (p.Fiber V)]
    (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J) (hlc : p.LocallyConnected J)
    {U : C} (a b : p.Fiber U)
    [HasSheafify (J.over U) AddCommGrpCat.{max w' v₂}]
    [HasExt.{x} (Sheaf (J.over U) AddCommGrpCat.{max w' v₂})]
    (H : Sheaf (J.over U) AddCommGrpCat.{max w' v₂})
    (θ : (abelianSheafAsGroupSheaf H).presheaf ≅
      p.morPresheaf a a ⋙ uliftFunctor.{w', v₂})
    (hθ : ∀ (V : (Over U)ᵒᵖ) (g h : H.obj.obj V),
      (θ.hom.app V (Multiplicative.ofAdd (g + h))).down =
      (θ.hom.app V (Multiplicative.ofAdd g)).down ≫
      (θ.hom.app V (Multiplicative.ofAdd h)).down)
    (hH1 : Subsingleton (Sheaf.H H 1)) : Nonempty (a ≅ b) := by
  let F := morPseudoTorsor p a b H (hst.isMorSheaf U a b) θ hθ
  have hF : F.IsTorsor := locally_nonempty_morPresheaf p hp hlc a b
  obtain ⟨s⟩ := torsor_has_global_section_of_subsingleton_H1 H ⟨F, hF⟩ hH1
  let V : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let m : p.pullbackFiber a (𝟙 U) ⟶ p.pullbackFiber b (𝟙 U) :=
    (s.app V (termIso.inv.app V PUnit.unit)).down
  exact ⟨(Functor.pullbackFiberIdIso a).symm ≪≫ asIso m ≪≫ Functor.pullbackFiberIdIso b⟩

noncomputable section

universe v u

attribute [local implicit_reducible] AddCommGrpCat.free FunctorToTypes.prod
private def pairBoundary {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w) :
    freeAbelianPresheaf (FunctorToTypes.prod P P) ⟶
      freeAbelianPresheaf P :=
  Functor.whiskerRight FunctorToTypes.prod.snd AddCommGrpCat.free -
    Functor.whiskerRight FunctorToTypes.prod.fst AddCommGrpCat.free

private lemma pairBoundary_of {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w)
    (V : Cᵒᵖ) (a b : P.obj V) :
    ((pairBoundary P).app V).hom (FreeAbelianGroup.of (a, b)) =
      FreeAbelianGroup.of b - FreeAbelianGroup.of a := by
  show FreeAbelianGroup.map _root_.Prod.snd (FreeAbelianGroup.of (a, b)) -
    FreeAbelianGroup.map _root_.Prod.fst (FreeAbelianGroup.of (a, b)) = _
  simp

private lemma pairBoundary_augmentation {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) :
    pairBoundary P ≫ freeAbelianPresheafAugmentation P = 0 := by
  ext V : 2
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  rintro ⟨a, b⟩
  show ((freeAbelianPresheafAugmentation P).app V).hom
    (((pairBoundary P).app V).hom (FreeAbelianGroup.of (a, b))) = 0
  rw [pairBoundary_of]
  show (FreeAbelianGroup.lift (fun _ : P.obj V => (⟨1⟩ : ULift.{w} ℤ)))
    (FreeAbelianGroup.of b - FreeAbelianGroup.of a) = 0
  simp

private def pairBoundaryToKernel {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) :
    freeAbelianPresheaf (FunctorToTypes.prod P P) ⟶
      freeAbelianPresheafAugmentationKernel P :=
  kernel.lift _ (pairBoundary P) (pairBoundary_augmentation P)

/-- Composing `pairBoundaryToKernel` with the kernel inclusion recovers `pairBoundary`. -/
private lemma kernel_ι_pairBoundaryToKernel_apply {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) (V : Cᵒᵖ) (x : (freeAbelianPresheaf (FunctorToTypes.prod P P)).obj V) :
    ((kernel.ι (freeAbelianPresheafAugmentation P)).app V).hom
      (((pairBoundaryToKernel P).app V).hom x) = ((pairBoundary P).app V).hom x :=
  ConcreteCategory.congr_hom (congrArg (fun k => k.app V) (kernel.lift_ι
    (freeAbelianPresheafAugmentation P) (pairBoundary P) (pairBoundary_augmentation P))) x

private lemma pairBoundaryToKernel_surjective {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) (V : Cᵒᵖ) :
    Function.Surjective ((pairBoundaryToKernel P).app V) := by
  classical
  let ι := (kernel.ι (freeAbelianPresheafAugmentation P)).app V
  have hinj : Function.Injective ι := (AddCommGrpCat.mono_iff_injective ι).mp inferInstance
  intro z
  have hz : ((freeAbelianPresheafAugmentation P).app V).hom (ι.hom z) = 0 :=
    ConcreteCategory.congr_hom
      (congrArg (fun k => k.app V) (kernel.condition (freeAbelianPresheafAugmentation P))) z
  by_cases hp : Nonempty (P.obj V)
  · let a := Classical.choice hp
    let t : FreeAbelianGroup (P.obj V) →+
        FreeAbelianGroup (P.obj V × P.obj V) :=
      FreeAbelianGroup.lift (fun b => FreeAbelianGroup.of (a, b))
    refine ⟨t (ι.hom z), hinj ?_⟩
    have hcomp : ((pairBoundary P).app V).hom (t (ι.hom z)) = ι.hom z := by
      have h : ∀ q : FreeAbelianGroup (P.obj V),
          (FreeAbelianGroup.lift (fun t : P.obj V × P.obj V =>
            FreeAbelianGroup.of t.2 - FreeAbelianGroup.of t.1)) (t q) = q -
            ((FreeAbelianGroup.lift (fun _ : P.obj V =>
              (⟨1⟩ : ULift.{w} ℤ))) q).down • FreeAbelianGroup.of a := by
        intro q
        induction q using FreeAbelianGroup.induction_on with
        | zero => simp
        | of b => simp [t]
        | neg b ih => simpa [map_neg, sub_eq_add_neg, add_comm] using congrArg Neg.neg ih
        | add q r hq hr =>
          simp only [map_add, ULift.add_down, add_zsmul, hq, hr]
          abel
      have hmap : ((pairBoundary P).app V).hom =
          FreeAbelianGroup.lift (fun t : P.obj V × P.obj V =>
            FreeAbelianGroup.of t.2 - FreeAbelianGroup.of t.1) := by
        apply FreeAbelianGroup.lift_ext
        rintro ⟨b, c⟩
        exact (pairBoundary_of P V b c).trans (FreeAbelianGroup.lift_apply_of _ _).symm
      rw [hmap]
      have hz' : (FreeAbelianGroup.lift (fun _ : P.obj V =>
          (⟨1⟩ : ULift.{w} ℤ))) (ι.hom z) = 0 := hz
      exact (h (ι.hom z)).trans (by rw [hz']; simp)
    exact (kernel_ι_pairBoundaryToKernel_apply P V _).trans hcomp
  · have : IsEmpty (P.obj V) := ⟨fun a => hp ⟨a⟩⟩
    refine ⟨0, hinj ?_⟩
    have : Subsingleton ((freeAbelianPresheaf P).obj V) := by
      show Subsingleton (FreeAbelianGroup (P.obj V))
      infer_instance
    simpa only [map_zero] using (Subsingleton.elim 0 (ι.hom z))

private lemma cocycleEvaluation_change_base {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) {A : Type*} [AddCommGroup A] (V : Cᵒᵖ)
    (z : P.obj V → P.obj V → P.obj V → A)
    (hz : ∀ a b c d, z b c d - z a c d + z a b d - z a b c = 0)
    (a b : P.obj V) (q : FreeAbelianGroup (P.obj V × P.obj V)) :
    FreeAbelianGroup.lift (fun t => z b t.1 t.2) q -
        FreeAbelianGroup.lift (fun t => z a t.1 t.2) q =
      FreeAbelianGroup.lift (fun c => -z a b c) (((pairBoundary P).app V).hom q) := by
  have h : (FreeAbelianGroup.lift (fun t => z b t.1 t.2) -
        FreeAbelianGroup.lift (fun t => z a t.1 t.2)) =
      (FreeAbelianGroup.lift (fun c => -z a b c)).comp ((pairBoundary P).app V).hom := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨c, d⟩
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
      FreeAbelianGroup.lift_apply_of]
    rw [pairBoundary_of]
    simp only [map_sub, FreeAbelianGroup.lift_apply_of]
    apply sub_eq_zero.mp
    calc
      _ = z b c d - z a c d + z a b d - z a b c := by abel
      _ = 0 := hz a b c d
  exact DFunLike.congr_fun h q

private def pairKernelCocycleAt {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) (G : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (z : ∀ V, P.obj V → P.obj V → P.obj V → G.obj V) (V : Cᵒᵖ) :
    (kernel (pairBoundaryToKernel P)).obj V →+ G.obj V := by
  classical
  exact if h : Nonempty (P.obj V) then
    (FreeAbelianGroup.lift (fun t => z V (Classical.choice h) t.1 t.2)).comp
      ((kernel.ι (pairBoundaryToKernel P)).app V).hom
  else 0

private lemma pairKernelCocycleAt_eq {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) (G : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (z : ∀ V, P.obj V → P.obj V → P.obj V → G.obj V)
    (hz : ∀ V a b c d, z V b c d - z V a c d + z V a b d - z V a b c = 0)
    (V : Cᵒᵖ) (a : P.obj V) (q : (kernel (pairBoundaryToKernel P)).obj V) :
    pairKernelCocycleAt P G z V q =
      FreeAbelianGroup.lift (fun t => z V a t.1 t.2)
        (((kernel.ι (pairBoundaryToKernel P)).app V).hom q) := by
  classical
  have hδ : ((pairBoundary P).app V).hom
      (((kernel.ι (pairBoundaryToKernel P)).app V).hom q) = 0 := by
    have h : kernel.ι (pairBoundaryToKernel P) ≫ pairBoundary P = 0 := by
      calc
        _ = (kernel.ι (pairBoundaryToKernel P) ≫ pairBoundaryToKernel P) ≫
            kernel.ι (freeAbelianPresheafAugmentation P) := by
          simp only [pairBoundaryToKernel, Category.assoc, kernel.lift_ι]
        _ = 0 := by rw [kernel.condition, zero_comp]
    exact ConcreteCategory.congr_hom (congrArg (fun k => k.app V) h) q
  simp only [pairKernelCocycleAt, dif_pos (show Nonempty (P.obj V) from ⟨a⟩),
    AddMonoidHom.comp_apply]
  exact sub_eq_zero.mp ((cocycleEvaluation_change_base P V (z V) (hz V) a
    (Classical.choice (show Nonempty (P.obj V) from ⟨a⟩)) _).trans
      ((congrArg (FreeAbelianGroup.lift _) hδ).trans (map_zero _)))

private lemma pairKernelCocycleAt_naturality {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) (G : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (z : ∀ V, P.obj V → P.obj V → P.obj V → G.obj V)
    (hz : ∀ V a b c d, z V b c d - z V a c d + z V a b d - z V a b c = 0)
    (hn : ∀ {V W} (f : V ⟶ W) a b c,
      z W (P.map f a) (P.map f b) (P.map f c) = G.map f (z V a b c))
    {V W : Cᵒᵖ} (f : V ⟶ W) (q : (kernel (pairBoundaryToKernel P)).obj V) :
    pairKernelCocycleAt P G z W ((kernel (pairBoundaryToKernel P)).map f q) =
      G.map f (pairKernelCocycleAt P G z V q) := by
  classical
  let ι := kernel.ι (pairBoundaryToKernel P)
  have hnat := NatTrans.naturality_apply ι f q
  by_cases hp : Nonempty (P.obj V)
  · let a := Classical.choice hp
    rw [pairKernelCocycleAt_eq P G z hz W (P.map f a),
      pairKernelCocycleAt_eq P G z hz V a, hnat]
    have h : (FreeAbelianGroup.lift (fun t => z W (P.map f a) t.1 t.2)).comp
        ((freeAbelianPresheaf (FunctorToTypes.prod P P)).map f).hom =
      (G.map f).hom.comp (FreeAbelianGroup.lift (fun t => z V a t.1 t.2)) := by
      apply FreeAbelianGroup.lift_ext
      rintro ⟨b, c⟩
      simpa [freeAbelianPresheaf, AddCommGrpCat.free] using hn f a b c
    exact DFunLike.congr_fun h (ι.app V q)
  · have : IsEmpty (P.obj V) := ⟨fun a => hp ⟨a⟩⟩
    have : Subsingleton ((freeAbelianPresheaf
        (FunctorToTypes.prod P P)).obj V) := by
      show Subsingleton (FreeAbelianGroup (P.obj V × P.obj V))
      infer_instance
    have hq : q = 0 :=
      (AddCommGrpCat.mono_iff_injective (ι.app V)).mp inferInstance
        (Subsingleton.elim _ _)
    simp [hq]

private def pairKernelCocycle {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) (G : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (z : ∀ V, P.obj V → P.obj V → P.obj V → G.obj V)
    (hz : ∀ V a b c d, z V b c d - z V a c d + z V a b d - z V a b c = 0)
    (hn : ∀ {V W} (f : V ⟶ W) a b c,
      z W (P.map f a) (P.map f b) (P.map f c) = G.map f (z V a b c)) :
    kernel (pairBoundaryToKernel P) ⟶ G where
  app V := AddCommGrpCat.ofHom (pairKernelCocycleAt P G z V)
  naturality V W f := by
    ext q
    exact pairKernelCocycleAt_naturality P G z hz hn f q

private lemma subsingleton_ext_kernel_of_ext_vanishing
    {A : Type*} [Category A] [Abelian A] [HasExt.{x} A]
    (S : ShortComplex A) (hS : S.ShortExact) (G : A) (n : ℕ)
    (h₀ : Subsingleton (Abelian.Ext S.X₂ G n))
    (h₁ : Subsingleton (Abelian.Ext S.X₃ G (n + 1))) :
    Subsingleton (Abelian.Ext S.X₁ G n) := by
  apply subsingleton_of_forall_eq 0
  intro z
  obtain ⟨b, hb⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS G z
    (Nat.add_comm 1 n) (h₁.elim _ _)
  rw [h₀.elim b 0, Abelian.Ext.comp_zero] at hb
  exact hb.symm

private lemma exists_extension_of_ext_one_vanishing
    {A : Type*} [Category A] [Abelian A] [HasExt.{x} A]
    (S : ShortComplex A) (hS : S.ShortExact) (G : A)
    (h : Subsingleton (Abelian.Ext S.X₃ G 1)) (z : S.X₁ ⟶ G) :
    ∃ b : S.X₂ ⟶ G, S.f ≫ b = z := by
  obtain ⟨b, hb⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS G
    (Abelian.Ext.mk₀ z) (add_zero 1) (h.elim _ _)
  refine ⟨Abelian.Ext.homEquiv₀ b, ?_⟩
  apply (Abelian.Ext.mk₀_bijective _ _).injective
  rwa [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_homEquiv₀_apply]

@[implicit_reducible] private def pairBoundaryComplex {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  ShortComplex.mk (kernel.ι (pairBoundaryToKernel P)) (pairBoundaryToKernel P)
    (kernel.condition _)

private lemma pairBoundaryComplex_shortExact {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) : (pairBoundaryComplex P).ShortExact := by
  have : ∀ V, Epi ((pairBoundaryToKernel P).app V) := fun V =>
    (AddCommGrpCat.epi_iff_surjective _).mpr (pairBoundaryToKernel_surjective P V)
  have : Epi (pairBoundaryToKernel P) := NatTrans.epi_of_epi_app _
  have : Mono (pairBoundaryComplex P).f := by
    show Mono (kernel.ι (pairBoundaryToKernel P))
    infer_instance
  have : Epi (pairBoundaryComplex P).g := by
    show Epi (pairBoundaryToKernel P)
    infer_instance
  exact ⟨ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)⟩

private lemma freeAbelianAugmentation_shortExact {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{w})]
    (P : Cᵒᵖ ⥤ Type w)
    (hloc : ∀ V : C, ∃ R ∈ J V, ∀ ⦃W : C⦄ (f : W ⟶ V), R f →
      Nonempty (P.obj (op W))) :
    ((freeAbelianPresheafAugmentationComplex P).map
      (presheafToSheaf J AddCommGrpCat.{w})).ShortExact := by
  let S := freeAbelianPresheafAugmentationComplex P
  have : Mono S.f := by
    dsimp [S, freeAbelianPresheafAugmentationComplex]
    infer_instance
  have : Presheaf.IsLocallySurjective J (freeAbelianPresheafAugmentation P) := by
    constructor
    intro U y
    obtain ⟨R, hR, hP⟩ := hloc U
    apply J.superset_covering (S := R) ?_ hR
    intro V f hf
    obtain ⟨a⟩ := hP f hf
    refine ⟨y.down • FreeAbelianGroup.of a, ?_⟩
    show (FreeAbelianGroup.lift (fun _ : P.obj (op V) =>
      (⟨1⟩ : ULift.{w} ℤ))) (y.down • FreeAbelianGroup.of a) = y
    rw [map_zsmul, FreeAbelianGroup.lift_apply_of]
    obtain ⟨n⟩ := y
    exact ULift.ext _ _ (mul_one n)
  have : Epi ((S.map (presheafToSheaf J AddCommGrpCat.{w})).g) :=
    sheafify_map_epi_of_locallySurjective
      (freeAbelianPresheafAugmentation P)
  have : Mono ((S.map (presheafToSheaf J AddCommGrpCat.{w})).f) := by
    show Mono ((presheafToSheaf J AddCommGrpCat.{w}).map S.f)
    infer_instance
  exact ⟨(freeAbelianPresheafAugmentationComplex_exact P).map_of_mono_of_preservesKernel
    (presheafToSheaf J AddCommGrpCat.{w}) (by infer_instance) (by infer_instance)⟩

private lemma pairBoundary_triangle {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) (V : Cᵒᵖ) (a b c : P.obj V) :
    ((pairBoundaryToKernel P).app V).hom
      (FreeAbelianGroup.of (b, c) - FreeAbelianGroup.of (a, c) +
        FreeAbelianGroup.of (a, b)) = 0 := by
  let ι := (kernel.ι (freeAbelianPresheafAugmentation P)).app V
  apply (AddCommGrpCat.mono_iff_injective ι).mp inferInstance
  rw [map_zero]
  refine (kernel_ι_pairBoundaryToKernel_apply P V _).trans ?_
  rw [map_add, map_sub, pairBoundary_of, pairBoundary_of, pairBoundary_of]
  abel

private lemma pairKernelCocycle_triangle {C : Type u} [Category.{v} C]
    (P : Cᵒᵖ ⥤ Type w) (G : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (z : ∀ V, P.obj V → P.obj V → P.obj V → G.obj V)
    (hz : ∀ V a b c d, z V b c d - z V a c d + z V a b d - z V a b c = 0)
    (V : Cᵒᵖ) (a b c : P.obj V) (q : (kernel (pairBoundaryToKernel P)).obj V)
    (hq : ((kernel.ι (pairBoundaryToKernel P)).app V).hom q =
      FreeAbelianGroup.of (b, c) - FreeAbelianGroup.of (a, c) +
        FreeAbelianGroup.of (a, b)) :
    pairKernelCocycleAt P G z V q = z V a b c := by
  rw [pairKernelCocycleAt_eq P G z hz V a q, hq]
  simp only [map_add, map_sub, FreeAbelianGroup.lift_apply_of]
  have h' : z V a a c = z V a a b :=
    sub_eq_zero.mp (by simpa only [sub_self, zero_add] using hz V a a b c)
  rw [h']
  abel

private lemma exists_pair_cochain_of_ext_vanishing
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{x} (Sheaf J AddCommGrpCat.{w})]
    (P : Cᵒᵖ ⥤ Type w) (G : Sheaf J AddCommGrpCat.{w})
    (hloc : ∀ V : C, ∃ R ∈ J V, ∀ ⦃W : C⦄ (f : W ⟶ V), R f →
      Nonempty (P.obj (op W)))
    (hH1 : Subsingleton (Abelian.Ext (freeAbelianSheafOnPresheaf P) G 1))
    (hH2 : Subsingleton (Sheaf.H G 2))
    (z : ∀ V, P.obj V → P.obj V → P.obj V → G.obj.obj V)
    (hz : ∀ V a b c d, z V b c d - z V a c d + z V a b d - z V a b c = 0)
    (hn : ∀ {V W} (f : V ⟶ W) a b c,
      z W (P.map f a) (P.map f b) (P.map f c) = G.obj.map f (z V a b c)) :
    ∃ b : ∀ V, P.obj V → P.obj V → G.obj.obj V,
      (∀ {V W} (f : V ⟶ W) a c,
        b W (P.map f a) (P.map f c) = G.obj.map f (b V a c)) ∧
      (∀ V a c d, b V c d - b V a d + b V a c = z V a c d) := by
  let L := presheafToSheaf J AddCommGrpCat.{w}
  let S₀ := (freeAbelianPresheafAugmentationComplex P).map L
  let S₁ := (pairBoundaryComplex P).map L
  have hS₀ : S₀.ShortExact := freeAbelianAugmentation_shortExact J P hloc
  have hS₁ : S₁.ShortExact := (pairBoundaryComplex_shortExact P).map_of_exact L
  have hK : Subsingleton (Abelian.Ext S₁.X₃ G 1) :=
    subsingleton_ext_kernel_of_ext_vanishing S₀ hS₀ G 1 hH1 hH2
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  let z' : S₁.X₁ ⟶ G := (adj.homEquiv _ _).symm (pairKernelCocycle P G.obj z hz hn)
  obtain ⟨b', hb'⟩ := exists_extension_of_ext_one_vanishing S₁ hS₁ G hK z'
  let b := adj.homEquiv _ _ b'
  have hb : kernel.ι (pairBoundaryToKernel P) ≫ b = pairKernelCocycle P G.obj z hz hn := by
    have h := adj.homEquiv_naturality_left (kernel.ι (pairBoundaryToKernel P)) b'
    change adj.homEquiv _ _ (S₁.f ≫ b') = kernel.ι (pairBoundaryToKernel P) ≫ b at h
    rw [hb'] at h
    exact h.symm.trans ((adj.homEquiv _ _).apply_symm_apply _)
  refine ⟨fun V a c => (b.app V).hom (FreeAbelianGroup.of (a, c)), ?_, ?_⟩
  · intro V W f a c
    have h := NatTrans.naturality_apply b f (FreeAbelianGroup.of (a, c))
    change (b.app W).hom
      (FreeAbelianGroup.map (fun t : P.obj V × P.obj V =>
        (P.map f t.1, P.map f t.2)) (FreeAbelianGroup.of (a, c))) = _ at h
    exact (congrArg (fun t : FreeAbelianGroup (P.obj W × P.obj W) => (b.app W).hom t)
      (FreeAbelianGroup.map_of (fun t : P.obj V × P.obj V =>
        (P.map f t.1, P.map f t.2)) (a, c))).symm.trans h
  · intro V a c d
    let t : FreeAbelianGroup (P.obj V × P.obj V) :=
      FreeAbelianGroup.of (c, d) - FreeAbelianGroup.of (a, d) + FreeAbelianGroup.of (a, c)
    have hT := (pairBoundaryComplex_shortExact P).map_of_exact
      ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj V)
    obtain ⟨q, hq⟩ := (ShortComplex.ab_exact_iff _).mp hT.exact t
      (pairBoundary_triangle P V a c d)
    change ((kernel.ι (pairBoundaryToKernel P)).app V).hom q = t at hq
    have he := ConcreteCategory.congr_hom (congrArg (fun k => k.app V) hb) q
    change (b.app V).hom (((kernel.ι (pairBoundaryToKernel P)).app V).hom q) =
      pairKernelCocycleAt P G.obj z V q at he
    have hzq := pairKernelCocycle_triangle P G.obj z hz V a c d q hq
    rw [hq, hzq] at he
    simpa only [t, map_add, map_sub] using he

attribute [local implicit_reducible] FormalCoproduct.incl

private abbrev familyPresheaf {C : Type u} [Category.{v} C] {ι : Type w} (X : ι → C) :
    Cᵒᵖ ⥤ Type (max w v) :=
  (FormalCoproduct.incl C).op ⋙ yoneda.obj (FormalCoproduct.mk ι X)

private lemma familyPresheaf_map_fromIncl {C : Type u} [Category.{v} C]
    {ι : Type w} (X : ι → C) {V W : Cᵒᵖ} (f : V ⟶ W) (i : ι) (g : V.unop ⟶ X i) :
    (familyPresheaf X).map f (FormalCoproduct.Hom.fromIncl i g) =
      FormalCoproduct.Hom.fromIncl i (f.unop ≫ g) := rfl

private lemma freeAbelianFamily_lift {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{max w v})]
    {ι : Type w} (X : ι → C) {I Q : Sheaf J AddCommGrpCat.{max w v}} (g : I ⟶ Q)
    (q : freeAbelianSheafOnPresheaf (familyPresheaf X) ⟶ Q)
    (h : ∀ i : ι, Function.Surjective (g.hom.app (op (X i)))) :
    ∃ b : freeAbelianSheafOnPresheaf (familyPresheaf X) ⟶ I, b ≫ g = q := by
  classical
  let P := familyPresheaf X
  let adj := sheafificationAdjunction J AddCommGrpCat.{max w v}
  let q₀ := adj.homEquiv _ _ q
  let a (i : ι) : Q.obj.obj (op (X i)) :=
    (q₀.app (op (X i))).hom (FreeAbelianGroup.of (FormalCoproduct.Hom.fromIncl i (𝟙 _)))
  choose t ht using fun i => h i (a i)
  let j : P ⟶ I.obj ⋙ forget AddCommGrpCat :=
    { app V := ↾fun s => I.obj.map (s.φ PUnit.unit).op (t (s.f PUnit.unit))
      naturality := by
        intro V W f
        ext s
        show I.obj.map (f.unop ≫ s.φ PUnit.unit).op (t (s.f PUnit.unit)) =
          I.obj.map f (I.obj.map (s.φ PUnit.unit).op (t (s.f PUnit.unit)))
        rw [op_comp, I.obj.map_comp]
        rfl }
  let b₀ := freeAbelianPresheafLift P I.obj j
  refine ⟨(adj.homEquiv _ _).symm b₀, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, (adj.homEquiv _ _).apply_symm_apply]
  show b₀ ≫ g.hom = q₀
  ext V : 2
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro s
  have hq := NatTrans.naturality_apply q₀ (s.φ PUnit.unit).op
    (FreeAbelianGroup.of (FormalCoproduct.Hom.fromIncl (s.f PUnit.unit) (𝟙 _)))
  change (q₀.app V).hom
      (FreeAbelianGroup.map ((P.map (s.φ PUnit.unit).op))
        (FreeAbelianGroup.of (FormalCoproduct.Hom.fromIncl (s.f PUnit.unit) (𝟙 _)))) =
    Q.obj.map (s.φ PUnit.unit).op (a (s.f PUnit.unit)) at hq
  have hs : P.map (s.φ PUnit.unit).op
      (FormalCoproduct.Hom.fromIncl (s.f PUnit.unit) (𝟙 _)) = s := by
    rw [familyPresheaf_map_fromIncl, Category.comp_id]
    exact FormalCoproduct.Hom.fromIncl_asSigma s
  have hq' : (q₀.app V).hom (FreeAbelianGroup.of s) =
      Q.obj.map (s.φ PUnit.unit).op (a (s.f PUnit.unit)) := by
    rw [FreeAbelianGroup.map_of_apply] at hq
    exact (congrArg (fun t => (q₀.app V).hom (FreeAbelianGroup.of t)) hs).symm.trans hq
  show (g.hom.app V).hom (FreeAbelianGroup.lift (j.app V) (FreeAbelianGroup.of s)) = _
  rw [FreeAbelianGroup.lift_apply_of]
  show (g.hom.app V).hom (I.obj.map (s.φ PUnit.unit).op (t (s.f PUnit.unit))) = _
  exact ((NatTrans.naturality_apply g.hom (s.φ PUnit.unit).op
    (t (s.f PUnit.unit))).trans (congrArg _ (ht _))).trans hq'.symm

private lemma ext_one_freeAbelianFamily_vanishes {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{max w v})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max w v})]
    {ι : Type w} (X : ι → C) (G : Sheaf J AddCommGrpCat.{max w v})
    (h : ∀ (S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})), S.ShortExact →
      S.X₁ = G → ∀ i : ι, Function.Surjective (S.g.hom.app (op (X i)))) :
    Subsingleton (Abelian.Ext (freeAbelianSheafOnPresheaf (familyPresheaf X)) G 1) := by
  apply subsingleton_of_forall_eq 0
  intro z
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι G))
  have hS : S.ShortExact := ⟨ShortComplex.exact_cokernel (Injective.ι G)⟩
  obtain ⟨q, hq⟩ := ext_one_boundary_surjective S hS _ z
  obtain ⟨b, hb⟩ := freeAbelianFamily_lift J X S.g q (h S hS rfl)
  exact hq.symm.trans ((ext_one_boundary_eq_zero_iff_lift S hS _ q).mpr ⟨b, hb⟩)

private lemma sections_surjective_of_H1_vanishing
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{x} (Sheaf J AddCommGrpCat.{w})]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    {T : C} (hT : IsTerminal T) (hH1 : Subsingleton (Sheaf.H S.X₁ 1)) :
    Function.Surjective (S.g.hom.app (op T)) := by
  intro a
  let z := (Sheaf.H.equiv₀ S.X₃ hT).symm a
  obtain ⟨b, hb⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hS z (zero_add 1)
    (hH1.elim _ _)
  refine ⟨Sheaf.H.equiv₀ S.X₂ hT b, ?_⟩
  rw [Sheaf.H.equiv₀_naturality]
  show Sheaf.H.equiv₀ S.X₃ hT (b.comp (Abelian.Ext.mk₀ S.g) (add_zero 0)) = a
  rw [hb]
  exact (Sheaf.H.equiv₀ S.X₃ hT).apply_symm_apply a

private lemma overMap_sections_surjective_of_H1_vanishing
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U V : C} (f : V ⟶ U)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v w}]
    [HasSheafify (J.over V) AddCommGrpCat.{max u v w}]
    [HasExt.{x} (Sheaf (J.over V) AddCommGrpCat.{max u v w})]
    (S : ShortComplex (Sheaf (J.over U) AddCommGrpCat.{max u v w})) (hS : S.ShortExact)
    (hH1 : Subsingleton (Sheaf.H ((J.overMapPullback AddCommGrpCat.{max u v w} f).obj S.X₁) 1)) :
    Function.Surjective (S.g.hom.app (op (Over.mk f))) := by
  let L := J.overMapPullback AddCommGrpCat.{max u v w} f
  have : L.Additive := ⟨rfl⟩
  have h := sections_surjective_of_H1_vanishing (S.map L) (hS.map_of_exact L)
    (Over.mkIdTerminal (X := V)) hH1
  change Function.Surjective (S.g.hom.app (op (Over.mk ((𝟙 V) ≫ f)))) at h
  exact Category.id_comp f ▸ h

private lemma ext_one_coverFamily_vanishes
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U : C}
    (E : PreZeroHypercover.{max u v w} U)
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{max u v w}]
    [∀ V : C, HasExt.{x} (Sheaf (J.over V) AddCommGrpCat.{max u v w})]
    (G : Sheaf J AddCommGrpCat.{max u v w})
    (hH1 : ∀ i : E.I₀, Subsingleton (Sheaf.H (G.over (E.X i)) 1)) :
    Subsingleton (Abelian.Ext (freeAbelianSheafOnPresheaf
      (familyPresheaf (fun i => Over.mk (E.f i)))) (G.over U) 1) := by
  let : IsGrothendieckAbelian.{max u v w} (Sheaf (J.over U) AddCommGrpCat.{max u v w}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall (J.over U) AddCommGrpCat.{max u v w}
  let : EnoughInjectives (Sheaf (J.over U) AddCommGrpCat.{max u v w}) :=
    IsGrothendieckAbelian.enoughInjectives
  apply ext_one_freeAbelianFamily_vanishes (J.over U) (fun i => Over.mk (E.f i)) (G.over U)
  intro S hS h i
  apply overMap_sections_surjective_of_H1_vanishing J (E.f i) S hS
  rw [h]
  exact hH1 i

private lemma familyPresheaf_locally_nonempty
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U : C}
    (E : PreZeroHypercover.{w} U) (hE : E.sieve₀ ∈ J U) :
    ∀ V : Over U, ∃ R ∈ (J.over U) V, ∀ ⦃W : Over U⦄ (f : W ⟶ V), R f →
      Nonempty ((familyPresheaf (fun i => Over.mk (E.f i))).obj (op W)) := by
  intro V
  refine ⟨(Sieve.overEquiv V).symm (E.sieve₀.pullback V.hom),
    J.overEquiv_symm_mem_over V _ (J.pullback_stable V.hom hE), fun W f hf => ?_⟩
  change E.sieve₀ (f.left ≫ V.hom) at hf
  rw [Over.w f] at hf
  obtain ⟨Z, g, _, ⟨i⟩, hg⟩ := hf
  exact ⟨FormalCoproduct.Hom.fromIncl i (Over.homMk g hg)⟩

private def coveringPullback {C : Type u} [Category.{v} C] {U : C}
    (E : PreZeroHypercover.{w} U) [∀ i j : E.I₀, HasPullback (E.f i) (E.f j)]
    (i j : E.I₀) : ChosenPullback (E.f i) (E.f j) where
  pullback := pullback (E.f i) (E.f j)
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  condition := pullback.condition
  isLimit := (IsPullback.of_hasPullback _ _).isLimit

private abbrev familyObject {C : Type u} {S : Type u₂} [Category.{v} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {U : C} (E : PreZeroHypercover.{w} U)
    (x : ∀ i : E.I₀, p.Fiber (E.X i)) {V : Over U}
    (a : (familyPresheaf (fun i => Over.mk (E.f i))).obj (op V)) : p.Fiber V.left :=
  p.pullbackFiber (x (a.f PUnit.unit)) (a.φ PUnit.unit).left

private def familyOverlap {C : Type u} {S : Type u₂} [Category.{v} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {U : C} (E : PreZeroHypercover.{w} U)
    [∀ i j : E.I₀, HasPullback (E.f i) (E.f j)]
    (x : ∀ i : E.I₀, p.Fiber (E.X i))
    (φ : ∀ i j, p.pullbackFiber (x i) (pullback.fst (E.f i) (E.f j)) ⟶
      p.pullbackFiber (x j) (pullback.snd (E.f i) (E.f j)))
    {V : Over U} (a b : (familyPresheaf (fun i => Over.mk (E.f i))).obj (op V)) :
    familyObject p E x a ⟶ familyObject p E x b :=
  Pseudofunctor.DescentData'.pullHom' (F := Functor.IsFibered.pullbackPseudofunctor p)
    (sq := coveringPullback E) φ V.hom (a.φ PUnit.unit).left (b.φ PUnit.unit).left
      (Over.w _) (Over.w _)

private lemma familyOverlap_map
    {C : Type u} {S : Type u₂} [Category.{v} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] {U : C} (E : PreZeroHypercover.{w} U)
    [∀ i j : E.I₀, HasPullback (E.f i) (E.f j)]
    (x : ∀ i : E.I₀, p.Fiber (E.X i))
    (φ : ∀ i j, p.pullbackFiber (x i) (pullback.fst (E.f i) (E.f j)) ⟶
      p.pullbackFiber (x j) (pullback.snd (E.f i) (E.f j)))
    {V W : Over U} (f : W ⟶ V)
    (a b : (familyPresheaf (fun i => Over.mk (E.f i))).obj (op V)) :
    familyOverlap p E x φ ((familyPresheaf _).map f.op a) ((familyPresheaf _).map f.op b) =
      (Functor.pullbackFiberCompIso (x (a.f PUnit.unit)) (a.φ PUnit.unit).left f.left).inv ≫
        Functor.pullbackFiberHom (familyOverlap p E x φ a b) f.left ≫
        (Functor.pullbackFiberCompIso (x (b.f PUnit.unit)) (b.φ PUnit.unit).left f.left).hom := by
  rw [← Functor.pullHom_eq]
  exact (Pseudofunctor.DescentData'.pullHom_pullHom'
    (F := Functor.IsFibered.pullbackPseudofunctor p) (sq := coveringPullback E) φ
    f.left V.hom W.hom (a.φ PUnit.unit).left (b.φ PUnit.unit).left
    (f.left ≫ (a.φ PUnit.unit).left) (f.left ≫ (b.φ PUnit.unit).left)
    (Over.w f) (Over.w _) (Over.w _) rfl rfl).symm

private lemma fiberHom_transport_defect
    {C : Type u} {S : Type u₂} [Category.{v} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered] [∀ V, IsGroupoid (p.Fiber V)]
    {V W : C} (f : W ⟶ V) {a b c : p.Fiber V} {a' b' c' : p.Fiber W}
    (α : a' ≅ p.pullbackFiber a f) (β : b' ≅ p.pullbackFiber b f)
    (γ : c' ≅ p.pullbackFiber c f) (m : a ⟶ b) (n : b ⟶ c) (o : a ⟶ c) :
    (α.hom ≫ Functor.pullbackFiberHom m f ≫ β.inv) ≫
      (β.hom ≫ Functor.pullbackFiberHom n f ≫ γ.inv) ≫
      inv (α.hom ≫ Functor.pullbackFiberHom o f ≫ γ.inv) =
    α.hom ≫ Functor.pullbackFiberHom (m ≫ n ≫ inv o) f ≫ α.inv := by
  simp only [IsIso.inv_comp, IsIso.Iso.inv_inv, IsIso.Iso.inv_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Functor.pullbackFiberHom_comp]
  rw [← Functor.pullbackPseudofunctor_map_map p f o,
    ← Functor.pullbackPseudofunctor_map_map p f (inv o)]
  exact congrArg (fun k => α.hom ≫ Functor.pullbackFiberHom m f ≫
    Functor.pullbackFiberHom n f ≫ k ≫ α.inv) (Functor.map_inv _ o).symm

private lemma autEquiv_map_eq_conj_pullbackFiberHom
    {C : Type u} {S : Type u₂} [Category.{v} C] [Category.{v₂} S]
    {J : GrothendieckTopology C} (p : S ⥤ C) [p.IsFibered] [∀ V, IsGroupoid (p.Fiber V)]
    (G : Sheaf J AddCommGrpCat.{w})
    (ε : ∀ V (y : p.Fiber V), G.obj.obj (op V) ≃ (y ⟶ y))
    (hconj : ∀ V (y z : p.Fiber V) (f : y ⟶ z) a,
      ε V z a = inv f ≫ ε V y a ≫ f)
    (hres : ∀ {V W} (y : p.Fiber V) (f : W ⟶ V) a,
      ε W (p.pullbackFiber y f) (G.obj.map f.op a) = Functor.pullbackFiberHom (ε V y a) f)
    {V W : C} (y : p.Fiber V) (f : W ⟶ V) {y' : p.Fiber W} (α : p.pullbackFiber y f ≅ y')
    (t : G.obj.obj (op V)) :
    ε W y' (G.obj.map f.op t) = α.inv ≫ Functor.pullbackFiberHom (ε V y t) f ≫ α.hom := by
  rw [hconj _ _ _ α.hom, hres, IsIso.Iso.inv_hom]

private lemma nonempty_descentData_of_familyHom
    {C : Type u} {S : Type u₂} [Category.{v} C] [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered]
    [∀ V, IsGroupoid (p.Fiber V)] {U : C} (E : PreZeroHypercover.{max u v v₂} U)
    (x : ∀ i : E.I₀, p.Fiber (E.X i))
    (n : ∀ {V : (Over U)ᵒᵖ} (a c : (familyPresheaf (fun i => Over.mk (E.f i))).obj V),
      familyObject p E x a ⟶ familyObject p E x c)
    (hnComp : ∀ {V : (Over U)ᵒᵖ} (a c d : (familyPresheaf (fun i => Over.mk (E.f i))).obj V),
      n a c ≫ n c d = n a d)
    (hnNat : ∀ {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
      (a c : (familyPresheaf (fun i => Over.mk (E.f i))).obj V),
      n ((familyPresheaf (fun i => Over.mk (E.f i))).map f a)
          ((familyPresheaf (fun i => Over.mk (E.f i))).map f c) =
        (Functor.pullbackFiberCompIso (x (a.f PUnit.unit)) (a.φ PUnit.unit).left
          f.unop.left).inv ≫
          Functor.pullbackFiberHom (n a c) f.unop.left ≫
        (Functor.pullbackFiberCompIso (x (c.f PUnit.unit)) (c.φ PUnit.unit).left
          f.unop.left).hom) :
    Nonempty ((Functor.IsFibered.pullbackPseudofunctor p).DescentData E.f) := by
  have hnSelf {V : (Over U)ᵒᵖ} (a : (familyPresheaf (fun i => Over.mk (E.f i))).obj V) :
      n a a = 𝟙 _ := by
    apply (cancel_epi (n a a)).mp
    simpa only [Category.comp_id] using hnComp a a a
  exact ⟨{
    obj := x
    hom := fun {Y} q {i j} f g hf hg =>
      n (V := op (Over.mk q)) (FormalCoproduct.Hom.fromIncl i (Over.homMk f hf))
        (FormalCoproduct.Hom.fromIncl j (Over.homMk g hg))
    hom_self := fun {Y} q {i} g hg => hnSelf _
    hom_comp := fun {Y} q {i j k} f g h hf hg hh => hnComp _ _ _
    pullHom_hom := by
      intro Y' Y g q q' hq i j f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      subst q' gf₁ gf₂
      exact (Functor.pullHom_eq p (x i) (x j) f₁ f₂ g _).trans <|
        (hnNat (Over.homMk g rfl : Over.mk (g ≫ q) ⟶ Over.mk q).op
          (FormalCoproduct.Hom.fromIncl i (Over.homMk f₁ hf₁))
          (FormalCoproduct.Hom.fromIncl j (Over.homMk f₂ hf₂))).symm }⟩

private lemma nonempty_descentData_of_pair_cochain
    {C : Type u} {S : Type u₂} [Category.{v} C] [Category.{v₂} S]
    (J : GrothendieckTopology C) (p : S ⥤ C) [p.IsFibered]
    [∀ V, IsGroupoid (p.Fiber V)] {U : C} (E : PreZeroHypercover.{max u v v₂} U)
    [∀ i j : E.I₀, HasPullback (E.f i) (E.f j)]
    (G : Sheaf J AddCommGrpCat.{max u v v₂})
    (ε : ∀ V (y : p.Fiber V), G.obj.obj (op V) ≃ (y ⟶ y))
    (hadd : ∀ V y a b, ε V y (a + b) = ε V y a ≫ ε V y b)
    (hconj : ∀ V (y z : p.Fiber V) (f : y ⟶ z) a,
      ε V z a = inv f ≫ ε V y a ≫ f)
    (hres : ∀ {V W} (y : p.Fiber V) (f : W ⟶ V) a,
      ε W (p.pullbackFiber y f) (G.obj.map f.op a) = Functor.pullbackFiberHom (ε V y a) f)
    (x : ∀ i : E.I₀, p.Fiber (E.X i))
    (φ : ∀ i j, p.pullbackFiber (x i) (pullback.fst (E.f i) (E.f j)) ⟶
      p.pullbackFiber (x j) (pullback.snd (E.f i) (E.f j)))
    (b : ∀ V, (familyPresheaf (fun i => Over.mk (E.f i))).obj V →
      (familyPresheaf (fun i => Over.mk (E.f i))).obj V → (G.over U).obj.obj V)
    (hbNat : ∀ {V W} (f : V ⟶ W) a c,
      b W ((familyPresheaf _).map f a) ((familyPresheaf _).map f c) =
        (G.over U).obj.map f (b V a c))
    (hb : ∀ V a c d, b V c d - b V a d + b V a c =
      (ε V.unop.left (familyObject p E x a)).symm (familyOverlap p E x φ a c ≫
        familyOverlap p E x φ c d ≫ inv (familyOverlap p E x φ a d))) :
    Nonempty ((Functor.IsFibered.pullbackPseudofunctor p).DescentData E.f) := by
  let P := familyPresheaf (fun i => Over.mk (E.f i))
  let y {V : (Over U)ᵒᵖ} (a : P.obj V) := familyObject p E x a
  let m {V : (Over U)ᵒᵖ} (a b : P.obj V) := familyOverlap p E x φ a b
  have hmNat {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (a c : P.obj V) :
      m (P.map f a) (P.map f c) =
      (Functor.pullbackFiberCompIso (x (a.f PUnit.unit)) (a.φ PUnit.unit).left f.unop.left).inv ≫
        Functor.pullbackFiberHom (m a c) f.unop.left ≫
      (Functor.pullbackFiberCompIso (x (c.f PUnit.unit)) (c.φ PUnit.unit).left f.unop.left).hom :=
    familyOverlap_map p E x φ f.unop a c
  let n {V : (Over U)ᵒᵖ} (a c : P.obj V) : y a ⟶ y c :=
    ε V.unop.left (y a) (-b V a c) ≫ m a c
  have hnComp {V : (Over U)ᵒᵖ} (a c d : P.obj V) : n a c ≫ n c d = n a d := by
    refine iso_cocycle_of_defect_eq_coboundary (asIso (m a c)) (asIso (m a d)) (asIso (m c d))
      (ε V.unop.left (y a)) (ε V.unop.left (y c)) (hadd _ _) ?_
      (b V a c) (b V a d) (b V c d) ?_
    · intro t
      rw [hconj _ (y a) (y c) (m a c)]
      simp
    · have heq : b V a c + b V c d - b V a d = b V c d - b V a d + b V a c := by abel
      exact (congrArg (fun t => ε V.unop.left (y a) t) (heq.trans (hb V a c d))).trans
        ((ε V.unop.left (y a)).apply_symm_apply _)
  have hnNat {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (a c : P.obj V) :
      n (P.map f a) (P.map f c) =
      (Functor.pullbackFiberCompIso (x (a.f PUnit.unit)) (a.φ PUnit.unit).left f.unop.left).inv ≫
        Functor.pullbackFiberHom (n a c) f.unop.left ≫
      (Functor.pullbackFiberCompIso (x (c.f PUnit.unit)) (c.φ PUnit.unit).left
        f.unop.left).hom := by
    have heNat : ε W.unop.left (y (P.map f a)) ((G.over U).obj.map f (-b V a c)) =
        (Functor.pullbackFiberCompIso (x (a.f PUnit.unit)) (a.φ PUnit.unit).left
          f.unop.left).inv ≫
          Functor.pullbackFiberHom (ε V.unop.left (y a) (-b V a c)) f.unop.left ≫
        (Functor.pullbackFiberCompIso (x (a.f PUnit.unit)) (a.φ PUnit.unit).left
          f.unop.left).hom :=
      autEquiv_map_eq_conj_pullbackFiberHom p G ε hconj hres (y a) f.unop.left _ _
    dsimp only [n]
    rw [hbNat, ← map_neg, heNat, hmNat]
    simp only [Functor.pullbackFiberHom_comp, Category.assoc, Iso.hom_inv_id_assoc]
  exact nonempty_descentData_of_familyHom p E x n hnComp hnNat

private lemma exists_corrected_familyOverlap
    {C : Type u} {S : Type u₂} [Category.{v} C] [Category.{v₂} S]
    (J : GrothendieckTopology C) (p : S ⥤ C) [p.IsFibered]
    [∀ V, IsGroupoid (p.Fiber V)] {U : C} (E : PreZeroHypercover.{max u v v₂} U)
    [∀ i j : E.I₀, HasPullback (E.f i) (E.f j)]
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{max u v v₂}]
    [∀ V : C, HasExt.{x} (Sheaf (J.over V) AddCommGrpCat.{max u v v₂})]
    (G : Sheaf J AddCommGrpCat.{max u v v₂})
    (ε : ∀ V (y : p.Fiber V), G.obj.obj (op V) ≃ (y ⟶ y))
    (hadd : ∀ V y a b, ε V y (a + b) = ε V y a ≫ ε V y b)
    (hconj : ∀ V (y z : p.Fiber V) (f : y ⟶ z) a,
      ε V z a = inv f ≫ ε V y a ≫ f)
    (hres : ∀ {V W} (y : p.Fiber V) (f : W ⟶ V) a,
      ε W (p.pullbackFiber y f) (G.obj.map f.op a) = Functor.pullbackFiberHom (ε V y a) f)
    (x : ∀ i : E.I₀, p.Fiber (E.X i))
    (φ : ∀ i j, p.pullbackFiber (x i) (pullback.fst (E.f i) (E.f j)) ⟶
      p.pullbackFiber (x j) (pullback.snd (E.f i) (E.f j)))
    (hE : E.sieve₀ ∈ J U)
    (hH1 : ∀ i, Subsingleton (Sheaf.H (G.over (E.X i)) 1))
    (hH2 : Subsingleton (Sheaf.H (G.over U) 2)) :
    Nonempty ((Functor.IsFibered.pullbackPseudofunctor p).DescentData E.f) := by
  let P := familyPresheaf (fun i => Over.mk (E.f i))
  let y {V : (Over U)ᵒᵖ} (a : P.obj V) := familyObject p E x a
  let m {V : (Over U)ᵒᵖ} (a b : P.obj V) := familyOverlap p E x φ a b
  let z (V : (Over U)ᵒᵖ) (a b c : P.obj V) : (G.over U).obj.obj V :=
    (ε V.unop.left (y a)).symm (m a b ≫ m b c ≫ inv (m a c))
  have hmNat {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (a c : P.obj V) :
      m (P.map f a) (P.map f c) =
      (Functor.pullbackFiberCompIso (x (a.f PUnit.unit)) (a.φ PUnit.unit).left f.unop.left).inv ≫
        Functor.pullbackFiberHom (m a c) f.unop.left ≫
      (Functor.pullbackFiberCompIso (x (c.f PUnit.unit)) (c.φ PUnit.unit).left f.unop.left).hom :=
    familyOverlap_map p E x φ f.unop a c
  have hz : ∀ V a b c d, z V b c d - z V a c d + z V a b d - z V a b c = 0 := by
    intro V a b c d
    apply additive_iso_defect_cocycle (asIso (m a b)) (asIso (m a c)) (asIso (m a d))
      (asIso (m b c)) (asIso (m b d)) (asIso (m c d))
      (ε V.unop.left (y a)) (ε V.unop.left (y b))
      (ε V.unop.left (y a)).injective (hadd _ _) _ _ _ _ _
      ((ε _ _).apply_symm_apply _) ((ε _ _).apply_symm_apply _)
      ((ε _ _).apply_symm_apply _) ((ε _ _).apply_symm_apply _)
    intro t
    rw [hconj _ (y a) (y b) (m a b)]
    simp
  have hn : ∀ {V W} (f : V ⟶ W) a b c,
      z W (P.map f a) (P.map f b) (P.map f c) = (G.over U).obj.map f (z V a b c) := by
    intro V W f a b c
    let α := Functor.pullbackFiberCompIso (x (a.f PUnit.unit))
      (a.φ PUnit.unit).left f.unop.left
    let β := Functor.pullbackFiberCompIso (x (b.f PUnit.unit))
      (b.φ PUnit.unit).left f.unop.left
    let γ := Functor.pullbackFiberCompIso (x (c.f PUnit.unit))
      (c.φ PUnit.unit).left f.unop.left
    apply (ε W.unop.left (y (P.map f a))).injective
    rw [show ε W.unop.left (y (P.map f a)) ((G.over U).obj.map f (z V a b c)) =
        α.inv ≫ Functor.pullbackFiberHom (ε V.unop.left (y a) (z V a b c)) f.unop.left ≫ α.hom
      from autEquiv_map_eq_conj_pullbackFiberHom p G ε hconj hres (y a) f.unop.left α _]
    dsimp only [z]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hmNat, hmNat, hmNat]
    exact fiberHom_transport_defect p f.unop.left α.symm β.symm γ.symm (m a b) (m b c) (m a c)
  obtain ⟨b, hbNat, hb⟩ := exists_pair_cochain_of_ext_vanishing (J.over U) P (G.over U)
    (familyPresheaf_locally_nonempty J E hE) (ext_one_coverFamily_vanishes J E G hH1)
    hH2 z hz hn
  exact nonempty_descentData_of_pair_cochain J p E G ε hadd hconj hres x φ b hbNat hb

end

private theorem exists_covering_family_with_objects
    {C : Type u₁} {S : Type u₂} [Category.{v₁} C]
    [Category.{v₂} S] (J : GrothendieckTopology C) (p : S ⥤ C)
    (hne : p.LocallyNonempty J) (U : C)
    (Cov : Set (PreZeroHypercover.{w} U))
    (hCofinal : ∀ R ∈ J U,
      ∃ E : PreZeroHypercover.{w} U, E ∈ Cov ∧ E.sieve₀ ≤ R) :
    ∃ E ∈ Cov, ∀ i : E.I₀, Nonempty (p.Fiber (E.X i)) := by
  obtain ⟨R, hR, hRobj⟩ := hne U
  obtain ⟨E, hE, hER⟩ := hCofinal R hR
  exact ⟨E, hE, fun i => hRobj (E.f i) (hER (E.f i) (E.sieve₀_f i))⟩

/-- **Stacks 0CK0.** Let `p : S ⥤ C` be a gerbe over the site `(C, J)` — fibred in groupoids, a
stack, locally nonempty, locally connected — and let `G` be the sheaf of abelian groups
constructed in Stacks 0CJY: an abelian sheaf given with comparisons `θ y : G|_V ≅ Aut(y)`, one
for every object `y` of every fibre, multiplicative and compatible with conjugation and with base
change. Let `U` be an object of `C` such that

1. there is a cofinal system `Cov` of coverings of `U` — a set of covering families refining every
   covering sieve of `U` — with `H¹(U_i, G) = 0` for every member `U_i` of every family in it and
   `H¹(U_i ×_U U_j, G) = 0` for every pair of members, and
2. `H²(U, G) = 0`.

Then there is an object of `S` lying over `U`.

That the automorphism sheaves of the gerbe are abelian needs no separate hypothesis: each `θ y` is
a multiplicative isomorphism onto `Aut(y)` from a sheaf of abelian groups, so `Aut(y)` is abelian.
For the form in which `G` and its comparisons are produced rather than assumed, see
`CategoryTheory.Gerbe.exists_band_nonempty_fiber_of_cohomology_vanishing`. -/
@[stacks 0CK0]
public theorem nonempty_fiber_of_cohomology_vanishing
    {C : Type u₁} {S : Type u₂}
    [Category.{v₁} C] [Category.{v₂} S]
    (J : GrothendieckTopology C) (p : S ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    (hne : p.LocallyNonempty J) (hlc : p.LocallyConnected J)
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u₁ v₁ v₂}]
    [∀ X : C, HasExt.{x} (Sheaf (J.over X) AddCommGrpCat.{max u₁ v₁ v₂})]
    (G : Sheaf J AddCommGrpCat.{max u₁ v₁ v₂})
    (hBand :
      haveI : p.IsFibered := hp.isFibered
      haveI : ∀ V : C, IsGroupoid (p.Fiber V) := hp.fiber_isGroupoid
      ∃ (θ : ∀ (V : C) (y : p.Fiber V),
          (Over.forget V).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp.{max u₁ v₁ v₂} ⋙
              forget CommGrpCat.{max u₁ v₁ v₂} ≅
            p.morPresheaf y y ⋙ uliftFunctor.{max u₁ v₁, v₂}),
        (∀ (V : C) (y : p.Fiber V) (g : Over V) (a b : G.obj.obj (op g.left)),
          ((θ V y).hom.app (op g) (Multiplicative.ofAdd (a + b))).down =
            ((θ V y).hom.app (op g) (Multiplicative.ofAdd a)).down ≫
              ((θ V y).hom.app (op g) (Multiplicative.ofAdd b)).down) ∧
        (∀ (V : C) (y z : p.Fiber V) (φ : y ⟶ z) (g : Over V)
            (a : G.obj.obj (op g.left)),
          ((θ V z).hom.app (op g) (Multiplicative.ofAdd a)).down =
            Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
              ((θ V y).hom.app (op g) (Multiplicative.ofAdd a)).down ≫
                Functor.pullbackFiberHom φ g.hom) ∧
        (∀ (V : C) (y : p.Fiber V) (g : Over V)
            (a : G.obj.obj (op g.left)),
          ((θ V y).hom.app (op g) (Multiplicative.ofAdd a)).down =
            (Functor.pullbackFiberIdIso (p.pullbackFiber y g.hom)).inv ≫
              ((θ g.left (p.pullbackFiber y g.hom)).hom.app
                (op (Over.mk (𝟙 g.left))) (Multiplicative.ofAdd a)).down ≫
                  (Functor.pullbackFiberIdIso (p.pullbackFiber y g.hom)).hom))
    (U : C) (Cov : Set (PreZeroHypercover.{max u₁ v₁ v₂} U))
    (hCover : ∀ E ∈ Cov, E.sieve₀ ∈ J U)
    (hCofinal : ∀ R ∈ J U, ∃ E : PreZeroHypercover.{max u₁ v₁ v₂} U,
      E ∈ Cov ∧ E.sieve₀ ≤ R)
    (hPullback : ∀ (E : PreZeroHypercover.{max u₁ v₁ v₂} U), E ∈ Cov →
      ∀ i j : E.I₀, HasPullback (E.f i) (E.f j))
    (hH1 : ∀ (E : PreZeroHypercover.{max u₁ v₁ v₂} U), E ∈ Cov →
      ∀ i : E.I₀, Subsingleton (Sheaf.H (G.over (E.X i)) 1))
    (hH1pair : ∀ (E : PreZeroHypercover.{max u₁ v₁ v₂} U) (hE : E ∈ Cov)
      (i j : E.I₀),
      let : HasPullback (E.f i) (E.f j) := hPullback E hE i j
      Subsingleton (Sheaf.H (G.over (pullback (E.f i) (E.f j))) 1))
    (hH2 : Subsingleton (Sheaf.H (G.over U) 2)) :
    Nonempty (p.Fiber U) := by
  classical
  let : p.IsFibered := hp.isFibered
  let : ∀ V : C, IsGroupoid (p.Fiber V) := hp.fiber_isGroupoid
  obtain ⟨θ, hθadd, hθconj, hθbase⟩ := hBand
  obtain ⟨E, hE, hObj⟩ := exists_covering_family_with_objects J p hne U Cov hCofinal
  let x : ∀ i : E.I₀, p.Fiber (E.X i) := fun i => (hObj i).some
  let : ∀ i j : E.I₀, HasPullback (E.f i) (E.f j) := hPullback E hE
  have hIso : ∀ i j : E.I₀,
      Nonempty (p.pullbackFiber (x i) (pullback.fst (E.f i) (E.f j)) ≅
        p.pullbackFiber (x j) (pullback.snd (E.f i) (E.f j))) := by
    intro i j
    let V := pullback (E.f i) (E.f j)
    let a := p.pullbackFiber (x i) (pullback.fst (E.f i) (E.f j))
    let b := p.pullbackFiber (x j) (pullback.snd (E.f i) (E.f j))
    exact nonempty_fiberIso_of_subsingleton_H1 p hp hst hlc a b (G.over V)
      (θ V a) (fun W g h => hθadd V a W.unop g h) (hH1pair E hE i j)
  let φ := fun i j => (hIso i j).some
  have hRestrict : ∀ {V W : C} (y : p.Fiber V) (f : W ⟶ V)
      (a : G.obj.obj (op V)),
      bandEndEquiv p G (p.pullbackFiber y f) (θ W (p.pullbackFiber y f))
          (G.obj.map f.op a) =
        Functor.pullbackFiberHom (bandEndEquiv p G y (θ V y) a) f :=
    fun y f a => bandEndEquiv_pullback_of_coherence p G y f (θ _ y)
      (θ _ (p.pullbackFiber y f)) (hθbase _ y (Over.mk f)) a
  obtain ⟨D⟩ := exists_corrected_familyOverlap J p E G
    (fun V y => bandEndEquiv p G y (θ V y))
    (fun V y => bandEndEquiv_add p G y (θ V y) (hθadd V y (Over.mk (𝟙 V))))
    (fun V y z f => bandEndEquiv_conj p G y z f (θ V y) (θ V z)
      (hθconj V y z f (Over.mk (𝟙 V))))
    hRestrict x (fun i j => (φ i j).hom) (hCover E hE) (hH1 E hE) hH2
  let := Functor.isEquivalence_toDescentData_of_isStack p hst E.f (hCover E hE)
  exact ⟨((Functor.IsFibered.pullbackPseudofunctor p).toDescentData E.f).objPreimage D⟩

/-- **Stacks 0CK0, with nothing assumed.** Let `p : S ⥤ C` be a gerbe over the site `(C, J)` whose
automorphism sheaves are abelian. Then there are a sheaf `G` of abelian groups on `C` and
comparisons `θ y : G|_V ≅ Aut(y)` — that is, the sheaf constructed in Stacks 0CJY, together with
the data that identifies it: multiplicativity, compatibility with conjugation, and compatibility
over varying base object — such that for every object `U` of `C` with

1. a cofinal system `Cov` of coverings of `U` whose members `U_i` have `H¹(U_i, G) = 0` and whose
   pairs of members have `H¹(U_i ×_U U_j, G) = 0`, and
2. `H²(U, G) = 0`

there is an object of `S` lying over `U`.

This is `CategoryTheory.Gerbe.nonempty_fiber_of_cohomology_vanishing` with its hypothesis on `G`
discharged: `G` is here the band of
`CategoryTheory.Gerbe.exists_sheaf_iso_morPresheaf_self_uliftFunctor_base`, carried from
`CommGrpCat` to `AddCommGrpCat` — the universe in which `Sheaf.H` takes its coefficients — along
`commGroupAddCommGroupEquivalence`, whose unit and counit are `Iso.refl`, so the comparisons
transport unchanged. No hypothesis of this statement is the conclusion of another tag. -/
@[stacks 0CK0]
public theorem exists_band_nonempty_fiber_of_cohomology_vanishing
    {C : Type u₁} {S : Type u₂}
    [Category.{v₁} C] [Category.{v₂} S]
    (J : GrothendieckTopology C) (p : S ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    (hne : p.LocallyNonempty J) (hlc : p.LocallyConnected J)
    (habel : ∀ (V : C) (y : p.Fiber V) (α β : y ⟶ y), α ≫ β = β ≫ α)
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u₁ v₁ v₂}]
    [∀ X : C, HasExt.{x} (Sheaf (J.over X) AddCommGrpCat.{max u₁ v₁ v₂})] :
    haveI : p.IsFibered := hp.isFibered
    haveI : ∀ V : C, IsGroupoid (p.Fiber V) := hp.fiber_isGroupoid
    ∃ (G : Sheaf J AddCommGrpCat.{max u₁ v₁ v₂})
      (θ : ∀ (V : C) (y : p.Fiber V),
        (Over.forget V).op ⋙ G.obj ⋙ AddCommGrpCat.toCommGrp.{max u₁ v₁ v₂} ⋙
            forget CommGrpCat.{max u₁ v₁ v₂} ≅
          p.morPresheaf y y ⋙ uliftFunctor.{max u₁ v₁, v₂}),
      (∀ (V : C) (y : p.Fiber V) (g : Over V) (a b : G.obj.obj (op g.left)),
          ((θ V y).hom.app (op g) (Multiplicative.ofAdd (a + b))).down =
            ((θ V y).hom.app (op g) (Multiplicative.ofAdd a)).down ≫
              ((θ V y).hom.app (op g) (Multiplicative.ofAdd b)).down) ∧
        (∀ (V : C) (y z : p.Fiber V) (φ : y ⟶ z) (g : Over V)
            (a : G.obj.obj (op g.left)),
          ((θ V z).hom.app (op g) (Multiplicative.ofAdd a)).down =
            Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
              ((θ V y).hom.app (op g) (Multiplicative.ofAdd a)).down ≫
                Functor.pullbackFiberHom φ g.hom) ∧
        (∀ (V : C) (y : p.Fiber V) (g : Over V)
            (a : G.obj.obj (op g.left)),
          ((θ V y).hom.app (op g) (Multiplicative.ofAdd a)).down =
            (Functor.pullbackFiberIdIso (p.pullbackFiber y g.hom)).inv ≫
              ((θ g.left (p.pullbackFiber y g.hom)).hom.app
                (op (Over.mk (𝟙 g.left))) (Multiplicative.ofAdd a)).down ≫
                  (Functor.pullbackFiberIdIso (p.pullbackFiber y g.hom)).hom) ∧
        ∀ (U : C) (Cov : Set (PreZeroHypercover.{max u₁ v₁ v₂} U)),
          (∀ E ∈ Cov, E.sieve₀ ∈ J U) →
          (∀ R ∈ J U, ∃ E : PreZeroHypercover.{max u₁ v₁ v₂} U, E ∈ Cov ∧ E.sieve₀ ≤ R) →
          ∀ hPullback : ∀ (E : PreZeroHypercover.{max u₁ v₁ v₂} U), E ∈ Cov →
              ∀ i j : E.I₀, HasPullback (E.f i) (E.f j),
            (∀ (E : PreZeroHypercover.{max u₁ v₁ v₂} U), E ∈ Cov →
              ∀ i : E.I₀, Subsingleton (Sheaf.H (G.over (E.X i)) 1)) →
            (∀ (E : PreZeroHypercover.{max u₁ v₁ v₂} U) (hE : E ∈ Cov) (i j : E.I₀),
              let : HasPullback (E.f i) (E.f j) := hPullback E hE i j
              Subsingleton (Sheaf.H (G.over (pullback (E.f i) (E.f j))) 1)) →
            Subsingleton (Sheaf.H (G.over U) 2) → Nonempty (p.Fiber U) := by
  let : p.IsFibered := hp.isFibered
  let : ∀ V : C, IsGroupoid (p.Fiber V) := hp.fiber_isGroupoid
  let : CommGrpCat.toAddCommGrp.{max u₁ v₁ v₂}.IsEquivalence :=
    commGroupAddCommGroupEquivalence.{max u₁ v₁ v₂}.isEquivalence_functor
  obtain ⟨𝒢, θ, hmul, hconj, hbase⟩ :=
    exists_sheaf_iso_morPresheaf_self_uliftFunctor_base p J hp hst hne hlc habel
  refine ⟨⟨𝒢.obj ⋙ CommGrpCat.toAddCommGrp.{max u₁ v₁ v₂},
      Presheaf.isSheaf_comp_of_isSheaf J _ CommGrpCat.toAddCommGrp.{max u₁ v₁ v₂} 𝒢.property⟩,
    θ, fun V y g a b => hmul V y g (Multiplicative.ofAdd a) (Multiplicative.ofAdd b),
    fun V y z φ g a => hconj V y z φ g (Multiplicative.ofAdd a),
    fun V y g a => hbase V y g (Multiplicative.ofAdd a), ?_⟩
  intro U Cov hCover hCofinal hPullback hH1 hH1pair hH2
  exact nonempty_fiber_of_cohomology_vanishing J p hp hst hne hlc _
    ⟨θ, fun V y g a b => hmul V y g (Multiplicative.ofAdd a) (Multiplicative.ofAdd b),
      fun V y z φ g a => hconj V y z φ g (Multiplicative.ofAdd a),
      fun V y g a => hbase V y g (Multiplicative.ofAdd a)⟩
    U Cov hCover hCofinal hPullback hH1 hH1pair hH2

end CategoryTheory.Gerbe

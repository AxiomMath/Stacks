module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Adequate.Tangent.TangentFunctor

/-!
# The second module structure on a right exact tangent functor

For a right exact tangent functor, the tangent functor carries binary direct sums of modules to
direct sums of tangent modules; consequently the second scalar action makes each tangent module a
module over the algebra, natural in the pair, and the multiplication map is linear for it.

## References

* [Stacks Project, Tag 06ZB](https://stacks.math.columbia.edu/tag/06ZB)
* [Stacks Project, Tag 06ZC](https://stacks.math.columbia.edu/tag/06ZC)
-/

@[expose] public section

namespace AdequateFunctor

section

open CategoryTheory AdequateFunctor


universe u v w

/-- If `f ≫ g` is the identity, then `g` is a retraction of `f` on tangent modules. -/
private theorem tangentMap_comp_apply_of_comp_eq_id (A : Type u) [CommRing A]
    (F : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)) {X Y : AlgebraModulePair.{v} A}
    (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) (z : tangentModule A F X) :
    (tangentFunctor A F).map g ((tangentFunctor A F).map f z) = z := by
  rw [← (tangentFunctor A F).map_comp f g z, h]
  exact (tangentFunctor A F).map_id X z

/-- If the module map of `f ≫ g` vanishes, then `g ∘ f` is zero on tangent modules. -/
private theorem tangentMap_comp_apply_of_linear_eq_zero (A : Type u) [CommRing A]
    (F : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)) {X Y Z : AlgebraModulePair.{v} A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : (f ≫ g).linear = 0) (z : tangentModule A F X) :
    (tangentFunctor A F).map g ((tangentFunctor A F).map f z) = 0 := by
  rw [← (tangentFunctor A F).map_comp f g z]
  exact DFunLike.congr_fun (tangentFunctor_map_eq_zero A F _ h) z

/-- A right exact tangent functor carries a binary direct sum of modules to
the direct sum of their tangent modules, via the two projections. -/
@[stacks 06ZB "direct_sum"]
theorem tangentModule_prod_bijective
    (T : RightExactTangentFunctor.{u, v, w})
    (B : Type v) [CommRing B] [Algebra T.A B]
    (N₁ N₂ : Type v) [AddCommGroup N₁] [Module B N₁]
    [AddCommGroup N₂] [Module B N₂] :
    Function.Bijective
      (fun x : tangentModule T.A T.F
          ({ algebra := B, module := N₁ × N₂ } : AlgebraModulePair.{v} T.A) =>
        ((tangentFunctor T.A T.F).map
            ({ base := AlgHom.id T.A B
               linear := LinearMap.fst B N₁ N₂ } :
              ({ algebra := B, module := N₁ × N₂ } : AlgebraModulePair.{v} T.A) ⟶
              ({ algebra := B, module := N₁ } : AlgebraModulePair.{v} T.A)) x,
         (tangentFunctor T.A T.F).map
            ({ base := AlgHom.id T.A B
               linear := LinearMap.snd B N₁ N₂ } :
              ({ algebra := B, module := N₁ × N₂ } : AlgebraModulePair.{v} T.A) ⟶
              ({ algebra := B, module := N₂ } : AlgebraModulePair.{v} T.A)) x)) := by
  let X₁ : AlgebraModulePair.{v} T.A := ⟨B, N₁⟩
  let X₂ : AlgebraModulePair.{v} T.A := ⟨B, N₂⟩
  let P : AlgebraModulePair.{v} T.A := ⟨B, N₁ × N₂⟩
  let i : X₁ ⟶ P :=
    ⟨AlgHom.id T.A B, LinearMap.inl B N₁ N₂⟩
  let s : X₂ ⟶ P :=
    ⟨AlgHom.id T.A B, LinearMap.inr B N₁ N₂⟩
  let p₁ : P ⟶ X₁ :=
    ⟨AlgHom.id T.A B, LinearMap.fst B N₁ N₂⟩
  let p₂ : P ⟶ X₂ :=
    ⟨AlgHom.id T.A B, LinearMap.snd B N₁ N₂⟩
  let S : ShortComplex (ModuleCat.{v} B) :=
    ShortComplex.moduleCatMk (LinearMap.inl B N₁ N₂) (LinearMap.snd B N₁ N₂)
      (by ext x; simp)
  have hS_exact : S.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change x.2 = 0 at hx
    refine ⟨x.1, ?_⟩
    show (x.1, 0) = x
    exact Prod.ext rfl hx.symm
  have hS_mono : Mono S.f := by
    rw [ModuleCat.mono_iff_injective]
    show Function.Injective (LinearMap.inl B N₁ N₂)
    exact LinearMap.inl_injective
  have hS_epi : Epi S.g := by
    rw [ModuleCat.epi_iff_surjective]
    show Function.Surjective (LinearMap.snd B N₁ N₂)
    intro y
    exact ⟨(0, y), rfl⟩
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' hS_exact hS_mono hS_epi
  have hExact :
      Function.Exact ((tangentFunctor T.A T.F).map i)
        ((tangentFunctor T.A T.F).map p₂) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp (T.rightExact B S hS).1
  have hs₁ : (s ≫ p₁).linear = 0 := by
    ext x
    rfl
  have hi₂ : (i ≫ p₂).linear = 0 := by
    ext x
    rfl
  have hm₁ := tangentMap_comp_apply_of_comp_eq_id T.A T.F i p₁
    (AlgebraModulePair.Hom.ext _ _ rfl fun _ => rfl)
  have hm₂ := tangentMap_comp_apply_of_comp_eq_id T.A T.F s p₂
    (AlgebraModulePair.Hom.ext _ _ rfl fun _ => rfl)
  have hm₃ := tangentMap_comp_apply_of_linear_eq_zero T.A T.F s p₁ hs₁
  have hm₄ := tangentMap_comp_apply_of_linear_eq_zero T.A T.F i p₂ hi₂
  have hdecomp (x : tangentModule T.A T.F P) :
      x = (tangentFunctor T.A T.F).map i
            ((tangentFunctor T.A T.F).map p₁ x) +
          (tangentFunctor T.A T.F).map s
            ((tangentFunctor T.A T.F).map p₂ x) := by
    have hk : (tangentFunctor T.A T.F).map p₂
        (x - (tangentFunctor T.A T.F).map s
          ((tangentFunctor T.A T.F).map p₂ x)) = 0 := by
      simp only [map_sub, hm₂, sub_self]
    obtain ⟨y, hy⟩ := Set.mem_range.mp ((hExact _).mp hk)
    have hy₁ := congrArg ((tangentFunctor T.A T.F).map p₁) hy
    rw [map_sub, hm₃, sub_zero, hm₁] at hy₁
    calc
      x = (x - (tangentFunctor T.A T.F).map s
            ((tangentFunctor T.A T.F).map p₂ x)) +
            (tangentFunctor T.A T.F).map s
              ((tangentFunctor T.A T.F).map p₂ x) := by simp
      _ = (tangentFunctor T.A T.F).map i y +
            (tangentFunctor T.A T.F).map s
              ((tangentFunctor T.A T.F).map p₂ x) := by rw [← hy]
      _ = (tangentFunctor T.A T.F).map i
            ((tangentFunctor T.A T.F).map p₁ x) +
            (tangentFunctor T.A T.F).map s
              ((tangentFunctor T.A T.F).map p₂ x) := by rw [hy₁]
  have hfun : Function.Injective (fun x : tangentModule T.A T.F P =>
      ((tangentFunctor T.A T.F).map p₁ x, (tangentFunctor T.A T.F).map p₂ x)) := by
    intro x y h
    have h₁ : (tangentFunctor T.A T.F).map p₁ x =
        (tangentFunctor T.A T.F).map p₁ y := congrArg Prod.fst h
    have h₂ : (tangentFunctor T.A T.F).map p₂ x =
        (tangentFunctor T.A T.F).map p₂ y := congrArg Prod.snd h
    rw [hdecomp x, hdecomp y, h₁, h₂]
  have hsurj : Function.Surjective (fun x : tangentModule T.A T.F P =>
      ((tangentFunctor T.A T.F).map p₁ x, (tangentFunctor T.A T.F).map p₂ x)) := by
    rintro ⟨x, y⟩
    refine ⟨(tangentFunctor T.A T.F).map i x + (tangentFunctor T.A T.F).map s y, ?_⟩
    show ((tangentFunctor T.A T.F).map p₁
        ((tangentFunctor T.A T.F).map i x + (tangentFunctor T.A T.F).map s y),
      (tangentFunctor T.A T.F).map p₂
        ((tangentFunctor T.A T.F).map i x + (tangentFunctor T.A T.F).map s y)) = (x, y)
    apply Prod.ext
    · calc
        (tangentFunctor T.A T.F).map p₁
            ((tangentFunctor T.A T.F).map i x + (tangentFunctor T.A T.F).map s y) =
            (tangentFunctor T.A T.F).map p₁ ((tangentFunctor T.A T.F).map i x) +
              (tangentFunctor T.A T.F).map p₁ ((tangentFunctor T.A T.F).map s y) :=
          map_add _ _ _
        _ = x := by rw [hm₁, hm₃]; simp
    · calc
        (tangentFunctor T.A T.F).map p₂
            ((tangentFunctor T.A T.F).map i x + (tangentFunctor T.A T.F).map s y) =
            (tangentFunctor T.A T.F).map p₂ ((tangentFunctor T.A T.F).map i x) +
              (tangentFunctor T.A T.F).map p₂ ((tangentFunctor T.A T.F).map s y) :=
          map_add _ _ _
        _ = y := by rw [hm₄, hm₂]; simp
  exact ⟨hfun, hsurj⟩

end

section

open CategoryTheory AdequateFunctor


universe u v w

variable (S : RightExactTangentFunctor.{u, v, w})

private abbrev scalarHom (X : AlgebraModulePair.{v} S.A) (b : X.algebra) : X ⟶ X :=
  { base := AlgHom.id S.A X.algebra
    linear := LinearMap.lsmul X.algebra X.module b }

private def pairAdd (B : Type v) [CommRing B] [Algebra S.A B]
    (N : Type v) [AddCommGroup N] [Module B N] :
    N × N →ₛₗ[(AlgHom.id S.A B).toRingHom] N :=
  { toFun := fun p => p.1 + p.2
    map_add' := by intro p q; simp [add_add_add_comm]
    map_smul' := by intro b p; simp [smul_add] }

private theorem tangentMap_add_components
    (B : Type v) [CommRing B] [Algebra S.A B]
    (N : Type v) [AddCommGroup N] [Module B N]
    (y : tangentModule S.A S.F
      ({ algebra := B, module := N × N } : AlgebraModulePair.{v} S.A)) :
    (tangentFunctor S.A S.F).map
        ({ base := AlgHom.id S.A B
           linear := pairAdd S B N } :
          ({ algebra := B, module := N × N } : AlgebraModulePair.{v} S.A) ⟶
          ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) y =
      (tangentFunctor S.A S.F).map
          ({ base := AlgHom.id S.A B
             linear := LinearMap.fst B N N } :
            ({ algebra := B, module := N × N } : AlgebraModulePair.{v} S.A) ⟶
            ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) y +
        (tangentFunctor S.A S.F).map
          ({ base := AlgHom.id S.A B
             linear := LinearMap.snd B N N } :
            ({ algebra := B, module := N × N } : AlgebraModulePair.{v} S.A) ⟶
            ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) y := by
  classical
  let P : AlgebraModulePair.{v} S.A := ⟨B, N × N⟩
  let X : AlgebraModulePair.{v} S.A := ⟨B, N⟩
  let i₁ : X ⟶ P := ⟨AlgHom.id S.A B, LinearMap.inl B N N⟩
  let i₂ : X ⟶ P := ⟨AlgHom.id S.A B, LinearMap.inr B N N⟩
  let p₁ : P ⟶ X := ⟨AlgHom.id S.A B, LinearMap.fst B N N⟩
  let p₂ : P ⟶ X := ⟨AlgHom.id S.A B, LinearMap.snd B N N⟩
  let add : P ⟶ X := ⟨AlgHom.id S.A B, pairAdd S B N⟩
  have hbij := AdequateFunctor.tangentModule_prod_bijective S B N N
  have hinj := hbij.1
  have hzero₁ : (i₂ ≫ p₁).linear = 0 := by
    ext n
    rfl
  have hzero₂ : (i₁ ≫ p₂).linear = 0 := by
    ext n
    rfl
  have hp₁i₁ := tangentMap_comp_apply_of_comp_eq_id S.A S.F i₁ p₁
    (AlgebraModulePair.Hom.ext _ _ rfl fun _ => rfl)
  have hp₂i₂ := tangentMap_comp_apply_of_comp_eq_id S.A S.F i₂ p₂
    (AlgebraModulePair.Hom.ext _ _ rfl fun _ => rfl)
  have hp₁i₂ := tangentMap_comp_apply_of_linear_eq_zero S.A S.F i₂ p₁ hzero₁
  have hp₂i₁ := tangentMap_comp_apply_of_linear_eq_zero S.A S.F i₁ p₂ hzero₂
  have hdecomp : y = (tangentFunctor S.A S.F).map i₁ ((tangentFunctor S.A S.F).map p₁ y) +
      (tangentFunctor S.A S.F).map i₂ ((tangentFunctor S.A S.F).map p₂ y) := by
    apply hinj
    apply Prod.ext
    · change (tangentFunctor S.A S.F).map p₁ y = (tangentFunctor S.A S.F).map p₁ _
      rw [map_add, hp₁i₁, hp₁i₂, add_zero]
    · change (tangentFunctor S.A S.F).map p₂ y = (tangentFunctor S.A S.F).map p₂ _
      rw [map_add, hp₂i₁, hp₂i₂, zero_add]
  have ha₁ : i₁ ≫ add = 𝟙 X := by
    apply AlgebraModulePair.Hom.ext
    · rfl
    · intro n
      show (n : N) + 0 = n
      simp
  have ha₂ : i₂ ≫ add = 𝟙 X := by
    apply AlgebraModulePair.Hom.ext
    · rfl
    · intro n
      show (0 : N) + n = n
      simp
  calc
    (tangentFunctor S.A S.F).map
        ({ base := AlgHom.id S.A B, linear := pairAdd S B N } : P ⟶ X) y =
        (tangentFunctor S.A S.F).map
          ({ base := AlgHom.id S.A B, linear := pairAdd S B N } : P ⟶ X)
          ((tangentFunctor S.A S.F).map i₁ ((tangentFunctor S.A S.F).map p₁ y) +
            (tangentFunctor S.A S.F).map i₂ ((tangentFunctor S.A S.F).map p₂ y)) :=
              congrArg ((tangentFunctor S.A S.F).map
                ({ base := AlgHom.id S.A B, linear := pairAdd S B N } : P ⟶ X)) hdecomp
    _ = (tangentFunctor S.A S.F).map
          ({ base := AlgHom.id S.A B, linear := pairAdd S B N } : P ⟶ X)
          ((tangentFunctor S.A S.F).map i₁ ((tangentFunctor S.A S.F).map p₁ y)) +
        (tangentFunctor S.A S.F).map add
          ((tangentFunctor S.A S.F).map i₂ ((tangentFunctor S.A S.F).map p₂ y)) :=
          ((tangentFunctor S.A S.F).map
            ({ base := AlgHom.id S.A B, linear := pairAdd S B N } : P ⟶ X)).map_add _ _
    _ = (tangentFunctor S.A S.F).map p₁ y + (tangentFunctor S.A S.F).map p₂ y := by
          calc
            _ = (tangentFunctor S.A S.F).map (i₁ ≫ add)
                    ((tangentFunctor S.A S.F).map p₁ y) +
                (tangentFunctor S.A S.F).map (i₂ ≫ add)
                    ((tangentFunctor S.A S.F).map p₂ y) := by
                      rw [(tangentFunctor S.A S.F).map_comp i₁ add,
                        (tangentFunctor S.A S.F).map_comp i₂ add]
            _ = _ := by
              rw [ha₁, ha₂]
              simp only [(tangentFunctor S.A S.F).map_id]

/-- The second module structure on a tangent module, characterized by the
action induced by multiplication on the module variable. -/
@[stacks 06ZB "second_module_structure"]
noncomputable def secondModuleStructure (X : AlgebraModulePair.{v} S.A) :
    { m : Module X.algebra (tangentModule S.A S.F X) //
      ∀ (b : X.algebra) (x : tangentModule S.A S.F X),
        m.toDistribMulAction.toSMul.smul b x =
          secondScalarAction S.A S.F X x b } := by
  classical
  let smul : X.algebra → tangentModule S.A S.F X → tangentModule S.A S.F X :=
    fun b x => secondScalarAction S.A S.F X x b
  let m : Module X.algebra (tangentModule S.A S.F X) := by
    letI : SMul X.algebra (tangentModule S.A S.F X) := ⟨smul⟩
    exact {
    smul := smul
    one_smul := by
      intro x
      change (tangentFunctor S.A S.F).map (scalarHom S X 1) x = x
      have hid : scalarHom S X 1 = 𝟙 X := by
        apply AlgebraModulePair.Hom.ext
        · rfl
        · intro n
          change (1 : X.algebra) • n = n
          simp
      rw [hid]
      exact (tangentFunctor S.A S.F).map_id X x
    mul_smul := by
      intro b c x
      have hmul : scalarHom S X (b * c) = scalarHom S X c ≫ scalarHom S X b := by
        apply AlgebraModulePair.Hom.ext
        · rfl
        · intro n
          change (b * c) • n = b • (c • n)
          simp [smul_smul]
      calc
        (tangentFunctor S.A S.F).map (scalarHom S X (b * c)) x =
            (tangentFunctor S.A S.F).map (scalarHom S X c ≫ scalarHom S X b) x := by
              rw [hmul]
        _ = (tangentFunctor S.A S.F).map (scalarHom S X b)
              ((tangentFunctor S.A S.F).map (scalarHom S X c) x) := by
              rw [(tangentFunctor S.A S.F).map_comp]
    smul_add := by
      intro b x y
      change (tangentFunctor S.A S.F).map (scalarHom S X b) (x + y) = _
      exact map_add ((tangentFunctor S.A S.F).map (scalarHom S X b)) x y
    smul_zero := by
      intro b
      change (tangentFunctor S.A S.F).map (scalarHom S X b) 0 = 0
      exact map_zero ((tangentFunctor S.A S.F).map (scalarHom S X b))
    add_smul := by
      intro b c x
      change secondScalarAction S.A S.F X x (b + c) =
        secondScalarAction S.A S.F X x b + secondScalarAction S.A S.F X x c
      let P : AlgebraModulePair.{v} S.A := ⟨X.algebra, X.module × X.module⟩
      let dlinear : X.module →ₗ[X.algebra] X.module × X.module :=
        { toFun := fun n => (b • n, c • n)
          map_add' := by intro n m; simp
          map_smul' := by
            intro r n
            apply Prod.ext <;> simp [smul_smul, mul_comm] }
      let d : X ⟶ P := ⟨AlgHom.id S.A X.algebra,
        dlinear⟩
      let a : P ⟶ X := ⟨AlgHom.id S.A X.algebra, pairAdd S X.algebra X.module⟩
      have hcomp : d ≫ a = scalarHom S X (b + c) := by
        apply AlgebraModulePair.Hom.ext
        · rfl
        · intro n
          change b • n + c • n = (b + c) • n
          rw [add_smul]
      have hp₁ : d ≫ ⟨AlgHom.id S.A X.algebra, LinearMap.fst X.algebra X.module X.module⟩ =
          scalarHom S X b := by
        apply AlgebraModulePair.Hom.ext
        · rfl
        · intro n
          rfl
      have hp₂ : d ≫ ⟨AlgHom.id S.A X.algebra, LinearMap.snd X.algebra X.module X.module⟩ =
          scalarHom S X c := by
        apply AlgebraModulePair.Hom.ext
        · rfl
        · intro n
          rfl
      calc
        secondScalarAction S.A S.F X x (b + c) =
            (tangentFunctor S.A S.F).map (scalarHom S X (b + c)) x := rfl
        _ = (tangentFunctor S.A S.F).map (d ≫ a) x := by rw [hcomp]
        _ = (tangentFunctor S.A S.F).map a ((tangentFunctor S.A S.F).map d x) := by
              rw [(tangentFunctor S.A S.F).map_comp]
        _ = (tangentFunctor S.A S.F).map (scalarHom S X b) x +
              (tangentFunctor S.A S.F).map (scalarHom S X c) x := by
              rw [tangentMap_add_components S X.algebra X.module,
                ← (tangentFunctor S.A S.F).map_comp, hp₁,
                ← (tangentFunctor S.A S.F).map_comp, hp₂]
    zero_smul := by
      intro x
      change (tangentFunctor S.A S.F).map (scalarHom S X 0) x = 0
      have hzero : (scalarHom S X 0).linear = 0 := by
        ext n
        change (0 : X.algebra) • n = 0
        exact zero_smul X.algebra n
      exact congrArg (fun g => g x)
        (tangentFunctor_map_eq_zero S.A S.F (scalarHom S X 0) hzero)
    }
  exact ⟨m, fun _ _ => rfl⟩

/-- Tangent maps commute with the second scalar action, semilinearly over
their maps of base algebras. -/
@[stacks 06ZB "second_module_structure"]
theorem secondScalarAction_naturality {X Y : AlgebraModulePair.{v} S.A}
    (f : X ⟶ Y) (x : tangentModule S.A S.F X) (b : X.algebra) :
    (tangentFunctor S.A S.F).map f (secondScalarAction S.A S.F X x b) =
      secondScalarAction S.A S.F Y ((tangentFunctor S.A S.F).map f x) (f.base b) := by
  calc
    (tangentFunctor S.A S.F).map f
        ((tangentFunctor S.A S.F).map (scalarHom S X b) x) =
      (tangentFunctor S.A S.F).map (scalarHom S X b ≫ f) x := by
        rw [(tangentFunctor S.A S.F).map_comp]
    _ = (tangentFunctor S.A S.F).map (f ≫ scalarHom S Y (f.base b)) x := by
        have hf : scalarHom S X b ≫ f = f ≫ scalarHom S Y (f.base b) := by
          apply AlgebraModulePair.Hom.ext
          · ext a
            show f.base (AlgHom.id S.A X.algebra a) =
              (AlgHom.id S.A Y.algebra) (f.base a)
            simp
          · intro n
            show f.linear (b • n) = f.base b • f.linear n
            exact f.linear.map_smulₛₗ b n
        exact congrArg (fun g => (tangentFunctor S.A S.F).map g x) hf
    _ = (tangentFunctor S.A S.F).map (scalarHom S Y (f.base b))
          ((tangentFunctor S.A S.F).map f x) := by
        rw [(tangentFunctor S.A S.F).map_comp]

end

section

open AdequateFunctor


universe u v w

private lemma moduleValueMap_id_apply (A : Type u) [CommRing A]
    (F : PresheafOfModules.{w} (AdequateFunctor.algebraStructurePresheaf.{v} A))
    (B : Type v) [CommRing B] [Algebra A B]
    (y : AdequateFunctor.moduleValue A F B) :
    AdequateFunctor.moduleValueMap A F (AlgHom.id A B) y = y := by
  show F.restrictₛₗ ((CommAlgCat.ofHom (AlgHom.id A B)).op.op) y = y
  rw [PresheafOfModules.restrictₛₗ_apply]
  have h : (CommAlgCat.ofHom (AlgHom.id A B)).op.op =
      CategoryTheory.CategoryStruct.id
        (Opposite.op (Opposite.op (CommAlgCat.of A B))) := by
    simp [CommAlgCat.ofHom_id]
  rw [h, F.map_id]
  show (ModuleCat.restrictScalarsId'App (RingHom.id B) rfl
    (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))).inv y = y
  rfl

/-- The canonical tangent multiplication map is linear for the second
`B`-module structure on the tangent module. -/
@[stacks 06ZB "multiplication_map_linear", stacks 06ZC]
theorem tangentMultiplication_smul_second (S : RightExactTangentFunctor.{u, v, w})
    (X : AlgebraModulePair.{v} S.A) (b : X.algebra)
    (t : TensorProduct X.algebra X.module (moduleValue S.A S.F X.algebra)) :
    (secondModuleStructure S X).val.toDistribMulAction.toSMul.smul b
        (tangentMultiplication S.A S.F X t) =
      tangentMultiplication S.A S.F X (b • t) := by
  let f : X ⟶ X :=
    { base := AlgHom.id S.A X.algebra
      linear := LinearMap.lsmul X.algebra X.module b }
  have hmap :
      TensorProduct.map f.linear (moduleValueMap S.A S.F f.base) t = b • t := by
    induction t using TensorProduct.induction_on with
    | zero => change (0 : TensorProduct X.algebra X.module
      (moduleValue S.A S.F X.algebra)) = 0; rfl
    | tmul n y =>
        rw [TensorProduct.map_tmul, TensorProduct.smul_tmul']
        show (b • n) ⊗ₜ[X.algebra]
          (moduleValueMap S.A S.F (AlgHom.id S.A X.algebra) y) = _
        rw [moduleValueMap_id_apply S.A S.F X.algebra y]
    | add x y hx hy =>
        rw [map_add, smul_add, hx, hy]
  rw [(secondModuleStructure S X).property b
    (tangentMultiplication S.A S.F X t)]
  rw [show AdequateFunctor.secondScalarAction S.A S.F X
      (tangentMultiplication S.A S.F X t) b =
      (tangentFunctor S.A S.F).map f (tangentMultiplication S.A S.F X t) by
        rfl]
  rw [tangentMultiplication_naturality S.A S.F f t]
  rw [hmap]

end

end AdequateFunctor

end

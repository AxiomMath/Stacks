module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Flat.Lazard

/-!
# An additive functor commuting with filtered colimits, on a flat module

Let `A` be a commutative ring and `F` an additive functor from `A`-modules to abelian groups,
and suppose that `F(A)` carries an `A`-module structure for which multiplication by `a` is
`F` of multiplication by `a`.  For every `A`-module `M` there is a canonical map
`M ⊗_A F(A) ⟶ F(M)`, sending `m ⊗ x` to `F(a ↦ a m)(x)`.  It is bijective when `M` is free of
finite rank, by additivity of `F`; and when `F` commutes with filtered colimits, it is bijective
for every flat `M`, because a flat module is a filtered colimit of free modules of finite rank
(Lazard's theorem, [Stacks, Tag 058G]).  This is the algebraic core of the flat base change
theorem for cohomology, [Stacks, Tag 073K].

The values of `F` are allowed to live in a universe larger than that of the modules, which is
the situation of the cohomology of sheaves on a site whose objects are larger than its
morphisms.

## Main definitions

* `CategoryTheory.Functor.unitObjModule`: the `A`-module structure on `F(A)` by functoriality.
* `CategoryTheory.Functor.tensorUnitComparison`: the map `M ⊗_A F(A) ⟶ F(M)`.

## Main results

* `CategoryTheory.Functor.tensorUnitComparison_naturality`: it is natural in `M`.
* `CategoryTheory.Functor.bijective_tensorUnitComparison_of_free_finite`: it is bijective for
  `M` free of finite rank.
* `CategoryTheory.Functor.bijective_tensorUnitComparison_of_flat`: it is bijective for `M` flat,
  if `F` commutes with filtered colimits.

## References

* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe v u

namespace CategoryTheory.Functor

/-- The `A`-module structure on `F(A)` through functoriality: `a` acts as `F` of
multiplication by `a`. -/
@[instance_reducible] def unitObjModule {A : Type u} [CommRing A]
    (F : ModuleCat.{u} A ⥤ AddCommGrpCat.{max u v}) [F.Additive] :
    Module A (F.obj (ModuleCat.of A A)) where
  smul b x := F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A b)) x
  one_smul x := by
    have h : ModuleCat.ofHom (LinearMap.toSpanSingleton A A 1) = 𝟙 _ :=
      ModuleCat.hom_ext (LinearMap.ext fun b => mul_one b)
    change F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A 1)) x = x
    rw [h, F.map_id]
    rfl
  mul_smul b c x := by
    have h : ModuleCat.ofHom (LinearMap.toSpanSingleton A A (b * c)) =
        ModuleCat.ofHom (LinearMap.toSpanSingleton A A c) ≫
          ModuleCat.ofHom (LinearMap.toSpanSingleton A A b) :=
      ModuleCat.hom_ext (LinearMap.ext fun a => by
        change a * (b * c) = a * c * b
        ring)
    change F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A (b * c))) x =
      F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A b))
        (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A c)) x)
    rw [h, F.map_comp]
    rfl
  smul_add b x y := (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A b))).hom.map_add x y
  smul_zero b := (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A b))).hom.map_zero
  add_smul b c x := by
    have h : ModuleCat.ofHom (LinearMap.toSpanSingleton A A (b + c)) =
        ModuleCat.ofHom (LinearMap.toSpanSingleton A A b) +
          ModuleCat.ofHom (LinearMap.toSpanSingleton A A c) :=
      ModuleCat.hom_ext (LinearMap.ext fun a => mul_add a b c)
    change F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A (b + c))) x =
      F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A b)) x +
        F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A c)) x
    rw [h, F.map_add]
    rfl
  zero_smul x := by
    have h : ModuleCat.ofHom (LinearMap.toSpanSingleton A A 0) = 0 :=
      ModuleCat.hom_ext (LinearMap.ext fun a => mul_zero a)
    change F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A 0)) x = 0
    rw [h, F.map_zero]
    rfl

/-- `a` acts on `F(A)` as `F` of multiplication by `a`. -/
theorem unitObjModule_smul {A : Type u} [CommRing A]
    (F : ModuleCat.{u} A ⥤ AddCommGrpCat.{max u v}) [F.Additive]
    (b : A) (x : F.obj (ModuleCat.of A A)) :
    letI := unitObjModule F
    b • x = F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A b)) x := rfl


variable {A : Type u} [CommRing A] (F : ModuleCat.{u} A ⥤ AddCommGrpCat.{max u v}) [F.Additive]
  [Module A (F.obj (ModuleCat.of A A))]
  (hF : ∀ (a : A) (x : F.obj (ModuleCat.of A A)),
    F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a)) x = a • x)

/-- The canonical map `M ⊗_A F(A) ⟶ F(M)`, `m ⊗ x ↦ F(a ↦ a m)(x)`. -/
def tensorUnitComparison (M : ModuleCat.{u} A) : M ⊗[A] F.obj (ModuleCat.of A A) →+ F.obj M := by
  let f : M →+ F.obj (ModuleCat.of A A) →+ F.obj M :=
    { toFun := fun m => (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))).hom
      map_zero' := by
        have hz : ModuleCat.ofHom (LinearMap.toSpanSingleton A M 0) = 0 := by
          ext; simp
        rw [hz, F.map_zero]
        rfl
      map_add' := by
        intro m n
        have ha : ModuleCat.ofHom (LinearMap.toSpanSingleton A M (m + n)) =
            ModuleCat.ofHom (LinearMap.toSpanSingleton A M m) +
              ModuleCat.ofHom (LinearMap.toSpanSingleton A M n) :=
          ModuleCat.hom_ext (LinearMap.ext fun b => smul_add b m n)
        rw [ha, F.map_add]
        rfl }
  refine TensorProduct.liftAddHom f ?_
  intro b m x
  have he : ModuleCat.ofHom (LinearMap.toSpanSingleton A M (b • m)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton A A b) ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton A M m) :=
    ModuleCat.hom_ext (LinearMap.ext fun a => smul_smul a b m)
  change F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M (b • m))) x =
    F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)) (b • x)
  rw [he, F.map_comp]
  change F.map _ (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A b)) x) = _
  rw [hF]

/-- The comparison `M ⊗_A F(A) ⟶ F(M)` sends `m ⊗ x` to `F(a ↦ a m)(x)`. -/
@[simp]
theorem tensorUnitComparison_tmul (M : ModuleCat.{u} A) (m : M)
    (x : F.obj (ModuleCat.of A A)) :
    tensorUnitComparison F hF M (m ⊗ₜ[A] x) =
      F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)) x := rfl

/-- Composing `a ↦ a m` with a linear map `f` gives `a ↦ a f(m)`. -/
private lemma ofHom_toSpanSingleton_comp {M N : ModuleCat.{u} A} (f : M ⟶ N) (m : M) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton A M m) ≫ f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton A N (f m)) :=
  ModuleCat.hom_ext (LinearMap.comp_toSpanSingleton f.hom m)

/-- Mapping a tensor product along `f` and then `g` in the first factor is mapping along
`f ≫ g`. -/
private lemma map_hom_id_map_hom_id {M N P : ModuleCat.{u} A} (f : M ⟶ N) (g : N ⟶ P)
    {T : Type*} [AddCommGroup T] [Module A T] (z : M ⊗[A] T) :
    TensorProduct.map g.hom LinearMap.id (TensorProduct.map f.hom LinearMap.id z) =
      TensorProduct.map (f ≫ g).hom LinearMap.id z := by
  rw [TensorProduct.map_map, ModuleCat.hom_comp, LinearMap.id_comp]

/-- The comparison `M ⊗_A F(A) ⟶ F(M)` is natural in `M`. -/
theorem tensorUnitComparison_naturality {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    (z : M ⊗[A] F.obj (ModuleCat.of A A)) :
    tensorUnitComparison F hF N (TensorProduct.map φ.hom LinearMap.id z) =
      F.map φ (tensorUnitComparison F hF M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, _root_.map_add, hx, hy, _root_.map_add]
  | tmul m t =>
    rw [TensorProduct.map_tmul, tensorUnitComparison_tmul, tensorUnitComparison_tmul]
    rw [← ofHom_toSpanSingleton_comp, F.map_comp]
    rfl

private lemma addCommGrp_sum_apply {ι : Type*} {M N : AddCommGrpCat}
    (s : Finset ι) (f : ι → (M ⟶ N)) (x : M) :
    (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

/-- **The comparison is bijective on a free module of finite rank**, by additivity of `F`. -/
theorem bijective_tensorUnitComparison_of_free_finite (M : ModuleCat.{u} A) [Module.Free A M]
    [Module.Finite A M] : Function.Bijective (tensorUnitComparison F hF M) := by
  let b := Module.Free.chooseBasis A M
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex A M)
  let g (x : F.obj M) : M ⊗[A] F.obj (ModuleCat.of A A) :=
    ∑ j, b j ⊗ₜ[A] (F.map (ModuleCat.ofHom (b.coord j))) x
  have hgadd (x y : F.obj M) : g (x + y) = g x + g y := by
    simp [g, TensorProduct.tmul_add, Finset.sum_add_distrib]
  have hsum : (∑ j, (ModuleCat.ofHom (b.coord j) ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton A M (b j)))) = 𝟙 M := by
    ext m
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact b.sum_repr m
  have hr (x : F.obj M) : tensorUnitComparison F hF M (g x) = x := by
    calc
      tensorUnitComparison F hF M (g x) =
          ∑ j, (F.map (ModuleCat.ofHom (b.coord j) ≫
            ModuleCat.ofHom (LinearMap.toSpanSingleton A M (b j)))) x := by
        rw [_root_.map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [tensorUnitComparison_tmul, F.map_comp]; rfl
      _ = (F.map (∑ j, ModuleCat.ofHom (b.coord j) ≫
            ModuleCat.ofHom (LinearMap.toSpanSingleton A M (b j)))) x := by
        rw [F.map_sum, addCommGrp_sum_apply]
      _ = x := by rw [hsum, F.map_id]; rfl
  have hl (z : M ⊗[A] F.obj (ModuleCat.of A A)) : g (tensorUnitComparison F hF M z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp [g]
    | add x y hx hy => rw [_root_.map_add, hgadd, hx, hy]
    | tmul m t =>
      rw [tensorUnitComparison_tmul]
      show (∑ j, b j ⊗ₜ[A] (F.map (ModuleCat.ofHom (b.coord j)))
        (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)) t)) = m ⊗ₜ[A] t
      have he (j : Module.Free.ChooseBasisIndex A M) :
          ModuleCat.ofHom (LinearMap.toSpanSingleton A M m) ≫ ModuleCat.ofHom (b.coord j) =
            ModuleCat.ofHom (LinearMap.toSpanSingleton A A (b.coord j m)) :=
        ofHom_toSpanSingleton_comp (ModuleCat.ofHom (b.coord j)) m
      calc
        (∑ j, b j ⊗ₜ[A] (F.map (ModuleCat.ofHom (b.coord j)))
            (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)) t)) =
            ∑ j, b j ⊗ₜ[A] ((b.coord j m) • t) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← AddCommGrpCat.comp_apply, ← F.map_comp, he, hF]
        _ = (∑ j, (b.coord j m) • b j) ⊗ₜ[A] t := by
          simp only [TensorProduct.tmul_smul, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
        _ = m ⊗ₜ[A] t := congrArg (fun m : M => m ⊗ₜ[A] t) (b.sum_repr m)
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

/-- The comparison on the colimit point of a cocone, at an element coming from the tensor
product of one of the terms. -/
private lemma tensorUnitComparison_map_cocone {J : Type*} [Category J] {D : J ⥤ ModuleCat.{u} A}
    (c : Cocone D) (j : J) (z : D.obj j ⊗[A] F.obj (ModuleCat.of A A)) :
    tensorUnitComparison F hF c.pt (TensorProduct.map (c.ι.app j).hom LinearMap.id z) =
      (F.mapCocone c).ι.app j (tensorUnitComparison F hF (D.obj j) z) :=
  tensorUnitComparison_naturality F hF (c.ι.app j) z

/-- **The comparison is bijective on a flat module**, if `F` commutes with filtered colimits: a
flat module is a filtered colimit of free modules of finite rank by Lazard's theorem
([Stacks, Tag 058G]), the comparison is bijective on each of them, and both sides commute with
the colimit. -/
theorem bijective_tensorUnitComparison_of_flat [PreservesFilteredColimitsOfSize.{u, u} F]
    (M : ModuleCat.{u} A) [Module.Flat A M] :
    Function.Bijective (tensorUnitComparison F hF M) := by
  obtain ⟨ι, _, _, _, _, G, _, _, f, _, hfree, hfinite, ⟨e⟩⟩ :=
    (flat_iff_directLimit_free_finite (R := A) M).mp inferInstance
  let D := ModuleCat.directLimitDiagram G f
  let c := ModuleCat.directLimitCocone G f
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  have hFc : IsColimit (F.mapCocone c) :=
    isColimitOfPreserves F (ModuleCat.directLimitIsColimit G f)
  have hD (i : ι) : Function.Bijective (tensorUnitComparison F hF (D.obj i)) := by
    have : Module.Free A (D.obj i) := hfree i
    have : Module.Finite A (D.obj i) := hfinite i
    exact bijective_tensorUnitComparison_of_free_finite F hF (D.obj i)
  -- every element of the tensor product of the colimit comes from one term
  have hrep (w : c.pt ⊗[A] F.obj (ModuleCat.of A A)) :
      ∃ (i : ι) (z : D.obj i ⊗[A] F.obj (ModuleCat.of A A)),
        TensorProduct.map (c.ι.app i).hom LinearMap.id z = w := by
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨Classical.arbitrary ι, 0, _root_.map_zero _⟩
    | tmul m t =>
      obtain ⟨i, g, rfl⟩ := Module.DirectLimit.exists_of m
      exact ⟨i, g ⊗ₜ[A] t, rfl⟩
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨i₁, z₁, rfl⟩ := h₁
      obtain ⟨i₂, z₂, rfl⟩ := h₂
      obtain ⟨k, hk₁, hk₂⟩ := exists_ge_ge i₁ i₂
      refine ⟨k, TensorProduct.map (D.map (homOfLE hk₁)).hom LinearMap.id z₁ +
        TensorProduct.map (D.map (homOfLE hk₂)).hom LinearMap.id z₂, ?_⟩
      rw [_root_.map_add, map_hom_id_map_hom_id, map_hom_id_map_hom_id, c.w, c.w]
  have hL : Function.Bijective (tensorUnitComparison F hF c.pt) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro w hw
      obtain ⟨i, z, rfl⟩ := hrep w
      rw [tensorUnitComparison_map_cocone] at hw
      obtain ⟨k, a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq _ hFc
        (tensorUnitComparison F hF (D.obj i) z) (0 : (D ⋙ F).obj i)
        (hw.trans (_root_.map_zero _).symm)
      have h0 : tensorUnitComparison F hF (D.obj k)
          (TensorProduct.map (D.map a).hom LinearMap.id z) = 0 := by
        rw [tensorUnitComparison_naturality]
        exact hab.trans (_root_.map_zero _)
      have hz : TensorProduct.map (D.map a).hom LinearMap.id z = 0 :=
        (injective_iff_map_eq_zero _).mp (hD k).1 _ h0
      rw [← c.w a, ← map_hom_id_map_hom_id, hz, _root_.map_zero]
    · intro y
      obtain ⟨i, x, rfl⟩ := Concrete.isColimit_exists_rep _ hFc y
      obtain ⟨z, rfl⟩ := (hD i).2 x
      exact ⟨_, tensorUnitComparison_map_cocone F hF c i z⟩
  -- transport along `M ≅ colim`
  let E : c.pt ≅ M := e.toModuleIso
  have key (z : M ⊗[A] F.obj (ModuleCat.of A A)) : tensorUnitComparison F hF M z =
      F.map E.hom (tensorUnitComparison F hF c.pt
        (TensorProduct.map E.inv.hom LinearMap.id z)) := by
    rw [← tensorUnitComparison_naturality, map_hom_id_map_hom_id, E.inv_hom_id, ModuleCat.hom_id,
      TensorProduct.map_id, LinearMap.id_apply]
  have hE : Function.Bijective (TensorProduct.map E.inv.hom
      (LinearMap.id (R := A) (M := F.obj (ModuleCat.of A A)))) :=
    (TensorProduct.congr (e.symm) (LinearEquiv.refl A _)).bijective
  have hFE : Function.Bijective (F.map E.hom) :=
    (ConcreteCategory.isIso_iff_bijective (F.map E.hom)).mp inferInstance
  have : ⇑(tensorUnitComparison F hF M) =
      F.map E.hom ∘ tensorUnitComparison F hF c.pt ∘ TensorProduct.map E.inv.hom LinearMap.id :=
    funext key
  rw [this]
  exact hFE.comp (hL.comp hE)

end CategoryTheory.Functor

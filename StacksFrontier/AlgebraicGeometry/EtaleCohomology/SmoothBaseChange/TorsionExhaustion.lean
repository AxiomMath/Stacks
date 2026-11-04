module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules

/-!
# An abelian étale sheaf with torsion stalks is the union of its `n`-torsion

Let `S` be a scheme and `F` an abelian sheaf on the small étale site of a scheme `T`, all of
whose stalks at geometric points are torsion of orders invertible on `S`. The smooth base change
theorem (Stacks, Theorem 0EYU) writes `F = colim F[n]` over the integers `n ≥ 1` invertible on
`S`, where `F[n]` is the subsheaf of sections annihilated by `n`. This file realizes that colimit
over `ℕ`: the products `N k` of the integers `1 ≤ m ≤ k` invertible on `S` form a chain under
divisibility which every integer invertible on `S` divides from some point on, and the subsheaves
`F[N k]` exhaust `F`.

## Main definitions

* `Stacks.EtaleCohomology.SmoothBaseChange.invertibleIndex` — the product `N k`.
* `Stacks.EtaleCohomology.SmoothBaseChange.torsionDiagram` — the chain `k ↦ F[N k]`.
* `Stacks.EtaleCohomology.SmoothBaseChange.torsionCocone` — the inclusions `F[N k] ⟶ F`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isColimitTorsionCocone` — `F` is the colimit of the
  chain, when its stalks are torsion of orders invertible on `S`.
* `Stacks.EtaleCohomology.SmoothBaseChange.isIso_app_of_isColimit` — a natural transformation
  between functors preserving a colimit is invertible at its point if it is at each object of
  the diagram.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

open Classical in
/-- The product of the integers `1 ≤ m ≤ k` invertible on `S`. -/
def invertibleIndex (S : Scheme.{u}) (k : ℕ) : ℕ :=
  ∏ m ∈ (Finset.range (k + 1)).filter (fun m : ℕ => 0 < m ∧ IsUnit ((m : ℤ) : Γ(S, ⊤))), m

/-- The product `invertibleIndex S k` is positive. -/
theorem invertibleIndex_pos (S : Scheme.{u}) (k : ℕ) : 0 < invertibleIndex S k := by
  classical
  unfold invertibleIndex
  exact Finset.prod_pos fun m hm => (Finset.mem_filter.1 hm).2.1

/-- The product `invertibleIndex S k` is invertible on `S`. -/
theorem isUnit_invertibleIndex (S : Scheme.{u}) (k : ℕ) :
    IsUnit ((invertibleIndex S k : ℤ) : Γ(S, ⊤)) := by
  classical
  unfold invertibleIndex
  push_cast
  exact (IsUnit.prod_iff (M := Γ(S, ⊤))).2 fun m hm => (Finset.mem_filter.1 hm).2.2

/-- For `k ≤ k'`, `invertibleIndex S k` divides `invertibleIndex S k'`. -/
theorem invertibleIndex_dvd_invertibleIndex (S : Scheme.{u}) {k k' : ℕ} (h : k ≤ k') :
    invertibleIndex S k ∣ invertibleIndex S k' := by
  classical
  unfold invertibleIndex
  refine Finset.prod_dvd_prod_of_subset _ _ _ fun m hm => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hm ⊢
  exact ⟨by omega, hm.2.1, hm.2.2⟩

/-- A positive integer `m` invertible on `S` divides `invertibleIndex S m`. -/
theorem dvd_invertibleIndex (S : Scheme.{u}) {m : ℕ} (hm : 0 < m)
    (hu : IsUnit ((m : ℤ) : Γ(S, ⊤))) : m ∣ invertibleIndex S m := by
  classical
  unfold invertibleIndex
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hm, hu⟩)

/-! ### The chain of torsion subsheaves -/

section Diagram

variable {C : Type*} [Category* C] [Preadditive C] [HasKernels C] (F : C)

/-- The inclusion `F[a] ⟶ F[b]` of the `a`-torsion into the `b`-torsion for `a ∣ b`. -/
def torsionInclusion {a b : ℤ} (hab : a ∣ b) : kernel (a • 𝟙 F) ⟶ kernel (b • 𝟙 F) :=
  kernel.lift _ (kernel.ι _) (by
    obtain ⟨c, rfl⟩ := hab
    rw [mul_comm, mul_zsmul, Preadditive.comp_zsmul, kernel.condition, zsmul_zero])

/-- The inclusion `F[a] ⟶ F[b]` commutes with the inclusions of `F[a]` and `F[b]` into `F`. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_ι {a b : ℤ} (hab : a ∣ b) :
    torsionInclusion F hab ≫ kernel.ι (b • 𝟙 F) = kernel.ι (a • 𝟙 F) :=
  kernel.lift_ι _ _ _

variable (S : Scheme.{u})

/-- **The chain `k ↦ F[N k]`** of the subobjects annihilated by the products `N k` of the
integers `1 ≤ m ≤ k` invertible on `S`, indexed by `ℕ` lifted to the universe `u + 1`. -/
def torsionDiagram : ULift.{u + 1} ℕ ⥤ C where
  obj k := kernel ((invertibleIndex S k.down : ℤ) • 𝟙 F)
  map {k k'} φ := torsionInclusion F (Int.natCast_dvd_natCast.2
    (invertibleIndex_dvd_invertibleIndex S (ULift.down_le.2 (leOfHom φ))))
  map_id _ := by
    ext
    simp
  map_comp _ _ := by
    ext
    simp

/-- The inclusions `F[N k] ⟶ F`. -/
def torsionCocone : Cocone (torsionDiagram F S) where
  pt := F
  ι :=
    { app _ := kernel.ι _
      naturality _ _ φ := (torsionInclusion_ι F (Int.natCast_dvd_natCast.2
          (invertibleIndex_dvd_invertibleIndex S (ULift.down_le.2 (leOfHom φ))))).trans
          (Category.comp_id _).symm }

end Diagram

/-! ### Natural transformations at a colimit -/

/-- **A natural transformation between functors preserving a colimit is invertible at its point
if it is invertible at each object of the diagram.** -/
theorem isIso_app_of_isColimit {J C D : Type*} [Category* J] [Category* C] [Category* D]
    {K : J ⥤ C} {c : Cocone K} (hc : IsColimit c) {Φ Ψ : C ⥤ D} (α : Φ ⟶ Ψ)
    [PreservesColimit K Φ] [PreservesColimit K Ψ] (h : ∀ j, IsIso (α.app (K.obj j))) :
    IsIso (α.app c.pt) := by
  let hΦ := isColimitOfPreserves Φ hc
  have : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) := h
  have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  let e := IsColimit.coconePointsIsoOfNatIso hΦ (isColimitOfPreserves Ψ hc)
    (asIso (Functor.whiskerLeft K α))
  have he : α.app c.pt = e.hom := hΦ.hom_ext fun j => by
    rw [IsColimit.coconePointsIsoOfNatIso_hom, IsColimit.ι_map]
    exact α.naturality (c.ι.app j)
  rw [he]
  infer_instance

/-! ### The chain exhausts a sheaf with torsion stalks -/

section Exhaustion

/-- A section of an abelian sheaf killed by an endomorphism is a section of its kernel. -/
theorem exists_kernel_section {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J Ab.{u + 1}] {F : Sheaf J Ab.{u + 1}} (a : F ⟶ F) {W : C}
    (z : F.obj.obj (op W)) (hz : a.hom.app (op W) z = 0) :
    ∃ y : (kernel a).obj.obj (op W), (kernel.ι a).hom.app (op W) y = z := by
  let E := sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation Cᵒᵖ Ab.{u + 1}).obj (op W)
  refine ⟨(PreservesKernel.iso E a).inv ((AddCommGrpCat.kernelIsoKer (E.map a)).inv ⟨z, hz⟩), ?_⟩
  show (E.map (kernel.ι a)) ((PreservesKernel.iso E a).inv
    ((AddCommGrpCat.kernelIsoKer (E.map a)).inv ⟨z, hz⟩)) = z
  rw [← CategoryTheory.comp_apply, PreservesKernel.iso_inv_ι E a, ← CategoryTheory.comp_apply,
    AddCommGrpCat.kernelIsoKer_inv_comp_ι (E.map a)]
  rfl

variable (S : Scheme.{u}) {T : Scheme.{u}} (F : Sheaf T.smallEtaleTopology Ab.{u + 1})

/-- **An abelian sheaf whose stalks are torsion of orders invertible on `S` is the colimit of its
subsheaves `F[N k]`.** The comparison from the colimit is a monomorphism, filtered colimits of
abelian sheaves being exact, and an epimorphism: a section of `F` has, at each point, a germ
killed by an integer `n` invertible on `S`, hence is killed by `n` on an étale neighbourhood of
that point, and so lies in `F[N n]` there. -/
noncomputable def isColimitTorsionCocone
    (hF : ∀ (t : GeometricPoint T) (a : (smallEtaleStalkAb t.hom).obj F),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0) :
    IsColimit (torsionCocone F S) := by
  let D := torsionDiagram F S
  let φ := (colimit.isColimit D).desc (torsionCocone F S)
  have hφ : ∀ k, colimit.ι D k ≫ φ = kernel.ι _ := fun k => (colimit.isColimit D).fac _ k
  have : ∀ k, Mono ((torsionCocone F S).ι.app k) := fun k =>
    (inferInstance : Mono (kernel.ι (((invertibleIndex S k.down : ℤ)) • 𝟙 F)))
  have : Mono (torsionCocone F S).ι := NatTrans.mono_of_mono_app _
  have hmono : Mono φ :=
    colim.map_mono' (torsionCocone F S).ι (colimit.isColimit D) (isColimitConstCocone _ F) φ
      fun k => (hφ k).trans (Category.comp_id _).symm
  have hloc : Presheaf.IsLocallySurjective T.smallEtaleTopology φ.hom := by
    constructor
    intro U x₀
    let x : F.obj.obj (op U) := x₀
    have hpt : ∀ w : U.left, ∃ (W : T.Etale) (g : W ⟶ U) (n : ℕ), 0 < n ∧
        IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ w ∈ Set.range g.left ∧ (n : ℤ) • F.obj.map g.op x = 0 := by
      intro w
      let y := U.left.algClosedPointHom w
      let t : GeometricPoint T := ⟨_, y ≫ U.hom⟩
      let v : (pointSmallEtale t.hom).fiber.obj U := Over.homMk y rfl
      obtain ⟨n, hn, hu, hz⟩ := hF t ((pointSmallEtale t.hom).toPresheafFiber U v F.obj x)
      have hz' : (pointSmallEtale t.hom).toPresheafFiber U v F.obj ((n : ℤ) • x) =
          (pointSmallEtale t.hom).toPresheafFiber U v F.obj 0 := by
        rwa [((pointSmallEtale t.hom).toPresheafFiber U v F.obj).hom.map_zsmul,
          ((pointSmallEtale t.hom).toPresheafFiber U v F.obj).hom.map_zero, natCast_zsmul]
      have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget Ab.{u + 1}) :=
        preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u}
          (CategoryTheory.forget Ab.{u + 1})
      obtain ⟨W, g, w', hw', hg⟩ :=
        ((pointSmallEtale t.hom).toPresheafFiber_eq_iff' (P := F.obj) U v _ _).1 hz'
      obtain ⟨pt⟩ : Nonempty (Spec (.of (AlgebraicClosure (U.left.residueField w)))) :=
        inferInstance
      refine ⟨W, g, n, hn, hu, ⟨(w'.left : Spec (.of _) ⟶ W.left) pt, ?_⟩, ?_⟩
      · change (w'.left ≫ g.left) pt = w
        rw [show w'.left ≫ g.left = y from congrArg CommaMorphism.left hw']
        exact U.left.algClosedPointHom_apply w _
      · rw [← (F.obj.map g.op).hom.map_zsmul]
        exact hg.trans ((F.obj.map g.op).hom.map_zero)
    choose W g n hn hu hw hz using hpt
    refine T.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff g).2 (Set.eq_univ_of_forall fun w =>
        Set.mem_iUnion.2 ⟨w, hw w⟩))
    rintro V _ ⟨_, b, _, ⟨w⟩, rfl⟩
    refine (Presheaf.imageSieve φ.hom x).downward_closed ?_ b
    let k : ULift.{u + 1} ℕ := ⟨n w⟩
    obtain ⟨c, hc⟩ : (n w : ℤ) ∣ (invertibleIndex S (n w) : ℤ) :=
      Int.natCast_dvd_natCast.2 (dvd_invertibleIndex S (hn w) (hu w))
    obtain ⟨y₀, hy₀⟩ := exists_kernel_section (((invertibleIndex S (n w) : ℤ)) • 𝟙 F)
      (F.obj.map (g w).op x) (by
        rw [Stacks.Cohomology.ZModSheaf.zsmul_app_apply]
        change ((invertibleIndex S (n w) : ℤ)) • (F.obj.map (g w).op x) = 0
        rw [hc, mul_comm, mul_zsmul, hz w, zsmul_zero])
    exact ⟨(colimit.ι D k).hom.app (op (W w)) y₀,
      (congrArg (fun m => m.hom.app (op (W w)) y₀) (hφ k)).trans hy₀⟩
  have hepi : Epi φ := by
    have : Sheaf.IsLocallySurjective φ := hloc
    infer_instance
  have : IsIso φ := isIso_of_mono_of_epi φ
  exact IsColimit.ofPointIso (colimit.isColimit D)

end Exhaustion

end Stacks.EtaleCohomology.SmoothBaseChange

end

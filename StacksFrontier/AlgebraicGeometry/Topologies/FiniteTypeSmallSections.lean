module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.Logic.Small.Set
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Sheaves of modules of finite type have small modules of sections

Let `R` be a sheaf of rings on an essentially `w`-small site, with `w`-small rings of sections,
and let `M` be a sheaf of `R`-modules of finite type, `PresheafOfModules.IsFiniteType`: some
family of objects covering the site carries, on each member, finitely many sections generating
`M` locally. Whatever the universe of the sections of `M`, each module of sections of `M` is then
`w`-small.

A section `t` of `M` over `V` is determined by its restrictions to the members of any covering
sieve, and on the covering sieve of the `W ⟶ V` over which `t` restricts to a linear
combination of restrictions of the local generators, these restrictions lie in a `w`-small set:
the linear combinations of the generators over the `w`-small set of representatives of the
members of the covering family, with coefficients in the `w`-small rings. Reading the
restrictions only along the `w`-small set of arrows out of a small model of the site, `t` is
determined by a `w`-small amount of data.

## Main results

* `SheafOfModules.small_sections_of_isFiniteType`: **the modules of sections of a sheaf of
  modules of finite type on an essentially small site are small.**
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **The modules of sections of a sheaf of modules of finite type are small**, on an
essentially `w`-small site whose rings of sections are `w`-small. -/
theorem small_sections_of_isFiniteType [EssentiallySmall.{w} C]
    [∀ X, Small.{w} (R.obj.obj X)] (M : SheafOfModules.{m} R)
    [hM : PresheafOfModules.IsFiniteType J M.val] (V : Cᵒᵖ) : Small.{w} (M.val.obj V) := by
  classical
  obtain ⟨I, U, hU, hgen⟩ := hM.exists_generators
  choose n s hs using hgen
  let ρ {W W' : C} (g : W' ⟶ W) := M.val.restrictₛₗ g.op
  have hρ {W W' W'' : C} (g : W' ⟶ W) (h : W'' ⟶ W') (x : M.val.obj (op W)) :
      ρ (h ≫ g) x = ρ h (ρ g x) := M.val.map_comp_apply _ _ _
  let e := equivSmallModel.{w} C
  let ι : SmallModel.{w} C → C := fun d ↦ e.inverse.obj d
  -- the representatives of the members of the covering family, with a chosen member each
  let T : Set (SmallModel.{w} C) := {d | ∃ i, Nonempty (ι d ≅ U i)}
  choose i₀ φ using fun d : T ↦ (show ∃ i, Nonempty (ι d ≅ U i) from d.2)
  -- the small set of linear combinations of restrictions of the chosen generators
  let A : (W : C) → Set (M.val.obj (op W)) := fun W ↦ Set.range
    (fun p : Σ (d : T), Σ (_ : W ⟶ U (i₀ d)), Fin (n (i₀ d)) → R.obj.obj (op W) ↦
      ∑ j, p.2.2 j • ρ p.2.1 (s (i₀ p.1) j))
  have hA (W : C) : Small.{w} ↥(insert (0 : M.val.obj (op W)) (A W)) := by
    have : ∀ d : T, Small.{w} (W ⟶ U (i₀ d)) := fun _ ↦ inferInstance
    infer_instance
  -- the set `A` is stable under restriction
  have hcomp {W W' W'' : C} (g : W' ⟶ W) (h : W'' ⟶ W') (x : M.val.obj (op W))
      (hx : ρ g x ∈ A W') : ρ (h ≫ g) x ∈ A W'' := by
    obtain ⟨⟨d, k, a⟩, hx⟩ := hx
    refine ⟨⟨d, h ≫ k, fun j ↦ R.obj.map h.op (a j)⟩, ?_⟩
    simp only [map_sum, map_smulₛₗ, hρ, ← hx]
  -- for each section, the sieve over which it restricts into `A` covers
  have hcov (W : C) (t : M.val.obj (op W)) :
      (⟨fun W' g ↦ ρ g t ∈ A W', fun {_ _} g hg h ↦ hcomp g h t hg⟩ : Sieve W) ∈ J W := by
    refine J.transitive (hU W) _ fun W' g hg ↦ ?_
    obtain ⟨i, ⟨g₀⟩⟩ := hg
    let d : T := ⟨e.functor.obj (U i), i, ⟨(e.unitIso.app (U i)).symm⟩⟩
    let g₁ : W' ⟶ U (i₀ d) := g₀ ≫ (e.unitIso.app (U i)).hom ≫ (φ d).some.hom
    obtain ⟨S, hS, hSgen⟩ := hs (i₀ d) W' g₁ (ρ g t)
    refine J.superset_covering (fun W'' g' hg' ↦ ?_) hS
    obtain ⟨a, ha⟩ := hSgen W'' g' hg'
    refine ⟨⟨d, g' ≫ g₁, a⟩, ?_⟩
    change ∑ j, a j • ρ (g' ≫ g₁) (s (i₀ d) j) = ρ (g' ≫ g) t
    rw [hρ g g']
    exact ha
  -- a section is determined by its restrictions into `A` along arrows out of the small model
  let Φ : M.val.obj V → ∀ p : Σ (d : SmallModel.{w} C), (ι d ⟶ V.unop),
      ↥(insert (0 : M.val.obj (op (ι p.1))) (A (ι p.1))) := fun t p ↦
    if h : ρ p.2 t ∈ A (ι p.1) then ⟨_, Set.mem_insert_of_mem _ h⟩
    else ⟨0, Set.mem_insert _ _⟩
  have hsheaf : Presieve.IsSheaf J (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type J _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf)
  have hinj : Function.Injective Φ := by
    intro t t' h
    let S₀ := J.intersection_covering (hcov V.unop t) (hcov V.unop t')
    refine (hsheaf _ S₀).isSeparatedFor.ext fun W g hg ↦ ?_
    obtain ⟨hg₁, hg₂⟩ := hg
    let ψ : ι (e.functor.obj W) ≅ W := (e.unitIso.app W).symm
    have key := congrArg Subtype.val (congrFun h ⟨e.functor.obj W, ψ.hom ≫ g⟩)
    simp only [Φ, dite_eq_left (hcomp _ _ t hg₁), dite_eq_left (hcomp _ _ t' hg₂)] at key
    have : ρ ψ.inv (ρ (ψ.hom ≫ g) t) = ρ ψ.inv (ρ (ψ.hom ≫ g) t') := by rw [key]
    rwa [← hρ, ← hρ, ← Category.assoc, ψ.inv_hom_id, Category.id_comp] at this
  exact small_of_injective hinj

end SheafOfModules

end

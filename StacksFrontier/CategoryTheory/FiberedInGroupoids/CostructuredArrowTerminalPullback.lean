module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoids

/-!
# Terminal arrows of a 1-morphism of categories fibred in groupoids, and fibre products

Let `p𝒳 : 𝒳 ⥤ 𝒞` and `p𝒴 : 𝒴 ⥤ 𝒞` be categories fibred in groupoids and `f : 𝒳 ⥤ 𝒴` a functor
over `𝒞`. For an object `y` of `𝒴`, a terminal object `t = (x₀, f x₀ ⟶ y)` of the comma category
`CostructuredArrow f y` is the fibre product `y ×_𝒴 𝒳` when the latter is representable, and this
file records the two facts about such terminal arrows that are read off in `𝒞`:

* **Their base square is cartesian.** For an arrow `φ : y ⟶ y'` and terminal arrows `t` at `y`
  and `t'` at `y'`, the arrow `k : x₀ ⟶ x₀'` induced by terminality lies over the base change of
  `p(φ)`: the square
  ```
    p(f x₀) --p(f k)--> p(f x₀')
       |                   |
    p(t)                 p(t')
       v                   v
     p(y) ----p(φ)----> p(y')
  ```
  is a pullback in `𝒞` (`CategoryTheory.isPullback_map_of_isTerminal_costructuredArrow`). The
  proof uses only the lifting properties of Stacks 003S, no representability.
* **They exist when `𝒳` and `𝒴` have terminal objects and `𝒞` has fibre products**: the terminal
  arrow at `y` lies over `p(y) ×_{p(y_⊤)} p(x_⊤)`
  (`CategoryTheory.exists_isTerminal_costructuredArrow`). This is the case of categories
  representable by objects of `𝒞`, i.e. 1-morphisms between algebraic stacks representable by
  schemes, which is the situation of Stacks 075P and Stacks 0765.

## Main results

* `CategoryTheory.isPullback_map_of_isTerminal_costructuredArrow`
* `CategoryTheory.exists_isTerminal_costructuredArrow`
* `CategoryTheory.isTerminalCostructuredArrowMkOfIsTerminal`: at a terminal object of `𝒴`, the
  terminal arrow is the one from the terminal object of `𝒳`.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₀ u₀ v₁ u₁ v₂ u₂

variable {𝒞 : Type u₀} [Category.{v₀} 𝒞] {𝒳 : Type u₁} [Category.{v₁} 𝒳]
  {𝒴 : Type u₂} [Category.{v₂} 𝒴]

/-- Every morphism of the base into the image of an object lifts, up to identifying its source
with the image of the lifted source. -/
theorem Functor.IsFiberedInGroupoids.exists_lift_eqToHom {p : 𝒳 ⥤ 𝒞}
    (hp : p.IsFiberedInGroupoids) {T : 𝒞} (x : 𝒳) (a : T ⟶ p.obj x) :
    ∃ (z : 𝒳) (hz : p.obj z = T) (α : z ⟶ x), p.map α = eqToHom hz ≫ a := by
  obtain ⟨z, α, hα⟩ := hp.exists_lift a x rfl
  refine ⟨z, IsHomLift.domain_eq p a α, α, ?_⟩
  rw [IsHomLift.fac' p a α, eqToHom_refl, Category.comp_id]

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)

/-- **The base square of terminal arrows is cartesian.** Let `f : 𝒳 ⥤ 𝒴` be a functor over `𝒞`
between categories fibred in groupoids, `φ : y ⟶ y'` an arrow of `𝒴`, and `t`, `t'` terminal
objects of `CostructuredArrow f y` and `CostructuredArrow f y'`. The arrow `k : t.left ⟶ t'.left`
induced by terminality of `t'` lies over the base change of `p(φ)` along `p(t')`. -/
theorem isPullback_map_of_isTerminal_costructuredArrow (hp𝒳 : p𝒳.IsFiberedInGroupoids)
    (hp𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) {y y' : 𝒴} (φ : y ⟶ y')
    {t : CostructuredArrow f y} (ht : IsTerminal t) {t' : CostructuredArrow f y'}
    (ht' : IsTerminal t') :
    IsPullback (p𝒴.map (f.map (ht'.from (CostructuredArrow.mk (t.hom ≫ φ))).left))
      (p𝒴.map t.hom) (p𝒴.map t'.hom) (p𝒴.map φ) := by
  subst hf
  let k : t.left ⟶ t'.left := (ht'.from (CostructuredArrow.mk (t.hom ≫ φ))).left
  have hk : f.map k ≫ t'.hom = t.hom ≫ φ := CostructuredArrow.w (ht'.from _)
  have sq : CommSq (p𝒴.map (f.map k)) (p𝒴.map t.hom) (p𝒴.map t'.hom) (p𝒴.map φ) :=
    ⟨by rw [← p𝒴.map_comp, hk, p𝒴.map_comp]⟩
  have key : ∀ s : PullbackCone (p𝒴.map t'.hom) (p𝒴.map φ),
      ∃ c : s.pt ⟶ p𝒴.obj (f.obj t.left), c ≫ p𝒴.map (f.map k) = s.fst ∧
        c ≫ p𝒴.map t.hom = s.snd ∧
        ∀ m : s.pt ⟶ p𝒴.obj (f.obj t.left), m ≫ p𝒴.map (f.map k) = s.fst →
          m ≫ p𝒴.map t.hom = s.snd → m = c := by
    intro s
    obtain ⟨z, hz, α, hα⟩ := hp𝒳.exists_lift_eqToHom t'.left s.fst
    replace hα : p𝒴.map (f.map α) = eqToHom hz ≫ s.fst := hα
    obtain ⟨β, ⟨hβ₁, hβ₂⟩, -⟩ := hp𝒴.unique_lift φ (f.map α ≫ t'.hom) (eqToHom hz ≫ s.snd)
      (by rw [Category.assoc, ← s.condition, p𝒴.map_comp, hα, Category.assoc])
    let m := (ht.from (CostructuredArrow.mk β)).left
    have hm : f.map m ≫ t.hom = β := CostructuredArrow.w (ht.from (CostructuredArrow.mk β))
    have hmk : m ≫ k = α := CostructuredArrow.IsUniversal.hom_ext ht' (by
      rw [f.map_comp, Category.assoc, hk, reassoc_of% hm, hβ₂])
    refine ⟨eqToHom hz.symm ≫ p𝒴.map (f.map m), ?_, ?_, ?_⟩
    · rw [Category.assoc, ← p𝒴.map_comp, ← f.map_comp, hmk, hα]
      simp
    · rw [Category.assoc, ← p𝒴.map_comp, hm, hβ₁]
      simp
    · intro m' h₁ h₂
      obtain ⟨z', hz', μ, hμ⟩ := hp𝒳.exists_lift_eqToHom t.left m'
      replace hμ : p𝒴.map (f.map μ) = eqToHom hz' ≫ m' := hμ
      obtain ⟨ι, ⟨hι₁, hι₂⟩, -⟩ := hp𝒳.unique_lift α (μ ≫ k) (eqToHom (hz'.trans hz.symm))
        (by
          change eqToHom (hz'.trans hz.symm) ≫ p𝒴.map (f.map α) =
            p𝒴.map (f.map (μ ≫ k))
          rw [hα, f.map_comp, p𝒴.map_comp, hμ, Category.assoc, h₁, eqToHom_trans_assoc])
      replace hι₁ : p𝒴.map (f.map ι) = eqToHom (hz'.trans hz.symm) := hι₁
      have hg : f.map ι ≫ β = f.map μ ≫ t.hom := by
        have hcond : p𝒴.map (f.map μ ≫ t.hom) ≫ p𝒴.map φ =
            p𝒴.map (f.map μ ≫ t.hom ≫ φ) := by
          rw [← p𝒴.map_comp, Category.assoc]
        refine (hp𝒴.unique_lift φ (f.map μ ≫ t.hom ≫ φ) _ hcond).unique ⟨?_, ?_⟩ ⟨rfl, ?_⟩
        · rw [p𝒴.map_comp, hι₁, hβ₁, p𝒴.map_comp, hμ, Category.assoc, h₂,
            eqToHom_trans_assoc]
        · rw [Category.assoc, hβ₂, ← Category.assoc, ← f.map_comp, hι₂, f.map_comp,
            Category.assoc, hk]
        · rw [Category.assoc]
      have hιm : ι ≫ m = μ := CostructuredArrow.IsUniversal.hom_ext ht (by
        rw [f.map_comp, Category.assoc, hm, hg])
      have : m' = eqToHom hz'.symm ≫ p𝒴.map (f.map μ) := by simp [hμ]
      rw [this, ← hιm, f.map_comp, p𝒴.map_comp, hι₁, eqToHom_trans_assoc]
  choose lift hl₁ hl₂ hl₃ using key
  exact IsPullback.of_isLimit' sq (PullbackCone.IsLimit.mk sq.w lift hl₁ hl₂ hl₃)

/-- At a terminal object `y_⊤` of `𝒴`, the arrow `f x_⊤ ⟶ y_⊤` from a terminal object `x_⊤` of
`𝒳` is terminal in `CostructuredArrow f y_⊤`. -/
def isTerminalCostructuredArrowMkOfIsTerminal {x₀ : 𝒳} (hx : IsTerminal x₀) {y₀ : 𝒴}
    (hy : IsTerminal y₀) : IsTerminal (CostructuredArrow.mk (hy.from (f.obj x₀))) :=
  IsTerminal.ofUniqueHom
    (fun c => CostructuredArrow.homMk (hx.from c.left) (hy.hom_ext _ _))
    (fun _ _ => CostructuredArrow.hom_ext _ _ (hx.hom_ext _ _))

/-- **Terminal arrows exist over fibre products.** Let `f : 𝒳 ⥤ 𝒴` be a functor over `𝒞` between
categories fibred in groupoids with terminal objects `x_⊤` and `y_⊤`. If `𝒞` has fibre products,
then for every `y` the comma category `CostructuredArrow f y` has a terminal object, lying over
the fibre product `p(y) ×_{p(y_⊤)} p(f x_⊤)`. -/
theorem exists_isTerminal_costructuredArrow [HasPullbacks 𝒞] (hp𝒳 : p𝒳.IsFiberedInGroupoids)
    (hp𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) {x₀ : 𝒳} (hx : IsTerminal x₀)
    {y₀ : 𝒴} (hy : IsTerminal y₀) (y : 𝒴) :
    ∃ t : CostructuredArrow f y, Nonempty (IsTerminal t) := by
  subst hf
  obtain ⟨z, hz, α, hα⟩ := hp𝒳.exists_lift_eqToHom x₀
    (pullback.snd (p𝒴.map (hy.from y)) (p𝒴.map (hy.from (f.obj x₀))))
  replace hα : p𝒴.map (f.map α) = eqToHom hz ≫ pullback.snd _ _ := hα
  have hcond : (eqToHom hz ≫ pullback.fst (p𝒴.map (hy.from y))
      (p𝒴.map (hy.from (f.obj x₀)))) ≫ p𝒴.map (hy.from y) = p𝒴.map (hy.from (f.obj z)) := by
    rw [hy.hom_ext (hy.from (f.obj z)) (f.map α ≫ hy.from (f.obj x₀)), p𝒴.map_comp, hα,
      Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨β, ⟨hβ₁, -⟩, -⟩ := hp𝒴.unique_lift (hy.from y) (hy.from (f.obj z)) _ hcond
  let l : ∀ c : CostructuredArrow f y, p𝒴.obj (f.obj c.left) ⟶
      pullback (p𝒴.map (hy.from y)) (p𝒴.map (hy.from (f.obj x₀))) := fun c =>
    pullback.lift (p𝒴.map c.hom) (p𝒴.map (f.map (hx.from c.left))) (by
      rw [← p𝒴.map_comp, ← p𝒴.map_comp]
      exact congrArg p𝒴.map (hy.hom_ext _ _))
  have hl : ∀ c : CostructuredArrow f y,
      (l c ≫ eqToHom hz.symm) ≫ p𝒴.map (f.map α) = p𝒴.map (f.map (hx.from c.left)) := by
    intro c
    rw [hα, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      pullback.lift_snd]
  have U := fun c => hp𝒳.unique_lift α (hx.from c.left) (l c ≫ eqToHom hz.symm) (hl c)
  refine ⟨CostructuredArrow.mk β, ⟨IsTerminal.ofUniqueHom (fun c => ?_) (fun c m => ?_)⟩⟩
  · let χ := (U c).exists.choose
    have hχ := (U c).exists.choose_spec
    refine CostructuredArrow.homMk χ ?_
    have hc : p𝒴.map c.hom ≫ p𝒴.map (hy.from y) = p𝒴.map (hy.from (f.obj c.left)) := by
      rw [← p𝒴.map_comp]
      exact congrArg p𝒴.map (hy.hom_ext _ _)
    refine (hp𝒴.unique_lift (hy.from y) (hy.from (f.obj c.left)) _ hc).unique ⟨?_, ?_⟩
      ⟨rfl, hy.hom_ext _ _⟩
    · change p𝒴.map (f.map χ ≫ β) = p𝒴.map c.hom
      rw [p𝒴.map_comp, show p𝒴.map (f.map χ) = _ from hχ.1, hβ₁]
      rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        pullback.lift_fst]
    · exact hy.hom_ext _ _
  · refine CostructuredArrow.hom_ext _ _ ?_
    have hmw : f.map m.left ≫ β = c.hom := CostructuredArrow.w m
    have hpm' : p𝒴.map (f.map m.left) ≫ eqToHom hz = l c := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, ← hmw, p𝒴.map_comp, hβ₁, Category.assoc]
      · rw [pullback.lift_snd, Category.assoc, ← hα, ← p𝒴.map_comp, ← f.map_comp]
        exact congrArg (fun g => p𝒴.map (f.map g)) (hx.hom_ext _ _)
    have hpm : p𝒴.map (f.map m.left) = l c ≫ eqToHom hz.symm := by
      rw [← hpm', Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact (U c).unique ⟨hpm, hx.hom_ext _ _⟩ (U c).exists.choose_spec

end CategoryTheory

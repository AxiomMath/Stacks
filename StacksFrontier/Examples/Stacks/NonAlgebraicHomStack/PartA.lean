module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ChangeOfUniverse
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyTorsion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyNonTorsionPointGeneral
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.BigFppfAbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ConstantSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassFirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.ClassOverAnObject
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftFirstCohomology
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.PartAGeometry
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.PartB
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.SituationGeometry

/-!
# Part (a) of Stacks 0AFB: `H¹(X₀, A)` is not torsion

In the situation of Section 0AF8 of the Stacks project, part (a) of the proof of Stacks 0AFB
asserts that the first fppf cohomology `H¹(X₀, A)` of the special fibre `X₀` with coefficients in
the constant abelian scheme `A = A₀ ×_k S` is not torsion. This is the input `hnotTorsion` of
`Stacks.Examples.NonAlgebraicHomStack.exists_compatible_ne_restrictTotal` and
`Stacks.Examples.NonAlgebraicHomStack.not_surjective_toCompatibleSystems`.

The source glues trivial `A₀`-torsors on the components of a loop of rational curves of `X₀`,
identifying them at one node `x₀` through a point `a₀ ∈ A₀(k)` of infinite order, and shows that no
multiple of the result is trivial using Stacks 0AEN. The glueing is done here as a Čech cocycle
for a Zariski covering of `X₀` by two opens, with no algebraic space formed:

* `V₀ = X₀ ∖ {x₀}` and `V₁ ∋ x₀`, with `V₀ ∩ V₁ = W' ⊔ W''`, where `W''` lies on the component
  `C₁` through `x₀` and `W'` off it
  (`Stacks.Examples.NonAlgebraicHomStack.exists_opens_of_component`);
* the cocycle is the section `σ` of `A` over `V₀ ∩ V₁` equal to `0` on `W'` and to `a₀` on `W''`.

Its class in `Ȟ¹`, and hence in `H¹(X₀, A)` (the comparison `Ȟ¹ ⟶ H¹` is injective,
Stacks 0A6G), has infinite order: if `n` times the cocycle is the coboundary of sections `s₀` over
`V₀` and `s₁` over `V₁`, then `s₀` and `s₁` agree on `W'` and differ by `n a₀` on `W''`, and going
around the loop with Stacks 0AEN forces `n a₀ = 0`
(`Stacks.Examples.NonAlgebraicHomStack.eq_one_of_loop`).

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.twoOpenCover_mem`: two opens covering `X₀` form a covering
  of `X₀` in the big fppf site over `S`.
* `Stacks.Examples.NonAlgebraicHomStack.twistCocycle_mem_cocycles1`: the glueing cocycle.
* `Stacks.Examples.NonAlgebraicHomStack.exists_sections_of_cechDifferential_eq`: a coboundary
  for a multiple of the cocycle gives sections over the two opens differing by that multiple.
* `Stacks.Examples.NonAlgebraicHomStack.not_isAddTorsion_H1_specialFibre`: **part (a) of
  Stacks 0AFB**, the input `hnotTorsion`.

## Implementation notes

The Čech comparison of Stacks 0A6G (`Stacks.CechSite.cechH1ToSliceH`) is stated with coefficients
in the universe of the objects of the site, one above the universe of the points sheaf of `A`, so
the sheaf is lifted along `ULift` and the classes are compared through
`Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv`, the comparison
`Stacks.Cohomology.Torsors.overClassEquiv` of cohomology over an object with the cohomology of the
localized site, and `CategoryTheory.Abelian.Ext.chgUnivAddEquiv` for the universe of the
`Ext`-groups; all of these are additive, so the non-torsion class is transported intact.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite CartesianMonoidalCategory
open MonoidalCategory
open scoped CategoryTheory.MonObj

universe w u a

namespace Stacks.Examples.NonAlgebraicHomStack

/-! ### Opens of the special fibre as objects of the big fppf site -/

section Opens

variable {k : Type u} [Field k] {B : BigFppfSite.{u}} {hS : B.Contains (base k)} {X : Scheme.{u}}
  {fX : X ⟶ base k} {hXn : ∀ n, B.Contains (thickening fX n)}

/-- An open of the special fibre lies in every big fppf site containing the special fibre. -/
theorem contains_open (B : BigFppfSite.{u}) {X : Scheme.{u}} (fX : X ⟶ base k)
    (hXn : ∀ n, B.Contains (thickening fX n)) (V : (thickening fX 0).Opens) :
    B.Contains V.toScheme :=
  Scheme.size_lt_of_isOpenImmersion V.ι (hXn 0)

/-- An open `V` of the special fibre `X₀`, as an object of the big fppf site over `S`. -/
def openObj (B : BigFppfSite.{u}) (hS : B.Contains (base k)) {X : Scheme.{u}} (fX : X ⟶ base k)
    (hXn : ∀ n, B.Contains (thickening fX n)) (V : (thickening fX 0).Opens) :
    BigFppfOver B (base k) hS :=
  Over.mk (Y := B.obj (contains_open B fX hXn V))
    (ObjectProperty.homMk (V.ι ≫ thickeningToTotal fX 0 ≫ fX))

/-- The inclusion `V ⟶ X₀` in the big fppf site over `S`. -/
def openHom (B : BigFppfSite.{u}) (hS : B.Contains (base k)) {X : Scheme.{u}} (fX : X ⟶ base k)
    (hXn : ∀ n, B.Contains (thickening fX n)) (V : (thickening fX 0).Opens) :
    openObj B hS fX hXn V ⟶ thickeningObj B hS fX hXn 0 :=
  Over.homMk (ObjectProperty.homMk (X := B.obj (contains_open B fX hXn V)) (Y := B.obj (hXn 0))
    V.ι) (by
      apply ObjectProperty.hom_ext
      rfl)

/-- An open `V` of the special fibre `X₀`, as an object of the localization at `X₀`. -/
abbrev openOverObj (B : BigFppfSite.{u}) (hS : B.Contains (base k)) {X : Scheme.{u}}
    (fX : X ⟶ base k) (hXn : ∀ n, B.Contains (thickening fX n)) (V : (thickening fX 0).Opens) :
    Over (thickeningObj B hS fX hXn 0) :=
  Over.mk (openHom B hS fX hXn V)

/-- The underlying morphism of schemes `T ⟶ X₀` of an object of the localization at `X₀`. -/
abbrev toSpecialFibre (T : Over (thickeningObj B hS fX hXn 0)) :
    T.left.left.obj ⟶ thickening fX 0 :=
  T.hom.left.hom

lemma toSpecialFibre_eq {V : (thickening fX 0).Opens} {T : Over (thickeningObj B hS fX hXn 0)}
    (φ : T ⟶ openOverObj B hS fX hXn V) : toSpecialFibre T = φ.left.left.hom ≫ V.ι := by
  have h := congrArg (fun f => f.left.hom) (Over.w φ)
  simp only [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom] at h
  exact h.symm

lemma toSpecialFibre_mem {V : (thickening fX 0).Opens} {T : Over (thickeningObj B hS fX hXn 0)}
    (φ : T ⟶ openOverObj B hS fX hXn V) (t : T.left.left.obj) : toSpecialFibre T t ∈ V := by
  rw [toSpecialFibre_eq φ]
  exact ι_apply_mem V _

/-- Morphisms into an open of the special fibre are unique: the open immersion is a
monomorphism. -/
lemma openOverObj_hom_ext {V : (thickening fX 0).Opens} {T : Over (thickeningObj B hS fX hXn 0)}
    (φ ψ : T ⟶ openOverObj B hS fX hXn V) : φ = ψ := by
  apply Over.OverMorphism.ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  refine (cancel_mono V.ι).1 ?_
  exact (toSpecialFibre_eq φ).symm.trans (toSpecialFibre_eq ψ)

instance {V : (thickening fX 0).Opens} {T : Over (thickeningObj B hS fX hXn 0)} :
    Subsingleton (T ⟶ openOverObj B hS fX hXn V) :=
  ⟨openOverObj_hom_ext⟩

/-- An object of the localization at `X₀` whose image lies in an open `V` maps to `V`. -/
def liftOpen (V : (thickening fX 0).Opens) (T : Over (thickeningObj B hS fX hXn 0))
    (hT : ∀ t, toSpecialFibre T t ∈ V) : T ⟶ openOverObj B hS fX hXn V := by
  let g := IsOpenImmersion.lift V.ι (toSpecialFibre T) (by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hT t)
  have hg : g ≫ V.ι = toSpecialFibre T := IsOpenImmersion.lift_fac _ _ _
  refine Over.homMk (Over.homMk (ObjectProperty.homMk (X := T.left.left)
    (Y := B.obj (contains_open B fX hXn V)) g) ?_) ?_
  · apply ObjectProperty.hom_ext
    have h := congrArg (fun f => f.hom) (Over.w T.hom)
    simp only [ObjectProperty.FullSubcategory.comp_hom] at h
    change g ≫ V.ι ≫ thickeningToTotal fX 0 ≫ fX = T.left.hom.hom
    rw [← Category.assoc, hg]
    exact h
  · apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hg

/-- The inclusion of opens `W ≤ V` of the special fibre, in the big fppf site over `S`. -/
def openIncl {W V : (thickening fX 0).Opens} (h : W ≤ V) :
    openObj B hS fX hXn W ⟶ openObj B hS fX hXn V :=
  (liftOpen V (openOverObj B hS fX hXn W) fun t =>
    h (toSpecialFibre_mem (𝟙 (openOverObj B hS fX hXn W)) t)).left

end Opens

/-! ### The covering by two opens -/

section Cover

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (base k)) {X : Scheme.{u}}
  (fX : X ⟶ base k) (hXn : ∀ n, B.Contains (thickening fX n))

/-- The family `{V₀ ⟶ X₀, V₁ ⟶ X₀}` of two opens of the special fibre, in the big fppf site over
`S`. -/
abbrev twoOpenCover (V₀ V₁ : (thickening fX 0).Opens) :
    PreZeroHypercover.{0} (thickeningObj B hS fX hXn 0) where
  I₀ := Fin 2
  X i := openObj B hS fX hXn (![V₀, V₁] i)
  f i := openHom B hS fX hXn (![V₀, V₁] i)

/-- Two opens covering the special fibre form a covering of it in the big fppf site over `S`: a
covering family of the site refines the open cover (Stacks 03WX,
`AlgebraicGeometry.bigFppfOver_openCoverData`). -/
theorem twoOpenCover_mem (V₀ V₁ : (thickening fX 0).Opens) (h : V₀ ⊔ V₁ = ⊤) :
    (twoOpenCover B hS fX hXn V₀ V₁).sieve₀ ∈
      BigFppfOver.topology B (base k) hS (thickeningObj B hS fX hXn 0) := by
  classical
  let O : (thickening fX 0) → (thickening fX 0).Opens := fun y => if y ∈ V₀ then V₀ else V₁
  have hO : TopologicalSpace.IsOpenCover O := by
    refine eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, ?_⟩
    by_cases hy : y ∈ V₀
    · simp only [O, ite_eq_left hy]; exact hy
    · simp only [O, ite_eq_right hy]
      have : y ∈ V₀ ⊔ V₁ := h ▸ trivial
      exact (TopologicalSpace.Opens.mem_sup.mp this).resolve_left hy
  obtain ⟨I, W, a, r, hcov, hsub⟩ :=
    bigFppfOver_openCoverData B (base k) hS (T := thickeningObj B hS fX hXn 0) O hO
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  intro T g hg
  obtain ⟨i, h', rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  refine Sieve.downward_closed _ ?_ h'
  have hmem : ∀ e : Fin 2, (∀ y, (BigFppfOver.toScheme B (base k) hS).map (a i) y ∈
      ![V₀, V₁] e) → (twoOpenCover B hS fX hXn V₀ V₁).sieve₀ (a i) := by
    intro e he
    let φ := liftOpen (![V₀, V₁] e) (Over.mk (a i)) he
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨e, φ.left, (Over.w φ).symm⟩
  by_cases hri : r i ∈ V₀
  · refine hmem 0 fun y => ?_
    have := hsub i y
    rw [show O (r i) = V₀ from ite_eq_left hri] at this
    exact this
  · refine hmem 1 fun y => ?_
    have := hsub i y
    rw [show O (r i) = V₁ from ite_eq_right hri] at this
    exact this

/-- The localization of the big fppf site at an object has finite products: binary products are
fibre products over the object. -/
theorem hasFiniteProducts_over_bigFppfOver {S : Scheme.{u}} {hS' : B.Contains S}
    (U : BigFppfOver B S hS') :
    HasFiniteProducts (Over U) :=
  have : HasBinaryProducts (Over U) := Over.ConstructProducts.over_binaryProduct_of_pullback
  hasFiniteProducts_of_has_binary_and_terminal

end Cover

/-! ### The glueing cocycle -/

section Cocycle

variable {k : Type u} [Field k] {B : BigFppfSite.{u}} {hS : B.Contains (base k)} {X : Scheme.{u}}
  {fX : X ⟶ base k} {hXn : ∀ n, B.Contains (thickening fX n)}
  {V₀ V₁ : (thickening fX 0).Opens}

attribute [local instance] hasFiniteProducts_over_bigFppfOver

/-- Any two morphisms into an iterated fibre product of members of the two-open family agree. -/
lemma twoOpenCover_hom_ext {n : ℕ} (l : Fin (n + 1) → Fin 2)
    {T : Over (thickeningObj B hS fX hXn 0)}
    (f g : T ⟶ ∏ᶜ fun j ↦ Over.mk ((twoOpenCover B hS fX hXn V₀ V₁).f (l j))) : f = g :=
  Pi.hom_ext _ _ fun b => openOverObj_hom_ext (V := ![V₀, V₁] (l b)) _ _

lemma fin_two_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  rcases a with ⟨_ | _ | a, ha⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- An iterated fibre product of members of the two-open family hitting both members maps to the
intersection `V₀ ∩ V₁`. -/
def toInter {n : ℕ} (l : Fin (n + 1) → Fin 2) (i i' : Fin (n + 1)) (hi : l i = 0) (hi' : l i' = 1) :
    (∏ᶜ fun j ↦ Over.mk ((twoOpenCover B hS fX hXn V₀ V₁).f (l j))) ⟶
      openOverObj B hS fX hXn (V₀ ⊓ V₁) :=
  liftOpen _ _ fun t => by
    have h₀ := toSpecialFibre_mem
      (Pi.π (fun j ↦ Over.mk ((twoOpenCover B hS fX hXn V₀ V₁).f (l j))) i) t
    have h₁ := toSpecialFibre_mem
      (Pi.π (fun j ↦ Over.mk ((twoOpenCover B hS fX hXn V₀ V₁).f (l j))) i') t
    rw [hi] at h₀
    rw [hi'] at h₁
    exact ⟨h₀, h₁⟩

variable (F : (BigFppfOver B (base k) hS)ᵒᵖ ⥤ AddCommGrpCat.{a})
  (σ : F.obj (op (openObj B hS fX hXn (V₀ ⊓ V₁))))

/-- **The glueing cocycle.** Its value over `Vᵢ ×_{X₀} Vⱼ` is `0` for `i = j`, the pullback of
`σ` for `(i, j) = (0, 1)` and of `-σ` for `(i, j) = (1, 0)`. -/
def twistCocycle : Stacks.CechSite.cechCochain (twoOpenCover B hS fX hXn V₀ V₁) F 1 := fun l =>
  if h : l 0 = 0 ∧ l 1 = 1 then F.map (toInter l 0 1 h.1 h.2).left.op σ
  else if h' : l 0 = 1 ∧ l 1 = 0 then -F.map (toInter l 1 0 h'.2 h'.1).left.op σ
  else 0

/-- Two pullbacks of a section over an open of the special fibre agree, as the morphisms into the
open are unique. -/
lemma map_map_eq_of_openOverObj {W : (thickening fX 0).Opens}
    {T T' : Over (thickeningObj B hS fX hXn 0)} (φ : T ⟶ T') (ψ : T' ⟶ openOverObj B hS fX hXn W)
    (χ : T ⟶ openOverObj B hS fX hXn W) (x : F.obj (op (openObj B hS fX hXn W))) :
    F.map φ.left.op (F.map ψ.left.op x) = F.map χ.left.op x := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, ← Over.comp_left,
    openOverObj_hom_ext (φ ≫ ψ) χ]

lemma twistCocycle_of_zero_one (l : Fin 2 → Fin 2) (h₀ : l 0 = 0) (h₁ : l 1 = 1) :
    twistCocycle F σ l = F.map (toInter l 0 1 h₀ h₁).left.op σ := by
  simp only [twistCocycle, dite_eq_left (And.intro h₀ h₁)]

lemma twistCocycle_of_one_zero (l : Fin 2 → Fin 2) (h₀ : l 0 = 1) (h₁ : l 1 = 0) :
    twistCocycle F σ l = -F.map (toInter l 1 0 h₁ h₀).left.op σ := by
  have : ¬ (l 0 = 0 ∧ l 1 = 1) := fun h => by simp [h₀] at h
  simp only [twistCocycle, dite_eq_right this, dite_eq_left (And.intro h₀ h₁)]

lemma twistCocycle_of_eq (l : Fin 2 → Fin 2) (h : l 0 = l 1) : twistCocycle F σ l = 0 := by
  have h₁ : ¬ (l 0 = 0 ∧ l 1 = 1) := fun h' => by
    have := h.symm.trans h'.1; rw [h'.2] at this; exact absurd this (by decide)
  have h₂ : ¬ (l 0 = 1 ∧ l 1 = 0) := fun h' => by
    have := h.symm.trans h'.1; rw [h'.2] at this; exact absurd this (by decide)
  simp only [twistCocycle, dite_eq_right h₁, dite_eq_right h₂]

/-- The glueing cocycle is a Čech `1`-cocycle. -/
theorem twistCocycle_mem_cocycles1 :
    twistCocycle F σ ∈ Stacks.CechSite.cocycles1 (twoOpenCover B hS fX hXn V₀ V₁) F := by
  rw [Stacks.CechSite.mem_cocycles1_iff']
  intro k
  have e00 : (0 : Fin 3).succAbove 0 = 1 := by decide
  have e01 : (0 : Fin 3).succAbove 1 = 2 := by decide
  have e10 : (1 : Fin 3).succAbove 0 = 0 := by decide
  have e11 : (1 : Fin 3).succAbove 1 = 2 := by decide
  have e20 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have e21 : (2 : Fin 3).succAbove 1 = 1 := by decide
  let l₀ : Fin 2 → Fin 2 := fun b ↦ k ((0 : Fin 3).succAbove b)
  let l₁ : Fin 2 → Fin 2 := fun b ↦ k ((1 : Fin 3).succAbove b)
  let l₂ : Fin 2 → Fin 2 := fun b ↦ k ((2 : Fin 3).succAbove b)
  have hl₀ : l₀ 0 = k 1 ∧ l₀ 1 = k 2 := ⟨congrArg k e00, congrArg k e01⟩
  have hl₁ : l₁ 0 = k 0 ∧ l₁ 1 = k 2 := ⟨congrArg k e10, congrArg k e11⟩
  have hl₂ : l₂ 0 = k 0 ∧ l₂ 1 = k 1 := ⟨congrArg k e20, congrArg k e21⟩
  change F.map _ (twistCocycle F σ l₀) + F.map _ (twistCocycle F σ l₂) =
    F.map _ (twistCocycle F σ l₁)
  rcases fin_two_eq_zero_or_one (k 0) with h0 | h0 <;>
  rcases fin_two_eq_zero_or_one (k 1) with h1 | h1 <;>
  rcases fin_two_eq_zero_or_one (k 2) with h2 | h2
  · rw [twistCocycle_of_eq F σ l₀ (by rw [hl₀.1, hl₀.2, h1, h2]),
      twistCocycle_of_eq F σ l₁ (by rw [hl₁.1, hl₁.2, h0, h2]),
      twistCocycle_of_eq F σ l₂ (by rw [hl₂.1, hl₂.2, h0, h1])]
    simp only [map_zero, add_zero]
  · let χ := toInter (B := B) (hS := hS) (hXn := hXn) (V₀ := V₀) (V₁ := V₁) k 0 2 h0 h2
    rw [twistCocycle_of_zero_one F σ l₀ (by rw [hl₀.1, h1]) (by rw [hl₀.2, h2]),
      twistCocycle_of_zero_one F σ l₁ (by rw [hl₁.1, h0]) (by rw [hl₁.2, h2]),
      twistCocycle_of_eq F σ l₂ (by rw [hl₂.1, hl₂.2, h0, h1])]
    simp only [map_zero, add_zero, map_map_eq_of_openOverObj F _ _ χ]
  · let χ := toInter (B := B) (hS := hS) (hXn := hXn) (V₀ := V₀) (V₁ := V₁) k 0 1 h0 h1
    rw [twistCocycle_of_one_zero F σ l₀ (by rw [hl₀.1, h1]) (by rw [hl₀.2, h2]),
      twistCocycle_of_eq F σ l₁ (by rw [hl₁.1, hl₁.2, h0, h2]),
      twistCocycle_of_zero_one F σ l₂ (by rw [hl₂.1, h0]) (by rw [hl₂.2, h1])]
    simp only [map_zero, map_neg, map_map_eq_of_openOverObj F _ _ χ, neg_add_cancel]
  · let χ := toInter (B := B) (hS := hS) (hXn := hXn) (V₀ := V₀) (V₁ := V₁) k 0 1 h0 h1
    rw [twistCocycle_of_eq F σ l₀ (by rw [hl₀.1, hl₀.2, h1, h2]),
      twistCocycle_of_zero_one F σ l₁ (by rw [hl₁.1, h0]) (by rw [hl₁.2, h2]),
      twistCocycle_of_zero_one F σ l₂ (by rw [hl₂.1, h0]) (by rw [hl₂.2, h1])]
    simp only [map_zero, zero_add, map_map_eq_of_openOverObj F _ _ χ]
  · let χ := toInter (B := B) (hS := hS) (hXn := hXn) (V₀ := V₀) (V₁ := V₁) k 1 0 h1 h0
    rw [twistCocycle_of_eq F σ l₀ (by rw [hl₀.1, hl₀.2, h1, h2]),
      twistCocycle_of_one_zero F σ l₁ (by rw [hl₁.1, h0]) (by rw [hl₁.2, h2]),
      twistCocycle_of_one_zero F σ l₂ (by rw [hl₂.1, h0]) (by rw [hl₂.2, h1])]
    simp only [map_zero, zero_add, map_neg, map_map_eq_of_openOverObj F _ _ χ]
  · let χ := toInter (B := B) (hS := hS) (hXn := hXn) (V₀ := V₀) (V₁ := V₁) k 1 0 h1 h0
    rw [twistCocycle_of_zero_one F σ l₀ (by rw [hl₀.1, h1]) (by rw [hl₀.2, h2]),
      twistCocycle_of_eq F σ l₁ (by rw [hl₁.1, hl₁.2, h0, h2]),
      twistCocycle_of_one_zero F σ l₂ (by rw [hl₂.1, h0]) (by rw [hl₂.2, h1])]
    simp only [map_zero, map_neg, map_map_eq_of_openOverObj F _ _ χ, add_neg_cancel]
  · let χ := toInter (B := B) (hS := hS) (hXn := hXn) (V₀ := V₀) (V₁ := V₁) k 2 0 h2 h0
    rw [twistCocycle_of_one_zero F σ l₀ (by rw [hl₀.1, h1]) (by rw [hl₀.2, h2]),
      twistCocycle_of_one_zero F σ l₁ (by rw [hl₁.1, h0]) (by rw [hl₁.2, h2]),
      twistCocycle_of_eq F σ l₂ (by rw [hl₂.1, hl₂.2, h0, h1])]
    simp only [map_zero, add_zero, map_neg, map_map_eq_of_openOverObj F _ _ χ]
  · rw [twistCocycle_of_eq F σ l₀ (by rw [hl₀.1, hl₀.2, h1, h2]),
      twistCocycle_of_eq F σ l₁ (by rw [hl₁.1, hl₁.2, h0, h2]),
      twistCocycle_of_eq F σ l₂ (by rw [hl₂.1, hl₂.2, h0, h1])]
    simp only [map_zero, add_zero]

/-- The glueing cocycle, as a Čech `1`-cocycle. -/
def twistCocycleOf : Stacks.CechSite.cocycles1 (twoOpenCover B hS fX hXn V₀ V₁) F :=
  ⟨twistCocycle F σ, twistCocycle_mem_cocycles1 F σ⟩

/-- **A coboundary for a multiple of the glueing cocycle.** If `n` times the glueing cocycle is
the Čech coboundary of a `0`-cochain, there are sections `s₀` over `V₀` and `s₁` over `V₁` whose
restrictions to `V₀ ∩ V₁` differ by `n σ`. -/
theorem exists_sections_of_cechDifferential_eq (n : ℕ)
    (t : Stacks.CechSite.cechCochain (twoOpenCover B hS fX hXn V₀ V₁) F 0)
    (ht : Stacks.CechSite.cechDifferential _ F 0 t = n • twistCocycle F σ) :
    ∃ (s₀ : F.obj (op (openObj B hS fX hXn V₀))) (s₁ : F.obj (op (openObj B hS fX hXn V₁))),
      F.map (openIncl (B := B) (hS := hS) (hXn := hXn) (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op s₁ -
        F.map (openIncl (B := B) (hS := hS) (hXn := hXn) (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op s₀ =
        n • σ := by
  let kk : Fin 2 → Fin 2 := ![0, 1]
  let E := twoOpenCover B hS fX hXn V₀ V₁
  let Wo := openOverObj B hS fX hXn (V₀ ⊓ V₁)
  have hW : ∀ t, toSpecialFibre Wo t ∈ V₀ ⊓ V₁ := toSpecialFibre_mem (𝟙 Wo)
  have hmemk : ∀ b t, toSpecialFibre Wo t ∈ ![V₀, V₁] (kk b) := by
    intro b t
    fin_cases b
    · exact (hW t).1
    · exact (hW t).2
  let ℓ : Wo ⟶ ∏ᶜ fun j ↦ Over.mk (E.f (kk j)) :=
    Pi.lift (f := fun j ↦ Over.mk (E.f (kk j))) fun b => liftOpen _ _ (hmemk b)
  let l₀ : Fin 1 → Fin 2 := fun b ↦ kk ((0 : Fin 2).succAbove b)
  let l₁ : Fin 1 → Fin 2 := fun b ↦ kk ((1 : Fin 2).succAbove b)
  have hl₀ : ∀ b, l₀ b = 1 := fun b => by
    rw [Subsingleton.elim b 0]; rfl
  have hl₁ : ∀ b, l₁ b = 0 := fun b => by
    rw [Subsingleton.elim b 0]; rfl
  let κ₀ : openOverObj B hS fX hXn V₀ ⟶ ∏ᶜ fun j ↦ Over.mk (E.f (l₁ j)) :=
    Pi.lift (f := fun j ↦ Over.mk (E.f (l₁ j))) fun b => liftOpen (![V₀, V₁] (l₁ b)) _ fun t => by
      rw [hl₁ b]; exact toSpecialFibre_mem (𝟙 _) t
  let κ₁ : openOverObj B hS fX hXn V₁ ⟶ ∏ᶜ fun j ↦ Over.mk (E.f (l₀ j)) :=
    Pi.lift (f := fun j ↦ Over.mk (E.f (l₀ j))) fun b => liftOpen (![V₀, V₁] (l₀ b)) _ fun t => by
      rw [hl₀ b]; exact toSpecialFibre_mem (𝟙 _) t
  refine ⟨F.map κ₀.left.op (t l₁), F.map κ₁.left.op (t l₀), ?_⟩
  have hk := congrArg (fun c => F.map ℓ.left.op (c kk)) ht
  simp only [Stacks.CechSite.cechDifferential_zero_apply, map_sub, Pi.smul_apply, map_nsmul] at hk
  change F.map ℓ.left.op (F.map _ (t l₀)) - F.map ℓ.left.op (F.map _ (t l₁)) =
    n • F.map ℓ.left.op (twistCocycle F σ kk) at hk
  rw [twistCocycle_of_zero_one F σ kk rfl rfl,
    map_map_eq_of_openOverObj F ℓ _ (𝟙 Wo), Over.id_left, op_id, F.map_id,
    ConcreteCategory.id_apply] at hk
  rw [← hk]
  congr 1
  · have e : openIncl (B := B) (hS := hS) (hXn := hXn) (inf_le_right : V₀ ⊓ V₁ ≤ V₁) ≫ κ₁.left =
        ℓ.left ≫ (Stacks.CechSite.faceProjection E kk 0).left := by
      change (liftOpen _ _ _).left ≫ κ₁.left = _
      rw [← Over.comp_left, ← Over.comp_left]
      exact congrArg Over.Hom.left (twoOpenCover_hom_ext _ _ _)
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, e, op_comp, F.map_comp,
      ConcreteCategory.comp_apply]
  · have e : openIncl (B := B) (hS := hS) (hXn := hXn) (inf_le_left : V₀ ⊓ V₁ ≤ V₀) ≫ κ₀.left =
        ℓ.left ≫ (Stacks.CechSite.faceProjection E kk 1).left := by
      change (liftOpen _ _ _).left ≫ κ₀.left = _
      rw [← Over.comp_left, ← Over.comp_left]
      exact congrArg Over.Hom.left (twoOpenCover_hom_ext _ _ _)
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, e, op_comp, F.map_comp,
      ConcreteCategory.comp_apply]

/-- **A torsion relation for the glueing class.** If `N` times the Čech class of the glueing
cocycle vanishes, there are sections `s₀` over `V₀` and `s₁` over `V₁` whose restrictions to
`V₀ ∩ V₁` differ by `N σ`. -/
theorem exists_sections_of_nsmul_cls_eq_zero (N : ℕ)
    (h : N • Stacks.CechSite.cls (twoOpenCover B hS fX hXn V₀ V₁) F (twistCocycleOf F σ) = 0) :
    ∃ (s₀ : F.obj (op (openObj B hS fX hXn V₀))) (s₁ : F.obj (op (openObj B hS fX hXn V₁))),
      F.map (openIncl (B := B) (hS := hS) (hXn := hXn) (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op s₁ -
        F.map (openIncl (B := B) (hS := hS) (hXn := hXn) (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op s₀ =
        N • σ := by
  have hmk : Stacks.CechSite.cls (twoOpenCover B hS fX hXn V₀ V₁) F (N • twistCocycleOf F σ) =
      N • Stacks.CechSite.cls (twoOpenCover B hS fX hXn V₀ V₁) F (twistCocycleOf F σ) :=
    QuotientAddGroup.mk_nsmul _ _ _
  rw [← hmk] at h
  obtain ⟨t, ht⟩ := (Stacks.CechSite.cls_eq_zero_iff _ F _).mp h
  exact exists_sections_of_cechDifferential_eq F σ N t ht

end Cocycle

/-- An identity between restrictions in the universe lift of an abelian sheaf holds in the sheaf. -/
lemma eq_of_uliftSheafFunctor_eq {C : Type*} [Category.{u} C] {J : GrothendieckTopology C}
    (A : Sheaf J AddCommGrpCat.{u}) {T T' T'' : C} (f : T ⟶ T') (g : T ⟶ T'')
    (x : ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} J).obj A).obj.obj (op T'))
    (y : ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} J).obj A).obj.obj (op T''))
    (z : ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} J).obj A).obj.obj (op T))
    (N : ℕ) (h : ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} J).obj A).obj.map
        f.op x - ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} J).obj A).obj.map
          g.op y = N • z) :
    A.obj.map f.op x.down - A.obj.map g.op y.down = N • z.down :=
  congrArg ULift.down h

section PointsSheaf

variable {B : BigFppfSite.{u}} {W : Scheme.{u}} {hW : B.Contains W} (G : Over W) [GrpObj G]
  [IsCommMonObj G] (hG : B.Contains G.left)

lemma pointsSheaf_toMul_sub {T : BigFppfOver B W hW}
    (x y : (pointsSheaf B W hW G hG).obj.obj (op T)) :
    Additive.toMul (α := (Over.post B.inclusion).obj T ⟶ G) (x - y) =
      Additive.toMul (α := (Over.post B.inclusion).obj T ⟶ G) x /
        Additive.toMul (α := (Over.post B.inclusion).obj T ⟶ G) y :=
  rfl

lemma pointsSheaf_toMul_nsmul {T : BigFppfOver B W hW}
    (x : (pointsSheaf B W hW G hG).obj.obj (op T)) (N : ℕ) :
    Additive.toMul (α := (Over.post B.inclusion).obj T ⟶ G) (N • x) =
      Additive.toMul (α := (Over.post B.inclusion).obj T ⟶ G) x ^ N :=
  rfl

lemma pointsSheaf_toMul_map {T T' : BigFppfOver B W hW} (f : T ⟶ T')
    (x : (pointsSheaf B W hW G hG).obj.obj (op T')) :
    Additive.toMul (α := (Over.post B.inclusion).obj T ⟶ G)
        ((pointsSheaf B W hW G hG).obj.map f.op x) =
      (Over.post B.inclusion).map f ≫ Additive.toMul (α := (Over.post B.inclusion).obj T' ⟶ G) x :=
  rfl

end PointsSheaf

/-! ### The special fibre over `k` -/

section SpecialFibre

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ base k)

/-- The structure morphism of the special fibre to `Spec k` is its morphism to `S` followed by
`S ⟶ Spec k`. -/
theorem thickeningToTotal_comp_baseToField :
    thickeningToTotal fX 0 ≫ fX ≫ Situation.baseToField = (specialFibre fX ↘ Spec (.of k)) := by
  change pullback.fst fX (adicThickeningι _ _ 0) ≫ fX ≫ _ =
    pullback.snd fX (adicThickeningι (PowerSeries k) (uniformizer k) 0) ≫ _
  rw [pullback.condition_assoc]
  congr 1
  simp only [adicThickeningι, Situation.baseToField, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The special fibre of a morphism locally of finite type over `k⟦t⟧` is locally of finite type
over `k`: `k ⟶ k⟦t⟧ / (t)` is surjective. -/
theorem locallyOfFiniteType_specialFibre [LocallyOfFiniteType fX] :
    LocallyOfFiniteType (specialFibre fX ↘ Spec (.of k)) := by
  change LocallyOfFiniteType (pullback.snd fX (adicThickeningι (PowerSeries k) (uniformizer k) 0) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k ⧸ uniformizer k ^ (0 + 1)))))
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap k (PowerSeries k ⧸ uniformizer k ^ (0 + 1))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    refine RingHom.FiniteType.of_surjective _ fun q => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨PowerSeries.constantCoeff p, ?_⟩
    change Ideal.Quotient.mk _ (algebraMap k (PowerSeries k) _) = _
    rw [Ideal.Quotient.eq, pow_one, uniformizer, Ideal.mem_span_singleton,
      PowerSeries.X_dvd_iff]
    simp
  infer_instance

end SpecialFibre

/-! ### Sections of the constant abelian scheme as morphisms to `A₀` -/

section Translation

variable {k : Type u} [Field k] (sit : Situation k) {B : BigFppfSite.{u}}
  {hS : B.Contains (base k)} {hXn : ∀ n, B.Contains (thickening sit.f n)}

/-- An open of the special fibre, as a scheme over `S`. -/
abbrev openOverBase (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    (hXn : ∀ n, B.Contains (thickening sit.f n)) (V : (thickening sit.f 0).Opens) : Over (base k) :=
  (Over.post B.inclusion).obj (openObj B hS sit.f hXn V)

/-- The comparison of an open of the special fibre over `k` with its image over `S` regarded over
`k`. -/
def openOverBaseIso (V : (thickening sit.f 0).Opens) :
    openOver (specialFibre sit.f ↘ Spec (.of k)) V ≅
      (Over.map Situation.baseToField).obj (openOverBase sit B hS hXn V) :=
  Over.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Over.map_obj_hom, Over.mk_hom,
      ← thickeningToTotal_comp_baseToField]
    rfl)

/-- **Sections of `A` as morphisms to `A₀`.** A morphism over `S` from an open `V` of the special
fibre to `A = A₀ ×_k S` is a morphism over `k` from `V` to `A₀`; the bijection is multiplicative. -/
def sectionMulEquiv (V : (thickening sit.f 0).Opens) :
    (openOverBase sit B hS hXn V ⟶ sit.abelianScheme) ≃*
      (openOver (specialFibre sit.f ↘ Spec (.of k)) V ⟶ sit.A₀) :=
  (overPullbackHomMulEquiv Situation.baseToField sit.A₀ _).symm.trans
    { toFun := fun g => (openOverBaseIso sit V).hom ≫ g
      invFun := fun g => (openOverBaseIso sit V).inv ≫ g
      left_inv := fun g => by simp
      right_inv := fun g => by simp
      map_mul' := fun g g' => MonObj.comp_mul _ _ _ }

/-- The restriction of a section of `A` along an inclusion of opens. -/
lemma sectionMulEquiv_comp {W V : (thickening sit.f 0).Opens} (h : W ≤ V)
    (s : openOverBase sit B hS hXn V ⟶ sit.abelianScheme) :
    sectionMulEquiv sit W ((Over.post B.inclusion).map (openIncl (B := B) (hS := hS)
      (hXn := hXn) h) ≫ s) = openOverHomOfLE _ h ≫ sectionMulEquiv sit V s := by
  simp only [sectionMulEquiv]
  change (openOverBaseIso sit W).hom ≫ ((Over.mapPullbackAdj _).homEquiv _ _).symm (_ ≫ s) =
    openOverHomOfLE _ h ≫ (openOverBaseIso sit V).hom ≫
      ((Over.mapPullbackAdj _).homEquiv _ _).symm s
  rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  congr 1

end Translation

/-! ### Part (a) -/

section PartA

variable {k : Type u} [Field k]

/-- An abelian variety over `k` which is not zero has positive dimension: a zero-dimensional one
is a point, and its unit section is then a surjective closed immersion onto a reduced scheme. -/
theorem pos_topologicalKrullDim_of_not_isIso (A₀ : Over (Spec (.of k))) [GrpObj A₀]
    [IsAbelianVariety k A₀] (h : ¬ IsIso A₀.hom) : 0 < topologicalKrullDim A₀.left := by
  by_contra hle
  have hle : topologicalKrullDim A₀.left ≤ 0 := not_lt.mp hle
  have hsub : Subsingleton A₀.left := by
    refine ⟨fun x y => ?_⟩
    have hgen : ∀ z : A₀.left, IsGenericPoint z ⊤ := fun z => by
      let c : TopologicalSpace.IrreducibleCloseds A₀.left :=
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
      let t : TopologicalSpace.IrreducibleCloseds A₀.left :=
        ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
      have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hle c
      have : c = t := hmax.eq_of_le (show closure {z} ⊆ Set.univ from Set.subset_univ _)
      exact isGenericPoint_def.mpr (congrArg (fun r : TopologicalSpace.IrreducibleCloseds _ =>
        (r : Set A₀.left)) this)
    exact (hgen x).eq (hgen y)
  let e : Spec (.of k) ⟶ A₀.left := η[A₀].left
  have he : e ≫ A₀.hom = 𝟙 _ := Over.w η[A₀]
  have : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id _ _ he
  have : Surjective e := ⟨fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have : IsIso e := isIso_of_isClosedImmersion_of_surjective e
  exact h ⟨⟨e, (cancel_epi e).mp (by rw [reassoc_of% he, Category.comp_id]), he⟩⟩

attribute [local instance] hasFiniteProducts_over_bigFppfOver

/-- **Čech classes of the universe lift give classes in `H¹`.** For a covering family `𝒰` of an
object `U` of the big fppf site over `S` and an abelian sheaf `A`, there is an injective additive
map from the first Čech cohomology `Ȟ¹(𝒰, A ⊗ ULift)` of the universe lift of `A` to `H¹(U, A)`:
the comparison of Stacks 0A6G, followed by the identifications of the cohomology of the universe
lift, of the cohomology of the localized site, and of the universe of the `Ext`-groups. -/
theorem exists_injective_cechH1_to_H' (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) (E : PreZeroHypercover.{0} U)
    (hE : E.sieve₀ ∈ BigFppfOver.topology B S hS U)
    (A : Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    [HasSheafify (BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})] :
    ∃ χ : Stacks.CechSite.cechH1 E
        ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u}
          (BigFppfOver.topology B S hS)).obj A).obj →+ Sheaf.H'.{w} A 1 U,
      Function.Injective χ := by
  let J := BigFppfOver.topology B S hS
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := J)
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, 0} (J := J)
  let : EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat_max.{0, u, u + 1} J
  let : HasSheafify (J.over U) AddCommGrpCat.{u + 1} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := J.over U)
  let : EnoughInjectives (Sheaf (J.over U) AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat_max.{0, u, u + 1} (J.over U)
  let : HasExt.{u + 1} (Sheaf (J.over U) AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives _
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, 0}
      (J := J.over U)
  let : ∀ V : BigFppfOver B S hS, HasSheafify (J.over V) AddCommGrpCat.{u} :=
    fun V => BigFppfOver.hasSheafify_over_abelian B S hS V
  let : ∀ V : BigFppfOver B S hS, HasExt.{u} (Sheaf (J.over V) AddCommGrpCat.{u}) :=
    fun V => BigFppfOver.hasExt_over_abelian B S hS V
  let : HasExt.{u} (Sheaf J AddCommGrpCat.{u}) := BigFppfOver.hasExt_abelian B S hS
  let : EnoughInjectives (Sheaf J AddCommGrpCat.{u}) :=
    BigFppfOver.enoughInjectives_abelian B S hS
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    BigFppfOver.wEqualsLocallyBijective_abelian B S hS
  have : EssentiallySmall.{u} (Over U) := Stacks.essentiallySmall_over U
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let G := (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} J).obj A
  let c := Stacks.CechSite.cechH1ToSliceH.{0} J E hE G
  let e₁ : Sheaf.H'.{u} A 1 U ≃+ Sheaf.H'.{w} A 1 U := Abelian.Ext.chgUnivAddEquiv
  let e₂ : Sheaf.H'.{u} A 1 U ≃+ Sheaf.H.{u} (A.over U) 1 :=
    Stacks.Cohomology.Torsors.overClassEquiv J A U
  let e₃ : Sheaf.H.{u} (A.over U) 1 ≃+ Sheaf.H.{u + 1}
      ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} (J.over U)).obj (A.over U)) 1 :=
    Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv.{u, u + 1, u + 1, u, u, u + 1} (J.over U)
      (A.over U)
  refine ⟨e₁.toAddMonoidHom.comp (e₂.symm.toAddMonoidHom.comp (e₃.symm.toAddMonoidHom.comp c)),
    e₁.injective.comp (e₂.symm.injective.comp (e₃.symm.injective.comp
      (Stacks.CechSite.cechH1ToSliceH_injective.{0} J E hE G)))⟩

/-- The structure morphism `X₀ ⟶ Spec k` of the special fibre. -/
abbrev specialFibreToField (sit : Situation k) : specialFibre sit.f ⟶ Spec (.of k) :=
  specialFibre sit.f ↘ Spec (.of k)

/-- **The Čech half of part (a).** Let `A` be an abelian sheaf on the big fppf site over `S`, let
`V₀`, `V₁` be opens covering the special fibre `X₀` and let `σ` be a section of `A` over
`V₀ ∩ V₁`. If `H¹(X₀, A)` is torsion then some positive multiple of the glueing class of `σ`
vanishes, so there are sections `s₀` over `V₀` and `s₁` over `V₁` whose restrictions to `V₀ ∩ V₁`
differ by `N σ`. -/
theorem exists_sections_of_isAddTorsion {k : Type u} [Field k] (B : BigFppfSite.{u})
    (hS : B.Contains (base k)) {X : Scheme.{u}} (fX : X ⟶ base k)
    (hXn : ∀ n, B.Contains (thickening fX n))
    (A : Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})
    [HasSheafify (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})]
    (V₀ V₁ : (thickening fX 0).Opens) (hcov : V₀ ⊔ V₁ = ⊤)
    (σ : A.obj.obj (op (openObj B hS fX hXn (V₀ ⊓ V₁))))
    (htors : IsAddTorsion (Sheaf.H' A 1 (thickeningObj B hS fX hXn 0))) :
    ∃ N, 0 < N ∧ ∃ (s₀ : A.obj.obj (op (openObj B hS fX hXn V₀)))
      (s₁ : A.obj.obj (op (openObj B hS fX hXn V₁))),
      A.obj.map (openIncl (B := B) (hS := hS) (hXn := hXn) (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op s₁ -
        A.obj.map (openIncl (B := B) (hS := hS) (hXn := hXn) (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op
          s₀ = N • σ := by
  let E := twoOpenCover B hS fX hXn V₀ V₁
  obtain ⟨χ, hχ⟩ := exists_injective_cechH1_to_H' B (base k) hS _ E
    (twoOpenCover_mem B hS fX hXn V₀ V₁ hcov) A
  let F := ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u}
    (BigFppfOver.topology B (base k) hS)).obj A).obj
  let σ' : F.obj (op (openObj B hS fX hXn (V₀ ⊓ V₁))) := ULift.up σ
  let z := twistCocycleOf (B := B) (hS := hS) (fX := fX) (hXn := hXn) (V₀ := V₀) (V₁ := V₁) F σ'
  obtain ⟨N, hNpos, hN⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
    (htors (χ (Stacks.CechSite.cls E F z)))
  have hcz : N • Stacks.CechSite.cls E F z = 0 :=
    hχ ((map_nsmul χ N _).trans (hN.trans (map_zero χ).symm))
  obtain ⟨s₀, s₁, hs⟩ := exists_sections_of_nsmul_cls_eq_zero (B := B) (hS := hS) (fX := fX)
    (hXn := hXn) (V₀ := V₀) (V₁ := V₁) F σ' N hcz
  exact ⟨N, hNpos, s₀.down, s₁.down, eq_of_uliftSheafFunctor_eq A _ _ s₁ s₀ σ' N hs⟩

/-- **The cohomological half of part (a).** For two opens `V₀`, `V₁` covering the special fibre
and a morphism `σ : V₀ ∩ V₁ ⟶ A₀` over `k`, if `H¹(X₀, A)` is torsion then some positive multiple
of the glueing class of `σ` vanishes, so there are morphisms `t₀ : V₀ ⟶ A₀` and `t₁ : V₁ ⟶ A₀`
over `k` with `t₁ = t₀ · σᴺ` on `V₀ ∩ V₁`. -/
theorem exists_relation_of_isAddTorsion (sit : Situation k) (B : BigFppfSite.{u})
    (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})]
    (V₀ V₁ : (thickening sit.f 0).Opens) (hcov : V₀ ⊔ V₁ = ⊤)
    (σk : openOver (specialFibreToField sit) (V₀ ⊓ V₁) ⟶ sit.A₀)
    (htors : IsAddTorsion (Sheaf.H' (pointsSheaf B (base k) hS sit.abelianScheme
      (sit.contains_abelianScheme hS)) 1
        (thickeningObj B hS sit.f (sit.contains_thickening hS) 0))) :
    ∃ N, 0 < N ∧ ∃ (t₀ : openOver (specialFibreToField sit) V₀ ⟶ sit.A₀)
      (t₁ : openOver (specialFibreToField sit) V₁ ⟶ sit.A₀),
      openOverHomOfLE (specialFibreToField sit) (inf_le_right : V₀ ⊓ V₁ ≤ V₁) ≫ t₁ =
        (openOverHomOfLE (specialFibreToField sit) (inf_le_left : V₀ ⊓ V₁ ≤ V₀) ≫ t₀) *
          σk ^ N := by
  let hXn := sit.contains_thickening hS
  let σ : Additive (openOverBase sit B hS hXn (V₀ ⊓ V₁) ⟶ sit.abelianScheme) :=
    Additive.ofMul ((sectionMulEquiv sit (hS := hS) (hXn := hXn) (V₀ ⊓ V₁)).symm σk)
  obtain ⟨N, hNpos, s₀, s₁, hA⟩ := exists_sections_of_isAddTorsion B hS sit.f hXn
    (pointsSheaf B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)) V₀ V₁ hcov σ htors
  let S₀ : openOverBase sit B hS hXn V₀ ⟶ sit.abelianScheme := Additive.toMul s₀
  let S₁ : openOverBase sit B hS hXn V₁ ⟶ sit.abelianScheme := Additive.toMul s₁
  have hmul : (Over.post B.inclusion).map (openIncl (B := B) (hS := hS) (hXn := hXn)
      (inf_le_right : V₀ ⊓ V₁ ≤ V₁)) ≫ S₁ =
      ((Over.post B.inclusion).map (openIncl (B := B) (hS := hS) (hXn := hXn)
        (inf_le_left : V₀ ⊓ V₁ ≤ V₀)) ≫ S₀) * (Additive.toMul σ) ^ N := by
    have h := congrArg (Additive.toMul (α := openOverBase sit B hS hXn (V₀ ⊓ V₁) ⟶
      sit.abelianScheme)) hA
    rw [pointsSheaf_toMul_sub, pointsSheaf_toMul_map, pointsSheaf_toMul_map] at h
    letI : CommGroup (openOverBase sit B hS hXn (V₀ ⊓ V₁) ⟶ sit.abelianScheme) :=
      CategoryTheory.Hom.commGroup
    exact div_eq_iff_eq_mul'.mp (h.trans (pointsSheaf_toMul_nsmul _ _ σ N))
  have hk := congrArg (sectionMulEquiv sit (hS := hS) (hXn := hXn) (V₀ ⊓ V₁)) hmul
  rw [map_mul, map_pow, sectionMulEquiv_comp, sectionMulEquiv_comp] at hk
  simp only [σ, toMul_ofMul, MulEquiv.apply_symm_apply] at hk
  exact ⟨N, hNpos, _, _, hk⟩

/-- **Part (a) of the proof of Stacks 0AFB: `H¹(X₀, A)` is not torsion.** In the situation of
Section 0AF8, the first fppf cohomology of the points sheaf of the constant abelian scheme
`A = A₀ ×_k S`, on the big fppf site over `S = Spec k⟦t⟧` at the special fibre `X₀`, is not a
torsion group. This is the hypothesis `hnotTorsion` of
`Stacks.Examples.NonAlgebraicHomStack.exists_compatible_ne_restrictTotal` and
`Stacks.Examples.NonAlgebraicHomStack.not_surjective_toCompatibleSystems`.

The class is that of the Čech cocycle on the covering `{V₀ = X₀ ∖ {x₀}, V₁}` of `X₀` which is a
point `a₀ ∈ A₀(k)` of infinite order (`Stacks.Groupoids.exists_not_isOfFinAddOrder`) on the part
`W''` of `V₀ ∩ V₁` lying on the component `C₁` through the node `x₀` of a loop of rational curves,
and `0` on the rest `W'`: the trivial torsors on the components glued with the twist `a₀` at `x₀`.
A multiple `N` of the class vanishing gives sections over `V₀` and `V₁` which agree on `W'` and
differ by `N a₀` on `W''`, and going around the loop with Stacks 0AEN gives `N a₀ = 0`. -/
theorem not_isAddTorsion_H1_specialFibre (sit : Situation k) (B : BigFppfSite.{u})
    (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})] :
    ¬ IsAddTorsion (Sheaf.H' (pointsSheaf B (base k) hS sit.abelianScheme
      (sit.contains_abelianScheme hS)) 1
        (thickeningObj B hS sit.f (sit.contains_thickening hS) 0)) := by
  classical
  intro htors
  have := sit.isAlgClosed
  have := sit.isAbelianVariety
  have := sit.isProper
  have := sit.isNoetherian
  have : LocallyOfFiniteType (specialFibreToField sit) := locallyOfFiniteType_specialFibre sit.f
  have : IsNoetherian (thickening sit.f 0) := isNoetherian_thickening sit.f 0
  -- a point of infinite order
  obtain ⟨a, ha⟩ := Stacks.Groupoids.exists_not_isOfFinAddOrder sit.not_isAlgebraic_finite sit.A₀
    (pos_topologicalKrullDim_of_not_isIso sit.A₀ sit.nonzero)
  -- the loop of rational curves and the two opens around the node `x₀`
  obtain ⟨m, hm, C, x, hCinj, hxinj, hnode, hmem, hiso⟩ := sit.hasLoop
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hxcl : ∀ i, IsClosed ({x i} : Set (specialFibre sit.f)) := fun i => (hnode i).1
  obtain ⟨V₀, V₁, W', W'', hcov, hW, hdisj, hW'le, hW''le, hx₀, hV₀, hW'C, hW''C⟩ :=
    exists_opens_of_component (specialFibre sit.f) (C 1)
      (isClosed_singleton_of_mem_component (specialFibreToField sit) (C 1) (hiso 1).some)
      (x 0) (hxcl 0)
  have hV₀' : ∀ i, i ≠ 0 → x i ∈ V₀ := fun i hi => hV₀ _ fun h => hi (hxinj h)
  -- the twist
  obtain ⟨σk, hσ', hσ''⟩ := exists_twist_section (specialFibreToField sit) sit.A₀ (V₀ ⊓ V₁) W' W''
    hW hW'le hW''le hdisj (Additive.toMul a)
  -- the cohomological half
  obtain ⟨N, hNpos, T₀, T₁, hk⟩ := exists_relation_of_isAddTorsion sit B hS V₀ V₁ hcov σk htors
  have hcomp : ∀ {P Q R : (specialFibre sit.f).Opens} (h₁ : P ≤ Q) (h₂ : Q ≤ R),
      openOverHomOfLE (specialFibreToField sit) h₁ ≫ openOverHomOfLE (specialFibreToField sit) h₂ =
        openOverHomOfLE (specialFibreToField sit) (h₁.trans h₂) :=
    fun h₁ h₂ => Over.OverMorphism.ext ((specialFibre sit.f).homOfLE_homOfLE h₁ h₂)
  have hres : ∀ {P : (specialFibre sit.f).Opens} (hP : P ≤ V₀ ⊓ V₁),
      openOverHomOfLE (specialFibreToField sit) (hP.trans inf_le_right) ≫ T₁ =
        (openOverHomOfLE (specialFibreToField sit) (hP.trans inf_le_left) ≫ T₀) *
          (openOverHomOfLE (specialFibreToField sit) hP ≫ σk) ^ N := by
    intro P hP
    have := congrArg (openOverHomOfLE (specialFibreToField sit) hP ≫ ·) hk
    simp only [MonObj.comp_mul, MonObj.comp_pow, ← Category.assoc, hcomp] at this
    exact this
  have hb : (Additive.toMul a) ^ N = 1 := by
    refine eq_one_of_loop (specialFibreToField sit) sit.A₀ n C x hCinj hxcl hmem
      (fun i => (hiso i).some) V₀ V₁ W' W''
      hcov hW (hW'le.trans inf_le_left) (hW'le.trans inf_le_right) (hW''le.trans inf_le_left)
      (hW''le.trans inf_le_right) hx₀ hV₀' hW'C (fun i hi => hW''C (C i) hi) T₀ T₁ _ ?_ ?_
    · rw [hres hW'le, hσ', one_pow, mul_one]
    · rw [hres hW''le, hσ'', MonObj.comp_mul,
        ← Category.assoc (openOverHomOfLE (specialFibreToField sit) (hW''le.trans inf_le_left))
          (toUnit _),
        toUnit_unique
          (openOverHomOfLE (specialFibreToField sit) (hW''le.trans inf_le_left) ≫ toUnit _)
          (toUnit _),
        MonObj.comp_pow]
  exact ha (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hNpos, by
    rw [← ofMul_toMul (N • a), toMul_nsmul, hb, ofMul_one]⟩)

end PartA

end Stacks.Examples.NonAlgebraicHomStack

end

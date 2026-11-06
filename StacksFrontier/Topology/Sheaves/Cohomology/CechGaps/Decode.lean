module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Decoding Mathlib's Čech complex of a presheaf on a space

For a family `U : ι → Opens X` of opens of a topological space and a presheaf `P` of abelian
groups on `X`, this file describes the terms and the differentials of the Čech complex
`(CategoryTheory.cechComplexFunctor U).obj P` degreewise.

## Main definitions

* `Stacks.CechGaps.cechEquiv`: an element of degree `n` is exactly a family of sections
  `s x ∈ P (⨅ₖ U (x k))`.
* `Stacks.CechGaps.cechAdditive`: `cechComplexFunctor U` is an additive functor.

## Main results

* `Stacks.CechGaps.prodOpens_eq_iInf`: the categorical product `∏ᶜ (U ∘ x)` in `Opens X` is
  equal to the intersection `⨅ k, U (x k)`.
* `Stacks.CechGaps.cech_X`: degree `n` of the Čech complex is `∏ᶜ x, P (⨅ₖ U (x k))`, the product
  over `x : Fin (n + 1) → ι`.
* `Stacks.CechGaps.cech_map_f`: the degree-`n` component of the map induced by `α : P ⟶ Q` is
  `Limits.Pi.map (fun x ↦ α.app _)`.
* `Stacks.CechGaps.cech_d_comp_π`: the `x`-component of the Čech differential is the alternating
  sum `∑ⱼ (-1)ʲ • (π_{x ∘ δⱼ} ≫ restriction)` over the faces `δⱼ = Fin.succAbove j`.
* `Stacks.CechGaps.cech_d_apply`: the same, on elements.

## References

* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w

namespace Stacks.CechGaps

section PiLemmas

variable {A : Type*} [Category* A] [Preadditive A] {J : Type*} {f g : J → A}
  [HasProduct f] [HasProduct g]

/-- `Limits.Pi.map` is additive in the family of morphisms. -/
lemma piMap_add (p q : ∀ j, f j ⟶ g j) :
    Limits.Pi.map (fun j ↦ p j + q j) = Limits.Pi.map p + Limits.Pi.map q :=
  Limits.Pi.hom_ext _ _ fun x ↦ by
    rw [Limits.Pi.map_π, Preadditive.add_comp, Limits.Pi.map_π, Limits.Pi.map_π,
      ← Preadditive.comp_add]

/-- `Limits.Pi.map` of the zero family is zero. -/
lemma piMap_zero : Limits.Pi.map (fun j ↦ (0 : f j ⟶ g j)) = 0 :=
  Limits.Pi.hom_ext _ _ fun x ↦ by rw [Limits.Pi.map_π, Limits.zero_comp, Limits.comp_zero]

end PiLemmas

/-- A finite `ℤ`-linear combination of morphisms of abelian groups, evaluated at an element. -/
lemma sum_zsmul_apply {A B : AddCommGrpCat.{w}} {J : Type*} [Fintype J] (c : J → ℤ)
    (t : J → (A ⟶ B)) (s : ToType A) :
    ConcreteCategory.hom (∑ j, c j • t j) s = ∑ j, c j • ConcreteCategory.hom (t j) s :=
  let ev : (A ⟶ B) →+ ToType B :=
    AddMonoidHom.mk' (fun h ↦ ConcreteCategory.hom h s) (fun _ _ ↦ rfl)
  (map_sum ev _ _).trans (Finset.sum_congr rfl fun _ _ ↦ map_zsmul ev _ _)

variable {X : Type u} [TopologicalSpace X] {ι : Type u} (U : ι → Opens X)

/-- The categorical product of the opens `U ∘ x` in `Opens X` is equal to their intersection
`⨅ k, U (x k)`. -/
lemma prodOpens_eq_iInf {n : ℕ} (x : Fin n → ι) : (∏ᶜ (U ∘ x) : Opens X) = ⨅ k, U (x k) :=
  le_antisymm (le_iInf fun k ↦ (Limits.Pi.π (U ∘ x) k).le)
    (Limits.Pi.lift (fun k ↦ homOfLE (iInf_le (fun k ↦ U (x k)) k))).le

/-- Reindexing a tuple enlarges the open it indexes: `U_{x₀…xₙ} ⊆ U_{x_{f 0}…x_{f m}}`. -/
lemma prodOpens_le {m n : ℕ} (x : Fin n → ι) (f : Fin m → Fin n) :
    (∏ᶜ (U ∘ x) : Opens X) ≤ ∏ᶜ (U ∘ (x ∘ f)) := by
  rw [prodOpens_eq_iInf, prodOpens_eq_iInf]
  exact le_iInf fun k ↦ iInf_le (fun k ↦ U (x k)) (f k)

section General

variable [HasProducts.{u} AddCommGrpCat.{w}]

/-- The family whose product is degree `n` of the Čech complex: the sections of `P` on the opens
`U_{x₀…xₙ}`, indexed by the tuples `x : Fin (n + 1) → ι`. -/
noncomputable abbrev cechDeg (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    (Fin (n + 1) → ι) → AddCommGrpCat.{w} :=
  fun x ↦ P.obj (op (∏ᶜ (U ∘ x)))

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w})

/-- The cosimplicial object of which the Čech complex is the alternating coface map complex. -/
noncomputable abbrev cechCosimp : CosimplicialObject AddCommGrpCat.{w} :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P

/-- Degree `n` of the Čech complex is the product of the sections of `P` over the opens
`U_{x₀…xₙ}`. -/
lemma cech_X (n : ℕ) : ((cechComplexFunctor U).obj P).X n = ∏ᶜ cechDeg U P n := rfl

/-- The `x`-component of the `j`-th coface map of the Čech cosimplicial object is restriction
along `U_{x₀…xₙ₊₁} ⊆ U_{x₀…x̂ⱼ…xₙ₊₁}`. -/
lemma cechCosimp_δ_comp_π (n : ℕ) (x : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    (cechCosimp U P).δ j ≫ Limits.Pi.π (cechDeg U P (n + 1)) x
      = Limits.Pi.π (cechDeg U P n) (x ∘ j.succAbove)
        ≫ P.map (homOfLE (prodOpens_le U x j.succAbove)).op := by
  rw [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  refine (Limits.Pi.lift_comp_π _ _).trans ?_
  congr 1

/-- The differential of the Čech complex is the alternating sum of the coface maps. -/
lemma cech_d_eq (n : ℕ) : ((cechComplexFunctor U).obj P).d n (n + 1)
    = AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimp U P) n := by
  dsimp only [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor, Functor.comp_obj,
    AlgebraicTopology.alternatingCofaceMapComplex_obj,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  exact CochainComplex.of_d (fun m : ℕ ↦ (cechCosimp U P).obj (SimplexCategory.mk m)) _ n

/-- The `x`-component of the Čech differential is `∑ⱼ (-1)ʲ` times restriction from
`U_{x₀…x̂ⱼ…xₙ₊₁}` to `U_{x₀…xₙ₊₁}`. -/
lemma cech_d_comp_π (n : ℕ) (x : Fin (n + 2) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ Limits.Pi.π (cechDeg U P (n + 1)) x
      = ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
          (Limits.Pi.π (cechDeg U P n) (x ∘ j.succAbove)
            ≫ P.map (homOfLE (prodOpens_le U x j.succAbove)).op) :=
  (congrArg (fun h ↦ h ≫ Limits.Pi.π (cechDeg U P (n + 1)) x) (cech_d_eq U P n)).trans
    ((Preadditive.sum_comp _ _ _).trans (Finset.sum_congr rfl fun j _ ↦
      (Preadditive.zsmul_comp _ _ _).trans
        (congrArg (fun g ↦ (-1 : ℤ) ^ (j : ℕ) • g) (cechCosimp_δ_comp_π U P n x j))))

end General

section Map

variable [HasProducts.{u} AddCommGrpCat.{w}] {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- The map of Čech complexes induced by a map of presheaves is, in each degree, the product
of its components. -/
lemma cech_map_f (α : P ⟶ Q) (n : ℕ) :
    ((cechComplexFunctor U).map α).f n
      = Limits.Pi.map (fun x : Fin (n + 1) → ι ↦ α.app (op (∏ᶜ (U ∘ x)))) := rfl

end Map

/-- `cechComplexFunctor U` is an additive functor. -/
instance cechAdditive [HasProducts.{u} AddCommGrpCat.{w}] :
    (cechComplexFunctor (A := AddCommGrpCat.{w}) U).Additive where
  map_add {P Q f g} := HomologicalComplex.hom_ext _ _ fun n ↦ by
    rw [HomologicalComplex.add_f_apply, cech_map_f, cech_map_f, cech_map_f]
    exact piMap_add _ _

section Elements

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)

/-- An element of degree `n` of the Čech complex is a family of sections of `P` over the opens
`U_{x₀…xₙ}`. -/
noncomputable def cechEquiv :
    ToType (((cechComplexFunctor U).obj P).X n) ≃
      ∀ x : Fin (n + 1) → ι, ToType (P.obj (op (∏ᶜ (U ∘ x)))) :=
  Limits.Concrete.productEquiv (cechDeg U P n)

/-- The components of an element of degree `n` are read off by the projections. -/
lemma cechEquiv_apply (s : ToType (((cechComplexFunctor U).obj P).X n))
    (x : Fin (n + 1) → ι) :
    cechEquiv U P n s x = Limits.Pi.π (cechDeg U P n) x s :=
  Limits.Concrete.productEquiv_apply_apply (cechDeg U P n) s x

/-- Building an element of degree `n` out of a family of sections. -/
lemma cechEquiv_symm_apply_π (s : ∀ x : Fin (n + 1) → ι, ToType (P.obj (op (∏ᶜ (U ∘ x)))))
    (x : Fin (n + 1) → ι) :
    Limits.Pi.π (cechDeg U P n) x ((cechEquiv U P n).symm s) = s x :=
  Limits.Concrete.productEquiv_symm_apply_π (cechDeg U P n) s x

/-- The `x`-component of the Čech differential of an element `s` is the alternating sum of the
restrictions of the components of `s`. -/
lemma cech_d_apply (s : ToType (((cechComplexFunctor U).obj P).X n))
    (x : Fin (n + 2) → ι) :
    Limits.Pi.π (cechDeg U P (n + 1)) x (((cechComplexFunctor U).obj P).d n (n + 1) s)
      = ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
          P.map (homOfLE (prodOpens_le U x j.succAbove)).op
            (Limits.Pi.π (cechDeg U P n) (x ∘ j.succAbove) s) :=
  ((ConcreteCategory.comp_apply _ _ s).symm.trans
      (congrArg (fun h : ((cechComplexFunctor U).obj P).X n ⟶ cechDeg U P (n + 1) x ↦
        ConcreteCategory.hom h s) (cech_d_comp_π U P n x))).trans
    ((sum_zsmul_apply _ _ s).trans
      (Finset.sum_congr rfl fun j _ ↦
        congrArg (fun z ↦ (-1 : ℤ) ^ (j : ℕ) • z) (ConcreteCategory.comp_apply _ _ s)))

end Elements

end Stacks.CechGaps

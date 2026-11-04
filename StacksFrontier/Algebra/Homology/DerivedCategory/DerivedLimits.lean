module

import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksFrontier.Algebra.Homology.DerivedCategory.Products
import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.CategoryTheory.Discrete.Basic
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Derived limits

Let `A` be an abelian category with countable products. This file treats derived limits of
inverse systems of its derived category `D(A)`, the limit of a tower of K-injective complexes
with degreewise split transition maps, and the existence of K-injective resolutions of
unbounded complexes.

First, if `A` has enough injectives and `F : ℕᵒᵖ ⥤ D(A)` is an inverse system `(Kₙ, fₙ)` all of
whose values are bounded below, i.e. a system of `D⁺(A)`, then the countable product `∏ Kₙ` and
the derived limit `R lim Kₙ` (`CategoryTheory.Pretriangulated.IsDerivedLimit`) exist in `D(A)`.
Note that `R lim Kₙ` is an object of `D(A)` and is in general not bounded below.

Second, let `𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ` be an inverse system of K-injective complexes whose
transition maps `𝓘ₙ₊₁ ⟶ 𝓘ₙ` are degreewise split epimorphisms. Then the limit `I = lim 𝓘`
exists, is K-injective, and represents the derived limit `R lim 𝓘ₙ` in `D(A)`. Suppose moreover
given a cochain complex `K` of `A`, not assumed bounded, together with quasi-isomorphisms
`fₙ : τ_{≥ -n} K ⟶ 𝓘ₙ` forming a commutative ladder over the canonical maps `K ⟶ τ_{≥ -n} K`.
Then `R lim 𝓘ₙ` is `R lim τ_{≥ -n} K`, and the canonical map `γ : K ⟶ I` — the unique map with
`γ ≫ πₙ = (K ⟶ τ_{≥ -n} K) ≫ fₙ` — is a quasi-isomorphism if and only if the canonical map
`c : K ⟶ R lim τ_{≥ -n} K` is an isomorphism in `D(A)`.

Third, if `A` has enough injectives and its countable products are exact (Grothendieck's axiom
AB4*), then every cochain complex `K` of objects of `A`, unbounded in both directions, admits a
quasi-isomorphism `K ⟶ I` to a K-injective complex `I`; that is, `A` has K-injective
resolutions.

## Main results

* `DerivedCategory.exists_isDerivedLimit_of_forall_isGE`: an inverse system in `D(A)` whose
  values are bounded below has a product, and hence a derived limit, in `D(A)`, whenever the
  abelian category `A` has countable products and enough injectives.
* `CochainComplex.isKInjective_limit_and_isDerivedLimit_of_isSplitEpi`: for a tower of
  K-injective complexes with degreewise split epimorphic transition maps, the limit exists, is
  K-injective, and is a derived limit of the system; and, for every complex `K` resolved by the
  system in the above sense, the canonical map `K ⟶ lim 𝓘` is a quasi-isomorphism exactly when
  the map into the derived limit of the truncations is an isomorphism.
* `CochainComplex.exists_quasiIso_isKInjective`: in an abelian category with enough injectives
  and exact countable products, every cochain complex admits a quasi-isomorphism to a
  K-injective complex.
* `CochainComplex.isIso_of_isDerivedLimit_of_eventually_isIso_homologyMap`: the content of
  Stacks 090Y that is not the reduction of Stacks 070M — a derived limit of a tower which
  receives a cone that is eventually a cohomology isomorphism in every degree is that cone's
  source.
* `CochainComplex.isIso_of_isDerivedLimit_of_quasiIso_truncGE`: the previous result for the
  system of Stacks 070F resolving the truncations `τ_{≥ -n} K`.

## References

* [Stacks Project, Tag 0BK7](https://stacks.math.columbia.edu/tag/0BK7)
* [Stacks Project, Tag 070M](https://stacks.math.columbia.edu/tag/070M)
* [Stacks Project, Tag 090Y](https://stacks.math.columbia.edu/tag/090Y)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC), for `IsDerivedLimit`
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6), for termwise products
  of K-injective complexes
* [Stacks Project, Tag 090X](https://stacks.math.columbia.edu/tag/090X), for K-injectivity in a
  distinguished triangle
* [Stacks Project, Tag 0H72](https://stacks.math.columbia.edu/tag/0H72), for the map `c`
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC), for the cohomology of a
  countable product
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe w v u w₁ v₁ v₂ u₁ u₂

/-! ### Limit fans of complexes -/

section FanHom

variable {C : Type u₁} [Category.{v₁} C] {α : Type w} {L : α → C} {t : Fan L}

/-- The family of components of a morphism into the vertex of a fan. -/
private def fanHom (t : Fan L) (X : C) (φ : X ⟶ t.pt) (a : α) : X ⟶ L a := φ ≫ t.proj a

@[local simp]
private lemma fanHom_apply (t : Fan L) {X : C} (φ : X ⟶ t.pt) (a : α) :
    fanHom t X φ a = φ ≫ t.proj a := rfl

private lemma bijective_fanHom (ht : IsLimit t) (X : C) : Function.Bijective (fanHom t X) :=
  ⟨fun _ _ h ↦ Fan.IsLimit.hom_ext ht _ _ fun a ↦ congrFun h a,
    fun u ↦ ⟨Fan.IsLimit.lift ht u, funext (Fan.IsLimit.fac ht u)⟩⟩

/-- A fan whose components map is bijective for every object is a limit fan. -/
private noncomputable def isLimitOfBijectiveFanHom
    (h : ∀ X : C, Function.Bijective (fanHom t X)) : IsLimit t :=
  Fan.IsLimit.mk _ (fun s ↦ ((h s.pt).existsUnique s.proj).choose)
    (fun s a ↦ congrFun ((h s.pt).existsUnique s.proj).choose_spec.1 a)
    (fun s m hm ↦ ((h s.pt).existsUnique s.proj).choose_spec.2 m (funext hm))

/-- Bijectivity of the components map only depends on the isomorphism class of the object. -/
private lemma bijective_fanHom_of_iso {X Y : C} (e : X ≅ Y)
    (h : Function.Bijective (fanHom t X)) : Function.Bijective (fanHom t Y) := by
  have hnat : fanHom t Y ∘ e.homFromEquiv
      = Pi.map (fun a ↦ (e.homFromEquiv (Z := L a) : (X ⟶ L a) → (Y ⟶ L a))) ∘ fanHom t X := by
    funext φ a
    simp
  refine (Function.Bijective.of_comp_iff _ (e.homFromEquiv (Z := t.pt)).bijective).1 ?_
  rw [hnat]
  exact (Function.Bijective.piMap fun a ↦ (e.homFromEquiv (Z := L a)).bijective).comp h

variable {D : Type u₂} [Category.{v₂} D]

/-- Taking the components of a morphism into the vertex of a fan commutes with a functor. -/
private lemma fanHom_comp_map (G : C ⥤ D) (Y : C) :
    fanHom (Fan.mk (G.obj t.pt) fun a => G.map (t.proj a)) (G.obj Y) ∘ G.map
      = Pi.map (fun a (f : Y ⟶ L a) => G.map f) ∘ fanHom t Y := by
  funext ψ a
  simp

/-- A functor which is essentially surjective and induces bijections on the morphisms into the
vertex and into the objects of a limit fan sends it to a limit fan. -/
private noncomputable def isLimitMapFan (G : C ⥤ D) [G.EssSurj] (ht : IsLimit t)
    (hpt : ∀ Y : C, Function.Bijective (G.map : (Y ⟶ t.pt) → _))
    (hL : ∀ (Y : C) (a : α), Function.Bijective (G.map : (Y ⟶ L a) → _)) :
    IsLimit (Fan.mk (G.obj t.pt) fun a => G.map (t.proj a)) :=
  isLimitOfBijectiveFanHom fun X ↦
    bijective_fanHom_of_iso (G.objObjPreimageIso X)
      ((Function.Bijective.of_comp_iff _ (hpt _)).1 (by
        rw [fanHom_comp_map]
        exact (Function.Bijective.piMap fun a ↦ hL _ a).comp (bijective_fanHom ht _)))

end FanHom

section Fan

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {α : Type w} {L : α → HomologicalComplex C c} [HasProductsOfShape α C] {t : Fan L}

/-- A limit fan of complexes is a limit fan in each degree. -/
private noncomputable def isLimitFanEval (ht : IsLimit t) (j : ι) :
    IsLimit (Fan.mk (t.pt.X j) fun a => (t.proj a).f j) :=
  Fan.isLimitMapConeEquiv (HomologicalComplex.eval C c j) L t (isLimitOfPreserves _ ht)

@[local simp]
private lemma isLimitFanEval_lift_proj (ht : IsLimit t) (j : ι) {X : C}
    (u : ∀ a, X ⟶ (L a).X j) (a : α) :
    Fan.IsLimit.lift (isLimitFanEval ht j) u ≫ (t.proj a).f j = u a :=
  Fan.IsLimit.fac (isLimitFanEval ht j) u a

/-- Two morphisms into the vertex of a limit fan of complexes are homotopic as soon as their
components are. -/
private noncomputable def homotopyOfFan (ht : IsLimit t) {K : HomologicalComplex C c}
    {f g : K ⟶ t.pt} (h : ∀ a, Homotopy (f ≫ t.proj a) (g ≫ t.proj a)) :
    Homotopy f g where
  hom i j := Fan.IsLimit.lift (isLimitFanEval ht j) fun a ↦ (h a).hom i j
  zero i j hij := Fan.IsLimit.hom_ext (isLimitFanEval ht j) _ _ fun a ↦ by
    simp [(h a).zero i j hij]
  comm i := Fan.IsLimit.hom_ext (isLimitFanEval ht i) _ _ fun a ↦ by
    simpa only [fan_mk_proj, Preadditive.add_comp, ← dNext_comp_right, ← prevD_comp_right,
      isLimitFanEval_lift_proj, ← HomologicalComplex.comp_f] using (h a).comm i

end Fan

section KInjective

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {α : Type w} {L : α → CochainComplex C ℤ}
  [HasProductsOfShape α C] {t : Fan L}

/-- The vertex of a limit fan of K-injective cochain complexes is K-injective. -/
private lemma isKInjective_of_isLimit (ht : IsLimit t) [∀ a, (L a).IsKInjective] :
    t.pt.IsKInjective where
  nonempty_homotopy_zero {_K} f hK :=
    ⟨homotopyOfFan ht (fun a ↦
      (CochainComplex.IsKInjective.homotopyZero (f ≫ t.proj a) hK).trans
        (Homotopy.ofEq zero_comp.symm))⟩

/-- The image in the homotopy category of a limit fan of cochain complexes is a limit fan: the
vertex is a product up to homotopy. -/
private noncomputable def isLimitFanQuotient (ht : IsLimit t) :
    IsLimit (Fan.mk ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj t.pt)
      (fun a => (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (t.proj a))) :=
  isLimitOfBijectiveFanHom fun Y ↦ by
    obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    refine ⟨fun ψ₁ ψ₂ hψ ↦ ?_, ?_⟩
    · obtain ⟨v₁, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective ψ₁
      obtain ⟨v₂, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective ψ₂
      exact HomotopyCategory.eq_of_homotopy _ _ (homotopyOfFan ht fun a ↦
        HomotopyCategory.homotopyOfEq _ _ (by simpa [fanHom_apply] using congrFun hψ a))
    · refine Function.Surjective.of_comp
        (g := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map) ?_
      rw [fanHom_comp_map]
      exact (Function.Surjective.piMap fun a ↦
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective).comp
          (bijective_fanHom ht Y).surjective

variable [HasDerivedCategory C]

/-- The image in the derived category of the vertex of a limit fan of K-injective cochain
complexes is a product of the images of the complexes. -/
private noncomputable def isLimitFanQh (ht : IsLimit t) [∀ a, (L a).IsKInjective] :
    IsLimit (Fan.mk (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj t.pt))
      (fun a => DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (t.proj a)))) :=
  have := isKInjective_of_isLimit ht
  isLimitMapFan DerivedCategory.Qh (isLimitFanQuotient ht)
    (fun Y ↦ CochainComplex.IsKInjective.Qh_map_bijective Y t.pt)
    (fun Y a ↦ CochainComplex.IsKInjective.Qh_map_bijective Y (L a))

end KInjective

namespace DerivedCategory

/-! ### Products of bounded below objects of the derived category -/

section Product

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C] [HasDerivedCategory C]

/-- A bounded below object of the derived category is the image of a K-injective cochain
complex. -/
private lemma exists_isKInjective_iso (X : DerivedCategory C) (a : ℤ) [X.IsGE a] :
    ∃ (L : CochainComplex C ℤ) (_ : L.IsKInjective), Nonempty (X ≅ DerivedCategory.Q.obj L) := by
  obtain ⟨K, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE a
  obtain ⟨M, i, _, hM, _⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K a
  have : IsIso (DerivedCategory.Q.map i) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  exact ⟨M, CochainComplex.isKInjective_of_injective M a,
    ⟨e ≪≫ asIso (DerivedCategory.Q.map i)⟩⟩

/-- A family of bounded below objects of the derived category of an abelian category with enough
injectives, indexed by a type whose products exist in that category, has a product in the derived
category. -/
private lemma hasProduct_of_forall_isGE {α : Type w} [HasProductsOfShape α C]
    (X : α → DerivedCategory C) (hX : ∀ a, ∃ n : ℤ, (X a).IsGE n) : HasProduct X := by
  have h : ∀ a, ∃ (M : CochainComplex C ℤ) (_ : M.IsKInjective),
      Nonempty (X a ≅ DerivedCategory.Q.obj M) := fun a ↦ by
    obtain ⟨n, _⟩ := hX a
    exact exists_isKInjective_iso _ n
  choose M _hM e using h
  have : HasProduct fun a ↦ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (M a)) :=
    ⟨_, isLimitFanQh (productIsProduct M)⟩
  refine hasLimit_of_iso (F := Discrete.functor fun a ↦ DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (M a))) (Discrete.natIso ?_)
  rintro ⟨a⟩
  exact (DerivedCategory.quotientCompQhIso C).app (M a) ≪≫ (e a).some.symm

end Product

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasProductsOfShape ℕ 𝒜]
  [EnoughInjectives 𝒜] [HasDerivedCategory 𝒜]

/-- Let `𝒜` be an abelian category with countable products and enough injectives. Then any
inverse system `F : ℕᵒᵖ ⥤ D(𝒜)` of objects of `D⁺(𝒜)`, i.e. whose values `Kₙ = F.obj ⟨n⟩` are
bounded below, has a product `∏ Kₙ` in `D(𝒜)` and a derived limit `K = R lim Kₙ`: an object
sitting in a distinguished triangle `K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ K⟦1⟧` whose middle map is
`(kₙ) ↦ (kₙ - fₙ₊₁(kₙ₊₁))`. -/
@[stacks 0BK7]
public theorem exists_isDerivedLimit_of_forall_isGE (F : ℕᵒᵖ ⥤ DerivedCategory 𝒜)
    (hF : ∀ n : ℕ, ∃ a : ℤ, (F.obj ⟨n⟩).IsGE a) :
    ∃ (_ : HasProduct fun n : ℕ => F.obj ⟨n⟩) (K : DerivedCategory 𝒜), IsDerivedLimit F K :=
  have := hasProduct_of_forall_isGE (fun n : ℕ ↦ F.obj ⟨n⟩) hF
  ⟨this, exists_isDerivedLimit F⟩

end DerivedCategory

namespace CochainComplex

/-! ### The section of the difference map of a tower -/

section TowerW

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The components of the section of the difference map of a tower: `w 0 = 0` and
`w (n + 1) = (w n - pₙ) ≫ σₙ`, where `σₙ` is a section of the `n`-th transition map. Unwound,
`w n = -∑_{k < n} pₖ ≫ σₖ ⋯ σₙ₋₁`. -/
private def towerW {P : A} (V : ℕ → A) (p : ∀ n, P ⟶ V n)
    (σ : ∀ n, V n ⟶ V (n + 1)) : ∀ n : ℕ, P ⟶ V n
  | 0 => 0
  | (n + 1) => (towerW V p σ n - p n) ≫ σ n

end TowerW

/-! ### The limit of a tower of K-injective complexes with degreewise split transition maps -/

section KInjectiveTower

open Category DerivedCategory

section

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]

/-- Countable products exist in a category with products indexed by `ℕ` and finite products. -/
private lemma hasProductsOfShape_of_countable (J : Type) [Countable J] :
    HasProductsOfShape J A := by
  rcases finite_or_infinite J with _ | _
  · infer_instance
  · exact hasLimitsOfShape_of_equivalence
      (Discrete.equivalence (nonempty_equiv_of_countable.some : J ≃ ℕ)).symm

/-- An abelian category with countable products has limits of shape `ℕᵒᵖ`. -/
private lemma hasLimitsOfShape_natOp : HasLimitsOfShape ℕᵒᵖ A := by
  have : Countable ℕᵒᵖ := Countable.of_equiv ℕ Opposite.equivToOpposite
  have h1 := hasProductsOfShape_of_countable (A := A) ℕᵒᵖ
  have h2 := hasProductsOfShape_of_countable (A := A) (Σ p : ℕᵒᵖ × ℕᵒᵖ, p.1 ⟶ p.2)
  exact ⟨fun F ↦ hasLimit_of_equalizer_and_product F⟩

/-- An inverse system of cochain complexes in an abelian category with countable products has a
limit, computed degreewise. -/
private lemma hasLimit_natOp (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) : HasLimit F := by
  have := hasLimitsOfShape_natOp (A := A)
  infer_instance

end

section

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The map `(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))` on the product of an inverse system, whose cone is a
derived limit of the system. -/
private noncomputable abbrev diffMap (F : ℕᵒᵖ ⥤ DerivedCategory A)
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] :
    (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ⟶ ∏ᶜ fun n : ℕ => F.obj ⟨n⟩ :=
  Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op

/-- In any category, if `u ≫ v` is an isomorphism then `u` is an isomorphism if and only if `v`
is. -/
private lemma isIso_iff_isIso_of_comp_isIso {C : Type*} [Category C] {X Y Z : C}
    (u : X ⟶ Y) (v : Y ⟶ Z) [IsIso (u ≫ v)] : IsIso u ↔ IsIso v := by
  refine ⟨fun _ ↦ IsIso.of_isIso_comp_left u v, fun _ ↦ ?_⟩
  rw [show u = (u ≫ v) ≫ inv v by simp]
  infer_instance

end

section

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]
  [HasDerivedCategory.{w} A]

/-- The canonical map from the image in `D(A)` of the limit of an inverse system of complexes to
the product of the images of its terms. -/
private noncomputable abbrev limPi (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit 𝓘]
    [HasProduct fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩] :
    Q.obj (limit 𝓘) ⟶ ∏ᶜ fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩ :=
  Pi.lift fun n : ℕ ↦ Q.map (limit.π 𝓘 ⟨n⟩)

/-- The transition map `𝓘ₙ₊₁ ⟶ 𝓘ₙ` of an inverse system indexed by `ℕᵒᵖ`. -/
private abbrev tow (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) : 𝓘.obj ⟨n + 1⟩ ⟶ 𝓘.obj ⟨n⟩ :=
  𝓘.map (homOfLE (Nat.le_succ n)).op

/-- The short complex `0 → lim 𝓘 → ∏ₙ 𝓘ₙ → ∏ₙ 𝓘ₙ → 0` of the source: the first map is given by
the projections of the limit, the second by `(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))`. -/
@[simps] private noncomputable def towerShortComplex (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit 𝓘] :
    ShortComplex (CochainComplex A ℤ) where
  X₁ := limit 𝓘
  X₂ := ∏ᶜ fun n : ℕ ↦ 𝓘.obj ⟨n⟩
  X₃ := ∏ᶜ fun n : ℕ ↦ 𝓘.obj ⟨n⟩
  f := Pi.lift fun n : ℕ ↦ limit.π 𝓘 ⟨n⟩
  g := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) (n + 1) ≫ tow 𝓘 n
  zero := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp only [zero_comp, assoc, Pi.lift_π, Preadditive.comp_sub, Pi.lift_π_assoc]
    rw [sub_eq_zero]
    exact (limit.w 𝓘 (homOfLE (Nat.le_succ n)).op).symm

/-- A product of cochain complexes is computed degreewise: in each degree `q` the object
`(∏ⱼ Iⱼ)ᵠ`, with the components of the projections, is a product of the `Iⱼᵠ`. This is
`HomologicalComplex.eval` preserving limits. -/
private noncomputable def evalPiIsLimit {J : Type} [HasProductsOfShape J A]
    (I : J → CochainComplex A ℤ) (q : ℤ) :
    IsLimit (Fan.mk (f := fun j ↦ (I j).X q) ((∏ᶜ I).X q) fun j ↦ (Pi.π I j).f q) :=
  isLimitFanMkObjOfIsLimit (HomologicalComplex.eval A (ComplexShape.up ℤ) q) _ _
    (productIsProduct I)

omit [HasProductsOfShape ℕ A] [HasDerivedCategory.{w} A] in
/-- **Stacks 0BK6, statement 1.** A termwise product of K-injective cochain complexes is
K-injective. -/
private theorem isKInjective_pi {J : Type} [HasProductsOfShape J A]
    (I : J → CochainComplex A ℤ)
    (hI : ∀ j, (I j).IsKInjective) : (∏ᶜ I).IsKInjective :=
  have : ∀ j, (I j).IsKInjective := hI
  isKInjective_of_isLimit (productIsProduct I)

/-- The localization functor `CochainComplex A ℤ ⥤ K(A)`. -/
private abbrev Kq : CochainComplex A ℤ ⥤ HomotopyCategory A (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient A (ComplexShape.up ℤ)

omit [HasProductsOfShape ℕ A] [HasDerivedCategory.{w} A] in
/-- A termwise product of complexes is a product in the homotopy category `K(A)`: a morphism into
it is the same as the family of its components. -/
private theorem bijective_quotient_comp_π {J : Type} [HasProductsOfShape J A]
    (I : J → CochainComplex A ℤ) (X : CochainComplex A ℤ) :
    Function.Bijective (fun (v : Kq.obj X ⟶ Kq.obj (∏ᶜ I)) (j : J) =>
      v ≫ Kq.map (Pi.π I j)) :=
  bijective_fanHom (isLimitFanQuotient (productIsProduct I)) (Kq.obj X)

omit [HasProductsOfShape ℕ A] in
/-- **Stacks 0BK6, statement 2.** A termwise product of K-injective cochain complexes represents
the product in `D(A)`: for every object `T` of `D(A)` the map
`Hom_{D(A)}(T, ∏ Iⱼ) → ∏ Hom_{D(A)}(T, Iⱼ)` is bijective. -/
private theorem bijective_comp_Q_pi_π {J : Type} [HasProductsOfShape J A]
    (I : J → CochainComplex A ℤ) (hI : ∀ j, (I j).IsKInjective) (T : DerivedCategory A) :
    Function.Bijective (fun (u : T ⟶ Q.obj (∏ᶜ I)) (j : J) => u ≫ Q.map (Pi.π I j)) := by
  have := isKInjective_pi I hI
  have key : ∀ X : CochainComplex A ℤ, Function.Bijective
      (fun (u : Q.obj X ⟶ Q.obj (∏ᶜ I)) (j : J) ↦ u ≫ Q.map (Pi.π I j)) := by
    intro X
    have h1 := CochainComplex.IsKInjective.Qh_map_bijective (Kq.obj X) (∏ᶜ I)
    have h2 : ∀ j, Function.Bijective (DerivedCategory.Qh.map :
        (Kq.obj X ⟶ Kq.obj (I j)) → _) := fun j ↦ by
      have := hI j
      exact CochainComplex.IsKInjective.Qh_map_bijective (Kq.obj X) (I j)
    constructor
    · intro u₁ u₂ h
      obtain ⟨v₁, rfl⟩ := h1.surjective u₁
      obtain ⟨v₂, rfl⟩ := h1.surjective u₂
      refine congrArg DerivedCategory.Qh.map ((bijective_quotient_comp_π I X).injective ?_)
      funext j
      refine (h2 j).injective ?_
      rw [Functor.map_comp, Functor.map_comp]
      exact congrFun h j
    · intro w
      choose w' hw' using fun j ↦ (h2 j).surjective (w j)
      obtain ⟨v, hv⟩ := (bijective_quotient_comp_π I X).surjective w'
      refine ⟨DerivedCategory.Qh.map v, ?_⟩
      funext j
      have hvj : v ≫ Kq.map (Pi.π I j) = w' j := congrFun hv j
      change DerivedCategory.Qh.map v ≫ Q.map (Pi.π I j) = w j
      exact (DerivedCategory.Qh.map_comp v (Kq.map (Pi.π I j))).symm.trans
        ((congrArg DerivedCategory.Qh.map hvj).trans (hw' j))
  exact bijective_fanHom_of_iso (t := Fan.mk (f := fun j ↦ Q.obj (I j)) (Q.obj (∏ᶜ I))
    fun j ↦ Q.map (Pi.π I j)) (Q.objObjPreimageIso T) (key _)

/-- **Stacks 0BK6, statement 2**, as a limit: the image of a termwise product of K-injective
complexes is a product in `D(A)`. -/
private noncomputable def isLimit_fan_Q_pi {J : Type} [HasProductsOfShape J A]
    (I : J → CochainComplex A ℤ)
    (hI : ∀ j, (I j).IsKInjective) :
    IsLimit (Fan.mk (f := fun j ↦ Q.obj (I j)) (Q.obj (∏ᶜ I)) fun j ↦ Q.map (Pi.π I j)) :=
  isLimitOfBijectiveFanHom fun T ↦ bijective_comp_Q_pi_π I hI T

omit [HasProductsOfShape ℕ A] [HasDerivedCategory.{w} A] in
/-- The splitting of the difference short complex of a tower, in the abstract form used in each
degree. Let `V : ℕ → A` be a tower with transition maps `t n : V (n+1) ⟶ V n` admitting sections
`σ n`, let `P` with projections `p` be a product of the `V n` and `L` with projections `q` a limit
of the tower, and let `f : L ⟶ P` and `g : P ⟶ P` be the maps determined by `f ≫ p n = q n` and
`g ≫ p n = p n - p (n+1) ≫ t n`. Then `0 → L → P → P → 0` is split. -/
private theorem towerSplittingData {L P : A} (V : ℕ → A)
    (p : ∀ n, P ⟶ V n) (hP : IsLimit (Fan.mk (f := V) P p))
    (t : ∀ n, V (n + 1) ⟶ V n) (σ : ∀ n, V n ⟶ V (n + 1)) (hσ : ∀ n, σ n ≫ t n = 𝟙 (V n))
    (q : ∀ n, L ⟶ V n) (hq : ∀ n, q (n + 1) ≫ t n = q n)
    (hL : ∀ {T : A} (u : ∀ n, T ⟶ V n), (∀ n, u (n + 1) ≫ t n = u n) →
      ∃! m : T ⟶ L, ∀ n, m ≫ q n = u n)
    (f : L ⟶ P) (hf : ∀ n, f ≫ p n = q n)
    (g : P ⟶ P) (hg : ∀ n, g ≫ p n = p n - p (n + 1) ≫ t n)
    (hfg : f ≫ g = 0) :
    ∃ (r : P ⟶ L) (s : P ⟶ P), f ≫ r = 𝟙 L ∧ s ≫ g = 𝟙 P ∧ r ≫ f + g ≫ s = 𝟙 P := by
  obtain ⟨w, hws⟩ : ∃ w : ∀ n, P ⟶ V n, ∀ n, w (n + 1) = (w n - p n) ≫ σ n :=
    ⟨towerW V p σ, fun _ ↦ rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : P ⟶ P, ∀ n, s ≫ p n = w n :=
    ⟨hP.lift (Fan.mk P w), fun n ↦ hP.fac (Fan.mk P w) ⟨n⟩⟩
  have hsg : s ≫ g = 𝟙 P := by
    refine hP.hom_ext fun j ↦ ?_
    obtain ⟨n⟩ := j
    simp only [Fan.mk_π_app]
    have h1 : s ≫ p (n + 1) ≫ t n = (w n - p n) ≫ 𝟙 (V n) := by
      rw [← Category.assoc, hs (n + 1), hws n, Category.assoc, hσ n]
    rw [Category.assoc, hg n, Preadditive.comp_sub, hs n, h1, Category.comp_id,
      sub_sub_cancel, Category.id_comp]
  have hv : ∀ n : ℕ, (p (n + 1) - g ≫ w (n + 1)) ≫ t n = p n - g ≫ w n := by
    intro n
    have h1 : (g ≫ w (n + 1)) ≫ t n = g ≫ w n - (p n - p (n + 1) ≫ t n) := by
      rw [hws n, Category.assoc, Category.assoc, hσ n, Category.comp_id,
        Preadditive.comp_sub, hg n]
    rw [Preadditive.sub_comp, h1]
    abel
  obtain ⟨r, hr, -⟩ := hL (fun n ↦ p n - g ≫ w n) hv
  refine ⟨r, s, ?_, hsg, ?_⟩
  · obtain ⟨m, -, hmuniq⟩ := hL q hq
    have h1 : ∀ n, (f ≫ r) ≫ q n = q n := by
      intro n
      rw [Category.assoc, hr n, Preadditive.comp_sub, hf n, ← Category.assoc, hfg,
        zero_comp, sub_zero]
    exact (hmuniq _ h1).trans (hmuniq _ (fun n ↦ Category.id_comp _)).symm
  · refine hP.hom_ext fun j ↦ ?_
    obtain ⟨n⟩ := j
    simp only [Fan.mk_π_app]
    rw [Preadditive.add_comp, Category.assoc, hf n, hr n, Category.assoc, hs n,
      Category.id_comp]
    abel

/-- **The degreewise splitting of `towerShortComplex`**, for a tower whose transition maps are
degreewise split epimorphisms. -/
private noncomputable def towerSplitting (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit 𝓘]
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((tow 𝓘 n).f i)) (i : ℤ) :
    ((towerShortComplex 𝓘).map (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting := by
  haveI : HasLimitsOfShape ℕᵒᵖ A := hasLimitsOfShape_natOp (A := A)
  have hLim := isLimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) i)
    (limit.isLimit 𝓘)
  have hq : ∀ n : ℕ, (limit.π 𝓘 ⟨n + 1⟩).f i ≫ (tow 𝓘 n).f i = (limit.π 𝓘 ⟨n⟩).f i := fun n ↦ by
    rw [← HomologicalComplex.comp_f]
    exact congrArg (fun φ : limit 𝓘 ⟶ 𝓘.obj ⟨n⟩ ↦ φ.f i)
      (limit.w 𝓘 (homOfLE (Nat.le_succ n)).op)
  have hL : ∀ {T : A} (u : ∀ n : ℕ, T ⟶ (𝓘.obj ⟨n⟩).X i),
      (∀ n, u (n + 1) ≫ (tow 𝓘 n).f i = u n) →
      ∃! m : T ⟶ (limit 𝓘).X i, ∀ n, m ≫ (limit.π 𝓘 ⟨n⟩).f i = u n := by
    intro T u hu
    let c : Cone (𝓘 ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i) :=
      { pt := T
        π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj T) u
          (fun n ↦ by simpa using (hu n).symm) }
    refine ⟨hLim.lift c, fun n ↦ hLim.fac c ⟨n⟩, fun y hy ↦ hLim.uniq c y ?_⟩
    intro j
    obtain ⟨n⟩ := j
    exact hy n
  have hf : ∀ n : ℕ, (Pi.lift fun n : ℕ ↦ limit.π 𝓘 ⟨n⟩).f i ≫
      (Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n).f i = (limit.π 𝓘 ⟨n⟩).f i := fun n ↦ by
    rw [← HomologicalComplex.comp_f, Pi.lift_π]
  have hg : ∀ n : ℕ, (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) (n + 1) ≫ tow 𝓘 n).f i ≫
      (Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n).f i
      = (Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n).f i
        - (Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) (n + 1)).f i ≫ (tow 𝓘 n).f i := fun n ↦ by
    rw [← HomologicalComplex.comp_f, Pi.lift_π]
    simp
  have hfg : (Pi.lift fun n : ℕ ↦ limit.π 𝓘 ⟨n⟩).f i ≫
      (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) (n + 1) ≫ tow 𝓘 n).f i = 0 := by
    rw [← HomologicalComplex.comp_f,
      show (Pi.lift fun n : ℕ ↦ limit.π 𝓘 ⟨n⟩) ≫
          (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) (n + 1) ≫ tow 𝓘 n) = 0 from
        (towerShortComplex 𝓘).zero]
    simp
  have H := towerSplittingData
    (fun n : ℕ ↦ (𝓘.obj ⟨n⟩).X i)
    (fun n ↦ (Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n).f i)
    (evalPiIsLimit (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) i)
    (fun n ↦ (tow 𝓘 n).f i)
    (fun n ↦ @section_ A _ _ _ ((tow 𝓘 n).f i) (hsplit n i))
    (fun n ↦ @IsSplitEpi.id A _ _ _ ((tow 𝓘 n).f i) (hsplit n i))
    (fun n ↦ (limit.π 𝓘 ⟨n⟩).f i) hq hL
    ((Pi.lift fun n : ℕ ↦ limit.π 𝓘 ⟨n⟩).f i) hf
    ((Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) (n + 1) ≫ tow 𝓘 n).f i) hg hfg
  exact { r := H.choose, s := H.choose_spec.choose,
          f_r := H.choose_spec.choose_spec.1,
          s_g := H.choose_spec.choose_spec.2.1,
          id := H.choose_spec.choose_spec.2.2 }

-- `towerShortComplex.X₂` is `∏ᶜ 𝓘ₙ` only after unfolding, which `rw` will not do on its own.
set_option backward.isDefEq.respectTransparency false in
/-- **The geometric input of Stacks 070M.** For an inverse system `𝓘` of
K-injective complexes with degreewise split epimorphic transition maps, the product `∏ₙ 𝓘ₙ`
exists in `D(A)`, the limit `lim 𝓘` is K-injective, and the canonical map
`Q (lim 𝓘) ⟶ ∏ₙ Q 𝓘ₙ` fits in a distinguished triangle whose second map is the difference map. -/
private theorem exists_hasProduct_isKInjective_and_distTriang
    (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) (h𝓘 : ∀ n : ℕ, (𝓘.obj ⟨n⟩).IsKInjective)
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((𝓘.map (homOfLE (Nat.le_succ n)).op).f i))
    [HasLimit 𝓘] :
    ∃ _ : HasProduct fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩, (limit 𝓘).IsKInjective ∧
      ∃ δ₀ : (∏ᶜ fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) ⟶ (Q.obj (limit 𝓘))⟦(1 : ℤ)⟧,
        Triangle.mk (limPi 𝓘) (diffMap (𝓘 ⋙ Q)) δ₀ ∈ distTriang (DerivedCategory A) := by
  have hfan : IsLimit (Fan.mk (f := fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩)
      (Q.obj (∏ᶜ fun n : ℕ ↦ 𝓘.obj ⟨n⟩))
      fun n : ℕ ↦ Q.map (Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n)) :=
    isLimit_fan_Q_pi (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) h𝓘
  have hP : HasProduct fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩ := ⟨_, hfan⟩
  have hdist := CochainComplex.trianglehOfDegreewiseSplit_distinguished (towerShortComplex 𝓘)
    (towerSplitting 𝓘 hsplit)
  refine ⟨hP, ?_, ?_⟩
  · have hpi := (CochainComplex.isKInjective_iff_rightOrthogonal _).1
      (isKInjective_pi (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) h𝓘)
    rw [CochainComplex.isKInjective_iff_rightOrthogonal]
    exact ObjectProperty.ext_of_isTriangulatedClosed₁ _ _ hdist hpi hpi
  have hdistD := DerivedCategory.Qh.map_distinguished _ hdist
  have hSf : (towerShortComplex 𝓘).f = Pi.lift fun n : ℕ ↦ limit.π 𝓘 ⟨n⟩ := rfl
  have hSg : (towerShortComplex 𝓘).g = Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) (n + 1) ≫ tow 𝓘 n := rfl
  obtain ⟨e, he⟩ :
      Σ' e : Q.obj (∏ᶜ fun n : ℕ ↦ 𝓘.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩,
        ∀ n : ℕ, e.hom ≫ Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) n
          = Q.map (Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n) :=
    ⟨hfan.conePointUniqueUpToIso (productIsProduct _), fun n ↦ by
      simpa [Fan.proj] using hfan.conePointUniqueUpToIso_hom_comp (productIsProduct _) ⟨n⟩⟩
  have he' : ∀ n : ℕ, e.inv ≫ Q.map (Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n)
      = Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) n := fun n ↦ by
    rw [← he n, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have h1 : limPi 𝓘 ≫ e.inv = Q.map ((towerShortComplex 𝓘).f) := by
    have h : Q.map (Pi.lift fun n : ℕ ↦ limit.π 𝓘 ⟨n⟩) ≫ e.hom = limPi 𝓘 := by
      refine Pi.hom_ext _ _ fun n ↦ ?_
      rw [Category.assoc, he n, ← Q.map_comp, Pi.lift_π, limPi, Pi.lift_π]
    rw [hSf, ← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  have h2 : diffMap (𝓘 ⋙ Q) ≫ e.inv = e.inv ≫ Q.map ((towerShortComplex 𝓘).g) := by
    refine Fan.IsLimit.hom_ext hfan _ _ fun n ↦ ?_
    have hR : e.inv ≫ Q.map ((towerShortComplex 𝓘).g) ≫
        Q.map (Pi.π (fun n : ℕ ↦ 𝓘.obj ⟨n⟩) n)
        = Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) (n + 1) ≫
            (𝓘 ⋙ Q).map (homOfLE (Nat.le_succ n)).op := by
      rw [← Q.map_comp, hSg, Pi.lift_π, Q.map_sub, Q.map_comp, Preadditive.comp_sub,
        he' n, ← Category.assoc, he' (n + 1)]
      rfl
    have hLl : diffMap (𝓘 ⋙ Q) ≫ Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) n
        = Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) (n + 1) ≫
            (𝓘 ⋙ Q).map (homOfLE (Nat.le_succ n)).op := by
      rw [Pi.lift_π]
    simp only [Fan.proj, Fan.mk_π_app, Category.assoc, he' n]
    rw [hLl, hR]
  have h1' : limPi 𝓘 ≫ e.inv
      = 𝟙 (Q.obj (limit 𝓘)) ≫ Q.map ((towerShortComplex 𝓘).f) := by
    rw [Category.id_comp]
    exact h1
  exact ⟨e.inv ≫ (DerivedCategory.Qh.mapTriangle.obj
      (CochainComplex.trianglehOfDegreewiseSplit (towerShortComplex 𝓘)
        (towerSplitting 𝓘 hsplit))).mor₃,
    isomorphic_distinguished _ hdistD _
      (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm h1' h2 (by simp))⟩

omit [HasProductsOfShape ℕ A] [HasDerivedCategory.{w} A] in
/-- The canonical map `γ : K ⟶ lim 𝓘` attached to a commutative ladder of maps
`τ_{≥ -n} K ⟶ 𝓘ₙ`. -/
private lemma exists_gamma (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit 𝓘]
    (K : CochainComplex A ℤ) (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ 𝓘.obj ⟨n⟩)
    (hladder : ∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫
      𝓘.map (homOfLE (Nat.le_succ n)).op = K.πTruncGE (-(n : ℤ)) ≫ f n) :
    ∃ γ : K ⟶ limit 𝓘, ∀ n : ℕ, γ ≫ limit.π 𝓘 ⟨n⟩ = K.πTruncGE (-(n : ℤ)) ≫ f n := by
  let c : Cone 𝓘 :=
    { pt := K
      π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj K) (G := 𝓘)
        (fun n ↦ K.πTruncGE (-(n : ℤ)) ≫ f n) (fun n ↦ by
          simpa using (hladder n).symm) }
  exact ⟨limit.lift 𝓘 c, fun n ↦ limit.lift_π c ⟨n⟩⟩

/-- In degrees `≥ m`, the cohomology of the canonical map `K ⟶ τ_{≥ m} K` followed by a
quasi-isomorphism `τ_{≥ m} K ⟶ J` is an isomorphism. -/
private theorem isIso_homologyFunctor_map_πTruncGE_comp
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A] (K : CochainComplex A ℤ)
    {J : CochainComplex A ℤ} {m : ℤ} (f : K.truncGE m ⟶ J) [QuasiIso f] {r : ℤ} (hr : m ≤ r) :
    IsIso ((DerivedCategory.homologyFunctor A r).map (Q.map (K.πTruncGE m ≫ f))) := by
  have h1 : IsIso (HomologicalComplex.homologyMap f r) :=
    (quasiIsoAt_iff_isIso_homologyMap f r).mp inferInstance
  have h2 : IsIso (HomologicalComplex.homologyMap (K.πTruncGE m) r) :=
    (quasiIsoAt_iff_isIso_homologyMap _ r).mp (K.quasiIsoAt_πTruncGE m r hr)
  rw [show (DerivedCategory.homologyFunctor A r).map (Q.map (K.πTruncGE m ≫ f)) =
      (Q ⋙ DerivedCategory.homologyFunctor A r).map (K.πTruncGE m ≫ f) from rfl,
    NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A r)]
  change IsIso (HomologicalComplex.homologyMap (K.πTruncGE m ≫ f) r)
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

omit [HasProductsOfShape ℕ A] in
/-- **The equivalence of Stacks 070M.** If `L` is a derived limit of `𝓘 ⋙ Q` and
`c : Q K ⟶ L` is compatible with the projections, then `c` is an isomorphism if and only if the
canonical map `γ : K ⟶ lim 𝓘` is a quasi-isomorphism. -/
private lemma isIso_iff_quasiIso (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit 𝓘]
    [HasProduct fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩]
    (δ₀ : (∏ᶜ fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) ⟶ (Q.obj (limit 𝓘))⟦(1 : ℤ)⟧)
    (h₀ : Triangle.mk (limPi 𝓘) (diffMap (𝓘 ⋙ Q)) δ₀ ∈ distTriang (DerivedCategory A))
    (K : CochainComplex A ℤ) (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ 𝓘.obj ⟨n⟩)
    (hf : ∀ n : ℕ, QuasiIso (f n)) (γ : K ⟶ limit 𝓘)
    (hγ : ∀ n : ℕ, γ ≫ limit.π 𝓘 ⟨n⟩ = K.πTruncGE (-(n : ℤ)) ≫ f n)
    (L : DerivedCategory A) (c : Q.obj K ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (diffMap (𝓘 ⋙ Q)) δ ∈ distTriang (DerivedCategory A))
    (hc : ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) n =
      Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n)) :
    IsIso c ↔ QuasiIso γ := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := complete_distinguished_triangle_morphism₁ _ _ hT h₀ (𝟙 _) (𝟙 _) (by simp)
  have hφ : p = φ ≫ limPi 𝓘 := by simpa using hφ₁
  have hφiso : IsIso φ := by
    have := isIso₁_of_isIso₂₃ (Triangle.homMk _ _ φ (𝟙 _) (𝟙 _) hφ₁ (by simp) hφ₂) hT h₀
      (by simp only [Triangle.homMk_hom₂]; infer_instance)
      (by simp only [Triangle.homMk_hom₃]; infer_instance)
    simpa using this
  rw [DerivedCategory.isIso_iff, ← DerivedCategory.isIso_Q_map_iff_quasiIso,
    DerivedCategory.isIso_iff]
  refine forall_congr' fun i ↦ ?_
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(n : ℤ) ≤ i :=
    ⟨i.natAbs, by rw [Int.natCast_natAbs]; exact neg_abs_le i⟩
  have key := isIso_homologyFunctor_map_πTruncGE_comp K (f n) hn
  have aux : ∀ {X : DerivedCategory A} (u : Q.obj K ⟶ X)
      (v : X ⟶ (𝓘 ⋙ Q).obj ⟨n⟩),
      u ≫ v = Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n) →
      (IsIso ((DerivedCategory.homologyFunctor A i).map u) ↔
        IsIso ((DerivedCategory.homologyFunctor A i).map v)) := fun u v h ↦ by
    have : IsIso ((DerivedCategory.homologyFunctor A i).map u ≫
        (DerivedCategory.homologyFunctor A i).map v) := by
      rw [← Functor.map_comp, h]
      exact key
    exact isIso_iff_isIso_of_comp_isIso _ _
  have e1 := aux c (p ≫ Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) n) (hc n)
  have e2 := aux (Q.map γ) (limPi 𝓘 ≫ Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) n)
    (by rw [limPi, Pi.lift_π, ← Q.map_comp, hγ n])
  have e3 : IsIso ((DerivedCategory.homologyFunctor A i).map
        (p ≫ Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) n)) ↔
      IsIso ((DerivedCategory.homologyFunctor A i).map
        (limPi 𝓘 ≫ Pi.π (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) n)) := by
    rw [hφ, assoc, Functor.map_comp]
    exact isIso_comp_left_iff _ _
  exact e1.trans (e3.trans e2.symm)

/-- Let `A` be an abelian category with countable products and let
`𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ` be an inverse system of K-injective complexes whose transition maps
are degreewise split epimorphisms. Then the limit `I = lim 𝓘` exists, it is K-injective, and it
represents the derived limit `R lim 𝓘ₙ`. Moreover, for every cochain complex `K` of `A` equipped
with quasi-isomorphisms `f n : τ_{≥ -n} K ⟶ 𝓘ₙ` making the ladder over the canonical maps
`K.πTruncGE (-n) : K ⟶ τ_{≥ -n} K` commute — the system produced by Stacks 070F, for which
`R lim 𝓘ₙ` is `R lim τ_{≥ -n} K`, as the `f n` become isomorphisms in `D(A)` — the unique map
`γ : K ⟶ I` compatible with the maps `K ⟶ τ_{≥ -n} K ⟶ 𝓘ₙ` is a quasi-isomorphism if and only if
every map `K ⟶ R lim τ_{≥ -n} K` compatible with the projections, as in Stacks 0H72, is an
isomorphism in `D(A)`. -/
@[stacks 070M]
public theorem isKInjective_limit_and_isDerivedLimit_of_isSplitEpi
    (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) (h𝓘 : ∀ n : ℕ, (𝓘.obj ⟨n⟩).IsKInjective)
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((𝓘.map (homOfLE (Nat.le_succ n)).op).f i)) :
    ∃ (_ : HasLimit 𝓘) (_ : HasProduct fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩),
      (limit 𝓘).IsKInjective ∧ IsDerivedLimit (𝓘 ⋙ Q) (Q.obj (limit 𝓘)) ∧
        ∀ (K : CochainComplex A ℤ) (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ 𝓘.obj ⟨n⟩),
          (∀ n : ℕ, QuasiIso (f n)) →
          (∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫
              𝓘.map (homOfLE (Nat.le_succ n)).op = K.πTruncGE (-(n : ℤ)) ≫ f n) →
          ∃ γ : K ⟶ limit 𝓘, (∀ n : ℕ, γ ≫ limit.π 𝓘 ⟨n⟩ = K.πTruncGE (-(n : ℤ)) ≫ f n) ∧
            (QuasiIso γ ↔ ∀ (L : DerivedCategory A) (c : Q.obj K ⟶ L)
              (p : L ⟶ ∏ᶜ fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩)
              (δ : (∏ᶜ fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧),
              Triangle.mk p (Pi.lift fun n : ℕ =>
                  Pi.π (fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) n -
                    Pi.π (fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) (n + 1) ≫
                      (𝓘 ⋙ Q).map (homOfLE (Nat.le_succ n)).op) δ ∈
                distTriang (DerivedCategory A) →
              (∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) n =
                Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n)) → IsIso c) := by
  have hlim : HasLimit 𝓘 := hasLimit_natOp 𝓘
  obtain ⟨hprod, hKinj, δ₀, h₀⟩ := exists_hasProduct_isKInjective_and_distTriang 𝓘 h𝓘 hsplit
  refine ⟨hlim, hprod, hKinj, ⟨limPi 𝓘, δ₀, h₀⟩, ?_⟩
  intro K f hf hladder
  obtain ⟨γ, hγ⟩ := exists_gamma 𝓘 K f hladder
  refine ⟨γ, hγ, ?_, ?_⟩
  · intro hqi L c p δ hT hcompat
    exact (isIso_iff_quasiIso 𝓘 δ₀ h₀ K f hf γ hγ L c p δ hT hcompat).2 hqi
  · intro h
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    refine h (Q.obj (limit 𝓘)) (Q.map γ) (limPi 𝓘) δ₀ h₀ fun n ↦ ?_
    rw [limPi, Pi.lift_π, ← Q.map_comp, hγ n]

end

end KInjectiveTower

/-! ### Existence of K-injective resolutions -/

section KInjectiveResolutions

open DerivedCategory ZeroObject

section Tower

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]

/-- The map `1 - shift : ∏ Vₙ ⟶ ∏ Vₙ` of an inverse system indexed by `ℕ` whose transition maps
`t n` are split epimorphisms is a split epimorphism; equivalently `lim¹` of such a system
vanishes. -/
private theorem isSplitEpi_pi_lift_sub (V : ℕ → A) [HasProduct V]
    (t : ∀ n, V (n + 1) ⟶ V n) (σ : ∀ n, V n ⟶ V (n + 1)) (hσ : ∀ n, σ n ≫ t n = 𝟙 (V n)) :
    IsSplitEpi (Pi.lift fun n => Pi.π V n - Pi.π V (n + 1) ≫ t n) :=
  IsSplitEpi.mk' ⟨Pi.lift (towerW V (Pi.π V) σ), Pi.hom_ext _ _ fun n ↦ by
    rw [Category.assoc, Pi.lift_π, Category.id_comp, Preadditive.comp_sub, Pi.lift_π,
      ← Category.assoc, Pi.lift_π,
      show towerW V (Pi.π V) σ (n + 1) = (towerW V (Pi.π V) σ n - Pi.π V n) ≫ σ n from rfl,
      Category.assoc, hσ n, Category.comp_id, sub_sub_cancel]⟩

/-- A compatible family of maps `u n : W ⟶ V n` into an inverse system indexed by `ℕ` is a cone,
i.e. `Pi.lift u` is annihilated by the map `1 - shift`. -/
private theorem pi_lift_comp_pi_lift_sub (V : ℕ → A) [HasProduct V] (t : ∀ n, V (n + 1) ⟶ V n)
    {W : A} (u : ∀ n, W ⟶ V n) (hu : ∀ n, u (n + 1) ≫ t n = u n) :
    Pi.lift u ≫ (Pi.lift fun n => Pi.π V n - Pi.π V (n + 1) ≫ t n) = 0 := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, Pi.lift_π, Preadditive.comp_sub, Pi.lift_π, ← Category.assoc, Pi.lift_π,
    hu n, sub_self, zero_comp]

/-- An inverse system `V : ℕ → A` indexed by `ℕ` which is zero below some `N` and constant equal to
`W` from `N` on — the maps `u n : W ⟶ V n` of the cone being isomorphisms for `n ≥ N` — has `W` as
its limit: `Pi.lift u` is a kernel of the map `1 - shift`. -/
private noncomputable def isLimitKernelForkPiLift (V : ℕ → A) [HasProduct V]
    (t : ∀ n, V (n + 1) ⟶ V n) {W : A} (u : ∀ n, W ⟶ V n) (hu : ∀ n, u (n + 1) ≫ t n = u n)
    (N : ℕ) (hzero : ∀ n, n < N → IsZero (V n)) (hiso : ∀ n, N ≤ n → IsIso (u n)) :
    IsLimit (KernelFork.ofι (Pi.lift u) (pi_lift_comp_pi_lift_sub V t u hu)) := by
  have hN := hiso N le_rfl
  have hisot : ∀ n, N ≤ n → IsIso (t n) := by
    intro n hn
    have h1 := hiso n hn
    have h2 := hiso (n + 1) (by omega)
    have h3 : t n = inv (u (n + 1)) ≫ u n := by rw [← hu n, IsIso.inv_hom_id_assoc]
    rw [h3]; infer_instance
  refine KernelFork.IsLimit.ofι _ _
    (fun {T} k _ ↦ k ≫ Pi.π V N ≫ inv (u N)) (fun {T} k hk ↦ ?_) (fun {T} k hk m hm ↦ ?_)
  · have hk' : ∀ n : ℕ, k ≫ Pi.π V n = k ≫ Pi.π V (n + 1) ≫ t n := by
      intro n
      have h := congrArg (fun x ↦ x ≫ Pi.π V n) hk
      simp only [Category.assoc, Pi.lift_π, Preadditive.comp_sub, zero_comp] at h
      exact sub_eq_zero.mp h
    have key : ∀ n : ℕ, N ≤ n → k ≫ Pi.π V n = k ≫ Pi.π V N ≫ inv (u N) ≫ u n := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => simp
      | succ n hn ih =>
          have h1 := hisot n hn
          rw [← cancel_mono (t n), Category.assoc, Category.assoc, Category.assoc,
            Category.assoc, hu n, ← hk' n]
          exact ih
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, Pi.lift_π]
    rcases lt_or_ge n N with h | h
    · exact (hzero n h).eq_of_tgt _ _
    · rw [Category.assoc, Category.assoc]; exact (key n h).symm
  · have h : m ≫ u N = k ≫ Pi.π V N := by rw [← hm, Category.assoc, Pi.lift_π]
    rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end Tower

section Kernels

variable {A : Type u₁} [Category.{v₁} A] [HasZeroMorphisms A]

/-- Two kernels of the same morphism are identified by any morphism between them which commutes
with the two inclusions. -/
private theorem isIso_of_isLimit_kernelFork {Y Z W₁ W₂ : A} {g : Y ⟶ Z} {a : W₁ ⟶ Y}
    {b : W₂ ⟶ Y} {ha0 : a ≫ g = 0} {hb0 : b ≫ g = 0} (ha : IsLimit (KernelFork.ofι a ha0))
    (hb : IsLimit (KernelFork.ofι b hb0)) {h : W₁ ⟶ W₂} (hab : h ≫ b = a) : IsIso h := by
  obtain ⟨k, hk⟩ := KernelFork.IsLimit.lift' ha b hb0
  have hk' : k ≫ a = b := hk
  have : Mono a := mono_of_isLimit_fork ha
  have : Mono b := mono_of_isLimit_fork hb
  exact ⟨k, by rw [← cancel_mono a, Category.assoc, hk', hab, Category.id_comp],
    by rw [← cancel_mono b, Category.assoc, hab, hk', Category.id_comp]⟩

/-- Transport of a kernel along an isomorphism conjugating two morphisms: if `e` is an
isomorphism with `e ≫ g' = g ≫ e'` and `a ≫ e` is a kernel of `g'`, then `a` is a kernel of
`g`. -/
private noncomputable def isLimitKernelForkOfConj {Y Y' Z Z' W : A} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (e : Y ⟶ Y') [IsIso e] {e' : Z ⟶ Z'} (he : e ≫ g' = g ≫ e') {a : W ⟶ Y} (h0 : a ≫ g = 0)
    (h : IsLimit (KernelFork.ofι (a ≫ e)
      (show (a ≫ e) ≫ g' = 0 by rw [Category.assoc, he, ← Category.assoc, h0, zero_comp]))) :
    IsLimit (KernelFork.ofι a h0) := by
  have hcomp : ∀ {T : A} (k : T ⟶ Y), k ≫ g = 0 → (k ≫ e) ≫ g' = 0 := fun k hk ↦ by
    rw [Category.assoc, he, ← Category.assoc, hk, zero_comp]
  refine KernelFork.IsLimit.ofι _ _
    (fun {T} k hk ↦ (KernelFork.IsLimit.lift' h (k ≫ e) (hcomp k hk)).1)
    (fun {T} k hk ↦ ?_) (fun {T} k hk m hm ↦ ?_)
  · rw [← cancel_mono e, Category.assoc]
    exact (KernelFork.IsLimit.lift' h (k ≫ e) (hcomp k hk)).2
  · refine Fork.IsLimit.hom_ext h ?_
    change m ≫ (a ≫ e) = _
    rw [← Category.assoc, hm]
    exact ((KernelFork.IsLimit.lift' h (k ≫ e) (hcomp k hk)).2).symm

end Kernels

section Transport

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] {D : Type*} [Category D] [Preadditive D]

omit [Preadditive A] [Preadditive D] in
/-- The comparison morphism `H(∏ Xₙ) ⟶ ∏ H(Xₙ)` carries the image of a `Pi.lift` to the
`Pi.lift` of the images. -/
public theorem map_pi_lift_comp_piComparison (H : D ⥤ A) (X : ℕ → D) [HasProduct X]
    [HasProduct fun n => H.obj (X n)] {Y : D} (w : ∀ n, Y ⟶ X n) :
    H.map (Pi.lift w) ≫ piComparison H X = Pi.lift fun n => H.map (w n) := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, piComparison_comp_π, ← H.map_comp, Pi.lift_π, Pi.lift_π]

/-- The comparison morphism `H(∏ Xₙ) ⟶ ∏ H(Xₙ)` conjugates the map `1 - shift` of an inverse
system into the map `1 - shift` of the inverse system of the images. -/
public theorem map_pi_lift_sub_comp_piComparison (H : D ⥤ A) [H.Additive] (X : ℕ → D)
    [HasProduct X] [HasProduct fun n => H.obj (X n)] (τ : ∀ n, X (n + 1) ⟶ X n) :
    H.map (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ τ n) ≫ piComparison H X =
      piComparison H X ≫ Pi.lift fun n => Pi.π (fun n => H.obj (X n)) n -
        Pi.π (fun n => H.obj (X n)) (n + 1) ≫ H.map (τ n) := by
  rw [map_pi_lift_comp_piComparison]
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Pi.lift_π, Category.assoc, Pi.lift_π, Preadditive.comp_sub, piComparison_comp_π,
    H.map_sub, H.map_comp, ← Category.assoc, piComparison_comp_π]

variable (H : D ⥤ A) [H.Additive] (X : ℕ → D) [HasProduct X] [HasProduct fun n => H.obj (X n)]
  [PreservesLimit (Discrete.functor X) H] (τ : ∀ n, X (n + 1) ⟶ X n) {Y : D} (v : ∀ n, Y ⟶ X n)

/-- The image under a product-preserving additive functor `H` of the map `1 - shift` of an inverse
system `X` indexed by `ℕ` is an epimorphism, as soon as `H(Xₙ)` vanishes below some `N` and the
maps `H(vₙ)` of a cone on `X` are isomorphisms from `N` on. -/
private theorem epi_map_pi_lift_sub (hv : ∀ n, v (n + 1) ≫ τ n = v n)
    (N : ℕ) (hzero : ∀ n, n < N → IsZero (H.obj (X n)))
    (hiso : ∀ n, N ≤ n → IsIso (H.map (v n))) :
    Epi (H.map (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ τ n)) := by
  have := isSplitEpi_pi_lift_sub (fun n => H.obj (X n)) (fun n => H.map (τ n))
    (fun n => if h : N ≤ n then (have := hiso n h; inv (H.map (v n)) ≫ H.map (v (n + 1)))
      else 0) fun n => by
      split
      · rename_i h
        have := hiso n h
        rw [Category.assoc, ← H.map_comp, hv n, IsIso.inv_hom_id]
      · exact (hzero n (by omega)).eq_of_src _ _
  rw [show H.map (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ τ n) =
      piComparison H X ≫ (Pi.lift fun n ↦ Pi.π (fun n ↦ H.obj (X n)) n -
        Pi.π (fun n ↦ H.obj (X n)) (n + 1) ≫ H.map (τ n)) ≫ inv (piComparison H X) by
    rw [← Category.assoc, ← map_pi_lift_sub_comp_piComparison, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- The image under a product-preserving additive functor `H` of the cone map `Pi.lift v` is a
kernel of the image of the map `1 - shift`, as soon as `H(Xₙ)` vanishes below some `N` and the
maps `H(vₙ)` are isomorphisms from `N` on. -/
private noncomputable def isLimitKernelForkMapPiLift (hv : ∀ n, v (n + 1) ≫ τ n = v n)
    (N : ℕ) (hzero : ∀ n, n < N → IsZero (H.obj (X n)))
    (hiso : ∀ n, N ≤ n → IsIso (H.map (v n))) :
    IsLimit (KernelFork.ofι (H.map (Pi.lift v))
      (show H.map (Pi.lift v) ≫ H.map (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ τ n) = 0 by
        rw [← H.map_comp, pi_lift_comp_pi_lift_sub X τ v hv, H.map_zero])) := by
  refine isLimitKernelForkOfConj (piComparison H X)
    (map_pi_lift_sub_comp_piComparison H X τ).symm _ ?_
  refine IsLimit.ofIsoLimit (isLimitKernelForkPiLift (fun n ↦ H.obj (X n))
    (fun n ↦ H.map (τ n)) (fun n ↦ H.map (v n)) (fun n ↦ by rw [← H.map_comp, hv n]) N hzero
    hiso) (Fork.ext (Iso.refl _) ?_)
  rw [Iso.refl_hom, Category.id_comp, Fork.ι_ofι, Fork.ι_ofι,
    map_pi_lift_comp_piComparison H X v]

end Transport

section DerivedLimit

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasProductsOfShape ℕ A]
  [HasExactLimitsOfShape (Discrete ℕ) A] [HasDerivedCategory.{w₁} A]

/-- **Stacks 07KC (3).** In an abelian category with exact countable products, the cohomology
functors of the derived category preserve countable products. -/
private theorem preservesLimitsOfShape_discrete_homologyFunctor (r : ℤ) :
    PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor A r) :=
  have := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory (A := A) (I := ℕ)
  Stacks.DerivedProducts.preservesLimitsOfShape_discrete_of_isIso_piComparison _
    fun Y ↦ Stacks.DerivedProducts.isIso_piComparison_homologyFunctor Y r

/-- **The content of Stacks 090Y that is not the reduction of Stacks 070M.** Let `Xₙ` be an
inverse system of `D(A)` with transition maps `τ n`, let `L` be a derived limit of it, presented
by the distinguished triangle `L ⟶ ∏ Xₙ ⟶ ∏ Xₙ ⟶ L[1]` whose middle map is `1 - shift`, and let
`c : Y ⟶ L` be compatible with a cone `v n : Y ⟶ Xₙ`. If in every cohomological degree `r` the
tower is eventually the constant `Hʳ(Y)` — `Hʳ(Xₙ) = 0` for `n < N r` and `Hʳ(v n)` an
isomorphism for `n ≥ N r` — then `c` is an isomorphism, i.e. `L = Y`. -/
theorem isIso_of_isDerivedLimit_of_eventually_isIso_homologyMap
    (X : ℕ → DerivedCategory A) [HasProduct X] (τ : ∀ n, X (n + 1) ⟶ X n)
    {Y : DerivedCategory A} (v : ∀ n, Y ⟶ X n) (hv : ∀ n, v (n + 1) ≫ τ n = v n)
    {L : DerivedCategory A} (c : Y ⟶ L) (p : L ⟶ ∏ᶜ X) (δ : (∏ᶜ X) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ τ n) δ ∈
      distTriang (DerivedCategory A))
    (hcp : c ≫ p = Pi.lift v) (N : ℤ → ℕ)
    (hzero : ∀ (r : ℤ) (n : ℕ), n < N r →
      IsZero ((DerivedCategory.homologyFunctor A r).obj (X n)))
    (hiso : ∀ (r : ℤ) (n : ℕ), N r ≤ n →
      IsIso ((DerivedCategory.homologyFunctor A r).map (v n))) :
    IsIso c := by
  have hpres := preservesLimitsOfShape_discrete_homologyFunctor (A := A)
  have hepi : ∀ r : ℤ, Epi ((DerivedCategory.homologyFunctor A r).map
      (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ τ n)) := fun r ↦
    have := hpres r
    epi_map_pi_lift_sub _ _ _ _ hv (N r) (hzero r) (hiso r)
  rw [DerivedCategory.isIso_iff]
  intro q
  have := hpres q
  have hmono := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (q - 1) q).mpr
      ((DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT (q - 1) q).mp
        (hepi (q - 1)))
  exact isIso_of_isLimit_kernelFork
    (isLimitKernelForkMapPiLift _ _ _ _ hv (N q) (hzero q) (hiso q))
    (DerivedCategory.HomologySequence.exact₂ _ hT q).fIsKernel
    (by rw [← Functor.map_comp]; exact congrArg _ hcp)

end DerivedLimit

section Truncation

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]

/-- The cohomology of a complex quasi-isomorphic to the truncation `τ_{≥ m} K` vanishes below
`m`. -/
private theorem isZero_homologyFunctor_obj_of_quasiIso {K J : CochainComplex A ℤ} {m : ℤ}
    (f : K.truncGE m ⟶ J) [QuasiIso f] {r : ℤ} (hr : r < m) :
    IsZero ((DerivedCategory.homologyFunctor A r).obj (Q.obj J)) :=
  have : IsIso (HomologicalComplex.homologyMap f r) :=
    (quasiIsoAt_iff_isIso_homologyMap f r).mp inferInstance
  ((CochainComplex.isZero_of_isGE (K.truncGE m) m r hr).of_iso
    (asIso (HomologicalComplex.homologyMap f r)).symm).of_iso
      ((DerivedCategory.homologyFunctorFactors A r).app J)

end Truncation

section Key

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasProductsOfShape ℕ A]
  [HasExactLimitsOfShape (Discrete ℕ) A] [HasDerivedCategory.{w₁} A]

/-- Stacks 090Y for the system of Stacks 070F: if the complexes `𝓘ₙ` of an inverse system resolve
the truncations `τ_{≥ -n} K` of a complex `K`, compatibly with the canonical maps
`K ⟶ τ_{≥ -n} K`, then any map `c : K ⟶ L` in `D(A)` into a derived limit `L` of the system which
is compatible with the projections of the defining triangle is an isomorphism. -/
theorem isIso_of_isDerivedLimit_of_quasiIso_truncGE
    (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasProduct fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩]
    (K : CochainComplex A ℤ) (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ 𝓘.obj ⟨n⟩)
    (hf : ∀ n : ℕ, QuasiIso (f n))
    (hladder : ∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫
        𝓘.map (homOfLE (Nat.le_succ n)).op = K.πTruncGE (-(n : ℤ)) ≫ f n)
    (L : DerivedCategory A) (c : Q.obj K ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) (n + 1) ≫
            (𝓘 ⋙ Q).map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang (DerivedCategory A))
    (hc : ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ => (𝓘 ⋙ Q).obj ⟨n⟩) n =
        Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n)) :
    IsIso c := by
  have hv : ∀ n : ℕ, Q.map (K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1)) ≫
      (𝓘 ⋙ Q).map (homOfLE (Nat.le_succ n)).op =
        Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n) := fun n ↦ by
    rw [Functor.comp_map, ← Functor.map_comp, Category.assoc, hladder n]
  refine isIso_of_isDerivedLimit_of_eventually_isIso_homologyMap
    (fun n : ℕ ↦ (𝓘 ⋙ Q).obj ⟨n⟩) (fun n ↦ (𝓘 ⋙ Q).map (homOfLE (Nat.le_succ n)).op)
    (fun n : ℕ ↦ Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n)) hv c p δ hT
    (Pi.hom_ext _ _ fun n ↦ by rw [Category.assoc, Pi.lift_π]; exact hc n)
    (fun r ↦ (-r).toNat) (fun r n hn ↦ ?_) (fun r n hn ↦ ?_)
  · have := hf n
    exact isZero_homologyFunctor_obj_of_quasiIso (f n) (by omega)
  · have := hf n
    exact isIso_homologyFunctor_map_πTruncGE_comp K (f n) (by omega)

end Key

/-- Let `𝒜` be an abelian category having enough injectives and exact countable
products. Then every cochain complex `K` of objects of `𝒜` admits a quasi-isomorphism `f : K ⟶ I`
to a K-injective complex `I`. -/
@[stacks 090Y]
public theorem exists_quasiIso_isKInjective {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    [EnoughInjectives 𝒜] [HasProductsOfShape ℕ 𝒜] [HasExactLimitsOfShape (Discrete ℕ) 𝒜]
    (K : CochainComplex 𝒜 ℤ) :
    ∃ (I : CochainComplex 𝒜 ℤ) (f : K ⟶ I) (_ : QuasiIso f), I.IsKInjective := by
  let _ : HasDerivedCategory.{max u v} 𝒜 := HasDerivedCategory.standard 𝒜
  have : ObjectProperty.ContainsZero (C := 𝒜) (fun X ↦ Injective X) :=
    ⟨⟨0, isZero_zero _, inferInstance⟩⟩
  obtain ⟨I, f, g, hf, -, hGE, hinj, hsplit, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncGE (fun X : 𝒜 ↦ Injective X)
      (fun X Y hX hY ↦ by have := hX; have := hY; infer_instance)
      (fun X ↦ ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩) K
  have hmapg : ∀ n : ℕ, (Functor.ofOpSequence g).map (homOfLE (Nat.le_succ n)).op = g n :=
    Functor.ofOpSequence_map_homOfLE_succ g
  have hg : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((g n).f i) := fun n i ↦ by
    obtain ⟨C, -, e, he⟩ := hsplit n i
    exact IsSplitEpi.mk' ⟨biprod.inl ≫ e.inv, by rw [Category.assoc, he]; simp⟩
  have hladder' : ∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫
      (Functor.ofOpSequence g).map (homOfLE (Nat.le_succ n)).op =
        K.πTruncGE (-(n : ℤ)) ≫ f n := fun n ↦ by rw [hmapg n]; exact hladder n
  have h𝓘 : ∀ n : ℕ, ((Functor.ofOpSequence g).obj ⟨n⟩).IsKInjective := fun n ↦ by
    have := hGE n
    have : ∀ i : ℤ, Injective ((I n).X i) := hinj n
    exact CochainComplex.isKInjective_of_injective (I n) (-(n : ℤ))
  obtain ⟨hlim, hprod, hKinj, hDL, hmain⟩ :=
    CochainComplex.isKInjective_limit_and_isDerivedLimit_of_isSplitEpi
      (Functor.ofOpSequence g) h𝓘 (fun n i ↦ by rw [hmapg n]; exact hg n i)
  obtain ⟨γ, hγ, hiff⟩ := hmain K f hf hladder'
  exact ⟨_, γ, hiff.mpr fun L c p δ hT hc ↦
    isIso_of_isDerivedLimit_of_quasiIso_truncGE (Functor.ofOpSequence g) K f hf hladder'
      L c p δ hT hc, hKinj⟩

end KInjectiveResolutions

end CochainComplex

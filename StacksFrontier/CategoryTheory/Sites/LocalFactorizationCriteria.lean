module

public import StacksFrontier.CategoryTheory.Sites.SectionsAlongAFunctorConnected

/-!
# Local factorization from a single covering morphism

For a functor `u : D ⥤ C` to a site `(C, J)`, the local-factorization conditions
`Stacks.Sites.HasLocalFactorizations`, `Stacks.Sites.HasConnectedLocalFactorizations` and
`Stacks.Sites.HasLocallyConnectedFactorizations` hold as soon as the required factorizations exist
along a single morphism whose generated sieve is covering. The results are specialized to the
inclusion of a full subcategory.

## Main results

* `Stacks.Sites.hasLocalFactorizations_of_exists_singleton_covering_factoring`: one covering
  morphism whose source maps to the image of `u` gives local factorization.
* `Stacks.Sites.hasLocalFactorizations_of_exists_singleton_covering`: the case in which that
  source is itself in the image of `u`.
* `Stacks.Sites.hasConnectedLocalFactorizations_of_exists_singleton_covering`: a single covering
  morphism along which two morphisms to the image of `u` become dominated gives local domination.
* `Stacks.Sites.hasLocallyConnectedFactorizations_of_exists_singleton_covering`: under the same
  hypothesis, `u` has locally connected factorizations.
* `Stacks.Sites.hasLocalFactorizations_ι_of_exists_singleton_covering_factoring`,
  `Stacks.Sites.hasLocalFactorizations_ι_of_exists_singleton_covering` and
  `Stacks.Sites.hasLocallyConnectedFactorizations_ι_of_exists_singleton_covering`: the same
  statements for the inclusion `P.ι` of a full subcategory.

## References

* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Sites

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C}

section Functor

variable {u : D ⥤ C}

/-- If every object of the site `(𝒞, J)` receives one covering morphism whose source admits a
morphism to the image of `u`, then `u` has local factorizations. -/
public theorem hasLocalFactorizations_of_exists_singleton_covering_factoring
    (h : ∀ x : C, ∃ (Y : C) (a : Y ⟶ x), Sieve.generate (Presieve.singleton a) ∈ J x ∧
      ∃ d : D, Nonempty (Y ⟶ u.obj d)) :
    HasLocalFactorizations J u := by
  refine hasLocalFactorizations_of_covering fun x => ?_
  obtain ⟨Y, a, ha, d, ⟨φ⟩⟩ := h x
  refine ⟨_, ha, ?_⟩
  rintro Z f ⟨W, g, k, hk, rfl⟩
  cases hk
  exact ⟨d, ⟨g ≫ φ⟩⟩

/-- If every object of the site `(𝒞, J)` receives a morphism from the image of `u` whose generated
sieve is covering, then `u` has local factorizations. -/
public theorem hasLocalFactorizations_of_exists_singleton_covering
    (h : ∀ x : C, ∃ (d : D) (a : u.obj d ⟶ x), Sieve.generate (Presieve.singleton a) ∈ J x) :
    HasLocalFactorizations J u :=
  hasLocalFactorizations_of_exists_singleton_covering_factoring fun x => by
    obtain ⟨d, a, ha⟩ := h x
    exact ⟨_, a, ha, d, ⟨𝟙 _⟩⟩

/-- If any two morphisms from an object of the site `(𝒞, J)` to the image of `u` become dominated
by a single morphism to the image of `u` after pulling back along one covering morphism, then `u`
has connected local factorizations. -/
public theorem hasConnectedLocalFactorizations_of_exists_singleton_covering
    (h : ∀ (x : C) (d₁ d₂ : D) (φ₁ : x ⟶ u.obj d₁) (φ₂ : x ⟶ u.obj d₂),
      ∃ (Y : C) (k : Y ⟶ x), Sieve.generate (Presieve.singleton k) ∈ J x ∧
        ∃ (d : D) (ψ : Y ⟶ u.obj d) (α : d ⟶ d₁) (β : d ⟶ d₂),
          ψ ≫ u.map α = k ≫ φ₁ ∧ ψ ≫ u.map β = k ≫ φ₂) :
    HasConnectedLocalFactorizations J u := by
  intro x d₁ d₂ φ₁ φ₂
  obtain ⟨Y, k, hk, d, ψ, α, β, e₁, e₂⟩ := h x d₁ d₂ φ₁ φ₂
  refine J.superset_covering ?_ hk
  rw [Sieve.generate_le_iff]
  rintro Z f hf
  cases hf
  exact ⟨d, ψ, α, β, e₁, e₂⟩

/-- If any two morphisms from an object of the site `(𝒞, J)` to the image of `u` become dominated
by a single morphism to the image of `u` after pulling back along one covering morphism, then `u`
has locally connected factorizations. -/
public theorem hasLocallyConnectedFactorizations_of_exists_singleton_covering
    (h : ∀ (x : C) (d₁ d₂ : D) (φ₁ : x ⟶ u.obj d₁) (φ₂ : x ⟶ u.obj d₂),
      ∃ (Y : C) (k : Y ⟶ x), Sieve.generate (Presieve.singleton k) ∈ J x ∧
        ∃ (d : D) (ψ : Y ⟶ u.obj d) (α : d ⟶ d₁) (β : d ⟶ d₂),
          ψ ≫ u.map α = k ≫ φ₁ ∧ ψ ≫ u.map β = k ≫ φ₂) :
    HasLocallyConnectedFactorizations J u :=
  hasLocallyConnectedFactorizations_of_hasConnectedLocalFactorizations
    (hasConnectedLocalFactorizations_of_exists_singleton_covering h)

end Functor

section FullSubcategory

variable {P : ObjectProperty C}

/-- If every object of the site `(𝒞, J)` receives one covering morphism whose source admits a
morphism to an object with the property `P`, then the inclusion of `P` has local
factorizations. -/
public theorem hasLocalFactorizations_ι_of_exists_singleton_covering_factoring
    (h : ∀ x : C, ∃ (Y : C) (a : Y ⟶ x), Sieve.generate (Presieve.singleton a) ∈ J x ∧
      ∃ (d : C) (_ : P d), Nonempty (Y ⟶ d)) :
    HasLocalFactorizations J P.ι :=
  hasLocalFactorizations_of_exists_singleton_covering_factoring fun x => by
    obtain ⟨Y, a, ha, d, hd, hφ⟩ := h x
    exact ⟨Y, a, ha, ⟨d, hd⟩, hφ⟩

/-- If every object of the site `(𝒞, J)` receives a morphism from an object with the property `P`
whose generated sieve is covering, then the inclusion of `P` has local factorizations. -/
public theorem hasLocalFactorizations_ι_of_exists_singleton_covering
    (h : ∀ x : C, ∃ (d : C) (_ : P d) (a : d ⟶ x),
      Sieve.generate (Presieve.singleton a) ∈ J x) :
    HasLocalFactorizations J P.ι :=
  hasLocalFactorizations_of_exists_singleton_covering fun x => by
    obtain ⟨d, hd, a, ha⟩ := h x
    exact ⟨⟨d, hd⟩, a, ha⟩

/-- If any two morphisms from an object of the site `(𝒞, J)` to objects with the property `P`
become dominated by a single morphism to an object with the property `P` after pulling back along
one covering morphism, then the inclusion of `P` has locally connected factorizations. -/
public theorem hasLocallyConnectedFactorizations_ι_of_exists_singleton_covering
    (h : ∀ (x d₁ d₂ : C), P d₁ → P d₂ → ∀ (φ₁ : x ⟶ d₁) (φ₂ : x ⟶ d₂),
      ∃ (Y : C) (k : Y ⟶ x), Sieve.generate (Presieve.singleton k) ∈ J x ∧
        ∃ (d : C) (_ : P d) (ψ : Y ⟶ d) (α : d ⟶ d₁) (β : d ⟶ d₂),
          ψ ≫ α = k ≫ φ₁ ∧ ψ ≫ β = k ≫ φ₂) :
    HasLocallyConnectedFactorizations J P.ι :=
  hasLocallyConnectedFactorizations_of_exists_singleton_covering fun x d₁ d₂ φ₁ φ₂ => by
    obtain ⟨Y, k, hk, d, hd, ψ, α, β, e₁, e₂⟩ :=
      h x d₁.obj d₂.obj d₁.property d₂.property φ₁ φ₂
    exact ⟨Y, k, hk, ⟨d, hd⟩, ψ, ObjectProperty.homMk α, ObjectProperty.homMk β, e₁, e₂⟩

end FullSubcategory

end Stacks.Sites

end

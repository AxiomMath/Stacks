module

public import Mathlib.CategoryTheory.IsConnected
public import StacksFrontier.CategoryTheory.Sites.SectionsAlongAFunctor

/-!
# Global sections along a functor of sites, from locally connected factorizations

Let `(𝒞, J)` be a site, let `u : 𝒟 ⥤ 𝒞` be any functor and let `F` be a sheaf of sets on `𝒞`.
Restriction of global sections of `F` along `u` is bijective as soon as every object of `𝒞` is
covered by objects admitting a morphism to the image of `u`, and any two morphisms
`x ⟶ u(d₁)`, `x ⟶ u(d₂)` are, locally on `x`, joined by a zigzag in the category `I^u_x` of
pairs `(d, x ⟶ u(d))`. Local domination by a single morphism to the image of `u` is a special
case of this condition.

## Main definitions

* `Stacks.Sites.connectedFactorizationSieve`: the sieve on `x` of morphisms along which two
  given morphisms to the image of `u` become connected in `I^u_x`.
* `Stacks.Sites.HasLocallyConnectedFactorizations`: local connectedness of the factorizations.

## Main results

* `Stacks.Sites.hasLocallyConnectedFactorizations_of_hasConnectedLocalFactorizations`: local
  domination implies local connectedness.
* `Stacks.Sites.hasLocalFactorizations_of_covering`: a covering sieve all of whose arrows have
  a source admitting a morphism to the image of `u` makes the factorization sieve covering.
* `Stacks.Sites.bijective_sectionsPrecomp_of_hasLocallyConnectedFactorizations`: with local
  factorization and local connectedness, restriction of global sections along `u` is bijective.
* `Stacks.Sites.sectionsEquivOfHasLocallyConnectedFactorizations`: the same, as an `Equiv`.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.Sites

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The sieve on `x` consisting of the morphisms `h` along which the two given morphisms `φ₁`
and `φ₂` to the image of `u` become connected by a zigzag in the category of pairs
`(d, source of h ⟶ u(d))`. -/
public def connectedFactorizationSieve (u : D ⥤ C) {x : C} {d₁ d₂ : D} (φ₁ : x ⟶ u.obj d₁)
    (φ₂ : x ⟶ u.obj d₂) : Sieve x where
  arrows Y h := Zigzag (StructuredArrow.mk (h ≫ φ₁) : StructuredArrow Y u)
    (StructuredArrow.mk (h ≫ φ₂))
  downward_closed := by
    intro Y Z f hf g
    simpa [Category.assoc] using zigzag_obj_of_zigzag (StructuredArrow.map (T := u) g) hf

/-- **Local connectedness of the factorizations**: for any two morphisms from an object of the
site `(𝒞, J)` to the image of `u`, the sieve of morphisms along which they become connected is
a covering sieve. -/
public def HasLocallyConnectedFactorizations (J : GrothendieckTopology C) (u : D ⥤ C) : Prop :=
  ∀ (x : C) (d₁ d₂ : D) (φ₁ : x ⟶ u.obj d₁) (φ₂ : x ⟶ u.obj d₂),
    connectedFactorizationSieve u φ₁ φ₂ ∈ J x

/-- If any two morphisms to the image of `u` are locally dominated by a single one, then they are
locally connected by a zigzag. -/
public theorem hasLocallyConnectedFactorizations_of_hasConnectedLocalFactorizations
    {J : GrothendieckTopology C} {u : D ⥤ C} (h : HasConnectedLocalFactorizations J u) :
    HasLocallyConnectedFactorizations J u := by
  intro x d₁ d₂ φ₁ φ₂
  refine J.superset_covering ?_ (h x d₁ d₂ φ₁ φ₂)
  rintro Y k ⟨d, ψ, α, β, e₁, e₂⟩
  exact Zigzag.of_inv_hom
    (StructuredArrow.homMk (f := StructuredArrow.mk ψ)
      (f' := StructuredArrow.mk (k ≫ φ₁)) α e₁)
    (StructuredArrow.homMk (f := StructuredArrow.mk ψ)
      (f' := StructuredArrow.mk (k ≫ φ₂)) β e₂)

/-- A covering sieve of `x` all of whose arrows have a source admitting a morphism to the image
of `u` makes the factorization sieve of `x` a covering sieve. -/
public theorem hasLocalFactorizations_of_covering {J : GrothendieckTopology C} {u : D ⥤ C}
    (h : ∀ x : C, ∃ R ∈ J x, ∀ ⦃Y : C⦄ ⦃f : Y ⟶ x⦄, (R : Sieve x).arrows f →
      ∃ d : D, Nonempty (Y ⟶ u.obj d)) :
    HasLocalFactorizations J u := by
  intro x
  obtain ⟨R, hR, hle⟩ := h x
  exact J.superset_covering (fun _ _ hf => hle hf) hR

section

variable {u : D ⥤ C} {F : Cᵒᵖ ⥤ Type w} (J : GrothendieckTopology C)

/-- Transport is constant along a morphism of the category of morphisms to the image of `u`. -/
private lemma transport_eq_of_hom (s : (u.op ⋙ F).sections) {y : C}
    {A B : StructuredArrow y u} (α : A ⟶ B) :
    transport s A.hom = transport s B.hom := by
  rw [← StructuredArrow.w α, transport_comp_map]

/-- Transport is constant on each connected component of the category of morphisms to the image
of `u`. -/
private lemma transport_eq_of_zigzag (s : (u.op ⋙ F).sections) {y : C}
    {A B : StructuredArrow y u} (h : Zigzag A B) :
    transport s A.hom = transport s B.hom := by
  induction h with
  | refl => rfl
  | tail _ hz ih =>
      refine ih.trans ?_
      obtain ⟨⟨α⟩⟩ | ⟨⟨α⟩⟩ := hz
      exacts [transport_eq_of_hom s α, (transport_eq_of_hom s α).symm]

/-- Under local connectedness the transported section does not depend on the chosen morphism to
the image of `u`. -/
public lemma transportIndep_of_hasLocallyConnectedFactorizations (hF : Presieve.IsSheaf J F)
    (hconn : HasLocallyConnectedFactorizations J u) : TransportIndep u F := by
  intro s y d₁ d₂ φ₁ φ₂
  refine (hF _ (hconn y d₁ d₂ φ₁ φ₂)).isSeparatedFor.ext ?_
  intro Z h hh
  rw [transport_map, transport_map]
  exact transport_eq_of_zigzag s hh

/-- Let `(𝒞, J)` be a site, `u : 𝒟 ⥤ 𝒞` a functor and `F` a sheaf of sets on `𝒞`. If every
object of `𝒞` is covered by objects admitting a morphism to the image of `u`, and if any two
morphisms to the image of `u` are locally connected by a zigzag, then restriction along `u` is a
bijection `Γ(𝒞, F) ≅ Γ(𝒟, u^{-1}F)`. -/
public theorem bijective_sectionsPrecomp_of_hasLocallyConnectedFactorizations
    (hF : Presieve.IsSheaf J F) (hfac : HasLocalFactorizations J u)
    (hconn : HasLocallyConnectedFactorizations J u) :
    Function.Bijective (Functor.sectionsPrecomp u.op (P := F)) :=
  have hindep := transportIndep_of_hasLocallyConnectedFactorizations J hF hconn
  ⟨injective_sectionsPrecomp_of_hasLocalFactorizations J hF hfac,
    fun s => ⟨glueSections J hF hfac hindep s, glueSections_restrict J hF hfac hindep s⟩⟩

/-- The comparison of global sections of
`Stacks.Sites.bijective_sectionsPrecomp_of_hasLocallyConnectedFactorizations`, as an
equivalence. -/
public noncomputable def sectionsEquivOfHasLocallyConnectedFactorizations
    (hF : Presieve.IsSheaf J F) (hfac : HasLocalFactorizations J u)
    (hconn : HasLocallyConnectedFactorizations J u) :
    F.sections ≃ (u.op ⋙ F).sections :=
  Equiv.ofBijective _
    (bijective_sectionsPrecomp_of_hasLocallyConnectedFactorizations J hF hfac hconn)

end

end Stacks.Sites

end

module

public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import StacksCore.Tactic.StacksAttribute

/-!
# Global sections along a functor of sites

Let `(𝒞, J)` be a site, let `u : 𝒟 ⥤ 𝒞` be any functor, and let `F` be a sheaf of sets on `𝒞`.
Restriction along `u` carries a compatible family of sections of `F` over `𝒞` to one of `u^{-1}F`
over `𝒟`. This restriction is a bijection `Γ(𝒞, F) = Γ(𝒟, u^{-1}F)` as soon as every object of
`𝒞` is covered by objects admitting a morphism to the image of `u`, and any two morphisms
`φ₁ : x ⟶ u(d₁)` and `φ₂ : x ⟶ u(d₂)` are, locally on `x`, dominated by a single morphism to
the image of `u`.

## Main definitions

* `Stacks.Sites.factorizationSieve`: the sieve on `x` of morphisms whose source admits a
  morphism to the image of `u`.
* `Stacks.Sites.connectingSieve`: the sieve on `x` of morphisms along which two given morphisms
  to the image of `u` are dominated by a single one.
* `Stacks.Sites.HasLocalFactorizations`: every factorization sieve is covering.
* `Stacks.Sites.HasConnectedLocalFactorizations`: every connecting sieve is covering.
* `Stacks.Sites.TransportIndep`: the transport of a compatible family of sections along a
  morphism to the image of `u` does not depend on the morphism.

## Main results

* `Stacks.Sites.injective_sectionsPrecomp_of_hasLocalFactorizations`: local factorization alone
  makes restriction of global sections along `u` injective.
* `Stacks.Sites.bijective_sectionsPrecomp_of_hasLocalFactorizations`: with local connectedness
  as well, it is bijective.
* `Stacks.Sites.sectionsEquivOfHasLocalFactorizations`: the same, as an `Equiv`.

## References

* [Stacks Project, Tag 06UN](https://stacks.math.columbia.edu/tag/06UN)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.Sites

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The sieve on `x` consisting of the morphisms whose source admits a morphism to the image
of `u`. -/
public def factorizationSieve (u : D ⥤ C) (x : C) : Sieve x where
  arrows Y _ := ∃ d : D, Nonempty (Y ⟶ u.obj d)
  downward_closed := by
    rintro Y Z f ⟨d, ⟨φ⟩⟩ g
    exact ⟨d, ⟨g ≫ φ⟩⟩

/-- The sieve on `x` consisting of the morphisms `h` along which the two given morphisms `φ₁`
and `φ₂` to the image of `u` are both dominated by a single morphism to the image of `u`. -/
public def connectingSieve (u : D ⥤ C) {x : C} {d₁ d₂ : D} (φ₁ : x ⟶ u.obj d₁)
    (φ₂ : x ⟶ u.obj d₂) : Sieve x where
  arrows Y h := ∃ (d : D) (ψ : Y ⟶ u.obj d) (α : d ⟶ d₁) (β : d ⟶ d₂),
    ψ ≫ u.map α = h ≫ φ₁ ∧ ψ ≫ u.map β = h ≫ φ₂
  downward_closed := by
    rintro Y Z f ⟨d, ψ, α, β, e₁, e₂⟩ g
    exact ⟨d, g ≫ ψ, α, β, by simp [e₁], by simp [e₂]⟩

/-- **Local factorization**: every object of the site `(𝒞, J)` is covered by objects admitting a
morphism to the image of `u`. -/
public def HasLocalFactorizations (J : GrothendieckTopology C) (u : D ⥤ C) : Prop :=
  ∀ x : C, factorizationSieve u x ∈ J x

/-- **Local connectedness**: any two morphisms from an object of the site `(𝒞, J)` to the image
of `u` are, locally on that object, dominated by a single morphism to the image of `u`. -/
public def HasConnectedLocalFactorizations (J : GrothendieckTopology C) (u : D ⥤ C) : Prop :=
  ∀ (x : C) (d₁ d₂ : D) (φ₁ : x ⟶ u.obj d₁) (φ₂ : x ⟶ u.obj d₂),
    connectingSieve u φ₁ φ₂ ∈ J x

section

variable {u : D ⥤ C} {F : Cᵒᵖ ⥤ Type w} (J : GrothendieckTopology C)

/-- Restricting a section twice is restricting it along the composite. -/
public lemma map_map {x y z : C} (g : y ⟶ x) (h : z ⟶ y) (a : F.obj (op x)) :
    F.map h.op (F.map g.op a) = F.map (h ≫ g).op a := by
  rw [op_comp, F.map_comp, types_comp_apply]

/-- The section of `F` over `y` obtained from a compatible family of sections of the restriction
of `F` along `u` by transport along a morphism `φ : y ⟶ u(d)`. -/
public def transport (s : (u.op ⋙ F).sections) {y : C} {d : D} (φ : y ⟶ u.obj d) :
    F.obj (op y) :=
  F.map φ.op (s.val (op d))

/-- Transport is unchanged by composing the morphism with one coming from `𝒟`. -/
public lemma transport_comp_map (s : (u.op ⋙ F).sections) {y : C} {d d' : D}
    (φ : y ⟶ u.obj d) (α : d ⟶ d') :
    transport s (φ ≫ u.map α) = transport s φ := by
  have h : F.map (u.map α).op (s.val (op d')) = s.val (op d) := s.property α.op
  simp only [transport, ← map_map, h]

/-- Transport is compatible with restriction along a morphism of `𝒞`. -/
public lemma transport_map (s : (u.op ⋙ F).sections) {z y : C} {d : D}
    (g : z ⟶ y) (φ : y ⟶ u.obj d) :
    F.map g.op (transport s φ) = transport s (g ≫ φ) := by
  simp only [transport, map_map]

/-- The family of elements of `F` on the factorization sieve of `x` obtained by transporting `s`
along a choice of morphism to the image of `u`. -/
public noncomputable def family (s : (u.op ⋙ F).sections) (x : C) :
    Presieve.FamilyOfElements F (factorizationSieve u x : Presieve x) :=
  fun _ _ hh => transport s hh.choose_spec.some

/-- Independence of the transported section from the chosen morphism to the image of `u`: for
every compatible family `s`, the transports of `s` along any two morphisms from an object `y` to
the image of `u` agree. -/
public def TransportIndep (u : D ⥤ C) (F : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ (s : (u.op ⋙ F).sections) {y : C} {d₁ d₂ : D} (φ₁ : y ⟶ u.obj d₁) (φ₂ : y ⟶ u.obj d₂),
    transport s φ₁ = transport s φ₂

/-- Under local domination of the factorizations the transported section does not depend on the
chosen morphism to the image of `u`. -/
public lemma transportIndep_of_hasConnectedLocalFactorizations (hF : Presieve.IsSheaf J F)
    (hconn : HasConnectedLocalFactorizations J u) : TransportIndep u F := by
  intro s y d₁ d₂ φ₁ φ₂
  refine (hF _ (hconn y d₁ d₂ φ₁ φ₂)).isSeparatedFor.ext ?_
  rintro Z h ⟨d, ψ, α, β, e₁, e₂⟩
  rw [transport_map, transport_map, ← e₁, ← e₂, transport_comp_map, transport_comp_map]

/-- The transported family is compatible. -/
public lemma family_compatible (hindep : TransportIndep u F) (s : (u.op ⋙ F).sections) (x : C) :
    (family s x).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
  simp only [family, transport_map]
  exact hindep s _ _

/-- The section of `F` over `x` amalgamating the transported family over the factorization
sieve. -/
public noncomputable def glue (hF : Presieve.IsSheaf J F) (hfac : HasLocalFactorizations J u)
    (hindep : TransportIndep u F) (s : (u.op ⋙ F).sections) (x : C) :
    F.obj (op x) :=
  (hF _ (hfac x)).amalgamate (family s x) (family_compatible hindep s x)

/-- The amalgamated section restricts along any morphism to the transport along any morphism to
the image of `u`. -/
public lemma map_glue (hF : Presieve.IsSheaf J F) (hfac : HasLocalFactorizations J u)
    (hindep : TransportIndep u F) (s : (u.op ⋙ F).sections) {y x : C}
    (h : y ⟶ x) {d : D} (φ : y ⟶ u.obj d) :
    F.map h.op (glue J hF hfac hindep s x) = transport s φ := by
  rw [glue, (hF _ (hfac x)).valid_glue _ h ⟨d, ⟨φ⟩⟩]
  exact hindep s _ _

/-- The amalgamated sections are compatible with every morphism of `𝒞`. -/
public lemma map_glue_eq (hF : Presieve.IsSheaf J F) (hfac : HasLocalFactorizations J u)
    (hindep : TransportIndep u F) (s : (u.op ⋙ F).sections) {y x : C} (g : y ⟶ x) :
    F.map g.op (glue J hF hfac hindep s x) = glue J hF hfac hindep s y := by
  refine (hF _ (hfac y)).isSeparatedFor.ext ?_
  rintro Z h ⟨d, ⟨φ⟩⟩
  rw [map_map, map_glue J hF hfac hindep s (h ≫ g) φ, map_glue J hF hfac hindep s h φ]

/-- The compatible family of sections of `F` over `𝒞` amalgamated from a compatible family of
sections of the restriction of `F` along `u`. -/
public noncomputable def glueSections (hF : Presieve.IsSheaf J F)
    (hfac : HasLocalFactorizations J u) (hindep : TransportIndep u F)
    (s : (u.op ⋙ F).sections) : F.sections where
  val j := glue J hF hfac hindep s j.unop
  property f := by simpa using map_glue_eq J hF hfac hindep s f.unop

/-- The amalgamated family restricts to the family it was built from. -/
public lemma glueSections_restrict (hF : Presieve.IsSheaf J F) (hfac : HasLocalFactorizations J u)
    (hindep : TransportIndep u F) (s : (u.op ⋙ F).sections) :
    Functor.sectionsPrecomp u.op (glueSections J hF hfac hindep s) = s := by
  refine Subtype.ext (funext fun ⟨d⟩ => ?_)
  simpa [glueSections, transport] using
    map_glue J hF hfac hindep s (𝟙 (u.obj d)) (𝟙 (u.obj d))

/-- Two compatible families of sections of `F` over `𝒞` agreeing on the image of `u` agree. -/
private lemma eq_of_restrict_eq (hF : Presieve.IsSheaf J F) (hfac : HasLocalFactorizations J u)
    (t₁ t₂ : F.sections) (h : ∀ d : D, t₁.val (op (u.obj d)) = t₂.val (op (u.obj d))) (x : C) :
    t₁.val (op x) = t₂.val (op x) := by
  refine (hF _ (hfac x)).isSeparatedFor.ext ?_
  rintro Z hz ⟨d, ⟨φ⟩⟩
  rw [t₁.property hz.op, t₂.property hz.op, ← t₁.property φ.op, ← t₂.property φ.op, h d]

/-- If every object of the site `(𝒞, J)` is covered by objects admitting a morphism to the image
of `u : 𝒟 ⥤ 𝒞`, then restriction of global sections of a sheaf of sets along `u` is injective. -/
public theorem injective_sectionsPrecomp_of_hasLocalFactorizations (hF : Presieve.IsSheaf J F)
    (hfac : HasLocalFactorizations J u) :
    Function.Injective (Functor.sectionsPrecomp u.op (P := F)) := by
  intro t₁ t₂ he
  refine Subtype.ext (funext fun ⟨x⟩ => ?_)
  exact eq_of_restrict_eq J hF hfac t₁ t₂
    (fun d => congrFun (congrArg Subtype.val he) (op d)) x

/-- Let `(𝒞, J)` be a site, `u : 𝒟 ⥤ 𝒞` a functor, and `F` a sheaf of sets on `𝒞`. If every
object of `𝒞` is covered by objects admitting a morphism to the image of `u`, and if any two
morphisms to the image of `u` are locally dominated by a single one, then restriction along `u`
is a bijection `Γ(𝒞, F) ≅ Γ(𝒟, u^{-1}F)`. -/
public theorem bijective_sectionsPrecomp_of_hasLocalFactorizations (hF : Presieve.IsSheaf J F)
    (hfac : HasLocalFactorizations J u) (hconn : HasConnectedLocalFactorizations J u) :
    Function.Bijective (Functor.sectionsPrecomp u.op (P := F)) :=
  have hindep := transportIndep_of_hasConnectedLocalFactorizations J hF hconn
  ⟨injective_sectionsPrecomp_of_hasLocalFactorizations J hF hfac,
    fun s => ⟨glueSections J hF hfac hindep s, glueSections_restrict J hF hfac hindep s⟩⟩

/-- The comparison of global sections of
`Stacks.Sites.bijective_sectionsPrecomp_of_hasLocalFactorizations`, as an equivalence. -/
public noncomputable def sectionsEquivOfHasLocalFactorizations (hF : Presieve.IsSheaf J F)
    (hfac : HasLocalFactorizations J u) (hconn : HasConnectedLocalFactorizations J u) :
    F.sections ≃ (u.op ⋙ F).sections :=
  Equiv.ofBijective _ (bijective_sectionsPrecomp_of_hasLocalFactorizations J hF hfac hconn)

end

end Stacks.Sites

end

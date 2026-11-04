module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence

/-!
# Sections of a morphism of algebraic spaces and invertible quotients

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `ℰ` be an `𝒪_X`-module on
the small étale site of `X`.  Tag 0B4I asserts that the sections of the projection
`𝐏(ℰ) ⟶ X` of the projective bundle of `ℰ` are in bijection with the surjections of `ℰ` onto an
invertible `𝒪_X`-module, taken up to isomorphism of the target; that such a section is a closed
immersion; and that the conormal sheaf of the section is `ker(ℰ ⟶ ℒ) ⊗ ℒ^{⊗ -1}`.

This file constructs the bijection, as in the scheme-level statement of Tag 0B3V, through a
*tautological datum* on the projection.  For a morphism `π : P ⟶ X` of algebraic spaces a
tautological datum is an invertible `𝒪_P`-module together with a surjection onto it from
`π^*ℰ`; on `𝐏(ℰ)` it is `𝒪(1)` with the universal surjection of Tag 01O4.  A section `σ` of `π`
yields an invertible quotient of `ℰ`, by pulling the datum's surjection back along `σ` and using
`σ ≫ π = 𝟙 X` to identify `σ^*π^*ℰ` with `ℰ`.  The bijectivity of the induced map on
isomorphism classes is the mapping-in half of the universal property of relative `Proj`,
`AlgebraicGeometry.Space.TautologicalDatum.IsUniversal`.

## Main definitions

* `AlgebraicGeometry.Space.InvertibleQuotient`: a surjection from an `𝒪_X`-module onto an
  invertible `𝒪_X`-module, with `AlgebraicGeometry.Space.InvertibleQuotient.IsEquivalent`,
  `AlgebraicGeometry.Space.invertibleQuotientSetoid` and
  `AlgebraicGeometry.Space.InvertibleQuotientClass` recording when two of them are identified.
* `AlgebraicGeometry.Space.TautologicalDatum`: an invertible `𝒪_P`-module together with a
  surjection onto it from `π^*ℰ`.
* `AlgebraicGeometry.Space.sectionPullbackIso`: the identification `ℰ ≅ σ^*π^*ℰ` attached to a
  section `σ` of `π`.
* `AlgebraicGeometry.Space.TautologicalDatum.pullbackQuotientMap`: the datum's surjection pulled
  back along a section, read as a map out of `ℰ` itself.
* `AlgebraicGeometry.Space.TautologicalDatum.pullbackQuotient`: that map as an invertible
  quotient of `ℰ`.
* `AlgebraicGeometry.Space.TautologicalDatum.Classifies`: the relation "the section `σ`
  classifies the invertible quotient `Q`", namely that `Q` is isomorphic over `ℰ` to the quotient
  `σ` pulls back.
* `AlgebraicGeometry.Space.TautologicalDatum.sectionsMap`: the induced map from the sections of
  `π` to the isomorphism classes of invertible quotients of `ℰ`.
* `AlgebraicGeometry.Space.TautologicalDatum.IsUniversal`: the assertion that every invertible
  quotient is classified by a section and that a section is determined by the quotient it
  classifies.
* `AlgebraicGeometry.Space.TautologicalDatum.sectionsEquivInvertibleQuotients`: the bijection
  between the sections of `π` and the isomorphism classes of invertible quotients of `ℰ`, for a
  universal tautological datum.

## Main results

* `AlgebraicGeometry.Space.TautologicalDatum.epi_pullbackQuotientMap`: the pulled-back surjection
  is again surjective.
* `AlgebraicGeometry.Space.TautologicalDatum.classifies_iff` and
  `AlgebraicGeometry.Space.TautologicalDatum.sectionsMap_eq_iff`: the classifying relation
  spelled out, and the normalization of `sectionsMap` by the datum's surjection.
* `AlgebraicGeometry.Space.TautologicalDatum.sectionsEquivInvertibleQuotients_eq_iff`: the same
  normalization for the bijection, and
  `AlgebraicGeometry.Space.TautologicalDatum.classifies_symm_apply`: the section attached to an
  invertible quotient by the inverse bijection classifies that quotient.
* `AlgebraicGeometry.Space.TautologicalDatum.isUniversal_of_equiv`: a bijection normalized by
  the datum's surjection forces `IsUniversal`, and
  `AlgebraicGeometry.Space.TautologicalDatum.eq_of_normalized`: a normalized bijection is
  unique.

## Implementation notes

The statements are for an arbitrary morphism `π` of algebraic spaces carrying a tautological
datum, in place of the projection of `𝐏(ℰ)`, and `IsUniversal` is a hypothesis, equivalent to
the bijection by `isUniversal_of_equiv`.  The two other assertions of Tag 0B4I, that a section is
a closed immersion and the description of its conormal sheaf, are not covered.

The pseudofunctoriality `AlgebraicGeometry.Space.ModulePushforwardCoherence` of Stacks 03LU is a
hypothesis; only its unit law `(𝟙 X)^* ≅ 𝟭` is used, in `sectionPullbackIso`.  Quasi-coherence of
`ℰ` is not assumed: the statements hold for every `𝒪_X`-module.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Invertible quotients of an `𝒪_X`-module -/

/-- An invertible quotient of an `𝒪_X`-module `E` on an algebraic space `X`: a surjection of `E`
onto an invertible `𝒪_X`-module. -/
structure InvertibleQuotient (X : AlgebraicSpaces B S hS)
    (E : Modules.{u, u} B S hS X.1 X.2) where
  /-- The invertible module the quotient maps onto. -/
  L : Modules.{u, u} B S hS X.1 X.2
  /-- It is invertible. -/
  invertible : IsInvertibleModule X L
  /-- The quotient map. -/
  q : E ⟶ L
  /-- It is surjective. -/
  epi : Epi q

namespace InvertibleQuotient

variable {X : AlgebraicSpaces B S hS} {E : Modules.{u, u} B S hS X.1 X.2}

/-- Two invertible quotients of `E` are equivalent when some isomorphism of their targets
carries the first quotient map to the second. -/
def IsEquivalent (Q R : InvertibleQuotient X E) : Prop :=
  ∃ α : Q.L ≅ R.L, Q.q ≫ α.hom = R.q

/-- An invertible quotient is equivalent to itself. -/
theorem IsEquivalent.refl (Q : InvertibleQuotient X E) : Q.IsEquivalent Q :=
  ⟨Iso.refl _, by simp⟩

/-- If `Q` is equivalent to `R`, then `R` is equivalent to `Q`. -/
theorem IsEquivalent.symm {Q R : InvertibleQuotient X E} (h : Q.IsEquivalent R) :
    R.IsEquivalent Q := by
  obtain ⟨α, hα⟩ := h
  exact ⟨α.symm, by rw [Iso.symm_hom, ← hα, Category.assoc, α.hom_inv_id, Category.comp_id]⟩

/-- If `Q` is equivalent to `R` and `R` to `T`, then `Q` is equivalent to `T`. -/
theorem IsEquivalent.trans {Q R T : InvertibleQuotient X E} (h : Q.IsEquivalent R)
    (h' : R.IsEquivalent T) : Q.IsEquivalent T := by
  obtain ⟨α, hα⟩ := h
  obtain ⟨β, hβ⟩ := h'
  exact ⟨α ≪≫ β, by rw [Iso.trans_hom, ← Category.assoc, hα, hβ]⟩

end InvertibleQuotient

/-- Equivalence of invertible quotients is an equivalence relation. -/
def invertibleQuotientSetoid (X : AlgebraicSpaces B S hS)
    (E : Modules.{u, u} B S hS X.1 X.2) : Setoid (InvertibleQuotient X E) where
  r := InvertibleQuotient.IsEquivalent
  iseqv :=
    ⟨InvertibleQuotient.IsEquivalent.refl, InvertibleQuotient.IsEquivalent.symm,
      InvertibleQuotient.IsEquivalent.trans⟩

/-- The isomorphism classes of invertible quotients of `E`. -/
abbrev InvertibleQuotientClass (X : AlgebraicSpaces B S hS)
    (E : Modules.{u, u} B S hS X.1 X.2) :=
  Quotient (invertibleQuotientSetoid X E)

/-! ### The identification `E ≅ σ^*π^*E` at a section -/

/-- The identification of `E` with `σ^*π^*E` attached to a section `σ` of `π`: the unit law
`(𝟙 X)^* ≅ 𝟭` followed by the comparison of the inverse image along `σ ≫ π = 𝟙 X` with the
iterated inverse image. -/
def sectionPullbackIso (hc : ModulePushforwardCoherence B S hS)
    {P X : AlgebraicSpaces B S hS} (π : P ⟶ X) {σ : X ⟶ P} (hσ : σ ≫ π = 𝟙 X)
    (E : Modules.{u, u} B S hS X.1 X.2) :
    E ≅ (modulePullback B S hS σ).obj ((modulePullback B S hS π).obj E) :=
  Iso.app ((hc.modulePullbackIdIso X).symm ≪≫ modulePullbackTriangle B S hS hσ) E

/-! ### Tautological data -/

/-- A tautological datum on `π : P ⟶ X` for the `𝒪_X`-module `E`: an invertible `𝒪_P`-module
together with a surjection onto it from `π^*E`.  On the projection of the projective bundle
`𝐏(E)` this is `𝒪(1)` with the universal surjection of Tag 01O4. -/
structure TautologicalDatum {P X : AlgebraicSpaces B S hS} (π : P ⟶ X)
    (E : Modules.{u, u} B S hS X.1 X.2) where
  /-- The tautological invertible module, `𝒪_{𝐏(E)}(1)`. -/
  twist : Modules.{u, u} B S hS P.1 P.2
  /-- It is invertible. -/
  invertible : IsInvertibleModule P twist
  /-- The tautological quotient map `π^*E ⟶ 𝒪(1)`. -/
  univ : (modulePullback B S hS π).obj E ⟶ twist
  /-- It is surjective. -/
  epi_univ : Epi univ

namespace TautologicalDatum

variable {P X : AlgebraicSpaces B S hS} {π : P ⟶ X} {E : Modules.{u, u} B S hS X.1 X.2}
  (hc : ModulePushforwardCoherence B S hS)

/-- The tautological quotient map pulled back along a section, read as a map out of `E` itself
through the identification `E ≅ σ^*π^*E`. -/
def pullbackQuotientMap (D : TautologicalDatum π E) {σ : X ⟶ P} (hσ : σ ≫ π = 𝟙 X) :
    E ⟶ (modulePullback B S hS σ).obj D.twist :=
  (sectionPullbackIso hc π hσ E).hom ≫ (modulePullback B S hS σ).map D.univ

/-- The pulled-back tautological quotient map is surjective. -/
instance epi_pullbackQuotientMap (D : TautologicalDatum π E) {σ : X ⟶ P}
    (hσ : σ ≫ π = 𝟙 X) : Epi (pullbackQuotientMap hc D hσ) := by
  have := D.epi_univ
  have : (modulePullback B S hS σ).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS σ)
  exact epi_comp _ _

/-- The invertible quotient of `E` classified by a section of `π`. -/
@[stacks 0B4I "the invertible quotient attached to a section, given the 03LU unit law"]
def pullbackQuotient (D : TautologicalDatum π E) {σ : X ⟶ P} (hσ : σ ≫ π = 𝟙 X) :
    InvertibleQuotient X E where
  L := (modulePullback B S hS σ).obj D.twist
  invertible := modulePullbackInvertible σ D.twist D.invertible
  q := pullbackQuotientMap hc D hσ
  epi := inferInstance

/-- The quotient map of `pullbackQuotient hc D hσ` is `pullbackQuotientMap hc D hσ`, the
tautological quotient map pulled back along the section. -/
@[simp]
theorem pullbackQuotient_q (D : TautologicalDatum π E) {σ : X ⟶ P} (hσ : σ ≫ π = 𝟙 X) :
    (pullbackQuotient hc D hσ).q = pullbackQuotientMap hc D hσ :=
  rfl

/-- The section `σ` classifies the invertible quotient `Q`: `Q` is isomorphic over `E` to the
quotient that `σ` pulls back from the tautological one. -/
def Classifies (D : TautologicalDatum π E) {σ : X ⟶ P} (hσ : σ ≫ π = 𝟙 X)
    (Q : InvertibleQuotient X E) : Prop :=
  (pullbackQuotient hc D hσ).IsEquivalent Q

/-- The classifying relation spelled out: an isomorphism from the inverse image of the
tautological module to the quotient module, carrying the pulled-back tautological map to
`Q.q`. -/
theorem classifies_iff (D : TautologicalDatum π E) {σ : X ⟶ P} (hσ : σ ≫ π = 𝟙 X)
    (Q : InvertibleQuotient X E) :
    Classifies hc D hσ Q ↔
      ∃ α : (modulePullback B S hS σ).obj D.twist ≅ Q.L,
        pullbackQuotientMap hc D hσ ≫ α.hom = Q.q :=
  Iff.rfl

/-- A section classifies the quotient it pulls back. -/
theorem classifies_pullbackQuotient (D : TautologicalDatum π E) {σ : X ⟶ P}
    (hσ : σ ≫ π = 𝟙 X) :
    Classifies hc D hσ (pullbackQuotient hc D hσ) :=
  InvertibleQuotient.IsEquivalent.refl _

/-- The classifying relation only depends on the isomorphism class of the quotient. -/
theorem Classifies.trans {D : TautologicalDatum π E}
    {σ : X ⟶ P} {hσ : σ ≫ π = 𝟙 X} {Q R : InvertibleQuotient X E}
    (h : Classifies hc D hσ Q) (hQR : Q.IsEquivalent R) : Classifies hc D hσ R :=
  InvertibleQuotient.IsEquivalent.trans h hQR

/-- The map from the sections of `π` to the isomorphism classes of invertible quotients of `E`,
sending a section to the class of the quotient it pulls back. -/
def sectionsMap (D : TautologicalDatum π E) :
    { σ : X ⟶ P // σ ≫ π = 𝟙 X } → InvertibleQuotientClass X E :=
  fun σ => Quotient.mk (invertibleQuotientSetoid X E) (pullbackQuotient hc D σ.2)

/-- `sectionsMap` sends a section to the class of `Q` exactly when the section classifies `Q`. -/
theorem sectionsMap_eq_iff (D : TautologicalDatum π E) (σ : { σ : X ⟶ P // σ ≫ π = 𝟙 X })
    (Q : InvertibleQuotient X E) :
    sectionsMap hc D σ = Quotient.mk (invertibleQuotientSetoid X E) Q ↔
      Classifies hc D σ.2 Q :=
  Quotient.eq (r := invertibleQuotientSetoid X E)

/-- The mapping-in half of the universal property of `𝐏(E)`, for a tautological datum: every
invertible quotient of `E` is classified by a section of `π`, and a section is determined by the
quotient it classifies. -/
structure IsUniversal (D : TautologicalDatum π E) : Prop where
  /-- Every invertible quotient is classified by a section. -/
  exists_classifies : ∀ Q : InvertibleQuotient X E, ∃ σ : X ⟶ P, ∃ hσ : σ ≫ π = 𝟙 X,
    Classifies hc D hσ Q
  /-- A section is determined by the quotient it classifies. -/
  eq_of_classifies : ∀ (σ σ' : X ⟶ P) (hσ : σ ≫ π = 𝟙 X) (hσ' : σ' ≫ π = 𝟙 X)
    (Q : InvertibleQuotient X E), Classifies hc D hσ Q → Classifies hc D hσ' Q →
    σ = σ'

/-- For a universal tautological datum, `sectionsMap` is bijective. -/
theorem bijective_sectionsMap (D : TautologicalDatum π E) (hD : IsUniversal hc D) :
    Function.Bijective (sectionsMap hc D) := by
  refine ⟨fun σ σ' h => Subtype.ext ?_, Quotient.ind fun Q => ?_⟩
  · exact hD.eq_of_classifies σ.1 σ'.1 σ.2 σ'.2 (pullbackQuotient hc D σ'.2)
      ((sectionsMap_eq_iff hc D σ _).1 h) (classifies_pullbackQuotient hc D σ'.2)
  · obtain ⟨σ, hσ, h⟩ := hD.exists_classifies Q
    exact ⟨⟨σ, hσ⟩, (sectionsMap_eq_iff hc D ⟨σ, hσ⟩ Q).2 h⟩

/-- The bijection between the sections of `π` and the invertible quotients of `E` up to
isomorphism, for a universal tautological datum, sending a section to the quotient it pulls
back. -/
@[stacks 0B4I "the bijection, for a universal tautological datum, given the 03LU unit law"]
def sectionsEquivInvertibleQuotients (D : TautologicalDatum π E) (hD : IsUniversal hc D) :
    { σ : X ⟶ P // σ ≫ π = 𝟙 X } ≃ InvertibleQuotientClass X E :=
  Equiv.ofBijective (sectionsMap hc D) (bijective_sectionsMap hc D hD)

/-- `sectionsEquivInvertibleQuotients` sends a section to the class of the invertible quotient
it pulls back. -/
@[simp]
theorem sectionsEquivInvertibleQuotients_apply (D : TautologicalDatum π E)
    (hD : IsUniversal hc D) (σ : { σ : X ⟶ P // σ ≫ π = 𝟙 X }) :
    sectionsEquivInvertibleQuotients hc D hD σ =
      Quotient.mk (invertibleQuotientSetoid X E) (pullbackQuotient hc D σ.2) :=
  rfl

/-- The bijection sends a section to the class of `Q` exactly when the section classifies
`Q`. -/
theorem sectionsEquivInvertibleQuotients_eq_iff (D : TautologicalDatum π E)
    (hD : IsUniversal hc D) {σ : X ⟶ P} (hσ : σ ≫ π = 𝟙 X) (Q : InvertibleQuotient X E) :
    sectionsEquivInvertibleQuotients hc D hD ⟨σ, hσ⟩ =
        Quotient.mk (invertibleQuotientSetoid X E) Q ↔ Classifies hc D hσ Q :=
  sectionsMap_eq_iff hc D ⟨σ, hσ⟩ Q

/-- The section attached to an invertible quotient by the inverse bijection classifies it. -/
theorem classifies_symm_apply (D : TautologicalDatum π E) (hD : IsUniversal hc D)
    (Q : InvertibleQuotient X E) :
    Classifies hc D
      ((sectionsEquivInvertibleQuotients hc D hD).symm
        (Quotient.mk (invertibleQuotientSetoid X E) Q)).2 Q :=
  (sectionsEquivInvertibleQuotients_eq_iff hc D hD _ Q).1
    ((sectionsEquivInvertibleQuotients hc D hD).apply_symm_apply _)

/-- A bijection between the sections of `π` and the isomorphism classes of invertible quotients
of `E`, sending a section to the class of `Q` exactly when it classifies `Q`, makes the
tautological datum universal. -/
theorem isUniversal_of_equiv (D : TautologicalDatum π E)
    (e : { σ : X ⟶ P // σ ≫ π = 𝟙 X } ≃ InvertibleQuotientClass X E)
    (he : ∀ (σ : X ⟶ P) (hσ : σ ≫ π = 𝟙 X) (Q : InvertibleQuotient X E),
      e ⟨σ, hσ⟩ = Quotient.mk (invertibleQuotientSetoid X E) Q ↔ Classifies hc D hσ Q) :
    IsUniversal hc D where
  exists_classifies Q :=
    ⟨(e.symm (Quotient.mk (invertibleQuotientSetoid X E) Q)).1,
      (e.symm (Quotient.mk (invertibleQuotientSetoid X E) Q)).2,
      (he _ _ Q).1 (by simp)⟩
  eq_of_classifies σ σ' hσ hσ' Q h h' :=
    congrArg Subtype.val (e.injective (((he σ hσ Q).2 h).trans ((he σ' hσ' Q).2 h').symm))

/-- A bijection between the sections of `π` and the isomorphism classes of invertible quotients
of `E` that is normalized by the tautological surjection is unique. -/
theorem eq_of_normalized (D : TautologicalDatum π E)
    (e e' : { σ : X ⟶ P // σ ≫ π = 𝟙 X } ≃ InvertibleQuotientClass X E)
    (he : ∀ (σ : X ⟶ P) (hσ : σ ≫ π = 𝟙 X) (Q : InvertibleQuotient X E),
      e ⟨σ, hσ⟩ = Quotient.mk (invertibleQuotientSetoid X E) Q ↔ Classifies hc D hσ Q)
    (he' : ∀ (σ : X ⟶ P) (hσ : σ ≫ π = 𝟙 X) (Q : InvertibleQuotient X E),
      e' ⟨σ, hσ⟩ = Quotient.mk (invertibleQuotientSetoid X E) Q ↔ Classifies hc D hσ Q) :
    e = e' := by
  refine Equiv.coe_inj.1 (funext fun σ => ?_)
  have h := classifies_pullbackQuotient hc D σ.2
  exact ((he _ _ _).2 h).trans ((he' _ _ _).2 h).symm

end TautologicalDatum

end AlgebraicGeometry.Space

end

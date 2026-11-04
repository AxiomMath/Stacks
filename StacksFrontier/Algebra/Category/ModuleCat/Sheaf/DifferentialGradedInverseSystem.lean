module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiCoherent

/-!
# Inverse systems of differential graded algebras

Let `R` be a ring and let `ℕ` carry the chaotic topology and the constant sheaf of rings with
value `R` (more generally, any preordered type in place of `ℕ`; see the implementation notes). A
sheaf `𝒜` of differential graded algebras on this site is an inverse system `(A_n)` of
differential graded `R`-algebras, and a sheaf of differential graded `𝒜`-modules is an inverse
system `(M_n)` with `M_n` a differential graded `A_n`-module and `A_{n + 1}`-linear transition
maps `M_{n + 1} → M_n`. Write `QC(𝒜)` for the full subcategory of quasi-coherent objects of
`D(𝒜, d)`.

A morphism `φ : (A_n) → (B_n)` of pro-objects is given by integers `m(1) ≤ m(2) ≤ ⋯` together with
homomorphisms `φ_n : A_{m(n)} → B_n` of differential graded `R`-algebras commuting with the
transition maps, that is, by a functor `ℕ ⥤ ℕ` and a map `g^*𝒜 → ℬ` of sheaves of differential
graded algebras over the induced morphism of chaotic sites. The functor `QC(𝒜) ⥤ QC(ℬ)` it
induces sends a good `𝓜 = (M_n)` to `(M_{m(n)} ⊗_{A_{m(n)}} B_n)`; it is the derived pullback
`Lg^*` of Tag 0GZC.

If `φ` is an *isomorphism* of pro-objects, with inverse represented by `ψ_i : B_{n(i)} → A_i`,
then after enlarging the two index functions the composite `B_{n(m(i))} → A_{m(i)} → B_i` is the
transition map. Hence the round trip `QC(ℬ) ⥤ QC(𝒜) ⥤ QC(ℬ)` carries `𝒩 = (N_n)` to
`(N_{n(m(i))} ⊗_{B_{n(m(i))}} B_i)`, and the canonical map of that system to `𝒩` is over each
stage the comparison map of quasi-coherence. It is therefore invertible on `QC(ℬ)`, and
symmetrically on `QC(𝒜)`, so `QC(𝒜) ⥤ QC(ℬ)` is an equivalence.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.proTransition`: the transition morphism of `ℕᵒᵖ`
  attached to an inequality `i ≤ j` of stages.
* `SheafOfModules.DifferentialGradedModule.SectionData.ReflectsIsomorphisms`: the derived
  sections over the stages of an inverse system detect isomorphisms of `D(𝒜, d)`.
* `SheafOfModules.DifferentialGradedModule.proRoundTripSectionsIso`: the derived sections over
  the `i`-th stage of a round trip of derived pullbacks are the base change of the derived
  sections over the stage `n(m(i))` along the transition homomorphism.
* `SheafOfModules.DifferentialGradedModule.ProIsomorphismData`: an isomorphism of pro-objects,
  in the form its two round trips take: cofinality of the composite reindexings together with the
  canonical maps of the round trips to the identity and the identification of their stagewise
  sections with the comparison maps of quasi-coherence.
* `SheafOfModules.DifferentialGradedModule.ProIsomorphismData.ofRoundTripSections`: the same data
  assembled from the two derived pullbacks and the identification of base change along two
  structure homomorphisms in turn with base change along the transition homomorphism.

## Main results

* `SheafOfModules.DifferentialGradedModule.isIso_app_of_isQC`: a canonical map to the identity
  whose stagewise sections are the comparison maps of quasi-coherence is invertible at every
  quasi-coherent object.
* `SheafOfModules.DifferentialGradedModule.isEquivalence_qcPullback`: the derived pullbacks
  along a pair of representatives whose round trips carry such canonical maps are mutually
  quasi-inverse on quasi-coherent objects, over an abstract section datum. Tag 0GZH itself is
  `DifferentialGradedAlgebra.SystemProHom.isEquivalence_qcPullback` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedChaoticProIsomorphism.lean`,
  where the derived pullback and the quasi-coherent objects are built from the inverse systems
  themselves.

## Implementation notes

The functor `QC(𝒜) ⥤ QC(ℬ)` of the source is not a new construction: a representative of a
morphism of pro-objects is exactly a functor `ℕ ⥤ ℕ` together with a `MorphismSectionData` for
it, its derived pullback is a `DerivedTensorData`, and the induced functor on quasi-coherent
objects is `SheafOfModules.DifferentialGradedModule.qcPullback` of Tag 0GZC. Only the
pro-isomorphism and its consequence are new here.

What is carried as a hypothesis, and why. The ambient library has no description of a morphism of
`D(𝒜, d)` between the images of two good differential graded modules — a morphism there is a
fraction, and good modules are K-flat rather than K-projective — so neither the canonical map of a
round trip to the identity nor the conservativity of the family of derived sections is
constructible from the data of a `GoodModuleData`. Both are therefore fields, respectively of
`ProIsomorphismData` and of the hypothesis `SectionData.ReflectsIsomorphisms`, in the same way
that the computation of the derived sections of a derived pullback is the field `sectionsIso` of
`DerivedPullbackSectionData`. Neither hypothesis asserts that anything is invertible: the
stagewise pinning of the canonical map is an existential identification of it with the comparison
map `RΓ(n(m(i)), 𝒩) ⊗^𝐋_{B_{n(m(i))}} B_i ⟶ RΓ(i, 𝒩)` up to a *choice* of isomorphism of its
source, and the invertibility of that comparison map is quasi-coherence, which is where the
conclusion comes from. That the identification is available is the content of
`proRoundTripSectionsIso`, which computes the source of the comparison map from the two derived
pullbacks and the identity `φ_i ∘ ψ_{m(i)} = ` transition expressing that `φ` is a
pro-isomorphism; `exists_sections_eq_sectionComparison` records that it supplies the field.

The index functions are packaged as functors `ι ⥤ ι`, which is exactly a monotone map, so the
monotonicity of the source's `m(·)` and `n(·)` carries no separate hypothesis; cofinality of the
two composites is the fields `le₁` and `le₂`.

*The index site.* The source's site is `ℕ`. The statements here are made for an arbitrary
preordered type `ι : Type w`, viewed as a small category, of which `ℕ` is the case `w = 0`. The
generality is what lets the site live in the universe of the ring: the triangulated structure of
`D(𝒜, d)` and the calculus of fractions on its quasi-isomorphisms (Tag 0FT4) are available for a
site, its morphisms and its sheaf of rings in one universe, and for a ring `R : Type u` the site
`ULift.{u} ℕ`, order-isomorphic to `ℕ`, is such a site where `ℕ` itself is not unless `u = 0`.

UNIVERSES. Apart from the universe `w` of the index site, the sheaf of rings, the algebra and
module components of the two sheaves of differential graded algebras, the objects and morphisms
of the two derived categories and the coefficient ring of the section algebras all keep
independent universes, as in `DifferentialGradedQuasiCoherent`.

## References

* [Stacks Project, Section 24.35 (Tag 0GZG)](https://stacks.math.columbia.edu/tag/0GZG)
* [Stacks Project, Lemma 24.35.1 (Tag 0GZH)](https://stacks.math.columbia.edu/tag/0GZH)
* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Lemma 24.33.4 (Tag 0GZC)](https://stacks.math.columbia.edu/tag/0GZC)
* [Stacks Project, Example 4.22.6 (Tag 05PY)](https://stacks.math.columbia.edu/tag/05PY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe s t a m d e a' m' d' e' w

namespace SheafOfModules.DifferentialGradedModule

/-! ### Stages of an inverse system, and conservativity of their derived sections -/

/-- The transition morphism `op j ⟶ op i` of `ιᵒᵖ` attached to `i ≤ j`: on the site `ι` of an
inverse system it is the arrow along which the `j`-th stage restricts to the `i`-th. -/
def proTransition {ι : Type w} [Preorder ι] {i j : ι} (h : i ≤ j) : (op j : ιᵒᵖ) ⟶ op i :=
  (homOfLE h).op

section Reflects

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {Λ : Type s} [CommRing Λ] {A : DifferentialGradedAlgebra.{t, a} R} {D : Type d}
  [Category.{e} D] {gA : GoodModuleData.{t, a, m, _, _, d, e} A D}

/-- The derived sections functors detect isomorphisms: a morphism of `D(𝒜, d)` is invertible as
soon as its derived sections over every object of the site are invertible. On a chaotic site a
morphism of the derived category is a fraction of homomorphisms, and a homomorphism whose
sections are quasi-isomorphisms over every object is a quasi-isomorphism. -/
def SectionData.ReflectsIsomorphisms (sd : SectionData Λ gA) : Prop :=
  ∀ ⦃X Y : D⦄ (f : X ⟶ Y), (∀ U : Cᵒᵖ, IsIso ((sd.derivedSections U).map f)) → IsIso f

end Reflects

/-! ### The round trip of two derived pullbacks -/

section RoundTrip

variable {ι : Type w} [Preorder ι] {J : GrothendieckTopology ι} {R : Sheaf J RingCat.{t}}
  {Λ : Type s} [CommRing Λ]
  {A₁ : DifferentialGradedAlgebra.{t, a} R} {A₂ : DifferentialGradedAlgebra.{t, a'} R}
  {D₁ : Type d} [Category.{e} D₁] {D₂ : Type d'} [Category.{e'} D₂]
  {g₁ : GoodModuleData.{t, a, m, w, w, d, e} A₁ D₁}
  {g₂ : GoodModuleData.{t, a', m', w, w, d', e'} A₂ D₂} {sd₁ : SectionData Λ g₁}
  {sd₂ : SectionData Λ g₂} {F₁ F₂ : ι ⥤ ι} {msd₁ : MorphismSectionData F₁ sd₁ sd₂}
  {msd₂ : MorphismSectionData F₂ sd₂ sd₁} {Lg₁ : DerivedTensorData g₁ g₂}
  {Lg₂ : DerivedTensorData g₂ g₁}

/-- The derived sections over the `i`-th stage of the round trip `Lg₂^* ∘ Lg₁^*`: they are the
base change along the transition homomorphism `A₂(F₂ F₁ i) → A₂(i)` of the derived sections over
the stage `F₂ (F₁ i)`. The hypothesis `bcc` is the identification of base change along the two
structure homomorphisms in turn with base change along their composite, which is the transition
homomorphism exactly when the two representatives compose to the identity of pro-objects. -/
def proRoundTripSectionsIso (dp₁ : DerivedPullbackSectionData msd₁ Lg₁)
    (dp₂ : DerivedPullbackSectionData msd₂ Lg₂) (h : ∀ i : ι, i ≤ F₂.obj (F₁.obj i))
    (bcc : ∀ i : ι, msd₂.baseChange (op (F₁.obj i)) ⋙ msd₁.baseChange (op i) ≅
      sd₂.baseChange (proTransition (h i))) (i : ι) :
    (Lg₂.derived ⋙ Lg₁.derived) ⋙ sd₂.derivedSections (op i) ≅
      sd₂.derivedSections (op (F₂.obj (F₁.obj i))) ⋙ sd₂.baseChange (proTransition (h i)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft Lg₂.derived (dp₁.sectionsIso (op i)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (dp₂.sectionsIso (op (F₁.obj i))) (msd₁.baseChange (op i)) ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (bcc i)

end RoundTrip

/-! ### A pro-isomorphism and the equivalence it induces -/

section ProIsomorphism

variable {ι : Type w} [Preorder ι] {J : GrothendieckTopology ι} {R : Sheaf J RingCat.{t}}
  {Λ : Type s} [CommRing Λ]
  {A₁ : DifferentialGradedAlgebra.{t, a} R} {A₂ : DifferentialGradedAlgebra.{t, a'} R}
  {D₁ : Type d} [Category.{e} D₁] {D₂ : Type d'} [Category.{e'} D₂]
  {g₁ : GoodModuleData.{t, a, m, w, w, d, e} A₁ D₁}
  {g₂ : GoodModuleData.{t, a', m', w, w, d', e'} A₂ D₂}

/-- An isomorphism of pro-objects `(A_n) → (B_n)`, in the form its two round trips take: the
composite reindexings are cofinal, each round trip carries a canonical map to the identity, and
over each stage that map is the comparison map of quasi-coherence. -/
structure ProIsomorphismData (sd₁ : SectionData Λ g₁) (sd₂ : SectionData Λ g₂) (F₁ F₂ : ι ⥤ ι)
    (Lg₁ : DerivedTensorData g₁ g₂) (Lg₂ : DerivedTensorData g₂ g₁) where
  /-- The reindexing of the round trip of `D(A₁, d)` is cofinal. -/
  le₁ : ∀ i : ι, i ≤ F₁.obj (F₂.obj i)
  /-- The reindexing of the round trip of `D(A₂, d)` is cofinal. -/
  le₂ : ∀ i : ι, i ≤ F₂.obj (F₁.obj i)
  /-- The canonical map of the round trip of `D(A₁, d)` to the identity. -/
  counit₁ : Lg₁.derived ⋙ Lg₂.derived ⟶ 𝟭 D₁
  /-- The canonical map of the round trip of `D(A₂, d)` to the identity. -/
  counit₂ : Lg₂.derived ⋙ Lg₁.derived ⟶ 𝟭 D₂
  /-- Over the `i`-th stage the canonical map of the round trip of `D(A₁, d)` is the comparison
  map `RΓ(F₁ F₂ i, K) ⊗^𝐋 A₁(i) ⟶ RΓ(i, K)` of quasi-coherence. -/
  sections_counit₁ (i : ι) (K : D₁) :
    ∃ e : (sd₁.derivedSections (op i)).obj ((Lg₁.derived ⋙ Lg₂.derived).obj K) ≅
        (sd₁.baseChange (proTransition (le₁ i))).obj
          ((sd₁.derivedSections (op (F₁.obj (F₂.obj i)))).obj K),
      (sd₁.derivedSections (op i)).map (counit₁.app K) =
        e.hom ≫ sectionComparison sd₁ (proTransition (le₁ i)) K
  /-- Over the `i`-th stage the canonical map of the round trip of `D(A₂, d)` is the comparison
  map `RΓ(F₂ F₁ i, K) ⊗^𝐋 A₂(i) ⟶ RΓ(i, K)` of quasi-coherence. -/
  sections_counit₂ (i : ι) (K : D₂) :
    ∃ e : (sd₂.derivedSections (op i)).obj ((Lg₂.derived ⋙ Lg₁.derived).obj K) ≅
        (sd₂.baseChange (proTransition (le₂ i))).obj
          ((sd₂.derivedSections (op (F₂.obj (F₁.obj i)))).obj K),
      (sd₂.derivedSections (op i)).map (counit₂.app K) =
        e.hom ≫ sectionComparison sd₂ (proTransition (le₂ i)) K

variable {sd₁ : SectionData Λ g₁} {sd₂ : SectionData Λ g₂} {F₁ F₂ : ι ⥤ ι}
  {Lg₁ : DerivedTensorData g₁ g₂} {Lg₂ : DerivedTensorData g₂ g₁}

/-- A pro-isomorphism read in the other direction. -/
def ProIsomorphismData.swap (data : ProIsomorphismData sd₁ sd₂ F₁ F₂ Lg₁ Lg₂) :
    ProIsomorphismData sd₂ sd₁ F₂ F₁ Lg₂ Lg₁ where
  le₁ := data.le₂
  le₂ := data.le₁
  counit₁ := data.counit₂
  counit₂ := data.counit₁
  sections_counit₁ := data.sections_counit₂
  sections_counit₂ := data.sections_counit₁

variable {msd₁ : MorphismSectionData F₁ sd₁ sd₂} {msd₂ : MorphismSectionData F₂ sd₂ sd₁}

/-- The stagewise identification required of a canonical map of a round trip is available as soon
as the map induces, over each stage, the comparison map of quasi-coherence read through
`proRoundTripSectionsIso`. -/
theorem exists_sections_eq_sectionComparison (dp₁ : DerivedPullbackSectionData msd₁ Lg₁)
    (dp₂ : DerivedPullbackSectionData msd₂ Lg₂) (h : ∀ i : ι, i ≤ F₂.obj (F₁.obj i))
    (bcc : ∀ i : ι, msd₂.baseChange (op (F₁.obj i)) ⋙ msd₁.baseChange (op i) ≅
      sd₂.baseChange (proTransition (h i))) (τ : Lg₂.derived ⋙ Lg₁.derived ⟶ 𝟭 D₂)
    (hτ : ∀ (i : ι) (K : D₂), (sd₂.derivedSections (op i)).map (τ.app K) =
      (proRoundTripSectionsIso dp₁ dp₂ h bcc i).hom.app K ≫
        sectionComparison sd₂ (proTransition (h i)) K) (i : ι) (K : D₂) :
    ∃ e : (sd₂.derivedSections (op i)).obj ((Lg₂.derived ⋙ Lg₁.derived).obj K) ≅
        (sd₂.baseChange (proTransition (h i))).obj
          ((sd₂.derivedSections (op (F₂.obj (F₁.obj i)))).obj K),
      (sd₂.derivedSections (op i)).map (τ.app K) =
        e.hom ≫ sectionComparison sd₂ (proTransition (h i)) K :=
  ⟨(proRoundTripSectionsIso dp₁ dp₂ h bcc i).app K, hτ i K⟩

/-- A pro-isomorphism assembled from the two derived pullbacks. Beyond the cofinality of the two
composite reindexings and the canonical maps of the two round trips, what is asked is the
identification of base change along two structure homomorphisms in turn with base change along the
transition homomorphism — which is what the identities `φ_i ∘ ψ_{m(i)} = ` transition and
`ψ_i ∘ φ_{n(i)} = ` transition of an isomorphism of pro-objects give — and the description of each
canonical map over the `i`-th stage through `proRoundTripSectionsIso`. -/
def ProIsomorphismData.ofRoundTripSections (dp₁ : DerivedPullbackSectionData msd₁ Lg₁)
    (dp₂ : DerivedPullbackSectionData msd₂ Lg₂) (le₁ : ∀ i : ι, i ≤ F₁.obj (F₂.obj i))
    (le₂ : ∀ i : ι, i ≤ F₂.obj (F₁.obj i))
    (bcc₁ : ∀ i : ι, msd₁.baseChange (op (F₂.obj i)) ⋙ msd₂.baseChange (op i) ≅
      sd₁.baseChange (proTransition (le₁ i)))
    (bcc₂ : ∀ i : ι, msd₂.baseChange (op (F₁.obj i)) ⋙ msd₁.baseChange (op i) ≅
      sd₂.baseChange (proTransition (le₂ i)))
    (counit₁ : Lg₁.derived ⋙ Lg₂.derived ⟶ 𝟭 D₁) (counit₂ : Lg₂.derived ⋙ Lg₁.derived ⟶ 𝟭 D₂)
    (h₁ : ∀ (i : ι) (K : D₁), (sd₁.derivedSections (op i)).map (counit₁.app K) =
      (proRoundTripSectionsIso dp₂ dp₁ le₁ bcc₁ i).hom.app K ≫
        sectionComparison sd₁ (proTransition (le₁ i)) K)
    (h₂ : ∀ (i : ι) (K : D₂), (sd₂.derivedSections (op i)).map (counit₂.app K) =
      (proRoundTripSectionsIso dp₁ dp₂ le₂ bcc₂ i).hom.app K ≫
        sectionComparison sd₂ (proTransition (le₂ i)) K) :
    ProIsomorphismData sd₁ sd₂ F₁ F₂ Lg₁ Lg₂ where
  le₁ := le₁
  le₂ := le₂
  counit₁ := counit₁
  counit₂ := counit₂
  sections_counit₁ := exists_sections_eq_sectionComparison dp₂ dp₁ le₁ bcc₁ counit₁ h₁
  sections_counit₂ := exists_sections_eq_sectionComparison dp₁ dp₂ le₂ bcc₂ counit₂ h₂

/-- A canonical map to the identity whose sections over every stage are the comparison maps of
quasi-coherence is invertible at a quasi-coherent object: those comparison maps are invertible by
quasi-coherence, and the derived sections detect isomorphisms. -/
theorem isIso_app_of_isQC (hc : sd₂.ReflectsIsomorphisms) {T : D₂ ⥤ D₂} (τ : T ⟶ 𝟭 D₂)
    {q : ι → ι} (h : ∀ i : ι, i ≤ q i)
    (hτ : ∀ (i : ι) (K : D₂),
      ∃ e : (sd₂.derivedSections (op i)).obj (T.obj K) ≅
          (sd₂.baseChange (proTransition (h i))).obj
            ((sd₂.derivedSections (op (q i))).obj K),
        (sd₂.derivedSections (op i)).map (τ.app K) =
          e.hom ≫ sectionComparison sd₂ (proTransition (h i)) K)
    (K : D₂) (hK : IsQC sd₂ K) : IsIso (τ.app K) := by
  have key : ∀ i : ι, IsIso ((sd₂.derivedSections (op i)).map (τ.app K)) := by
    intro i
    obtain ⟨e, he⟩ := hτ i K
    rw [he]
    have := hK (proTransition (h i))
    infer_instance
  exact hc _ fun U => key U.unop

/-- The derived pullback of a quasi-coherent object has the derived pullback of its underlying
object. -/
@[simp] theorem qcPullback_obj_obj (dp : DerivedPullbackSectionData msd₁ Lg₁) (K : QC sd₁) :
    ((qcPullback dp).obj K).obj = Lg₁.derived.obj K.obj :=
  rfl

/-- The derived pullback of a morphism of quasi-coherent objects is the derived pullback of the
underlying morphism. -/
@[simp] theorem qcPullback_map_hom (dp : DerivedPullbackSectionData msd₁ Lg₁) {K L : QC sd₁}
    (f : K ⟶ L) : ((qcPullback dp).map f).hom = Lg₁.derived.map f.hom :=
  rfl

/-- The canonical map of the round trip of `QC(A₂, d)` to the identity: the round trip of derived
pullbacks preserves quasi-coherence, so the canonical map of `D(A₂, d)` is one of the full
subcategory. -/
def qcRoundTripCounit (dp₁ : DerivedPullbackSectionData msd₁ Lg₁)
    (dp₂ : DerivedPullbackSectionData msd₂ Lg₂)
    (data : ProIsomorphismData sd₁ sd₂ F₁ F₂ Lg₁ Lg₂) :
    qcPullback dp₂ ⋙ qcPullback dp₁ ⟶ 𝟭 (QC sd₂) where
  app K := ObjectProperty.homMk (data.counit₂.app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ (data.counit₂.naturality f.hom)

/-- The component of the canonical map of the round trip of `QC(A₂, d)` at `K` is the component
of the canonical map of the round trip of `D(A₂, d)` at the underlying object of `K`. -/
@[simp] theorem qcRoundTripCounit_app_hom (dp₁ : DerivedPullbackSectionData msd₁ Lg₁)
    (dp₂ : DerivedPullbackSectionData msd₂ Lg₂)
    (data : ProIsomorphismData sd₁ sd₂ F₁ F₂ Lg₁ Lg₂) (K : QC sd₂) :
    ((qcRoundTripCounit dp₁ dp₂ data).app K).hom = data.counit₂.app K.obj :=
  rfl

/-- On quasi-coherent objects the canonical map of the round trip is an isomorphism. -/
theorem isIso_qcRoundTripCounit (dp₁ : DerivedPullbackSectionData msd₁ Lg₁)
    (dp₂ : DerivedPullbackSectionData msd₂ Lg₂) (hc : sd₂.ReflectsIsomorphisms)
    (data : ProIsomorphismData sd₁ sd₂ F₁ F₂ Lg₁ Lg₂) :
    IsIso (qcRoundTripCounit dp₁ dp₂ data) := by
  have key : ∀ K : QC sd₂, IsIso ((qcRoundTripCounit dp₁ dp₂ data).app K) := by
    intro K
    obtain ⟨g, hg₁, hg₂⟩ :=
      (isIso_app_of_isQC hc data.counit₂ data.le₂ data.sections_counit₂ K.obj K.property).out
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg₁, ObjectProperty.hom_ext _ hg₂⟩
  exact NatIso.isIso_of_isIso_app _

/-- The round trip of quasi-coherent objects along a pro-isomorphism is isomorphic to the
identity. -/
def qcRoundTripIso (dp₁ : DerivedPullbackSectionData msd₁ Lg₁)
    (dp₂ : DerivedPullbackSectionData msd₂ Lg₂) (hc : sd₂.ReflectsIsomorphisms)
    (data : ProIsomorphismData sd₁ sd₂ F₁ F₂ Lg₁ Lg₂) :
    qcPullback dp₂ ⋙ qcPullback dp₁ ≅ 𝟭 (QC sd₂) :=
  haveI := isIso_qcRoundTripCounit dp₁ dp₂ hc data
  asIso (qcRoundTripCounit dp₁ dp₂ data)

/-- **Two derived pullbacks whose round trips carry canonical maps to the identity which are,
stage by stage, the comparison maps of quasi-coherence are mutually quasi-inverse on
quasi-coherent objects**, over a section datum whose derived sections detect isomorphisms.

This is the shape of the argument of Tag 0GZH over an abstract section datum: over the `i`-th
stage the canonical map of a round trip is the comparison map `RΓ(n(m(i)), -) ⊗^𝐋 B_i ⟶ RΓ(i, -)`,
which quasi-coherence inverts, and the derived sections detect isomorphisms. The tag itself, for
the derived pullback and the quasi-coherent objects built from the inverse systems, is
`DifferentialGradedAlgebra.SystemProHom.isEquivalence_qcPullback`. -/
theorem isEquivalence_qcPullback (dp₁ : DerivedPullbackSectionData msd₁ Lg₁)
    (dp₂ : DerivedPullbackSectionData msd₂ Lg₂) (hc₁ : sd₁.ReflectsIsomorphisms)
    (hc₂ : sd₂.ReflectsIsomorphisms) (data : ProIsomorphismData sd₁ sd₂ F₁ F₂ Lg₁ Lg₂) :
    (qcPullback dp₁).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (qcPullback dp₁) (qcPullback dp₂)
    (qcRoundTripIso dp₂ dp₁ hc₁ data.swap).symm
    (qcRoundTripIso dp₁ dp₂ hc₂ data)).isEquivalence_functor

end ProIsomorphism

end SheafOfModules.DifferentialGradedModule

end

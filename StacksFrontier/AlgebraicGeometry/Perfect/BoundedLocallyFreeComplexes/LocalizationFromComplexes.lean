module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedHomotopy
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedRoof
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.LocalizationCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentative

/-!
# From complexes to `K^b(A)`: the three hypotheses of the localization criterion

Three properties of the canonical functor `K^b(A) ⥤ D_perf(𝒪_X)` — essential surjectivity,
representation of every morphism by a right fraction, and faithfulness up to precomposition by a
quasi-isomorphism — each deduced from the corresponding statement about bounded complexes of
finite locally free modules and `CategoryTheory.DerivedCategory.Q`: the conclusions of
[Stacks, Tag 0F8F], [Stacks, Tag 0F8G] and [Stacks, Tag 0F8H]. Together they give the
equivalence clause of [Stacks, Tag 0F8I]: the canonical functor is a localization at the
quasi-isomorphisms.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.essSurj_perfectComplexFunctor_of_exists_iso`:
  essential surjectivity of the canonical functor from the conclusion of [Stacks, Tag 0F8F].
* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectComplexFunctor_rightFractions_of_exists_roof`:
  the right-fraction representation from the conclusion of [Stacks, Tag 0F8G].
* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectComplexFunctor_faithful_of_exists_homotopy`:
  faithfulness up to precomposition from the conclusion of [Stacks, Tag 0F8H].
* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectComplexFunctor_isLocalization_of_complexes`:
  the three together give `(perfectComplexFunctor X).IsLocalization (quasiIsomorphisms X)`.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
* [Stacks Project, Tag 0F8H](https://stacks.math.columbia.edu/tag/0F8H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
  Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

/-- Transport of a right-fraction representation along isomorphisms identifying one roof with
another. -/
private lemma comp_eq_of_natural_isos {D : Type*} [Category* D]
    {H' A' B' H A B : D} (eH : H' ≅ H) (eA : A' ≅ A) (eB : B' ≅ B)
    (p' : H' ⟶ A') (q' : H' ⟶ B') (p : H ⟶ A) (q : H ⟶ B) (g : A' ⟶ B') [IsIso p]
    (hp : p' ≫ eA.hom = eH.hom ≫ p) (hq : q' ≫ eB.hom = eH.hom ≫ q)
    (hroof : inv p ≫ q = eA.inv ≫ g ≫ eB.hom) :
    p' ≫ g = q' := by
  rw [← cancel_mono eB.hom, hq, Category.assoc, (Iso.inv_comp_eq eA).mp hroof.symm,
    reassoc_of% hp, IsIso.hom_inv_id_assoc]

/-- Transport of an equality of morphisms along isomorphisms. -/
private lemma eq_of_natural_isos {D : Type*} [Category* D] {A' B' A B : D}
    (eA : A' ≅ A) (eB : B' ≅ B) {u' v' : A' ⟶ B'} {u v : A ⟶ B}
    (hu : u' ≫ eB.hom = eA.hom ≫ u) (hv : v' ≫ eB.hom = eA.hom ≫ v) (h : u' = v') :
    u = v := by
  rw [← cancel_epi eA.hom, ← hu, ← hv, h]

section Scheme

attribute [local instance 10000] HasDerivedCategory.standard

/-- The object of `K^b(A)` carried by a bounded complex of finite locally free modules: its
image in the homotopy category, together with the complex as the witness. -/
@[implicit_reducible]
def ofComplex (X : Scheme.{u}) {E : CochainComplex X.Modules ℤ}
    (hE : boundedFiniteLocallyFreeComplex X E) :
    BoundedFiniteLocallyFreeHomotopyCategory X :=
  ⟨(HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj E,
    ObjectProperty.strictMap_obj _ _ hE⟩

/-- The underlying object of `ofComplex X hE` is the image of `E` in the homotopy category. -/
@[simp]
lemma ofComplex_obj (X : Scheme.{u}) {E : CochainComplex X.Modules ℤ}
    (hE : boundedFiniteLocallyFreeComplex X E) :
    (ofComplex X hE).obj =
      (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj E :=
  rfl

/-- The morphism of `K^b(A)` carried by a map of bounded complexes of finite locally free
modules: its homotopy class. -/
@[implicit_reducible]
def mapOfComplex (X : Scheme.{u}) {E F : CochainComplex X.Modules ℤ}
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (f : E ⟶ F) : ofComplex X hE ⟶ ofComplex X hF :=
  ObjectProperty.homMk ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map f)

/-- The underlying morphism of `mapOfComplex X hE hF f` is the homotopy class of `f`. -/
@[simp]
lemma mapOfComplex_hom (X : Scheme.{u}) {E F : CochainComplex X.Modules ℤ}
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (f : E ⟶ F) :
    (mapOfComplex X hE hF f).hom =
      (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map f :=
  rfl

/-- **A quasi-isomorphism of complexes is a morphism of the system `S`.** -/
lemma quasiIsomorphisms_mapOfComplex (X : Scheme.{u}) {E F : CochainComplex X.Modules ℤ}
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (f : E ⟶ F) (hf : QuasiIso f) : quasiIsomorphisms X (mapOfComplex X hE hF f) :=
  (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf

/-- **Essential surjectivity of `K^b(A) ⥤ D_perf(𝒪_X)` from [Stacks, Tag 0F8F].**  The hypothesis
is the conclusion of that tag: every perfect object of `D(𝒪_X)` is isomorphic to the image of a
bounded complex of finite locally free modules. -/
theorem essSurj_perfectComplexFunctor_of_exists_iso (X : Scheme.{u})
    (h0F8F : ∀ (K : DerivedCategory X.Modules), IsPerfect (X := X.toRingedSpace) K →
      ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
        Nonempty (DerivedCategory.Q.obj E ≅ K)) :
    (perfectComplexFunctor X).EssSurj where
  mem_essImage Y := by
    obtain ⟨E, hE, ⟨e⟩⟩ := h0F8F Y.obj Y.property
    exact ⟨ofComplex X hE,
      ⟨ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso X.Modules).app E ≪≫ e)⟩⟩

/-- **Every morphism of `D_perf(𝒪_X)` between images is the image of a right fraction, from
[Stacks, Tag 0F8G].**  The hypothesis is the conclusion of that tag: a morphism of `D(𝒪_X)`
between bounded complexes of finite locally free modules is represented by a roof of such
complexes whose left leg is a quasi-isomorphism. -/
theorem perfectComplexFunctor_rightFractions_of_exists_roof (X : Scheme.{u})
    (h0F8G : ∀ E F : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E →
      boundedFiniteLocallyFreeComplex X F →
      ∀ α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F,
      ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
        boundedFiniteLocallyFreeComplex X G ∧
          inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α) :
    ∀ (a b : BoundedFiniteLocallyFreeHomotopyCategory X)
      (g : (perfectComplexFunctor X).obj a ⟶ (perfectComplexFunctor X).obj b),
      ∃ (c : BoundedFiniteLocallyFreeHomotopyCategory X) (s : c ⟶ a)
        (hs : quasiIsomorphisms X s) (f : c ⟶ b),
        g = (MorphismProperty.RightFraction.mk s hs f).map (perfectComplexFunctor X)
          (quasiIsomorphisms_isInvertedBy_perfectComplexFunctor X) := by
  rintro ⟨-, ⟨E, hE⟩⟩ ⟨-, ⟨F, hF⟩⟩ g
  obtain ⟨G, p, hp, q, hG, hroof⟩ := h0F8G E F hE hF
    (((DerivedCategory.quotientCompQhIso X.Modules).app E).inv ≫ g.hom ≫
      ((DerivedCategory.quotientCompQhIso X.Modules).app F).hom)
  have hinv : IsIso ((perfectComplexFunctor X).map (mapOfComplex X hG hE p)) :=
    quasiIsomorphisms_isInvertedBy_perfectComplexFunctor X _
      (quasiIsomorphisms_mapOfComplex X hG hE p hp)
  refine ⟨ofComplex X hG, mapOfComplex X hG hE p,
    quasiIsomorphisms_mapOfComplex X hG hE p hp, mapOfComplex X hG hF q, ?_⟩
  show g = inv ((perfectComplexFunctor X).map (mapOfComplex X hG hE p)) ≫
    (perfectComplexFunctor X).map (mapOfComplex X hG hF q)
  rw [IsIso.eq_inv_comp]
  exact ObjectProperty.hom_ext _ (comp_eq_of_natural_isos
    ((DerivedCategory.quotientCompQhIso X.Modules).app G)
    ((DerivedCategory.quotientCompQhIso X.Modules).app E)
    ((DerivedCategory.quotientCompQhIso X.Modules).app F)
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map p))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map q))
    (DerivedCategory.Q.map p) (DerivedCategory.Q.map q) g.hom
    (DerivedCategory.quotientCompQhIso_hom_naturality p)
    (DerivedCategory.quotientCompQhIso_hom_naturality q) hroof)

/-- **Two morphisms of `K^b(A)` with the same image are equalized by a quasi-isomorphism, from
[Stacks, Tag 0F8H].**  The hypothesis is the conclusion of that tag: two maps of bounded
complexes of finite locally free modules defining the same morphism of `D(𝒪_X)` become homotopic
after a quasi-isomorphism from such a complex. -/
theorem perfectComplexFunctor_faithful_of_exists_homotopy (X : Scheme.{u})
    (h0F8H : ∀ E F : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E →
      boundedFiniteLocallyFreeComplex X F → ∀ α β : E ⟶ F,
      DerivedCategory.Q.map α = DerivedCategory.Q.map β →
      ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
        boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β))) :
    ∀ ⦃a b : BoundedFiniteLocallyFreeHomotopyCategory X⦄ (u v : a ⟶ b),
      (perfectComplexFunctor X).map u = (perfectComplexFunctor X).map v →
        ∃ (c : BoundedFiniteLocallyFreeHomotopyCategory X) (t : c ⟶ a),
          quasiIsomorphisms X t ∧ t ≫ u = t ≫ v := by
  rintro ⟨-, ⟨E, hE⟩⟩ ⟨-, ⟨F, hF⟩⟩ u v huv
  obtain ⟨α, hα⟩ := (HomotopyCategory.quotient X.Modules
    (ComplexShape.up ℤ)).map_surjective u.hom
  obtain ⟨β, hβ⟩ := (HomotopyCategory.quotient X.Modules
    (ComplexShape.up ℤ)).map_surjective v.hom
  have hQ : DerivedCategory.Q.map α = DerivedCategory.Q.map β := by
    refine eq_of_natural_isos
      ((DerivedCategory.quotientCompQhIso X.Modules).app E)
      ((DerivedCategory.quotientCompQhIso X.Modules).app F)
      (DerivedCategory.quotientCompQhIso_hom_naturality α)
      (DerivedCategory.quotientCompQhIso_hom_naturality β) ?_
    rw [hα, hβ]
    exact Functor.congr_map
      (ObjectProperty.ι (fun K : DerivedCategory X.Modules =>
        IsPerfect (X := X.toRingedSpace) K)) huv
  obtain ⟨G, γ, hγ, hG, ⟨hhom⟩⟩ := h0F8H E F hE hF α β hQ
  have hu : mapOfComplex X hE hF α = u := ObjectProperty.hom_ext _ hα
  have hv : mapOfComplex X hE hF β = v := ObjectProperty.hom_ext _ hβ
  refine ⟨ofComplex X hG, mapOfComplex X hG hE γ,
    quasiIsomorphisms_mapOfComplex X hG hE γ hγ, ?_⟩
  rw [← hu, ← hv]
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, mapOfComplex_hom, ← Functor.map_comp]
  exact HomotopyCategory.eq_of_homotopy _ _ hhom

/-- **The canonical functor presents `D_perf(𝒪_X)` as `S⁻¹K^b(A)`, from the complex-level forms of
[Stacks, Tag 0F8F], [Stacks, Tag 0F8G] and [Stacks, Tag 0F8H].** Given those three statements,
`perfectComplexFunctor X` is a localization at `quasiIsomorphisms X`: the equivalence clause of
[Stacks, Tag 0F8I]. -/
theorem perfectComplexFunctor_isLocalization_of_complexes (X : Scheme.{u})
    (h0F8F : ∀ (K : DerivedCategory X.Modules), IsPerfect (X := X.toRingedSpace) K →
      ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
        Nonempty (DerivedCategory.Q.obj E ≅ K))
    (h0F8G : ∀ E F : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E →
      boundedFiniteLocallyFreeComplex X F →
      ∀ α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F,
      ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
        boundedFiniteLocallyFreeComplex X G ∧
          inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α)
    (h0F8H : ∀ E F : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E →
      boundedFiniteLocallyFreeComplex X F → ∀ α β : E ⟶ F,
      DerivedCategory.Q.map α = DerivedCategory.Q.map β →
      ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
        boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β))) :
    (perfectComplexFunctor X).IsLocalization (quasiIsomorphisms X) :=
  perfectComplexFunctor_isLocalization X
    (essSurj_perfectComplexFunctor_of_exists_iso X h0F8F)
    (perfectComplexFunctor_rightFractions_of_exists_roof X h0F8G)
    (perfectComplexFunctor_faithful_of_exists_homotopy X h0F8H)

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

end

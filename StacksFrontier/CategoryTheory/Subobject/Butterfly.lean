module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksCore.CategoryTheory.Abelian.Subobject

/-!
# The butterfly (Zassenhaus) lemma for subobjects of an abelian category

Let `A' ≤ A` and `B' ≤ B` be subobjects of an object `X` of an abelian category. The butterfly
lemma identifies two subquotients of `X`:
```
((A ⊓ B) ⊔ A') / ((A ⊓ B') ⊔ A')  ≅  ((A ⊓ B) ⊔ B') / ((A' ⊓ B) ⊔ B')
```

The proof has a lattice half and a categorical half.

The lattice half is that the two denominators cut the *same* subobject out of the common numerator
source `A ⊓ B`:
```
((A ⊓ B') ⊔ A') ⊓ (A ⊓ B) = (A ⊓ B') ⊔ (A' ⊓ B) = ((A' ⊓ B) ⊔ B') ⊓ (A ⊓ B)
```
Each equality is one application of the modular law, available because `Subobject X` is a modular
lattice (`StacksCore.CategoryTheory.Abelian.Subobject`).

The categorical half is that both sides are quotients of `A ⊓ B`: the inclusion `A ⊓ B ⟶ N` is
epimorphic onto `N / D` in each case, because `N` is the join of `A ⊓ B` with a subobject of `D`.
Two quotients of a common source whose kernels agree differ by a unique isomorphism, and by the
lattice half the kernels are computed by the same subobject.

## Main results

* `CategoryTheory.Subobject.inf_sup_left_inf_inf`,
  `CategoryTheory.Subobject.inf_sup_right_inf_inf`: the lattice half.
* `CategoryTheory.Subobject.exists_iso_butterfly`: the butterfly isomorphism.

The file opens with refinement lemmas on factoring through subobjects, used here and by the
spectral sequence files: `exists_refinement_of_factors_sup` (a morphism through a join is, after
an epimorphic refinement, a sum of morphisms through each part), `imageSubobject_factors_iff`
(factoring through an image, up to a refinement), and `mk_pullback_arrow_comp` (pulling back along
a monomorphism and pushing forward again is the meet with its image).
-/

@[expose] public section

universe v u

namespace CategoryTheory.Subobject

open Limits Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C]

section Refinements

omit [Abelian C] in
/-- A monomorphism factoring through a subobject has its subobject below it. -/
lemma mk_le_of_factors {X Y : C} {Q : Subobject X} (f : Y ⟶ X) [Mono f]
    (h : Q.Factors f) : Subobject.mk f ≤ Q :=
  Subobject.mk_le_of_comm (Q.factorThru f h) (Q.factorThru_arrow f h)

/-- Subobjects absorb differences of the morphisms they factor. -/
lemma factors_sub {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (hf : P.Factors f)
    (hg : P.Factors g) : P.Factors (f - g) :=
  (Subobject.factors_iff _ _).2 ⟨P.factorThru f hf - P.factorThru g hg, by simp⟩

/-- If a refinement of `f` factors through a subobject, then so does `f`. -/
lemma factors_of_epi_comp {T T' X : C} {Z : Subobject X} (z : T' ⟶ T) [Epi z]
    (f : T ⟶ X) (h : Z.Factors (z ≫ f)) : Z.Factors f := by
  have hz : f ≫ cokernel.π Z.arrow = 0 := by
    rw [← cancel_epi z, comp_zero, ← Category.assoc, ← Z.factorThru_arrow (z ≫ f) h,
      Category.assoc, cokernel.condition, comp_zero]
  rw [← Abelian.monoLift_comp Z.arrow f hz]
  exact Subobject.factors_comp_arrow _

/-- A morphism factors through the image of `f` exactly when it is, up to a refinement, a
morphism through `f`. -/
lemma imageSubobject_factors_iff {X Y T : C} (f : X ⟶ Y) (g : T ⟶ Y) :
    (imageSubobject f).Factors g ↔
      ∃ (T' : C) (z : T' ⟶ T) (_ : Epi z) (x : T' ⟶ X), z ≫ g = x ≫ f := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨T', z, hz, x, fac⟩ := surjective_up_to_refinements_of_epi
      (factorThruImageSubobject f) ((imageSubobject f).factorThru g h)
    exact ⟨T', z, hz, x, by rw [← (imageSubobject f).factorThru_arrow g h, ← Category.assoc, fac,
      Category.assoc, imageSubobject_arrow_comp]⟩
  · rintro ⟨T', z, hz, x, fac⟩
    exact factors_of_epi_comp z g (by rw [fac]; exact imageSubobject_factors_comp_self _ x)

/-- A morphism factoring through a join `x ⊔ y` becomes, after precomposition with an
epimorphism, the sum of a morphism through `x` and a morphism through `y`. -/
lemma exists_refinement_of_factors_sup {T Z : C} {x y : Subobject Z} (f : T ⟶ Z)
    (hf : (x ⊔ y).Factors f) :
    ∃ (T' : C) (z : T' ⟶ T) (_ : Epi z) (β : T' ⟶ (x : C)) (γ : T' ⟶ (y : C)),
      z ≫ f = β ≫ x.arrow + γ ≫ y.arrow := by
  have hIm : x ⊔ y ≤ imageSubobject (biprod.desc x.arrow y.arrow) := by
    refine sup_le (Subobject.le_of_factors ?_) (Subobject.le_of_factors ?_)
    · simpa using imageSubobject_factors_comp_self (biprod.desc x.arrow y.arrow) biprod.inl
    · simpa using imageSubobject_factors_comp_self (biprod.desc x.arrow y.arrow) biprod.inr
  obtain ⟨T', z, hz, w, fac⟩ := (imageSubobject_factors_iff _ f).1
    (Subobject.factors_of_le f hIm hf)
  refine ⟨T', z, hz, w ≫ biprod.fst, w ≫ biprod.snd, ?_⟩
  rw [fac, biprod.desc_eq, comp_add, Category.assoc, Category.assoc]

/-- Pulling a subobject back along a monomorphism and pushing it forward again is the meet with
the image of that monomorphism. -/
lemma mk_pullback_arrow_comp {X Y : C} (f : Y ⟶ X) (G : Subobject X) [Mono f] :
    Subobject.mk (((Subobject.pullback f).obj G).arrow ≫ f) = Subobject.mk f ⊓ G := by
  refine le_antisymm (mk_le_of_factors _ ((Subobject.inf_factors _).2
    ⟨Subobject.factors_of_factors_right _ (Subobject.mk_factors_self f),
      (pullback_factors_iff _ _ _).1 (Subobject.factors_self _)⟩))
    (Subobject.le_of_factors ?_)
  obtain ⟨s, hs⟩ : ∃ s : ((Subobject.mk f ⊓ G : Subobject X) : C) ⟶ Y,
      s ≫ f = (Subobject.mk f ⊓ G).arrow :=
    ⟨(Subobject.mk f).factorThru _ (Subobject.inf_arrow_factors_left _ _)
        ≫ (Subobject.underlyingIso f).hom,
      by rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.factorThru_arrow]⟩
  have hs' : ((Subobject.pullback f).obj G).Factors s := by
    rw [pullback_factors_iff, hs]
    exact Subobject.inf_arrow_factors_right _ _
  rw [← hs, ← ((Subobject.pullback f).obj G).factorThru_arrow _ hs', Category.assoc]
  exact Subobject.factors_of_factors_right _ (Subobject.mk_factors_self _)

/-- The arrow of a subobject below the kernel of `g` composes to zero with `g`. -/
lemma arrow_comp_eq_zero_of_le_kernelSubobject {X Y : C} {g : X ⟶ Y} {P : Subobject X}
    (h : P ≤ kernelSubobject g) : P.arrow ≫ g = 0 := by
  rw [← Subobject.ofLE_arrow h, Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-- A morphism to a subobject which is the image of `f` and which recovers `f` is the canonical
epimorphism onto that image. -/
lemma epi_of_comp_arrow_eq {X Z : C} {f : X ⟶ Z} {P : Subobject Z}
    (hP : P = imageSubobject f) (u : X ⟶ (P : C)) (hu : u ≫ P.arrow = f) : Epi u := by
  subst hP
  rw [show u = factorThruImageSubobject f by
    rw [← cancel_mono (imageSubobject f).arrow, hu, imageSubobject_arrow_comp]]
  infer_instance

end Refinements

section Lattice

variable {X : C} {A A' B B' : Subobject X}

/-- The `A`-side denominator cuts `(A ⊓ B') ⊔ (A' ⊓ B)` out of `A ⊓ B`. One application of the
modular law. -/
lemma inf_sup_left_inf_inf (hA : A' ≤ A) (hB : B' ≤ B) :
    ((A ⊓ B') ⊔ A') ⊓ (A ⊓ B) = (A ⊓ B') ⊔ (A' ⊓ B) := by
  rw [sup_inf_assoc_of_le _ (inf_le_inf_left A hB)]
  congr 1
  rw [← inf_assoc, inf_eq_left.2 hA]

/-- The `B`-side denominator cuts the same `(A ⊓ B') ⊔ (A' ⊓ B)` out of `A ⊓ B`. -/
lemma inf_sup_right_inf_inf (hA : A' ≤ A) (hB : B' ≤ B) :
    ((A' ⊓ B) ⊔ B') ⊓ (A ⊓ B) = (A ⊓ B') ⊔ (A' ⊓ B) := by
  rw [sup_inf_assoc_of_le _ (inf_le_inf_right B hA), sup_comm]
  congr 1
  rw [inf_comm B' (A ⊓ B), inf_assoc, inf_eq_right.2 hB]

/-- The two butterfly denominators agree on the common numerator source `A ⊓ B`. -/
lemma butterfly_denominators_inf_eq (hA : A' ≤ A) (hB : B' ≤ B) :
    ((A ⊓ B') ⊔ A') ⊓ (A ⊓ B) = ((A' ⊓ B) ⊔ B') ⊓ (A ⊓ B) := by
  rw [inf_sup_left_inf_inf hA hB, inf_sup_right_inf_inf hA hB]

end Lattice

section Quotients

variable {Z Z' T : C}

/-- A morphism to `Q` has vanishing class in the quotient `Q / P` exactly when it factors
through `P`. -/
lemma comp_cokernel_π_eq_zero_iff {P Q : Subobject Z} (m : (P : C) ⟶ (Q : C))
    (hm : m ≫ Q.arrow = P.arrow) (u : T ⟶ (Q : C)) :
    u ≫ cokernel.π m = 0 ↔ P.Factors (u ≫ Q.arrow) := by
  have : Mono m := mono_of_mono_fac hm
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · rw [show u ≫ Q.arrow = Abelian.monoLift m u hu ≫ P.arrow by
      rw [← hm, ← Category.assoc, Abelian.monoLift_comp]]
    exact Subobject.factors_comp_arrow _
  · rw [show u = P.factorThru (u ≫ Q.arrow) hu ≫ m by
      rw [← cancel_mono Q.arrow, Category.assoc, hm, P.factorThru_arrow], Category.assoc,
      cokernel.condition, comp_zero]

/-- The quotient `Q / P` is generated by the image of `u : T ⟶ Q`, as soon as `Q` is contained in
that image joined with a subobject `Y` of `P`. -/
lemma epi_comp_cokernel_π {P Q Y : Subobject Z} (m : (P : C) ⟶ (Q : C))
    (hm : m ≫ Q.arrow = P.arrow) (u : T ⟶ (Q : C)) [Mono (u ≫ Q.arrow)]
    (hQ : Q ≤ Subobject.mk (u ≫ Q.arrow) ⊔ Y) (hY : Y ≤ P) : Epi (u ≫ cokernel.π m) := by
  have hmk : Subobject.mk (u ≫ Q.arrow) ≤ Q := mk_le_of_factors _ (Subobject.factors_comp_arrow u)
  have hYQ : Y ≤ Q := hY.trans (Subobject.le_of_comm m hm)
  rw [Preadditive.epi_iff_cancel_zero]
  intro R g hg
  obtain ⟨T', w, hw, β, γ, fac⟩ := exists_refinement_of_factors_sup Q.arrow
    (Subobject.factors_of_le _ hQ (Subobject.factors_self Q))
  have hβ : Subobject.ofLE _ Q hmk ≫ cokernel.π m ≫ g = 0 := by
    refine zero_of_epi_comp (Subobject.underlyingIso (u ≫ Q.arrow)).inv ?_
    rw [← Category.assoc, show (Subobject.underlyingIso (u ≫ Q.arrow)).inv
        ≫ Subobject.ofLE _ Q hmk = u by
      rw [← cancel_mono Q.arrow]; simp, ← Category.assoc]
    exact hg
  have hγ : Subobject.ofLE Y Q hYQ ≫ cokernel.π m ≫ g = 0 := by
    rw [show Subobject.ofLE Y Q hYQ = Subobject.ofLE Y P hY ≫ m by
      rw [← cancel_mono Q.arrow]; simp [hm],
      Category.assoc, ← Category.assoc m, cokernel.condition, zero_comp, comp_zero]
  have hπg : cokernel.π m ≫ g = 0 := by
    refine zero_of_epi_comp w ?_
    rw [show w = β ≫ Subobject.ofLE _ Q hmk + γ ≫ Subobject.ofLE Y Q hYQ by
      rw [← cancel_mono Q.arrow]; simp [fac], add_comp, Category.assoc, Category.assoc,
      hβ, hγ, comp_zero, comp_zero, add_zero]
  exact (cancel_epi (cokernel.π m)).1 (by rw [hπg, comp_zero])

/-- `epi_comp_cokernel_π` for the inclusion of a subobject `R ≤ Q`: the quotient `Q / P` is
generated by `R` as soon as `Q` is contained in `R` joined with a subobject `Y` of `P`. -/
lemma epi_ofLE_comp_cokernel_π {P Q R Y : Subobject Z} (m : (P : C) ⟶ (Q : C))
    (hm : m ≫ Q.arrow = P.arrow) (hRQ : R ≤ Q) (hQ : Q ≤ R ⊔ Y) (hY : Y ≤ P) :
    Epi (Subobject.ofLE R Q hRQ ≫ cokernel.π m) :=
  epi_comp_cokernel_π m hm _ (hQ.trans (sup_le_sup_right
    (Subobject.le_mk_of_comm (𝟙 _) (by rw [Category.id_comp, Subobject.ofLE_arrow])) _)) hY

/-- Two epimorphisms out of a common source, each vanishing on the other's kernel, differ by an
isomorphism of their targets. -/
lemma exists_iso_of_epi_of_kernel {X Y : C} (u : T ⟶ X) (v : T ⟶ Y) [Epi u] [Epi v]
    (h₁ : kernel.ι u ≫ v = 0) (h₂ : kernel.ι v ≫ u = 0) : ∃ e : X ≅ Y, u ≫ e.hom = v := by
  refine ⟨⟨Abelian.epiDesc u v h₁, Abelian.epiDesc v u h₂, ?_, ?_⟩, Abelian.comp_epiDesc _ _ _⟩
  · rw [← cancel_epi u]; simp
  · rw [← cancel_epi v]; simp

/-- Two quotients `Q / P` and `Q' / P'` of a common source, by way of morphisms `u : T ⟶ Q` and
`v : T ⟶ Q'` generating them: if a morphism to `T` lands in `P` through `u` exactly when it lands
in `P'` through `v`, the two quotient maps differ by an isomorphism `cokernel m ≅ cokernel m'`. -/
lemma exists_iso_cokernel_of_factors_iff {P Q : Subobject Z} {P' Q' : Subobject Z'}
    (m : (P : C) ⟶ (Q : C)) (hm : m ≫ Q.arrow = P.arrow) (m' : (P' : C) ⟶ (Q' : C))
    (hm' : m' ≫ Q'.arrow = P'.arrow) (u : T ⟶ (Q : C)) (v : T ⟶ (Q' : C))
    [Epi (u ≫ cokernel.π m)] [Epi (v ≫ cokernel.π m')]
    (h : ∀ {T' : C} (g : T' ⟶ T),
      P.Factors (g ≫ u ≫ Q.arrow) ↔ P'.Factors (g ≫ v ≫ Q'.arrow)) :
    ∃ e : cokernel m ≅ cokernel m', u ≫ cokernel.π m ≫ e.hom = v ≫ cokernel.π m' := by
  have key : ∀ {T' : C} (k : T' ⟶ T),
      k ≫ u ≫ cokernel.π m = 0 ↔ k ≫ v ≫ cokernel.π m' = 0 := by
    intro T' k
    rw [← Category.assoc, comp_cokernel_π_eq_zero_iff m hm, ← Category.assoc,
      comp_cokernel_π_eq_zero_iff m' hm']
    simpa only [Category.assoc] using h k
  obtain ⟨e, he⟩ := exists_iso_of_epi_of_kernel (u ≫ cokernel.π m) (v ≫ cokernel.π m')
    ((key _).1 (kernel.condition _)) ((key _).2 (kernel.condition _))
  exact ⟨e, by rwa [← Category.assoc]⟩

end Quotients

/-- **The butterfly (Zassenhaus) lemma.** For subobjects `A' ≤ A` and `B' ≤ B` of an object `X` of
an abelian category, the two subquotients
`((A ⊓ B) ⊔ A') / ((A ⊓ B') ⊔ A')` and `((A ⊓ B) ⊔ B') / ((A' ⊓ B) ⊔ B')` are isomorphic,
compatibly with the two projections from `A ⊓ B`. -/
lemma exists_iso_butterfly {X : C} {A A' B B' : Subobject X} (hA : A' ≤ A) (hB : B' ≤ B)
    (j₁ : (((A ⊓ B') ⊔ A' : Subobject X) : C) ⟶ (((A ⊓ B) ⊔ A' : Subobject X) : C))
    (hj₁ : j₁ ≫ ((A ⊓ B) ⊔ A' : Subobject X).arrow = ((A ⊓ B') ⊔ A' : Subobject X).arrow)
    (j₂ : (((A' ⊓ B) ⊔ B' : Subobject X) : C) ⟶ (((A ⊓ B) ⊔ B' : Subobject X) : C))
    (hj₂ : j₂ ≫ ((A ⊓ B) ⊔ B' : Subobject X).arrow = ((A' ⊓ B) ⊔ B' : Subobject X).arrow) :
    ∃ e : cokernel j₁ ≅ cokernel j₂,
      Subobject.ofLE _ _ le_sup_left ≫ cokernel.π j₁ ≫ e.hom
        = Subobject.ofLE (A ⊓ B) _ le_sup_left ≫ cokernel.π j₂ := by
  have hepi₁ : Epi (Subobject.ofLE (A ⊓ B) ((A ⊓ B) ⊔ A') le_sup_left ≫ cokernel.π j₁) :=
    epi_ofLE_comp_cokernel_π j₁ hj₁ le_sup_left le_rfl le_sup_right
  have hepi₂ : Epi (Subobject.ofLE (A ⊓ B) ((A ⊓ B) ⊔ B') le_sup_left ≫ cokernel.π j₂) :=
    epi_ofLE_comp_cokernel_π j₂ hj₂ le_sup_left le_rfl le_sup_right
  refine exists_iso_cokernel_of_factors_iff j₁ hj₁ j₂ hj₂ _ _ (fun {T'} g => ?_)
  simp only [Subobject.ofLE_arrow]
  have hg := Subobject.factors_comp_arrow g
  have key : ∀ P : Subobject X, P.Factors (g ≫ (A ⊓ B).arrow) ↔
      (P ⊓ (A ⊓ B)).Factors (g ≫ (A ⊓ B).arrow) := fun P => by
    rw [Subobject.inf_factors, and_iff_left hg]
  rw [key ((A ⊓ B') ⊔ A'), butterfly_denominators_inf_eq hA hB, ← key]

/-- Two subobjects whose inclusion has vanishing cokernel are equal: the inclusion is then an
epimorphism, hence an isomorphism, so the larger subobject factors through the smaller. -/
public lemma eq_of_isZero_cokernel_ofLE {X : C} {A B : Subobject X} (h : A ≤ B)
    (hz : Limits.IsZero (Limits.cokernel (Subobject.ofLE A B h))) : A = B := by
  have hepi : Epi (Subobject.ofLE A B h) := Preadditive.epi_of_isZero_cokernel _ hz
  have : IsIso (Subobject.ofLE A B h) := isIso_of_mono_of_epi _
  exact le_antisymm h (Subobject.le_of_comm (inv (Subobject.ofLE A B h)) (by
    rw [← Subobject.ofLE_arrow h, IsIso.inv_hom_id_assoc]))

end CategoryTheory.Subobject

end

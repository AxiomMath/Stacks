module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Approximation of a derived object in degrees above a bound

Fix an abelian category `C` with a derived category. A morphism `α : P ⟶ E` in `D(C)`
*approximates `E` from `m`* when `H^i(α)` is an isomorphism for `i > m` and an epimorphism
for `i = m`. This is the cohomological condition in the definition of approximation by
perfect complexes.

## Main definitions

* `DerivedCategory.ApproximatesFrom`: the condition on `α` just described.

## Main results

* `DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃`: for a distinguished triangle
  whose first morphism is `α`, the condition holds exactly when the third vertex has
  vanishing cohomology in all degrees `≥ m`. This is what makes the condition composable.
* `DerivedCategory.isZero_homology_obj₃_of_epi_top`: if the first two vertices of a
  distinguished triangle have vanishing cohomology above `t` and the first morphism is an
  epimorphism on `H^t`, the third vertex has vanishing cohomology in all degrees `≥ t`.
* `DerivedCategory.exists_approximatesFrom_of_triangle`: given a distinguished triangle
  `P ⟶ E ⟶ E' ⟶ P⟦1⟧` and a morphism `P' ⟶ E'` approximating `E'` from `m`, there is an
  object `P''` fitting into a distinguished triangle `P' ⟶ P⟦1⟧ ⟶ P''⟦1⟧ ⟶ P'⟦1⟧`
  together with a morphism `P'' ⟶ E` approximating `E` from `m`.

## Implementation notes

The reformulation through the third vertex replaces a five-lemma argument on two long exact
sequences by a single application of the octahedron axiom: the approximating object for `E`
is produced as a shift of the cone of `P' ⟶ P⟦1⟧`, and the octahedron identifies the cone of
the new approximation with the cone of the old one, so no cohomology bookkeeping survives
into the induction step.

Both directions of the reformulation use only the four `Epi`/`Mono` criteria of
`DerivedCategory.HomologySequence`, so the whole file is stated for an arbitrary abelian
category and carries no sheaf-theoretic hypotheses.

## References

* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- `α : P ⟶ E` approximates `E` from `m`: the induced map on `H^i` is an isomorphism for
`i > m` and an epimorphism for `i = m`. -/
def ApproximatesFrom {P E : DerivedCategory C} (α : P ⟶ E) (m : ℤ) : Prop :=
  (∀ i : ℤ, m < i → IsIso ((homologyFunctor C i).map α)) ∧
    Epi ((homologyFunctor C m).map α)

namespace HomologySequence

omit [HasDerivedCategory.{w} C] in
/-- An object receiving an epimorphism which is the zero morphism is zero. -/
theorem isZero_of_epi_zero {A B : C} (h : Epi (0 : A ⟶ B)) : IsZero B := by
  rw [IsZero.iff_id_eq_zero]
  exact h.left_cancellation _ _ (by simp)

/-- If the connecting map `H^i(T.obj₃) ⟶ H^{i+1}(T.obj₁)` vanishes and `H^i(T.mor₁)` is an
epimorphism, then `H^i(T.obj₃)` is zero. -/
private theorem isZero_homology_obj₃_of_δ_eq_zero_of_epi (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (i : ℤ) (hδ : HomologySequence.δ T i (i + 1) rfl = 0)
    (hmor₁ : Epi ((homologyFunctor C i).map T.mor₁)) :
    IsZero ((homologyFunctor C i).obj T.obj₃) :=
  isZero_of_epi_zero (C := C)
    ((HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hmor₁ ▸
      (HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl).2 hδ)

/-- **The cone of a top-degree surjection.** If the first two vertices of a distinguished
triangle have vanishing cohomology in degrees `> t`, and the first morphism is surjective on
`H^t`, then the third vertex has vanishing cohomology in every degree `≥ t`. -/
theorem isZero_homology_obj₃_of_epi_top (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (t : ℤ)
    (h₁ : ∀ i : ℤ, t < i → IsZero ((homologyFunctor C i).obj T.obj₁))
    (h₂ : ∀ i : ℤ, t < i → IsZero ((homologyFunctor C i).obj T.obj₂))
    (hepi : Epi ((homologyFunctor C t).map T.mor₁)) :
    ∀ i : ℤ, t ≤ i → IsZero ((homologyFunctor C i).obj T.obj₃) := by
  intro i hi
  refine isZero_homology_obj₃_of_δ_eq_zero_of_epi T hT i ((h₁ (i + 1) (by lia)).eq_of_tgt _ _) ?_
  rcases eq_or_lt_of_le hi with h | h
  · exact h ▸ hepi
  · exact ⟨fun g₁ g₂ _ => (h₂ i h).eq_of_src g₁ g₂⟩

end HomologySequence

/-- **Approximation read off the third vertex.** For a distinguished triangle
`P ⟶ E ⟶ Q ⟶ P⟦1⟧`, the first morphism approximates `E` from `m` exactly when `Q` has
vanishing cohomology in every degree `≥ m`. -/
theorem approximatesFrom_iff_isZero_homology_obj₃ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (m : ℤ) :
    ApproximatesFrom T.mor₁ m ↔
      ∀ i : ℤ, m ≤ i → IsZero ((homologyFunctor C i).obj T.obj₃) := by
  constructor
  · rintro ⟨hiso, hepi⟩ i hi
    have hmono : Mono ((homologyFunctor C (i + 1)).map T.mor₁) := by
      have := hiso (i + 1) (by lia)
      infer_instance
    refine HomologySequence.isZero_homology_obj₃_of_δ_eq_zero_of_epi T hT i
      ((HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1) rfl).1 hmono) ?_
    rcases eq_or_lt_of_le hi with h | h
    · exact h ▸ hepi
    · have := hiso i h
      infer_instance
  · intro hvan
    refine ⟨fun i hi => ?_, ?_⟩
    · have hepi : Epi ((homologyFunctor C i).map T.mor₁) :=
        (HomologySequence.epi_homologyMap_mor₁_iff T hT i).2
          ((hvan i hi.le).eq_of_tgt _ _)
      have hmono : Mono ((homologyFunctor C i).map T.mor₁) :=
        (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by lia)).2
          ((hvan (i - 1) (by lia)).eq_of_src _ _)
      exact isIso_of_mono_of_epi _
    · exact (HomologySequence.epi_homologyMap_mor₁_iff T hT m).2
        ((hvan m le_rfl).eq_of_tgt _ _)

/-- The cohomology functors of the derived category form a shift sequence; this is the
resulting comparison `H^i(X⟦1⟧) ≅ H^{i+1}(X)`. -/
noncomputable def homologyShiftIso (i : ℤ) :
    shiftFunctor (DerivedCategory C) (1 : ℤ) ⋙ homologyFunctor C i ≅
      homologyFunctor C (i + 1) :=
  (homologyFunctor C 0).shiftIso 1 i (i + 1) (by lia)

/-- `H^i(X⟦1⟧)` is zero if and only if `H^{i+1}(X)` is zero. -/
theorem isZero_homology_shift_iff (X : DerivedCategory C) (i : ℤ) :
    IsZero ((homologyFunctor C i).obj (X⟦(1 : ℤ)⟧)) ↔
      IsZero ((homologyFunctor C (i + 1)).obj X) :=
  ⟨fun h => h.of_iso ((homologyShiftIso i).app X).symm,
    fun h => h.of_iso ((homologyShiftIso i).app X)⟩

/-- Shifting a morphism shifts the degree from which it approximates. -/
theorem approximatesFrom_shift_one_iff {P E : DerivedCategory C} (f : P ⟶ E) (m : ℤ) :
    ApproximatesFrom (f⟦(1 : ℤ)⟧') m ↔ ApproximatesFrom f (m + 1) := by
  have key : ∀ i : ℤ,
      ((IsIso ((homologyFunctor C i).map (f⟦(1 : ℤ)⟧')) ↔
          IsIso ((homologyFunctor C (i + 1)).map f)) ∧
        (Epi ((homologyFunctor C i).map (f⟦(1 : ℤ)⟧')) ↔
          Epi ((homologyFunctor C (i + 1)).map f))) := by
    intro i
    have hsq := (homologyShiftIso (C := C) i).hom.naturality f
    set u := (homologyShiftIso (C := C) i).hom.app P with hu
    set v := (homologyShiftIso (C := C) i).hom.app E with hv
    have hiu : IsIso u := by rw [hu]; infer_instance
    have hiv : IsIso v := by rw [hv]; infer_instance
    have hfac : (homologyFunctor C i).map (f⟦(1 : ℤ)⟧') =
        u ≫ (homologyFunctor C (i + 1)).map f ≫ inv v := by
      rw [← Category.assoc, ← hsq]
      simp
    refine ⟨?_, ?_⟩
    · rw [hfac]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h' : IsIso ((homologyFunctor C (i + 1)).map f ≫ inv v) :=
          IsIso.of_isIso_comp_left u _
        exact IsIso.of_isIso_comp_right _ (inv v)
      · infer_instance
    · rw [hfac]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h' : Epi ((homologyFunctor C (i + 1)).map f ≫ inv v) := epi_of_epi u _
        have := epi_comp ((homologyFunctor C (i + 1)).map f ≫ inv v) v
        simpa using this
      · infer_instance
  constructor
  · rintro ⟨hiso, hepi⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hiso (i - 1) (by lia)
      have h2 := ((key (i - 1)).1).1 this
      rwa [show i - 1 + 1 = i by lia] at h2
    · exact ((key m).2).1 hepi
  · rintro ⟨hiso, hepi⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · exact ((key i).1).2 (hiso (i + 1) (by lia))
    · exact ((key m).2).2 hepi

/-- **The induction step of Tag 08EQ.** Let `P ⟶ E ⟶ E' ⟶ P⟦1⟧` be a distinguished triangle
and let `α : P' ⟶ E'` approximate `E'` from `m`. Then the object `P''` completing
`P ⟶ P'' ⟶ P' ⟶ P⟦1⟧` with third morphism `α ≫ (E' ⟶ P⟦1⟧)` carries a morphism to `E`
approximating `E` from `m`.

The octahedron axiom applied to `P' ⟶ E' ⟶ P⟦1⟧` identifies the cone of the new
approximation with the cone of `α`, which is what makes the conclusion hold with the same
bound `m`. -/
theorem exists_approximatesFrom_of_triangle [IsTriangulated (DerivedCategory C)]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (m : ℤ)
    {P' : DerivedCategory C} (α : P' ⟶ T.obj₃) (hα : ApproximatesFrom α m) :
    ∃ (P'' : DerivedCategory C) (u : T.obj₁ ⟶ P'') (v : P'' ⟶ P'),
      Triangle.mk u v (α ≫ T.mor₃) ∈ distTriang (DerivedCategory C) ∧
        ∃ φ : P'' ⟶ T.obj₂, ApproximatesFrom φ m := by
  obtain ⟨Cα, v₁₂, w₁₂, h₁₂⟩ := distinguished_cocone_triangle α
  obtain ⟨P'', u, v, h₁₃'⟩ := distinguished_cocone_triangle₂ (α ≫ T.mor₃)
  refine ⟨P'', u, v, h₁₃', ?_⟩
  have h₂₃ : Triangle.mk T.mor₃ (-T.mor₁⟦(1 : ℤ)⟧') (-T.mor₂⟦(1 : ℤ)⟧') ∈
      distTriang (DerivedCategory C) := rot_of_distTriang _ (rot_of_distTriang _ hT)
  have h₁₃ : Triangle.mk (α ≫ T.mor₃) (-u⟦(1 : ℤ)⟧') (-v⟦(1 : ℤ)⟧') ∈
      distTriang (DerivedCategory C) := rot_of_distTriang _ (rot_of_distTriang _ h₁₃')
  have oct := someOctahedron (u₁₂ := α) (u₂₃ := T.mor₃) rfl h₁₂ h₂₃ h₁₃
  have hrot : Triangle.mk oct.m₃ ((-T.mor₂⟦(1 : ℤ)⟧') ≫ v₁₂⟦(1 : ℤ)⟧')
      (-oct.m₁⟦(1 : ℤ)⟧') ∈ distTriang (DerivedCategory C) :=
    rot_of_distTriang _ oct.mem
  have hCα : ∀ i : ℤ, m ≤ i → IsZero ((homologyFunctor C i).obj Cα) :=
    (approximatesFrom_iff_isZero_homology_obj₃ (Triangle.mk α v₁₂ w₁₂) h₁₂ m).1 hα
  have hshift : ApproximatesFrom oct.m₃ (m - 1) := by
    refine (approximatesFrom_iff_isZero_homology_obj₃ _ hrot (m - 1)).2 ?_
    intro i hi
    exact (isZero_homology_shift_iff Cα i).2 (hCα (i + 1) (by lia))
  refine ⟨(shiftFunctor (DerivedCategory C) (1 : ℤ)).preimage oct.m₃, ?_⟩
  have hmap : ((shiftFunctor (DerivedCategory C) (1 : ℤ)).preimage oct.m₃)⟦(1 : ℤ)⟧' =
      oct.m₃ := Functor.map_preimage _ _
  have hpre : ApproximatesFrom
      (((shiftFunctor (DerivedCategory C) (1 : ℤ)).preimage oct.m₃)⟦(1 : ℤ)⟧') (m - 1) := by
    rw [hmap]; exact hshift
  have := (approximatesFrom_shift_one_iff _ (m - 1)).1 hpre
  rwa [show m - 1 + 1 = m by lia] at this

/-- Precomposing with an isomorphism does not change whether a morphism approximates from
`m`. -/
theorem approximatesFrom_iso_comp_iff {P P' E : DerivedCategory C} (e : P' ≅ P) (f : P ⟶ E)
    (m : ℤ) : ApproximatesFrom (e.hom ≫ f) m ↔ ApproximatesFrom f m := by
  have h : ∀ i : ℤ, (homologyFunctor C i).map (e.hom ≫ f) =
      ((homologyFunctor C i).mapIso e).hom ≫ (homologyFunctor C i).map f := fun i =>
    (homologyFunctor C i).map_comp _ _
  constructor
  · rintro ⟨hiso, hepi⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hiso i hi
      rw [h] at this
      exact IsIso.of_isIso_comp_left ((homologyFunctor C i).mapIso e).hom
        ((homologyFunctor C i).map f)
    · rw [h] at hepi
      exact epi_of_epi ((homologyFunctor C m).mapIso e).hom ((homologyFunctor C m).map f)
  · rintro ⟨hiso, hepi⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hiso i hi
      rw [h]; infer_instance
    · rw [h]; infer_instance

/-- Postcomposing with an isomorphism does not change whether a morphism approximates from
`m`. -/
theorem approximatesFrom_comp_iso_iff {P E E' : DerivedCategory C} (f : P ⟶ E) (e : E ≅ E')
    (m : ℤ) : ApproximatesFrom (f ≫ e.hom) m ↔ ApproximatesFrom f m := by
  have h : ∀ i : ℤ, (homologyFunctor C i).map (f ≫ e.hom) =
      (homologyFunctor C i).map f ≫ ((homologyFunctor C i).mapIso e).hom := fun i =>
    (homologyFunctor C i).map_comp _ _
  constructor
  · rintro ⟨hiso, hepi⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hiso i hi
      rw [h] at this
      exact IsIso.of_isIso_comp_right ((homologyFunctor C i).map f)
        ((homologyFunctor C i).mapIso e).hom
    · rw [h] at hepi
      have := epi_comp ((homologyFunctor C m).map f ≫ ((homologyFunctor C m).mapIso e).hom)
        ((homologyFunctor C m).mapIso e).inv
      simpa using this
  · rintro ⟨hiso, hepi⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hiso i hi
      rw [h]; infer_instance
    · rw [h]; infer_instance

/-- A morphism between objects whose cohomology vanishes in all degrees `≥ m` approximates
from `m`, there being nothing to check. -/
theorem approximatesFrom_of_isZero {P E : DerivedCategory C} (α : P ⟶ E) (m : ℤ)
    (hP : ∀ i : ℤ, m ≤ i → IsZero ((homologyFunctor C i).obj P))
    (hE : ∀ i : ℤ, m ≤ i → IsZero ((homologyFunctor C i).obj E)) :
    ApproximatesFrom α m :=
  ⟨fun i hi => ⟨⟨0, (hP i hi.le).eq_of_src _ _, (hE i hi.le).eq_of_tgt _ _⟩⟩,
    ⟨fun g₁ g₂ _ => (hE m le_rfl).eq_of_src g₁ g₂⟩⟩

/-- **The induction of Tag 08EQ.** Let `Q` single out a class of objects and `R` the class of
admissible approximating objects. Suppose

* `R` is stable in the middle of a distinguished triangle whose outer vertices are in `R`;
* `Q` passes to the third vertex of a distinguished triangle whose first vertex is in `R`;
* for every `E` in `Q` whose cohomology vanishes above some `t ≥ m` there is an object of `R`,
  with cohomology vanishing above `t` as well, mapping to `E` surjectively on `H^t`.

Then every `E` in `Q` with cohomology vanishing above some degree receives a morphism from an
object of `R` approximating it from `m`.

This is the induction on the top nonvanishing cohomological degree in the source, with the
one-step construction abstracted into `hstep`. The base case is `hstep` at degree `m` itself:
once the cohomology of `E` vanishes in all degrees `≥ m`, nothing is left to approximate. -/
theorem exists_approximatesFrom_of_step [IsTriangulated (DerivedCategory C)]
    (Q R : DerivedCategory C → Prop) (m : ℤ)
    (hR : ∀ (A B D : DerivedCategory C) (u : A ⟶ B) (v : B ⟶ D) (w : D ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk u v w ∈ distTriang (DerivedCategory C) → R A → R D → R B)
    (hQ : ∀ T : Triangle (DerivedCategory C), T ∈ distTriang (DerivedCategory C) →
      R T.obj₁ → Q T.obj₂ → Q T.obj₃)
    (hstep : ∀ (E : DerivedCategory C), Q E → ∀ t : ℤ, m ≤ t →
      (∀ i : ℤ, t < i → IsZero ((homologyFunctor C i).obj E)) →
      ∃ P : DerivedCategory C, R P ∧
        (∀ i : ℤ, t < i → IsZero ((homologyFunctor C i).obj P)) ∧
        ∃ α : P ⟶ E, Epi ((homologyFunctor C t).map α))
    (E : DerivedCategory C) (hE : Q E) (t : ℤ)
    (hvan : ∀ i : ℤ, t < i → IsZero ((homologyFunctor C i).obj E)) :
    ∃ P : DerivedCategory C, R P ∧ ∃ α : P ⟶ E, ApproximatesFrom α m := by
  suffices H : ∀ n : ℕ, ∀ s : ℤ, s < m + n → ∀ F : DerivedCategory C, Q F →
      (∀ i : ℤ, s < i → IsZero ((homologyFunctor C i).obj F)) →
      ∃ P : DerivedCategory C, R P ∧ ∃ α : P ⟶ F, ApproximatesFrom α m by
    refine H (t + 1 - m).toNat t ?_ E hE hvan
    have : (t + 1 - m : ℤ) ≤ ((t + 1 - m).toNat : ℤ) := Int.self_le_toNat _
    lia
  intro n
  induction n with
  | zero =>
    intro s hs F hF hvanF
    obtain ⟨P, hP, hPvan, α, hαepi⟩ := hstep F hF m le_rfl (fun i hi => hvanF i (by lia))
    refine ⟨P, hP, α, fun i hi => ?_, hαepi⟩
    exact ⟨⟨0, (hPvan i hi).eq_of_src _ _, (hvanF i (by lia)).eq_of_tgt _ _⟩⟩
  | succ n ih =>
    intro s hs F hF hvanF
    rcases lt_or_ge s (m + n) with hlt | hge
    · exact ih s (by exact_mod_cast hlt) F hF hvanF
    have hsm : m ≤ s := by
      have : (0 : ℤ) ≤ n := Int.natCast_nonneg n
      lia
    obtain ⟨P, hP, hPvan, α, hαepi⟩ := hstep F hF s hsm hvanF
    obtain ⟨F', g, h, hTri⟩ := distinguished_cocone_triangle α
    have hF'van : ∀ i : ℤ, s ≤ i → IsZero ((homologyFunctor C i).obj F') :=
      HomologySequence.isZero_homology_obj₃_of_epi_top (Triangle.mk α g h) hTri s
        hPvan hvanF hαepi
    have hQF' : Q F' := hQ (Triangle.mk α g h) hTri hP hF
    obtain ⟨P', hP', α', hα'⟩ := ih (s - 1) (by push_cast at hs ⊢; lia) F' hQF'
      (fun i hi => hF'van i (by lia))
    obtain ⟨P'', u, v, hTri'', φ, hφ⟩ :=
      exists_approximatesFrom_of_triangle (Triangle.mk α g h) hTri m α' hα'
    exact ⟨P'', hR _ _ _ u v _ hTri'' hP hP', φ, hφ⟩

end DerivedCategory

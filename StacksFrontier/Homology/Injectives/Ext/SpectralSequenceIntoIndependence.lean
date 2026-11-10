module

public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceIntoFunctoriality
public import StacksFrontier.Homology.Injectives.FilteredComplex.MappingCone

/-!
# Independence of the Ext spectral sequence of the chosen representative

Let `A` be a Grothendieck abelian category, let `M` be an object of `D(A)` and let `K^•` be a
filtered complex of `A`.  The spectral sequence of Tag 0G1X is built out of a *chosen* filtered
K-injective resolution `j : K^• ⟶ J^•` (Tag 0BKI), so it is not functorial on the nose, and a
morphism `K^• ⟶ L^•` of filtered complexes does not induce one of the chosen resolutions.  This
file supplies the missing comparison and deduces the independence assertion of Tag 0G1Y.

The comparison is obtained not by lifting `K^• ⟶ L^•` to the chosen resolutions — which would
need a filtered lifting theorem for filtered K-injective complexes — but by mapping both chosen
resolutions into one filtered complex.  Given a morphism `f : K^• ⟶ L^•` which is a
quasi-isomorphism on every filtration step, write `j_K : K^• ⟶ J_K^•` and `j_L : L^• ⟶ J_L^•` for
the chosen resolutions and form the mapping cone `D^•` of
`(j_K, f ≫ j_L) : K^• ⟶ J_K^• ⊕ J_L^•`.  Both `J_K^• ⟶ D^•` and `J_L^• ⟶ D^•` are then
quasi-isomorphisms on every filtration step: in the derived category of `A` the triangle attached
to the cone of a morphism into a direct sum whose first component is invertible splits, and the
inclusion of a complementary summand becomes an isomorphism onto the cone.  Composing with the
chosen resolution of `D^•` gives morphisms of chosen resolutions
`J_K^• ⟶ J_D^• ⟵ J_L^•`, each a quasi-isomorphism on every filtration step, and
`Stacks.Injectives.nonempty_extSpectralSequenceInto_iso_of_quasiIso` turns each into an
isomorphism of Ext spectral sequences.

## Main results

* `Stacks.Injectives.isIso_comp_mor₂_of_retraction`: a distinguished triangle whose first morphism
  is a split monomorphism splits, so the inclusion of a complement of the image of that morphism
  becomes an isomorphism onto the third vertex.
* `Stacks.Injectives.quasiIso_comp_mappingCone_inr`: the resulting criterion for a morphism into a
  mapping cone to be a quasi-isomorphism.
* `Stacks.Injectives.quasiIso_natTrans_app_resolutionComparison_fst` and
  `Stacks.Injectives.quasiIso_natTrans_app_resolutionComparison_snd`: **the comparison of chosen
  filtered K-injective resolutions**, as two morphisms of chosen resolutions into the chosen
  resolution of the filtered mapping cone.
* `Stacks.Injectives.nonempty_extSpectralSequenceInto_iso_of_quasiIso_filtered`: a morphism of
  filtered complexes which is a quasi-isomorphism on every filtration step induces an isomorphism
  of the Ext spectral sequences of Tag 0G1X.
* `Stacks.Injectives.nonempty_canonicalExtSpectralSequenceInto_iso`: **Tag 0G1Y, representative
  independence.** The Ext spectral sequence of the canonical truncation filtration does not depend
  on the complex chosen to represent an object of `D(A)`.

## Implementation notes

The splitting lemma is stated for a general pretriangulated category and for the three morphisms
of the triangle rather than for a bundled triangle, so that it applies to the image of
`CochainComplex.mappingCone.triangle` under `DerivedCategory.Q` without unfolding that image.  Its
hypotheses are exactly the data of a retraction `r` of the first morphism, a complement
`c : W ⟶ Y`, `c' : Y ⟶ W` of its image inside the second vertex, and the identity
`r ≫ ι + c' ≫ c = 𝟙`; no compatibility between `ι` and the first morphism is required, which is
what makes the direct-sum instance immediate from `biprod.total`.

The filtered mapping cone is
`Stacks.Injectives.filteredMappingCone`; its `p`-th filtration step is the mapping cone of the
`p`-th filtration step of the morphism, so the two legs are, on each filtration step, exactly the
morphisms treated by `Stacks.Injectives.quasiIso_comp_mappingCone_inr`.

## References

* [Stacks Project, Tag 0G1Y](https://stacks.math.columbia.edu/tag/0G1Y)
* [Stacks Project, Tag 0G1X](https://stacks.math.columbia.edu/tag/0G1X)
* [Stacks Project, Tag 0BKI](https://stacks.math.columbia.edu/tag/0BKI)
-/

@[expose] public noncomputable section

universe w' w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.Injectives

section Splitting

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A distinguished triangle whose first morphism is a split monomorphism splits.**  If
`X --w--> Y --g--> Z --δ--> X⟦1⟧` is distinguished, `r` is a retraction of `w`, and
`c : W ⟶ Y`, `c' : Y ⟶ W` exhibit `W` as a complement of the image of `r` inside `Y` in the sense
that `c ≫ c' = 𝟙`, `c ≫ r = 0` and `r ≫ ι + c' ≫ c = 𝟙` for some `ι : X ⟶ Y`, then `c ≫ g` is an
isomorphism. -/
theorem isIso_comp_mor₂_of_retraction {X Y Z W : D} (w : X ⟶ Y) (g : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk w g δ ∈ distTriang D)
    (r : Y ⟶ X) (ι : X ⟶ Y) (c : W ⟶ Y) (c' : Y ⟶ W)
    (hwr : w ≫ r = 𝟙 X) (hcc' : c ≫ c' = 𝟙 W) (hcr : c ≫ r = 0)
    (htotal : r ≫ ι + c' ≫ c = 𝟙 Y) :
    IsIso (c ≫ g) := by
  have h12 : w ≫ g = 0 := comp_distTriang_mor_zero₁₂ (Triangle.mk w g δ) hT
  have hδ : δ = 0 := by
    have h : δ ≫ w⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ (Triangle.mk w g δ) hT
    have h' : δ ≫ w⟦(1 : ℤ)⟧' ≫ r⟦(1 : ℤ)⟧' = 0 := by
      rw [← Category.assoc, h, zero_comp]
    rwa [← CategoryTheory.Functor.map_comp, hwr, CategoryTheory.Functor.map_id,
      Category.comp_id] at h'
  obtain ⟨s, hsg, hsr⟩ : ∃ s : Z ⟶ Y, s ≫ g = 𝟙 Z ∧ s ≫ r = 0 := by
    obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Z ⟶ Y, 𝟙 Z = s₀ ≫ g :=
      Triangle.coyoneda_exact₃ (Triangle.mk w g δ) hT (𝟙 Z)
        (by rw [show (Triangle.mk w g δ).mor₃ = δ from rfl, hδ, comp_zero])
    refine ⟨s₀ - s₀ ≫ r ≫ w, ?_, ?_⟩
    · have h2 : (s₀ ≫ r ≫ w) ≫ g = 0 := by
        rw [Category.assoc, Category.assoc, h12, comp_zero, comp_zero]
      rw [Preadditive.sub_comp, h2, sub_zero, ← hs₀]
    · have h2 : (s₀ ≫ r ≫ w) ≫ r = s₀ ≫ r := by
        rw [Category.assoc, Category.assoc, hwr, Category.comp_id]
      rw [Preadditive.sub_comp, h2, sub_self]
  have he₁ : (r ≫ w) ≫ r ≫ w = r ≫ w := by
    rw [Category.assoc, ← Category.assoc w r, hwr, Category.id_comp]
  have he₂ : (g ≫ s) ≫ g ≫ s = g ≫ s := by
    rw [Category.assoc, ← Category.assoc s g, hsg, Category.id_comp]
  have he₁₂ : (r ≫ w) ≫ g ≫ s = 0 := by
    rw [Category.assoc, ← Category.assoc w g, h12, zero_comp, comp_zero]
  have he₂₁ : (g ≫ s) ≫ r ≫ w = 0 := by
    rw [Category.assoc, ← Category.assoc s r, hsr, zero_comp, comp_zero]
  have hsplit : g ≫ s = 𝟙 Y - r ≫ w := by
    have hwn : w ≫ (𝟙 Y - r ≫ w - g ≫ s) = 0 := by
      have h1 : w ≫ r ≫ w = w := by rw [← Category.assoc, hwr, Category.id_comp]
      have h2 : w ≫ g ≫ s = 0 := by rw [← Category.assoc, h12, zero_comp]
      simp only [Preadditive.comp_sub, Category.comp_id, h1, h2, sub_self]
    obtain ⟨t, ht⟩ : ∃ t : Z ⟶ Y, 𝟙 Y - r ≫ w - g ≫ s = g ≫ t :=
      Triangle.yoneda_exact₂ (Triangle.mk w g δ) hT _ hwn
    have hne₂ : (𝟙 Y - r ≫ w - g ≫ s) ≫ g ≫ s = 0 := by
      simp only [Preadditive.sub_comp, Category.id_comp, he₁₂, he₂, sub_zero, sub_self]
    have hne₁ : (𝟙 Y - r ≫ w - g ≫ s) ≫ r ≫ w = 0 := by
      simp only [Preadditive.sub_comp, Category.id_comp, he₁, he₂₁, sub_self]
    have htg : t ≫ g = 0 := by
      have h1 : g ≫ t ≫ g ≫ s = 0 := by rw [← Category.assoc, ← ht]; exact hne₂
      have h2 : t ≫ g ≫ s = 0 := by
        have h3 := congrArg (fun x => s ≫ x) h1
        simp only [comp_zero] at h3
        rwa [← Category.assoc, hsg, Category.id_comp] at h3
      have h4 := congrArg (fun x => x ≫ g) h2
      simp only [zero_comp] at h4
      rwa [Category.assoc, Category.assoc, hsg, Category.comp_id] at h4
    have hnn : (𝟙 Y - r ≫ w - g ≫ s) ≫ (𝟙 Y - r ≫ w - g ≫ s) = 0 := by
      rw [ht, Category.assoc, ← Category.assoc t, htg, zero_comp, comp_zero]
    have hzero : 𝟙 Y - r ≫ w - g ≫ s = 0 := by
      have hcid : (𝟙 Y - r ≫ w - g ≫ s) ≫ 𝟙 Y = 𝟙 Y - r ≫ w - g ≫ s := Category.comp_id _
      have hexp : (𝟙 Y - r ≫ w - g ≫ s) ≫ 𝟙 Y =
          (𝟙 Y - r ≫ w - g ≫ s) ≫ (r ≫ w) + (𝟙 Y - r ≫ w - g ≫ s) ≫ (g ≫ s) +
            (𝟙 Y - r ≫ w - g ≫ s) ≫ (𝟙 Y - r ≫ w - g ≫ s) := by
        rw [← Preadditive.comp_add, ← Preadditive.comp_add]
        congr 1
        abel
      rw [hne₁, hne₂, hnn] at hexp
      simpa using hcid.symm.trans hexp
    rw [sub_eq_zero] at hzero
    rw [← hzero]
  have hcc : c' ≫ c = 𝟙 Y - r ≫ ι := by rw [eq_sub_iff_add_eq, add_comm]; exact htotal
  refine ⟨s ≫ c', ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc g, hsplit, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, hcc', ← Category.assoc,
      ← Category.assoc c r, hcr, zero_comp, zero_comp, sub_zero]
  · calc (s ≫ c') ≫ (c ≫ g) = s ≫ (c' ≫ c) ≫ g := by simp only [Category.assoc]
      _ = s ≫ (𝟙 Y - r ≫ ι) ≫ g := by rw [hcc]
      _ = s ≫ g - (s ≫ r) ≫ ι ≫ g := by
            rw [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub]
            simp only [Category.assoc]
      _ = 𝟙 Z := by rw [hsr, zero_comp, sub_zero, hsg]

end Splitting

section MappingCone

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **A complement of a split summand of the target maps quasi-isomorphically into a mapping
cone.**  If `w : X^• ⟶ Y^•` has a projection `p : Y^• ⟶ Z^•` with `w ≫ p` a quasi-isomorphism, and
`c : W^• ⟶ Y^•`, `c' : Y^• ⟶ W^•` exhibit `W^•` as a complement of `Z^•` in `Y^•`, then
`c ≫ inr w : W^• ⟶ C(w)` is a quasi-isomorphism. -/
theorem quasiIso_comp_mappingCone_inr {X Y Z W : CochainComplex A ℤ} (w : X ⟶ Y) (p : Y ⟶ Z)
    (ι : Z ⟶ Y) (c : W ⟶ Y) (c' : Y ⟶ W) (t : X ⟶ Z) [QuasiIso t]
    (hwp : w ≫ p = t) (hcc' : c ≫ c' = 𝟙 W) (hcp : c ≫ p = 0)
    (htotal : p ≫ ι + c' ≫ c = 𝟙 Y) :
    QuasiIso (c ≫ CochainComplex.mappingCone.inr w) := by
  have ht : IsIso (DerivedCategory.Q.map t) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := t)).2 inferInstance
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, DerivedCategory.Q.map_comp]
  refine isIso_comp_mor₂_of_retraction (DerivedCategory.Q.map w)
    (DerivedCategory.Q.map (CochainComplex.mappingCone.inr w)) _
    (DerivedCategory.mappingCone_triangle_distinguished w)
    (DerivedCategory.Q.map p ≫ inv (DerivedCategory.Q.map t))
    (DerivedCategory.Q.map t ≫ DerivedCategory.Q.map ι)
    (DerivedCategory.Q.map c) (DerivedCategory.Q.map c') ?_ ?_ ?_ ?_
  · have h : DerivedCategory.Q.map w ≫ DerivedCategory.Q.map p = DerivedCategory.Q.map t := by
      rw [← DerivedCategory.Q.map_comp, hwp]
    rw [← Category.assoc, h, IsIso.hom_inv_id]
  · have h : DerivedCategory.Q.map c ≫ DerivedCategory.Q.map c' =
        DerivedCategory.Q.map (c ≫ c') := (DerivedCategory.Q.map_comp c c').symm
    rw [h, hcc', CategoryTheory.Functor.map_id]
  · have h : DerivedCategory.Q.map c ≫ DerivedCategory.Q.map p =
        DerivedCategory.Q.map (c ≫ p) := (DerivedCategory.Q.map_comp c p).symm
    rw [← Category.assoc, h, hcp, CategoryTheory.Functor.map_zero, zero_comp]
  · have h1 : (DerivedCategory.Q.map p ≫ inv (DerivedCategory.Q.map t)) ≫
        (DerivedCategory.Q.map t ≫ DerivedCategory.Q.map ι) =
        DerivedCategory.Q.map (p ≫ ι) := by
      rw [Category.assoc, IsIso.inv_hom_id_assoc, DerivedCategory.Q.map_comp]
    have h2 : DerivedCategory.Q.map c' ≫ DerivedCategory.Q.map c =
        DerivedCategory.Q.map (c' ≫ c) := (DerivedCategory.Q.map_comp _ _).symm
    rw [h1, h2, ← CategoryTheory.Functor.map_add, htotal, CategoryTheory.Functor.map_id]

/-- The first summand maps quasi-isomorphically into the mapping cone of `(u, v)` as soon as the
second component `v` is a quasi-isomorphism. -/
theorem quasiIso_biprod_inl_comp_mappingCone_inr {X Y₁ Y₂ : CochainComplex A ℤ}
    (u : X ⟶ Y₁) (v : X ⟶ Y₂) [QuasiIso v] :
    QuasiIso (biprod.inl ≫ CochainComplex.mappingCone.inr (biprod.lift u v)) :=
  quasiIso_comp_mappingCone_inr (biprod.lift u v) biprod.snd biprod.inr biprod.inl biprod.fst v
    (biprod.lift_snd u v) biprod.inl_fst biprod.inl_snd
    (by rw [add_comm]; exact biprod.total)

/-- The second summand maps quasi-isomorphically into the mapping cone of `(u, v)` as soon as the
first component `u` is a quasi-isomorphism. -/
theorem quasiIso_biprod_inr_comp_mappingCone_inr {X Y₁ Y₂ : CochainComplex A ℤ}
    (u : X ⟶ Y₁) (v : X ⟶ Y₂) [QuasiIso u] :
    QuasiIso (biprod.inr ≫ CochainComplex.mappingCone.inr (biprod.lift u v)) :=
  quasiIso_comp_mappingCone_inr (biprod.lift u v) biprod.fst biprod.inl biprod.inr biprod.snd u
    (biprod.lift_fst u v) biprod.inr_snd biprod.inr_fst biprod.total

end MappingCone

section Comparison

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w'} A] [HasDerivedCategory.{w} A]

/-- The chosen filtered K-injective resolution of `K^•`, with `K^•` itself — rather than the `K`
field of the setup — recorded as its source. -/
def extIntoResolution (M : DerivedCategory A) (K : CochainComplex.Filtered A) :
    K ⟶ (extIntoSetup.{w', w} M K).J :=
  (extIntoSetup.{w', w} M K).j

variable (M : DerivedCategory A) {K L : CochainComplex.Filtered A} (f : K ⟶ L)

/-- The morphism `(j_K, f ≫ j_L) : K^• ⟶ J_K^• ⊕ J_L^•` into the direct sum of the two chosen
filtered K-injective resolutions. -/
def resolutionSumMap :
    K ⟶ FilteredObject.biprodObj (extIntoSetup.{w', w} M K).J (extIntoSetup.{w', w} M L).J :=
  FilteredObject.biprodObjLift (extIntoResolution.{w', w} M K)
    (f ≫ extIntoResolution.{w', w} M L)

/-- The filtered complex into which both chosen resolutions map: the mapping cone of
`(j_K, f ≫ j_L)`. -/
def resolutionCone : CochainComplex.Filtered A :=
  filteredMappingCone (resolutionSumMap.{w', w} M f)

/-- The leg `J_K^• ⟶ D^•` of the comparison. -/
def resolutionConeFst : (extIntoSetup.{w', w} M K).J ⟶ resolutionCone.{w', w} M f :=
  (FilteredObject.biprodBicone _ _).inl ≫ filteredMappingConeInr (resolutionSumMap.{w', w} M f)

/-- The leg `J_L^• ⟶ D^•` of the comparison. -/
def resolutionConeSnd : (extIntoSetup.{w', w} M L).J ⟶ resolutionCone.{w', w} M f :=
  (FilteredObject.biprodBicone _ _).inr ≫ filteredMappingConeInr (resolutionSumMap.{w', w} M f)

/-- On the `p`-th filtration step, `(j_K, f ≫ j_L)` is the pairing of the `p`-th steps. -/
lemma resolutionSumMap_natTrans_app (i : ℤᵒᵖ) :
    (resolutionSumMap.{w', w} M f).natTrans.app i =
      biprod.lift ((extIntoResolution.{w', w} M K).natTrans.app i)
        (f.natTrans.app i ≫ (extIntoResolution.{w', w} M L).natTrans.app i) :=
  rfl

/-- The chosen resolution of `K^•` is a quasi-isomorphism on every filtration step. -/
lemma quasiIso_extIntoResolution_natTrans_app (p : ℤ) :
    QuasiIso ((extIntoResolution.{w', w} M K).natTrans.app (op p)) :=
  (extIntoSetup.{w', w} M K).resolution.2.2.2.2.2.2.2.2.2.1 p

/-- **The first leg of the comparison is a quasi-isomorphism on every filtration step.** -/
lemma quasiIso_resolutionConeFst_natTrans_app
    (hf : ∀ p : ℤ, QuasiIso (f.natTrans.app (op p))) (p : ℤ) :
    QuasiIso ((resolutionConeFst.{w', w} M f).natTrans.app (op p)) := by
  have h₁ := hf p
  have h₂ := quasiIso_extIntoResolution_natTrans_app.{w', w} M (K := L) p
  have h₃ : QuasiIso (f.natTrans.app (op p) ≫
      (extIntoResolution.{w', w} M L).natTrans.app (op p)) := inferInstance
  change QuasiIso (biprod.inl ≫
    CochainComplex.mappingCone.inr ((resolutionSumMap.{w', w} M f).natTrans.app (op p)))
  rw [resolutionSumMap_natTrans_app]
  exact quasiIso_biprod_inl_comp_mappingCone_inr _ _

/-- **The second leg of the comparison is a quasi-isomorphism on every filtration step.** -/
lemma quasiIso_resolutionConeSnd_natTrans_app (p : ℤ) :
    QuasiIso ((resolutionConeSnd.{w', w} M f).natTrans.app (op p)) := by
  have h₁ := quasiIso_extIntoResolution_natTrans_app.{w', w} M (K := K) p
  change QuasiIso (biprod.inr ≫
    CochainComplex.mappingCone.inr ((resolutionSumMap.{w', w} M f).natTrans.app (op p)))
  rw [resolutionSumMap_natTrans_app]
  exact quasiIso_biprod_inr_comp_mappingCone_inr _ _

/-- The comparison of the chosen resolution of `K^•` with the chosen resolution of the filtered
mapping cone. -/
def resolutionComparisonFst :
    (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M (resolutionCone.{w', w} M f)).J :=
  resolutionConeFst.{w', w} M f ≫ extIntoResolution.{w', w} M (resolutionCone.{w', w} M f)

/-- The comparison of the chosen resolution of `L^•` with the chosen resolution of the filtered
mapping cone. -/
def resolutionComparisonSnd :
    (extIntoSetup.{w', w} M L).J ⟶ (extIntoSetup.{w', w} M (resolutionCone.{w', w} M f)).J :=
  resolutionConeSnd.{w', w} M f ≫ extIntoResolution.{w', w} M (resolutionCone.{w', w} M f)

/-- Composing a morphism into the filtered mapping cone which is a quasi-isomorphism on the `p`-th
filtration step with the chosen resolution of the cone gives a quasi-isomorphism there. -/
private lemma quasiIso_natTrans_app_comp_extIntoResolution {X : CochainComplex.Filtered A}
    (a : X ⟶ resolutionCone.{w', w} M f) (p : ℤ) (h : QuasiIso (a.natTrans.app (op p))) :
    QuasiIso ((a ≫ extIntoResolution.{w', w} M (resolutionCone.{w', w} M f)).natTrans.app
      (op p)) := by
  have := quasiIso_extIntoResolution_natTrans_app.{w', w} M (K := resolutionCone.{w', w} M f) p
  change QuasiIso (a.natTrans.app (op p) ≫ _)
  infer_instance

/-- **The comparison of chosen filtered K-injective resolutions, first leg.**  It is a
quasi-isomorphism on every filtration step. -/
theorem quasiIso_natTrans_app_resolutionComparison_fst
    (hf : ∀ p : ℤ, QuasiIso (f.natTrans.app (op p))) (p : ℤ) :
    QuasiIso ((resolutionComparisonFst.{w', w} M f).natTrans.app (op p)) :=
  quasiIso_natTrans_app_comp_extIntoResolution.{w', w} M f _ p
    (quasiIso_resolutionConeFst_natTrans_app.{w', w} M f hf p)

/-- **The comparison of chosen filtered K-injective resolutions, second leg.**  It is a
quasi-isomorphism on every filtration step. -/
theorem quasiIso_natTrans_app_resolutionComparison_snd (p : ℤ) :
    QuasiIso ((resolutionComparisonSnd.{w', w} M f).natTrans.app (op p)) :=
  quasiIso_natTrans_app_comp_extIntoResolution.{w', w} M f _ p
    (quasiIso_resolutionConeSnd_natTrans_app.{w', w} M f p)

/-- **A filtered quasi-isomorphism of filtered complexes induces an isomorphism of Ext spectral
sequences.**  If `f : K^• ⟶ L^•` is a quasi-isomorphism on every filtration step then the spectral
sequences of Tag 0G1X attached to `K^•` and to `L^•` are isomorphic, hence have the same pages,
differentials and page-turning isomorphisms. -/
theorem nonempty_extSpectralSequenceInto_iso_of_quasiIso_filtered
    (hf : ∀ p : ℤ, QuasiIso (f.natTrans.app (op p))) :
    Nonempty ((extSpectralSequenceInto.{w', w} M K).1 ≅
      (extSpectralSequenceInto.{w', w} M L).1) := by
  obtain ⟨h₁⟩ := nonempty_extSpectralSequenceInto_iso_of_quasiIso.{w', w} M
    (resolutionComparisonFst.{w', w} M f)
    (quasiIso_natTrans_app_resolutionComparison_fst.{w', w} M f hf)
  obtain ⟨h₂⟩ := nonempty_extSpectralSequenceInto_iso_of_quasiIso.{w', w} M
    (resolutionComparisonSnd.{w', w} M f)
    (quasiIso_natTrans_app_resolutionComparison_snd.{w', w} M f)
  exact ⟨h₁ ≪≫ h₂.symm⟩

end Comparison

section CanonicalTruncation

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w'} A] [HasDerivedCategory.{w} A]

/-- **Stacks 0G1Y, representative independence.**  Let `A` be a Grothendieck abelian category and
let `M` and `K` be objects of `D(A)`.  The Ext spectral sequence of Tag 0G1X attached to the
canonical truncation filtration `F^pK^• = τ_{≤ -p}K^•` of a complex `K^•` representing `K` does
not depend on the choice of `K^•`: for any two complexes `K₁^•` and `K₂^•` representing `K` the
two spectral sequences are isomorphic, so they have the same pages, differentials and
page-turning isomorphisms from `E₁` onward.

The two spectral sequences compared are the ones named
`Stacks.Injectives.canonicalExtSpectralSequenceInto M K₁` and
`Stacks.Injectives.canonicalExtSpectralSequenceInto M K₂`, that name being by definition the Ext
spectral sequence of Tag 0G1X applied to the canonical truncation filtration; it is written out
here so that this file does not depend on the module which introduces it. -/
@[stacks 0G1Y "representative_independence"]
theorem nonempty_canonicalExtSpectralSequenceInto_iso (M : DerivedCategory A)
    (K : DerivedCategory A) (K₁ K₂ : CochainComplex A ℤ)
    (e₁ : DerivedCategory.Q.obj K₁ ≅ K) (e₂ : DerivedCategory.Q.obj K₂ ≅ K) :
    Nonempty ((extSpectralSequenceInto.{w', w} M
        (CochainComplex.canonicalTruncationFiltration K₁)).1 ≅
      (extSpectralSequenceInto.{w', w} M
        (CochainComplex.canonicalTruncationFiltration K₂)).1) := by
  let f : DerivedCategory.Q.obj K₁ ⟶ DerivedCategory.Q.obj K₂ := e₁.hom ≫ e₂.inv
  have hf : IsIso f := by
    dsimp [f]
    infer_instance
  obtain ⟨X, s, hs, g, hfac⟩ := DerivedCategory.right_fac f
  have hEq : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ f := by
    calc
      DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫
          inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g := by simp
      _ = DerivedCategory.Q.map s ≫ f := by rw [hfac]
  have hgIso : IsIso (DerivedCategory.Q.map g) := by
    rw [hEq]
    infer_instance
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).1 hs
  have : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := g)).1 hgIso
  obtain ⟨h₁⟩ := nonempty_extSpectralSequenceInto_iso_of_quasiIso_filtered.{w', w} M
    (CochainComplex.truncationFiltrationMap s)
    (fun p => quasiIso_truncationFiltrationMap_natTrans_app s p)
  obtain ⟨h₂⟩ := nonempty_extSpectralSequenceInto_iso_of_quasiIso_filtered.{w', w} M
    (CochainComplex.truncationFiltrationMap g)
    (fun p => quasiIso_truncationFiltrationMap_natTrans_app g p)
  exact ⟨h₁.symm ≪≫ h₂⟩

end CanonicalTruncation

end Stacks.Injectives

end

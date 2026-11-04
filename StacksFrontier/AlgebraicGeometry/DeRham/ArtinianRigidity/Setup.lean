module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The graph of the trivial deformation and its infinitesimal neighbourhoods

Let `A` be a local ring with a coefficient field `σ : A/𝔪 → A`, and let `f : X ⟶ Spec A` be
separated. Write `X₀ = X ×_A Spec(A/𝔪)` for the special fibre and `X' = X₀ ×_{A/𝔪} Spec A` for the
trivial deformation of `X₀` (formed with `σ`). The closed immersions `i : X₀ ⟶ X` and
`i' : X₀ ⟶ X'` identify the two special fibres, and `Γ = (i, i') : X₀ ⟶ W = X ×_A X'` is the graph
of that identification, a closed immersion. Its `N`-th infinitesimal neighbourhood `W_N` is the
closed subscheme cut out by `I_Γ^N`, with projections `q : W_N ⟶ X` and `q' : W_N ⟶ X'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.DeRhamRigidity

variable (A : CommRingCat.{u}) [IsLocalRing A]

/-- The residue field `A/𝔪`, as a commutative ring. -/
abbrev residueRing : CommRingCat.{u} := CommRingCat.of (A ⧸ maximalIdeal A)

/-- The residue map `A → A/𝔪`. -/
abbrev residueMap : A ⟶ residueRing A := CommRingCat.ofHom (Ideal.Quotient.mk _)

variable {A} (σ : A ⧸ maximalIdeal A →+* A)

/-- The coefficient field `σ : A/𝔪 → A`, as a morphism of commutative rings. -/
abbrev sectionMap : residueRing A ⟶ A := CommRingCat.ofHom σ

variable {σ} (hσ : (Ideal.Quotient.mk (maximalIdeal A)).comp σ = RingHom.id _)

include hσ in
/-- The composite `A/𝔪 → A → A/𝔪` of the coefficient field and the residue map is the identity. -/
theorem sectionMap_residueMap : sectionMap σ ≫ residueMap A = 𝟙 _ := by
  ext x
  exact congrArg (fun φ : A ⧸ maximalIdeal A →+* A ⧸ maximalIdeal A => φ x) hσ

include hσ in
/-- The composite `Spec(A/𝔪) ⟶ Spec A ⟶ Spec(A/𝔪)` induced by the residue map and the coefficient
field is the identity. -/
theorem specMap_residueMap_sectionMap :
    Spec.map (residueMap A) ≫ Spec.map (sectionMap σ) = 𝟙 _ := by
  rw [← Spec.map_comp, sectionMap_residueMap hσ, Spec.map_id]

variable {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- **The special fibre** `X₀ = X ×_A Spec(A/𝔪)`. -/
abbrev special : Scheme.{u} := pullback f (Spec.map (residueMap A))

/-- The structure map `X₀ ⟶ Spec(A/𝔪)`. -/
abbrev specialMap : special f ⟶ Spec (residueRing A) := pullback.snd _ _

/-- The inclusion `i : X₀ ⟶ X` of the special fibre. -/
abbrev specialIncl : special f ⟶ X := pullback.fst _ _

variable (σ) in
/-- **The trivial deformation** `X' = X₀ ×_{A/𝔪} Spec A` of the special fibre, formed with the
coefficient field. -/
abbrev trivialDef : Scheme.{u} := pullback (specialMap f) (Spec.map (sectionMap σ))

variable (σ) in
/-- The structure map `X' ⟶ Spec A`. -/
abbrev trivialMap : trivialDef σ f ⟶ Spec A := pullback.snd _ _

/-- The inclusion `i' : X₀ ⟶ X'` of the special fibre into the trivial deformation. -/
def trivialIncl : special f ⟶ trivialDef σ f :=
  pullback.lift (𝟙 _) (specialMap f ≫ Spec.map (residueMap A)) (by
    rw [Category.id_comp, Category.assoc, specMap_residueMap_sectionMap hσ, Category.comp_id])

/-- The composite of `i' : X₀ ⟶ X'` with the projection `X' ⟶ X₀` is the identity. -/
@[reassoc (attr := simp)]
theorem trivialIncl_fst : trivialIncl hσ f ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _

/-- The composite of `i' : X₀ ⟶ X'` with `X' ⟶ Spec A` is `X₀ ⟶ Spec(A/𝔪) ⟶ Spec A`. -/
@[reassoc (attr := simp)]
theorem trivialIncl_snd :
    trivialIncl hσ f ≫ trivialMap σ f = specialMap f ≫ Spec.map (residueMap A) :=
  pullback.lift_snd _ _ _

/-- The special fibre of the trivial deformation is `X₀`. -/
theorem isPullback_trivialIncl :
    IsPullback (trivialIncl hσ f) (specialMap f) (trivialMap σ f) (Spec.map (residueMap A)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (specialMap f) (Spec.map (sectionMap σ)))
    (h₂₂ := Spec.map (sectionMap σ)) (v₁₃ := specialMap f) ?_ (trivialIncl_snd hσ f)
    (IsPullback.of_hasPullback _ _)
  rw [trivialIncl_fst, specMap_residueMap_sectionMap hσ]
  exact IsPullback.of_id_fst

/-- The special fibre of `X` is `X₀`. -/
theorem isPullback_specialIncl :
    IsPullback (specialIncl f) (specialMap f) f (Spec.map (residueMap A)) :=
  IsPullback.of_hasPullback _ _

variable (σ) in
/-- The fibre product `W = X ×_A X'`. -/
abbrev graphSpace : Scheme.{u} := pullback f (trivialMap σ f)

/-- The inclusions `i : X₀ ⟶ X` and `i' : X₀ ⟶ X'` agree over `Spec A`. -/
theorem specialIncl_comp : specialIncl f ≫ f = trivialIncl hσ f ≫ trivialMap σ f := by
  rw [trivialIncl_snd, pullback.condition]

/-- **The graph** `Γ = (i, i') : X₀ ⟶ X ×_A X'` of the identification of the special fibres. -/
def graph : special f ⟶ graphSpace σ f :=
  pullback.lift (specialIncl f) (trivialIncl hσ f) (specialIncl_comp hσ f)

/-- The first component of the graph `Γ` is `i : X₀ ⟶ X`. -/
@[reassoc (attr := simp)]
theorem graph_fst : graph hσ f ≫ pullback.fst _ _ = specialIncl f := pullback.lift_fst _ _ _

/-- The second component of the graph `Γ` is `i' : X₀ ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem graph_snd : graph hσ f ≫ pullback.snd _ _ = trivialIncl hσ f := pullback.lift_snd _ _ _

/-- **The graph is a closed immersion**: it is the graph of `i'` over `Spec A`, a closed immersion
because `X'` is separated over `A`, followed by the base change of the closed immersion `i`. -/
instance isClosedImmersion_graph [IsSeparated f] : IsClosedImmersion (graph hσ f) := by
  haveI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
    ⟨fun _ _ hf hg => by haveI := hf; haveI := hg; infer_instance⟩
  have hmap : IsClosedImmersion (pullback.map (trivialIncl hσ f ≫ trivialMap σ f) (trivialMap σ f)
      f (trivialMap σ f) (specialIncl f) (𝟙 _) (𝟙 _) (by rw [Category.comp_id,
        specialIncl_comp hσ f]) (by simp)) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance
      (inferInstance : IsClosedImmersion (𝟙 (trivialDef σ f))) (specialIncl_comp hσ f).symm
      (Category.id_comp _).symm
  have hfac : graph hσ f = pullback.lift (𝟙 _) (trivialIncl hσ f)
      (Category.id_comp (trivialIncl hσ f ≫ trivialMap σ f)) ≫
      pullback.map (trivialIncl hσ f ≫ trivialMap σ f) (trivialMap σ f) f (trivialMap σ f)
        (specialIncl f) (𝟙 _) (𝟙 _) (by rw [Category.comp_id, specialIncl_comp hσ f])
        (by simp) := by
    apply pullback.hom_ext <;>
      simp only [graph, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.map,
        pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]
  rw [hfac]
  infer_instance

/-- **The ideal sheaf of the graph** `I_Γ ⊆ 𝒪_W`. -/
abbrev graphIdealSheaf [IsSeparated f] : (graphSpace σ f).IdealSheafData := (graph hσ f).ker

variable (N : ℕ)

/-- **The `N`-th infinitesimal neighbourhood of the graph**, `W_N = V(I_Γ^N) ⊆ W`. -/
abbrev graphNbhd [IsSeparated f] : Scheme.{u} := (graphIdealSheaf hσ f ^ N).subscheme

/-- The closed immersion `W_N ⟶ W`. -/
abbrev graphNbhdι [IsSeparated f] : graphNbhd hσ f N ⟶ graphSpace σ f :=
  (graphIdealSheaf hσ f ^ N).subschemeι

/-- The projection `q : W_N ⟶ X`. -/
abbrev graphNbhdFst [IsSeparated f] : graphNbhd hσ f N ⟶ X :=
  graphNbhdι hσ f N ≫ pullback.fst _ _

/-- The projection `q' : W_N ⟶ X'`. -/
abbrev graphNbhdSnd [IsSeparated f] : graphNbhd hσ f N ⟶ trivialDef σ f :=
  graphNbhdι hσ f N ≫ pullback.snd _ _

/-- The projections `q : W_N ⟶ X` and `q' : W_N ⟶ X'` agree over `Spec A`. -/
theorem graphNbhdFst_comp [IsSeparated f] :
    graphNbhdFst hσ f N ≫ f = graphNbhdSnd hσ f N ≫ trivialMap σ f := by
  simp [pullback.condition]

/-- **Every point of `W_N` lies on the graph.** -/
theorem range_graphNbhdι_subset [IsSeparated f] (hN : N ≠ 0) :
    Set.range (graphNbhdι hσ f N) ⊆ Set.range (graph hσ f) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow _ _ hN,
    Scheme.Hom.support_ker, (graph hσ f).isClosedEmbedding.isClosed_range.closure_eq]

end Stacks.DeRhamRigidity

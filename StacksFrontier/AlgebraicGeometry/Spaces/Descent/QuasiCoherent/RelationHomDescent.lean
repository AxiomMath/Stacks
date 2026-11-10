module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMorphismHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapEtaleAtlasDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Descent of morphisms of modules along an étale atlas, from the relation

Let `φ : U ⟶ X` be a relatively representable surjective étale morphism of algebraic spaces and
`t, s : R ⟶ U` exhibit `R` as `U ×_X U`. A morphism `ψ : φ^*M ⟶ φ^*N` of the inverse images of two
`𝒪_X`-modules which is compatible on `R`, with the canonical comparison of Stacks 04W5 at the pair
`(t, s)`, is the inverse image of a unique morphism `M ⟶ N`.

Descent along `φ` asks for the compatibility at every pair of morphisms into `U` with equal
composites to `X`
(`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_dominated`);
every such pair factors through `R`, and the canonical comparison along a factored pair is the
reindexing of the comparison at `(t, s)`
(`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_hom_eq_modulePullbackReindex`),
so the condition at `(t, s)` suffices. No quasi-coherence is needed.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.existsUnique_modulePullback_map_eq_of_relation`.
* `AlgebraicGeometry.Space.Presentation.existsUnique_modulePullback_atlas_map_eq`: the same along
  the atlas of an étale presentation.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X U R : AlgebraicSpaces B S hS}

/-- **The canonical comparison along a pair factored through a pair `(t, s)` is the reindexing of
the canonical comparison at `(t, s)`.** -/
theorem canonicalComparison_hom_eq_modulePullbackReindex (t s : R ⟶ U) (φ : U ⟶ X)
    (hw : t ≫ φ = s ≫ φ) (M : Modules.{u, u} B S hS X.1 X.2) {P : AlgebraicSpaces B S hS}
    (v : P ⟶ R) (h' : (v ≫ t) ≫ φ = (v ≫ s) ≫ φ) :
    (canonicalComparison (v ≫ t) (v ≫ s) φ φ h' M).hom =
      modulePullbackReindex v (canonicalComparison t s φ φ hw M).hom := by
  have key : modulePullbackFlatten φ (modulePullbackReindex v
      (canonicalComparison t s φ φ hw M).hom) = pullbackTransport M h' := by
    rw [canonicalComparison_hom_eq_unflatten,
      (modulePullbackCompIsoAssoc B S hS).modulePullbackFlatten_reindex v φ,
      modulePullbackFlatten_unflatten, pullbackTransport_eq_eqToHom,
      modulePullbackReindex_eqToHom v M hw, pullbackTransport_eq_eqToHom]
  refine (canonicalComparison_hom_eq_unflatten B S hS _ _ φ h' M).trans ?_
  exact (congrArg (modulePullbackUnflatten φ) key.symm).trans
    (modulePullbackUnflatten_flatten φ _)

/-- Reindexing preserves a commutative square with the inverse images of a morphism. -/
theorem map_comp_modulePullbackReindex {a b : U ⟶ X} {M' N' : Modules.{u, u} B S hS X.1 X.2}
    (ψ : M' ⟶ N') (αM : (modulePullback B S hS a).obj M' ⟶ (modulePullback B S hS b).obj M')
    (αN : (modulePullback B S hS a).obj N' ⟶ (modulePullback B S hS b).obj N')
    (h : (modulePullback B S hS a).map ψ ≫ αN = αM ≫ (modulePullback B S hS b).map ψ)
    {P : AlgebraicSpaces B S hS} (v : P ⟶ U) :
    (modulePullback B S hS (v ≫ a)).map ψ ≫ modulePullbackReindex v αN =
      modulePullbackReindex v αM ≫ (modulePullback B S hS (v ≫ b)).map ψ := by
  have h₁ := (modulePullbackCompIso B S hS v a).inv.naturality ψ
  have h₂ := (modulePullbackCompIso B S hS v b).hom.naturality ψ
  simp only [Functor.comp_map] at h₁ h₂
  simp only [modulePullbackReindex, ← Category.assoc, h₁]
  simp only [Category.assoc, ← h₂, ← Functor.map_comp_assoc, h]

/-- **Compatibility on the relation gives compatibility at every factored pair.** -/
theorem map_comp_canonicalComparison_of_relation (t s : R ⟶ U) (φ : U ⟶ X)
    (hw : t ≫ φ = s ≫ φ) {M N : Modules.{u, u} B S hS X.1 X.2}
    (ψ : (modulePullback B S hS φ).obj M ⟶ (modulePullback B S hS φ).obj N)
    (hψ : (modulePullback B S hS t).map ψ ≫ (canonicalComparison t s φ φ hw N).hom =
      (canonicalComparison t s φ φ hw M).hom ≫ (modulePullback B S hS s).map ψ)
    {P : AlgebraicSpaces B S hS} (v : P ⟶ R) (h' : (v ≫ t) ≫ φ = (v ≫ s) ≫ φ) :
    (modulePullback B S hS (v ≫ t)).map ψ ≫ (canonicalComparison (v ≫ t) (v ≫ s) φ φ h' N).hom =
      (canonicalComparison (v ≫ t) (v ≫ s) φ φ h' M).hom ≫
        (modulePullback B S hS (v ≫ s)).map ψ :=
  (whisker_eq _ (canonicalComparison_hom_eq_modulePullbackReindex B S hS t s φ hw N v h')).trans
    ((map_comp_modulePullbackReindex B S hS ψ _ _ hψ v).trans
      (eq_whisker (canonicalComparison_hom_eq_modulePullbackReindex B S hS t s φ hw M v h').symm
        _))

/-- **Descent of morphisms along an étale atlas, from the relation.** For a relatively
representable surjective étale `φ : U ⟶ X` with `R = U ×_X U` along `t, s`, a morphism
`ψ : φ^*M ⟶ φ^*N` compatible with the canonical comparison at `(t, s)` is the inverse image of
a unique morphism `M ⟶ N`. -/
theorem existsUnique_modulePullback_map_eq_of_relation (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => U.1) (fun _ => φ.hom)) (t s : R ⟶ U)
    (hpb : IsPullback t.hom s.hom φ.hom φ.hom) (hw : t ≫ φ = s ≫ φ)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (ψ : (modulePullback B S hS φ).obj M ⟶ (modulePullback B S hS φ).obj N)
    (hψ : (modulePullback B S hS t).map ψ ≫ (canonicalComparison t s φ φ hw N).hom =
      (canonicalComparison t s φ φ hw M).hom ≫ (modulePullback B S hS s).map ψ) :
    ∃! χ : M ⟶ N, (modulePullback B S hS φ).map χ = ψ := by
  obtain ⟨χ, hχ⟩ := exists_modulePullback_map_eq_of_dominated B S hS φ hφ hrep hcov ψ
    fun P a b hab => by
      obtain ⟨v, rfl, rfl⟩ : ∃ v : P ⟶ R, v ≫ t = a ∧ v ≫ s = b :=
        ⟨ObjectProperty.homMk (hpb.lift a.hom b.hom (congrArg (fun f : P ⟶ X => f.hom) hab)),
          ObjectProperty.hom_ext _ (hpb.lift_fst _ _ _),
          ObjectProperty.hom_ext _ (hpb.lift_snd _ _ _)⟩
      exact map_comp_canonicalComparison_of_relation B S hS t s φ hw ψ hψ v hab
  refine ⟨χ, hχ, fun χ' hχ' => ?_⟩
  exact modulePullback_map_injective_of_isEtaleCovering B S hS (fun _ : Unit => U)
    (fun _ => φ) hcov χ' χ fun _ => hχ'.trans hχ.symm

end AlgebraicGeometry.Space.QuasiCoherentDescent

namespace AlgebraicGeometry.Space.Presentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.1 X.2)

/-- The target projection of a presentation, as a morphism of algebraic spaces. -/
abbrev relationTarget : schemeSpace P.R ⟶ schemeSpace P.U := schemeSpaceMap P.target

/-- The source projection of a presentation, as a morphism of algebraic spaces. -/
abbrev relationSource : schemeSpace P.R ⟶ schemeSpace P.U := schemeSpaceMap P.source

theorem relationTarget_comp_atlas : P.relationTarget ≫ P.atlas = P.relationSource ≫ P.atlas :=
  ObjectProperty.hom_ext _ P.isPullback.w

/-- **Descent of morphisms of `𝒪_X`-modules along the atlas of an étale presentation `X = U/R`**:
a morphism `ψ : φ^*M ⟶ φ^*N` of the inverse images along the atlas `φ : U ⟶ X` which is
compatible on `R` with the canonical comparison of Stacks 04W5 is the inverse image of a unique
morphism `M ⟶ N`. -/
theorem existsUnique_modulePullback_atlas_map_eq {M N : Modules.{u, u} B S hS X.1 X.2}
    (ψ : (modulePullback B S hS P.atlas).obj M ⟶ (modulePullback B S hS P.atlas).obj N)
    (hψ : (modulePullback B S hS P.relationTarget).map ψ ≫
        (QuasiCoherentDescent.canonicalComparison P.relationTarget P.relationSource P.atlas
          P.atlas P.relationTarget_comp_atlas N).hom =
      (QuasiCoherentDescent.canonicalComparison P.relationTarget P.relationSource P.atlas
          P.atlas P.relationTarget_comp_atlas M).hom ≫
        (modulePullback B S hS P.relationSource).map ψ) :
    ∃! χ : M ⟶ N, (modulePullback B S hS P.atlas).map χ = ψ :=
  QuasiCoherentDescent.existsUnique_modulePullback_map_eq_of_relation B S hS P.atlas
    P.isEtale_atlas
    (relativelyRepresentable_of_representableSource B S hS P.atlas P.U (Iso.refl _))
    (isEtaleCovering_atlas B S hS X.2 P.surjective P.etale) P.relationTarget P.relationSource
    P.isPullback P.relationTarget_comp_atlas ψ hψ

end AlgebraicGeometry.Space.Presentation

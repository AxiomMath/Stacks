module

public import StacksFrontier.AlgebraicGeometry.GeomConnectedFibres.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.EtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsRationalPoints
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsSeparablePoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The pieces of `X ×_k Spec(E)` over the points of `Spec(Γ(X, 𝒪_X) ⊗_k E)`

Let `X` be a nonempty smooth projective scheme over a field `k`, `k' = Γ(X, 𝒪_X)` (a finite
étale `k`-algebra) and `E/k` a finite separable extension splitting `k'`. Then
`Spec(k') ×_k Spec(E) = ∐_σ Spec(E)`, `σ` running over `Hom_k(k', E)`, with coprojections
`ι_σ = (Spec(σ), id)` (`Stacks.WeilCohomology.SmoothProjectiveScheme.splitInj`). Pulling this
decomposition back along `π × id : X ×_k Spec(E) ⟶ Spec(k') ×_k Spec(E)`, `π : X ⟶ Spec(k')` the
canonical morphism, gives the pieces

`Y_σ = (X ×_k Spec(E)) ×_{Spec(k') ×_k Spec(E), ι_σ} Spec(E) = X ×_{Spec(k'), Spec(σ)} Spec(E)`.

This file shows that `Y_σ ⟶ Spec(E)` is smooth, projective and **geometrically irreducible**:
smooth and projective because it is the restriction of `X ×_k Spec(E) ⟶ Spec(E)` to an open and
closed subscheme; geometrically connected because it is a base change of `X ⟶ Spec(k')`, whose
fibres are geometrically connected (Varieties, Lemma 0FD1); geometrically irreducible because a
geometrically connected smooth scheme over a field is geometrically irreducible.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.baseChangeMap`: `π × id`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.piece`: the scheme `Y_σ`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.pieceToSpec`: `Y_σ ⟶ Spec(E)`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.pieceHom`: `Y_σ ⟶ X ×_k Spec(E)`, a morphism of
  smooth projective `k`-schemes.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.geometricallyIrreducible_pieceToSpec`.

## References

* [Stacks Project, Tag 0FI0](https://stacks.math.columbia.edu/tag/0FI0)
* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- `Spec Γ(X, 𝒪_X)` has dimension zero when `X` is nonempty. -/
theorem topologicalKrullDim_specGlobalSections [Nontrivial (globalSections X)] :
    topologicalKrullDim (specGlobalSections X).obj.left = 0 :=
  topologicalKrullDim_spec_eq_zero (k := k) (globalSections X)

variable (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E] [Algebra.IsSeparable k E]

/-- **`π × id : X ×_k Spec(E) ⟶ Spec(k') ×_k Spec(E)`**, `π : X ⟶ Spec(k')` the canonical
morphism, `k' = Γ(X, 𝒪_X)`. -/
def baseChangeMap : prod X (spec k E) ⟶ prod (specGlobalSections X) (spec k E) :=
  prodLift (fst X (spec k E) ≫ toSpecGlobalSections X) (snd X (spec k E))

/-- The first component of `π × id` is `X ×_k Spec(E) ⟶ X ⟶ Spec(k')`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_fst :
    baseChangeMap X E ≫ fst _ _ = fst X (spec k E) ≫ toSpecGlobalSections X :=
  prodLift_fst _ _

/-- The second component of `π × id` is the projection `X ×_k Spec(E) ⟶ Spec(E)`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_snd : baseChangeMap X E ≫ snd _ _ = snd X (spec k E) :=
  prodLift_snd _ _

/-- The square `X ×_k Spec(E) ⟶ X`, `π × id`, `π`, `Spec(k') ×_k Spec(E) ⟶ Spec(k')` is
cartesian: `X ×_k Spec(E) = X ×_{Spec(k')} (Spec(k') ×_k Spec(E))`. -/
theorem isPullback_baseChangeMap :
    IsPullback (fst X (spec k E)).hom.left (baseChangeMap X E).hom.left
      (toSpecGlobalSections X).hom.left (fst (specGlobalSections X) (spec k E)).hom.left := by
  have houter : IsPullback ((baseChangeMap X E).hom.left ≫
      (snd (specGlobalSections X) (spec k E)).hom.left) (fst X (spec k E)).hom.left
      (spec k E).obj.hom ((toSpecGlobalSections X).hom.left ≫ (specGlobalSections X).obj.hom) := by
    rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, baseChangeMap_snd,
      Over.w (toSpecGlobalSections X).hom]
    exact (IsPullback.of_hasPullback X.obj.hom (spec k E).obj.hom).flip
  refine (houter.of_right ?_
    (IsPullback.of_hasPullback (specGlobalSections X).obj.hom (spec k E).obj.hom).flip).flip
  exact congrArg (fun f ↦ f.hom.left) (baseChangeMap_fst X E)

variable [Nontrivial (globalSections X)]
  (hsplit : ∀ a : globalSections (specGlobalSections X),
    ((minpoly k a).map (algebraMap k E)).Splits)

include hsplit in
/-- The coprojection `ι_σ : Spec(E) ⟶ Spec(k') ×_k Spec(E)` is an open immersion. -/
theorem isOpenImmersion_splitInj (σ : globalSections (specGlobalSections X) →ₐ[k] E) :
    IsOpenImmersion (splitInj (topologicalKrullDim_specGlobalSections X) E σ).hom.left := by
  obtain ⟨hc⟩ := FirstChernClassData.nonempty_isColimit_splitCofan_left (k := k)
    (K' := globalSections X) E hsplit
  let G : (globalSections (specGlobalSections X) →ₐ[k] E) → Scheme.{u} :=
    fun _ ↦ Spec (.of E)
  let φ := (colimit.isColimit (Discrete.functor G)).coconePointUniqueUpToIso hc
  have hφ : Sigma.ι G σ ≫ φ.hom =
      (splitInj (topologicalKrullDim_specGlobalSections X) E σ).hom.left :=
    (colimit.isColimit (Discrete.functor G)).comp_coconePointUniqueUpToIso_hom hc ⟨σ⟩
  rw [← hφ]
  infer_instance

/-- The coprojection `ι_σ` is a closed immersion: a section of the projection to `Spec(E)`. -/
instance isClosedImmersion_splitInj (σ : globalSections (specGlobalSections X) →ₐ[k] E) :
    IsClosedImmersion (splitInj (topologicalKrullDim_specGlobalSections X) E σ).hom.left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of E)) (snd _ (spec k E)).hom.left _
    (congrArg (fun f ↦ f.hom.left) (splitInj_snd _ E σ))

variable (σ : globalSections (specGlobalSections X) →ₐ[k] E)

/-- **The piece `Y_σ = (X ×_k Spec(E)) ×_{Spec(k') ×_k Spec(E), ι_σ} Spec(E)`.** -/
abbrev piece : Scheme.{u} :=
  Limits.pullback (baseChangeMap X E).hom.left
    (splitInj (topologicalKrullDim_specGlobalSections X) E σ).hom.left

/-- The inclusion `Y_σ ⟶ X ×_k Spec(E)`. -/
abbrev pieceι : piece X E σ ⟶ (prod X (spec k E)).obj.left := Limits.pullback.fst _ _

/-- The structure morphism `Y_σ ⟶ Spec(E)`. -/
abbrev pieceToSpec : piece X E σ ⟶ (fieldChowSituation E).S := Limits.pullback.snd _ _

include hsplit in
/-- The inclusion `Y_σ ⟶ X ×_k Spec(E)` is an open immersion. -/
theorem isOpenImmersion_pieceι : IsOpenImmersion (pieceι X E σ) :=
  have := isOpenImmersion_splitInj X E hsplit σ
  inferInstance

/-- The inclusion `Y_σ ⟶ X ×_k Spec(E)` is a closed immersion. -/
instance : IsClosedImmersion (pieceι X E σ) := inferInstance

/-- The composite `Y_σ ⟶ X ×_k Spec(E) ⟶ Spec(E)` is the structure morphism `Y_σ ⟶ Spec(E)`. -/
theorem pieceι_snd : pieceι X E σ ≫ (snd X (spec k E)).hom.left = pieceToSpec X E σ := by
  have h := Limits.pullback.condition (f := (baseChangeMap X E).hom.left)
    (g := (splitInj (topologicalKrullDim_specGlobalSections X) E σ).hom.left)
  have h2 := congrArg (fun f ↦ f.hom.left) (baseChangeMap_snd X E)
  have h3 := congrArg (fun f ↦ f.hom.left)
    (splitInj_snd (topologicalKrullDim_specGlobalSections X) E σ)
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left] at h2 h3
  show pieceι X E σ ≫ (snd X (spec k E)).hom.left = pieceToSpec X E σ
  rw [← h2, ← Category.assoc, h, Category.assoc, h3]
  exact Category.comp_id _

include hsplit in
/-- The structure morphism `Y_σ ⟶ Spec(E)` is smooth. -/
theorem smooth_pieceToSpec : Smooth (pieceToSpec X E σ) := by
  have := isOpenImmersion_pieceι X E hsplit σ
  have : Smooth (snd X (spec k E)).hom.left :=
    inferInstanceAs (Smooth (Limits.pullback.snd X.obj.hom (spec k E).obj.hom))
  rw [← pieceι_snd]
  infer_instance

/-- `Y_σ ⟶ Spec(E)` is projective: `X ×_k Spec(E) ⟶ Spec(E)` is (Stacks 01WF), and `Y_σ` is a
closed subscheme of `X ×_k Spec(E)`. -/
theorem isProjectiveMorphism_pieceToSpec : IsProjectiveMorphism (pieceToSpec X E σ) := by
  have hsnd : IsProjectiveMorphism (snd X (spec k E)).hom.left :=
    AlgebraicGeometry.IsProjectiveMorphism.baseChange (f := X.obj.hom)
      ((AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine _).1
        (SmoothProjectiveScheme.isProjective X))
      (spec k E).obj.hom
  obtain ⟨n, i, hi, h⟩ := hsnd
  have := hi
  refine ⟨n, pieceι X E σ ≫ i, inferInstance, ?_⟩
  rw [← pieceι_snd, Category.assoc]
  exact congrArg (pieceι X E σ ≫ ·) h

/-- The square `Y_σ ⟶ X`, `Y_σ ⟶ Spec(E)`, `π`, `Spec(σ)` is cartesian:
`Y_σ = X ×_{Spec(k'), Spec(σ)} Spec(E)`. -/
theorem isPullback_piece :
    IsPullback (pieceι X E σ ≫ (fst X (spec k E)).hom.left) (pieceToSpec X E σ)
      (toSpecGlobalSections X).hom.left
      ((splitInj (topologicalKrullDim_specGlobalSections X) E σ).hom.left ≫
        (fst (specGlobalSections X) (spec k E)).hom.left) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) (isPullback_baseChangeMap X E)

include hsplit in
/-- **`Y_σ ⟶ Spec(E)` is geometrically irreducible.** It is a base change of `X ⟶ Spec(k')`,
which has geometrically connected fibres (Stacks 0FD1), and it is smooth, so geometrically
irreducible. -/
theorem geometricallyIrreducible_pieceToSpec : GeometricallyIrreducible (pieceToSpec X E σ) := by
  have := smooth_pieceToSpec X E hsplit σ
  have : IsProper X.obj.hom := inferInstance
  have hconn : GeometricallyConnected X.obj.left.toSpecΓ :=
    AlgebraicGeometry.ProperGeomConnected.geometricallyConnected_toSpecΓ_of_isProper_over_field
      k X.obj.left X.obj.hom
  have hσ : GeometricallyConnected (pieceToSpec X E σ) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) (isPullback_piece X E σ) hconn
  have : QuasiCompact (pieceToSpec X E σ) := by
    have := isProper_of_isProjectiveMorphism _ (isProjectiveMorphism_pieceToSpec X E σ)
    infer_instance
  exact geometricallyIrreducible_of_geometricallyConnected_of_smooth _ hσ

/-- **`Y_σ` as a smooth projective scheme over `k`**, through `Y_σ ⟶ Spec(E) ⟶ Spec(k)`. -/
abbrev pieceObj : (SmoothProjectiveScheme k).FullSubcategory :=
  haveI := smooth_pieceToSpec X E hsplit σ
  ofOverField (k := k) (pieceToSpec X E σ) (isProjectiveMorphism_pieceToSpec X E σ)

/-- **The inclusion `Y_σ ⟶ X ×_k Spec(E)`**, a morphism of smooth projective `k`-schemes. -/
def pieceHom : pieceObj X E hsplit σ ⟶ prod X (spec k E) :=
  ObjectProperty.homMk (Over.homMk (pieceι X E σ) (by
    have hc : (fst X (spec k E)).hom.left ≫ X.obj.hom =
        (snd X (spec k E)).hom.left ≫ specStructure k E := Limits.pullback.condition
    change pieceι X E σ ≫ (fst X (spec k E)).hom.left ≫ X.obj.hom =
      pieceToSpec X E σ ≫ specStructure k E
    rw [hc, ← Category.assoc]
    exact congrArg (· ≫ specStructure k E) (pieceι_snd X E σ)))

/-- The underlying morphism of schemes of `pieceHom` is the inclusion `Y_σ ⟶ X ×_k Spec(E)`. -/
@[simp]
theorem pieceHom_left : (pieceHom X E hsplit σ).hom.left = pieceι X E σ :=
  rfl

end Stacks.WeilCohomology.SmoothProjectiveScheme

end

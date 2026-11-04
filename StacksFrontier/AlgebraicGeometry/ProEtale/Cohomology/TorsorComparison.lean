module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ComparisonWithEtale
public import StacksFrontier.CategoryTheory.Filtered.FiniteProductColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IteratedFibreProductLift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.InverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionEquivGroupRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionsFromCocycles
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf

/-!
# Torsors on the étale and the pro-étale site

Let `X` be a scheme and let `ε : X_proétale → X_étale` be the morphism of sites given by the
inclusion of the small étale site into the small pro-étale site. For a sheaf of (possibly
non-commutative) groups `G` on `X_étale`, the inverse image `ε⁻¹` induces a bijection

  `H¹(X_étale, G) = H¹(X_proétale, ε⁻¹G)`

on the sets of isomorphism classes of torsors (Stacks 099X).

## Main definitions

* `AlgebraicGeometry.ProEtale.torsorClassesEquiv`: the bijection of Stacks 099X, as an
  equivalence.

## Main results

* `AlgebraicGeometry.ProEtale.exists_stage_map_eq` and
  `AlgebraicGeometry.ProEtale.exists_stage_map_eq_map`: Stacks 099S on the iterated fibre
  products of a cofiltered limit of families.
* `AlgebraicGeometry.ProEtale.exists_covering_nonempty`: a pseudo-torsor under a sheaf of groups
  whose underlying sheaf of sets comes from `X_étale`, which has sections pro-étale locally on an
  object of `X_étale`, has sections étale locally on it.
* `AlgebraicGeometry.ProEtale.exists_covering_nonempty_of_isTorsor`: every `ε⁻¹G`-torsor on
  `X_proétale` has sections étale locally on `X`.
* `AlgebraicGeometry.ProEtale.bijective_torsorClassesMap`: the map induced by `ε⁻¹` on isomorphism
  classes of torsors, `H¹(X_étale, G) → H¹(X_proétale, ε⁻¹G)`, is bijective.

## Implementation notes

The proof is the source's. Injectivity holds because `ε⁻¹` is fully faithful (Stacks 099T). For
surjectivity it suffices that an `ε⁻¹G`-torsor `T` has sections étale locally: then the
restriction `ε_* T` is a `G`-torsor and the counit `ε⁻¹ε_* T ⟶ T` is a morphism of torsors
(`SheafOfGroups.TorsorClasses.map_bijective_of_adjunction`). Over an affine object `U` of
`X_étale`, `T` is trivialized by a finite covering `{V_k → U}` by affine objects ind-étale over
`U` (Proposition 097Z), and each `V_k` is the limit of affine schemes `V_{k,λ}` étale over `U`.
The cocycle of the trivializations is a family of sections of `ε⁻¹G` over the
`V_k ×_U V_l = lim V_{k,λ} ×_U V_{l,λ}`; by Stacks 099S it comes from sections over the
`V_{k,λ} ×_U V_{l,λ}` for some `λ`, which satisfy the cocycle condition at a later stage. That
cocycle produces sections of `T` over the `V_{l,λ}` (`PseudoTorsor.nonempty_of_cocycle`), and
these form an étale covering of `U`. The "details omitted" of the source, the relationship
between torsors and 1-cocycles, are supplied in this form: no torsor is glued from the cocycle;
the cocycle is only used to glue sections of `T`.

The inverse image `ε⁻¹` of sheaves of sets is the sheafified left Kan extension
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`, the model for which Stacks 099S
and 099T are proved. Torsors and sheaves of groups have their sections in the universe
`max (u + 1) v` of the coefficients of these sheaves of sets.

## References

* [Stacks Project, Tag 099X](https://stacks.math.columbia.edu/tag/099X)
* [Stacks Project, Tag 099S](https://stacks.math.columbia.edu/tag/099S)
* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite

universe v u

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u})

/-- The inverse image `ε⁻¹` of sheaves of sets along the inclusion of the small étale site into
the small pro-étale site is left exact: it is the sheafification of a left exact left Kan
extension. -/
instance preservesFiniteLimits_sheafPullback_etaleToProetale :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)) := by
  have : RepresentablyFlat X.etaleToProetale := flat_of_preservesFiniteLimits _
  have : PreservesFiniteLimits (X.etaleToProetale.op.lan :
      (X.Etaleᵒᵖ ⥤ Type (max (u + 1) v)) ⥤ _) :=
    Stacks.Topology.lan_preservesFiniteLimits_of_flat _ (fun _ ↦ inferInstance)
  infer_instance

/-- The inverse image `ε⁻¹` of sheaves of sets along the inclusion of the small étale site into
the small pro-étale site is a left adjoint. -/
instance isLeftAdjoint_sheafPullback_etaleToProetale :
    (Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).IsLeftAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
    (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).isLeftAdjoint


/-! ### Coverings of the small pro-étale site are jointly surjective -/

variable {X} in
/-! ### Sections of `ε⁻¹F` over the iterated fibre products of a limit of families -/

section Stages

variable {X} {U : X.ProEt} [IsAffine U.left] (E : PreZeroHypercover.{u} U)
  [∀ k, IsAffine (E.X k).left]
  {Λ : Type u} [SmallCategory Λ] [IsCofiltered Λ] (M : E.I₀ → Λ ⥤ X.ProEt)
  (m : ∀ k, M k ⟶ (Functor.const Λ).obj U)
  (πM : ∀ k, (Functor.const Λ).obj (E.X k) ⟶ M k)
  (hπ : ∀ k j, (πM k).app j ≫ (m k).app j =
    E.f k ≫ NatTrans.app (𝟙 ((Functor.const Λ).obj U)) j)
  (hMa : ∀ k j, IsAffine ((M k).obj j).left)
  (hB : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone
    (Cone.mk U (𝟙 ((Functor.const Λ).obj U)))))
  (hM : ∀ k, IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone
    (Cone.mk (E.X k) (πM k))))
  (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))

omit [∀ k, IsAffine (E.X k).left] [IsCofiltered Λ] in
include hMa in
/-- The iterated fibre products at the stages have affine underlying schemes. -/
lemma isAffine_stageFibreProduct_obj (n : ℕ) (t : Fin (n + 1) → E.I₀) (j : Λ) :
    IsAffine ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j).left :=
  have : IsAffine (((Functor.const Λ).obj U).obj j).left := ‹IsAffine U.left›
  isAffine_left_prod (stageFamily E _ M m j) (fun k ↦ hMa k j) n t

include hB hM in
/-- The iterated fibre products of `E` are the limits of those at the stages. -/
def isLimitStageFibreProductCone (n : ℕ) (t : Fin (n + 1) → E.I₀) :
    IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone
      (stageFibreProductCone E _ M m (𝟙 _) πM hπ n t)) := by
  let q := Scheme.ProEt.forget X ⋙ Over.forget X
  have : ∀ (n : ℕ) (t : Fin (n + 1) → E.I₀),
      PreservesLimit (Discrete.functor fun a ↦ Over.mk (E.f (t a))) (Over.post q) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost q E (fun _ _ _ ↦ inferInstance)
      (fun _ _ _ ↦ inferInstance)
  have : ∀ (j : Λ) (n : ℕ) (t : Fin (n + 1) → E.I₀),
      PreservesLimit (Discrete.functor fun a ↦ Over.mk
        ((stageFamily E ((Functor.const Λ).obj U) M m j).f (t a))) (Over.post q) := fun j ↦
    Stacks.Sites.preservesLimit_fibreProducts_overPost q (stageFamily E _ M m j)
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance)
  exact isLimitMapConeStageFibreProductCone E _ M m (𝟙 _) πM hπ q hB hM n t

omit [∀ k, IsAffine (E.X k).left] in
include hMa hB hM in
/-- **Stacks 099S, surjectivity, on iterated fibre products.** Every section of `ε⁻¹F` over an
iterated fibre product of `E` comes from a section over the corresponding iterated fibre product
at some stage. -/
lemma exists_stage_map_eq (n : ℕ) (t : Fin (n + 1) → E.I₀)
    (x : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.obj
        (op (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left)) :
    ∃ (j : Λ) (y : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.obj
        (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j))),
      ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.map
          ((stageFibreProductCone E _ M m (𝟙 _) πM hπ n t).π.app j).op y = x := by
  have := isAffine_stageFibreProduct_obj E M m hMa n t
  have : ∀ {i j : Λ} (f : i ⟶ j),
      IsAffineHom ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).map f).left :=
    fun _ ↦ inferInstance
  exact Scheme.proetaleInverseImage_jointly_surjective_of_isLimit.{u, v} X _ _
    (isLimitStageFibreProductCone E M m πM hπ hB hM n t) F x

omit [∀ k, IsAffine (E.X k).left] in
include hMa hB hM in
/-- **Stacks 099S, injectivity, on iterated fibre products.** Two sections of `ε⁻¹F` over an
iterated fibre product at a stage which agree over the iterated fibre product of `E` agree at a
later stage. -/
lemma exists_stage_map_eq_map (n : ℕ) (t : Fin (n + 1) → E.I₀) (j : Λ)
    (y y' : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.obj
      (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j)))
    (h : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.map
          ((stageFibreProductCone E _ M m (𝟙 _) πM hπ n t).π.app j).op y =
      ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.map
          ((stageFibreProductCone E _ M m (𝟙 _) πM hπ n t).π.app j).op y') :
    ∃ (i : Λ) (g : i ⟶ j),
      ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.map
          ((stageFibreProduct E _ M m n t).map g).op y =
        ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.map
            ((stageFibreProduct E _ M m n t).map g).op y' := by
  have := isAffine_stageFibreProduct_obj E M m hMa n t
  have : ∀ {i j : Λ} (f : i ⟶ j),
      IsAffineHom ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).map f).left :=
    fun _ ↦ inferInstance
  exact Scheme.proetaleInverseImage_exists_map_eq_of_isLimit.{u, v} X _ _
    (isLimitStageFibreProductCone E M m πM hπ hB hM n t) (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance) F j y y' h

omit [∀ k, IsAffine (E.X k).left] in
include hMa hB hM in
/-- `AlgebraicGeometry.ProEtale.exists_stage_map_eq` for a presheaf isomorphic to the
underlying presheaf of `ε⁻¹F`. -/
lemma exists_stage_map_eq_of_iso {Q : X.ProEtᵒᵖ ⥤ Type (max (u + 1) v)}
    (e : Q ≅ ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj)
    (n : ℕ) (t : Fin (n + 1) → E.I₀) (x : Q.obj (op (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left)) :
    ∃ (j : Λ) (y : Q.obj (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j))),
      Q.map ((stageFibreProductCone E _ M m (𝟙 _) πM hπ n t).π.app j).op y = x := by
  obtain ⟨j, y, hy⟩ := exists_stage_map_eq E M m πM hπ hMa hB hM F n t (e.hom.app _ x)
  refine ⟨j, e.inv.app _ y, ?_⟩
  rw [← NatTrans.naturality_apply, hy]
  exact congrFun (congrArg (fun f ↦ f.app _) e.hom_inv_id) x

omit [∀ k, IsAffine (E.X k).left] in
include hMa hB hM in
/-- `AlgebraicGeometry.ProEtale.exists_stage_map_eq_map` for a presheaf isomorphic to the
underlying presheaf of `ε⁻¹F`. -/
lemma exists_stage_map_eq_map_of_iso {Q : X.ProEtᵒᵖ ⥤ Type (max (u + 1) v)}
    (e : Q ≅ ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj)
    (n : ℕ) (t : Fin (n + 1) → E.I₀) (j : Λ)
    (y y' : Q.obj (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j)))
    (h : Q.map ((stageFibreProductCone E _ M m (𝟙 _) πM hπ n t).π.app j).op y =
      Q.map ((stageFibreProductCone E _ M m (𝟙 _) πM hπ n t).π.app j).op y') :
    ∃ (i : Λ) (g : i ⟶ j), Q.map ((stageFibreProduct E _ M m n t).map g).op y =
      Q.map ((stageFibreProduct E _ M m n t).map g).op y' := by
  obtain ⟨i, g, hg⟩ := exists_stage_map_eq_map E M m πM hπ hMa hB hM F n t j
    (e.hom.app _ y) (e.hom.app _ y') (by rw [← NatTrans.naturality_apply,
      ← NatTrans.naturality_apply, h])
  refine ⟨i, g, (Equiv.injective (e.app _).toEquiv) ?_⟩
  show e.hom.app _ _ = e.hom.app _ _
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hg]

variable {Q : X.ProEtᵒᵖ ⥤ Type*}

/-- A section of a presheaf over an iterated fibre product at a stage, evaluated at a tuple of
maps into the members of the family at that stage. -/
def stageEval {n : ℕ} {t : Fin (n + 1) → E.I₀} {j : Λ}
    (γ : Q.obj
      (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j)))
    {W : X.ProEt} (w : W ⟶ U) (y : ∀ a, W ⟶ (M (t a)).obj j)
    (hy : ∀ a, y a ≫ (m (t a)).app j = w) : Q.obj (op W) :=
  Q.map (cechProductLift (stageFamily E _ M m j) n t w y hy).op γ

omit [IsAffine U.left] [∀ k, IsAffine (E.X k).left] [IsCofiltered Λ] in
/-- `AlgebraicGeometry.ProEtale.stageEval` is the restriction along any morphism with the given
components. -/
lemma stageEval_eq_map {n : ℕ} {t : Fin (n + 1) → E.I₀} {j : Λ}
    (γ : Q.obj
      (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j)))
    {W : X.ProEt} (w : W ⟶ U) (y : ∀ a, W ⟶ (M (t a)).obj j)
    (hy : ∀ a, y a ≫ (m (t a)).app j = w)
    (h : W ⟶ (stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j)
    (hh : ∀ a, h ≫ (Pi.π (fun a ↦ Over.mk ((stageFamily E ((Functor.const Λ).obj U) M m j).f
      (t a))) a).left = y a) :
    stageEval E M m γ w y hy = Q.map h.op γ := by
  have : cechProductLift (stageFamily E _ M m j) n t w y hy = h :=
    cechProduct_left_hom_ext (stageFamily E _ M m j) n t fun a ↦ by
      rw [cechProductLift_π_left, hh]
  rw [stageEval, this]

omit [IsAffine U.left] [∀ k, IsAffine (E.X k).left] [IsCofiltered Λ] in
/-- Restriction of an evaluation is evaluation at the restricted tuple. -/
lemma map_stageEval {n : ℕ} {t : Fin (n + 1) → E.I₀} {j : Λ}
    (γ : Q.obj
      (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j)))
    {W W' : X.ProEt} (h : W' ⟶ W) (w : W ⟶ U) (y : ∀ a, W ⟶ (M (t a)).obj j)
    (hy : ∀ a, y a ≫ (m (t a)).app j = w) (w' : W' ⟶ U) (y' : ∀ a, W' ⟶ (M (t a)).obj j)
    (hy' : ∀ a, y' a ≫ (m (t a)).app j = w') (hyy' : ∀ a, h ≫ y a = y' a) :
    Q.map h.op (stageEval E M m γ w y hy) = stageEval E M m γ w' y' hy' := by
  rw [stageEval_eq_map E M m γ w' y' hy' (h ≫ cechProductLift (stageFamily E _ M m j) n t w y hy)
    (fun a ↦ by rw [Category.assoc, cechProductLift_π_left, hyy']), op_comp,
    FunctorToTypes.map_comp_apply]
  rfl

omit [IsAffine U.left] [∀ k, IsAffine (E.X k).left] [IsCofiltered Λ] in
/-- Evaluation of a section restricted along a transition map of the stages. -/
lemma stageEval_map_transition {n : ℕ} {t : Fin (n + 1) → E.I₀} {i j : Λ} (g : i ⟶ j)
    (γ : Q.obj
      (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j)))
    {W : X.ProEt} (w : W ⟶ U) (y : ∀ a, W ⟶ (M (t a)).obj i)
    (hy : ∀ a, y a ≫ (m (t a)).app i = w) (y' : ∀ a, W ⟶ (M (t a)).obj j)
    (hy' : ∀ a, y' a ≫ (m (t a)).app j = w) (hyy' : ∀ a, y a ≫ (M (t a)).map g = y' a) :
    stageEval E M m (Q.map ((stageFibreProduct E _ M m n t).map g).op γ) w y hy =
      stageEval E M m γ w y' hy' := by
  rw [stageEval, ← FunctorToTypes.map_comp_apply, ← op_comp]
  refine (stageEval_eq_map E M m γ w y' hy' _ fun a ↦ ?_).symm
  rw [Category.assoc, stageFibreProduct_map, cechProductMap_stageFamilyHomOver_comp_π_left,
    cechProductLift_π_left_assoc, hyy']

omit [IsAffine U.left] [∀ k, IsAffine (E.X k).left] [IsCofiltered Λ] in
/-- Evaluation of a section at the images of maps into the members of `E` is the restriction of
its image over the iterated fibre product of `E`. -/
lemma stageEval_comp_πM {n : ℕ} {t : Fin (n + 1) → E.I₀} {j : Λ}
    (γ : Q.obj
      (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j)))
    {W : X.ProEt} (w : W ⟶ U) (b : ∀ a, W ⟶ E.X (t a)) (hb : ∀ a, b a ≫ E.f (t a) = w)
    (y : ∀ a, W ⟶ (M (t a)).obj j) (hy : ∀ a, y a ≫ (m (t a)).app j = w)
    (hby : ∀ a, b a ≫ (πM (t a)).app j = y a) :
    stageEval E M m γ w y hy = Q.map (cechProductLift E n t w b hb).op
      (Q.map ((stageFibreProductCone E _ M m (𝟙 _) πM hπ n t).π.app j).op γ) := by
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  refine stageEval_eq_map E M m γ w y hy _ fun a ↦ ?_
  rw [Category.assoc, stageFibreProductCone_π_app, cechProductMap_toStageFamily_comp_π_left,
    cechProductLift_π_left_assoc, hby]

omit [IsAffine U.left] [∀ k, IsAffine (E.X k).left] [IsCofiltered Λ] in
/-- Two tuples with the same components have the same evaluation. -/
lemma stageEval_congr {n : ℕ} {t : Fin (n + 1) → E.I₀} {j : Λ}
    (γ : Q.obj
      (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j)))
    {W : X.ProEt} (w w' : W ⟶ U) (y y' : ∀ a, W ⟶ (M (t a)).obj j)
    (hy : ∀ a, y a ≫ (m (t a)).app j = w) (hy' : ∀ a, y' a ≫ (m (t a)).app j = w')
    (h : ∀ a, y a = y' a) : stageEval E M m γ w y hy = stageEval E M m γ w' y' hy' := by
  obtain rfl : y = y' := funext h
  obtain rfl : w = w' := (hy 0).symm.trans (hy' 0)
  rfl

end Stages

/-- The pair `(x, z)` of morphisms as a tuple indexed by `Fin 2`. -/
abbrev tuple₂ {C : Type*} [Category* C] {ι : Type*} {Z : ι → C} {W : C} {k l : ι}
    (x : W ⟶ Z k) (z : W ⟶ Z l) : ∀ a : Fin 2, W ⟶ Z (![k, l] a) :=
  Fin.cons x (Fin.cons z finZeroElim)

/-- The triple `(x, y, z)` of morphisms as a tuple indexed by `Fin 3`. -/
abbrev tuple₃ {C : Type*} [Category* C] {ι : Type*} {Z : ι → C} {W : C} {k k' l : ι}
    (x : W ⟶ Z k) (y : W ⟶ Z k') (z : W ⟶ Z l) : ∀ a : Fin 3, W ⟶ Z (![k, k', l] a) :=
  Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))

/-- If `x ≫ f k = w` and `z ≫ f l = w`, then every entry of `tuple₂ x z` composed with the
corresponding `f` is `w`. -/
lemma tuple₂_comp {C : Type*} [Category* C] {ι : Type*} {Z : ι → C} {W B : C} {k l : ι}
    {f : ∀ i, Z i ⟶ B} {w : W ⟶ B} (x : W ⟶ Z k) (z : W ⟶ Z l) (hx : x ≫ f k = w)
    (hz : z ≫ f l = w) (a : Fin 2) : tuple₂ x z a ≫ f (![k, l] a) = w := by
  fin_cases a
  exacts [hx, hz]

/-- If `x`, `y` and `z` all compose with the corresponding `f` to `w`, then so does every entry of
`tuple₃ x y z`. -/
lemma tuple₃_comp {C : Type*} [Category* C] {ι : Type*} {Z : ι → C} {W B : C} {k k' l : ι}
    {f : ∀ i, Z i ⟶ B} {w : W ⟶ B} (x : W ⟶ Z k) (y : W ⟶ Z k') (z : W ⟶ Z l)
    (hx : x ≫ f k = w) (hy : y ≫ f k' = w) (hz : z ≫ f l = w) (a : Fin 3) :
    tuple₃ x y z a ≫ f (![k, k', l] a) = w := by
  fin_cases a
  exacts [hx, hy, hz]

section Coboundary

variable {X} {U : X.ProEt} [IsAffine U.left] (E : PreZeroHypercover.{u} U)
  {Λ : Type u} [SmallCategory Λ] [IsCofiltered Λ] (M : E.I₀ → Λ ⥤ X.ProEt)
  (m : ∀ k, M k ⟶ (Functor.const Λ).obj U) {Q : X.ProEtᵒᵖ ⥤ Type*}

/-- The projection of an iterated fibre product at a stage to one of its factors. -/
abbrev stageπ {n : ℕ} (t : Fin (n + 1) → E.I₀) (j : Λ) (a : Fin (n + 1)) :
    (stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j ⟶ (M (t a)).obj j :=
  (Pi.π (fun a ↦ Over.mk ((stageFamily E ((Functor.const Λ).obj U) M m j).f (t a))) a).left

/-- The structure morphism of an iterated fibre product at a stage. -/
abbrev stageBase {n : ℕ} (t : Fin (n + 1) → E.I₀) (j : Λ) :
    (stageFibreProduct E ((Functor.const Λ).obj U) M m n t).obj j ⟶ U :=
  (∏ᶜ fun a ↦ Over.mk ((stageFamily E ((Functor.const Λ).obj U) M m j).f (t a))).hom

omit [IsAffine U.left] [IsCofiltered Λ] in
/-- The projection `stageπ` to a factor, composed with the structure morphism of that factor, is
the structure morphism `stageBase` of the iterated fibre product. -/
lemma stageπ_comp {n : ℕ} (t : Fin (n + 1) → E.I₀) (j : Λ) (a : Fin (n + 1)) :
    stageπ E M m t j a ≫ (m (t a)).app j = stageBase E M m t j :=
  Over.w (Pi.π (fun a ↦ Over.mk ((stageFamily E ((Functor.const Λ).obj U) M m j).f (t a))) a)

/-- A family of sections over the double fibre products at a stage, evaluated on the pair of
factors `(i, i')` of a triple fibre product. -/
def stagePairEval {j : Λ}
    (γ : ∀ t : Fin 2 → E.I₀, Q.obj
      (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m 1 t).obj j)))
    (τ : Fin 3 → E.I₀) (i i' : Fin 3) :
    Q.obj (op ((stageFibreProduct E ((Functor.const Λ).obj U) M m 2 τ).obj j)) :=
  stageEval E M m (γ ![τ i, τ i']) (stageBase E M m τ j)
    (tuple₂ (Z := fun k ↦ (M k).obj j) (stageπ E M m τ j i) (stageπ E M m τ j i'))
    (tuple₂_comp (f := fun k ↦ (m k).app j) _ _ (stageπ_comp E M m τ j i)
      (stageπ_comp E M m τ j i'))

end Coboundary

/-! ### Étale local triviality of torsors under `ε⁻¹G` -/

variable {X} in
/-- **Pseudo-torsors with sections pro-étale locally have sections étale locally, over an
affine object.** Let `H` be a sheaf of groups on `X_proétale` whose underlying sheaf of sets is
the inverse image `ε⁻¹F` of a sheaf of sets on `X_étale` (for instance `H = ε⁻¹G` for a sheaf of
groups `G` on `X_étale`), and let `T` be a pseudo-`H`-torsor. If `T` has sections on a pro-étale
covering of an affine object `U` of `X_étale`, then it has sections on an étale covering of `U`. -/
theorem exists_covering_nonempty_of_isAffine
    (H : SheafOfGroups.{max (u + 1) v} (Scheme.ProEt.topology X))
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (e : H.presheaf ≅ ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj)
    (T : PseudoTorsor.{max (u + 1) v} H) (U : X.Etale) [IsAffine U.left]
    (hT : ∃ S ∈ Scheme.ProEt.topology X (X.etaleToProetale.obj U),
      ∀ ⦃V : X.ProEt⦄ ⦃f : V ⟶ X.etaleToProetale.obj U⦄, S f → Nonempty (T.presheaf.obj (op V))) :
    ∃ S ∈ X.smallEtaleTopology U, ∀ ⦃V : X.Etale⦄ ⦃f : V ⟶ U⦄, S f →
      Nonempty (T.presheaf.obj (op (X.etaleToProetale.obj V))) := by
  classical
  let U' := X.etaleToProetale.obj U
  have : IsAffine U'.left := ‹IsAffine U.left›
  -- a finite covering by affine objects ind-étale over `U` trivializing `T`
  let R : Sieve U' :=
    { arrows := fun V _ => Nonempty (T.presheaf.obj (op V))
      downward_closed := fun ⟨s⟩ h => ⟨T.presheaf.map h.op s⟩ }
  have hR : R ∈ Scheme.ProEt.topology X U' := by
    obtain ⟨S, hS, hs⟩ := hT
    exact (Scheme.ProEt.topology X).superset_covering (fun V g hg => hs hg) hS
  obtain ⟨E, hfin, hE, hER, hEaff⟩ := exists_indEtale_covering_le R hR
  have := hfin
  have : ∀ k, IsAffine (E.X k).left := fun k => (hEaff k).1
  let s : ∀ k, T.presheaf.obj (op (E.X k)) := fun k => Classical.choice (hER _ (E.sieve₀_f k))
  obtain ⟨Λ, _, _, M, m, πM, hπ, ⟨hB⟩, hM, hMa, hMe⟩ :=
    exists_cofilteredSystem_of_indEtale E (fun k => (hEaff k).2)
  let B := (Functor.const Λ).obj U'
  let hM' := fun k => (hM k).some
  -- the cocycle of the trivializations over the double fibre products
  let pr (n : ℕ) (t : Fin (n + 1) → E.I₀) (a : Fin (n + 1)) :
      (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left ⟶ E.X (t a) :=
    (Pi.π (fun a ↦ Over.mk (E.f (t a))) a).left
  let g (t : Fin 2 → E.I₀) : H.presheaf.obj (op (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left) :=
    (T.sectionEquivGroup _ (T.presheaf.map (pr 1 t 0).op (s (t 0)))).symm
      (T.presheaf.map (pr 1 t 1).op (s (t 1)))
  -- Stacks 099S: the cocycle comes from a stage
  let j₀ : Λ := (IsCofiltered.nonempty (C := Λ)).some
  have hmono₁ : ∀ (t : Fin 2 → E.I₀) {j j' : Λ} (f : j' ⟶ j),
      (∃ γ : H.presheaf.obj (op ((stageFibreProduct E B M m 1 t).obj j)),
        H.presheaf.map ((stageFibreProductCone E B M m (𝟙 _) πM hπ 1 t).π.app j).op γ = g t) →
      ∃ γ : H.presheaf.obj (op ((stageFibreProduct E B M m 1 t).obj j')),
        H.presheaf.map ((stageFibreProductCone E B M m (𝟙 _) πM hπ 1 t).π.app j').op γ = g t :=
    fun t j j' f ⟨γ, hγ⟩ => ⟨H.presheaf.map ((stageFibreProduct E B M m 1 t).map f).op γ,
      by rw [← FunctorToTypes.map_comp_apply, ← op_comp, Cone.w]; exact hγ⟩
  obtain ⟨j₁, -, hj₁⟩ := Stacks.FilteredColimit.exists_hom_forall_of_finite (K := Λᵒᵖ) (op j₀)
    (fun t j _ => ∃ γ : H.presheaf.obj (op ((stageFibreProduct E B M m 1 t).obj j.unop)),
      H.presheaf.map ((stageFibreProductCone E B M m (𝟙 _) πM hπ 1 t).π.app j.unop).op γ = g t)
    (fun t _ _ _ f h => hmono₁ t f.unop h)
    (fun t => by
      obtain ⟨j, γ, hγ⟩ := exists_stage_map_eq_of_iso E M m πM hπ hMa hB hM' F e 1 t (g t)
      exact ⟨op (IsCofiltered.min j j₀), (IsCofiltered.minToRight j j₀).op,
        hmono₁ t (IsCofiltered.minToLeft j j₀) ⟨γ, hγ⟩⟩)
  choose γ₁ hγ₁ using hj₁
  let j1 : Λ := j₁.unop
  let P (n : ℕ) (t : Fin (n + 1) → E.I₀) : Λ ⥤ X.ProEt := stageFibreProduct E B M m n t
  -- the stage cochain, evaluated at maps coming from the members of `E`, is the cocycle
  have hrestr : ∀ (k₁ k₂ : E.I₀) {W : X.ProEt} (c : W ⟶ U') (x : W ⟶ E.X k₁)
      (z : W ⟶ E.X k₂) (hx : x ≫ E.f k₁ = c) (hz : z ≫ E.f k₂ = c)
      (y₁ : W ⟶ (M k₁).obj j1) (y₂ : W ⟶ (M k₂).obj j1)
      (hy₁ : x ≫ (πM k₁).app j1 = y₁) (hy₂ : z ≫ (πM k₂).app j1 = y₂)
      (hy : ∀ a, tuple₂ (Z := fun i ↦ (M i).obj j1) y₁ y₂ a ≫ (m (![k₁, k₂] a)).app j1 = c),
      stageEval E M m (γ₁ ![k₁, k₂]) c (tuple₂ (Z := fun i ↦ (M i).obj j1) y₁ y₂) hy =
        (T.sectionEquivGroup (op W) (T.presheaf.map x.op (s k₁))).symm
          (T.presheaf.map z.op (s k₂)) := by
    intro k₁ k₂ W c x z hx hz y₁ y₂ hy₁ hy₂ hy
    have hxz : ∀ a, tuple₂ (Z := E.X) x z a ≫ E.f (![k₁, k₂] a) = c := tuple₂_comp _ _ hx hz
    rw [stageEval_comp_πM E M m πM hπ (γ₁ ![k₁, k₂]) c (tuple₂ (Z := E.X) x z) hxz _ hy
      (fun a ↦ by fin_cases a; exacts [hy₁, hy₂])]
    show H.presheaf.map _ (H.presheaf.map _ _) = _
    rw [hγ₁ ![k₁, k₂]]
    show H.presheaf.map _ ((T.sectionEquivGroup _ _).symm _) = _
    rw [T.map_sectionEquivGroup_symm, ← FunctorToTypes.map_comp_apply,
      ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp]
    exact congrArg₂ (fun a b ↦ (T.sectionEquivGroup (op W)
        (T.presheaf.map (Quiver.Hom.op a) (s k₁))).symm (T.presheaf.map (Quiver.Hom.op b) (s k₂)))
      (cechProductLift_π_left E 1 ![k₁, k₂] c _ hxz 0)
      (cechProductLift_π_left E 1 ![k₁, k₂] c _ hxz 1)
  -- the coboundary of the stage cochain over the triple fibre products at the stage
  let Γ (τ : Fin 3 → E.I₀) (i i' : Fin 3) : H.presheaf.obj (op ((P 2 τ).obj j1)) :=
    stagePairEval E M m γ₁ τ i i'
  let cob (τ : Fin 3 → E.I₀) : H.presheaf.obj (op ((P 2 τ).obj j1)) :=
    Γ τ 1 2 * Γ τ 0 1 * (Γ τ 0 2)⁻¹
  have hcob : ∀ τ, H.presheaf.map ((stageFibreProductCone E B M m (𝟙 _) πM hπ 2 τ).π.app j1).op
      (cob τ) = H.presheaf.map ((stageFibreProductCone E B M m (𝟙 _) πM hπ 2 τ).π.app j1).op 1 := by
    intro τ
    let κ := (stageFibreProductCone E B M m (𝟙 _) πM hπ 2 τ).π.app j1
    let c₃ := (∏ᶜ fun a ↦ Over.mk (E.f (τ a))).hom
    have hpr : ∀ a, pr 2 τ a ≫ E.f (τ a) = c₃ := fun a ↦
      Over.w (Pi.π (fun a ↦ Over.mk (E.f (τ a))) a)
    have hκ : ∀ a, κ ≫ stageπ E M m τ j1 a = pr 2 τ a ≫ (πM (τ a)).app j1 := fun a ↦
      cechProductMap_toStageFamily_comp_π_left E B M m (𝟙 _) πM hπ j1 2 τ a
    have hΓ : ∀ i i', H.presheaf.map κ.op (Γ τ i i') =
        (T.sectionEquivGroup (op _) (T.presheaf.map (pr 2 τ i).op (s (τ i)))).symm
          (T.presheaf.map (pr 2 τ i').op (s (τ i'))) := by
      intro i i'
      have hc : ∀ a, (pr 2 τ a ≫ (πM (τ a)).app j1) ≫ (m (τ a)).app j1 = c₃ := fun a ↦ by
        rw [Category.assoc, hπ]
        simpa using hpr a
      have hy : ∀ a, tuple₂ (Z := fun k ↦ (M k).obj j1) (pr 2 τ i ≫ (πM (τ i)).app j1)
          (pr 2 τ i' ≫ (πM (τ i')).app j1) a ≫ (m (![τ i, τ i'] a)).app j1 = c₃ :=
        tuple₂_comp (f := fun k ↦ (m k).app j1) _ _ (hc i) (hc i')
      refine (map_stageEval E M m _ κ _ _ _ c₃ _ hy
        (fun a ↦ by fin_cases a; exacts [hκ i, hκ i'])).trans ?_
      exact hrestr (τ i) (τ i') c₃ (pr 2 τ i) (pr 2 τ i') (hpr i) (hpr i') _ _ rfl rfl hy
    show H.presheaf.map κ.op (Γ τ 1 2 * Γ τ 0 1 * (Γ τ 0 2)⁻¹) = H.presheaf.map κ.op 1
    rw [H.map_mul, H.map_mul, ← H.presheafMapHom_apply κ.op (Γ τ 0 2)⁻¹, map_inv,
      H.presheafMapHom_apply, hΓ, hΓ, hΓ, T.sectionEquivGroup_symm_mul,
      mul_inv_cancel, SheafOfGroups.map_one (G := H)]
  -- Stacks 099S: the coboundary vanishes at a later stage
  have hmono₂ : ∀ (τ : Fin 3 → E.I₀) {j j' : Λ} (f : j ⟶ j1) (f' : j' ⟶ j),
      H.presheaf.map ((P 2 τ).map f).op (cob τ) = H.presheaf.map ((P 2 τ).map f).op 1 →
      H.presheaf.map ((P 2 τ).map (f' ≫ f)).op (cob τ) =
        H.presheaf.map ((P 2 τ).map (f' ≫ f)).op 1 := by
    intro τ j j' f f' h
    rw [Functor.map_comp, op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply,
      h]
  obtain ⟨jμ, gop, hμ⟩ := Stacks.FilteredColimit.exists_hom_forall_of_finite (K := Λᵒᵖ) (op j1)
    (fun τ _ f => H.presheaf.map ((P 2 τ).map f.unop).op (cob τ) =
      H.presheaf.map ((P 2 τ).map f.unop).op 1)
    (fun τ _ _ f f' h => hmono₂ τ f.unop f'.unop h)
    (fun τ => by
      obtain ⟨i, g, hg⟩ := exists_stage_map_eq_map_of_iso E M m πM hπ hMa hB hM' F e 2 τ j1 (cob τ)
        (1 : H.presheaf.obj (op ((P 2 τ).obj j1))) (hcob τ)
      exact ⟨op i, g.op, hg⟩)
  let μ : Λ := jμ.unop
  let g : μ ⟶ j1 := gop.unop
  -- the descended cocycle at the stage `μ`
  have hπμ : ∀ k, (πM k).app μ ≫ (m k).app μ = E.f k := fun k ↦ by
    simpa using hπ k μ
  let γ (k l : E.I₀) {W : X.ProEt} (x : W ⟶ (M k).obj μ) (z : W ⟶ (M l).obj μ)
      (hxz : x ≫ (m k).app μ = z ≫ (m l).app μ) : H.presheaf.obj (op W) :=
    stageEval E M m (j := μ) (t := ![k, l])
      (H.presheaf.map ((P 1 ![k, l]).map g).op (γ₁ ![k, l])) (x ≫ (m k).app μ)
      (tuple₂ (Z := fun k ↦ (M k).obj μ) x z)
      (tuple₂_comp (f := fun k ↦ (m k).app μ) x z rfl hxz.symm)
  have hmn : ∀ i, (M i).map g ≫ (m i).app j1 = (m i).app μ := fun i ↦ by
    simp
  have hγ : ∀ (k l : E.I₀) {W : X.ProEt} (x : W ⟶ (M k).obj μ) (z : W ⟶ (M l).obj μ)
      (hxz : x ≫ (m k).app μ = z ≫ (m l).app μ),
      γ k l x z hxz = stageEval E M m (j := j1) (γ₁ ![k, l]) (x ≫ (m k).app μ)
        (tuple₂ (Z := fun k ↦ (M k).obj j1) (x ≫ (M k).map g) (z ≫ (M l).map g))
        (tuple₂_comp (f := fun k ↦ (m k).app j1) _ _
          (by rw [Category.assoc, hmn]) (by rw [Category.assoc, hmn, hxz])) := by
    intro k l W x z hxz
    exact stageEval_map_transition E M m g _ _ _ _ _ _ (fun a ↦ by fin_cases a <;> rfl)
  have hnat : ∀ (k l : E.I₀) {W W' : X.ProEt} (h : W' ⟶ W) (x : W ⟶ (M k).obj μ)
      (z : W ⟶ (M l).obj μ) (hxz : x ≫ (m k).app μ = z ≫ (m l).app μ),
      γ k l (h ≫ x) (h ≫ z) (by rw [Category.assoc, Category.assoc, hxz]) =
        H.presheaf.map h.op (γ k l x z hxz) := by
    intro k l W W' h x z hxz
    exact (map_stageEval E M m _ h _ _ _ _ _ _ (fun a ↦ by fin_cases a <;> rfl)).symm
  have hlift : ∀ (k l : E.I₀) {W : X.ProEt} (a : W ⟶ E.X k) (b : W ⟶ E.X l)
      (hab : a ≫ E.f k = b ≫ E.f l),
      T.act (op W) (γ k l (a ≫ (πM k).app μ) (b ≫ (πM l).app μ)
          (by rw [Category.assoc, Category.assoc, hπμ, hπμ, hab]))
        (T.presheaf.map a.op (s k)) = T.presheaf.map b.op (s l) := by
    intro k l W a b hab
    rw [hγ k l _ _ (by rw [Category.assoc, Category.assoc, hπμ, hπμ, hab])]
    have hn : ∀ i, (πM i).app μ ≫ (M i).map g = (πM i).app j1 := fun i ↦ by
      simpa using ((πM i).naturality g).symm
    rw [hrestr k l ((a ≫ (πM k).app μ) ≫ (m k).app μ) a b
      (by rw [Category.assoc, hπμ]) (by rw [Category.assoc, hπμ, hab]) _ _
      (by rw [Category.assoc, hn]) (by rw [Category.assoc, hn])]
    exact (T.sectionEquivGroup _ _).apply_symm_apply _
  have hcocycle : ∀ (k k' l : E.I₀) {W : X.ProEt} (x : W ⟶ (M k).obj μ)
      (y : W ⟶ (M k').obj μ) (z : W ⟶ (M l).obj μ)
      (hxy : x ≫ (m k).app μ = y ≫ (m k').app μ) (hyz : y ≫ (m k').app μ = z ≫ (m l).app μ),
      γ k l x z (hxy.trans hyz) = γ k' l y z hyz * γ k k' x y hxy := by
    intro k k' l W x y z hxy hyz
    let τ : Fin 3 → E.I₀ := ![k, k', l]
    have hy₃ : ∀ a, tuple₃ (Z := fun k ↦ (M k).obj μ) x y z a ≫ (m (τ a)).app μ =
        x ≫ (m k).app μ :=
      tuple₃_comp (f := fun k ↦ (m k).app μ) x y z rfl hxy.symm (hxy.trans hyz).symm
    let ℓ := cechProductLift (stageFamily E B M m μ) 2 τ (x ≫ (m k).app μ)
      (tuple₃ (Z := fun k ↦ (M k).obj μ) x y z) hy₃
    have hℓ : ∀ a, (ℓ ≫ (P 2 τ).map g) ≫ stageπ E M m τ j1 a =
        tuple₃ (Z := fun k ↦ (M k).obj μ) x y z a ≫ (M (τ a)).map g := fun a ↦ by
      rw [Category.assoc, stageFibreProduct_map, cechProductMap_stageFamilyHomOver_comp_π_left,
        cechProductLift_π_left_assoc]
    have hbase : (ℓ ≫ (P 2 τ).map g) ≫ stageBase E M m τ j1 = x ≫ (m k).app μ := by
      rw [← stageπ_comp E M m τ j1 0, ← Category.assoc, hℓ 0, Category.assoc, hmn]
      rfl
    have hΓ : ∀ (i i' : Fin 3) (hii' : (tuple₃ (Z := fun k ↦ (M k).obj μ) x y z i) ≫
        (m (τ i)).app μ = (tuple₃ (Z := fun k ↦ (M k).obj μ) x y z i') ≫ (m (τ i')).app μ)
        (hi : (tuple₃ (Z := fun k ↦ (M k).obj μ) x y z i) ≫ (m (τ i)).app μ = x ≫ (m k).app μ),
        H.presheaf.map (ℓ ≫ (P 2 τ).map g).op (Γ τ i i') =
          γ (τ i) (τ i') (tuple₃ (Z := fun k ↦ (M k).obj μ) x y z i)
            (tuple₃ (Z := fun k ↦ (M k).obj μ) x y z i') hii' := by
      intro i i' hii' hi
      rw [hγ _ _ _ _ hii']
      exact map_stageEval E M m _ (ℓ ≫ (P 2 τ).map g) _ _ _ _ _ _
        (fun a ↦ by fin_cases a; exacts [hℓ i, hℓ i'])
    have h1 := hμ τ
    change H.presheaf.map ((P 2 τ).map g).op (cob τ) = H.presheaf.map ((P 2 τ).map g).op 1 at h1
    have h2 := congrArg (H.presheaf.map ℓ.op) h1
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp,
      SheafOfGroups.map_one (G := H)] at h2
    change H.presheaf.map (ℓ ≫ (P 2 τ).map g).op (Γ τ 1 2 * Γ τ 0 1 * (Γ τ 0 2)⁻¹) = 1 at h2
    rw [H.map_mul, H.map_mul, ← H.presheafMapHom_apply (ℓ ≫ (P 2 τ).map g).op (Γ τ 0 2)⁻¹,
      map_inv, H.presheafMapHom_apply, hΓ 1 2 hyz hxy.symm, hΓ 0 1 hxy rfl,
      hΓ 0 2 (hxy.trans hyz) rfl] at h2
    exact (mul_inv_eq_one.1 h2).symm
  have hsec := fun l ↦ PseudoTorsor.nonempty_of_cocycle (T := T) (E := E) (s := s)
    (m := fun k ↦ (m k).app μ) (π := fun k ↦ (πM k).app μ) (hπ := fun k ↦ hπμ k) (γ := γ) hE
    hnat hlift hcocycle l
  -- the stages at `μ` form an étale covering of `U`
  have hMet : ∀ l, Etale (((m l).app μ).left ≫ U.hom) := fun l ↦
    have : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    MorphismProperty.comp_mem @Etale _ _ (hMe l μ) U.prop
  let Wl (l : E.I₀) : X.Etale := @Scheme.Etale.mk _ _ (((m l).app μ).left ≫ U.hom) (hMet l)
  let wl (l : E.I₀) : Wl l ⟶ U := MorphismProperty.Over.homMk ((m l).app μ).left rfl
  let el (l : E.I₀) : X.etaleToProetale.obj (Wl l) ⟶ (M l).obj μ :=
    MorphismProperty.Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ ((M l).obj μ).hom = ((m l).app μ).left ≫ U.hom
      rw [Category.id_comp]
      exact (MorphismProperty.Over.w ((m l).app μ)).symm)
  refine ⟨Sieve.ofArrows Wl wl, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨V, h, hh, y, rfl⟩ := Scheme.ProEt.exists_mem_range_of_mem_topology hE x
    obtain ⟨_, a, _, ⟨k⟩, rfl⟩ := hh
    refine Set.mem_iUnion.2 ⟨k, (a ≫ (πM k).app μ).left y, ?_⟩
    show ((a ≫ (πM k).app μ) ≫ (m k).app μ).left y = (a ≫ E.f k).left y
    rw [Category.assoc, hπμ]
  · rintro V f ⟨_, h, _, ⟨l⟩, rfl⟩
    obtain ⟨t⟩ := hsec l
    exact ⟨T.presheaf.map (X.etaleToProetale.map h ≫ el l).op t⟩


variable {X} in
/-- **Pseudo-torsors with sections pro-étale locally have sections étale locally.** Let `H` be a
sheaf of groups on `X_proétale` whose underlying sheaf of sets is the inverse image `ε⁻¹F` of a
sheaf of sets on `X_étale`, and let `T` be a pseudo-`H`-torsor. If `T` has sections on a pro-étale
covering of an object `U` of `X_étale`, then it has sections on an étale covering of `U`: this
holds over the affine objects (`AlgebraicGeometry.ProEtale.exists_covering_nonempty_of_isAffine`),
which cover `U`. -/
theorem exists_covering_nonempty
    (H : SheafOfGroups.{max (u + 1) v} (Scheme.ProEt.topology X))
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (e : H.presheaf ≅ ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj)
    (T : PseudoTorsor.{max (u + 1) v} H) (U : X.Etale)
    (hT : ∃ S ∈ Scheme.ProEt.topology X (X.etaleToProetale.obj U),
      ∀ ⦃V : X.ProEt⦄ ⦃f : V ⟶ X.etaleToProetale.obj U⦄, S f → Nonempty (T.presheaf.obj (op V))) :
    ∃ S ∈ X.smallEtaleTopology U, ∀ ⦃V : X.Etale⦄ ⦃f : V ⟶ U⦄, S f →
      Nonempty (T.presheaf.obj (op (X.etaleToProetale.obj V))) := by
  let S : Sieve U :=
    { arrows := fun V _ => Nonempty (T.presheaf.obj (op (X.etaleToProetale.obj V)))
      downward_closed := fun ⟨t⟩ h => ⟨T.presheaf.map (X.etaleToProetale.map h).op t⟩ }
  refine ⟨S, ?_, fun V f hf => hf⟩
  obtain ⟨P, hP, hPaff⟩ := exists_affine_presieve_mem_smallEtaleTopology X U
  refine X.smallEtaleTopology.transitive hP S fun W f hf => ?_
  obtain ⟨W', h, f', hf', rfl⟩ := hf
  have : IsAffine W'.left := hPaff f' hf'
  obtain ⟨R, hR, hr⟩ := hT
  obtain ⟨S', hS', hs'⟩ := exists_covering_nonempty_of_isAffine H F e T W'
    ⟨R.pullback (X.etaleToProetale.map f'),
      (Scheme.ProEt.topology X).pullback_stable _ hR, fun _ _ hg => hr hg⟩
  rw [Sieve.pullback_comp]
  exact X.smallEtaleTopology.pullback_stable h
    (X.smallEtaleTopology.superset_covering (fun V g hg => hs' hg) hS')

variable {X} in
/-- **Torsors under `ε⁻¹G` have sections étale locally.** Let `G` be a sheaf of groups on
`X_étale` and `T` an `ε⁻¹G`-torsor on `X_proétale`. Every object `U` of `X_étale` has an étale
covering by objects over which `T` has a section. -/
theorem exists_covering_nonempty_of_isTorsor
    (G : SheafOfGroups.{max (u + 1) v} X.smallEtaleTopology)
    (T : PseudoTorsor.{max (u + 1) v} (G.map
      (Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X))))
    (hT : T.IsTorsor) (U : X.Etale) :
    ∃ S ∈ X.smallEtaleTopology U, ∀ ⦃V : X.Etale⦄ ⦃f : V ⟶ U⦄, S f →
      Nonempty (T.presheaf.obj (op (X.etaleToProetale.obj V))) :=
  exists_covering_nonempty _ G.sheaf (Iso.refl _) T U (hT _)

/-! ### Stacks 099X -/

/-- **Stacks 099X.** Let `X` be a scheme and `G` a sheaf of (possibly non-commutative) groups on
`X_étale`. The inverse image `ε⁻¹` along the inclusion of the small étale site into the small
pro-étale site induces a bijection `H¹(X_étale, G) → H¹(X_proétale, ε⁻¹G)` of the sets of
isomorphism classes of torsors.

`H¹` is `SheafOfGroups.TorsorClasses`, the set of isomorphism classes of torsors (Stacks,
Cohomology on Sites, Section 21.4); the map sends the class of a `G`-torsor `F` to the class of the
`ε⁻¹G`-torsor `ε⁻¹F`. -/
theorem bijective_torsorClassesMap (G : SheafOfGroups.{max (u + 1) v} X.smallEtaleTopology) :
    Function.Bijective (SheafOfGroups.TorsorClasses.map (G := G)
      (Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X))) :=
  have := Scheme.isIso_proetaleInverseImageAdjunction_unit.{u, v} X
  SheafOfGroups.TorsorClasses.map_bijective_of_adjunction X.etaleToProetale
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X))
    (fun T hT U => exists_covering_nonempty_of_isTorsor G T hT U)

/-- The identification `H¹(X_étale, G) = H¹(X_proétale, ε⁻¹G)` of Stacks 099X, as an
equivalence of sets. -/
def torsorClassesEquiv (G : SheafOfGroups.{max (u + 1) v} X.smallEtaleTopology) :
    SheafOfGroups.TorsorClasses.{max (u + 1) v} G ≃
      SheafOfGroups.TorsorClasses.{max (u + 1) v} (G.map
        (Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X))) :=
  Equiv.ofBijective _ (bijective_torsorClassesMap X G)

/-- The equivalence of Stacks 099X sends the class of a torsor to the class of its inverse
image. -/
theorem torsorClassesEquiv_mk (G : SheafOfGroups.{max (u + 1) v} X.smallEtaleTopology)
    (F : PseudoTorsor.{max (u + 1) v} G) (hF : F.IsTorsor) :
    torsorClassesEquiv X G (SheafOfGroups.TorsorClasses.mk F hF) =
      SheafOfGroups.TorsorClasses.mk
        (F.map (Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)))
        (PseudoTorsor.isTorsor_map _ hF) :=
  rfl

end AlgebraicGeometry.ProEtale

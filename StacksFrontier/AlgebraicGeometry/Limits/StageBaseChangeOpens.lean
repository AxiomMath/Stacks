module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Opens of a base change of a limit of schemes come from a stage

Let `D : I ⥤ Scheme` be a cofiltered diagram of schemes with affine transition morphisms, let `c`
be a limit cone with vertex `X = lim D`, and let `n : N ⟶ D i` be a morphism into one stage.
Base change along `n` turns the cone into a cone with vertex `X ×_{D i} N` over the diagram
`j ↦ D j ×_{D i} N` indexed by the objects `j` over `i`; that cone is again a limit cone, and its
transition morphisms are again affine. Consequently the preimages of affine opens of the stages
`D j ×_{D i} N` form a basis of the topology of `X ×_{D i} N`.

The form in which this is used: if a point `(x, t)` of `X ×_{D i} N`, given by a morphism `x`
into the limit and a morphism `t` into `N`, lies in an open `O`, then so does every point
`(x', t)` with the same second component for which `x'` agrees with `x` at a sufficiently late
stage.

## Main definitions

* `AlgebraicGeometry.stageBaseChangeDiagram` — the diagram `j ↦ D j ×_{D i} N` over `Over i`.
* `AlgebraicGeometry.stageBaseChangeCone` — its cone with vertex `X ×_{D i} N`.

## Main results

* `AlgebraicGeometry.stageBaseChangeConeIsLimit` — that cone is a limit cone.
* `AlgebraicGeometry.stageBaseChangeDiagram_map_isAffineHom` — its transition morphisms are
  affine.
* `AlgebraicGeometry.exists_stage_forall_lift_mem_of_isLimit` — membership of a point in an open
  of `X ×_{D i} N` is decided at a finite stage.

## Implementation notes

The diagram and the cone are written with explicit fibre products, so that their objects are the
fibre products `pullback (D.map j.hom) N` on the nose. The limit statement is Mathlib's
`CategoryTheory.Limits.isLimitOfIsPullbackOfIsConnected`, as in Mathlib's
`AlgebraicGeometry.isLimitOpensCone`; the basis statement is Mathlib's
`AlgebraicGeometry.isBasis_preimage_isAffineOpen` applied to the new diagram.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The base change `j ↦ D j ×_{D i} N` of the part of a diagram over `i` along a morphism
`n : N ⟶ D i`. -/
abbrev stageBaseChangeDiagram (i : I) (X : Over (D.obj i)) : Over i ⥤ Scheme.{u} where
  obj j := pullback (D.map j.hom) X.hom
  map {j k} φ := pullback.lift (pullback.fst _ _ ≫ D.map φ.left) (pullback.snd _ _)
    (by rw [Category.assoc, ← D.map_comp, Over.w φ, pullback.condition])
  map_id j := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simp
    · rw [pullback.lift_snd]
      simp
  map_comp φ ψ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Over.comp_left, Functor.map_comp, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- The first projections `D j ×_{D i} N ⟶ D j`. -/
abbrev stageBaseChangeDiagramι (i : I) (X : Over (D.obj i)) :
    stageBaseChangeDiagram D i X ⟶ Over.forget i ⋙ D where
  app j := pullback.fst (D.map j.hom) X.hom
  naturality _ _ _ := pullback.lift_fst _ _ _

/-- The base change `X ×_{D i} N` of the cone, as a cone over `j ↦ D j ×_{D i} N`. -/
abbrev stageBaseChangeCone (i : I) (X : Over (D.obj i)) :
    Cone (stageBaseChangeDiagram D i X) where
  pt := pullback (c.π.app i) X.hom
  π :=
    { app := fun j => pullback.lift (pullback.fst _ _ ≫ c.π.app j.left) (pullback.snd _ _)
        (by rw [Category.assoc, c.w, pullback.condition])
      naturality := fun j k φ => by
        apply pullback.hom_ext
        · change (𝟙 _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ =
            (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _
          rw [Category.id_comp, pullback.lift_fst, Category.assoc, pullback.lift_fst,
            pullback.lift_fst_assoc, Category.assoc, c.w]
        · change (𝟙 _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ _ =
            (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ _
          rw [Category.id_comp, pullback.lift_snd, Category.assoc, pullback.lift_snd,
            pullback.lift_snd] }

/-- The projection `X ×_{D i} N ⟶ X`, as a morphism of cones over the first projections. -/
def stageBaseChangeConeHom (i : I) (X : Over (D.obj i)) :
    (Cone.postcompose (stageBaseChangeDiagramι D i X)).obj (stageBaseChangeCone D c i X) ⟶
      c.whisker (Over.forget i) where
  hom := pullback.fst (c.π.app i) X.hom
  w _ := (pullback.lift_fst _ _ _).symm

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

/-- **The base change of a limit along a morphism into a stage is a limit.** -/
def stageBaseChangeConeIsLimit [IsCofiltered I] (hc : IsLimit c) (i : I)
    (X : Over (D.obj i)) : IsLimit (stageBaseChangeCone D c i X) :=
  isLimitOfIsPullbackOfIsConnected (stageBaseChangeDiagramι D i X) _ _
    (stageBaseChangeConeHom D c i X)
    (fun j => by
      refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
        (IsPullback.of_hasPullback (D.map j.hom) X.hom).flip
      rw [pullback.lift_snd]
      exact (c.w j.hom).symm ▸ (IsPullback.of_hasPullback (c.π.app i) X.hom).flip)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

/-- The transition morphisms of the base-changed diagram are affine when those of the diagram
are. -/
lemma stageBaseChangeDiagram_map_isAffineHom [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) (X : Over (D.obj i)) {j k : Over i} (φ : j ⟶ k) :
    IsAffineHom ((stageBaseChangeDiagram D i X).map φ) := by
  have h : IsPullback ((stageBaseChangeDiagram D i X).map φ) (pullback.fst (D.map j.hom) X.hom)
      (pullback.fst (D.map k.hom) X.hom) (D.map φ.left) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (D.map k.hom) X.hom).flip
    rw [pullback.lift_snd, ← D.map_comp, Over.w φ]
    exact (IsPullback.of_hasPullback (D.map j.hom) X.hom).flip
  exact MorphismProperty.of_isPullback h.flip inferInstance

/-- **Membership in an open of a base change of a limit is decided at a finite stage.** Let
`O` be an open of `X_∞ ×_{D i} X`, where `X_∞ = lim D`, and let `(x, t)` be a `T`-valued point of
`X_∞ ×_{D i} X` whose image of the point `p` of `T` lies in `O`. Then there is a stage `j` over `i`
such that every `(x', t)` with `x'` agreeing with `x` at `j` also sends `p` into `O`. -/
theorem exists_stage_forall_lift_mem_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c) (i : I) (X : Over (D.obj i))
    (O : (pullback (c.π.app i) X.hom).Opens) {T : Scheme.{u}} (p : T)
    (x : T ⟶ c.pt) (t : T ⟶ X.left) (h : x ≫ c.π.app i = t ≫ X.hom)
    (hO : (pullback.lift x t h) p ∈ O) :
    ∃ (j : I) (_ : j ⟶ i), ∀ (x' : T ⟶ c.pt) (h' : x' ≫ c.π.app i = t ≫ X.hom),
      x' ≫ c.π.app j = x ≫ c.π.app j → (pullback.lift x' t h') p ∈ O := by
  have := stageBaseChangeDiagram_map_isAffineHom D
  obtain ⟨_, ⟨k, V, _, rfl⟩, hpV, hVO⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (isBasis_preimage_isAffineOpen _ _ (stageBaseChangeConeIsLimit D c hc i X))) hO
  refine ⟨k.left, k.hom, fun x' h' hx' => hVO ?_⟩
  have hπ : pullback.lift x' t h' ≫ (stageBaseChangeCone D c i X).π.app k =
      pullback.lift x t h ≫ (stageBaseChangeCone D c i X).π.app k := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact hx'
    · simp only [Category.assoc, pullback.lift_snd]
  have key : ((stageBaseChangeCone D c i X).π.app k) ((pullback.lift x' t h') p) =
      ((stageBaseChangeCone D c i X).π.app k) ((pullback.lift x t h) p) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hπ]
  refine (Scheme.Hom.mem_preimage (f := (stageBaseChangeCone D c i X).π.app k)).mpr ?_
  rw [key]
  exact (Scheme.Hom.mem_preimage (f := (stageBaseChangeCone D c i X).π.app k)).mp hpV

end AlgebraicGeometry

module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Basic

/-!
# Composing finite-type approximations

Noetherian approximation of a quasi-compact quasi-separated scheme `S` relative to a
quasi-compact open `U` is proved by adding one affine open at a time to `U`.  Chaining the
individual steps requires composing two approximations: one of a scheme `S₁` relative to an
open `U₁ ⊆ S₁`, and one of `S` relative to an open `V ⊆ S` identified with `S₁`, the latter
taken over the inverse system produced by the former.

## Main results

* `AlgebraicGeometry.initial_dual_functor_of_cofinal`: a monotone map between directed
  preorders with cofinal image induces an initial functor on the opposite categories, so
  restricting an inverse limit along it does not change the limit.
* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.comp`: the composite approximation.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.FiniteTypeApproximation.indexPreorder
  Scheme.FiniteTypeApproximation.indexNonempty Scheme.FiniteTypeApproximation.indexDirected

/-- A monotone map between preorders whose image is cofinal induces an initial functor between
the opposite categories, provided the source is directed and nonempty. -/
lemma initial_dual_functor_of_cofinal {I J : Type u} [Preorder I] [Preorder J]
    [Nonempty J] [IsDirected J (· ≤ ·)] (α : J →o I)
    (hα : ∀ i, ∃ j, i ≤ α j) : (α.monotone.dual.functor).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d ↦ ?_) (fun {d c} s s' ↦ ?_)
  · obtain ⟨j, hj⟩ := hα (OrderDual.ofDual d)
    exact ⟨OrderDual.toDual j, ⟨CategoryTheory.homOfLE hj⟩⟩
  · exact ⟨c, 𝟙 c, by rw [Subsingleton.elim s s']⟩

namespace Scheme.FiniteTypeApproximation

variable {I : Type u} [Preorder I] {D : Iᵒᵈ ⥤ Scheme.{u}}

/-- **Composition of finite-type approximations.**  Let `A₁` approximate `S₁` relative to an
open `U₁ ⊆ S₁` over the system `D`, and let `A₂` approximate `S` relative to an open
`V ⊆ S` over the system produced by `A₁`.  Suppose `e` identifies `V` with `S₁` compatibly
with the limiting cone of `A₁`, that `U ≤ V` is an open of `S` identified by the isomorphism
`ε` with `U₁`, and that the index map of `A₂` has cofinal image.  Then `S` is approximated
relative to `U` over `D`. -/
noncomputable def comp
    {S₁ : Scheme.{u}} {U₁ : S₁.Opens} {p₁ : (Functor.const Iᵒᵈ).obj (U₁ : Scheme.{u}) ⟶ D}
    (A₁ : FiniteTypeApproximation D S₁ U₁ p₁)
    {S : Scheme.{u}} {V : S.Opens}
    {p₂ : (Functor.const A₁.indexTypeᵒᵈ).obj (V : Scheme.{u}) ⟶ A₁.ambient}
    (A₂ : FiniteTypeApproximation A₁.ambient S V p₂)
    (e : (V : Scheme.{u}) ⟶ S₁) (he : ∀ j, e ≫ A₁.ambientCone.app j = p₂.app j)
    {U : S.Opens} (hUV : U ≤ V) (ε : (U : Scheme.{u}) ≅ (U₁ : Scheme.{u}))
    (hε : ε.hom ≫ U₁.ι = S.homOfLE hUV ≫ e)
    (hcofinal : ∀ i : A₁.indexType, ∃ j : A₂.indexType, i ≤ A₂.index j)
    {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D}
    (hp : ∀ i, p.app i = ε.hom ≫ p₁.app i) :
    FiniteTypeApproximation D S U p where
  indexType := A₂.indexType
  index := A₁.index.comp A₂.index
  ambient := A₂.ambient
  openPart := A₂.index.monotone.dual.functor ⋙ A₁.openPart
  inclusion :=
    Functor.whiskerLeft A₂.index.monotone.dual.functor A₁.inclusion ≫
      A₂.comparison.inv ≫ A₂.inclusion
  comparison := Functor.isoWhiskerLeft A₂.index.monotone.dual.functor A₁.comparison
  ambientCone := A₂.ambientCone
  openCone :=
    { app := fun j ↦ ε.hom ≫ A₁.openCone.app (A₂.index.monotone.dual.functor.obj j)
      naturality := fun {j j'} f ↦ by
        simpa using (A₁.openCone.naturality (A₂.index.monotone.dual.functor.map f)).symm ▸ rfl }
  transition_affine := A₂.transition_affine
  locallyOfFiniteType := A₂.locallyOfFiniteType
  quasiCompact := A₂.quasiCompact
  inclusion_isOpenImmersion := fun j ↦ by
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    have h₁ : IsOpenImmersion (A₁.inclusion.app (A₂.index.monotone.dual.functor.obj j)) :=
      A₁.inclusion_isOpenImmersion _
    have h₂ : IsOpenImmersion (A₂.comparison.inv.app j) := IsOpenImmersion.of_isIso _
    have h₃ : IsOpenImmersion (A₂.inclusion.app j) := A₂.inclusion_isOpenImmersion _
    exact MorphismProperty.comp_mem _ _ _ h₁ (MorphismProperty.comp_mem _ _ _ h₂ h₃)
  transition_isPullback := fun {j j'} f ↦ by
    have h₂ : IsPullback (A₁.ambient.map (A₂.index.monotone.dual.functor.map f))
        (A₂.comparison.inv.app j) (A₂.comparison.inv.app j') (A₂.openPart.map f) :=
      IsPullback.of_vert_isIso ⟨A₂.comparison.inv.naturality f⟩
    have h := ((A₁.transition_isPullback
      (A₂.index.monotone.dual.functor.map f)).paste_vert h₂).paste_vert
      (A₂.transition_isPullback f)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map, Functor.comp_obj,
      Category.assoc] at h ⊢
    exact h
  ambientCone_isLimit := A₂.ambientCone_isLimit
  openCone_isLimit := by
    have hinit : (A₂.index.monotone.dual.functor).Initial :=
      initial_dual_functor_of_cofinal A₂.index hcofinal
    have hc : IsLimit ((Cone.mk (U₁ : Scheme.{u}) A₁.openCone).whisker
        A₂.index.monotone.dual.functor) :=
      (Functor.Initial.isLimitWhiskerEquiv A₂.index.monotone.dual.functor _).symm
        A₁.openCone_isLimit
    exact IsLimit.ofIsoLimit hc (Cone.ext ε.symm fun j ↦ by simp)
  inclusion_compatibility := fun j ↦ by
    have hoc : e ≫ A₁.ambientCone.app (A₂.index.monotone.dual.functor.obj j) ≫
        A₂.comparison.inv.app j = A₂.openCone.app j := by
      rw [← Category.assoc, he, ← A₂.comparison_compatibility j, Category.assoc,
        A₂.comparison.hom_inv_id_app, Category.comp_id]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
    rw [← reassoc_of% (A₁.inclusion_compatibility (A₂.index.monotone.dual.functor.obj j)),
      reassoc_of% hε, reassoc_of% hoc, ← A₂.inclusion_compatibility j,
      Scheme.homOfLE_ι_assoc]
  comparison_compatibility := fun j ↦ by
    simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun g ↦ ε.hom ≫ g) (A₁.comparison_compatibility _)).trans (hp _).symm)

end Scheme.FiniteTypeApproximation

end AlgebraicGeometry

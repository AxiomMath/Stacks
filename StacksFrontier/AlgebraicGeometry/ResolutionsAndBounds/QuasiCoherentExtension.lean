module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Subobject.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BiproductQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.GraphKernel

/-!
# Extending quasi-coherent modules across a quasi-compact open immersion

Let `j : U ⟶ X` be a quasi-compact open immersion of schemes, `F` a quasi-coherent module on `X`
and `G` a quasi-coherent module on `U` with a map `φ : G ⟶ j⁻¹F`. The *graph kernel* of `φ` is
the kernel of the difference of the adjunction unit `F ⟶ j_*j⁻¹F` and the pushforward of `φ`; it
is a quasi-coherent module on `X` whose restriction to `U` is `G` and whose projection to `F`
restricts to `φ`. This is the construction behind Stacks 01PE: both a morphism of quasi-coherent
modules and a quasi-coherent submodule defined on a quasi-compact open extend to the whole
scheme.

## Main definitions

* `AlgebraicGeometry.graphKernelMap` is the difference of the adjunction unit on `F` and the
  pushforward of `φ`, out of the direct sum `F ⊞ j_*G`.
* `AlgebraicGeometry.graphKernel` is its kernel, and `AlgebraicGeometry.graphKernelProjection`
  its first projection to `F`.

## Main results

* `AlgebraicGeometry.graphKernel_isQuasicoherent`: the graph kernel is quasi-coherent.
* `AlgebraicGeometry.graphKernelPullbackIso` identifies its restriction to `U` with `G`, and
  `AlgebraicGeometry.graphKernelPullbackIso_hom_comp` says that under this identification the
  restricted projection is `φ`.
* `AlgebraicGeometry.graphKernelProjection_mono`: the projection is injective when `φ` is.
* `AlgebraicGeometry.exists_quasicoherent_extension`: **Tag 01PE**, extension of a morphism.
* `AlgebraicGeometry.exists_quasicoherentSubobject_restrict`: **Tag 01PE**, extension of a
  quasi-coherent submodule.

## Implementation notes

Restriction along `j` is used in two interchangeable guises, the inverse image functor
`Scheme.Modules.pullback j` and `Scheme.Modules.restrictFunctor j`, compared by
`Scheme.Modules.restrictFunctorIsoPullback`. Equality of two subsheaves is recorded as an
isomorphism of the underlying modules commuting with their inclusions into the ambient module,
which is stronger than an abstract isomorphism of the underlying modules.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

universe u

/-- Quasi-coherence is affine-local: a module whose restriction to every affine open is
quasi-coherent is quasi-coherent. -/
theorem isQuasicoherent_of_restrict_isAffineOpen {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ U : X.Opens, IsAffineOpen U → (M.restrict U.ι).IsQuasicoherent) :
    M.IsQuasicoherent := by
  refine Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations M
    (fun V : X.affineOpens ↦ (V : X.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top X))
    fun V ↦ ?_
  obtain ⟨V, hV⟩ := V
  have : (M.restrict (V : X.Opens).ι).IsQuasicoherent := h V hV
  exact (Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec
    hV.isoSpec _).some

variable {U X : Scheme.{u}} (j : U ⟶ X)
  (F : X.Modules) (G : U.Modules)
  (φ : G ⟶ (Scheme.Modules.pullback j).obj F)

/-- The kernel of `(𝟙, -f) : A ⊞ B ⟶ A` is `B`, embedded as the graph of `f`. -/
noncomputable def standardGraphKernelIso {Y : Scheme.{u}} {A B : Y.Modules} (f : B ⟶ A) :
    kernel (biprod.desc (𝟙 A) (-f)) ≅ B := by
  let d : A ⊞ B ⟶ A := biprod.desc (𝟙 A) (-f)
  let s : B ⟶ A ⊞ B := biprod.lift f (𝟙 B)
  have hs : s ≫ d = 0 := by
    simp [d, s, biprod.lift_desc]
  refine
    { hom := kernel.ι d ≫ biprod.snd
      inv := kernel.lift d s hs
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (cancel_mono (kernel.ι d)).1
    simp only [Category.assoc, kernel.lift_ι]
    apply biprod.hom_ext
    · simp only [s, biprod.lift_fst, Category.assoc]
      have h : kernel.ι d ≫ biprod.fst + -(kernel.ι d ≫ biprod.snd ≫ f) = 0 := by
        simpa [d, biprod.desc_eq, Category.assoc] using kernel.condition d
      exact (add_neg_eq_zero.mp h).symm
    · simp [s, Category.assoc]
  · simp [s]

/-- **Stacks Project, Tag 01PE.** A morphism from a quasi-coherent module on a quasi-compact
open subscheme to the restriction of a quasi-coherent module extends to a morphism of
quasi-coherent modules on the whole scheme. -/
@[stacks 01PE "extend_quasicoherent_morphism"]
lemma exists_quasicoherent_extension
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : U.Modules) [G.IsQuasicoherent] (φ : G ⟶ F.restrict j) :
    ∃ (H : X.Modules) (_ : H.IsQuasicoherent)
      (ψ : H ⟶ F) (e : H.restrict j ≅ G),
      e.hom ≫ φ = (Scheme.Modules.restrictFunctor j).map ψ := by
  let φ' : G ⟶ (Scheme.Modules.pullback j).obj F :=
    φ ≫ (Scheme.Modules.restrictFunctorIsoPullback j).hom.app F
  let H : X.Modules := graphKernel j F G φ'
  let ψ : H ⟶ F := graphKernelProjection j F G φ'
  let e : H.restrict j ≅ G :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app H ≪≫ graphKernelPullbackIso j F G φ'
  refine ⟨H, inferInstance, ψ, e, ?_⟩
  apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app F)).1
  calc
    (e.hom ≫ φ) ≫ (Scheme.Modules.restrictFunctorIsoPullback j).hom.app F =
        (Scheme.Modules.restrictFunctorIsoPullback j).hom.app H ≫
          (graphKernelPullbackIso j F G φ').hom ≫ φ' := by
            simp [e, φ', Category.assoc]
    _ = (Scheme.Modules.restrictFunctorIsoPullback j).hom.app H ≫
          (Scheme.Modules.pullback j).map ψ := by
            rw [graphKernelPullbackIso_hom_comp]
    _ = (Scheme.Modules.restrictFunctor j).map ψ ≫
          (Scheme.Modules.restrictFunctorIsoPullback j).hom.app F :=
            ((Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality ψ).symm

/-- **Stacks Project, Tag 01PE.** A quasi-coherent submodule of the restriction of a
quasi-coherent module to a quasi-compact open subscheme extends to a quasi-coherent submodule
of the ambient module. -/
@[stacks 01PE "extend_quasicoherent_subsheaf"]
theorem exists_quasicoherentSubobject_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : Subobject (F.restrict j)) (hG : (G : U.Modules).IsQuasicoherent) :
    ∃ H : Subobject F, (H : X.Modules).IsQuasicoherent ∧
      ∃ e : (H : X.Modules).restrict j ≅ (G : U.Modules),
        e.hom ≫ G.arrow = (restrictFunctor j).map H.arrow := by
  let t := (Scheme.Modules.restrictFunctorIsoPullback j).app F
  let φ := G.arrow ≫ t.hom
  let K := graphKernel j F (G : U.Modules) φ
  let p := graphKernelProjection j F (G : U.Modules) φ
  have : Mono φ := by
    dsimp [φ]
    infer_instance
  have : Mono p := graphKernelProjection_mono j F (G : U.Modules) φ
  let q := Subobject.underlyingIso p
  let e₀ := graphKernelPullbackIso j F (G : U.Modules) φ
  let s := (restrictFunctor j).mapIso q
  let e := s ≪≫ (Scheme.Modules.restrictFunctorIsoPullback j).app K ≪≫ e₀
  have : (G : U.Modules).IsQuasicoherent := hG
  refine ⟨Subobject.mk p, ?_, ?_⟩
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso q.symm
      (inferInstance : K.IsQuasicoherent)
  · refine ⟨e, ?_⟩
    apply (cancel_mono t.hom).1
    calc
      e.hom ≫ G.arrow ≫ t.hom =
          s.hom ≫ (Scheme.Modules.restrictFunctorIsoPullback j).hom.app K ≫
            (e₀.hom ≫ φ) := by simp [e, φ, Category.assoc]
      _ =
          s.hom ≫ (Scheme.Modules.restrictFunctorIsoPullback j).hom.app K ≫
            (Scheme.Modules.pullback j).map p := by
          rw [graphKernelPullbackIso_hom_comp]
      _ = s.hom ≫ ((restrictFunctor j).map p ≫ t.hom) := by
          congr 1
          exact (Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality p |>.symm
      _ = ((restrictFunctor j).map q.hom ≫ (restrictFunctor j).map p) ≫ t.hom := by
          simp [s, Category.assoc]
      _ = (restrictFunctor j).map (Subobject.mk p).arrow ≫ t.hom := by
          rw [← Functor.map_comp, Subobject.underlyingIso_hom_comp_eq_mk]

end AlgebraicGeometry

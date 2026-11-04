module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.LocalLifting

/-!
# Local representation of a derived morphism out of a strictly perfect complex

Let `X` be a ringed space, let `E` be a strictly perfect complex of `𝒪_X`-modules and let `F`
be any complex of `𝒪_X`-modules. A morphism `E ⟶ F` in the derived category of `𝒪_X`-modules
is, on a neighbourhood of every point of `X`, induced by an actual morphism of complexes. This
is half of [Stacks, Tag 08C9]; the other half, that a derived-zero morphism out of a strictly
perfect complex is locally null-homotopic, is
`AlgebraicGeometry.RingedSpace.exists_local_homotopy_zero_of_derived_eq_zero`.

## Main results

* `Stacks.Cohomology.exists_local_complex_map`: the local complex representatives of a derived
  morphism out of a strictly perfect complex.

## Implementation notes

An open covering is expressed pointwise, as `∀ x, ∃ U, x ∈ U ∧ …`. Restriction to an open
subspace is `AlgebraicGeometry.RingedSpace.restrictModules`; its additivity and exactness
witnesses are part of the local existence assertion, so the induced functor on derived
categories and its canonical comparison with restriction of complexes are named without
arbitrary choices, and the equality with the given derived morphism is stated through that
comparison.

All universes of the ringed space coincide, as they must for `StrictlyPerfect.OXMod` to exist;
the derived-category universes on `X` and on its open subspaces stay independent.
`AlgebraicGeometry.RingedSpace.restrictModules` is polymorphic in the module universe, which the
complexes `E` and `F` here fix to be the universe `u` of the ringed space; that instantiation is
written out as `restrictModules.{u, u}` because the hypotheses on the restriction functor
mention it in positions that do not themselves determine it.

## References

* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
* [Stacks Project, Tag 08C8](https://stacks.math.columbia.edu/tag/08C8)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open StrictlyPerfect

attribute [local instance] AlgebraicGeometry.RingedSpace.overToRestricted_additive

namespace Stacks.Cohomology

universe u d d'

variable {X : RingedSpace.{u, u}}
variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]

local instance hasDerivedCategory_restrict (U : Opens X.carrier) :
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) :=
  (inferInstance : ∀ U : Opens X.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))) U

variable {E F : CochainComplex (OXMod.{u, u} X) ℤ}

/-- Transporting a lift along a natural isomorphism of functors: if `β` lifts `γ` through `f`
after applying `F₁` and `Q`, then its conjugate by `e : F₁ ≅ F₂` does so after applying `F₂`
and `Q`. -/
private lemma map_conj_comp_eq {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    {F₁ F₂ : C₁ ⥤ C₂} (e : F₁ ≅ F₂) (Q : C₂ ⥤ C₃) {A B C : C₁}
    (β : F₁.obj A ⟶ F₁.obj B) (f : B ⟶ C) (γ : A ⟶ C)
    (h : Q.map (β ≫ F₁.map f) = Q.map (F₁.map γ)) :
    Q.map (e.inv.app A ≫ β ≫ e.hom.app B) ≫ Q.map (F₂.map f) = Q.map (F₂.map γ) := by
  have key : e.inv.app A ≫ F₁.map γ ≫ e.hom.app C = F₂.map γ := by
    rw [e.hom.naturality γ, ← Category.assoc, e.inv_hom_id_app, Category.id_comp]
  rw [← Q.map_comp, ← key, Category.assoc, Category.assoc, ← e.hom.naturality f]
  simp only [Functor.map_comp] at h ⊢
  rw [reassoc_of% h]

/-- The square comparing a left fraction `c ≫ i` with a lift `b` of `c` commutes, given the
two naturality squares of the comparison, a right inverse `tinv` of `t` and a left inverse `j`
of `i`. -/
private lemma comp_eq_of_lift_fraction {D : Type*} [Category D] {dE dF dG qE qF qG : D}
    (φE : dE ⟶ qE) (φF : dF ⟶ qF) (φG : dG ⟶ qG)
    (c : dE ⟶ dG) (i : dG ⟶ dF) (j : dF ⟶ dG)
    (t : qF ⟶ qG) (tinv : qG ⟶ qF) (b : qE ⟶ qF) (g : qE ⟶ qG)
    (hij : i ≫ j = 𝟙 dG) (htt : t ≫ tinv = 𝟙 qF)
    (hnatf : φF ≫ t = j ≫ φG) (hnatg : c ≫ φG = φE ≫ g)
    (hb : b ≫ t = g) :
    (c ≫ i) ≫ φF = φE ≫ b := by
  rw [← Category.comp_id φF, ← Category.comp_id b, ← htt, reassoc_of% hnatf, reassoc_of% hb,
    Category.assoc, reassoc_of% hij, reassoc_of% hnatg]

/-- If `γ` lifts through `f` up to homotopy over an open `U`, then the restriction to `U` of the
left fraction `Q(γ) ∘ Q(f)⁻¹` is represented by a morphism of complexes. -/
private lemma exists_restricted_complex_map (U : Opens X.carrier)
    (hadd : (RingedSpace.restrictModules.{u, u} X U).Additive)
    (hlim : PreservesFiniteLimits (RingedSpace.restrictModules.{u, u} X U))
    (hcolim : PreservesFiniteColimits (RingedSpace.restrictModules.{u, u} X U))
    {G : CochainComplex (OXMod.{u, u} X) ℤ} (γ : E ⟶ G) (f : F ⟶ G)
    [IsIso (DerivedCategory.Q.map f)] [QuasiIso f]
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (hα : α = DerivedCategory.Q.map γ ≫ inv (DerivedCategory.Q.map f))
    (β : ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E ⟶
        ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)
    (hhom : Nonempty (Homotopy
      (β ≫ ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)
      (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map γ))) :
    letI := hadd
    letI := hlim
    letI := hcolim
    ∃ βR : ((RingedSpace.restrictModules.{u, u} X U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E ⟶
        ((RingedSpace.restrictModules.{u, u} X U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F,
      (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategory.map α ≫
          (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app F =
        (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app E ≫
          DerivedCategory.Q.map βR := by
  let := hadd
  let := hlim
  let := hcolim
  let R := RingedSpace.restrictModules.{u, u} X U
  let T := RingedSpace.overToRestricted X U
  let O := SheafOfModules.overFunctor (structureSheafOfRings X) U
  let OHC := O.mapHomologicalComplex (ComplexShape.up ℤ)
  let THC := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let RHC := R.mapHomologicalComplex (ComplexShape.up ℤ)
  let QU := DerivedCategory.Q (C := OXMod.{u, u} (X.restrict U.isOpenEmbedding))
  let eHC := Functor.mapHomologicalComplexCompIso
    (RingedSpace.restrictModulesIsoOverComp X U) (ComplexShape.up ℤ)
  let : R.PreservesHomology := Functor.preservesHomologyOfExact R
  have hfRiso : IsIso (QU.map (RHC.map f)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := OXMod.{u, u} (X.restrict U.isOpenEmbedding)) (RHC.map f)).2 inferInstance
  have hhc : QU.map (THC.map β ≫ THC.map (OHC.map f)) = QU.map (THC.map (OHC.map γ)) := by
    obtain ⟨hhom⟩ := hhom
    have hh := DerivedCategory.Q_map_eq_of_homotopy
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) (T.mapHomotopy hhom)
    simpa only [Functor.map_comp] using hh
  refine ⟨eHC.inv.app E ≫ THC.map β ≫ eHC.hom.app F, ?_⟩
  have hb : QU.map (eHC.inv.app E ≫ THC.map β ≫ eHC.hom.app F) ≫ QU.map (RHC.map f) =
      QU.map (RHC.map γ) := map_conj_comp_eq eHC QU (THC.map β) f γ hhc
  have hnatf := R.mapDerivedCategoryFactors.hom.naturality f
  have hnatγ := R.mapDerivedCategoryFactors.hom.naturality γ
  simp only [Functor.comp_map] at hnatf hnatγ
  have hmapα : R.mapDerivedCategory.map α =
      R.mapDerivedCategory.map (DerivedCategory.Q.map γ) ≫
        R.mapDerivedCategory.map (inv (DerivedCategory.Q.map f)) := by
    rw [hα, R.mapDerivedCategory.map_comp]
  have hinvcancel : R.mapDerivedCategory.map (inv (DerivedCategory.Q.map f)) ≫
      R.mapDerivedCategory.map (DerivedCategory.Q.map f) = 𝟙 _ := by
    rw [Functor.map_inv]
    exact IsIso.inv_hom_id _
  have key := comp_eq_of_lift_fraction
    (R.mapDerivedCategoryFactors.hom.app E) (R.mapDerivedCategoryFactors.hom.app F)
    (R.mapDerivedCategoryFactors.hom.app G)
    (R.mapDerivedCategory.map (DerivedCategory.Q.map γ))
    (R.mapDerivedCategory.map (inv (DerivedCategory.Q.map f)))
    (R.mapDerivedCategory.map (DerivedCategory.Q.map f)) (QU.map (RHC.map f))
    (inv (QU.map (RHC.map f))) (QU.map (eHC.inv.app E ≫ THC.map β ≫ eHC.hom.app F))
    (QU.map (RHC.map γ)) hinvcancel (IsIso.hom_inv_id _) hnatf.symm hnatγ hb
  exact (congrArg (fun z => z ≫ R.mapDerivedCategoryFactors.hom.app F) hmapα).trans key

omit [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))] in
/-- A derived morphism `α` out of a strictly perfect complex is a left fraction whose numerator
lifts through its denominator, up to homotopy, on a neighbourhood of `x`. -/
private lemma exists_local_lift_of_left_fac (hE : IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (x : X.carrier) :
    ∃ (G : CochainComplex (OXMod.{u, u} X) ℤ) (γ : E ⟶ G) (f : F ⟶ G)
      (hf : IsIso (DerivedCategory.Q.map f)),
      letI := hf
      QuasiIso f ∧ α = DerivedCategory.Q.map γ ≫ inv (DerivedCategory.Q.map f) ∧
        ∃ U : Opens X.carrier, x ∈ U ∧
          ∃ β : ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj E ⟶
              ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj F,
            Nonempty (Homotopy
              (β ≫ ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f)
              (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).map γ)) := by
  obtain ⟨G, γ, f, hf, hα⟩ := DerivedCategory.left_fac (C := OXMod.{u, u} X) α
  let support : Finset ℤ := insert 0 hE.bounded.toFinset
  have hsupport : support.Nonempty := by simp [support]
  let a : ℤ := support.min' hsupport
  have hEa : ∀ j : ℤ, j < a → IsZero (E.X j) := fun j hj => by
    by_contra hnot
    exact absurd hj (not_lt.2 (Finset.min'_le support j
      (Finset.mem_insert_of_mem (hE.bounded.mem_toFinset.mpr hnot))))
  have hfq : QuasiIso f :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := OXMod.{u, u} X) f).mp hf
  have hf_iso : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap f j) := fun j =>
    (quasiIsoAt_iff_isIso_homologyMap _ j).1 (hfq.quasiIsoAt j)
  have hf_a : Epi (HomologicalComplex.homologyMap f a) := by
    have := hf_iso a
    infer_instance
  obtain ⟨U, hx, β, hhom⟩ :=
    exists_local_lift_homotopy (α := γ) (f := f) (a := a) hE hEa (fun j _ => hf_iso j) hf_a x
  exact ⟨G, γ, f, hf, hfq, hα, U, hx, β, hhom⟩

/-- A derived morphism out of a strictly perfect complex is locally represented by a morphism of
complexes. -/
@[stacks 08C9 "local_representation"]
theorem exists_local_complex_map (hE : IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (hadd : (RingedSpace.restrictModules.{u, u} X U).Additive)
        (hlim : PreservesFiniteLimits (RingedSpace.restrictModules.{u, u} X U))
        (hcolim : PreservesFiniteColimits (RingedSpace.restrictModules.{u, u} X U)),
        letI := hadd
        letI := hlim
        letI := hcolim
        ∃ β : ((RingedSpace.restrictModules.{u, u} X U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E ⟶
            ((RingedSpace.restrictModules.{u, u} X U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F,
          (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategory.map α ≫
              (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app F =
          (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app E ≫
              DerivedCategory.Q.map β := by
  intro x
  obtain ⟨_, γ, f, hf, hfq, hα, U, hx, β, hhom⟩ := exists_local_lift_of_left_fac hE α x
  let hadd : (RingedSpace.restrictModules.{u, u} X U).Additive := inferInstance
  let hlim : PreservesFiniteLimits (RingedSpace.restrictModules.{u, u} X U) :=
    RingedSpace.restrictModules_preservesFiniteLimits X U
  let hcolim : PreservesFiniteColimits (RingedSpace.restrictModules.{u, u} X U) :=
    RingedSpace.restrictModules_preservesFiniteColimits X U
  exact ⟨U, hx, hadd, hlim, hcolim,
    exists_restricted_complex_map U hadd hlim hcolim γ f α hα β hhom⟩

end Stacks.Cohomology

end

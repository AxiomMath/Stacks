module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibres of étale morphisms

Let `f : X ⟶ S` be a morphism of schemes whose fibres are disjoint unions of spectra of
finite separable residue-field extensions. At every point of `X` the induced residue field
extension is finite and separable. Consequently, in a commutative square of schemes whose
vertical arrows are étale, the induced morphism between the fibres over a point and its image
is again étale.

## Main definitions

* `AlgebraicGeometry.fiberMap` is the canonical morphism between the two fibres in a
  commutative square.

## Main results

* `AlgebraicGeometry.LocallyQuasiFinite.of_etale` says that an étale morphism is locally
  quasi-finite.
* `AlgebraicGeometry.finite_residueField_of_etale_fibers` gives finiteness of the
  residue-field extension.
* `AlgebraicGeometry.isSeparable_residueField_of_etale_fibers` gives separability of that
  extension.
* `AlgebraicGeometry.etale_fiberMap` says that the morphism of fibres is étale when both
  vertical arrows are étale.

## Implementation notes

An étale scheme over a field is precisely a disjoint union of spectra of finite separable
field extensions, with the isomorphism respecting the morphism to the spectrum of that field.
The hypothesis from the source is therefore expressed by requiring every canonical fibre
morphism to the spectrum of the residue field to be étale. Finiteness and separability are
stated separately, both for the algebra structure induced by the canonical residue-field map.
The morphism of fibres is expressed by the canonical map between the two pullbacks defining
the scheme-theoretic fibres, so the construction also records its natural dependence on the
commutative square and on the residue field map induced at the chosen point.

## References

* [Stacks Project, Tag 04NI](https://stacks.math.columbia.edu/tag/04NI)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- An étale morphism of schemes is locally quasi-finite: on an affine pair the induced ring
map is étale, hence formally unramified and free, so quasi-finite. -/
@[ega "IV 17.4.3" "étale morphisms"]
instance LocallyQuasiFinite.of_etale {X S : Scheme.{u}} (f : X ⟶ S)
    [Etale f] : LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  have h := f.etale_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  constructor
  intro p hp
  exact Algebra.FormallyUnramified.finite_of_free _ _

private lemma residueFieldMap_finiteType_formallyUnramified
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hfib : ∀ s : S, Etale (f.fiberToSpecResidueField s)) (x : X) :
    (f.residueFieldMap x).hom.FiniteType ∧
      (f.residueFieldMap x).hom.FormallyUnramified := by
  have := hfib (f x)
  have : LocallyQuasiFinite (f.fiberToSpecResidueField (f x)) :=
    LocallyQuasiFinite.of_etale _
  have : IsLocallyArtinian (f.fiber (f x)) :=
    IsLocallyArtinian.of_locallyQuasiFinite (f.fiberToSpecResidueField (f x))
  have : IsClosedImmersion (f.asFiberHom x) :=
    IsClosedImmersion.of_isPreimmersion _ (isClosed_discrete _)
  have hft : LocallyOfFiniteType (Spec.map (f.residueFieldMap x)) := by
    rw [← f.asFiberHom_fiberToSpecResidueField x]
    infer_instance
  have hfu : FormallyUnramified (Spec.map (f.residueFieldMap x)) := by
    rw [← f.asFiberHom_fiberToSpecResidueField x]
    exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  exact ⟨(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft,
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp hfu⟩

private lemma residueField_finite_separable_of_etale_fibers
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hfib : ∀ s : S, Etale (f.fiberToSpecResidueField s)) (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (S.residueField (f x)) (X.residueField x) ∧
      Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) := by
  obtain ⟨hft, hfu⟩ := residueFieldMap_finiteType_formallyUnramified f hfib x
  algebraize [(f.residueFieldMap x).hom]
  exact ⟨Algebra.FormallyUnramified.finite_of_free _ _,
    Algebra.FormallyUnramified.isSeparable _ _⟩

/-- Under the same fibre hypothesis, the residue field at a point of the source is finite over
the residue field at its image. -/
public lemma finite_residueField_of_etale_fibers
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hfib : ∀ s : S, Etale (f.fiberToSpecResidueField s)) (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (S.residueField (f x)) (X.residueField x) :=
  (residueField_finite_separable_of_etale_fibers f hfib x).1

/-- Under the same fibre hypothesis, the residue field at a point of the source is separable
over the residue field at its image. -/
public lemma isSeparable_residueField_of_etale_fibers
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hfib : ∀ s : S, Etale (f.fiberToSpecResidueField s)) (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) :=
  (residueField_finite_separable_of_etale_fibers f hfib x).2

section FiberMap

variable {U' U V' V : Scheme.{u}}

/-- The canonical morphism from a fibre to the spectrum of the residue field is étale. -/
private lemma etale_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (y : Y) :
    Etale (f.fiberToSpecResidueField y) := by
  change Etale (Limits.pullback.snd f (Y.fromSpecResidueField y))
  infer_instance

lemma etale_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (x : X) : Etale (Spec.map (f.residueFieldMap x)) := by
  have hfib : ∀ y : Y, Etale (f.fiberToSpecResidueField y) :=
    etale_fiberToSpecResidueField f
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
    finite_residueField_of_etale_fibers f hfib x
  have : Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) :=
    isSeparable_residueField_of_etale_fibers f hfib x
  have : Module.FinitePresentation (Y.residueField (f x)) (X.residueField x) :=
    Module.finitePresentation_of_finite _ _
  have h : Algebra.Etale (Y.residueField (f x)) (X.residueField x) :=
    ⟨Algebra.FormallyEtale.of_isSeparable _ _, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr h

private lemma etale_asFiberHom {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (x : X) : Etale (f.asFiberHom x) := by
  have := etale_fiberToSpecResidueField f (f x)
  have hcomp : Etale (f.asFiberHom x ≫ f.fiberToSpecResidueField (f x)) := by
    rw [f.asFiberHom_fiberToSpecResidueField]
    exact etale_residueFieldMap f x
  exact Etale.of_comp (f := f.asFiberHom x) (g := f.fiberToSpecResidueField (f x))

/-- The canonical morphism from the fibre over `v'` in a commutative square to
the fibre over its image in the bottom row. -/
public noncomputable def fiberMap (f' : U' ⟶ V') (g' : U' ⟶ U)
    (g : V' ⟶ V) (f : U ⟶ V) (h : g' ≫ f = f' ≫ g) (v' : V') :
    f'.fiber v' ⟶ f.fiber (g v') :=
  pullback.map _ _ _ _ g' (Spec.map (g.residueFieldMap v')) g h.symm (by simp)

/-- **Stacks Project, Tag 04NI.** The morphism between corresponding fibres in
a commutative square with étale vertical arrows is étale. -/
@[stacks 04NI]
public lemma etale_fiberMap (f' : U' ⟶ V') (g' : U' ⟶ U)
    (g : V' ⟶ V) (f : U ⟶ V) (h : g' ≫ f = f' ≫ g) (v' : V')
    [Etale g'] [Etale g] : Etale (fiberMap f' g' g f h v') := by
  have : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ _ _ _ ↦ inferInstance⟩
  have hm₁ := MorphismProperty.pullbackMap (P := @Etale)
    (g' := pullback.fst g (V.fromSpecResidueField (g v'))) (inferInstance : Etale (𝟙 U'))
    (etale_asFiberHom g v') (Category.id_comp f').symm (g.asFiberHom_fiberι v').symm
  have hm₂ := MorphismProperty.pullbackMap (P := @Etale) (inferInstance : Etale g')
    (inferInstance : Etale (𝟙 (Spec (V.residueField (g v'))))) h.symm
    (Category.id_comp (V.fromSpecResidueField (g v'))).symm
  have key : ∀ {S' S : Scheme.{u}} (s' : S' ⟶ V') (s : S ⟶ V) (k : S' ⟶ S)
      (h₂ : s' ≫ g = k ≫ s), pullback.map f' s' f s g' k g h.symm h₂ =
        pullback.map f' s' f' (pullback.fst g s) (𝟙 _) (pullback.lift s' k h₂) (𝟙 _)
          (by simp) (by simp) ≫ (pullbackRightPullbackFstIso g s f').hom ≫
        pullback.map (f' ≫ g) s f s g' (𝟙 _) (𝟙 _) (by simp [h]) (by simp) := by
    intro S' S s' s k h₂
    apply pullback.hom_ext <;>
      simp [pullback.map]
  rw [fiberMap, key]
  exact MorphismProperty.comp_mem _ _ _ hm₁ (MorphismProperty.comp_mem _ _ _ inferInstance hm₂)

end FiberMap

end AlgebraicGeometry

end

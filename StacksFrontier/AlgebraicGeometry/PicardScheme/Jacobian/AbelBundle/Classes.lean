module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelMorphism

/-!
# The Abel morphism read on Picard classes

Let `f : X ⟶ S` be a proper smooth relative curve with a section `σ`, let `θ` be a Picard class of
`X` of degree `d` on every fibre, let `H` represent the degree-`d` Hilbert functor, let `A`
represent `Pic⁰_{X/S,σ}` through `e`, and let `γ : H ⟶ A` be the Abel morphism
`Stacks.RigidifiedPicard.abelMorphism`. The *universal class* of `A` is the class in
`Pic(X_A)` of the element of `Pic⁰_{X/S,σ}(A)` that `e` attaches to the identity of `A`; a
morphism `v : T ⟶ A` corresponds under `e` to its pullback along `X_T ⟶ X_A`.

This file reads the defining property of `γ` on classes: for a degree-`d` family `Z` over `T`
and `v : T ⟶ A`, the morphism classifying `Z` composed with `γ` is `v` exactly when the class of
`𝒪_{X_T}(Z)` is the pullback of the universal class translated by `θ`, up to a class pulled back
from `T`.

## Main definitions

* `Stacks.RigidifiedPicard.abelUniversalElement` and `Stacks.RigidifiedPicard.abelUniversalClass`:
  the universal element of `Pic⁰_{X/S,σ}(A)` and its class in `Pic(X_A)`.
* `Stacks.RigidifiedPicard.abelTranslatedClass`: the universal class translated by `θ`.

## Main results

* `Stacks.RigidifiedPicard.smallEquiv_e_hom_app`: the class corresponding to `v : T ⟶ A` is the
  pullback of the universal class.
* `Stacks.RigidifiedPicard.comp_abelMorphism_eq_iff`: `m ≫ γ = v` exactly when the normalised
  class of the family classified by `m` is the pullback of the universal class along `v`.
* `Stacks.RigidifiedPicard.exists_abelClass_add_eq_of_comp_abelMorphism`: if `m ≫ γ = w` then
  `[𝒪(D_m)]` is the pullback of the translated universal class along `w`, up to a class from `T`.
* `Stacks.RigidifiedPicard.family_symm_comp_abelMorphism_of_abelClass_eq`: conversely, a family
  whose class is the pullback of the translated universal class along `w` is classified by a
  morphism `m` with `m ≫ γ = w`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsProper f]
  [SmoothOfRelativeDimension 1 f] [LocallyOfFiniteType f]
  (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
  (A : Grp (Over S)) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)

/-- **The universal element of `Pic⁰_{X/S,σ}(A)`**: the element `e` attaches to `𝟙 A`. -/
def abelUniversalElement : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op A.X) :=
  (e.hom.app (op A.X)).hom (𝟙 A.X)

/-- **The universal class**: the class in `Pic(X_A)` of the universal element. -/
def abelUniversalClass : Stacks.Picard.ofScheme (bc f A.X) :=
  smallEquiv _ (((Multiplicative.toAdd (abelUniversalElement f hdim σ hσ A e) :
    groupZero f hdim σ hσ A.X) : group f σ hσ A.X) : Stacks.Picard.smallOfScheme (bc f A.X))

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- The universal class is rigidified along the section. -/
theorem schemePullbackClass_bcSection_abelUniversalClass :
    Stacks.Picard.schemePullbackClass (bcSection f σ hσ A.X)
      (abelUniversalClass f hdim σ hσ A e) = 0 :=
  (mem_group_iff f σ hσ A.X _).1
    ((Multiplicative.toAdd (abelUniversalElement f hdim σ hσ A e) :
      groupZero f hdim σ hσ A.X) : group f σ hσ A.X).2

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- **The class corresponding to `v : T ⟶ A`** is the pullback of the universal class along
`X_T ⟶ X_A`. -/
theorem smallEquiv_e_hom_app {T : Over S} (v : T ⟶ A.X) :
    smallEquiv _ (((Multiplicative.toAdd ((e.hom.app (op T)).hom v) :
      groupZero f hdim σ hσ T) : group f σ hσ T) : Stacks.Picard.smallOfScheme (bc f T)) =
      Stacks.Picard.schemePullbackClass (bcMap f v) (abelUniversalClass f hdim σ hσ A e) := by
  have hn : (e.hom.app (op T)).hom ((yonedaGrp.obj A).map v.op (𝟙 A.X)) =
      (functorZero f hdim σ hσ).map v.op ((e.hom.app (op A.X)).hom (𝟙 A.X)) :=
    congrArg (fun φ => GrpCat.Hom.hom φ (𝟙 A.X)) (e.hom.naturality v.op)
  have hv : (yonedaGrp.obj A).map v.op (𝟙 A.X) = v := Category.comp_id v
  rw [hv] at hn
  rw [hn]
  exact functorZero_map_val f hdim σ hσ v _

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- The component of `e` at `T` is injective. -/
theorem e_hom_app_injective (T : Over S) : Function.Injective (e.hom.app (op T)).hom := by
  refine Function.LeftInverse.injective (g := (e.inv.app (op T)).hom) fun a => ?_
  change (e.hom.app (op T) ≫ e.inv.app (op T)).hom a = a
  rw [Iso.hom_inv_id_app]
  rfl

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- The pullback of the universal class is rigidified along the section. -/
theorem schemePullbackClass_bcSection_bcMap_abelUniversalClass {T : Over S} (v : T ⟶ A.X) :
    Stacks.Picard.schemePullbackClass (bcSection f σ hσ T)
      (Stacks.Picard.schemePullbackClass (bcMap f v) (abelUniversalClass f hdim σ hσ A e)) = 0 := by
  rw [← smallEquiv_e_hom_app f hdim σ hσ A e v]
  exact (mem_group_iff f σ hσ T _).1
    ((Multiplicative.toAdd ((e.hom.app (op T)).hom v) : groupZero f hdim σ hσ T) :
      group f σ hσ T).2

variable (θ : Stacks.Picard.ofScheme X) {d : ℕ}
  (hθ : ∀ s : S, relativeInvertibleDegreeHomAt f hdim s θ = d)
  {H : Over S} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **`m ≫ γ = v` read on classes**: the normalised Abel class of the family classified by `m`
is the pullback of the universal class along `v`, and conversely. -/
theorem comp_abelMorphism_eq_iff {T : Over S} (m : T ⟶ H) (v : T ⟶ A.X) :
    m ≫ abelMorphism f hdim σ hσ θ hθ hH A e = v ↔
      abelNormalized f σ hσ θ (hH.family m) =
        Stacks.Picard.schemePullbackClass (bcMap f v) (abelUniversalClass f hdim σ hσ A e) := by
  constructor
  · rintro rfl
    rw [← smallEquiv_e_hom_app f hdim σ hσ A e, abelMorphism_spec, smallEquiv_abelElement]
  · intro h
    refine e_hom_app_injective f hdim σ hσ A e T ?_
    rw [abelMorphism_spec]
    refine ext_functorZero f hdim σ hσ ?_
    rw [smallEquiv_abelElement, smallEquiv_e_hom_app, h]

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsProper f]
  [SmoothOfRelativeDimension 1 f] [LocallyOfFiniteType f]
  (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
  (A : Grp (Over S)) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
  (θ : Stacks.Picard.ofScheme X) {d : ℕ}
  (hθ : ∀ s : S, relativeInvertibleDegreeHomAt f hdim s θ = d)
  {H : Over S} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)

/-- **The universal class translated by `θ`**: the class on `X_A` whose pullbacks are the classes
`[𝒪(D)]` of the families mapped by `γ`. -/
def abelTranslatedClass : Stacks.Picard.ofScheme (bc f A.X) :=
  abelUniversalClass f hdim σ hσ A e +
    Stacks.Picard.schemePullbackClass (pullback.fst f A.X.hom) θ

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- The pullback of the translated universal class along `X_T ⟶ X_A` is the pullback of the
universal class translated by the pullback of `θ`. -/
theorem schemePullbackClass_bcMap_abelTranslatedClass {T : Over S} (w : T ⟶ A.X) :
    Stacks.Picard.schemePullbackClass (bcMap f w) (abelTranslatedClass f hdim σ hσ A e θ) =
      Stacks.Picard.schemePullbackClass (bcMap f w) (abelUniversalClass f hdim σ hσ A e) +
        Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ := by
  rw [abelTranslatedClass, Stacks.Picard.schemePullbackClass_add,
    Stacks.Picard.schemePullbackClass_comp, bcMap_fst]

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **A family whose class is pulled back from the translated universal class along `w` is
classified by a morphism lying over `w`.** -/
theorem family_symm_comp_abelMorphism_of_abelClass_eq {T : Over S} (w : T ⟶ A.X)
    (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d)
    (hZ : abelClass f Z = Stacks.Picard.schemePullbackClass (bcMap f w)
      (abelTranslatedClass f hdim σ hσ A e θ)) :
    hH.family.symm Z ≫ abelMorphism f hdim σ hσ θ hθ hH A e = w := by
  rw [comp_abelMorphism_eq_iff, Equiv.apply_symm_apply, abelNormalized, hZ,
    schemePullbackClass_bcMap_abelTranslatedClass, add_sub_cancel_right]
  exact normalize_eq_self f σ hσ T _
    (schemePullbackClass_bcSection_bcMap_abelUniversalClass f hdim σ hσ A e w)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **The class of the family classified by a morphism lying over `w`** is pulled back from the
translated universal class along `w`, up to a class pulled back from the base. -/
theorem exists_abelClass_add_eq_of_comp_abelMorphism {T : Over S} (m : T ⟶ H) (w : T ⟶ A.X)
    (hm : m ≫ abelMorphism f hdim σ hσ θ hθ hH A e = w) :
    ∃ n : Stacks.Picard.ofScheme T.left,
      abelClass f (hH.family m) + Stacks.Picard.schemePullbackClass (bcProj f T) n =
        Stacks.Picard.schemePullbackClass (bcMap f w) (abelTranslatedClass f hdim σ hσ A e θ) := by
  obtain ⟨n, hn⟩ := abelNormalized_add_eq f σ hσ θ (hH.family m)
  refine ⟨n, ?_⟩
  rw [← hn, (comp_abelMorphism_eq_iff f hdim σ hσ A e θ hθ hH m w).1 hm,
    schemePullbackClass_bcMap_abelTranslatedClass]

end Stacks.RigidifiedPicard

end

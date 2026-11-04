module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatRimSchlessingerStar
public import StacksFrontier.Deformation.Artin.FormalObject.Effectiveness
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs

/-!
# Effective systems of finitely presented, flat and proper families

A system `ξ : ℕ ⥤ Spaces'_{fp, flat, proper}` is effective over a cocone `c` of its bases
(`Deformation.Artin.IsEffectiveSystem`) when `c` is the image of a cocone of families. This file
reduces that to a statement about algebraic spaces: it suffices to give one finitely presented,
flat and proper algebraic space `X` over the vertex of `c`, together with morphisms from the
algebraic spaces of the system into `X` over the legs of `c`, each a cartesian square, and
compatible with the transition morphisms of the system. This is the form in which the body of
the proof of [Stacks Project, Tag 0D3X] produces its conclusion: "We have to find a flat, proper,
finitely presented morphism `X → Spec(lim Rₙ)` ... such that `Xₙ` is the base change of `X` for
all `n`."

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isEffectiveSystem_of_spaces`: the reduction above.
* `AlgebraicGeometry.surjective_and_ker_sq_eq_bot_Γ_map_of_specIso`: a morphism identified with
  `Spec(φ)`, for `φ` surjective with square-zero kernel, is surjective with square-zero kernel on
  global functions.
* `AlgebraicGeometry.isSquareZeroClosedImmersion_of_squareZeroTower`: in the situation of
  `Deformation.Artin.IsSquareZeroFormallyEffective`, every transition morphism of the bases of the
  system is a square-zero closed immersion, so that `(X₁ ⊂ Xₙ) → (Spec(R₁) ⊂ Spec(Rₙ))` is a
  morphism of first order thickenings as the source says.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An effective system of proper flat families from algebraic spaces.**  Let
`ξ : ℕ ⥤ Spaces'_{fp, flat, proper}` be a system and `c` a cocone of its bases. Given an algebraic
space `X` with a finitely presented, flat and proper morphism `π` to the vertex of `c`, and
morphisms `a n` from the algebraic space of `ξ n` to `X` lying over the legs of `c`, each forming
a cartesian square and compatible with the transition morphisms of `ξ`, the system is effective
over `c`. -/
theorem isEffectiveSystem_of_spaces (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
    (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS)) (X : AlgebraicSpaces B S hS)
    (π : X.obj ⟶ yoneda.obj c.pt)
    (hπ : Space.IsFinitePresentation B S hS π ∧ Space.IsFlat B S hS π ∧
      Space.IsProper B S hS π)
    (a : ∀ n, ((comma B S hS).obj (ξ.obj n)).left.obj ⟶ X.obj)
    (ha : ∀ n, IsPullback ((comma B S hS).obj (ξ.obj n)).hom (a n)
      (yoneda.map (c.ι.app n)) π)
    (hcompat : ∀ {m n : ℕ} (k : m ⟶ n), ((comma B S hS).map (ξ.map k)).left.hom ≫ a n = a m) :
    Deformation.Artin.IsEffectiveSystem (cartesianProperFlatProjection B S hS) ξ c := by
  let pt : CartesianProperFlatSpaces B S hS := ⟨⟨⟨X, c.pt, π⟩, hπ⟩⟩
  let ι (n : ℕ) : ξ.obj n ⟶ pt :=
    ⟨ObjectProperty.homMk
      { left := ObjectProperty.homMk (a n)
        right := c.ι.app n
        w := (ha n).w.symm },
      AlgebraicGeometry.isStronglyCartesian_of_isPullback B S hS _ (ha n)⟩
  refine ⟨⟨pt, ⟨ι, fun m n k => ?_⟩⟩, rfl⟩
  exact total_hom_ext (ObjectProperty.hom_ext _ ((hcompat k).trans (Category.comp_id _).symm))
    ((c.ι.naturality k).trans (Category.comp_id _).symm)

end AlgebraicGeometry.ProperFlatFibre

namespace AlgebraicGeometry

/-- A morphism of schemes identified, by isomorphisms of its source and target with spectra, with
the spectrum of a surjection of rings with square-zero kernel is a first order thickening. -/
theorem isFirstOrderThickening_of_specIso {X Y : Scheme.{u}} {A C : CommRingCat.{u}} (φ : A ⟶ C)
    (hφ : Function.Surjective φ.hom) (hsq : RingHom.ker φ.hom ^ 2 = ⊥) (f : X ⟶ Y)
    (eX : X ≅ Spec C) (eY : Y ≅ Spec A) (w : f ≫ eY.hom = eX.hom ≫ Spec.map φ) :
    Stacks.Thickenings.IsFirstOrderThickening f :=
  Stacks.Thickenings.isFirstOrderThickening_of_isPullback (IsPullback.of_vert_isIso ⟨w⟩)
    (Stacks.Smooth.isFirstOrderThickening_specMap φ hφ hsq)

/-- **Pullback of global functions along a morphism identified with `Spec(φ)` is surjective with
square-zero kernel when `φ` is.**  For `f : X ⟶ Y` and isomorphisms `X ≅ Spec C`, `Y ≅ Spec A`
carrying `f` to `Spec(φ)`, the map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` is `φ` conjugated by ring
isomorphisms. -/
theorem surjective_and_ker_sq_eq_bot_Γ_map_of_specIso {X Y : Scheme.{u}} {A C : CommRingCat.{u}}
    (φ : A ⟶ C) (hφ : Function.Surjective φ.hom) (hsq : RingHom.ker φ.hom ^ 2 = ⊥) (f : X ⟶ Y)
    (eX : X ≅ Spec C) (eY : Y ≅ Spec A) (w : f ≫ eY.hom = eX.hom ≫ Spec.map φ) :
    Function.Surjective (Scheme.Γ.map f.op).hom ∧
      RingHom.ker (Scheme.Γ.map f.op).hom ^ 2 = ⊥ := by
  -- `Γ(f) = σ ≫ φ ≫ τ` with `σ = Γ(eY⁻¹) ≫ Γ(Spec A ≅ A)`, `τ = Γ(Spec C ≅ C)⁻¹ ≫ Γ(eX)`
  have hf : f = eX.hom ≫ Spec.map φ ≫ eY.inv := by
    rw [← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Scheme.Γ_map_op]
  let σ : Γ(Y, ⊤) ⟶ A := eY.inv.appTop ≫ (Scheme.ΓSpecIso A).hom
  let τ : C ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso C).inv ≫ eX.hom.appTop
  have : IsIso eY.inv.appTop := (Scheme.Γ.mapIso eY.symm.op).isIso_hom
  have : IsIso eX.hom.appTop := (Scheme.Γ.mapIso eX.op).isIso_hom
  have : IsIso σ := by
    dsimp only [σ]
    infer_instance
  have : IsIso τ := by
    dsimp only [τ]
    infer_instance
  have hΓ : f.appTop = σ ≫ φ ≫ τ := by
    rw [hf]
    simp only [σ, τ, Scheme.Hom.comp_appTop, Category.assoc]
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id_assoc]
  have hσ := ConcreteCategory.bijective_of_isIso σ
  have hτ := ConcreteCategory.bijective_of_isIso τ
  have hker : ∀ a, f.appTop.hom a = 0 → σ.hom a ∈ RingHom.ker φ.hom := fun a ha =>
    hτ.1 ((show f.appTop.hom a = τ.hom (φ.hom (σ.hom a)) by rw [hΓ]; rfl).symm.trans
      (ha.trans (map_zero _).symm))
  refine ⟨?_, ?_⟩
  · rw [hΓ]
    exact hτ.2.comp (hφ.comp hσ.2)
  · refine le_bot_iff.mp ?_
    rw [pow_two, Submodule.mul_le]
    intro a ha b hb
    rw [Ideal.mem_bot]
    have hm := Ideal.mul_mem_mul (hker a ha) (hker b hb)
    rw [← pow_two, hsq, Ideal.mem_bot] at hm
    exact hσ.1 (((map_mul σ.hom a b).trans hm).trans (map_zero _).symm)

/-- **The bases of a square-zero tower are first order thickenings of one another.** In the
situation of `Deformation.Artin.IsSquareZeroFormallyEffective` — a system of objects of the big
fppf site identified with the spectra of a tower of algebras whose transition maps are surjective
with square-zero kernel — every transition morphism of the system is a square-zero closed
immersion. -/
theorem isSquareZeroClosedImmersion_of_squareZeroTower
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Λ : Type u} [CommRing Λ]
    (R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ)
    (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
    (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
    (Y : ℕ ⥤ BigFppfOver B S hS)
    (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (Y.obj n) ≅ Spec (.of (R.obj (.op n))))
    (he : ∀ {i j : ℕ} (f : i ⟶ j), (BigFppfOver.toScheme B S hS).map (Y.map f) ≫ (e j).hom =
      (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
    {i j : ℕ} (f : i ⟶ j) : Space.IsSquareZeroClosedImmersion B S hS (Y.map f) :=
  isFirstOrderThickening_of_specIso (CommRingCat.ofHom (R.map f.op).hom.toRingHom)
    (hsurj f.op) (hsq f.op) _ (e i) (e j) (he f)

end AlgebraicGeometry

end

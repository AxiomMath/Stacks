module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleAffineSpace
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SeparableClosedPoints

/-!
# Density of the finite separable closed points of a smooth scheme

For a scheme smooth over a field, the closed points whose residue fields are finite separable
extensions of the base field are dense.

## Main results

* `AlgebraicGeometry.dense_closedPoints_with_finite_separable_residueField_of_smooth`: the closed
  points with finite separable residue field are dense in a scheme smooth over a field.

## Implementation notes

The algebra structure on the residue field at `x` is the one induced by the composite of the
map on global sections of the structure morphism with evaluation at `x`, so the finiteness and
separability conditions refer to the given structure morphism `X ⟶ Spec k`.

Density is proved by exhibiting one such point in an arbitrary nonempty open subset `O`. On `O`
the morphism is still smooth, so it is étale-locally an affine space
(`AlgebraicGeometry.exists_affine_open_etale_affineSpace`); the image of the chart is open in
affine space, hence contains a closed point with finite separable residue field
(`AlgebraicGeometry.exists_closedPoint_finite_separable_residueField`). An étale morphism
induces a finite separable extension of residue fields — separability is immediate from formal
unramifiedness, and finiteness follows because the extension is essentially of finite type and
formally unramified, hence finite. The chosen point is closed in the ambient scheme by
`AlgebraicGeometry.isClosed_of_isAlgebraic_residueField`.

## References

* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The structure map of the residue field at `x` over `k`, for `f ≫ g`, factors through the one
for `g` at `f x` followed by `f.residueFieldMap x`. -/
private theorem algebraMap_comp_residueFieldMap {k : Type u} [Field k] {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) (f : X ⟶ Y) (x : X) :
    (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ g).appTop ≫ X.Γevaluation x =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Y.Γevaluation (f x)) ≫ f.residueFieldMap x := by
  rw [Scheme.Hom.comp_appTop]
  simp only [Category.assoc, Scheme.Γevaluation_naturality]

/-- If the residue field of `Y` at `f x` is finite separable over `k`, then so is the residue
field of `X` at `x`, for an étale morphism `f : X ⟶ Y` over `k`. -/
private theorem finite_isSeparable_residueField_of_etale {k : Type u} [Field k] {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [Etale f] (x : X)
    (h : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Y.Γevaluation (f x)).hom.toAlgebra
      Module.Finite k (Y.residueField (f x)) ∧ Algebra.IsSeparable k (Y.residueField (f x))) :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ g).appTop ≫ X.Γevaluation x).hom.toAlgebra
    Module.Finite k (X.residueField x) ∧ Algebra.IsSeparable k (X.residueField x) := by
  rw [algebraMap_comp_residueFieldMap]
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Y.Γevaluation (f x)).hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  let := (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Y.Γevaluation (f x)) ≫
    f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k (Y.residueField (f x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) := by
    have hEss : Algebra.EssFiniteType (Y.residueField (f x)) (X.residueField x) := by
      algebraize [(f.stalkMap x).hom]
      have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
        inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
      have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
        rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
        exact LocallyOfFiniteType.stalkMap f x
      have : Algebra.EssFiniteType (Y.presheaf.stalk (f x))
          (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
        Algebra.EssFiniteType.comp (Y.presheaf.stalk (f x))
          (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
      have : Algebra.EssFiniteType
          (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
          (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
        Algebra.EssFiniteType.of_comp (Y.presheaf.stalk (f x))
          (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
          (IsLocalRing.ResidueField (X.presheaf.stalk x))
      convert this <;> try rfl
      rename_i hring₁ hring₂
      cases hring₁
      cases hring₂
      exact Eq.heq (Algebra.algebra_ext _ _ fun _ => rfl)
    have : Algebra.FormallyUnramified (Y.residueField (f x)) (X.residueField x) :=
      (Algebra.FormallyUnramified.iff_isSeparable _ _).2 inferInstance
    exact Algebra.FormallyUnramified.finite_of_free _ _
  obtain ⟨_, _⟩ := h
  exact ⟨Module.Finite.trans (Y.residueField (f x)) _,
    Algebra.IsSeparable.trans k (Y.residueField (f x)) _⟩

/-- Finiteness and separability of the residue field over `k` are transported along an open
immersion `m : U ⟶ X` over `k`. -/
private theorem finite_isSeparable_residueField_of_isOpenImmersion {k : Type u} [Field k]
    {U X : Scheme.{u}} (m : U ⟶ X) [IsOpenImmersion m] (f : X ⟶ Spec (.of k)) (y : U)
    (h : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ (m ≫ f).appTop ≫ U.Γevaluation y).hom.toAlgebra
      Module.Finite k (U.residueField y) ∧ Algebra.IsSeparable k (U.residueField y)) :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (m y)).hom.toAlgebra
    Module.Finite k (X.residueField (m y)) ∧ Algebra.IsSeparable k (X.residueField (m y)) := by
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ (m ≫ f).appTop ≫ U.Γevaluation y).hom.toAlgebra
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (m y)).hom.toAlgebra
  obtain ⟨_, hsep⟩ := h
  let e : X.residueField (m y) ≃ₐ[k] U.residueField y :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (m.residueFieldMap y).hom
      (ConcreteCategory.bijective_of_isIso (m.residueFieldMap y))) fun a =>
      (congrArg (fun q => q.hom a) (algebraMap_comp_residueFieldMap f m y)).symm
  exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
    (Algebra.IsSeparable.iff_of_equiv_equiv (RingEquiv.refl k) e.symm.toRingEquiv
      (by ext a; simp [AlgEquiv.commutes])).mp hsep⟩

/-- A point of a scheme over a field `k` whose residue field is finite over `k` is closed. -/
private theorem mem_closedPoints_of_finite_residueField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X)
    (h : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.Finite k (X.residueField x)) :
    x ∈ closedPoints X := by
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : IsScalarTower k ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      congrArg (fun q => ((Scheme.ΓSpecIso (.of k)).inv ≫ q).hom a)
        (Scheme.Γevaluation_naturality f x).symm
  have := h
  exact isClosed_of_isAlgebraic_residueField f x
    (Algebra.IsAlgebraic.tower_top (K := k) _) isClosed_singleton

/-- **Stacks Project, Tag 056U.** If `X` is smooth over a field `k`, then the closed points of
`X` whose residue fields are finite separable extensions of `k` are dense in `X`. -/
@[stacks 056U]
theorem dense_closedPoints_with_finite_separable_residueField_of_smooth
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] :
    Dense {x : X | x ∈ closedPoints X ∧
      letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.Finite k (X.residueField x) ∧
        Algebra.IsSeparable k (X.residueField x)} := by
  rw [dense_iff_inter_open]
  intro O hO ⟨x, hx⟩
  let V : X.Opens := ⟨O, hO⟩
  let X' := V.toScheme
  let g : X' ⟶ Spec (.of k) := V.ι ≫ f
  let x' : X' := ⟨x, hx⟩
  have htop : IsAffineOpen (⊤ : (Spec (.of k)).Opens) := isAffineOpen_top _
  obtain ⟨U₀, ⟨U₀, hU₀, rfl⟩, hxU₀, -⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  have hxg : InfinitesimalLifting.SmoothAt g x' :=
    (InfinitesimalLifting.smoothAt_iff_exists_affine g x').2
      ⟨U₀, ⊤, hU₀, htop, hxU₀, le_top, g.smooth_appLE htop hU₀ le_top⟩
  obtain ⟨d, U, hU, hxU, hUV, π, hπ, hcomp⟩ :=
    exists_affine_open_etale_affineSpace g x' ⊤ htop (by simp) hxg
  let S := Spec (.of k)
  let T := (⊤ : S.Opens).toScheme
  let A := AffineSpace (ULift.{u} (Fin d)) T
  let A₀ := AffineSpace (ULift.{u} (Fin d)) S
  let e : A ≅ A₀ :=
    { hom := AffineSpace.map _ (Scheme.topIso S).hom
      inv := AffineSpace.map _ (Scheme.topIso S).inv
      hom_inv_id := by
        rw [← AffineSpace.map_comp, (Scheme.topIso S).hom_inv_id, AffineSpace.map_id]
      inv_hom_id := by
        rw [← AffineSpace.map_comp, (Scheme.topIso S).inv_hom_id, AffineSpace.map_id] }
  let W : Set A := (fun z : U.toScheme => π z) '' (Set.univ : Set U.toScheme)
  have hWnonempty : W.Nonempty := ⟨π ⟨x', hxU⟩, ⟨⟨x', hxU⟩, Set.mem_univ _, rfl⟩⟩
  let : MorphismProperty.ContainsIdentities @UniversallyOpen :=
    ⟨fun Y => by let : IsOpenImmersion (𝟙 Y) := inferInstance; infer_instance⟩
  let : IsIso e.hom := e.isIso_hom
  have : UniversallyOpen e.hom := MorphismProperty.of_isIso _ e.hom
  obtain ⟨_, ⟨_, ⟨y, -, rfl⟩, rfl⟩, -, hwfin, hwsep⟩ :=
    exists_closedPoint_finite_separable_residueField (e.hom '' W)
      (e.hom.isOpenMap _ (π.isOpenMap _ isOpen_univ)) (hWnonempty.image _)
  let π₀ : U.toScheme ⟶ A₀ := π ≫ e.hom
  have hchart : π₀ ≫ (A₀ ↘ S) = U.ι ≫ g := by
    dsimp only [π₀, A₀, S, e]
    rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, hcomp]
    exact Scheme.Hom.resLE_comp_ι g hUV
  have : Etale π₀ := inferInstanceAs (Etale (π ≫ e.hom))
  have hy := finite_isSeparable_residueField_of_etale (A₀ ↘ S) π₀ y ⟨hwfin, hwsep⟩
  rw [hchart] at hy
  obtain ⟨hfin, hsep⟩ := finite_isSeparable_residueField_of_isOpenImmersion V.ι f _
    (finite_isSeparable_residueField_of_isOpenImmersion U.ι g y hy)
  exact ⟨_, (U.ι y).2, mem_closedPoints_of_finite_residueField f _ hfin, hfin, hsep⟩

end AlgebraicGeometry

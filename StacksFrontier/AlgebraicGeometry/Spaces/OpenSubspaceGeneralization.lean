module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Scheme-valued points of an algebraic space landing in an open subspace

Let `X` be an algebraic space over `S` and `Z ⊆ X` an open subspace. If a scheme-valued point
`s : T ⟶ X` sends a point `t₀` of `T` into `Z`, then it sends every generization `t` of `t₀` into
`Z`; consequently a morphism `Y ⟶ T` all of whose points go to `t` composes with `s` to a point of
`X` factoring through `Z`.

## Main results

* `AlgebraicGeometry.Space.exists_isOpen_factor_openSubspace`: the points sent into `Z` form an
  open set, through which such morphisms factor.
* `AlgebraicGeometry.Space.exists_factor_openSubspace_of_specializes`: the statement above.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The points of a scheme-valued point landing in an open subspace form an open set.** Let
`Z ⊆ X` be an open subspace and `s : T ⟶ X` a scheme-valued point sending the point of a
field-valued point `p₀` of `T` into `Z`. There is an open `V` of the scheme `T` containing the
underlying point of `p₀` such that every morphism `g : Y ⟶ T` all of whose points lie in `V` makes
`g ≫ s` factor through `Z`. -/
theorem exists_isOpen_factor_openSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : Subfunctor X) (hZ : IsOpenSubspace B S hS Z)
    (T : BigFppfOver B S hS) (s : yoneda.obj T ⟶ X)
    (p₀ : FieldValuedPoint B S hS (yoneda.obj T))
    (hp₀ : pointsMap B S hS (yoneda.obj T) s (p₀.class B S hS (yoneda.obj T)) ∈
      Set.range (pointsMap B S hS Z.toFunctor Z.ι)) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj T), IsOpen V ∧ schemePoint B S hS T p₀ ∈ V ∧
      ∀ (Y : BigFppfOver B S hS) (g : Y ⟶ T),
        (∀ y, (BigFppfOver.toScheme B S hS).map g y ∈ V) →
        ∃ α : yoneda.obj Y ⟶ Z.toFunctor, α ≫ Z.ι = yoneda.map g ≫ s := by
  let W : Set (points B S hS X) := Set.range (pointsMap B S hS Z.toFunctor Z.ι)
  have hW : IsOpen W := by
    have h := (openSubspacesOrderIso B S hS X hX ⟨Z, hZ⟩).2
    rwa [openSubspacesOrderIso_apply B S hS X hX ⟨Z, hZ⟩] at h
  let D : Set (points B S hS (yoneda.obj T)) := pointsMap B S hS (yoneda.obj T) s ⁻¹' W
  have hD : IsOpen D := (continuous_pointsMap B S hS s).isOpen_preimage W hW
  obtain ⟨V, hV, hVspec⟩ := (isOpen_yoneda_iff_isSchemeOpen B S hS T D).mp hD
  refine ⟨V, hV, (hVspec p₀).mp hp₀, fun Y g hg => ?_⟩
  refine (factorsThrough_openSubspace_iff_points B S hS hX
    (isAlgebraicSpace_yoneda B S hS Y) Z hZ (yoneda.map g ≫ s)).2 ?_
  rintro _ ⟨y₀, rfl⟩
  induction y₀ using Quot.inductionOn with
  | h q =>
    change pointsMap B S hS (yoneda.obj Y) (yoneda.map g ≫ s)
      (q.class B S hS (yoneda.obj Y)) ∈ W
    rw [pointsMap_comp_apply]
    change pointsMap B S hS (yoneda.obj T) s
      ((FieldValuedPoint.map B S hS (yoneda.obj Y) (yoneda.map g) q).class B S hS
        (yoneda.obj T)) ∈ W
    refine (hVspec _).mpr ?_
    rw [schemePoint_map_yoneda]
    exact hg _

/-- **Points landing in an open subspace, under generization.** Let `Z ⊆ X` be an open subspace,
`s : T ⟶ X` a scheme-valued point sending the point of a field-valued point `p₀` of `T` into `Z`,
and `t` a generization of the underlying scheme point of `p₀`. Every morphism `g : Y ⟶ T` all of
whose points go to `t` makes `g ≫ s` factor through `Z`. -/
theorem exists_factor_openSubspace_of_specializes
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : Subfunctor X) (hZ : IsOpenSubspace B S hS Z)
    (T : BigFppfOver B S hS) (s : yoneda.obj T ⟶ X)
    (p₀ : FieldValuedPoint B S hS (yoneda.obj T))
    (hp₀ : pointsMap B S hS (yoneda.obj T) s (p₀.class B S hS (yoneda.obj T)) ∈
      Set.range (pointsMap B S hS Z.toFunctor Z.ι))
    (t : (BigFppfOver.toScheme B S hS).obj T) (ht : t ⤳ schemePoint B S hS T p₀)
    (Y : BigFppfOver B S hS) (g : Y ⟶ T)
    (hg : ∀ y, (BigFppfOver.toScheme B S hS).map g y = t) :
    ∃ α : yoneda.obj Y ⟶ Z.toFunctor, α ≫ Z.ι = yoneda.map g ≫ s := by
  obtain ⟨V, hV, hpV, hfac⟩ := exists_isOpen_factor_openSubspace B S hS hX Z hZ T s p₀ hp₀
  exact hfac Y g fun y => hg y ▸ ht.mem_open hV hpV

end AlgebraicGeometry.Space

end

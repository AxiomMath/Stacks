module

public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem

/-!
# Improving coherent formal modules

Let `X` be a Noetherian scheme, let `T ⊆ X` be stable under specialization and let `(ℱₙ)` be an
inverse system of coherent `𝒪_X`-modules. Dividing each term by its subsheaf of sections
supported on `T` produces an inverse system `(ℱ'ₙ)` of coherent modules together with a map
`(ℱₙ) ⟶ (ℱ'ₙ)`: the transition maps of `(ℱ'ₙ)` are the ones the universal property of the
depth-one quotient supplies, and every term of `(ℱ'ₙ)` has depth at least one along `T`.

## Main definitions

* `Stacks.Algebraization.improvedSystem`: the inverse system `(ℱ'ₙ)` of depth-one quotients.
* `Stacks.Algebraization.toImprovedSystem`: the canonical map `(ℱₙ) ⟶ (ℱ'ₙ)`.

## Main results

* `Stacks.Algebraization.isDepthOneQuotient_toImprovedSystem_app`: every component of the
  canonical map is the depth-one quotient of its source, so each `ℱ'ₙ` is coherent, each
  `ℱₙ ⟶ ℱ'ₙ` is surjective and an isomorphism on stalks away from `T`, and `ℱ'ₙ` has depth at
  least one at every point of `T`.
* `Stacks.Algebraization.exists_improving_map_of_coherentAdicSystem`: the same statement for an
  object of `Coh(X, ℐ)`.

## References

* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
  (F : ℕᵒᵖ ⥤ X.Modules) [∀ n : ℕᵒᵖ, (F.obj n).IsCoherent]

/-- Two maps out of a depth-one quotient agree as soon as they agree after the quotient map,
which is surjective. -/
theorem depthOneQuotient_hom_ext {n : ℕᵒᵖ} {G : X.Modules}
    {l₁ l₂ : depthOneQuotient X T hT (F.obj n) ⟶ G}
    (h : toDepthOneQuotient X T hT (F.obj n) ≫ l₁ =
      toDepthOneQuotient X T hT (F.obj n) ≫ l₂) : l₁ = l₂ :=
  have := (depthOneQuotient_spec X T hT (F.obj n)).2.1
  (cancel_epi _).mp h

/-- The transition map `ℱ'ₘ ⟶ ℱ'ₙ` of depth-one quotients induced by a transition map
`ℱₘ ⟶ ℱₙ`, obtained from the universal property of the depth-one quotient. -/
def improvedMap {m n : ℕᵒᵖ} (f : m ⟶ n) :
    depthOneQuotient X T hT (F.obj m) ⟶ depthOneQuotient X T hT (F.obj n) :=
  have := (depthOneQuotient_spec X T hT (F.obj n)).1
  (depthOneQuotient_lift X T hT (F.obj m) (depthOneQuotient X T hT (F.obj n))
    (F.map f ≫ toDepthOneQuotient X T hT (F.obj n))
    (depthOneQuotient_spec X T hT (F.obj n)).2.2.2).choose

/-- The induced transition map of depth-one quotients is compatible with the quotient maps. -/
theorem toDepthOneQuotient_comp_improvedMap {m n : ℕᵒᵖ} (f : m ⟶ n) :
    toDepthOneQuotient X T hT (F.obj m) ≫ improvedMap T hT F f =
      F.map f ≫ toDepthOneQuotient X T hT (F.obj n) :=
  have := (depthOneQuotient_spec X T hT (F.obj n)).1
  (depthOneQuotient_lift X T hT (F.obj m) (depthOneQuotient X T hT (F.obj n))
    (F.map f ≫ toDepthOneQuotient X T hT (F.obj n))
    (depthOneQuotient_spec X T hT (F.obj n)).2.2.2).choose_spec.1

/-- The inverse system `(ℱ'ₙ)` obtained by dividing each term of `(ℱₙ)` by its sections
supported on `T`. -/
def improvedSystem : ℕᵒᵖ ⥤ X.Modules where
  obj n := depthOneQuotient X T hT (F.obj n)
  map f := improvedMap T hT F f
  map_id n := by
    refine depthOneQuotient_hom_ext T hT F ?_
    rw [toDepthOneQuotient_comp_improvedMap, F.map_id, Category.id_comp, Category.comp_id]
  map_comp {l m n} f g := by
    refine depthOneQuotient_hom_ext T hT F ?_
    rw [toDepthOneQuotient_comp_improvedMap, F.map_comp, Category.assoc,
      ← Category.assoc (toDepthOneQuotient X T hT (F.obj l)), toDepthOneQuotient_comp_improvedMap,
      Category.assoc, toDepthOneQuotient_comp_improvedMap]

/-- The `n`-th term of the improved system is the depth-one quotient of `ℱₙ`. -/
@[simp]
theorem improvedSystem_obj (n : ℕᵒᵖ) :
    (improvedSystem T hT F).obj n = depthOneQuotient X T hT (F.obj n) :=
  rfl

/-- The canonical map `(ℱₙ) ⟶ (ℱ'ₙ)` of inverse systems, given in each degree by the
depth-one quotient map. -/
def toImprovedSystem : F ⟶ improvedSystem T hT F where
  app n := toDepthOneQuotient X T hT (F.obj n)
  naturality _ _ f := (toDepthOneQuotient_comp_improvedMap T hT F f).symm

/-- The `n`-th component of the canonical map `(ℱₙ) ⟶ (ℱ'ₙ)` is the depth-one quotient map of
`ℱₙ`. -/
@[simp]
theorem toImprovedSystem_app (n : ℕᵒᵖ) :
    (toImprovedSystem T hT F).app n = toDepthOneQuotient X T hT (F.obj n) :=
  rfl

/-- Each component of the canonical map `(ℱₙ) ⟶ (ℱ'ₙ)` is the depth-one quotient of its source:
`ℱ'ₙ` is coherent, the map is surjective and an isomorphism on stalks outside `T`, and `ℱ'ₙ` has
depth at least one at every point of `T`. -/
@[stacks 0EJE "the canonical map (ℱₙ) → (ℱ'ₙ) of inverse systems of coherent modules, and its \
property (1); properties (2) and (3), which identify (ℱ'ₙ) pro-isomorphically with an object \
of Coh(X, ℐ), are not covered: they rest on Tag 0EIE, which this library does not carry"]
theorem isDepthOneQuotient_toImprovedSystem_app (n : ℕᵒᵖ) :
    IsDepthOneQuotient T ((toImprovedSystem T hT F).app n) :=
  depthOneQuotient_spec X T hT (F.obj n)

/-- **Stacks Project, Tag 0EJE, property (1).** Every term of the improved system has depth at
least one at each point of `T`. -/
theorem one_le_depth_improvedSystem_stalk (n : ℕᵒᵖ) (x : X) (hx : x ∈ T) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) ((improvedSystem T hT F).obj n).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) ((improvedSystem T hT F).obj n).val x
    (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) ((improvedSystem T hT F).obj n).val.presheaf x) :=
  (depthOneQuotient_spec X T hT (F.obj n)).2.2.2 x hx

include hT in
/-- A coherent adic system along an ideal sheaf admits a map to an inverse system of coherent
modules each of whose terms is the quotient of the corresponding term by its sections supported
on `T`, hence has depth at least one along `T`. -/
@[stacks 0EJE "the canonical map out of an object of Coh(X, ℐ) and its property (1)"]
theorem exists_improving_map_of_coherentAdicSystem {I : X.IdealSheafData}
    (F : Stacks.Coherent.CoherentAdicSystems I) :
    ∃ (G : ℕᵒᵖ ⥤ X.Modules) (τ : F.obj ⟶ G), ∀ n : ℕᵒᵖ, IsDepthOneQuotient T (τ.app n) := by
  have : ∀ n : ℕᵒᵖ, (F.obj.obj n).IsCoherent := fun n => F.property.1 n.unop
  exact ⟨improvedSystem T hT F.obj, toImprovedSystem T hT F.obj,
    isDepthOneQuotient_toImprovedSystem_app T hT F.obj⟩

end Stacks.Algebraization

end

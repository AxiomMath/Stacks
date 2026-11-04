module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.PointFiber
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint

/-!
# A constructible sheaf with flat stalks is constructible flat

Let `Λ` be a Noetherian ring and `F` a constructible sheaf of `Λ`-modules on the small étale site
of `X`. If every étale stalk of `F` is a flat `Λ`-module, then `F` is constructible flat: on each
stratum of a constructible stratification of an affine open, `F` is locally constant with finite
projective values.

## Main results

* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_of_flat_etaleModuleStalk` — a constructible
  sheaf of `Λ`-modules whose étale stalks are flat is constructible flat.
* `AlgebraicGeometry.exists_iso_etaleModuleStalk_of_constant` — a constant value of the inverse
  image of a sheaf to an object with a point is an étale stalk of the sheaf.
* `AlgebraicGeometry.ofArrows_nonempty_mem_topology` — discarding the members with empty
  underlying scheme from a covering family of the small étale site leaves a covering family.

## Implementation notes

The constant value `E` of `F` over a member `V` of a trivialising covering of a stratum is
identified with an étale stalk of `F` at a geometric point of `V`, through the constant-sheaf
fibre (`CategoryTheory.GrothendieckTopology.Point.constantFiberIso`), the fibre at a localized
point (Stacks 04H2, `CategoryTheory.GrothendieckTopology.Point.sheafFiberOverIso`) and the
compatibility of inverse image with stalks (Stacks 03Q1,
`AlgebraicGeometry.smallEtalePullbackSheafFiberIso`). A member with empty underlying scheme has
no geometric point; such members are discarded first, which leaves a covering family, since the
empty sieve covers an object with empty underlying scheme.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r

namespace AlgebraicGeometry

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u})

/-- Discarding the members with empty underlying scheme from a covering family of the small
étale site leaves a covering family: an object with empty underlying scheme is covered by the
empty sieve. -/
theorem ofArrows_nonempty_mem_topology (Y : B.Scheme) {U : SmallEtale B Y.obj Y.property}
    {I : Type*} (V : I → SmallEtale B Y.obj Y.property) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ SmallEtale.topology B Y.obj Y.property U) :
    Sieve.ofArrows (fun j : {i // Nonempty ((SmallEtale.toScheme B Y.obj Y.property).obj (V i))} =>
        V j.1) (fun j => f j.1) ∈ SmallEtale.topology B Y.obj Y.property U := by
  refine (SmallEtale.topology B Y.obj Y.property).transitive hf _ (fun W g hg => ?_)
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).1 hg
  by_cases hi : Nonempty ((SmallEtale.toScheme B Y.obj Y.property).obj (V i))
  · rw [Sieve.pullback_eq_top_of_mem _ (Sieve.downward_closed _
      (Sieve.ofArrows_mk _ (fun j : {i // Nonempty ((SmallEtale.toScheme B Y.obj Y.property).obj
        (V i))} => f j.1) ⟨i, hi⟩) h)]
    exact (SmallEtale.topology B Y.obj Y.property).top_mem W
  · have hW : IsEmpty ((SmallEtale.toScheme B Y.obj Y.property).obj W) :=
      ⟨fun x => hi ⟨((SmallEtale.toScheme B Y.obj Y.property).map h).base x⟩⟩
    exact (SmallEtale.topology B Y.obj Y.property).superset_covering bot_le
      (Stacks.EtaleCohomology.bot_mem_topology B Y.property hW)

variable (X : B.Scheme) (Λ : Type r) [CommRing Λ]

/-- **A constant value of the inverse image of `F` to an object over `X` is an étale stalk of
`F`.** If the inverse image of `F` along `g : Y ⟶ X`, restricted to an object `V` of the small
étale site of `Y` with a point, is the constant sheaf on `E`, then `E` is isomorphic to the étale
stalk of `F` at a geometric point of `X`. -/
theorem exists_iso_etaleModuleStalk_of_constant {Y : B.Scheme} (g : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (V : SmallEtale B Y.obj Y.property)
    (v : (SmallEtale.toScheme B Y.obj Y.property).obj V) (E : ModuleCat.{max (u + 1) r} Λ)
    (e : (constantSheaf ((SmallEtale.topology B Y.obj Y.property).over V)
        (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
      ((SmallEtale.topology B Y.obj Y.property).overPullback (ModuleCat.{max (u + 1) r} Λ) V).obj
        (((smallEtaleBaseChange B g).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Y.obj Y.property)).obj F)) :
    ∃ s : GeometricPoint X.obj,
      Nonempty (E ≅ (etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj F) := by
  let t₀ := GeometricPoint.ofPoint ((SmallEtale.toScheme B Y.obj Y.property).obj V) v
  let t : GeometricPoint Y.obj := t₀.map (B.inclusion.map V.obj.hom)
  let q := geometricPointSitePoint B Y.obj Y.property t
  let y : q.fiber.obj V := ⟨t₀.hom, rfl⟩
  exact ⟨t.map (B.inclusion.map g),
    ⟨(GrothendieckTopology.Point.constantFiberIso _ _ (q.over y) E).symm ≪≫
      (q.over y).sheafFiber.mapIso e ≪≫
      (GrothendieckTopology.Point.sheafFiberOverIso q y (ModuleCat.{max (u + 1) r} Λ)).app _ ≪≫
      (smallEtalePullbackSheafFiberIso B g t (ModuleCat.{max (u + 1) r} Λ)).app F⟩⟩

/-- **A constructible sheaf of `Λ`-modules with flat étale stalks is constructible flat**, for a
Noetherian ring `Λ`. -/
public theorem isConstructibleFlatModuleSheaf_of_flat_etaleModuleStalk [IsNoetherianRing Λ]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F)
    (hflat : ∀ s : GeometricPoint X.obj,
      Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj F)) :
    IsConstructibleFlatModuleSheaf B X Λ F := by
  intro U
  obtain ⟨σ, hσ⟩ := hF U
  refine ⟨σ, fun i U' => ?_⟩
  obtain ⟨I, V, f, hcov, hloc⟩ := hσ i U'
  refine ⟨{j // Nonempty ((SmallEtale.toScheme B (σ.piece i).obj (σ.piece i).property).obj
      (V j))}, fun j => V j.1, fun j => f j.1,
    ofArrows_nonempty_mem_topology B (σ.piece i) V f hcov, fun j => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hloc j.1
  obtain ⟨v⟩ := j.2
  obtain ⟨s, ⟨eE⟩⟩ := exists_iso_etaleModuleStalk_of_constant B X Λ (σ.inclusion i) F (V j.1) v E e
  have : Module.Finite Λ E := by rwa [ModuleCat.isFG_iff] at hE
  have := hflat s
  have : Module.Flat Λ E := Module.Flat.of_linearEquiv eE.toLinearEquiv
  have : Module.FinitePresentation Λ E := Module.finitePresentation_of_finite Λ E
  exact ⟨E, inferInstance, Module.Flat.projective_of_finitePresentation, ⟨e⟩⟩

end AlgebraicGeometry

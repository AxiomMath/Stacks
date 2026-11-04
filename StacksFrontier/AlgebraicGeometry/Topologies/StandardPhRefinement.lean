module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardCoveringsReindex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Refinements by standard ph coverings

A *standard ph covering* of an affine scheme `T`, `AlgebraicGeometry.StandardPHCovering`, is
a finite family of morphisms from affine schemes obtained by restricting a proper surjective
morphism `g : U ⟶ T` to the members of a finite affine open covering of `U`.

The first result here is the first half of Stacks 0DBF: every Zariski open covering of an affine
scheme is refined by a standard ph covering. This is the degenerate case of the definition in
which the proper surjective morphism is the identity of `T`, so the content is that an open
covering of a quasi-compact scheme is refined by a *finite* family of open immersions with
*affine* source.

Stacks 0DBH follows: a Zariski open covering of an arbitrary scheme is a ph covering, since the
base change of such a covering to an affine open of the target is again a Zariski open covering.

## Main results

* `AlgebraicGeometry.exists_finite_affine_refinement`: an open covering of a quasi-compact
  scheme is refined by a finite family of open immersions with affine source.
* `AlgebraicGeometry.exists_standardPHCovering_refinement_of_openCover`: every Zariski open
  covering of an affine scheme is refined by a standard ph covering.
* `AlgebraicGeometry.IsPHCovering.of_openCover`: every Zariski open covering is a ph covering.

## Implementation notes

Families of morphisms with fixed target are `CategoryTheory.PreZeroHypercover`, and a
refinement is a `CategoryTheory.PreZeroHypercover.Hom`.

`AlgebraicGeometry.exists_finite_affine_refinement` produces its index type as
`ULift (Fin n)`, which is the only way to land a finite type in a prescribed universe `v` that
is unrelated to the universe `u` of the schemes. For the same reason Mathlib's
`AlgebraicGeometry.Scheme.OpenCover.fromAffineRefinement` cannot be used: morphisms in the
category of covers of a scheme are only defined between covers indexed in a *single* universe,
while `Scheme.OpenCover.affineRefinement` raises the index universe from `v` to `max v u`. The
refinement is therefore built by hand, from the affine open covers of the members of the given
cover, before being cut down to a finite subcover and reindexed.

`AlgebraicGeometry.IsPHCovering` asks for a refining standard ph covering indexed in the
universe `u` of the schemes, whereas the refinement produced above is indexed in the universe
`v` of the index type of the given covering. The two are reconciled by
`AlgebraicGeometry.StandardPHCovering.reindex`, which transports a standard ph covering along
a bijection of index types, the index type here being finite.

## References

* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
* [Stacks Project, Tag 0DBH](https://stacks.math.columbia.edu/tag/0DBH)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- An open covering of a quasi-compact scheme `T` is refined by a *finite* family of open
immersions into `T` with *affine* source.

The refining family is obtained by covering each member of the given covering by affine opens,
extracting a finite subcover of the resulting covering of `T`, and reindexing it by a finite
type in the universe of the given covering's index type. -/
@[sga "3 IV 6.3" "(c)"]
theorem exists_finite_affine_refinement {T : Scheme.{u}} [CompactSpace T] (U : T.OpenCover.{v}) :
    ∃ E : PreZeroHypercover.{v} T, Finite E.I₀ ∧ (∀ i, IsAffine (E.X i)) ∧
      (∀ i, IsOpenImmersion (E.f i)) ∧ (⋃ i, Set.range (E.f i)) = Set.univ ∧
      Nonempty (E.Hom U.toPreZeroHypercover) := by
  classical
  -- For a point `x` of `T`, pick a member of `U` whose range contains `x`, a preimage `y x` of
  -- `x` in it, and an affine open of that member whose range contains `y x`.
  set k : T → U.I₀ := fun x => U.idx x
  set y : ∀ x : T, U.X (k x) := fun x => (U.covers x).choose
  set 𝒞 : ∀ x : T, (U.X (k x)).AffineOpenCover := fun x => (U.X (k x)).affineOpenCover
  set m : ∀ x : T, (𝒞 x).I₀ := fun x => (𝒞 x).idx (y x)
  set h : ∀ x : T, Spec ((𝒞 x).X (m x)) ⟶ U.X (k x) := fun x => (𝒞 x).f (m x)
  -- These affine opens cover `T`, so they form an open covering of `T` indexed by its points.
  let 𝒲 : T.OpenCover.{u} :=
    Scheme.Cover.mkOfCovers T (fun x => Spec ((𝒞 x).X (m x))) (fun x => h x ≫ U.f (k x))
      (fun x => by
        obtain ⟨z, hz⟩ := (𝒞 x).covers (y x)
        exact ⟨x, z, by
          rw [Scheme.Hom.comp_apply, show h x z = y x from hz, (U.covers x).choose_spec]⟩)
  -- Cut it down to a finite subcover and reindex it by a finite type in `Type v`.
  let 𝒱 := 𝒲.finiteSubcover
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin 𝒱.I₀
  let e' : ULift.{v} (Fin n) ≃ 𝒱.I₀ := Equiv.ulift.trans e.symm
  refine ⟨{ I₀ := ULift.{v} (Fin n), X := fun i => 𝒱.X (e' i), f := fun i => 𝒱.f (e' i) },
    inferInstance, fun i => ?_, fun i => inferInstance, ?_, ⟨?_⟩⟩
  · show IsAffine (Spec _)
    infer_instance
  · rw [e'.surjective.iUnion_comp fun j => Set.range (𝒱.f j)]
    exact 𝒱.iUnion_range
  · exact { s₀ := fun i => k (𝒲.idx (e' i).1)
            h₀ := fun i => h (𝒲.idx (e' i).1)
            w₀ := fun _ => rfl }

/-- **Stacks Project, Tag 0DBF, part (1).** Every Zariski open covering of an affine scheme has
a refinement which is a standard ph covering.

The standard ph covering is the finite affine refinement of
`AlgebraicGeometry.exists_finite_affine_refinement`, presented by the identity of `T`, which is
proper and surjective. -/
@[stacks 0DBF "part (1)"]
theorem exists_standardPHCovering_refinement_of_openCover {T : Scheme.{u}} [IsAffine T]
    (U : T.OpenCover.{v}) :
    ∃ E : PreZeroHypercover.{v} T,
      StandardPHCovering E.f ∧ Nonempty (E.Hom U.toPreZeroHypercover) := by
  obtain ⟨E, _, haff, hopen, hunion, hhom⟩ := exists_finite_affine_refinement U
  exact ⟨E, ⟨inferInstance, haff, T, 𝟙 T, E.f, inferInstance, inferInstance, hopen, hunion,
    fun _ => Category.comp_id _⟩, hhom⟩

/-- **Stacks Project, Tag 0DBH.** A Zariski open covering of a scheme is a ph covering.

Over an affine open `V` of the target, the base change of the covering is again a Zariski open
covering, so `AlgebraicGeometry.exists_standardPHCovering_refinement_of_openCover` refines it by
a standard ph covering; that covering is then reindexed into the universe of the schemes by
`AlgebraicGeometry.StandardPHCovering.reindex`. -/
@[stacks 0DBH]
theorem IsPHCovering.of_openCover {T : Scheme.{u}} (𝒰 : T.OpenCover.{v}) :
    IsPHCovering 𝒰.X 𝒰.f := by
  refine ⟨fun i => inferInstance, fun V hV => ?_⟩
  have : IsAffine V.toScheme := hV
  obtain ⟨E, hE, ⟨φ⟩⟩ := exists_standardPHCovering_refinement_of_openCover (𝒰.pullback₂ V.ι)
  -- `E` is indexed in `Type v`; reindex it by a finite type in `Type u`.
  have : Finite E.I₀ := hE.finite
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin E.I₀
  let e' : ULift.{u} (Fin n) ≃ E.I₀ := Equiv.ulift.trans e.symm
  exact ⟨E.reindex e', hE.reindex e', ⟨(E.restrictIndexHom e').comp φ⟩⟩

end AlgebraicGeometry

end

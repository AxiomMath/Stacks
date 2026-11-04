module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyPrincipal
public import StacksFrontier.Topology.Dimension.OpenGeneralizingMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree

/-!
# A finite endomorphism of a regular variety is flat

Let `X` be an integral scheme of finite type over a field whose local rings are regular, and let
`f : X ⟶ X` be finite. Then `f` is surjective and flat. This is the flatness step in the proof of
[Stacks, Tag 0BFG], where `X` is an abelian variety and `f` is multiplication by `d`.

## Main results

* `AlgebraicGeometry.surjective_of_locallyQuasiFinite_of_isClosedMap`: a locally quasi-finite
  closed endomorphism of an irreducible scheme of finite dimension is surjective.
* `AlgebraicGeometry.ringKrullDim_quotient_map_maximalIdeal_eq_zero_of_quasiFinite`: the fibre
  ring `S/𝔪_R S` of a quasi-finite local homomorphism has dimension zero.
* `AlgebraicGeometry.flat_of_isFinite_of_isRegularLocalRing`: a finite endomorphism of a variety
  with regular local rings is flat, by miracle flatness ([Stacks, Tag 00R4]).

## References

* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **A locally quasi-finite endomorphism of an irreducible scheme of finite Krull dimension that
is a closed map is surjective.** Its image is closed, and of the same dimension as the source,
because a locally quasi-finite morphism identifies no two distinct points one of which
specializes the other; a proper closed subset of an irreducible space of finite dimension has
smaller dimension. -/
theorem surjective_of_locallyQuasiFinite_of_isClosedMap {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ X) [LocallyQuasiFinite f] (hcl : IsClosedMap f) (hfin : topologicalKrullDim X ≠ ⊤) :
    Function.Surjective f := by
  rw [← Set.range_eq_univ]
  by_contra hne
  set Z := Set.range f with hZ
  have hZc : IsClosed Z := hcl.isClosed_range
  have hZss : Z ⊂ (Set.univ : Set X) := Set.ssubset_univ_iff.mpr hne
  -- `dim X ≤ dim Z`
  have hle : topologicalKrullDim X ≤ topologicalKrullDim Z := by
    refine Topology.topologicalKrullDim_le_of_injOn_specializes (Set.rangeFactorization f)
      (f.continuous.subtype_mk _) fun a b hab hfab => ?_
    have hfab' : f a = f b := congrArg Subtype.val hfab
    exact (f.isDiscrete_preimage_singleton (f b)).eq_of_specializes hab hfab' rfl
  have hbot : topologicalKrullDim X ≠ ⊥ :=
    Order.krullDim_ne_bot_iff.mpr ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hm' : m ≠ ⊤ := fun h => hfin (by rw [← hm, h]; rfl)
  lift m to ℕ using hm'
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp ((show ((m : ℕ) : WithBot ℕ∞) ≤ _ from
    hm ▸ le_rfl).trans hle)
  have h := succ_le_topologicalKrullDim_of_ssubset hZc (IrreducibleSpace.isIrreducible_univ X)
    hZss p
  have huniv : topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph
  rw [huniv, ← hm, hp] at h
  exact absurd (WithBot.coe_le_coe.mp h) (by exact_mod_cast Nat.not_succ_le_self m)

/-- **A finite endomorphism of a variety with regular local rings is flat** (and surjective). It is
surjective by `AlgebraicGeometry.surjective_of_locallyQuasiFinite_of_isClosedMap`, hence dominant,
so by the dimension formula ([Stacks, Tag 02JU], the base being universally catenary) it preserves
the dimensions of the local rings; its fibre rings have dimension zero; and miracle flatness
([Stacks, Tag 00R4]) applies at every point, regular local rings being Cohen–Macaulay. -/
theorem flat_of_isFinite_of_isRegularLocalRing (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType p] [QuasiCompact p]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (f : X ⟶ X) [IsFinite f] :
    Flat f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : Surjective f := ⟨surjective_of_locallyQuasiFinite_of_isClosedMap f f.isClosedMap
    (topologicalKrullDim_ne_top_of_locallyOfFiniteType k p)⟩
  have : LocallyOfFiniteType f := inferInstance
  have hS := Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field k p
  rw [Flat.iff_flat_stalkMap]
  intro x
  let : Algebra (X.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have := hreg (f x)
  have := hreg x
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.QuasiFinite (X.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    have h : (f.stalkMap x).hom.QuasiFinite := f.quasiFiniteAt x
    rwa [← RingHom.algebraMap_toAlgebra (f.stalkMap x).hom, RingHom.quasiFinite_algebraMap] at h
  have hCM :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      (X.presheaf.stalk x)).2
  change Module.Flat _ _
  refine Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add hCM ?_
  rw [ringKrullDim_quotient_map_maximalIdeal_eq_zero_of_quasiFinite, add_zero]
  exact ringKrullDim_stalk_eq_of_locallyQuasiFinite f hS x

end AlgebraicGeometry

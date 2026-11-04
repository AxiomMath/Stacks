module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.ZeroLimit

/-!
# The surjectivity condition after base change is limit preserving on affine schemes

Let `u : F ⟶ G` be a homomorphism of quasi-coherent modules on a scheme `X` over `S`, with `G`
of finite type and `X ⟶ S` quasi-compact.  If an inverse system of affine schemes over `S`,
indexed by a cofiltered category, has limit `T`, and if `u` becomes surjective after base change
to `T`, then it already becomes surjective after base change to one of the stages.

## Main definitions

* `Stacks.Flatness.ModuleMapBaseChangeSituation.cokernelSituation`: the situation obtained by
  replacing the homomorphism by the projection of its target onto its cokernel.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.isSurjectiveAfterBaseChange_iff_cokernel`:
  surjectivity of a base change of the homomorphism is vanishing of the corresponding base
  change of the projection onto the cokernel.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.exists_isSurjectiveAfterBaseChange_of_isColimit`
  and `…surjectivityFunctor_preservesColimit_of_isAffine`.

## Implementation notes

Surjectivity is reduced to the vanishing already treated in
`StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.ZeroLimit`.  Inverse image of modules
along a morphism of schemes is a left adjoint, so it is right exact: it carries the cokernel of
the homomorphism to the cokernel of its base change, and the projection onto the cokernel to an
epimorphism.  A morphism in an additive category with a cokernel is an epimorphism exactly when
that cokernel is a zero object, so the base change of the homomorphism is surjective exactly
when the base change of the projection onto its cokernel is zero.  The hypothesis that the
target is of finite type becomes the hypothesis of the vanishing statement, which asks the
source of its situation to be of finite type.

## References

* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

/-- **The cokernel situation.**  The situation with the same morphism of schemes whose
homomorphism of quasi-coherent modules is the projection of the target onto the cokernel. -/
noncomputable def cokernelSituation (D : ModuleMapBaseChangeSituation.{u}) :
    ModuleMapBaseChangeSituation.{u} where
  S := D.S
  X := D.X
  f := D.f
  F := D.G
  G := cokernel D.hom
  hom := cokernel.π D.hom

/-- **Surjectivity after base change is vanishing of the projection onto the cokernel after base
change.**  Inverse image of modules is right exact, so it carries the cokernel of the
homomorphism to the cokernel of its base change; a morphism is an epimorphism exactly when its
cokernel is a zero object. -/
theorem isSurjectiveAfterBaseChange_iff_cokernel (D : ModuleMapBaseChangeSituation.{u})
    (T : Over D.S) :
    D.IsSurjectiveAfterBaseChange T ↔ (cokernelSituation D).IsZeroAfterBaseChange T := by
  set P := Scheme.Modules.pullback (pullback.fst D.f T.hom) with hP
  have hpres : PreservesColimitsOfSize.{0, 0} P :=
    Adjunction.leftAdjoint_preservesColimits
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.fst D.f T.hom))
  have he : P.obj (cokernel D.hom) ≅ cokernel (P.map D.hom) := PreservesCokernel.iso P D.hom
  have hepi : Epi (P.map (cokernel.π D.hom)) :=
    preserves_epi_of_preservesColimit P (cokernel.π D.hom)
  change Epi (P.map D.hom) ↔ P.map (cokernel.π D.hom) = 0
  rw [Preadditive.epi_iff_isZero_cokernel]
  refine ⟨fun hu => (IsZero.of_iso hu he).eq_of_tgt _ 0, fun hv => IsZero.of_iso ?_ he.symm⟩
  exact (IsZero.iff_id_eq_zero _).2 ((cancel_epi (P.map (cokernel.π D.hom))).1 (by simp [hv]))

/-- **The surjectivity condition after base change descends to a stage.**  If an inverse system
of affine schemes over the base, indexed by a cofiltered category in the universe of the
schemes, has limit `T` and the homomorphism of the situation becomes surjective after base
change to `T`, then it already becomes surjective after base change to one of the stages. -/
theorem exists_isSurjectiveAfterBaseChange_of_isColimit (D : ModuleMapBaseChangeSituation.{u})
    [QuasiCompact D.f] [D.G.IsFiniteType] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (T : I ⥤ Over D.S) (hT : ∀ i, IsAffine (T.obj i).left) (c : Cocone T.op)
    (hc : IsColimit c) (h : D.IsSurjectiveAfterBaseChange c.pt.unop) :
    ∃ i, D.IsSurjectiveAfterBaseChange (T.obj i) := by
  have hqc : QuasiCompact (cokernelSituation D).f := inferInstanceAs (QuasiCompact D.f)
  have hft : (cokernelSituation D).F.IsFiniteType := inferInstanceAs D.G.IsFiniteType
  obtain ⟨i, hi⟩ := exists_isZeroAfterBaseChange_of_isColimit (cokernelSituation D) T hT c hc
    ((D.isSurjectiveAfterBaseChange_iff_cokernel c.pt.unop).1 h)
  exact ⟨i, (D.isSurjectiveAfterBaseChange_iff_cokernel (T.obj i)).2 hi⟩

/-- **Stacks Project, Tag 05MJ.**  The surjectivity functor of a homomorphism of quasi-coherent
modules with target of finite type, along a quasi-compact morphism, preserves the filtered
colimit attached to a cofiltered inverse system of affine schemes over the base. -/
@[stacks 05MJ "surj_limit"]
theorem surjectivityFunctor_preservesColimit_of_isAffine (D : ModuleMapBaseChangeSituation.{u})
    [QuasiCompact D.f] [D.G.IsFiniteType] (I : Type u) [Category.{u} I] [IsCofiltered I]
    (T : I ⥤ Over D.S) (hT : ∀ i, IsAffine (T.obj i).left) :
    PreservesColimit T.op D.surjectivityFunctor := by
  classical
  refine ⟨fun {c} hc => ⟨Types.FilteredColimit.isColimitOf (T.op ⋙ D.surjectivityFunctor)
    (D.surjectivityFunctor.mapCocone c) (fun x => ?_) fun j k x y _ => ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_isSurjectiveAfterBaseChange_of_isColimit D T hT c hc x.down
    exact ⟨op i, ⟨hi⟩, rfl⟩
  · obtain ⟨l, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j k
    exact ⟨l, f, g, rfl⟩

end Stacks.Flatness.ModuleMapBaseChangeSituation

end

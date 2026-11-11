module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyFlatPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace

/-!
# Flatness of the solution of a contraction problem over a Dedekind base

Let `s` be a solution of Artin's contraction problem of Stacks 0GH8 with target `X`, over an
affine base `S` whose ring of functions `Γ(S)` is a Dedekind domain, such that the open subspace
`U ≅ U'` has point set `|X| ∖ T`, `X'` is a scheme `Z` flat over `S`, and `W` is the completion of
`Spec A` at its closed point for an adically complete local `Γ(S)`-algebra `A` with algebraically
closed residue field on which no nonzero element of `Γ(S)` is a zero divisor. If `X` is locally of
finite type over `S`, then `X` is flat over `S`.

This is the flatness of the family of curves of Stacks 0D5E.

The proof is chart by chart and point by point. At a point of an étale chart `V ⟶ X` lying over
`|X| ∖ T`, an open neighbourhood of the point maps étale to `U ≅ U' ⊆ Z`, which is flat over `S`.
At a point over `T`, the local ring is torsion free over `Γ(S)`
(`AlgebraicGeometry.Artin.ContractionSituation.Solution.flat_stalkMap_of_mem_T`).

## Main results

* `AlgebraicGeometry.Space.isFlat_terminal_from_of_forall_chart`: an algebraic space is flat
  over `S` once every étale chart of it is.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.flat_stalkMap_of_not_mem_T`: flatness
  of a chart at a point over `|X| ∖ T`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.isFlat_terminal_from`: `X` is flat over
  `S`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An algebraic space over `S` is flat over `S` as soon as the structure morphism of every étale
chart of it is flat: by Stacks 03MJ it suffices to test one surjective étale chart of the source
against the identity chart of the terminal object `S`. -/
theorem isFlat_terminal_from_of_forall_chart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (h : ∀ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ X),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a → Flat (B.inclusion.map V.hom)) :
    IsFlat B S hS (terminal.from X) := by
  obtain ⟨V, q, hqs, hqe⟩ := hX.exists_atlas
  have hterm := isTerminal_yoneda_obj_terminal B S hS
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map (terminal.from V)) := by
    have := h V q hqe
    have e : (BigFppfOver.toScheme B S hS).map (terminal.from V) =
        B.inclusion.map V.hom ≫ (toSchemeTerminalIso B S hS).inv := by
      rw [← toScheme_map_terminal_from B S hS V, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [e]
    infer_instance
  have h1 : HoldsOnEveryEtaleChart B S hS (@Flat.{u} : MorphismProperty Scheme.{u})
      (hterm.from X) :=
    (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _ Flat.isEtaleLocalOnSourceAndTarget hX
      (isAlgebraicSpace_yoneda B S hS _) (hterm.from X)).2
      ⟨V, ⊤_ (BigFppfOver B S hS), q, 𝟙 _, terminal.from V, hqe, presheaf_etale_id B S hS _,
        hqs, hterm.hom_ext _ _, hflat⟩
  exact holdsOnEveryEtaleChart_of_isTerminal B S hS hterm terminalIsTerminal _ _ h1

end Space

namespace Artin.ContractionSituation.Solution

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : Solution c X)

/-- **Flatness at a point over `|X| ∖ T`.** Let `a : V ⟶ X` be an étale chart and `v ∈ V` a
point not over `T`. The points of `V` not over `T` form an open neighbourhood `O` of `v` whose
chart factors through `U ≅ U' ⊆ X' ≅ Z`, étale; so `O` is flat over `S` since `Z` is. -/
theorem flat_stalkMap_of_not_mem_T
    (hU : Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ)
    {Zo : BigFppfOver B S hS} (eZ : c.X' ≅ yoneda.obj Zo) (hZ : Flat (B.inclusion.map Zo.hom))
    {V : BigFppfOver B S hS} (a : yoneda.obj V ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : Space.pointsMap B S hS (yoneda.obj V) a
      ((Space.schemePointsHomeomorph B S hS V).symm v) ∉ s.T) :
    ((B.inclusion.map V.hom).stalkMap v).hom.Flat := by
  let φ : (BigFppfOver.toScheme B S hS).obj V → Space.points B S hS X :=
    fun y => Space.pointsMap B S hS (yoneda.obj V) a
      ((Space.schemePointsHomeomorph B S hS V).symm y)
  have hφ : Continuous φ :=
    (Space.continuous_pointsMap B S hS a).comp
      (Space.schemePointsHomeomorph B S hS V).symm.continuous
  let O : ((BigFppfOver.toScheme B S hS).obj V).Opens :=
    ⟨φ ⁻¹' s.Tᶜ, s.isClosed_T.isOpen_compl.preimage hφ⟩
  have hvO : v ∈ O := hv
  let V' : BigFppfOver B S hS :=
    Over.mk (Y := B.obj (Scheme.size_lt_of_isOpenImmersion O.ι V.left.property))
      (ObjectProperty.homMk (O.ι ≫ V.hom.hom))
  let i : V' ⟶ V := Over.homMk (ObjectProperty.homMk O.ι)
  have hiE : Etale ((BigFppfOver.toScheme B S hS).map i) := by
    change Etale O.ι
    infer_instance
  have ha'E : Space.IsEtale B S hS (yoneda.map i ≫ a) :=
    Space.isEtale_comp B S hS ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((Space.presheaf_yoneda_map_etale_iff B S hS i).2 hiE))
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS a).2 ha)
  have hrange : Set.range (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map i ≫ a)) ⊆
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) := by
    rw [hU]
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := (Space.schemePointsHomeomorph B S hS V').symm.surjective z
    rw [Space.pointsMap_comp, Function.comp_apply, Space.schemePointsHomeomorph_symm_naturality]
    exact y.2
  obtain ⟨g, hg⟩ := (Space.factorsThrough_openSubspace_iff_points B S hS s.isAlgebraicSpace_X
    (isAlgebraicSpace_yoneda B S hS V') s.U s.isOpenSubspace_U (yoneda.map i ≫ a)).2 hrange
  let k' : yoneda.obj V' ⟶ yoneda.obj Zo := g ≫ s.isoU.inv ≫ c.U'.ι ≫ eZ.hom
  have hk'E : Space.IsEtale B S hS k' :=
    Space.isEtale_comp B S hS (Space.isEtale_of_isEtale_over B S hS
        (isAlgebraicSpace_yoneda B S hS V') s.isOpenSubspace_U.1 s.isAlgebraicSpace_X g
        (yoneda.map i ≫ a) s.U.ι ha'E (Space.isEtale_of_isOpenImmersion B S hS
          s.isOpenSubspace_U.2) hg)
      (Space.isEtale_comp B S hS (Space.isEtale_of_isIso B S hS _)
        (Space.isEtale_comp B S hS (Space.isEtale_of_isOpenImmersion B S hS
          c.isOpenSubspace_U'.2) (Space.isEtale_of_isIso B S hS _)))
  let k : V' ⟶ Zo := yoneda.preimage k'
  have hkE : Etale ((BigFppfOver.toScheme B S hS).map k) :=
    (Space.presheaf_yoneda_map_etale_iff B S hS k).1 (by
      rw [Functor.map_preimage]
      exact (Space.isEtale_iff_presheaf_of_yoneda B S hS k').1 hk'E)
  have := hZ
  have hflat' : Flat (O.ι ≫ B.inclusion.map V.hom) := by
    have hw : O.ι ≫ B.inclusion.map V.hom =
        (BigFppfOver.toScheme B S hS).map k ≫ B.inclusion.map Zo.hom :=
      (congrArg (fun m => m.hom) (Over.w k)).symm
    rw [hw]
    infer_instance
  let x : O.toScheme := ⟨v, hvO⟩
  have hfl := Flat.stalkMap (O.ι ≫ B.inclusion.map V.hom) x
  rw [Scheme.Hom.stalkMap_comp O.ι (B.inclusion.map V.hom) x] at hfl
  have : IsIso (O.ι.stalkMap x) := inferInstance
  exact (RingHom.Flat.comp_iff_of_bijective_left (g := (O.ι.stalkMap x).hom)
    (ConcreteCategory.bijective_of_isIso _)).1 hfl

variable [IsAffine S]

/-- **Flatness of the contraction over a Dedekind base (Stacks 0D5E).** Let `S` be affine with
`Γ(S)` a Dedekind domain, and let `s` be a solution of the contraction problem with target `X`,
locally of finite type over `S`, such that `U` has point set `|X| ∖ T`, `X'` is a scheme flat over
`S`, and `W` is the completion of `Spec A` at its closed point, `A` an adically complete local
`Γ(S)`-algebra with algebraically closed residue field on which no nonzero element of `Γ(S)` is
a zero divisor. Then `X` is flat over `S`. -/
theorem isFlat_terminal_from [IsDomain Γ(S, ⊤)] [IsDedekindDomain Γ(S, ⊤)]
    (hU : Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ)
    {Zo : BigFppfOver B S hS} (eZ : c.X' ≅ yoneda.obj Zo) (hZ : Flat (B.inclusion.map Zo.hom))
    {A : Type u} [CommRing A] [IsLocalRing A] [Algebra Γ(S, ⊤) A]
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAt : ∀ r : Γ(S, ⊤), r ≠ 0 → IsSMulRegular A r)
    (hA : B.Contains (Spec (.of A)))
    (eW : c.W ≅ Space.completionSheaf B S hS
      (yoneda.obj (Space.specOver B S hS S.isoSpec.inv A hA))
      {(Space.schemePointsHomeomorph B S hS (Space.specOver B S hS S.isoSpec.inv A hA)).symm
        (IsLocalRing.closedPoint A)})
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    Space.IsFlat B S hS (terminal.from X) := by
  refine Space.isFlat_terminal_from_of_forall_chart s.isAlgebraicSpace_X fun V a ha => ?_
  refine Flat.of_stalkMap _ fun v => ?_
  by_cases hv : Space.pointsMap B S hS (yoneda.obj V) a
      ((Space.schemePointsHomeomorph B S hS V).symm v) ∈ s.T
  · have := c.isLocallyNoetherian_base
    have := Space.isLocallyNoetherian_of_presheafEtale B S hS hft V a ha
    let : Algebra Γ(S, ⊤) (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) :=
      (Space.chartStalkStructureMap V v).hom.toAlgebra
    exact s.flat_stalkMap_of_mem_T eW a rfl hv ha hAc hAt
  · exact s.flat_stalkMap_of_not_mem_T hU eZ hZ a ha v hv

end Artin.ContractionSituation.Solution

end AlgebraicGeometry

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusPullback
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.DescentTopology

/-!
# Locality of the generic-rank condition

For the family of Situation 05MP, the condition that the module pulled back to `X ×_S T` is free
of rank `p` near the generic point of every fibre over `T` is local on `T` for the Zariski
topology, and the rank `p` for which it holds is determined by the fibre over any one point. A
morphism representing the generic-rank functor of a module of finite presentation is locally of
finite presentation. Finally, the complement of a closed immersion of finite presentation into
an affine scheme is quasi-compact.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.condition_of_openCover`: the generic-rank
  condition holds over a scheme as soon as it holds over each member of an open cover.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.eq_of_condition_of_condition_residueField`:
  the rank is determined by the fibre over the spectrum of a residue field.
* `locallyOfFinitePresentation_hom_of_representableBy`, in the namespace
  `AlgebraicGeometry.FreeAtGenericPointsSituation`: a representative of the generic-rank functor
  of a finitely presented module is locally of finite presentation.
* `AlgebraicGeometry.isCompact_compl_range_of_isClosedImmersion`: the complement of a closed
  immersion locally of finite presentation into an affine scheme is quasi-compact.

## References

* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
* [Stacks Project, Tag 05LX](https://stacks.math.columbia.edu/tag/05LX)
* [Stacks Project, Tag 054H](https://stacks.math.columbia.edu/tag/054H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite

universe u

namespace AlgebraicGeometry

/-- The complement of a closed immersion locally of finite presentation into an affine scheme is
quasi-compact. -/
theorem isCompact_compl_range_of_isClosedImmersion {V Z : Scheme.{u}} [IsAffine V] (i : Z ⟶ V)
    [IsClosedImmersion i] [LocallyOfFinitePresentation i] : IsCompact (Set.range i.base)ᶜ := by
  rw [← Set.image_univ]
  exact ConnectedComponentSection.isCompact_of_isConstructible
    (isConstructible_compl.mpr (i.isConstructible_image IsConstructible.univ))

namespace FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)

/-- The generic-rank condition is Zariski local on the base: if it holds over each member of an
open cover of `T`, it holds over `T`. -/
theorem condition_of_openCover {T : Scheme.{u}} (a : T ⟶ D.S) {K : Type u} (O : K → T.Opens)
    (hO : ∀ t, ∃ k, t ∈ O k) (h : ∀ k, D.Condition p (Over.mk ((O k).ι ≫ a))) :
    D.Condition p (Over.mk a) := by
  rw [D.condition_iff_baseRankLocus_eq_univ, Set.eq_univ_iff_forall]
  intro t
  obtain ⟨k, hk⟩ := hO t
  let g : Over.mk ((O k).ι ≫ a) ⟶ Over.mk a := Over.homMk (O k).ι
  have : IsOpenImmersion (D.transitionHom g) := MorphismProperty.of_isPullback
    (D.isPullback_transitionHom g).flip (inferInstanceAs (IsOpenImmersion (O k).ι))
  obtain ⟨y, hy, hyt⟩ :=
    Set.eq_univ_iff_forall.mp ((D.condition_iff_baseRankLocus_eq_univ p _).mp (h k)) ⟨t, hk⟩
  refine ⟨D.transitionHom g y, ?_, ?_⟩
  · exact freeAtPointOfRank_of_isOpenImmersion (D.transitionHom g) _ y p
      (freeAtPointOfRank_of_moduleIso (D.transitionModuleIso g).symm hy)
  · have hw := congrArg (fun k : _ ⟶ T ↦ k.base y) (D.transitionHom_comp_snd g)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hw
    show (D.baseChangeMap (Over.mk a)).base (D.transitionHom g y) = t
    rw [hw]
    show (O k).ι.base ((D.baseChangeMap _).base y) = t
    rw [hyt]
    rfl

/-- The rank is determined by a single fibre: if the generic-rank condition holds with rank `q`
over `T`, and with rank `q'` over the spectrum of the residue field of the image in `S` of a point
`t` of `T`, then `q = q'`. -/
theorem eq_of_condition_of_condition_residueField {T : Over D.S} {q q' : ℕ}
    (h : D.Condition q T) (t : T.left)
    (h' : D.Condition q' (Over.mk (D.S.fromSpecResidueField (T.hom.base t)))) : q = q' := by
  let T₀ : Over D.S := Over.mk (T.left.fromSpecResidueField t ≫ T.hom)
  let g₁ : T₀ ⟶ T := Over.homMk (T.left.fromSpecResidueField t)
  let g₂ : T₀ ⟶ Over.mk (D.S.fromSpecResidueField (T.hom.base t)) :=
    Over.homMk (Spec.map (T.hom.residueFieldMap t))
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField T.hom t)
  have : Unique (PrimeSpectrum (T.left.residueField t)) := PrimeSpectrum.instUnique
  let τ : T₀.left := (default : PrimeSpectrum (T.left.residueField t))
  obtain ⟨ξ, hξ⟩ := D.exists_isGenericPoint_fiber_baseChangeMap T₀ τ
  exact freeAtPointOfRank_unique _ (D.condition_of_hom q g₁ h τ ξ hξ)
    (D.condition_of_hom q' g₂ h' τ ξ hξ)

/-- A representative of the generic-rank functor of a finitely presented module is locally of
finite presentation. -/
theorem locallyOfFinitePresentation_hom_of_representableBy [D.F.IsFinitePresentation]
    {W : Over D.S} (e : (D.freeAtGenericPointsFunctor p).RepresentableBy W) :
    LocallyOfFinitePresentation W.hom := by
  refine (Scheme.locallyOfFinitePresentation_iff_isLimitPreserving_yoneda W.hom).2 ?_
  intro I _ _ E hE
  have hpres : PreservesColimit E.op (D.freeAtGenericPointsFunctor p) := by
    have : IsConnected I := IsCofiltered.isConnected I
    refine ⟨fun {c} hc => ⟨Types.FilteredColimit.isColimitOf (E.op ⋙ _)
      ((D.freeAtGenericPointsFunctor p).mapCocone c) (fun x => ?_) fun j k x y _ => ?_⟩⟩
    · have hlim : IsLimit ((Over.forget D.S).mapCone c.unop) :=
        isLimitOfPreserves (Over.forget D.S) hc.unop
      have : ∀ i, IsAffine ((E ⋙ Over.forget D.S).obj i) := hE
      have hpt : IsAffine ((Over.forget D.S).obj c.unop.pt) :=
        Scheme.isAffine_of_isLimit _ hlim
      obtain ⟨i, hi⟩ := D.exists_condition_of_isLimit p E c.unop hlim hE hpt x.down.down
      exact ⟨op i, ⟨⟨hi⟩⟩,
        (D.subsingleton_freeAtGenericPointsFunctor_obj p c.pt).elim _ _⟩
    · obtain ⟨l, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j k
      exact ⟨l, f, g,
        (D.subsingleton_freeAtGenericPointsFunctor_obj p (op (E.obj l.unop))).elim _ _⟩
  exact preservesColimit_of_natIso E.op e.toIso.symm

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end

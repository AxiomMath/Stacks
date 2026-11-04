module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineOpenEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport

/-!
# The complement of a locally principal closed subspace is affine over the space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `Z ⊆ X`
be a locally principal closed subspace in the sense of Stacks 083B(1), and let `U = X \ Z` be
the open complement. Then `U ⟶ X` is an affine morphism (Stacks 083D).

## Main definitions

* `AlgebraicGeometry.Space.chartComplement`: the open subscheme of a chart cutting out the
  complement of the preimage of the point set of a closed subspace.

## Main results

* `AlgebraicGeometry.Space.preimage_range_rep_snd`: the preimage of the point set of a closed
  subspace along a morphism of étale charts is its point set on the source chart.
* `AlgebraicGeometry.Space.isAffineOpen_chartComplement`: on an affine étale chart, the
  complement of the preimage of the point set of a locally principal closed subspace is an
  affine open.
* `AlgebraicGeometry.Space.isAffineHom_ι_openComplement`: the inclusion of the open complement
  of a locally principal closed subspace is an affine morphism.

## References

* [Stacks Project, Tag 083D](https://stacks.math.columbia.edu/tag/083D)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
* [Stacks Project, Tag 07ZT](https://stacks.math.columbia.edu/tag/07ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-! ### The point set of a closed subspace on a chart -/

/-- The preimage in a chart of the point set of a closed subspace is closed. -/
theorem isClosed_range_rep_snd {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ X.1) :
    IsClosed (Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd q))) := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd q)) := Z.2.2.property_snd q
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion.mp ‹_›).2

/-- The open subscheme of a chart cutting out the complement of the preimage of the point set
of a closed subspace `Z`, that is, the subscheme of the chart cut out by the open complement
`X \ Z`. -/
def chartComplement {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ X.1) :
    ((BigFppfOver.toScheme B S hS).obj A).Opens :=
  ⟨(Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd q)))ᶜ,
    (isClosed_range_rep_snd B S hS X Z q).isOpen_compl⟩

/-- The underlying set of `chartComplement` is the complement of the preimage in the chart of
the point set of `Z`. -/
@[simp]
theorem coe_chartComplement {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ X.1) :
    (chartComplement B S hS X Z q : Set ((BigFppfOver.toScheme B S hS).obj A)) =
      (Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd q)))ᶜ :=
  rfl

/-- For a morphism `g : V ⟶ U` of étale charts of `X`, the preimage along `g` of the point set
of `Z` on `U` is the point set of `Z` on `V`. -/
theorem preimage_range_rep_snd {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map g) ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)) =
      Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)) := by
  have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map g) ≫ U.1.hom = V.1.hom :=
    CostructuredArrow.w g.hom
  refine Set.ext fun z => ?_
  obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS V.1.left z
  have hnat : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map g)
        (pointsToScheme B S hS V.1.left w) =
      pointsToScheme B S hS U.1.left (pointsMap B S hS (yoneda.obj V.1.left)
        (yoneda.map ((SmallEtale.toOver B S hS X.1).map g)) w) :=
    (pointsToScheme_pointsMap_yoneda B S hS _ w).symm
  rw [Set.mem_preimage, hnat,
    ← mem_range_pointsMap_ι_iff B S hS X Z U.1.hom _,
    ← mem_range_pointsMap_ι_iff B S hS X Z V.1.hom w,
    ← pointsMap_comp_apply, hw]

/-! ### The complement is an affine open of an affine chart -/

/-- Let `Z ⊆ X` be a locally principal closed subspace and let `A` be an affine object of the
site carrying an étale chart `q` of `X`. Then `AlgebraicGeometry.Space.chartComplement` is an
affine open of `A`. -/
theorem isAffineOpen_chartComplement (hZ : IsLocallyPrincipal B S hS X Z)
    {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ X.1) (hq : IsEtale B S hS q)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A)) :
    IsAffineOpen (chartComplement B S hS X Z q) := by
  let UA : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk q, (isEtale_iff_presheaf_of_yoneda B S hS q).mp hq⟩
  have hUAhom : UA.1.hom = q := rfl
  have hcharts : ∀ x : (BigFppfOver.toScheme B S hS).obj A,
      ∃ (W : SmallEtale B S hS X.1) (g : W ⟶ UA),
        IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X.1).map g)) ∧
        ∃ a : Γ((BigFppfOver.toScheme B S hS).obj W.1.left, ⊤),
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map g) ⁻¹ᵁ
              chartComplement B S hS X Z q =
            ((BigFppfOver.toScheme B S hS).obj W.1.left).basicOpen a := by
    intro x
    obtain ⟨W, g, hWaff, ⟨x', hx'⟩, a, hiff⟩ :=
      exists_affine_chart_mem_range_pointsMap_iff B S hS X Z hZ UA x
    refine ⟨W, g, hWaff, ⟨x', hx'⟩, a, ?_⟩
    have hzl : Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd W.1.hom)) =
        ((BigFppfOver.toScheme B S hS).obj W.1.left).zeroLocus {a} := by
      refine Set.ext fun z => ?_
      obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS W.1.left z
      rw [← mem_range_pointsMap_ι_iff B S hS X Z W.1.hom w]
      exact hiff w
    have hset : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map g) ⁻¹'
        (Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd q)))ᶜ =
        (((BigFppfOver.toScheme B S hS).obj W.1.left).basicOpen a :
          Set ((BigFppfOver.toScheme B S hS).obj W.1.left)) := by
      rw [Set.preimage_compl, ← hUAhom, preimage_range_rep_snd B S hS X Z g, hzl,
        Scheme.zeroLocus_singleton, compl_compl]
    exact TopologicalSpace.Opens.ext hset
  choose W g hWaff hmem a hbasic using hcharts
  have hopen : ∀ x, IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (g x)))) := by
    intro x
    have : Etale ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (g x))) := etale_toScheme_toOver_map B S hS X.1 (g x)
    exact ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (g x))).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ := (isCompact_univ (X := (BigFppfOver.toScheme B S hS).obj A)).elim_finite_subcover
    (fun x => Set.range ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (g x)))) hopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hmem x⟩)
  refine Stacks.Descent.isAffineOpen_of_finite_etale_cover_preimage_eq_basicOpen hA
    (ι := {x : (BigFppfOver.toScheme B S hS).obj A // x ∈ s})
    (fun i => (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (g i.1)))
    (fun i => hWaff i.1)
    (fun i => etale_toScheme_toOver_map B S hS X.1 (g i.1)) ?_
    (fun i => a i.1) (fun i => hbasic i.1)
  exact Set.eq_univ_of_univ_subset (hs.trans
    (Set.iUnion₂_subset fun x hx => Set.subset_iUnion_of_subset ⟨x, hx⟩ (le_refl _)))

/-! ### Stacks 083D -/

/-- Let `X` be an algebraic space over a scheme `S` and let `Z ⊆ X` be a locally principal
closed subspace. Then the inclusion of the open complement `X \ Z` into `X` is an affine
morphism. -/
@[stacks 083D]
theorem isAffineHom_ι_openComplement (hZ : IsLocallyPrincipal B S hS X Z) :
    IsAffineHom B S hS (openComplement B S hS Z.1).ι := by
  have hsrc : IsAlgebraicSpace B S hS (openComplement B S hS Z.1).toFunctor :=
    (isOpenSubspace_openComplement B S hS X.2 Z.1 Z.2).1
  refine ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (openComplement B S hS Z.1).ι
    hsrc X.2).out 3 2).mp ?_
  intro V g hg
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj V)) := V.property
  obtain ⟨b, i, hiopen, hirange, hiuniv⟩ := exists_restrict_bigFppfOver
    ((BigAffineFppf.inclusion B S hS).obj V) (chartComplement B S hS X Z g)
  have haff : IsAffineOpen (chartComplement B S hS X Z g) :=
    isAffineOpen_chartComplement B S hS X Z hZ g hg hVaff
  have _ : IsAffine (chartComplement B S hS X Z g).toScheme := haff
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj b) :=
    IsAffine.of_isIso (IsOpenImmersion.isoOfRangeEq
      ((BigFppfOver.toScheme B S hS).map i) (chartComplement B S hS X Z g).ι
      (hirange.trans (Scheme.Opens.range_ι _).symm)).hom
  have hrange : Subfunctor.range (yoneda.map i) =
      (openComplement B S hS Z.1).preimage g := by
    rw [openComplement_eq_openSubspaceOfPoints_compl]
    refine range_yoneda_map_eq_preimage_openSubspaceOfPoints B S hS _ g i
      (chartComplement B S hS X Z g : Set _) hirange (fun {A'} h hh => hiuniv h hh)
      fun p => ?_
    rw [Set.mem_compl_iff, coe_chartComplement, Set.mem_compl_iff,
      ← pointsToScheme_class B S hS _ p,
      mem_range_pointsMap_ι_iff B S hS X Z g (p.class B S hS (yoneda.obj _))]
  have hmono : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map i)))
  have hnat : ∀ {T : BigFppfOver B S hS} (t : T ⟶ (BigAffineFppf.inclusion B S hS).obj V),
      X.1.map t.op (yonedaEquiv g) = g.app (op T) t := fun t => by
    rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  have hmem : X.1.map i.op (yonedaEquiv g) ∈ (openComplement B S hS Z.1).obj (op b) := by
    have h1 : i ∈ (Subfunctor.range (yoneda.map i)).obj (op b) := ⟨𝟙 b, by simp⟩
    rw [hrange] at h1
    rwa [hnat]
  refine ⟨⟨b, ‹IsAffine ((BigFppfOver.toScheme B S hS).obj b)›⟩,
    yonedaEquiv.symm (⟨_, hmem⟩ : (openComplement B S hS Z.1).toFunctor.obj (op b)), i, ?_⟩
  have hsq := Subfunctor.isPullback_yoneda_of_forall_exists
    (openComplement B S hS Z.1) i (yonedaEquiv g) (⟨_, hmem⟩) rfl
    (fun T t ht => (by rw [hrange]; rwa [hnat] at ht :
      t ∈ (Subfunctor.range (yoneda.map i)).obj (op T)))
  simpa using hsq

end AlgebraicGeometry.Space

end

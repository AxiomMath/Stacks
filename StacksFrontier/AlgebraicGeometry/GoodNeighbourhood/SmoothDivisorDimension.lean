module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.TowerStep
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionEquality
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChangeDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.Topology.Dimension.LocalDimensionComponents

/-!
# A smooth divisor in a smooth scheme has one dimension less

Let `G` be smooth of relative dimension `r + 1` over a field `k`, let `t` be a global section of
an invertible module on `G` which does not vanish at any generic point of `G`, and suppose that
the zero scheme `Z(t)` is smooth over `k`. Then `Z(t)` is smooth of relative dimension `r`.

This is the dimension count of the inductive Bertini argument in SGA 4, Exposé XI, 3.3: each cut
`V(v₁, …, v_{m+1}) = V(v₁, …, v_m) ∩ Z(v_{m+1})` lowers the relative dimension by exactly one,
provided `v_{m+1}` vanishes identically on no component.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.smoothOfRelativeDimension_zeroScheme`: the statement above.

## Implementation notes

Over a field, smoothness of relative dimension `r` is smoothness together with local dimension `r`
at every point (`Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq`). The local
dimension of `Z(t)` at a point `w` is computed on a small irreducible open neighbourhood: `Z(t)`
is smooth, hence normal, so `w` has an integral open neighbourhood `O`; it is cut out of `Z(t)` by
an open `N''` of `G`, and an integral open `N' ⊆ N''` of `G` around `w` gives the open
`Z(t) ∩ N' = Z(t|_{N'})` of `O`. That scheme is irreducible, so its local dimension is its
dimension, and since `t|_{N'}` is a nonzero section on the integral `N'` of dimension `r + 1`
the dimension is `r` (`Stacks.Chow.topologicalKrullDim_zeroScheme_eq_of_ne_zero`, which rests on
Krull's principal ideal theorem through Tag 02RK).
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

/-- The inverse image of a zero scheme along an open immersion is an open subscheme of it: the
comparison map of the closed subschemes is an open immersion. -/
theorem isOpenImmersion_subschemeMap_comap_of_isOpenImmersion {X Y : Scheme.{u}}
    (I : Y.IdealSheafData)
    (j : X ⟶ Y) [IsOpenImmersion j] :
    IsOpenImmersion (Scheme.IdealSheafData.subschemeMap (I.comap j) I j (I.le_map_comap j)) :=
  MorphismProperty.of_isPullback (Scheme.IdealSheafData.isPullback_comap I j)
    ‹IsOpenImmersion j›

/-- **The closure of the image of the generic point of an irreducible scheme under an open
immersion is an irreducible component.** -/
theorem closure_singleton_mem_irreducibleComponents_of_isOpenImmersion {N G : Scheme.{u}}
    (j : N ⟶ G) [IsOpenImmersion j] [IrreducibleSpace N] :
    closure ({j (genericPoint N)} : Set G) ∈ irreducibleComponents G := by
  have hirrR : IsIrreducible (Set.range j.base) := by
    have := (IrreducibleSpace.isIrreducible_univ N).image _ j.continuous.continuousOn
    rwa [Set.image_univ] at this
  have hcl : closure ({j (genericPoint N)} : Set G) = closure (Set.range j.base) := by
    refine le_antisymm (closure_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)) ?_
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ closure ({genericPoint N} : Set N) := by
      rw [(genericPoint_spec N).def]
      trivial
    have := image_closure_subset_closure_image (f := j.base) j.continuous ⟨y, hy, rfl⟩
    simpa [Set.image_singleton] using this
  have : IrreducibleSpace (Set.range j.base) := Subtype.irreducibleSpace hirrR
  have hD : (Set.univ : Set (Set.range j.base)) ∈ irreducibleComponents (Set.range j.base) := by
    rw [irreducibleComponents_eq_singleton]
    rfl
  have := closure_image_mem_irreducibleComponents_of_isOpen j.isOpenEmbedding.isOpen_range hD
  rwa [Set.image_univ, Subtype.range_coe, ← hcl] at this

/-- **On an integral open of a smooth scheme of relative dimension `r + 1` the zero scheme of a
section not vanishing at the generic point has dimension `r`**, as soon as it is nonempty. -/
theorem topologicalKrullDim_comap_zeroScheme {k : Type u} [Field k] {G : Scheme.{u}}
    (f : G ⟶ Spec (.of k)) (r : ℕ) [SmoothOfRelativeDimension (r + 1) f] (M : G.Modules)
    [SheafOfModules.IsInvertible G.sheaf.obj G.ringCatSheaf.property M] (t : Γ(M, ⊤))
    {N : Scheme.{u}} (j : N ⟶ G) [IsOpenImmersion j] [IsIntegral N]
    (hgen : j (genericPoint N) ∉ (zeroScheme G M t).support)
    (hne : Nonempty ((zeroScheme G M t).comap j).subscheme) :
    topologicalKrullDim ((zeroScheme G M t).comap j).subscheme = (r : WithBot ℕ∞) := by
  set t' := pullbackGlobalSections j M t
  have hZ : (zeroScheme G M t).comap j = zeroScheme N ((Scheme.Modules.pullback j).obj M) t' :=
    (Stacks.Divisors.zeroScheme_pullback j M t).symm
  have ht' : t' ≠ 0 := by
    intro h0
    apply hgen
    have hmem : genericPoint N ∈ ((zeroScheme G M t).comap j).support := by
      rw [hZ, h0, zeroScheme_zero, Scheme.IdealSheafData.support_bot]
      trivial
    rwa [Scheme.IdealSheafData.support_comap] at hmem
  have h0 : SmoothOfRelativeDimension (0 + (r + 1)) (j ≫ f) := inferInstance
  have : SmoothOfRelativeDimension (r + 1) (j ≫ f) := by rwa [zero_add] at h0
  have : Smooth (j ≫ f) := SmoothOfRelativeDimension.smooth (r + 1) _
  have hdimN : topologicalKrullDim N = ((r + 1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field (r + 1) (j ≫ f)
  have : LocallyOfFiniteType (show N ⟶ (Stacks.Chow.fieldChowSituation k).S from j ≫ f) :=
    (inferInstance : LocallyOfFiniteType (j ≫ f))
  rw [hZ] at hne ⊢
  exact Stacks.Chow.topologicalKrullDim_zeroScheme_eq_of_ne_zero
    (show N ⟶ (Stacks.Chow.fieldChowSituation k).S from j ≫ f) _ t' ht' hdimN

/-- **A smooth zero scheme in a smooth scheme of relative dimension `r + 1` over a field, of a
section vanishing at no generic point, is smooth of relative dimension `r`.** -/
theorem smoothOfRelativeDimension_zeroScheme {k : Type u} [Field k] {G : Scheme.{u}}
    (f : G ⟶ Spec (.of k)) (r : ℕ) [SmoothOfRelativeDimension (r + 1) f] (M : G.Modules)
    [SheafOfModules.IsInvertible G.sheaf.obj G.ringCatSheaf.property M] (t : Γ(M, ⊤))
    (ht : ∀ η : G, closure ({η} : Set G) ∈ irreducibleComponents G →
      η ∉ (zeroScheme G M t).support)
    (hsm : Smooth ((zeroScheme G M t).subschemeι ≫ f)) :
    SmoothOfRelativeDimension r ((zeroScheme G M t).subschemeι ≫ f) := by
  set Z := zeroScheme G M t with hZdef
  have hsub : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Smooth f := SmoothOfRelativeDimension.smooth (r + 1) f
  have : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal G := isNormal_of_smooth f
  have : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ f)
  have : IsNormal Z.subscheme := isNormal_of_smooth (Z.subschemeι ≫ f)
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ r fun w => ?_
  rw [topologicalKrullDimAt_fiber_eq_of_subsingleton]
  -- an integral open neighbourhood `O` of `w` in `Z(t)`, cut out by an open `N''` of `G`
  obtain ⟨O, hwO, hO⟩ := exists_isIntegral_opens_of_isNormal Z.subscheme w
  obtain ⟨N'', hN''open, hN''⟩ :=
    (Z.subschemeι.isClosedEmbedding.isInducing.isOpen_iff).mp O.isOpen
  -- an integral open neighbourhood `N₀` of the image of `w` in `G`
  obtain ⟨N₀, hwN₀, hN₀⟩ := exists_isIntegral_opens_of_isNormal G (Z.subschemeι w)
  have hmem := Set.ext_iff.1 hN''
  -- the integral open `N = N₀ ∩ N''` of `G`, as a scheme with its open immersion `j`
  set V : N₀.toScheme.Opens := N₀.ι ⁻¹ᵁ ⟨N'', hN''open⟩
  have hwV : (⟨Z.subschemeι w, hwN₀⟩ : N₀.toScheme) ∈ V := (hmem w).2 hwO
  have : Nonempty V := ⟨⟨_, hwV⟩⟩
  set j : V.toScheme ⟶ G := V.ι ≫ N₀.ι
  -- the open `Z(t) ∩ N` of `Z(t)`, which lies in `O`
  set e := Scheme.IdealSheafData.subschemeMap (Z.comap j) Z j (Z.le_map_comap j)
  have : IsOpenImmersion e := isOpenImmersion_subschemeMap_comap_of_isOpenImmersion Z j
  have he : e ≫ Z.subschemeι = (Z.comap j).subschemeι ≫ j :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have hcomp : ∀ q, Z.subschemeι (e q) = j ((Z.comap j).subschemeι q) := fun q => by
    rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
  obtain ⟨w', hw'⟩ : w ∈ Set.range e.base := by
    set y : V.toScheme := ⟨⟨Z.subschemeι w, hwN₀⟩, hwV⟩
    have hy : j y = Z.subschemeι w := rfl
    have hysupp : y ∈ ((Z.comap j).support : Set V.toScheme) := by
      rw [Scheme.IdealSheafData.support_comap]
      change j y ∈ (Z.support : Set G)
      rw [hy, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    rw [← Scheme.IdealSheafData.range_subschemeι] at hysupp
    obtain ⟨w', hw'⟩ := hysupp
    exact ⟨w', Z.subschemeι.isClosedEmbedding.injective (by rw [hcomp, hw', hy])⟩
  have hrangeO : Set.range e.base ⊆ (O : Set Z.subscheme) := by
    rintro _ ⟨q, rfl⟩
    exact (hmem _).1 (by rw [Set.mem_preimage, hcomp]; exact ((Z.comap j).subschemeι q).2)
  -- `Z(t) ∩ N` is irreducible
  have hOirr : IsPreirreducible (O : Set Z.subscheme) :=
    @IsPreirreducible.of_subtype _ _ _ (inferInstanceAs (PreirreducibleSpace O.toScheme))
  have hirr : IrreducibleSpace (Z.comap j).subscheme := by
    have hR : IsPreirreducible (Set.range e.base) :=
      hOirr.open_subset e.isOpenEmbedding.isOpen_range hrangeO
    have hpre := hR.preimage e.isOpenEmbedding
    rw [Set.preimage_range] at hpre
    exact (irreducibleSpace_def _).2 ⟨⟨w', trivial⟩, hpre⟩
  rw [← hw', e.isOpenEmbedding.topologicalKrullDimAt_eq w',
    topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k _
      ((Z.comap j).subschemeι ≫ j ≫ f)
      (TopologicalSpace.Equidimensional.of_preirreducibleSpace _) w']
  exact topologicalKrullDim_comap_zeroScheme f r M t j
    (ht _ (closure_singleton_mem_irreducibleComponents_of_isOpenImmersion j)) ⟨w'⟩

end AlgebraicGeometry.GoodNeighbourhood

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange

/-!
# The open locus on the base over which a flat morphism becomes surjective, or an isomorphism

Consider a commutative triangle of algebraic spaces over a scheme `S`: a morphism `f : X ⟶ Y`
together with morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` such that `f ≫ q = p`. If `f` itself is
flat and locally of finite presentation and `q` is closed, there is an open subspace of `Z`
through which a morphism `Z' ⟶ Z` factors exactly when the base change of `f` along it is
surjective; if moreover `p` is locally of finite type and universally closed and `q` is
separated and locally of finite type, there is an open subspace of `Z` through which `Z' ⟶ Z`
factors exactly when the base change of `f` along it is an isomorphism.

Neither statement is a special case of Stacks 05XD, which assumes instead that `p` is flat and
locally of finite presentation and deduces flatness of the base changes of `f` only over the
flat locus of Stacks 05X3; here it is `f` that is flat, and `p` is only assumed locally of
finite type. Since `f` is flat outright that locus is all of `Z`, so neither result needs
Stacks 05X3 (`AlgebraicGeometry.Space.flatLocusOpenAndStableUnderBaseChange`) at all. The
intended instance is an `f` which is étale, hence flat and locally of finite presentation.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isSurjective_baseChange_of_isFlat`: the
  surjectivity locus on the base, for a flat `f` locally of finite presentation.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isIso_baseChange_of_isFlat`: the
  isomorphism locus on the base, for such an `f`.

## Implementation notes

The surjectivity locus is the set of points of `Z` whose fibre in `|Y|` lies in the image of
`f`, cut out as an open subspace through the correspondence of Stacks 03BZ. It is open because
`q` is closed and because `f`, being flat and locally of finite presentation, is universally
open by Stacks 042S and so open on points; containment of the image of the points of `Z'` in it
is surjectivity of the base change. This is the argument of Stacks 05XC with the flat locus
`W₀` of Stacks 05XB replaced by the whole of `Z`, which is what flatness of `f` itself buys.

The isomorphism locus is the intersection of that locus with the one of Stacks 05XA, over which
the base change is a closed immersion, the intersection being formed on point sets. A
surjective flat closed immersion is an isomorphism, which is
`AlgebraicGeometry.Space.isIso_of_isClosedImmersion_of_isFlat_of_isSurjective`, and the
flatness its use needs is flatness of the base change of `f`, which here is read off from
flatness of `f` by the base-change statement for the every-étale-chart condition behind
Stacks 03XH; conversely an isomorphism is surjective, flat and a closed immersion.

No hypothesis is carried: every input is an unconditional result of the library.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
* [Stacks Project, Tag 05XA](https://stacks.math.columbia.edu/tag/05XA)
* [Stacks Project, Tag 05XC](https://stacks.math.columbia.edu/tag/05XC)
* [Stacks Project, Tag 05XD](https://stacks.math.columbia.edu/tag/05XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If `u` is an open map and `v` is a closed map, the set of points of the target of `v` whose
fibre under `v` is contained in the image of `u` is open: it is the complement of the image
under `v` of the closed complement of the open image of `u`. -/
@[ega "IV 15.5.10" "more general"]
private theorem isOpen_setOf_forall_eq_imp_mem_range_of_isOpenMap
    {A C D : Type*} [TopologicalSpace A] [TopologicalSpace C] [TopologicalSpace D]
    {u : A → C} {v : C → D} (hu : IsOpenMap u) (hv : IsClosedMap v) :
    IsOpen {z | ∀ y, v y = z → y ∈ Set.range u} := by
  have hset : {z | ∀ y, v y = z → y ∈ Set.range u} = (v '' (Set.range u)ᶜ)ᶜ := by
    ext z
    rw [Set.mem_compl_iff, Set.mem_image, Set.mem_ofPred_eq]
    exact ⟨fun h ⟨y, hy, hvy⟩ => hy (h y hvy),
      fun h y hvy => Classical.byContradiction fun hy => h ⟨y, hy, hvy⟩⟩
  rw [hset, isOpen_compl_iff]
  exact hv _ (isClosed_compl_iff.mpr hu.isOpen_range)

/-- Flatness of a morphism of algebraic spaces over `S` is inherited by its base change along
an arbitrary morphism of presheaves: flatness of morphisms of schemes is stable under base
change and composition, holds for étale morphisms and descends along a surjective flat
morphism of sources. -/
theorem isFlat_of_isPullback_of_isAlgebraicSpace
    {W X' Y' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ Z'} {b : W ⟶ X'} {g : Z' ⟶ Y'} {f : X' ⟶ Y'}
    (sq : IsPullback a b g f) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y') (hf : IsFlat B S hS f) :
    IsFlat B S hS a :=
  holdsOnEveryEtaleChart_of_isPullback_of_descent B S hS
    AlgebraicGeometry.Flat.isStableUnderBaseChange inferInstance
    (fun i hi => by let := hi; infer_instance)
    (fun α k hα hαet hflat => by
      let := hα
      let := hαet
      let : AlgebraicGeometry.Flat α := inferInstance
      let := hflat
      exact flat_of_comp_of_surjective_flat α k)
    sq hX' hY' hf

/-! ### The surjectivity locus on the base for a flat morphism -/

/-- **The open locus on the base over which the base change of a flat morphism is surjective.**
Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and target are given
over a third algebraic space `Z` by morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`. If
`f` is flat and locally of finite presentation and `q` is closed, then there is an open subspace
`W` of `Z` through which a morphism `Z' ⟶ Z` from an algebraic space factors exactly when the
base change of `f` along it is surjective. -/
theorem exists_isOpenSubspace_iff_isSurjective_baseChange_of_isFlat
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hfflat : IsFlat B S hS f) (hffp : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsClosedMorphism B S hS q) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsSurjective B S hS (baseChangeOverBase B S hS f p q hfq g) := by
  obtain ⟨W, hWopen, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hZ
    {z | ∀ y, pointsMap B S hS Y q y = z → y ∈ Set.range (pointsMap B S hS X f)}
    (isOpen_setOf_forall_eq_imp_mem_range_of_isOpenMap
      (isOpen_of_universallyOpen B S hS hY f
        (universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS hX hY f hfflat hffp))
      hqc)
  refine ⟨W, hWopen, fun Z' hZ' g => ?_⟩
  rw [factorsThrough_openSubspace_iff_points B S hS hZ hZ' W hWopen g, hWrange,
    isSurjective_baseChangeOverBase_iff B S hS f p q hfq g]

/-! ### The isomorphism locus on the base for a flat morphism -/

/-- **The open locus on the base over which the base change of a flat morphism is an
isomorphism.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and
target are given over a third algebraic space `Z` by morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` with
`f ≫ q = p`. If `f` is flat and locally of finite presentation, `p` is locally of finite type
and universally closed, and `q` is separated and closed, then there is an open subspace `W` of
`Z` through which a morphism `Z' ⟶ Z` from an algebraic space factors exactly when the base
change of `f` along it is an isomorphism.

This is the specialisation of Stacks 05XD to a flat `f`, and unlike that result it needs no
flat-locus input. -/
theorem exists_isOpenSubspace_iff_isIso_baseChange_of_isFlat
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hfflat : IsFlat B S hS f) (hffp : IsLocallyOfFinitePresentation B S hS f)
    (hp : IsLocallyOfFiniteType B S hS p) (hpuc : UniversallyClosed B S hS p)
    (hqsep : IsSeparated B S hS q) (hqc : IsClosedMorphism B S hS q) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsIso (baseChangeOverBase B S hS f p q hfq g) := by
  obtain ⟨W₁, hW₁, hW₁prop⟩ := exists_isOpenSubspace_iff_isSurjective_baseChange_of_isFlat
    B S hS hX hY hZ f p q hfq hfflat hffp hqc
  obtain ⟨W₂, hW₂, hW₂prop⟩ := exists_isOpenSubspace_iff_isClosedImmersion_baseChange
    B S hS hX hY hZ f p q hfq hp hpuc hqsep
  obtain ⟨W, hWopen, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hZ
    (Set.range (pointsMap B S hS W₁.toFunctor W₁.ι) ∩
      Set.range (pointsMap B S hS W₂.toFunctor W₂.ι))
    ((isOpen_range_pointsMap_of_isOpenImmersion B S hS W₁.ι hW₁.2).inter
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS W₂.ι hW₂.2))
  refine ⟨W, hWopen, fun Z' hZ' g => ?_⟩
  have hfactor : (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
      ((∃ r : Z' ⟶ W₁.toFunctor, r ≫ W₁.ι = g) ∧
        ∃ r : Z' ⟶ W₂.toFunctor, r ≫ W₂.ι = g) := by
    rw [factorsThrough_openSubspace_iff_points B S hS hZ hZ' W hWopen g,
      factorsThrough_openSubspace_iff_points B S hS hZ hZ' W₁ hW₁ g,
      factorsThrough_openSubspace_iff_points B S hS hZ hZ' W₂ hW₂ g, hWrange,
      Set.subset_inter_iff]
  rw [hfactor, hW₁prop Z' hZ' g, hW₂prop Z' hZ' g]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact isIso_of_isClosedImmersion_of_isFlat_of_isSurjective B S hS
      (isAlgebraicSpace_pullback B S hS p g hX hZ' hZ)
      (isAlgebraicSpace_pullback B S hS q g hY hZ' hZ) _ h.2
      (isFlat_of_isPullback_of_isAlgebraicSpace B S hS
        (isPullback_baseChangeOverBase B S hS f p q hfq g).flip hX hY hfflat) h.1
  · have _ : IsIso (baseChangeOverBase B S hS f p q hfq g) := h
    exact ⟨isSurjective_of_isIso B S hS _, isClosedImmersion_of_isIso B S hS _⟩

end AlgebraicGeometry.Space

end

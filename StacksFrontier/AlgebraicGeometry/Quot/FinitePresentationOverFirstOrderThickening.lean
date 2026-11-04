module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleFirstOrderThickeningPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleStrictness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.Deformation.ToposThickening.FlatFinitePresentationLift
public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessEquivalence

/-!
# Finite presentation over a first order thickening of algebraic spaces (Stacks 08W7)

Let

```
  X --i--> X'
  |        |
  f        f'
  v        v
  T --j--> T'
```

be a cartesian square of algebraic spaces over `S` in which `j : T ⟶ T'` is a first order
thickening. Let `ℱ'` be an `𝒪_{X'}`-module flat over `T'` and set `ℱ = i^*ℱ'`. Stacks 08W7: the
following are equivalent

1. `ℱ'` is a quasi-coherent `𝒪_{X'}`-module of finite presentation,
2. `ℱ'` is an `𝒪_{X'}`-module of finite presentation,
3. `ℱ` is a quasi-coherent `𝒪_X`-module of finite presentation,
4. `ℱ` is an `𝒪_X`-module of finite presentation.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_modulePullback_preimageSubspace`: the
  implication (4) ⇒ (2) when `T ⊆ T'` is a closed subspace and `X = f'⁻¹(T)` its inverse image.
* `AlgebraicGeometry.Space.tfae_isFinitePresentationOnSite_of_isPullback`: **Stacks 08W7**.

## How the statement is read

* A first order thickening `j : T ⟶ T'` is a morphism identifying `T` with its range, which is a
  first order thickening of `T'` in the sense of Stacks 05ZK, part (2): `IsIso` of
  `CategoryTheory.Subfunctor.toRange j.hom` together with
  `AlgebraicGeometry.Space.IsFirstOrderThickening` of `Subfunctor.range j.hom`. This is the form
  of `AlgebraicGeometry.Space.IsThickeningHom`, with first order.
* `ℱ'` is an arbitrary `𝒪_{X'}`-module, not assumed quasi-coherent, so "flat over `T'`" is
  flatness for the morphism of small étale ringed topoi `f'` of Stacks 03G8, in the sense of
  Modules on Sites: `ℱ'` is flat as a module over `f'⁻¹𝒪_{T'}`, which is
  `Deformation.ToposThickening.baseModule`. This is the hypothesis the source's proof hands to
  Deformation Theory, Lemma 08VU.
* Quasi-coherence and finite presentation are Stacks 03DL (6) and (7) on the small étale site,
  `SheafOfModules.IsQuasicoherentOnSite` and `SheafOfModules.IsFinitePresentationOnSite`, as for
  the objects of `Coh_{X/Y}` (Stacks 08KB).

## How the proof goes

As in the source: a module of finite presentation is quasi-coherent, which gives (1) ⇔ (2) and
(3) ⇔ (4); (2) ⇒ (4) is Stacks 03DO; and (4) ⇒ (2) is Stacks 08VU, in the form
`Deformation.ToposThickening.isFinitePresentation_of_isFinitePresentation_pullbackModules`. Its
inputs are supplied as follows. The range of `j` is a closed subspace `T₀ ⊆ T'` and its inverse
image `Z = f'⁻¹(T₀) ⊆ X'` is a first order thickening (Stacks 09ZX), whose small étale ringed
topos is a first order thickening of ringed topoi
(`AlgebraicGeometry.Space.smallEtaleFirstOrderThickening`). The square is strict on sections
(`AlgebraicGeometry.Space.kernelGeneratedByImage_preimageSubspace`), so flatness of `ℱ'` over
`f'⁻¹𝒪_{T'}` makes relations with coefficients in the ideal of `Z` vanish trivially. Finally `Z`
maps to `X` over `X'`, by the universal property of the cartesian square, so `ι^*ℱ'` is an
inverse image of `ℱ` and is of finite presentation with it.

## References

* [Stacks Project, Tag 08W7](https://stacks.math.columbia.edu/tag/08W7)
* [Stacks Project, Tag 08VU](https://stacks.math.columbia.edu/tag/08VU)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- On the small étale site of an algebraic space the two renderings of Stacks 03DL (7) agree. -/
theorem isFinitePresentation_iff_isFinitePresentationOnSite {X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) :
    M.IsFinitePresentation ↔ M.IsFinitePresentationOnSite := by
  let (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
      HasSheafify ((smallEtaleRingedSite B S hS X.1 X.2).J.over V) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
      (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over V)) : Small.{u} N.sections :=
    SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N
  exact ⟨fun _ => SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation M,
    fun _ => Stacks.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite_of_small M⟩

/-- **Stacks 08W7, (4) ⇒ (2), for the inverse image of a closed subspace.** Let `f' : X' ⟶ T'`
be a morphism of algebraic spaces, `T₀ ⊆ T'` a first order thickening and `ℱ'` an
`𝒪_{X'}`-module flat over `T'`. If the restriction of `ℱ'` to `f'⁻¹(T₀)` is of finite
presentation, then so is `ℱ'`. -/
theorem isFinitePresentationOnSite_of_modulePullback_preimageSubspace
    {X' T' : AlgebraicSpaces B S hS} (f' : X' ⟶ T') (T₀ : ClosedSubspaces B S hS T'.1)
    (hT₀ : IsFirstOrderThickening B S hS T' T₀.1) (F' : Modules.{u, u} B S hS X'.1 X'.2)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      (Deformation.ToposThickening.baseModule (smallEtaleRingedToposHom B S hS f') F'))
    (hF : ((modulePullback B S hS
      (subspaceInclusion B S hS X' (preimageSubspace B S hS f' T₀))).obj
        F').IsFinitePresentationOnSite) :
    F'.IsFinitePresentationOnSite := by
  have hvan := Deformation.ToposThickening.ReductionPresentation.idealRelationsVanish_of_isFlat
    (C := SmallEtale B S hS X'.1) (J := SmallEtale.topology B S hS X'.1) (F' := F')
    (kernelGeneratedByImage_preimageSubspace B S hS f' T₀) hflat
  exact (isFinitePresentation_iff_isFinitePresentationOnSite B S hS F').1 <|
    Deformation.ToposThickening.isFinitePresentation_of_isFinitePresentation_pullbackModules
      (smallEtaleFirstOrderThickening B S hS (preimageSubspace B S hS f' T₀)
        (isFirstOrderThickening_preimage B S hS T₀.1 f' hT₀)) F' hvan
      ((isFinitePresentation_iff_isFinitePresentationOnSite B S hS _).2 hF)

variable {X X' T T' : AlgebraicSpaces B S hS}

/-- The range of a first order thickening `j : T ⟶ T'`, as a closed subspace of `T'`. -/
abbrev thickeningRange (j : T ⟶ T')
    (hj : IsFirstOrderThickening B S hS T' (Subfunctor.range j.hom)) :
    ClosedSubspaces B S hS T'.1 :=
  ⟨Subfunctor.range j.hom, hj.1.1⟩

/-- In a cartesian square over a first order thickening `j`, the inverse image of the range of
`j` maps to the top left corner over the top right corner. -/
theorem exists_preimageSubspace_comp_eq (i : X ⟶ X') (f : X ⟶ T) (f' : X' ⟶ T') (j : T ⟶ T')
    (hpb : IsPullback i f f' j) [IsIso (Subfunctor.toRange j.hom)]
    (hj : IsFirstOrderThickening B S hS T' (Subfunctor.range j.hom)) :
    ∃ k : (⟨(preimageSubspace B S hS f' (thickeningRange B S hS j hj)).1.toFunctor,
        (preimageSubspace B S hS f' (thickeningRange B S hS j hj)).2.1⟩ : AlgebraicSpaces B S hS) ⟶
        X, k ≫ i = subspaceInclusion B S hS X'
          (preimageSubspace B S hS f' (thickeningRange B S hS j hj)) := by
  let T₀ := thickeningRange B S hS j hj
  let e : (⟨T₀.1.toFunctor, T₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ T :=
    ObjectProperty.homMk (inv (Subfunctor.toRange j.hom))
  have hw : subspaceInclusion B S hS X' (preimageSubspace B S hS f' T₀) ≫ f' =
      (preimageProjection B S hS f' T₀ ≫ e) ≫ j := by
    apply ObjectProperty.hom_ext
    change (T₀.1.preimage f'.hom).ι ≫ f'.hom =
      (T₀.1.fromPreimage f'.hom ≫ inv (Subfunctor.toRange j.hom)) ≫ j.hom
    rw [← Subfunctor.fromPreimage_ι, Category.assoc]
    congr 1
    exact (IsIso.eq_inv_comp _).2 (Subfunctor.toRange_ι j.hom)
  exact ⟨hpb.lift _ _ hw, hpb.lift_fst _ _ hw⟩

/-- **Stacks 08W7.** Let `X ⟶ X'` over `T ⟶ T'` be a cartesian square of algebraic spaces in
which `j : T ⟶ T'` is a first order thickening, let `ℱ'` be an `𝒪_{X'}`-module flat over `T'`
and set `ℱ = i^*ℱ'`. The following are equivalent:

1. `ℱ'` is a quasi-coherent `𝒪_{X'}`-module of finite presentation,
2. `ℱ'` is an `𝒪_{X'}`-module of finite presentation,
3. `ℱ` is a quasi-coherent `𝒪_X`-module of finite presentation,
4. `ℱ` is an `𝒪_X`-module of finite presentation.

The square is `CategoryTheory.IsPullback i f f' j`; that `j` is a first order thickening is that
it identifies `T` with its range (`IsIso` of `Subfunctor.toRange j.hom`), which is a first order
thickening of `T'` (Stacks 05ZK, part (2)); flatness of `ℱ'` over `T'` is flatness over
`f'⁻¹𝒪_{T'}` for the morphism of small étale ringed topoi of `f'`; see the module docstring. -/
theorem tfae_isFinitePresentationOnSite_of_isPullback (i : X ⟶ X') (f : X ⟶ T) (f' : X' ⟶ T')
    (j : T ⟶ T') (hpb : IsPullback i f f' j) [IsIso (Subfunctor.toRange j.hom)]
    (hj : IsFirstOrderThickening B S hS T' (Subfunctor.range j.hom))
    (F' : Modules.{u, u} B S hS X'.1 X'.2)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      (Deformation.ToposThickening.baseModule (smallEtaleRingedToposHom B S hS f') F')) :
    List.TFAE [F'.IsQuasicoherentOnSite ∧ F'.IsFinitePresentationOnSite,
      F'.IsFinitePresentationOnSite,
      ((modulePullback B S hS i).obj F').IsQuasicoherentOnSite ∧
        ((modulePullback B S hS i).obj F').IsFinitePresentationOnSite,
      ((modulePullback B S hS i).obj F').IsFinitePresentationOnSite] := by
  tfae_have 1 ↔ 2 := ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩
  tfae_have 3 ↔ 4 := ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩
  tfae_have 2 → 4 := isFinitePresentationOnSite_modulePullback B S hS i F'
  tfae_have 4 → 2 := fun hF => by
    obtain ⟨k, hk⟩ := exists_preimageSubspace_comp_eq B S hS i f f' j hpb hj
    exact isFinitePresentationOnSite_of_modulePullback_preimageSubspace B S hS f'
      (thickeningRange B S hS j hj) hj F' hflat
      (SheafOfModules.IsFinitePresentationOnSite.of_iso
        ((modulePullbackTriangle B S hS hk).app F').symm
        (isFinitePresentationOnSite_modulePullback B S hS k _ hF))
  tfae_finish

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineInvertiblePresentation
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionOverlapComparison

/-!
# The reconstruction charts agree on their overlaps

Let `X` and `Y` be quasi-compact quasi-separated schemes with an equivalence
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)`, and let `U i` be an affine open cover of `X`. The reconstruction of
[Stacks, Tag 0GPJ] produces opens `V i` covering `Y` and isomorphisms `f i : V i ≅ U i`. This file
proves that these charts agree on the overlaps:

`(V i ⊓ V j → V i → U i → X) = (V i ⊓ V j → V j → U j → X)`,

which is the hypothesis `hVcompat` of
`AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible`.

## The argument

`AlgebraicGeometry.pullbackTensorFunctorOverlapIso` already supplies, from the per-chart data,
an isomorphism of functors

`b_i^*(-) ⊗ N_i ≅ b_j^*(-) ⊗ N_j`

over the overlap, where `b_i` is the `i`-th chart map read on `V i ⊓ V j` and `N_i` is the
restriction of the invertible sheaf `L i`.  The rigidity theorem
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset` turns such an isomorphism
into the equality `b_i = b_j`, but it asks for its source to be **affine** and for the two
invertible sheaves to arrive in the presentation "inverse image along `W ≅ Spec Γ(W, ⊤)` of the
sheaf attached to an invertible module".  The overlap is not affine, and the restricted sheaves
are bare invertible sheaves.

Both gaps are closed here by assembly.
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_isInvertible` is rigidity with the source
an arbitrary scheme and the two sheaves arbitrary invertible sheaves: cover the source by the
affine opens of `AlgebraicGeometry.Scheme.affineCover`, restrict the isomorphism of functors to
each of them with `AlgebraicGeometry.pullbackTensorFunctorPullbackIso`, put each restricted
sheaf into the required presentation with
`AlgebraicGeometry.exists_module_invertible_iso_pullback_tilde_of_hom`, transport the isomorphism
along that identification with `AlgebraicGeometry.pullbackTensorFunctorIsoOfSheafIso`, apply the
affine-source rigidity on each piece and reassemble with
`AlgebraicGeometry.Scheme.Cover.hom_ext`.

## Main definitions

* `AlgebraicGeometry.pullbackTensorFunctorIsoOfSheafIso`: isomorphic sheaves give isomorphic
  inverse-image-and-tensor functors.

## Main results

* `AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_isInvertible`: rigidity of the
  inverse-image-and-tensor functor with arbitrary source and arbitrary invertible sheaves.
* `AlgebraicGeometry.homOfLE_comp_eq_of_chartIso_overlap`: for the chart data of
  [Stacks, Tag 0GPJ] on two opens of `Y`, the two chart maps agree on the overlap as morphisms
  into `X`.
* `AlgebraicGeometry.exists_isOpenCover_schemeIso_overlapCompatible_of_isAffineOpenCover`: there
  are opens `V i` covering `Y` and isomorphisms `f i : V i ≅ U i` whose chart maps agree on every
  overlap.

## What this does and does not give for [Stacks, Tag 0GPJ]

Of the three obstructions recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalIso.lean`, the first two are
resolved: the hypothesis of the rigidity theorem is produced from the reconstruction's charts
(`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionOverlapComparison.lean`) and its
affineness-of-the-source restriction is removed here, the invertible-sheaf presentation being
supplied by
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineInvertiblePresentation.lean`.  So `hVcompat`
is discharged.

The third obstruction, `hUcompat`, the mirror compatibility of the `(f i).inv` over
`U i ⊓ U j`, is not proved in this file (the one-sided version of the gluing is false — see the
two-point counterexample in the module documentation of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGluedIso.lean`).  It is proved
downstream, from the inverse of a reconstruction pair, by
`AlgebraicGeometry.exists_isOpenCover_schemeIso_mirrorOverlapCompatible_of_isAffineOpenCover`
(`QuasiCoherent/ReconstructionGlobalSchemeIso.lean`); the gluing of the invertible modules is
`QuasiCoherent/ReconstructionGlobalModule.lean`, and the whole of [Stacks, Tag 0GPJ] is
`AlgebraicGeometry.exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence`
(`QuasiCoherent/ReconstructionGlobalComparison.lean`).

## Implementation notes

The structure sheaf of a scheme is named both as `AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf, and
instance search, which runs at reducible transparency, sees through neither chain; the
definitions involved are therefore made locally `implicit_reducible`.

The affine cover used to shrink the source is `AlgebraicGeometry.Scheme.affineCover`, whose
members are spectra of rings rather than open subschemes.  Nothing in the argument needs them to
be opens: `AlgebraicGeometry.pullbackTensorFunctorPullbackIso` restricts along an arbitrary
morphism, and `AlgebraicGeometry.Scheme.Cover.hom_ext` reassembles along an arbitrary open cover.

The indexed statement is assembled with `choose`, so that the families `V`, `f` and `L` stay
opaque local variables; handing an explicit composite to `refine` instead makes the conclusion
unfold definitionally once per index and per conjunct, as recorded in the implementation notes
of `StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalForm.lean`.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 17.23.3 (Tag 0B8L)](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  Without this
an invertibility hypothesis spelled with `ringCatSheaf.2` does not deliver
`Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence`.  The same list is declared in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean`. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf TopCat.Presheaf.IsSheaf

/-! ### Transporting the tensor factor along an isomorphism of sheaves -/

/-- For `g : W ⟶ X` and an isomorphism `e : N ≅ N'` of sheaves of `𝒪_W`-modules, the isomorphism
`g^*(-) ⊗ N ≅ g^*(-) ⊗ N'` of functors on quasi-coherent `𝒪_X`-modules induced by `e`.

This is `mapIso` of the native sheaf tensor bifunctor, whiskered on the left by the inverse
image. It is what lets the rigidity theorem
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset` be fed an invertible sheaf
that arrives in a different presentation from the one it names. -/
def pullbackTensorFunctorIsoOfSheafIso {X W : Scheme.{u}} (g : W ⟶ X)
    {N N' : SheafOfModules.{u} W.ringCatSheaf} (e : N ≅ N') :
    pullbackTensorFunctor g N ≅ pullbackTensorFunctor g N' :=
  Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
    (Functor.isoWhiskerLeft (Scheme.Modules.pullback g)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).mapIso
        (X := N) (Y := N') e))

/-! ### Rigidity with neither source nor target affine -/

/-- Let `W` be a scheme, let `X` be quasi-compact and quasi-separated, let `g g' : W ⟶ X` and let
`N`, `N'` be invertible sheaves of `𝒪_W`-modules. If inverse image along `g` followed by
tensoring with `N` is isomorphic to the same for `g'` and `N'`, and the image of `g` lies in some
affine open `U ⊆ X`, then `g = g'`.

This is `AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset` with the affineness
of the source and the presentation of the two sheaves both removed.  The source is covered by the
spectra of `AlgebraicGeometry.Scheme.affineCover`; on each of them the isomorphism of functors
restricts by `AlgebraicGeometry.pullbackTensorFunctorPullbackIso`, the restricted sheaves are
invertible by [Stacks, Tag 0B8L] and acquire the required presentation by
`AlgebraicGeometry.exists_module_invertible_iso_pullback_tilde_of_hom`, along which the
isomorphism is transported by `AlgebraicGeometry.pullbackTensorFunctorIsoOfSheafIso`.  The
resulting equalities are reassembled by `AlgebraicGeometry.Scheme.Cover.hom_ext`.

Nothing is assumed about `g'`; that it too lands in `U` is proved inside the affine-source
statement. -/
theorem eq_of_iso_pullbackTensorFunctor_of_isInvertible {W X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (g g' : W ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (N N' : SheafOfModules.{u} W.ringCatSheaf)
    [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N]
    [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N']
    (θ : pullbackTensorFunctor g N ≅ pullbackTensorFunctor g' N')
    (hg : Set.range g ⊆ (U : Set X)) :
    g = g' := by
  refine Scheme.Cover.hom_ext W.affineCover g g' fun x => ?_
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    exists_module_invertible_iso_pullback_tilde_of_hom (W.affineCover.f x) N inferInstance
  obtain ⟨M', hM', ⟨e'⟩⟩ :=
    exists_module_invertible_iso_pullback_tilde_of_hom (W.affineCover.f x) N' inferInstance
  refine eq_of_iso_pullbackTensorFunctor_of_range_subset _ _ U hU M M' ?_ ?_
  · exact (pullbackTensorFunctorIsoOfSheafIso _ e).symm ≪≫
      (pullbackTensorFunctorPullbackIso g (W.affineCover.f x) N).symm ≪≫
      Functor.isoWhiskerRight θ (Scheme.Modules.pullback (W.affineCover.f x)) ≪≫
      pullbackTensorFunctorPullbackIso g' (W.affineCover.f x) N' ≪≫
      pullbackTensorFunctorIsoOfSheafIso _ e'
  · rintro z ⟨y, rfl⟩
    exact hg ⟨W.affineCover.f x y, (Scheme.Hom.comp_apply _ _ _).symm⟩

/-! ### The overlap compatibility for two charts -/

/-- Given the chart data of [Stacks, Tag 0GPJ] for two opens `V₁, V₂ ⊆ Y` with the same functor
`E` — an isomorphism of schemes `fₐ : Vₐ ≅ Uₐ`, an invertible sheaf `Lₐ` of `𝒪_{Vₐ}`-modules and
the two isomorphisms `αₐ`, `βₐ` — the two chart maps read on the overlap `V₁ ⊓ V₂` are equal as
morphisms into `X`, provided `U₁` is affine.

This is the hypothesis `hVcompat` of
`AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible` for a single pair of
charts.  The isomorphism of functors it is deduced from is
`AlgebraicGeometry.pullbackTensorFunctorOverlapIso`, the containment of the image of the first
chart map in `U₁` is `AlgebraicGeometry.range_subset_coe_of_comp_ι`, the restrictions of the `Lₐ`
to the overlap are invertible by [Stacks, Tag 0B8L], and the conclusion is
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_isInvertible`.  Note that the overlap is
not required to be quasi-compact: that hypothesis was only needed for the weaker statement
`AlgebraicGeometry.range_eq_of_chartIso_overlap` about images. -/
theorem homOfLE_comp_eq_of_chartIso_overlap {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {V₁ V₂ : Y.Opens} {U₁ U₂ : X.Opens}
    {F₁ : (SheafOfModules.isQuasicoherent U₁.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V₁.toScheme.ringCatSheaf).FullSubcategory}
    {F₂ : (SheafOfModules.isQuasicoherent U₂.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V₂.toScheme.ringCatSheaf).FullSubcategory}
    (f₁ : V₁.toScheme ≅ U₁.toScheme) (f₂ : V₂.toScheme ≅ U₂.toScheme)
    (L₁ : SheafOfModules.{u} V₁.toScheme.ringCatSheaf)
    (L₂ : SheafOfModules.{u} V₂.toScheme.ringCatSheaf)
    [Stacks.SheafOfModules.IsInvertible V₁.toScheme.presheaf V₁.toScheme.ringCatSheaf.2 L₁]
    [Stacks.SheafOfModules.IsInvertible V₂.toScheme.presheaf V₂.toScheme.ringCatSheaf.2 L₂]
    (α₁ : E ⋙ quasicoherentRestriction V₁.ι ≅ quasicoherentRestriction U₁.ι ⋙ F₁)
    (β₁ : F₁ ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V₁.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f₁.hom L₁)
    (α₂ : E ⋙ quasicoherentRestriction V₂.ι ≅ quasicoherentRestriction U₂.ι ⋙ F₂)
    (β₂ : F₂ ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V₂.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f₂.hom L₂)
    (hU₁ : IsAffineOpen U₁) :
    Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ≫ f₁.hom ≫ U₁.ι =
      Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂) ≫ f₂.hom ≫ U₂.ι := by
  have h₁ := @Stacks.RingedSpace.modulePullback_isInvertible _ _
    (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).toLRSHom.toShHom L₁ inferInstance
  have h₂ := @Stacks.RingedSpace.modulePullback_isInvertible _ _
    (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).toLRSHom.toShHom L₂ inferInstance
  exact eq_of_iso_pullbackTensorFunctor_of_isInvertible _ _ U₁ hU₁ _ _
    (pullbackTensorFunctorOverlapIso E f₁ f₂ L₁ L₂ α₁ β₁ α₂ β₂)
    (range_subset_coe_of_comp_ι (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ≫ f₁.hom) _
      (Category.assoc _ _ _))

/-! ### `hVcompat` for the reconstruction's own charts -/

/-- Let `X` and `Y` be quasi-compact and quasi-separated schemes, let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence and let `U i` be an affine open cover of `X`. Then
there are opens `V i` covering `Y` and isomorphisms `f i : V i ≅ U i` such that for every pair
`i, j` the two chart maps read on `V i ⊓ V j` are equal as morphisms into `X`.

The conclusion is verbatim the hypothesis `hVcompat` of
`AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible`, which glues the charts
into a single isomorphism `Y ≅ X`.  Its mirror hypothesis `hUcompat` is a separate matter, proved
by `AlgebraicGeometry.exists_isOpenCover_schemeIso_mirrorOverlapCompatible_of_isAffineOpenCover`.

This is `AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover`
with the functors `F i`, the invertible sheaves `L i` and the two per-chart isomorphisms all
consumed by `AlgebraicGeometry.homOfLE_comp_eq_of_chartIso_overlap`. -/
theorem exists_isOpenCover_schemeIso_overlapCompatible_of_isAffineOpenCover {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {ι : Type u} (U : ι → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    ∃ (V : ι → Y.Opens) (f : ∀ i, (V i).toScheme ≅ (U i).toScheme),
      IsOpenCover V ∧
        ∀ i j, Y.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ (f i).hom ≫ (U i).ι =
          Y.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ (f j).hom ≫ (U j).ι := by
  obtain ⟨V, hVcover, hV⟩ :=
    exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover e U hUaff hUcover
  choose hVaff hVc F f L hFequiv hLinv hα hβ using hV
  refine ⟨V, f, hVcover, fun i j => ?_⟩
  have := hLinv i
  have := hLinv j
  exact homOfLE_comp_eq_of_chartIso_overlap e.functor (f i) (f j) (L i) (L j)
    (hα i).some (hβ i).some (hα j).some (hβ j).some (hUaff i)

end AlgebraicGeometry

end

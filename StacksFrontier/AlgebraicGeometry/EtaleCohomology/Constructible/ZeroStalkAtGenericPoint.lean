module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion
public import StacksFrontier.CategoryTheory.Limits.ArrowImageFilteredColimit
public import StacksFrontier.Topology.Sober.Generization
public import StacksFrontier.Topology.Spectral.BijectionHomeomorph
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale sheaves with vanishing stalk at a geometric generic point

Let `X` be a quasi-compact and quasi-separated scheme and let `η` be a generic point of an
irreducible component of `X`. An abelian sheaf on `X_étale` whose stalk at a geometric point
`η̄` above `η` vanishes is a filtered colimit of constructible abelian sheaves each of whose
supports is contained in a closed subscheme of `X` not containing `η`. This is Stacks 0F0M (1).

## Main results

* `AlgebraicGeometry.isZero_etaleStalk_image_of_etaleStalkFunctor_map_eq_zero` — the geometric
  stalk of the image of a morphism whose geometric stalk vanishes, vanishes.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_image` — the image of a morphism of constructible
  abelian sheaves is constructible, which is Stacks 03RZ for abelian sheaves applied to the
  factorisation of a morphism through its image.
* `Topology.notMem_closure_of_mem_genericPoints_of_isConstructible` — on a spectral space, a
  constructible set avoiding a generic point of an irreducible component has closure avoiding it.
  This is the last step of the source proof, cited there to Topology, Lemma 005K.
* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_notMem_supportSheaf` —
  the whole of Stacks 0F0M (1) except its last step: the supports of the terms do not contain `η`.
* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_support_notMem` —
  **Stacks 0F0M (1)**, with two inputs carried as hypotheses, see below.

## Implementation notes

The conclusion is given as data and not as a bare existence statement about the sheaf: an index
category, an instance witnessing that it is filtered, a diagram, a cocone with apex `ℱ` itself, a
colimit witness for that cocone, constructibility of every term of the diagram, and for every term
a closed subset avoiding `η` which contains its support. A closed subscheme of `X` and a closed
subset of `X` carry exactly the same condition here, since the support of a sheaf is a subset of
`X` and every closed subset is the underlying set of a closed subscheme (the reduced induced
structure), so the support condition is stated with the closed subset.

The index category produced is the category of those transition maps of a presentation of `ℱ` by
constructible sheaves whose stalk at `η̄` vanishes, and the diagram is the images of those
transition maps; that this is again a filtered colimit of `ℱ` is
`CategoryTheory.Limits.isColimitArrowImageCocone`, and is the mechanism of the proof in the
source, there described as a reindexing of the directed set.

Two inputs of the source proof are carried as explicit hypotheses, each of them an input the
library does not have available in the shape the proof uses.

* `h03SA` is Stacks 03SA, that a torsion abelian sheaf is a filtered colimit of constructible
  abelian sheaves. The library does not have it; this is also the only place the torsion
  hypothesis of the source statement is used, so it does not appear here.
* `h095P` is Stacks 095P, that a filtered system of constructible sheaves whose colimit has
  vanishing stalk at `η̄` has, out of every stage, a transition map with vanishing stalk at `η̄`.
  The library has Stacks 095P itself
  (`AlgebraicGeometry.isEssentiallyConstantWith_of_isConstructibleAbelianSheaf_colimit`) but not
  the restriction of a sheaf to the point `η` along which the source applies it.

The last step of the source proof, from `η ∉ E` for a constructible `E` to `η ∉ closure E`, is
*proved*, as `Topology.notMem_closure_of_mem_genericPoints_of_isConstructible`. The source cites
Topology, Lemma 005K for it; the library has that lemma in the shape the source states it
(`Topology.tfae_with_generic_point`), about finite unions of locally closed subsets, and that
shape is not enough — the step needs `E` to be constructible in the retrocompact sense. What
discharges it is Stacks 0903 (1),
`Topology.IsConstructible.exists_mem_specializes_of_mem_closure`, together with the fact that a
generic point of an irreducible component of a Kolmogorov space has no other generization,
`TopologicalSpace.forall_specializes_eq_of_mem_genericPoints`.

## References

* [Stacks Project, Tag 0F0M](https://stacks.math.columbia.edu/tag/0F0M)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 005K](https://stacks.math.columbia.edu/tag/005K)
* [Stacks Project, Tag 0903](https://stacks.math.columbia.edu/tag/0903)
* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **On a spectral space a constructible set avoiding a generic point of an irreducible
component has closure avoiding it.** This is the last step of the proof of Stacks 0F0M, cited
there to Topology, Lemma 005K.

A point of the closure of a constructible set is a specialization of a point of the set by
Stacks 0903 (1), and a generic point of an irreducible component of a Kolmogorov space has no
generization but itself, so that point is the generic point itself. -/
@[sga "1 IV 6.3" "special case"]
public theorem Topology.notMem_closure_of_mem_genericPoints_of_isConstructible
    {α : Type*} [TopologicalSpace α] [SpectralSpace α] {η : α} (hη : η ∈ genericPoints α)
    {E : Set α} (hE : Topology.IsConstructible E) (hηE : η ∉ E) : η ∉ closure E := fun hmem =>
  have ⟨z, hzE, hz⟩ := Topology.IsConstructible.exists_mem_specializes_of_mem_closure hE hmem
  hηE (TopologicalSpace.forall_specializes_eq_of_mem_genericPoints hη z hz ▸ hzE)

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The stalk at a geometric point as a functor on abelian sheaves on the small étale site. It is
the fibre functor of the point of the site attached to the geometric point, so the general theory
of points of a site applies to it; objectwise it is `AlgebraicGeometry.etaleStalk`. -/
public abbrev smallEtaleGeometricStalkFunctor (p : GeometricPoint X.obj) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} :=
  (geometricPointSitePoint B X.obj X.property p).sheafFiber (A := AddCommGrpCat.{u + 1})

/-- **The geometric stalk of the image of a morphism whose geometric stalk vanishes, vanishes.**
The stalk functor at a geometric point is exact, so it carries the epimorphism onto and the
monomorphism out of the image to an epimorphism and a monomorphism; the composite of the two is
the stalk of the morphism, which is zero, so the monomorphism out of the stalk of the image is
zero and the stalk of the image is a zero object. -/
public theorem isZero_etaleStalk_image_of_etaleStalkFunctor_map_eq_zero
    (p : GeometricPoint X.obj)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (hf : (smallEtaleGeometricStalkFunctor B X p).map f = 0) :
    IsZero ((smallEtaleGeometricStalkFunctor B X p).obj (Limits.image f)) := by
  have hAB5 : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  have hmono : Mono ((smallEtaleGeometricStalkFunctor B X p).map (Limits.image.ι f)) :=
    (smallEtaleGeometricStalkFunctor B X p).map_mono _
  have hepi : Epi ((smallEtaleGeometricStalkFunctor B X p).map (factorThruImage f)) :=
    (smallEtaleGeometricStalkFunctor B X p).map_epi _
  have hcomp : (smallEtaleGeometricStalkFunctor B X p).map (factorThruImage f) ≫
      (smallEtaleGeometricStalkFunctor B X p).map (Limits.image.ι f) = 0 := by
    rw [← Functor.map_comp, Limits.image.fac, hf]
  have hzero : (smallEtaleGeometricStalkFunctor B X p).map (Limits.image.ι f) = 0 :=
    zero_of_epi_comp _ hcomp
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← cancel_mono ((smallEtaleGeometricStalkFunctor B X p).map (Limits.image.ι f)),
    Category.id_comp, hzero, zero_comp]

section

variable
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **The image of a morphism of constructible abelian sheaves is constructible.** The image is
the kernel of the cokernel of the morphism, and constructible abelian sheaves are closed under
kernels and cokernels by Stacks 03RZ. -/
public theorem isConstructibleAbelianSheaf_image
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (hF : IsConstructibleAbelianSheaf B X F) (hG : IsConstructibleAbelianSheaf B X G) :
    IsConstructibleAbelianSheaf B X (Limits.image f) :=
  ObjectProperty.prop_of_iso
    (P := fun F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
      IsConstructibleAbelianSheaf B X F)
    (Abelian.imageIsoImage f)
    (ObjectProperty.prop_kernel _ (cokernel.π f) hG (ObjectProperty.prop_cokernel _ f hF hG))

/-- **Stacks 0F0M (1), with the support condition before taking closures.** Let `X` be a scheme,
let `η` be a point of `X` and let `η̄` be a geometric point above it. An abelian sheaf `ℱ` on the
small étale site of `X` whose stalk at `η̄` is zero is a filtered colimit of constructible abelian
sheaves whose supports do not contain `η`.

This is the whole of the source proof except its last step, which replaces "the support does not
contain `η`" by "the support is contained in a closed subscheme not containing `η`". Neither the
hypothesis that `X` be quasi-compact and quasi-separated nor the hypothesis that `η` be a generic
point of an irreducible component is needed for this much.

`h03SA` and `h095P` are carried, as described in the module documentation. -/
public theorem exists_isFilteredColimit_isConstructibleAbelianSheaf_notMem_supportSheaf
    (η : X.obj) (p : GeometricPoint X.obj) (hp : GeometricPoint.LiesOver p η)
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hstalk : IsZero ((smallEtaleGeometricStalkFunctor B X p).obj ℱ))
    (h03SA : ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj ℱ),
      Nonempty (IsColimit (Cocone.mk ℱ ι)) ∧ ∀ i, IsConstructibleAbelianSheaf B X (D.obj i))
    (h095P : ∀ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj ℱ), IsColimit (Cocone.mk ℱ ι) →
      (∀ i, IsConstructibleAbelianSheaf B X (D.obj i)) →
      IsZero ((smallEtaleGeometricStalkFunctor B X p).obj ℱ) →
      ∀ i : I, ∃ (j : I) (f : i ⟶ j),
        (smallEtaleGeometricStalkFunctor B X p).map (D.map f) = 0) :
    ∃ (J : Type (u + 1)) (_ : SmallCategory J) (_ : IsFiltered J)
      (G : J ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (κ : G ⟶ (Functor.const J).obj ℱ),
      Nonempty (IsColimit (Cocone.mk ℱ κ)) ∧
        (∀ j, IsConstructibleAbelianSheaf B X (G.obj j)) ∧
          ∀ j, η ∉ supportSheaf.{u, u + 1} B X.obj X.property (G.obj j) := by
  classical
  obtain ⟨I, hI, hIfiltered, D, ι, ⟨hc⟩, hD⟩ := h03SA
  let _ : SmallCategory I := hI
  have _ : IsFiltered I := hIfiltered
  choose n φ hφ using h095P I hI hIfiltered D ι hc hD hstalk
  -- the arrows of `I` whose stalk at `η̄` vanishes
  set P : ObjectProperty (Arrow I) :=
    fun a => (smallEtaleGeometricStalkFunctor B X p).map (D.map a.hom) = 0 with hP
  have hφ' : ∀ i, P (Arrow.mk (φ i)) := hφ
  have _ : IsFiltered P.FullSubcategory := isFiltered_arrowFullSubcategory P φ hφ'
  obtain ⟨hcolim⟩ := isColimitArrowImageCocone P D φ hφ' hc
  refine ⟨P.FullSubcategory, inferInstance, inferInstance, arrowImageDiagram P D,
    (arrowImageCocone P D (Cocone.mk ℱ ι)).ι, ⟨hcolim⟩,
    fun a => isConstructibleAbelianSheaf_image B X (D.map a.obj.hom) (hD _) (hD _),
    fun a => ?_⟩
  have hzero : IsZero (etaleStalk B X.obj X.property p
      (Limits.image (D.map a.obj.hom)).obj) :=
    isZero_etaleStalk_image_of_etaleStalkFunctor_map_eq_zero B X p (D.map a.obj.hom) a.property
  rw [mem_supportSheaf_iff.{u, u + 1} B X.obj X.property _ p η hp]
  exact not_not.2 ((isZero_etaleStalk_ulift_iff.{u, u + 1} B X.obj X.property _ p).2 hzero)

variable [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
  [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
    ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1}]

/-- **Stacks 0F0M (1).** Let `X` be a quasi-compact and quasi-separated scheme and let `η` be a
generic point of an irreducible component of `X`. Let `ℱ` be an abelian sheaf on the small étale
site of `X` whose stalk at a geometric point `η̄` above `η` is zero. Then `ℱ` is a filtered
colimit of constructible abelian sheaves, each of whose supports is contained in a closed subset
of `X` — equivalently a closed subscheme of `X` — not containing `η`.

Two inputs of the source proof are carried as hypotheses, as described in the module
documentation: `h03SA` is Stacks 03SA for torsion abelian sheaves, the presentation of `ℱ` as a
filtered colimit of constructible abelian sheaves, which is also where the torsion hypothesis of
the source statement is used and so does not appear here; and `h095P` is Stacks 095P in the form
the proof uses it, after restriction to `η`. Everything else is proved: the construction of the
index category and of the diagram, that it is filtered and that its colimit is `ℱ` again,
constructibility of its terms by Stacks 03RZ, vanishing of their stalks at `η̄`, constructibility
of their supports by Stacks 09YS (2), and that the closure of such a support avoids `η`. -/
@[stacks 0F0M "part (1), abelian sheaves, with Stacks 03SA for torsion abelian sheaves (h03SA) \
and Stacks 095P after restriction to η (h095P) carried as hypotheses"]
public theorem exists_isFilteredColimit_isConstructibleAbelianSheaf_support_notMem
    (η : X.obj) (hη : η ∈ genericPoints X.obj)
    (p : GeometricPoint X.obj) (hp : GeometricPoint.LiesOver p η)
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hstalk : IsZero ((smallEtaleGeometricStalkFunctor B X p).obj ℱ))
    (h03SA : ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj ℱ),
      Nonempty (IsColimit (Cocone.mk ℱ ι)) ∧ ∀ i, IsConstructibleAbelianSheaf B X (D.obj i))
    (h095P : ∀ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj ℱ), IsColimit (Cocone.mk ℱ ι) →
      (∀ i, IsConstructibleAbelianSheaf B X (D.obj i)) →
      IsZero ((smallEtaleGeometricStalkFunctor B X p).obj ℱ) →
      ∀ i : I, ∃ (j : I) (f : i ⟶ j),
        (smallEtaleGeometricStalkFunctor B X p).map (D.map f) = 0) :
    ∃ (J : Type (u + 1)) (_ : SmallCategory J) (_ : IsFiltered J)
      (G : J ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (κ : G ⟶ (Functor.const J).obj ℱ),
      Nonempty (IsColimit (Cocone.mk ℱ κ)) ∧
        (∀ j, IsConstructibleAbelianSheaf B X (G.obj j)) ∧
          ∀ j, ∃ Z : Set X.obj, IsClosed Z ∧ η ∉ Z ∧
            supportSheaf.{u, u + 1} B X.obj X.property (G.obj j) ⊆ Z := by
  have hspec : SpectralSpace X.obj :=
    Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace X.obj
  obtain ⟨J, hJ, hJfiltered, G, κ, hcolim, hG, hsupp⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_notMem_supportSheaf
      B X η p hp ℱ hstalk h03SA h095P
  refine ⟨J, hJ, hJfiltered, G, κ, hcolim, hG, fun j => ?_⟩
  refine ⟨closure (supportSheaf.{u, u + 1} B X.obj X.property (G.obj j)), isClosed_closure,
    ?_, subset_closure⟩
  exact Topology.notMem_closure_of_mem_genericPoints_of_isConstructible hη
    (isConstructible_supportSheaf B X (G.obj j) (hG j)) (hsupp j)

end

end AlgebraicGeometry

end

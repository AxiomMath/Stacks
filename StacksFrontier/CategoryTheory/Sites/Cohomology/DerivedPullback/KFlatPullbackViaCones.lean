module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackCyclesInput
import StacksCore.Tactic.StacksAttribute

/-!
# The K-flatness assertion of Tag 0G7E needs Stacks 05VD alone

`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` proves the K-flatness
assertion of Stacks 0G7E —
the pullback of a K-flat complex of `O`-modules with flat terms along a morphism of ringed
topoi is K-flat — from **three** inputs:
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat` (Stacks 05VD),
`Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact` (Stacks 0G6R) and
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.CyclesIsFlat`
(Stacks 0G7C).  The third is discharged by
`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`.

**This file removes the second.**  The resulting statement takes `PullbackPreservesIsFlat`
(Stacks 05VD) as its only input.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_pullbackPreservesIsFlat`:
  the K-flatness assertion of
  Stacks 0G7E on `PullbackPreservesIsFlat` (Stacks 05VD) alone.
* `Stacks.Sheaves.DerivedPullback.KFlatPullback.mappingCone_resolution_facts` and
  `kFlat_pullbackComplex_of_mappingCone`: the two halves of that argument, split off so that
  each concrete mapping cone is elaborated in its own declaration.

## Why 0G6R drops out

The source's argument resolves `K` by
  `Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit`, which gives a
quasi-isomorphism `α : Λ = colim D ⟶ K` out of the colimit of a sequence of bounded above
complexes of flat modules, and then compares `f^*K` with `f^*Λ` through the **kernel** of `α`:
`0 ⟶ ker α ⟶ Λ ⟶ K ⟶ 0` is short exact, so `f^*` of it is short exact by Tag 0G6R and
Tag 0G7B finishes.  That is the only place 0G6R enters
(`Stacks.Sheaves.DerivedPullback.KFlatPullback.shortExact_map_pullbackComplex` is its sole
consumer in the Stacks 0G7E development).

Comparing `f^*K` with `f^*Λ` through the **mapping cone** of `α` instead needs no exactness of
`f^*` at all, because the mapping cone is built out of biproducts and an additive functor
commutes with it on the nose
(`HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso`).  The three facts about
`cone α` that the argument needs are each already in the tree:

* `cone α` is **acyclic**, because `α` is a quasi-isomorphism
  (`CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone`);
* `cone α` is **K-flat**, as the third vertex of the distinguished mapping-cone triangle whose
  other two vertices `Λ` and `K` are K-flat
  (`CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang`);
* `cone α` has **flat terms**, its degree `i` term being `Λ^{i+1} ⊞ K^i`
  (`Stacks.Sheaves.RingedToposDerivedPullback.isFlat_biprod`).

So `cone α` is an acyclic K-flat complex with flat terms, and
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_acyclic` — which runs on
  05VD alone, the resolution's
kernel sequence never arising there — gives that `f^*(cone α)` is K-flat.  Transporting along
the commutation isomorphism, `cone (f^*α)` is K-flat; `f^*Λ` is K-flat by the engine
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_isColimit`, also on 05VD
  alone; and `f^*K` is the
**second** vertex of the distinguished mapping-cone triangle of `f^*α`, so
`CochainComplex.KFlatBifunctor.kFlat_obj₂_of_distTriang` concludes.

Two-out-of-three in a distinguished triangle is available for `Stacks.SheafOfModules.KFlat.KFlat`
  in all
three positions (`kFlat_obj₁_of_distTriang`, `kFlat_obj₂_of_distTriang`,
`kFlat_obj₃_of_distTriang`) precisely because K-flatness relative to a bifunctor is "the image
under `Φ_G` lies in the acyclic subcategory" for every acyclic `G`, and that is a triangulated
subcategory.  The class *"K-flat **with flat terms**"* is **not** so closed — a contractible
complex with non-flat terms is isomorphic in `K(O')` to the zero complex — which is why
`Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone` is stated for mapping cones of
  morphisms of complexes
rather than for an abstract third vertex.  Nothing here needs the conjunction to be
triangulated: flat terms of `cone α` are computed from its biproduct description, and the
conclusion is about `Stacks.SheafOfModules.KFlat.KFlat` alone.

## Tagging

**No tag is placed here.**  Stacks 0G7E registers three clause strings; the
statement below is the one the tag calls "K-flatness", but it carries
`Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat`, a `Prop`-valued
hypothesis the tag does not have and
which no declaration in either tree concludes.  The remaining untagged string, for
flatness of the pulled-back terms, is registered on the 05VD declaration itself and is
likewise open.  The one clause that is covered is tagged in the Stacks 0G7E development, on the
`PreservesZeroMorphisms` instance.

**When Stacks 05VD lands, this is the declaration the K-flatness tag goes on**, and the edit is
to delete the `hpf` binder and apply 05VD in its place.

## Universes

Both ringed topoi are at `AlgebraicGeometry.RingedTopos.{u, u, u}`: the object, morphism and
section universes agree, and `AlgebraicGeometry.RingedToposSiteHom` presents the geometric
morphism by a continuous functor between the underlying sites.  Neither narrowing is chosen
here.  The universe collapse is forced **four** independent ways on this chain —
`SheafOfModules.pullback`, Tag 03EX, `CategoryTheory.Functor.IsMorphismOfSites` (declared for
`{C D : Type u}` with `SmallCategory` on both) and
`Stacks.Sheaves.ModuleAdjunction.extendScalars` — and the same narrowing is carried by the
already-tagged chain this file sits on (`06YS`, `03EX`, `03EY`, `0G7B`).  The presentation of
the morphism is the one tag `01D3` part (2) is carried on in this tree.

## References

* [The Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [The Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [The Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [The Stacks Project, Tag 0G6E](https://stacks.math.columbia.edu/tag/0G6E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.KFlatPullback

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]

/-- **The mapping cone of a resolution.**  For a quasi-isomorphism `α : L ⟶ K` of complexes of
`O`-modules with `K` and `L` K-flat with flat terms, the mapping cone of `α` is acyclic, is
K-flat, and has flat terms — the last because each of its terms is a biproduct `L^{i+1} ⊕ K^i`
(Stacks 06YY).

This is the `O`-side half of the cone route and mentions no morphism of ringed topoi.  It is a
separate declaration because elaborating `CochainComplex.mappingCone α` over complexes of
sheaves of modules costs a few tens of thousands of heartbeats per occurrence, so the whole
argument does not fit the elaboration budget of a single declaration. -/
theorem mappingCone_resolution_facts
    [HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (hK : Stacks.SheafOfModules.KFlat.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hΛflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hΛkflat : Stacks.SheafOfModules.KFlat.KFlat Y.O L)
    (α : L ⟶ K) (hqis : QuasiIso α) :
    (CochainComplex.mappingCone α).Acyclic ∧
      Stacks.SheafOfModules.KFlat.KFlat Y.O (CochainComplex.mappingCone α) ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
        ((CochainComplex.mappingCone α).X i)) := by
  refine ⟨(CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone α).1 hqis, ?_,
    fun i ↦ ?_⟩
  · exact CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang _ _ _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished α) hΛkflat hK
  · have := HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct α i (i + 1) rfl
    exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso Y.O
      (HomologicalComplex.homotopyCofiber.XIsoBiprod α i (i + 1) rfl).symm
      (Stacks.Sheaves.RingedToposDerivedPullback.isFlat_biprod Y.O _ _ (hΛflat (i + 1))
        (hflatK i))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The cone route, pullback half.**  If the pullbacks of `L` and of the mapping cone of
`α : L ⟶ K` are K-flat, so is the pullback of `K`:  an additive functor commutes with the
mapping cone on the nose, so `f^*(cone α)` is `cone (f^*α)`, and the distinguished triangle
`f^*L ⟶ f^*K ⟶ cone (f^*α)` gives the middle term.  No exactness of `f^*` is used, which is
what removes Stacks 0G6R from the hypotheses.

Stated separately from `kFlat_pullbackComplex_of_pullbackPreservesIsFlat` for the same reason as
`mappingCone_resolution_facts`: the two concrete mapping cones, one over `Y` and one over `X`,
cannot both be elaborated inside one declaration's budget. -/
theorem kFlat_pullbackComplex_of_mappingCone
    [HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (α : L ⟶ K)
    (hpC : Stacks.SheafOfModules.KFlat.KFlat X.O
      ((pullbackComplex f).obj (CochainComplex.mappingCone α)))
    (hpΛ : Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj L)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj K) :=
  have : (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) from
        f.pullbackTopos).Additive :=
    AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_additive f
  CochainComplex.KFlatBifunctor.kFlat_obj₂_of_distTriang _ _ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished ((pullbackComplex f).map α)) hpΛ
    (CochainComplex.KFlatBifunctor.KFlat.of_iso _ hpC
      (HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso α _))

/-- **The K-flatness assertion of Stacks Tag 0G7E, on Stacks 05VD alone.**

The pullback of a K-flat complex of `O`-modules with flat terms along a morphism of ringed
topoi is a K-flat complex of `O'`-modules, assuming only that pullback preserves flatness of a
module (`PullbackPreservesIsFlat`, Stacks 05VD).

This is `kFlat_pullbackComplex` with its `PullbackPreservesShortExact` (Stacks 0G6R) input
removed: the resolution of `K` is compared with `K` through the mapping cone of the resolving
quasi-isomorphism rather than through its kernel, and an additive functor commutes with the
mapping cone on the nose, so no exactness of `f^*` is used.  See the implementation notes. -/
theorem kFlat_pullbackComplex_of_pullbackPreservesIsFlat
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj K) := by
  have hbbY : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    :=
    inferInstance
  have hbbX : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    :=
    inferInstance
  obtain ⟨D, α, hLE, hDflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit Y.O K
  obtain ⟨hCacyc, hCkflat, hCflat⟩ := mappingCone_resolution_facts hK hflatK
    (Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X Y.O D hDflat)
    (Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat Y.O D hLE
      hDflat) α hqis
  have hpC : Stacks.SheafOfModules.KFlat.KFlat X.O
      ((pullbackComplex f).obj (CochainComplex.mappingCone α)) :=
    kFlat_pullbackComplex_of_acyclic f hmos hpf _ hCacyc hCkflat hCflat
  have hpΛ : Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj (colimit D)) :=
    kFlat_pullbackComplex_colimit f hmos hpf D hLE hDflat
  exact kFlat_pullbackComplex_of_mappingCone f α hpC hpΛ

end Stacks.Sheaves.DerivedPullback.KFlatPullback

end

end

module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedCounitCommShift
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
import all StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback along a morphism of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi.  Tag 06YY asserts that
degreewise pullback has a left derived functor

`Lf^* : D(𝒪') ⟶ D(𝒪)`

which is *exact* as a functor of triangulated categories, and that `Lf^* 𝒦^• = f^* 𝒦^•` for a
K-flat complex `𝒦^•` with flat terms, in particular for a bounded above complex of flat
`𝒪'`-modules.

The derived functor itself,
  `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback`, and its canonical
    comparison
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison` with degreewise
  pullback are already built in
Chapter 21, Section 19, from a resolving datum whose resolving half is discharged by Tag 06YS.
What this file adds is the rest of 06YY: the compatibility of the derived pullback with the
shift, its *exactness*, and the two computation statements.

Everything here is relative to the single hypothesis
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` — that degreewise pullback
carries a quasi-isomorphism between K-flat complexes of `𝒪'`-modules to an isomorphism of
`D(𝒪)`.  That hypothesis is exactly the input the source obtains from Tags 0G7E and 06YT, or, in
the other route the source offers, from Tags 0G7C and 0G6R.  **The second route now closes**, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackExistence.lean`,
whose `pullbackInvertsQuasiIso_isKFlat` discharges the hypothesis for every morphism of ringed
topoi and where the unconditional forms of the clauses below carry the tag.  It is still a
parameter here, because the reduction to Tag 0G6R is downstream of this file in the import
order and because the results below hold along any morphism with the resolving property,
whether or not its underlying continuous functor is a morphism of sites.  So
`derivedPullback_commShift`,
`derivedPullback_isTriangulated` and the two `isIso_derivedPullbackComparison_app_*` results
below are the whole of 06YY once it is supplied.  Nothing else is left over:
`derivedPullback_isTriangulated` is the conclusion "there exists an exact functor `Lf^*`", and
the computation statements are "`Lf^* 𝒦^• = f^* 𝒦^•`" in the form of invertibility of the
canonical comparison.

## Main definitions

* `Stacks.Sheaves.RingedToposDerivedPullback.derivedPullbackComparisonCommShift` is the
  compatibility of the canonical
  comparison with the commutation of `Lf^*` with the shift.

## Main results

* `Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone`: the mapping cone of a morphism
  between K-flat complexes
  with flat terms is again K-flat with flat terms.
* `Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift`: `Lf^*` commutes with the
  shift.
* `Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated`: **the exactness
  assertion of Tag 06YY.**
  `Lf^*` is an exact functor of triangulated categories.
* `Stacks.Sheaves.RingedToposDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat_of_flat`:
  **the computation
  assertion of Tag 06YY.**  The canonical comparison `Lf^* 𝒦^• ⟶ f^* 𝒦^•` is invertible for a
  K-flat complex `𝒦^•` with flat terms, which is the form the source states.
* `isIso_derivedPullbackComparison_app_of_boundedAbove_of_flat`: the same for a
  bounded above complex of flat `𝒪'`-modules, by Tag 06YQ.
* `Stacks.Sheaves.RingedToposDerivedPullback.pullbackInvertsQuasiIso_isKFlat_of_exact`: the
  hypothesis carried through this
  file is satisfiable — it holds along every morphism whose degreewise pullback is exact.
* `Stacks.Sheaves.RingedToposDerivedPullback.isFlat_biprod`: a binary biproduct of flat sheaves of
  modules is flat, on a small site.  Its clients are elsewhere in the tree;
  `isKFlat_mappingCone` reads the terms `K^{i+1} ⊞ L^i` of the cone off
  `Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize` instead, which is the same fact
  with the module universe free of the site.

## Implementation notes

*Why the hypothesis is carried here even though it is now discharged.*  The source's proof of 06YY
  applies the
general criterion of Derived Categories, Lemma 06XN to the class of K-flat complexes with flat
terms.  Condition (1) of that criterion — that the class resolves every complex — is Tag 06YS
and is proved (`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat`).
  Condition (2) is that `f^*` carries a
quasi-isomorphism between members of the class to a quasi-isomorphism, and the source obtains
it by writing `f^* = (f^{-1}-) ⊗_{f^{-1}𝒪'} 𝒪`, using exactness of `f^{-1}`, stability of
K-flatness under pullback (Tag 0G7E) and Tag 06YT.  Tag 06YT has no declaration anywhere in the
tree, and Tag 0G7E is in the tree only as
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex`, conditional on
`f.u.IsMorphismOfSites` together with its three named predicates, of which `CyclesIsFlat`
(Tag 0G7C) is discharged unconditionally by
`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`, `PullbackPreservesIsFlat`
(Tag 05VD) by `AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat` and
`PullbackPreservesShortExact` (Tag 0G6R) by
`AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesShortExact`, both in
`StacksFrontier/CategoryTheory/Sites/Modules/FlatMorphisms/PullbackPreservesFlatness.lean`.  The
route through 0G7C and 0G6R therefore closes, and condition (2) follows — but only downstream of
this file, so condition (2) is still the parameter `hinv` here, in the spelling Chapter 21,
Section 19 already uses for it.  Note that 0G7E states K-flatness with
`Stacks.SheafOfModules.KFlat.KFlat`, which `Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor`
  identifies with the
spelling `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` uses here.

*The class is K-flatness together with flatness of the terms.*
  `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` is the
conjunction, which is the class Tag 06YS resolves by and the class Tag 0G7E's argument consumes.
The cone-closure step is therefore `isKFlat_mappingCone` and **not** an
`IsTriangulatedClosed₃`: termwise flatness is not invariant under homotopy equivalence, so the
abstract third vertex of a distinguished triangle of `K(𝒪')` need not have flat terms even when
the first two do.  `derivedPullback_isTriangulated` consequently builds its triangle as the
mapping-cone triangle of a representative `(P.ι.map a.hom).out` of the morphism supplied by
essential surjectivity, rather than from `Pretriangulated.distinguished_cocone_triangle`; the
identification of the two first maps is `HomotopyCategory.quotient_map_out`.  This is the one
place where flatness of a binary biproduct of flat sheaves of modules is needed, which is
`Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize`.

*The comparison's compatibility with shifts is not in the library at the generality needed.*
`StacksDraft.PseudoCoherence.leftDerivedCommShift` makes a total left derived functor commute
with the shift, but `Functor.isTriangulated_of_rightExtension` also wants the counit to be
compatible with that commutation, and the only copy of that statement,
`leftDerivedCommShift_compatibility` in `StacksFrontier/Homology/Tor/DerivedExtensionScalars.lean`,
is `private`.  The abstract statement this file needs is
`CategoryTheory.Functor.IsLeftDerivedFunctor.natTrans_commShift` of
`StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedCounitCommShift`, which is imported
rather than copied.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Sheaves.RingedToposDerivedPullback

/-! ### Flatness of a binary biproduct of sheaves of modules -/

section Biproduct

universe u

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- **A binary biproduct of flat sheaves of modules is flat.**

The tree has Tag 03EY only in its part (2) form — the *left* term of a short exact sequence is
flat when the other two are — so the split sequence `0 ⟶ M ⟶ M ⊞ N ⟶ N ⟶ 0` does not give
this.  It is instead the coproduct statement of Tag 03EU at a two-element index, transported
along `M ⊞ N ≅ M ⨿ N ≅ ∐ g`.  The index has to be lifted to the module universe, since Tag
03EU's coproducts are indexed by `Type u` while `WalkingPair` lives in `Type 0`.

This is the one thing a cone-closure argument for the class *"K-flat with flat terms"* needs
beyond what is already available: the degree `i` term of a mapping cone is
`K^{i+1} ⊞ L^i`. -/
theorem isFlat_biprod (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
  R))
    (hM : SheafOfModules.IsFlat.{u, u, u, u} (O := R) M)
    (hN : SheafOfModules.IsFlat.{u, u, u, u} (O := R) N) :
    SheafOfModules.IsFlat.{u, u, u, u} (O := R) (M ⊞ N) := by
  let g : ULift.{u, 0} WalkingPair →
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) :=
    fun i ↦ WalkingPair.casesOn i.down M N
  have hcop := Stacks.SheafOfModules.FlatCoproduct.isFlat_coproduct.{u, u} g
    (by rintro ⟨⟨⟩⟩ <;> assumption)
  have := Stacks.SheafOfModules.FlatCoproduct.hasColimitsOfShape_discrete.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf R) (ULift.{u, 0} WalkingPair)
  exact SheafOfModules.IsFlat.of_iso R ((HasColimit.isoOfEquivalence (F := Discrete.functor g)
    (G := pair M N) (Discrete.equivalence Equiv.ulift) (Iso.refl _)) ≪≫
      (biprod.isoCoprod M N).symm) hcop

end Biproduct

/-! ### Derived pullback for a morphism of ringed topoi -/

universe w

attribute [local instance] HasDerivedCategory.standard

section MappingCone

universe v₁ u₁ w₁

variable {Y : RingedTopos.{v₁, u₁, w₁}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [HasSheafify Y.J AddCommGrpCat.{w₁}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The class of K-flat complexes with flat terms is stable under mapping cones.**  If
`φ : K ⟶ L` is a morphism of complexes of `𝒪'`-modules whose source and target are K-flat with
flat terms, then so is its mapping cone.

K-flatness of the cone is `CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang` at the
mapping-cone triangle.  Flatness of its terms is
  `Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize`, since the degree
`i` term of the cone is `K^{i+1} ⊞ L^i` by
`HomologicalComplex.homotopyCofiber.XIsoBiprod`.

**The statement cannot be made about the abstract third vertex of a distinguished triangle.**
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` asks for flatness of the *terms*,
  and a homotopy equivalence does not
preserve that — a contractible complex with non-flat terms is isomorphic in `K(𝒪')` to the zero
complex.  So the class is closed under cones of morphisms of complexes while **not** being an
`ObjectProperty.IsTriangulatedClosed₃`, and `derivedPullback_isTriangulated` below is written
with the mapping-cone triangle of a representative rather than with an abstract cocone.

**Universes.**  The three universes of the target ringed topos are independent, matching
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` itself, so that the statement
applies at `RingedTopos.{u, u + 1, u}` — the shape of
`AlgebraicGeometry.Space.smallEtaleRingedTopos`.  Nothing in the argument sees the site: the
cone's K-flatness is a statement about a distinguished triangle in an abstract abelian
category, and the flatness of `K^{i+1} ⊞ L^i` is
`Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize`, which reads the colimit
preservation of `⊗_𝒪` off Stacks 05NB rather than off the monoidal closed structure of
`Mod(𝒪)` and so needs no relation between the module universe and the site. -/
theorem isKFlat_mappingCone
    {K L : CochainComplex (SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (φ : K ⟶ L)
    (h₁ : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (h₂ : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone φ)) := by
  refine ⟨CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang _ _ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ) h₁.1 h₂.1, fun i => ?_⟩
  have := HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
  exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize Y.O
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).symm
    (Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize Y.O _ _
      (h₁.2 (i + 1)) (h₂.2 i))

end MappingCone

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposSiteHom X Y)

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The hypothesis is satisfiable.**  Along a morphism of ringed topoi whose degreewise
pullback is exact, pullback inverts *every* quasi-isomorphism, hence in particular the ones
between K-flat complexes.  So the hypothesis carried through this file is not vacuous, and the
results below have content at every such morphism. -/
theorem pullbackInvertsQuasiIso_isKFlat_of_exact
    [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos] :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)) :=
  fun s hs _ _ ↦
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackInvertsQuasiIso_top
      f s hs trivial trivial

variable [(Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
  f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ))]

/-- **Tag 06YY, compatibility with shifts.**  The derived pullback commutes with the shift
functors of the two derived categories. -/
@[stacks 06YY "compatibility with shifts"]
noncomputable instance derivedPullback_commShift :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f).CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) ℤ

/-- The canonical comparison is compatible with `derivedPullback_commShift`. -/
instance derivedPullbackComparisonCommShift :
    NatTrans.CommShift
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f) ℤ :=
  Functor.IsLeftDerivedFunctor.natTrans_commShift
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) ℤ

variable (hinv : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f
  (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)))

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hinv in
/-- **Tag 06YY, the computation.**  The canonical comparison `Lf^* 𝒦^• ⟶ f^* 𝒦^•` is
invertible at a K-flat complex of `𝒪'`-modules with flat terms: the derived pullback of such a
complex is computed by degreewise pullback.  This is the form the source states.

The flatness of the terms enters only through the resolving class
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat`, which is K-flatness *and*
  termwise flatness. -/
theorem isIso_derivedPullbackComparison_app_of_kFlat_of_flat
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK :
      letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{w, w, w, w, w} Y.O
      @CochainComplex.KFlatBifunctor.KFlat
        (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        (Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, w, w, w} Y.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{w, w, w, w, w} Y.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{w, w, w, w, w} Y.O)
        inferInstance K)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat.{w, w, w, w} (O := Y.O) (K.X i)) :
    IsIso ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{w, w, w, w, w} Y.O
  LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y))
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy f) hinv
      DerivedCategory.Qh
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f)
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f) _
      ⟨hK, hflat⟩

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hinv in
/-- **Tag 06YY, the computation on bounded above complexes of flat modules.**  A bounded above
complex of flat `𝒪'`-modules is K-flat by Tag 06YQ, so its derived pullback is computed by
degreewise pullback. -/
theorem isIso_derivedPullbackComparison_app_of_boundedAbove_of_flat
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hbound : ∃ n : ℤ, K.IsStrictlyLE n)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat.{w, w, w, w} (O := Y.O) (K.X i)) :
    IsIso ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{w, w, w, w, w} Y.O
  isIso_derivedPullbackComparison_app_of_kFlat_of_flat f hinv K
    (Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat Y.O K hbound hflat) hflat

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hinv in
/-- **Tag 06YY, exactness.**  The derived pullback is an exact functor of triangulated
categories: every morphism of `D(𝒪')` is, up to isomorphism, the image of a morphism between
K-flat complexes, the cone of such a morphism is again K-flat by
`isKFlat_isTriangulatedClosed₃`, and the canonical comparison is invertible there. -/
theorem derivedPullback_isTriangulated :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f).IsTriangulated := by
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)
  let P : ObjectProperty (HomotopyCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)) :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism W P).HasLeftResolutions :=
    fun M => by
      obtain ⟨K, hK, s, hs⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat (Y := Y) M
      exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism W P
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι W P
  have : (P.ι ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage P.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism W P) DerivedCategory.Qh
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    (P.ι ⋙ DerivedCategory.Qh) (W.inverseImage P.ι)
  have hiso : ∀ M, P M → IsIso
      ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison
        f).app M) :=
    fun M hM => isIso_derivedPullbackComparison_app_of_kFlat_of_flat f hinv M.as hM.1 hM.2
  apply Functor.isTriangulated_of_rightExtension
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f)
  intro K L g
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (P.ι ⋙ DerivedCategory.Qh).mapArrow) (Arrow.mk g)
  exact ⟨CochainComplex.mappingCone.triangleh (P.ι.map a.hom).out,
    HomotopyCategory.mappingCone_triangleh_distinguished _, hiso _ a.left.property,
    hiso _ a.right.property,
    hiso _ (isKFlat_mappingCone (P.ι.map a.hom).out a.left.property a.right.property),
    ⟨eqToIso (congrArg (fun m => Arrow.mk (DerivedCategory.Qh.map m))
      (HomotopyCategory.quotient_map_out (P.ι.map a.hom))) ≪≫ ea⟩⟩

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A right adjoint of the derived pullback preserves boundedness below**, as soon as the
derived pullback preserves boundedness above. `D^{≥n}` is the right orthogonal of `D^{≤n-1}`,
and a morphism from an object `L` of `D^{≤n-1}` into `Rf_*K` is adjoint to a morphism
`Lf^*L ⟶ K` with `Lf^*L` again in `D^{≤n-1}`, hence zero.

The derived adjunction is produced in two ways in this development — from exactness of
degreewise pullback (`pullbackInvertsQuasiIso_isKFlat_of_exact`) and from `f` being a morphism
of sites — and the argument is the same for both, so it is stated here with the adjunction and
the boundedness-above statement as hypotheses. -/
theorem isGE_derivedPushforward_obj_of_adjunction
    [(Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f).IsTriangulated]
    (adj : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f ⊣
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward f)
    (hLE : ∀ (L : DerivedCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (m : ℤ), L.IsLE m →
      ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f).obj L).IsLE m)
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (hK : K.IsGE n) :
    ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward f).obj
      K).IsGE n := by
  show DerivedCategory.TStructure.t.IsGE
    ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward f).obj K) n
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro L g hL
  have := hLE L (n - 1) hL
  refine (adj.homEquiv L K).symm.injective
    ((DerivedCategory.TStructure.t.zero ((adj.homEquiv L K).symm g) (n - 1) n (by omega)).trans ?_)
  rw [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]

end Stacks.Sheaves.RingedToposDerivedPullback

end

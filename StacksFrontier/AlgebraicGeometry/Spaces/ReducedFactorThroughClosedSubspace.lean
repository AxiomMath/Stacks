module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Maps out of a reduced algebraic space into a closed subspace

Let `X` and `Y` be algebraic spaces over a scheme `S` and let `Z ⊆ X` be a closed subspace.
If `Y` is reduced then a morphism `f : Y ⟶ X` factors through `Z` exactly when the image of
`|Y|` in `|X|` is contained in `|Z|`. One direction is formal; the content is the converse,
which is the scheme statement that a morphism from a reduced scheme into a scheme factors
through any closed subscheme containing its image, transported along a presentation.

## Main results

* `AlgebraicGeometry.Space.exists_lift_closedSubspace_iff_pointsMap_range_subset` is
  **Stacks 03JJ**: factorization through a closed subspace is detected on points.
* `AlgebraicGeometry.Space.factorThroughSubfunctor_of_locallySurjective`: on an arbitrary
  site, a morphism into a sheaf factors through a subsheaf as soon as it does so after
  precomposition with a locally surjective morphism.

## Implementation notes

A closed subspace is a `CategoryTheory.Subfunctor` of `X`, so factoring through it means
equality with its inclusion, and the point set of the subspace inside `|X|` is the range of
the map on points induced by that inclusion.  Reducedness of `Y` is the étale-local scheme
property of Stacks 03E6, and `AlgebraicGeometry.Space.exists_atlas_iff_forall_etale` —
Stacks 03E8 — turns it into reducedness of *every* étale scheme chart of `Y`; the locality
instance it consumes is `AlgebraicGeometry.isReduced_isLocal_etale`.

The argument chooses a surjective étale chart `a : h_V ⟶ X` and lifts it along `f` by
Stacks 02X1 to a surjective étale chart `p : h_T ⟶ Y` together with `α : T ⟶ V`.  The base
change `P = Z ×_X T` of the closed subspace to that chart is representable and its projection
`j : P ⟶ T` is a closed immersion of schemes; the hypothesis on points makes `j` surjective
on points, hence surjective — Stacks 03H4 produces the required point of the fibre product and
Stacks 03H5 converts point surjectivity back into surjectivity of the morphism.  A surjective
closed immersion of schemes with reduced target is an isomorphism, which is where reducedness
is used, so `h_T ⟶ X` factors through `Z`.  Finally `p` is locally surjective for the fppf
topology by Stacks 05VM, and `Z` is a subsheaf of the sheaf `X`, so the factorization descends
from the chart to `Y`; that last step is `factorThroughSubfunctor_of_locallySurjective`, which
is stated for an arbitrary site.

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A morphism into a sheaf factors through a subsheaf as soon as it does so after
precomposition with a locally surjective morphism: the sieve of sections of the subfunctor at
a section of the target contains the image sieve of the locally surjective map, hence
covers. -/
theorem factorThroughSubfunctor_of_locallySurjective {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G H : Cᵒᵖ ⥤ Type u} (Z : Subfunctor F) (f : G ⟶ F)
    (p : H ⟶ G) (hp : Presheaf.IsLocallySurjective J p) (hF : Presieve.IsSheaf J F)
    (hZ : Presieve.IsSheaf J Z.toFunctor) (g : H ⟶ Z.toFunctor) (hg : g ≫ Z.ι = p ≫ f) :
    ∃ g' : G ⟶ Z.toFunctor, g' ≫ Z.ι = f := by
  have hmem (U : Cᵒᵖ) (x : G.obj U) : f.app U x ∈ Z.obj U := by
    have hc : Z.sieveOfSection (f.app U x) ∈ J U.unop := by
      apply J.superset_covering _ (hp.imageSieve_mem x)
      rintro V a ⟨y, hy⟩
      show F.map a.op (f.app U x) ∈ Z.obj (Opposite.op V)
      have hcomp : Z.ι.app (Opposite.op V) (g.app (Opposite.op V) y) =
          f.app (Opposite.op V) (p.app (Opposite.op V) y) := by
        simpa using congrArg (fun k : H ⟶ F => k.app (Opposite.op V) y) hg
      rw [← NatTrans.naturality_apply f a.op x, ← hy, ← hcomp]
      exact (g.app (Opposite.op V) y).property
    exact (Z.isSheaf_iff hF).1 hZ U (f.app U x) hc
  let g' : G ⟶ Z.toFunctor :=
    { app U := ↾fun x => ⟨f.app U x, hmem U x⟩
      naturality U V a := by
        ext x
        apply Subtype.ext
        exact NatTrans.naturality_apply f a x }
  refine ⟨g', ?_⟩
  ext U x
  rfl

/-- **Stacks 03JJ.** A morphism from a reduced algebraic space factors through a closed
subspace if and only if its image on underlying points lies in that closed subspace. -/
@[stacks 03JJ]
theorem exists_lift_closedSubspace_iff_pointsMap_range_subset (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z)
    (hred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z.toFunctor, g ≫ Z.ι = f) ↔
      Set.range (pointsMap B S hS Y f) ⊆ Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
  constructor
  · rintro ⟨g, hg⟩ _ ⟨y, rfl⟩
    exact ⟨pointsMap B S hS Y g y, (congrFun (pointsMap_comp B S hS Y g Z.ι) y).symm.trans
      (congrArg (fun k : Y ⟶ X => pointsMap B S hS Y k y) hg)⟩
  · intro h
    classical
    let J := BigFppfOver.topology B S hS
    have hredAll :=
      (exists_atlas_iff_forall_etale B S hS Y (fun T : Scheme.{u} => IsReduced T) hY).1 hred
    obtain ⟨V, a, haSurj, haEtale⟩ := hX.exists_atlas
    obtain ⟨T, p, α, hpα, hpSurj, hpEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS hY hX f V a haSurj haEtale
    have : IsReduced ((BigFppfOver.toScheme B S hS).obj T) := hredAll T p hpEtale
    let q : yoneda.obj T ⟶ X := yoneda.map α ≫ a
    have hpq : p ≫ f = q := hpα
    obtain ⟨P, j, i, hij⟩ := hZ.2.1 q
    have hjClosed :
        (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
          (BigFppfOver.toScheme B S hS)) j := hZ.2.2 q i j hij
    have hsurjPoints :
        Function.Surjective (pointsMap B S hS (yoneda.obj P) (yoneda.map j)) := by
      intro x
      have hxY : pointsMap B S hS (yoneda.obj T) q x ∈
          Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
        refine h ⟨pointsMap B S hS (yoneda.obj T) p x, ?_⟩
        simpa [q, hpq] using (congrFun (pointsMap_comp B S hS (yoneda.obj T) p f) x).symm
      obtain ⟨z, hz⟩ := hxY
      let Z' : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZ.1⟩
      let T' : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
      let P' : AlgebraicSpaces B S hS := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩
      let zi : Z' ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS) := ObjectProperty.homMk Z.ι
      let qt : T' ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS) := ObjectProperty.homMk q
      let pi : P' ⟶ Z' := ObjectProperty.homMk i
      let pj : P' ⟶ T' := ObjectProperty.homMk (yoneda.map j)
      have hsq : IsPullback pi pj zi qt :=
        IsPullback.of_map_of_faithful
          (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
            IsAlgebraicSpace B S hS F)) hij
      obtain ⟨w, -, hw₂⟩ :=
        exists_point_of_isPullback B S hS hsq z x (by simpa [zi, qt] using hz)
      exact ⟨w, by simpa [pj] using hw₂⟩
    have hsurjPresheaf :=
      (surjective_iff_surjective_pointsMap B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T) P (yoneda.map j)).2 hsurjPoints
    have hsqId : IsPullback (𝟙 (yoneda.obj P)) (yoneda.map j) (yoneda.map j)
        (𝟙 (yoneda.obj T)) := IsPullback.of_id_fst
    have hjSurj : Surjective ((BigFppfOver.toScheme B S hS).map j) :=
      hsurjPresheaf.property (𝟙 (yoneda.obj T)) (𝟙 (yoneda.obj P)) j hsqId
    have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j) := hjClosed
    have hjIso : IsIso ((BigFppfOver.toScheme B S hS).map j) := by
      rw [IsClosedImmersion.isIso_iff_ker_eq_bot,
        ← Scheme.IdealSheafData.support_eq_top_iff,
        ← SetLike.coe_injective.eq_iff, Scheme.Hom.support_ker]
      have hmaprange : Set.range (Over.Hom.left j).hom = Set.univ :=
        Set.range_eq_univ.mpr (by simpa using hjSurj.surj)
      simp [hmaprange]
    have : IsIso j := (isIso_iff_of_reflects_iso j (BigFppfOver.toScheme B S hS)).mp hjIso
    have hg : (yoneda.map (inv j) ≫ i) ≫ Z.ι = q := by
      rw [Category.assoc, hij.w]
      simp
    have hpLocal : Presheaf.IsLocallySurjective J p := by
      have hpFppf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
          ((fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f) :
            MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) p := by
        refine ⟨hpEtale.1, ?_⟩
        intro A C k b c hbc
        have : Etale ((BigFppfOver.toScheme B S hS).map c) := hpEtale.2 k b c hbc
        exact ⟨inferInstance, inferInstance, hpSurj.2 k b c hbc⟩
      let psh : (⟨yoneda.obj T, (isAlgebraicSpace_yoneda B S hS T).isSheaf⟩ :
        Sheaf J (Type u)) ⟶ ⟨Y, hY.isSheaf⟩ := ⟨p⟩
      show Presheaf.IsLocallySurjective J psh.hom
      exact isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
        B S hS psh hpFppf
    exact factorThroughSubfunctor_of_locallySurjective Z f p hpLocal
      ((isSheaf_iff_isSheaf_of_type J X).1 hX.isSheaf)
      ((isSheaf_iff_isSheaf_of_type J Z.toFunctor).1 hZ.1.isSheaf)
      (yoneda.map (inv j) ≫ i) (by rw [hg, hpq])

end AlgebraicGeometry.Space

end

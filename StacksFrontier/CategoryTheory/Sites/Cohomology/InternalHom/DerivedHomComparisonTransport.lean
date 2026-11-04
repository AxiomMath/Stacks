module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects

/-!
# Transporting the derived internal Hom comparison along a map into a K-injective complex

Let `X` be a ringed site. The derived internal Hom `RSheafHom(Q N, Q C)` of the classes of two
complexes of `O`-modules is identified with the class of an ordinary internal Hom complex in two
ways. For an arbitrary target `C` it is the class of `SheafHom(N, I(C))`, where `I(C)` is the
chosen functorial K-injective resolution; that identification is
`derivedSheafHomResolutionComparison`. For a K-injective target `J` it is the class of
`SheafHom(N, J)` itself; that identification is `derivedSheafHomComparison`.

This file relates the two along an arbitrary morphism `q : C ⟶ J` with `J` K-injective: the
composite that goes from `SheafHom(N, I(C))` back to `RSheafHom(Q N, Q C)`, across `q`, and then
down to `SheafHom(N, J)`, is the map `SheafHom(N, q)` induced by `q`, once it is entered through
the augmentation `C ⟶ I(C)`.

The point of recording this is that it needs **no** homotopy-theoretic input. One might expect
to need that `SheafHom(N, ·)` carries chain homotopies to chain homotopies — which is not in the
library — because the two morphisms being compared have equal classes in `D(O)` without being
equal. They are not compared directly: the naturality square of the augmentation
`𝟭 ⟹ kInjectiveResolution` at `q` is a *strict* equality of morphisms of complexes,
`aug_C ≫ I(q) = q ≫ aug_J`, and applying the functoriality `homMap_comp` of the internal Hom
complex to that equality is enough. So the only inputs are that naturality, `homMap_comp`, and
the naturality of `derivedSheafHomResolutionComparison`, none of which sees a homotopy.

## Main results

* `AlgebraicGeometry.RingedSite.Q_map_homMap_augmentation_comp_comparison`: the composite
  described above is `SheafHom(N, q)`.
* `AlgebraicGeometry.RingedSite.Q_map_homMap_congr_of_isKInjective`: consequently `SheafHom(N, q)`
  depends on `q` only through its class in `D(O)`, for a K-injective target.
* `AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso_comparison_naturality_right`:
  the identification of `RSheafHom(M, L)` with the class of `SheafHom(N, I)`, for a K-injective
  `I` representing `L`, is natural in that representative.
* `AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso_comparison_naturality_source`:
  the same identification is natural in the representative `N` of `M`, contravariantly. No
  K-injectivity is needed of `N`, the source of an internal Hom being unconstrained.
* `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor_map_op_comp`: the bookkeeping
  underlying it, that two representing isomorphisms compared by a morphism of complexes induce
  the same map in the contravariant slot.

## Implementation notes

Neither statement asks `q` to be a quasi-isomorphism. That hypothesis is what makes the
transport an isomorphism, and it is imposed by the consumers rather than here, because the
equality of morphisms holds without it.

`derivedSheafHomComparison` is by definition the resolution comparison followed by the inverse
of the augmentation-induced map at the K-injective target, so the proof begins by unfolding it
with `dsimp only`; the `IsIso` instance for that augmentation-induced map at a K-injective target
is `isIso_Q_map_homMap_kInjectiveAugmentation`.

## References

* [Stacks Project, Lemma 20.49.5 (Tag 0A97)](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Lemma 20.47.5 (Tag 0A90)](https://stacks.math.columbia.edu/tag/0A90)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **Entering the derived internal Hom through the augmentation and leaving it through a map
into a K-injective complex gives the induced map of internal Hom complexes.** The augmentation
`C ⟶ I(C)` induces the first map, the resolution comparison identifies `SheafHom(N, I(C))` with
`RSheafHom(Q N, Q C)`, the morphism `q` moves the target, and the K-injective comparison lands in
`SheafHom(N, J)`; the composite is the map induced by `q`. -/
theorem Q_map_homMap_augmentation_comp_comparison
    (N C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : C ⟶ J) :
    DerivedCategory.Q.map (homMap X (𝟙 N) ((kInjectiveAugmentation X).app C)) ≫
        (derivedSheafHomResolutionComparison X N C).inv ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj N))).map
          (DerivedCategory.Q.map q) ≫
        (derivedSheafHomComparison X N J).hom =
      DerivedCategory.Q.map (homMap X (𝟙 N) q) := by
  have hnat := derivedSheafHomResolutionComparison_naturality X (𝟙 N) q
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hnat
  have hnat' : (derivedSheafHomResolutionComparison X N C).inv ≫
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj N))).map
        (DerivedCategory.Q.map q) ≫
      (derivedSheafHomResolutionComparison X N J).hom =
        DerivedCategory.Q.map
          (homMap X (𝟙 N) ((kInjectiveResolution X).map q)) := by
    rw [hnat, Iso.inv_hom_id_assoc]
  have haug : (kInjectiveAugmentation X).app C ≫ (kInjectiveResolution X).map q =
      q ≫ (kInjectiveAugmentation X).app J := by
    simpa using ((kInjectiveAugmentation X).naturality q).symm
  dsimp only [derivedSheafHomComparison, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [← cancel_mono (DerivedCategory.Q.map
    (homMap X (𝟙 N) ((kInjectiveAugmentation X).app J)))]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hnat', ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    homMap_comp, homMap_comp, Category.id_comp, haug]

/-- The forward map of `derivedSheafHomObjectsModelIso`, as a composite of two whiskered maps. -/
private theorem derivedSheafHomObjectsModelIso_hom_eq
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) (eI : DerivedCategory.Q.obj I ≅ M) :
    (derivedSheafHomObjectsModelIso X eA eI).hom =
      ((derivedSheafHomBifunctor X).map eA.op.hom).app M ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map eI.inv := rfl

/-- **The K-injective model identification of `RSheafHom(M, L)` is natural in the representative
of `L`.** If `i : I ⟶ I'` is a morphism of K-injective complexes representing `L` compatibly
with the two representing isomorphisms, then it intertwines the two identifications. -/
theorem derivedSheafHomObjectsModelIso_comparison_naturality_right
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {I I' N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L) (eI' : DerivedCategory.Q.obj I' ≅ L)
    (eN : DerivedCategory.Q.obj N ≅ M) (i : I ⟶ I')
    (hi : DerivedCategory.Q.map i = eI.hom ≫ eI'.inv) :
    (derivedSheafHomObjectsModelIso X eN eI).hom ≫
        (derivedSheafHomComparison X N I).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 N) i) =
      (derivedSheafHomObjectsModelIso X eN eI').hom ≫
        (derivedSheafHomComparison X N I').hom := by
  simp only [derivedSheafHomObjectsModelIso_hom_eq, Category.assoc]
  rw [← derivedSheafHomComparison_naturality_id_source X N i,
    ← CategoryTheory.Functor.map_comp_assoc, hi, Iso.inv_hom_id_assoc]

/-- **The map of internal Hom complexes induced by a morphism into a K-injective complex
depends on that morphism only through its class in `D(O)`.** This is an immediate consequence of
`Q_map_homMap_augmentation_comp_comparison`, whose right-hand side is the induced map while its
left-hand side mentions the morphism only as `Q q`. No K-injectivity is needed of the source. -/
theorem Q_map_homMap_congr_of_isKInjective
    (N C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    {q q' : C ⟶ J} (h : DerivedCategory.Q.map q = DerivedCategory.Q.map q') :
    DerivedCategory.Q.map (homMap X (𝟙 N) q) =
      DerivedCategory.Q.map (homMap X (𝟙 N) q') := by
  rw [← Q_map_homMap_augmentation_comp_comparison X N C q,
    ← Q_map_homMap_augmentation_comp_comparison X N C q', h]

/-- Two representing isomorphisms of the same object of `D(O)`, compared by a morphism of
complexes, induce the same map of derived internal Hom functors in the contravariant slot. -/
theorem derivedSheafHomBifunctor_map_op_comp
    {M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {N N₁ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ M) (eN₁ : DerivedCategory.Q.obj N₁ ≅ M) (n : N₁ ⟶ N)
    (hn : DerivedCategory.Q.map n = eN₁.hom ≫ eN.inv)
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).map eN.op.hom).app Z ≫
        ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map n).op).app Z =
      ((derivedSheafHomBifunctor X).map eN₁.op.hom).app Z := by
  rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp]
  congr 2
  rw [Iso.op_hom, Iso.op_hom, ← op_comp, hn, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **The K-injective model identification of `RSheafHom(M, L)` is natural in the representative
of `M`.** This is the contravariant counterpart of
`derivedSheafHomObjectsModelIso_comparison_naturality_right`: the source of the internal Hom
needs no K-injectivity, so `N` and `N₁` are arbitrary. -/
theorem derivedSheafHomObjectsModelIso_comparison_naturality_source
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {I N N₁ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L) (eN : DerivedCategory.Q.obj N ≅ M)
    (eN₁ : DerivedCategory.Q.obj N₁ ≅ M) (n : N₁ ⟶ N)
    (hn : DerivedCategory.Q.map n = eN₁.hom ≫ eN.inv) :
    (derivedSheafHomObjectsModelIso X eN eI).hom ≫
        (derivedSheafHomComparison X N I).hom ≫
        DerivedCategory.Q.map (homMap X n (𝟙 I)) =
      (derivedSheafHomObjectsModelIso X eN₁ eI).hom ≫
        (derivedSheafHomComparison X N₁ I).hom := by
  simp only [derivedSheafHomObjectsModelIso_hom_eq, Category.assoc]
  rw [← derivedSheafHomComparison_naturality_id_target X I n, ← NatTrans.naturality_assoc]
  rw [reassoc_of% (derivedSheafHomBifunctor_map_op_comp X eN eN₁ n hn
      (DerivedCategory.Q.obj I)), NatTrans.naturality_assoc]

end AlgebraicGeometry.RingedSite

end

module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardRestrictMate

/-!
# The derived comparison of iterated pullbacks is the derived image of the underived one

Let

```
  U --- i ---> X
  |            |
  g            f
  |            |
  V --- j ---> Y
```

be a commutative square of ringed spaces, `w : i ≫ f = g ≫ j`.  Two comparisons of iterated
pullbacks sit over it.  Underived, `Stacks.Cohomology.pullbackCompSquare` compares `j^* ⋙ g^*`
with `f^* ⋙ i^*`, both identified with pullback along the common composite by the composition
isomorphism of [Stacks, Tag 0096].  Derived,
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare` compares `Lj^* ⋙ Lg^*` with
`Lf^* ⋙ Li^*`, both identified with the derived pullback along the common composite by the
composition formula of [Stacks, Tag 0D5S].  The derived base change map of [Stacks, Tag 08HY] is
the mate of the second, as `Stacks.Cohomology.pushforwardRestrictMap_eq_mateEquiv` exhibits the
underived base change as the mate of the first.

Suppose pullback along each of the four morphisms is exact — for the inclusion of a closed
subset this is unconditional, by
`Stacks.Cohomology.SupportedComplexes.preservesFiniteLimits_modulePullback_closedSubsetInclusion`.
Then `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory` identifies
each `L?^*` with the functor `D(?^*)` induced degreewise, and the main result of this file says
that under those four identifications the derived comparison *is* the derived image of the
underived one.  Both sides are maps out of a left derived functor of degreewise pullback along
the common composite, so no computation at a complex is needed: the three universal properties
already in the development pin down the three pieces, and what is left is a diagram chase among
ten objects of a category.

The derived image of a square is built here in two steps at an arbitrary abelian category.  An
isomorphism `F ⋙ G ≅ H` of exact functors induces `D(F) ⋙ D(G) ≅ D(H)`
(`Stacks.Homology.mapDerivedCategoryCompIso`, from
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality`),
and an isomorphism `H ≅ H'` induces `D(H) ≅ D(H')`
(`Stacks.Homology.mapDerivedCategoryIsoOfIso`).  Reading an invertible 2-square `T ⋙ R ≅ L ⋙ Bo`
through the first at both composites and the second in between gives
`Stacks.Homology.mapDerivedCategoryTwoSquareOfIso`.

## Main definitions

* `Stacks.Homology.mapDerivedCategoryTwoSquareOfIso`: the image on derived categories of a
  2-square of exact functors whose transformation is invertible.
* `Stacks.Cohomology.pullbackCompIso`: the underived comparison of the two iterated pullbacks
  around the square, as an isomorphism; its `hom` is the transformation of
  `Stacks.Cohomology.pullbackCompSquare`.
* `Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare`: the derived image of that
  comparison.

## Main results

* `Stacks.Homology.mapDerivedCategoryCompIso_trans` and
  `Stacks.Homology.mapDerivedCategoryIsoOfIso_refl`: the two coherences of the induced-functor
  comparisons that make the derived image of a square computable — transporting
  `D(F) ⋙ D(G) ≅ D(H)` along an isomorphism of `H` composes with the induced map, and at an
  identity isomorphism the induced map is the identity.  Both are proved from the universal
  property of the left derived functor, not at a complex.
* `Stacks.Homology.mapDerivedCategoryTwoSquareOfIso_natTrans`: the derived image of a 2-square,
  read through a common identification of the two composites with exact functors.
* `Stacks.Cohomology.modulePullbackComp_eq_symm`: the two pullback-composition isomorphisms of
  the development, `RingedSpaceModuleAdjunction.modulePullbackComp` and
  `Stacks.DerivedPullback.Composition.modulePullbackComp`, are inverse to each other.
* `Stacks.Cohomology.derivedPullbackIsoMapDerivedCategory_eqToHom`: the identification
  `Lf^* ≅ D(f^*)` is compatible with transport along an equality of morphisms.  This is what
  absorbs the `eqToIso` that the commutativity of the square puts inside
  `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`.
* `Stacks.Cohomology.derivedPullbackSquare_eq_mapDerivedCategory`: **the main result.**  For a
  square of ringed spaces with exact pullbacks, the derived comparison
  `Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare` of [Stacks, Tag 08HY] is, under the
  four identifications `L?^* ≅ D(?^*)`, the derived image
  `Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare` of the underived comparison
  `Stacks.Cohomology.pullbackCompSquare`.

## References

* [Stacks Project, Remark 20.28.3 (Tag 08HY)](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Section 17.6 (Tag 0096)](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.Homology

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] in
/-- Transporting the degreewise comparison of two composable additive functors along an
isomorphism of the target is composing with the induced map on homotopy categories. -/
theorem mapHomotopyCategoryCompIso_trans (F : A ⥤ B) (G : B ⥤ C) (H H' : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] [H'.Additive]
    (e : F ⋙ G ≅ H) (u : H ≅ H') :
    (Functor.mapHomotopyCategoryCompIso (e ≪≫ u) (ComplexShape.up ℤ)).hom =
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory u.hom (ComplexShape.up ℤ) := by
  ext ⟨K⟩
  simp only [Functor.mapHomotopyCategoryCompIso, Functor.mapHomologicalComplexCompIso]
  rfl

/-- Transporting the structure map of `D(F) ⋙ D(G)` along an isomorphism of the target. -/
theorem mapDerivedCategoryCompComparison_trans (F : A ⥤ B) (G : B ⥤ C) (H H' : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] [H'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ⋙ G ≅ H) (u : H ≅ H') :
    (mapDerivedCategoryCompComparison F G H' (e ≪≫ u)).hom =
      (mapDerivedCategoryCompComparison F G H e).hom ≫
        Functor.whiskerRight (NatTrans.mapHomotopyCategory u.hom (ComplexShape.up ℤ))
          DerivedCategory.Qh := by
  simp only [mapDerivedCategoryCompComparison, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    mapHomotopyCategoryCompIso_trans F G H H' e u, Functor.whiskerRight_comp, Category.assoc]

/-- **The universal property of `Stacks.Homology.mapDerivedCategoryIsoOfIso` with the twist moved
to the other side**: composing with the structure map of the target is the structure map of the
source followed by the degreewise comparison on homotopy categories. -/
theorem whiskerLeft_mapDerivedCategoryIsoOfIso_hom (H H' : A ⥤ C) [H.Additive] [H'.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H'] (u : H ≅ H') :
    Functor.whiskerLeft DerivedCategory.Qh (mapDerivedCategoryIsoOfIso H H' u).hom ≫
        H'.mapDerivedCategoryFactorsh.hom =
      H.mapDerivedCategoryFactorsh.hom ≫
        Functor.whiskerRight (NatTrans.mapHomotopyCategory u.hom (ComplexShape.up ℤ))
          DerivedCategory.Qh := by
  have hu : Functor.whiskerLeft DerivedCategory.Qh (mapDerivedCategoryIsoOfIso H H' u).hom ≫
      (mapDerivedCategoryComparisonOfIso H H' u).hom = H.mapDerivedCategoryFactorsh.hom :=
    whiskerLeft_leftDerivedIsoMapDerivedCategoryOfIso_hom H H' H.mapDerivedCategory
      H.mapDerivedCategoryFactorsh.hom u
  rw [mapDerivedCategoryComparisonOfIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    show (mapHomotopyCategoryIso u.symm (ComplexShape.up ℤ)).hom =
      NatTrans.mapHomotopyCategory u.inv (ComplexShape.up ℤ) from rfl] at hu
  have key : Functor.whiskerRight
        (NatTrans.mapHomotopyCategory u.inv (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
      Functor.whiskerRight
        (NatTrans.mapHomotopyCategory u.hom (ComplexShape.up ℤ)) DerivedCategory.Qh = 𝟙 _ := by
    rw [← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp, u.inv_hom_id,
      NatTrans.mapHomotopyCategory_id]
    simp
  rw [← hu, Category.assoc, Category.assoc, key, Category.comp_id]

/-- **The comparison `D(F) ⋙ D(G) ≅ D(H)` is transported along an isomorphism of `H`** by the
isomorphism of induced functors that isomorphism gives.  Both sides are maps of left derived
functors of `K(H') ⋙ Q_h`, so it suffices to compare their composites with the structure map of
the target. -/
theorem mapDerivedCategoryCompIso_trans (F : A ⥤ B) (G : B ⥤ C) (H H' : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] [H'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (e : F ⋙ G ≅ H) (u : H ≅ H') :
    mapDerivedCategoryCompIso F G H' (e ≪≫ u) =
      mapDerivedCategoryCompIso F G H e ≪≫ mapDerivedCategoryIsoOfIso H H' u := by
  refine Iso.ext (Functor.leftDerived_ext H'.mapDerivedCategory
    H'.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_)
  have hL := whiskerLeft_mapDerivedCategoryCompIso_hom F G H' (e ≪≫ u)
  have hR := whiskerLeft_mapDerivedCategoryCompIso_hom F G H e
  rw [hL, Iso.trans_hom, Functor.whiskerLeft_comp, Category.assoc,
    whiskerLeft_mapDerivedCategoryIsoOfIso_hom, ← Category.assoc, hR,
    mapDerivedCategoryCompComparison_trans]

/-- **At the identity isomorphism the comparison of induced functors is the identity.**  Both
`Stacks.Homology.leftDerivedIsoMapDerivedCategory` of `D(F)` against its own structure map and
`Stacks.Homology.mapDerivedCategoryIsoOfIso` at `Iso.refl F` are the same isomorphism, so
`Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_eq` reads `X = X ≪≫ X`. -/
theorem mapDerivedCategoryIsoOfIso_refl (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    mapDerivedCategoryIsoOfIso F F (Iso.refl F) = Iso.refl F.mapDerivedCategory := by
  have h : mapDerivedCategoryIsoOfIso F F (Iso.refl F) =
      mapDerivedCategoryIsoOfIso F F (Iso.refl F) ≪≫
        mapDerivedCategoryIsoOfIso F F (Iso.refl F) :=
    leftDerivedIsoMapDerivedCategoryOfIso_eq F F F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh.hom (Iso.refl F)
  have h2 := congrArg Iso.hom h
  rw [Iso.trans_hom] at h2
  refine Iso.ext ?_
  have h3 : (mapDerivedCategoryIsoOfIso F F (Iso.refl F)).hom ≫ 𝟙 _ =
      (mapDerivedCategoryIsoOfIso F F (Iso.refl F)).hom ≫
        (mapDerivedCategoryIsoOfIso F F (Iso.refl F)).hom := by
    rw [Category.comp_id]; exact h2
  exact ((cancel_epi (mapDerivedCategoryIsoOfIso F F (Iso.refl F)).hom).mp h3).symm

section TwoSquare

universe w₄ v₄ u₄

variable {E : Type u₄} [Category.{v₄} E] [Abelian E] [HasDerivedCategory.{w₄} E]
  (T : A ⥤ B) (L : A ⥤ C) (R : B ⥤ E) (Bo : C ⥤ E)
  [T.Additive] [L.Additive] [R.Additive] [Bo.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits Bo] [PreservesFiniteColimits Bo]

/-- **The image on derived categories of a 2-square of exact functors whose transformation is
invertible.**  The two composites `T ⋙ R` and `L ⋙ Bo` induce functors on derived categories
canonically identified with `D(T) ⋙ D(R)` and `D(L) ⋙ D(Bo)` by
`Stacks.Homology.mapDerivedCategoryCompIso`, and in between sits the isomorphism of induced
functors that `α` gives, by `Stacks.Homology.mapDerivedCategoryIsoOfIso`. -/
def mapDerivedCategoryTwoSquareOfIso (α : T ⋙ R ≅ L ⋙ Bo) :
    TwoSquare T.mapDerivedCategory L.mapDerivedCategory R.mapDerivedCategory
      Bo.mapDerivedCategory :=
  TwoSquare.mk _ _ _ _
    ((mapDerivedCategoryCompIso T R (T ⋙ R) (Iso.refl _)).hom ≫
      (mapDerivedCategoryIsoOfIso (T ⋙ R) (L ⋙ Bo) α).hom ≫
      (mapDerivedCategoryCompIso L Bo (L ⋙ Bo) (Iso.refl _)).inv)

/-- **The derived image of a 2-square read through a common identification of the two
composites.**  If both composites are identified with exact functors `H₁` and `H₂` and `α` is the
resulting comparison, then the derived image of `α` is the comparison of `D(T) ⋙ D(R)` with
`D(H₁)`, the image of `t` and the comparison of `D(H₂)` with `D(L) ⋙ D(Bo)`. -/
theorem mapDerivedCategoryTwoSquareOfIso_natTrans (H₁ H₂ : A ⥤ E)
    [H₁.Additive] [H₂.Additive]
    [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
    [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]
    (eT : T ⋙ R ≅ H₁) (eL : L ⋙ Bo ≅ H₂) (t : H₁ ≅ H₂) :
    (mapDerivedCategoryTwoSquareOfIso T L R Bo (eT ≪≫ t ≪≫ eL.symm)) =
      (mapDerivedCategoryCompIso T R H₁ eT).hom ≫
        (mapDerivedCategoryIsoOfIso H₁ H₂ t).hom ≫
          (mapDerivedCategoryCompIso L Bo H₂ eL).inv := by
  have s1 := mapDerivedCategoryCompIso_trans T R (T ⋙ R) (L ⋙ Bo) (Iso.refl _)
    (eT ≪≫ t ≪≫ eL.symm)
  rw [Iso.refl_trans] at s1
  have s2 := mapDerivedCategoryCompIso_trans T R H₂ (L ⋙ Bo) (eT ≪≫ t) eL.symm
  rw [Iso.trans_assoc] at s2
  have s3 := mapDerivedCategoryCompIso_trans T R H₁ H₂ eT t
  have s4 := mapDerivedCategoryCompIso_trans L Bo H₂ (L ⋙ Bo) eL eL.symm
  rw [Iso.self_symm_id] at s4
  have s1h : (mapDerivedCategoryCompIso T R (T ⋙ R) (Iso.refl _)).hom ≫
        (mapDerivedCategoryIsoOfIso (T ⋙ R) (L ⋙ Bo) (eT ≪≫ t ≪≫ eL.symm)).hom =
      (mapDerivedCategoryCompIso T R (L ⋙ Bo) (eT ≪≫ t ≪≫ eL.symm)).hom := by
    rw [s1, Iso.trans_hom]
  have s2h : (mapDerivedCategoryCompIso T R (L ⋙ Bo) (eT ≪≫ t ≪≫ eL.symm)).hom =
      (mapDerivedCategoryCompIso T R H₁ eT).hom ≫
        (mapDerivedCategoryIsoOfIso H₁ H₂ t).hom ≫
          (mapDerivedCategoryIsoOfIso H₂ (L ⋙ Bo) eL.symm).hom := by
    rw [s2, s3, Iso.trans_hom, Iso.trans_hom, Category.assoc]
  have s4h : (mapDerivedCategoryCompIso L Bo (L ⋙ Bo) (Iso.refl _)).inv =
      (mapDerivedCategoryIsoOfIso H₂ (L ⋙ Bo) eL.symm).inv ≫
        (mapDerivedCategoryCompIso L Bo H₂ eL).inv := by
    rw [s4, Iso.trans_inv]
  dsimp only [mapDerivedCategoryTwoSquareOfIso, TwoSquare.mk]
  rw [← Category.assoc, s1h, s2h, s4h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end TwoSquare

end Stacks.Homology

namespace Stacks.Cohomology

universe u

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard

/-! ### The two spellings of the pullback composition isomorphism -/

/-- **The two pullback-composition isomorphisms of the development are inverse to each other.**
`RingedSpaceModuleAdjunction.modulePullbackComp` reads `(f ≫ g)^* ≅ g^* ⋙ f^*` and
`Stacks.DerivedPullback.Composition.modulePullbackComp` reads `g^* ⋙ f^* ≅ (f ≫ g)^*`; both are
produced from the pushforward-composition isomorphism by uniqueness of left adjoints, so their
conjugates under `CategoryTheory.conjugateEquiv` agree and the bijection does the rest. -/
theorem modulePullbackComp_eq_symm {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingedSpaceModuleAdjunction.modulePullbackComp f g =
      (Stacks.DerivedPullback.Composition.modulePullbackComp f g).symm := by
  have h2 : conjugateEquiv ((modulePullbackPushforwardAdjunction g).comp
        (modulePullbackPushforwardAdjunction f)) (modulePullbackPushforwardAdjunction (f ≫ g))
      (Stacks.DerivedPullback.Composition.modulePullbackComp f g).inv =
      (modulePushforwardComp f g).hom := by
    rw [Stacks.DerivedPullback.Composition.modulePullbackComp]
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  exact Iso.ext ((conjugateEquiv _ _).injective
    ((RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom f g).trans h2.symm))

/-! ### Exactness of pullback along a composite

Pullback along a composite of morphisms of ringed spaces with exact pullbacks is exact; this is
`Stacks.DerivedPullback.Composition.preservesFiniteLimits_modulePullback_comp` and its colimit
counterpart, which are made local instances so that the pullback along the common composite of
the square is seen to be exact. -/

attribute [local instance]
  Stacks.DerivedPullback.Composition.preservesFiniteLimits_modulePullback_comp
  Stacks.DerivedPullback.Composition.preservesFiniteColimits_modulePullback_comp

/-! ### The comparison of iterated pullbacks as an isomorphism -/

variable {X Y U V : RingedSpace.{u, u}} (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)

/-- **The comparison of the two iterated pullbacks around a commutative square of ringed spaces
is an isomorphism**, `j^* ⋙ g^* ≅ f^* ⋙ i^*`: it is a composite of the two pullback-composition
isomorphisms of [Stacks, Tag 0096] and the transport along the commutativity of the square. -/
def pullbackCompIso (w : i ≫ f = g ≫ j) :
    modulePullback j ⋙ modulePullback g ≅ modulePullback f ⋙ modulePullback i :=
  (RingedSpaceModuleAdjunction.modulePullbackComp g j).symm ≪≫
    eqToIso (congrArg modulePullback w.symm) ≪≫
    RingedSpaceModuleAdjunction.modulePullbackComp i f

/-- `Stacks.Cohomology.pullbackCompIso` is the transformation of
`Stacks.Cohomology.pullbackCompSquare`. -/
theorem pullbackCompIso_hom (w : i ≫ f = g ≫ j) :
    (pullbackCompIso f i j g w).hom = (pullbackCompSquare f i j g w) :=
  rfl

/-- `Stacks.Cohomology.pullbackCompIso` written in the orientation of
`Stacks.DerivedPullback.Composition.modulePullbackComp`, which is the one the derived
composition isomorphism of Tag 0D5S is stated in. -/
theorem pullbackCompIso_eq (w : i ≫ f = g ≫ j) :
    pullbackCompIso f i j g w =
      Stacks.DerivedPullback.Composition.modulePullbackComp g j ≪≫
        eqToIso (congrArg modulePullback w.symm) ≪≫
          (Stacks.DerivedPullback.Composition.modulePullbackComp i f).symm := by
  rw [pullbackCompIso, modulePullbackComp_eq_symm g j, modulePullbackComp_eq_symm i f,
    Iso.symm_symm_eq]

/-! ### The transport along an equality of morphisms -/

/-- **The identification of the derived pullback with the degreewise pullback is compatible with
transport along an equality of morphisms of ringed spaces.**  Both transports become identities
once the two morphisms are identified, and the degreewise one is then
`Stacks.Homology.mapDerivedCategoryIsoOfIso` at an identity isomorphism. -/
theorem derivedPullbackIsoMapDerivedCategory_eqToHom {a b : U ⟶ Y} (h : a = b)
    [PreservesFiniteLimits (modulePullback a)] [PreservesFiniteColimits (modulePullback a)]
    [PreservesFiniteLimits (modulePullback b)] [PreservesFiniteColimits (modulePullback b)] :
    eqToHom (congrArg (fun q : U ⟶ Y => derivedPullback q) h) ≫
        (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory b).hom =
      (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory a).hom ≫
        (Stacks.Homology.mapDerivedCategoryIsoOfIso (modulePullback a) (modulePullback b)
          (eqToIso (congrArg modulePullback h))).hom := by
  subst h
  rw [show eqToIso (congrArg modulePullback (rfl : a = a)) = Iso.refl (modulePullback a) from rfl,
    Stacks.Homology.mapDerivedCategoryIsoOfIso_refl]
  rw [show eqToHom (congrArg (fun q : U ⟶ Y => derivedPullback q) (rfl : a = a)) =
    𝟙 (derivedPullback a) from rfl]
  rw [Category.id_comp, Iso.refl_hom, Category.comp_id]

/-! ### The derived base change square is the degreewise one -/

/-- The formal identity left over after the three universal properties are inserted.  Stated for
morphisms in an arbitrary category, with the objects implicit: the rewriting is then done in a
context that mentions no derived category, which is what keeps it inside the heartbeat budget. -/
private theorem square_chase {D : Type*} [Category D]
    {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ : D}
    (A : o₁ ⟶ o₂) (TL : o₂ ⟶ o₃) (Bh : o₄ ⟶ o₃) (Bi : o₃ ⟶ o₄)
    (c₁ : o₂ ⟶ o₆) (c₂ : o₃ ⟶ o₇)
    (ΦT₁ : o₁ ⟶ o₉) (ΦT₂ : o₉ ⟶ o₅) (ΦB₁ : o₄ ⟶ o₁₀) (ΦB₂ : o₁₀ ⟶ o₈)
    (mQ : o₅ ⟶ o₆) (mS : o₈ ⟶ o₇) (mSi : o₇ ⟶ o₈) (Mt : o₆ ⟶ o₇)
    (hQ : A ≫ c₁ = ΦT₁ ≫ ΦT₂ ≫ mQ) (hS : Bh ≫ c₂ = ΦB₁ ≫ ΦB₂ ≫ mS)
    (hT : TL ≫ c₂ = c₁ ≫ Mt) (hinv : Bi ≫ Bh = 𝟙 o₃) (hSinv : mS ≫ mSi = 𝟙 o₈) :
    ((A ≫ TL) ≫ Bi) ≫ ΦB₁ ≫ ΦB₂ = ΦT₁ ≫ ΦT₂ ≫ mQ ≫ Mt ≫ mSi := by
  have h1 : Bh ≫ c₂ ≫ mSi = ΦB₁ ≫ ΦB₂ := by
    rw [reassoc_of% hS, hSinv, Category.comp_id]
  rw [← h1]
  simp only [Category.assoc, reassoc_of% hinv, reassoc_of% hT, reassoc_of% hQ]

section Degreewise

variable [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)]
  [PreservesFiniteLimits (modulePullback i)] [PreservesFiniteColimits (modulePullback i)]
  [PreservesFiniteLimits (modulePullback j)] [PreservesFiniteColimits (modulePullback j)]
  [PreservesFiniteLimits (modulePullback g)] [PreservesFiniteColimits (modulePullback g)]

/-- **The derived image of the comparison of the two iterated pullbacks around a commutative
square of ringed spaces with exact pullbacks**, as a two-square of the functors the four
degreewise pullbacks induce on derived categories.  This is
`Stacks.Homology.mapDerivedCategoryTwoSquareOfIso` at
`Stacks.Cohomology.pullbackCompIso`, whose `hom` is the transformation of
`Stacks.Cohomology.pullbackCompSquare` by `Stacks.Cohomology.pullbackCompIso_hom`. -/
def mapDerivedCategoryPullbackCompSquare (w : i ≫ f = g ≫ j) :
    TwoSquare (modulePullback j).mapDerivedCategory (modulePullback f).mapDerivedCategory
      (modulePullback g).mapDerivedCategory (modulePullback i).mapDerivedCategory :=
  Stacks.Homology.mapDerivedCategoryTwoSquareOfIso (modulePullback j) (modulePullback f)
    (modulePullback g) (modulePullback i) (pullbackCompIso f i j g w)

/-- `Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare` read through the two composition
isomorphisms of [Stacks, Tag 0096] and the transport along the commutativity of the square. -/
theorem mapDerivedCategoryPullbackCompSquare_natTrans (w : i ≫ f = g ≫ j) :
    (mapDerivedCategoryPullbackCompSquare f i j g w) =
      (Stacks.Homology.mapDerivedCategoryCompIso (modulePullback j) (modulePullback g)
          (modulePullback (g ≫ j))
          (Stacks.DerivedPullback.Composition.modulePullbackComp g j)).hom ≫
        (Stacks.Homology.mapDerivedCategoryIsoOfIso (modulePullback (g ≫ j))
            (modulePullback (i ≫ f)) (eqToIso (congrArg modulePullback w.symm))).hom ≫
          (Stacks.Homology.mapDerivedCategoryCompIso (modulePullback f) (modulePullback i)
            (modulePullback (i ≫ f))
            (Stacks.DerivedPullback.Composition.modulePullbackComp i f)).inv := by
  rw [mapDerivedCategoryPullbackCompSquare, pullbackCompIso_eq]
  exact Stacks.Homology.mapDerivedCategoryTwoSquareOfIso_natTrans (modulePullback j)
    (modulePullback f) (modulePullback g) (modulePullback i) (modulePullback (g ≫ j))
    (modulePullback (i ≫ f)) (Stacks.DerivedPullback.Composition.modulePullbackComp g j)
    (Stacks.DerivedPullback.Composition.modulePullbackComp i f)
    (eqToIso (congrArg modulePullback w.symm))

/-- **The derived base change comparison of iterated derived pullbacks is the derived image of
the underived one.**  For a commutative square of ringed spaces along whose four morphisms
pullback of sheaves of modules is exact, the two-square
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare` of [Stacks, Tag 08HY] corresponds,
under the four identifications `Lf^* ≅ D(f^*)` of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory`, to the derived
image `Stacks.Cohomology.mapDerivedCategoryPullbackCompSquare` of the underived comparison
`Stacks.Cohomology.pullbackCompSquare`.

Together with `Stacks.Cohomology.pushforwardRestrictMap_eq_mateEquiv`, which exhibits the
underived base change as the mate of `pullbackCompSquare`, this identifies the derived base
change of [Stacks, Tag 08HY] with the underived one whenever the square is exact.

Both targets of the square are left derived functors of degreewise pullback along the common
composite, and the compatibility of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory` with composition
supplies the two triangles; the transport along the commutativity of the square is
`Stacks.Cohomology.derivedPullbackIsoMapDerivedCategory_eqToHom`. -/
theorem derivedPullbackSquare_eq_mapDerivedCategory (w : i ≫ f = g ≫ j) :
    (DerivedBaseChange.derivedPullbackSquare i g f j w) ≫
        Functor.whiskerRight
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom
            (derivedPullback i) ≫
          Functor.whiskerLeft (modulePullback f).mapDerivedCategory
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).hom =
      Functor.whiskerRight
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory j).hom
            (derivedPullback g) ≫
          Functor.whiskerLeft (modulePullback j).mapDerivedCategory
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory g).hom ≫
        (mapDerivedCategoryPullbackCompSquare f i j g w) := by
  have hsq : (DerivedBaseChange.derivedPullbackSquare i g f j w) =
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g j).hom ≫
        eqToHom (congrArg (fun q : U ⟶ Y => derivedPullback q) w.symm)) ≫
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical i f).inv := rfl
  rw [hsq, mapDerivedCategoryPullbackCompSquare_natTrans]
  exact square_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory_comp g j)
    (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory_comp i f)
    (derivedPullbackIsoMapDerivedCategory_eqToHom w.symm) (Iso.inv_hom_id _) (Iso.hom_inv_id _)

end Degreewise

end Stacks.Cohomology

end

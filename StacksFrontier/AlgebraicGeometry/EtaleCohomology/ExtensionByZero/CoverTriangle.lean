module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorsTriangle
public import StacksFrontier.CategoryTheory.Abelian.PointwiseBiproductFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The Mayer--Vietoris triangle of a cover by two open subschemes

Let `X` be a scheme covered by two open subschemes `U` and `V`.  For every object `K` of the
derived category of abelian sheaves on the small étale site of `X` there is a distinguished
triangle
`j_{U ∩ V!} K|_{U ∩ V} ⟶ j_{U!} K|_U ⊕ j_{V!} K|_V ⟶ K ⟶ (j_{U ∩ V!} K|_{U ∩ V})[1]`.

## Main definitions

* `Stacks.EtaleCohomology.coverComparison`: for an étale morphism factoring through an open
  immersion `j`, the canonical map `j_{W!} j_W^{-1} ⟶ j_! j^{-1}` over the identity functor.
* `Stacks.EtaleCohomology.coverBiprod`: the functor `F ↦ j_{U!}F|_U ⊕ j_{V!}F|_V`.
* `Stacks.EtaleCohomology.coverToBiprod` and `Stacks.EtaleCohomology.coverFromBiprod`: the two
  maps `j_{U ∩ V!}F|_{U ∩ V} ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F` of the Mayer--Vietoris sequence.

## Main results

* `Stacks.EtaleCohomology.shortExact_coverShortComplex`: the resulting short complex of abelian
  sheaves is short exact.
* `Stacks.EtaleCohomology.exists_distTriang_cover`: **Stacks Project, Tag 0GKK** for abelian
  coefficients, the distinguished triangle above.
* `Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianInverseImage_family`: a family of
  morphisms to `X` whose images cover `X` jointly reflects isomorphisms of abelian sheaves on
  `X_étale`.

## The sign

The source displays the sequence
`0 → j_{U ∩ V!}F|_{U ∩ V} → j_{U!}F|_U ⊕ j_{V!}F|_V → F → 0`
without signs.  It is exact only with a sign: on `U ∩ V` both summands restrict to `F` and the
two canonical maps to `F` agree, so an unsigned first map composes with the second to twice the
inclusion rather than to zero.  The first map below is therefore `(ι, -ι)`, the second
`(ε_U, ε_V)`; that is the corrected form, and it is what the source's own proof supports.

## Coefficients

Stacks Tag 0GKK is stated for an arbitrary coefficient ring `Λ` and the derived category
`D(X_étale, Λ)`.  The theorem below is the case of abelian sheaves, that is `Λ = ℤ`.  Nothing in
the argument uses the coefficients, and the same proof over an arbitrary `Λ` is
`Stacks.EtaleCohomology.exists_distTriang_etaleModuleCover` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules`, which
carries the unrestricted tag.

## Implementation notes

The proof is the source's: the four functors involved are exact, so it suffices to produce the
short exact sequence of abelian sheaves, and that is checked at geometric points.  The family of
geometric points used is the one indexed by the points of `X`, through
`Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianInverseImage_family`, a family version of the
two-member statement already in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence`.

At a geometric point `x` the sequence falls into three cases and each is formal, by
`CategoryTheory.ShortComplex.shortExact_biprodMayerVietoris_of_isIso_fst` and its companion: the
counit `j_! j^{-1}F ⟶ F` becomes invertible after inverse image along any morphism factoring
through `j`, and the two extensions by zero vanish after inverse image along a morphism whose
image misses the open.  No stalk of an extension by zero is computed.

The comparison `j_{W!}j_W^{-1} ⟶ j_! j^{-1}` for `W` inside `U` is obtained from the adjunction
`j_{W!} ⊣ j_W^{-1}`, the transpose being the inverse of the restriction to `W` of the counit of
`j_! ⊣ j^{-1}`; that inverse is natural, so no naturality has to be checked by hand, and the
characterising identity `comparison ≫ ε_U = ε_W` is immediate from the triangle identity.

## References

* [Stacks Project, Tag 0GKK](https://stacks.math.columbia.edu/tag/0GKK)
* [Stacks Project, Tag 0GKL](https://stacks.math.columbia.edu/tag/0GKL)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe w u v

namespace Stacks.EtaleCohomology

/-! ### Vanishing away from the open an extension by zero comes from -/

section Disjoint

variable {T U X : Scheme.{u}} (g : T ⟶ X) (j : U ⟶ X) [Etale j]
  (hgj : Disjoint (Set.range g.base) (Set.range j.base))

include hgj

/-- The base change along `g` of an étale scheme over `U` is empty when the images of `g` and of
`j` are disjoint. -/
theorem isEmpty_smallEtaleBaseChange_smallEtaleCompose_of_disjoint (W : U.Etale) :
    IsEmpty ((smallEtaleBaseChange g).obj ((smallEtaleCompose j).obj W)).left := by
  show IsEmpty (Limits.pullback (C := Scheme.{u}) (W.hom ≫ j) g)
  refine Scheme.isEmpty_pullback _ _ (Set.disjoint_left.2 ?_)
  rintro x ⟨w, rfl⟩ hx
  exact Set.disjoint_right.1 hgj ⟨W.hom.base w, by simp⟩ hx

/-- Restricting to `U` a direct image along a morphism whose image misses `U` gives zero. -/
theorem isZero_etaleRestriction_etaleAbelianDirectImage_of_disjoint
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsZero ((etaleRestriction.{u, v} j).obj ((etaleAbelianDirectImage.{u, v} g).obj G)) :=
  isZero_of_forall_isZero_sections _ fun W ↦
    isZero_sections_of_isEmpty G _
      (isEmpty_smallEtaleBaseChange_smallEtaleCompose_of_disjoint g j hgj W)

/-- The inverse image along `g` of an extension by zero from `U` is zero when the images of `g`
and of `j` are disjoint. -/
theorem isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsZero ((etaleAbelianInverseImage.{u, v} g).obj ((extensionByZero.{u, v} j).obj G)) := by
  rw [IsZero.iff_id_eq_zero]
  exact ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).homEquiv _ _).injective
    (((extensionByZeroAdj.{u, v} j).homEquiv _ _).injective
      ((isZero_etaleRestriction_etaleAbelianDirectImage_of_disjoint g j hgj _).eq_of_tgt _ _))

end Disjoint

/-! ### The counit after an inverse image factoring through the open -/

section Factors

variable {T U X : Scheme.{u}} (g : T ⟶ X) (j : U ⟶ X) [IsOpenImmersion j] (k : T ⟶ U)
  (hk : k ≫ j = g)

include hk

/-- The counit `j_! j^{-1} F ⟶ F` of an open immersion becomes an isomorphism after inverse
image along any morphism factoring through `j`: the inverse image of a composite is the
composite of the inverse images, and the counit is already invertible after `j^{-1}`. -/
theorem isIso_etaleAbelianInverseImage_map_counit_of_factors
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((etaleAbelianInverseImage.{u, v} g).map
      ((extensionByZeroAdj.{u, v} j).counit.app F)) := by
  subst hk
  have _ : IsIso ((etaleAbelianInverseImage.{u, v} j).map
      ((extensionByZeroAdj.{u, v} j).counit.app F)) :=
    (NatIso.isIso_map_iff (etaleAbelianInverseImageRestrictionIso.{u, v} j)
      ((extensionByZeroAdj.{u, v} j).counit.app F)).mpr
        (isIso_etaleRestriction_map_counit.{u, v} j F)
  refine (NatIso.isIso_map_iff (etaleAbelianInverseImageCompIso.{u, v} k j)
    ((extensionByZeroAdj.{u, v} j).counit.app F)).mpr ?_
  show IsIso ((etaleAbelianInverseImage.{u, v} k).map
    ((etaleAbelianInverseImage.{u, v} j).map ((extensionByZeroAdj.{u, v} j).counit.app F)))
  exact Functor.map_isIso _ _

/-- The counit `j_! j^{-1} F ⟶ F` of an open immersion becomes an isomorphism after restriction
along any étale morphism factoring through `j`. -/
theorem isIso_etaleRestriction_map_counit_of_factors [Etale g]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((etaleRestriction.{u, v} g).map ((extensionByZeroAdj.{u, v} j).counit.app F)) :=
  (NatIso.isIso_map_iff (etaleAbelianInverseImageRestrictionIso.{u, v} g)
    ((extensionByZeroAdj.{u, v} j).counit.app F)).mp
      (isIso_etaleAbelianInverseImage_map_counit_of_factors g j k hk F)

end Factors

/-! ### A covering family of morphisms reflects isomorphisms -/

/-- The residue geometric points of the sources of a jointly surjective family, composed with
the family, are again jointly surjective. -/
theorem iUnion_range_residueGeometricPoint_comp_eq_univ {X : Scheme.{u}} {ι : Type u}
    {T : ι → Scheme.{u}} (g : ∀ a, T a ⟶ X) (hg : ⋃ a, Set.range (g a).base = Set.univ) :
    ⋃ p : (a : ι) × (T a),
      Set.range (residueGeometricPoint (T p.1) p.2 ≫ g p.1) = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have hx : x ∈ ⋃ a, Set.range (g a).base := by simp [hg]
  obtain ⟨a, t, rfl⟩ := Set.mem_iUnion.1 hx
  refine Set.mem_iUnion.2 ⟨⟨a, t⟩, default, ?_⟩
  show (g a).base ((residueGeometricPoint (T a) t).base default) = (g a).base t
  rw [residueGeometricPoint_apply]

/-- A family of morphisms `g a : T a ⟶ X` whose images cover `X` jointly reflects isomorphisms
of abelian sheaves on the small étale site of `X`.

The residue geometric points of the `T a`, pushed forward along the `g a`, form a conservative
family of points of `X_étale`, and the stalk of an inverse image at such a point is the stalk of
the original sheaf at its image. -/
theorem isIso_of_isIso_etaleAbelianInverseImage_family {X : Scheme.{u}} {ι : Type u}
    {T : ι → Scheme.{u}} (g : ∀ a, T a ⟶ X)
    (hg : ⋃ a, Set.range (g a).base = Set.univ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (γ : F ⟶ G)
    (hγ : ∀ a, IsIso ((etaleAbelianInverseImage.{u, v} (g a)).map γ)) : IsIso γ := by
  let Φ := fun p : (a : ι) × (T a) ↦
    (pointSmallEtale (residueGeometricPoint (T p.1) p.2 ≫ g p.1)).ulift.{max (u + 1) v}
  have hP : (ObjectProperty.ofObj Φ).IsConservativeFamilyOfPoints :=
    Scheme.isConservative_pointSmallEtale_ulift _
      (iUnion_range_residueGeometricPoint_comp_eq_univ g hg)
  have happ : ∀ q : (ObjectProperty.ofObj Φ).FullSubcategory,
      IsIso (q.obj.sheafFiber.map γ) := by
    rintro ⟨_, ⟨p⟩⟩
    obtain ⟨a, t⟩ := p
    have _ := hγ a
    refine (NatIso.isIso_map_iff (etaleAbelianInverseImageSheafFiberIso.{u, v} (g a)
      (residueGeometricPoint (T a) t)) γ).mp ?_
    show IsIso (((pointSmallEtale
      (residueGeometricPoint (T a) t)).ulift.{max (u + 1) v}).sheafFiber.map
        ((etaleAbelianInverseImage.{u, v} (g a)).map γ))
    exact Functor.map_isIso _ _
  exact (hP.jointlyReflectIsomorphisms AddCommGrpCat.{max (u + 1) v}).isIso γ

/-! ### The comparison of two extensions by zero -/

section Comparison

variable {W U X : Scheme.{u}} (jW : W ⟶ X) [Etale jW] (j : U ⟶ X) [IsOpenImmersion j]
  (k : W ⟶ U) (hk : k ≫ j = jW)

include hk

/-- For an étale `jW` factoring through the open immersion `j`, restricting the counit of
`j_! ⊣ j^{-1}` along `jW` gives an isomorphism of functors. -/
def restrictionCounitIso :
    extensionByZeroOfRestriction.{u, v} j ⋙ etaleRestriction.{u, v} jW ≅
      etaleRestriction.{u, v} jW := by
  have happ : ∀ F, IsIso ((Functor.whiskerRight (extensionByZeroAdj.{u, v} j).counit
      (etaleRestriction.{u, v} jW)).app F) :=
    isIso_etaleRestriction_map_counit_of_factors jW j k hk
  have _ : IsIso (Functor.whiskerRight (extensionByZeroAdj.{u, v} j).counit
      (etaleRestriction.{u, v} jW)) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerRight (extensionByZeroAdj.{u, v} j).counit
    (etaleRestriction.{u, v} jW))

/-- The canonical map `j_{W!} j_W^{-1} ⟶ j_! j^{-1}` attached to an étale `jW` factoring
through the open immersion `j`: the transpose, under `j_{W!} ⊣ j_W^{-1}`, of the inverse of
`Stacks.EtaleCohomology.restrictionCounitIso`. -/
def coverComparison :
    extensionByZeroOfRestriction.{u, v} jW ⟶ extensionByZeroOfRestriction.{u, v} j :=
  Functor.whiskerRight (restrictionCounitIso.{u, v} jW j k hk).inv
      (extensionByZero.{u, v} jW) ≫
    Functor.whiskerLeft (extensionByZeroOfRestriction.{u, v} j)
      (extensionByZeroAdj.{u, v} jW).counit

/-- The comparison followed by the counit of `j_! ⊣ j^{-1}` is the counit of
`j_{W!} ⊣ j_W^{-1}`; this is what pins the comparison down. -/
theorem coverComparison_comp_counit
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (coverComparison.{u, v} jW j k hk).app F ≫ (extensionByZeroAdj.{u, v} j).counit.app F =
      (extensionByZeroAdj.{u, v} jW).counit.app F := by
  have hinv : (restrictionCounitIso.{u, v} jW j k hk).inv.app F ≫
      (etaleRestriction.{u, v} jW).map ((extensionByZeroAdj.{u, v} j).counit.app F) = 𝟙 _ :=
    (restrictionCounitIso.{u, v} jW j k hk).inv_hom_id_app F
  have hnat := (extensionByZeroAdj.{u, v} jW).counit.naturality
    ((extensionByZeroAdj.{u, v} j).counit.app F)
  simp only [Functor.comp_map, Functor.id_map] at hnat
  dsimp only [coverComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc, ← hnat, ← Functor.map_comp_assoc, hinv]
  simp

end Comparison

/-! ### Inverse images at a residue geometric point -/

section ResidueGeometricPoint

variable {X : Scheme.{u}} (W W' : X.Opens)
  (k : (W : Scheme.{u}) ⟶ (W' : Scheme.{u})) (hk : k ≫ W'.ι = W.ι) (x : X)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})

/-- The counit `j_{W!} F|_W ⟶ F` becomes an isomorphism of abelian sheaves after inverse image
at a residue geometric point lying in the open subscheme `W`. -/
theorem isIso_etaleAbelianInverseImage_residueGeometricPoint_map_counit (hxW : x ∈ W) :
    IsIso ((etaleAbelianInverseImage.{u, v} (residueGeometricPoint X x)).map
      ((extensionByZeroAdj.{u, v} W.ι).counit.app F)) := by
  have hsub : Set.range (residueGeometricPoint X x) ⊆ Set.range W.ι := by
    rintro z ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι, residueGeometricPoint_apply]
    exact hxW
  exact isIso_etaleAbelianInverseImage_map_counit_of_factors _ W.ι
    (IsOpenImmersion.lift W.ι _ hsub) (IsOpenImmersion.lift_fac _ _ hsub) F

/-- An extension by zero from an open subscheme `W` has zero inverse image at a residue
geometric point outside `W`. -/
theorem isZero_etaleAbelianInverseImage_residueGeometricPoint_extensionByZero (hxW : x ∉ W) :
    IsZero ((etaleAbelianInverseImage.{u, v} (residueGeometricPoint X x)).obj
      ((extensionByZeroOfRestriction.{u, v} W.ι).obj F)) := by
  have hd : Disjoint (Set.range (residueGeometricPoint X x).base) (Set.range (W.ι).base) := by
    refine Set.disjoint_left.2 ?_
    rintro z ⟨t, rfl⟩ hz
    rw [Scheme.Opens.range_ι, residueGeometricPoint_apply] at hz
    exact hxW hz
  exact isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint _ W.ι hd _

/-- The comparison `j_{W!} F|_W ⟶ j_{W'!} F|_{W'}` of two extensions by zero is an isomorphism
after inverse image at a residue geometric point of `W`: both sides then compute the counit. -/
theorem isIso_etaleAbelianInverseImage_residueGeometricPoint_map_coverComparison_of_mem
    (hxW : x ∈ W) (hxW' : x ∈ W') :
    IsIso ((etaleAbelianInverseImage.{u, v} (residueGeometricPoint X x)).map
      ((coverComparison.{u, v} W.ι W'.ι k hk).app F)) := by
  have _ := isIso_etaleAbelianInverseImage_residueGeometricPoint_map_counit W x F hxW
  have _ := isIso_etaleAbelianInverseImage_residueGeometricPoint_map_counit W' x F hxW'
  have hfac : (etaleAbelianInverseImage.{u, v} (residueGeometricPoint X x)).map
        ((coverComparison.{u, v} W.ι W'.ι k hk).app F) ≫
        (etaleAbelianInverseImage.{u, v} (residueGeometricPoint X x)).map
          ((extensionByZeroAdj.{u, v} W'.ι).counit.app F) =
      (etaleAbelianInverseImage.{u, v} (residueGeometricPoint X x)).map
        ((extensionByZeroAdj.{u, v} W.ι).counit.app F) := by
    rw [← Functor.map_comp, coverComparison_comp_counit]
  exact IsIso.of_isIso_fac_right hfac

/-- The comparison `j_{W!} F|_W ⟶ j_{W'!} F|_{W'}` of two extensions by zero is an isomorphism
after inverse image at a residue geometric point outside both opens: both sides vanish. -/
theorem isIso_etaleAbelianInverseImage_residueGeometricPoint_map_coverComparison_of_notMem
    (hxW : x ∉ W) (hxW' : x ∉ W') :
    IsIso ((etaleAbelianInverseImage.{u, v} (residueGeometricPoint X x)).map
      ((coverComparison.{u, v} W.ι W'.ι k hk).app F)) :=
  ⟨⟨0, (isZero_etaleAbelianInverseImage_residueGeometricPoint_extensionByZero W x F
      hxW).eq_of_src _ _,
    (isZero_etaleAbelianInverseImage_residueGeometricPoint_extensionByZero W' x F
      hxW').eq_of_src _ _⟩⟩

end ResidueGeometricPoint

/-! ### The Mayer--Vietoris short complex of a cover by two opens -/

section Cover

variable {X : Scheme.{u}} (U V : X.Opens)

/-- The functor `F ↦ j_{U!}F|_U ⊕ j_{V!}F|_V` of a pair of open subschemes. -/
abbrev coverBiprod : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Functor.pointwiseBiprod (extensionByZeroOfRestriction.{u, v} U.ι)
    (extensionByZeroOfRestriction.{u, v} V.ι)

/-- The canonical map `j_{U ∩ V!}F|_{U ∩ V} ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V`.  The second component
carries a sign: without it the composite with the next map is twice the inclusion of
`j_{U ∩ V!}F|_{U ∩ V}` in `F`, not zero. -/
def coverToBiprod :
    extensionByZeroOfRestriction.{u, v} (U ⊓ V).ι ⟶ coverBiprod.{u, v} U V :=
  Functor.pointwiseBiprod.lift _ _
    (coverComparison.{u, v} (U ⊓ V).ι U.ι (X.homOfLE inf_le_left) (X.homOfLE_ι _))
    (-coverComparison.{u, v} (U ⊓ V).ι V.ι (X.homOfLE inf_le_right) (X.homOfLE_ι _))

/-- The canonical map `j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F`, given by the two counits. -/
def coverFromBiprod : coverBiprod.{u, v} U V ⟶ 𝟭 _ :=
  Functor.pointwiseBiprod.desc _ _ (extensionByZeroAdj.{u, v} U.ι).counit
    (extensionByZeroAdj.{u, v} V.ι).counit

/-- The two canonical maps of the Mayer--Vietoris sequence compose to zero. -/
theorem coverToBiprod_comp_coverFromBiprod
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (coverToBiprod.{u, v} U V).app F ≫ (coverFromBiprod.{u, v} U V).app F = 0 := by
  show biprod.lift
      ((coverComparison.{u, v} (U ⊓ V).ι U.ι (X.homOfLE inf_le_left) (X.homOfLE_ι _)).app F)
      (-((coverComparison.{u, v} (U ⊓ V).ι V.ι (X.homOfLE inf_le_right)
        (X.homOfLE_ι _)).app F)) ≫
    biprod.desc ((extensionByZeroAdj.{u, v} U.ι).counit.app F)
      ((extensionByZeroAdj.{u, v} V.ι).counit.app F) = 0
  rw [biprod.lift_desc, Preadditive.neg_comp, coverComparison_comp_counit,
    coverComparison_comp_counit, add_neg_cancel]

/-- Both comparisons out of `j_{U ⊓ V!}F|_{U ⊓ V}`, followed by the counit of the open they
land over, give the counit of `j_{U ⊓ V!} ⊣ j_{U ⊓ V}^{-1}`, hence agree. -/
theorem coverComparison_counit_comm
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (coverComparison.{u, v} (U ⊓ V).ι U.ι (X.homOfLE inf_le_left)
          (X.homOfLE_ι _)).app F ≫ (extensionByZeroAdj.{u, v} U.ι).counit.app F =
      (coverComparison.{u, v} (U ⊓ V).ι V.ι (X.homOfLE inf_le_right)
          (X.homOfLE_ι _)).app F ≫ (extensionByZeroAdj.{u, v} V.ι).counit.app F := by
  rw [coverComparison_comp_counit, coverComparison_comp_counit]

/-- The comparison `j_{U ⊓ V!}F|_{U ⊓ V} ⟶ j_{V!}F|_V` is an isomorphism after inverse image at
any residue geometric point of `U`: inside `V` both sides compute the counit, outside `V` both
vanish. -/
theorem isIso_etaleAbelianInverseImage_residueGeometricPoint_map_coverComparison_of_mem_left
    (x : X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (hxU : x ∈ U) :
    IsIso ((etaleAbelianInverseImage.{u, v} (residueGeometricPoint X x)).map
      ((coverComparison.{u, v} (U ⊓ V).ι V.ι (X.homOfLE inf_le_right)
        (X.homOfLE_ι _)).app F)) := by
  by_cases hxV : x ∈ V
  · exact isIso_etaleAbelianInverseImage_residueGeometricPoint_map_coverComparison_of_mem
      (U ⊓ V) V _ _ x F ⟨hxU, hxV⟩ hxV
  · exact isIso_etaleAbelianInverseImage_residueGeometricPoint_map_coverComparison_of_notMem
      (U ⊓ V) V _ _ x F (fun h ↦ hxV h.2) hxV

variable (hUV : U ⊔ V = ⊤)

include hUV

/-- The Mayer--Vietoris short exact sequence of a cover of `X` by two open subschemes: for every
abelian sheaf `F` on the small étale site of `X` the sequence
`0 ⟶ j_{U ∩ V!}F|_{U ∩ V} ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`
is short exact, the first map being `(ι, -ι)` and the second the pair of counits.

Exactness is checked at the geometric points of `X`: at a point of `U ∩ V` all four maps become
invertible, and at a point of only one of the two opens the terms belonging to the other open
vanish. -/
theorem shortExact_coverShortComplex
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (ShortComplex.mk ((coverToBiprod.{u, v} U V).app F) ((coverFromBiprod.{u, v} U V).app F)
      (coverToBiprod_comp_coverFromBiprod.{u, v} U V F)).ShortExact := by
  show (ShortComplex.biprodMayerVietoris
      ((coverComparison.{u, v} (U ⊓ V).ι U.ι (X.homOfLE inf_le_left) (X.homOfLE_ι _)).app F)
      ((coverComparison.{u, v} (U ⊓ V).ι V.ι (X.homOfLE inf_le_right) (X.homOfLE_ι _)).app F)
      ((extensionByZeroAdj.{u, v} U.ι).counit.app F)
      ((extensionByZeroAdj.{u, v} V.ι).counit.app F)
      (coverComparison_counit_comm.{u, v} U V F)).ShortExact
  have hcov : ⋃ x : X, Set.range (residueGeometricPoint X x).base = Set.univ :=
    Set.eq_univ_of_forall fun x ↦
      Set.mem_iUnion.2 ⟨x, default, residueGeometricPoint_apply X x default⟩
  let Lf : (x : X) → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Spec (.of (SeparableClosure (X.residueField x)))).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v} :=
    fun x ↦ etaleAbelianInverseImage.{u, v} (residueGeometricPoint X x)
  have _ : ∀ x, PreservesFiniteLimits (Lf x) := fun x ↦ inferInstance
  have _ : ∀ x, PreservesFiniteColimits (Lf x) := fun x ↦ inferInstance
  have hL : JointlyReflectIsomorphisms Lf :=
    ⟨isIso_of_isIso_etaleAbelianInverseImage_family (residueGeometricPoint X) hcov⟩
  refine (hL.shortExact_iff _).2 fun x ↦ ?_
  refine ShortComplex.shortExact_map_biprodMayerVietoris (Lf x) _ _ _ _ _ ?_
  by_cases hxU : x ∈ U
  · have _ := isIso_etaleAbelianInverseImage_residueGeometricPoint_map_counit U x F hxU
    have _ :=
      isIso_etaleAbelianInverseImage_residueGeometricPoint_map_coverComparison_of_mem_left
        U V x F hxU
    exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_fst _ _ _ _ _
  · have hxV : x ∈ V :=
      (TopologicalSpace.Opens.mem_sup.1 (by simp [hUV] : x ∈ U ⊔ V)).resolve_left hxU
    have _ := isIso_etaleAbelianInverseImage_residueGeometricPoint_map_counit V x F hxV
    have _ := isIso_etaleAbelianInverseImage_residueGeometricPoint_map_coverComparison_of_notMem
      (U ⊓ V) U (X.homOfLE inf_le_left) (X.homOfLE_ι _) x F (fun h ↦ hxU h.1) hxU
    exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_snd _ _ _ _ _

/-- **Stacks Project, Tag 0GKK, for abelian coefficients.**  Let `X` be a scheme with
`X = U ∪ V` for open subschemes `U` and `V`.  For every object `K` of the derived category of
abelian sheaves on the small étale site of `X` there is a distinguished triangle
`j_{U ∩ V!} K|_{U ∩ V} ⟶ j_{U!} K|_U ⊕ j_{V!} K|_V ⟶ K ⟶ (j_{U ∩ V!} K|_{U ∩ V})[1]`,
the first arrow being `(ι, -ι)` and the second the pair of counits of `j_! ⊣ j^{-1}`, both
induced on the derived category by exactness of the functors involved.

Correction to the source: the displayed sequence is exact only with the Mayer--Vietoris sign on
one of the two components of the first arrow, which is carried here.  The source states the
triangle for sheaves of `Λ`-modules over an arbitrary ring `Λ`; this is the case `Λ = ℤ`, and
the general case is `Stacks.EtaleCohomology.exists_distTriang_etaleModuleCover`. -/
@[stacks 0GKK "abelian coefficients; first map carries the Mayer-Vietoris sign"]
theorem exists_distTriang_cover
    [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    ∃ δ : K ⟶
        ((extensionByZeroOfRestriction.{u, v} (U ⊓ V).ι).mapDerivedCategory.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk
        ((derivedNatTrans (extensionByZeroOfRestriction.{u, v} (U ⊓ V).ι)
          (coverBiprod.{u, v} U V) (coverToBiprod.{u, v} U V)).app K)
        (((coverBiprod.{u, v} U V).mapDerivedCategoryTransToId
          (coverFromBiprod.{u, v} U V)).app K) δ ∈
        distTriang (DerivedCategory
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :=
  DerivedCategory.exists_distTriang_of_natTrans_shortExact_toId _ _
    (coverToBiprod.{u, v} U V) (coverFromBiprod.{u, v} U V)
    (coverToBiprod_comp_coverFromBiprod.{u, v} U V)
    (shortExact_coverShortComplex.{u, v} U V hUV) K

end Cover

end Stacks.EtaleCohomology

end

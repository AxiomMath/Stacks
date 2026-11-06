module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingGermsOnOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedGeometricPointIndependence
public import StacksFrontier.CategoryTheory.Sites.Point.FiberIsoTransport
public import StacksFrontier.Cotangent.Spaces.RepresentableEpsilonSquare
public import StacksFrontier.Cotangent.Spaces.RepresentableEpsilon

/-!
# The stalks of `ε` at the geometric points of a represented algebraic space

Let `T` be an object of the big fppf site over `S`, `X = yoneda.obj T` the algebraic space it
represents and `X₀` the underlying scheme, and let
`ε = AlgebraicGeometry.Space.representedToZariskiRingedToposHom` be the comparison morphism of
ringed topoi `(X_étale, 𝒪_X) ⟶ (X₀,Zar, 𝒪_{X₀})` of Derived Categories of Spaces, Section 071P.
This file computes the stalks of `ε⁻¹` and of the inverse-image form `ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` of `ε♯`
at the points of the small étale site attached to the geometric points of `X`, which form a
conservative family (`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_uliftEtaleSitePoint`).

At the point attached to a geometric point `x̄` lying over `x ∈ X₀`, the stalk of `ε⁻¹N` is the
stalk `N_x` (Stacks 05V1: the image point of the point of `X_étale` on the Zariski site of `X₀`
is `x`), the stalk of `𝒪_X` is the étale local ring `𝒪_{X, x̄}`, and the stalk of `ε♯` is the
canonical map `𝒪_{X₀, x} → 𝒪_{X, x̄}` of Stacks 05VP, which is a strict henselization by
Stacks 04KF.

## Main definitions

* `AlgebraicGeometry.Space.representedImageRestrictionToInverseImage`: the comparison map from
  the restriction of a sheaf on `X₀` along the image-open functor to its inverse image `ε⁻¹`.
* `AlgebraicGeometry.Space.representedInverseImageStalkIso`: the stalk of `ε⁻¹N` at the point
  attached to `x̄` is the lift of `N_x`.
* `AlgebraicGeometry.Space.smallEtaleStructureSheafULiftStalkEquiv`: the stalk of the lifted
  structure sheaf of an algebraic space at a geometric point is the étale local ring.
* `AlgebraicGeometry.Space.smallEtaleInverseImageStructureSheafULiftStalkEquiv`: for a
  representable morphism `f : X ⟶ Y`, the stalk of the lifted `f⁻¹𝒪_Y` at `x̄` is the étale local
  ring of `Y` at `f(x̄)` (Stacks 04K2 (4)).
* `AlgebraicGeometry.Scheme.Hom.zariskiInverseImageStalkIso`: for a morphism of schemes `g`, the
  stalk of `g⁻¹N` at `x` is the stalk of `N` at `g x`.
* `Stacks.SitePointFiberIso.sheafFiberObjIsoOfLeftAdjoint`: the fibre of an inverse image, given
  as any left adjoint of restriction along a continuous functor, is the fibre at the image point,
  with values in any category.

## Main results

* `AlgebraicGeometry.Space.W_representedImageRestrictionToInverseImage`: the comparison map is
  inverted by sheafification, so it is an isomorphism on every stalk.
* `AlgebraicGeometry.Space.representedToZariskiRingedToposHom_stalk_isHenselization` and
  `AlgebraicGeometry.Space.representedToZariskiRingedToposHom_stalk_isHenselization_of_mem`: the
  stalk of `ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` at each of these points is a strict henselization.
* `AlgebraicGeometry.Space.representedBaseMap_stalk_isHenselization` and
  `AlgebraicGeometry.Space.representedBaseMap_stalk_isHenselization_of_mem`: for `h : T₁ ⟶ T₂`,
  the stalk of the base map `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y` of the square of Remark 08GH at each of
  these points is the canonical map `𝒪_{Y₀, y} → 𝒪_{Y, ȳ}` of Stacks 05VP, a strict
  henselization.

## Implementation notes

The inverse image `ε⁻¹` of sheaves of commutative rings is the inverse image of sheaves of sets
with its ring structure transported (`Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf`), so its
stalks are not computed by Mathlib's `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso`
for sheaves of rings.  Instead the site functor of `ε` has a left adjoint, the image-open functor
(`AlgebraicGeometry.Space.representedImageOpenAdjunction`), and the transpose of the unit of
`ε⁻¹ ⊣ ε_*` under restriction along it is a map of presheaves of rings
`(image open)^* N ⟶ ε⁻¹N` which every sheaf sees as a bijection on morphisms: it is the
composite of the adjunction bijections.  It is therefore in `J.W`, and Mathlib's
`CategoryTheory.GrothendieckTopology.Point.W_isInvertedBy_presheafFiber` makes it an isomorphism
on stalks.  The stalk of the restriction along the image-open functor is the Zariski stalk at `x`
because the image opens of the lifts of `x̄` are cofinal among the open neighbourhoods of `x`
(`AlgebraicGeometry.Space.representedNeighborhoodFunctor` is initial).

For the base map of the square of Remark 08GH the same stalk computation of `ε⁻¹` applies to
`f₀⁻¹𝒪_{Y₀}`, whose Zariski stalk at `x` is `𝒪_{Y₀, y}`, and the stalk of `f_small⁻¹𝒪_Y` at `x̄`
is the stalk of `𝒪_Y` at `f(x̄)`.  Both fibre comparisons are instances of
`Stacks.SitePointFiberIso.sheafFiberObjIsoOfLeftAdjoint`, the conjugate of the identification of
skyscraper sheaves, for which the germ formula is read off the skyscraper adjunctions; the
direct image of `f_small` is taken as restriction along chart base change through
`AlgebraicGeometry.Space.chartComparisonCommRing`, the identification the base map itself is
built with.  A germ of a function `b` on `V ∋ y` is then followed through the base map to the
germ of `b` on the chart `V` of `yoneda.obj T₂` at `f(x̄)`, which is the image of the germ of `b`
under the canonical map of Stacks 05VP.

The étale local ring lives in `Type (u + 1)` and the local ring `𝒪_{X₀, x}` in `Type u`, so the
source of the henselization is `ULift 𝒪_{X₀, x}`, and the prescribed residue extension is the
residue field of the étale local ring; `IsLocalRing.IsHenselization.residueField_of_ringEquiv`
carries Stacks 04KF across.

## References

* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH)
* [Stacks Project, Tag 08VF](https://stacks.math.columbia.edu/tag/08VF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace IsLocalRing.IsHenselization

open IsLocalRing

/-- **Changing the base of a henselization along a ring isomorphism.**  If `Rh` is a
henselization of `R` and `σ : R' ≃+* R` is compatible with the structure maps, then `Rh` is a
henselization of `R'`, with respect to its own residue field. -/
theorem residueField_of_ringEquiv {R : Type*} [CommRing R] [IsLocalRing R]
    {L : Type*} [Field L] [Algebra (ResidueField R) L]
    {Rh : Type*} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsHenselization R L Rh]
    {R' : Type*} [CommRing R'] [IsLocalRing R'] [Algebra R' Rh] (σ : R' ≃+* R)
    (hσ : ∀ r, algebraMap R' Rh r = algebraMap R Rh (σ r)) [IsLocalHom (algebraMap R' Rh)] :
    IsHenselization R' (ResidueField Rh) Rh where
  henselian := henselian (R := R) (L := L)
  ind_etale := StacksDraft.indEtale_of_equiv σ.symm (RingEquiv.refl Rh)
    (fun a => by rw [hσ, σ.apply_symm_apply]; rfl) (ind_etale (R := R) (L := L))
  exists_residueFieldEquiv := ⟨RingEquiv.refl _, fun r => ResidueField.algebraMap_residue r⟩

end IsLocalRing.IsHenselization

namespace Stacks.SitePointFiberIso

open CategoryTheory.GrothendieckTopology

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type u₃} [Category.{v₃} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
  (Phi : Point.{w} K) (uf : C ⥤ D) [uf.IsContinuous J K]
  {L : Sheaf J A ⥤ Sheaf K A} (adj : L ⊣ uf.sheafPushforwardContinuous A J K)
  (Psi : Point.{w} J) (e : Psi.fiber ≅ uf ⋙ Phi.fiber)

/-- **The fibre of an inverse image at a point is the fibre at the image point**, for an
inverse image given as an arbitrary left adjoint `L` of the direct image along a continuous
functor `uf`, sheaves with values in any category `A`, and a point `Psi` whose fibre is
isomorphic to `uf ⋙ Phi.fiber`: the conjugate of the identification of the skyscraper of the
transported point with the direct image of the skyscraper of `Phi`. -/
noncomputable def sheafFiberConjugateIso :
    (pointOfFiberIso Psi e).sheafFiber (A := A) ≅ L ⋙ Phi.sheafFiber :=
  (conjugateIsoEquiv (adj.comp Phi.skyscraperSheafAdjunction)
    (pointOfFiberIso Psi e).skyscraperSheafAdjunction).symm (Iso.refl _)

/-- `Stacks.SitePointFiberIso.sheafFiberConjugateIso` on germs: the germ at a lift `q` of a
section is sent to the germ at the same lift of its image under the unit of `L ⊣ uf_*`. -/
theorem toPresheafFiber_sheafFiberConjugateIso_hom (P : Sheaf J A) (V : C)
    (q : (uf ⋙ Phi.fiber).obj V) :
    (pointOfFiberIso Psi e).toPresheafFiber V q P.obj ≫
        (sheafFiberConjugateIso Phi uf adj Psi e).hom.app P =
      (adj.homEquiv P (L.obj P) (𝟙 _)).hom.app (op V) ≫
        Phi.toPresheafFiber (uf.obj V) q (L.obj P).obj := by
  let Psi' := pointOfFiberIso Psi e
  let M := (Phi.sheafFiber (A := A)).obj (L.obj P)
  let X : P ⟶ Psi'.skyscraperSheafFunctor.obj M :=
    adj.homEquiv P (L.obj P) (𝟙 _) ≫ (uf.sheafPushforwardContinuous A J K).map
      (Phi.skyscraperSheafAdjunction.homEquiv (L.obj P) M (𝟙 _)) ≫
        (Iso.refl (Phi.skyscraperSheafFunctor ⋙ uf.sheafPushforwardContinuous A J K)).hom.app M
  let b := (Psi'.skyscraperSheafAdjunction.homEquiv P M).symm X
  have hb : (sheafFiberConjugateIso Phi uf adj Psi e).hom.app P = b := by
    have h := Adjunction.conjugate_comp adj Phi.skyscraperSheafAdjunction
      Psi'.skyscraperSheafAdjunction (Iso.refl _) (adj.homEquiv P (L.obj P) (𝟙 _)) (𝟙 M) b
      (Equiv.apply_symm_apply (Psi'.skyscraperSheafAdjunction.homEquiv P M) X).symm
    simp only [Equiv.symm_apply_apply, CategoryTheory.Functor.map_id] at h
    refine Eq.trans ?_ h
    exact (Category.comp_id _).symm.trans
      (congrArg (_ ≫ ·) (Category.comp_id (𝟙 M)).symm)
  rw [hb]
  refine (Point.toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm Psi' P M X V q).trans
    ?_
  have hX : X.hom.app (op V) = (adj.homEquiv P (L.obj P) (𝟙 _)).hom.app (op V) ≫
      (Phi.skyscraperSheafAdjunction.homEquiv (L.obj P) M (𝟙 _)).hom.app (op (uf.obj V)) :=
    congrArg (_ ≫ ·) (Category.comp_id _)
  refine (congrArg (· ≫ _) hX).trans ((Category.assoc _ _ _).trans ?_)
  exact congrArg (_ ≫ ·) (Point.skyscraperSheafAdjunction_unit_π Phi (L.obj P) (uf.obj V) q)

/-- **The fibre of an inverse image at a point is the fibre at the image point, on one sheaf**:
the fibre at `Psi` of a sheaf `P` is the fibre at `Phi` of `L P`.  It is the transport of the
fibre along `e` followed by `Stacks.SitePointFiberIso.sheafFiberConjugateIso`. -/
noncomputable def sheafFiberObjIsoOfLeftAdjoint (P : Sheaf J A) :
    (Psi.presheafFiber (A := A)).obj P.obj ≅ (Phi.presheafFiber (A := A)).obj (L.obj P).obj :=
  Stacks.presheafFiberIsoAlong Psi (pointOfFiberIso Psi e) e P.obj ≪≫
    (sheafFiberConjugateIso Phi uf adj Psi e).app P

/-- `Stacks.SitePointFiberIso.sheafFiberObjIsoOfLeftAdjoint` on germs: the germ at a lift `q`
of a section of `P` is sent to the germ at the transported lift `e q` of its image under the
unit of `L ⊣ uf_*`. -/
theorem toPresheafFiber_sheafFiberObjIsoOfLeftAdjoint_hom (P : Sheaf J A) (V : C)
    (q : Psi.fiber.obj V) :
    Psi.toPresheafFiber V q P.obj ≫ (sheafFiberObjIsoOfLeftAdjoint Phi uf adj Psi e P).hom =
      (adj.homEquiv P (L.obj P) (𝟙 _)).hom.app (op V) ≫
        Phi.toPresheafFiber (uf.obj V) (e.hom.app V q) (L.obj P).obj := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Stacks.toPresheafFiber_presheafFiberMapAlong Psi
    (pointOfFiberIso Psi e) e.hom P.obj V q)).trans ?_
  exact toPresheafFiber_sheafFiberConjugateIso_hom Phi uf adj Psi e P V (e.hom.app V q)

end Stacks.SitePointFiberIso

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.SitePointFiberIso

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The adjunction between the inverse image of sheaves of commutative rings along the Zariski
morphism of topoi of a morphism of schemes and restriction along the inverse image of opens. -/
noncomputable abbrev zariskiInverseImageAdjunction :=
  (commRingImageAdjunction (zariskiRingedToposHom g).toToposHom).ofNatIsoRight
    (restrictionCommRingNatIso (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      (Opens.map g.base))

/-- **The stalk of the Zariski inverse image of a sheaf of rings is the stalk at the image
point.**  For a morphism of schemes `g : X ⟶ Y`, a point `x` of `X` and a sheaf `N` of
commutative rings on `Y`, the stalk of `g⁻¹N` at `x` is the stalk of `N` at `g x`. -/
noncomputable def zariskiInverseImageStalkIso
    (N : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) (x : X) :
    TopCat.Presheaf.stalk (X := X.toTopCat)
        ((inverseImageCommRingFunctor (zariskiRingedToposHom g).toToposHom).obj N).obj x ≅
      TopCat.Presheaf.stalk (X := Y.toTopCat) N.obj (g x) :=
  (Opens.pointFiberStalkIso x _).symm ≪≫
    (sheafFiberObjIsoOfLeftAdjoint (J := Opens.grothendieckTopology Y)
      (K := Opens.grothendieckTopology X) (Opens.pointGrothendieckTopology x) (Opens.map g.base)
      (zariskiInverseImageAdjunction g) (Opens.pointGrothendieckTopology (g x)) (Iso.refl _)
        N).symm ≪≫
    Opens.pointFiberStalkIso (g x) N.obj

/-- `AlgebraicGeometry.Scheme.Hom.zariskiInverseImageStalkIso` on germs: the germ at `g x` of a
section of `N` over `V` corresponds to the germ at `x` of its image in `(g⁻¹N)(g⁻¹V)` under the
unit of `g⁻¹ ⊣ g_*`. -/
theorem germ_zariskiInverseImageStalkIso_inv
    (N : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) (x : X) (V : Y.Opens)
    (hx : g x ∈ V) :
    TopCat.Presheaf.germ (X := Y.toTopCat) N.obj V (g x) hx ≫
        (zariskiInverseImageStalkIso g N x).inv =
      ((zariskiInverseImageAdjunction g).homEquiv N _ (𝟙 _)).hom.app (op V) ≫
        TopCat.Presheaf.germ (X := X.toTopCat)
          ((inverseImageCommRingFunctor (zariskiRingedToposHom g).toToposHom).obj N).obj
          (g ⁻¹ᵁ V) x hx := by
  have h1 := Opens.germ_pointFiberStalkInv (g x) N.obj V hx
  have h2 := toPresheafFiber_sheafFiberObjIsoOfLeftAdjoint_hom (J := Opens.grothendieckTopology Y)
    (K := Opens.grothendieckTopology X) (Opens.pointGrothendieckTopology x) (Opens.map g.base)
    (zariskiInverseImageAdjunction g) (Opens.pointGrothendieckTopology (g x)) (Iso.refl _) N V
    ⟨⟨hx⟩⟩
  have h3 := Opens.toPresheafFiber_pointFiberStalkHom x
    ((inverseImageCommRingFunctor (zariskiRingedToposHom g).toToposHom).obj N).obj (g ⁻¹ᵁ V)
    ⟨⟨hx⟩⟩
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1))).trans ?_
  refine (congrArg (· ≫ _) h2).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h3)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- The adjunction between restriction along the image-open functor and restriction along the
site functor of `ε`, on presheaves of commutative rings. -/
noncomputable abbrev representedRestrictionAdjunction :=
  (representedImageOpenAdjunction B S hS T).op.whiskerLeft CommRingCat.{u + 1}

/-- The comparison map from the restriction along the image-open functor to `ε⁻¹`. -/
noncomputable def representedImageRestrictionToInverseImage
    (M : Sheaf (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      CommRingCat.{u + 1}) :
    (representedImageOpenFunctor B S hS T).op ⋙ M.obj ⟶
      ((inverseImageCommRingFunctor (representedToZariskiMorphismOfTopoi B S hS T)).obj M).obj :=
  ((representedRestrictionAdjunction B S hS T).homEquiv _ _).symm
    ((commRingImageAdjunction (representedToZariskiMorphismOfTopoi B S hS T)).unit.app M ≫
      (restrictionCommRingIso (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
        (SmallEtale.topology B S hS (yoneda.obj T)) (representedOpensToSmallEtale B S hS T)
        ((inverseImageCommRingFunctor (representedToZariskiMorphismOfTopoi B S hS T)).obj
          M)).hom).hom

/-- The comparison map followed by a morphism `h : ε⁻¹M ⟶ Q` of sheaves is the transpose, under
restriction along the image-open functor, of the transpose of `h` under `ε⁻¹ ⊣ ε_*`. -/
theorem representedImageRestrictionToInverseImage_comp
    (M : Sheaf (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      CommRingCat.{u + 1})
    (Q : Sheaf (SmallEtale.topology B S hS (yoneda.obj T)) CommRingCat.{u + 1})
    (h : (inverseImageCommRingFunctor (representedToZariskiMorphismOfTopoi B S hS T)).obj M ⟶ Q) :
    representedImageRestrictionToInverseImage B S hS T M ≫ h.hom =
      ((representedRestrictionAdjunction B S hS T).homEquiv _ _).symm
        (((commRingImageAdjunction (representedToZariskiMorphismOfTopoi B S hS T)).homEquiv M Q h ≫
          (restrictionCommRingIso (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
            (SmallEtale.topology B S hS (yoneda.obj T)) (representedOpensToSmallEtale B S hS T)
            Q).hom).hom) := by
  let ε := representedToZariskiMorphismOfTopoi B S hS T
  let JZ := Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T)
  let JE := SmallEtale.topology B S hS (yoneda.obj T)
  let F := representedOpensToSmallEtale B S hS T
  let R₀ := (inverseImageCommRingFunctor ε).obj M
  have hn := restrictionCommRingIso_naturality JZ JE F h
  rw [Adjunction.homEquiv_unit]
  refine ((representedRestrictionAdjunction B S hS T).homEquiv_naturality_right_symm _
    h.hom).symm.trans (congrArg _ ?_)
  exact Eq.trans (rfl : _ = ((commRingImageAdjunction ε).unit.app M ≫
      (restrictionCommRingIso JZ JE F R₀).hom ≫
        (F.sheafPushforwardContinuous CommRingCat.{u + 1} JZ JE).map h).hom)
    ((congrArg (fun k => ((commRingImageAdjunction ε).unit.app M ≫ k).hom) hn.symm).trans
      (congrArg InducedCategory.Hom.hom
        (Category.assoc ((commRingImageAdjunction ε).unit.app M)
          ((pushforwardCommRingFunctor ε).map h) (restrictionCommRingIso JZ JE F Q).hom).symm))

/-- **The comparison map is a local isomorphism.**  Every sheaf `Q` sees it as a bijection
`(ε⁻¹M ⟶ Q) ≃ ((image open)^* M ⟶ Q)`: it is the composite of the adjunction `ε⁻¹ ⊣ ε_*`, the
identification of `ε_*` with restriction along the site functor, and the adjunction between the
restrictions along the image-open functor and the site functor. -/
theorem W_representedImageRestrictionToInverseImage
    (M : Sheaf (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      CommRingCat.{u + 1}) :
    (SmallEtale.topology B S hS (yoneda.obj T)).W
      (representedImageRestrictionToInverseImage B S hS T M) := by
  intro Q hQ
  let ε := representedToZariskiMorphismOfTopoi B S hS T
  let JZ := Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T)
  let JE := SmallEtale.topology B S hS (yoneda.obj T)
  let F := representedOpensToSmallEtale B S hS T
  let Q' : Sheaf JE CommRingCat.{u + 1} := ⟨Q, hQ⟩
  let e := Sheaf.homEquiv.symm.trans <| ((commRingImageAdjunction ε).homEquiv M Q').trans <|
    (restrictionCommRingIso JZ JE F Q').homToEquiv.trans <|
      Sheaf.homEquiv.trans ((representedRestrictionAdjunction B S hS T).homEquiv _ _).symm
  have he : (fun h : ((inverseImageCommRingFunctor ε).obj M).obj ⟶ Q =>
      representedImageRestrictionToInverseImage B S hS T M ≫ h) = e := by
    funext h
    exact representedImageRestrictionToInverseImage_comp B S hS T M Q' (Sheaf.homEquiv.symm h)
  rw [he]
  exact e.bijective

/-- The comparison map is an isomorphism on the fibres at every point of the small étale site. -/
theorem W_isInvertedBy_representedImageRestrictionToInverseImage
    (M : Sheaf (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      CommRingCat.{u + 1})
    (Φ : (SmallEtale.topology B S hS (yoneda.obj T)).Point.{u + 1}) :
    IsIso ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map
      (representedImageRestrictionToInverseImage B S hS T M)) :=
  Φ.W_isInvertedBy_presheafFiber _ (W_representedImageRestrictionToInverseImage B S hS T M)

/-- The point `x` of `X₀` under a geometric point `x̄` lies in the image open of every étale
chart into which `x̄` lifts. -/
theorem chartPoint_yonedaIdentityNeighborhood_mem (xb : GeometricPoint B S hS (yoneda.obj T))
    (U : SmallEtale B S hS (yoneda.obj T)) (s : GeometricFiber B S hS (yoneda.obj T) xb U) :
    chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb) ∈
      (representedImageOpenFunctor B S hS T).obj U := by
  refine ⟨(BigFppfOver.toScheme B S hS).map s.1 (IsLocalRing.closedPoint xb.val.carrier), ?_⟩
  have key : ∀ {A Z : BigFppfOver B S hS} (α : yoneda.obj A ⟶ yoneda.obj T) (f : Z ⟶ A),
      α.app (op Z) f = f ≫ yonedaEquiv α := by
    intro A Z α f
    conv_lhs => rw [← yonedaEquiv.symm_apply_apply α]
    rfl
  have h : s.1 ≫ yonedaEquiv U.obj.hom = xb.val.value := (key U.obj.hom s.1).symm.trans s.2
  change ((BigFppfOver.toScheme B S hS).map s.1 ≫
    (BigFppfOver.toScheme B S hS).map (yonedaEquiv U.obj.hom)) _ = _
  rw [← Functor.map_comp, h]
  rfl

/-- **The stalk of the lifted structure sheaf at a geometric point is the étale local ring.**
For an algebraic space `X` and a geometric point `x̄`, the fibre of
`AlgebraicGeometry.Space.smallEtaleStructureSheafULift` at the universe lift of the point of the
small étale site attached to `x̄` is `𝒪_{X, x̄}`. -/
noncomputable def smallEtaleStructureSheafULiftStalkEquiv (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) :
    (((etaleSitePoint B S hS X.1 x X.2).ulift.{u + 1}).presheafFiber
        (A := CommRingCat.{u + 1})).obj (smallEtaleStructureSheafULift B S hS X).obj ≃+*
      etaleLocalRing B S hS X.1 x :=
  (Stacks.uliftRingFiberIso' (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O.obj).commRingCatIsoToRingEquiv.trans
    (ULift.ringEquiv.trans (pointStalkRingEquiv B S hS X x))

/-- `AlgebraicGeometry.Space.smallEtaleStructureSheafULiftStalkEquiv` sends the germ at a lift
of `x̄` of a lifted regular function to its germ in the étale local ring. -/
theorem smallEtaleStructureSheafULiftStalkEquiv_germ (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (U : SmallEtale B S hS X.1)
    (p : GeometricFiber B S hS X.1 x U)
    (a : (structurePresheaf B S hS X.1).obj (op U)) :
    smallEtaleStructureSheafULiftStalkEquiv B S hS X x
        (((etaleSitePoint B S hS X.1 x X.2).ulift.{u + 1}).toPresheafFiber U (ULift.up p)
          (smallEtaleStructureSheafULift B S hS X).obj (ULift.up a)) =
      etaleLocalRingGerm B S hS X.1 x (op ⟨U, p.1, p.2⟩) a := by
  have h := ConcreteCategory.congr_hom (Stacks.uliftRingFiberIso'_germ
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O.obj U p) (ULift.up a)
  refine Eq.trans ?_ (pointStalkRingEquiv_germ B S hS X x U p a)
  exact congrArg (fun z => pointStalkRingEquiv B S hS X x (ULift.ringEquiv z)) h

attribute [local instance] isContinuous_smallBaseChange

/-- The adjunction between the inverse image of sheaves of commutative rings along the small
étale morphism of a representable morphism `f` and restriction along chart base change, the
direct image being identified with that restriction by
`AlgebraicGeometry.Space.chartComparisonCommRing`. -/
noncomputable abbrev smallBaseChangeInverseImageAdjunction {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) :=
  (commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS f).toToposHom).ofNatIsoRight
      (chartComparisonCommRing B S hS f hf)

/-- **The stalk of `sheafULift (f⁻¹𝒪_Y)` at a geometric point `x̄` of `X` is the étale local
ring of `Y` at `f(x̄)`**, for a representable morphism `f : X ⟶ Y` of algebraic spaces: the
stalk of `f⁻¹𝒪_Y` at `x̄` is the stalk of `𝒪_Y` at `f(x̄)` (Stacks 04K2 (4)). -/
noncomputable def smallEtaleInverseImageStructureSheafULiftStalkEquiv {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1) :
    (((etaleSitePoint B S hS X.1 x X.2).ulift.{u + 1}).presheafFiber
        (A := CommRingCat.{u + 1})).obj
        ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).obj
          ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
            (smallEtaleRingedTopos B S hS Y).O)).obj ≃+*
      etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x) :=
  (Stacks.uliftRingFiberIso' (etaleSitePoint B S hS X.1 x X.2)
      ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O).obj).commRingCatIsoToRingEquiv.trans
    (ULift.ringEquiv.trans
      ((Stacks.SitePointFiberIso.sheafFiberObjIsoOfLeftAdjoint (etaleSitePoint B S hS X.1 x X.2)
        (smallBaseChange B S hS f hf) (smallBaseChangeInverseImageAdjunction B S hS f hf)
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallBaseChangeFiberIso B S hS f hf x).symm
        (smallEtaleRingedTopos B S hS Y).O).symm.commRingCatIsoToRingEquiv.trans
      (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x))))

/-- `AlgebraicGeometry.Space.smallEtaleInverseImageStructureSheafULiftStalkEquiv` on germs, at the
lift of `x̄` determined by a lift `q` of `f(x̄)`. -/
private theorem smallEtaleInverseImageStructureSheafULiftStalkEquiv_germ_aux
    {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) V)
    (t : (structurePresheaf B S hS Y.1).obj (op V)) :
    smallEtaleInverseImageStructureSheafULiftStalkEquiv B S hS f hf x
        (((etaleSitePoint B S hS X.1 x X.2).ulift.{u + 1}).toPresheafFiber
          ((smallBaseChange B S hS f hf).obj V)
          (ULift.up ((smallBaseChangeFiberIso B S hS f hf x).inv.app V q))
          ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).obj
            ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
              (smallEtaleRingedTopos B S hS Y).O)).obj
          (ULift.up ((((smallBaseChangeInverseImageAdjunction B S hS f hf).homEquiv _ _
            (𝟙 _)).hom.app (op V)) t))) =
      etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op ⟨V, q.1, q.2⟩) t := by
  let Φ := etaleSitePoint B S hS X.1 x X.2
  let Ψ := etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2
  let N := (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
    (smallEtaleRingedTopos B S hS Y).O
  let I := Stacks.SitePointFiberIso.sheafFiberObjIsoOfLeftAdjoint Φ
    (smallBaseChange B S hS f hf) (smallBaseChangeInverseImageAdjunction B S hS f hf) Ψ
    (smallBaseChangeFiberIso B S hS f hf x).symm (smallEtaleRingedTopos B S hS Y).O
  have h1 := ConcreteCategory.congr_hom (Stacks.uliftRingFiberIso'_germ Φ N.obj
    ((smallBaseChange B S hS f hf).obj V) ((smallBaseChangeFiberIso B S hS f hf x).inv.app V q))
    (ULift.up ((((smallBaseChangeInverseImageAdjunction B S hS f hf).homEquiv _ _
      (𝟙 _)).hom.app (op V)) t))
  have h2 := ConcreteCategory.congr_hom
    (Stacks.SitePointFiberIso.toPresheafFiber_sheafFiberObjIsoOfLeftAdjoint_hom Φ
      (smallBaseChange B S hS f hf) (smallBaseChangeInverseImageAdjunction B S hS f hf) Ψ
      (smallBaseChangeFiberIso B S hS f hf x).symm (smallEtaleRingedTopos B S hS Y).O V q) t
  have h3 : I.inv (Φ.toPresheafFiber ((smallBaseChange B S hS f hf).obj V)
      ((smallBaseChangeFiberIso B S hS f hf x).inv.app V q) N.obj
      ((((smallBaseChangeInverseImageAdjunction B S hS f hf).homEquiv _ _
        (𝟙 _)).hom.app (op V)) t)) =
        Ψ.toPresheafFiber V q (smallEtaleRingedTopos B S hS Y).O.obj t :=
    (congrArg I.inv h2.symm).trans (ConcreteCategory.congr_hom I.hom_inv_id _)
  refine Eq.trans ?_ (pointStalkRingEquiv_germ B S hS Y (geometricPointMap f.hom x) V q t)
  exact congrArg (fun z => pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)
    (I.inv (ULift.ringEquiv z))) h1 |>.trans (congrArg _ h3)

/-- `AlgebraicGeometry.Space.smallEtaleInverseImageStructureSheafULiftStalkEquiv` on germs: the
germ at a lift `p` of `x̄` into `X ×_Y V` of the image of a function `t` on `V` under the unit of
`f⁻¹ ⊣ f_*` is the germ of `t` at `V` with the lift of `f(x̄)` obtained by projecting `p`. -/
theorem smallEtaleInverseImageStructureSheafULiftStalkEquiv_germ {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (p : GeometricFiber B S hS X.1 x ((smallBaseChange B S hS f hf).obj V))
    (t : (structurePresheaf B S hS Y.1).obj (op V)) :
    smallEtaleInverseImageStructureSheafULiftStalkEquiv B S hS f hf x
        (((etaleSitePoint B S hS X.1 x X.2).ulift.{u + 1}).toPresheafFiber
          ((smallBaseChange B S hS f hf).obj V) (ULift.up p)
          ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).obj
            ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
              (smallEtaleRingedTopos B S hS Y).O)).obj
          (ULift.up ((((smallBaseChangeInverseImageAdjunction B S hS f hf).homEquiv _ _
            (𝟙 _)).hom.app (op V)) t))) =
      etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x)
        (op ⟨V, ((smallBaseChangeFiberMap B S hS f hf x).app V p).1,
          ((smallBaseChangeFiberMap B S hS f hf x).app V p).2⟩) t := by
  have hp : (smallBaseChangeFiberIso B S hS f hf x).inv.app V
      ((smallBaseChangeFiberMap B S hS f hf x).app V p) = p :=
    ConcreteCategory.congr_hom ((smallBaseChangeFiberIso B S hS f hf x).hom_inv_id_app V) p
  refine Eq.trans ?_ (smallEtaleInverseImageStructureSheafULiftStalkEquiv_germ_aux B S hS f hf x V
    ((smallBaseChangeFiberMap B S hS f hf x).app V p) t)
  exact congrArg (fun p' => smallEtaleInverseImageStructureSheafULiftStalkEquiv B S hS f hf x
    (((etaleSitePoint B S hS X.1 x X.2).ulift.{u + 1}).toPresheafFiber
      ((smallBaseChange B S hS f hf).obj V) (ULift.up p')
      ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).obj
        ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
          (smallEtaleRingedTopos B S hS Y).O)).obj
      (ULift.up ((((smallBaseChangeInverseImageAdjunction B S hS f hf).homEquiv _ _
        (𝟙 _)).hom.app (op V)) t)))) hp.symm

variable (xb : GeometricPoint B S hS (yoneda.obj T))

/-- The image open of a lift of `x̄` into an étale chart of `yoneda.obj T`, as an open
neighbourhood of the point `x` of `X₀` under `x̄`. -/
noncomputable def representedNeighborhoodFunctor :
    (etaleSitePoint B S hS (yoneda.obj T) xb (isAlgebraicSpace_yoneda B S hS T)).fiber.Elements ⥤
      OpenNhds (chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb)) where
  obj e := ⟨(representedImageOpenFunctor B S hS T).obj e.1,
    chartPoint_yonedaIdentityNeighborhood_mem B S hS T xb e.1 e.2⟩
  map f := homOfLE (leOfHom ((representedImageOpenFunctor B S hS T).map f.1))

/-- The image opens of the lifts of `x̄` are cofinal among the open neighbourhoods of `x`: every
open `W ∋ x` contains the image of the lift of `x̄` into `W` itself. -/
instance : (representedNeighborhoodFunctor B S hS T xb).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro W
    let N := chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T xb) W.1 W.2
    refine ⟨Functor.elementsMk _ N.chart ⟨N.point, N.point_comp⟩, ⟨homOfLE ?_⟩⟩
    exact leOfHom ((representedImageOpenAdjunction B S hS T).counit.app W.1)
  · intro W e s s'
    exact ⟨e, 𝟙 e, Subsingleton.elim _ _⟩

/-- The fibre at the point of the small étale site attached to `x̄` of the restriction of a
presheaf on `X₀` along the image-open functor is the stalk of that presheaf at the point `x` of
`X₀` under `x̄`: the image opens of the lifts of `x̄` are cofinal among the neighbourhoods of
`x`. -/
noncomputable def representedImagePresheafFiberIso
    (P : ((BigFppfOver.toScheme B S hS).obj T).Opensᵒᵖ ⥤ CommRingCat.{u}) :
    ((etaleSitePoint B S hS (yoneda.obj T) xb (isAlgebraicSpace_yoneda B S hS T)).presheafFiber
        (A := CommRingCat.{u})).obj ((representedImageOpenFunctor B S hS T).op ⋙ P) ≅
      TopCat.Presheaf.stalk (X := ((BigFppfOver.toScheme B S hS).obj T).toTopCat) P
        (chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb)) :=
  Functor.Final.colimitIso (representedNeighborhoodFunctor B S hS T xb).op
    ((OpenNhds.inclusion _).op ⋙ P)

/-- `AlgebraicGeometry.Space.representedImagePresheafFiberIso` sends the germ at a lift of `x̄`
to the ordinary germ at `x` over the image open. -/
theorem toPresheafFiber_representedImagePresheafFiberIso_hom
    (P : ((BigFppfOver.toScheme B S hS).obj T).Opensᵒᵖ ⥤ CommRingCat.{u})
    (U : SmallEtale B S hS (yoneda.obj T))
    (s : (etaleSitePoint B S hS (yoneda.obj T) xb (isAlgebraicSpace_yoneda B S hS T)).fiber.obj U) :
    (etaleSitePoint B S hS (yoneda.obj T) xb (isAlgebraicSpace_yoneda B S hS T)).toPresheafFiber
        U s ((representedImageOpenFunctor B S hS T).op ⋙ P) ≫
      (representedImagePresheafFiberIso B S hS T xb P).hom =
      TopCat.Presheaf.germ (X := ((BigFppfOver.toScheme B S hS).obj T).toTopCat) P
        ((representedImageOpenFunctor B S hS T).obj U) _
        (chartPoint_yonedaIdentityNeighborhood_mem B S hS T xb U s) :=
  Functor.Final.ι_colimitIso_hom (representedNeighborhoodFunctor B S hS T xb).op
    ((OpenNhds.inclusion _).op ⋙ P) (op (Functor.elementsMk _ U s))

/-- **The stalk of `ε⁻¹` at a geometric point (Stacks 05V1).**  For a sheaf of commutative
rings `N` on `X₀`, lifted to the universe of the étale site, the stalk of `ε⁻¹N` at the universe
lift of the point attached to `x̄` is the lift of the stalk `N_x` at the point `x` of `X₀` under
`x̄`. -/
noncomputable def representedInverseImageStalkIso
    (N : Sheaf (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      CommRingCat.{u}) :
    (((etaleSitePoint B S hS (yoneda.obj T) xb
        (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1}).presheafFiber
          (A := CommRingCat.{u + 1})).obj
        ((inverseImageCommRingFunctor (representedToZariskiMorphismOfTopoi B S hS T)).obj
          ((sheafCompose _ SheafOfModules.commRingCatULift.{u, u + 1}).obj N)).obj ≅
      SheafOfModules.commRingCatULift.{u, u + 1}.obj
        (TopCat.Presheaf.stalk (X := ((BigFppfOver.toScheme B S hS).obj T).toTopCat) N.obj
          (chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb))) :=
  haveI := W_isInvertedBy_representedImageRestrictionToInverseImage B S hS T
    ((sheafCompose _ SheafOfModules.commRingCatULift.{u, u + 1}).obj N)
    ((etaleSitePoint B S hS (yoneda.obj T) xb (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1})
  (asIso ((((etaleSitePoint B S hS (yoneda.obj T) xb
      (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1}).presheafFiber
        (A := CommRingCat.{u + 1})).map (representedImageRestrictionToInverseImage B S hS T
          ((sheafCompose _ SheafOfModules.commRingCatULift.{u, u + 1}).obj N)))).symm ≪≫
    Stacks.uliftRingFiberIso' _ ((representedImageOpenFunctor B S hS T).op ⋙ N.obj) ≪≫
    SheafOfModules.commRingCatULift.{u, u + 1}.mapIso
      (representedImagePresheafFiberIso B S hS T xb N.obj)

/-- `AlgebraicGeometry.Space.representedInverseImageStalkIso` on germs: the germ of `ε⁻¹N` at
a lift of `x̄` of the image of a section of `N` over the image open is the lift of the ordinary
germ of that section at `x`. -/
theorem representedInverseImageStalkIso_germ
    (N : Sheaf (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      CommRingCat.{u})
    (U : SmallEtale B S hS (yoneda.obj T))
    (s : (etaleSitePoint B S hS (yoneda.obj T) xb (isAlgebraicSpace_yoneda B S hS T)).fiber.obj U) :
    ((etaleSitePoint B S hS (yoneda.obj T) xb
        (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1}).toPresheafFiber U (ULift.up s) _ ≫
      ((((etaleSitePoint B S hS (yoneda.obj T) xb
        (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1}).presheafFiber
          (A := CommRingCat.{u + 1})).map (representedImageRestrictionToInverseImage B S hS T
          ((sheafCompose _ SheafOfModules.commRingCatULift.{u, u + 1}).obj N))) ≫
      (representedInverseImageStalkIso B S hS T xb N).hom =
      SheafOfModules.commRingCatULift.{u, u + 1}.map
        (TopCat.Presheaf.germ (X := ((BigFppfOver.toScheme B S hS).obj T).toTopCat) N.obj
          ((representedImageOpenFunctor B S hS T).obj U) _
          (chartPoint_yonedaIdentityNeighborhood_mem B S hS T xb U s)) := by
  have := W_isInvertedBy_representedImageRestrictionToInverseImage B S hS T
    ((sheafCompose _ SheafOfModules.commRingCatULift.{u, u + 1}).obj N)
    ((etaleSitePoint B S hS (yoneda.obj T) xb (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1})
  simp only [representedInverseImageStalkIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    IsIso.hom_inv_id_assoc]
  have h1 := Stacks.uliftRingFiberIso'_germ
    (etaleSitePoint B S hS (yoneda.obj T) xb (isAlgebraicSpace_yoneda B S hS T))
    ((representedImageOpenFunctor B S hS T).op ⋙ N.obj) U s
  have h2 := toPresheafFiber_representedImagePresheafFiberIso_hom B S hS T xb N.obj U s
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    ((Functor.map_comp _ _ _).symm.trans (congrArg _ h2)))

/-- The transpose under `AlgebraicGeometry.Space.representedRestrictionAdjunction`, over an
étale chart `U`: evaluate at the image open of `U`, then restrict along the unit
`U ⟶ ε(image of U)`. -/
theorem representedRestrictionAdjunction_homEquiv_symm_app
    (P : ((BigFppfOver.toScheme B S hS).obj T).Opensᵒᵖ ⥤ CommRingCat.{u + 1})
    (Q : (SmallEtale B S hS (yoneda.obj T))ᵒᵖ ⥤ CommRingCat.{u + 1})
    (β : P ⟶ (representedOpensToSmallEtale B S hS T).op ⋙ Q)
    (U : SmallEtale B S hS (yoneda.obj T)) :
    (((representedRestrictionAdjunction B S hS T).homEquiv P Q).symm β).app (op U) =
      β.app (op ((representedImageOpenFunctor B S hS T).obj U)) ≫
        Q.map ((representedImageOpenAdjunction B S hS T).unit.app U).op := by
  rw [Adjunction.homEquiv_counit]
  simp [Adjunction.whiskerLeft_counit_app_app]

/-- The comparison map followed by the inverse-image form of `ε♯` is the transpose of the
restriction form `AlgebraicGeometry.Space.representedZariskiSharp` of `ε♯`. -/
theorem representedImageRestrictionToInverseImage_comp_fSharpInverseImage :
    representedImageRestrictionToInverseImage B S hS T (representedZariskiRingedTopos B S hS T).O ≫
        (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage.hom =
      ((representedRestrictionAdjunction B S hS T).homEquiv _ _).symm
        (representedZariskiSharp B S hS T).hom := by
  refine (representedImageRestrictionToInverseImage_comp B S hS T _ _ _).trans
    (congrArg _ (congrArg InducedCategory.Hom.hom ?_))
  refine Eq.trans ?_ (representedToZariskiRingedToposHom_fSharp_comp B S hS T)
  exact congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)

/-- Over an étale chart `U`, the comparison map followed by the inverse-image form of `ε♯` sends
a lifted function on the image open of `U` to its restriction along the unit
`U ⟶ ε(image of U)`, read through `𝒪_{X₀}(W) = Γ(W, 𝒪_W)`. -/
theorem representedImageRestrictionToInverseImage_comp_fSharpInverseImage_app
    (U : SmallEtale B S hS (yoneda.obj T)) :
    (representedImageRestrictionToInverseImage B S hS T (representedZariskiRingedTopos B S hS T).O ≫
        (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage.hom).app (op U) =
      SheafOfModules.commRingCatULift.{u, u + 1}.map
          (Scheme.Opens.topIso ((representedImageOpenFunctor B S hS T).obj U)).inv ≫
        (smallEtaleStructureSheafULift B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).obj.map
          ((representedImageOpenAdjunction B S hS T).unit.app U).op := by
  rw [representedImageRestrictionToInverseImage_comp_fSharpInverseImage,
    ← representedZariskiSharp_hom_app]
  exact representedRestrictionAdjunction_homEquiv_symm_app B S hS T _ _ _ U

/-- The comparison map followed by the inverse-image form of `ε♯`, on a lifted section over the
image open of an étale chart. -/
theorem representedImageRestrictionToInverseImage_comp_fSharpInverseImage_app_apply
    (U : SmallEtale B S hS (yoneda.obj T))
    (a : Γ((BigFppfOver.toScheme B S hS).obj T, (representedImageOpenFunctor B S hS T).obj U)) :
    (representedImageRestrictionToInverseImage B S hS T (representedZariskiRingedTopos B S hS T).O ≫
        (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage.hom).app (op U)
        (ULift.up a) =
      (smallEtaleStructureSheafULift B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).obj.map
          ((representedImageOpenAdjunction B S hS T).unit.app U).op
        (ULift.up
          ((Scheme.Opens.topIso ((representedImageOpenFunctor B S hS T).obj U)).inv a)) := by
  rw [representedImageRestrictionToInverseImage_comp_fSharpInverseImage_app]
  rfl

/-- Every lift of `x̄` into the étale chart given by an open `W ∋ x` is the lift used by
`AlgebraicGeometry.Space.chartOpenNeighborhood`. -/
private theorem geometricFiber_representedOpensToSmallEtale_eq_aux
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hw : chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb) ∈ W)
    (q : GeometricFiber B S hS (yoneda.obj T) xb ((representedOpensToSmallEtale B S hS T).obj W)) :
    q.1 = (chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T xb) W hw).point := by
  let V₀ := yonedaIdentityNeighborhood T xb
  have hmono : ∀ p p' : xb.val.siteObject ⟶ chartOpenOver B S hS V₀.chart W,
      p ≫ chartOpenOverι B S hS V₀.chart W = p' ≫ chartOpenOverι B S hS V₀.chart W → p = p' := by
    intro p p' h
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (cancel_mono W.ι).1 (congrArg (fun k => k.left.hom) h)
  exact hmono _ _ (q.2.trans (chartOpenNeighborhood_point_comp B S hS V₀ W hw).symm)

/-- Transporting a lift of `x̄` into an étale chart `U` along the unit `U ⟶ ε(image of U)`
gives the lift of `x̄` into the Zariski open `image of U ⊆ X₀` used by
`AlgebraicGeometry.Space.chartOpenNeighborhood`. -/
theorem geometricFiber_map_representedImageOpenAdjunction_unit
    (U : SmallEtale B S hS (yoneda.obj T)) (s : GeometricFiber B S hS (yoneda.obj T) xb U) :
    ((etaleSitePoint B S hS (yoneda.obj T) xb (isAlgebraicSpace_yoneda B S hS T)).fiber.map
        ((representedImageOpenAdjunction B S hS T).unit.app U) s).1 =
      (chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T xb)
        ((representedImageOpenFunctor B S hS T).obj U)
        (chartPoint_yonedaIdentityNeighborhood_mem B S hS T xb U s)).point :=
  geometricFiber_representedOpensToSmallEtale_eq_aux B S hS T xb _ _ _

/-- **Lifts of `x̄` into a Zariski open of `X₀` are unique**: every lift of `x̄` into the étale
chart given by an open `W ∋ x` is the lift used by
`AlgebraicGeometry.Space.chartOpenNeighborhood`, the open immersion `W ⟶ X₀` being a
monomorphism. -/
theorem geometricFiber_representedOpensToSmallEtale_eq
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hw : chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb) ∈ W)
    (q : GeometricFiber B S hS (yoneda.obj T) xb ((representedOpensToSmallEtale B S hS T).obj W)) :
    q.1 = (chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T xb) W hw).point :=
  geometricFiber_representedOpensToSmallEtale_eq_aux B S hS T xb W hw q

/-- The germ in the étale local ring at a lift of `x̄` into the chart given by an open `W ∋ x`
is the germ at `AlgebraicGeometry.Space.chartOpenNeighborhood`: that lift is unique. -/
theorem etaleLocalRingGerm_representedOpensToSmallEtale
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hw : chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb) ∈ W)
    (q : GeometricFiber B S hS (yoneda.obj T) xb ((representedOpensToSmallEtale B S hS T).obj W))
    (a : (structurePresheaf B S hS (yoneda.obj T)).obj
      (op ((representedOpensToSmallEtale B S hS T).obj W))) :
    etaleLocalRingGerm B S hS (yoneda.obj T) xb (op ⟨_, q.1, q.2⟩) a =
      etaleLocalRingGerm B S hS (yoneda.obj T) xb
        (op (chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T xb) W hw)) a := by
  have hq := geometricFiber_representedOpensToSmallEtale_eq B S hS T xb W hw q
  obtain ⟨q, hq'⟩ := q
  simp only at hq
  subst hq
  rfl

/-- The canonical map `𝒪_{X₀, x} → 𝒪_{X, x̄}` of Stacks 05VP on the germ of a function `b` on an
open `W ∋ x` is the germ of `b` at any lift of `x̄` into the chart `W`. -/
theorem chartLocalRingToEtaleLocalRing_germ_representedOpens
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hw : chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb) ∈ W)
    (b : Γ((BigFppfOver.toScheme B S hS).obj T, W))
    (q : GeometricFiber B S hS (yoneda.obj T) xb ((representedOpensToSmallEtale B S hS T).obj W)) :
    etaleLocalRingGerm B S hS (yoneda.obj T) xb (op ⟨_, q.1, q.2⟩) ((Scheme.Opens.topIso W).inv b) =
      chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
        (yonedaIdentityNeighborhood T xb)
        (TopCat.Presheaf.germ (X := ((BigFppfOver.toScheme B S hS).obj T).toTopCat)
          ((BigFppfOver.toScheme B S hS).obj T).presheaf W _ hw b) :=
  (etaleLocalRingGerm_representedOpensToSmallEtale B S hS T xb W hw q _).trans
    (chartLocalRingToEtaleLocalRing_germ_open B S hS (isAlgebraicSpace_yoneda B S hS T)
      (yonedaIdentityNeighborhood T xb) W hw b).symm

/-- A ring homomorphism whose source and target are identified, through ring isomorphisms `e₀` and
`e`, with the lift of `𝒪_{X₀, x}` and with `𝒪_{X, x̄}`, and which becomes the canonical map of
Stacks 05VP, is a strict henselization up to ring isomorphisms of source and target. -/
private theorem exists_isHenselization_of_chartLocalRingToEtaleLocalRing
    (xb : GeometricPoint B S hS (yoneda.obj T)) {P₀ P : Type (u + 1)} [CommRing P₀] [CommRing P]
    (e₀ : P₀ ≃+* ULift.{u + 1}
      (chartLocalRing B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb)))
    (e : P ≃+* etaleLocalRing B S hS (yoneda.obj T) xb) (φ : P₀ →+* P)
    (hφ : ∀ y, e (φ y) = chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T) (yonedaIdentityNeighborhood T xb) (e₀ y).down) :
    ∃ (A₀ A : Type (u + 1)) (_ : CommRing A₀) (_ : CommRing A) (_ : IsLocalRing A₀)
      (_ : IsLocalRing A) (_ : Algebra A₀ A) (L : Type (u + 1)) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField A₀) L) (_ : IsLocalRing.IsHenselization A₀ L A)
      (e₀ : P₀ ≃+* A₀) (e : P ≃+* A), ∀ y, e (φ y) = algebraMap A₀ A (e₀ y) := by
  let hX := isAlgebraicSpace_yoneda B S hS T
  let V₀ := yonedaIdentityNeighborhood T xb
  let R₀ := chartLocalRing B S hS (yoneda.obj T) V₀
  let E := etaleLocalRing B S hS (yoneda.obj T) xb
  let c := chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T) hX V₀
  let hE : IsLocalRing E := isLocalRing_etaleLocalRing B S hS _ hX xb
  let : Algebra R₀ E := c.toAlgebra
  have : IsLocalRing.IsHenselization R₀
      (separableClosure (IsLocalRing.ResidueField R₀) (chartGeometricPoint V₀).residueField) E :=
    isHenselization_etaleLocalRing_chart B S hS hX V₀
  let σ : ULift.{u + 1} R₀ ≃+* R₀ := ULift.ringEquiv
  let hA₀ : IsLocalRing (ULift.{u + 1} R₀) := σ.symm.isLocalRing
  let alg : Algebra (ULift.{u + 1} R₀) E := (c.comp σ.toRingHom).toAlgebra
  have : IsLocalHom c := isLocalHom_chartLocalRingToEtaleLocalRing B S hS _ hX V₀
  have : IsLocalHom σ.toRingHom := ⟨fun _ h => (isLocalHom_equiv σ).map_nonunit _ h⟩
  have : IsLocalHom (algebraMap (ULift.{u + 1} R₀) E) :=
    RingHom.isLocalHom_comp c σ.toRingHom
  have hH := IsLocalRing.IsHenselization.residueField_of_ringEquiv
    (L := separableClosure (IsLocalRing.ResidueField R₀) (chartGeometricPoint V₀).residueField)
    (Rh := E) σ (fun _ => rfl)
  exact ⟨ULift.{u + 1} R₀, E, inferInstance, inferInstance, hA₀, hE, alg,
    IsLocalRing.ResidueField E, inferInstance, inferInstance, hH, e₀, e, hφ⟩

/-- **The stalk of `ε♯` at a geometric point is a strict henselization (Stacks 05V1, 04KF).**
At the universe lift of the point of the small étale site attached to a geometric point `x̄` of
`yoneda.obj T`, lying over the point `x` of `X₀`, the stalk of the inverse-image form
`ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` of the structure map of `ε` is, up to ring isomorphisms of source and target,
the canonical map `𝒪_{X₀, x} → 𝒪_{X, x̄}` of Stacks 05VP (lifted to the universe `u + 1`), which
is a strict henselization by Stacks 04KF. -/
theorem representedToZariskiRingedToposHom_stalk_isHenselization :
    ∃ (A₀ A : Type (u + 1)) (_ : CommRing A₀) (_ : CommRing A) (_ : IsLocalRing A₀)
      (_ : IsLocalRing A) (_ : Algebra A₀ A) (L : Type (u + 1)) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField A₀) L) (_ : IsLocalRing.IsHenselization A₀ L A)
      (e₀ : (((etaleSitePoint B S hS (yoneda.obj T) xb
          (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1}).presheafFiber
            (A := CommRingCat.{u + 1})).obj
          ((inverseImageCommRingFunctor
            (representedToZariskiRingedToposHom B S hS T).toToposHom).obj
              (representedZariskiRingedTopos B S hS T).O).obj ≃+* A₀)
      (e : (((etaleSitePoint B S hS (yoneda.obj T) xb
          (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1}).presheafFiber
            (A := CommRingCat.{u + 1})).obj
          (smallEtaleStructureSheafULift B S hS
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).obj ≃+* A),
      ∀ y, e ((((etaleSitePoint B S hS (yoneda.obj T) xb
          (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1}).presheafFiber
            (A := CommRingCat.{u + 1})).map
          (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage.hom y) =
        algebraMap A₀ A (e₀ y) := by
  let hX := isAlgebraicSpace_yoneda B S hS T
  let Φ₀ := etaleSitePoint B S hS (yoneda.obj T) xb hX
  let Φ := Φ₀.ulift.{u + 1}
  let V₀ := yonedaIdentityNeighborhood T xb
  let c := chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T) hX V₀
  let ρ := representedImageRestrictionToInverseImage B S hS T
    (representedZariskiRingedTopos B S hS T).O
  have : IsIso ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map ρ) :=
    W_isInvertedBy_representedImageRestrictionToInverseImage B S hS T _ Φ
  let e₀ := (representedInverseImageStalkIso B S hS T xb
    ((BigFppfOver.toScheme B S hS).obj T).sheaf).commRingCatIsoToRingEquiv
  let e := smallEtaleStructureSheafULiftStalkEquiv B S hS ⟨yoneda.obj T, hX⟩ xb
  have key : ∀ y, e ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map
      (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage.hom y) = c (e₀ y).down := by
    intro y
    obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map ρ)).2 y
    obtain ⟨U, ⟨s⟩, ⟨a⟩, rfl⟩ := Φ.toPresheafFiber_jointly_surjective z
    let g := (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage
    let Rx := smallEtaleStructureSheafULift B S hS ⟨yoneda.obj T, hX⟩
    let G := representedImageOpenFunctor B S hS T
    let η := (representedImageOpenAdjunction B S hS T).unit.app U
    let hw := chartPoint_yonedaIdentityNeighborhood_mem B S hS T xb U s
    -- the left-hand side: the germ of the image section
    have h1 : (Φ.presheafFiber (A := CommRingCat.{u + 1})).map g.hom
        ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map ρ
          (Φ.toPresheafFiber U (ULift.up s)
            ((representedImageOpenFunctor B S hS T).op ⋙
              (representedZariskiRingedTopos B S hS T).O.obj) (ULift.up a))) =
        Φ.toPresheafFiber U (ULift.up s) Rx.obj ((ρ ≫ g.hom).app (op U) (ULift.up a)) :=
      (ConcreteCategory.congr_hom
        ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map_comp ρ g.hom).symm _).trans
        (Φ.toPresheafFiber_naturality_apply (ρ ≫ g.hom) U (ULift.up s) (ULift.up a))
    have h2 : (ρ ≫ g.hom).app (op U) (ULift.up a) = Rx.obj.map η.op
        (ULift.up ((Scheme.Opens.topIso (G.obj U)).inv a)) :=
      representedImageRestrictionToInverseImage_comp_fSharpInverseImage_app_apply B S hS T U a
    have h3 := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w η (ULift.up s) Rx.obj)
      (ULift.up ((Scheme.Opens.topIso (G.obj U)).inv a))
    have h4 := smallEtaleStructureSheafULiftStalkEquiv_germ B S hS ⟨yoneda.obj T, hX⟩ xb
      ((representedOpensToSmallEtale B S hS T).obj (G.obj U)) (Φ₀.fiber.map η s)
      ((Scheme.Opens.topIso (G.obj U)).inv a)
    -- the right-hand side: the canonical map on the ordinary germ
    have h5 := ConcreteCategory.congr_hom (representedInverseImageStalkIso_germ B S hS T xb
      ((BigFppfOver.toScheme B S hS).obj T).sheaf U s) (ULift.up a)
    have h6 := chartLocalRingToEtaleLocalRing_germ_open B S hS hX V₀ (G.obj U) hw a
    refine Eq.trans (congrArg (smallEtaleStructureSheafULiftStalkEquiv B S hS ⟨yoneda.obj T, hX⟩ xb)
      (h1.trans (congrArg _ h2))) ?_
    refine Eq.trans (congrArg (smallEtaleStructureSheafULiftStalkEquiv B S hS ⟨yoneda.obj T, hX⟩ xb)
      h3) ?_
    refine Eq.trans h4 ?_
    refine Eq.trans ?_ (congrArg (fun z => c z.down) h5.symm)
    refine Eq.trans ?_ h6.symm
    exact etaleLocalRingGerm_representedOpensToSmallEtale B S hS T xb (G.obj U) hw _ _
  exact exists_isHenselization_of_chartLocalRingToEtaleLocalRing B S hS T xb e₀ e _ key

omit xb in
/-- **The stalks of `ε♯` along the geometric points are strict henselizations.**  At every
point of the conservative family of universe lifts of the points of the small étale site
attached to the geometric points of `yoneda.obj T`
(`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_uliftEtaleSitePoint`), the stalk of the
inverse-image form `ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` of the structure map of `ε` is a henselization of the local
ring of its source, up to ring isomorphisms of source and target: this is
`AlgebraicGeometry.Space.representedToZariskiRingedToposHom_stalk_isHenselization` at each
geometric point. -/
theorem representedToZariskiRingedToposHom_stalk_isHenselization_of_mem
    (Φ : (SmallEtale.topology B S hS (yoneda.obj T)).Point.{u + 1})
    (hΦ : ObjectProperty.ofObj (fun x : GeometricPoint B S hS (yoneda.obj T) =>
      (etaleSitePoint B S hS (yoneda.obj T) x
        (isAlgebraicSpace_yoneda B S hS T)).ulift.{u + 1}) Φ) :
    ∃ (A₀ A : Type (u + 1)) (_ : CommRing A₀) (_ : CommRing A) (_ : IsLocalRing A₀)
      (_ : IsLocalRing A) (_ : Algebra A₀ A) (L : Type (u + 1)) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField A₀) L) (_ : IsLocalRing.IsHenselization A₀ L A)
      (e₀ : (Φ.presheafFiber (A := CommRingCat.{u + 1})).obj
          ((inverseImageCommRingFunctor
            (representedToZariskiRingedToposHom B S hS T).toToposHom).obj
              (representedZariskiRingedTopos B S hS T).O).obj ≃+* A₀)
      (e : (Φ.presheafFiber (A := CommRingCat.{u + 1})).obj
          (smallEtaleStructureSheafULift B S hS
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).obj ≃+* A),
      ∀ y, e ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map
          (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage.hom y) =
        algebraMap A₀ A (e₀ y) := by
  obtain ⟨xb⟩ := hΦ
  exact representedToZariskiRingedToposHom_stalk_isHenselization B S hS T xb

/-! ### The stalks of the base map of the square of Remark 08GH -/

section Square

variable {T₁ T₂ : BigFppfOver B S hS} (h : T₁ ⟶ T₂)

/-- A lifted morphism of sheaves of commutative rings, followed by any map, on a lifted section:
the lift is computed sectionwise. -/
private theorem sheafCompose_commRingCatULift_map_comp_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose SheafOfModules.commRingCatULift.{u, u + 1}]
    {P P' : Sheaf J CommRingCat.{u}} (φ : P ⟶ P') (W : Cᵒᵖ) {Z : CommRingCat.{u + 1}}
    (m : SheafOfModules.commRingCatULift.{u, u + 1}.obj (P'.obj.obj W) ⟶ Z)
    (c : P.obj.obj W) :
    (((sheafCompose J SheafOfModules.commRingCatULift.{u, u + 1}).map φ).hom.app W ≫ m)
        (ULift.up c) = m (ULift.up (φ.hom.app W c)) :=
  rfl

/-- Sections of a composite of three morphisms of sheaves of commutative rings. -/
private theorem sheafHom_comp_comp_app_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P Q R W : Sheaf J CommRingCat.{u}} (a : P ⟶ Q) (m : Q ⟶ R)
    (r : R ⟶ W) (V : Cᵒᵖ) (b : P.obj.obj V) :
    (a ≫ m ≫ r).hom.app V b = r.hom.app V (m.hom.app V (a.hom.app V b)) :=
  rfl

/-- Restriction along the geometric half of the square of Remark 08GH is, over an open `V` of
`Y₀`, restriction along the comparison `f₀⁻¹V ⟶ X ×_Y V` of étale charts. -/
theorem representedBaseChangeRestriction_app_hom_app
    (G : Sheaf (SmallEtale.topology B S hS (yoneda.obj T₁)) CommRingCat.{u})
    (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens) :
    ((representedBaseChangeRestriction B S hS h).app G).hom.app (op V) =
      G.obj.map ((representedOpensBaseChangeIso B S hS h).hom.app V).op := by
  rfl

/-- `AlgebraicGeometry.Space.representedBaseSharp` on a section `b` of `𝒪_{Y₀}` over `V`: view
`b` as a function on the chart `V` of `yoneda.obj T₂`, take its image under the unit of
`f⁻¹ ⊣ f_*` on the base change `X ×_Y V`, and restrict it to the chart `f₀⁻¹V` of
`yoneda.obj T₁` along the geometric half of the square. -/
theorem representedBaseSharp_hom_app_apply (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens)
    (b : Γ((BigFppfOver.toScheme B S hS).obj T₂, V)) :
    (representedBaseSharp B S hS h).hom.app (op V) b =
      ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h)).toToposHom).obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O).obj.map
        ((representedOpensBaseChangeIso B S hS h).hom.app V).op
        (((((commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toToposHom).homEquiv
            _ _ (𝟙 _)) ≫ (chartComparisonCommRing B S hS (representedSpaceMap B S hS h)
              (relativelyRepresentable_yoneda_map B S hS h)).hom.app _).hom.app
          (op ((representedOpensToSmallEtale B S hS T₂).obj V)))
          ((Scheme.Opens.topIso V).inv b)) := by
  refine (sheafHom_comp_comp_app_apply _ _ _ _ _).trans ?_
  refine (ConcreteCategory.congr_hom
    (representedBaseChangeRestriction_app_hom_app B S hS h _ V) _).trans ?_
  rfl

/-- The comparison map followed by the base map of the square of Remark 08GH, over an étale
chart `U` of `yoneda.obj T₁`: the lift of `AlgebraicGeometry.Space.representedBaseMapU` over the
image open of `U`, followed by restriction along the unit `U ⟶ ε(image of U)`. -/
theorem representedImageRestrictionToInverseImage_comp_baseMap_app
    (U : SmallEtale B S hS (yoneda.obj T₁)) :
    (representedImageRestrictionToInverseImage B S hS T₁
        ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          SheafOfModules.commRingCatULift.{u, u + 1}).obj
          ((inverseImageCommRingFunctor
            (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
            ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O)) ≫
        (representedBaseMap B S hS h).hom).app (op U) =
      ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          SheafOfModules.commRingCatULift.{u, u + 1}).map (representedBaseMapU B S hS h)).hom.app
            (op ((representedImageOpenFunctor B S hS T₁).obj U)) ≫
        ((SheafOfModules.sheafULift.{u, u + 1, u}
            (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
          ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toToposHom).obj
            (smallEtaleRingedTopos B S hS
              ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)).obj.map
          ((representedImageOpenAdjunction B S hS T₁).unit.app U).op := by
  let JZ := Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁)
  let JE := SmallEtale.topology B S hS (yoneda.obj T₁)
  let M := (sheafCompose JZ SheafOfModules.commRingCatULift.{u, u + 1}).obj
    ((inverseImageCommRingFunctor
      (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
      ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O)
  let Q := (SheafOfModules.sheafULift.{u, u + 1, u} JE).obj
    ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)
  let rI := restrictionCommRingIso JZ JE (representedOpensToSmallEtale B S hS T₁) Q
  let X := (sheafCompose JZ SheafOfModules.commRingCatULift.{u, u + 1}).map
    (representedBaseMapU B S hS h)
  have h1 := representedImageRestrictionToInverseImage_comp B S hS T₁ M Q
    (representedBaseMap B S hS h)
  have h2 : (commRingImageAdjunction (representedToZariskiMorphismOfTopoi B S hS T₁)).homEquiv M Q
      (representedBaseMap B S hS h) ≫ rI.hom = X :=
    (congrArg (· ≫ rI.hom) (Equiv.apply_symm_apply _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (X ≫ ·) rI.inv_hom_id).trans (Category.comp_id _)))
  refine (NatTrans.congr_app h1 (op U)).trans ?_
  refine (NatTrans.congr_app (congrArg (fun k : M ⟶ (representedOpensToSmallEtale B S hS
    T₁).sheafPushforwardContinuous CommRingCat.{u + 1} JZ JE |>.obj Q =>
      ((representedRestrictionAdjunction B S hS T₁).homEquiv M.obj
        ((sheafToPresheaf JE CommRingCat.{u + 1}).obj Q)).symm k.hom) h2) (op U)).trans ?_
  exact representedRestrictionAdjunction_homEquiv_symm_app B S hS T₁ _ _ _ U

/-- `AlgebraicGeometry.Space.representedImageRestrictionToInverseImage_comp_baseMap_app` on a
lifted section over the image open. -/
theorem representedImageRestrictionToInverseImage_comp_baseMap_app_apply
    (U : SmallEtale B S hS (yoneda.obj T₁))
    (c : ((inverseImageCommRingFunctor
      (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
        ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O).obj.obj
          (op ((representedImageOpenFunctor B S hS T₁).obj U))) :
    (representedImageRestrictionToInverseImage B S hS T₁
        ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          SheafOfModules.commRingCatULift.{u, u + 1}).obj
          ((inverseImageCommRingFunctor
            (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
            ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O)) ≫
        (representedBaseMap B S hS h).hom).app (op U) (ULift.up c) =
      ((SheafOfModules.sheafULift.{u, u + 1, u}
            (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
          ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toToposHom).obj
            (smallEtaleRingedTopos B S hS
              ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)).obj.map
          ((representedImageOpenAdjunction B S hS T₁).unit.app U).op
        (ULift.up ((representedBaseMapU B S hS h).hom.app
          (op ((representedImageOpenFunctor B S hS T₁).obj U)) c)) := by
  refine (ConcreteCategory.congr_hom
    (representedImageRestrictionToInverseImage_comp_baseMap_app B S hS h U) (ULift.up c)).trans ?_
  exact sheafCompose_commRingCatULift_map_comp_apply (representedBaseMapU B S hS h)
    (op ((representedImageOpenFunctor B S hS T₁).obj U))
    (((SheafOfModules.sheafULift.{u, u + 1, u}
            (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
          ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toToposHom).obj
            (smallEtaleRingedTopos B S hS
              ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)).obj.map
          ((representedImageOpenAdjunction B S hS T₁).unit.app U).op) c

/-- `AlgebraicGeometry.Space.representedBaseMapU` on the image of a section `b` of `𝒪_{Y₀}` over
`V` under the unit of `f₀⁻¹ ⊣ f₀,*` is `AlgebraicGeometry.Space.representedBaseSharp` on `b`. -/
theorem representedBaseMapU_hom_app_unit (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens)
    (b : Γ((BigFppfOver.toScheme B S hS).obj T₂, V)) :
    (representedBaseMapU B S hS h).hom.app (op (((BigFppfOver.toScheme B S hS).map h) ⁻¹ᵁ V))
        ((((Scheme.Hom.zariskiInverseImageAdjunction ((BigFppfOver.toScheme B S hS).map h)).homEquiv
          _ _ (𝟙 _)).hom.app (op V)) b) =
      (representedBaseSharp B S hS h).hom.app (op V) b := by
  let f₀ := (BigFppfOver.toScheme B S hS).map h
  let JY := Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂)
  let JX := Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁)
  let adj := commRingImageAdjunction (Scheme.Hom.zariskiRingedToposHom f₀).toToposHom
  let rN := restrictionCommRingNatIso JY JX (Opens.map f₀.base)
  let O := ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O
  let G := ((representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u}
    JX (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
    ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)
  have key : (adj.ofNatIsoRight rN).homEquiv O _ (𝟙 _) ≫
      ((Opens.map f₀.base).sheafPushforwardContinuous CommRingCat.{u} JY JX).map
        (representedBaseMapU B S hS h) = representedBaseSharp B S hS h := by
    refine ((adj.ofNatIsoRight rN).homEquiv_naturality_right (𝟙 _)
      (representedBaseMapU B S hS h)).symm.trans ?_
    refine (congrArg _ (Category.id_comp _)).trans ?_
    refine (Adjunction.homEquiv_ofNatIsoRight_apply adj rN _).trans ?_
    refine (congrArg (· ≫ rN.hom.app G) (Equiv.apply_symm_apply _ _)).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (restrictionCommRingIso JY JX (Opens.map f₀.base) G).inv_hom_id).trans (Category.comp_id _))
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom key)
    (op V)) b

variable (xb : GeometricPoint B S hS (yoneda.obj T₁))

/-- The source of the stalk of `AlgebraicGeometry.Space.representedBaseMap` at the point attached
to `x̄`: the stalk of `ε⁻¹f₀⁻¹𝒪_{Y₀}` is the lift of `𝒪_{Y₀, y}`, `y` the image in `Y₀` of the
point `x` of `X₀` under `x̄` (Stacks 05V1, twice). -/
noncomputable def representedBaseMapSourceStalkEquiv :
    (((etaleSitePoint B S hS (yoneda.obj T₁) xb
      (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
        (A := CommRingCat.{u + 1})).obj
      ((representedToZariskiRingedToposHom B S hS T₁).toToposHom.inverseImageRing.obj
        ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          SheafOfModules.commRingCatULift.{u, u + 1}).obj
          ((inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom
            ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
            ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O))).obj ≃+*
      ULift.{u + 1} (chartLocalRing B S hS (yoneda.obj T₂)
        (yonedaIdentityNeighborhood T₂
          (geometricPointMap (representedSpaceMap B S hS h).hom xb))) :=
  ((representedInverseImageStalkIso B S hS T₁ xb
      ((inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom
        ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
        ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O)) ≪≫
    SheafOfModules.commRingCatULift.{u, u + 1}.mapIso
      (Scheme.Hom.zariskiInverseImageStalkIso ((BigFppfOver.toScheme B S hS).map h)
        ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O
        (chartPoint B S hS (yoneda.obj T₁)
          (yonedaIdentityNeighborhood T₁ xb)))).commRingCatIsoToRingEquiv

/-- The germ in the stalk of `ε⁻¹f₀⁻¹𝒪_{Y₀}` at the point attached to `x̄` of a function `b` on
an open `V ∋ y` of `Y₀`: the image of `b` in `f₀⁻¹𝒪_{Y₀}(f₀⁻¹V)`, restricted to the image open of
the chart `f₀⁻¹V` and carried into `ε⁻¹` by the comparison map. -/
noncomputable def representedBaseMapSourceGerm (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens)
    (hy : (BigFppfOver.toScheme B S hS).map h
      (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)) ∈ V)
    (b : Γ((BigFppfOver.toScheme B S hS).obj T₂, V)) :
    (((etaleSitePoint B S hS (yoneda.obj T₁) xb
      (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
        (A := CommRingCat.{u + 1})).obj
      ((representedToZariskiRingedToposHom B S hS T₁).toToposHom.inverseImageRing.obj
        ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          SheafOfModules.commRingCatULift.{u, u + 1}).obj
          ((inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom
            ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
            ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O))).obj :=
  let hX₁ := isAlgebraicSpace_yoneda B S hS T₁
  let f₀ := (BigFppfOver.toScheme B S hS).map h
  let Φ₀ := etaleSitePoint B S hS (yoneda.obj T₁) xb hX₁
  let Φ := Φ₀.ulift.{u + 1}
  let F₁ := representedOpensToSmallEtale B S hS T₁
  let G₁ := representedImageOpenFunctor B S hS T₁
  let x := chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)
  let N := (inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom f₀).toToposHom).obj
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O
  let M := (sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
    SheafOfModules.commRingCatULift.{u, u + 1}).obj N
  let ρ := representedImageRestrictionToInverseImage B S hS T₁ M
  let unitZ := (Scheme.Hom.zariskiInverseImageAdjunction f₀).homEquiv
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O N (𝟙 N)
  let W := f₀ ⁻¹ᵁ V
  have hx : x ∈ W := hy
  let Nx := chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T₁ xb) W hx
  let U := F₁.obj W
  let s : Φ₀.fiber.obj U := ⟨Nx.point, Nx.point_comp⟩
  let res : G₁.obj U ⟶ W := (representedImageOpenAdjunction B S hS T₁).counit.app W
  let c' := N.obj.map res.op (unitZ.hom.app (op V) b)
  (Φ.presheafFiber (A := CommRingCat.{u + 1})).map ρ
    (Φ.toPresheafFiber U (ULift.up s) (G₁.op ⋙ M.obj) (ULift.up c'))

/-- `AlgebraicGeometry.Space.representedBaseMapSourceStalkEquiv` sends the germ of `b` to the
germ of `b` at `y`. -/
theorem representedBaseMapSourceStalkEquiv_germ (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens)
    (hy : (BigFppfOver.toScheme B S hS).map h
      (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)) ∈ V)
    (b : Γ((BigFppfOver.toScheme B S hS).obj T₂, V)) :
    representedBaseMapSourceStalkEquiv B S hS h xb
        (representedBaseMapSourceGerm B S hS h xb V hy b) =
      ULift.up (TopCat.Presheaf.germ (X := ((BigFppfOver.toScheme B S hS).obj T₂).toTopCat)
        ((BigFppfOver.toScheme B S hS).obj T₂).presheaf V
        ((BigFppfOver.toScheme B S hS).map h
          (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb))) hy b) := by
  let hX₁ := isAlgebraicSpace_yoneda B S hS T₁
  let f₀ := (BigFppfOver.toScheme B S hS).map h
  let Φ₀ := etaleSitePoint B S hS (yoneda.obj T₁) xb hX₁
  let F₁ := representedOpensToSmallEtale B S hS T₁
  let G₁ := representedImageOpenFunctor B S hS T₁
  let x := chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)
  let N := (inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom f₀).toToposHom).obj
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O
  let unitZ := (Scheme.Hom.zariskiInverseImageAdjunction f₀).homEquiv
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O N (𝟙 N)
  let W := f₀ ⁻¹ᵁ V
  have hx : x ∈ W := hy
  let Nx := chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T₁ xb) W hx
  let U := F₁.obj W
  let s : Φ₀.fiber.obj U := ⟨Nx.point, Nx.point_comp⟩
  let res : G₁.obj U ⟶ W := (representedImageOpenAdjunction B S hS T₁).counit.app W
  let c' := N.obj.map res.op (unitZ.hom.app (op V) b)
  let I₂ := Scheme.Hom.zariskiInverseImageStalkIso f₀
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O x
  have hmem := chartPoint_yonedaIdentityNeighborhood_mem B S hS T₁ xb U s
  have h1 := ConcreteCategory.congr_hom
    (representedInverseImageStalkIso_germ B S hS T₁ xb N U s) (ULift.up c')
  have h2 : TopCat.Presheaf.germ (X := ((BigFppfOver.toScheme B S hS).obj T₁).toTopCat) N.obj
      (G₁.obj U) x hmem c' =
      TopCat.Presheaf.germ (X := ((BigFppfOver.toScheme B S hS).obj T₁).toTopCat) N.obj W x hx
        (unitZ.hom.app (op V) b) :=
    TopCat.Presheaf.germ_res_apply _ res x hmem _
  have h3 := ConcreteCategory.congr_hom (Scheme.Hom.germ_zariskiInverseImageStalkIso_inv f₀
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O x V hy) b
  refine (congrArg (fun w => SheafOfModules.commRingCatULift.{u, u + 1}.map I₂.hom w) h1).trans ?_
  refine congrArg ULift.up ((congrArg I₂.hom h2).trans ?_)
  exact (congrArg I₂.hom h3.symm).trans (ConcreteCategory.congr_hom I₂.inv_hom_id _)

/-- **The stalk of the base map on germs.**  The stalk of
`AlgebraicGeometry.Space.representedBaseMap` at the point attached to `x̄`, read in the étale local
ring of `Y` at `f(x̄)` (Stacks 04K2 (4)), sends the germ of a function `b` on an open `V ∋ y` of
`Y₀` to the image of the germ of `b` at `y` under the canonical map of Stacks 05VP. -/
theorem representedBaseMap_stalk_germ (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens)
    (hy : (BigFppfOver.toScheme B S hS).map h
      (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)) ∈ V)
    (b : Γ((BigFppfOver.toScheme B S hS).obj T₂, V)) :
    smallEtaleInverseImageStructureSheafULiftStalkEquiv B S hS (representedSpaceMap B S hS h)
        (relativelyRepresentable_yoneda_map B S hS h) xb
        ((((etaleSitePoint B S hS (yoneda.obj T₁) xb
          (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
            (A := CommRingCat.{u + 1})).map (representedBaseMap B S hS h).hom
          (representedBaseMapSourceGerm B S hS h xb V hy b)) =
      chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T₂) (isAlgebraicSpace_yoneda B S hS T₂)
        (yonedaIdentityNeighborhood T₂ (geometricPointMap (representedSpaceMap B S hS h).hom xb))
        (TopCat.Presheaf.germ (X := ((BigFppfOver.toScheme B S hS).obj T₂).toTopCat)
        ((BigFppfOver.toScheme B S hS).obj T₂).presheaf V
        ((BigFppfOver.toScheme B S hS).map h
          (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb))) hy b) := by
  let f := representedSpaceMap B S hS h
  let hf := relativelyRepresentable_yoneda_map B S hS h
  let f₀ := (BigFppfOver.toScheme B S hS).map h
  let yb := geometricPointMap f.hom xb
  let Φ₀ := etaleSitePoint B S hS (yoneda.obj T₁) xb (isAlgebraicSpace_yoneda B S hS T₁)
  let Φ := Φ₀.ulift.{u + 1}
  let F₁ := representedOpensToSmallEtale B S hS T₁
  let G₁ := representedImageOpenFunctor B S hS T₁
  let N := (inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom f₀).toToposHom).obj
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O
  let M := (sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
    SheafOfModules.commRingCatULift.{u, u + 1}).obj N
  let ρ := representedImageRestrictionToInverseImage B S hS T₁ M
  let OY := (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O
  let Pf := (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj OY
  let Rt := (SheafOfModules.sheafULift.{u, u + 1, u}
    (SmallEtale.topology B S hS (yoneda.obj T₁))).obj Pf
  let unitZ := (Scheme.Hom.zariskiInverseImageAdjunction f₀).homEquiv
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O N (𝟙 N)
  let W := f₀ ⁻¹ᵁ V
  let Nx := chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T₁ xb) W hy
  let U := F₁.obj W
  let s : Φ₀.fiber.obj U := ⟨Nx.point, Nx.point_comp⟩
  let res : G₁.obj U ⟶ W := (representedImageOpenAdjunction B S hS T₁).counit.app W
  let c' := N.obj.map res.op (unitZ.hom.app (op V) b)
  let z₀ := representedBaseMapSourceGerm B S hS h xb V hy b
  let e := smallEtaleInverseImageStructureSheafULiftStalkEquiv B S hS f hf xb
  -- the image of the germ
  let g := representedBaseMap B S hS h
  let η := (representedImageOpenAdjunction B S hS T₁).unit.app U
  let FY := representedOpensToSmallEtale B S hS T₂
  let k := (representedOpensBaseChangeIso B S hS h).hom.app V
  let t := (Scheme.Opens.topIso V).inv b
  let adjF := smallBaseChangeInverseImageAdjunction B S hS f hf
  let w := (adjF.homEquiv OY Pf (𝟙 _)).hom.app (op (FY.obj V)) t
  have l1 : (Φ.presheafFiber (A := CommRingCat.{u + 1})).map g.hom z₀ =
      Φ.toPresheafFiber U (ULift.up s) Rt.obj ((ρ ≫ g.hom).app (op U) (ULift.up c')) :=
    (ConcreteCategory.congr_hom
      ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map_comp ρ g.hom).symm _).trans
      (Φ.toPresheafFiber_naturality_apply (ρ ≫ g.hom) U (ULift.up s) (ULift.up c'))
  have l12 := l1.trans (congrArg (Φ.toPresheafFiber U (ULift.up s) Rt.obj)
    (representedImageRestrictionToInverseImage_comp_baseMap_app_apply B S hS h U c'))
  have l3 : (representedBaseMapU B S hS h).hom.app (op (G₁.obj U)) c' =
      Pf.obj.map (F₁.map res).op
        ((representedBaseMapU B S hS h).hom.app (op W) (unitZ.hom.app (op V) b)) :=
    NatTrans.naturality_apply (representedBaseMapU B S hS h).hom res.op _
  have l4 := representedBaseMapU_hom_app_unit B S hS h V b
  have l5 := representedBaseSharp_hom_app_apply B S hS h V b
  have l5' : ((((commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS f).toToposHom).homEquiv OY Pf (𝟙 _)) ≫
          (chartComparisonCommRing B S hS f hf).hom.app Pf).hom.app (op (FY.obj V))) t = w :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom
      (Adjunction.homEquiv_ofNatIsoRight_apply (commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS f).toToposHom) (chartComparisonCommRing B S hS f hf)
        (𝟙 ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
          OY))).symm) (op (FY.obj V))) t
  let t₁ := Φ.fiber.map η (ULift.up s)
  let t₂ := Φ.fiber.map (F₁.map res) t₁
  let pX : GeometricFiber B S hS (yoneda.obj T₁) xb
      ((smallBaseChange B S hS f hf).obj (FY.obj V)) := (Φ.fiber.map k t₂).down
  have hv : ULift.up ((representedBaseMapU B S hS h).hom.app (op (G₁.obj U)) c') =
      Rt.obj.map (F₁.map res).op (Rt.obj.map k.op (ULift.up.{u + 1} w)) :=
    (congrArg ULift.up (l3.trans (congrArg _ (l4.trans (l5.trans (congrArg _ l5')))))).trans rfl
  refine (congrArg e l12).trans ?_
  refine (congrArg e (Φ.toPresheafFiber_w_apply η (ULift.up s) Rt.obj _)).trans ?_
  refine (congrArg (fun v => e (Φ.toPresheafFiber _ t₁ Rt.obj v)) hv).trans ?_
  refine (congrArg e (Φ.toPresheafFiber_w_apply (F₁.map res) t₁ Rt.obj _)).trans ?_
  refine (congrArg e (Φ.toPresheafFiber_w_apply k t₂ Rt.obj _)).trans ?_
  refine (smallEtaleInverseImageStructureSheafULiftStalkEquiv_germ B S hS f hf xb (FY.obj V) pX
    t).trans ?_
  exact chartLocalRingToEtaleLocalRing_germ_representedOpens B S hS T₂ yb V hy b
    ((smallBaseChangeFiberMap B S hS f hf xb).app (FY.obj V) pX)

/-- **The stalk of the base map of the square of Remark 08GH at a geometric point is a strict
henselization (Stacks 05V1, 04K2, 04KF).**  At the universe lift of the point of the small étale
site attached to a geometric point `x̄` of `X = yoneda.obj T₁`, with image `ȳ = f(x̄)` lying
over the point `y = f₀(x)` of `Y₀`, the stalk of the canonical map
`AlgebraicGeometry.Space.representedBaseMap : ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y` is, up to ring
isomorphisms of source and target, the canonical map `𝒪_{Y₀, y} → 𝒪_{Y, ȳ}` of Stacks 05VP
(lifted to the universe `u + 1`), which is a strict henselization by Stacks 04KF. -/
theorem representedBaseMap_stalk_isHenselization :
    ∃ (A₀ A : Type (u + 1)) (_ : CommRing A₀) (_ : CommRing A) (_ : IsLocalRing A₀)
      (_ : IsLocalRing A) (_ : Algebra A₀ A) (L : Type (u + 1)) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField A₀) L) (_ : IsLocalRing.IsHenselization A₀ L A)
      (e₀ : (((etaleSitePoint B S hS (yoneda.obj T₁) xb
          (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
            (A := CommRingCat.{u + 1})).obj
          ((representedToZariskiRingedToposHom B S hS T₁).toToposHom.inverseImageRing.obj
            ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
              SheafOfModules.commRingCatULift.{u, u + 1}).obj
              ((inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom
                ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
                ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O))).obj ≃+* A₀)
      (e : (((etaleSitePoint B S hS (yoneda.obj T₁) xb
          (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
            (A := CommRingCat.{u + 1})).obj
          ((SheafOfModules.sheafULift.{u, u + 1, u}
            (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
            ((smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS h)).toToposHom.inverseImageRing.obj
              (smallEtaleRingedTopos B S hS
                ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)).obj ≃+* A),
      ∀ y, e ((((etaleSitePoint B S hS (yoneda.obj T₁) xb
          (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
            (A := CommRingCat.{u + 1})).map (representedBaseMap B S hS h).hom y) =
        algebraMap A₀ A (e₀ y) := by
  let f := representedSpaceMap B S hS h
  let hf := relativelyRepresentable_yoneda_map B S hS h
  let yb := geometricPointMap f.hom xb
  let e₀ := representedBaseMapSourceStalkEquiv B S hS h xb
  let e := smallEtaleInverseImageStructureSheafULiftStalkEquiv B S hS f hf xb
  have key : ∀ z, e ((((etaleSitePoint B S hS (yoneda.obj T₁) xb
      (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
        (A := CommRingCat.{u + 1})).map (representedBaseMap B S hS h).hom z) =
      chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T₂) (isAlgebraicSpace_yoneda B S hS T₂)
        (yonedaIdentityNeighborhood T₂ yb) (e₀ z).down := by
    intro z
    choose V hy b hb using TopCat.Presheaf.exists_germ_eq
      (X := ((BigFppfOver.toScheme B S hS).obj T₂).toTopCat)
      ((BigFppfOver.toScheme B S hS).obj T₂).presheaf (e₀ z).down
    have hz : e₀ z = ULift.up (TopCat.Presheaf.germ
        (X := ((BigFppfOver.toScheme B S hS).obj T₂).toTopCat)
        ((BigFppfOver.toScheme B S hS).obj T₂).presheaf V _ hy b) := ULift.ext hb.symm
    have hz' : z = representedBaseMapSourceGerm B S hS h xb V hy b :=
      (e₀.symm_apply_apply z).symm.trans (e₀.symm_apply_eq.mpr
        (hz.trans (representedBaseMapSourceStalkEquiv_germ B S hS h xb V hy b).symm))
    refine (congrArg (fun z' => e ((((etaleSitePoint B S hS (yoneda.obj T₁) xb
      (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
        (A := CommRingCat.{u + 1})).map (representedBaseMap B S hS h).hom z')) hz').trans ?_
    exact (representedBaseMap_stalk_germ B S hS h xb V hy b).trans
      (congrArg (fun w => chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T₂)
        (isAlgebraicSpace_yoneda B S hS T₂) (yonedaIdentityNeighborhood T₂ yb) (ULift.down w))
        hz.symm)
  exact exists_isHenselization_of_chartLocalRingToEtaleLocalRing B S hS T₂ yb e₀ e _ key

omit xb in
/-- **The stalks of the base map along the geometric points are strict henselizations.**  At
every point of the conservative family of universe lifts of the points of the small étale site
attached to the geometric points of `yoneda.obj T₁`, the stalk of
`AlgebraicGeometry.Space.representedBaseMap` is a henselization of the local ring of its source,
up to ring isomorphisms of source and target: this is
`AlgebraicGeometry.Space.representedBaseMap_stalk_isHenselization` at each geometric point. -/
theorem representedBaseMap_stalk_isHenselization_of_mem
    (Φ : (SmallEtale.topology B S hS (yoneda.obj T₁)).Point.{u + 1})
    (hΦ : ObjectProperty.ofObj (fun x : GeometricPoint B S hS (yoneda.obj T₁) =>
      (etaleSitePoint B S hS (yoneda.obj T₁) x
        (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}) Φ) :
    ∃ (A₀ A : Type (u + 1)) (_ : CommRing A₀) (_ : CommRing A) (_ : IsLocalRing A₀)
      (_ : IsLocalRing A) (_ : Algebra A₀ A) (L : Type (u + 1)) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField A₀) L) (_ : IsLocalRing.IsHenselization A₀ L A)
      (e₀ : (Φ.presheafFiber (A := CommRingCat.{u + 1})).obj
          ((representedToZariskiRingedToposHom B S hS T₁).toToposHom.inverseImageRing.obj
            ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
              SheafOfModules.commRingCatULift.{u, u + 1}).obj
              ((inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom
                ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
                ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O))).obj ≃+* A₀)
      (e : (Φ.presheafFiber (A := CommRingCat.{u + 1})).obj
          ((SheafOfModules.sheafULift.{u, u + 1, u}
            (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
            ((smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS h)).toToposHom.inverseImageRing.obj
              (smallEtaleRingedTopos B S hS
                ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)).obj ≃+* A),
      ∀ y, e ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map
          (representedBaseMap B S hS h).hom y) = algebraMap A₀ A (e₀ y) := by
  obtain ⟨xb⟩ := hΦ
  exact representedBaseMap_stalk_isHenselization B S hS h xb

end Square

end AlgebraicGeometry.Space

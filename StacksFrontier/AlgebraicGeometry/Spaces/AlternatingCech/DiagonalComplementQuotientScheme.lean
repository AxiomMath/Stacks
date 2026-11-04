module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementFreeAction
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementOrbitQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionOrbitQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldPoints

/-!
# The quotient `U_p = W_p/S_{p+1}` through a scheme representing `W_p`

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S` with
`U` *representable*, and let `W = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `n` factors be the
space `W_p` of [Stacks, Tag 0726] for `n = p + 1`.  Then `W` is representable as well, by
`AlgebraicGeometry.Space.SpacesEtale.exists_siteObj_iso_underlying_diagonalComplement`: there is
an object `V` of the big fppf site with an identification `e` of the presheaf it represents with
the one underlying `W`.

This file transports the action of `S_n` on `W` to an action on `V` by automorphisms of the
site, proves it free in the sense of [Stacks, Tag 071S], and identifies the quotient
`U_p = W_p/S_{p+1}` of `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotient` with
the quotient sheaf `V/S_n` of the graph relation of the transported action.  Everything the
scheme theory of `V/S_n` gives — affineness by [Stacks, Tag 03BM], separatedness by
[Stacks, Tag 02Z4], quasi-compactness and quasi-separatedness — is thereby a statement about
`U_p`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementSchemeAut` is the action of `S_n` on
  the object `V` representing `W`, transported along `e`, and
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementOverAut` is that action read on the
  underlying scheme of `V` over `S`.
* `AlgebraicGeometry.Space.orbitPresheafCongr` and
  `AlgebraicGeometry.Space.orbitQuotientSheafCongr`: the quotients of two presheaves by group
  actions agree when the presheaves are identified equivariantly along a surjective group
  homomorphism.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientIsoActionQuotient`: **the
  quotient `U_p` is the quotient sheaf of the graph relation of the transported action.**

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.actsFreelyOnNonemptyPoints_diagonalComplementSchemeAut`:
  the transported action is free in the sense of [Stacks, Tag 071S].

## Implementation notes

Freeness is the one input that is not formal.  It is read off from
`AlgebraicGeometry.Space.SpacesEtale.eq_one_of_comp_diagonalComplementAut_of_nonempty_points`
through the criterion of [Stacks, Tag 02Z2]: a permutation fixing a point of the representing
scheme and acting trivially on its residue field fixes the canonical morphism `Spec κ(w) ⟶ W`,
whose source has a point, so that permutation is the identity. Going through residue fields is
necessary and not merely convenient — the action of `S_n` on the *point set* of `W` is not
free in general, already for a separable quadratic extension of fields.

The quotient `U_p` is formed as the fppf sheafification of the pointwise orbits of the lifted
group `ULift (Equiv.Perm (Fin n))` on the points of `W`.  The identification with `V/S_n` passes
through the presheaf of points of the underlying scheme of `V`, on which `S_n` itself acts by
translation, and then through `AlgebraicGeometry.Space.isoOrbitQuotientActionQuotient`; the
change of group along `MulEquiv.ulift` changes no orbit.

## References

* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An endomorphism of a scheme fixing a point and acting trivially on its residue field fixes
the canonical morphism from the residue-field point. -/
theorem fromSpecResidueField_comp_of_residueFieldMap_eq {Y : Scheme.{u}} (g : Y ⟶ Y) (y : Y)
    (hy : g y = y) (hres : g.residueFieldMap y = (Y.residueFieldCongr hy).hom) :
    Y.fromSpecResidueField y ≫ g = Y.fromSpecResidueField y := by
  have h := g.SpecMap_residueFieldMap_fromSpecResidueField y
  rw [hres, Scheme.residueFieldCongr_fromSpecResidueField hy] at h
  exact h.symm

namespace Space

section ResidueFieldPoint

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical point of the presheaf represented by the residue-field point of a scheme in
the big fppf site: the identity of that object, read as a field-valued point. -/
def residueFieldObjectPoint (V : BigFppfOver B S hS) (w : V.left.1)
    (hw : B.Contains (Spec (.of (V.left.1.residueField w)))) :
    points B S hS (yoneda.obj (residueFieldObject B S hS V w hw)) :=
  (⟨V.left.1.residueField w, hw, V.left.1.fromSpecResidueField w ≫ V.hom.1,
      𝟙 (residueFieldObject B S hS V w hw)⟩ :
    FieldValuedPoint B S hS
      (yoneda.obj (residueFieldObject B S hS V w hw))).class B S hS _

end ResidueFieldPoint

namespace SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).obj)

/-- The action of `S_n` on the presheaf underlying `W`, read off from the action on `W` as an
object of the spaces-étale site of `X`. -/
def diagonalComplementPresheafAut : Equiv.Perm (Fin n) →*
    Aut (underlying B S hS X (diagonalComplement B S hS X U n hsep)).obj :=
  ((Functor.mapAut (underlying B S hS X (diagonalComplement B S hS X U n hsep))
        (ObjectProperty.ι (IsAlgebraicSpace B S hS))).comp
      (Functor.mapAut (diagonalComplement B S hS X U n hsep) (toSpaces B S hS X))).comp
    (diagonalComplementAut B S hS X U n hsep)

/-- The automorphism of the presheaf underlying `W` given by `σ` is the morphism of presheaves
underlying the automorphism `σ` of `W`. -/
@[simp]
theorem diagonalComplementPresheafAut_hom (σ : Equiv.Perm (Fin n)) :
    (diagonalComplementPresheafAut B S hS X U n hsep σ).hom =
      ((toSpaces B S hS X).map
        (diagonalComplementAut B S hS X U n hsep σ).hom).hom :=
  rfl

/-- The action of `S_n` on the scheme representing `W`, transported along the identification
`e` of the presheaf it represents with the presheaf underlying `W`. -/
def diagonalComplementSchemeAut : Equiv.Perm (Fin n) →* Aut V :=
  ((Yoneda.fullyFaithful.autMulEquivOfFullyFaithful V).symm.toMonoidHom.comp
      (Aut.autMulEquivOfIso e).symm.toMonoidHom).comp
    (diagonalComplementPresheafAut B S hS X U n hsep)

/-- Under the Yoneda embedding, the automorphism of `V` given by `σ` is the conjugate by `e` of
the action of `σ` on the presheaf underlying `W`. -/
theorem yoneda_map_diagonalComplementSchemeAut_hom (σ : Equiv.Perm (Fin n)) :
    yoneda.map (diagonalComplementSchemeAut B S hS X U n hsep V e σ).hom =
      e.hom ≫ ((toSpaces B S hS X).map
        (diagonalComplementAut B S hS X U n hsep σ).hom).hom ≫ e.inv := by
  show yoneda.map (Yoneda.fullyFaithful.preimage
      (e.hom ≫ (diagonalComplementPresheafAut B S hS X U n hsep σ).hom ≫ e.inv)) = _
  rw [Functor.FullyFaithful.map_preimage, diagonalComplementPresheafAut_hom]

/-- The morphism `yoneda.obj V ⟶ W` fixed by a permutation fixing the morphism `V ⟶ V` it
acts by. -/
theorem comp_diagonalComplementAut_eq_of_comp_schemeAut_eq
    {T : BigFppfOver B S hS} (m : T ⟶ V) (σ : Equiv.Perm (Fin n))
    (hm : m ≫ (diagonalComplementSchemeAut B S hS X U n hsep V e σ).hom = m) :
    (yoneda.map m ≫ e.hom) ≫ ((toSpaces B S hS X).map
        (diagonalComplementAut B S hS X U n hsep σ).hom).hom =
      yoneda.map m ≫ e.hom := by
  have h : yoneda.map m ≫ yoneda.map
      (diagonalComplementSchemeAut B S hS X U n hsep V e σ).hom = yoneda.map m := by
    rw [← Functor.map_comp, hm]
  rw [yoneda_map_diagonalComplementSchemeAut_hom] at h
  simpa using congrArg (fun k => k ≫ e.hom) h

/-- Freeness of the action of `S_n` on `W` against a representable test object: a morphism
`yoneda.obj T ⟶ W` from a representable with a point, fixed by `σ`, forces `σ = 1`. -/
theorem eq_one_of_yoneda_comp_diagonalComplementAut (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).obj)
    (t : points B S hS (yoneda.obj T)) (σ : Equiv.Perm (Fin n))
    (hx : x ≫ ((toSpaces B S hS X).map
      (diagonalComplementAut B S hS X U n hsep σ).hom).hom = x) :
    σ = 1 :=
  eq_one_of_comp_diagonalComplementAut_of_nonempty_points B S hS X U n hsep
    (T := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (ObjectProperty.homMk x) ⟨t⟩ σ (ObjectProperty.hom_ext _ hx)

/-- If the automorphism of `V` given by `σ` fixes the canonical morphism `Spec κ(w) ⟶ V` of
underlying schemes, then it fixes the corresponding morphism `residueFieldMap` in the site. -/
theorem residueFieldMap_comp_schemeAut_eq (w : V.left.1)
    (hw : B.Contains (Spec (.of (V.left.1.residueField w)))) (σ : Equiv.Perm (Fin n))
    (h : V.left.1.fromSpecResidueField w ≫
      ((Functor.mapAut V (Over.post B.inclusion)).comp
        (diagonalComplementSchemeAut B S hS X U n hsep V e) σ).hom.left =
      V.left.1.fromSpecResidueField w) :
    residueFieldMap B S hS V w hw ≫
        (diagonalComplementSchemeAut B S hS X U n hsep V e σ).hom =
      residueFieldMap B S hS V w hw :=
  Over.OverMorphism.ext (B.inclusion.map_injective h)

/-- **Freeness of the transported action.** A permutation fixing a point of the scheme
representing `W` and acting trivially on the residue field there is the identity: the
canonical morphism from the residue-field point of that point into `W` is then fixed, and its
source has a point. -/
theorem actsNontriviallyOnFixedResidueFields_diagonalComplementSchemeAut :
    ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) (Equiv.Perm (Fin n))
      ((Functor.mapAut V (Over.post B.inclusion)).comp
        (diagonalComplementSchemeAut B S hS X U n hsep V e)) := by
  intro σ w hw hσ hres
  have hcon : B.Contains (Spec (.of (V.left.1.residueField w))) :=
    B.residueField_spec_contains V.left.2 w
  have hbase := fromSpecResidueField_comp_of_residueFieldMap_eq
    (((Functor.mapAut V (Over.post B.inclusion)).comp
      (diagonalComplementSchemeAut B S hS X U n hsep V e) σ).hom.left) w hw hres
  have hm := residueFieldMap_comp_schemeAut_eq B S hS X U n hsep V e w hcon σ hbase
  have hfix := comp_diagonalComplementAut_eq_of_comp_schemeAut_eq B S hS X U n hsep V e
    (residueFieldMap B S hS V w hcon) σ hm
  exact hσ (eq_one_of_yoneda_comp_diagonalComplementAut B S hS X U n hsep
    (residueFieldObject B S hS V w hcon)
    (yoneda.map (residueFieldMap B S hS V w hcon) ≫ e.hom)
    (residueFieldObjectPoint B S hS V w hcon) σ hfix)

/-- **Freeness of the transported action**: it acts freely on nonempty points in the sense of
[Stacks, Tag 071S]. -/
theorem actsFreelyOnNonemptyPoints_diagonalComplementSchemeAut :
    ActsFreelyOnNonemptyPoints (underlyingOver B hS V) (Equiv.Perm (Fin n))
      ((Functor.mapAut V (Over.post B.inclusion)).comp
        (diagonalComplementSchemeAut B S hS X U n hsep V e)) :=
  actsFreelyOnNonemptyPoints_of_actsNontriviallyOnFixedResidueFields _ _ _
    (actsNontriviallyOnFixedResidueFields_diagonalComplementSchemeAut
      B S hS X U n hsep V e)

/-- The action of `S_n` on `V` transported from the action on `W`, read as an action on the
underlying scheme of `V` over `S` by automorphisms. This is the action whose quotient sheaf
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientIsoActionQuotient` identifies
with `U_p`. -/
abbrev diagonalComplementOverAut : Equiv.Perm (Fin n) →* Aut (underlyingOver B hS V) :=
  (Functor.mapAut V (Over.post B.inclusion)).comp
    (diagonalComplementSchemeAut B S hS X U n hsep V e)

end SpacesEtale

/-! ### Quotients along an equivariant identification -/

section OrbitCongr

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G G' : Type*} [Group G] [Group G']
    {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [∀ T, MulAction G (Y.obj T)]
    [∀ T, MulAction G' (Y'.obj T)]
    (hY : IsNaturalAction B S hS G Y) (hY' : IsNaturalAction B S hS G' Y')
    {φ : G →* G'} (hφ : Function.Surjective φ) (ψ : Y ≅ Y')
    (hψ : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (g : G) (y : Y.obj T),
      ψ.hom.app T (g • y) = φ g • ψ.hom.app T y)

include hφ hψ in
/-- An equivariant identification along a surjective group homomorphism identifies the orbit
relations. -/
theorem orbitRel_iff_of_equivariant (T : (BigFppfOver B S hS)ᵒᵖ) (y₁ y₂ : Y.obj T) :
    MulAction.orbitRel G (Y.obj T) y₁ y₂ ↔
      MulAction.orbitRel G' (Y'.obj T) (ψ.hom.app T y₁) (ψ.hom.app T y₂) := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨φ g, (hψ T g y₂).symm⟩
  · rintro ⟨g', hg'⟩
    obtain ⟨g, rfl⟩ := hφ g'
    exact ⟨g, (ψ.app T).toEquiv.injective ((hψ T g y₂).trans hg')⟩

/-- **The presheaves of pointwise orbits of two equivariantly identified actions agree**, the
identification being along a surjective group homomorphism. -/
def orbitPresheafCongr :
    orbitPresheaf B S hS G Y hY ≅ orbitPresheaf B S hS G' Y' hY' :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (Quotient.congr (ψ.app T).toEquiv
      (orbitRel_iff_of_equivariant hφ ψ hψ T)))
    (fun {T T'} f => by
      ext q
      induction q using Quotient.inductionOn with
      | _ y =>
        change Quotient.mk _ (ψ.hom.app T' (Y.map f y)) =
          Quotient.mk _ (Y'.map f (ψ.hom.app T y))
        rw [← NatTrans.naturality_apply ψ.hom f y])

/-- **The quotient sheaves of two equivariantly identified actions agree**, the identification
being along a surjective group homomorphism. -/
noncomputable def orbitQuotientSheafCongr
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] :
    orbitQuotientSheaf B S hS G Y hY ≅ orbitQuotientSheaf B S hS G' Y' hY' :=
  (presheafToSheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
    (orbitPresheafCongr hY hY' hφ ψ hψ)

end OrbitCongr

/-! ### `U_p` as the quotient of the representing object -/

namespace SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).obj)

/-- The points of `W` are the points of the underlying scheme of `V` over `S`: the
identification `e`, followed by the inclusion of the site into the schemes over `S`, which is
fully faithful. -/
noncomputable def diagonalComplementPointsIso :
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).obj ≅
      Stacks.Groupoids.points (Over.post B.inclusion) (underlyingOver B hS V) :=
  e.symm ≪≫ NatIso.ofComponents
    (fun T => Equiv.toIso
      ((Functor.FullyFaithful.ofFullyFaithful (Over.post (X := B.obj hS) B.inclusion)).homEquiv
        (X := T.unop) (Y := V)))
    (fun _ => rfl)

/-- The identification of points sends a point `x` of `W` over `T` to the image of `e⁻¹ x` under
the inclusion of the site into the schemes over `S`. -/
@[simp]
theorem diagonalComplementPointsIso_hom_app (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (underlying B S hS X (diagonalComplement B S hS X U n hsep)).obj.obj T) :
    (diagonalComplementPointsIso B S hS X U n hsep V e).hom.app T x =
      (Over.post B.inclusion).map (e.inv.app T x) :=
  rfl

/-- **The identification of the points of `W` with those of `V` is equivariant**: a permutation
acting on `W` corresponds to translation by the transported automorphism of `V`. -/
theorem diagonalComplementPointsIso_hom_app_smul (T : (BigFppfOver B S hS)ᵒᵖ)
    (σ : ULift.{u} (Equiv.Perm (Fin n)))
    (x : (underlying B S hS X (diagonalComplement B S hS X U n hsep)).obj.obj T) :
    (diagonalComplementPointsIso B S hS X U n hsep V e).hom.app T (σ • x) =
      (diagonalComplementPointsIso B S hS X U n hsep V e).hom.app T x ≫
        (diagonalComplementOverAut B S hS X U n hsep V e (MulEquiv.ulift σ)).hom := by
  have h := congrArg (fun k => k.app T (e.inv.app T x))
    (yoneda_map_diagonalComplementSchemeAut_hom B S hS X U n hsep V e σ.down)
  simp only [yoneda_map_app, NatTrans.comp_app, types_comp_apply,
    Iso.inv_hom_id_app_apply] at h
  rw [diagonalComplementPointsIso_hom_app, diagonalComplementPointsIso_hom_app,
    diagonalComplementMulAction_smul]
  show _ = (Over.post B.inclusion).map (e.inv.app T x) ≫
    (Over.post B.inclusion).map (diagonalComplementSchemeAut B S hS X U n hsep V e σ.down).hom
  rw [← Functor.map_comp]
  exact congrArg (Over.post B.inclusion).map h.symm

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The quotient `U_p = W/S_n` is the quotient sheaf `V/S_n` of the graph relation of the
transported action.** The orbits of `S_n` on the points of `W` are those of `S_n` on the points
of the underlying scheme of `V` under translation by the transported automorphisms, and the
sheafification of the latter is `V/S_n` by
`AlgebraicGeometry.Space.isoOrbitQuotientActionQuotient`,
the graph relation lying in the site because the action is free. -/
noncomputable def diagonalComplementQuotientIsoActionQuotient :
    (diagonalComplementQuotient B S hS X U n hsep).obj ≅
      actionQuotient (Equiv.Perm (Fin n)) B hS V
        (diagonalComplementOverAut B S hS X U n hsep V e) :=
  letI := mulActionPoints B hS V (Equiv.Perm (Fin n))
    (diagonalComplementOverAut B S hS X U n hsep V e)
  (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
      (orbitQuotientSheafCongr (isNaturalAction_diagonalComplement B S hS X U n hsep)
        (isNaturalAction_points_of_smul_eq B hS V (Equiv.Perm (Fin n))
          (diagonalComplementOverAut B S hS X U n hsep V e) fun _ _ _ => rfl)
        (φ := (MulEquiv.ulift (α := Equiv.Perm (Fin n))).toMonoidHom)
        (fun g => ⟨ULift.up g, rfl⟩)
        (diagonalComplementPointsIso B S hS X U n hsep V e)
        (diagonalComplementPointsIso_hom_app_smul B S hS X U n hsep V e)) ≪≫
    isoOrbitQuotientActionQuotient B hS V (Equiv.Perm (Fin n))
      (diagonalComplementOverAut B S hS X U n hsep V e) _ (fun _ _ _ => rfl)
      (contains_actionRelationScheme (Equiv.Perm (Fin n)) B hS V _
        (actsNontriviallyOnFixedResidueFields_diagonalComplementSchemeAut B S hS X U n hsep V e))

end SpacesEtale

end Space

end AlgebraicGeometry

end

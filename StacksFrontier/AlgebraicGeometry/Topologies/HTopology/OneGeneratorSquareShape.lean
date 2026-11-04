module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.PrincipalCenterConverse
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSheafCriterion

/-!
# Almost blowup squares with a closed-immersion modification have the one-generator shape

Over an affine base an almost blowup square whose modification is a closed immersion and whose
centre is cut out by a single global function is one of the squares of Stacks 0EVG: the base is
`Spec A` for `A` the ring of global functions, the modification is `Spec (A/J) ⟶ Spec A` for `J`
the ideal of global functions killed by the modification, and `J` is finitely generated and
annihilated by a power of the generator of the centre.

This is the step of the proof of Stacks 0EVI which turns its condition (3) — stated for the
squares of Example 0EVG — into a statement about an arbitrary almost blowup square with a
closed-immersion modification and a principal centre.  The two inputs are the converse of Stacks
0EVG, `AlgebraicGeometry.exists_pow_mul_eq_zero_of_isAlmostBlowUpSquare`, which supplies the
annihilation, and the universal property of a closed immersion, which supplies the isomorphisms.

## Main results

* `AlgebraicGeometry.exists_iso_comp_eq_of_ker_eq`: two closed immersions with the same ideal
  sheaf differ by an isomorphism of their sources over the common target.
* `AlgebraicGeometry.isOneGeneratorAlmostBlowUpModel_of_restrict_isIso`: over an affine base, a
  closed immersion of finite presentation which is an isomorphism away from a principal centre
  has the shape of Example 0EVG.
* `AlgebraicGeometry.isOneGeneratorAlmostBlowUpModel_of_isAlmostBlowUpSquare`: the same for an
  almost blowup square with a closed-immersion modification and a principal centre.

## Implementation notes

The shape `AlgebraicGeometry.IsOneGeneratorAlmostBlowUpModel` asks for isomorphisms of the base,
of the modification and of the centre with the three corners of the model square, subject to two
commuting squares.  The isomorphism of bases is `AlgebraicGeometry.Scheme.isoSpec`, and both
other isomorphisms are produced the same way: the two morphisms to be compared are closed
immersions into `Spec Γ(X, ⊤)` whose ideal sheaves agree, because an ideal sheaf on an affine
scheme is determined by its ideal of global sections and both ideals come out as the inverse
image of the same ideal of `Γ(X, ⊤)` along `Γ(Spec Γ(X, ⊤), ⊤) ≅ Γ(X, ⊤)`.  That inverse image
is the reason the model centre of Example 0EVG is stated as the ideal sheaf attached to the
image of `(f)` under the inverse of `AlgebraicGeometry.Scheme.ΓSpecIso`.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-- The inverse image of an ideal along the forward direction of an isomorphism of rings is its
image along the backward direction. -/
public theorem ideal_comap_isoHom_eq_map_isoInv {R S : CommRingCat.{u}} (e : R ≅ S)
    (K : Ideal S) : K.comap e.hom.hom = K.map e.inv.hom := by
  have hfwd (x : S) : e.hom.hom (e.inv.hom x) = x := by
    rw [← CommRingCat.comp_apply, e.inv_hom_id, CommRingCat.id_apply]
  have hbwd (x : R) : e.inv.hom (e.hom.hom x) = x := by
    rw [← CommRingCat.comp_apply, e.hom_inv_id, CommRingCat.id_apply]
  refine le_antisymm (fun x hx => ?_) (Ideal.map_le_iff_le_comap.2 fun y hy => ?_)
  · rw [← hbwd x]
    exact Ideal.mem_map_of_mem _ hx
  · simpa only [Ideal.mem_comap, hfwd] using hy

/-- **Two closed immersions with the same ideal sheaf agree up to an isomorphism of their
sources.** The isomorphism is over the common target. -/
public theorem exists_iso_comp_eq_of_ker_eq {Y W₁ W₂ : Scheme.{u}} (c₁ : W₁ ⟶ Y) (c₂ : W₂ ⟶ Y)
    [IsClosedImmersion c₁] [IsClosedImmersion c₂] (hker : c₁.ker = c₂.ker) :
    ∃ i : W₁ ≅ W₂, c₁ = i.hom ≫ c₂ := by
  have hfac := IsClosedImmersion.lift_fac c₂ c₁ hker.ge
  have := IsClosedImmersion.isIso_of_ker_eq c₁ c₂ _ hfac hker
  exact ⟨asIso (IsClosedImmersion.lift c₂ c₁ hker.ge), hfac.symm⟩

/-- The ideal of global sections of the ideal sheaf of a morphism to an affine scheme composed
with the canonical isomorphism of that scheme with the spectrum of its global functions. -/
public theorem ker_comp_isoSpec_hom_ideal_top {X W : Scheme.{u}} [IsAffine X] (p : W ⟶ X) :
    (p ≫ X.isoSpec.hom).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (RingHom.ker (p.appTop).hom).comap (Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom := by
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  rw [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, CommRingCat.hom_comp,
    ← RingHom.comap_ker]

/-- The ideal of global sections of the ideal sheaf of `Spec` of a ring map. -/
public theorem ker_Spec_map_ideal_top {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (Spec.map φ).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom := by
  have happ : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hk : RingHom.ker ((φ ≫ (Scheme.ΓSpecIso S).inv)).hom = RingHom.ker φ.hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).1
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  rw [happ, CommRingCat.hom_comp, ← RingHom.comap_ker, hk]

/-- **A closed immersion of finite presentation over an affine base which is an isomorphism away
from a principal centre has the shape of Stacks 0EVG.** The base is the spectrum of its ring of
global functions, the modification is the spectrum of the quotient by the ideal of functions it
kills, and the centre is cut out by the chosen generator. -/
public theorem isOneGeneratorAlmostBlowUpModel_of_restrict_isIso {X X' : Scheme.{u}}
    [IsAffine X] (I : X.IdealSheafData) (b : X' ⟶ X) [IsClosedImmersion b]
    (hfp : FinitePresentation b)
    (hiso : IsIso (b ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens)))
    (t : Γ(X, ⊤)) (ht : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {t}) :
    IsOneGeneratorAlmostBlowUpModel b I.subschemeι := by
  classical
  refine ⟨Γ(X, ⊤), inferInstance, t, RingHom.ker (b.appTop).hom,
    fg_ker_appTop_of_finitePresentation b hfp,
    exists_pow_mul_eq_zero_of_restrict_isIso I b hfp hiso t ht, ?_⟩
  show IsModelPairOverBase b I.subschemeι
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (b.appTop).hom))))
    (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom (Ideal.span {t}))).subschemeι
  obtain ⟨iX', hiX'⟩ := exists_iso_comp_eq_of_ker_eq (b ≫ X.isoSpec.hom)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (b.appTop).hom))))
    (Scheme.IdealSheafData.ext_of_isAffine (by
      rw [ker_comp_isoSpec_hom_ideal_top, ker_Spec_map_ideal_top]
      congr 1
      exact (Ideal.mk_ker (I := RingHom.ker (b.appTop).hom)).symm))
  obtain ⟨iZ, hiZ⟩ := exists_iso_comp_eq_of_ker_eq (I.subschemeι ≫ X.isoSpec.hom)
    (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom (Ideal.span {t}))).subschemeι
    (Scheme.IdealSheafData.ext_of_isAffine (by
      rw [ker_comp_isoSpec_hom_ideal_top, Scheme.IdealSheafData.ker_subschemeι,
        Scheme.IdealSheafData.ofIdealTop_ideal]
      simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id,
        Ideal.map_id]
      rw [← ideal_comap_isoHom_eq_map_isoInv, ← ht]
      congr 1
      exact Scheme.IdealSheafData.ker_subschemeι_app (I := I) ⟨⊤, isAffineOpen_top X⟩))
  exact ⟨X.isoSpec, iX', iZ, hiX', hiZ⟩

/-- **An almost blowup square with a closed-immersion modification and a principal centre over an
affine base has the shape of Stacks 0EVG.** -/
public theorem isOneGeneratorAlmostBlowUpModel_of_isAlmostBlowUpSquare {X X' : Scheme.{u}}
    [IsAffine X] (I : X.IdealSheafData) (b : X' ⟶ X) [IsClosedImmersion b]
    (h : IsAlmostBlowUpSquare I b) (t : Γ(X, ⊤))
    (ht : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {t}) :
    IsOneGeneratorAlmostBlowUpModel b I.subschemeι :=
  isOneGeneratorAlmostBlowUpModel_of_restrict_isIso I b h.finitePresentation
    (isIso_restrict_compl_support I b h) t ht

/-- The shape of a pair is unchanged if the centre is replaced by an isomorphic one over the
base. -/
public theorem IsModelPairOverBase.of_centre_iso {X X' Z Z' Xm X'm Zm : Scheme.{u}}
    {b : X' ⟶ X} {z : Z ⟶ X} {z' : Z' ⟶ X} {bm : X'm ⟶ Xm} {zm : Zm ⟶ Xm}
    (h : IsModelPairOverBase b z bm zm) (w : Over.mk z' ≅ Over.mk z) :
    IsModelPairOverBase b z' bm zm := by
  obtain ⟨iX, iX', iZ, hb, hz⟩ := h
  refine ⟨iX, iX', (Over.forget X).mapIso w ≪≫ iZ, hb, ?_⟩
  have hw : w.hom.left ≫ z = z' := Over.w w.hom
  rw [Iso.trans_hom, Category.assoc, ← hz, ← Category.assoc]
  simp only [Functor.mapIso_hom, Over.forget_map, hw]

/-- The one-generator shape of a pair is unchanged if the centre is replaced by an isomorphic one
over the base. -/
public theorem IsOneGeneratorAlmostBlowUpModel.of_centre_iso {X X' Z Z' : Scheme.{u}}
    {b : X' ⟶ X} {z : Z ⟶ X} {z' : Z' ⟶ X}
    (h : IsOneGeneratorAlmostBlowUpModel b z) (w : Over.mk z' ≅ Over.mk z) :
    IsOneGeneratorAlmostBlowUpModel b z' := by
  obtain ⟨A, hA, f, J, hfg, hann, hm⟩ := h
  exact ⟨A, hA, f, J, hfg, hann, hm.of_centre_iso w⟩

/-- **The one-generator shape of Stacks 0EVG covers every almost blowup square of the site with
affine base, closed-immersion modification and principal centre.** Condition (3) of Stacks 0EVI
therefore applies to such a square verbatim.

This is the affine core of the second step of the proof of Stacks 0EVI: the source deduces from
condition (3) that the image of such a square is cartesian by passing to an affine open covering
of the base on which the centre becomes principal, and this is the statement it uses on each
member of that covering. -/
public theorem BigHOver.isPullback_of_isOneGeneratorAlmostBlowUpSheaf_of_isClosedImmersion
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)
    (h1 : BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F)
    (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (haff : IsAffine ((BigHOver.toScheme B S hS).obj X))
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b))
    (hci : IsClosedImmersion ((BigHOver.toScheme B S hS).map b))
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι))
    (hsq : IsPullback ((BigHOver.toScheme B S hS).map e) ((BigHOver.toScheme B S hS).map d)
      ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map b))
    (t : Γ((BigHOver.toScheme B S hS).obj X, ⊤))
    (ht : I.ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {t}) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map d.op) := by
  obtain ⟨w⟩ := hZ
  exact h1 X X' Z E b z d e I haff hb ⟨w⟩ hsq
    ((isOneGeneratorAlmostBlowUpModel_of_isAlmostBlowUpSquare I _ hb t ht).of_centre_iso w)

end AlgebraicGeometry

end

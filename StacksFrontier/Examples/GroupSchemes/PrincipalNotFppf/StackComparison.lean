module

public import StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Torsor
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsToPrincipal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# The stacks `G-Principal` and `G-Torsors` are not equivalent

Let `S = Spec ℚ` and let `G = ∏ᵢ μ_{i+2}` be the group scheme of
`StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Group`, acting on the radical tower
`P = Spec ℚ[x₀, x₁, …]/(xᵢ ^ (i + 2) - 2)`.  Over any big fppf site `(Sch/S)_fppf` this file
places `G` and `P` in the categories of Stacks 04UN and Stacks 04UR: `G` becomes a group
algebraic space over `S`, and `P` an object of the category `G-Principal` of principal
homogeneous `G`-spaces.  No object of the category `G-Torsors` of fppf `G`-torsors is sent to it,
up to isomorphism, by the canonical functor `G-Torsors ⥤ G-Principal`, so that functor is not
essentially surjective and the two stacks are not equivalent.  This is Stacks 077B.

## Main definitions

* `Stacks.Examples.RadicalTower.groupSpace`: the group algebraic space `G` over `Spec ℚ`.
* `Stacks.Examples.RadicalTower.principalObj`: `P`, as an object of `G-Principal`.

## Main results

* `Stacks.Examples.RadicalTower.isEmpty_iso_principalObj`: no fppf `G`-torsor is isomorphic
  to `P` in `G-Principal`.
* `Stacks.Examples.RadicalTower.not_essSurj_toPrincipal` and
  `Stacks.Examples.RadicalTower.not_isEquivalence_toPrincipal`: over every big fppf site the
  canonical functor `AlgebraicGeometry.Space.FppfTorsors.toPrincipal` is neither essentially
  surjective nor an equivalence.
* `Stacks.Examples.RadicalTower.exists_not_isEquivalence_fppfTorsors_toPrincipal`:
  **Stacks 077B**.

## Implementation notes

The group algebraic space is `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`
at `G`, and the action on `B ⨯ P` is
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSiteModObj`; both are obtained from
the scheme-level data by restricting the functor of points to the site and forming the product
with the base, so the pseudo-torsor property of the scheme-level action
(`Stacks.Examples.RadicalTower.isPseudoTorsor`) is carried across by
`CategoryTheory.isIso_leftSMul_opCompYoneda` and `CategoryTheory.isIso_leftSMul_overProdFst`.
The object of `G-Principal` has the base `Spec ℚ` itself, with the restriction of `B ⨯ P` along
the identity as total space, as the definition of `G-Principal` asks; it is trivialized by the
fpqc covering `{P → Spec ℚ}`, by
`AlgebraicGeometry.Space.isFpqcCovering_yoneda_map_of_flat_of_surjective`, over which the
diagonal is a section.

The negative statement follows the source.  An fppf covering of algebraic spaces trivializing a
torsor isomorphic to `P` has a member with a point, because it is jointly surjective and the base
is nonempty; an étale scheme chart of that member is then a nonempty scheme, locally of finite
presentation over `Spec ℚ` by the chart condition of Stacks 03XP, carrying a morphism to `P`.
Such a scheme has a point with residue field finite over `ℚ` (Stacks 0478), and the radical
tower admits no morphism from the spectrum of such a field:
`Stacks.Examples.RadicalTower.isEmpty_of_locallyOfFiniteType`.

The source states the lemma for an arbitrary scheme `S` and group scheme `G` over `S`, "in
general", and proves it by exhibiting this `S` and this `G`; the formal statement is accordingly
an existence statement over a big fppf site, which exists by
`AlgebraicGeometry.BigFppfSite.exists_contains`.

## References

* [Stacks Project, Tag 077B](https://stacks.math.columbia.edu/tag/077B)
* [Stacks Project, Tag 04UN](https://stacks.math.columbia.edu/tag/04UN)
* [Stacks Project, Tag 04UR](https://stacks.math.columbia.edu/tag/04UR)
* [Stacks Project, Tag 0478](https://stacks.math.columbia.edu/tag/0478)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Space CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj

namespace Stacks.Examples.RadicalTower

variable (𝒞 : BigFppfSite.{0})

/-- The spectrum of a countable ring belongs to every big fppf site. -/
theorem contains_spec_of_countable (R : Type) [CommRing R] [Countable R] :
    𝒞.Contains (Spec (.of R)) := by
  change (Spec (.of R)).size < 𝒞.cutoff
  rw [Scheme.size_Spec]
  exact (max_le le_rfl Cardinal.mk_le_aleph0).trans_lt 𝒞.aleph0_lt_cutoff

instance : Countable Alg :=
  Function.Surjective.countable (f := Ideal.Quotient.mk relationsIdeal)
    Ideal.Quotient.mk_surjective

instance : Countable Exponents := inferInstanceAs (Countable (Π₀ i : ℕ, ZMod (i + 2)))

instance : Countable CharGroup := inferInstanceAs (Countable Exponents)

instance : Countable Coord :=
  Function.Surjective.countable (f := MonoidAlgebra.ofCoeff) fun x => ⟨x.coeff, rfl⟩

/-- `Spec ℚ` belongs to every big fppf site. -/
theorem contains_base : 𝒞.Contains base := contains_spec_of_countable 𝒞 ℚ

/-- The base `Spec ℚ`, as the terminal object of the big fppf site over itself. -/
abbrev baseSite : BigFppfOver 𝒞 base (contains_base 𝒞) :=
  BigFppfOver.mk 𝒞 base (contains_base 𝒞) (contains_base 𝒞) (𝟙 base)

/-- The group scheme `G`, as an object of the big fppf site over `Spec ℚ`. -/
abbrev groupSite : BigFppfOver 𝒞 base (contains_base 𝒞) :=
  BigFppfOver.mk 𝒞 base (contains_base 𝒞) (contains_spec_of_countable 𝒞 Coord) groupObj.hom

/-- The scheme `P`, as an object of the big fppf site over `Spec ℚ`. -/
abbrev torsorSite : BigFppfOver 𝒞 base (contains_base 𝒞) :=
  BigFppfOver.mk 𝒞 base (contains_base 𝒞) (contains_spec_of_countable 𝒞 Alg) torsorObj.hom

/-- The group-object structure on `groupSite`, read through the slice over `Spec ℚ`. -/
abbrev grpObjGroupSite : GrpObj ((toSchemeOver 𝒞 base (contains_base 𝒞)).obj (groupSite 𝒞)) :=
  grpObjGroupObj

/-- The base `Spec ℚ`, as an algebraic space. -/
abbrev baseSpace : (BigFppfOver 𝒞 base (contains_base 𝒞))ᵒᵖ ⥤ Type :=
  yoneda.obj (baseSite 𝒞)

theorem isAlgebraicSpace_baseSpace : IsAlgebraicSpace 𝒞 base (contains_base 𝒞) (baseSpace 𝒞) :=
  isAlgebraicSpace_yoneda 𝒞 base (contains_base 𝒞) (baseSite 𝒞)

/-- The group scheme `G = ∏ᵢ μ_{i+2}`, as a group algebraic space over `Spec ℚ`. -/
abbrev groupSpace :
    GroupAlgebraicSpace 𝒞 base (contains_base 𝒞) (baseSpace 𝒞) (isAlgebraicSpace_baseSpace 𝒞) :=
  GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 base (contains_base 𝒞) (baseSpace 𝒞)
    (isAlgebraicSpace_baseSpace 𝒞) (groupSite 𝒞) (grpObjGroupSite 𝒞)

/-- The functor of points of `P` on the big fppf site over `Spec ℚ`. -/
abbrev torsorPoints : (BigFppfOver 𝒞 base (contains_base 𝒞))ᵒᵖ ⥤ Type :=
  (toSchemeOver 𝒞 base (contains_base 𝒞)).op ⋙ yoneda.obj torsorObj

/-- The scheme `P`, as an algebraic space over `Spec ℚ` in the slice over the base. -/
abbrev torsorSpace : Over (baseSpace 𝒞) :=
  Over.mk (prod.fst : baseSpace 𝒞 ⨯ torsorPoints 𝒞 ⟶ baseSpace 𝒞)

/-- The action of `G` on `P`, read through the group-object structure of `groupSite`. -/
abbrev modObjTorsorSite :
    letI := grpObjGroupSite 𝒞
    ModObj ((toSchemeOver 𝒞 base (contains_base 𝒞)).obj (groupSite 𝒞)) torsorObj :=
  modObjTorsor

/-- The action of `G` on `P` on points over the site. -/
abbrev modObjTorsorPoints :
    ModObj (pointsOnSite 𝒞 base (contains_base 𝒞) (groupSite 𝒞) (grpObjGroupSite 𝒞) ⋙
      forget GrpCat) (torsorPoints 𝒞) :=
  pointsOnSiteModObj 𝒞 base (contains_base 𝒞) (groupSite 𝒞) (grpObjGroupSite 𝒞)
    torsorObj (modObjTorsorSite 𝒞)

/-- The action of `G` on `P` over `Spec ℚ`, in the slice over the base. -/
instance modObjTorsorSpace : ModObj (groupSpace 𝒞).obj.X (torsorSpace 𝒞) :=
  GroupAlgebraicSpace.ofGroupSchemeInSiteModObj 𝒞 base (contains_base 𝒞) (baseSpace 𝒞)
    (groupSite 𝒞) (grpObjGroupSite 𝒞) torsorObj (modObjTorsorSite 𝒞)

/-- The action of `G` on `P` on points over the site is a pseudo-torsor. -/
theorem isPseudoTorsor_points :
    letI := modObjTorsorPoints 𝒞
    IsPseudoTorsor (pointsOnSite 𝒞 base (contains_base 𝒞) (groupSite 𝒞) (grpObjGroupSite 𝒞) ⋙
      forget GrpCat) (torsorPoints 𝒞) :=
  letI := grpObjGroupSite 𝒞
  letI := modObjTorsorSite 𝒞
  isIso_leftSMul_opCompYoneda (toSchemeOver 𝒞 base (contains_base 𝒞))
    ((toSchemeOver 𝒞 base (contains_base 𝒞)).obj (groupSite 𝒞)) torsorObj isPseudoTorsor

/-- The action of the group algebraic space `G` on `P` over `Spec ℚ` is a pseudo-torsor. -/
theorem isPseudoTorsor_torsorSpace : IsPseudoTorsor (groupSpace 𝒞).obj.X (torsorSpace 𝒞) :=
  @isIso_leftSMul_overProdFst _ _ _ _ (baseSpace 𝒞) _
    (pointsOnSite 𝒞 base (contains_base 𝒞) (groupSite 𝒞) (grpObjGroupSite 𝒞) ⋙ forget GrpCat)
    (grpObjCompForget _) (torsorPoints 𝒞) (modObjTorsorPoints 𝒞) (isPseudoTorsor_points 𝒞)

/-- `P` is an algebraic space over `Spec ℚ`. -/
theorem isAlgebraicSpace_torsorSpace :
    IsAlgebraicSpace 𝒞 base (contains_base 𝒞) (torsorSpace 𝒞).left :=
  isAlgebraicSpace_prod_toSchemeOverYoneda 𝒞 base (contains_base 𝒞) (baseSpace 𝒞)
    (isAlgebraicSpace_baseSpace 𝒞) (torsorSite 𝒞)

/-- The structure morphism `P → Spec ℚ`, as a morphism of the big fppf site. -/
abbrev torsorProj : torsorSite 𝒞 ⟶ baseSite 𝒞 :=
  BigFppfOver.homMk 𝒞 base (contains_base 𝒞) (contains_base 𝒞) (𝟙 base)
    (T := torsorSite 𝒞) proj ((Category.comp_id _).trans rfl)

theorem toScheme_map_torsorProj :
    (BigFppfOver.toScheme 𝒞 base (contains_base 𝒞)).map (torsorProj 𝒞) = proj :=
  BigFppfOver.toScheme_map_homMk _ _ _ _ _ _ _

/-- The one-member family `{P → Spec ℚ}` is an fpqc covering of algebraic spaces. -/
theorem isFpqcCovering_torsorProj :
    IsFpqcCovering 𝒞 base (contains_base 𝒞)
      (fun _ : PUnit.{2} => yoneda.map (torsorProj 𝒞)) := by
  have hf : Flat ((BigFppfOver.toScheme 𝒞 base (contains_base 𝒞)).map (torsorProj 𝒞)) := by
    rw [toScheme_map_torsorProj]
    exact inferInstanceAs (Flat proj)
  have hs : Surjective ((BigFppfOver.toScheme 𝒞 base (contains_base 𝒞)).map (torsorProj 𝒞)) := by
    rw [toScheme_map_torsorProj]
    exact inferInstanceAs (Surjective proj)
  exact isFpqcCovering_yoneda_map_of_flat_of_surjective (torsorProj 𝒞)
    (inferInstanceAs (IsAffine (Spec (.of Alg))))
    (inferInstanceAs (IsAffine (Spec (.of ℚ)))) hf hs

/-- Over the fpqc covering `{P → Spec ℚ}` the space `P` has a section, the diagonal. -/
theorem nonempty_section_torsorProj :
    Nonempty (𝟙_ (Over (yoneda.obj (torsorSite 𝒞))) ⟶
      (Over.pullback (yoneda.map (torsorProj 𝒞))).obj
        ((Over.pullback (𝟙 (baseSpace 𝒞))).obj (torsorSpace 𝒞))) := by
  rw [nonempty_unitHom_pullback_iff]
  exact ⟨pullback.lift (prod.lift (yoneda.map (torsorProj 𝒞))
      (toSchemeOverYonedaObjIso 𝒞 base (contains_base 𝒞) (torsorSite 𝒞)).hom)
      (yoneda.map (torsorProj 𝒞)) ((prod.lift_fst _ _).trans (Category.comp_id _).symm),
      pullback.lift_snd _ _ _⟩

/-- The principal homogeneous `G`-space `P` over `Spec ℚ`, as an object of the category
`G-Principal` of Stacks 04UN: its base is `Spec ℚ` itself, and it is trivialized by the fpqc
covering `{P → Spec ℚ}`, over which the diagonal is a section. -/
def principalObj :
    PrincipalHomogeneousSpaces (isAlgebraicSpace_baseSpace 𝒞) (groupSpace 𝒞) where
  base := baseSite 𝒞
  sec := 𝟙 _
  total := (Over.pullback (𝟙 (baseSpace 𝒞))).obj (torsorSpace 𝒞)
  isAlgebraicSpace := isAlgebraicSpace_pullback 𝒞 base (contains_base 𝒞) _ _
    (isAlgebraicSpace_torsorSpace 𝒞) (isAlgebraicSpace_baseSpace 𝒞)
    (isAlgebraicSpace_baseSpace 𝒞)
  action := @restrictModObj _ _ _ _ _ (𝟙 (baseSpace 𝒞)) (groupSpace 𝒞).obj.X (torsorSpace 𝒞) _
    (modObjTorsorSpace 𝒞)
  isTorsor := ⟨@isPseudoTorsor_restrict _ _ _ _ _ (𝟙 (baseSpace 𝒞)) (groupSpace 𝒞).obj.X
      (torsorSpace 𝒞) _ (modObjTorsorSpace 𝒞) (isPseudoTorsor_torsorSpace 𝒞), PUnit,
    fun _ => yoneda.obj (torsorSite 𝒞), fun _ => yoneda.map (torsorProj 𝒞),
    fun _ => isAlgebraicSpace_yoneda 𝒞 base (contains_base 𝒞) _,
    isFpqcCovering_torsorProj 𝒞, fun _ => nonempty_section_torsorProj 𝒞⟩

/-- No fppf `G`-torsor is isomorphic, in `G-Principal`, to `P`: an fppf covering of the base of
such a torsor has a nonempty member, an étale chart of that member is a nonempty scheme locally
of finite type over `Spec ℚ` mapping to `P`, and no such scheme exists. -/
theorem isEmpty_iso_principalObj
    (T : FppfTorsors (isAlgebraicSpace_baseSpace 𝒞) (groupSpace 𝒞)) :
    IsEmpty ((FppfTorsors.toPrincipal _ _).obj T ≅ principalObj 𝒞) := by
  refine ⟨fun e => ?_⟩
  let hS := contains_base 𝒞
  let Φ := BigFppfOver.toScheme 𝒞 base hS
  have hbase : IsIso (TorsorsFor.Hom.base e.hom) :=
    ⟨TorsorsFor.Hom.base e.inv, congrArg TorsorsFor.Hom.base e.hom_inv_id,
      congrArg TorsorsFor.Hom.base e.inv_hom_id⟩
  obtain ⟨-, I, Bᵢ, f, hBᵢ, hcov, hsec⟩ := T.isTorsor
  let x₀ : points 𝒞 base hS (yoneda.obj T.base) :=
    (pointsEquivScheme 𝒞 base hS T.base).symm
      (Φ.map (TorsorsFor.Hom.base e.inv) (Classical.arbitrary base))
  have hx₀ : x₀ ∈ ⋃ i, Set.range (pointsMap 𝒞 base hS (Bᵢ i) (f i)) := by
    rw [hcov.jointly_surjective]
    trivial
  obtain ⟨i, y, -⟩ := Set.mem_iUnion.mp hx₀
  obtain ⟨V, a, ha_surj, ha_et⟩ := (hBᵢ i).exists_atlas
  obtain ⟨v, -⟩ := isSurjective_of_presheafSurjective 𝒞 base hS a ha_surj y
  have hV : Nonempty (Φ.obj V) := ⟨pointsEquivScheme 𝒞 base hS V v⟩
  let h : V ⟶ T.base := yoneda.preimage (a ≫ f i)
  have hlfp : LocallyOfFinitePresentation (Φ.map h) :=
    hcov.locallyOfFinitePresentation i V T.base a (yoneda.map (𝟙 T.base)) h ha_et
      (presheaf_yoneda_map_id_etale 𝒞 base hS T.base) (by simp [h])
  obtain ⟨t, -⟩ := (nonempty_unitHom_pullback_iff (f i) T.total).1 (hsec i)
  let k : yoneda.obj V ⟶ torsorPoints 𝒞 :=
    a ≫ t ≫ (TorsorsFor.Hom.map e.hom : T.total.left ⟶ (principalObj 𝒞).total.left) ≫
      pullback.fst (torsorSpace 𝒞).hom (𝟙 (baseSpace 𝒞)) ≫ prod.snd
  let g : Φ.obj V ⟶ total := (yonedaEquiv k).left
  let fV : Φ.obj V ⟶ base := Φ.map h ≫ Φ.map (TorsorsFor.Hom.base e.hom)
  have : IsIso (Φ.map (TorsorsFor.Hom.base e.hom)) := Functor.map_isIso Φ _
  have : IsOpenImmersion (Φ.map (TorsorsFor.Hom.base e.hom)) := inferInstance
  have h₂ : LocallyOfFiniteType (Φ.map (TorsorsFor.Hom.base e.hom)) := inferInstance
  have h₁ : LocallyOfFiniteType (Φ.map h) := inferInstance
  have : LocallyOfFiniteType fV := MorphismProperty.comp_mem @LocallyOfFiniteType _ _ h₁ h₂
  exact (isEmpty_of_locallyOfFiniteType fV g).false (Classical.arbitrary _)

/-- The canonical functor `G-Torsors ⥤ G-Principal` is not essentially surjective for
`S = Spec ℚ` and `G = ∏ᵢ μ_{i+2}`, over any big fppf site. -/
theorem not_essSurj_toPrincipal :
    ¬ (FppfTorsors.toPrincipal (isAlgebraicSpace_baseSpace 𝒞) (groupSpace 𝒞)).EssSurj := by
  intro h
  obtain ⟨T, ⟨e⟩⟩ := h.mem_essImage (principalObj 𝒞)
  exact (isEmpty_iso_principalObj 𝒞 T).false e

/-- The canonical functor `G-Torsors ⥤ G-Principal` is not an equivalence for `S = Spec ℚ` and
`G = ∏ᵢ μ_{i+2}`, over any big fppf site. -/
theorem not_isEquivalence_toPrincipal :
    ¬ (FppfTorsors.toPrincipal (isAlgebraicSpace_baseSpace 𝒞) (groupSpace 𝒞)).IsEquivalence :=
  fun _ => not_essSurj_toPrincipal 𝒞 inferInstance

/-- **Stacks Project, Tag 077B.**  The stack `G-Principal` of principal homogeneous `G`-spaces
(Stacks 04UN) and the stack `G-Torsors` of fppf `G`-torsors (Stacks 04UR) are not equivalent in
general: there are a big fppf site, a scheme `S` in it and a group scheme `G` over `S` in it,
regarded as a group algebraic space over `S`, for which the canonical functor
`G-Torsors ⥤ G-Principal` is not essentially surjective, hence not an equivalence.  One may take
`S = Spec ℚ` and `G = ∏ᵢ μ_{i+2}`, over any big fppf site: this is
`Stacks.Examples.RadicalTower.not_essSurj_toPrincipal`. -/
@[stacks 077B "G-Principal and G-Torsors are not equivalent in general: for S = Spec ℚ and the \
group scheme G = ∏ᵢ μ_{i+2} the canonical functor G-Torsors ⥤ G-Principal is not essentially \
surjective, hence not an equivalence, over every big fppf site"]
theorem exists_not_isEquivalence_fppfTorsors_toPrincipal :
    ∃ (𝒞 : BigFppfSite.{0}) (S : Scheme.{0}) (hS : 𝒞.Contains S)
      (G : BigFppfOver 𝒞 S hS) (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)),
      ¬ (FppfTorsors.toPrincipal (isAlgebraicSpace_yoneda 𝒞 S hS (BigFppfOver.mk 𝒞 S hS hS (𝟙 S)))
          (GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS _ _ G hG)).EssSurj ∧
      ¬ (FppfTorsors.toPrincipal (isAlgebraicSpace_yoneda 𝒞 S hS (BigFppfOver.mk 𝒞 S hS hS (𝟙 S)))
          (GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS _ _ G hG)).IsEquivalence := by
  obtain ⟨𝒞, -⟩ := BigFppfSite.exists_contains base
  exact ⟨𝒞, base, contains_base 𝒞, groupSite 𝒞, grpObjGroupSite 𝒞, not_essSurj_toPrincipal 𝒞,
    not_isEquivalence_toPrincipal 𝒞⟩

end Stacks.Examples.RadicalTower

end

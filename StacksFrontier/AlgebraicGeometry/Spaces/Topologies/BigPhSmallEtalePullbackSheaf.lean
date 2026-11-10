module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtaleFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtaleSectionsHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# The pullback of a small étale sheaf to the big ph site of an algebraic space

Let `P` be a big ph site of algebraic spaces over a scheme `S`, `E` a big étale site of algebraic
spaces built on the same big fppf site of schemes (`h : P.fppfSite = E.fppfSite`), and `X` an
algebraic space of `P`. Write `π_X` for the morphism from the big étale topos of `X` to its small
étale topos, `ε_X` for the change of topology from the big ph topos of `X` to its big étale topos
and `a_X = π_X ∘ ε_X` (Stacks 0DGW). For a sheaf `F` on `X_étale` the big étale sheaf `π_X⁻¹F` is
already a ph sheaf, so `a_X⁻¹F = ε_X⁻¹π_X⁻¹F` is `π_X⁻¹F` read as a ph sheaf. This gives part (1)
of Stacks 0DGT: `ε_{X,*}a_X⁻¹F = π_X⁻¹F` and `a_{X,*}a_X⁻¹F = F`.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.isSheaf_bigToSmallEtale_inverseImage`: `π_X⁻¹F` is a ph
  sheaf.
* `AlgebraicGeometry.BigPHSpaceSite.isIso_phToBigEtale_unit_app_inverseImage` and
  `AlgebraicGeometry.BigPHSpaceSite.isIso_phToSmallEtale_unit_app`: the two clauses of Stacks
  0DGT (1), as invertibility of the adjunction units; the natural-isomorphism forms are
  `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtale_inverseImage_comp_phToBigEtale_pushforwardIso`
  and `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtale_inverseImage_comp_pushforwardIso`.
* `AlgebraicGeometry.BigPHSpaceSite.isSheaf_bigToSmallEtale_abelianInverseImage`: the same ph
  sheaf property for the abelian inverse image of an abelian sheaf.

## Implementation notes

The proper-surjective half of the ph sheaf condition rests on full faithfulness of descent along a
proper surjection of algebraic spaces,
`AlgebraicGeometry.Space.isPrestackFor_of_isProper_isSurjective` (towards Stacks 0DFX), whose
scheme case is `AlgebraicGeometry.Space.properSurjectivePrestackOverSchemes`, from proper base
change in degree zero (Stacks 0A3U). The étale
half of the ph sheaf criterion of Stacks 0DFM is
`AlgebraicGeometry.BigEtaleSpaceSite.isEtaleSheafOver_inverseImage`; the proper-surjective half is
`AlgebraicGeometry.BigEtaleSpaceSite.isSheafFor_inverseImage_of_isProper_isSurjective`. The two
sites `P` and `E` are related by destructuring them and substituting `h`, after which the
identity-on-spaces functors of slices are the identity, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleSheaf` (Stacks 0DGF), whose
structure this file follows.

## References

* [Stacks Project, Tag 0DFM](https://stacks.math.columbia.edu/tag/0DFM)
* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
* [Stacks Project, Tag 0DGT](https://stacks.math.columbia.edu/tag/0DGT)
* [Stacks Project, Tag 0DGW](https://stacks.math.columbia.edu/tag/0DGW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigPHSpaceSite

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite)

/-- **`π_X⁻¹F` is a ph sheaf** (Stacks 0DGT, part (1), first step). For a sheaf `G` on the small
étale site of `X`, the big étale sheaf `π_X⁻¹G`, read on the big ph slice at `X`, is a sheaf for
the big ph topology of `X`: by Stacks 0DFM it suffices to check étale descent, which holds for
every étale covering family of the slice, and descent along every proper surjective morphism,
which is `AlgebraicGeometry.BigEtaleSpaceSite.isSheafFor_inverseImage_of_isProper_isSurjective`. -/
theorem isSheaf_bigToSmallEtale_inverseImage
    (X : P.Spaces)
    (G : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      (Type (u + 1))) :
    Presheaf.IsSheaf (BigPHSpaceOver.topology P X)
      ((Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).functor.op ⋙
        ((E.bigToSmallEtaleMorphism (etaleSpace P E h X)).inverseImage.obj G).obj) := by
  cases P with
  | mk pSchemeSite pSchemeMem pFppfSite pFppfMem pCutoffEq pInitial pInitialSmall pInitialPH
      pBound pOrdinal pOrdinalLim pInitialBounded pIsSite pRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let P' : BigPHSpaceSite S :=
        ⟨pSchemeSite, pSchemeMem, pFppfSite, pFppfMem, pCutoffEq, pInitial, pInitialSmall,
          pInitialPH, pBound, pOrdinal, pOrdinalLim, pInitialBounded, pIsSite, pRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, pFppfSite, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      let Q := ((E'.bigToSmallEtaleMorphism X).inverseImage.obj G).obj
      change Presheaf.IsSheaf (BigPHSpaceOver.topology P' X) Q
      rw [isSheaf_iff_isSheaf_of_type]
      exact Space.isSheaf_of_etale_and_properSurjective P' X Q
        (E'.isEtaleSheafOver_inverseImage X G)
        (fun _ _ f hp hs => E'.isSheafFor_inverseImage_of_isProper_isSurjective
          (Space.properSurjectivePrestackOverSchemes _ _ _) f hp hs G)

/-- **The unit of `ε_X⁻¹ ⊣ ε_{X,*}` at a ph sheaf.** Let `K` be a big étale sheaf on `X` whose
underlying presheaf, read on the big ph slice at `X`, is a ph sheaf. Then `K ⟶ ε_{X,*}ε_X⁻¹K` is an
isomorphism: `ε_{X,*}` is restriction along the identity-on-spaces functor, hence fully faithful,
and `K` is in its essential image. -/
theorem isIso_phToBigEtaleMorphism_unit_app_of_isSheaf (X : P.Spaces)
    (K : Sheaf (E.bigEtaleTopology (etaleSpace P E h X)) (Type (u + 1)))
    (hK : Presheaf.IsSheaf (BigPHSpaceOver.topology P X)
      ((Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).functor.op ⋙ K.obj)) :
    IsIso ((phToBigEtaleMorphism P E h X).adj.unit.app K) := by
  cases P with
  | mk pSchemeSite pSchemeMem pFppfSite pFppfMem pCutoffEq pInitial pInitialSmall pInitialPH
      pBound pOrdinal pOrdinalLim pInitialBounded pIsSite pRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let P' : BigPHSpaceSite S :=
        ⟨pSchemeSite, pSchemeMem, pFppfSite, pFppfMem, pCutoffEq, pInitial, pInitialSmall,
          pInitialPH, pBound, pOrdinal, pOrdinalLim, pInitialBounded, pIsSite, pRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, pFppfSite, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      let ff : (phToBigEtaleMorphism P' E' rfl X).pushforward.FullyFaithful :=
        { preimage := fun f => ObjectProperty.homMk f.hom }
      have := ff.full
      have := ff.faithful
      rw [Adjunction.isIso_unit_app_iff_mem_essImage]
      exact ⟨⟨K.obj, hK⟩, ⟨Iso.refl _⟩⟩

/-- **Stacks 0DGT, part (1), `ε_{X,*}a_X⁻¹ℱ = π_X⁻¹ℱ`.** For a sheaf of sets `ℱ` on `X_étale` the
unit `π_X⁻¹ℱ ⟶ ε_{X,*}ε_X⁻¹π_X⁻¹ℱ = ε_{X,*}a_X⁻¹ℱ` is an isomorphism. -/
@[stacks 0DGT "part (1), the equality ε_{X,*}a_X⁻¹ℱ = π_X⁻¹ℱ"]
theorem isIso_phToBigEtale_unit_app_inverseImage
    (X : P.Spaces)
    (ℱ : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      (Type (u + 1))) :
    IsIso ((phToBigEtaleMorphism P E h X).adj.unit.app
      ((E.bigToSmallEtaleMorphism (etaleSpace P E h X)).inverseImage.obj ℱ)) :=
  isIso_phToBigEtaleMorphism_unit_app_of_isSheaf P E h X _
    (isSheaf_bigToSmallEtale_inverseImage P E h X ℱ)

/-- **Stacks 0DGT, part (1), `a_{X,*}a_X⁻¹ℱ = ℱ`.** For a sheaf of sets `ℱ` on `X_étale` the unit
`ℱ ⟶ a_{X,*}a_X⁻¹ℱ` is an isomorphism. It is the unit of `π_X⁻¹ ⊣ π_{X,*}`, an isomorphism by
Stacks 0DF3, followed by `π_{X,*}` of the unit of `ε_X⁻¹ ⊣ ε_{X,*}` at `π_X⁻¹ℱ`. -/
@[stacks 0DGT "part (1), the equality a_{X,*}a_X⁻¹ℱ = ℱ"]
theorem isIso_phToSmallEtale_unit_app
    (X : P.Spaces)
    (ℱ : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      (Type (u + 1))) :
    IsIso ((phToSmallEtaleMorphism P E h X).adj.unit.app ℱ) := by
  have := E.isIso_bigToSmallEtaleMorphism_unit (etaleSpace P E h X)
  have := isIso_phToBigEtale_unit_app_inverseImage P E h X ℱ
  change IsIso (((E.bigToSmallEtaleMorphism (etaleSpace P E h X)).adj.comp
    (phToBigEtaleMorphism P E h X).adj).unit.app ℱ)
  rw [Adjunction.comp_unit_app]
  infer_instance

/-- The unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism. -/
theorem isIso_phToSmallEtaleMorphism_unit
    (X : P.Spaces) :
    IsIso (phToSmallEtaleMorphism P E h X).adj.unit := by
  have : ∀ ℱ, IsIso ((phToSmallEtaleMorphism P E h X).adj.unit.app ℱ) := fun ℱ ↦
    isIso_phToSmallEtale_unit_app P E h X ℱ
  exact NatIso.isIso_of_isIso_app _

/-- `a_X⁻¹` is fully faithful, its unit being an isomorphism. -/
def phToSmallEtale_inverseImage_fullyFaithful
    (X : P.Spaces) :
    (phToSmallEtaleMorphism P E h X).inverseImage.FullyFaithful :=
  haveI := isIso_phToSmallEtaleMorphism_unit P E h X
  (phToSmallEtaleMorphism P E h X).adj.fullyFaithfulLOfIsIsoUnit

/-- Stacks 0DGT (1), first clause, as a natural isomorphism `ε_{X,*} ∘ a_X⁻¹ ≅ π_X⁻¹`: the
inverse of the unit of `ε_X⁻¹ ⊣ ε_{X,*}` whiskered by `π_X⁻¹`. -/
def phToSmallEtale_inverseImage_comp_phToBigEtale_pushforwardIso
    (X : P.Spaces) :
    (phToSmallEtaleMorphism P E h X).inverseImage ⋙ (phToBigEtaleMorphism P E h X).pushforward ≅
      (E.bigToSmallEtaleMorphism (etaleSpace P E h X)).inverseImage :=
  haveI : ∀ G, IsIso ((Functor.whiskerLeft
      (E.bigToSmallEtaleMorphism (etaleSpace P E h X)).inverseImage
      (phToBigEtaleMorphism P E h X).adj.unit).app G) := fun G ↦
    isIso_phToBigEtale_unit_app_inverseImage P E h X G
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerLeft (E.bigToSmallEtaleMorphism (etaleSpace P E h X)).inverseImage
      (phToBigEtaleMorphism P E h X).adj.unit)
  (asIso (Functor.whiskerLeft (E.bigToSmallEtaleMorphism (etaleSpace P E h X)).inverseImage
      (phToBigEtaleMorphism P E h X).adj.unit)).symm

/-- Stacks 0DGT (1), second clause, as a natural isomorphism `a_{X,*} ∘ a_X⁻¹ ≅ 𝟭`: the inverse
of the unit of `a_X⁻¹ ⊣ a_{X,*}`. -/
def phToSmallEtale_inverseImage_comp_pushforwardIso
    (X : P.Spaces) :
    (phToSmallEtaleMorphism P E h X).inverseImage ⋙
        (phToSmallEtaleMorphism P E h X).pushforward ≅ 𝟭 _ :=
  haveI := isIso_phToSmallEtaleMorphism_unit P E h X
  (asIso (phToSmallEtaleMorphism P E h X).adj.unit).symm

/-- An abelian big étale sheaf on `X` whose underlying sheaf of sets is `π_X⁻¹G` is a ph sheaf:
the sheaf condition for abelian groups is detected by the underlying sets. -/
theorem isSheaf_of_forget_iso_bigToSmallEtale_inverseImage
    (X : P.Spaces)
    (K : Sheaf (E.bigEtaleTopology (etaleSpace P E h X)) AddCommGrpCat.{u + 1})
    (G : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      (Type (u + 1)))
    (e : (sheafCompose _ (forget AddCommGrpCat.{u + 1})).obj K ≅
      (E.bigToSmallEtaleMorphism (etaleSpace P E h X)).inverseImage.obj G) :
    Presheaf.IsSheaf (BigPHSpaceOver.topology P X)
      ((Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).functor.op ⋙ K.obj) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget AddCommGrpCat.{u + 1})]
  refine (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerLeft
    (Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).functor.op
    ((sheafToPresheaf _ _).mapIso e))).2 ?_
  exact isSheaf_bigToSmallEtale_inverseImage P E h X G

/-- **The abelian `π_X⁻¹ℱ` is a ph sheaf.** For an abelian sheaf `ℱ` on `X_étale`, the abelian
inverse image `CategoryTheory.Sites.abelianInverseImage π_X ℱ` (Stacks 04JC), read on the big ph
slice at `X`, is a sheaf for the big ph topology: its underlying sheaf of sets is `π_X⁻¹` of that
of `ℱ`. -/
theorem isSheaf_bigToSmallEtale_abelianInverseImage
    (X : P.Spaces)
    (ℱ : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      AddCommGrpCat.{u + 1}) :
    Presheaf.IsSheaf (BigPHSpaceOver.topology P X)
      ((Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).functor.op ⋙
        ((Sites.abelianInverseImage (E.bigToSmallEtaleMorphism (etaleSpace P E h X))).obj ℱ).obj) :=
  isSheaf_of_forget_iso_bigToSmallEtale_inverseImage P E h X _ _
    ((Sites.abelianInverseImage_forgetIso (E.bigToSmallEtaleMorphism (etaleSpace P E h X))).app ℱ)

end AlgebraicGeometry.BigPHSpaceSite

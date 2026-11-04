module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleRingedToposEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism

/-!
# Transporting 2-isomorphisms and the canonical morphism along the change of big site

An object `U` of a big fppf site over `S` is at once a chart of the representable algebraic
space `yoneda.obj U` and a scheme of the big étale site
`AlgebraicGeometry.associatedBigEtaleSite B`, and
`AlgebraicGeometry.Space.representedSmallEtaleRingedToposHom` identifies the two readings of
its small étale ringed topos.  `AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHom`
conjugates a morphism of the small étale ringed topoi of two representable algebraic spaces
into a morphism of the small étale ringed topoi of the two schemes.

This file carries the two remaining pieces of structure across that conjugation: a
2-isomorphism of morphisms of ringed topoi, and the canonical morphism of small étale ringed
topoi of a morphism of schemes.

## Main definitions

* `CategoryTheory.Equivalence.conjugateSquareIso` and `.conjugateSquareIso'`: transposing a
  square of functors across two equivalences, in both directions.
* `AlgebraicGeometry.RingedToposHom.TwoIso.ofCommonRightAdjoint`: two morphisms of ringed topoi
  whose inverse images are left adjoints of one and the same functor, and whose structure maps
  are the adjunct of one and the same morphism, are 2-isomorphic.
* `AlgebraicGeometry.Space.representedSmallEtaleRestrictionAdjunction`: restriction along the
  equivalence of the two small étale sites of a chart is left adjoint to restriction along the
  inverse equivalence.
* `AlgebraicGeometry.Space.transportRightAdjoint`, `transportStructureMap` and the two
  adjunctions `transportSchemeAdjunction`, `transportSpaceAdjunction`: the common right adjoint
  of the two composites round the naturality square, the common adjunct, and the two
  adjunctions exhibiting the two inverse images as left adjoints of it.

## Main results

* `AlgebraicGeometry.Space.twoIsoSchemeOfRepresentedRingedToposHom`: **the transport of
  `AlgebraicGeometry.RingedToposHom.TwoIso`** — the conjugation carries a 2-isomorphism to a
  2-isomorphism.  It is two whiskerings and nothing else.
* `AlgebraicGeometry.Space.representedSmallEtaleRingedToposNaturality`: **the transport of
  `AlgebraicGeometry.smallEtaleRingedToposHom`** — the identification is natural in the chart,
  so the morphism of small étale ringed topoi of a morphism of schemes does not depend on which
  big site the schemes are read in.  `…NaturalityOfMap` is the same with the representability
  witness and the continuity of chart base change discharged, neither being mentioned by either
  side of the 2-isomorphism.
* `AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget_comp_eq_homEquiv_symm`: the
  inverse-image structure map of a composite, as an adjunct for a composite of two *chosen*
  adjunctions.  This is the bookkeeping of each side of the square, done once with the four
  functors and both adjunctions as variables.
* `AlgebraicGeometry.Space.transportSquare_structureMap`: the structure-map equation of the
  square, on the source of the equivalence, and
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_inv_comp_snd`, the one
  geometric input it reduces to.

## Implementation notes

The direct image of `AlgebraicGeometry.Space.representedSmallEtaleRingedToposHom` is
`CategoryTheory.Functor.inv` of restriction along the equivalence of sites — a quasi-inverse
produced by `CategoryTheory.Functor.objPreimage`, hence by choice — so **no comparison of the
direct images of the two composites can be computed on sections**, and the direct-image form of
the square is not the form to work in.  Its *inverse* image, by contrast, is restriction along
the equivalence on the nose, and the comparison of structure sheaves
`AlgebraicGeometry.Space.representedCommRingStructureIso` is the identity on underlying
presheaves.  That is why the square is stated through
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso`, packaged here as
`AlgebraicGeometry.RingedToposHom.TwoIso.ofCommonRightAdjoint`: neither adjunction it consumes
has to be the canonical one, and no hypothesis relates the chosen right adjoint to either
direct image.

Three identities of the identification are definitional and carry the whole comparison of the
two structure sheaves: restriction along the equivalence carries the structure sheaf of the
scheme's small étale site to the structure sheaf of the chart's and back (both by `rfl`), the
inverse-image form of the identification's structure map is the identity, and the counit of
`representedSmallEtaleRestrictionAdjunction` is the identity at the structure sheaf — the unit
of the equivalence of sites being the identity on underlying schemes.

The geometric content is one scheme identity,
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_inv_comp_snd`: the comparison
of the two fibre products is a morphism over their projections to the chart.  Everything else is
adjunction bookkeeping, and it is done with the functors as variables
(`CategoryTheory.Equivalence.conjugateSquareIso_hom_app_eq` and
`AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget_comp_eq_homEquiv_symm`) so that at the
geometric instantiation no argument is a restatement.

Two things about `AlgebraicGeometry.Space.chartComparison` are worth knowing.  It, not
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`, is the comparison of the
direct image with chart base change that is computable on sections, which is why
`AlgebraicGeometry.Space.chartComparison_structureSharp` exists and is the input used here; and
its statement carries the continuity of chart base change as a `letI`, which `rw` cannot see
through, so `AlgebraicGeometry.Space.representedChartComparison` restates it with that
continuity as an instance of the ambient context.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory

universe vA uA vB uB vC uC vD uD

/-- **Conjugating a square of functors by two equivalences.**  Given equivalences
`eU : 𝒜 ≌ ℬ` and `eV : 𝒞 ≌ 𝒟` and functors `P : 𝒜 ⥤ 𝒞`, `Q : ℬ ⥤ 𝒟`, an isomorphism
`eU⁻¹ ⋙ P ≅ Q ⋙ eV⁻¹` is the same thing as an isomorphism `P ⋙ eV ≅ eU ⋙ Q`: transpose by
the unit of `eU` and the counit of `eV`. -/
def Equivalence.conjugateSquareIso {𝒜 : Type uA} [Category.{vA} 𝒜] {ℬ : Type uB}
    [Category.{vB} ℬ] {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒟 : Type uD} [Category.{vD} 𝒟]
    (eU : 𝒜 ≌ ℬ) (eV : 𝒞 ≌ 𝒟) (P : 𝒜 ⥤ 𝒞) (Q : ℬ ⥤ 𝒟)
    (τ : eU.inverse ⋙ P ≅ Q ⋙ eV.inverse) :
    P ⋙ eV.functor ≅ eU.functor ⋙ Q :=
  Functor.isoWhiskerRight eU.unitIso (P ⋙ eV.functor) ≪≫
    Functor.isoWhiskerLeft eU.functor (Functor.isoWhiskerRight τ eV.functor) ≪≫
      Functor.isoWhiskerLeft (eU.functor ⋙ Q) eV.counitIso

/-- The reverse transposition: an isomorphism `P ⋙ eV ≅ eU ⋙ Q` gives one
`eU⁻¹ ⋙ P ≅ Q ⋙ eV⁻¹`. -/
def Equivalence.conjugateSquareIso' {𝒜 : Type uA} [Category.{vA} 𝒜] {ℬ : Type uB}
    [Category.{vB} ℬ] {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒟 : Type uD} [Category.{vD} 𝒟]
    (eU : 𝒜 ≌ ℬ) (eV : 𝒞 ≌ 𝒟) (P : 𝒜 ⥤ 𝒞) (Q : ℬ ⥤ 𝒟)
    (τ : P ⋙ eV.functor ≅ eU.functor ⋙ Q) :
    eU.inverse ⋙ P ≅ Q ⋙ eV.inverse :=
  Functor.isoWhiskerLeft (eU.inverse ⋙ P) eV.unitIso ≪≫
    Functor.isoWhiskerLeft eU.inverse (Functor.isoWhiskerRight τ eV.inverse) ≪≫
      Functor.isoWhiskerRight eU.counitIso (Q ⋙ eV.inverse)

/-- **The conjugated square, read at one object and against one morphism.**  A morphism `u` into
`P A` and a morphism `w` into `Q (eU A)` are carried to one another by
`CategoryTheory.Equivalence.conjugateSquareIso` as soon as their transposes across `eV` agree
through the unit of `eU` and the given isomorphism `τ`.

This is the whole bookkeeping of the naturality square of an identification: it reduces an
equation over the target of `eV` to one over its source, where both sides are given by the two
structure maps. -/
theorem Equivalence.conjugateSquareIso_hom_app_eq {𝒜 : Type uA} [Category.{vA} 𝒜] {ℬ : Type uB}
    [Category.{vB} ℬ] {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒟 : Type uD} [Category.{vD} 𝒟]
    (eU : 𝒜 ≌ ℬ) (eV : 𝒞 ≌ 𝒟) (P : 𝒜 ⥤ 𝒞) (Q : ℬ ⥤ 𝒟)
    (τ : eU.inverse ⋙ P ≅ Q ⋙ eV.inverse) (A : 𝒜) {N : 𝒞}
    (u : N ⟶ P.obj A) (w : eV.functor.obj N ⟶ Q.obj (eU.functor.obj A))
    (h : u ≫ P.map (eU.unitIso.hom.app A) ≫ τ.hom.app (eU.functor.obj A) =
      eV.unitIso.hom.app N ≫ eV.inverse.map w) :
    eV.functor.map u ≫ (eU.conjugateSquareIso eV P Q τ).hom.app A = w := by
  have hcomp : (eU.conjugateSquareIso eV P Q τ).hom.app A =
      eV.functor.map (P.map (eU.unitIso.hom.app A)) ≫
        eV.functor.map (τ.hom.app (eU.functor.obj A)) ≫
          eV.counitIso.hom.app (Q.obj (eU.functor.obj A)) := rfl
  rw [hcomp, ← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
    Category.assoc, h, Functor.map_comp, Category.assoc]
  simp

end CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

section CommonRightAdjoint

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₁}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₁})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [A.J.HasSheafCompose (forget CommRingCat.{w₁})]
  [B.J.HasSheafCompose (forget CommRingCat.{w₁})]

/-- **Two morphisms of ringed topoi whose inverse images are left adjoints of one and the same
functor, and whose structure maps are the adjunct of one and the same morphism, are
2-isomorphic.**

This is the form in which a commuting square of ringed topoi arrives whenever two of its sides
are identifications: the direct images of the two composites need not be computable — they are
quasi-inverses chosen by `CategoryTheory.Functor.inv` — while a *concrete* common right adjoint
`G` is available, and then the whole comparison is
`CategoryTheory.Adjunction.leftAdjointUniq`, whose action on an adjunct is to change nothing but
the adjunction it is taken for
(`CategoryTheory.Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm`).

No hypothesis relates `G` to either direct image, and neither adjunction has to be the
canonical one. -/
noncomputable def TwoIso.ofCommonRightAdjoint {p q : RingedToposHom A B}
    (G : A.Topos ⥤ B.Topos)
    (adjp : p.toToposHom.inverseImage ⊣ G) (adjq : q.toToposHom.inverseImage ⊣ G)
    (t : B.forgetRing.obj B.O ⟶ G.obj (A.forgetRing.obj A.O))
    (hp : p.fSharpInverseImageForget =
      (adjp.homEquiv (B.forgetRing.obj B.O) (A.forgetRing.obj A.O)).symm t)
    (hq : q.fSharpInverseImageForget =
      (adjq.homEquiv (B.forgetRing.obj B.O) (A.forgetRing.obj A.O)).symm t) :
    TwoIso p q :=
  TwoIso.ofInverseImageIso (adjq.leftAdjointUniq adjp)
    (by
      rw [forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget,
        forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget, hp, hq]
      exact Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm adjq adjp t)

end CommonRightAdjoint

section CompAdjunct

universe v₃ u₃

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₁}}
  {C : RingedTopos.{v₃, u₃, w₁}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₁})]
  [C.J.HasSheafCompose (forget RingCat.{w₁})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]

/-- **The inverse-image structure map of a composite, as an adjunct for a composite of two
chosen adjunctions.**  Each factor's structure map is given as the adjunct of a morphism into a
*chosen* right adjoint — not necessarily the direct image — and the structure map of the
composite is then the adjunct, for the composite adjunction, of the evident composite of the
two.

This is the bookkeeping that the naturality square of an identification of ringed topoi needs
on each of its two sides, and it is done once here with the four functors and both adjunctions
as variables: at a geometric instantiation every hypothesis is then an existing lemma applied
verbatim. -/
theorem fSharpInverseImageForget_comp_eq_homEquiv_symm
    (f : RingedToposHom B C) (ε : RingedToposHom A B)
    {Rf : B.Topos ⥤ C.Topos} (adjf : f.toToposHom.inverseImage ⊣ Rf)
    {Rε : A.Topos ⥤ B.Topos} (adjε : ε.toToposHom.inverseImage ⊣ Rε)
    (a : C.forgetRing.obj C.O ⟶ Rf.obj (B.forgetRing.obj B.O))
    (haf : f.fSharpInverseImageForget =
      (adjf.homEquiv (C.forgetRing.obj C.O) (B.forgetRing.obj B.O)).symm a)
    (u : B.forgetRing.obj B.O ⟶ Rε.obj (A.forgetRing.obj A.O))
    (hε : ε.fSharpInverseImageForget =
      (adjε.homEquiv (B.forgetRing.obj B.O) (A.forgetRing.obj A.O)).symm u)
    (t : C.forgetRing.obj C.O ⟶ (Rε ⋙ Rf).obj (A.forgetRing.obj A.O))
    (ht : t = a ≫ Rf.map u) :
    (f.comp ε).fSharpInverseImageForget =
      ((adjf.comp adjε).homEquiv (C.forgetRing.obj C.O)
        (A.forgetRing.obj A.O)).symm t := by
  rw [ht, Adjunction.comp_homEquiv_symm_comp, ← haf, ← hε, fSharpInverseImageForget_comp]

end CompAdjunct

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U V : BigFppfOver B S hS)

/-- Conjugation carries a 2-isomorphism to a 2-isomorphism. -/
noncomputable def twoIsoSchemeOfRepresentedRingedToposHom
    {ψ₁ ψ₂ : RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)}
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} ψ₁ ψ₂) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (schemeOfRepresentedRingedToposHom B S hS U V ψ₁)
      (schemeOfRepresentedRingedToposHom B S hS U V ψ₂) :=
  RingedToposHom.TwoIso.whiskerRight.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
    (RingedToposHom.TwoIso.whiskerLeft.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
      (representedSmallEtaleRingedToposInverse B S hS U) t)
    (representedSmallEtaleRingedToposHom B S hS V)




/-! ### The naturality square of the identification -/

/-- **The equivalence of the two small étale sheaf topoi of a chart**, induced by the
equivalence of the two sites.  Its `functor` is restriction along the inverse equivalence and
its `inverse` is restriction along the equivalence, and its unit and counit are restriction
along the unit and counit of the equivalence of sites — all of it explicit, which is what makes
the naturality square below computable. -/
noncomputable abbrev representedSmallEtaleSheafCongr :
    Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) (Type u) ≌
      Sheaf (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) (Type u) :=
  (representedSmallEtaleEquivalence B S hS U).sheafCongr
    (SmallEtale.topology B S hS (yoneda.obj U))
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) (Type u)

/-- **Restriction along the equivalence of the two small étale sites of a chart is left adjoint
to restriction along the inverse equivalence.**  This is the adjoint equivalence of
`CategoryTheory.Equivalence.sheafCongr`, whose unit and counit are restriction along the unit
and counit of the equivalence of sites — in contrast to the adjunction carried by
`AlgebraicGeometry.Space.representedSmallEtaleToposHom`, whose right adjoint is
`CategoryTheory.Functor.inv`, a quasi-inverse produced by choice. -/
noncomputable def representedSmallEtaleRestrictionAdjunction :
    (representedSmallEtaleToposHom B S hS U).inverseImage ⊣
      representedSmallEtaleRestrictionInverse B S hS U :=
  (representedSmallEtaleSheafCongr B S hS U).symm.toAdjunction

/-- **The structure map of the identification, in inverse-image form, is the identity on
underlying sheaves of sets.**  Both sides send a chart to the global regular functions on the
same scheme, which is what `AlgebraicGeometry.Space.representedCommRingStructureIso` records. -/
theorem forgetRing_map_representedSmallEtaleRingedToposHom_fSharpInverseImage :
    (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.map
        (representedSmallEtaleRingedToposHom B S hS U).fSharpInverseImage = 𝟙 _ := by
  rw [representedSmallEtaleRingedToposHom_fSharpInverseImage]
  rfl

/-- The same, in the spelling `AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget`. -/
theorem representedSmallEtaleRingedToposHom_fSharpInverseImageForget :
    (representedSmallEtaleRingedToposHom B S hS U).fSharpInverseImageForget =
      𝟙 ((smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
        (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) :=
  (RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
      (representedSmallEtaleRingedToposHom B S hS U)).symm.trans
    (forgetRing_map_representedSmallEtaleRingedToposHom_fSharpInverseImage B S hS U)

/-- **The structure map of the identification is the adjunct of the identity** for the adjoint
equivalence of `AlgebraicGeometry.Space.representedSmallEtaleRestrictionAdjunction`.  This is
the shape in which
`AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget_comp_eq_homEquiv_symm` consumes it. -/
theorem representedSmallEtale_homEquiv_fSharpInverseImageForget :
    (representedSmallEtaleRestrictionAdjunction B S hS U).homEquiv
        ((_root_.AlgebraicGeometry.RingedSite.toRingedTopos
            (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).forgetRing.obj
          (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
            (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).O)
        ((smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)
        (representedSmallEtaleRingedToposHom B S hS U).fSharpInverseImageForget = 𝟙 _ :=
  (congrArg ((representedSmallEtaleRestrictionAdjunction B S hS U).homEquiv _ _)
      (representedSmallEtaleRingedToposHom_fSharpInverseImageForget B S hS U)).trans rfl

/-- **The counit of the adjoint equivalence is the identity at the structure sheaf.**  The unit
of the equivalence of sites is the identity on underlying schemes, so restricting the global
regular functions along it changes nothing. -/
theorem representedSmallEtaleRestrictionAdjunction_counit_structureSheaf :
    (representedSmallEtaleRestrictionAdjunction B S hS U).counit.app
        ((smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) = 𝟙 _ :=
  rfl

variable (g : U ⟶ V)

/-- The common right adjoint of the two composites round the naturality square: restriction
along the inverse equivalence of the sites of `U`, followed by small étale base change of
schemes along the morphism underlying `g`. -/
noncomputable abbrev transportRightAdjoint :
    Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) (Type u) ⥤
      Sheaf (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property) (Type u) :=
  representedSmallEtaleRestrictionInverse B S hS U ⋙
    (_root_.AlgebraicGeometry.smallEtaleRingedToposHom
      (associatedBigEtaleSite B) g.left).toToposHom.pushforward

/-- The adjunction exhibiting the inverse image of the scheme-side composite as a left adjoint
of `AlgebraicGeometry.Space.transportRightAdjoint`. -/
noncomputable def transportSchemeAdjunction :
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left)
        (representedSmallEtaleRingedToposHom B S hS U)).toToposHom.inverseImage ⊣
      transportRightAdjoint B S hS U V g :=
  (_root_.AlgebraicGeometry.smallEtaleRingedToposHom
      (associatedBigEtaleSite B) g.left).toToposHom.adj.comp
    (representedSmallEtaleRestrictionAdjunction B S hS U)

/-- **The common adjunct of the two composites round the square**: the structure map of the
morphism of small étale ringed topoi of the morphism of schemes underlying `g`, whose target is
the common right adjoint applied to the structure sheaf because restriction along the inverse
equivalence carries the structure sheaf of the chart to the structure sheaf of the scheme on the
nose. -/
noncomputable abbrev transportStructureMap :
    (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property)).forgetRing.obj
        (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property)).O ⟶
      (transportRightAdjoint B S hS U V g).obj
        ((smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) :=
  RingedToposHom.forgetFSharp
    (_root_.AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left)

/-- **The scheme-side composite's structure map is the adjunct of the common one.** -/
theorem transportScheme_fSharpInverseImageForget :
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left)
        (representedSmallEtaleRingedToposHom B S hS U)).fSharpInverseImageForget =
      ((transportSchemeAdjunction B S hS U V g).homEquiv _ _).symm
        (transportStructureMap B S hS U V g) :=
  RingedToposHom.fSharpInverseImageForget_comp_eq_homEquiv_symm
    (_root_.AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left)
    (representedSmallEtaleRingedToposHom B S hS U)
    (_root_.AlgebraicGeometry.smallEtaleRingedToposHom
      (associatedBigEtaleSite B) g.left).toToposHom.adj
    (representedSmallEtaleRestrictionAdjunction B S hS U)
    (RingedToposHom.forgetFSharp
      (_root_.AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left))
    rfl (𝟙 _)
    ((Equiv.eq_symm_apply _).mpr
      (representedSmallEtale_homEquiv_fSharpInverseImageForget B S hS U))
    (transportStructureMap B S hS U V g) rfl

/-! ### The space side of the square -/

variable (hg : yoneda.relativelyRepresentable (yoneda.map g))
  [(smallBaseChange B S hS (representedSpaceMap B S hS g) hg).IsContinuous
    (SmallEtale.topology B S hS (yoneda.obj V)) (SmallEtale.topology B S hS (yoneda.obj U))]

/-- **The sheaf-level image of the site square of
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`**: restriction along the
equivalence for `U`, followed by restriction along chart base change, is restriction along
base change of schemes followed by restriction along the equivalence for `V`. -/
noncomputable def representedSmallEtaleBaseChangeRestrictionIso :
    representedSmallEtaleRestriction B S hS U ⋙
        (smallBaseChange B S hS (representedSpaceMap B S hS g) hg).sheafPushforwardContinuous
          (Type u) (SmallEtale.topology B S hS (yoneda.obj V))
          (SmallEtale.topology B S hS (yoneda.obj U)) ≅
      (_root_.AlgebraicGeometry.smallEtaleRingedToposHom
            (associatedBigEtaleSite B) g.left).toToposHom.pushforward ⋙
        representedSmallEtaleRestriction B S hS V :=
  letI : (_root_.AlgebraicGeometry.smallEtaleBaseChange
      (associatedBigEtaleSite B) g.left).IsContinuous
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :=
    _root_.AlgebraicGeometry.smallEtaleBaseChange_isContinuous (associatedBigEtaleSite B) g.left
  letI := Functor.isContinuous_comp (representedSmallEtaleEquivalence B S hS V).functor
    (_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) g.left)
    (SmallEtale.topology B S hS (yoneda.obj V))
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
  Functor.sheafPushforwardContinuousComp'
    (representedSmallEtaleBaseChangeIso B S hS g hg) (Type u)
    (SmallEtale.topology B S hS (yoneda.obj V))
    (SmallEtale.topology B S hS (yoneda.obj U))
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)

/-- `AlgebraicGeometry.Space.chartComparison` with its type written out, so that the continuity
of chart base change is an ordinary instance of the ambient context rather than a `let` inside
the statement; `rw` cannot see through the latter. -/
noncomputable def representedChartComparison :
    smallEtaleDirectImage B S hS (representedSpaceMap B S hS g) ≅
      (smallBaseChange B S hS (representedSpaceMap B S hS g) hg).sheafPushforwardContinuous
        (Type u) (SmallEtale.topology B S hS (yoneda.obj V))
        (SmallEtale.topology B S hS (yoneda.obj U)) :=
  chartComparison B S hS (representedSpaceMap B S hS g) hg

/-- **The two right adjoints agree**: restriction along chart base change followed by
restriction along the inverse equivalence for `V` is restriction along the inverse equivalence
for `U` followed by base change of schemes.  This is the conjugate of the sheaf-level square. -/
noncomputable def transportRightAdjointIso :
    (smallBaseChange B S hS (representedSpaceMap B S hS g) hg).sheafPushforwardContinuous
          (Type u) (SmallEtale.topology B S hS (yoneda.obj V))
          (SmallEtale.topology B S hS (yoneda.obj U)) ⋙
        representedSmallEtaleRestrictionInverse B S hS V ≅
      transportRightAdjoint B S hS U V g :=
  (representedSmallEtaleSheafCongr B S hS U).conjugateSquareIso
    (representedSmallEtaleSheafCongr B S hS V) _ _
    (representedSmallEtaleBaseChangeRestrictionIso B S hS U V g hg)

/-- **The structure map of the space-side morphism, read through the chart comparison**:
pullback of regular functions along the cartesian chart projection, by
`AlgebraicGeometry.Space.chartComparison_structureSharp`. -/
noncomputable abbrev transportSpaceStructureMap :
    (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩).forgetRing.obj
        (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩).O ⟶
      ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).sheafPushforwardContinuous
          (Type u) (SmallEtale.topology B S hS (yoneda.obj V))
          (SmallEtale.topology B S hS (yoneda.obj U))).obj
        ((smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) :=
  RingedToposHom.forgetFSharp
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)) ≫
    (representedChartComparison B S hS U V g hg).hom.app
      ((smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
        (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)

/-- The adjunction for the space-side composite, with its right adjoint in the form the chart
comparison gives, before the conjugation of `AlgebraicGeometry.Space.transportRightAdjointIso`. -/
noncomputable def transportSpaceAdjunction₀ :
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (representedSmallEtaleRingedToposHom B S hS V)
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g))).toToposHom.inverseImage ⊣
      (smallBaseChange B S hS (representedSpaceMap B S hS g) hg).sheafPushforwardContinuous
          (Type u) (SmallEtale.topology B S hS (yoneda.obj V))
          (SmallEtale.topology B S hS (yoneda.obj U)) ⋙
        representedSmallEtaleRestrictionInverse B S hS V :=
  (representedSmallEtaleRestrictionAdjunction B S hS V).comp
    ((smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toToposHom.adj.ofNatIsoRight
      (representedChartComparison B S hS U V g hg))

/-- The adjunction exhibiting the inverse image of the space-side composite as a left adjoint of
the common right adjoint `AlgebraicGeometry.Space.transportRightAdjoint`. -/
noncomputable abbrev transportSpaceAdjunction :
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (representedSmallEtaleRingedToposHom B S hS V)
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g))).toToposHom.inverseImage ⊣
      transportRightAdjoint B S hS U V g :=
  (transportSpaceAdjunction₀ B S hS U V g hg).ofNatIsoRight
    (transportRightAdjointIso B S hS U V g hg)

/-- **The space-side structure map, read through the chart comparison, is pullback of regular
functions along the cartesian chart projection.**  This is the morphism-level form of
`AlgebraicGeometry.Space.chartComparison_structureSharp`. -/
theorem transportSpaceStructureMap_eq :
    transportSpaceStructureMap B S hS U V g hg =
      (sheafCompose (SmallEtale.topology B S hS (yoneda.obj V)) (forget CommRingCat.{u})).map
        (smallBaseChangeSharpCommRingCat B S hS (representedSpaceMap B S hS g) hg) := by
  refine CategoryTheory.Sheaf.hom_ext_sections fun W s => ?_
  exact chartComparison_structureSharp B S hS (representedSpaceMap B S hS g) hg W.unop s

omit [(smallBaseChange B S hS (representedSpaceMap B S hS g) hg).IsContinuous
    (SmallEtale.topology B S hS (yoneda.obj V)) (SmallEtale.topology B S hS (yoneda.obj U))] in
/-- **The inverse of the chart comparison, followed by the cartesian projection of chart base
change, is the cartesian projection of base change of schemes.**  This is the one geometric
input of the naturality square: both objects are fibre products of the same cospan, and the
comparison is a morphism over the two projections. -/
theorem representedSmallEtaleBaseChangeComponent_inv_comp_snd
    (Z : SmallEtale B S hS (yoneda.obj V)) :
    (representedSmallEtaleBaseChangeComponent B S hS g hg Z).inv.hom.left ≫
        (hg.snd Z.1.hom).left =
      Limits.pullback.fst (yonedaEquiv Z.1.hom).left g.left := by
  have h1 : (representedSmallEtaleBaseChangeComponent B S hS g hg Z).hom.hom.left ≫
      Limits.pullback.fst (yonedaEquiv Z.1.hom).left g.left = (hg.snd Z.1.hom).left := by
    rw [representedSmallEtaleBaseChangeComponent_hom]
    exact (isPullback_representedChart_schemes B S hS g hg Z).isoIsPullback_hom_fst _ _ _
  have h2 : (representedSmallEtaleBaseChangeComponent B S hS g hg Z).inv.hom.left ≫
      (representedSmallEtaleBaseChangeComponent B S hS g hg Z).hom.hom.left = 𝟙 _ :=
    congrArg (fun m => m.hom.left)
      (representedSmallEtaleBaseChangeComponent B S hS g hg Z).inv_hom_id
  exact (congrArg
      (fun m => (representedSmallEtaleBaseChangeComponent B S hS g hg Z).inv.hom.left ≫ m)
      h1.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ Limits.pullback.fst (yonedaEquiv Z.1.hom).left g.left) h2).trans
        (Category.id_comp _)))

/-- **The structure-map equation of the naturality square, on the source of the equivalence.**
The space-side structure map, carried through the sheaf-level square, is the scheme-side
structure map read along the inverse equivalence.  Over an étale chart both sides are pullback
of regular functions along a projection of one and the same fibre product of schemes, and the
comparison of the two fibre products is a morphism over those projections — which is
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_inv_comp_snd`. -/
theorem transportSquare_structureMap :
    transportSpaceStructureMap B S hS U V g hg ≫
      ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).sheafPushforwardContinuous
          (Type u) (SmallEtale.topology B S hS (yoneda.obj V))
          (SmallEtale.topology B S hS (yoneda.obj U))).map
        ((representedSmallEtaleSheafCongr B S hS U).unitIso.hom.app
          ((smallEtaleRingedTopos B S hS
              ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
            (smallEtaleRingedTopos B S hS
              ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)) ≫
        (representedSmallEtaleBaseChangeRestrictionIso B S hS U V g hg).hom.app
          ((representedSmallEtaleSheafCongr B S hS U).functor.obj
            ((smallEtaleRingedTopos B S hS
                ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
              (smallEtaleRingedTopos B S hS
                ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)) =
    (representedSmallEtaleSheafCongr B S hS V).unitIso.hom.app
        ((smallEtaleRingedTopos B S hS
            ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩).forgetRing.obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩).O) ≫
      (representedSmallEtaleSheafCongr B S hS V).inverse.map
        (transportStructureMap B S hS U V g) := by
  rw [transportSpaceStructureMap_eq]
  refine CategoryTheory.Sheaf.hom_ext_sections fun W s => ?_
  have hGamma : ∀ {X Y Z : B.Schemes} (a : X ⟶ Y) (b : Y ⟶ Z)
      (t : (forget CommRingCat.{u}).obj (Scheme.Γ.obj (Opposite.op (B.inclusion.obj Z)))),
      (forget CommRingCat.{u}).map (Scheme.Γ.map (B.inclusion.map (a ≫ b)).op) t =
        (forget CommRingCat.{u}).map (Scheme.Γ.map (B.inclusion.map a).op)
          ((forget CommRingCat.{u}).map (Scheme.Γ.map (B.inclusion.map b).op) t) := by
    intro X Y Z a b t
    rw [B.inclusion.map_comp, op_comp, Scheme.Γ.map_comp]
    rfl
  exact (hGamma (representedSmallEtaleBaseChangeComponent B S hS g hg W.unop).inv.hom.left
      (hg.snd W.unop.1.hom).left s).symm.trans
    (congrArg (fun m => (forget CommRingCat.{u}).map
        (Scheme.Γ.map (B.inclusion.map m).op) s)
      (representedSmallEtaleBaseChangeComponent_inv_comp_snd B S hS U V g hg W.unop))

/-- **The space side of the square: its structure map is the adjunct of the common one.** -/
theorem transportSpace_fSharpInverseImageForget :
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (representedSmallEtaleRingedToposHom B S hS V)
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g))).fSharpInverseImageForget =
      ((transportSpaceAdjunction B S hS U V g hg).homEquiv _ _).symm
        (transportStructureMap B S hS U V g) := by
  have h0 := RingedToposHom.fSharpInverseImageForget_comp_eq_homEquiv_symm
    (representedSmallEtaleRingedToposHom B S hS V)
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
    (representedSmallEtaleRestrictionAdjunction B S hS V)
    ((smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS g)).toToposHom.adj.ofNatIsoRight
      (representedChartComparison B S hS U V g hg))
    (𝟙 _)
    ((Equiv.eq_symm_apply _).mpr
      (representedSmallEtale_homEquiv_fSharpInverseImageForget B S hS V))
    (transportSpaceStructureMap B S hS U V g hg)
    ((Equiv.eq_symm_apply _).mpr
      ((Adjunction.homEquiv_ofNatIsoRight_apply
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toToposHom.adj
          (representedChartComparison B S hS U V g hg)
          (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS g)).fSharpInverseImageForget).trans
        (congrArg
          (fun m => m ≫ (representedChartComparison B S hS U V g hg).hom.app
            ((smallEtaleRingedTopos B S hS
                ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
              (smallEtaleRingedTopos B S hS
                ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O))
          (Equiv.apply_symm_apply _ _))))
    _ rfl
  refine h0.trans ((congrArg (fun z =>
      ((transportSpaceAdjunction₀ B S hS U V g hg).homEquiv
        ((_root_.AlgebraicGeometry.RingedSite.toRingedTopos
            (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)).forgetRing.obj
          (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
            (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)).O)
        ((smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)).symm z) ?_).trans
    (Adjunction.homEquiv_ofNatIsoRight_symm_apply
      (transportSpaceAdjunction₀ B S hS U V g hg)
      (transportRightAdjointIso B S hS U V g hg)
      (transportStructureMap B S hS U V g)).symm)
  refine (Iso.eq_comp_inv ((transportRightAdjointIso B S hS U V g hg).app _)).mpr ?_
  exact (congrArg (fun m => m ≫ ((transportRightAdjointIso B S hS U V g hg).app
        ((smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)).hom)
      (Category.id_comp ((representedSmallEtaleRestrictionInverse B S hS V).map
        (transportSpaceStructureMap B S hS U V g hg)))).trans
    (Equivalence.conjugateSquareIso_hom_app_eq
      (representedSmallEtaleSheafCongr B S hS U) (representedSmallEtaleSheafCongr B S hS V)
      ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).sheafPushforwardContinuous
        (Type u) (SmallEtale.topology B S hS (yoneda.obj V))
        (SmallEtale.topology B S hS (yoneda.obj U)))
      (_root_.AlgebraicGeometry.smallEtaleRingedToposHom
        (associatedBigEtaleSite B) g.left).toToposHom.pushforward
      (representedSmallEtaleBaseChangeRestrictionIso B S hS U V g hg)
      ((smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
        (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)
      (transportSpaceStructureMap B S hS U V g hg) (transportStructureMap B S hS U V g)
      (transportSquare_structureMap B S hS U V g hg))

/-- **THE NATURALITY SQUARE: the identification of the two readings of a chart's small étale
ringed topos is natural in the chart.**  For a morphism `g : U ⟶ V` of the big fppf category
over `S`, the identification for `V` after the morphism of small étale ringed topoi of the
represented morphism of algebraic spaces is 2-isomorphic to the morphism of small étale ringed
topoi of the underlying morphism of schemes after the identification for `U`.

This is the transport of `AlgebraicGeometry.smallEtaleRingedToposHom` along
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`: the morphism of small étale ringed
topoi of a morphism of schemes does not depend on which big site the schemes are read in. -/
noncomputable def representedSmallEtaleRingedToposNaturality :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (representedSmallEtaleRingedToposHom B S hS V)
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left)
        (representedSmallEtaleRingedToposHom B S hS U)) :=
  RingedToposHom.TwoIso.ofCommonRightAdjoint.{u, u + 1, u, u, u + 1}
    (transportRightAdjoint B S hS U V g)
    (transportSpaceAdjunction B S hS U V g hg)
    (transportSchemeAdjunction B S hS U V g)
    (transportStructureMap B S hS U V g)
    (transportSpace_fSharpInverseImageForget B S hS U V g hg)
    (transportScheme_fSharpInverseImageForget B S hS U V g)

/-- **The naturality square, depending on nothing but the morphism `g`.**  Neither side of the
2-isomorphism mentions the representability witness of the represented morphism or the
continuity of chart base change along it, and both are canonically available, so both are
discharged here. -/
noncomputable def representedSmallEtaleRingedToposNaturalityOfMap :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (representedSmallEtaleRingedToposHom B S hS V)
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left)
        (representedSmallEtaleRingedToposHom B S hS U)) :=
  letI := isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g)
    (relativelyRepresentable_yoneda_map B S hS g)
  representedSmallEtaleRingedToposNaturality B S hS U V g
    (relativelyRepresentable_yoneda_map B S hS g)

end AlgebraicGeometry.Space

end

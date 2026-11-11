module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.TopologicalProperties.RelativeFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PullbackIdentityOnCohomology

/-!
# Cohomological triviality of an étale self-map isomorphic to the identity

Let `g : X ⟶ X` be a morphism of schemes and suppose that every étale `X`-scheme `U` is
isomorphic over `X` to its base change `U ×_{g} X`, functorially in `U`. Then `g` induces
the identity on étale cohomology of any abelian sheaf. This is the étale-site lemma behind
the baffling theorem: the absolute Frobenius of a scheme in characteristic `p` satisfies
the hypothesis, so it acts trivially on cohomology.

The hypothesis is recorded as a natural isomorphism `𝟭 X.Etale ≅ smallEtaleBaseChange g`
of site endofunctors of the small étale site of `X`. It identifies the direct image with the
identity functor on abelian sheaves, and hence, by taking the left-adjoint mate, the pullback
`g^{-1}` as well. The unit of the pullback–direct image adjunction read through the first
identification is the map `F ⟶ g^{-1}F` on sheaves, and the map it induces on cohomology is
the pullback of cohomology classes along `g`; the conclusion is that this map followed by the
comparison `H^n(X, g^{-1}F) ≅ H^n(X, F)` is the identity of `H^n(X, F)`, in every degree and
for every sheaf.

The absolute Frobenius of a scheme of characteristic `p` does satisfy the hypothesis: the
relative Frobenius of an étale `X`-scheme `U` is the canonical arrow from `U` to its base
change `U ×_{X, F_X} X`, it is natural in `U`, and it is an isomorphism because `U` is étale
over `X`. This is the baffling theorem.

## Main definitions

* `Stacks.EtaleCohomology.etaleSheafPullbackComparison` — the comparison between sheaf
  pullback along small étale base change and the identity functor on abelian sheaves.
* `Stacks.EtaleCohomology.etaleSheafPullbackUnit` — the map `F ⟶ g^{-1}F` induced by `g` on
  abelian sheaves.
* `Stacks.EtaleCohomology.etaleCohomologyPullbackMap` — the map `g` induces on cohomology,
  `H^n(X, F) ⟶ H^n(X, g^{-1}F)`.
* `Stacks.EtaleCohomology.absoluteFrobeniusEtaleSiteIso` — the identification of base change
  along the absolute Frobenius with the identity functor of the small étale site.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyPullbackMap_comp_comparison` — the map induced by the
  unit `F ⟶ g^{-1}F` on cohomology, followed by the comparison, is the identity, in every degree
  and for every sheaf. The statement of [Stacks, Tag 03SP] itself, with the canonical pullback
  map `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`, is
  `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comparison_eq_self`.
* `Stacks.EtaleCohomology.etaleCohomologyFunctorIsoOfBaseChangeIso` — the induced
  identification of the cohomology of the pullback with the cohomology of the sheaf, naturally
  in the sheaf.
* `Stacks.EtaleCohomology.absoluteFrobeniusCohomologyFunctorIso` — the same identification
  for the absolute Frobenius of a scheme of characteristic `p`.
* `Stacks.EtaleCohomology.absoluteFrobeniusConstantCohomologyAddEquiv` — its specialization
  to constant `ℤ/nℤ` coefficients.

## Implementation notes

The comparison on sheaves is obtained as the left-adjoint mate of the isomorphism of direct
images, so it is the canonical map and not merely an unspecified isomorphism; it is
`Stacks.EtaleCohomology.etaleSheafInverseImageComparison` with abelian coefficients. The
coefficient universe is kept independent of the universe of `X`, and the universe in which
`Ext`-groups are computed is independent of both.

The direct image along base change by `g` is identified with the identity functor, hence
exact, so the map induced on cohomology by the unit `F ⟶ g^{-1}F` is the usual pullback of
cohomology classes along `g`: the edge map of the Leray spectral sequence of the direct image,
read through that identification.

The component of the Frobenius site isomorphism at `U` is the relative Frobenius of `U`,
pinned down by its two projections in
`Stacks.EtaleCohomology.absoluteFrobeniusEtaleSiteIsoApp_hom_left_fst` and
`Stacks.EtaleCohomology.absoluteFrobeniusEtaleSiteIsoApp_hom_left_snd`; naturality in `U` is
naturality of the relative Frobenius.

## References

* [Stacks Project, Tag 03SN](https://stacks.math.columbia.edu/tag/03SN)
* [Stacks Project, Tag 03SP](https://stacks.math.columbia.edu/tag/03SP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u v w

namespace Stacks.EtaleCohomology

/-- The canonical comparison between pullback of abelian étale sheaves along base change by
`g : X ⟶ X` and the identity functor, available whenever base change by `g` is isomorphic
to the identity functor of the small étale site. It is the left-adjoint mate of the
isomorphism of direct-image functors induced by that isomorphism of sites.

See [Stacks Project, Tag 03SP](https://stacks.math.columbia.edu/tag/03SP). -/
public def etaleSheafPullbackComparison (X : Scheme.{u}) (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F] :
    Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange g)
        AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology X) (smallEtaleTopology X) ≅
      𝟭 (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}) :=
  etaleSheafInverseImageComparison X g e AddCommGrpCat.{max (u + 1) v}

/-- The adjunction between pullback and direct image of abelian étale sheaves along base change
by `g : X ⟶ X`. -/
public def etaleSheafPullbackAdjunction (X : Scheme.{u}) (g : X ⟶ X)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F] :
    Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange g)
        AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology X) (smallEtaleTopology X) ⊣
      (smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (smallEtaleTopology X) (smallEtaleTopology X) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
    AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology X) (smallEtaleTopology X)

/-- The comparison `g^{-1}F ≅ F` is the mate of the identification of the direct image with the
identity functor. -/
public theorem etaleSheafPullbackComparison_eq (X : Scheme.{u}) (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F] :
    etaleSheafPullbackComparison.{u, v} X g e =
      Adjunction.leftAdjointIdIso (etaleSheafPullbackAdjunction.{u, v} X g)
        (etaleSheafPushforwardComparison X g e AddCommGrpCat.{max (u + 1) v}).symm :=
  Adjunction.leftAdjointUniq_id_ofNatIsoRight _ _

/-- If base change by `g : X ⟶ X` is isomorphic to the identity functor of the small étale
site of `X`, then taking the pullback of an abelian sheaf along it and then cohomology in
degree `n` is identified with taking cohomology in degree `n`, naturally in the sheaf.

See [Stacks Project, Tag 03SP](https://stacks.math.columbia.edu/tag/03SP). -/
public def etaleCohomologyFunctorIsoOfBaseChangeIso (X : Scheme.{u}) (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})] (n : ℕ) :
    Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange g)
          AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology X) (smallEtaleTopology X) ⋙
        Sheaf.functorH (smallEtaleTopology X) n ≅
      Sheaf.functorH (smallEtaleTopology X) n :=
  Functor.isoWhiskerRight (etaleSheafPullbackComparison X g e) _ ≪≫ Functor.leftUnitor _

/-- The map `F ⟶ g^{-1}F` which `g : X ⟶ X` induces on an abelian étale sheaf when base change
by `g` is isomorphic to the identity functor of the small étale site: the unit of the
pullback–direct image adjunction, read through the identification of the direct image with the
identity functor.

See [Stacks Project, Tag 03SP](https://stacks.math.columbia.edu/tag/03SP). -/
public def etaleSheafPullbackUnit (X : Scheme.{u}) (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F] :
    𝟭 (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}) ⟶
      Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange g)
        AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology X) (smallEtaleTopology X) :=
  Adjunction.unitToLeftAdjoint (etaleSheafPullbackAdjunction.{u, v} X g)
    (etaleSheafPushforwardComparison X g e AddCommGrpCat.{max (u + 1) v}).symm

/-- The map `F ⟶ g^{-1}F` induced by `g` is inverse to the canonical comparison `g^{-1}F ≅ F`:
the composite `F ⟶ g^{-1}F ⟶ F` is the identity. -/
@[reassoc (attr := simp)]
public theorem etaleSheafPullbackUnit_app_comp_comparison (X : Scheme.{u}) (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}) :
    (etaleSheafPullbackUnit.{u, v} X g e).app F ≫
        (etaleSheafPullbackComparison.{u, v} X g e).hom.app F = 𝟙 F := by
  rw [etaleSheafPullbackComparison_eq]
  exact Adjunction.unitToLeftAdjoint_comp_leftAdjointIdIso_hom_app _ _ F

/-- The map `g : X ⟶ X` induces on étale cohomology, `H^n(X, F) ⟶ H^n(X, g^{-1}F)`: the map
induced by the unit `F ⟶ g^{-1}F`. The direct image along base change by `g` is identified with
the identity functor, hence exact, so this is the pullback of cohomology classes along `g`.

See [Stacks Project, Tag 03SP](https://stacks.math.columbia.edu/tag/03SP). -/
public def etaleCohomologyPullbackMap (X : Scheme.{u}) (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}) (n : ℕ) :
    Sheaf.H.{w} F n →+
      Sheaf.H.{w} ((Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange g)
        AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology X) (smallEtaleTopology X)).obj F) n :=
  Sheaf.H.map ((etaleSheafPullbackUnit.{u, v} X g e).app F) n

/-- The map `H^n(X, F) ⟶ H^n(X, g^{-1}F)` induced by the unit `F ⟶ g^{-1}F` read through the
identification `e` of base change by `g` with the identity functor, followed by the comparison
`H^n(X, g^{-1}F) ≅ H^n(X, F)`, is the identity of `H^n(X, F)`. Both maps are built from `e`, and
the comparison is the mate of the identification the unit is read through, so this is formal.

The content of [Stacks, Tag 03SP] is the same statement for the canonical pullback map
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap g`, which does not depend on `e`: it is
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comparison_eq_self`, and
`Stacks.EtaleCohomology.etaleCohomologyPullbackMap_eq_etaleCohomologyRestrictionMap` identifies
the map here with the canonical one. -/
public theorem etaleCohomologyPullbackMap_comp_comparison (X : Scheme.{u}) (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}) (n : ℕ) :
    (Sheaf.H.map ((etaleSheafPullbackComparison.{u, v} X g e).hom.app F) n).comp
        (etaleCohomologyPullbackMap.{u, v, w} X g e F n) =
      AddMonoidHom.id (Sheaf.H.{w} F n) := by
  rw [etaleSheafPullbackComparison_eq]
  exact Stacks.Cohomology.cohomologyPullbackMap_comp_leftAdjointIdIso _ _ F n

section AbsoluteFrobenius

open CategoryTheory.Limits

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- The canonical isomorphism between an étale scheme `U` over a scheme `X` of characteristic
`p` and its base change along the absolute Frobenius of `X`. Its underlying morphism of schemes
is the relative Frobenius of `U`, the arrow `U ⟶ U ×_{X, F_X} X` determined by the absolute
Frobenius of `U` and the structure morphism of `U`; it is an isomorphism because `U` is étale
over `X`.

See [Stacks Project, Tag 03SN](https://stacks.math.columbia.edu/tag/03SN). -/
@[sga "3 VIIA 4.1.1.1" "more general",
  sga "4½ Fonctions_L 3.4",
  sga "4½ Rapport 1.2" "special case"]
public def absoluteFrobeniusEtaleSiteIsoApp (U : X.Etale) :
    U ≅ (smallEtaleBaseChange (absoluteFrobenius X p hX)).obj U :=
  haveI : AlgebraicGeometry.Etale (CategoryTheory.Over.mk U.hom).hom := U.prop
  MorphismProperty.Over.isoMk
    ((CategoryTheory.Over.forget X).mapIso
      (asIso (relativeFrobenius X p hX (CategoryTheory.Over.mk U.hom))))
    (relativeFrobenius_snd X p hX (CategoryTheory.Over.mk U.hom))

/-- The underlying morphism of schemes of the Frobenius comparison at `U` is the relative
Frobenius of `U` over `X`. -/
@[simp]
public lemma absoluteFrobeniusEtaleSiteIsoApp_hom_left (U : X.Etale) :
    (absoluteFrobeniusEtaleSiteIsoApp X p hX U).hom.left =
      (relativeFrobenius X p hX (CategoryTheory.Over.mk U.hom)).left := rfl

/-- The Frobenius comparison at `U` followed by the first projection is the absolute Frobenius
of `U`: the comparison is the canonical arrow of the Frobenius square, not merely some
isomorphism.

See [Stacks Project, Tag 03SN](https://stacks.math.columbia.edu/tag/03SN). -/
@[reassoc (attr := simp)]
public lemma absoluteFrobeniusEtaleSiteIsoApp_hom_left_fst (U : X.Etale) :
    (absoluteFrobeniusEtaleSiteIsoApp X p hX U).hom.left ≫
        pullback.fst U.hom (absoluteFrobenius X p hX) =
      absoluteFrobenius U.left p (isInCharacteristic_of_hom U.hom p hX) :=
  relativeFrobenius_fst X p hX (CategoryTheory.Over.mk U.hom)

/-- The Frobenius comparison at `U` followed by the second projection is the structure morphism
of `U`. -/
@[reassoc (attr := simp)]
public lemma absoluteFrobeniusEtaleSiteIsoApp_hom_left_snd (U : X.Etale) :
    (absoluteFrobeniusEtaleSiteIsoApp X p hX U).hom.left ≫
        pullback.snd U.hom (absoluteFrobenius X p hX) = U.hom :=
  relativeFrobenius_snd X p hX (CategoryTheory.Over.mk U.hom)

/-- **Stacks Project, Tag 03SN.** For a scheme `X` of characteristic `p`, base change along the
absolute Frobenius of `X` is isomorphic to the identity functor of the small étale site of `X`.
The isomorphism at an étale `X`-scheme `U` is the relative Frobenius of `U`, and naturality in
`U` is naturality of the relative Frobenius.

See [Stacks Project, Tag 03SN](https://stacks.math.columbia.edu/tag/03SN). -/
@[sga "3 VIIA 4.1.1.1" "more general", sga "4½ Fonctions_L 3.4"]
public def absoluteFrobeniusEtaleSiteIso :
    𝟭 X.Etale ≅ smallEtaleBaseChange (absoluteFrobenius X p hX) :=
  NatIso.ofComponents (absoluteFrobeniusEtaleSiteIsoApp X p hX) fun {U V} f ↦ by
    refine MorphismProperty.Over.Hom.ext ?_
    exact (congrArg CommaMorphism.left (relativeFrobenius_naturality X p hX
      (CategoryTheory.Over.homMk f.left (MorphismProperty.Over.w f) :
        CategoryTheory.Over.mk U.hom ⟶ CategoryTheory.Over.mk V.hom))).symm

/-- The component of the Frobenius site isomorphism at `U` followed by the first projection is
the absolute Frobenius of `U`. -/
@[reassoc (attr := simp)]
public lemma absoluteFrobeniusEtaleSiteIso_hom_app_left_fst (U : X.Etale) :
    ((absoluteFrobeniusEtaleSiteIso X p hX).hom.app U).left ≫
        pullback.fst U.hom (absoluteFrobenius X p hX) =
      absoluteFrobenius U.left p (isInCharacteristic_of_hom U.hom p hX) :=
  absoluteFrobeniusEtaleSiteIsoApp_hom_left_fst X p hX U

/-- On a scheme `X` of characteristic `p`, pullback along the absolute Frobenius is identified
with the identity functor on abelian étale sheaves, so composing it with cohomology in degree `j`
gives back cohomology in degree `j`, naturally in the sheaf.

See [Stacks Project, Tag 03SN](https://stacks.math.columbia.edu/tag/03SN). -/
@[stacks 03SN "pullback along the absolute Frobenius is identified with the identity functor"]
public def absoluteFrobeniusCohomologyFunctorIso
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange (absoluteFrobenius X p hX)).op.HasLeftKanExtension F]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})] (j : ℕ) :
    Functor.sheafPullbackConstruction.sheafPullback
          (smallEtaleBaseChange (absoluteFrobenius X p hX)) AddCommGrpCat.{max (u + 1) v}
          (smallEtaleTopology X) (smallEtaleTopology X) ⋙
        Sheaf.functorH (smallEtaleTopology X) j ≅
      Sheaf.functorH (smallEtaleTopology X) j :=
  etaleCohomologyFunctorIsoOfBaseChangeIso.{u, v, w} X (absoluteFrobenius X p hX)
    (absoluteFrobeniusEtaleSiteIso X p hX) j

/-- **The Baffling Theorem** with constant `ℤ/nℤ` coefficients. On a scheme of characteristic
`p` the canonical Frobenius comparison identifies the étale cohomology of the pullback of the
constant sheaf `ℤ/nℤ` along the absolute Frobenius with the étale cohomology of that constant
sheaf itself, in every degree `j`.

See [Stacks Project, Tag 03SN](https://stacks.math.columbia.edu/tag/03SN). -/
public def absoluteFrobeniusConstantCohomologyAddEquiv
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange (absoluteFrobenius X p hX)).op.HasLeftKanExtension F]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})] (n j : ℕ) :
    Sheaf.H.{w}
        ((Functor.sheafPullbackConstruction.sheafPullback
            (smallEtaleBaseChange (absoluteFrobenius X p hX)) AddCommGrpCat.{max (u + 1) v}
            (smallEtaleTopology X) (smallEtaleTopology X)).obj
          ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n))))) j ≃+
      Sheaf.H.{w}
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n)))) j :=
  ((absoluteFrobeniusCohomologyFunctorIso.{u, v, w} X p hX j).app
    ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}).obj
      (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n))))).addCommGroupIsoToAddEquiv

end AbsoluteFrobenius

end Stacks.EtaleCohomology

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images as sheafified cohomology presheaves

For a morphism of ringed spaces `f : X ⟶ Y`, the `n`-th higher direct image of a sheaf of
modules on `X` is the sheaf associated to the presheaf sending an open `V ⊆ Y` to the
cohomology of its inverse image `f⁻¹(V)`.  The restriction maps of that presheaf are the
usual restriction maps in cohomology.  The same description holds for the cohomology
sheaves of the derived pushforward of a bounded below complex.

All declarations below live in the namespace
`Stacks.Cohomology.HigherDirectImagePresheaf` and are named unqualified here.

## Main definitions

* `cohPresheafModule`, specialized to the functor on opens induced by `f`, is the presheaf
  `V ↦ Hⁿ(f⁻¹(V), ℱ)`.  It is taken from Tag 072W and is not redefined here.
* `preimageHypercohomologyPresheaf` is its bounded-below-complex analogue.
* `hypercohomologyRestrict` is restriction on bounded-below hypercohomology.

## Main results

* `preimageCohomologyPresheaf_evaluation_iso` identifies the values of the cohomology
  presheaf.
* `preimageCohomologyPresheaf_map_eq_Hrestrict` identifies its restriction maps with
  `Hrestrict`.
* `higherDirectImage_iso_sheafify_preimageCohomology` identifies higher direct images with
  the sheafification of that presheaf, naturally in the module.
* `preimageHypercohomologyPresheaf_evaluation_iso` and
  `derivedPushforwardPlus_homology_iso_sheafify_preimageHypercohomology` give the
  corresponding description for bounded below complexes.
* `preimageHypercohomologyPresheaf_map_eq_hypercohomologyRestrict` identifies the
  restriction maps in that description.
* `derivedPlusToStandardObjOfResolution` compares the two definitions of `Rⁿ F` through a
  given injective resolution, and `derivedPlusToStandardObjOfResolution_eq` shows that the
  comparison does not depend on which resolution is used.

## Implementation notes

The cohomology presheaf is the right derived functor of the presheaf-valued functor
`V ↦ Γ(f⁻¹(V), -)`.  Thus all opens and all restriction maps are assembled before deriving.
The displayed equalities in the source are expressed here by natural isomorphisms; this
records their canonical nature and naturality in the sheaf or in the complex.  The explicit
naturality equation for evaluation identifies the presheaf maps with the restriction maps
`Hrestrict` of Tag 01E2.  Higher direct images use `CategoryTheory.Functor.rightDerivedPlus`,
the convention fixed by Tag 05U4; `derivedPlusToStandard` also identifies this with the
injective-resolution convention `CategoryTheory.Functor.rightDerived` used to define
`Hrestrict`.

The supporting homological algebra occupies the bulk of the file and is stated for arbitrary
abelian categories: `rightDerivedPostcomposeIso` (an exact functor commutes with ordinary
right derived functors), `derivedPlusToStandard` (the two conventions for `Rⁿ F` agree) and
`postcomposeHomologyIso` (an exact functor commutes with the cohomology of a total right
derived functor on bounded below complexes).  Only these three, and the natural-isomorphism
transport lemmas `rightDerivedPlusNatIsoOfIso` and `rightDerivedFunctorPlusNatIsoOfIso`, are
used to assemble the statements of the tag.

`homologyFunctorObjIso` records the identity isomorphism between
`(HomologicalComplex.homologyFunctor _ _ i).obj K` and `K.homology i`.  Without it the
comparisons glued together in `extendedHomologyIso` meet at an object that is presented in
two different ways, so the resulting composite cannot be taken apart again by `simp`.

`derivedPlusToStandard` is built from `derivedPlusToStandardObjOfResolution`, the comparison
computed through a *given* injective resolution, by specializing to the resolution chosen by
`CategoryTheory.injectiveResolution`.  Everything in that chain is in term mode, so a consumer
in another module can state equations about it: `derivedPlusToStandard_app`,
`derivedPlusToStandardObjOfResolution_eq_trans` and `derivedPlusToStandardObj_eq_trans` expose
the three factors.  `derivedPlusToStandardObjOfResolution_eq` is the resolution-independence:
the comparison through `I` and the comparison through `J` are the *same* isomorphism for any
two injective resolutions of the same object, so a consumer quantifying over an arbitrary
resolution may rewrite with `derivedPlusToStandardObj_eq` and
`derivedPlusToStandard_app_eq`.

## References

* [The Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [The Stacks Project, Tag 01E2](https://stacks.math.columbia.edu/tag/01E2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

add_to_stacks 01E2 Hrestrict

namespace Stacks.Cohomology.HigherDirectImagePresheaf

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

variable {X Y : RingedSpace.{u, u}}

attribute [local instance] RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint

/-- The presheaf-valued sections functor of Tag 072W attached to `f` is additive: it is the
pushforward followed by the forgetful functor to presheaves of modules. -/
public instance cohFunctor_additive (f : X ⟶ Y) :
    (cohFunctor.{u, u, u, u, u, u} (opensMap f) (structureSheafRing X) (structureSheafRing Y)
      (structureSheafHom f)).Additive := by
  change (modulePushforward f ⋙ SheafOfModules.forget (structureSheafRing Y)).Additive
  infer_instance

-- Keep proof-only constructions from sharing generated proof constants with the statement.
/-- An exact functor commutes with the ordinary right derived functors. -/
@[no_expose] noncomputable def rightDerivedPostcomposeIso
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E] [HasInjectiveResolutions A]
    {F : A ⥤ B} [F.Additive] (G : B ⥤ E) [G.Additive] [G.PreservesHomology]
    (n : ℕ) : F.rightDerived n ⋙ G ≅ (F ⋙ G).rightDerived n := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
      HomotopyCategory.homologyFunctor
    exact (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((injectiveResolutions A).obj X).as).sc n).mapHomologyIso G |>.symm
  · intro X Y f
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℕ)).map_surjective
      ((injectiveResolutions A).map f)
    unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
    simp only [Functor.comp_map]
    rw [← hg]
    unfold HomotopyCategory.homologyFunctor
    dsimp [Functor.comp_map, Functor.mapHomotopyCategory,
      HomologicalComplex.homologyFunctor]
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℕ) n).map
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)) G

/-- `rightDerivedPostcomposeIso` is natural in the postcomposed functor. -/
private theorem rightDerivedPostcomposeIso_naturality
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E] [HasInjectiveResolutions A]
    {F : A ⥤ B} [F.Additive] {G H : B ⥤ E}
    [G.Additive] [H.Additive] [G.PreservesHomology] [H.PreservesHomology]
    (α : G ⟶ H) (n : ℕ) :
    Functor.whiskerLeft (F.rightDerived n) α ≫
        (rightDerivedPostcomposeIso (F := F) H n).hom =
        (rightDerivedPostcomposeIso (F := F) G n).hom ≫
        NatTrans.rightDerived (Functor.whiskerLeft F α) n := by
  ext M
  unfold rightDerivedPostcomposeIso
  dsimp [NatTrans.rightDerived, NatTrans.rightDerivedToHomotopyCategory]
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((injectiveResolutions A).obj M).as
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
  simp only [Functor.comp_obj]
  unfold HomotopyCategory.homologyFunctor
  change α.app (K.sc n).homology ≫ ((K.sc n).mapHomologyIso H).inv =
    ((K.sc n).mapHomologyIso G).inv ≫
      ShortComplex.homologyMap ((K.sc n).mapNatTrans α)
  simp only [NatTrans.app_homology, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The degreewise image of a natural isomorphism of additive functors, read in the ambient
homotopy category**: the isomorphism of functors `K⁺(𝒜) ⥤ K(ℬ)` between the two composites of
`mapHomotopyCategoryPlus` with the inclusion. This is `mapHomotopyCategoryPlusIsoOfIso` below
before that inclusion is cancelled off.

It is written as a single `CategoryTheory.NatIso.ofComponents` rather than glued from
`CategoryTheory.ObjectProperty.liftCompιIso` on either side of the comparison on the unbounded
homotopy category. Those two factors are `Iso.refl` at an object with two definitionally equal
but syntactically different spellings — `F.mapHomotopyCategoryPlus ⋙ Plus.ι ℬ` against
`Plus.ι 𝒜 ⋙ F.mapHomotopyCategory` — so a composite through them cannot be taken apart again:
`CategoryTheory.Iso.trans_hom` would produce a composite whose two ends are spelled
differently, which is not type-correct under the `implicit` transparency level, and `simp`
declines to apply it. Written this way the components are available by `rfl`, which is what
`ι_map_mapHomotopyCategoryPlusIsoOfIso_hom_app` needs. -/
noncomputable def mapHomotopyCategoryPlusCompιIsoOfIso
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
      G.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B := by
  refine NatIso.ofComponents (fun K =>
    (HomotopyCategory.quotient B (ComplexShape.up ℤ)).mapIso
      ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app K.obj.as)) ?_
  intro K L φ
  simp only [Functor.mapIso_hom]
  exact (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).naturality
    ((HomotopyCategory.Plus.ι A).map φ)

/-- The components of `mapHomotopyCategoryPlusCompιIsoOfIso` are those of
`CategoryTheory.NatTrans.mapHomotopyCategory`, that is, the degreewise image of `e`. -/
theorem mapHomotopyCategoryPlusCompιIsoOfIso_hom_app
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusCompιIsoOfIso e).hom.app K =
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K.obj := rfl

/-- A natural isomorphism induces one on bounded below homotopy categories. -/
@[no_expose] noncomputable def mapHomotopyCategoryPlusIsoOfIso
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategoryPlus ≅ G.mapHomotopyCategoryPlus :=
  Functor.fullyFaithfulCancelRight (HomotopyCategory.Plus.ι B)
    (mapHomotopyCategoryPlusCompιIsoOfIso e)

/-- **The characterizing formula for `mapHomotopyCategoryPlusIsoOfIso`.** Read in the ambient
homotopy category, its components are the degreewise image of `e`.

The definition is `no_expose` and is built with
`CategoryTheory.Functor.fullyFaithfulCancelRight`, so outside this file its components cannot
be computed without this. It is the handle a consumer needs in order to recognise the transport
`rightDerivedFunctorPlusNatIsoOfIso` below as an identity: the underived input of the Leray
comparison `Stacks.Cohomology.RelativeLeray.derivedPushforwardPlusCompIso` of
[Stacks, Tag 01F5], namely
`Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso`, has identity components, and so
therefore does the transport it induces. -/
theorem ι_map_mapHomotopyCategoryPlusIsoOfIso_hom_app
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (K : HomotopyCategory.Plus A) :
    (HomotopyCategory.Plus.ι B).map ((mapHomotopyCategoryPlusIsoOfIso e).hom.app K) =
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K.obj := by
  dsimp only [mapHomotopyCategoryPlusIsoOfIso]
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  exact mapHomotopyCategoryPlusCompιIsoOfIso_hom_app e K

/-- A natural isomorphism induces one between total right derived functors. -/
@[no_expose] noncomputable def rightDerivedFunctorPlusNatIsoOfIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus :=
  Functor.rightDerivedNatIso F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
    (Functor.isoWhiskerRight (mapHomotopyCategoryPlusIsoOfIso e)
      DerivedCategory.Plus.Qh)

/-- **The characterizing factorization of `rightDerivedFunctorPlusNatIsoOfIso`.** On a bounded
below complex `K`, the derived-functor unit of `RF` followed by the transport is the degreewise
comparison followed by the derived-functor unit of `RG`.

Since `RF` is a right derived functor with that unit, this determines the transport, and it is
the only handle on it: the definition is `no_expose`, so nothing outside this file can unfold it.
A consumer that has to *compute* with a comparison assembled from
`rightDerivedFunctorPlusNatIsoOfIso` — the Leray isomorphism
`Stacks.Cohomology.RelativeLeray.derivedPushforwardPlusCompIso` of [Stacks, Tag 01F5] is one —
needs this for that factor, together with
`CategoryTheory.Functor.rightDerivedFunctorPlusComp_fac_app` for the other. -/
theorem rightDerivedFunctorPlusNatIsoOfIso_fac_app
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (K : HomotopyCategory.Plus A) :
    F.rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusNatIsoOfIso e).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIsoOfIso e).hom.app K) ≫
        G.rightDerivedFunctorPlusUnith.app K :=
  Functor.rightDerivedNatTrans_app F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
    (Functor.isoWhiskerRight (mapHomotopyCategoryPlusIsoOfIso e)
      DerivedCategory.Plus.Qh).hom K

/-- **A transport along an isomorphism with identity degreewise image is the identity.** If the
degreewise image of `e : F ≅ F` has identity components then so does
`rightDerivedFunctorPlusNatIsoOfIso e`.

This is what makes the comparison of [Stacks, Tag 01F5] computable. The Leray isomorphism
`Stacks.Cohomology.RelativeLeray.derivedPushforwardPlusCompIso` is the canonical comparison
`CategoryTheory.Functor.rightDerivedFunctorPlusComp` of [Stacks, Tag 05T2] precomposed with
`rightDerivedFunctorPlusNatIsoOfIso` along
`Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso f g`, whose two functors are *equal*
(`Stacks.PullbackPseudofunctor.modulePushforward_comp` holds by `rfl`), so the hypothesis below
is available there and the Leray isomorphism is the canonical comparison on the nose.

Both sides descend the same transformation along the unit of `RF`, which exhibits `RF` as a left
Kan extension, so `CategoryTheory.Functor.rightDerived_ext` identifies them; the descended
transformations agree by `rightDerivedFunctorPlusNatIsoOfIso_fac_app` together with
`ι_map_mapHomotopyCategoryPlusIsoOfIso_hom_app` and the faithfulness of the inclusion of the
bounded below homotopy category. -/
theorem rightDerivedFunctorPlusNatIsoOfIso_hom_eq_id
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    {F : A ⥤ B} [F.Additive] (e : F ≅ F)
    (he : ∀ K : HomotopyCategory.Plus A,
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K.obj = 𝟙 _) :
    (rightDerivedFunctorPlusNatIsoOfIso e).hom = 𝟙 F.rightDerivedFunctorPlus := by
  have hid : ∀ K : HomotopyCategory.Plus A,
      (mapHomotopyCategoryPlusIsoOfIso e).hom.app K = 𝟙 _ := fun K =>
    (HomotopyCategory.Plus.ι B).map_injective <| by
      rw [ι_map_mapHomotopyCategoryPlusIsoOfIso_hom_app]
      exact (he K).trans
        ((HomotopyCategory.Plus.ι B).map_id (F.mapHomotopyCategoryPlus.obj K)).symm
  refine Functor.rightDerived_ext F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A) _ _ _ (NatTrans.ext (funext fun K => ?_))
  have h := rightDerivedFunctorPlusNatIsoOfIso_fac_app e K
  rw [hid K, DerivedCategory.Plus.Qh.map_id, Category.id_comp] at h
  simpa using h

/-- A natural isomorphism induces one between the cohomology functors of derived objects. -/
@[no_expose] noncomputable def rightDerivedPlusNatIsoOfIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (i : ℤ) :
    F.rightDerivedPlus i ≅ G.rightDerivedPlus i := by
  let S := DerivedCategory.Plus.singleFunctor A 0
  exact Functor.isoWhiskerLeft S
    (Functor.isoWhiskerRight (rightDerivedFunctorPlusNatIsoOfIso e)
      (DerivedCategory.Plus.homologyFunctor B i))

/-- The degreewise comparison between applying a functor and extension by zero. -/
noncomputable def derivedMapExtendXIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    {ι : Type*} {c : ComplexShape ι} (F : A ⥤ B) [F.Additive]
    (K : HomologicalComplex A c) :
    ∀ o : Option ι, F.obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) o
  | some _ => Iso.refl _
  | none => (F.map_isZero (HomologicalComplex.extend.isZero_X K rfl)).iso
      (HomologicalComplex.extend.isZero_X _ rfl)

/-- `derivedMapExtendXIso` is compatible with the differentials of the extended complexes. -/
private theorem derivedMapExtendXIso_d
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    {ι : Type*} {c : ComplexShape ι} (F : A ⥤ B) [F.Additive]
    (K : HomologicalComplex A c) (a b : Option ι) :
    (derivedMapExtendXIso F K a).hom ≫
        HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) a b =
      F.map (HomologicalComplex.extend.d K a b) ≫ (derivedMapExtendXIso F K b).hom := by
  cases a <;> cases b
  · exact (F.map_isZero (HomologicalComplex.extend.isZero_X K rfl)).eq_of_src _ _
  · exact (F.map_isZero (HomologicalComplex.extend.isZero_X K rfl)).eq_of_src _ _
  · exact (HomologicalComplex.extend.isZero_X ((F.mapHomologicalComplex c).obj K)
      (i := none) rfl).eq_of_tgt _ _
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Applying an additive functor commutes with extending a complex by zero. -/
noncomputable def derivedMapExtendIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    {ι : Type*} {c : ComplexShape ι}
    (F : A ⥤ B) [F.Additive] (e : c.Embedding (ComplexShape.up ℤ))
    (K : HomologicalComplex A c) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun j => derivedMapExtendXIso F K (e.r j))
    (by intro j k hjk; exact derivedMapExtendXIso_d F K (e.r j) (e.r k))

/-- `derivedMapExtendXIso` is natural in the complex. -/
private theorem derivedMapExtendXIso_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    {ι : Type*} {c : ComplexShape ι} (F : A ⥤ B) [F.Additive]
    {K L : HomologicalComplex A c} (φ : K ⟶ L) (o : Option ι) :
    F.map (HomologicalComplex.extend.mapX φ o) ≫ (derivedMapExtendXIso F L o).hom =
      (derivedMapExtendXIso F K o).hom ≫
        HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) o := by
  cases o with
  | none => exact (F.map_isZero (HomologicalComplex.extend.isZero_X K rfl)).eq_of_src _ _
  | some k =>
    dsimp [derivedMapExtendXIso, HomologicalComplex.extend.mapX, HomologicalComplex.extend.X]
    simp

/-- `derivedMapExtendIso` is natural in the complex. -/
theorem derivedMapExtendIso_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] {K L : CochainComplex A ℕ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) ≫
        (derivedMapExtendIso F ComplexShape.embeddingUpNat L).hom =
      (derivedMapExtendIso F ComplexShape.embeddingUpNat K).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ)
          ComplexShape.embeddingUpNat := by
  ext j
  exact derivedMapExtendXIso_naturality F φ (ComplexShape.embeddingUpNat.r j)

/-- The value of `HomologicalComplex.homologyFunctor` at a complex is that complex's
homology.  Recording this as an explicit isomorphism keeps the two presentations of the
object syntactically distinct, so that the comparisons below can be composed and taken
apart again without relying on definitional unfolding of `homologyFunctor`. -/
noncomputable def homologyFunctorObjIso
    {B : Type*} [Category* B] [Abelian B] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex B c) (i : ι) :
    (HomologicalComplex.homologyFunctor B c i).obj K ≅ K.homology i :=
  Iso.refl _

/-- `homologyFunctorObjIso` intertwines the action of `homologyFunctor` on morphisms with
`HomologicalComplex.homologyMap`. -/
theorem homologyFunctorObjIso_hom_naturality
    {B : Type*} [Category* B] [Abelian B] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex B c} (f : K ⟶ L) (i : ι) :
    (HomologicalComplex.homologyFunctor B c i).map f ≫ (homologyFunctorObjIso L i).hom =
      (homologyFunctorObjIso K i).hom ≫ HomologicalComplex.homologyMap f i := by
  change HomologicalComplex.homologyMap f i ≫ 𝟙 (L.homology i) =
    𝟙 (K.homology i) ≫ HomologicalComplex.homologyMap f i
  simp

/-- In a fixed degree, the homology of the image of an extended complex agrees with the
homology of the extension of the image.  This is the part of `extendedHomologyIso` that
lives entirely inside `HomologicalComplex`. -/
noncomputable def extendedHomologyTailIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℕ) (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj K).homology n :=
  HomologicalComplex.homologyMapIso
      (derivedMapExtendIso F ComplexShape.embeddingUpNat K) (n : ℤ) ≪≫
    (((F.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp))

/-- `extendedHomologyTailIso` is natural in the complex. -/
private theorem extendedHomologyTailIso_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] {K L : CochainComplex A ℕ} (φ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        (extendedHomologyTailIso F L n).hom =
      (extendedHomologyTailIso F K n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g (n : ℤ))
    (derivedMapExtendIso_naturality F φ)
  simp only [HomologicalComplex.homologyMap_comp] at h
  simp only [extendedHomologyTailIso, Iso.trans_hom,
    HomologicalComplex.homologyMapIso_hom]
  rw [reassoc_of% h, HomologicalComplex.extendHomologyIso_hom_naturality,
    ← Category.assoc]

/-- Cohomology of the image of an extended complex agrees with its original cohomology. -/
noncomputable def extendedHomologyIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat)))) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj K).homology n :=
  (DerivedCategory.homologyFunctor B (n : ℤ)).mapIso
      ((DerivedCategory.quotientCompQhIso B).app ((F.mapHomologicalComplex _).obj
        (K.extend ComplexShape.embeddingUpNat))) ≪≫
    ((DerivedCategory.homologyFunctorFactors B (n : ℤ)).app
      ((F.mapHomologicalComplex _).obj (K.extend ComplexShape.embeddingUpNat))) ≪≫
    homologyFunctorObjIso
      ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat))
      (n : ℤ) ≪≫
    extendedHomologyTailIso F K n

/-- `extendedHomologyIso` is natural in the complex. -/
theorem extendedHomologyIso_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex A ℕ} (φ : K ⟶ L) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map
          ((F.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)))) ≫
        (extendedHomologyIso F L n).hom =
      (extendedHomologyIso F K n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n := by
  let ψ := (F.mapHomologicalComplex (.up ℤ)).map
    (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  have h₁ := congrArg ((DerivedCategory.homologyFunctor B (n : ℤ)).map)
    ((DerivedCategory.quotientCompQhIso B).hom.naturality ψ)
  have h₂ := (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.naturality ψ
  dsimp only [Functor.comp_map] at h₁ h₂
  simp only [Functor.map_comp] at h₁
  simp only [extendedHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [← Category.assoc]
  rw [h₁]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% homologyFunctorObjIso_hom_naturality]
  simp only [ψ]
  rw [extendedHomologyTailIso_naturality]

-- Exposed, unlike the other auxiliary constructions here: the value of `resolutionSinglePlusHom`
-- is a morphism of bounded below complexes whose source is `singleCochainPlusFunctor.obj M`, and
-- while elaborating an exposed declaration a `@[no_expose]` definition is opaque, so the
-- underlying complex of that object would not reduce.
/-- The complex concentrated in degree zero, regarded as a bounded below complex. -/
noncomputable def singleCochainPlusFunctor
    {A : Type*} [Category A] [Abelian A] : A ⥤ CochainComplex.Plus A where
  obj M := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  map f := ⟨(CochainComplex.singleFunctor A 0).map f⟩
  map_id M := by ext; simp
  map_comp f g := by ext; simp

/-- The two constructions of a single complex in the bounded below homotopy category agree. -/
noncomputable def singlePlusToCochainQuotientIso
    {A : Type*} [Category A] [Abelian A] :
    HomotopyCategory.Plus.singleFunctor A 0 ≅
      singleCochainPlusFunctor (A := A) ⋙ HomotopyCategory.Plus.quotient A := by
  apply Functor.fullyFaithfulCancelRight (HomotopyCategory.Plus.ι A)
  calc
    _ ≅ HomotopyCategory.singleFunctor A 0 :=
      HomotopyCategory.Plus.singleFunctorCompιIso A 0
    _ ≅ CochainComplex.singleFunctor A 0 ⋙
        HomotopyCategory.quotient A (ComplexShape.up ℤ) :=
      HomotopyCategory.singleFunctorPostcompQuotientIso A 0
    _ ≅ singleCochainPlusFunctor (A := A) ⋙
        HomotopyCategory.Plus.quotient A ⋙ HomotopyCategory.Plus.ι A :=
      Functor.isoWhiskerLeft (singleCochainPlusFunctor (A := A))
        (HomotopyCategory.Plus.quotientCompιIso A).symm

/-- An injective resolution of `M`, extended by zero into a bounded below cochain complex. -/
noncomputable def resolutionCochainPlus
    {A : Type*} [Category* A] [Abelian A] {M : A} (I : InjectiveResolution M) :
    CochainComplex.Plus A :=
  ⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩

/-- Every term of `resolutionCochainPlus I` is injective.  Instance search cannot see this
through `resolutionCochainPlus`, so it is recorded here; together with Mathlib's instances it
is what makes the unit of the total right derived functor invertible at the image of
`resolutionCochainPlus I` in the bounded below homotopy category. -/
instance resolutionCochainPlus_injective
    {A : Type*} [Category* A] [Abelian A] {M : A} (I : InjectiveResolution M) (j : ℤ) :
    Injective ((resolutionCochainPlus I).obj.X j) := by
  dsimp only [resolutionCochainPlus]
  infer_instance

/-- The quasi-isomorphism comparing `M`, placed in degree zero, with the extension of an
injective resolution of `M`. -/
noncomputable def resolutionSingleHom
    {A : Type*} [Category* A] [Abelian A] {M : A} (I : InjectiveResolution M) :
    (CochainComplex.singleFunctor A 0).obj M ⟶
      I.cocomplex.extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 (by simp)).inv ≫
    HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat

/-- `resolutionSingleHom` is a quasi-isomorphism: it is the extension of the augmentation of
an injective resolution. -/
instance resolutionSingleHom_quasiIso
    {A : Type*} [Category* A] [Abelian A] {M : A} (I : InjectiveResolution M) :
    QuasiIso (resolutionSingleHom I) := by
  dsimp only [resolutionSingleHom]
  infer_instance

/-- `resolutionSingleHom`, read as a morphism of bounded below cochain complexes. -/
noncomputable def resolutionSinglePlusHom
    {A : Type*} [Category* A] [Abelian A] {M : A} (I : InjectiveResolution M) :
    (singleCochainPlusFunctor (A := A)).obj M ⟶ resolutionCochainPlus I :=
  ⟨resolutionSingleHom I⟩

/-- The localization functor `Qh` inverts `resolutionSinglePlusHom`, which is a
quasi-isomorphism. -/
theorem resolutionSinglePlusHom_qh_isIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] {M : A}
    (I : InjectiveResolution M) :
    IsIso (DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom I))) :=
  Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff (resolutionSingleHom I)).2
      (inferInstanceAs (QuasiIso (resolutionSingleHom I))))

/-- In the bounded below derived category, `M` placed in degree zero is isomorphic to the
extension of any injective resolution `I` of `M`. -/
noncomputable def resolutionDerivedIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] {M : A}
    (I : InjectiveResolution M) :
    (DerivedCategory.Plus.singleFunctor A 0).obj M ≅
      DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I)) :=
  (Functor.singleFunctorPlusIsoCompQh (A := A) 0).app M ≪≫
    Functor.mapIso DerivedCategory.Plus.Qh
      ((singlePlusToCochainQuotientIso (A := A)).app M) ≪≫
    @asIso _ _ _ _ (DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom I)))
      (resolutionSinglePlusHom_qh_isIso I)

/-- The value at `M` of the derived-category right derived functor, compared with the
cohomology of the image under `F` of the extension of an injective resolution of `M`.  This
is the half of `derivedPlusToStandardObj` that happens in the derived category; the other
half is `extendedHomologyIso`. -/
noncomputable def derivedPlusResolutionHomologyIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] {M : A} (I : InjectiveResolution M) (n : ℕ) :
    (F.rightDerivedPlus (n : ℤ)).obj M ≅
      (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj
        ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj
          ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I))) :=
  (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).mapIso
    (F.rightDerivedFunctorPlus.mapIso (resolutionDerivedIso I) ≪≫
      (asIso (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I)))).symm)

/-- The derived-category and injective-resolution definitions of cohomology agree on objects,
the second computed through a *given* injective resolution `I` of `M`.  Independence of the
choice of `I` is `derivedPlusToStandardObjOfResolution_eq`. -/
noncomputable def derivedPlusToStandardObjOfResolution
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] {M : A} (I : InjectiveResolution M) (n : ℕ) :
    (F.rightDerivedPlus (n : ℤ)).obj M ≅ (F.rightDerived n).obj M :=
  derivedPlusResolutionHomologyIso F I n ≪≫
    extendedHomologyIso F I.cocomplex n ≪≫ (I.isoRightDerivedObj F n).symm

/-- The derived-category and injective-resolution definitions of cohomology agree on objects.
This is `derivedPlusToStandardObjOfResolution` at the injective resolution chosen by
`CategoryTheory.injectiveResolution`; by `derivedPlusToStandardObj_eq` it agrees with the
comparison computed through any other resolution. -/
noncomputable def derivedPlusToStandardObj
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    (F.rightDerivedPlus (n : ℤ)).obj M ≅ (F.rightDerived n).obj M :=
  derivedPlusToStandardObjOfResolution F (injectiveResolution M) n

/-- `HomologicalComplex.extendSingleIso` is natural in the object. -/
private theorem extendSingleIso_hom_naturality
    {A : Type*} [Category A] [Abelian A] {M N : A} (f : M ⟶ N) :
    HomologicalComplex.extendMap ((CochainComplex.single₀ A).map f)
        ComplexShape.embeddingUpNat ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N 0 0
        (by simp)).hom =
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0
      (by simp)).hom ≫
      (CochainComplex.singleFunctor A 0).map f := by
  apply HomologicalComplex.to_single_hom_ext
  simp [HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingUpNat.f 0 = 0 by simp),
    HomologicalComplex.extendSingleIso, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single_map_f_self,
    Category.assoc]
  dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    CochainComplex.single₀, HomologicalComplex.single,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  simp

/-- The inverse of `HomologicalComplex.extendSingleIso` is natural in the object. -/
private theorem extendSingleIso_inv_naturality
    {A : Type*} [Category A] [Abelian A] {M N : A} (f : M ⟶ N) :
    (CochainComplex.singleFunctor A 0).map f ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N 0 0 (by simp)).inv =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 (by simp)).inv ≫
        HomologicalComplex.extendMap ((CochainComplex.single₀ A).map f)
          ComplexShape.embeddingUpNat := by
  apply (cancel_mono
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N 0 0 (by simp)).hom).1
  calc
    _ = (CochainComplex.singleFunctor A 0).map f := by simp [Category.assoc]
    _ = (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 (by simp)).inv ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 (by simp)).hom ≫
            (CochainComplex.singleFunctor A 0).map f := by simp
    _ = (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 (by simp)).inv ≫
          (HomologicalComplex.extendMap ((CochainComplex.single₀ A).map f)
            ComplexShape.embeddingUpNat ≫
              (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N 0 0
                (by simp)).hom) := by
          rw [extendSingleIso_hom_naturality]
    _ = _ := by simp [Category.assoc]

-- This proof manipulates `CategoryTheory.InjectiveResolution.isoRightDerivedObj`, whose
-- statements present the same object both as `(HomologicalComplex.homologyFunctor _ _ n).obj K`
-- and as `K.homology n`.  The two agree only after unfolding, so `Category.assoc` does not fire
-- across that junction and the reassociations are built as terms, where elaboration sees the two
-- presentations as equal.
/-- `derivedPlusToStandardObjOfResolution` is natural, whatever injective resolutions are used. -/
private theorem derivedPlusToStandardObjOfResolution_naturality_aux
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (n : ℕ) {M N : A} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    (F.rightDerivedPlus (n : ℤ)).map f ≫ (derivedPlusToStandardObjOfResolution F J n).hom =
      (derivedPlusToStandardObjOfResolution F I n).hom ≫ (F.rightDerived n).map f := by
  let φ := InjectiveResolution.desc f J I
  have comm := InjectiveResolution.desc_commutes f J I
  have hres : resolutionSingleHom I ≫ HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat =
      (CochainComplex.singleFunctor A 0).map f ≫ resolutionSingleHom J := by
    dsimp only [resolutionSingleHom]
    rw [Category.assoc, ← HomologicalComplex.extendMap_comp, comm,
      HomologicalComplex.extendMap_comp, ← Category.assoc, ← Category.assoc,
      extendSingleIso_inv_naturality]
  let φp : resolutionCochainPlus I ⟶ resolutionCochainPlus J :=
    ⟨HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat⟩
  have hsp : resolutionSinglePlusHom I ≫ φp =
      (singleCochainPlusFunctor (A := A)).map f ≫ resolutionSinglePlusHom J := by
    ext j
    exact HomologicalComplex.congr_hom hres j
  let qφ := (HomotopyCategory.Plus.quotient A).map φp
  have hη : (DerivedCategory.Plus.singleFunctor A 0).map f ≫ (resolutionDerivedIso J).hom =
      (resolutionDerivedIso I).hom ≫ DerivedCategory.Plus.Qh.map qφ := by
    have hε := congrArg DerivedCategory.Plus.Qh.map
      ((singlePlusToCochainQuotientIso (A := A)).hom.naturality f)
    have hq := congrArg
      (fun g => DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient A).map g)) hsp
    simp only [Functor.map_comp] at hε hq
    simp only [resolutionDerivedIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, asIso_hom,
      Category.assoc]
    rw [reassoc_of% (Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.naturality f,
      reassoc_of% hε]
    congr 2
    exact hq.symm
  let uI := F.rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I))
  let uJ := F.rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus J))
  have hu : F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map qφ) ≫ inv uJ =
      inv uI ≫ (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map qφ := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact (F.rightDerivedFunctorPlusUnith.naturality qφ).symm
  have hmid := congrArg (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
    (show F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map f) ≫
        (F.rightDerivedFunctorPlus.map (resolutionDerivedIso J).hom ≫ inv uJ) =
      (F.rightDerivedFunctorPlus.map (resolutionDerivedIso I).hom ≫ inv uI) ≫
        (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map qφ by
      rw [← Category.assoc, ← Functor.map_comp, hη, Functor.map_comp, Category.assoc, hu,
        Category.assoc])
  have htail : (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
        ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map qφ) ≫
      (extendedHomologyIso F J.cocomplex n).hom =
    (extendedHomologyIso F I.cocomplex n).hom ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n :=
    extendedHomologyIso_naturality F φ n
  have hObj : ∀ {X : A} (R : InjectiveResolution X),
      (derivedPlusToStandardObjOfResolution F R n).hom ≫ (R.isoRightDerivedObj F n).hom =
        (derivedPlusResolutionHomologyIso F R n).hom ≫ (extendedHomologyIso F R.cocomplex n).hom :=
    fun R => by
      rw [derivedPlusToStandardObjOfResolution, Iso.trans_hom, Category.assoc]
      erw [Iso.trans_hom (extendedHomologyIso F R.cocomplex n), Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      rfl
  rw [← cancel_mono (J.isoRightDerivedObj F n).hom, Category.assoc, Category.assoc,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ
      (by rw [← HomologicalComplex.comp_f, comm, HomologicalComplex.comp_f,
        CochainComplex.single₀_map_f_zero]; rfl) F n, hObj, ← Category.assoc, hObj]
  change (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map f)) ≫
      ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
        (F.rightDerivedFunctorPlus.map (resolutionDerivedIso J).hom ≫ inv uJ) ≫
          (extendedHomologyIso F J.cocomplex n).hom) =
    ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
        (F.rightDerivedFunctorPlus.map (resolutionDerivedIso I).hom ≫ inv uI) ≫
      (extendedHomologyIso F I.cocomplex n).hom) ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _)
      ((Functor.map_comp _ _ _).symm.trans (hmid.trans (Functor.map_comp _ _ _)))).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) htail).trans (Category.assoc _ _ _).symm

/-- `derivedPlusToStandardObj` is natural in the object. -/
private theorem derivedPlusToStandardObj_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (n : ℕ) {M N : A} (f : M ⟶ N) :
    (F.rightDerivedPlus (n : ℤ)).map f ≫ (derivedPlusToStandardObj F N n).hom =
      (derivedPlusToStandardObj F M n).hom ≫ (F.rightDerived n).map f :=
  derivedPlusToStandardObjOfResolution_naturality_aux F n f _ _

/-- The derived-category and injective-resolution definitions of cohomology agree naturally. -/
noncomputable def derivedPlusToStandard
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (n : ℕ) : F.rightDerivedPlus (n : ℤ) ≅ F.rightDerived n :=
  NatIso.ofComponents (fun M => derivedPlusToStandardObj F M n)
    (by intro M N f; exact derivedPlusToStandardObj_naturality F n f)

/-- The components of `derivedPlusToStandard` are `derivedPlusToStandardObj`. -/
theorem derivedPlusToStandard_app
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    (derivedPlusToStandard F n).app M = derivedPlusToStandardObj F M n :=
  rfl

/-- `derivedPlusToStandardObjOfResolution`, written out as the composite of its three factors:
the comparison inside the derived category, the identification of the cohomology of the image
of the extended resolution, and the inverse of
`CategoryTheory.InjectiveResolution.isoRightDerivedObj`. -/
theorem derivedPlusToStandardObjOfResolution_eq_trans
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] {M : A} (I : InjectiveResolution M) (n : ℕ) :
    derivedPlusToStandardObjOfResolution F I n =
      derivedPlusResolutionHomologyIso F I n ≪≫
        extendedHomologyIso F I.cocomplex n ≪≫ (I.isoRightDerivedObj F n).symm :=
  rfl

/-- `derivedPlusToStandardObj`, written out as an explicit composite through the injective
resolution chosen by `CategoryTheory.injectiveResolution`. -/
theorem derivedPlusToStandardObj_eq_trans
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    derivedPlusToStandardObj F M n =
      derivedPlusResolutionHomologyIso F (injectiveResolution M) n ≪≫
        extendedHomologyIso F (injectiveResolution M).cocomplex n ≪≫
          ((injectiveResolution M).isoRightDerivedObj F n).symm :=
  rfl

-- Naturality of the comparison at `𝟙 M` between the two resolutions, which exists for any two
-- injective resolutions of `M`.
/-- **The comparison does not depend on the chosen injective resolution.**  For any two
injective resolutions `I` and `J` of the same object, the two comparisons between the
derived-category and the injective-resolution definitions of `Rⁿ F` agree.

No compatibility between `I` and `J` is assumed: the proof transports along the descent
`CategoryTheory.InjectiveResolution.homotopyEquiv I J` of the identity, which exists for any
two injective resolutions of the same object. -/
theorem derivedPlusToStandardObjOfResolution_eq
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] {M : A} (I J : InjectiveResolution M) (n : ℕ) :
    derivedPlusToStandardObjOfResolution F I n =
      derivedPlusToStandardObjOfResolution F J n := by
  refine Iso.ext ?_
  simpa using (derivedPlusToStandardObjOfResolution_naturality_aux F n (𝟙 M) I J).symm

/-- `derivedPlusToStandardObj` agrees with the comparison computed through *any* injective
resolution of `M`, not only the chosen one. -/
theorem derivedPlusToStandardObj_eq
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] {M : A} (I : InjectiveResolution M) (n : ℕ) :
    derivedPlusToStandardObj F M n = derivedPlusToStandardObjOfResolution F I n :=
  derivedPlusToStandardObjOfResolution_eq F (injectiveResolution M) I n

/-- The component of `derivedPlusToStandard` at `M`, computed through an arbitrary injective
resolution of `M`. -/
theorem derivedPlusToStandard_app_eq
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] {M : A} (I : InjectiveResolution M) (n : ℕ) :
    (derivedPlusToStandard F n).app M = derivedPlusToStandardObjOfResolution F I n :=
  (derivedPlusToStandard_app F M n).trans (derivedPlusToStandardObj_eq F I n)

/-- The comparison stated through arbitrary injective resolutions is natural: no compatibility
between `I` and `J` is needed, since by `derivedPlusToStandardObjOfResolution_eq` neither side
depends on the resolution. -/
theorem derivedPlusToStandardObjOfResolution_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (n : ℕ) {M N : A} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    (F.rightDerivedPlus (n : ℤ)).map f ≫ (derivedPlusToStandardObjOfResolution F J n).hom =
      (derivedPlusToStandardObjOfResolution F I n).hom ≫ (F.rightDerived n).map f := by
  exact derivedPlusToStandardObjOfResolution_naturality_aux F n f I J

/-- The comparison read through arbitrary injective resolutions `I` of `M` and `J` of `N` and
an arbitrary descent `φ` of `f : M ⟶ N` along them: the resulting square commutes, with the
right-hand vertical map computed by `φ` as in
`CategoryTheory.Functor.rightDerived_map_eq`. -/
theorem derivedPlusToStandardObjOfResolution_comp_isoRightDerivedObj_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (n : ℕ) {M N : A} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι ≫ φ = (CochainComplex.single₀ A).map f ≫ J.ι) :
    (F.rightDerivedPlus (n : ℤ)).map f ≫ (derivedPlusToStandardObjOfResolution F J n).hom ≫
        (J.isoRightDerivedObj F n).hom =
      (derivedPlusToStandardObjOfResolution F I n).hom ≫ (I.isoRightDerivedObj F n).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).map φ := by
  rw [← Category.assoc, derivedPlusToStandardObjOfResolution_naturality F n f I J,
    Category.assoc, InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ
      (by rw [← HomologicalComplex.comp_f, comm, HomologicalComplex.comp_f,
        CochainComplex.single₀_map_f_zero]; rfl) F n]

/-- Cohomology after applying an additive functor to a bounded below homotopy complex. -/
@[no_expose] noncomputable def homotopyHomology
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] (i : ℤ) : HomotopyCategory.Plus A ⥤ B :=
  HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (.up ℤ) ⋙
    HomotopyCategory.homologyFunctor B (.up ℤ) i

/-- Cohomology on the homotopy category agrees with cohomology after localization. -/
@[no_expose] noncomputable def homotopyHomologyIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive] (i : ℤ) :
    homotopyHomology F i ≅ F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
      DerivedCategory.Plus.homologyFunctor B i := by
  change (HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (.up ℤ)) ⋙
      HomotopyCategory.homologyFunctor B (.up ℤ) i ≅ _
  exact Functor.isoWhiskerLeft
    (HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (.up ℤ))
    (DerivedCategory.homologyFunctorFactorsh B i).symm

/-- The comparison from cohomology of a complex to cohomology of its derived image. -/
@[no_expose] noncomputable def homologyDerivedUnit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (i : ℤ) :
    homotopyHomology F i ⟶ DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B i :=
  (homotopyHomologyIso F i).hom ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnith
      (DerivedCategory.Plus.homologyFunctor B i)

/-- After postcomposition with an arbitrary functor `G`, the cohomology of the total right
derived functor of `F` is the right derived functor of `homotopyHomology F i ⋙ G`. -/
private theorem homologyDerivedUnit_isDerived
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] (i : ℤ) (G : B ⥤ E) :
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B i ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight (homologyDerivedUnit F i) G)
        (HomotopyCategory.Plus.quasiIso A) := by
  apply (HomotopyCategory.Plus.localizerMorphism_derives
    (homotopyHomology F i ⋙ G)).isRightDerivedFunctor_of_isIso
  intro K
  dsimp [homologyDerivedUnit]
  infer_instance

/-- Exact postcomposition commutes with cohomology on the homotopy category. -/
@[no_expose] noncomputable def homotopyHomologyPostIso
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Abelian A] [Abelian B] [Abelian E]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ E) [G.Additive] [G.PreservesHomology]
    (i : ℤ) : homotopyHomology (F ⋙ G) i ≅ homotopyHomology F i ⋙ G := by
  refine NatIso.ofComponents (fun K => ?_) ?_
  · unfold homotopyHomology HomotopyCategory.homologyFunctor
    exact (((F.mapHomologicalComplex (.up ℤ)).obj K.obj.as).sc i).mapHomologyIso G
  intro K L φ
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective φ.hom
  dsimp [homotopyHomology]
  rw [← hg]
  unfold HomotopyCategory.homologyFunctor
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor B (.up ℤ) i).map
      ((F.mapHomologicalComplex (.up ℤ)).map g)) G

/-- Exact postcomposition commutes with cohomology of total right derived functors. -/
@[no_expose] noncomputable def postcomposeHomologyIso
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ E) [G.Additive] [G.PreservesHomology]
    (i : ℤ) : (F ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor E i ≅
      F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B i ⋙ G := by
  letI : (F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B i ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight (homologyDerivedUnit F i) G)
        (HomotopyCategory.Plus.quasiIso A) := by
    exact homologyDerivedUnit_isDerived F i G
  letI : ((F ⋙ G).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor E i).IsRightDerivedFunctor
      (homologyDerivedUnit (F ⋙ G) i)
        (HomotopyCategory.Plus.quasiIso A) := by
    apply (HomotopyCategory.Plus.localizerMorphism_derives
      (homotopyHomology (F ⋙ G) i)).isRightDerivedFunctor_of_isIso
    intro K
    dsimp [homologyDerivedUnit]
    infer_instance
  exact Functor.rightDerivedNatIso _ _
    (homologyDerivedUnit (F ⋙ G) i)
    (Functor.whiskerRight (homologyDerivedUnit F i) G)
    (HomotopyCategory.Plus.quasiIso A) (homotopyHomologyPostIso F G i)

/-- A natural transformation induces one on bounded below homotopy categories. -/
@[no_expose] noncomputable def mapPlusNatTrans
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus where
  app K := ObjectProperty.homMk ((α.mapHomotopyCategory (.up ℤ)).app K.1)
  naturality K L φ := by
    ext
    exact (α.mapHomotopyCategory (.up ℤ)).naturality φ.hom

/-- The map on derived cohomology induced by a natural transformation. -/
@[no_expose] noncomputable def derivedHomologyMap
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) (i : ℤ) :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B i ⟶
      G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B i :=
  Functor.whiskerRight
    (Functor.rightDerivedNatTrans _ _ F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso A)
      (Functor.whiskerRight (mapPlusNatTrans α) DerivedCategory.Plus.Qh))
    (DerivedCategory.Plus.homologyFunctor B i)

/-- The map on homotopy cohomology induced by a natural transformation. -/
@[no_expose] noncomputable def homotopyHomologyMap
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) (i : ℤ) :
    homotopyHomology F i ⟶ homotopyHomology G i :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι A)
    (Functor.whiskerRight (α.mapHomotopyCategory (.up ℤ))
      (HomotopyCategory.homologyFunctor B (.up ℤ) i))

/-- `homologyDerivedUnit` is natural in the functor being derived. -/
private theorem homologyDerivedUnit_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) (i : ℤ) :
    homologyDerivedUnit F i ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        (derivedHomologyMap α i) =
      homotopyHomologyMap α i ≫ homologyDerivedUnit G i := by
  ext K
  have h := Functor.rightDerivedNatTrans_app _ _ F.rightDerivedFunctorPlusUnith
    G.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A)
    (Functor.whiskerRight (mapPlusNatTrans α) DerivedCategory.Plus.Qh) K
  have h' := congrArg ((DerivedCategory.Plus.homologyFunctor B i).map) h
  have hnat := (DerivedCategory.homologyFunctorFactorsh B i).inv.naturality
    ((α.mapHomotopyCategory (.up ℤ)).app K.obj)
  dsimp [homologyDerivedUnit, derivedHomologyMap, homotopyHomologyIso,
    homotopyHomologyMap]
  simp only [Functor.map_comp] at h'
  rw [Category.assoc, h']
  change (DerivedCategory.homologyFunctorFactorsh B i).inv.app
      ((F.mapHomotopyCategory (.up ℤ)).obj K.obj) ≫
      (DerivedCategory.homologyFunctor B i).map
        (DerivedCategory.Qh.map ((α.mapHomotopyCategory (.up ℤ)).app K.obj)) ≫
      (DerivedCategory.Plus.homologyFunctor B i).map (G.rightDerivedFunctorPlusUnith.app K) =
    (HomotopyCategory.homologyFunctor B (.up ℤ) i).map
      ((α.mapHomotopyCategory (.up ℤ)).app K.obj) ≫
      (DerivedCategory.homologyFunctorFactorsh B i).inv.app
        ((G.mapHomotopyCategory (.up ℤ)).obj K.obj) ≫
      (DerivedCategory.Plus.homologyFunctor B i).map (G.rightDerivedFunctorPlusUnith.app K)
  dsimp only [Functor.comp_map] at hnat
  have hnat' := reassoc_of% hnat
  exact (hnat' _).symm

/-- `homotopyHomologyPostIso` is natural in the postcomposed functor. -/
private theorem homotopyHomologyPostIso_naturality
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Abelian A] [Abelian B] [Abelian E]
    (F : A ⥤ B) [F.Additive] {G H : B ⥤ E} [G.Additive] [H.Additive]
    [G.PreservesHomology] [H.PreservesHomology] (α : G ⟶ H) (i : ℤ) :
    homotopyHomologyMap (Functor.whiskerLeft F α) i ≫
        (homotopyHomologyPostIso F H i).hom =
      (homotopyHomologyPostIso F G i).hom ≫
        Functor.whiskerLeft (homotopyHomology F i) α := by
  ext K
  dsimp [homotopyHomologyPostIso, homotopyHomologyMap]
  unfold homotopyHomology HomotopyCategory.homologyFunctor
  let S := ((F.mapHomologicalComplex (.up ℤ)).obj K.obj.as).sc i
  change ShortComplex.homologyMap (S.mapNatTrans α) ≫ (S.mapHomologyIso H).hom =
    (S.mapHomologyIso G).hom ≫ α.app S.homology
  simp only [NatTrans.app_homology, Iso.hom_inv_id_assoc]

/-- The cohomology of the total right derived functor of `F` is the right derived functor of
`homotopyHomology F i`, with unit `homologyDerivedUnit F i`. -/
private theorem homologyDerivedUnit_isDerived_self
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (i : ℤ) :
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B i).IsRightDerivedFunctor
      (homologyDerivedUnit F i) (HomotopyCategory.Plus.quasiIso A) := by
  exact homologyDerivedUnit_isDerived F i (𝟭 B)

attribute [local instance] homologyDerivedUnit_isDerived_self homologyDerivedUnit_isDerived

/-- `postcomposeHomologyIso` is compatible with the units of the two right derived functors
that it compares. -/
private theorem postcomposeHomologyIso_fac
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ E) [G.Additive] [G.PreservesHomology]
    (i : ℤ) :
    homologyDerivedUnit (F ⋙ G) i ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        (postcomposeHomologyIso F G i).hom =
      (homotopyHomologyPostIso F G i).hom ≫
        Functor.whiskerRight (homologyDerivedUnit F i) G := by
  unfold postcomposeHomologyIso
  rw [Functor.rightDerivedNatIso_hom]
  exact Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

/-- `postcomposeHomologyIso` is natural in the postcomposed functor. -/
private theorem postcomposeHomologyIso_naturality
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] {G H : B ⥤ E} [G.Additive] [H.Additive]
    [G.PreservesHomology] [H.PreservesHomology] (α : G ⟶ H) (i : ℤ) :
    derivedHomologyMap (Functor.whiskerLeft F α) i ≫ (postcomposeHomologyIso F H i).hom =
      (postcomposeHomologyIso F G i).hom ≫
        Functor.whiskerLeft (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B i)
          α := by
  apply Functor.rightDerived_ext _ (homologyDerivedUnit (F ⋙ G) i)
    (HomotopyCategory.Plus.quasiIso A)
  ext K
  have h₁ := congr_app (homologyDerivedUnit_naturality (Functor.whiskerLeft F α) i) K
  have h₂ := congr_app (postcomposeHomologyIso_fac F H i) K
  have h₃ := congr_app (postcomposeHomologyIso_fac F G i) K
  have h₄ := congr_app (homotopyHomologyPostIso_naturality F α i) K
  have h₅ := α.naturality ((homologyDerivedUnit F i).app K)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at *
  rw [reassoc_of% h₁, h₂, ← Category.assoc, h₄]
  simp only [Category.assoc]
  rw [← h₅, ← reassoc_of% h₃]
  rfl

/-- The inverse of `postcomposeHomologyIso` is natural in the postcomposed functor. -/
private theorem postcomposeHomologyIso_inv_naturality
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] {G H : B ⥤ E} [G.Additive] [H.Additive]
    [G.PreservesHomology] [H.PreservesHomology] (α : G ⟶ H) (i : ℤ) :
    Functor.whiskerLeft (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B i) α ≫
        (postcomposeHomologyIso F H i).inv =
      (postcomposeHomologyIso F G i).inv ≫ derivedHomologyMap (Functor.whiskerLeft F α) i := by
  rw [← cancel_epi (postcomposeHomologyIso F G i).hom]
  simp only [← Category.assoc]
  rw [← postcomposeHomologyIso_naturality]
  simp

/-- Exact postcomposition commutes with the derived-category cohomology of objects. -/
@[no_expose] noncomputable def rightDerivedPlusPostcomposeIso
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    (G : B ⥤ E) [G.Additive] [Limits.PreservesFiniteLimits G]
    [Limits.PreservesFiniteColimits G] (i : ℤ) :
    F.rightDerivedPlus i ⋙ G ≅ (F ⋙ G).rightDerivedPlus i := by
  letI : G.PreservesHomology := Functor.preservesHomologyOfExact G
  exact Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
    (postcomposeHomologyIso F G i).symm


/-- The value on `V` of the cohomology presheaf is canonically and naturally isomorphic
to `Hⁿ(f⁻¹(V), -)`. -/
@[stacks 01E4 "values on opens"]
public noncomputable def preimageCohomologyPresheaf_evaluation_iso
    (f : X ⟶ Y) (V : Opens Y.carrier) (n : ℕ) :
    (cohFunctor.{u, u, u, u, u, u} (opensMap f) (structureSheafRing X) (structureSheafRing Y)
        (structureSheafHom f)).rightDerived n ⋙
        PresheafOfModules.toPresheaf (structureSheafRing Y).obj ⋙
        (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op V) ≅
    Hfunctor (structureSheafRing X) ((opensMap f).obj V) n := by
  let F := cohFunctor.{u, u, u, u, u, u}
    (opensMap f) (structureSheafRing X) (structureSheafRing Y) (structureSheafHom f)
  let G := PresheafOfModules.toPresheaf (structureSheafRing Y).obj ⋙
    (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  change F.rightDerived n ⋙ G ≅ (F ⋙ G).rightDerived n
  exact rightDerivedPostcomposeIso (F := F) G n

/-- Under the canonical identifications of its values with cohomology, the map of the
cohomology presheaf along `U ⊆ V` is the restriction map of Tag 01E2. -/
@[stacks 01E4 "restriction mappings"]
public theorem preimageCohomologyPresheaf_map_eq_Hrestrict
    (f : X ⟶ Y) {U V : Opens Y.carrier} (h : U ≤ V) (n : ℕ)
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).obj
          (cohPresheafModule.{u, u, u, u}
            (opensMap f) (structureSheafRing X) (structureSheafRing Y)
            (structureSheafHom f) n F)).map (homOfLE h).op ≫
        (preimageCohomologyPresheaf_evaluation_iso f U n).hom.app F =
    (preimageCohomologyPresheaf_evaluation_iso f V n).hom.app F ≫
        Hrestrict (structureSheafRing X) (leOfHom ((opensMap f).map (homOfLE h))) n F := by
  let P := PresheafOfModules.toPresheaf (structureSheafRing Y).obj
  let F' := cohFunctor.{u, u, u, u, u, u}
    (opensMap f) (structureSheafRing X) (structureSheafRing Y) (structureSheafHom f)
  let G_V := P ⋙ (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat).obj (op V)
  let G_U := P ⋙ (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat).obj (op U)
  let α : G_V ⟶ G_U := Functor.whiskerLeft P
    ((evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat).map (homOfLE h).op)
  have hα := rightDerivedPostcomposeIso_naturality (F := F') α n
  unfold preimageCohomologyPresheaf_evaluation_iso
  change α.app ((F'.rightDerived n).obj F) ≫
      (rightDerivedPostcomposeIso (F := F') G_U n).hom.app F =
    (rightDerivedPostcomposeIso (F := F') G_V n).hom.app F ≫
      (NatTrans.rightDerived (Functor.whiskerLeft F' α) n).app F
  exact congr_app hα F

/-- The `n`-th higher direct image is naturally isomorphic to the sheafification of the
presheaf `V ↦ Hⁿ(f⁻¹(V), -)`. -/
@[stacks 01E4 "associated sheaf"]
public noncomputable def higherDirectImage_iso_sheafify_preimageCohomology
    (f : X ⟶ Y) (n : ℕ) :
    (modulePushforward f).rightDerivedPlus n ≅
      (cohFunctor.{u, u, u, u, u, u} (opensMap f) (structureSheafRing X) (structureSheafRing Y)
          (structureSheafHom f)).rightDerived n ⋙
        PresheafOfModules.sheafification (𝟙 (structureSheafRing Y).obj) := by
  let F := cohFunctor.{u, u, u, u, u, u}
    (opensMap f) (structureSheafRing X) (structureSheafRing Y) (structureSheafHom f)
  let Q := modulePushforward f ⋙ SheafOfModules.forget (structureSheafRing Y)
  let a := PresheafOfModules.sheafification (𝟙 (structureSheafRing Y).obj)
  let ePush := pushforward_iso_pushforwardForget_comp_sheafification
    (opensMap f) (structureSheafRing X) (structureSheafRing Y) (structureSheafHom f)
  haveI : (modulePushforward f).Additive := modulePushforward_additive f
  haveI : (SheafOfModules.pushforward (structureSheafHom f)).Additive := by
    change (modulePushforward f).Additive
    exact modulePushforward_additive f
  haveI : Q.Additive := by dsimp [Q]; infer_instance
  haveI : a.Additive := by
    dsimp [a]
    exact sheafification_additive (structureSheafRing Y)
  haveI : (Q ⋙ a).Additive := Functor.additive_of_iso ePush
  haveI : Limits.PreservesFiniteLimits a := by dsimp [a]; infer_instance
  haveI : Limits.PreservesFiniteColimits a := ⟨fun _ _ _ =>
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafRing Y).obj)).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩
  let e0 := rightDerivedPlusNatIsoOfIso ePush n
  let e1 := rightDerivedPlusPostcomposeIso Q a (n : ℤ)
  let e2 : Q.rightDerived n ≅ F.rightDerived n :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro M N g; rfl)
  exact e0 ≪≫ e1.symm ≪≫
    Functor.isoWhiskerRight (derivedPlusToStandard Q n ≪≫ e2) a

/-- The presheaf `V ↦ Hⁱ(f⁻¹(V), K)` for a bounded below complex `K`, including
its restriction maps. -/
public noncomputable abbrev preimageHypercohomologyPresheaf (f : X ⟶ Y)
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ) :
    PresheafOfModules.{u} (structureSheafRing Y).obj :=
  (DerivedCategory.Plus.homologyFunctor _ i).obj
    ((modulePushforward f ⋙
      SheafOfModules.forget (structureSheafRing Y)).rightDerivedFunctorPlus.obj K)

/-- The value on `V` of the bounded-below hypercohomology presheaf is canonically and
naturally isomorphic to the `i`-th hypercohomology of `K` on `f⁻¹(V)`. -/
@[stacks 01E4 "bounded below values on opens"]
public noncomputable def preimageHypercohomologyPresheaf_evaluation_iso
    (f : X ⟶ Y) (V : Opens Y.carrier) (i : ℤ) :
    (modulePushforward f ⋙ SheafOfModules.forget (structureSheafRing Y)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ i ⋙
        PresheafOfModules.toPresheaf (structureSheafRing Y).obj ⋙
        (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op V) ≅
      (secF (structureSheafRing X) ((opensMap f).obj V)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i := by
  let P := modulePushforward f ⋙ SheafOfModules.forget (structureSheafRing Y)
  let G := PresheafOfModules.toPresheaf (structureSheafRing Y).obj ⋙
    (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  exact (postcomposeHomologyIso P G i).symm

/-- The restriction map on bounded-below hypercohomology induced by restriction of
sections from `V` to `U`.  It is natural in the bounded-below complex. -/
public noncomputable def hypercohomologyRestrict
    (R : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u})
    {U V : Opens X.carrier} (h : U ≤ V) (i : ℤ) :
    (secF R V).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i ⟶
      (secF R U).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i :=
  let a := secRestrict R h
  let aPlus :
      (secF R V).mapHomotopyCategoryPlus ⟶
        (secF R U).mapHomotopyCategoryPlus :=
    { app := fun K ↦
        ObjectProperty.homMk ((a.mapHomotopyCategory (.up ℤ)).app K.1)
      naturality := fun K L φ ↦ by
        ext
        exact (a.mapHomotopyCategory (.up ℤ)).naturality φ.hom }
  Functor.whiskerRight
      ((secF R V).rightDerivedFunctorPlus.rightDerivedNatTrans
        (secF R U).rightDerivedFunctorPlus
        (secF R V).rightDerivedFunctorPlusUnith
        (secF R U).rightDerivedFunctorPlusUnith
        (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} R))
        (Functor.whiskerRight aPlus DerivedCategory.Plus.Qh))
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i)

/-- Under the canonical identifications of its values with hypercohomology, the map of
the bounded-below hypercohomology presheaf along `U ⊆ V` is the restriction map
induced by restriction of sections. -/
@[stacks 01E4 "bounded below restriction mappings"]
public theorem preimageHypercohomologyPresheaf_map_eq_hypercohomologyRestrict
    (f : X ⟶ Y) {U V : Opens Y.carrier} (h : U ≤ V) (i : ℤ)
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).obj
          (preimageHypercohomologyPresheaf f K i)).map (homOfLE h).op ≫
        (preimageHypercohomologyPresheaf_evaluation_iso f U i).hom.app K =
      (preimageHypercohomologyPresheaf_evaluation_iso f V i).hom.app K ≫
        (hypercohomologyRestrict (structureSheafRing X)
          (leOfHom ((opensMap f).map (homOfLE h))) i).app K := by
  let P := modulePushforward f ⋙ SheafOfModules.forget (structureSheafRing Y)
  let T := PresheafOfModules.toPresheaf (structureSheafRing Y).obj
  let GV := T ⋙ (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let GU := T ⋙ (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let α : GV ⟶ GU := Functor.whiskerLeft T
    ((evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat.{u}).map (homOfLE h).op)
  have hα := postcomposeHomologyIso_inv_naturality P α i
  change α.app ((P.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ i).obj K) ≫
      (postcomposeHomologyIso P GU i).inv.app K =
    (postcomposeHomologyIso P GV i).inv.app K ≫
      (derivedHomologyMap (Functor.whiskerLeft P α) i).app K
  exact congr_app hα K


/-- For a bounded below complex, the `i`-th cohomology sheaf of its derived pushforward
is naturally isomorphic to the sheafification of `V ↦ Hⁱ(f⁻¹(V), K)`. -/
@[stacks 01E4 "bounded below associated sheaf", ega "0 12.4.3" "special case"]
public noncomputable def
    derivedPushforwardPlus_homology_iso_sheafify_preimageHypercohomology
    (f : X ⟶ Y) (i : ℤ) :
    (modulePushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ i ≅
      (modulePushforward f ⋙ SheafOfModules.forget (structureSheafRing Y)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ i ⋙
          PresheafOfModules.sheafification (𝟙 (structureSheafRing Y).obj) := by
  let P := modulePushforward f ⋙ SheafOfModules.forget (structureSheafRing Y)
  let a := PresheafOfModules.sheafification (𝟙 (structureSheafRing Y).obj)
  let Hs := DerivedCategory.Plus.homologyFunctor (SheafOfModules (structureSheafRing Y)) i
  let ePush := pushforward_iso_pushforwardForget_comp_sheafification
    (opensMap f) (structureSheafRing X) (structureSheafRing Y) (structureSheafHom f)
  haveI : (modulePushforward f).Additive := modulePushforward_additive f
  haveI : (SheafOfModules.pushforward (structureSheafHom f)).Additive := by
    change (modulePushforward f).Additive
    exact modulePushforward_additive f
  haveI : P.Additive := by dsimp [P]; infer_instance
  haveI : a.Additive := by
    dsimp [a]
    exact sheafification_additive (structureSheafRing Y)
  haveI : (P ⋙ a).Additive := Functor.additive_of_iso ePush
  let eDerived := rightDerivedFunctorPlusNatIsoOfIso ePush
  haveI : Limits.PreservesFiniteLimits a := by dsimp [a]; infer_instance
  haveI : Limits.PreservesFiniteColimits a := ⟨fun _ _ _ =>
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafRing Y).obj)).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩
  let eComp := postcomposeHomologyIso P a i
  exact Functor.isoWhiskerRight eDerived Hs ≪≫ eComp

end Stacks.Cohomology.HigherDirectImagePresheaf

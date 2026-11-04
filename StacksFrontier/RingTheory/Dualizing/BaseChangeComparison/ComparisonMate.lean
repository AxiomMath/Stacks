module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
import all StacksFrontier.Homology.Tor.IndependenceBaseChange

/-!
# The derived base-change comparison of Stacks 065Z is the Beck--Chevalley mate

Let

`R ⟶ A`, `R ⟶ R'`, `A ⟶ A'`, `R' ⟶ A'`

be a commutative square of commutative rings.  [stacks 065Z] produces a comparison
`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'` of derived base changes,
`RingTheory.TorIndependence.derivedBaseChangeComparison`, characterized — by
`RingTheory.TorIndependence.derivedBaseChangeComparison_snd_eq` — as the unique transformation
whose composite with the counit of derived extension of scalars along `A → A'` is the counit along
`R → R'` followed by the underived comparison.

This file records the *unit* side of the same morphism, the side on which the projection-formula
compatibility of [stacks 0E2A] reads it.  Restriction of scalars along the two legs of the
square agrees — both are restriction along the composite — and the resulting isomorphism
`RingTheory.TorIndependence.restrictSquareDerivedIso` of derived restrictions has a
Beck--Chevalley mate along the two extension-of-scalars adjunctions of [stacks 0GMT],
`RingTheory.TorIndependence.derivedBaseChangeMate`.  The main result is that this mate **is** the
comparison of [stacks 065Z], with no hypothesis whatsoever: no Tor independence, no K-flatness, no
condition on the chosen models.

Equivalently, in the form `RingTheory.TorIndependence.unit_comp_derivedBaseChangeComparison`:

`η^{R→R'}_{K|_R} ≫ (065Z)|_R = (η^{A→A'}_K)|_R`,

the unit of [stacks 0GMT] along `R → R'` followed by the restricted comparison is the restricted
unit along `A → A'`.

## Main definitions

* `RingTheory.TorIndependence.restrictSquareIso` — the identification of the two restrictions
  along the square, at the level of modules.  On elements it is the identity.
* `RingTheory.TorIndependence.restrictSquareDerivedIso` — the same identification on derived
  categories, obtained by descending the degreewise one through the localization.
* `RingTheory.TorIndependence.derivedBaseChangeMate` — the Beck--Chevalley mate of
  `restrictSquareDerivedIso` along the two adjunctions of [stacks 0GMT].

## Main results

* `RingTheory.TorIndependence.restrictSquareDerivedIso_hom_app_q_obj` and its primed form — the
  component of `restrictSquareDerivedIso` at the class of a complex, the primed form with the two
  comparison isomorphisms of derived restriction already absorbed.
* `RingTheory.TorIndependence.derivedBaseChangeMate_eq` — **the derived comparison of
  [stacks 065Z] is the Beck--Chevalley mate**, unconditionally.
* `RingTheory.TorIndependence.unit_comp_derivedBaseChangeComparison` — the same statement as an
  equation between units of [stacks 0GMT].

## Implementation notes

`RingTheory.TorIndependence.restrictSquareDerivedIso` is built with
`CategoryTheory.Localization.liftNatIso`, so its components at classes of complexes are computed
by `CategoryTheory.Localization.liftNatTrans_app`; the two `Localization.Lifting` instances it
uses are `Localization.Lifting.compLeft`, whose isomorphism is the identity, which is why no
coherence morphism survives in the component formula.

The additivity of degreewise extension of scalars along a bare ring homomorphism is the `private`
`extendScalarsAdditive` of `StacksFrontier.Homology.Tor.IndependenceBaseChange`, reached by
`import all` so that the statements here use the same instance as `derivedBaseChangeComparison`'s
own signature.  A private instance may not occur in a public signature, which is why the
chain-level identity — whose statement mentions
`CategoryTheory.Adjunction.mapHomologicalComplex` of the degreewise extension/restriction
adjunction, and hence that instance — is `private`.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

namespace RingTheory.TorIndependence

universe uR uA uRp uAp v

attribute [local instance] extendScalarsAdditive

variable {R : Type uR} {A : Type uA} {R' : Type uRp} {A' : Type uAp}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
  (sq : h.comp f = i.comp g)

/-- **The two restrictions along a commutative square of rings agree.** Restricting an
`A'`-module along `A → A'` and then along `R → A` is the same as restricting along `R' → A'` and
then along `R → R'`: both are restriction along the composite, which the square identifies.  On
underlying elements the isomorphism is the identity. -/
def restrictSquareIso :
    ModuleCat.restrictScalars.{max v uR uA uRp uAp} h ⋙
        ModuleCat.restrictScalars.{max v uR uA uRp uAp} f ≅
      ModuleCat.restrictScalars.{max v uR uA uRp uAp} i ⋙
        ModuleCat.restrictScalars.{max v uR uA uRp uAp} g :=
  (ModuleCat.restrictScalarsComp.{max v uR uA uRp uAp} f h).symm ≪≫
    ModuleCat.restrictScalarsComp'.{max v uR uA uRp uAp} g i (h.comp f) sq

/-- `RingTheory.TorIndependence.restrictSquareIso` is the identity on underlying elements. -/
theorem restrictSquareIso_hom_app_apply (M : ModuleCat.{max v uR uA uRp uAp} A') (x : M) :
    (restrictSquareIso.{uR, uA, uRp, uAp, v} f g h i sq).hom.app M x = x :=
  rfl

section Derived

variable [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R)]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A)]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R')]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A')]

/-- **The two derived restrictions along a commutative square of rings agree.** Restriction of
scalars is exact, so `RingTheory.TorIndependence.restrictSquareIso` descends to the derived
categories through the localization. -/
def restrictSquareDerivedIso :
    (ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A') (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙
      ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory))
    (DerivedCategory.Q ⋙
      ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory)) _ _
    (Functor.isoWhiskerRight
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapDerivedCategoryFactors
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft
        ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (restrictSquareIso.{uR, uA, uRp, uAp, v} f g h i sq)
          (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      (Functor.isoWhiskerLeft
        ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategoryFactors).symm ≪≫
      (Functor.isoWhiskerRight
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategoryFactors
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory).symm)

/-- **The component of `RingTheory.TorIndependence.restrictSquareDerivedIso` at the class of a
complex.** It is the degreewise isomorphism, read through the four comparisons of
`CategoryTheory.Functor.mapDerivedCategoryFactors` of the four restriction functors.  No coherence
morphism occurs: the `CategoryTheory.Localization.Lifting` instances used in the construction are
`CategoryTheory.Localization.Lifting.compLeft`, whose isomorphism is the identity. -/
theorem restrictSquareDerivedIso_hom_app_q_obj
    (K : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A') ℤ) :
    (restrictSquareDerivedIso.{uR, uA, uRp, uAp, v} f g h i sq).hom.app
        (DerivedCategory.Q.obj K) =
      (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapDerivedCategoryFactors.hom.app
            K) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (restrictSquareIso.{uR, uA, uRp, uAp, v} f g h i sq).hom
                (ComplexShape.up ℤ)).app K) ≫
            (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategoryFactors.inv.app
                (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory.map
                ((ModuleCat.restrictScalars.{max v uR uA uRp uAp}
                  i).mapDerivedCategoryFactors.inv.app K) := by
  simp only [restrictSquareDerivedIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Functor.comp_obj, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv]
  rfl

/-- **The component of `RingTheory.TorIndependence.restrictSquareDerivedIso`, with the two outer
comparisons absorbed.** Preceded by the inverse comparison of derived restriction along `h` and
followed by the comparison along `i`, the component at the class of a complex is the degreewise
isomorphism read through the two remaining comparisons. -/
theorem restrictSquareDerivedIso_hom_app_q_obj'
    (K : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A') ℤ) :
    (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapDerivedCategoryFactors.inv.app
            K) ≫
        (restrictSquareDerivedIso.{uR, uA, uRp, uAp, v} f g h i sq).hom.app
            (DerivedCategory.Q.obj K) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp}
              i).mapDerivedCategoryFactors.hom.app K) =
      (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (restrictSquareIso.{uR, uA, uRp, uAp, v} f g h i sq).hom
              (ComplexShape.up ℤ)).app K) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) := by
  rw [restrictSquareDerivedIso_hom_app_q_obj]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  simp

section Models

variable
  [(ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).IsLeftAdjoint]
  [(ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).IsLeftAdjoint]
  (L_g : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R'))
  (L_h : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A'))
  (alpha_g : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R) ⋙ L_g ⟶
    (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (alpha_h : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A) ⋙ L_h ⟶
    (ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [L_g.IsLeftDerivedFunctor alpha_g
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} R) (ComplexShape.up ℤ))]
  [L_h.IsLeftDerivedFunctor alpha_h
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))]

/-- **The Beck--Chevalley mate of the square of restrictions.** Transposing
`RingTheory.TorIndependence.restrictSquareDerivedIso` along the extension-of-scalars adjunctions
of [stacks 0GMT] at `A → A'` and at `R → R'` gives a morphism

`(K|_R) ⊗ᴸ_R R' ⟶ (K ⊗ᴸ_A A')|_{R'}`,

natural in the object `K` of `D(A)`.  It is the comparison of [stacks 065Z], by
`RingTheory.TorIndependence.derivedBaseChangeMate_eq`. -/
def derivedBaseChangeMate :
    (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory ⋙ L_g ⟶
      L_h ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory :=
  (mateEquiv
      (derivedExtensionScalarsAdjunction.{uA, uAp, max v uR uRp} h L_h alpha_h)
      (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA uAp} g L_g alpha_g)).symm
    (restrictSquareDerivedIso.{uR, uA, uRp, uAp, v} f g h i sq).hom

/-- **The mate identity for the underived comparison, at a module.** The degreewise unit of
extension of scalars along `A → A'`, restricted along `R → A` and read through
`RingTheory.TorIndependence.restrictSquareIso`, is the degreewise unit along `R → R'` followed by
the underived comparison of [stacks 065Z]. -/
theorem restrictSquare_unit_comp (M : ModuleCat.{max v uR uA uRp uAp} A) :
    (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).map
          ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uA, uAp} h).unit.app M) ≫
        (restrictSquareIso.{uR, uA, uRp, uAp, v} f g h i sq).hom.app
          ((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).obj M) =
      (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uAp, uR, uRp} g).unit.app
          ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).map
          ((derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
            L_g L_h alpha_g alpha_h).1.app M) := by
  ext m
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have key := derivedBaseChangeComparison_fst_app_tmul.{uR, uA, uRp, uAp, v} f g h i sq
    L_g L_h alpha_g alpha_h M 1 m
  rw [map_one] at key
  exact key.symm

/-- `RingTheory.TorIndependence.restrictSquare_unit_comp` degreewise on a complex. -/
private theorem restrictSquare_unit_comp_complex
    (K : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A) ℤ) :
    ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uA, uAp}
            h).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K) ≫
        (NatTrans.mapHomologicalComplex
          (restrictSquareIso.{uR, uA, uRp, uAp, v} f g h i sq).hom (ComplexShape.up ℤ)).app
          (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) =
      ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uAp, uR, uRp} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app
          (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
            (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
              L_g L_h alpha_g alpha_h).1 (ComplexShape.up ℤ)).app K) :=
  HomologicalComplex.hom_ext _ _ (fun n =>
    restrictSquare_unit_comp.{uR, uA, uRp, uAp, v} f g h i sq L_g L_h alpha_g alpha_h (K.X n))

/-- **The derived comparison of [stacks 065Z] is the Beck--Chevalley mate of the square of
derived restrictions.** Unconditionally: no Tor independence, no K-flatness, no condition on the
two chosen models of derived extension of scalars. -/
theorem derivedBaseChangeMate_eq :
    derivedBaseChangeMate.{uR, uA, uRp, uAp, v} f g h i sq L_g L_h alpha_g alpha_h =
      (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
        L_g L_h alpha_g alpha_h).2.1 := by
  refine derivedBaseChangeComparison_snd_eq.{uR, uA, uRp, uAp, v} f g h i sq
    L_g L_h alpha_g alpha_h _ ?_
  intro K _
  refine ((derivedExtensionScalarsAdjunction.{uR, uRp, max v uA uAp} g L_g alpha_g).homEquiv
    _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [derivedBaseChangeMate]
  have hm := (unit_mateEquiv_symm
      (derivedExtensionScalarsAdjunction.{uA, uAp, max v uR uRp} h L_h alpha_h)
      (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA uAp} g L_g alpha_g)
      ((restrictSquareDerivedIso.{uR, uA, uRp, uAp, v} f g h i sq).hom)
      (DerivedCategory.Q.obj K)).symm
  refine Eq.trans (congrArg (fun z => z ≫ _) hm) ?_
  have hn := (restrictSquareDerivedIso.{uR, uA, uRp, uAp, v} f g h i sq).hom.naturality
    (alpha_h.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← hn]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [← CategoryTheory.Functor.map_comp,
    derivedExtensionScalarsAdjunction_unit_app.{uA, uAp, max v uR uRp} h L_h alpha_h K]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [restrictSquareDerivedIso_hom_app_q_obj']
  have hf := (ModuleCat.restrictScalars.{max v uR uA uRp uAp}
      f).mapDerivedCategoryFactors.hom.naturality
    (((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uA, uAp} h).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hf
  slice_lhs 1 2 => rw [hf]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, Functor.comp_obj]
  slice_rhs 2 3 => rw [derivedExtensionScalarsAdjunction_unit_app.{uR, uRp, max v uA uAp}
    g L_g alpha_g (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)]
  simp only [Functor.id_obj, Category.assoc]
  refine congrArg (fun z => _ ≫ z) ?_
  have hgn := (ModuleCat.restrictScalars.{max v uR uA uRp uAp}
      g).mapDerivedCategoryFactors.inv.naturality
    ((NatTrans.mapHomologicalComplex
      (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq L_g L_h alpha_g alpha_h).1
      (ComplexShape.up ℤ)).app K)
  simp only [Functor.comp_map] at hgn
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    restrictSquare_unit_comp_complex.{uR, uA, uRp, uAp, v} f g h i sq L_g L_h alpha_g alpha_h K,
    CategoryTheory.Functor.map_comp, Category.assoc]
  exact congrArg (fun z => DerivedCategory.Q.map
    (((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uAp, uR, uRp} g).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app
      (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) ≫ z) hgn

/-- **The unit form of `RingTheory.TorIndependence.derivedBaseChangeMate_eq`.** At an object `K`
of `D(A)` the unit of [stacks 0GMT] along `R → R'` at `K|_R`, followed by the restriction along
`R → R'` of the comparison of [stacks 065Z], is the restriction along `R → A` of the unit of
[stacks 0GMT] along `A → A'` at `K`, followed by the identification of the two derived
restrictions. -/
theorem unit_comp_derivedBaseChangeComparison
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A)) :
    (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA uAp} g L_g alpha_g).unit.app
          ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory.obj K) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory.map
          ((derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
            L_g L_h alpha_g alpha_h).2.1.app K) =
      (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory.map
          ((derivedExtensionScalarsAdjunction.{uA, uAp, max v uR uRp} h L_h alpha_h).unit.app
            K) ≫
        (restrictSquareDerivedIso.{uR, uA, uRp, uAp, v} f g h i sq).hom.app (L_h.obj K) := by
  rw [← derivedBaseChangeMate_eq.{uR, uA, uRp, uAp, v} f g h i sq L_g L_h alpha_g alpha_h]
  exact (unit_mateEquiv_symm
    (derivedExtensionScalarsAdjunction.{uA, uAp, max v uR uRp} h L_h alpha_h)
    (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA uAp} g L_g alpha_g)
    ((restrictSquareDerivedIso.{uR, uA, uRp, uAp, v} f g h i sq).hom) K).symm

end Models

end Derived

end RingTheory.TorIndependence

end

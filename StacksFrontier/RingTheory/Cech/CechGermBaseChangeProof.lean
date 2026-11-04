module

public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.RingTheory.Cech.CechGermBaseChange
public import StacksFrontier.RingTheory.Cech.CechUnderColimit

/-!
# Stacks 099D, condition (c): the base-change statement at the germ maps

Let `Dat` be a `Stacks.PairSite.PresentedCechDatum`, `(A, I)` a pair with `I` finitely generated
and `X` an object of the index category of step 2 of [Stacks, Tag 099D]. Then the comparison
`𝒦•(X.pair) ⊗^L_{X.pair.ring} A ⟶ K(A, I)` built from the germ map is an isomorphism in `D(A)`
(`Stacks.PairSite.GermBaseChange`). Hence the complex `K(A, I)` of step 2 satisfies condition (c)
of the tag, `K(A, I) ⊗^L_A B ≅ K(B, IB)`, at every ring map `A → B`.

Here `R = X.pair.ring`, `P ⟶ 𝒦•(X.pair)` is a K-flat resolution and `R_Y` is the ring of an
object `Y` under `X`.

## Main definitions

* `Stacks.PairSite.PairOver.underResMap` and `Stacks.PairSite.PairOver.underResElt`: the
  resolution restricted to an object under `X`, and its values.
* `Stacks.PairSite.PairOver.underAdjointHom`: the adjoint `R_Y ⊗_R P ⟶ 𝒦•(Y.right.pair)`, with
  `Stacks.PairSite.PairOver.underAlpha` the natural transformation it defines.
* `Stacks.PairSite.PairOver.germAdjointHom`: the adjoint `A ⊗_R P ⟶ K(A, I)`, read over `R`.

## Main results

* `Stacks.PairSite.PairOver.quasiIso_underAdjointHom`: the comparison at an object under `X` is
  a quasi-isomorphism.
* `Stacks.PairSite.PairOver.underTensorCocone_ι_comp`: the comparison at `(A, I)` is the map
  induced on the colimits by those comparisons.
* `Stacks.PairSite.PairOver.quasiIso_germAdjointHom`: the comparison at `(A, I)` is a
  quasi-isomorphism.
* `Stacks.PairSite.germBaseChange`: `Stacks.PairSite.GermBaseChange` holds for every
  `Stacks.PairSite.PresentedCechDatum`.
* `Stacks.PairSite.colimitBaseChange`: condition (c) of the tag for the colimit complex of
  step 2, at every ring map.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.PairSite

variable {A : Type u} [CommRing A] {I : Ideal A}

namespace PairOver

/-! ### The comparison maps over the objects under a fixed one -/

variable {X : PairOver A I} {K : CochainComplex PairModule.{u} ℤ}
  {P : CochainComplex (ModuleCat.{u} X.pair.ring) ℤ}

/-- The restriction of a resolution of `𝒦•(X.pair)` to an object under `X`. -/
def underResMap (π : P ⟶ sectionsComplex K X.pair) (Y : Under X) :
    P ⟶ ((ModuleCat.restrictScalars (underHom Y)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (sectionsComplex K Y.right.pair) :=
  π ≫ sectionsMap K (Hom.toHom Y.hom)

/-- The value at an object under `X` of the restricted resolution. -/
def underResElt (π : P ⟶ sectionsComplex K X.pair) (Y : Under X) (n : ℤ) (p : P.X n) :
    (sectionsComplex K Y.right.pair).X n := ((underResMap π Y).f n).hom p

/-- Restricting the value of the restricted resolution at `Y` along a morphism `Y ⟶ Z` under `X`
gives its value at `Z`. -/
theorem restriction_underResElt (π : P ⟶ sectionsComplex K X.pair) {Y Z : Under X} (f : Y ⟶ Z)
    (n : ℤ) (p : P.X n) :
    (K.X n).restriction (Hom.toHom f.right) (underResElt π Y n p) = underResElt π Z n p :=
  (PairModule.restriction_comp_apply (K.X n) (Hom.toHom Y.hom) (Hom.toHom f.right)
    ((π.f n).hom p)).symm.trans
    (congrArg (fun h : X.pair ⟶ Z.right.pair ↦ (K.X n).restriction h ((π.f n).hom p))
      (congrArg Hom.toHom (Under.w f)))

/-- **The base-change comparison at an object under `X`**: the map of complexes
`A₀ ⊗_{R} P ⟶ 𝒦•(A₀, I₀)` adjoint to the restriction of the resolution. -/
def underAdjointHom (π : P ⟶ sectionsComplex K X.pair) (Y : Under X) :
    (underTensorComplex X P).obj Y ⟶ (underSectionsComplex K X).obj Y :=
  (tensorComplexBaseIso (underHom Y) P).hom ≫
    (CochainComplex.restrictScalars (underHom Y)).map
      (((Stacks.CechRingBaseChange.complexAdj (underHom Y)).homEquiv P
        (sectionsComplex K Y.right.pair)).symm (underResMap π Y))

/-- The comparison `underAdjointHom π Y` sends `s ⊗ p` to `s • underResElt π Y n p`. -/
theorem underAdjointHom_f_tmulBase (π : P ⟶ sectionsComplex K X.pair) (Y : Under X) (n : ℤ)
    (s : Y.right.pair.ring) (p : P.X n) :
    ((underAdjointHom π Y).f n).hom (tmulBase (underHom Y) (P.X n) s p) =
      s • underResElt π Y n p :=
  (congrArg
    (fun w : (ModuleCat.extendScalars (underHom Y)).obj (P.X n) ⟶
        (sectionsComplex K Y.right.pair).X n ↦
      w.hom (tmulBase (underHom Y) (P.X n) s p))
    (complexAdj_homEquiv_symm_f (underHom Y) (underResMap π Y) n)).trans
    (adjointHom_tmulBase (underHom Y) ((underResMap π Y).f n) s p)

/-- **The base-change comparisons over the objects under `X`, as a natural transformation.** -/
def underAlpha (π : P ⟶ sectionsComplex K X.pair) :
    underTensorComplex X P ⟶ underSectionsComplex K X where
  app Y := underAdjointHom π Y
  naturality {Y Z} f := HomologicalComplex.hom_ext _ _ fun n ↦ by
    refine hom_ext_tmulBase (V := P.X n) (underHom Y) fun s p ↦ ?_
    change ((underAdjointHom π Z).f n).hom
        (tmulBase (underHom Z) (P.X n) ((Hom.toHom f.right).toRingHom s) p) =
      (K.X n).restriction (Hom.toHom f.right)
        (((underAdjointHom π Y).f n).hom (tmulBase (underHom Y) (P.X n) s p))
    rw [underAdjointHom_f_tmulBase, underAdjointHom_f_tmulBase]
    exact (congrArg (fun z : (K.X n).value Z.right.pair ↦ (Hom.toHom f.right).toRingHom s • z)
        (restriction_underResElt π f n p).symm).trans
      (((K.X n).restriction (Hom.toHom f.right)).hom.map_smul s (underResElt π Y n p)).symm

/-! ### The comparisons under `X` are quasi-isomorphisms -/

/-- A morphism equal to an isomorphism is an isomorphism, with the invertibility as an explicit
argument. -/
theorem isIso_of_eq' {C : Type*} [Category C] {V W : C} {a b : V ⟶ W} (h : a = b)
    (ha : IsIso a) : IsIso b := h ▸ ha

/-- Cancel an invertible left factor out of an invertible composite, with the invertibility of
the factor and of the composite as explicit arguments. -/
theorem isIso_of_isIso_comp_left' {C : Type*} [Category C] {V W Z : C} (f : V ⟶ W) (g : W ⟶ Z)
    (hf : IsIso f) (hfg : IsIso (f ≫ g)) : IsIso g := by
  have := hf
  have := hfg
  exact IsIso.of_isIso_comp_left f g

/-- `underAdjointHom π Y` is the base-change isomorphism followed by the restriction of scalars of
the adjoint of `underResMap π Y`. -/
theorem underAdjointHom_eq (π : P ⟶ sectionsComplex K X.pair) (Y : Under X) :
    underAdjointHom π Y =
      (tensorComplexBaseIso (underHom Y) P).hom ≫
        ((ModuleCat.restrictScalars (underHom Y)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((Stacks.CechRingBaseChange.complexAdj (underHom Y)).homEquiv P
            (sectionsComplex K Y.right.pair)).symm (underResMap π Y)) := rfl

/-- Precomposing with a quasi-isomorphism does not change whether the derived base-change
comparison is invertible. -/
private theorem isIso_derivedBaseChange_comp_iff {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : CochainComplex (ModuleCat.{u} S) ℤ} (π : K' ⟶ K) [QuasiIso π]
    (u : K ⟶ (CochainComplex.restrictScalars φ).obj L) :
    IsIso (LocalCohomology.derivedBaseChange φ (π ≫ u)) ↔
      IsIso (LocalCohomology.derivedBaseChange φ u) := by
  have : IsIso ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
      φ).functor.map (DerivedCategory.Q.map π)) := inferInstance
  rw [LocalCohomology.derivedBaseChange_comp_left]
  exact isIso_comp_left_iff _ _

/-- The base-change isomorphism followed by the restriction of an adjoint is a quasi-isomorphism
iff the adjoint is. -/
private theorem quasiIso_tensorComplexBaseIso_comp_iff {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (L : CochainComplex (ModuleCat.{u} S) ℤ)
    (g : (CochainComplex.extendScalars φ).obj P ⟶ L) :
    QuasiIso ((tensorComplexBaseIso φ P).hom ≫
      (CochainComplex.restrictScalars φ).map g) ↔ QuasiIso g := by
  rw [quasiIso_iff_comp_left]
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (ModuleCat.restrictScalars φ)

open CochainComplex.DerivedExtensionScalars Stacks.CechRingBaseChange in
/-- **The base-change comparison at an object under `X` is a quasi-isomorphism.** -/
theorem quasiIso_underAdjointHom (Dat : PresentedCechDatum.{u}) {X : PairOver A I}
    {P : CochainComplex (ModuleCat.{u} X.pair.ring) ℤ} (hP : CochainComplex.KFlat.{u, u} P)
    (π : P ⟶ sectionsComplex Dat.complex X.pair) (hπ : QuasiIso π) (Y : Under X) :
    QuasiIso (underAdjointHom π Y) := by
  have := hπ
  have hA : IsIso (LocalCohomology.derivedBaseChange (underHom Y) (underResMap π Y)) :=
    (isIso_derivedBaseChange_comp_iff _ π _).mpr (Dat.isIso_derivedBaseChange (Hom.toHom Y.hom))
  have hC : IsIso ((derivedExtension (underHom Y)).comparison.app P) :=
    (derivedExtension (underHom Y)).comparison_isIso_of_kFlat P hP
  rw [derivedBaseChange_eq, isIso_comp_left_iff] at hA
  exact (quasiIso_tensorComplexBaseIso_comp_iff _ P _ _).mpr
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hA)

/-! ### The comparison at `(A, I)` itself, as the colimit of the comparisons under `X` -/

/-- **The base-change comparison at `(A, I)`**: the complex-level adjoint
`A ⊗_{R} P ⟶ K(A, I)` of the germ map, read over the ring of `X.pair`. -/
def germAdjointHom (hI : I.FG) (π : P ⟶ sectionsComplex K X.pair) :
    (underTensorCocone hI X P).pt ⟶ (underSectionsComplexCocone hI K X).pt :=
  (tensorComplexBaseIso X.hom P).hom ≫
    ((ModuleCat.restrictScalars X.hom).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((Stacks.CechRingBaseChange.complexAdj X.hom).homEquiv P
        ((colimitComplexFunctor hI).obj K)).symm (π ≫ germComplexMap hI K X))

/-- `germAdjointHom hI π` is the base-change isomorphism followed by the restriction of scalars of
the adjoint of `π ≫ germComplexMap hI K X`. -/
theorem germAdjointHom_eq (hI : I.FG) (π : P ⟶ sectionsComplex K X.pair) :
    germAdjointHom hI π =
      (tensorComplexBaseIso X.hom P).hom ≫
        ((ModuleCat.restrictScalars X.hom).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((Stacks.CechRingBaseChange.complexAdj X.hom).homEquiv P
            ((colimitComplexFunctor hI).obj K)).symm (π ≫ germComplexMap hI K X)) := rfl

/-- The comparison `germAdjointHom hI π` sends `a ⊗ p` to `a` times the germ of `π p` at `X`. -/
theorem germAdjointHom_f_tmulBase (hI : I.FG) (π : P ⟶ sectionsComplex K X.pair) (n : ℤ)
    (a : A) (p : P.X n) :
    ((germAdjointHom hI π).f n).hom (tmulBase X.hom (P.X n) a p) =
      a • germAt hI (K.X n) X ((π.f n).hom p) :=
  (congrArg
    (fun w : (ModuleCat.extendScalars X.hom).obj (P.X n) ⟶
        ((colimitComplexFunctor hI).obj K).X n ↦ w.hom (tmulBase X.hom (P.X n) a p))
    (complexAdj_homEquiv_symm_f X.hom (π ≫ germComplexMap hI K X) n)).trans
    (adjointHom_tmulBase X.hom ((π ≫ germComplexMap hI K X).f n) a p)

/-- The cocone map of `underTensorCocone` at `Y` sends `s ⊗ p` to `Y.right.hom s ⊗ p`. -/
theorem underTensorCocone_ι_f_tmulBase (hI : I.FG) (Y : Under X) (n : ℤ)
    (s : Y.right.pair.ring) (p : P.X n) :
    (((underTensorCocone hI X P).ι.app Y).f n).hom (tmulBase (underHom Y) (P.X n) s p) =
      tmulBase X.hom (P.X n) (Y.right.hom s) p :=
  (whiskerRight_tmulBase (underHom Y) X.hom ((underRingCocone hI X).ι.app Y) s p).trans
    (congrArg (fun a : A ↦ tmulBase X.hom (P.X n) a p) (underRingCocone_ι_app_apply hI X Y s))

/-- The germ at `Y.right` of the value of the restricted resolution at `Y` is the germ at `X` of
the value of `π`. -/
theorem germAt_underResElt (hI : I.FG) (π : P ⟶ sectionsComplex K X.pair) (Y : Under X) (n : ℤ)
    (p : P.X n) :
    germAt hI (K.X n) Y.right (underResElt π Y n p) =
      germAt hI (K.X n) X ((π.f n).hom p) :=
  germAt_restriction hI (K.X n) Y.hom ((π.f n).hom p)

/-- **The comparison at `(A, I)` is the colimit of the comparisons under `X`.** -/
theorem underTensorCocone_ι_comp (hI : I.FG) (π : P ⟶ sectionsComplex K X.pair) (Y : Under X) :
    (underTensorCocone hI X P).ι.app Y ≫ germAdjointHom hI π =
      (underAlpha π).app Y ≫ (underSectionsComplexCocone hI K X).ι.app Y := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  refine hom_ext_tmulBase (V := P.X n) (underHom Y) fun s p ↦ ?_
  show ((germAdjointHom hI π).f n).hom
      ((((underTensorCocone hI X P).ι.app Y).f n).hom (tmulBase (underHom Y) (P.X n) s p)) =
    germAt hI (K.X n) Y.right (((underAdjointHom π Y).f n).hom
      (tmulBase (underHom Y) (P.X n) s p))
  rw [underTensorCocone_ι_f_tmulBase, germAdjointHom_f_tmulBase, underAdjointHom_f_tmulBase]
  exact (congrArg (fun z : (colimitFunctor hI).obj (K.X n) ↦ Y.right.hom s • z)
      (germAt_underResElt hI π Y n p).symm).trans
    (germAt_smul hI (K.X n) Y.right s (underResElt π Y n p)).symm

/-- **The base-change comparison at `(A, I)` is a quasi-isomorphism.** -/
theorem quasiIso_germAdjointHom (Dat : PresentedCechDatum.{u}) (hI : I.FG) {X : PairOver A I}
    {P : CochainComplex (ModuleCat.{u} X.pair.ring) ℤ} (hP : CochainComplex.KFlat.{u, u} P)
    (π : P ⟶ sectionsComplex Dat.complex X.pair) (hπ : QuasiIso π) :
    QuasiIso (germAdjointHom hI π) :=
  (Stacks.HomologyColimit.isStableUnderColimitsOfShape_quasiIso
      (A := ModuleCat.{u} X.pair.ring) (J := Under X) (ComplexShape.up ℤ)).condition
    (underTensorComplex X P) (underSectionsComplex Dat.complex X)
    (underTensorCocone hI X P) (underSectionsComplexCocone hI Dat.complex X)
    (isColimit_underTensorCocone hI X P) (isColimit_underSectionsComplexCocone hI Dat.complex X)
    (underAlpha π) (fun Y ↦ quasiIso_underAdjointHom Dat hP π hπ Y) (germAdjointHom hI π)
    (fun Y ↦ underTensorCocone_ι_comp hI π Y)

end PairOver

open PairOver

/-! ### The base-change statement at the germ maps -/

open CochainComplex.DerivedExtensionScalars Stacks.CechRingBaseChange in
/-- The complex-level adjoint of the germ map, precomposed with a K-flat resolution, is a
quasi-isomorphism. -/
theorem quasiIso_complexAdj_germ (Dat : PresentedCechDatum.{u}) (hI : I.FG) {X : PairOver A I}
    {P : CochainComplex (ModuleCat.{u} X.pair.ring) ℤ} (hP : CochainComplex.KFlat.{u, u} P)
    (π : P ⟶ sectionsComplex Dat.complex X.pair) (hπ : QuasiIso π) :
    QuasiIso (((complexAdj X.hom).homEquiv P
      ((colimitComplexFunctor hI).obj Dat.complex)).symm
        (π ≫ germComplexMap hI Dat.complex X)) := by
  exact (quasiIso_tensorComplexBaseIso_comp_iff _ P _ _).mp (quasiIso_germAdjointHom Dat hI hP π hπ)

open CochainComplex.DerivedExtensionScalars Stacks.CechRingBaseChange in
/-- **The base-change statement at the germ maps of [Stacks, Tag 099D], for every pair.** For a
pair `(A, I)` with `I` finitely generated and an object `X` of the index category of step 2, the
comparison `𝒦•(X.pair) ⊗^L_{X.pair.ring} A ⟶ K(A, I)` built from the germ map is an isomorphism
in `D(A)`. -/
theorem germBaseChange (Dat : PresentedCechDatum.{u}) : GermBaseChange Dat := by
  intro A _ I hI X
  obtain ⟨P, π, hPk, -, hπ, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (sectionsComplex Dat.complex X.pair)
  have := hπ
  exact (isIso_derivedBaseChange_comp_iff X.hom π _).mp
    (isIso_derivedBaseChange_of_kFlat X.hom hPk (π ≫ germComplexMap hI Dat.complex X)
      (quasiIso_complexAdj_germ Dat hI hPk π hπ))

/-- **Condition (c) of [Stacks, Tag 099D] for the colimit complex of step 2, at every ring
map.** -/
theorem colimitBaseChange (Dat : PresentedCechDatum.{u}) : ColimitBaseChange Dat :=
  colimitBaseChange_of_germBaseChange Dat (germBaseChange Dat)

end Stacks.PairSite

end

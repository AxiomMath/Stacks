module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Naturality in the sheaf of the derived functors of the sheaf-to-presheaf inclusion

Let `(C, J)` be a small site. [Stacks, Tag 03AY] states that the inclusion
`i = sheafToPresheaf J AddCommGrpCat` of abelian sheaves into abelian presheaves is left exact,
and that its right derived functors are the cohomology presheaves, `Rᵖ i = H̲ᵖ`. The left
exactness and the *objectwise* half of the second assertion are proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf`,
which records that
  the naturality in the
sheaf is left unproved. This file supplies that naturality, so that the identification is one of
functors `Ab(C) ⥤ PAb(C)`, which is how Tag 03AZ (the Čech-to-cohomology spectral sequence)
consumes it.

The comparison of Section 21.7 is a four-factor chain
`Extᵖ(L U, G) ≃+ Hᵖ(Hom(single (L U), I.cochainComplex)) ≃+ ⋯ ≃+ Hᵖ(I^•(U))`
for an injective resolution `I` of `G` and the local generator `L U`. Naturality of each factor
in the resolution is already available: factor A is
`Stacks.Cohomology.extAddEquivCohomologyClass_naturality_coeff`, factor D is
`homologyAddEquiv_postcomp`, factor C is
`Stacks.Cohomology.homComplexSingleIsoCoyoneda_naturality` and factor B is
`Stacks.Cohomology.mapExtendHomologyIso_naturality_complex`. What is added here is the assembly:
`factorBCDApply_naturality` glues D, C and B, `extEquivHomComplexHomology_naturality_coeff` adds
A, and `extEquivSectionHomology_naturality_coeff` adds the corepresentability step
`Stacks.Cohomology.homComplexHomologyEquivSectionHomology_naturality_coeff`. The resulting
naturality square for `Stacks.Cohomology.cohomologyPresheafIsoResolution` is then composed with
Mathlib's `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality`, which handles
the right-derived-functor side, to give the natural isomorphism
`rightDerivedSheafToPresheafIso`.

## Main definitions

* `Stacks.Cohomology.factorBCDApply`: the last three comparison isomorphisms of the chain above,
  applied to a cohomology class, in an arbitrary abelian category.
* `Stacks.Cohomology.rightDerivedSheafToPresheafIso`: **Stacks 03AY**, second half — the natural
  isomorphism `(sheafToPresheaf J AddCommGrpCat).rightDerived p ≅ Sheaf.cohomologyPresheafFunctor
  J p`.

## Main results

* `Stacks.Cohomology.factorBCDApply_naturality`: `factorBCDApply` is natural in the injective
  resolution, along a morphism of resolutions.
* `Stacks.Cohomology.extEquivHomComplexHomology_naturality_coeff`,
  `Stacks.Cohomology.extEquivSectionHomology_naturality_coeff`: the comparisons of Section 21.7
  are natural in the sheaf.
* `Stacks.Cohomology.cohomologyPresheafIsoResolution_inv_naturality`,
  `Stacks.Cohomology.cohomologyPresheafIsoResolution_hom_naturality`: the naturality square of
  `cohomologyPresheafIsoResolution` in the sheaf, in both directions.

## Implementation notes

The generic section is stated for `A : Type (v + 1)` with `[Category.{v} A]` rather than for an
arbitrary `A : Type uA`. This is not a choice: the two inputs
`Stacks.Cohomology.Locality.mapExtendHomologyIso` and
`Stacks.Cohomology.mapExtendHomologyIso_naturality_complex` require their source and target
categories to live in the *same* `Type` universe, and the target here is the category
`AddCommGrpCat.{v} : Type (v + 1)` of the corepresentable functor `preadditiveCoyoneda.obj (op
X)`. The instance used below is `A = Sheaf J AddCommGrpCat.{u} : Type (u + 1)` with
`[Category.{u} A]`, the small-site convention of `RightDerivedSheafToPresheaf`, so the
restriction is invisible at the point of use. Keeping the assembly generic is what makes it
elaborate inside the default heartbeat budget: the same argument written directly over
`Sheaf J AddCommGrpCat.{u}` costs more than a million heartbeats, because every step re-unifies
the sheaf category's instances.

`cohomologyPresheafIsoResolution_hom_naturality` is derived from the inverse-direction square
rather than proved directly, because only the inverse direction has components that are
`Stacks.Cohomology.Locality.extEquivSectionHomology` itself, which is where the coefficient-level
  lemmas
apply.

## References

* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Cohomology

section Generic

variable {A : Type (v + 1)} [Category.{v} A] [Abelian A]

/-- The composite of the last three comparison isomorphisms computing `Ext` from an injective
resolution `I` of `Z`, applied to a degree-`p` cohomology class of
`Hom^•(single X, I.cochainComplex)`: the Mathlib comparison `homologyAddEquiv`, the
identification of a Hom complex out of a single complex with the degreewise corepresentable
functor (`Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda`), and the passage from the
  `ℤ`-extension
back to the `ℕ`-indexed resolution (`Stacks.Cohomology.Locality.mapExtendHomologyIso`). This is
`Stacks.Cohomology.Locality.factorBCD` in applied form. -/
noncomputable abbrev factorBCDApply (X : A) {Z : A} (I : InjectiveResolution Z) (p : ℕ)
    (cls : CochainComplex.HomComplex.CohomologyClass
      ((CochainComplex.singleFunctor A 0).obj X) I.cochainComplex (p : ℤ)) :
    (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology p :=
  (Stacks.Cohomology.Locality.mapExtendHomologyIso
      (preadditiveCoyoneda.obj (Opposite.op X)) I.cocomplex p).hom
    (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) (p : ℤ)).mapIso
      (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda X I.cochainComplex)).hom
      ((CochainComplex.HomComplex.homologyAddEquiv
        ((CochainComplex.singleFunctor A 0).obj X) I.cochainComplex (p : ℤ)).symm cls))

/-- **Naturality of `factorBCDApply` in the resolution.** A morphism `φ` of injective resolutions
above `f : Z ⟶ Z'` turns postcomposition of cohomology classes with `φ.hom'` into the map induced
on the homology of the corepresentable complexes by `φ.hom`. This is the three-factor glue: the
`homologyAddEquiv` factor is `homologyAddEquiv_postcomp`, the corepresentability factor is
`homComplexSingleIsoCoyoneda_naturality` and the extension factor is
`mapExtendHomologyIso_naturality_complex`. -/
theorem factorBCDApply_naturality (X : A) {Z Z' : A} {f : Z ⟶ Z'}
    (I : InjectiveResolution Z) (I' : InjectiveResolution Z') (φ : I.Hom I' f) (p : ℕ)
    (cls : CochainComplex.HomComplex.CohomologyClass
      ((CochainComplex.singleFunctor A 0).obj X) I.cochainComplex (p : ℤ)) :
    factorBCDApply X I' p
        (cohomologyClassPostcomp ((CochainComplex.singleFunctor A 0).obj X) φ.hom' (p : ℤ) cls) =
      (HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ.hom) p) (factorBCDApply X I p cls) := by
  have hD : (CochainComplex.HomComplex.homologyAddEquiv
        ((CochainComplex.singleFunctor A 0).obj X) I'.cochainComplex (p : ℤ)).symm
      (cohomologyClassPostcomp ((CochainComplex.singleFunctor A 0).obj X) φ.hom' (p : ℤ) cls) =
      (HomologicalComplex.homologyMap
        (homComplexPostcomp ((CochainComplex.singleFunctor A 0).obj X) φ.hom') (p : ℤ))
        ((CochainComplex.HomComplex.homologyAddEquiv
          ((CochainComplex.singleFunctor A 0).obj X) I.cochainComplex (p : ℤ)).symm cls) := by
    apply (CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor A 0).obj X) I'.cochainComplex (p : ℤ)).injective
    rw [AddEquiv.apply_symm_apply, ← homologyAddEquiv_postcomp, AddEquiv.apply_symm_apply]
  have hCmor :
      HomologicalComplex.homologyMap
          (homComplexPostcomp ((CochainComplex.singleFunctor A 0).obj X) φ.hom') (p : ℤ) ≫
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) (p : ℤ)).mapIso
          (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda X I'.cochainComplex)).hom =
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) (p : ℤ)).mapIso
          (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda X I.cochainComplex)).hom ≫
        HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ.hom') (p : ℤ) := by
    have h := congrArg
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) (p : ℤ)).map)
      (homComplexSingleIsoCoyoneda_naturality X φ.hom')
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hC (η : (((CochainComplex.singleFunctor A 0).obj X).HomComplex
      I.cochainComplex).homology (p : ℤ)) :
      (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) (p : ℤ)).mapIso
          (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda X I'.cochainComplex)).hom)
        ((HomologicalComplex.homologyMap
          (homComplexPostcomp ((CochainComplex.singleFunctor A 0).obj X) φ.hom') (p : ℤ)) η) =
      (HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ.hom') (p : ℤ))
        ((((HomologicalComplex.homologyFunctor AddCommGrpCat.{v}
          (ComplexShape.up ℤ) (p : ℤ)).mapIso
          (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda X I.cochainComplex)).hom) η) :=
    ConcreteCategory.congr_hom hCmor η
  have hBmor := mapExtendHomologyIso_naturality_complex
    (preadditiveCoyoneda.obj (Opposite.op X)) φ.hom p
  have hB (η : (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.cochainComplex).homology (p : ℤ)) :
      (Stacks.Cohomology.Locality.mapExtendHomologyIso
          (preadditiveCoyoneda.obj (Opposite.op X)) I'.cocomplex p).hom
        ((HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ.hom') (p : ℤ)) η) =
      (HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ.hom) p)
        ((Stacks.Cohomology.Locality.mapExtendHomologyIso
          (preadditiveCoyoneda.obj (Opposite.op X)) I.cocomplex p).hom η) := by
    rw [InjectiveResolution.Hom.hom']
    exact ConcreteCategory.congr_hom hBmor η
  rw [factorBCDApply, factorBCDApply, hD, hC]
  exact hB _

end Generic

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]

attribute [local instance 10000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- **`Stacks.Cohomology.Locality.extEquivHomComplexHomology` is natural in the sheaf.** Composing
  an `Ext`
class out of the local generator `L U` with `Abelian.Ext.mk₀ f` corresponds to the map on
Hom-complex homology induced by a lift `φ` of `f : G ⟶ H` to the chosen injective resolutions. -/
theorem extEquivHomComplexHomology_naturality_coeff
    {G H : Sheaf J AddCommGrpCat.{u}} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f)
    (p : ℕ) (U : C) (ξ : Abelian.Ext (Stacks.Cohomology.Locality.freeYonedaSheaf (J := J) U) G p) :
    Stacks.Cohomology.Locality.extEquivHomComplexHomology H I' p U
        (ξ.comp (Abelian.Ext.mk₀ f) (add_zero p)) =
      (HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (Opposite.op
          (Stacks.Cohomology.Locality.freeYonedaSheaf (J := J) U))).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ.hom) p)
        (Stacks.Cohomology.Locality.extEquivHomComplexHomology G I p U ξ) := by
  have hchain : ∀ (G' : Sheaf J AddCommGrpCat.{u}) (I'' : InjectiveResolution G')
      (x : Abelian.Ext (Stacks.Cohomology.Locality.freeYonedaSheaf (J := J) U) G' p),
      Stacks.Cohomology.Locality.extEquivHomComplexHomology G' I'' p U x =
        factorBCDApply (Stacks.Cohomology.Locality.freeYonedaSheaf (J := J) U) I'' p
          (I''.extAddEquivCohomologyClass x) := fun _ _ _ => rfl
  rw [hchain, hchain,
    extAddEquivCohomologyClass_naturality_coeff f I I' φ p
      (Stacks.Cohomology.Locality.freeYonedaSheaf (J := J) U) ξ,
    factorBCDApply_naturality]

/-- **The bridge `Stacks.Cohomology.Locality.extEquivSectionHomology` is natural in the sheaf.** It
intertwines composition of an `Ext` class with `Abelian.Ext.mk₀ f` with the map induced on the
homology of the section complexes by a lift `φ` of `f`, evaluated at `U`. -/
theorem extEquivSectionHomology_naturality_coeff
    {G H : Sheaf J AddCommGrpCat.{u}} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f)
    (p : ℕ) (U : C) (ξ : Abelian.Ext (Stacks.Cohomology.Locality.freeYonedaSheaf (J := J) U) G p) :
    Stacks.Cohomology.Locality.extEquivSectionHomology H I' p U
        (ξ.comp (Abelian.Ext.mk₀ f) (add_zero p)) =
      ((HomologicalComplex.homologyMap
        (((sheafToPresheaf J AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ.hom) p).app (Opposite.op U))
        (Stacks.Cohomology.Locality.extEquivSectionHomology G I p U ξ) := by
  simp only [Stacks.Cohomology.Locality.extEquivSectionHomology, AddEquiv.trans_apply]
  rw [extEquivHomComplexHomology_naturality_coeff J f I I' φ p U ξ]
  exact homComplexHomologyEquivSectionHomology_naturality_coeff J f I I' φ p U _

/-- The components of the inverse of `cohomologyPresheafIsoResolution` are the bridge
`Stacks.Cohomology.Locality.extEquivSectionHomology` of Section 21.7. -/
theorem cohomologyPresheafIsoResolution_inv_app (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (p : ℕ) (U : C) :
    (cohomologyPresheafIsoResolution J G I p).inv.app (Opposite.op U) =
      (Stacks.Cohomology.Locality.extEquivSectionHomology G I p U).toAddCommGrpIso.hom :=
  rfl

/-- **`cohomologyPresheafIsoResolution` is natural in the sheaf, inverse direction.** A morphism
`φ` of injective resolutions above `f : G ⟶ H` makes the identifications of the cohomology
presheaves with the homology presheaves of the section complexes into a commutative square. -/
theorem cohomologyPresheafIsoResolution_inv_naturality
    {G H : Sheaf J AddCommGrpCat.{u}} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f) (p : ℕ) :
    (Sheaf.cohomologyPresheafFunctor J p).map f ≫
        (cohomologyPresheafIsoResolution J H I' p).inv =
      (cohomologyPresheafIsoResolution J G I p).inv ≫
        ((sheafToPresheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map φ.hom := by
  ext ⟨U⟩ ξ
  exact extEquivSectionHomology_naturality_coeff J f I I' φ p U ξ

/-- **`cohomologyPresheafIsoResolution` is natural in the sheaf.** The forward form of
`cohomologyPresheafIsoResolution_inv_naturality`. -/
theorem cohomologyPresheafIsoResolution_hom_naturality
    {G H : Sheaf J AddCommGrpCat.{u}} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f) (p : ℕ) :
    ((sheafToPresheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map φ.hom ≫
        (cohomologyPresheafIsoResolution J H I' p).hom =
      (cohomologyPresheafIsoResolution J G I p).hom ≫
        (Sheaf.cohomologyPresheafFunctor J p).map f := by
  rw [← Iso.eq_comp_inv, Category.assoc,
    cohomologyPresheafIsoResolution_inv_naturality J f I I' φ p,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- `rightDerivedObjIsoCohomologyPresheaf` is, by construction, the composite of the computation
of the right derived functor on the chosen injective resolution with
`cohomologyPresheafIsoResolution`. -/
theorem rightDerivedObjIsoCohomologyPresheaf_hom (G : Sheaf J AddCommGrpCat.{u}) (p : ℕ) :
    (rightDerivedObjIsoCohomologyPresheaf J G p).hom =
      ((injectiveResolution G).isoRightDerivedObj
        (sheafToPresheaf J AddCommGrpCat.{u}) p).hom ≫
        (cohomologyPresheafIsoResolution J G (injectiveResolution G) p).hom :=
  rfl

/-- **Stacks 03AY, right derived functors.** The `p`-th right derived functor of the inclusion of
abelian sheaves into abelian presheaves on a small site is naturally isomorphic to the functor
sending an abelian sheaf to its degree-`p` cohomology presheaf. -/
@[stacks 03AY "right derived functors", sga "4 IV 4.8" "partial", sga "4 V 2.4.2" "special case"]
noncomputable def rightDerivedSheafToPresheafIso (p : ℕ) :
    (sheafToPresheaf J AddCommGrpCat.{u}).rightDerived p ≅
      Sheaf.cohomologyPresheafFunctor J p :=
  NatIso.ofComponents (fun G ↦ rightDerivedObjIsoCohomologyPresheaf J G p) (by
    intro G H f
    let φ : (injectiveResolution G).Hom (injectiveResolution H) f :=
      ⟨InjectiveResolution.desc f _ _, by
        simpa using InjectiveResolution.desc_commutes_zero f
          (injectiveResolution H) (injectiveResolution G)⟩
    rw [rightDerivedObjIsoCohomologyPresheaf_hom, rightDerivedObjIsoCohomologyPresheaf_hom,
      ← Category.assoc,
      InjectiveResolution.isoRightDerivedObj_hom_naturality f _ _ φ.hom
        (by simpa using φ.ι_f_zero_comp_hom_f_zero),
      Category.assoc,
      cohomologyPresheafIsoResolution_hom_naturality J f _ _ φ p, Category.assoc])

end Stacks.Cohomology

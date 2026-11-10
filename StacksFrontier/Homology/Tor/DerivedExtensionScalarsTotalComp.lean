module

public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

@[expose] public noncomputable section

/-!
# Functoriality of derived extension of scalars in the ring

Derived extension of scalars along a homomorphism of commutative rings is a pseudofunctor from
rings to derived categories of modules: for `f : A →+* B` and `g : B →+* C` the composite
`- ⊗ᴸ_A B ⊗ᴸ_B C` is canonically isomorphic to `- ⊗ᴸ_A C`, the identity homomorphism induces the
identity functor, and these isomorphisms satisfy the cocycle condition and the two unit laws.

The comparison isomorphisms are constructed by uniqueness of maps into a total left derived
functor, and are isomorphisms because all three comparison maps are isomorphisms on a K-flat
complex and extension of scalars preserves K-flatness. The cocycle condition and the right unit
law hold because both sides are maps into the total left derived functor of one and the same
degreewise extension of scalars, so it suffices to compare them after restricting along the
localization functor, where they become composites of comparison maps and of the underived
coherence isomorphisms of `ModuleCat.extendScalars`; the left unit law then follows formally.

## Main definitions

* `CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexComp` and
  `CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexId`: the scalar-tower
  composition and the unit isomorphism for degreewise extension of scalars on complexes,
  followed by localization.
* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp`: the composition
  isomorphism `(- ⊗ᴸ_A B) ⋙ (- ⊗ᴸ_B C) ≅ - ⊗ᴸ_A C` of unbounded derived extension-of-scalars
  functors.
* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId`: the unit isomorphism
  identifying derived extension of scalars along the identity with the identity functor.

## Main results

* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_comparison`: the
  composition isomorphism is compatible with the comparison maps to degreewise extension of
  scalars.
* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_assoc`: the cocycle
  condition for three composable ring homomorphisms.
* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_id_comp` and
  `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_comp_id`: the left
  and right unit laws.

## Implementation notes

The two derived categories are instance arguments throughout, as they are in
`StacksFrontier.Homology.Tor.DerivedExtensionScalars`: `HasDerivedCategory` carries the localized
category as data, so a statement proved at one model says nothing about another, and consumers
work at locally small models. A composition isomorphism therefore takes three free model
binders, one for each of the three rings involved, and the cocycle condition takes four.

## References

* [The Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

open CategoryTheory

universe u v wA wB wC wD

namespace CochainComplex.DerivedExtensionScalars

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

/-- The scalar-tower isomorphism for degreewise extension of scalars on cochain complexes,
followed by the localization functor to the derived category. -/
public def extensionOfScalarsComplexComp
    [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)] (f : A →+* B) (g : B →+* C) :
    extensionOfScalarsComplex.{u, u, v} (g.comp f) ≅
      (ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        extensionOfScalarsComplex.{u, u, v} g :=
  Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{u, max u v} f g) (ComplexShape.up ℤ))
    DerivedCategory.Q

/-- Degreewise extension of scalars along the identity homomorphism, followed by localization,
is the localization functor. -/
public def extensionOfScalarsComplexId (R : Type u) [CommRing R]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} R)] :
    extensionOfScalarsComplexGeneral.{u, v, u} (RingHom.id R) ≅
      DerivedCategory.Q (C := ModuleCat.{max u v} R) :=
  Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsId.{u, max u v} R) (ComplexShape.up ℤ))
    DerivedCategory.Q

/-- The cocycle condition for the scalar-tower isomorphisms of extension of scalars, read on
inverses. -/
private lemma extendScalarsComp_inv_app (f : A →+* B) (g : B →+* C) (h : C →+* D)
    (M : ModuleCat.{max u v} A) :
    (ModuleCat.extendScalars.{u, u, max u v} h).map
        ((ModuleCat.extendScalarsComp.{u, max u v} f g).inv.app M) ≫
      (ModuleCat.extendScalarsComp.{u, max u v} (g.comp f) h).inv.app M =
    (ModuleCat.extendScalarsComp.{u, max u v} g h).inv.app
        ((ModuleCat.extendScalars.{u, u, max u v} f).obj M) ≫
      (ModuleCat.extendScalarsComp.{u, max u v} f (h.comp g)).inv.app M := by
  let e₁ := ModuleCat.extendScalarsComp.{u, max u v} (g.comp f) h ≪≫
    Functor.isoWhiskerRight (ModuleCat.extendScalarsComp.{u, max u v} f g)
      (ModuleCat.extendScalars.{u, u, max u v} h)
  let e₂ := ModuleCat.extendScalarsComp.{u, max u v} f (h.comp g) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, max u v} f)
      (ModuleCat.extendScalarsComp.{u, max u v} g h) ≪≫
    (Functor.associator _ _ _).symm
  have he : e₁ = e₂ := Iso.ext (ModuleCat.extendScalars_assoc.{u, max u v} f g h)
  simpa [e₁, e₂] using congrArg (fun e ↦ e.inv.app M) he

/-- The complex-level scalar-tower comparison for extension of scalars, on inverses. -/
private def extendScalarsCompInv (f : A →+* B) (g : B →+* C)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    ((ModuleCat.extendScalars.{u, u, max u v} g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶
      ((ModuleCat.extendScalars.{u, u, max u v} (g.comp f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, max u v} f g)
    (ComplexShape.up ℤ)).inv.app P

/-- The cocycle condition for the complex-level scalar-tower comparisons. -/
private lemma extendScalarsCompInv_assoc (f : A →+* B) (g : B →+* C) (h : C →+* D)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    ((ModuleCat.extendScalars.{u, u, max u v} h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extendScalarsCompInv.{u, v} f g P) ≫
        extendScalarsCompInv.{u, v} (g.comp f) h P =
      extendScalarsCompInv.{u, v} g h
          (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        extendScalarsCompInv.{u, v} f (h.comp g) P := by
  ext i : 1
  exact extendScalarsComp_inv_app f g h (P.X i)

/-- The complex-level unit comparison for extension of scalars, on inverses. -/
private def extendScalarsIdInv (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    P ⟶ ((ModuleCat.extendScalars.{u, u, max u v} (RingHom.id R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P :=
  (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId.{u, max u v} R)
    (ComplexShape.up ℤ)).inv.app P

/-- The scalar-tower isomorphism at a trailing identity homomorphism is the unit. -/
private lemma extendScalarsComp_id_hom_app (f : A →+* B) (M : ModuleCat.{max u v} A) :
    (ModuleCat.extendScalarsComp.{u, max u v} f (RingHom.id B)).hom.app M =
      (ModuleCat.extendScalarsId.{u, max u v} B).inv.app
        ((ModuleCat.extendScalars.{u, u, max u v} f).obj M) := by
  have h : (ModuleCat.extendScalarsComp.{u, max u v} f (RingHom.id B)).hom.app M ≫
      (ModuleCat.extendScalarsId.{u, max u v} B).hom.app
        ((ModuleCat.extendScalars.{u, u, max u v} f).obj M) = 𝟙 _ := by
    simpa using NatTrans.congr_app (ModuleCat.extendScalars_comp_id.{u, max u v} f) M
  exact (Iso.comp_hom_eq_id ((ModuleCat.extendScalarsId.{u, max u v} B).app _)).mp h

/-- The right unit law for the complex-level scalar-tower comparisons. -/
private lemma extendScalarsCompInv_id (f : A →+* B)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    extendScalarsIdInv.{u, v} B
          (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        extendScalarsCompInv.{u, v} f (RingHom.id B) P = 𝟙 _ := by
  ext i : 1
  change (ModuleCat.extendScalarsId.{u, max u v} B).inv.app
        ((ModuleCat.extendScalars.{u, u, max u v} f).obj (P.X i)) ≫
      (ModuleCat.extendScalarsComp.{u, max u v} f (RingHom.id B)).inv.app (P.X i) = 𝟙 _
  refine (congrArg (fun t ↦ t ≫ (ModuleCat.extendScalarsComp.{u, max u v} f
    (RingHom.id B)).inv.app (P.X i))
      (extendScalarsComp_id_hom_app.{u, v} f (P.X i)).symm).trans ?_
  exact (ModuleCat.extendScalarsComp.{u, max u v} f (RingHom.id B)).hom_inv_id_app (P.X i)

section Comp

variable [HasDerivedCategory.{wA} (ModuleCat.{max u v} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
  [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)]

/-- The comparison from the composite of two derived extension-of-scalars functors to
degreewise extension of scalars along the composite ring homomorphism. -/
private def compComparison (f : A →+* B) (g : B →+* C) :
    DerivedCategory.Q ⋙ ((totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
      (totalDerivedExtensionScalars.{u, u, v} g).functor) ⟶
        extensionOfScalarsComplexGeneral.{u, v, u} (g.comp f) :=
  Functor.whiskerRight (totalDerivedExtensionScalars.{u, u, v} f).comparison
      (totalDerivedExtensionScalars.{u, u, v} g).functor ≫
    Functor.whiskerLeft ((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (totalDerivedExtensionScalars.{u, u, v} g).comparison ≫
    (extensionOfScalarsComplexComp.{u, v, wC} f g).inv

/-- The value of the composite comparison on a complex. -/
private lemma compComparison_app (f : A →+* B) (g : B →+* C)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (compComparison.{u, v} f g).app P =
      (totalDerivedExtensionScalars.{u, u, v} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, v} g).comparison.app
          (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (extensionOfScalarsComplexComp.{u, v, wC} f g).inv.app P :=
  rfl

/-- The map from the composite of two derived extension-of-scalars functors to derived
extension of scalars along the composite, induced by the universal property. -/
private def compHom (f : A →+* B) (g : B →+* C) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
      (totalDerivedExtensionScalars.{u, u, v} g).functor ⟶
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor :=
  (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor.leftDerivedLift
    (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (.up ℤ)) _
    (compComparison f g)

/-- The defining factorization of the induced map through the comparisons. -/
private lemma compHom_fac (f : A →+* B) (g : B →+* C)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (compHom.{u, v} f g).app (DerivedCategory.Q.obj P) ≫
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P =
    (compComparison.{u, v} f g).app P :=
  (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor.leftDerived_fac_app
    (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (.up ℤ)) _
    (compComparison f g) P

/-- The induced map is an isomorphism, since all three comparisons are isomorphisms on a
K-flat complex and every object is the image of one. -/
private lemma isIso_compHom_app (f : A →+* B) (g : B →+* C)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    IsIso ((compHom.{u, v} f g).app X) := by
  have hα (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : P.KFlat) :
      IsIso ((compHom.{u, v} f g).app (DerivedCategory.Q.obj P)) := by
    have hD := (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison_isIso_of_kFlat P hP
    have hfP := (totalDerivedExtensionScalars.{u, u, v} f).comparison_isIso_of_kFlat P hP
    have hgP := (totalDerivedExtensionScalars.{u, u, v} g).comparison_isIso_of_kFlat
      (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P)
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, v} f P hP)
    have t₁ : IsIso ((totalDerivedExtensionScalars.{u, u, v} g).functor.map
      ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P)) := inferInstance
    have t₃ : IsIso ((extensionOfScalarsComplexComp.{u, v, wC} f g).inv.app P) := inferInstance
    have : IsIso ((compComparison.{u, v} f g).app P) := by
      rw [compComparison_app]
      exact IsIso.comp_isIso' t₁ (IsIso.comp_isIso' hgP t₃)
    rw [← compHom_fac] at this
    exact IsIso.of_isIso_comp_right _
      ((totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P)
  obtain ⟨P, p, hP, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, v}
    (DerivedCategory.Q.objPreimage X)
  exact (NatTrans.isIso_app_iff_of_iso (compHom.{u, v} f g)
    (asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X)).mp (hα P hP)

/-- **The composition isomorphism for derived extension of scalars.** Deriving extension of
scalars along `f : A →+* B` and then along `g : B →+* C` is deriving extension of scalars along
`g.comp f`. -/
@[no_expose]
public def totalDerivedExtensionScalarsComp (f : A →+* B) (g : B →+* C) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, v} g).functor ≅
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor :=
  @asIso _ _ _ _ (compHom.{u, v} f g)
    (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ (compHom.{u, v} f g)
      fun X ↦ isIso_compHom_app.{u, v} f g X)

/-- The composition isomorphism is compatible with the comparisons to degreewise extension of
scalars. -/
public theorem totalDerivedExtensionScalarsComp_comparison (f : A →+* B) (g : B →+* C)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (totalDerivedExtensionScalars.{u, u, v} g).functor.map
        ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P) ≫
      (totalDerivedExtensionScalars.{u, u, v} g).comparison.app
        (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
      (extensionOfScalarsComplexComp.{u, v, wC} f g).inv.app P =
    (totalDerivedExtensionScalarsComp.{u, v} f g).hom.app (DerivedCategory.Q.obj P) ≫
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P := by
  rw [← compComparison_app]
  exact (compHom_fac.{u, v} f g P).symm

/-- The comparison map evaluated at a complex, with source and target written out. -/
private def comparisonApp (f : A →+* B) (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  (totalDerivedExtensionScalars.{u, u, v} f).comparison.app P

/-- The composition isomorphism evaluated at an object, with source and target written out. -/
private def compHomApp (f : A →+* B) (g : B →+* C)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (totalDerivedExtensionScalars.{u, u, v} g).functor.obj
        ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj X) ⟶
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor.obj X :=
  (totalDerivedExtensionScalarsComp.{u, v} f g).hom.app X

/-- Two natural transformations into derived extension of scalars agree if they agree after
composing with the comparison at every complex. -/
private lemma app_eq_of_comp_comparisonApp (f : A →+* B)
    {G : DerivedCategory (ModuleCat.{max u v} A) ⥤ DerivedCategory (ModuleCat.{max u v} B)}
    (γ₁ γ₂ : G ⟶ (totalDerivedExtensionScalars.{u, u, v} f).functor)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      γ₁.app (DerivedCategory.Q.obj P) ≫ comparisonApp.{u, v} f P =
        γ₂.app (DerivedCategory.Q.obj P) ≫ comparisonApp.{u, v} f P)
    (X : DerivedCategory (ModuleCat.{max u v} A)) : γ₁.app X = γ₂.app X :=
  NatTrans.congr_app (Functor.leftDerived_ext _
    (totalDerivedExtensionScalars.{u, u, v} f).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (.up ℤ)) _ γ₁ γ₂
    (by ext P; exact h P)) X

/-- Naturality of the composition isomorphism. -/
private lemma compHomApp_naturality (f : A →+* B) (g : B →+* C)
    {X Y : DerivedCategory (ModuleCat.{max u v} A)} (φ : X ⟶ Y) :
    (totalDerivedExtensionScalars.{u, u, v} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, v} f).functor.map φ) ≫
        compHomApp.{u, v} f g Y =
      compHomApp.{u, v} f g X ≫
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor.map φ :=
  (totalDerivedExtensionScalarsComp.{u, v} f g).hom.naturality φ

/-- Naturality of the comparison map in the complex. -/
private lemma comparisonApp_naturality (f : A →+* B)
    {P P' : CochainComplex (ModuleCat.{max u v} A) ℤ} (φ : P ⟶ P') :
    (totalDerivedExtensionScalars.{u, u, v} f).functor.map (DerivedCategory.Q.map φ) ≫
        comparisonApp.{u, v} f P' =
      comparisonApp.{u, v} f P ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) :=
  (totalDerivedExtensionScalars.{u, u, v} f).comparison.naturality φ

/-- The compatibility of the composition isomorphism with the comparisons, with all sources and
targets written out. -/
private lemma compHomApp_comparisonApp (f : A →+* B) (g : B →+* C)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    compHomApp.{u, v} f g (DerivedCategory.Q.obj P) ≫ comparisonApp.{u, v} (g.comp f) P =
      (totalDerivedExtensionScalars.{u, u, v} g).functor.map (comparisonApp.{u, v} f P) ≫
        comparisonApp.{u, v} g
            (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (extendScalarsCompInv.{u, v} f g P) :=
  (totalDerivedExtensionScalarsComp_comparison.{u, v} f g P).symm

end Comp

section Assoc

variable [HasDerivedCategory.{wA} (ModuleCat.{max u v} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
  [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)]
  [HasDerivedCategory.{wD} (ModuleCat.{max u v} D)]

/-- **The cocycle condition for derived extension of scalars.** The two ways of comparing the
threefold composite of derived extension-of-scalars functors with derived extension of scalars
along the composite of three ring homomorphisms agree. -/
public theorem totalDerivedExtensionScalarsComp_assoc (f : A →+* B) (g : B →+* C) (h : C →+* D)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (totalDerivedExtensionScalars.{u, u, v} h).functor.map
        ((totalDerivedExtensionScalarsComp.{u, v} f g).hom.app X) ≫
      (totalDerivedExtensionScalarsComp.{u, v} (g.comp f) h).hom.app X =
    (totalDerivedExtensionScalarsComp.{u, v} g h).hom.app
        ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj X) ≫
      (totalDerivedExtensionScalarsComp.{u, v} f (h.comp g)).hom.app X := by
  let α : ((totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
    (totalDerivedExtensionScalars.{u, u, v} g).functor) ⋙
    (totalDerivedExtensionScalars.{u, u, v} h).functor ⟶
      (totalDerivedExtensionScalars.{u, u, v} (h.comp (g.comp f))).functor :=
    Functor.whiskerRight (totalDerivedExtensionScalarsComp.{u, v} f g).hom
        (totalDerivedExtensionScalars.{u, u, v} h).functor ≫
      (totalDerivedExtensionScalarsComp.{u, v} (g.comp f) h).hom
  let β : ((totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
    (totalDerivedExtensionScalars.{u, u, v} g).functor) ⋙
    (totalDerivedExtensionScalars.{u, u, v} h).functor ⟶
      (totalDerivedExtensionScalars.{u, u, v} (h.comp (g.comp f))).functor :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (totalDerivedExtensionScalars.{u, u, v} f).functor
          (totalDerivedExtensionScalarsComp.{u, v} g h).hom ≫
        (totalDerivedExtensionScalarsComp.{u, v} f (h.comp g)).hom
  simpa [α, β] using app_eq_of_comp_comparisonApp.{u, v} (h.comp (g.comp f)) α β (fun P ↦ by
    dsimp [α, β]
    simp only [Category.id_comp, Category.assoc]
    change (totalDerivedExtensionScalars.{u, u, v} h).functor.map
          (compHomApp.{u, v} f g (DerivedCategory.Q.obj P)) ≫
        compHomApp.{u, v} (g.comp f) h (DerivedCategory.Q.obj P) ≫
          comparisonApp.{u, v} (h.comp (g.comp f)) P =
      compHomApp.{u, v} g h
          ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj (DerivedCategory.Q.obj P)) ≫
        compHomApp.{u, v} f (h.comp g) (DerivedCategory.Q.obj P) ≫
          comparisonApp.{u, v} (h.comp (g.comp f)) P
    have k₂ : compHomApp.{u, v} f (h.comp g) (DerivedCategory.Q.obj P) ≫
        comparisonApp.{u, v} (h.comp (g.comp f)) P = _ :=
      compHomApp_comparisonApp.{u, v} f (h.comp g) P
    rw [compHomApp_comparisonApp.{u, v} (g.comp f) h P, k₂, ← Functor.map_comp_assoc,
      compHomApp_comparisonApp.{u, v} f g P]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% compHomApp_naturality.{u, v} g h (comparisonApp.{u, v} f P),
      reassoc_of% compHomApp_comparisonApp.{u, v} g h
        (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P),
      reassoc_of% comparisonApp_naturality.{u, v} h (extendScalarsCompInv.{u, v} f g P),
      ← Functor.map_comp, ← Functor.map_comp, extendScalarsCompInv_assoc.{u, v} f g h P]) X

end Assoc

section Unit

variable [HasDerivedCategory.{wA} (ModuleCat.{max u v} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]

/-- **The unit isomorphism for derived extension of scalars.** Derived extension of scalars
along the identity homomorphism of `R` is the identity functor of `D(R)`. -/
@[no_expose]
public def totalDerivedExtensionScalarsId (R : Type u) [CommRing R]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} R)] :
    𝟭 (DerivedCategory (ModuleCat.{max u v} R)) ≅
      (totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)).functor := by
  let D := totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)
  let e : DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{max u v} R)) ≅
      extensionOfScalarsComplexGeneral.{u, v, u} (RingHom.id R) :=
    (Functor.rightUnitor _) ≪≫ (extensionOfScalarsComplexId.{u, v, wA} R).symm
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (.up ℤ)) _ e
  change 𝟭 _ ≅ D.functor
  letI : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (.up ℤ)) := D.isLeftDerived
  exact Functor.leftDerivedUnique D.functor (𝟭 _) e.hom D.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (.up ℤ))

/-- The unit isomorphism is compatible with the comparisons to degreewise extension of
scalars. -/
public theorem totalDerivedExtensionScalarsId_comparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} R)]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (totalDerivedExtensionScalarsId.{u, v, wA} R).hom.app (DerivedCategory.Q.obj P) ≫
      (totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)).comparison.app P =
        (extensionOfScalarsComplexId.{u, v, wA} R).inv.app P := by
  simp [totalDerivedExtensionScalarsId, Functor.leftDerivedUnique,
    Functor.leftDerivedNatIso, Functor.leftDerivedNatTrans]

/-- The unit isomorphism evaluated at an object, with source and target written out. -/
private def unitApp (R : Type u) [CommRing R]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} R)]
    (X : DerivedCategory (ModuleCat.{max u v} R)) :
    X ⟶ (totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)).functor.obj X :=
  (totalDerivedExtensionScalarsId.{u, v, wA} R).hom.app X

/-- Naturality of the unit isomorphism. -/
private lemma unitApp_naturality (R : Type u) [CommRing R]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} R)]
    {X Y : DerivedCategory (ModuleCat.{max u v} R)} (φ : X ⟶ Y) :
    φ ≫ unitApp.{u, v} R Y =
      unitApp.{u, v} R X ≫
        (totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)).functor.map φ :=
  (totalDerivedExtensionScalarsId.{u, v, wA} R).hom.naturality φ

/-- The compatibility of the unit isomorphism with the comparisons, with all sources and
targets written out. -/
private lemma unitApp_comparisonApp (R : Type u) [CommRing R]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} R)]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    unitApp.{u, v} R (DerivedCategory.Q.obj P) ≫ comparisonApp.{u, v} (RingHom.id R) P =
      DerivedCategory.Q.map (extendScalarsIdInv.{u, v} R P) :=
  totalDerivedExtensionScalarsId_comparison.{u, v, wA} R P

/-- **The right unit law for derived extension of scalars.** Composing derived extension of
scalars along `f : A →+* B` with derived extension of scalars along the identity of `B` gives
back the original functor. -/
public theorem totalDerivedExtensionScalarsComp_comp_id (f : A →+* B)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (totalDerivedExtensionScalarsId.{u, v, wB} B).hom.app
        ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj X) ≫
      (totalDerivedExtensionScalarsComp.{u, v} f (RingHom.id B)).hom.app X = 𝟙 _ := by
  let α : (totalDerivedExtensionScalars.{u, u, v} f).functor ⟶
      (totalDerivedExtensionScalars.{u, u, v} f).functor :=
    Functor.whiskerLeft (totalDerivedExtensionScalars.{u, u, v} f).functor
        (totalDerivedExtensionScalarsId.{u, v, wB} B).hom ≫
      (totalDerivedExtensionScalarsComp.{u, v} f (RingHom.id B)).hom
  exact app_eq_of_comp_comparisonApp.{u, v} f α (𝟙 _) (fun P ↦ by
    dsimp [α]
    simp only [Category.id_comp, Category.assoc]
    change unitApp.{u, v} B ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj
          (DerivedCategory.Q.obj P)) ≫
        compHomApp.{u, v} f (RingHom.id B) (DerivedCategory.Q.obj P) ≫
          comparisonApp.{u, v} f P =
      comparisonApp.{u, v} f P
    have k₁ : compHomApp.{u, v} f (RingHom.id B) (DerivedCategory.Q.obj P) ≫
        comparisonApp.{u, v} f P = _ :=
      compHomApp_comparisonApp.{u, v} f (RingHom.id B) P
    rw [k₁, ← reassoc_of% unitApp_naturality.{u, v} B (comparisonApp.{u, v} f P),
      reassoc_of% unitApp_comparisonApp.{u, v} B
        (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P),
      ← Functor.map_comp, extendScalarsCompInv_id.{u, v} f P,
      CategoryTheory.Functor.map_id, Category.comp_id]) X

/-- **The left unit law for derived extension of scalars.** Composing derived extension of
scalars along the identity of `A` with derived extension of scalars along `f : A →+* B` gives
back the original functor. -/
public theorem totalDerivedExtensionScalarsComp_id_comp (f : A →+* B)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor.map
        ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app X) ≫
      (totalDerivedExtensionScalarsComp.{u, v} (RingHom.id A) f).hom.app X = 𝟙 _ := by
  have hc := totalDerivedExtensionScalarsComp_assoc.{u, v}
    (RingHom.id A) (RingHom.id A) f X
  have hu := totalDerivedExtensionScalarsComp_comp_id.{u, v} (RingHom.id A) X
  have hη : (totalDerivedExtensionScalars.{u, u, v} (RingHom.id A)).functor.map
        ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app X) =
      (totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app
        ((totalDerivedExtensionScalars.{u, u, v} (RingHom.id A)).functor.obj X) :=
    (cancel_epi ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app X)).mp
      ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.naturality
        ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app X)).symm
  have hL : (totalDerivedExtensionScalarsComp.{u, v} (RingHom.id A) f).hom.app
        ((totalDerivedExtensionScalars.{u, u, v} (RingHom.id A)).functor.obj X) =
      (totalDerivedExtensionScalars.{u, u, v} f).functor.map
        ((totalDerivedExtensionScalarsComp.{u, v} (RingHom.id A) (RingHom.id A)).hom.app X) :=
    ((cancel_mono ((totalDerivedExtensionScalarsComp.{u, v}
      (RingHom.id A) f).hom.app X)).mp hc).symm
  have hleft : (totalDerivedExtensionScalarsComp.{u, v} (RingHom.id A) f).hom.app X ≫
      (totalDerivedExtensionScalars.{u, u, v} f).functor.map
        ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app X) = 𝟙 _ := by
    calc
      _ = (totalDerivedExtensionScalars.{u, u, v} f).functor.map
            ((totalDerivedExtensionScalars.{u, u, v} (RingHom.id A)).functor.map
              ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app X)) ≫
          (totalDerivedExtensionScalarsComp.{u, v} (RingHom.id A) f).hom.app
            ((totalDerivedExtensionScalars.{u, u, v} (RingHom.id A)).functor.obj X) :=
        ((totalDerivedExtensionScalarsComp.{u, v} (RingHom.id A) f).hom.naturality
          ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app X)).symm
      _ = (totalDerivedExtensionScalars.{u, u, v} f).functor.map
            ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app
                ((totalDerivedExtensionScalars.{u, u, v} (RingHom.id A)).functor.obj X) ≫
              (totalDerivedExtensionScalarsComp.{u, v} (RingHom.id A)
                (RingHom.id A)).hom.app X) := by
        rw [hη, hL, (totalDerivedExtensionScalars.{u, u, v} f).functor.map_comp]
      _ = 𝟙 _ := by
        rw [hu, (totalDerivedExtensionScalars.{u, u, v} f).functor.map_id]
  apply (cancel_mono ((totalDerivedExtensionScalars.{u, u, v} f).functor.map
    ((totalDerivedExtensionScalarsId.{u, v, wA} A).hom.app X))).mp
  rw [Category.assoc, hleft]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end Unit

end CochainComplex.DerivedExtensionScalars

end

module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsComp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# The coherence between the two presentations of derived extension of scalars

Let `ε : R →+* R₂` be an isomorphism of commutative rings with inverse `ε'`, and let
`ψ : R₂ →+* R'` and `χ : R' →+* R''` be homomorphisms.  Two isomorphisms of derived
extension-of-scalars functors are then in play:

* `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso`, which identifies derived
  restriction of scalars along `ε'` followed by derived extension of scalars along a
  homomorphism out of `R₂` with derived extension of scalars along that homomorphism
  precomposed with `ε`;
* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso`, which identifies the
  composite of two derived extension-of-scalars functors with derived extension of scalars along
  the composite homomorphism.

Both can be used to bring
`restrictScalars ε' ⋙ extendScalars ψ ⋙ extendScalars χ` down to
`extendScalars (χ ∘ ψ ∘ ε)`: either merge `ψ` with `χ` first and absorb `ε` afterwards, or absorb
`ε` into `ψ` first and merge with `χ` afterwards.

## Main results

* `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso_comp_compIso`: the two agree.
* `StacksDraft.DerivedRingIso.restrictIsoApp_of_eq_id`: **the identity case.**  When `ε = ε'` is a
  homomorphism *equal to the identity* — which is what the germ comparison of a point of a scheme
  with itself is — absorbing it into `ψ` is derived extension of scalars along `ψ` applied to the
  collapse `StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso` of derived restriction of
  scalars, followed by the transport from `ψ` to `ψ ∘ ε`.

## Implementation notes

The equation carries no transport.  Composition of ring homomorphisms is associative
definitionally, so `χ.comp (ψ.comp ε)` and `(χ.comp ψ).comp ε` are the same term and the two
sides have the same target.  (They are not the same *expression*, so a rewrite whose statement
spells the target one way is quoted through a `have` that spells it the other.)

Both sides are maps into the total left derived functor of degreewise extension of scalars along
`χ ∘ ψ ∘ ε`, so `CategoryTheory.Functor.leftDerived_ext` reduces the equation to an equation
below the localization functor, exactly as
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_assoc` is proved.  There
the characterizing equations of the two isomorphisms —
`comparison_comp_comparison_comp_mapHomologicalComplexCompIso` in
`StacksDraft.DerivedExtensionScalarsComp` and
`StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso_hom_app_Q_comp_comparison` — turn
it into `DerivedCategory.Q` of a question about cochain complexes, and that question is answered
degreewise by `extendScalarsRestrictIso_hom_app_comp_extendScalarsComp_inv_app`: the naturality of
the degreewise merge `ModuleCat.extendScalarsComp` at the comparison of restriction along `ε'`
with extension along `ε`, together with the degreewise cocycle condition coming from
`ModuleCat.extendScalars_assoc`.

The comparisons of the chosen models with degreewise extension of scalars are quoted here through
the wrappers `comparisonApp`, `compIsoApp` and `restrictIsoApp`, whose sources and targets are
written out.  The comparison's own target is spelled
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral`, which is the composite
of degreewise extension of scalars with the localization functor but not that term; a goal mixing
the two spellings is not type-correct at the transparency `rw` type-checks its motives at, and
every rewrite on it fails.  The wrappers state the localized spelling once.

## References

* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedExtensionScalarsComp

noncomputable section

namespace StacksDraft.DerivedRingIso

universe u

attribute [local instance] HasDerivedCategory.standard

section Wrappers

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- The comparison of the chosen model of total derived extension of scalars with degreewise
extension of scalars, at a cochain complex, with its source and target written out. -/
def comparisonApp (φ : A →+* B) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          P) :=
  (totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P

/-- The composition isomorphism of derived extension of scalars at an object, with its source and
target written out. -/
def compIsoApp (φ : A →+* B) (γ : B →+* C) (X : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalars.{u, u, u} γ).functor.obj
        ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj X) ⟶
      (totalDerivedExtensionScalars.{u, u, u} (γ.comp φ)).functor.obj X :=
  (derivedExtensionScalarsCompIso φ γ).hom.app X

/-- The degreewise merge of two extensions of scalars at a cochain complex. -/
def extendScalarsCompInvApp (φ : A →+* B) (γ : B →+* C)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} γ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          P) ⟶
      ((ModuleCat.extendScalars.{u, u, u} (γ.comp φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp.{u, u} φ γ).symm
    (ComplexShape.up ℤ)).hom.app P

/-- Naturality of the composition isomorphism, at the wrappers. -/
theorem compIsoApp_naturality (φ : A →+* B) (γ : B →+* C)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (τ : X ⟶ Y) :
    (totalDerivedExtensionScalars.{u, u, u} γ).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} φ).functor.map τ) ≫
        compIsoApp φ γ Y =
      compIsoApp φ γ X ≫ (totalDerivedExtensionScalars.{u, u, u} (γ.comp φ)).functor.map τ :=
  (derivedExtensionScalarsCompIso φ γ).hom.naturality τ

/-- Naturality of the comparison, at the wrappers. -/
theorem comparisonApp_naturality (φ : A →+* B)
    {P P' : CochainComplex (ModuleCat.{u} A) ℤ} (τ : P ⟶ P') :
    (totalDerivedExtensionScalars.{u, u, u} φ).functor.map (DerivedCategory.Q.map τ) ≫
        comparisonApp φ P' =
      comparisonApp φ P ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          τ) :=
  (totalDerivedExtensionScalars.{u, u, u} φ).comparison.naturality τ

/-- **The characterizing equation of the composition isomorphism, at the wrappers.** -/
theorem compIsoApp_comparisonApp (φ : A →+* B) (γ : B →+* C)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    compIsoApp φ γ (DerivedCategory.Q.obj P) ≫ comparisonApp (γ.comp φ) P =
      (totalDerivedExtensionScalars.{u, u, u} γ).functor.map (comparisonApp φ P) ≫
        comparisonApp γ
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (extendScalarsCompInvApp φ γ P) :=
  (comparison_comp_comparison_comp_mapHomologicalComplexCompIso φ γ P).symm

/-- Two natural transformations into total derived extension of scalars agree if they do after
composing with the comparison at every cochain complex. -/
private theorem totalDerivedExtensionScalars_hom_ext_app (φ : A →+* B)
    {G : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B)}
    (α β : G ⟶ (totalDerivedExtensionScalars.{u, u, u} φ).functor)
    (h : ∀ P, α.app (DerivedCategory.Q.obj P) ≫ comparisonApp φ P =
      β.app (DerivedCategory.Q.obj P) ≫ comparisonApp φ P)
    (X : DerivedCategory (ModuleCat.{u} A)) : α.app X = β.app X := by
  have heq : α = β := by
    apply Functor.leftDerived_ext _ (totalDerivedExtensionScalars.{u, u, u} φ).comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) _ α β
    ext P
    exact h P
  rw [heq]

end Wrappers

section Coherence

variable {R R₂ R' R'' : Type u} [CommRing R] [CommRing R₂] [CommRing R'] [CommRing R'']
  (ε : R →+* R₂) (ε' : R₂ →+* R) (h₁ : ∀ x, ε' (ε x) = x) (h₂ : ∀ y, ε (ε' y) = y)

include h₁ h₂

/-- **The degreewise coherence.**  Extension of scalars along `χ` of the comparison for `ψ`,
followed by the merge of `ψ ∘ ε` with `χ`, is the merge of `ψ` with `χ` followed by the comparison
for `χ ∘ ψ`.

The merge of `ε` with `ψ` inside the comparison is carried across by the degreewise cocycle
condition for `ModuleCat.extendScalarsComp`, which `ModuleCat.extendScalars_assoc` supplies; what
is left is the naturality of the merge of `ψ` with `χ` at the comparison of restriction of scalars
along `ε'` with extension of scalars along `ε`. -/
theorem extendScalarsRestrictIso_hom_app_comp_extendScalarsComp_inv_app (ψ : R₂ →+* R')
    (χ : R' →+* R'') (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars.{u, u, u} χ).map
          ((extendScalarsRestrictIso ε ε' h₁ h₂ ψ).hom.app M) ≫
        (ModuleCat.extendScalarsComp.{u, u} (ψ.comp ε) χ).inv.app M =
      (ModuleCat.extendScalarsComp.{u, u} ψ χ).inv.app
          ((ModuleCat.restrictScalars.{u, u, u} ε').obj M) ≫
        (extendScalarsRestrictIso ε ε' h₁ h₂ (χ.comp ψ)).hom.app M := by
  have hcoc : (ModuleCat.extendScalars.{u, u, u} χ).map
          ((ModuleCat.extendScalarsComp.{u, u} ε ψ).inv.app M) ≫
        (ModuleCat.extendScalarsComp.{u, u} (ψ.comp ε) χ).inv.app M =
      (ModuleCat.extendScalarsComp.{u, u} ψ χ).inv.app
          ((ModuleCat.extendScalars.{u, u, u} ε).obj M) ≫
        (ModuleCat.extendScalarsComp.{u, u} ε (χ.comp ψ)).inv.app M := by
    have he : ModuleCat.extendScalarsComp.{u, u} (ψ.comp ε) χ ≪≫
          Functor.isoWhiskerRight (ModuleCat.extendScalarsComp.{u, u} ε ψ)
            (ModuleCat.extendScalars.{u, u, u} χ) =
        ModuleCat.extendScalarsComp.{u, u} ε (χ.comp ψ) ≪≫
          Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u} ε)
              (ModuleCat.extendScalarsComp.{u, u} ψ χ) ≪≫
            (Functor.associator _ _ _).symm :=
      Iso.ext (ModuleCat.extendScalars_assoc.{u, u} ε ψ χ)
    simpa using congrArg (fun e ↦ e.inv.app M) he
  simp only [extendScalarsRestrictIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [hcoc, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (ModuleCat.extendScalarsComp.{u, u} ψ χ).inv.naturality
    ((extendScalarsIsoRestrictScalars ε ε' h₁ h₂).hom.app M)

/-- Derived restriction of scalars along `ε'` factored through the localization functor, with its
source and target written out. -/
def restrictFactorsApp (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategoryFactors.hom.app P

/-- `derivedExtensionScalarsRestrictIso` at an object, with its source and target written
out. -/
def restrictIsoApp (ψ : R₂ →+* R') (X : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj
        ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.obj X) ⟶
      (totalDerivedExtensionScalars.{u, u, u} (ψ.comp ε)).functor.obj X :=
  (derivedExtensionScalarsRestrictIso ε ε' h₁ h₂ ψ).hom.app X

/-- The degreewise comparison `extendScalarsRestrictIso` at a cochain complex, with its source
and target written out. -/
def extendScalarsRestrictComplexApp (ψ : R₂ →+* R')
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶
      ((ModuleCat.extendScalars.{u, u, u} (ψ.comp ε)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  (NatTrans.mapHomologicalComplex (extendScalarsRestrictIso ε ε' h₁ h₂ ψ).hom
    (ComplexShape.up ℤ)).app P

/-- **The characterizing equation of `derivedExtensionScalarsRestrictIso`, at the wrappers.** -/
theorem restrictIsoApp_comparisonApp (ψ : R₂ →+* R')
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    restrictIsoApp ε ε' h₁ h₂ ψ (DerivedCategory.Q.obj P) ≫ comparisonApp (ψ.comp ε) P =
      (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map (restrictFactorsApp ε' P) ≫
        comparisonApp ψ
            (((ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (extendScalarsRestrictComplexApp ε ε' h₁ h₂ ψ P) :=
  derivedExtensionScalarsRestrictIso_hom_app_Q_comp_comparison ε ε' h₁ h₂ ψ P

/-- **The coherence on cochain complexes.**  The degreewise coherence read on complexes. -/
theorem extendScalarsRestrictComplexApp_comp_extendScalarsCompInvApp (ψ : R₂ →+* R')
    (χ : R' →+* R'') (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extendScalarsRestrictComplexApp ε ε' h₁ h₂ ψ P) ≫
        extendScalarsCompInvApp (ψ.comp ε) χ P =
      extendScalarsCompInvApp ψ χ
          (((ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        extendScalarsRestrictComplexApp ε ε' h₁ h₂ (χ.comp ψ) P := by
  ext i : 1
  exact extendScalarsRestrictIso_hom_app_comp_extendScalarsComp_inv_app ε ε' h₁ h₂ ψ χ (P.X i)

/-- **The coherence between the two presentations of derived extension of scalars along
`χ ∘ ψ ∘ ε`.**  Absorbing the isomorphism `ε` into `ψ` and then merging with `χ` agrees with
merging `ψ` with `χ` and then absorbing `ε`.

This is the coherence the local identity of Stacks 0E23 reduces to.  It carries no transport:
composition of ring homomorphisms is associative definitionally, so the two sides have the same
target. -/
theorem derivedExtensionScalarsRestrictIso_comp_compIso (ψ : R₂ →+* R') (χ : R' →+* R'')
    (X : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalars.{u, u, u} χ).functor.map
          ((derivedExtensionScalarsRestrictIso ε ε' h₁ h₂ ψ).hom.app X) ≫
        (derivedExtensionScalarsCompIso (ψ.comp ε) χ).hom.app X =
      (derivedExtensionScalarsCompIso ψ χ).hom.app
          ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.obj X) ≫
        (derivedExtensionScalarsRestrictIso ε ε' h₁ h₂ (χ.comp ψ)).hom.app X := by
  let A : ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor) ⋙
      (totalDerivedExtensionScalars.{u, u, u} χ).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} (χ.comp (ψ.comp ε))).functor :=
    Functor.whiskerRight (derivedExtensionScalarsRestrictIso ε ε' h₁ h₂ ψ).hom
        (totalDerivedExtensionScalars.{u, u, u} χ).functor ≫
      (derivedExtensionScalarsCompIso (ψ.comp ε) χ).hom
  let B : ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor) ⋙
      (totalDerivedExtensionScalars.{u, u, u} χ).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} (χ.comp (ψ.comp ε))).functor :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory
          (derivedExtensionScalarsCompIso ψ χ).hom ≫
        (derivedExtensionScalarsRestrictIso ε ε' h₁ h₂ (χ.comp ψ)).hom
  have key := totalDerivedExtensionScalars_hom_ext_app (χ.comp (ψ.comp ε)) A B (fun P => by
    dsimp [A, B]
    simp only [Category.id_comp, Category.assoc]
    show (totalDerivedExtensionScalars.{u, u, u} χ).functor.map
            (restrictIsoApp ε ε' h₁ h₂ ψ (DerivedCategory.Q.obj P)) ≫
          compIsoApp (ψ.comp ε) χ (DerivedCategory.Q.obj P) ≫
            comparisonApp (χ.comp (ψ.comp ε)) P =
        compIsoApp ψ χ
            ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.obj
              (DerivedCategory.Q.obj P)) ≫
          restrictIsoApp ε ε' h₁ h₂ (χ.comp ψ) (DerivedCategory.Q.obj P) ≫
            comparisonApp (χ.comp (ψ.comp ε)) P
    have eR : restrictIsoApp ε ε' h₁ h₂ (χ.comp ψ) (DerivedCategory.Q.obj P) ≫
          comparisonApp (χ.comp (ψ.comp ε)) P = _ :=
      restrictIsoApp_comparisonApp ε ε' h₁ h₂ (χ.comp ψ) P
    rw [compIsoApp_comparisonApp (ψ.comp ε) χ P, ← Functor.map_comp_assoc,
      restrictIsoApp_comparisonApp ε ε' h₁ h₂ ψ P, eR,
      ← reassoc_of% compIsoApp_naturality ψ χ (restrictFactorsApp ε' P),
      reassoc_of% compIsoApp_comparisonApp ψ χ
        (((ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% comparisonApp_naturality χ (extendScalarsRestrictComplexApp ε ε' h₁ h₂ ψ P),
      ← Functor.map_comp,
      extendScalarsRestrictComplexApp_comp_extendScalarsCompInvApp ε ε' h₁ h₂ ψ χ P,
      Functor.map_comp]) X
  simpa [A, B] using key

end Coherence

/-! ### The identity case

The consumer instantiates `derivedExtensionScalarsRestrictIso` at the germ comparison of a point of
a scheme with itself, which is a ring homomorphism equal to the identity.  There the comparison has
to be the collapse `StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso` of derived restriction
of scalars, followed by the transport from `ψ` to `ψ ∘ σ`: that is `restrictIsoApp_of_eq_id`, and
it is what lets a chase cancel the comparison against the transport of the point.

The proof is uniqueness of the total left derived functor.  Both sides are natural transformations
out of `(restrictScalars σ)^D ⋙ T_ψ`, which is a total left derived functor of degreewise extension
of scalars along `ψ ∘ σ` by
`StacksDraft.DerivedRingIso.isLeftDerivedFunctor_restrictCompComparison`, so
`CategoryTheory.Functor.leftDerived_ext` reduces the equality to an equality at the image of a
cochain complex, and there the characterizing equations of the two sides reduce it to the
degreewise identity case
`StacksDraft.DerivedRingIso.extendScalarsRestrictIso_hom_app_of_eq_id`. -/

section Identity

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- **The comparison with degreewise extension of scalars, transported along an equation of ring
homomorphisms, at the wrappers.**  This is
`StacksDraft.DerivedExtensionScalarsComp.comparison_app_comp_Q_map_eqToHom` read backwards and at
`comparisonApp`, which is the spelling the chase below is in. -/
theorem comparisonApp_eqToHom (φ χ : R →+* R') (h : φ = χ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    eqToHom (congrArg (fun ρ =>
          (totalDerivedExtensionScalars.{u, u, u} ρ).functor.obj
            (DerivedCategory.Q.obj P)) h) ≫ comparisonApp χ P =
      comparisonApp φ P ≫ DerivedCategory.Q.map (eqToHom (congrArg (fun ρ =>
        ((ModuleCat.extendScalars.{u, u, u} ρ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) h)) :=
  (comparison_app_comp_Q_map_eqToHom φ χ h P).symm

/-- **The identity case on cochain complexes.**  The degreewise identity case
`StacksDraft.DerivedRingIso.extendScalarsRestrictIso_hom_app_of_eq_id`, read on complexes. -/
theorem extendScalarsRestrictComplexApp_of_eq_id (σ : R →+* R) (hσ : σ = RingHom.id R)
    (k₁ : ∀ x, σ (σ x) = x) (k₂ : ∀ y, σ (σ y) = y) (ψ : R →+* R')
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    extendScalarsRestrictComplexApp σ σ k₁ k₂ ψ P =
      ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (restrictScalarsIdComplexApp.{u} σ hσ P) ≫
        eqToHom (congrArg (fun ρ =>
          ((ModuleCat.extendScalars.{u, u, u} ρ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          ((congrArg ψ.comp hσ).trans (RingHom.comp_id ψ)).symm) := by
  subst hσ
  ext i
  simp [extendScalarsRestrictComplexApp, restrictScalarsIdComplexApp,
    restrictScalarsIdComplexIso, extendScalarsRestrictIso_hom_app_of_eq_id]

/-- **The identity case of `derivedExtensionScalarsRestrictIso`.**  For `σ` a ring homomorphism
equal to the identity, absorbing `σ` into `ψ` is total derived extension of scalars along `ψ`
applied to the collapse `restrictScalarsIdDerivedIso` of derived restriction of scalars, followed
by the transport from `ψ` to `ψ ∘ σ`.

This is one of the two identity cases Stacks 0E23 waits on: the other is
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkFunctorCongr_self`, and the two cancel
because both are stated at `restrictScalarsIdDerivedIso`. -/
theorem restrictIsoApp_of_eq_id (σ : R →+* R) (hσ : σ = RingHom.id R)
    (k₁ : ∀ x, σ (σ x) = x) (k₂ : ∀ y, σ (σ y) = y) (ψ : R →+* R')
    (X : DerivedCategory (ModuleCat.{u} R)) :
    restrictIsoApp σ σ k₁ k₂ ψ X =
      (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
          ((restrictScalarsIdDerivedIso.{u} σ hσ).hom.app X) ≫
        eqToHom (congrArg (fun ρ =>
            (totalDerivedExtensionScalars.{u, u, u} ρ).functor.obj X)
          ((congrArg ψ.comp hσ).trans (RingHom.comp_id ψ)).symm) := by
  let A : (ModuleCat.restrictScalars.{u, u, u} σ).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} (ψ.comp σ)).functor :=
    (derivedExtensionScalarsRestrictIso σ σ k₁ k₂ ψ).hom
  let B : (ModuleCat.restrictScalars.{u, u, u} σ).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} (ψ.comp σ)).functor :=
    Functor.whiskerRight (restrictScalarsIdDerivedIso.{u} σ hσ).hom
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor ≫
      (Functor.leftUnitor _).hom ≫
        eqToHom (congrArg (fun ρ => (totalDerivedExtensionScalars.{u, u, u} ρ).functor)
          ((congrArg ψ.comp hσ).trans (RingHom.comp_id ψ)).symm)
  have key := totalDerivedExtensionScalars_hom_ext_app (ψ.comp σ) A B (fun P => by
    dsimp [A, B]
    simp only [Category.id_comp, Category.assoc, eqToHom_app]
    show restrictIsoApp σ σ k₁ k₂ ψ (DerivedCategory.Q.obj P) ≫
          comparisonApp (ψ.comp σ) P =
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((restrictScalarsIdDerivedIso.{u} σ hσ).hom.app (DerivedCategory.Q.obj P)) ≫
          eqToHom (congrArg (fun ρ =>
              (totalDerivedExtensionScalars.{u, u, u} ρ).functor.obj
                (DerivedCategory.Q.obj P))
            ((congrArg ψ.comp hσ).trans (RingHom.comp_id ψ)).symm) ≫
            comparisonApp (ψ.comp σ) P
    rw [restrictIsoApp_comparisonApp σ σ k₁ k₂ ψ P,
      comparisonApp_eqToHom ψ (ψ.comp σ)
        ((congrArg ψ.comp hσ).trans (RingHom.comp_id ψ)).symm P,
      restrictScalarsIdDerivedIso_hom_app_Q σ hσ P, Functor.map_comp, Category.assoc,
      reassoc_of% comparisonApp_naturality ψ (restrictScalarsIdComplexApp.{u} σ hσ P),
      ← Functor.map_comp, ← extendScalarsRestrictComplexApp_of_eq_id σ hσ k₁ k₂ ψ P,
      restrictFactorsApp]) X
  simpa [A, B, restrictIsoApp] using key

/-- `restrictIsoApp_of_eq_id` with the comparison spelled as the component of the isomorphism,
which is the form the geometric consumer meets. -/
theorem derivedExtensionScalarsRestrictIso_hom_app_of_eq_id (σ : R →+* R)
    (hσ : σ = RingHom.id R) (k₁ : ∀ x, σ (σ x) = x) (k₂ : ∀ y, σ (σ y) = y) (ψ : R →+* R')
    (X : DerivedCategory (ModuleCat.{u} R)) :
    (derivedExtensionScalarsRestrictIso σ σ k₁ k₂ ψ).hom.app X =
      (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
          ((restrictScalarsIdDerivedIso.{u} σ hσ).hom.app X) ≫
        eqToHom (congrArg (fun ρ =>
            (totalDerivedExtensionScalars.{u, u, u} ρ).functor.obj X)
          ((congrArg ψ.comp hσ).trans (RingHom.comp_id ψ)).symm) :=
  restrictIsoApp_of_eq_id σ hσ k₁ k₂ ψ X

end Identity

end StacksDraft.DerivedRingIso

end

end

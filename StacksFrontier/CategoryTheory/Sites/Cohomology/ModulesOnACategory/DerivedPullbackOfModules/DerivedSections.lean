module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PresheafOfModulesProjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackQuasiCoherentBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit

/-!
# The derived pullback of modules on a chaotic site and its derived sections

Let `C` and `C'` be categories viewed as sites with the chaotic topology, let `O : Cᵒᵖ ⥤ RingCat`
and `O' : C'ᵒᵖ ⥤ RingCat` be sheaves of rings on them, and let a functor `F : C' ⥤ C` together
with a map of sheaves of rings `φ : F⁻¹O ⟶ O'` be the datum of a morphism of ringed topoi
`g : (Sh(C'), O') → (Sh(C), O)`. Its pullback of modules is the inverse image of presheaves of
modules followed by the objectwise extension of scalars along `φ`, and the derived pullback
`Lg^*` is obtained by deriving the two factors separately.

The inverse image of presheaves of modules is exact, so it descends to the derived categories
with no derived correction, and its derived sections over an object `U'` of `C'` are the derived
sections of the argument over `F U'`.

Extension of scalars is only right exact, and it is the factor that has to be derived. Presheaves
of modules have enough projectives and exact colimits indexed by `ℕ` with the site, ring and
module universes independent, so Stacks 0794 at the class of projective objects produces the
total left derived functor `D(F⁻¹O) ⥤ D(O')`; restriction of scalars along `φ` is exact, so
Stacks 09T5 makes the derived extension of scalars left adjoint to the functor it induces on
derived categories. The composite of the two factors is the derived pullback `Lg^*`.

Its derived sections are then computed, which is Stacks 0D6D for these sites: over an object `U'`
of `C'` the derived sections of `Lg^*K` are the derived base change along the structure map
`O(F U') ⟶ O'(U')` of the derived sections of `K` over `F U'`. Only the derived extension of
scalars contributes, and for that factor both sides of the computation are *left adjoints*: the
right adjoint of taking sections over `U'` is the coevaluation `M ↦ ∏_{V' ⟶ U'} M`, which is
exact, so it descends to derived categories and the derived sections over `U'` are a left adjoint
too. The two right adjoints agree because restriction of scalars along `φ` commutes with the
coevaluations — the conjugate of the fact that extension of scalars of presheaves of modules is
objectwise — so the two left adjoints agree by uniqueness of left adjoints.

## Main definitions

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dInverseImage`: the derived inverse
  image `D(O) ⥤ D(F⁻¹O)`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dExtendScalars` and
  `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dExtendScalarsCounit`: the total left
  derived functor of extension of scalars along `φ`, and its comparison transformation.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.derivedPullback`: the derived
  pullback `Lg^* : D(O) ⥤ D(O')`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.coevaluation` and
  `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dCoevaluation`: the right adjoint
  `Mod(R(U')) ⥤ Mod(R)` of taking sections over `U'`, and the functor it induces on derived
  categories.

## Main results

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dInverseImageCompRGamma`: the derived
  sections of the derived inverse image over `U'` are the derived sections over `F U'`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.restrictScalars_preservesHomology`:
  restriction of scalars along `φ` is exact.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dExtendScalars_isLeftDerivedFunctor`:
  `dExtendScalars` is a left derived functor of extension of scalars, for the comparison
  transformation `dExtendScalarsCounit`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dExtendScalarsAdjunction`: the
  derived extension of scalars is left adjoint to the derived restriction of scalars.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.coevaluationAdjunction` and
  `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dCoevaluationAdjunction`: taking
  sections over `U'` is left adjoint to the coevaluation, and the derived sections over `U'` are
  left adjoint to the derived coevaluation. The coevaluation is exact:
  `coevaluation_preservesHomology`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.coevaluationRestrictScalarsSquare`:
  restriction of scalars along `φ` commutes with the coevaluations.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dExtendScalarsCompRGamma`: the
  derived sections over `U'` of the derived extension of scalars are the derived base change
  along the structure map at `U'` of the derived sections over `U'`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.derivedPullbackCompRGamma`: Stacks
  0D6D, the derived sections of `Lg^*K` over `U'` are the derived base change along the structure
  map of the derived sections of `K` over `F U'`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.restrictionMap_dInverseImage`: the
  computation `dInverseImageCompRGamma` of the derived sections of the derived inverse image is
  compatible with the canonical derived restriction maps.

## Implementation notes

The chosen derived category of presheaves of modules is
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory`, whose module
universe is `max u v r w` with `w` free. In a statement where no occurrence of `DMod` pins that
free universe, instance search cannot solve `max ?w u' v' r =?= max u v u' v' r` and stalls; the
instance is therefore supplied with its universes written out, and the same holds for the enough
projectives and exact `ℕ`-colimits instances of `PresheafOfModulesProjectives`. This is also why
`dCoevaluation` is introduced as a definition whose stated codomain is `DMod`: nothing in
`coevaluation.mapDerivedCategory` pins the module universe of the derived category it lands in.

The coevaluation is *not* taken as the abstract right adjoint of taking sections. The sections
computation is obtained by conjugating a commuting square of right adjoints, and the square has
to be known for the coevaluation itself, not merely up to an unspecified isomorphism; the formula
`(coev M)(V') = ∏_{a : V' ⟶ U'} M`, with the index `a` acting through `R(a)`, is what makes the
square the naturality square of `φ`. Exactness of the coevaluation is the only input where the
chaotic topology and the shape of the formula matter: products of modules are exact.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.DerivedCategoryComparisons (mapDerivedCategoryCompIso
  mapDerivedCategoryCompIso_inv_app_Q mapDerivedCategoryIsoOfNatIso)

universe r v u v' u' w

namespace Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C' ⥤ C)
  (O : Cᵒᵖ ⥤ RingCat.{r}) (O' : C'ᵒᵖ ⥤ RingCat.{r}) (φ : F.op ⋙ O ⟶ O')
  (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x)
  (hO' : ∀ (U' : C'ᵒᵖ) (x y : O'.obj U'), x * y = y * x)

attribute [local instance] HasDerivedCategory.standard

/-! ### Descents of exact functors on the image of a cochain complex -/

section Descent

universe t₁ t₂

variable {A₁ : Type*} [Category A₁] [Abelian A₁] [HasDerivedCategory.{t₁} A₁]
  {A₂ : Type*} [Category A₂] [Abelian A₂] [HasDerivedCategory.{t₂} A₂]

/-- The isomorphism of descents induced by an isomorphism of exact functors, evaluated at the
image of a cochain complex: it is the induced isomorphism of complexes, conjugated by the
canonical factorizations of the two descents. -/
private theorem mapDerivedCategoryIsoOfNatIso_hom_app_Q (G₁ G₂ : A₁ ⥤ A₂)
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂] (e : G₁ ≅ G₂)
    (P : CochainComplex A₁ ℤ) :
    (mapDerivedCategoryIsoOfNatIso G₁ G₂ e).hom.app (DerivedCategory.Q.obj P) =
      G₁.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) ≫
        G₂.mapDerivedCategoryFactors.inv.app P :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q G₁ G₂ e P

universe t₃

variable {A₃ : Type*} [Category A₃] [Abelian A₃] [HasDerivedCategory.{t₃} A₃]

/-- The inverse of the isomorphism of descents induced by an isomorphism of exact functors,
evaluated at the image of a cochain complex: it is the inverse of the induced isomorphism of
complexes, conjugated by the canonical factorizations of the two descents. -/
private theorem mapDerivedCategoryIsoOfNatIso_inv_app_Q (G₁ G₂ : A₁ ⥤ A₂)
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂] (e : G₁ ≅ G₂)
    (P : CochainComplex A₁ ℤ) :
    (mapDerivedCategoryIsoOfNatIso G₁ G₂ e).inv.app (DerivedCategory.Q.obj P) =
      G₂.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).inv.app P) ≫
        G₁.mapDerivedCategoryFactors.inv.app P :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_inv_app_Q G₁ G₂ e P

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- The comparison of the descent of a composite with the composite of the descents, evaluated
at the image of a cochain complex: it is the canonical factorization of the descent of the
composite, against the canonical factorizations of the two factors. -/
private theorem mapDerivedCategoryCompIso_hom_app_Q (G₁ : A₁ ⥤ A₂) (G₂ : A₂ ⥤ A₃)
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (P : CochainComplex A₁ ℤ) :
    (mapDerivedCategoryCompIso G₁ G₂).hom.app (DerivedCategory.Q.obj P) =
      (G₁ ⋙ G₂).mapDerivedCategoryFactors.hom.app P ≫
        G₂.mapDerivedCategoryFactors.inv.app
          ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.inv.app P) :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q G₁ G₂ P

/-- The canonical factorization of the descent of a composite, followed by the composition
comparison, is the pair of canonical factorizations of the two factors. -/
private theorem factors_inv_comp_compIso_hom_app_Q (G₁ : A₁ ⥤ A₂) (G₂ : A₂ ⥤ A₃)
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (P : CochainComplex A₁ ℤ) :
    (G₁ ⋙ G₂).mapDerivedCategoryFactors.inv.app P ≫
        (mapDerivedCategoryCompIso G₁ G₂).hom.app (DerivedCategory.Q.obj P) =
      G₂.mapDerivedCategoryFactors.inv.app
          ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.inv.app P) := by
  rw [mapDerivedCategoryCompIso_hom_app_Q]
  simp
end Descent

section Bookkeeping

universe t₄ t₅ t₆ t₇ s₄ s₅ s₆ s₇

variable {E₁ : Type t₄} [Category.{s₄} E₁] {E₂ : Type t₅} [Category.{s₅} E₂]
  {E₃ : Type t₆} [Category.{s₆} E₃] {E₄ : Type t₇} [Category.{s₇} E₄]

/-- Cancelling a pair of mutually inverse morphisms and an identity inside a composite. -/
private theorem cancel_mid {X Y Y' Z W : E₂} (a : X ⟶ Y) (b : Y ⟶ Y') (i : Y' ⟶ Z) (j : Z ⟶ Y')
    (hij : i ≫ j = 𝟙 Y') (e : Y' ⟶ Y') (he : e = 𝟙 Y') (f : Y' ⟶ W) :
    (a ≫ b ≫ i) ≫ j ≫ e ≫ f = a ≫ b ≫ f := by
  rw [he, Category.id_comp, Category.assoc, Category.assoc, ← Category.assoc i j, hij,
    Category.id_comp]

/-- Composing two compatibilities `h₁` and `h₃` of comparison morphisms with restriction maps
across a naturality square `h₂`: the composite with identities inserted commutes. -/
private theorem comp_map_eq_of_mate {R : E₁ ⥤ E₂} {T : E₃ ⥤ E₂} {S : E₄ ⥤ E₃}
    {x₀ : E₂} {y₀ y₁ y₂ : E₁} {d₀ d₁ : E₄} {e₀ e₁ : E₃}
    {L : x₀ ⟶ R.obj y₀} {fU : y₀ ⟶ y₂} {gU : y₂ ⟶ y₁} {fV : x₀ ⟶ T.obj e₀}
    {c : d₀ ⟶ d₁} {c' : e₀ ⟶ e₁} {ρ : e₀ ⟶ S.obj d₀} {ρ' : e₁ ⟶ S.obj d₁}
    {γ₀ : T.obj (S.obj d₀) ⟶ R.obj y₂} {γ : T.obj (S.obj d₁) ⟶ R.obj y₁}
    (h₁ : L ≫ R.map fU = fV ≫ T.map ρ ≫ γ₀)
    (h₂ : T.map (S.map c) ≫ γ = γ₀ ≫ R.map gU)
    (h₃ : ρ ≫ S.map c = c' ≫ ρ') :
    L ≫ R.map (𝟙 y₀ ≫ fU ≫ 𝟙 y₂ ≫ gU) =
      (𝟙 x₀ ≫ fV ≫ 𝟙 (T.obj e₀) ≫ T.map c') ≫ T.map ρ' ≫ γ := by
  rw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp, Functor.map_comp,
    reassoc_of% h₁, Category.assoc, ← h₂, ← Functor.map_comp_assoc, h₃, Functor.map_comp]
  simp only [Category.assoc]

end Bookkeeping

/-! ### The derived inverse image -/

/-- **The derived inverse image `D(O) ⥤ D(F⁻¹O)`.** The inverse image of presheaves of modules is
exact, so this is its induced functor on derived categories. -/
noncomputable def dInverseImage : DMod.{max u' v'} O ⥤ DMod.{max u v} (F.op ⋙ O) :=
  (PresheafOfModules.pushforward₀.{max u v u' v' r} F O).mapDerivedCategory

/-- **The derived sections of the derived inverse image.** Over an object `U'` of `C'` they are
the derived sections of the argument over `F U'`, the inverse image leaving sections unchanged up
to reindexing along `F.op`. -/
noncomputable def dInverseImageCompRGamma (U' : C'ᵒᵖ) :
    dInverseImage.{r, v, u, v', u'} F O ⋙ RGamma.{max u v} (F.op ⋙ O) U' ≅
      RGamma.{max u' v'} O (F.op.obj U') :=
  (mapDerivedCategoryCompIso (PresheafOfModules.pushforward₀.{max u v u' v' r} F O)
    (PresheafOfModules.evaluation.{max u v u' v' r} (F.op ⋙ O) U')).symm ≪≫
  mapDerivedCategoryIsoOfNatIso _ _
    (eqToIso (pushforward₀_comp_evaluation.{r, v, u, v', u'} F O U'))

/-- The computation of the derived sections of the derived inverse image, evaluated at the image
of a cochain complex `P`: both descents are canonically factored, and the inverse image leaves the
sections of `P` unchanged. -/
private theorem dInverseImageCompRGamma_hom_app_Q (W' : C'ᵒᵖ)
    (P : CochainComplex (PresheafOfModules.{max u v u' v' r} O) ℤ) :
    (dInverseImageCompRGamma.{r, v, u, v', u'} F O W').hom.app (DerivedCategory.Q.obj P) =
      (RGamma.{max u v} (F.op ⋙ O) W').map
          ((PresheafOfModules.pushforward₀.{max u v u' v' r} F
            O).mapDerivedCategoryFactors.hom.app P) ≫
        (PresheafOfModules.evaluation.{max u v u' v' r} (F.op ⋙ O)
            W').mapDerivedCategoryFactors.hom.app
          (((PresheafOfModules.pushforward₀.{max u v u' v' r} F O).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (PresheafOfModules.evaluation.{max u v u' v' r} O
          (F.op.obj W')).mapDerivedCategoryFactors.inv.app P := by
  have h : (dInverseImageCompRGamma.{r, v, u, v', u'} F O W').hom.app
        (DerivedCategory.Q.obj P) =
      (mapDerivedCategoryCompIso (PresheafOfModules.pushforward₀.{max u v u' v' r} F O)
          (PresheafOfModules.evaluation.{max u v u' v' r} (F.op ⋙ O) W')).inv.app
        (DerivedCategory.Q.obj P) ≫
      (mapDerivedCategoryIsoOfNatIso
        (PresheafOfModules.pushforward₀.{max u v u' v' r} F O ⋙
          PresheafOfModules.evaluation.{max u v u' v' r} (F.op ⋙ O) W')
        (PresheafOfModules.evaluation.{max u v u' v' r} O (F.op.obj W'))
        (eqToIso (pushforward₀_comp_evaluation.{r, v, u, v', u'} F O W'))).hom.app
        (DerivedCategory.Q.obj P) := rfl
  rw [h, mapDerivedCategoryCompIso_inv_app_Q, mapDerivedCategoryIsoOfNatIso_hom_app_Q]
  refine cancel_mid _ _ _ _ ?_ _ ?_ _
  · exact Iso.inv_hom_id_app _ _
  · exact DerivedCategory.Q.map_id _

/-- The canonical derived restriction maps are compatible with the computation of the derived
sections of the derived inverse image, as natural transformations. -/
private theorem whiskerLeft_restrictionNatTrans {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    Functor.whiskerLeft (dInverseImage.{r, v, u, v', u'} F O)
          (restrictionNatTrans.{max u v} (F.op ⋙ O) a') ≫
        Functor.whiskerRight (dInverseImageCompRGamma.{r, v, u, v', u'} F O U').hom
          (DRestrict.{max u' v'} O (F.op.map a')) =
      (dInverseImageCompRGamma.{r, v, u, v', u'} F O V').hom ≫
        restrictionNatTrans.{max u' v'} O (F.op.map a') := by
  -- The module universe of `D(O)` is not pinned by the statement of `natTrans_ext`, so the
  -- derived category of presheaves of `O`-modules is named with its universes written out.
  let _ : HasDerivedCategory.{max u v u' v' r} (PresheafOfModules.{max u v u' v' r} O) :=
    derivedPresheafCategory.{max u' v', u, v, r} O
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (PresheafOfModules.{max u v u' v' r} O) (ComplexShape.up ℤ))
    fun P ↦ ?_
  have hn := (restrictionNatTrans.{max u v} (F.op ⋙ O) a').naturality
    ((PresheafOfModules.pushforward₀.{max u v u' v' r} F O).mapDerivedCategoryFactors.hom.app P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map] at hn ⊢
  rw [restrictionNatTrans_app, restrictionNatTrans_app] at hn
  simp only [Functor.comp_obj] at hn
  rw [restrictionMap_Q] at hn
  rw [restrictionNatTrans_app, restrictionNatTrans_app, dInverseImageCompRGamma_hom_app_Q,
    dInverseImageCompRGamma_hom_app_Q]
  exact comp_map_eq_comp_of_naturality hn (restrictionMap_Q O (F.op.map a') P)
    (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)

/-- **The computation of the derived sections of the derived inverse image is compatible with the
canonical derived restriction maps.** Over a morphism `a'` of `C'ᵒᵖ` it carries the restriction map
of `F⁻¹K` along `a'` to the restriction map of `K` along `F a'`. -/
theorem restrictionMap_dInverseImage {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') (K : DMod.{max u' v'} O) :
    restrictionMap.{max u v} (F.op ⋙ O) a' ((dInverseImage.{r, v, u, v', u'} F O).obj K) ≫
        (DRestrict.{max u' v'} O (F.op.map a')).map
          ((dInverseImageCompRGamma.{r, v, u, v', u'} F O U').hom.app K) =
      (dInverseImageCompRGamma.{r, v, u, v', u'} F O V').hom.app K ≫
        restrictionMap.{max u' v'} O (F.op.map a') K :=
  congr_app (whiskerLeft_restrictionNatTrans F O a') K

/-! ### Restriction of scalars along the structure map is exact -/

/-- **Restriction of scalars of presheaves of modules is exact**: it does not change the
underlying presheaf of abelian groups, and exactness of presheaves of modules is tested there. -/
instance restrictScalars_preservesHomology :
    (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun _ hS ↦
    (PresheafOfModules.toPresheaf (F.op ⋙ O)).reflects_exact_of_faithful _
      (hS.map (PresheafOfModules.toPresheaf O'))

/-- Restriction of scalars of presheaves of modules is left exact. -/
instance restrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafOfModules.restrictScalars.{max u v u' v' r} φ) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- Restriction of scalars of presheaves of modules is right exact. -/
instance restrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (PresheafOfModules.restrictScalars.{max u v u' v' r} φ) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-! ### The derived extension of scalars -/

/-- **Extension of scalars along `φ` has a total left derived functor, defined at every object.**
This is Stacks 0794 at the class of projective objects: extension of scalars is right exact,
being a left adjoint, and presheaves of modules have enough projectives and exact colimits
indexed by `ℕ`. -/
theorem extendScalars_hasPointwiseLeftDerivedFunctor :
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : _ ⥤ DMod.{max u v} O')).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (PresheafOfModules.{max u v u' v' r} (F.op ⋙ O)) (ComplexShape.up ℤ)) :=
  let : HasDerivedCategory.{max u v u' v' r}
      (PresheafOfModules.{max u v u' v' r} (F.op ⋙ O)) :=
    derivedPresheafCategory.{max u v, u', v', r} (F.op ⋙ O)
  let : HasDerivedCategory.{max u v u' v' r} (PresheafOfModules.{max u v u' v' r} O') :=
    derivedPresheafCategory.{max u v, u', v', r} O'
  let := enoughProjectives.{r, max u v, v', u'} (F.op ⋙ O)
  let := hasExactColimitsOfShapeNat.{r, max u v, v', u'} (F.op ⋙ O)
  let := hasExactColimitsOfShapeNat.{r, max u v, v', u'} O'
  Stacks.CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives _

/-- **The total left derived functor `D(F⁻¹O) ⥤ D(O')` of extension of scalars along `φ`.**
Extension of scalars is right exact but not exact, so this is a genuine derived functor. -/
noncomputable def dExtendScalars : DMod.{max u v} (F.op ⋙ O) ⥤ DMod.{max u v} O' :=
  letI := extendScalars_hasPointwiseLeftDerivedFunctor F O O' φ
  ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (PresheafOfModules.{max u v u' v' r} (F.op ⋙ O))
      (ComplexShape.up ℤ))

/-- The comparison transformation exhibiting `dExtendScalars` as a left derived functor of
extension of scalars along `φ`. -/
noncomputable def dExtendScalarsCounit :
    DerivedCategory.Qh ⋙ dExtendScalars F O O' φ ⟶
      (Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ (DerivedCategory.Qh : _ ⥤ DMod.{max u v} O') :=
  letI := extendScalars_hasPointwiseLeftDerivedFunctor F O O' φ
  ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (PresheafOfModules.{max u v u' v' r} (F.op ⋙ O))
      (ComplexShape.up ℤ))

/-- **The comparison transformation does exhibit `dExtendScalars` as a left derived functor** of
extension of scalars along `φ`. -/
theorem dExtendScalars_isLeftDerivedFunctor :
    (dExtendScalars F O O' φ).IsLeftDerivedFunctor (dExtendScalarsCounit F O O' φ)
      (HomotopyCategory.quasiIso (PresheafOfModules.{max u v u' v' r} (F.op ⋙ O))
        (ComplexShape.up ℤ)) := by
  have := extendScalars_hasPointwiseLeftDerivedFunctor F O O' φ
  dsimp only [dExtendScalars, dExtendScalarsCounit]
  infer_instance

/-- **Stacks 09T5 for extension of scalars: the derived extension of scalars along `φ` is left
adjoint to the derived restriction of scalars.** Restriction of scalars is exact, so the right
adjoint needs no derived correction. -/
noncomputable def dExtendScalarsAdjunction :
    dExtendScalars F O O' φ ⊣
      (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory :=
  letI := enoughProjectives.{r, max u v, v', u'} (F.op ⋙ O)
  letI := hasExactColimitsOfShapeNat.{r, max u v, v', u'} (F.op ⋙ O)
  letI := hasExactColimitsOfShapeNat.{r, max u v, v', u'} O'
  letI := extendScalars_hasPointwiseLeftDerivedFunctor F O O' φ
  letI := dExtendScalars_isLeftDerivedFunctor F O O' φ
  Stacks.CategoryHomology.derivedAdjunctionOfEnoughProjectives
    (Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{max u v u' v'} φ)
    (dExtendScalars F O O' φ) (dExtendScalarsCounit F O O' φ)

/-! ### The right adjoint of taking sections -/

section Coevaluation

variable (R : C'ᵒᵖ ⥤ RingCat.{r}) (U' : C'ᵒᵖ)

/-- **The coevaluation of a module `M` over `R(U')`, on sections over `V'`**: the families of
elements of `M` indexed by the morphisms `a : V' ⟶ U'`, the index `a` acting through restriction
of scalars along `R(a)`. -/
noncomputable def coevaluationObj (M : ModuleCat.{max u' v' r w} (R.obj U')) (V' : C'ᵒᵖ) :
    ModuleCat.{max u' v' r w} (R.obj V') :=
  ModuleCat.of (R.obj V') ((a : V' ⟶ U') → ((ModuleCat.restrictScalars (R.map a).hom).obj M))

/-- The restriction map of the coevaluation along `g : V' ⟶ W'`: reindexing a family along
`g ≫ -`. It is semilinear over `R(g)` because the index `g ≫ c` acts through `R(g ≫ c)`, which
is `R(c)` after `R(g)`. -/
noncomputable def coevaluationRestrict (M : ModuleCat.{max u' v' r w} (R.obj U'))
    {V' W' : C'ᵒᵖ} (g : V' ⟶ W') :
    coevaluationObj.{r, v', u', w} R U' M V' →ₛₗ[(R.map g).hom]
      coevaluationObj.{r, v', u', w} R U' M W' where
  toFun x := fun c => x (g ≫ c)
  map_add' _ _ := rfl
  map_smul' s x := by
    funext c
    change (R.map (g ≫ c)).hom s • x (g ≫ c) = (R.map c).hom ((R.map g).hom s) • x (g ≫ c)
    rw [R.map_comp]
    rfl

/-- **The coevaluation of a module over `R(U')` as a presheaf of `R`-modules.** Its sections over
`V'` are the families indexed by the morphisms `V' ⟶ U'`, restricted by reindexing. -/
noncomputable def coevaluationPresheaf (M : ModuleCat.{max u' v' r w} (R.obj U')) :
    PresheafOfModules.{max u' v' r w} R where
  obj V' := coevaluationObj.{r, v', u', w} R U' M V'
  map g :=
    (ModuleCat.semilinearMapAddEquiv (R.map g).hom _ _)
      (coevaluationRestrict.{r, v', u', w} R U' M g)
  map_id V' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext c
    change x (𝟙 V' ≫ c) = x c
    rw [Category.id_comp]
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext c
    change x ((g ≫ h) ≫ c) = x (g ≫ h ≫ c)
    rw [Category.assoc]

/-- **The coevaluation functor `Mod(R(U')) ⥤ Mod(R)`**, right adjoint to taking sections over
`U'`. It is the right Kan extension of a module along the inclusion of the object `U'`. -/
noncomputable def coevaluation :
    ModuleCat.{max u' v' r w} (R.obj U') ⥤ PresheafOfModules.{max u' v' r w} R where
  obj M := coevaluationPresheaf.{r, v', u', w} R U' M
  map {_ _} ψ :=
    { app := fun _ => ModuleCat.ofHom
        { toFun := fun x c => ψ (x c)
          map_add' := fun x y => by funext c; exact ψ.hom.map_add (x c) (y c)
          map_smul' := fun s x => by
            funext c
            exact ψ.hom.map_smul ((R.map c).hom s) (x c) }
      naturality := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The evaluation at the identity of `U'`, from the sections of a coevaluation over `U'` to the
module it is the coevaluation of. It is the counit of `coevaluationAdjunction`. -/
noncomputable def coevaluationProj (M : ModuleCat.{max u' v' r w} (R.obj U')) :
    ((coevaluation.{r, v', u', w} R U').obj M).obj U' ⟶ M :=
  ModuleCat.ofHom (LinearMap.proj (R := R.obj U') (𝟙 U')) ≫
    (ModuleCat.restrictScalarsId' (R.map (𝟙 U')).hom
      (congrArg RingCat.Hom.hom (R.map_id U'))).hom.app M

/-- The map to a coevaluation attached to a map of sections over `U'`: a section over `V'` is
sent to the family of the images of its restrictions. -/
noncomputable def coevaluationMk {N : PresheafOfModules.{max u' v' r w} R}
    {M : ModuleCat.{max u' v' r w} (R.obj U')} (g : N.obj U' ⟶ M) :
    N ⟶ (coevaluation.{r, v', u', w} R U').obj M where
  app V' := ModuleCat.ofHom
    (LinearMap.pi (fun c : V' ⟶ U' =>
      (N.map c ≫ (ModuleCat.restrictScalars (R.map c).hom).map g).hom))
  naturality {_ _} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro n
    funext c
    change g (N.map c (N.map h n)) = g (N.map (h ≫ c) n)
    rw [PresheafOfModules.map_comp_apply]

/-- **Maps into a coevaluation are maps of sections over `U'`.** A map `N ⟶ coev M` is
determined by what it does to sections over `U'`, every other component being forced by
naturality, and any map of sections over `U'` arises this way. -/
noncomputable def coevaluationHomEquiv (N : PresheafOfModules.{max u' v' r w} R)
    (M : ModuleCat.{max u' v' r w} (R.obj U')) :
    ((PresheafOfModules.evaluation.{max u' v' r w} R U').obj N ⟶ M) ≃
      (N ⟶ (coevaluation.{r, v', u', w} R U').obj M) where
  toFun g := coevaluationMk.{r, v', u', w} R U' g
  invFun f := f.app U' ≫ coevaluationProj.{r, v', u', w} R U' M
  left_inv g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro n
    change g (N.map (𝟙 U') n) = g n
    rw [PresheafOfModules.map_id]
    rfl
  right_inv f := by
    ext V' n
    funext c
    change (f.app U') (N.map c n) (𝟙 U') = f.app V' n c
    exact (congrFun (PresheafOfModules.naturality_apply f c n) (𝟙 U')).trans
      (congrArg (fun d => f.app V' n d) (Category.comp_id c))

/-- **Taking sections over `U'` is left adjoint to the coevaluation.** -/
noncomputable def coevaluationAdjunction :
    PresheafOfModules.evaluation.{max u' v' r w} R U' ⊣ coevaluation.{r, v', u', w} R U' :=
  Adjunction.mkOfHomEquiv
    { homEquiv := coevaluationHomEquiv.{r, v', u', w} R U'
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; rfl }

/-- The coevaluation is additive, being a product of copies of its argument. -/
instance coevaluation_additive : (coevaluation.{r, v', u', w} R U').Additive where
  map_add {_ _ _ _} := by
    apply PresheafOfModules.hom_ext
    intro V'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext c
    rfl

/-- **The coevaluation preserves epimorphisms**: an epimorphism of modules is surjective, so a
family of elements of the target lifts index by index. -/
instance coevaluation_preservesEpimorphisms :
    (coevaluation.{r, v', u', w} R U').PreservesEpimorphisms where
  preserves {_ _} f hf := by
    obtain ⟨s, hsr⟩ := ((ModuleCat.epi_iff_surjective _).mp hf).hasRightInverse
    exact PresheafOfModules.epi_of_surjective fun {_} y ↦
      ⟨fun c ↦ s (y c), funext fun c ↦ hsr (y c)⟩

/-- The coevaluation is left exact, being a right adjoint. -/
instance coevaluation_preservesFiniteLimits :
    PreservesFiniteLimits (coevaluation.{r, v', u', w} R U') :=
  letI := (coevaluationAdjunction.{r, v', u', w} R U').rightAdjoint_preservesLimits.{0, 0}
  PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _

/-- **The coevaluation is exact.** It preserves kernels, being a right adjoint, and
epimorphisms, products of modules being exact; that is exactness. -/
instance coevaluation_preservesHomology :
    (coevaluation.{r, v', u', w} R U').PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The coevaluation is right exact. -/
instance coevaluation_preservesFiniteColimits :
    PreservesFiniteColimits (coevaluation.{r, v', u', w} R U') :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- **The derived coevaluation `D(R(U')) ⥤ D(R)`.** The coevaluation is exact, so this is its
induced functor on derived categories. -/
noncomputable def dCoevaluation :
    DerivedCategory (ModuleCat.{max u' v' r w} (R.obj U')) ⥤ DMod.{w} R :=
  (coevaluation.{r, v', u', w} R U').mapDerivedCategory

/-- **The derived sections over `U'` are left adjoint to the derived coevaluation**, by descent
of `coevaluationAdjunction` to the localizations at the quasi-isomorphisms. -/
noncomputable def dCoevaluationAdjunction :
    RGamma.{w} R U' ⊣ dCoevaluation.{r, v', u', w} R U' := by
  letI : CatCommSq
      ((PresheafOfModules.evaluation.{max u' v' r w} R U').mapHomologicalComplex
        (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q (RGamma.{w} R U') :=
    ⟨(PresheafOfModules.evaluation.{max u' v' r w} R U').mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq ((coevaluation.{r, v', u', w} R U').mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (dCoevaluation.{r, v', u', w} R U') :=
    ⟨(coevaluation.{r, v', u', w} R U').mapDerivedCategoryFactors.symm⟩
  exact ((coevaluationAdjunction.{r, v', u', w} R U').mapHomologicalComplex
      (ComplexShape.up ℤ)).localization
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (PresheafOfModules.{max u' v' r w} R) (ComplexShape.up ℤ))
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u' v' r w} (R.obj U')) (ComplexShape.up ℤ)) _ _

end Coevaluation

/-! ### The derived pullback -/

/-- **The derived pullback `Lg^* : D(O) ⥤ D(O')`** along the morphism of ringed topoi on chaotic
sites given by `F` and `φ`: the exact derived inverse image followed by the derived extension of
scalars along the structure map. -/
noncomputable def derivedPullback : DMod.{max u' v'} O ⥤ DMod.{max u v} O' :=
  dInverseImage F O ⋙ dExtendScalars F O O' φ

/-! ### The derived sections of the derived pullback -/

/-- **The sections of extension of scalars along `φ`.** Over `U'` they are the extension of
scalars of the sections along the structure map at `U'`, extension of scalars of presheaves of
modules being objectwise. -/
theorem extendScalars_comp_evaluation (U' : C'ᵒᵖ) :
    Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ ⋙
        PresheafOfModules.evaluation.{max u v u' v' r} O' U' =
      PresheafOfModules.evaluation.{max u v u' v' r} (F.op ⋙ O) U' ⋙
        Stacks.NoncommChangeOfRings.extendScalars.{max u v u' v' r} (φ.app U').hom := rfl

/-- **Restriction of scalars along `φ` commutes with the coevaluations.** The two composites are
right adjoints of the two sides of `extendScalars_comp_evaluation`, so this is its conjugate; on
sections over `V'` it is the naturality square of `φ` at `V' ⟶ U'`. -/
noncomputable def coevaluationRestrictScalarsSquare (U' : C'ᵒᵖ) :
    coevaluation.{r, v', u', max u v} O' U' ⋙
        PresheafOfModules.restrictScalars.{max u v u' v' r} φ ≅
      ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom ⋙
        coevaluation.{r, v', u', max u v} (F.op ⋙ O) U' :=
  conjugateIsoEquiv
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{max u v u' v'} φ).comp
      (coevaluationAdjunction.{r, v', u', max u v} O' U'))
    ((coevaluationAdjunction.{r, v', u', max u v} (F.op ⋙ O) U').comp
      (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{max u v u' v'} (φ.app U').hom))
    (eqToIso (extendScalars_comp_evaluation F O O' φ U').symm)

/-- **Derived restriction of scalars along `φ` commutes with the derived coevaluations**, the
coevaluations and the two restrictions of scalars all being exact. -/
noncomputable def dCoevaluationRestrictScalarsSquare (U' : C'ᵒᵖ) :
    dCoevaluation.{r, v', u', max u v} O' U' ⋙
        (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory ≅
      dRestrictScalars.{r, max u v u' v' r} (φ.app U') ⋙
        dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) U' :=
  (mapDerivedCategoryCompIso _ _).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _ (coevaluationRestrictScalarsSquare F O O' φ U') ≪≫
    mapDerivedCategoryCompIso _ _

/-- The derived sections over `U'` of the derived extension of scalars are a left adjoint, being
the composite of the two left adjoints `dExtendScalarsAdjunction` and
`dCoevaluationAdjunction`. -/
noncomputable def dExtendScalarsSectionsAdjunction (U' : C'ᵒᵖ) :
    dExtendScalars F O O' φ ⋙ RGamma.{max u v} O' U' ⊣
      dCoevaluation.{r, v', u', max u v} O' U' ⋙
        (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory :=
  (dExtendScalarsAdjunction F O O' φ).comp (dCoevaluationAdjunction.{r, v', u', max u v} O' U')

/-- The derived base change along the structure map at `U'` of the derived sections over `U'` is
a left adjoint, being the composite of the two left adjoints `dCoevaluationAdjunction` and
`Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.dBaseChangeAdj`. -/
noncomputable def dBaseChangeSectionsAdjunction (U' : C'ᵒᵖ) :
    RGamma.{max u v} (F.op ⋙ O) U' ⋙
        PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _) ⊣
      dRestrictScalars.{r, max u v u' v' r} (φ.app U') ⋙
        dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) U' :=
  (dCoevaluationAdjunction.{r, v', u', max u v} (F.op ⋙ O) U').comp
    (PullbackQuasiCoherentBaseChange.dBaseChangeAdj.{r, max u v u' v'} (φ.app U')
      (hO _) (hO' _))

/-- **The derived sections of the derived extension of scalars**: over `U'` they are the derived
base change along the structure map at `U'` of the derived sections over `U'`. -/
noncomputable def dExtendScalarsCompRGamma (U' : C'ᵒᵖ) :
    dExtendScalars F O O' φ ⋙ RGamma.{max u v} O' U' ≅
      RGamma.{max u v} (F.op ⋙ O) U' ⋙
        PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _) :=
  ((conjugateIsoEquiv (dExtendScalarsSectionsAdjunction F O O' φ U')
    (dBaseChangeSectionsAdjunction F O O' φ hO hO' U')).symm
      (dCoevaluationRestrictScalarsSquare F O O' φ U')).symm

/-- **Stacks 0D6D for the derived pullback of modules on chaotic sites.** The derived sections of
`Lg^*K` over `U'` are the derived base change along the structure map at `U'` of the derived
sections of `K` over `F U'`, naturally in `K`. -/
noncomputable def derivedPullbackCompRGamma (U' : C'ᵒᵖ) :
    derivedPullback F O O' φ ⋙ RGamma.{max u v} O' U' ≅
      RGamma.{max u' v'} O (F.op.obj U') ⋙
        (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').baseChange U' :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (dInverseImage F O) (dExtendScalarsCompRGamma F O O' φ hO hO' U') ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (dInverseImageCompRGamma.{r, v, u, v', u'} F O U')
      (PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U') (hO _) (hO' _))

end Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

end

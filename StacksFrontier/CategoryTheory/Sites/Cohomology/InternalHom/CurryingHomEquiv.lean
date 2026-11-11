module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality
import StacksCore.Tactic.StacksAttribute

/-! # The currying bijection of morphism groups of complexes on a ringed site

Let `(C, O)` be a ringed site and let `A`, `B`, `D` be complexes of `O`-modules. **Stacks 0A90**
identifies the complexes `SheafHom(A, SheafHom(B, D))` and `SheafHom(Tot(A ⊗_O B), D)`; this file
reads that identification on degree-zero global cocycles, where it becomes a bijection of
morphism groups of `Comp(Mod(O))`

`(A ⟶ SheafHom(B, D)) ≃ (Tot(A ⊗_O B) ⟶ D)`.

The image of the identity of `SheafHom(B, D)` under it is the cochain-level evaluation morphism
`Tot(SheafHom(B, D) ⊗_O B) ⟶ D`.

## Main definitions

* `AlgebraicGeometry.RingedSite.curryGlobalIso`: the isomorphism of Stacks 0A90 read on global
  sections, as an isomorphism of (universe-lifted) Hom complexes of abelian groups.
* `AlgebraicGeometry.RingedSite.curryCochainEquiv`: currying of degree-`n` cochains.
* `AlgebraicGeometry.RingedSite.curryCocycleEquiv`: currying of degree-`n` cocycles.
* `AlgebraicGeometry.RingedSite.curryHomAddEquiv` and
  `AlgebraicGeometry.RingedSite.curryHomEquiv`: **the currying bijection of morphism groups**,
  as an isomorphism of abelian groups and as a bare bijection.
* `AlgebraicGeometry.RingedSite.curryHomEquivPair`: the same bijection in the shape the abstract
  transpose construction of Tag 08I3 asks for — the internal Hom complex as a bifunctor and the
  total tensor complex on pairs.
* `AlgebraicGeometry.RingedSite.cochainEvaluation`: the cochain-level evaluation morphism
  `Tot(SheafHom(B, D) ⊗_O B) ⟶ D`, the transpose of the identity.

## Main results

* `AlgebraicGeometry.RingedSite.curryCochainEquiv_delta`: currying of cochains commutes with the
  Hom-complex differentials, which is what makes it descend to cocycles.
* `AlgebraicGeometry.RingedSite.curryHomEquiv_f`: the degreewise components of the transpose of a
  morphism.
* `AlgebraicGeometry.RingedSite.curryHomEquiv_symm_cochainEvaluation`: the evaluation morphism is
  the transpose of the identity, so it cannot be degenerate.
* `AlgebraicGeometry.RingedSite.curryGlobalIso_natural_source` and
  `AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_source`: naturality in the source
  complex, the cochain-level counterpart of Stacks 08J8.
* `AlgebraicGeometry.RingedSite.curryHomEquiv_eq_tensor_evaluation`: **the transpose of `f` is
  `f ⊗ 1` followed by the evaluation**, so the bijection is determined by `cochainEvaluation` —
  the cochain-level counterpart of
  `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation`.

## Nothing here is tagged

Tag 0A90 is the isomorphism of complexes
`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso`, which already carries the tag; the
published form of Tag 08DJ is `Stacks.SheafOfModules.derivedCurryingData`, which also already
carries its tag. The bijection below is neither: it is the step by which the *cochain-level*
currying of Tag 0A90 is brought into the shape the abstract transpose construction of Tag 08I3
consumes, and so a step of the proof of Tag 0GM7. No declaration here carries a tag.

## What is still owed to Tag 0GM7

With `cochainEvaluation` in hand the last recorded step of Tag 0GM7 is statable: the following
equation in `DerivedCategory (StructureSheafModules Rc)` **typechecks** (the derived evaluation of
Stacks 08DI against the cochain-level one, conjugated by the comparison of Stacks 08DM and the
K-flat comparison of Stacks 06YU):

```
((derivedTensor Rc).map (strictlyPerfectHomComparison Rc B C)).app (DerivedCategory.Q.obj B) ≫
    RingedSite.derivedCurryHomEquiv (ringedSite Rc)
      (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj B))).obj (DerivedCategory.Q.obj C))
      (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
  ((canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight
      (RingedSite.sheafHomComplex (ringedSite Rc) B C).obj B hB).hom ≫
    DerivedCategory.Q.map (RingedSite.cochainEvaluation (ringedSite Rc) B C)
```

for `B` K-flat and `C` arbitrary, with the hypotheses of
`Stacks.SheafOfModules.strictlyPerfectHomComparison_derivedCurryIso` — no hypothesis on `C`, only
K-flatness of `B` — and with `Stacks.SheafOfModules.derivedTensor Rc` and
`(canonicalDerivedTensorProduct (ringedSite Rc)).tensor` unifying, so the two legs compose.

The inputs it needs are available.

* Stacks 08JA read against the degree-zero global *cocycle* description used here is
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomsFromCocycles`, whose
  `AlgebraicGeometry.RingedSite.globalCohomologyClassOfHom_curryHomEquiv` carries the
  cochain-level currying of Tag 0A90 across it; the agreement of the model-based Stacks 08JA with
  the form at given complexes is
  `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_apply_of_isKFlat`, in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsAgreement`.
* The comparison of Stacks 08DM, `strictlyPerfectHomComparison`, as a degree-zero global
  hypercohomology class is
  `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparisonClass`, in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectHomComparisonClass`,
  and `RingedSite.derivedSheafHomGlobalSectionsEquiv_symm_strictlyPerfectHomComparison`
  says it is the Stacks 08JA preimage of the comparison. The comparison **factors** as the class
  of a morphism of complexes followed by two isomorphisms of `D(O)` — the morphism of internal Hom
  complexes induced by the K-injective augmentation `𝜀_F : F ⟶ R F`, then the inverse of the
  K-injective model comparison, then the inverse of the map `𝜀_F` induces on derived internal
  Hom — which is its definition, so the factorization is `rfl`. Only that first factor has to be
  of the form `DerivedCategory.Q.map f`, Stacks 08JA being natural in its target for an arbitrary
  morphism of `D(O)`.
* No hypothesis on the target `C` is needed: the module
  `StrictlyPerfectHomComparisonEvaluation` (in the folder
  `StacksDraft.CategoryTheory.Sites.Cohomology.InternalHom`) writes both sides of the
  square above as the corresponding side of a more general square at a
  morphism of complexes `f : A ⟶ SheafHom(B, C)`, pushed along `f ⊗ 1` — the cochain side by
  `AlgebraicGeometry.RingedSite.comparisonRight_comp_curryHomEquiv`, the derived side by Stacks
  08J8 in the source variable — and
  `AlgebraicGeometry.RingedSite.evaluationSquare_of_curryingSquare_kFlatResolution` reads it at
  the chosen K-flat resolution of `SheafHom(B, C)` (Stacks 06YS), whose augmentation is a
  quasi-isomorphism and may therefore be cancelled. There the source is K-flat for an arbitrary
  `C`, so `strictlyPerfectHomComparisonClass` applies with `hE = hB` and `hEF` the K-flatness of
  the resolution, and Stacks 0GM5 is not used.

Reducing both sides of the square to their value at an identity —
`curryHomEquiv_eq_tensor_evaluation` here and
`Stacks.SheafOfModules.derivedCurryHomEquiv_eq_tensor_evaluation` on the derived side — turns it
into the single statement that the bijection of Stacks 08DI carries the comparison to the K-flat
comparison of Stacks 06YU followed by `DerivedCategory.Q` of `cochainEvaluation`. Since
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` is Stacks 08JA inverted, then degree-zero
global hypercohomology of the currying isomorphism of Stacks 08DJ, then Stacks 08JA again
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections`), what is left is one currying
square, written out in the module note of `StrictlyPerfectHomComparisonEvaluation`.

**A route for that square, not elaborated.** It is the computation of degree-zero global
hypercohomology of the currying isomorphism of Stacks 08DJ on the class, a push along the two
factors above. For the second factor, the covariant functoriality of the derived internal Hom in
the inner variable, the commutation is `Stacks.SheafOfModules.derivedCurryIso_naturality_target`;
for the first, the K-injective model comparison, it is
`Stacks.SheafOfModules.derivedCurryIso_comparison` (K-flat middle, K-injective target), and at the
remaining class of a morphism of complexes `globalCohomologyClassOfHom_curryHomEquiv` applies.

## Implementation notes

*Why the detour through global sections.* A morphism `A ⟶ SheafHom(B, D)` of complexes is the
same thing as a degree-zero cocycle from `A` to `SheafHom(B, D)`
(`CochainComplex.HomComplex.Cocycle.equivHom`), and the degree-`n` cochains from `A` to `M` are
exactly the degree-`n` global sections of `SheafHom(A, M)` — that is the content of the
`globalSectionsIso` field of `AlgebraicGeometry.RingedSite.SheafHomComplex`, the global half of
the characterisation of the internal Hom complex of Tag 0A8Z. So the isomorphism of complexes
of Tag 0A90, pushed to global sections and read through those two identifications, *is* a
bijection of cochain groups commuting with `δ`, and therefore a bijection of morphism groups.
Nothing is constructed by hand: every map below is the image of
`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso` under a functor or a conjugation by named
isomorphisms, which is also why none of them can be degenerate — each is invertible, with the
inverse coming from the same isomorphism.

*The universe lift.* `globalSectionsIso` lands in the universe lift
`AddCommGrpCat.uliftFunctor.mapHomologicalComplex` of the Hom complex, because the sections of a
sheaf of modules on a site live in the larger of the universe of the site and the universe of the
sections. At the diagonal `RingedSite.{u, u, u}` used here the lift is an endofunctor of
`AddCommGrpCat.{u}`, and it is stripped off with `AddEquiv.ulift` rather than removed from
`globalSectionsIso`: the statement of the field is the one Tag 0A8Z is proved at.

*The differentials.* `curryCochainEquiv_delta` is the commutation of the degree-`n` component of
`curryGlobalIso` with the differentials of the two Hom complexes, read on an element. Both the
differential of a lifted complex and the differential of a Hom complex act on an element by `rfl`
— they are `AddCommGrpCat.uliftFunctor.map` of `CochainComplex.HomComplex.δ` — so the whole lemma
is `congrArg ULift.down` of `HomologicalComplex.Hom.comm`, with no rewriting at all.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A8M](https://stacks.math.columbia.edu/tag/0A8M)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The currying isomorphism of Stacks 0A90, read on global sections.** Taking degreewise
global sections of

`SheafHom(A, SheafHom(B, D)) ≅ SheafHom(Tot(A ⊗_O B), D)`

and identifying each side with the universe lift of a Hom complex of abelian groups by the
global description of Tag 0A8Z gives an isomorphism of complexes

`Hom^•(A, SheafHom(B, D)) ≅ Hom^•(Tot(A ⊗_O B), D)`. -/
def curryGlobalIso :
    (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (A.HomComplex (sheafHomComplex X B D).obj) ≅
      (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.HomComplex
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) D) :=
  (sheafHomComplex X A (sheafHomComplex X B D).obj).globalSectionsIso.symm ≪≫
    ((abelianGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso (sheafHomTensorCurryIso X A B D)) ≪≫
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
      D).globalSectionsIso

/-- `curryGlobalIso` is the global-sections image of the isomorphism of Stacks 0A90, conjugated
by the two global descriptions of Tag 0A8Z. This is its definition, recorded so that a consumer
can see that no other map is involved. -/
theorem curryGlobalIso_hom :
    (curryGlobalIso X A B D).hom =
      (sheafHomComplex X A (sheafHomComplex X B D).obj).globalSectionsIso.inv ≫
        globalSectionsComplexMap X (sheafHomTensorCurryIso X A B D).hom ≫
          (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
            D).globalSectionsIso.hom :=
  rfl

/-- **Currying of cochains.** A degree-`n` cochain from `A` to `SheafHom(B, D)` is a degree-`n`
global section of `SheafHom(A, SheafHom(B, D))`, so the isomorphism of Stacks 0A90 carries it to
a degree-`n` cochain from `Tot(A ⊗_O B)` to `D`, bijectively and additively. -/
def curryCochainEquiv (n : ℤ) :
    Cochain A (sheafHomComplex X B D).obj n ≃+
      Cochain (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) D n :=
  AddEquiv.ulift.symm.trans
    ((((HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) n).mapIso
      (curryGlobalIso X A B D)).addCommGroupIsoToAddEquiv).trans AddEquiv.ulift)

/-- Currying of cochains is the degree-`n` component of `curryGlobalIso`. -/
theorem curryCochainEquiv_apply (n : ℤ) (z : Cochain A (sheafHomComplex X B D).obj n) :
    curryCochainEquiv X A B D n z =
      (AddCommGrpCat.Hom.hom ((curryGlobalIso X A B D).hom.f n) (ULift.up z)).down :=
  rfl

/-- **Currying of cochains commutes with the Hom-complex differentials.** This is the
commutation of `curryGlobalIso` with the differentials, read on a cochain. -/
theorem curryCochainEquiv_delta (n : ℤ) (z : Cochain A (sheafHomComplex X B D).obj n) :
    δ n (n + 1) (curryCochainEquiv X A B D n z) =
      curryCochainEquiv X A B D (n + 1) (δ n (n + 1) z) := by
  have h := ConcreteCategory.congr_hom ((curryGlobalIso X A B D).hom.comm n (n + 1))
    (ULift.up z)
  exact congrArg ULift.down h

/-- **Currying of cocycles.** Currying of cochains commutes with `δ`, so it restricts to a
bijection of the degree-`n` cocycles. -/
def curryCocycleEquiv (n : ℤ) :
    Cocycle A (sheafHomComplex X B D).obj n ≃+
      Cocycle (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) D n where
  toFun z := Cocycle.mk (curryCochainEquiv X A B D n z) (n + 1) rfl (by
    rw [curryCochainEquiv_delta, Cocycle.δ_eq_zero z (n + 1), map_zero])
  invFun w := Cocycle.mk ((curryCochainEquiv X A B D n).symm w) (n + 1) rfl (by
    apply (curryCochainEquiv X A B D (n + 1)).injective
    rw [← curryCochainEquiv_delta, AddEquiv.apply_symm_apply, Cocycle.δ_eq_zero w (n + 1),
      map_zero])
  left_inv z := Cocycle.ext (by
    simp only [Cocycle.mk_coe]
    exact (curryCochainEquiv X A B D n).symm_apply_apply _)
  right_inv w := Cocycle.ext (by
    simp only [Cocycle.mk_coe]
    exact (curryCochainEquiv X A B D n).apply_symm_apply _)
  map_add' z w := Cocycle.ext (by
    simp only [Cocycle.mk_coe, Cocycle.coe_add]
    exact map_add _ _ _)

/-- **The currying bijection of morphism groups, as an isomorphism of abelian groups.** For
complexes `A`, `B`, `D` of `O`-modules on a ringed site,

`(A ⟶ SheafHom(B, D)) ≅ (Tot(A ⊗_O B) ⟶ D)`,

the isomorphism of Stacks 0A90 read on degree-zero global cocycles. -/
def curryHomAddEquiv :
    (A ⟶ (sheafHomComplex X B D).obj) ≃+
      ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) ⟶ D) :=
  (Cocycle.equivHom A (sheafHomComplex X B D).obj).trans
    ((curryCocycleEquiv X A B D 0).trans
      (Cocycle.equivHom (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) D).symm)

/-- **The currying bijection of morphism groups** of Stacks 0A90:

`(A ⟶ SheafHom(B, D)) ≃ (Tot(A ⊗_O B) ⟶ D)`.

This is the bare bijection underlying `curryHomAddEquiv`; it is the shape the abstract transpose
construction of Tag 08I3 asks for. -/
def curryHomEquiv :
    (A ⟶ (sheafHomComplex X B D).obj) ≃
      ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) ⟶ D) :=
  (curryHomAddEquiv X A B D).toEquiv

/-- The degreewise components of the transpose of a morphism: the diagonal values of the curried
degree-zero cochain. -/
theorem curryHomEquiv_f (f : A ⟶ (sheafHomComplex X B D).obj) (i : ℤ) :
    (curryHomEquiv X A B D f).f i =
      (curryCochainEquiv X A B D 0 (Cochain.ofHom f)).v i i (add_zero i) :=
  rfl

/-- **The bijection in the shape the abstract transpose construction of Tag 08I3 asks for.**
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison` takes an internal hom as a
*bifunctor* `H : D₁ᵒᵖ ⥤ D₁ ⥤ D₁`, a tensor product as a functor `T : D₁ × D₁ ⥤ D₁` on *pairs*,
and a bijection `∀ A B D, (A ⟶ (H.obj (op B)).obj D) ≃ (T.obj (A, B) ⟶ D)`. At the internal Hom
bifunctor of Tag 0A8Z (`sheafHomComplexBifunctor`) and the total tensor complex on pairs, that
bijection is `curryHomEquiv` on the nose: both rewritings hold by `rfl`.

This is what lets the transpose construction be instantiated at the Tag 0A8Z/0A90 data rather
than at the monoidal-closed internal hom of `Comp(Mod(O))`, which is a different complex — see
the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackComplexMap`. -/
def curryHomEquivPair :
    (A ⟶ ((sheafHomComplexBifunctor X).obj (op B)).obj D) ≃
      ((Functor.uncurry.obj
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂HomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))).obj (A, B) ⟶ D) :=
  curryHomEquiv X A B D

/-- **The cochain-level evaluation morphism** `Tot(SheafHom(B, D) ⊗_O B) ⟶ D`: the transpose of
the identity of `SheafHom(B, D)` under the currying bijection.

Together with the bijection being a bijection this pins every transpose down: the transpose of
`f : A ⟶ SheafHom(B, D)` is `f ⊗ 1` followed by this evaluation, which is the cochain-level form
of the reduction `Stacks.SheafOfModules.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation`
performs for the derived bijection of Tag 08DI. -/
def cochainEvaluation :
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj (sheafHomComplex X B D).obj).obj B) ⟶
      D :=
  curryHomEquiv X (sheafHomComplex X B D).obj B D (𝟙 _)

/-- **The evaluation morphism is the transpose of the identity, and nothing weaker.** Running the
bijection backwards on `cochainEvaluation` returns the identity of `SheafHom(B, D)`.

This is what rules out a degenerate evaluation: a zero `cochainEvaluation` would force
`𝟙 SheafHom(B, D) = 0`, since `curryHomEquiv` is an isomorphism of abelian groups. -/
theorem curryHomEquiv_symm_cochainEvaluation :
    (curryHomEquiv X (sheafHomComplex X B D).obj B D).symm (cochainEvaluation X B D) =
      𝟙 (sheafHomComplex X B D).obj :=
  (curryHomEquiv X (sheafHomComplex X B D).obj B D).symm_apply_apply _

/-! ### Naturality in the source complex, and the reduction to evaluation -/

section Source

/-- **The pasting of two conjugation squares.** Stated over an abstract category with every
object and morphism a variable, which is what makes it one `isDefEq` instead of a dozen keyed
rewrites against terms of the size the global Hom complexes have. -/
lemma paste_two_conjugations {E : Type*} [Category E]
    {P₁ P₂ Q₁ Q₂ U₁ U₂ V₁ V₂ : E}
    (a₁ : P₁ ≅ U₁) (a₂ : P₂ ≅ U₂) (b₁ : Q₁ ≅ V₁) (b₂ : Q₂ ≅ V₂)
    (p : P₁ ⟶ P₂) (q : Q₁ ⟶ Q₂) (c₁ : P₁ ⟶ Q₁) (c₂ : P₂ ⟶ Q₂) (α : U₁ ⟶ U₂) (β : V₁ ⟶ V₂)
    (h₁ : p ≫ a₂.hom = a₁.hom ≫ α) (h₂ : q ≫ b₂.hom = b₁.hom ≫ β) (h₃ : p ≫ c₂ = c₁ ≫ q) :
    α ≫ a₂.inv ≫ c₂ ≫ b₂.hom = (a₁.inv ≫ c₁ ≫ b₁.hom) ≫ β := by
  have hα : α = a₁.inv ≫ p ≫ a₂.hom := by rw [h₁, Iso.inv_hom_id_assoc]
  rw [hα]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc p c₂, h₃, Category.assoc, h₂]

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Global sections of a composite of morphisms of complexes of `O`-modules. -/
lemma globalSectionsComplexMap_comp
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    globalSectionsComplexMap X φ ≫ globalSectionsComplexMap X ψ =
      globalSectionsComplexMap X (φ ≫ ψ) := by
  rw [← Functor.map_comp, ← Functor.map_comp]

variable {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The isomorphism of Stacks 0A90 is natural in its source complex, after global sections.**
Precomposition with `u : A' ⟶ A` on the iterated side corresponds to precomposition with
`u ⊗ 1` on the tensor side. -/
theorem curryGlobalIso_natural_source (u : A' ⟶ A)
    (B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexConj u (𝟙 (sheafHomComplex X B D).obj)) ≫
        (curryGlobalIso X A' B D).hom =
      (curryGlobalIso X A B D).hom ≫
        (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexConj (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map u).app B)
            (𝟙 D)) := by
  have hcurry : homMap X u (𝟙 (sheafHomComplex X B D).obj) ≫
      (sheafHomTensorCurryIso X A' B D).hom =
    (sheafHomTensorCurryIso X A B D).hom ≫
      homMap X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map u).app B) (𝟙 D) := by
    have h := sheafHomTensorCurryIso_natural X u (𝟙 B) (𝟙 D)
    rwa [homMap_id, CategoryTheory.Functor.map_id, Category.comp_id] at h
  have h₃ := globalSectionsComplexMap_comp X (homMap X u (𝟙 (sheafHomComplex X B D).obj))
    (sheafHomTensorCurryIso X A' B D).hom
  rw [hcurry, ← globalSectionsComplexMap_comp] at h₃
  exact paste_two_conjugations
    (sheafHomComplex X A (sheafHomComplex X B D).obj).globalSectionsIso
    (sheafHomComplex X A' (sheafHomComplex X B D).obj).globalSectionsIso
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
      D).globalSectionsIso
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A').obj B)
      D).globalSectionsIso
    _ _ _ _ _ _
    (globalSectionsIso_homMap X u (𝟙 (sheafHomComplex X B D).obj))
    (globalSectionsIso_homMap X
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map u).app B) (𝟙 D))
    h₃

/-- Currying of cochains is natural in the source complex. -/
theorem curryCochainEquiv_homComplexConj (u : A' ⟶ A)
    (B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (z : Cochain A (sheafHomComplex X B D).obj n) :
    curryCochainEquiv X A' B D n
        (AddCommGrpCat.Hom.hom
          ((homComplexConj u (𝟙 (sheafHomComplex X B D).obj)).f n) z) =
      AddCommGrpCat.Hom.hom
        ((homComplexConj (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map u).app B)
          (𝟙 D)).f n) (curryCochainEquiv X A B D n z) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun φ => HomologicalComplex.Hom.f φ n)
      (curryGlobalIso_natural_source X u B D)) (ULift.up z)
  exact congrArg ULift.down h

/-- **The currying bijection is natural in the source complex.** The transpose of `u ≫ f` is
`u ⊗ 1` followed by the transpose of `f`. This is the cochain-level counterpart of
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source` (Stacks 08J8). -/
theorem curryHomEquiv_naturality_source (u : A' ⟶ A)
    (B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : A ⟶ (sheafHomComplex X B D).obj) :
    curryHomEquiv X A' B D (u ≫ f) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map u).app B ≫
        curryHomEquiv X A B D f := by
  have hz : Cochain.ofHom (u ≫ f) =
      AddCommGrpCat.Hom.hom
        ((homComplexConj u (𝟙 (sheafHomComplex X B D).obj)).f 0) (Cochain.ofHom f) := by
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    obtain rfl : p = q := by omega
    rw [homComplexConj_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.id_f,
      Category.comp_id, HomologicalComplex.comp_f]
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  rw [curryHomEquiv_f, hz, curryCochainEquiv_homComplexConj, homComplexConj_v,
    HomologicalComplex.comp_f, curryHomEquiv_f, HomologicalComplex.id_f, Category.comp_id]

/-- **The transpose of a morphism is tensoring with the identity and then evaluating.** So the
currying bijection is determined by its value at the identity, which is `cochainEvaluation`.

This is the cochain-level counterpart of
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation`, and it is what makes
`cochainEvaluation` the whole content of the bijection. -/
theorem curryHomEquiv_eq_tensor_evaluation
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : A ⟶ (sheafHomComplex X B D).obj) :
    curryHomEquiv X A B D f =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app B ≫
        cochainEvaluation X B D := by
  have h := curryHomEquiv_naturality_source X f B D (𝟙 (sheafHomComplex X B D).obj)
  rwa [Category.comp_id] at h

end Source

end AlgebraicGeometry.RingedSite

end

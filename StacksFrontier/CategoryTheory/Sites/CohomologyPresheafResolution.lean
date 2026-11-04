module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology presheaf of an abelian sheaf, computed by an injective resolution

Let `J` be a Grothendieck topology on a category `C`. Mathlib defines the cohomology
presheaf `CategoryTheory.Sheaf.cohomologyPresheaf F n` of an abelian sheaf `F` by
`U ↦ Ext^n (freeYonedaSheaf J U, F)`, where `freeYonedaSheaf J U` is the sheafification of
the free abelian presheaf on the presheaf of sets `yoneda.obj U`. This file identifies that
abelian group, for a chosen injective resolution `F ⟶ I^•`, with the degree-`n` cohomology of
the complex of sections `Γ(U, I^•)`.

Two of the three ingredients are in Mathlib:

* `CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass` computes `Ext X Y n` as the
  group of degree-`n` cohomology classes of the Hom-complex from the single complex `X` to an
  injective resolution of `Y`, and `CochainComplex.HomComplex.homologyAddEquiv` identifies
  that group of cohomology classes with the homology of the Hom-complex.
* `CochainComplex.HomComplex.Cochain.fromSingleEquiv` identifies a degree-`n` cochain from a
  single complex concentrated in degree `0` with a morphism into the degree-`n` term, and
  `CochainComplex.HomComplex.Cochain.δ_fromSingleMk` says that the Hom-complex differential
  is, under that identification, composition with the differential of the target.

What is added here is the third one, the coefficient computation
`Hom(freeYonedaSheaf J U, Z) ≃+ Γ(U, Z)` as an *additive* equivalence
(`freeYonedaSheafHomAddEquiv`): Mathlib's `CategoryTheory.Sheaf.freeYonedaHomEquiv` is a bare
`Equiv`, and is moreover stated for the coproduct presentation
`CategoryTheory.Presheaf.freeYoneda` of the free abelian presheaf rather than for the
`AddCommGrpCat.free`-presentation used by `cohomologyPresheaf`. Together they give the
isomorphism of cochain complexes of abelian groups `homComplexIsoSectionsCochainComplex` and
hence the identification `extAddEquivSectionsHomology`.

## Main definitions and results

* `freeYonedaFreeHomAddEquiv`: `(yoneda.obj U ⋙ AddCommGrpCat.free ⟶ Q) ≃+ Q.obj (op U)`, the
  additive form of the Yoneda plus free/forgetful computation for presheaves of abelian
  groups.
* `freeYonedaSheaf J U`: the abelian sheaf out of which
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor` takes `Ext`-groups.
* `freeYonedaSheafHomAddEquiv`: `(freeYonedaSheaf J U ⟶ Z) ≃+ Γ(U, Z)`, additively, natural
  in `Z` (`freeYonedaSheafHomAddEquiv_naturality`) and in `U`
  (`freeYonedaSheafHomAddEquiv_naturality_left`).
* `sectionsCochainComplex R U`: the complex of sections `Γ(U, I^•)` of an injective
  resolution, as a `ℤ`-indexed cochain complex of abelian groups.
* `homComplexIsoSectionsCochainComplex`: the Hom-complex from the single complex
  `freeYonedaSheaf J U` to `R.cochainComplex` is isomorphic to `sectionsCochainComplex R U`.
* `extAddEquivSectionsHomology` and `cohomologyPresheafObjAddEquiv`: the resulting additive
  equivalences `Ext^n (freeYonedaSheaf J U, F) ≃+ H^n (Γ(U, I^•))` and
  `(F.cohomologyPresheaf n).obj (op U) ≃+ H^n (Γ(U, I^•))`.

This is the coefficient half of the identification of the second page of the
Čech-to-derived-functor spectral sequence: it is what turns `H^q` of a resolution into the
cohomology presheaf `H^q(F)`. The analogue for sheaves of modules, where the cohomology
presheaf is defined by a right derived functor and no such bridge is needed, is
`Stacks.Cohomology.CechSpectral.cechDoubleHomologyNatIso`.

## Implementation notes

The equivalences produced here are stated at a fixed object `U` of the site and a fixed sheaf
`F` with a fixed injective resolution. Naturality in `U`, which would upgrade
`cohomologyPresheafObjAddEquiv` to an isomorphism of presheaves, is **not** proved: it needs
the compatibility of `CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass` with
precomposition in the first variable — available elementwise in Mathlib as
`CategoryTheory.InjectiveResolution.mk₀_comp_extMk` — to be transported through the homology
of the Hom-complex, for which the functoriality of `CochainComplex.HomComplex` in its first
variable would first have to be set up. Naturality in `F` is likewise not proved.

The site is taken to have a single universe, `C : Type u` with `Category.{u} C`. This is a
genuine restriction: `CategoryTheory.Sheaf.cohomologyPresheafFunctor` forces the coefficient
category to be `AddCommGrpCat.{v}` when `Category.{v} C`, while the Hom-complex of
`Sheaf J AddCommGrpCat.{v}` is a complex of objects of `AddCommGrpCat.{max u v}`, and the two
must agree for the complexes to be compared. The universe `w'` of the `Ext`-groups stays
arbitrary.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex

universe w' u

namespace Stacks.Cohomology.CohomologyPresheaf

variable {C : Type u} [Category.{u} C]

/-- The additive form of the computation of the group of morphisms out of the free abelian
presheaf `yoneda.obj U ⋙ AddCommGrpCat.free` on the presheaf of sets `yoneda.obj U`: it is
the group of sections over `U`. The underlying bijection is the right-whiskered free/forgetful
adjunction followed by the Yoneda lemma. -/
@[sga "4 I 5.8.2" "Abelian groups"]
noncomputable def freeYonedaFreeHomAddEquiv (U : C) (Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ Q) ≃+ Q.obj (op U) where
  __ := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) Q).trans yonedaEquiv
  map_add' α β := by
    change ((α + β).app (op U)) _ = ((α.app (op U)) _ + (β.app (op U)) _)
    rw [NatTrans.app_add]
    rfl

/-- `freeYonedaFreeHomAddEquiv` is the right-whiskered free/forgetful adjunction followed by
the Yoneda lemma. -/
lemma freeYonedaFreeHomAddEquiv_eq (U : C) (Q : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (α : yoneda.obj U ⋙ AddCommGrpCat.free ⟶ Q) :
    freeYonedaFreeHomAddEquiv U Q α =
      yonedaEquiv ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) Q α) :=
  rfl

/-- `freeYonedaFreeHomAddEquiv` evaluates a morphism at the generator of the free abelian
group on `yoneda.obj U` which corresponds to the identity of `U`. -/
lemma freeYonedaFreeHomAddEquiv_apply (U : C) (Q : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (α : yoneda.obj U ⋙ AddCommGrpCat.free ⟶ Q) :
    freeYonedaFreeHomAddEquiv U Q α = (α.app (op U)) (FreeAbelianGroup.of (𝟙 U)) :=
  rfl

/-- `freeYonedaFreeHomAddEquiv` is natural in the target presheaf. -/
lemma freeYonedaFreeHomAddEquiv_naturality (U : C) {Q Q' : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (β : Q ⟶ Q') (α : yoneda.obj U ⋙ AddCommGrpCat.free ⟶ Q) :
    freeYonedaFreeHomAddEquiv U Q' (α ≫ β) =
      (β.app (op U)) (freeYonedaFreeHomAddEquiv U Q α) := by
  rw [freeYonedaFreeHomAddEquiv_eq, freeYonedaFreeHomAddEquiv_eq,
    Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]
  rfl

/-- `freeYonedaFreeHomAddEquiv` is natural in `U`: precomposition with the map of free abelian
presheaves induced by `g : V ⟶ U` is restriction of sections along `g`. -/
lemma freeYonedaFreeHomAddEquiv_naturality_left {U V : C} (g : V ⟶ U)
    (Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (α : yoneda.obj U ⋙ AddCommGrpCat.free ⟶ Q) :
    freeYonedaFreeHomAddEquiv V Q
        (Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free ≫ α) =
      (Q.map g.op) (freeYonedaFreeHomAddEquiv U Q α) := by
  rw [freeYonedaFreeHomAddEquiv_eq, freeYonedaFreeHomAddEquiv_eq,
    show Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free =
      ((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free).map
        (yoneda.map g) from rfl, Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) Q α) g).symm

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]

/-- The sheaf associated to the free abelian presheaf on `yoneda.obj U`. This is the object
out of which `CategoryTheory.Sheaf.cohomologyPresheafFunctor` takes `Ext`-groups. -/
noncomputable abbrev freeYonedaSheaf (U : C) : Sheaf J AddCommGrpCat.{u} :=
  (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- The morphism `freeYonedaSheaf J V ⟶ freeYonedaSheaf J U` induced by `g : V ⟶ U`; it is the
map along which `CategoryTheory.Sheaf.cohomologyPresheaf` restricts. -/
noncomputable abbrev freeYonedaSheafMap {U V : C} (g : V ⟶ U) :
    freeYonedaSheaf J V ⟶ freeYonedaSheaf J U :=
  (presheafToSheaf J AddCommGrpCat.{u}).map
    (Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free)

variable {J}

/-- The group of morphisms from `freeYonedaSheaf J U` to an abelian sheaf `Z` is the group of
sections of `Z` over `U`, additively. This is the additive refinement of
`CategoryTheory.Sheaf.freeYonedaHomEquiv` for the `AddCommGrpCat.free`-presentation of the
free abelian presheaf. -/
noncomputable def freeYonedaSheafHomAddEquiv (U : C) (Z : Sheaf J AddCommGrpCat.{u}) :
    (freeYonedaSheaf J U ⟶ Z) ≃+ ((sheafSections J AddCommGrpCat.{u}).obj (op U)).obj Z :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homAddEquiv _ Z).trans
    (freeYonedaFreeHomAddEquiv U Z.obj)

/-- `freeYonedaSheafHomAddEquiv` is the sheafification adjunction followed by
`freeYonedaFreeHomAddEquiv`. -/
lemma freeYonedaSheafHomAddEquiv_eq (U : C) (Z : Sheaf J AddCommGrpCat.{u})
    (α : freeYonedaSheaf J U ⟶ Z) :
    freeYonedaSheafHomAddEquiv U Z α = freeYonedaFreeHomAddEquiv U Z.obj
      ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ Z α) :=
  rfl

/-- `freeYonedaSheafHomAddEquiv` is natural in the target sheaf. -/
lemma freeYonedaSheafHomAddEquiv_naturality (U : C) {Z Z' : Sheaf J AddCommGrpCat.{u}}
    (f : Z ⟶ Z') (α : freeYonedaSheaf J U ⟶ Z) :
    freeYonedaSheafHomAddEquiv U Z' (α ≫ f) =
      (((sheafSections J AddCommGrpCat.{u}).obj (op U)).map f)
        (freeYonedaSheafHomAddEquiv U Z α) := by
  rw [freeYonedaSheafHomAddEquiv_eq, freeYonedaSheafHomAddEquiv_eq,
    Adjunction.homEquiv_naturality_right, freeYonedaFreeHomAddEquiv_naturality]
  rfl

/-- `freeYonedaSheafHomAddEquiv` is natural in `U`: precomposition with `freeYonedaSheafMap g`
is restriction of sections along `g`. -/
lemma freeYonedaSheafHomAddEquiv_naturality_left {U V : C} (g : V ⟶ U)
    (Z : Sheaf J AddCommGrpCat.{u}) (α : freeYonedaSheaf J U ⟶ Z) :
    freeYonedaSheafHomAddEquiv V Z (freeYonedaSheafMap J g ≫ α) =
      (Z.obj.map g.op) (freeYonedaSheafHomAddEquiv U Z α) := by
  rw [freeYonedaSheafHomAddEquiv_eq, freeYonedaSheafHomAddEquiv_eq,
    Adjunction.homEquiv_naturality_left, freeYonedaFreeHomAddEquiv_naturality_left]

variable {F : Sheaf J AddCommGrpCat.{u}} (R : InjectiveResolution F)

/-- The complex of sections over `U` of (the `ℤ`-indexed extension by zero of) an injective
resolution: in degree `n` it is `Γ(U, I^n)`. -/
noncomputable def sectionsCochainComplex (U : C) : CochainComplex AddCommGrpCat.{u} ℤ :=
  (((sheafSections J AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex _).obj R.cochainComplex

/-- In degree `k : ℕ`, the complex of sections of an injective resolution is the group of
sections over `U` of the `k`-th term of the resolution. -/
noncomputable def sectionsCochainComplexXIso (U : C) (n : ℤ) (k : ℕ) (h : k = n) :
    (sectionsCochainComplex R U).X n ≅ (R.cocomplex.X k).obj.obj (op U) :=
  ((sheafSections J AddCommGrpCat.{u}).obj (op U)).mapIso (R.cochainComplexXIso n k h)

/-- The degreewise comparison underlying `homComplexIsoSectionsCochainComplex`: a degree-`n`
cochain from the single complex `freeYonedaSheaf J U` to the resolution is a section over `U`
of the degree-`n` term of the resolution. -/
noncomputable def cochainAddEquivSections (U : C) (n : ℤ) :
    Cochain ((singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj (freeYonedaSheaf J U))
        R.cochainComplex n ≃+
      ((sheafSections J AddCommGrpCat.{u}).obj (op U)).obj (R.cochainComplex.X n) :=
  (Cochain.fromSingleEquiv (K := R.cochainComplex) (X := freeYonedaSheaf J U) (p := 0)
    (q := n) (n := n) (zero_add n)).trans
      (freeYonedaSheafHomAddEquiv U (R.cochainComplex.X n))

/-- Under `cochainAddEquivSections`, the differential of the Hom-complex is the differential of
the complex of sections. -/
lemma cochainAddEquivSections_δ (U : C) (n m : ℤ)
    (α : Cochain ((singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj (freeYonedaSheaf J U))
      R.cochainComplex n) :
    cochainAddEquivSections R U m (δ n m α) =
      (((sheafSections J AddCommGrpCat.{u}).obj (op U)).map (R.cochainComplex.d n m))
        (cochainAddEquivSections R U n α) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective α n (zero_add n)
  dsimp only [cochainAddEquivSections, AddEquiv.trans_apply]
  rw [Cochain.δ_fromSingleMk f (zero_add n) m m (zero_add m),
    Cochain.fromSingleEquiv_fromSingleMk, Cochain.fromSingleEquiv_fromSingleMk,
    freeYonedaSheafHomAddEquiv_naturality]

/-- `cochainAddEquivSections` as an isomorphism in `AddCommGrpCat`. -/
noncomputable def cochainIsoSections (U : C) (n : ℤ) :
    (HomComplex ((singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj (freeYonedaSheaf J U))
      R.cochainComplex).X n ≅ (sectionsCochainComplex R U).X n :=
  (cochainAddEquivSections R U n).toAddCommGrpIso

/-- The Hom-complex from the single complex `freeYonedaSheaf J U` concentrated in degree `0`
to an injective resolution `I^•` of `F` is the complex of sections `Γ(U, I^•)`. -/
noncomputable def homComplexIsoSectionsCochainComplex (U : C) :
    HomComplex ((singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj (freeYonedaSheaf J U))
      R.cochainComplex ≅ sectionsCochainComplex R U :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ cochainIsoSections R U n)
    (fun n m _ ↦ AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun α ↦ (cochainAddEquivSections_δ R U n m α).symm))

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{u})]

/-- **An `Ext`-group out of `freeYonedaSheaf J U` is computed by an injective resolution of the
target.** For `R` an injective resolution of an abelian sheaf `F`, the group
`Ext^n (freeYonedaSheaf J U, F)` is the degree-`n` cohomology of the complex of sections
`Γ(U, I^•)`. -/
noncomputable def extAddEquivSectionsHomology (U : C) (n : ℕ) :
    Ext (freeYonedaSheaf J U) F n ≃+ (sectionsCochainComplex R U).homology (n : ℤ) :=
  (R.extAddEquivCohomologyClass (X := freeYonedaSheaf J U) (n := n)).trans
    (((CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm).trans
      (((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
        (n : ℤ)).mapIso (homComplexIsoSectionsCochainComplex R U)).addCommGroupIsoToAddEquiv))

/-- The value of `CategoryTheory.Sheaf.cohomologyPresheaf` at `U` is the `Ext`-group out of
`freeYonedaSheaf J U`. -/
lemma cohomologyPresheaf_obj (n : ℕ) (U : C) :
    (F.cohomologyPresheaf n).obj (op U) =
      AddCommGrpCat.of (Ext (freeYonedaSheaf J U) F n) :=
  rfl

/-- The restriction maps of `CategoryTheory.Sheaf.cohomologyPresheaf` are precomposition with
the maps `freeYonedaSheafMap`. -/
lemma cohomologyPresheaf_map (n : ℕ) {U V : C} (g : V ⟶ U) :
    (F.cohomologyPresheaf n).map g.op = AddCommGrpCat.ofHom (AddMonoidHom.mk'
      (fun α ↦ (Ext.mk₀ (freeYonedaSheafMap J g)).comp α (zero_add _)) (by simp)) :=
  rfl

/-- **The cohomology presheaf of an abelian sheaf is computed by an injective resolution.** At
each object `U` of the site, the value of `CategoryTheory.Sheaf.cohomologyPresheaf F n` is the
degree-`n` cohomology of the complex of sections `Γ(U, I^•)` of an injective resolution `I^•`
of `F`. This is an additive equivalence for each fixed `U` and each fixed `F`; naturality in
`U` and in `F` is not asserted. -/
noncomputable def cohomologyPresheafObjAddEquiv (n : ℕ) (U : C) :
    (F.cohomologyPresheaf n).obj (op U) ≃+ (sectionsCochainComplex R U).homology (n : ℤ) :=
  extAddEquivSectionsHomology R U n

end Stacks.Cohomology.CohomologyPresheaf

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictCoextendScalarsComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoextendScalarsRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEpiFullyFaithful
public import StacksFrontier.Algebra.Homology.HomComplexTargetIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.HomAfterLocalization
public import StacksCore.Tactic.StacksAttribute

/-!
# Mapping a complex of modules into a coextension of scalars

Let `φ₀ : 𝒪 ⟶ 𝒪'` be a morphism of sheaves of commutative rings on a site `𝒞`, let `L` be a
complex of sheaves of `𝒪'`-modules and let `I` be a complex of sheaves of `𝒪`-modules. Over
every object `U` of `𝒞`, the degree-`n` cochains from `L|_U` into `SheafHom_𝒪(𝒪', I)|_U` are the
degree-`n` cochains from the restriction of `L|_U` to `𝒪|_U` into `I|_U`.

This is Stacks Tag 0932 — the adjunction between restriction and coextension of scalars — read
on the slice sites, which is the form in which the proof of Stacks Tag 0996(2) uses it. The two
inputs are `Stacks.SheafOfModules.CoextendScalars.homComplexRestrictCoextendIso`, Tag 0932 for
Hom complexes, and `Stacks.SheafOfModules.CoextendScalars.sheafCoextOverIso`, which identifies
the restriction to a slice of a coextension of scalars with the coextension along the restricted
morphism.

## Main definitions

* `AlgebraicGeometry.RingedSite.coextSectionIso`: the comparison of section complexes over an
  object of the site.
* `AlgebraicGeometry.RingedSite.coextHomComplexIso`: **Tag 0996(2) at the complex level**, the
  comparison as an isomorphism of complexes of sheaves of modules.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_coextendScalarsIso`: **Stacks Tag 0996(2).**
* `AlgebraicGeometry.RingedSite.derivedSheafHom_coextendScalars_idempotent`: coextension of
  scalars along an epimorphism of sheaves of commutative rings is idempotent. The "in
  particular" of Tag 0996(2) is its instance at the localization `𝒪 ⟶ 𝒪_f`, where the
  epimorphism hypothesis is discharged, and that is where the tag is registered; see
  `AlgebraicGeometry.RingedSite.derivedSheafHom_awayCoextendScalars_idempotent`.
* `AlgebraicGeometry.RingedSite.coextSectionLinearEquiv`: the same comparison, as a linear
  equivalence over the sections of `𝒪`.
* `AlgebraicGeometry.RingedSite.coextSectionComparison`: the comparison as a plain morphism of
  complexes of abelian groups.

## Main results

* `AlgebraicGeometry.RingedSite.coextSectionIso_apply`: the comparison evaluates each local
  component of a cochain — which is a local morphism `𝒪'|_W ⟶ I|_W` — at the unit section. This
  pins the comparison down rather than merely asserting that some isomorphism exists.
* `AlgebraicGeometry.RingedSite.coextSectionLinearEquiv_natural`: the comparison is compatible
  with restriction along an arrow of the site.
* `AlgebraicGeometry.RingedSite.coextHomComplexIso_hom_apply`: the same description for the
  complex-level comparison, which is what makes it the canonical one.

## Implementation notes

The comparison is built from the target of Tag 0932 towards its source, so that the formula for
it involves the *inverse* of the Tag 0932 Hom-bijection, which is the explicit one: evaluate a
local morphism out of `𝒪'` at the unit section. The forward bijection would leave the comparison
described only up to the inverse of `sheafCoextOverIso`, which is then not computable on
sections.

`Stacks.PresheafOfModules.CoextendScalars.invSecVal_smul` and `invSecVal_smul_left` are what make
the comparison linear: a local scalar of `𝒪'` acts on the coextension by precomposition with
right multiplication, so evaluating at the unit section after acting by `a'` is evaluating at
`a'`, and evaluating at the image of a local scalar of `𝒪` is scaling the value at the unit
section.

The comparison of internal Hom complexes is assembled degreewise and then shown to be an
isomorphism, rather than built as an isomorphism of complexes: the compatibility with the
differential crosses twice between the differential of a complex of sheaves of modules and the
differential of its section complex, which does not fit in one declaration's elaboration
budget. `sectionComparison_comm_apply` makes that crossing once, for an arbitrary family of
morphisms of section complexes, and `coextSectionFamily` carries the retyping of the comparison
over the single ringed site `X`.

The "in particular" of the clause is not a consequence of the adjunction alone: for a general
morphism of ring sheaves `SheafHom_𝒪(𝒪', SheafHom_𝒪(𝒪', H))` is `SheafHom_𝒪(𝒪' ⊗_𝒪 𝒪', H)`,
which is `SheafHom_𝒪(𝒪', H)` only because `φ₀` is an epimorphism. What is used is the
epimorphism form of that: restriction of scalars along an epimorphism of sheaves of commutative
rings is fully faithful, Stacks Tag 0930 — `restrictScalars_fullyFaithful_of_epi` of
`HomAfterLocalization.lean` — so the unit of Tag 0932 is an isomorphism. For the localization
`𝒪 ⟶ 𝒪_f` the epimorphism hypothesis is a theorem, `epi_toAwaySheaf`.

## References

* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.CoextendScalars Stacks.PresheafOfModules.CoextendScalars

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) (O' : Sheaf X.J CommRingCat.{u}) (φ₀ : X.O ⟶ O')

/-- The ringed site with the same underlying site and the structure sheaf `O'`. -/
abbrev coeffSite : RingedSite.{u, u, u} := { C := X.C, J := X.J, O := O' }

/-- `φ₀` read as a morphism of sheaves of not necessarily commutative rings, which is the form
restriction and coextension of scalars take. -/
abbrev coeffHom :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf O') :=
  (sheafCompose X.J (forget₂ CommRingCat RingCat.{u})).map φ₀

/-- Restriction of scalars along `φ₀`, with the module universe pinned. -/
abbrev coeffRestrict :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O') ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  SheafOfModules.restrictScalars.{u} (coeffHom X O' φ₀)

/-- Coextension of scalars along `φ₀`, with the module universe pinned. -/
abbrev coeffCoextend :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O') :=
  coextendScalars.{u} (coeffHom X O' φ₀)

/-- Restriction of scalars along `φ₀`, applied degreewise to cochain complexes. -/
abbrev coeffRestrictComplex :=
  (coeffRestrict X O' φ₀).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Coextension of scalars along `φ₀`, applied degreewise to cochain complexes. -/
abbrev coeffCoextendComplex :=
  (coeffCoextend X O' φ₀).mapHomologicalComplex (ComplexShape.up ℤ)

variable (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O')) ℤ)
  (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- Restricting `SheafHom_O(O', I)` to a slice site is the coextension along the restricted
morphism of the restriction of `I`, degreewise by
`Stacks.SheafOfModules.CoextendScalars.sheafCoextOverIso`. -/
def coextOverComplexIso (U : X.C) :
    restrictComplex (coeffSite X O') ((coeffCoextendComplex X O' φ₀).obj I) U ≅
      ((coextendScalars.{u} (sliceHom (coeffHom X O' φ₀) U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (restrictComplex X I U) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => sheafCoextOverIso (coeffHom X O' φ₀) U (I.X n))
    (fun n m _ => (coextOverHom_naturality (coeffHom X O' φ₀) U (I.d n m)).symm)

/-- **The comparison of section complexes on a slice site.** Over `U`, a cochain from `L` into
`SheafHom_O(O', I)` is a cochain from the restriction of `L` to `O` into `I`: this is Tag 0932
for Hom complexes on the slice site, read through the restriction to that slice of the
coextension of scalars. -/
def coextSectionIso (U : X.C) :
    sectionComplex (coeffSite X O')
        (sheafHomComplex (coeffSite X O') L ((coeffCoextendComplex X O' φ₀).obj I)).obj U ≅
      sectionComplex X (sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).obj U :=
  (sheafHomComplex (coeffSite X O') L ((coeffCoextendComplex X O' φ₀).obj I)).sectionsIso U ≪≫
    CochainComplex.HomComplex.targetIso _ (coextOverComplexIso X O' φ₀ I U) ≪≫
    (homComplexRestrictCoextendIso (sliceHom (coeffHom X O' φ₀) U)
      (restrictComplex (coeffSite X O') L U) (restrictComplex X I U)).symm ≪≫
    ((sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).sectionsIso U).symm

section Adjunction

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {O O'' : Sheaf J RingCat.{u}}

/-- The inverse of the Tag 0932 Hom-bijection evaluates a local morphism at the unit section:
`β' ↦ (y ↦ β'(y)(1))`. -/
theorem adjHomEquiv_symm_val_app_apply (ψ : O ⟶ O'')
    (G : SheafOfModules.{u} O'') (F : SheafOfModules.{u} O)
    (β : G ⟶ (coextendScalars ψ).obj F) (Y : Cᵒᵖ) (y : G.val.obj Y) :
    (((((restrictScalars_coextendScalars_adjunction ψ).homEquiv G F).symm) β).val.app Y).hom y =
      invSecVal ψ.hom F.val Y ((β.val.app Y).hom y) := by
  rw [show ((restrictScalars_coextendScalars_adjunction ψ).homEquiv G F) =
      coextendScalarsSheafHomEquiv ψ G F from by
    simp only [Stacks.SheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction,
      Adjunction.mkOfHomEquiv_homEquiv]]
  rfl

/-- The inverse of the complex-level Tag 0932 isomorphism acts on each homogeneous component by
the inverse of the Hom-bijection. -/
theorem homComplexRestrictCoextend_inv_v (ψ : O ⟶ O'')
    (A : CochainComplex (SheafOfModules.{u} O'') ℤ)
    (B : CochainComplex (SheafOfModules.{u} O) ℤ) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain A
      (((coextendScalars ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj B) n)
    (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom ((homComplexRestrictCoextendIso ψ A B).inv.f n) z).v p q hpq =
      ((restrictScalars_coextendScalars_adjunction ψ).homEquiv (A.X p) (B.X q)).symm
        (z.v p q hpq) :=
  rfl

end Adjunction

/-- The forward comparison appears in `coextSectionIso` precomposed by the inverse of the
section description of the target, so that inverse never has to be computed. -/
theorem coextSectionIso_cochain (U : X.C) (n : ℤ)
    (t : ((sheafHomComplex (coeffSite X O') L
      ((coeffCoextendComplex X O' φ₀).obj I)).obj.X n).val.obj (op U)) :
    AddCommGrpCat.Hom.hom
        (((sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).sectionsIso U).hom.f n)
        (AddCommGrpCat.Hom.hom ((coextSectionIso X O' φ₀ L I U).hom.f n) t) =
      AddCommGrpCat.Hom.hom
        ((homComplexRestrictCoextendIso (sliceHom (coeffHom X O' φ₀) U)
          (restrictComplex (coeffSite X O') L U) (restrictComplex X I U)).inv.f n)
        (AddCommGrpCat.Hom.hom
          ((CochainComplex.HomComplex.targetIso _ (coextOverComplexIso X O' φ₀ I U)).hom.f n)
          (AddCommGrpCat.Hom.hom
            (((sheafHomComplex (coeffSite X O') L
              ((coeffCoextendComplex X O' φ₀).obj I)).sectionsIso U).hom.f n) t)) :=
  Iso.inv_hom_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    ((sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).sectionsIso U)) _

/-- **The comparison, on a local section.** A degree-`n` section over `U` of the internal Hom
complex from `L` into `SheafHom_O(O', I)` is a cochain whose local components take values in
local morphisms `O'|_W ⟶ I|_W`; the comparison evaluates each of those at the unit section. -/
theorem coextSectionIso_apply (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (t : ((sheafHomComplex (coeffSite X O') L
      ((coeffCoextendComplex X O' φ₀).obj I)).obj.X n).val.obj (op U))
    {W : X.C} (g : W ⟶ U) (x : (L.X p).val.obj (op W)) :
    (((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).sectionsIso U).hom.f n)
        (AddCommGrpCat.Hom.hom
          ((coextSectionIso X O' φ₀ L I U).hom.f n) t)).v p q hpq).val.app
        (op (Over.mk g))) x =
      invSecVal (coeffHom X O' φ₀).hom (I.X q).val (op W)
        ((((AddCommGrpCat.Hom.hom
          (((sheafHomComplex (coeffSite X O') L
            ((coeffCoextendComplex X O' φ₀).obj I)).sectionsIso U).hom.f n) t).v
            p q hpq).val.app (op (Over.mk g))) x) := by
  refine Eq.trans (congrArg
    (fun c => (((CochainComplex.HomComplex.Cochain.v c p q hpq).val.app
      (op (Over.mk g))).hom x)) (coextSectionIso_cochain X O' φ₀ L I U n t)) ?_
  refine Eq.trans (congrArg (fun m => ((m.val.app (op (Over.mk g))).hom x))
    (homComplexRestrictCoextend_inv_v (sliceHom (coeffHom X O' φ₀) U)
      (restrictComplex (coeffSite X O') L U) (restrictComplex X I U) n _ p q hpq)) ?_
  refine Eq.trans (adjHomEquiv_symm_val_app_apply (sliceHom (coeffHom X O' φ₀) U)
    ((restrictComplex (coeffSite X O') L U).X p) ((restrictComplex X I U).X q) _
    (op (Over.mk g)) x) ?_
  refine Eq.trans (congrArg
    (fun m : (restrictComplex (coeffSite X O') L U).X p ⟶
        (coextendScalars (sliceHom (coeffHom X O' φ₀) U)).obj
          ((restrictComplex X I U).X q) =>
      invSecVal (sliceHom (coeffHom X O' φ₀) U).hom ((restrictComplex X I U).X q).val
        (op (Over.mk g)) ((m.val.app (op (Over.mk g))).hom x))
    (CochainComplex.HomComplex.targetIso_hom_apply_v
      (restrictComplex (coeffSite X O') L U) (coextOverComplexIso X O' φ₀ I U) n _ p q hpq)) ?_
  exact coextOverHom_app_apply (coeffHom X O' φ₀) U (I.X q) (op (Over.mk g)) _
    (op (Over.mk (𝟙 (Over.mk g)))) 1

/-- The structure map `φ₀` is natural: mapping a section of `O` into `O'` and restricting it
along `g` is restricting it and then mapping it into `O'`. -/
theorem coeffHom_naturality_apply {W U : X.C} (g : W ⟶ U)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) :
    (coeffHom X O' φ₀).hom.app (op W)
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op r) =
      (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.map g.op
        ((coeffHom X O' φ₀).hom.app (op U) r) :=
  ConcreteCategory.congr_hom ((coeffHom X O' φ₀).hom.naturality g.op) r

/-- **The comparison is linear over the structure sheaf of `X`**, the source being a module over
it by restriction of scalars along `φ₀`. -/
def coextSectionLinearEquiv (U : X.C) (n : ℤ) :
    ((((coeffRestrictComplex X O' φ₀).obj (sheafHomComplex (coeffSite X O') L
        ((coeffCoextendComplex X O' φ₀).obj I)).obj).X n).val.obj (op U))
      ≃ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)]
      (((sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).obj.X n).val.obj
        (op U)) where
  toFun := AddCommGrpCat.Hom.hom ((coextSectionIso X O' φ₀ L I U).hom.f n)
  invFun := AddCommGrpCat.Hom.hom ((coextSectionIso X O' φ₀ L I U).inv.f n)
  left_inv := Iso.hom_inv_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    (coextSectionIso X O' φ₀ L I U))
  right_inv := Iso.inv_hom_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    (coextSectionIso X O' φ₀ L I U))
  map_add' := map_add _
  map_smul' r t := by
    apply sheafHomSection_ext (sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I) U n
    intro p q hpq T x
    obtain ⟨T⟩ := T
    obtain ⟨W, g, rfl⟩ := Over.mk_surjective T
    simp only [RingHom.id_apply]
    refine Eq.trans (coextSectionIso_apply X O' φ₀ L I U n p q hpq (r • t) g x) ?_
    refine Eq.trans (congrArg (invSecVal (coeffHom X O' φ₀).hom (I.X q).val (op W))
      ((sheafHomComplex (coeffSite X O') L
        ((coeffCoextendComplex X O' φ₀).obj I)).smul_natural U
          ((coeffHom X O' φ₀).hom.app (op U) r) n p q hpq t g x)) ?_
    refine Eq.trans (invSecVal_smul (coeffHom X O' φ₀).hom (I.X q).val (op W) _ _) ?_
    refine Eq.trans (congrArg
      (fun a => ((((AddCommGrpCat.Hom.hom
          (((sheafHomComplex (coeffSite X O') L
            ((coeffCoextendComplex X O' φ₀).obj I)).sectionsIso U).hom.f n) t).v
            p q hpq).val.app (op (Over.mk g))) x).app (op (Over.mk (𝟙 W))) a)
      (coeffHom_naturality_apply X O' φ₀ g r).symm) ?_
    refine Eq.trans (invSecVal_smul_left (coeffHom X O' φ₀).hom (I.X q).val (op W)
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op r) _) ?_
    refine Eq.trans (congrArg (fun z : (I.X q).val.obj (op W) ↦
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op r) • z)
      (coextSectionIso_apply X O' φ₀ L I U n p q hpq t g x).symm) ?_
    exact ((sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).smul_natural U r
      n p q hpq _ g x).symm

/-- **The comparison is compatible with restriction along an arrow of the site.** Both sides
evaluate a local section of the internal Hom complex at the composite arrow, so the equality is
the naturality of the two section descriptions. -/
theorem coextSectionLinearEquiv_natural (n : ℤ) {V U : X.C} (i : V ⟶ U)
    (t : ((((coeffRestrictComplex X O' φ₀).obj (sheafHomComplex (coeffSite X O') L
      ((coeffCoextendComplex X O' φ₀).obj I)).obj).X n).val.obj (op U))) :
    coextSectionLinearEquiv X O' φ₀ L I V n
        ((((coeffRestrictComplex X O' φ₀).obj (sheafHomComplex (coeffSite X O') L
          ((coeffCoextendComplex X O' φ₀).obj I)).obj).X n).val.map i.op t) =
      (((sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).obj.X n).val.map i.op)
        (coextSectionLinearEquiv X O' φ₀ L I U n t) := by
  apply sheafHomSection_ext (sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I) V n
  intro p q hpq T x
  obtain ⟨T⟩ := T
  obtain ⟨W, g, rfl⟩ := Over.mk_surjective T
  refine Eq.trans (coextSectionIso_apply X O' φ₀ L I V n p q hpq _ g x) ?_
  refine Eq.trans (congrArg (invSecVal (coeffHom X O' φ₀).hom (I.X q).val (op W))
    ((sheafHomComplex (coeffSite X O') L
      ((coeffCoextendComplex X O' φ₀).obj I)).restrict_natural i n p q hpq t g x).symm) ?_
  refine Eq.trans (coextSectionIso_apply X O' φ₀ L I U n p q hpq t (g ≫ i) x).symm ?_
  exact (sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).restrict_natural i
    n p q hpq _ g x

/-- The internal Hom complex over `𝒪'` of `L` and of `SheafHom_𝒪(𝒪', I)`, read as a complex of
sheaves of `𝒪`-modules. -/
abbrev coextSource :=
  (coeffRestrictComplex X O' φ₀).obj
    (sheafHomComplex (coeffSite X O') L ((coeffCoextendComplex X O' φ₀).obj I)).obj

/-- The internal Hom complex over `𝒪` of the restriction of `L` and of `I`. -/
abbrev coextTarget := (sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).obj

/-- The differential of a complex of sheaves of modules, read on the sections over an object,
is the differential of the section complex. -/
theorem sectionComplex_d_apply (Z : RingedSite.{u, u, u})
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (U : Z.C) (n m : ℤ)
    (t : (K.X n).val.obj (op U)) :
    AddCommGrpCat.Hom.hom ((sectionComplex Z K U).d n m) t =
      ((K.d n m).val.app (op U)).hom t :=
  rfl

/-- Restriction of scalars does not change the differential on sections. -/
theorem coeffRestrict_d_val_app
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O')) ℤ)
    (U : X.Cᵒᵖ)
    (n m : ℤ) (t : (M.X n).val.obj U) :
    ((((coeffRestrictComplex X O' φ₀).obj M).d n m).val.app U).hom t =
      ((M.d n m).val.app U).hom t :=
  rfl

/-- The section comparison, as a morphism of complexes of abelian groups.

This is a `def`, so that checking the comparison of internal Hom complexes against the
differential does not unfold the composite of four isomorphisms the comparison is built from. -/
def coextSectionComparison (U : X.C) :
    sectionComplex (coeffSite X O') (sheafHomComplex (coeffSite X O') L
        ((coeffCoextendComplex X O' φ₀).obj I)).obj U ⟶
      sectionComplex X (sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).obj U :=
  (coextSectionIso X O' φ₀ L I U).hom

/-- In each degree, `coextSectionComparison` is the corresponding component of
`coextSectionIso`. -/
theorem coextSectionComparison_f (U : X.C) (n : ℤ)
    (t : ((coextSource X O' φ₀ L I).X n).val.obj (op U)) :
    AddCommGrpCat.Hom.hom ((coextSectionComparison X O' φ₀ L I U).f n) t =
      AddCommGrpCat.Hom.hom ((coextSectionIso X O' φ₀ L I U).hom.f n) t :=
  rfl

/-- A family of morphisms of section complexes, one for each object of the site, commutes with
the differentials of the two complexes read on sections. -/
theorem sectionComparison_comm_apply (Z : RingedSite.{u, u, u})
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    (c : ∀ U : Z.C, sectionComplex Z K U ⟶ sectionComplex Z K' U)
    (U : Z.C) (n m : ℤ) (t : (K.X n).val.obj (op U)) :
    ((K'.d n m).val.app (op U)).hom (AddCommGrpCat.Hom.hom ((c U).f n) t) =
      AddCommGrpCat.Hom.hom ((c U).f m) (((K.d n m).val.app (op U)).hom t) :=
  (sectionComplex_d_apply Z K' U n m _).symm.trans
    ((ConcreteCategory.congr_hom ((c U).comm n m) t).trans
      (congrArg (AddCommGrpCat.Hom.hom ((c U).f m)) (sectionComplex_d_apply Z K U n m t)))

/-- The section comparison, read over the single ringed site `X`: restriction of scalars does
not change the section complex of a complex of sheaves of modules. -/
def coextSectionFamily (U : X.C) :
    sectionComplex X (coextSource X O' φ₀ L I) U ⟶
      sectionComplex X (coextTarget X O' φ₀ L I) U :=
  coextSectionComparison X O' φ₀ L I U

/-- The comparison in degree `n`, as a morphism of sheaves of modules: the section comparison on
every object of the site, which is linear by `coextSectionLinearEquiv` and natural by
`coextSectionLinearEquiv_natural`. -/
def coextHomComplexMapF (n : ℤ) :
    (coextSource X O' φ₀ L I).X n ⟶ (coextTarget X O' φ₀ L I).X n :=
  ⟨{ app U := ModuleCat.ofHom
      (X := ((coextSource X O' φ₀ L I).X n).val.obj U)
      (Y := ((coextTarget X O' φ₀ L I).X n).val.obj U)
      { toFun t := AddCommGrpCat.Hom.hom ((coextSectionFamily X O' φ₀ L I U.unop).f n) t
        map_add' := map_add _
        map_smul' r t := (coextSectionLinearEquiv X O' φ₀ L I U.unop n).map_smul r t }
     naturality {U V} i := by
      ext t
      exact coextSectionLinearEquiv_natural X O' φ₀ L I n i.unop t }⟩

/-- On sections over `U`, `coextHomComplexMapF` in degree `n` is the degree-`n` component of the
section comparison over `U`. -/
theorem coextHomComplexMapF_val_app (n : ℤ) (U : X.Cᵒᵖ)
    (t : ((coextSource X O' φ₀ L I).X n).val.obj U) :
    ((coextHomComplexMapF X O' φ₀ L I n).val.app U).hom t =
      AddCommGrpCat.Hom.hom ((coextSectionFamily X O' φ₀ L I U.unop).f n) t :=
  rfl

/-- **The comparison morphism of internal Hom complexes.** It commutes with the differential
because every section comparison is a morphism of complexes. -/
def coextHomComplexMap : coextSource X O' φ₀ L I ⟶ coextTarget X O' φ₀ L I where
  f n := coextHomComplexMapF X O' φ₀ L I n
  comm' n m _ := by
    ext U t
    exact sectionComparison_comm_apply X (coextSectionFamily X O' φ₀ L I) U.unop n m t

/-- On sections over each object, the degree-`n` comparison `coextHomComplexMapF` is an
isomorphism of modules. -/
instance isIso_coextHomComplexMapF_val_app (n : ℤ) (U : X.Cᵒᵖ) :
    IsIso ((coextHomComplexMapF X O' φ₀ L I n).val.app U) := by
  have h : (coextHomComplexMapF X O' φ₀ L I n).val.app U =
      (coextSectionLinearEquiv X O' φ₀ L I U.unop n).toModuleIso.hom := rfl
  rw [h]
  infer_instance

/-- The degree-`n` comparison `coextHomComplexMapF` is an isomorphism of presheaves of
modules. -/
instance isIso_coextHomComplexMapF_val (n : ℤ) :
    IsIso (coextHomComplexMapF X O' φ₀ L I n).val := by
  have h : (coextHomComplexMapF X O' φ₀ L I n).val =
      (PresheafOfModules.isoMk
        (fun U => asIso ((coextHomComplexMapF X O' φ₀ L I n).val.app U))
        (fun _ _ i => (coextHomComplexMapF X O' φ₀ L I n).val.naturality i)).hom := rfl
  rw [h]
  infer_instance

/-- The degree-`n` comparison `coextHomComplexMapF` is an isomorphism of sheaves of modules. -/
instance isIso_coextHomComplexMapF (n : ℤ) : IsIso (coextHomComplexMapF X O' φ₀ L I n) :=
  have : IsIso ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
      (coextHomComplexMapF X O' φ₀ L I n)) :=
    inferInstanceAs (IsIso (coextHomComplexMapF X O' φ₀ L I n).val)
  (SheafOfModules.fullyFaithfulForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).isIso_of_isIso_map
    (coextHomComplexMapF X O' φ₀ L I n)

/-- The comparison `coextHomComplexMap` of internal Hom complexes is an isomorphism of
complexes. -/
instance isIso_coextHomComplexMap : IsIso (coextHomComplexMap X O' φ₀ L I) := by
  have hn (n : ℤ) : IsIso ((coextHomComplexMap X O' φ₀ L I).f n) :=
    inferInstanceAs (IsIso (coextHomComplexMapF X O' φ₀ L I n))
  let := hn
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Stacks Tag 0996(2) at the complex level.** For a morphism `φ₀ : 𝒪 ⟶ 𝒪'` of sheaves of
commutative rings on a site, a complex `L` of sheaves of `𝒪'`-modules and a complex `I` of
sheaves of `𝒪`-modules, the internal Hom complex over `𝒪'` of `L` and of `SheafHom_𝒪(𝒪', I)`
is, as a complex of sheaves of `𝒪`-modules, the internal Hom complex over `𝒪` of the
restriction of `L` and of `I`. -/
def coextHomComplexIso : coextSource X O' φ₀ L I ≅ coextTarget X O' φ₀ L I :=
  asIso (coextHomComplexMap X O' φ₀ L I)

/-- **Stacks Tag 0996(2).** Let `(𝒞, 𝒪)` be a ringed site, let `φ₀ : 𝒪 ⟶ 𝒪'` be a morphism of
sheaves of commutative rings — for instance the localization `𝒪 ⟶ 𝒪_f` at a global section —
let `K ∈ D(𝒪)` and `L ∈ D(𝒪')`. Then

`R SheafHom_𝒪(L, K) = R SheafHom_{𝒪'}(L, R SheafHom_𝒪(𝒪', K))`.

Computing `K` by a K-injective complex `I` of sheaves of `𝒪`-modules, the right-hand side is
the internal Hom complex over `𝒪'` of `L` and of `SheafHom_𝒪(𝒪', I)` = `coeffCoextendComplex`
applied to `I`, the latter representing `R SheafHom_𝒪(𝒪', K)`; the left-hand side is the
internal Hom complex over `𝒪` of the restriction of scalars of `L` and of `I`. The
identification is of complexes of sheaves of `𝒪`-modules. -/
@[stacks 0996 "part (2)"]
def derivedSheafHom_coextendScalarsIso [I.IsKInjective] :
    DerivedCategory.Q.obj (sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).obj ≅
      DerivedCategory.Q.obj ((coeffRestrictComplex X O' φ₀).obj
        (sheafHomComplex (coeffSite X O') L ((coeffCoextendComplex X O' φ₀).obj I)).obj) :=
  DerivedCategory.Q.mapIso (coextHomComplexIso X O' φ₀ L I).symm

/-- The derived comparison of Tag 0996(2) is the image of the complex-level comparison. -/
theorem derivedSheafHom_coextendScalarsIso_eq [I.IsKInjective] :
    DerivedCategory.Q.mapIso (coextHomComplexIso X O' φ₀ L I).symm =
      derivedSheafHom_coextendScalarsIso X O' φ₀ L I :=
  rfl

/-- **The comparison of Tag 0996(2) is the canonical one.** On a local section it evaluates each
local component of a cochain — a local morphism `𝒪'|_W ⟶ I|_W` — at the unit section, so it is
not merely some isomorphism between the two complexes. -/
@[stacks 0996 "part (2)"]
theorem coextHomComplexIso_hom_apply (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (t : ((coextSource X O' φ₀ L I).X n).val.obj (op U))
    {W : X.C} (g : W ⟶ U) (x : (L.X p).val.obj (op W)) :
    (((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X ((coeffRestrictComplex X O' φ₀).obj L) I).sectionsIso U).hom.f n)
        ((((coextHomComplexIso X O' φ₀ L I).hom.f n).val.app (op U)).hom t)).v
          p q hpq).val.app (op (Over.mk g))) x =
      invSecVal (coeffHom X O' φ₀).hom (I.X q).val (op W)
        ((((AddCommGrpCat.Hom.hom
          (((sheafHomComplex (coeffSite X O') L
            ((coeffCoextendComplex X O' φ₀).obj I)).sectionsIso U).hom.f n) t).v
            p q hpq).val.app (op (Over.mk g))) x) :=
  coextSectionIso_apply X O' φ₀ L I U n p q hpq t g x

/-- **Stacks Tag 093Z**, in the coextension-of-scalars spelling: `SheafHom_𝒪(𝒪', I)` is a
K-injective complex of sheaves of `𝒪'`-modules whenever `I` is a K-injective complex of sheaves
of `𝒪`-modules.

The criterion is Stacks Tag 08BJ — `CochainComplex.isKInjective_mapHomologicalComplex_of_exact`
— applied to the adjunction of Tag 0932, whose left adjoint is restriction of scalars along
`φ₀`, and that is exact. Nothing is assumed of `φ₀`. -/
instance isKInjective_coeffCoextendComplex [I.IsKInjective] :
    CochainComplex.IsKInjective ((coeffCoextendComplex X O' φ₀).obj I) :=
  letI : (coeffCoextend X O' φ₀).Additive :=
    (restrictScalars_coextendScalars_adjunction (coeffHom X O' φ₀)).right_adjoint_additive
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (coeffCoextend X O' φ₀) (coeffRestrict X O' φ₀)
    (restrictScalars_coextendScalars_adjunction (coeffHom X O' φ₀)) I

/-- For an epimorphism of sheaves of commutative rings, restriction of scalars is fully
faithful — Stacks Tag 0930, in the form
`AlgebraicGeometry.RingedSite.restrictScalars_fullyFaithful_of_epi` — so the unit of the
adjunction of Tag 0932 is an isomorphism.

The hypothesis is epimorphy of `φ₀` in the category of sheaves of
commutative rings, which is the category Tag 0996 localizes in, and is weaker than epimorphy of
`coeffHom X O' φ₀` in sheaves of not necessarily commutative rings. -/
theorem isIso_coextUnit [Epi φ₀]
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    IsIso ((restrictScalars_coextendScalars_adjunction (coeffHom X O' φ₀)).unit.app G) := by
  obtain ⟨hff⟩ : Nonempty
      (SheafOfModules.restrictScalars.{u} (coeffHom X O' φ₀)).FullyFaithful :=
    restrictScalars_fullyFaithful_of_epi φ₀
  have := hff.full
  have := hff.faithful
  infer_instance

/-- **The "in particular" of Stacks Tag 0996(2), at the complex level.** When `φ₀` is an
epimorphism of sheaves of commutative rings — as the localization `𝒪 ⟶ 𝒪_f` at a global section
is, by `AlgebraicGeometry.RingedSite.epi_toAwaySheaf` —
coextension of scalars is idempotent:
`SheafHom_𝒪(𝒪', SheafHom_𝒪(𝒪', I)) = SheafHom_𝒪(𝒪', I)`. The comparison is the unit of Tag
0932, which is an isomorphism because its left adjoint is fully faithful. -/
def coextIdempotentComplexIso [Epi φ₀] :
    (coeffCoextendComplex X O' φ₀).obj I ≅
      (coeffCoextendComplex X O' φ₀).obj ((coeffRestrictComplex X O' φ₀).obj
        ((coeffCoextendComplex X O' φ₀).obj I)) :=
  have _h := isIso_coextUnit X O' φ₀
  HomologicalComplex.Hom.isoOfComponents
    (fun n => asIso ((restrictScalars_coextendScalars_adjunction (coeffHom X O' φ₀)).unit.app
      ((coeffCoextend X O' φ₀).obj (I.X n))))
    (fun n m _ => ((restrictScalars_coextendScalars_adjunction (coeffHom X O' φ₀)).unit.naturality
      ((coeffCoextend X O' φ₀).map (I.d n m))).symm)

/-- `R SheafHom_𝒪(𝒪', R SheafHom_𝒪(𝒪', K)) = R SheafHom_𝒪(𝒪', K)` for an epimorphism
`φ₀ : 𝒪 ⟶ 𝒪'` of sheaves of commutative rings. The inner `R SheafHom_𝒪(𝒪', K)` is the
coextension of a K-injective representative `I` of `K`.

This is the general statement, for an arbitrary `φ₀` that is *assumed* to be an epimorphism. The
"in particular" of [Stacks, Tag 0996(2)] is the case `φ₀ = (𝒪 ⟶ 𝒪_f)` of it, where epimorphy is
a theorem rather than an assumption; that case is
`AlgebraicGeometry.RingedSite.derivedSheafHom_awayCoextendScalars_idempotent`, and it is where
the tag is registered. -/
def derivedSheafHom_coextendScalars_idempotent [Epi φ₀] [I.IsKInjective] :
    DerivedCategory.Q.obj ((coeffCoextendComplex X O' φ₀).obj I) ≅
      DerivedCategory.Q.obj ((coeffCoextendComplex X O' φ₀).obj
        ((coeffRestrictComplex X O' φ₀).obj ((coeffCoextendComplex X O' φ₀).obj I))) :=
  DerivedCategory.Q.mapIso (coextIdempotentComplexIso X O' φ₀ I)

end AlgebraicGeometry.RingedSite

end

module

public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto

/-!
# Mayer--Vietoris over an ambient open subset

Let `X` be a topological space, `O` a sheaf of rings on `X`, and let `U`, `V` be two opens
contained in a third open `W` with `U ⊔ V = W`.  For every sheaf of `O`-modules `F` this file
produces the long exact sequence

`0 ⟶ H⁰(W,F) ⟶ H⁰(U,F) ⊞ H⁰(V,F) ⟶ H⁰(U ⊓ V,F) ⟶ H¹(W,F) ⟶ H¹(U,F) ⊞ H¹(V,F) ⟶ ⋯`

in the cohomology `Hgroup` of `StacksDraft.Ch20.Sec7.Tag01E3`, with all three maps natural in
`F` and with the two non-connecting maps being the restriction maps `HrestrictNT` on the nose.

For `W = ⊤` the statement is Stacks 01EB, which
`Stacks.Cohomology.AbsoluteMayerVietoris.mayerVietoris_exact` already proves: the terms agree,
and `ambientFirst_eq` and `Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq` give the two
non-connecting maps the same `HrestrictNT` spelling that theorem has.  The two *connecting* maps
are built from different short complexes of functors, and nothing here compares them.

The ambient open is genuinely more general, because a cover `U ⊔ V = W` of a proper open subset
need not be the restriction to `W` of a cover of `X`: for `X = ℝ`, `W = ℝ \ {0}`, `U = (-∞,0)`
and `V = (0,∞)`, any open `U'` of `X` with `U' ⊓ W = U` is contained in `U` — it cannot contain
`0`, since an open set containing `0` meets `(0,∞) ⊆ W` — and likewise `V' ≤ V`, so no cover of
`X` restricts to this cover of `W`.

## Main definitions

* `Stacks.Cohomology.AmbientMayerVietoris.ambientToCover` and
  `Stacks.Cohomology.AmbientMayerVietoris.ambientToIntersection`: the two maps of the
  Mayer--Vietoris short complex of sections functors over the ambient open, the pair of the
  restrictions `Γ(W,-) ⟶ Γ(U,-) ⊞ Γ(V,-)` and the difference of the two restrictions
  `Γ(U,-) ⊞ Γ(V,-) ⟶ Γ(U ⊓ V,-)`.
* `Stacks.Cohomology.AmbientMayerVietoris.ambientFirst`,
  `Stacks.Cohomology.AmbientMayerVietoris.ambientSecond` and
  `Stacks.Cohomology.AmbientMayerVietoris.ambientDelta`: the three maps of the long exact
  sequence, as natural transformations between the cohomology functors `Hfunctor`.

## Main results

* `Stacks.Cohomology.AmbientMayerVietoris.ambientShortExact_on_injectives`: the Mayer--Vietoris
  short complex of sections functors over `W` is short exact at every injective sheaf of
  modules.  Its three halves are the two halves of the sheaf condition for the cover
  `U ⊔ V = W` and the surjectivity of the restriction maps of an injective sheaf of modules
  (Stacks 01EA).
* `Stacks.Cohomology.AmbientMayerVietoris.mayerVietorisAmbient_exact` and
  `Stacks.Cohomology.AmbientMayerVietoris.mono_ambientFirst_zero`: **the long exact sequence.**
* `Stacks.Cohomology.AmbientMayerVietoris.mayerVietorisAmbient_exact_four` and
  `Stacks.Cohomology.AmbientMayerVietoris.mayerVietorisAmbient_exact_four_delta`: the two
  four-arrow windows of the sequence, as `Exact` objects of `ComposableArrows _ 4`, which is
  the shape the five lemma `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`
  consumes.  The middle object of the first is `Hᵖ(U ⊓ V,F)` and of the second is
  `Hᵖ⁺¹(W,F)`.
* `Stacks.Cohomology.AmbientMayerVietoris.ambientFirst_eq` and
  `Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq`: the first map is the pair of
  restrictions `Hⁿ(W,-) ⟶ Hⁿ(U,-) ⊞ Hⁿ(V,-)` and the second is the difference of the two
  restrictions to `U ⊓ V`, both spelled with `HrestrictNT`.
* `Stacks.Cohomology.AmbientMayerVietoris.isIso_ambient_of_chase` and
  `Stacks.Cohomology.AmbientMayerVietoris.isIso_ambient_of_isIso_on_cover`: **the five-lemma
  chase, run.**  A morphism `φ : F ⟶ G` inducing isomorphisms on `Hᵖ(U,-)`, `Hᵖ(V,-)` and
  `Hᵖ(U ⊓ V,-)` in two consecutive degrees induces one on `Hⁿ⁺¹(W,-)`.

## Implementation notes

The construction follows the proof of Stacks 01EB, with the ambient open in place of `X`: the
sheaf condition for the cover `U ⊔ V = W` gives exactness of
`Γ(W,F) ⟶ Γ(U,F) ⊞ Γ(V,F) ⟶ Γ(U ⊓ V,F)` for any sheaf of modules, Stacks 01EA makes the second
map surjective when the sheaf is injective, and the long exact sequence is then
`CategoryTheory.rightDerivedDelta` together with
`CategoryTheory.exact_rightDerived_composableArrows₅`, taken in that form so that the
connecting map is a named natural transformation rather than an existential witness.

Because the terms of the short complex are the sections functors `secF O U` themselves, and not
the sections over `W` of a restricted module, no identification of the terms is needed: the
middle term of the derived sequence is split by `CategoryTheory.Functor.rightDerivedBiprodIso`
and the outer two terms are `Hfunctor` on the nose.  In particular no `eqToHom` occurs anywhere
in this file, and `ambientFirst_eq`/`Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq` are
`biprod` bookkeeping.

All three maps of the sequence are natural transformations, so a morphism `φ : F ⟶ G` of sheaves
of modules induces a morphism of the two sequences with no further work, by
`CategoryTheory.NatTrans.naturality`.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ExtensionByZeroModules
open Stacks.Cohomology.RestrictionCover
open Stacks.Cohomology.AbsoluteMayerVietoris

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Cohomology.AmbientMayerVietoris

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

/-! ### Binary biproducts of functors, evaluated at an object -/

section Biproducts

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable (G₁ G₂ : C ⥤ D) [HasBinaryBiproduct G₁ G₂]

/-- The first inclusion followed by the first projection, evaluated at an object. -/
public theorem biprod_inl_fst_app (M : C) : (biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app M ≫
    (biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app M = 𝟙 _ := by
  rw [← NatTrans.comp_app, biprod.inl_fst, NatTrans.id_app]

/-- The first inclusion followed by the second projection, evaluated at an object. -/
public theorem biprod_inl_snd_app (M : C) : (biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app M ≫
    (biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app M = 0 := by
  rw [← NatTrans.comp_app, biprod.inl_snd, NatTrans.app_zero]

/-- The second inclusion followed by the first projection, evaluated at an object. -/
public theorem biprod_inr_fst_app (M : C) : (biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app M ≫
    (biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app M = 0 := by
  rw [← NatTrans.comp_app, biprod.inr_fst, NatTrans.app_zero]

/-- The second inclusion followed by the second projection, evaluated at an object. -/
public theorem biprod_inr_snd_app (M : C) : (biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app M ≫
    (biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app M = 𝟙 _ := by
  rw [← NatTrans.comp_app, biprod.inr_snd, NatTrans.id_app]

/-- `CategoryTheory.Limits.biprod.total` for a biproduct of two functors, evaluated at an
object. -/
public theorem biprod_total_app (M : C) :
    (biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app M ≫ (biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app M +
      (biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app M ≫ (biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app M = 𝟙 _ := by
  have h := NatTrans.congr_app (biprod.total (X := G₁) (Y := G₂)) M
  simpa only [NatTrans.comp_app, NatTrans.app_add, NatTrans.id_app] using h

/-- **A biproduct of two functors inverts a morphism as soon as both summands do.**  The
inverse is the diagonal matrix of the two inverses, and both triangle identities are diagonal
matrix computations through `CategoryTheory.Functor.biprod_map_eq`. -/
public theorem isIso_biprod_map {A B : C} (φ : A ⟶ B)
    (h₁ : IsIso (G₁.map φ)) (h₂ : IsIso (G₂.map φ)) : IsIso ((G₁ ⊞ G₂).map φ) := by
  have _ := h₁
  have _ := h₂
  refine ⟨(biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app B ≫ inv (G₁.map φ) ≫
      (biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app A +
    (biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app B ≫ inv (G₂.map φ) ≫
      (biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app A, ?_, ?_⟩
  all_goals
    rw [Functor.biprod_map_eq]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      reassoc_of% biprod_inl_fst_app G₁ G₂, reassoc_of% biprod_inl_snd_app G₁ G₂,
      reassoc_of% biprod_inr_fst_app G₁ G₂, reassoc_of% biprod_inr_snd_app G₁ G₂,
      zero_comp, comp_zero, add_zero, zero_add, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc]
    apply biprod_total_app

end Biproducts

/-- An element of a binary biproduct of two functors into abelian groups, evaluated at an
object, is the sum of its two components.  This is `biprod_total_app` read on elements. -/
public theorem app_biprod_total {A : Type u₁} [Category.{v₁} A]
    (R S : A ⥤ AddCommGrpCat.{u}) (M : A)
    (x : (((R ⊞ S).obj M : AddCommGrpCat.{u}) : Type u)) :
    (biprod.inl : R ⟶ R ⊞ S).app M ((biprod.fst : R ⊞ S ⟶ R).app M x)
      + (biprod.inr : S ⟶ R ⊞ S).app M ((biprod.snd : R ⊞ S ⟶ S).app M x) = x := by
  have h := congrArg (fun (f : ((R ⊞ S).obj M : AddCommGrpCat.{u}) ⟶ _) => f x)
    (biprod_total_app R S M)
  simp only [AddCommGrpCat.hom_add, AddMonoidHom.add_apply] at h
  simpa [AddCommGrpCat.comp_apply] using h

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Restriction of sections is transitive: `Γ(W,-) ⟶ Γ(U,-) ⟶ Γ(T,-)` is `Γ(W,-) ⟶ Γ(T,-)`,
because `sheafSections` is a functor in the open. -/
public theorem secRestrict_comp {T U W : Opens X} (h₁ : U ≤ W) (h₂ : T ≤ U) :
    secRestrict O h₁ ≫ secRestrict O h₂ = secRestrict O (h₂.trans h₁) := by
  dsimp [secRestrict]
  rw [← Functor.whiskerLeft_comp]
  congr 1
  rw [← Functor.map_comp]
  congr 1

/-! ### The Mayer--Vietoris short complex of sections functors over an ambient open -/

/-- The first map of the Mayer--Vietoris short complex over the ambient open `W`: the pair of
the restrictions to the two members of the cover. -/
public def ambientToCover (W U V : Opens X) (hU : U ≤ W) (hV : V ≤ W) :
    secF O W ⟶ secF O U ⊞ secF O V :=
  biprod.lift (secRestrict O hU) (secRestrict O hV)

/-- The second map of the Mayer--Vietoris short complex: the difference of the two restrictions
to the intersection. -/
public def ambientToIntersection (U V : Opens X) :
    secF O U ⊞ secF O V ⟶ secF O (U ⊓ V) :=
  biprod.desc (secRestrict O (inf_le_left : U ⊓ V ≤ U))
    (-secRestrict O (inf_le_right : U ⊓ V ≤ V))

/-- The two maps of the short complex compose to zero: restricting from `W` to `U` and then to
`U ⊓ V` is restricting to `U ⊓ V`, as is the same through `V`, so their difference vanishes. -/
public theorem ambientToCover_comp_ambientToIntersection (W U V : Opens X) (hU : U ≤ W)
    (hV : V ≤ W) :
    ambientToCover O W U V hU hV ≫ ambientToIntersection O U V = 0 := by
  dsimp only [ambientToCover, ambientToIntersection]
  rw [biprod.lift_desc, Preadditive.comp_neg, secRestrict_comp, secRestrict_comp,
    add_neg_cancel]

section Exactness

variable (W U V : Opens X) (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W)
  (M : SheafOfModules.{u} O)

/-- The sections of a sheaf of `O`-modules as a presheaf of types, which is the shape in which
the sheaf condition for the Mayer--Vietoris square of two opens is available. -/
public abbrev sectionsPresheaf : TopCat.Presheaf (Type u) X :=
  ((SheafOfModules.toSheaf O).obj M).obj ⋙ forget AddCommGrpCat.{u}

/-- The sections of a sheaf of `O`-modules form a sheaf of types. -/
public theorem sectionsPresheaf_isSheaf : (sectionsPresheaf O M).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u}) _).mp
    ((SheafOfModules.toSheaf O).obj M).property

/-- The first component of `ambientToCover` is the restriction `Γ(W,-) ⟶ Γ(U,-)`. -/
public theorem ambientToCover_comp_fst :
    (ambientToCover O W U V hU hV).app M ≫
        (biprod.fst : secF O U ⊞ secF O V ⟶ secF O U).app M =
      (secRestrict O hU).app M := by
  rw [← NatTrans.comp_app]
  congr 1
  exact biprod.lift_fst _ _

/-- The second component of `ambientToCover` is the restriction `Γ(W,-) ⟶ Γ(V,-)`. -/
public theorem ambientToCover_comp_snd :
    (ambientToCover O W U V hU hV).app M ≫
        (biprod.snd : secF O U ⊞ secF O V ⟶ secF O V).app M =
      (secRestrict O hV).app M := by
  rw [← NatTrans.comp_app]
  congr 1
  exact biprod.lift_snd _ _

/-- The restriction of `ambientToIntersection` to the `U`-summand is the restriction map
`Γ(U,-) ⟶ Γ(U ⊓ V,-)`. -/
public theorem inl_comp_ambientToIntersection :
    (biprod.inl : secF O U ⟶ secF O U ⊞ secF O V).app M ≫
        (ambientToIntersection O U V).app M =
      (secRestrict O (inf_le_left : U ⊓ V ≤ U)).app M := by
  rw [← NatTrans.comp_app]
  congr 1
  exact biprod.inl_desc _ _

/-- The restriction of `ambientToIntersection` to the `V`-summand is minus the restriction map
`Γ(V,-) ⟶ Γ(U ⊓ V,-)`. -/
public theorem inr_comp_ambientToIntersection :
    (biprod.inr : secF O V ⟶ secF O U ⊞ secF O V).app M ≫
        (ambientToIntersection O U V).app M =
      -(secRestrict O (inf_le_right : U ⊓ V ≤ V)).app M := by
  rw [← NatTrans.comp_app]
  rw [show (biprod.inr : secF O V ⟶ secF O U ⊞ secF O V) ≫ ambientToIntersection O U V =
    -secRestrict O (inf_le_right : U ⊓ V ≤ V) from biprod.inr_desc _ _]
  simp

include hUV in
/-- **The first map of the Mayer--Vietoris short complex is a monomorphism**: a section over
`W` which restricts to zero on `U` and on `V` is zero, since `U` and `V` cover `W`. -/
public theorem mono_ambientToCover_app : Mono ((ambientToCover O W U V hU hV).app M) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro x y hxy
  have h₁ : (secRestrict O hU).app M x = (secRestrict O hU).app M y := by
    rw [← ambientToCover_comp_fst O W U V hU hV M, AddCommGrpCat.comp_apply,
      AddCommGrpCat.comp_apply, hxy]
  have h₂ : (secRestrict O hV).app M x = (secRestrict O hV).app M y := by
    rw [← ambientToCover_comp_snd O W U V hU hV M, AddCommGrpCat.comp_apply,
      AddCommGrpCat.comp_apply, hxy]
  exact sheafSections_ext_cover (sectionsPresheaf O M) (sectionsPresheaf_isSheaf O M)
    U V W hUV x y h₁ h₂

include hUV in
/-- **The Mayer--Vietoris short complex is exact in the middle**: a pair of sections over `U`
and `V` whose restrictions to `U ⊓ V` agree glues to a section over `W`. -/
public theorem exact_ambientShortComplex_app :
    (NatTrans.appShortComplex (ambientToCover O W U V hU hV) (ambientToIntersection O U V)
      (ambientToCover_comp_ambientToIntersection O W U V hU hV) M).Exact := by
  apply (ShortComplex.ab_exact_iff _).2
  intro x hx
  have hx' : (ambientToIntersection O U V).app M x = 0 := hx
  set a := (biprod.fst : secF O U ⊞ secF O V ⟶ secF O U).app M x with ha
  set b := (biprod.snd : secF O U ⊞ secF O V ⟶ secF O V).app M x with hb
  have hrep : (biprod.inl : secF O U ⟶ secF O U ⊞ secF O V).app M a
      + (biprod.inr : secF O V ⟶ secF O U ⊞ secF O V).app M b = x :=
    app_biprod_total (secF O U) (secF O V) M x
  rw [← hrep, map_add, ← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply,
    inl_comp_ambientToIntersection O U V M, inr_comp_ambientToIntersection O U V M] at hx'
  simp only [AddCommGrpCat.hom_neg, AddMonoidHom.neg_apply] at hx'
  have hcompat : (secRestrict O (inf_le_left : U ⊓ V ≤ U)).app M a =
      (secRestrict O (inf_le_right : U ⊓ V ≤ V)).app M b := add_neg_eq_zero.mp hx'
  obtain ⟨s, hsU, hsV⟩ := sheafSections_glue_cover (sectionsPresheaf O M)
    (sectionsPresheaf_isSheaf O M) U V W hUV a b hcompat
  refine ⟨s, ?_⟩
  show (ambientToCover O W U V hU hV).app M s = x
  have hfst : (biprod.fst : secF O U ⊞ secF O V ⟶ secF O U).app M
      ((ambientToCover O W U V hU hV).app M s) = a := by
    rw [← AddCommGrpCat.comp_apply, ambientToCover_comp_fst]
    exact hsU
  have hsnd : (biprod.snd : secF O U ⊞ secF O V ⟶ secF O V).app M
      ((ambientToCover O W U V hU hV).app M s) = b := by
    rw [← AddCommGrpCat.comp_apply, ambientToCover_comp_snd]
    exact hsV
  have htot := app_biprod_total (secF O U) (secF O V) M
    ((ambientToCover O W U V hU hV).app M s)
  rw [hfst, hsnd] at htot
  exact htot.symm.trans hrep

/-- **The second map of the Mayer--Vietoris short complex is an epimorphism at an injective
sheaf of modules**: the restriction map `Γ(U,I) ⟶ Γ(U ⊓ V,I)` is already surjective, by
Stacks 01EA. -/
public theorem epi_ambientToIntersection_app (hM : Injective M) :
    Epi ((ambientToIntersection O U V).app M) := by
  have : Injective M := hM
  rw [AddCommGrpCat.epi_iff_surjective]
  intro z
  obtain ⟨y, hy⟩ := Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
    O M (inf_le_left : U ⊓ V ≤ U) z
  refine ⟨(biprod.inl : secF O U ⟶ secF O U ⊞ secF O V).app M y, ?_⟩
  show ((biprod.inl : secF O U ⟶ secF O U ⊞ secF O V).app M ≫
    (ambientToIntersection O U V).app M) y = z
  rw [inl_comp_ambientToIntersection O U V M]
  exact hy

include hUV in
/-- **The Mayer--Vietoris short complex of sections functors over the ambient open `W` is short
exact at every injective sheaf of modules.** -/
public theorem ambientShortExact_on_injectives (hM : Injective M) :
    (NatTrans.appShortComplex (ambientToCover O W U V hU hV) (ambientToIntersection O U V)
      (ambientToCover_comp_ambientToIntersection O W U V hU hV) M).ShortExact :=
  ShortComplex.ShortExact.mk' (exact_ambientShortComplex_app O W U V hU hV hUV M)
    (mono_ambientToCover_app O W U V hU hV hUV M)
    (epi_ambientToIntersection_app O U V M hM)

end Exactness

/-! ### The Mayer--Vietoris long exact sequence over an ambient open -/

section Hgroup

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]
variable (W U V : Opens X) (hU : U ≤ W) (hV : V ≤ W)

/-- **The first map of the Mayer--Vietoris sequence**, `Hⁿ(W,-) ⟶ Hⁿ(U,-) ⊞ Hⁿ(V,-)`. -/
public def ambientFirst (n : ℕ) : Hfunctor O W n ⟶ Hfunctor O U n ⊞ Hfunctor O V n :=
  NatTrans.rightDerived (ambientToCover O W U V hU hV) n ≫
    (Functor.rightDerivedBiprodIso (secF O U) (secF O V) n).hom

/-- The biproduct comparison followed by the derived difference map is the pair of restrictions
to the intersection. It is stated directly about the composite so that
`Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond` can serve as the second map of the sequence. -/
private theorem biprodIso_inv_comp_rightDerived_ambientToIntersection (n : ℕ) :
    (Functor.rightDerivedBiprodIso (secF O U) (secF O V) n).inv ≫
        NatTrans.rightDerived (ambientToIntersection O U V) n =
      biprod.desc (HrestrictNT O (inf_le_left : U ⊓ V ≤ U) n)
        (-HrestrictNT O (inf_le_right : U ⊓ V ≤ V) n) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.inl_desc, Functor.rightDerivedBiprodIso_inv, ← Category.assoc, biprod.inl_desc,
      ← NatTrans.rightDerived_comp]
    dsimp only [ambientToIntersection]
    rw [biprod.inl_desc]
    rfl
  · rw [biprod.inr_desc, Functor.rightDerivedBiprodIso_inv, ← Category.assoc, biprod.inr_desc,
      ← NatTrans.rightDerived_comp]
    dsimp only [ambientToIntersection]
    rw [biprod.inr_desc, natTrans_rightDerived_neg]
    rfl

/-- The derived difference map factors through `mvSecond`. This replaces the definitional
unfolding of the deleted `Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond`. -/
private theorem rightDerived_ambientToIntersection_eq (n : ℕ) :
    NatTrans.rightDerived (ambientToIntersection O U V) n =
      (Functor.rightDerivedBiprodIso (secF O U) (secF O V) n).hom ≫
        Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V n := by
  rw [Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq,
    ← biprodIso_inv_comp_rightDerived_ambientToIntersection, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- **The first map of the Mayer--Vietoris sequence is the pair of the two restriction
maps.** -/
public theorem ambientFirst_eq (n : ℕ) :
    ambientFirst O W U V hU hV n = biprod.lift (HrestrictNT O hU n) (HrestrictNT O hV n) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp only [ambientFirst, ambientToCover, Category.assoc, Functor.rightDerivedBiprodIso_hom,
      biprod.lift_fst, biprod.lift_snd, ← NatTrans.rightDerived_comp] <;> rfl

variable (hUV : U ⊔ V = W)

include hUV

/-- **The connecting map of the Mayer--Vietoris sequence**,
`Hⁿ(U ⊓ V,-) ⟶ Hⁿ⁺¹(W,-)`. -/
public def ambientDelta (n : ℕ) : Hfunctor O (U ⊓ V) n ⟶ Hfunctor O W (n + 1) :=
  CategoryTheory.rightDerivedDelta (ambientToCover O W U V hU hV)
    (ambientToIntersection O U V) (ambientToCover_comp_ambientToIntersection O W U V hU hV)
    (fun M hM => ambientShortExact_on_injectives O W U V hU hV hUV M hM) n

/-- **Mayer--Vietoris over an ambient open subset.**  For `U ⊔ V = W` every six-term window
`Hⁿ(W,F) ⟶ Hⁿ(U,F) ⊞ Hⁿ(V,F) ⟶ Hⁿ(U ⊓ V,F) ⟶ Hⁿ⁺¹(W,F) ⟶ Hⁿ⁺¹(U,F) ⊞ Hⁿ⁺¹(V,F) ⟶
Hⁿ⁺¹(U ⊓ V,F)` is exact.  The two outer maps are the restriction maps, by `ambientFirst_eq`
and `Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq`.  For `W = ⊤` the statement is
Stacks 01EB. -/
public theorem mayerVietorisAmbient_exact (n : ℕ) (F : SheafOfModules.{u} O) :
    (ComposableArrows.mk₅ ((ambientFirst O W U V hU hV n).app F)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V n).app F)
      ((ambientDelta O W U V hU hV hUV n).app F)
      ((ambientFirst O W U V hU hV (n + 1)).app F)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V (n + 1)).app F)).Exact := by
  have hraw := CategoryTheory.exact_rightDerived_composableArrows₅
      (ambientToCover O W U V hU hV) (ambientToIntersection O U V)
      (ambientToCover_comp_ambientToIntersection O W U V hU hV)
      (fun M hM => ambientShortExact_on_injectives O W U V hU hV hUV M hM)
      (injectiveResolution F) n
  refine ComposableArrows.exact_of_iso ?_ hraw
  refine ComposableArrows.isoMk₅ (Iso.refl _)
    ((Functor.rightDerivedBiprodIso (secF O U) (secF O V) n).app F) (Iso.refl _)
    (Iso.refl _) ((Functor.rightDerivedBiprodIso (secF O U) (secF O V) (n + 1)).app F)
    (Iso.refl _) ?_ ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · refine (Category.comp_id _).trans ?_
    rw [rightDerived_ambientToIntersection_eq O U V n]
    rfl
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · refine (Category.comp_id _).trans ?_
    rw [rightDerived_ambientToIntersection_eq O U V (n + 1)]
    rfl

/-- **The four-arrow window whose middle object is `Hⁿ(U ⊓ V,F)`**, extracted from the
Mayer--Vietoris sequence over `W`: the row
`Hⁿ(W,F) ⟶ Hⁿ(U,F) ⊞ Hⁿ(V,F) ⟶ Hⁿ(U ⊓ V,F) ⟶ Hⁿ⁺¹(W,F) ⟶ Hⁿ⁺¹(U,F) ⊞ Hⁿ⁺¹(V,F)` is exact as a
`CategoryTheory.ComposableArrows _ 4`, which is the shape
`CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono` (Stacks 05QB) takes. -/
public theorem mayerVietorisAmbient_exact_four (n : ℕ) (F : SheafOfModules.{u} O) :
    (ComposableArrows.mk₅ ((ambientFirst O W U V hU hV n).app F)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V n).app F)
      ((ambientDelta O W U V hU hV hUV n).app F)
      ((ambientFirst O W U V hU hV (n + 1)).app F)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V (n + 1)).app F)).δlast.Exact :=
  ((ComposableArrows.exact_iff_δlast _).1
    (mayerVietorisAmbient_exact O W U V hU hV hUV n F)).1

/-- **The four-arrow window whose middle object is `Hⁿ⁺¹(W,F)`**, extracted from the
Mayer--Vietoris sequence over `W`: the row
`Hⁿ(U,F) ⊞ Hⁿ(V,F) ⟶ Hⁿ(U ⊓ V,F) ⟶ Hⁿ⁺¹(W,F) ⟶ Hⁿ⁺¹(U,F) ⊞ Hⁿ⁺¹(V,F) ⟶ Hⁿ⁺¹(U ⊓ V,F)` is
exact as a `CategoryTheory.ComposableArrows _ 4`.  This is the window in which a five-lemma
chase controls the cohomology of the ambient open `W` from that of `U`, `V` and `U ⊓ V`. -/
public theorem mayerVietorisAmbient_exact_four_delta (n : ℕ) (F : SheafOfModules.{u} O) :
    (ComposableArrows.mk₅ ((ambientFirst O W U V hU hV n).app F)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V n).app F)
      ((ambientDelta O W U V hU hV hUV n).app F)
      ((ambientFirst O W U V hU hV (n + 1)).app F)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V (n + 1)).app F)).δ₀.Exact :=
  ((ComposableArrows.exact_iff_δ₀ _).1
    (mayerVietorisAmbient_exact O W U V hU hV hUV n F)).2

/-- **The Mayer--Vietoris sequence over `W` starts with a zero**: the pair of restriction maps
`H⁰(W,F) ⟶ H⁰(U,F) ⊞ H⁰(V,F)` is a monomorphism. -/
public theorem mono_ambientFirst_zero (F : SheafOfModules.{u} O) :
    Mono ((ambientFirst O W U V hU hV 0).app F) := by
  have h₁ : Mono ((NatTrans.rightDerived (ambientToCover O W U V hU hV) 0).app F) :=
    CategoryTheory.mono_rightDerived_zero_app (ambientToCover O W U V hU hV)
      (ambientToIntersection O U V)
      (ambientToCover_comp_ambientToIntersection O W U V hU hV)
      (fun M hM => ambientShortExact_on_injectives O W U V hU hV hUV M hM) F
  have h₂ : IsIso ((Functor.rightDerivedBiprodIso (secF O U) (secF O V) 0).hom.app F) :=
    inferInstanceAs
      (IsIso ((Functor.rightDerivedBiprodIso (secF O U) (secF O V) 0).app F).hom)
  show Mono ((NatTrans.rightDerived (ambientToCover O W U V hU hV) 0).app F ≫
    (Functor.rightDerivedBiprodIso (secF O U) (secF O V) 0).hom.app F)
  infer_instance

/-! ### The five-lemma chase on the ambient open -/

/-- **The morphism of Mayer--Vietoris windows induced by a morphism of sheaves of modules.**
All three maps of the sequence are natural transformations, so every square commutes by
`CategoryTheory.NatTrans.naturality`. -/
public def mayerVietorisAmbientHom (n : ℕ) {F G : SheafOfModules.{u} O} (φ : F ⟶ G) :
    (ComposableArrows.mk₅ ((ambientFirst O W U V hU hV n).app F)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V n).app F)
      ((ambientDelta O W U V hU hV hUV n).app F)
      ((ambientFirst O W U V hU hV (n + 1)).app F)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V (n + 1)).app F)) ⟶
    (ComposableArrows.mk₅ ((ambientFirst O W U V hU hV n).app G)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V n).app G)
      ((ambientDelta O W U V hU hV hUV n).app G)
      ((ambientFirst O W U V hU hV (n + 1)).app G)
      ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V (n + 1)).app G)) :=
  ComposableArrows.homMk₅ ((Hfunctor O W n).map φ)
    ((Hfunctor O U n ⊞ Hfunctor O V n).map φ) ((Hfunctor O (U ⊓ V) n).map φ)
    ((Hfunctor O W (n + 1)).map φ)
    ((Hfunctor O U (n + 1) ⊞ Hfunctor O V (n + 1)).map φ)
    ((Hfunctor O (U ⊓ V) (n + 1)).map φ)
    ((ambientFirst O W U V hU hV n).naturality φ).symm
    ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V n).naturality φ).symm
    ((ambientDelta O W U V hU hV hUV n).naturality φ).symm
    ((ambientFirst O W U V hU hV (n + 1)).naturality φ).symm
    ((Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond O U V (n + 1)).naturality φ).symm

include hU hV in
/-- **The five lemma on the Mayer--Vietoris sequence over the ambient open `W`.**  This is
`CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono'` (Stacks 05QB) applied to
`mayerVietorisAmbientHom` at offset one, so that the conclusion sits at `Hⁿ⁺¹(W,-)`: the
hypotheses are exactly the four the five lemma consumes at the four neighbouring positions. -/
public theorem isIso_ambient_of_chase (n : ℕ) {F G : SheafOfModules.{u} O} (φ : F ⟶ G)
    (h₀ : Epi ((Hfunctor O U n ⊞ Hfunctor O V n).map φ))
    (h₁ : IsIso ((Hfunctor O (U ⊓ V) n).map φ))
    (h₃ : IsIso ((Hfunctor O U (n + 1) ⊞ Hfunctor O V (n + 1)).map φ))
    (h₄ : Mono ((Hfunctor O (U ⊓ V) (n + 1)).map φ)) :
    IsIso ((Hfunctor O W (n + 1)).map φ) :=
  CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono'
    (k := 1) (n := 5) (by omega)
    (mayerVietorisAmbient_exact O W U V hU hV hUV n F)
    (mayerVietorisAmbient_exact O W U V hU hV hUV n G)
    (mayerVietorisAmbientHom O W U V hU hV hUV n φ) 1 2 3 4 5 rfl rfl rfl rfl rfl h₀ h₁ h₃ h₄

include hU hV in
/-- **Mayer--Vietoris descent of an isomorphism on cohomology.**  If `φ : F ⟶ G` induces
isomorphisms on `Hᵖ(U,-)`, `Hᵖ(V,-)` and `Hᵖ(U ⊓ V,-)` in the two degrees `n` and `n + 1`, then
it induces one on `Hⁿ⁺¹(W,-)`.  This is the step the induction of Stacks 09MR and 01PW performs
over an ambient open. -/
public theorem isIso_ambient_of_isIso_on_cover (n : ℕ) {F G : SheafOfModules.{u} O} (φ : F ⟶ G)
    (hU' : IsIso ((Hfunctor O U n).map φ)) (hV' : IsIso ((Hfunctor O V n).map φ))
    (hI : IsIso ((Hfunctor O (U ⊓ V) n).map φ))
    (hU'' : IsIso ((Hfunctor O U (n + 1)).map φ)) (hV'' : IsIso ((Hfunctor O V (n + 1)).map φ))
    (hI' : IsIso ((Hfunctor O (U ⊓ V) (n + 1)).map φ)) :
    IsIso ((Hfunctor O W (n + 1)).map φ) := by
  have h₀ : IsIso ((Hfunctor O U n ⊞ Hfunctor O V n).map φ) :=
    isIso_biprod_map (Hfunctor O U n) (Hfunctor O V n) φ hU' hV'
  have h₃ : IsIso ((Hfunctor O U (n + 1) ⊞ Hfunctor O V (n + 1)).map φ) :=
    isIso_biprod_map (Hfunctor O U (n + 1)) (Hfunctor O V (n + 1)) φ hU'' hV''
  have _ := hI'
  exact isIso_ambient_of_chase O W U V hU hV hUV n φ inferInstance hI inferInstance
    inferInstance

end Hgroup

end Stacks.Cohomology.AmbientMayerVietoris

end

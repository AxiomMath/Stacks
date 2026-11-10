module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization

/-!
# The underlying module of an ungraded realization is the sheafified direct sum

Let `R` be a sheaf of rings on a site, let `P : ι → PresheafOfModules R.val` be a graded family
and let `A` be a graded algebra structure on it. If `T` is a sheaf of rings receiving a locally
bijective morphism `β` from the ungraded realization `Stacks.GradedAlgebra.totalPresheaf`, and
`σ : R ⟶ T` is a morphism of sheaves of rings compatible with the structure map of `A`, then the
`R`-module underlying `T` is the sheafification of the objectwise direct sum `⨁ᵢ Pᵢ`.

This is the second half of Tag 01CF's passage from a sheaf of graded algebras to the ungraded
sheaf of rings it presents: the first half, the construction of the ring structure, is
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization`.

## Main definitions

* `Stacks.sheafifyHomOfPresheafHom`: the morphism from the sheafification of a presheaf of
  modules into a sheaf of modules induced by a morphism into its sections.
* `Stacks.sheafifyIsoOfLocallyBijective`: **a presheaf of modules which maps locally bijectively
  into a sheaf of modules exhibits that sheaf as its sheafification.**
* `Stacks.sheafifyDirectSumIso`: **the sheafification of the objectwise direct sum of a family
  of sheaves of modules is their coproduct.**
* `Stacks.GradedAlgebra.directSumHom`: the comparison morphism from the objectwise direct sum of
  the homogeneous components to the module underlying the ungraded realization.
* `Stacks.GradedAlgebra.directSumIsoUnderlyingModule`: **the module underlying the ungraded
  realization of a graded algebra is the sheafification of the direct sum of the homogeneous
  components.**
* `Stacks.directSumNatToInt`: the inclusion of the direct sum over the nonnegative degrees of a
  `ℤ`-graded family into the direct sum over all degrees.

## Main results

* `Stacks.GradedAlgebra.smul_eq_structureMap_mul`: the module structure of the ungraded
  realization over the base ring is multiplication by the image of the structure map. This is
  what makes the comparison morphism linear.
* `Stacks.bijective_directSumNatToIntApp`: that inclusion is bijective as soon as the negative
  components have no nonzero sections.
* `Stacks.subsingleton_of_isZero`: a zero sheaf of modules has no nonzero local sections, which
  is how the vanishing of the negative components is fed to the previous result.
* `Stacks.isLocallyInjective_toPresheaf_map_comp` and
  `Stacks.isLocallySurjective_toPresheaf_map_comp`: local bijectivity of the underlying morphism
  of presheaves of abelian groups is stable under composition.

## Implementation notes

The comparison morphism is the identity on sections: both the objectwise direct sum and the
module underlying the ungraded realization have `Stacks.GradedAlgebra.Total` as their sections,
and the only thing to check is that the two scalar actions agree, which is
`Stacks.GradedAlgebra.smul_eq_structureMap_mul`. The whole content of the comparison is
therefore the passage from the presheaf to its sheafification, and that is carried out
abstractly in `Stacks.sheafifyIsoOfLocallyBijective`: a locally bijective morphism of presheaves
of abelian groups lies in `CategoryTheory.GrothendieckTopology.W`, so the transposed morphism of
sheaves of modules becomes an isomorphism after `SheafOfModules.toSheaf`, which reflects
isomorphisms.

Local injectivity and local surjectivity are properties of the maps on sections only, so they
transfer from a morphism of presheaves of rings to the underlying morphism of presheaves of
abelian groups by the structure projections of `CategoryTheory.Presheaf.IsLocallyInjective` and
`CategoryTheory.Presheaf.IsLocallySurjective`; no comparison of the two concrete structures is
needed.

The implicit arguments of `PresheafOfModules.sheafificationHomEquiv` have to be supplied by
name. Its right-hand side is `M₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget R).obj F)`,
and solving `(restrictScalars (𝟙 R.val)).obj ?F.val ≟ M.val` for `?F` sends unification into
the sheafification functor; naming `F` avoids it.

Local injectivity and local surjectivity are taken as explicit hypotheses rather than as
instances throughout: the comparison morphisms carry the compatibility proof as an argument, and
instance resolution does not solve the resulting higher-order unification problem.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks

/-! ### A presheaf of modules mapping locally bijectively into a sheaf of modules -/

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {M₀ : PresheafOfModules.{w} R.obj} {M : SheafOfModules.{w} R} (c : M₀ ⟶ M.val)

/-- The morphism from the sheafification of a presheaf of modules `M₀` to a sheaf of modules `M`
determined by a morphism `M₀ ⟶ M.val`. -/
noncomputable def sheafifyHomOfPresheafHom :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj M₀ ⟶ M :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (P := M₀) (F := M)).symm c

/-- On underlying sheaves of abelian groups, `Stacks.sheafifyHomOfPresheafHom` is the
sheafification of the morphism of presheaves of abelian groups underlying `c`. -/
theorem toSheaf_map_sheafifyHomOfPresheafHom :
    (SheafOfModules.toSheaf.{w} R).map (sheafifyHomOfPresheafHom c) =
      (presheafToSheaf J AddCommGrpCat.{w}).map ((PresheafOfModules.toPresheaf R.obj).map c) ≫
        (CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{w}).counit.app
          ((SheafOfModules.toSheaf.{w} R).obj M) :=
  (PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm (𝟙 R.obj) (P := M₀) (F := M) c).trans
    (Adjunction.homEquiv_counit
      (CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{w}) _ _ _)

variable (hinj : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map c))
  (hsurj : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map c))

include hinj hsurj

/-- A locally bijective morphism into a sheaf of modules induces an isomorphism out of the
sheafification. -/
theorem isIso_sheafifyHomOfPresheafHom : IsIso (sheafifyHomOfPresheafHom c) := by
  have := hinj
  have := hsurj
  have h : IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map
      ((PresheafOfModules.toPresheaf R.obj).map c)) :=
    (J.W_iff _).mp (GrothendieckTopology.W_of_isLocallyBijective J
      ((PresheafOfModules.toPresheaf R.obj).map c))
  have : IsIso ((SheafOfModules.toSheaf.{w} R).map (sheafifyHomOfPresheafHom c)) := by
    rw [toSheaf_map_sheafifyHomOfPresheafHom]
    exact IsIso.comp_isIso' h (CategoryTheory.isIso_sheafificationAdjunction_counit _)
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{w} R)

/-- **A presheaf of modules which maps locally bijectively into a sheaf of modules exhibits that
sheaf as its sheafification.** -/
noncomputable def sheafifyIsoOfLocallyBijective :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj M₀ ≅ M :=
  haveI := isIso_sheafifyHomOfPresheafHom c hinj hsurj
  asIso (sheafifyHomOfPresheafHom c)

end Sheafify

/-! ### Local bijectivity of morphisms of presheaves of modules -/

section LocallyBijective

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {R : Cᵒᵖ ⥤ RingCat.{w}}
  {M₀ M₁ M₂ : PresheafOfModules.{w} R} (f : M₀ ⟶ M₁) (g : M₁ ⟶ M₂)

/-- Local injectivity of the underlying morphism of presheaves of abelian groups is stable under
composition. -/
lemma isLocallyInjective_toPresheaf_map_comp
    (hf : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map f))
    (hg : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map g)) :
    Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map (f ≫ g)) := by
  have := hf
  have := hg
  rw [Functor.map_comp]
  infer_instance

/-- Local surjectivity of the underlying morphism of presheaves of abelian groups is stable under
composition. -/
lemma isLocallySurjective_toPresheaf_map_comp
    (hf : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map f))
    (hg : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map g)) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map (f ≫ g)) := by
  have := hf
  have := hg
  rw [Functor.map_comp]
  infer_instance

end LocallyBijective

/-! ### Sections of a zero sheaf of modules -/

section IsZero

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A zero sheaf of modules has no nonzero local sections. -/
theorem subsingleton_of_isZero {M : SheafOfModules.{w} R} (hM : IsZero M) (X : Cᵒᵖ) :
    Subsingleton (M.val.obj X) := by
  have key : ∀ x : M.val.obj X, x = 0 := fun x => by
    have h : (𝟙 M : M ⟶ M).val.app X x = (0 : M ⟶ M).val.app X x := by
      rw [hM.eq_of_src (𝟙 M) 0]
    have h0 : (0 : M ⟶ M).val.app X x = 0 := by
      change (0 : M.val ⟶ M.val).app X x = 0
      simp
    simpa [h0] using h
  exact subsingleton_of_forall_eq 0 key

end IsZero

/-! ### The sheafified direct sum of a family of sheaves of modules -/

section DirectSum

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {ι : Type} [DecidableEq ι] (N : ι → SheafOfModules.{w} R)

/-- Sheafifying the objectwise direct sum of a family of sheaves of modules gives back the
family, componentwise. -/
noncomputable def sheafificationDirectSumComponentIso :
    Discrete.functor (fun i => (N i).val) ⋙ PresheafOfModules.sheafification (𝟙 R.obj) ≅
      Discrete.functor N :=
  Discrete.natIso fun i =>
    (asIso (PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)).counit).app (N i.as)

variable [HasCoproduct N]

/-- **The sheafification of the objectwise direct sum of a family of sheaves of modules is their
coproduct.** -/
noncomputable def sheafifyDirectSumIso :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj (directSum fun i => (N i).val) ≅ ∐ N :=
  (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj))
      (directSumIsColimit fun i => (N i).val)).coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv (sheafificationDirectSumComponentIso N) _).symm
      (colimit.isColimit (Discrete.functor N)))

end DirectSum

/-! ### The direct sum over the nonnegative degrees -/

section Reindex

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} (P : ℤ → PresheafOfModules.{w} R)

/-- The inclusion of the direct sum over the nonnegative degrees of a `ℤ`-graded family of
presheaves of modules into the direct sum over all degrees. -/
noncomputable def directSumNatToInt : directSum (fun n : ℕ => P (n : ℤ)) ⟶ directSum P :=
  directSumDesc _ fun n => inclHom P (n : ℤ)

/-- The inclusion `Stacks.directSumNatToInt` on sections, as an additive map whose target type
is written as a direct sum. -/
noncomputable def directSumNatToIntApp (X : Cᵒᵖ) :
    DirectSumType (fun n : ℕ => P (n : ℤ)) X →+ DirectSumType P X where
  toFun z := (directSumNatToInt P).app X z
  map_zero' := map_zero ((directSumNatToInt P).app X).hom
  map_add' z z' := map_add ((directSumNatToInt P).app X).hom z z'

/-- The inclusion of the nonnegative part sends a homogeneous section of degree `n` to the same
section, viewed in degree `(n : ℤ)`. -/
@[simp]
lemma directSumNatToIntApp_of (X : Cᵒᵖ) (n : ℕ) (x : (P (n : ℤ)).obj X) :
    directSumNatToIntApp P X (DirectSum.of _ n x) =
      DirectSum.of (fun m : ℤ => ((P m).obj X : Type w)) (n : ℤ) x :=
  congrArg (fun f : P (n : ℤ) ⟶ directSum P => f.app X x)
    (inclHom_directSumDesc (fun m : ℕ => P (m : ℤ)) (fun m => inclHom P (m : ℤ)) n)

/-- The inclusion of the nonnegative part does not change the component of nonnegative
degree. -/
lemma directSumNatToIntApp_apply_natCast (X : Cᵒᵖ) (m : ℕ)
    (z : DirectSumType (fun n : ℕ => P (n : ℤ)) X) :
    directSumNatToIntApp P X z (m : ℤ) = z m := by
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply]
  | of n x =>
    rw [directSumNatToIntApp_of]
    rcases eq_or_ne n m with rfl | hnm
    · rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ fun h => hnm (Nat.cast_injective h).symm,
        DirectSum.of_eq_of_ne _ _ _ fun h => hnm h.symm]
  | add z z' hz hz' => rw [map_add, DirectSum.add_apply, hz, hz', DirectSum.add_apply]

/-- **The direct sum over the nonnegative degrees of a `ℤ`-graded family of presheaves of
modules is the direct sum over all degrees**, as soon as the components of negative degree have
no nonzero sections. -/
theorem bijective_directSumNatToIntApp (X : Cᵒᵖ)
    (hP : ∀ n : ℤ, n < 0 → Subsingleton ((P n).obj X)) :
    Function.Bijective (directSumNatToIntApp P X) := by
  refine ⟨fun z z' h => DirectSum.ext fun m => ?_, fun y => ?_⟩
  · rw [← directSumNatToIntApp_apply_natCast, ← directSumNatToIntApp_apply_natCast, h]
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n x =>
    rcases lt_or_ge n 0 with hn | hn
    · have := hP n hn
      exact ⟨0, by rw [map_zero, Subsingleton.elim x 0, map_zero]⟩
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      exact ⟨DirectSum.of _ m x, directSumNatToIntApp_of P X m x⟩
  | add y y' hy hy' =>
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨z', rfl⟩ := hy'
    exact ⟨z + z', map_add _ z z'⟩

variable (J : GrothendieckTopology C)
  (hP : ∀ (n : ℤ), n < 0 → ∀ X : Cᵒᵖ, Subsingleton ((P n).obj X))

include hP

/-- The inclusion of the nonnegative part is locally injective, being injective. -/
lemma isLocallyInjective_directSumNatToInt :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R).map (directSumNatToInt P)) :=
  Presheaf.isLocallyInjective_of_injective J _ fun X =>
    (bijective_directSumNatToIntApp P X fun n hn => hP n hn X).1

/-- The inclusion of the nonnegative part is locally surjective, being surjective. -/
lemma isLocallySurjective_directSumNatToInt :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R).map (directSumNatToInt P)) :=
  Presheaf.isLocallySurjective_of_surjective J _ fun X =>
    (bijective_directSumNatToIntApp P X fun n hn => hP n hn X).2

end Reindex

/-! ### The module underlying the ungraded realization -/

namespace GradedAlgebra

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {ι : Type} [DecidableEq ι] [AddMonoid ι] {P : ι → PresheafOfModules.{w} R.obj}
  (A : GradedAlgebra P)

/-- The module structure of the ungraded realization over the base ring is multiplication by the
image of the structure map. -/
lemma smul_eq_structureMap_mul {X : Cᵒᵖ} (r : R.obj.obj X) (a : A.Total X) :
    r • a = A.structureMap X r * a := by
  have h : A.structureMap X r * a = r • (1 : A.Total X) * a := rfl
  rw [h, A.smul_mul_eq, _root_.one_mul]

variable {T : Sheaf J RingCat.{w}} (σ : R ⟶ T) (β : A.totalPresheaf ⟶ T.obj)

/-- A morphism of presheaves of rings out of the ungraded realization which is compatible with
the structure maps is semilinear over the base ring. -/
lemma map_smul_totalPresheaf (fac : A.structureHom ≫ β = σ.hom) (X : Cᵒᵖ) (r : R.obj.obj X)
    (a : A.Total X) :
    (β.app X).hom (r • a) = (σ.hom.app X).hom r * (β.app X).hom a := by
  have hr : (β.app X).hom (A.structureMap X r) = (σ.hom.app X).hom r :=
    congrArg (fun f : R.obj ⟶ T.obj => (f.app X).hom r) fac
  rw [A.smul_eq_structureMap_mul]
  exact (map_mul (β.app X).hom _ _).trans (by rw [hr])

/-- The comparison morphism from the objectwise direct sum of the homogeneous components of a
graded algebra to the module underlying a sheaf of rings receiving its ungraded realization. -/
noncomputable def directSumHom (fac : A.structureHom ≫ β = σ.hom) :
    directSum P ⟶ ((SheafOfModules.restrictScalars.{w} σ).obj (SheafOfModules.unit T)).val where
  app X := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (σ.hom.app X).hom).obj
        (ModuleCat.of (T.obj.obj X) (T.obj.obj X)))
    { toFun := fun z => (β.app X).hom z
      map_add' := fun z z' => map_add (β.app X).hom z z'
      map_smul' := fun r z => A.map_smul_totalPresheaf σ β fac X r z }
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    exact CategoryTheory.congr_fun (β.naturality f) z

/-- The comparison morphism of `Stacks.GradedAlgebra.directSumHom` is locally injective as soon
as the morphism into the sheafified ring is. -/
lemma isLocallyInjective_toPresheaf_map_directSumHom
    (fac : A.structureHom ≫ β = σ.hom) (hβ : Presheaf.IsLocallyInjective J β) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map (A.directSumHom σ β fac)) :=
  have := hβ
  ⟨fun x y h => Presheaf.equalizerSieve_mem J β x y h⟩

/-- The comparison morphism of `Stacks.GradedAlgebra.directSumHom` is locally surjective as soon
as the morphism into the sheafified ring is. -/
lemma isLocallySurjective_toPresheaf_map_directSumHom
    (fac : A.structureHom ≫ β = σ.hom) (hβ : Presheaf.IsLocallySurjective J β) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (A.directSumHom σ β fac)) :=
  have := hβ
  ⟨fun s => Presheaf.imageSieve_mem J β s⟩

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The module underlying the ungraded realization of a graded algebra is the sheafification of
the objectwise direct sum of the homogeneous components.** -/
noncomputable def directSumIsoUnderlyingModule (fac : A.structureHom ≫ β = σ.hom)
    (hinj : Presheaf.IsLocallyInjective J β) (hsurj : Presheaf.IsLocallySurjective J β) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj (directSum P) ≅
      (SheafOfModules.restrictScalars.{w} σ).obj (SheafOfModules.unit T) :=
  sheafifyIsoOfLocallyBijective (A.directSumHom σ β fac)
    (A.isLocallyInjective_toPresheaf_map_directSumHom σ β fac hinj)
    (A.isLocallySurjective_toPresheaf_map_directSumHom σ β fac hsurj)

end

end GradedAlgebra

end Stacks

end

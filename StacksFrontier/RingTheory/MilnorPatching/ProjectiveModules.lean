module

public import Mathlib
public import StacksFrontier.RingTheory.MilnorPatching.RelativeProperties
public import StacksFrontier.RingTheory.Localization.Glueing.CategoricalPullback

/-!
# Finite projective modules over a fibre product of rings

For a fibre product `B' = B ×_A A'` in which `A' → A` is surjective, extension of scalars
identifies the finite projective `B'`-modules with the compatible pairs consisting of a finite
projective `B`-module and a finite projective `A'`-module.

## Main results

* `MilnorPatching.finiteProjectiveModulesEquivalenceOverFibreProduct` is Stacks Tag 0D2J: the
  equivalence of the two categories of finite projective modules.

## Implementation notes

Finite projectivity is `Module.Finite` together with `Module.Projective`.  The natural isomorphism
with the ambient extension-of-scalars functor records that the equivalence is the canonical one.
The proof runs through the relative situation of Stacks Tag 08KK specialized to `D' = B'`, so it
uses the finiteness, flatness and finite presentation results of the relative sections even though
its statement is about the absolute square.

## References

* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
-/

section

section
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u

namespace MilnorPatching
open ModuleGlueing
variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
variable (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
variable (base : RingFibreProduct.Situation toBase surjection I)

private noncomputable def rel : RelativeModuleFibreProductSituation
    (D' := base.fibreProduct) base := ⟨RingHom.id _⟩

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for `TensorProduct R R X` with `Algebra` structures from `RingHom.toAlgebra`
/-- The inclusion of the second factor of `R ⊗ X` is bijective. -/
private theorem includeRight_bijective_of_id {R X : Type u} [CommRing R] [CommRing X]
    (f : R →+* X) :
    letI : Algebra R X := f.toAlgebra
    letI : Algebra R R := (RingHom.id R).toAlgebra
    Function.Bijective
      (Algebra.TensorProduct.includeRight.toRingHom : X →+* TensorProduct R R X) := by
  let : Algebra R X := f.toAlgebra
  let : Algebra R R := (RingHom.id R).toAlgebra
  exact Algebra.TensorProduct.includeRight_bijective (R := R) (A := R) (B := X)
    Function.bijective_id

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for `TensorProduct R R X` with `Algebra` structures from `RingHom.toAlgebra`
/-- In `R ⊗ X`, the two ways of including `r : R` agree. -/
private theorem tmul_one_eq_one_tmul_of_id {R X : Type u} [CommRing R] [CommRing X]
    (f : R →+* X) (r : R) :
    letI : Algebra R X := f.toAlgebra
    letI : Algebra R R := (RingHom.id R).toAlgebra
    (r ⊗ₜ[R] (1 : X) : TensorProduct R R X) = 1 ⊗ₜ[R] f r := by
  let : Algebra R X := f.toAlgebra
  let : Algebra R R := (RingHom.id R).toAlgebra
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R) (A := R) (B := X) r

private theorem btoD_bijective : Function.Bijective
    (rel toBase surjection I base).BtoD :=
  includeRight_bijective_of_id base.pullbackCone.fst.hom

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for the `Algebra` structures on the fibre product's tensor products
private theorem toD_eq : (rel toBase surjection I base).toD =
    ((rel toBase surjection I base).BtoD).comp base.pullbackCone.fst.hom :=
  RingHom.ext (tmul_one_eq_one_tmul_of_id base.pullbackCone.fst.hom)

private theorem a'toC'_bijective : Function.Bijective
    (rel toBase surjection I base).A'toC' :=
  includeRight_bijective_of_id base.pullbackCone.snd.hom

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for the `Algebra` structures on the fibre product's tensor products
private theorem toC'_eq : (rel toBase surjection I base).toC' =
    ((rel toBase surjection I base).A'toC').comp base.pullbackCone.snd.hom :=
  RingHom.ext (tmul_one_eq_one_tmul_of_id base.pullbackCone.snd.hom)

private theorem projective_baseChange
    (L : ModuleCat.{u} base.fibreProduct)
    (hL : Module.Finite base.fibreProduct L ∧ Module.Projective base.fibreProduct L) :
    let E := extensionOfScalarsToPullback base.pullbackCone.fst.hom
      base.pullbackCone.snd.hom toBase surjection (by
        simpa using congrArg CommRingCat.Hom.hom base.pullbackCone.condition)
    (Module.Finite B (E.obj L).fst ∧ Module.Projective B (E.obj L).fst) ∧
      (Module.Finite A' (E.obj L).snd ∧ Module.Projective A' (E.obj L).snd) := by
  obtain ⟨_, _⟩ := hL
  let : Algebra base.fibreProduct B := base.pullbackCone.fst.hom.toAlgebra
  let : Algebra base.fibreProduct A' := base.pullbackCone.snd.hom.toAlgebra
  change (Module.Finite B (TensorProduct base.fibreProduct B L) ∧
      Module.Projective B (TensorProduct base.fibreProduct B L)) ∧
    (Module.Finite A' (TensorProduct base.fibreProduct A' L) ∧
      Module.Projective A' (TensorProduct base.fibreProduct A' L))
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩

/-- Base change along `f : R →+* S` followed by a bijective `g : S →+* T` stays finitely
presented over `T`, and is flat over `S` once restricted along `g`. -/
private theorem baseChange_components {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hg : Function.Bijective g) (L : ModuleCat.{u} R)
    (hS : Module.FinitePresentation S ((ModuleCat.extendScalars f).obj L) ∧
      Module.Flat S ((ModuleCat.extendScalars f).obj L))
    (h : R →+* T) (hh : h = g.comp f) (M : ModuleCat.{u} T)
    (hM : M = (ModuleCat.extendScalars h).obj L) :
    Module.FinitePresentation T M ∧ Module.Flat S ((ModuleCat.restrictScalars g).obj M) := by
  subst hh
  let i : M ≅ (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj L) :=
    eqToIso hM ≪≫ (ModuleCat.extendScalarsComp f g).app L
  let : Algebra S T := g.toAlgebra
  let : Module.FinitePresentation S ((ModuleCat.extendScalars f).obj L) := hS.1
  let : Module.Flat S T := RingHom.Flat.of_bijective hg
  let : Module.Flat S ((ModuleCat.extendScalars f).obj L) := hS.2
  have hfp : Module.FinitePresentation T ((ModuleCat.extendScalars g).obj
      ((ModuleCat.extendScalars f).obj L)) := by
    change Module.FinitePresentation T (TensorProduct S T ((ModuleCat.extendScalars f).obj L))
    infer_instance
  have hflat : Module.Flat S ((ModuleCat.restrictScalars g).obj ((ModuleCat.extendScalars g).obj
      ((ModuleCat.extendScalars f).obj L))) := by
    change Module.Flat S (TensorProduct S T ((ModuleCat.extendScalars f).obj L))
    exact Module.Flat.trans S T _
  exact ⟨Module.FinitePresentation.of_equiv i.symm.toLinearEquiv,
    Module.Flat.of_linearEquiv ((ModuleCat.restrictScalars g).mapIso i).toLinearEquiv⟩

private theorem relativeComponents_of_baseComponents
    (L : ModuleCat.{u} base.fibreProduct)
    (hB : Module.FinitePresentation B
        ((ModuleCat.extendScalars base.pullbackCone.fst.hom).obj L) ∧
      Module.Flat B ((ModuleCat.extendScalars base.pullbackCone.fst.hom).obj L))
    (hA' : Module.FinitePresentation A'
        ((ModuleCat.extendScalars base.pullbackCone.snd.hom).obj L) ∧
      Module.Flat A' ((ModuleCat.extendScalars base.pullbackCone.snd.hom).obj L)) :
    let r := rel toBase surjection I base
    let Er : ModuleCat.{u} base.fibreProduct ⥤ r.CompatibleModules :=
      letI : Algebra base.fibreProduct base.fibreProduct := r.toD'.toAlgebra
      letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
      letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
      letI : Algebra base.fibreProduct A :=
        (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
      extensionOfScalarsToTensorProductPullback (D' := base.fibreProduct)
        ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
        ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A)
    Module.FinitePresentation r.D (Er.obj L).fst ∧
      Module.Flat B ((ModuleCat.restrictScalars r.BtoD).obj (Er.obj L).fst) ∧
    Module.FinitePresentation r.C' (Er.obj L).snd ∧
      Module.Flat A' ((ModuleCat.restrictScalars r.A'toC').obj (Er.obj L).snd) := by
  intro r Er
  have hb := baseChange_components base.pullbackCone.fst.hom r.BtoD
    (btoD_bijective toBase surjection I base) L hB r.toD (toD_eq toBase surjection I base)
    (Er.obj L).fst rfl
  have hc := baseChange_components base.pullbackCone.snd.hom r.A'toC'
    (a'toC'_bijective toBase surjection I base) L hA' r.toC' (toC'_eq toBase surjection I base)
    (Er.obj L).snd rfl
  exact ⟨hb.1, hb.2, hc⟩

private theorem finitePresentation_of_baseComponents
    (L : ModuleCat.{u} base.fibreProduct)
    (hflat : Module.Flat base.fibreProduct L)
    (hB : Module.FinitePresentation B
        ((ModuleCat.extendScalars base.pullbackCone.fst.hom).obj L) ∧
      Module.Flat B ((ModuleCat.extendScalars base.pullbackCone.fst.hom).obj L))
    (hA' : Module.FinitePresentation A'
        ((ModuleCat.extendScalars base.pullbackCone.snd.hom).obj L) ∧
      Module.Flat A' ((ModuleCat.extendScalars base.pullbackCone.snd.hom).obj L)) :
    Module.FinitePresentation base.fibreProduct L := by
  let r := rel toBase surjection I base
  let Er : ModuleCat.{u} base.fibreProduct ⥤ r.CompatibleModules :=
    let : Algebra base.fibreProduct base.fibreProduct := r.toD'.toAlgebra
    let : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    let : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    let : Algebra base.fibreProduct A :=
      (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
    extensionOfScalarsToTensorProductPullback (D' := base.fibreProduct)
      ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
      ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A)
  obtain ⟨hDfp, hDflat, hC'fp, hC'flat⟩ :=
    relativeComponents_of_baseComponents toBase surjection I base L hB hA'
  obtain ⟨Fkm, _, adjkm, _, hcounit⟩ :=
    relativeCompatiblePairsRightAdjoint_counit_isIso r
  obtain ⟨Frw, _, adjrw, _, _, _, _, hunitrw, _⟩ :=
    relativelyFlatModulesEquivalenceOverFibreProduct r
  have hflatR : Module.Flat base.fibreProduct
      ((ModuleCat.restrictScalars r.toD').obj L) := by
    change Module.Flat base.fibreProduct
      ((ModuleCat.restrictScalars (RingHom.id base.fibreProduct)).obj L)
    let : Module.Flat base.fibreProduct ((𝟭 (ModuleCat.{u} base.fibreProduct)).obj L) := hflat
    exact Module.Flat.of_linearEquiv
      ((ModuleCat.restrictScalarsId base.fibreProduct).app L).toLinearEquiv
  let c := adjkm.rightAdjointUniq adjrw
  have huComp : IsIso (adjkm.unit.app L ≫ c.hom.app (Er.obj L)) := by
    rw [Adjunction.unit_rightAdjointUniq_hom_app adjkm adjrw L]
    exact hunitrw L hflatR
  have huKM : IsIso (adjkm.unit.app L) := by
    have : IsIso (c.hom.app (Er.obj L)) := by
      change IsIso (c.app (Er.obj L)).hom
      infer_instance
    exact IsIso.of_isIso_comp_right (adjkm.unit.app L) (c.hom.app (Er.obj L))
  have hfpF : Module.FinitePresentation base.fibreProduct (Fkm.obj (Er.obj L)) :=
    finitePresentation_rightAdjoint_obj_of_factorization
      (D'' := base.fibreProduct) r Fkm adjkm hcounit (Er.obj L)
      hDfp hDflat hC'fp hC'flat (RingHom.id _) (RingHom.id _) rfl inferInstance
      (RingHom.FinitePresentation.id _)
  let : Module.FinitePresentation base.fibreProduct ((Er ⋙ Fkm).obj L) := hfpF
  exact Module.FinitePresentation.of_equiv
    (show ((Er ⋙ Fkm).obj L) ≃ₗ[base.fibreProduct] L from
      (asIso (adjkm.unit.app L)).toLinearEquiv.symm)

private theorem finiteProjective_rightAdjoint_obj
    (F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
        (ModuleCat.extendScalars.{u, u, u} surjection) ⥤
      ModuleCat.{u} base.fibreProduct)
    (adj : extensionOfScalarsToPullback base.pullbackCone.fst.hom
      base.pullbackCone.snd.hom toBase surjection (by
        simpa using congrArg CommRingCat.Hom.hom base.pullbackCone.condition) ⊣ F)
    (hcounit : IsIso adj.counit)
    (hflat : ∀ X,
      (Module.Flat B X.fst ∧ Module.Flat A' X.snd) →
        Module.Flat base.fibreProduct (F.obj X))
    (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection))
    (hX : (Module.Finite B X.fst ∧ Module.Projective B X.fst) ∧
      (Module.Finite A' X.snd ∧ Module.Projective A' X.snd)) :
    Module.Finite base.fibreProduct (F.obj X) ∧
      Module.Projective base.fibreProduct (F.obj X) := by
  let E := extensionOfScalarsToPullback base.pullbackCone.fst.hom
    base.pullbackCone.snd.hom toBase surjection (by
      simpa using congrArg CommRingCat.Hom.hom base.pullbackCone.condition)
  obtain ⟨⟨hBf, _⟩, hA'f, _⟩ := hX
  have hXflat : Module.Flat B X.fst ∧ Module.Flat A' X.snd := ⟨inferInstance, inferInstance⟩
  let : Module.Flat base.fibreProduct (F.obj X) := hflat X hXflat
  let eB := (asIso ((adj.counit.app X).fst)).toLinearEquiv
  let eA' := (asIso ((adj.counit.app X).snd)).toLinearEquiv
  have hBfp : Module.FinitePresentation B (E.obj (F.obj X)).fst := by
    let : Module.FinitePresentation B ((𝟭 _).obj X).fst :=
      Module.finitePresentation_of_projective B X.fst
    exact Module.FinitePresentation.of_equiv eB.symm
  have hBflat : Module.Flat B (E.obj (F.obj X)).fst := by
    let : Module.Flat B ((𝟭 _).obj X).fst := hXflat.1
    exact Module.Flat.of_linearEquiv eB
  have hA'fp : Module.FinitePresentation A' (E.obj (F.obj X)).snd := by
    let : Module.FinitePresentation A' ((𝟭 _).obj X).snd :=
      Module.finitePresentation_of_projective A' X.snd
    exact Module.FinitePresentation.of_equiv eA'.symm
  have hA'flat : Module.Flat A' (E.obj (F.obj X)).snd := by
    let : Module.Flat A' ((𝟭 _).obj X).snd := hXflat.2
    exact Module.Flat.of_linearEquiv eA'
  have hFfp : Module.FinitePresentation base.fibreProduct (F.obj X) :=
    finitePresentation_of_baseComponents toBase surjection I base (F.obj X)
      (hflat X hXflat) ⟨hBfp, hBflat⟩ ⟨hA'fp, hA'flat⟩
  exact ⟨finite_rightAdjoint_obj_of_finite_components
      toBase surjection I base F adj hcounit X hBf hA'f,
    Module.Flat.projective_of_finitePresentation⟩

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for the `Algebra` structures on the fibre product's tensor products
/-- **Stacks Project, Tag 0D2J.** Over a fibre product `B' = B ×_A A'` with `A' → A`
surjective, extension of scalars gives an equivalence from finite projective `B'`-modules to
compatible pairs whose `B`- and `A'`-components are finite projective. -/
@[stacks 0D2J]
public theorem finiteProjectiveModulesEquivalenceOverFibreProduct
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (s : RingFibreProduct.Situation toBase surjection I) :
    let toB : s.fibreProduct →+* B := s.pullbackCone.fst.hom
    let toA' : s.fibreProduct →+* A' := s.pullbackCone.snd.hom
    let comm : toBase.comp toB = surjection.comp toA' := by
      change toBase.comp s.pullbackCone.fst.hom =
        surjection.comp s.pullbackCone.snd.hom
      exact congrArg CommRingCat.Hom.hom s.pullbackCone.condition
    let E := extensionOfScalarsToPullback toB toA' toBase surjection comm
    let finiteProjectiveSource : ObjectProperty (ModuleCat.{u} s.fibreProduct) :=
      fun L ↦ Module.Finite s.fibreProduct L ∧ Module.Projective s.fibreProduct L
    let finiteProjectiveTarget : ObjectProperty
        (CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
          (ModuleCat.extendScalars.{u, u, u} surjection)) :=
      fun X ↦ (Module.Finite B X.fst ∧ Module.Projective B X.fst) ∧
        (Module.Finite A' X.snd ∧ Module.Projective A' X.snd)
    ∃ q : finiteProjectiveSource.FullSubcategory ≌
        finiteProjectiveTarget.FullSubcategory,
      Nonempty (finiteProjectiveSource.ι ⋙ E ≅ q.functor ⋙ finiteProjectiveTarget.ι) := by
  let E := extensionOfScalarsToPullback s.pullbackCone.fst.hom
    s.pullbackCone.snd.hom toBase surjection (by
      simpa using congrArg CommRingCat.Hom.hom s.pullbackCone.condition)
  let P : ObjectProperty (ModuleCat.{u} s.fibreProduct) :=
    fun L ↦ Module.Finite s.fibreProduct L ∧ Module.Projective s.fibreProduct L
  let Q : ObjectProperty
      (CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
        (ModuleCat.extendScalars.{u, u, u} surjection)) :=
    fun X ↦ (Module.Finite B X.fst ∧ Module.Projective B X.fst) ∧
      (Module.Finite A' X.snd ∧ Module.Projective A' X.snd)
  obtain ⟨F, _, adj, _, hcounit, hflatF, hunit, _⟩ :=
    flatModulesEquivalenceOverFibreProduct toBase surjection I s
  have hE : ∀ L : P.FullSubcategory, Q (E.obj L.obj) := fun L ↦
    projective_baseChange toBase surjection I s L.obj L.property
  have hF : ∀ X : Q.FullSubcategory, P (F.obj X.obj) := fun X ↦
    finiteProjective_rightAdjoint_obj toBase surjection I s F adj hcounit hflatF X.obj X.property
  let qE : P.FullSubcategory ⥤ Q.FullSubcategory := Q.lift (P.ι ⋙ E) hE
  let qF : Q.FullSubcategory ⥤ P.FullSubcategory := P.lift (Q.ι ⋙ F) hF
  let commE : P.ι ⋙ E ≅ qE ⋙ Q.ι := Iso.refl _
  let commF : Q.ι ⋙ F ≅ qF ⋙ P.ι := Iso.refl _
  let adjR := adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι commE commF
  have hunitR (X : P.FullSubcategory) : IsIso (adjR.unit.app X) := by
    apply (ObjectProperty.isIso_hom_iff (adjR.unit.app X)).mp
    have hmap := Adjunction.map_restrictFullyFaithful_unit_app adj
      P.fullyFaithfulι Q.fullyFaithfulι commE commF X
    have hflatX : Module.Flat s.fibreProduct X.obj := by
      let : Module.Projective s.fibreProduct X.obj := X.property.2
      infer_instance
    change IsIso (P.ι.map (adjR.unit.app X))
    rw [show P.ι.map (adjR.unit.app X) = _ by simpa only [adjR] using hmap]
    exact IsIso.comp_isIso' (hunit X.obj hflatX) (IsIso.comp_isIso'
      (F.mapIso (commE.app X)).isIso_hom (commF.app (qE.obj X)).isIso_hom)
  have hcounitR (Y : Q.FullSubcategory) : IsIso (adjR.counit.app Y) := by
    apply (ObjectProperty.isIso_hom_iff (adjR.counit.app Y)).mp
    have hmap := Adjunction.map_restrictFullyFaithful_counit_app adj
      P.fullyFaithfulι Q.fullyFaithfulι commE commF Y
    change IsIso (Q.ι.map (adjR.counit.app Y))
    rw [show Q.ι.map (adjR.counit.app Y) = _ by simpa only [adjR] using hmap]
    exact IsIso.comp_isIso' (commE.app (qF.obj Y)).symm.isIso_hom
      (IsIso.comp_isIso' (E.mapIso (commF.app Y).symm).isIso_hom
        (NatIso.isIso_app_of_isIso adj.counit (Q.ι.obj Y)))
  exact ⟨adjR.toEquivalence, ⟨Iso.refl _⟩⟩

end MilnorPatching
end

end

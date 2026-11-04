module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalProperties.Injective
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso

/-!
# Dualizing complexes

A dualizing complex over a Noetherian commutative ring `A` is an object `K` of the derived
category of `A`-modules which has finite injective dimension, has finite cohomology modules,
and for which the scalar homothety `A → RHom_A(K, K)` is a quasi-isomorphism. This file sets
up that definition and proves that the property is preserved by localization.

For a bounded complex of injectives `I` representing `K`, the Hom complex `Hom•_A(I, I)`
computes `RHom_A(K, K)`, so the third condition is expressed as the quasi-isomorphism
property of an explicit chain map `homothety I` out of the complex concentrated in degree
zero at `A`. Localization is treated for an abstract localization `IsLocalization S B`
rather than for the chosen model `Localization S`: the derived extension of scalars
transports a bounded injective representative to a bounded injective representative over
`B`, finiteness of cohomology is flat base change of finite modules, and the homothety
condition transports along the base-change isomorphism for derived Hom.

## Main definitions

* `Dualizing.liftedEndomorphismComplex` is the universe-lifted Hom complex of a
  representative.
* `Dualizing.homothety` is the canonical scalar homothety map to the endomorphism complex
  of a representative.
* `Dualizing.IsDerivedHomothetyQuasiIso` says that this map is a quasi-isomorphism for
  bounded injective representatives.
* `Dualizing.IsDualizingComplex` is the predicate of being a dualizing complex.

## Main results

* `Dualizing.homComplex_represents_derivedHom` identifies the cohomology of the Hom complex
  of a bounded-below injective representative with derived morphisms.
* `Dualizing.isDualizingComplex_localization` says that localization preserves dualizing
  complexes.
* `Dualizing.quasiIso_homothety_of_rankOne` reduces the homothety condition to rank one of the
  zeroth endomorphism module together with vanishing in the other degrees; the hypothesis is an
  arbitrary `R`-linear equivalence `(HomComplexR R J J).homology 0 ≃ₗ[R] R`, with no
  compatibility clause.

## Implementation notes

The derived category of `A`-modules is an **instance argument**: `IsDualizingComplex`,
`IsDerivedHomothetyQuasiIso` and `homComplex_represents_derivedHom` each take
`[HasDerivedCategory.{w} (ModuleCat.{v} A)]`, rather than fixing the model with a file-level
`attribute [local instance] HasDerivedCategory.standard`. Nothing in the definition needs the
standard model: `StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension`,
`DerivedCategory.homologyFunctor` and `DerivedCategory.Q` are all model-generic. A statement
proved for the standard model says nothing about another model, because `HasDerivedCategory` is
`CategoryTheory.MorphismProperty.HasLocalization`, a *data*-carrying class, so two routes to it
give genuinely different types of `DerivedCategory`.

`Dualizing.isDualizingComplex_localization` goes through
`StacksDraft.PseudoCoherence.derivedExtensionScalars`,
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` and
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange`, each of which is pinned at the
standard model, so the localization section uses the standard model as a local instance and its
statements are standard-model ones.

`StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension` supplies the notion of finite
injective dimension from Tag 0A5S: its witness is a bounded complex of injectives
representing the given derived object. For such a representative `I`,
`homComplex_represents_derivedHom` shows that its Hom complex represents `RHom_A(K, K)`.
The map `homothety I` is the actual chain map from the complex concentrated in degree zero
at `A`, sending `a` to `a • 𝟙 I`; both source and target are universe-lifted to a common
category of additive commutative groups. Thus `QuasiIso (homothety I)` is precisely the
source's canonical quasi-isomorphism condition, not merely a characterization by the
resulting cohomology groups. The three fields of `IsDualizingComplex` correspond
respectively to parts (1), (2), and (3) of the source definition.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
-/

@[expose] public section

namespace Dualizing

section Definition

open CategoryTheory

universe v u w

/-- The additive endomorphism complex of `I`, lifted to a universe containing both its
groups of cochains and the base ring. -/
noncomputable abbrev liftedEndomorphismComplex {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{v} A) ℤ) : CochainComplex AddCommGrpCat.{max u v} ℤ :=
  ((AddCommGrpCat.uliftFunctor.{u, v}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (CochainComplex.HomComplex I I)

/-- The canonical scalar homothety chain map
`A[0] → Hom•_A(I, I)`, with both complexes universe-lifted. -/
@[implicit_reducible]
noncomputable def homothety {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{v} A) ℤ) :
    (CochainComplex.singleFunctor AddCommGrpCat 0).obj
        (AddCommGrpCat.of (ULift.{v} A)) ⟶ liftedEndomorphismComplex I :=
  HomologicalComplex.mkHomFromSingle
    (AddCommGrpCat.ofHom
      { toFun := fun a ↦
          ULift.up (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I))
        map_zero' := by ext; simp; rfl
        map_add' := by intros; ext; simp [add_smul]; rfl })
    (fun k hk ↦ by
      obtain rfl : (1 : ℤ) = k := by simpa using hk
      ext a
      change ULift.up (CochainComplex.HomComplex.δ 0 1
        (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I))) = 0
      apply ULift.ext; simp)

/-- In degree zero the scalar homothety sends a scalar `a`, viewed in the single complex at
`ULift A` through the canonical identification of its degree-zero term, to the cochain
`a • 𝟙`. -/
theorem homothety_f_zero_apply_source {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{v} A) ℤ)
    (a : ((CochainComplex.singleFunctor AddCommGrpCat 0).obj
      (AddCommGrpCat.of (ULift.{v} A))).X 0) :
    ((homothety I).f 0).hom a =
      ULift.up (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (AddCommGrpCat.of (ULift.{v} A))).hom.hom a).down •
          CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) :=
  rfl

/-- If `I` is a bounded-below complex of injective modules, its Hom complex computes
derived Hom: degree-`n` cohomology classes are canonically the morphisms from `I` to
`I⟦n⟧` in the derived category. -/
theorem homComplex_represents_derivedHom {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    (I : CochainComplex (ModuleCat.{v} A) ℤ) (a n : ℤ) [I.IsStrictlyGE a]
    [∀ i, Injective (I.X i)] :
    Function.Bijective
      (fun (c : CochainComplex.HomComplex.CohomologyClass I I n) ↦
        DerivedCategory.Qh.map
          (CochainComplex.HomComplex.CohomologyClass.homAddEquiv c)) := by
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  exact (CochainComplex.IsKInjective.Qh_map_bijective _ _).comp
    (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (K := I) (L := I) (n := n)).bijective

/-- The canonical map `A → RHom_A(K, K)` is a quasi-isomorphism.

For every bounded injective representative `I` of `K`, the Hom complex of `I` computes
the derived Hom, so this is stated as the quasi-isomorphism property of `homothety I`. -/
abbrev IsDerivedHomothetyQuasiIso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    (K : DerivedCategory (ModuleCat.{v} A)) : Prop :=
  ∀ (I : CochainComplex (ModuleCat.{v} A) ℤ), Nonempty (DerivedCategory.Q.obj I ≅ K) →
    (∀ i : ℤ, Injective (I.X i)) →
      (∃ a b : ℤ, I.IsStrictlyGE a ∧ I.IsStrictlyLE b) → QuasiIso (homothety I)

/-- A dualizing complex over a Noetherian commutative ring is a derived object of finite
injective dimension whose cohomology modules are finite and whose homothety map to its derived
endomorphism complex is a quasi-isomorphism. -/
@[stacks 0A7B, sga "5 I 1.7" "affine/ring case"]
structure IsDualizingComplex {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    (K : DerivedCategory (ModuleCat.{v} A)) : Prop where
  /-- The complex has finite injective dimension. -/
  finiteInjectiveDimension : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K
  /-- Every cohomology module is finite over the base ring. -/
  finiteCohomology : ∀ i : ℤ,
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)
  /-- Homothety from the base ring to the derived endomorphism complex is a
  quasi-isomorphism. -/
  homothetyQuasiIso : IsDerivedHomothetyQuasiIso K

end Definition

section Localization

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w
universe uC vC uD vD

/-- An additive fully faithful functor identifies the cochains between two complexes with
the cochains between their images. -/
noncomputable def cochainAddEquivOfFullyFaithful
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Preadditive C] [Preadditive D] (Φ : C ⥤ D) [Φ.Additive]
    [Φ.Full] [Φ.Faithful]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain K L n ≃+
      CochainComplex.HomComplex.Cochain
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n where
  toFun z := z.map Φ
  invFun z := CochainComplex.HomComplex.Cochain.mk
    (fun p q hpq => Φ.preimage (z.v p q hpq))
  left_inv z := CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq =>
    Φ.preimage_map (z.v p q hpq)
  right_inv z := CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq =>
    Φ.map_preimage (z.v p q hpq)
  map_add' z z' := CochainComplex.HomComplex.Cochain.map_add z z' Φ

/-- The fully faithful universe lift identifies cochains linearly. -/
noncomputable def cochainULiftLinearEquiv
    {R : Type u} [CommRing R] (K L : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) :
    ULift.{w, v} (CochainComplex.HomComplex.Cochain K L n) ≃ₗ[R]
      CochainComplex.HomComplex.Cochain
        (((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) n := by
  let U := ModuleCat.uliftFunctor.{w, v} R
  let e := cochainAddEquivOfFullyFaithful U K L n
  let f : ULift.{w, v} (CochainComplex.HomComplex.Cochain K L n) →ₗ[R] _ := {
    toFun := fun z => e z.down
    map_add' := by intro z z'; simp
    map_smul' r z := CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq =>
      U.map_smul r (z.down.v p q hpq) }
  exact LinearEquiv.ofBijective f
    ⟨fun z z' h => ULift.ext _ _ (e.injective h),
      fun z => ⟨ULift.up (e.symm z), e.apply_symm_apply z⟩⟩

/-- Universe lifting commutes with the module-valued Hom complex. -/
noncomputable def homComplexULiftIso
    {R : Type u} [CommRing R] (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    (((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR R K L)) ≅
      CochainComplex.HomComplexR R
        (((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainULiftLinearEquiv K L n).toModuleIso)

/-- Restriction along a ring equivalence commutes with the module-valued Hom complex. -/
noncomputable def homComplexRestrictScalarsIso
    {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    (e : S ≃+* R) (I : CochainComplex (ModuleCat.{v} R) ℤ) :
    (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR R I I)) ≅
      CochainComplex.HomComplexR S
        (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
        (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) := by
  let F := ModuleCat.restrictScalars.{v} e.toRingHom
  haveI : F.Additive := inferInstance
  apply HomologicalComplex.Hom.isoOfComponents
    (fun n => by
      let h := cochainAddEquivOfFullyFaithful F I I n
      let f : F.obj ((CochainComplex.HomComplexR R I I).X n) →ₗ[S] _ := {
        toFun := fun z => h z
        map_add' := h.map_add
        map_smul' _ _ := CochainComplex.HomComplex.Cochain.ext _ _ fun _ _ _ => rfl }
      exact (LinearEquiv.ofBijective f h.bijective).toModuleIso)

/-- Direct universe lifting agrees with two successive universe lifts. -/
noncomputable def uliftCompLinearEquiv
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    ULift.{max u w, v} M ≃ₗ[R] ULift.{w, max u v} (ULift.{u, v} M) where
  toFun x := ⟨⟨x.down⟩⟩
  invFun x := ⟨x.down.down⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x with | up x => cases x; rfl
  map_add' x y := rfl
  map_smul' r x := rfl

/-- Lifting a complex directly to the join of two universes agrees with lifting it twice. -/
noncomputable def uliftCompComplexIso
    {R : Type u} [CommRing R] (I : CochainComplex (ModuleCat.{v} R) ℤ) :
    (((ModuleCat.uliftFunctor.{max u w, v} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) ≅
    (((ModuleCat.uliftFunctor.{w, max u v} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((ModuleCat.uliftFunctor.{u, v} R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) := by
  apply HomologicalComplex.Hom.isoOfComponents
    (fun i => (uliftCompLinearEquiv (I.X i)).toModuleIso)

/-- Conjugation by a complex isomorphism identifies its endomorphism complexes. -/
noncomputable def homComplexCongrIso
    {R : Type u} [CommRing R] {I J : CochainComplex (ModuleCat.{v} R) ℤ}
    (e : I ≅ J) :
    CochainComplex.HomComplexR R I I ≅ CochainComplex.HomComplexR R J J := by
  let p : CochainComplex.HomComplexR R I I ≅ CochainComplex.HomComplexR R J I := {
    hom := Stacks.HomComplex.TensorHomMap.precomp R J I I e.inv
    inv := Stacks.HomComplex.TensorHomMap.precomp R I J I e.hom
    hom_inv_id := by simp [← Stacks.HomComplex.TensorHomMap.precomp_comp]
    inv_hom_id := by simp [← Stacks.HomComplex.TensorHomMap.precomp_comp] }
  let q : CochainComplex.HomComplexR R J I ≅ CochainComplex.HomComplexR R J J := {
    hom := Stacks.HomComplex.TensorHomMap.postcomp R J I J e.hom
    inv := Stacks.HomComplex.TensorHomMap.postcomp R J J I e.inv
    hom_inv_id := by simp [← Stacks.HomComplex.TensorHomMap.postcomp_comp]
    inv_hom_id := by simp [← Stacks.HomComplex.TensorHomMap.postcomp_comp] }
  exact p ≪≫ q

/-- A unital scalar action on a rank-one free endomorphism module is an isomorphism. -/
private theorem bijective_algebraMap_end_of_linearEquiv
    {R : Type u} [CommRing R] {C : Type uC} [Category.{vC} C]
    [Preadditive C] [Linear R C] (X : C)
    (e : R ≃ₗ[R] End X) : Function.Bijective (algebraMap R (End X)) := by
  by_cases h : Subsingleton R
  · have : Subsingleton (End X) := Equiv.subsingleton e.symm.toEquiv
    exact ⟨fun x y _ => Subsingleton.elim x y, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  · let : Nontrivial R := not_subsingleton_iff_nontrivial.mp h
    let : Module.Free R (End X) := Module.Free.of_equiv' inferInstance e
    have hrank : Module.finrank R (End X) = 1 :=
      (Module.nonempty_linearEquiv_iff_finrank_eq_one).mp ⟨e⟩
    exact Module.Free.bijective_algebraMap_of_finrank_eq_one hrank

/-- Zeroth Hom-complex homology identifies additively with derived endomorphisms. -/
noncomputable def homologyZeroEndAddEquiv
    {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{v} R) ℤ) [J.IsKInjective] :
    (CochainComplex.HomComplexR R J J).homology 0 ≃+
      End (DerivedCategory.Q.obj J) := by
  let V := forget₂ (ModuleCat.{v} R) AddCommGrpCat
  let H := CochainComplex.HomComplexR R J J
  let eV : (H.homology 0) ≃+ (J.HomComplex J).homology 0 :=
    ((H.sc 0).mapHomologyIso V).symm.addCommGroupIsoToAddEquiv
  let eH := (CochainComplex.HomComplex.homologyAddEquiv J J 0).trans
    (cohomologyClassRHomAddEquivOfIsKInjective J J 0)
  let q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let eSrc : DerivedCategory.Qh.obj (q.obj J) ≅ DerivedCategory.Q.obj J :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app J
  let zJ : J ≅ J⟦(0 : ℤ)⟧ :=
    ((shiftFunctorZero (CochainComplex (ModuleCat.{v} R) ℤ) ℤ).app J).symm
  let eTgt : DerivedCategory.Qh.obj (q.obj (J⟦(0 : ℤ)⟧)) ≅
      DerivedCategory.Q.obj J :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app (J⟦(0 : ℤ)⟧) ≪≫
      DerivedCategory.Q.mapIso zJ.symm
  let f : (DerivedCategory.Qh.obj (q.obj J) ⟶
      DerivedCategory.Qh.obj (q.obj (J⟦(0 : ℤ)⟧))) →+
      End (DerivedCategory.Q.obj J) := {
    toFun := fun x => eSrc.inv ≫ x ≫ eTgt.hom
    map_zero' := by simp
    map_add' := by intro x y; simp }
  let eEnd : (DerivedCategory.Qh.obj (q.obj J) ⟶
      DerivedCategory.Qh.obj (q.obj (J⟦(0 : ℤ)⟧))) ≃+
      End (DerivedCategory.Q.obj J) :=
    AddEquiv.ofBijective f (Iso.homCongr eSrc eTgt).bijective
  exact eV.trans (eH.trans eEnd)

/-- A cycle of the endomorphism complex, read as a cocycle of cochains. -/
private noncomputable def cyclesCocycle {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (z : (CochainComplex.HomComplexR R J J).cycles n) :
    CochainComplex.HomComplex.Cocycle J J n :=
  CochainComplex.HomComplex.Cocycle.mk
    (((CochainComplex.HomComplexR R J J).iCycles n).hom z) (n + 1) rfl
    (ConcreteCategory.congr_hom
      (HomologicalComplex.iCycles_d (CochainComplex.HomComplexR R J J) n (n + 1)) z)

private theorem forgetHomologyπ {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (z : (CochainComplex.HomComplexR R J J).cycles n) :
    (CochainComplex.HomComplex.homologyAddEquiv J J n)
      (((((CochainComplex.HomComplexR R J J).sc n).mapHomologyIso
        (forget₂ (ModuleCat.{v} R) AddCommGrpCat)).inv).hom
          (((CochainComplex.HomComplexR R J J).homologyπ n).hom z)) =
      CochainComplex.HomComplex.CohomologyClass.mk (cyclesCocycle J n z) := by
  let H := CochainComplex.HomComplexR R J J
  let V := forget₂ (ModuleCat.{v} R) AddCommGrpCat
  let h := CochainComplex.HomComplex.leftHomologyData J J n
  let h₀ := (H.sc n).leftHomologyData
  let hV := h₀.map V
  have hh : h₀.cyclesIso.hom = 𝟙 _ :=
    (cancel_mono h₀.i).mp (h₀.cyclesIso_hom_comp_i.trans (Category.id_comp h₀.i).symm)
  have hmap : ((H.sc n).mapHomologyIso V).inv =
      V.map h₀.homologyIso.hom ≫ hV.homologyIso.inv :=
    congrArg Iso.inv (h₀.mapHomologyIso_eq V)
  have hπι : (H.sc n).homologyπ ≫ h₀.homologyIso.hom = h₀.π :=
    h₀.homologyπ_comp_homologyIso_hom.trans
      ((congrArg (fun f : (H.sc n).cycles ⟶ h₀.K => f ≫ h₀.π) hh).trans
        (Category.id_comp h₀.π))
  have hstep₁ : V.map (H.sc n).homologyπ ≫ ((H.sc n).mapHomologyIso V).inv =
      V.map (H.sc n).homologyπ ≫ V.map h₀.homologyIso.hom ≫ hV.homologyIso.inv :=
    congrArg (fun f => V.map (H.sc n).homologyπ ≫ f) hmap
  have hstep₂ :
      V.map (H.sc n).homologyπ ≫ V.map h₀.homologyIso.hom ≫ hV.homologyIso.inv =
        V.map ((H.sc n).homologyπ ≫ h₀.homologyIso.hom) ≫ hV.homologyIso.inv :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ hV.homologyIso.inv)
        (V.map_comp (H.sc n).homologyπ h₀.homologyIso.hom).symm)
  have hstep₃ :
      V.map ((H.sc n).homologyπ ≫ h₀.homologyIso.hom) ≫ hV.homologyIso.inv =
        hV.cyclesIso.inv ≫ ((H.sc n).map V).homologyπ :=
    (congrArg (fun g => V.map g ≫ hV.homologyIso.inv) hπι).trans
      hV.π_comp_homologyIso_inv
  have hπeq := hstep₁.trans (hstep₂.trans hstep₃)
  have hπ := ConcreteCategory.congr_hom hπeq z
  change ((H.sc n).mapHomologyIso V).inv.hom ((H.homologyπ n).hom z) =
    ((J.HomComplex J).homologyπ n).hom (hV.cyclesIso.inv.hom z) at hπ
  rw [hπ]
  have hπ' := ConcreteCategory.congr_hom
    (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom _ h)
      (hV.cyclesIso.inv.hom z)
  change _ = CochainComplex.HomComplex.CohomologyClass.mk
    (h.cyclesIso.hom.hom (hV.cyclesIso.inv.hom z)) at hπ'
  refine hπ'.trans ?_
  congr 1
  apply Subtype.ext
  have h₁ := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i
    (hV.cyclesIso.inv.hom z)
  have h₂ := ConcreteCategory.congr_hom hV.cyclesIso_inv_comp_iCycles z
  exact h₁.trans h₂

private theorem equivHomShift_zero {R : Type u} [CommRing R]
    {J : CochainComplex (ModuleCat.{v} R) ℤ}
    (z : CochainComplex.HomComplex.Cocycle J J 0) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm z ≫
      (shiftFunctorZero (CochainComplex (ModuleCat.{v} R) ℤ) ℤ).hom.app J = z.homOf := by
  ext i : 1
  simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.HomComplex.Cocycle.homOf,
    CochainComplex.HomComplex.Cochain.rightShift_v,
    CochainComplex.shiftFunctorZero_hom_app_f]

private theorem homologyZeroEndAddEquiv_π {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{v} R) ℤ) [J.IsKInjective]
    (z : (CochainComplex.HomComplexR R J J).cycles 0) :
    homologyZeroEndAddEquiv J (((CochainComplex.HomComplexR R J J).homologyπ 0).hom z) =
      DerivedCategory.Q.map (cyclesCocycle J 0 z).homOf := by
  let η := DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)
  let V := forget₂ (ModuleCat.{v} R) AddCommGrpCat
  let H := CochainComplex.HomComplexR R J J
  change (η.app J).inv ≫ DerivedCategory.Qh.map
    (CochainComplex.HomComplex.CohomologyClass.toHom
      ((CochainComplex.HomComplex.homologyAddEquiv J J 0)
        (((H.sc 0).mapHomologyIso V).inv.hom ((H.homologyπ 0).hom z)))) ≫
    ((η.app (J⟦(0 : ℤ)⟧)).hom ≫ DerivedCategory.Q.map
      ((shiftFunctorZero (CochainComplex (ModuleCat.{v} R) ℤ) ℤ).hom.app J)) = _
  rw [forgetHomologyπ, CochainComplex.HomComplex.CohomologyClass.toHom_mk]
  have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.naturality
    (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (cyclesCocycle J 0 z))
  change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
        (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (cyclesCocycle J 0 z))) ≫
      (η.app _).hom = (η.app J).hom ≫ DerivedCategory.Q.map _ at hnat
  rw [← Category.assoc (DerivedCategory.Qh.map _) (η.app _).hom, hnat]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
    equivHomShift_zero]

/-- Zeroth Hom-complex homology identifies `R`-linearly with derived endomorphisms. -/
noncomputable def homologyZeroEndLinearEquiv {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{v} R) ℤ) [J.IsKInjective] :
    (CochainComplex.HomComplexR R J J).homology 0 ≃ₗ[R]
      End (DerivedCategory.Q.obj J) :=
  { homologyZeroEndAddEquiv J with
    map_smul' := by
      intro r x
      obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
        ((CochainComplex.HomComplexR R J J).homologyπ 0)).mp inferInstance x
      change homologyZeroEndAddEquiv J (r • _) = r • homologyZeroEndAddEquiv J _
      rw [← map_smul, homologyZeroEndAddEquiv_π, homologyZeroEndAddEquiv_π]
      change DerivedCategory.Q.map (cyclesCocycle J 0 (r • z)).homOf = _
      have heq : (cyclesCocycle J 0 (r • z)).homOf =
          r • (cyclesCocycle J 0 z).homOf := by
        ext i : 1
        change (((CochainComplex.HomComplexR R J J).iCycles 0).hom (r • z)).v i i _ =
          r • (((CochainComplex.HomComplexR R J J).iCycles 0).hom z).v i i _
        have hsmul : ((CochainComplex.HomComplexR R J J).iCycles 0).hom (r • z) =
            r • ((CochainComplex.HomComplexR R J J).iCycles 0).hom z := map_smul _ r z
        rw [hsmul]
        rfl
      rw [heq, Functor.map_smul] }

/-- The scalar homothety before forgetting the module structure. -/
noncomputable def moduleScalarHomothety {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj
      (ModuleCat.of R (ULift.{max u v} R)) ⟶ CochainComplex.HomComplexR R J J :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom ((LinearMap.smulRight (LinearMap.id : R →ₗ[R] R)
      (CochainComplex.HomComplex.Cochain.ofHom (𝟙 J))).comp
        (ULift.moduleEquiv (R := R)).toLinearMap)) (by
      intro k hk
      obtain rfl : (1 : ℤ) = k := by simpa using hk
      ext x
      change CochainComplex.HomComplex.δ 0 1
        (x.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 J)) = 0
      simp)

private theorem moduleScalarHomothety_homology_zero {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective]
    (x : ULift.{max u v} R) :
    homologyZeroEndLinearEquiv J
      ((HomologicalComplex.homologyMap (moduleScalarHomothety J) 0).hom
        ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
          (ModuleCat.of R (ULift.{max u v} R))).inv.hom x)) =
      algebraMap R (End (DerivedCategory.Q.obj J)) x.down := by
  let H := CochainComplex.HomComplexR R J J
  let M := ModuleCat.of R (ULift.{max u v} R)
  let eC := HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 M
  let eH := HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M
  let z := (HomologicalComplex.cyclesMap (moduleScalarHomothety J) 0).hom (eC.inv.hom x)
  have hmap : (HomologicalComplex.homologyMap (moduleScalarHomothety J) 0).hom
      (eH.inv.hom x) = (H.homologyπ 0).hom z := by
    have heq := congrArg (fun f => eC.inv ≫ f)
      (HomologicalComplex.homologyπ_naturality (moduleScalarHomothety J) 0)
    change eC.inv ≫
      ((HomologicalComplex.single (ModuleCat.{max u v} R)
        (ComplexShape.up ℤ) 0).obj M).homologyπ 0 ≫
        HomologicalComplex.homologyMap (moduleScalarHomothety J) 0 = _ at heq
    rw [← Category.assoc, HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ] at heq
    exact ConcreteCategory.congr_hom heq x
  have hz : cyclesCocycle J 0 z =
      CochainComplex.HomComplex.Cocycle.ofHom (x.down • 𝟙 J) := by
    apply Subtype.ext
    have heq := congrArg (fun f => eC.inv ≫ f)
      (HomologicalComplex.cyclesMap_i (moduleScalarHomothety J) 0)
    have hx := ConcreteCategory.congr_hom heq x
    change (H.iCycles 0).hom z = _ at hx
    change (H.iCycles 0).hom z = _
    rw [hx]
    have heq' : eC.inv ≫
        (((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M).iCycles 0) ≫
          (moduleScalarHomothety J).f 0 =
        ModuleCat.ofHom ((LinearMap.smulRight (LinearMap.id : R →ₗ[R] R)
          (CochainComplex.HomComplex.Cochain.ofHom (𝟙 J))).comp
            (ULift.moduleEquiv (R := R)).toLinearMap) := by
      change eC.inv ≫
        ((HomologicalComplex.single (ModuleCat.{max u v} R)
          (ComplexShape.up ℤ) 0).obj M).iCycles 0 ≫ _ = _
      rw [← Category.assoc, HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles]
      have hf : (moduleScalarHomothety J).f 0 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom ≫
            ModuleCat.ofHom ((LinearMap.smulRight (LinearMap.id : R →ₗ[R] R)
              (CochainComplex.HomComplex.Cochain.ofHom (𝟙 J))).comp
                (ULift.moduleEquiv (R := R)).toLinearMap) :=
        HomologicalComplex.mkHomFromSingle_f _ _
      rw [hf]
      exact Iso.inv_hom_id_assoc _ _
    change _ = CochainComplex.HomComplex.Cochain.ofHom (x.down • 𝟙 J)
    rw [show _ = x.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 J) from
      ConcreteCategory.congr_hom heq' x]
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    obtain rfl : j = i := by omega
    rfl
  change homologyZeroEndAddEquiv J
    ((HomologicalComplex.homologyMap (moduleScalarHomothety J) 0).hom (eH.inv.hom x)) = _
  rw [hmap, homologyZeroEndAddEquiv_π, hz,
    CochainComplex.HomComplex.Cocycle.homOf_ofHom_eq_self, Functor.map_smul,
    CategoryTheory.Functor.map_id]
  rfl

/-- Rank one of derived endomorphisms makes the canonical scalar homothety invertible. -/
private theorem isIso_homologyMap_moduleScalarHomothety {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective]
    (e : (CochainComplex.HomComplexR R J J).homology 0 ≃ₗ[R] R) :
    IsIso (HomologicalComplex.homologyMap (moduleScalarHomothety J) 0) := by
  let eEnd := homologyZeroEndLinearEquiv J
  let eS := HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
    (ModuleCat.of R (ULift.{max u v} R))
  let f := HomologicalComplex.homologyMap (moduleScalarHomothety J) 0
  have hAlg := bijective_algebraMap_end_of_linearEquiv (DerivedCategory.Q.obj J)
    (e.symm.trans eEnd)
  have hc : Function.Bijective
      ((eEnd : _ → _) ∘ f.hom ∘ eS.inv.hom) := by
    have heq : ((eEnd : _ → _) ∘ f.hom ∘ eS.inv.hom) =
        (algebraMap R (End (DerivedCategory.Q.obj J))) ∘
          (ULift.moduleEquiv (R := R) (M := R) : ULift.{max u v} R → R) := by
      funext x
      exact moduleScalarHomothety_homology_zero J x
    rw [heq]
    exact hAlg.comp (ULift.moduleEquiv (R := R) (M := R)).bijective
  have hc' : Function.Bijective (f.hom ∘ eS.inv.hom) :=
    hc.of_comp_left eEnd.injective
  exact (ConcreteCategory.isIso_iff_bijective f).2
    ((Function.Bijective.of_comp_iff f.hom eS.toLinearEquiv.symm.bijective).1 hc')

/-- The additive homothety `A[0] ⟶ Hom^•(J, J)` of `Dualizing.homothety` and the `R`-linear
`Dualizing.moduleScalarHomothety` differ only by the isomorphisms comparing the forgetful image of
`Hom^•_R(J, J)` with its universe lift, so one is a quasi-isomorphism exactly when the other is. -/
theorem quasiIso_homothety_iff_moduleScalarHomothety {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    QuasiIso (homothety J) ↔ QuasiIso (moduleScalarHomothety J) := by
  let V := forget₂ (ModuleCat.{max u v} R) AddCommGrpCat
  let H := CochainComplex.HomComplexR R J J
  let eLift : (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj H ≅
      liftedEndomorphismComplex J :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => (AddEquiv.ulift.symm :
        CochainComplex.HomComplex.Cochain J J n ≃+
          ULift.{u} (CochainComplex.HomComplex.Cochain J J n)).toAddCommGrpIso)
  let eS := (Functor.mapCochainComplexSingleFunctor V 0).app
    (ModuleCat.of R (ULift.{max u v} R))
  have hEq : eS.inv ≫
      (V.mapHomologicalComplex (ComplexShape.up ℤ)).map (moduleScalarHomothety J) ≫
        eLift.hom = homothety J := by
    apply HomologicalComplex.from_single_hom_ext
    ext x
    rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hmap : (V.mapHomologicalComplex (ComplexShape.up ℤ)).map (moduleScalarHomothety J) =
        eS.hom ≫ homothety J ≫ eLift.inv := by
      rw [← hEq]
      simp
    have : QuasiIso ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (moduleScalarHomothety J)) := by
      rw [hmap]
      infer_instance
    exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      (moduleScalarHomothety J) V).1 this
  · rw [← hEq]
    infer_instance

/-- A rank-one zeroth endomorphism module and vanishing in the other degrees imply
that the canonical homothety is a quasi-isomorphism. -/
theorem quasiIso_homothety_of_rankOne {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) [J.IsKInjective]
    (e : (CochainComplex.HomComplexR R J J).homology 0 ≃ₗ[R] R)
    (hz : ∀ n : ℤ, n ≠ 0 → IsZero ((CochainComplex.HomComplexR R J J).homology n)) :
    QuasiIso (homothety J) := by
  refine (quasiIso_homothety_iff_moduleScalarHomothety J).2 ?_
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hn : n = 0
  · subst n
    exact isIso_homologyMap_moduleScalarHomothety J e
  · exact IsZero.isIso
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
        (ModuleCat.of R (ULift.{max u v} R)) n hn) (hz n hn) _

/-- A functor preserving zero morphisms preserves strict lower bounds of complexes. -/
private theorem isStrictlyGE_map_obj {R : Type*} {S : Type*} [Category R] [Category S]
    [HasZeroMorphisms R] [HasZeroMorphisms S] (F : R ⥤ S) [F.PreservesZeroMorphisms]
    (K : CochainComplex R ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi => F.map_isZero ((CochainComplex.isStrictlyGE_iff K a).mp ‹_› i hi)

/-- A bounded-below injective representative computes mixed-universe derived internal Hom. -/
noncomputable def derivedInternalHomModelIso
    {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hInj : ∀ i, Injective (I.X i)) :
    (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v} R).obj
        (Opposite.op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR R I I) := by
  let S := ULift.{max u v} R
  let e : S ≃+* R := ULift.ringEquiv
  let F := ModuleCat.restrictScalars.{max u v} e.toRingHom
  let G := ModuleCat.restrictScalars.{max u v} e.symm.toRingHom
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} R
  let J : CochainComplex (ModuleCat.{max u v} S) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  haveI : J.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Functor.map_isZero F ((CochainComplex.isStrictlyGE_iff I a).mp hGE i hi)
  haveI : ∀ i, Injective (J.X i) := by
    intro i
    change Injective (F.obj (I.X i))
    let : Injective (I.X i) := hInj i
    infer_instance
  haveI : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  let eJ : E.functor.obj (DerivedCategory.Q.obj I) ≅ DerivedCategory.Q.obj J :=
    F.mapDerivedCategoryFactors.app I
  let eH := Stacks.DerivedHom.BaseChange.homModelIso J J eJ eJ
  let eG := G.mapDerivedCategoryFactors.app (CochainComplex.HomComplexR S J J)
  let eC := homComplexRestrictScalarsIso e.symm J
  let eM := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let eI : I ≅ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
    eM.unitIso.app I
  exact E.inverse.mapIso eH ≪≫ eG ≪≫
    DerivedCategory.Q.mapIso eC ≪≫
    DerivedCategory.Q.mapIso (homComplexCongrIso eI.symm)

/-- The additive homothety, viewed as a morphism of modules after lifting its
endomorphism complex to the common scalar/module universe. -/
noncomputable def liftedModuleHomothety {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{v} R) ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj
        (ModuleCat.of R (ULift.{v} R)) ⟶
      ((ModuleCat.uliftFunctor.{u} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.HomComplexR R I I) := by
  let smul : R →ₗ[R] CochainComplex.HomComplex.Cochain I I 0 :=
    LinearMap.smulRight (LinearMap.id : R →ₗ[R] R)
      (CochainComplex.HomComplex.Cochain.ofHom (𝟙 I))
  let f : ULift.{v} R →ₗ[R]
      (((ModuleCat.uliftFunctor.{u} R).obj
        ((CochainComplex.HomComplexR R I I).X 0)) : Type max u v) :=
    (ULift.moduleEquiv.{u, v, u} (R := R)
      (M := CochainComplex.HomComplex.Cochain I I 0)).symm.toLinearMap.comp
      (smul.comp (ULift.moduleEquiv.{u, u, v} (R := R) (M := R)).toLinearMap)
  exact HomologicalComplex.mkHomFromSingle (ModuleCat.ofHom f) (by
    intro k hk
    have hk' : (1 : ℤ) = k := by simpa using hk
    subst k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change ULift.up (CochainComplex.HomComplex.δ 0 1
      (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I))) = 0
    apply ULift.ext
    simp)

/-- Forgetting the module structure turns the module-valued homothety back into the additive
homothety, up to the comparison of the two single-object complexes. -/
private theorem liftedModuleHomothety_forget {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{v} R) ℤ) :
    let V := forget₂ (ModuleCat.{max u v} R) AddCommGrpCat
    let g := (V.mapHomologicalComplex (ComplexShape.up ℤ)).map (liftedModuleHomothety I)
    let e := (Functor.mapCochainComplexSingleFunctor V 0).app
      (ModuleCat.of R (ULift.{v} R))
    e.inv ≫ g = homothety I := by
  dsimp only
  apply HomologicalComplex.from_single_hom_ext
  ext a
  rfl

/-- The module-valued homothety is a quasi-isomorphism as soon as the additive one is. -/
theorem quasiIso_liftedModuleHomothety {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{v} R) ℤ)
    (hI : QuasiIso (homothety I)) : QuasiIso (liftedModuleHomothety I) := by
  let V := forget₂ (ModuleCat.{max u v} R) AddCommGrpCat
  let g := (V.mapHomologicalComplex (ComplexShape.up ℤ)).map (liftedModuleHomothety I)
  let e := (Functor.mapCochainComplexSingleFunctor V 0).app
    (ModuleCat.of R (ULift.{v} R))
  have hcomp : QuasiIso (e.inv ≫ g) := by
    rw [liftedModuleHomothety_forget]
    exact hI
  have hg : QuasiIso g := quasiIso_of_comp_left e.inv g
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (liftedModuleHomothety I) V).1 hg

/-- The scalar homothety map into the Hom complex of the universe-lifted representative. -/
noncomputable def firstLiftHomothety {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{v} R) ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj
        (ModuleCat.of R (ULift.{v} R)) ⟶
      CochainComplex.HomComplexR R
        (((ModuleCat.uliftFunctor.{u, v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
        (((ModuleCat.uliftFunctor.{u, v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
  liftedModuleHomothety I ≫ (homComplexULiftIso.{u, v, u} I I).hom

private theorem firstLiftHomothety_quasiIso {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{v} R) ℤ)
    (hI : QuasiIso (homothety I)) :
    QuasiIso (firstLiftHomothety I) := by
  unfold firstLiftHomothety
  let : QuasiIso (liftedModuleHomothety I) := quasiIso_liftedModuleHomothety I hI
  infer_instance

private theorem secondLiftHomothety_quasiIso {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{v} R) ℤ)
    (hI : QuasiIso (homothety I)) :
    let I₁ := ((ModuleCat.uliftFunctor.{u, v} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
    let U₂ := ModuleCat.uliftFunctor.{w, max u v} R
    QuasiIso (((U₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (firstLiftHomothety I)) ≫ (homComplexULiftIso.{u, max u v, w} I₁ I₁).hom) := by
  dsimp only
  let U₂ := ModuleCat.uliftFunctor.{w, max u v} R
  have hmap : QuasiIso ((U₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (firstLiftHomothety I)) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      (firstLiftHomothety I) U₂).2 (firstLiftHomothety_quasiIso I hI)
  infer_instance

/-- The source homothety, transported into the module universe used by base change. -/
noncomputable def sourceHomothetyAtCommonUniverse {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{v} R) ℤ) :
    let Iu := ((ModuleCat.uliftFunctor.{max u w, v} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
    let U₂ := ModuleCat.uliftFunctor.{w, max u v} R
    (U₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))) ⟶
      CochainComplex.HomComplexR R Iu Iu := by
  dsimp only
  let I₁ := ((ModuleCat.uliftFunctor.{u, v} R).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  let U₂ := ModuleCat.uliftFunctor.{w, max u v} R
  exact (U₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (firstLiftHomothety I) ≫
    (homComplexULiftIso.{u, max u v, w} I₁ I₁).hom ≫
    (homComplexCongrIso (uliftCompComplexIso.{u, v, w} I).symm).hom

/-- The transported source homothety is a quasi-isomorphism as soon as the additive homothety
of the representative is. -/
theorem sourceHomothetyAtCommonUniverse_quasiIso {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{v} R) ℤ)
    (hI : QuasiIso (homothety I)) :
    QuasiIso (sourceHomothetyAtCommonUniverse.{u, v, w} I) := by
  dsimp only [sourceHomothetyAtCommonUniverse, id_eq]
  let : QuasiIso (((ModuleCat.uliftFunctor.{w, max u v} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (firstLiftHomothety I) ≫
      (homComplexULiftIso.{u, max u v, w}
        (((ModuleCat.uliftFunctor.{u, v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
        (((ModuleCat.uliftFunctor.{u, v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)).hom) :=
    secondLiftHomothety_quasiIso I hI
  rw [← Category.assoc]
  infer_instance

/-- The base ring of a dualizing complex is small relative to the module universe. -/
theorem small_base_from_dualizing {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : IsDualizingComplex K) : Small.{v} A := by
  obtain ⟨a, b, hAmp⟩ := hK.finiteInjectiveDimension
  obtain ⟨I, hGE, hLE, hIinj, hIrep⟩ := hAmp
  obtain ⟨e⟩ := hIrep
  have hQI := hK.homothetyQuasiIso I ⟨e.symm⟩ hIinj ⟨a, b, hGE, hLE⟩
  let H := HomologicalComplex.homologyMap (homothety I) 0
  have hIso : IsIso H :=
    (quasiIsoAt_iff_isIso_homologyMap (homothety I) 0).mp (hQI.quasiIsoAt 0)
  let AS := AddCommGrpCat.of (ULift.{v} A)
  let e0 := HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.up ℤ) 0 AS
  let target := (liftedEndomorphismComplex I).homology 0
  let f : ULift.{v} A → target := fun x => H.hom (e0.inv.hom x)
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : e0.inv.hom x = e0.inv.hom y :=
      (ConcreteCategory.isIso_iff_bijective H).1 hIso |>.1 hxy
    exact ((ConcreteCategory.isIso_iff_bijective e0.inv).1
      (by infer_instance : IsIso e0.inv)).1 hxy'
  let HC := CochainComplex.HomComplex I I
  let F := AddCommGrpCat.uliftFunctor.{u, v}
  let eC := (HC.sc 0).mapHomologyIso F
  have hsmallF : Small.{v} (F.obj (HC.sc 0).homology) := by
    let : Small.{v} (HC.sc 0).homology := inferInstance
    exact small_of_surjective (f := fun x => (ULift.up x)) ULift.up_surjective
  have hsmallTarget : Small.{v} target := by
    change Small.{v} ((HC.sc 0).map F).homology
    let : Small.{v} (F.obj (HC.sc 0).homology) := hsmallF
    exact small_of_injective (f := eC.hom.hom)
      ((ConcreteCategory.isIso_iff_bijective eC.hom).1 (by infer_instance)).1
  let : Small.{v} target := hsmallTarget
  have hsmallULift : Small.{v} (ULift.{v} A) := small_of_injective hf
  exact small_of_injective (f := fun x : A => (⟨x⟩ : ULift.{v} A))
    fun _ _ h => congrArg ULift.down h

private theorem localized_extension_injective {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (S : Submonoid A) [IsLocalization S B] [Small.{v} A]
    (M : ModuleCat.{v} A) [Injective M] :
    Injective ((ModuleCat.extendScalars (algebraMap A B)).obj
      ((ModuleCat.uliftFunctor.{max u w} A).obj M)) := by
  let U := ModuleCat.uliftFunctor.{max u w} A
  let F := ModuleCat.extendScalars.{u, w, max v u w} (algebraMap A B)
  let T := TensorProduct A B (M : Type v)
  have hT : Module.Injective B T := by
    let : Module.Injective A (M : Type v) :=
      (Module.injective_iff_injective_object A M).mpr inferInstance
    let f : M →ₗ[A] TensorProduct A B (M : Type v) := TensorProduct.mk A B M 1
    let : IsLocalizedModule S f :=
      IsLocalization.tensorProduct_isLocalizedModule (S := S) (A := B) (M := M)
    exact Module.injective_of_isLocalizedModule S f
  let : Small.{max u w v} B := inferInstance
  have hLift : Module.Injective B (ULift.{max u w, max w v} T) :=
    Module.ulift_injective_of_injective.{w, max w v, max u w} B hT
  let B_A := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  let : IsScalarTower A B B_A :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let eB : B ≃ₗ[B] B_A := LinearEquiv.refl B B
  let eM : (M : Type v) ≃ₗ[A] ULift.{max u w, v} (M : Type v) :=
    (ULift.moduleEquiv (R := A)).symm
  let e := (ULift.moduleEquiv (R := B)).trans
    (TensorProduct.AlgebraTensorModule.congr eB eM)
  let eIso : ModuleCat.of B (ULift.{max u w, max w v} T) ≅
      F.obj (U.obj M) := by
    change ModuleCat.of B (ULift.{max u w, max w v} T) ≅
      ModuleCat.of B (TensorProduct A B_A (ULift.{max u w, v} (M : Type v)))
    exact e.toModuleIso
  let : Injective (ModuleCat.of B (ULift.{max u w, max w v} T)) :=
    (Module.injective_iff_injective_object B (ULift.{max u w, max w v} T)).mp hLift
  exact Injective.of_iso eIso inferInstance

/-- The cohomology modules of the universe lift of a dualizing complex are finite. -/
private theorem finite_homology_lift {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K) (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor
      (ModuleCat.{max (max u v) w} A) i).obj
      ((ModuleCat.uliftFunctor.{max u w} A).mapDerivedCategory.obj K)) := by
  let U := ModuleCat.uliftFunctor.{max u w} A
  have eU := (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso U i).app K
  let : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K) :=
    hK.finiteCohomology i
  have hfinite : Module.Finite A
      (U.obj ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) :=
    Module.Finite.equiv ULift.moduleEquiv.symm
  let : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i ⋙ U).obj K) := by
    simpa only [Functor.comp_obj] using hfinite
  exact Module.Finite.equiv eU.toLinearEquiv.symm

private theorem lifted_pseudoCoherent {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{v} A))
    (hK : IsDualizingComplex K) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.uliftFunctor.{max u w} A).mapDerivedCategory.obj K) := by
  let U := ModuleCat.uliftFunctor.{max u w} A
  let KU := U.mapDerivedCategory.obj K
  obtain ⟨a, b, hAmp⟩ := hK.finiteInjectiveDimension
  obtain ⟨I, hGE, hLE, hIinj, ⟨e⟩⟩ := hAmp
  have hbound : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K) := by
    refine ⟨b, ?_⟩
    intro i hi
    have hz := DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj I) b i hi
    exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).mapIso e)
  have hboundU : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max (max u v) w} A) i).obj KU) := by
    obtain ⟨b, hb⟩ := hbound
    refine ⟨b, ?_⟩
    intro i hi
    have hz := hb i hi
    have eU := (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso U i).app K
    exact (Functor.map_isZero U hz).of_iso eU
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    KU 0 (ULift.{max (max u v) w} A)).2.1.mpr ⟨hboundU, finite_homology_lift K hK⟩

private theorem finiteCohomology_localization {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (S : Submonoid A) [IsLocalization S B]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K) :
    ∀ i : ℤ, Module.Finite B ((DerivedCategory.homologyFunctor
      (ModuleCat.{max (max u v) w} B) i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, w, v}
        (algebraMap A B)).functor.obj
        ((ModuleCat.uliftFunctor.{max u w} A).mapDerivedCategory.obj K))) := by
  intro i
  let U := ModuleCat.uliftFunctor.{max u w} A
  let KU := U.mapDerivedCategory.obj K
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, w, v}
    (algebraMap A B)
  have hf : (algebraMap A B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S)
  have eH := (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, w, v}
    (algebraMap A B) hf i).app KU
  let M := ((DerivedCategory.homologyFunctor (ModuleCat.{max (max u v) w} A) i).obj KU)
  let : Algebra A B := (algebraMap A B).toAlgebra
  let : Module.Finite A M := finite_homology_lift K hK i
  have hExt : Module.Finite B ((ModuleCat.extendScalars (algebraMap A B)).obj
      (ModuleCat.of A M)) := by
    change Module.Finite B (TensorProduct A B M)
    exact Module.Finite.base_change A B M
  let : Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{max (max u v) w} A) i ⋙
        ModuleCat.extendScalars (algebraMap A B)).obj KU) := by
    simpa only [Functor.comp_obj, M] using hExt
  exact Module.Finite.equiv eH.toLinearEquiv.symm

private theorem localized_extension_model {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (S : Submonoid A) [IsLocalization S B]
    (J : CochainComplex (ModuleCat.{max v u w} A) ℤ) :
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, w, v}
      (algebraMap A B)).comparison.app J) := by
  let hf : (algebraMap A B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S)
  let : Algebra A B := (algebraMap A B).toAlgebra
  let F := CochainComplex.DerivedTensor.extensionScalars.{u, w, v} (algebraMap A B)
  have : F.PreservesHomology :=
    CochainComplex.DerivedTensor.extensionScalars_preservesHomology.{u, w, v}
      (algebraMap A B) hf
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, w, v}
    (algebraMap A B)
  have : IsIso D.comparison := by
    apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts D.functor D.comparison
      (W := HomologicalComplex.quasiIso (ModuleCat.{max v u w} A) (ComplexShape.up ℤ))
    intro X Y g hg
    have : QuasiIso g := hg
    change IsIso (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g))
    infer_instance
  infer_instance

/-- Extension of scalars along `A → B` carries the universe-lifted scalar module `A` to `B`. -/
noncomputable def localized_baseModuleEquiv {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] [Algebra A B] :
    ((ModuleCat.extendScalars.{u, w, max v u w} (algebraMap A B)).obj
      ((ModuleCat.uliftFunctor.{w, max u v} A).obj
        (ModuleCat.of A (ULift.{v} A)))) ≃ₗ[B] B := by
  let B_A := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B B_A :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let eB : B_A ≃ₗ[B] B := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by intro a x; rfl }
  let eM : ULift.{w, max u v} (ULift.{v} A) ≃ₗ[A] A :=
    (ULift.moduleEquiv (R := A)).trans (ULift.moduleEquiv (R := A))
  change TensorProduct A B_A (ULift.{w, max u v} (ULift.{v} A)) ≃ₗ[B] B
  exact (TensorProduct.AlgebraTensorModule.congr eB eM).trans
    (TensorProduct.AlgebraTensorModule.rid A B B)

/-- The derived extension of a dualizing complex along a localization is a dualizing complex
over the localized ring. -/
@[stacks 0A7G]
theorem isDualizingComplex_localization {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] (S : Submonoid A) [IsLocalization S B]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K) :
    @IsDualizingComplex (A := B) inferInstance
      (IsLocalization.isNoetherianRing S B inferInstance) inferInstance
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj K) := by
  let : Small.{v} A := small_base_from_dualizing K hK
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing S B inferInstance
  let U := ModuleCat.uliftFunctor.{max u w} A
  let KU := U.mapDerivedCategory.obj K
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, w, v}
    (algebraMap A B)
  obtain ⟨a, b, I, hGE, hLE, hIinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
  let Iu : CochainComplex (ModuleCat.{max v u w} A) ℤ :=
    (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let F := ModuleCat.extendScalars.{u, w, max v u w} (algebraMap A B)
  let : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v u w, u, w} (algebraMap A B)).isLeftAdjoint
  have : F.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits F; infer_instance)
  have hIuGE : Iu.IsStrictlyGE a := isStrictlyGE_map_obj U I a
  let IB : CochainComplex (ModuleCat.{max v u w} B) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Iu
  have hcomp : IsIso (D.comparison.app Iu) := localized_extension_model S Iu
  let eU : U.mapDerivedCategory.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj Iu := U.mapDerivedCategoryFactors.app I
  let eK : KU ≅ DerivedCategory.Q.obj Iu :=
    U.mapDerivedCategory.mapIso eI ≪≫ eU
  let eB : (StacksDraft.PseudoCoherence.derivedExtensionScalars
      (algebraMap A B)).obj K ≅ DerivedCategory.Q.obj IB :=
    D.functor.mapIso eK ≪≫ @asIso _ _ _ _ (D.comparison.app Iu) hcomp
  refine ⟨⟨a, b, IB, ?_, ?_, ?_, ⟨eB⟩⟩, ?_, ?_⟩
  · exact isStrictlyGE_map_obj F Iu a
  · change IB.IsStrictlyLE b
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have hzero := (CochainComplex.isStrictlyLE_iff I b).mp hLE i hi
    simpa [IB, Iu] using Functor.map_isZero F
      (Functor.map_isZero U hzero)
  · intro i
    change Injective (F.obj (U.obj (I.X i)))
    exact localized_extension_injective S (I.X i)
  · exact finiteCohomology_localization S K hK
  · have hKUge : KU.IsGE a := by
      have hIQge' : (DerivedCategory.Q.obj Iu).IsGE a :=
        (DerivedCategory.isGE_Q_obj_iff Iu a).2 (inferInstance : Iu.IsGE a)
      exact DerivedCategory.TStructure.t.isGE_of_iso eK.symm a
    let hf : (algebraMap A B).Flat :=
      RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S)
    have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent KU :=
      lifted_pseudoCoherent (A := A) (B := B) K hK
    let F0 := CochainComplex.DerivedTensor.extensionScalars.{u, w, v} (algebraMap A B)
    have : F0.PreservesHomology :=
      CochainComplex.DerivedTensor.extensionScalars_preservesHomology.{u, w, v}
        (algebraMap A B) hf
    have : PreservesFiniteLimits F0 := F0.preservesFiniteLimits_of_preservesHomology
    let eComp :
        CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{u, v, w}
        (algebraMap A B) ≅
        F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
      eqToIso rfl
    let α : DerivedCategory.Q ⋙ D.functor ⟶
        F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
      D.comparison ≫ eComp.hom
    have hLD : D.functor.IsLeftDerivedFunctor α
        (HomologicalComplex.quasiIso (ModuleCat.{max v u w} A) (ComplexShape.up ℤ)) := by
      have hright := Functor.IsLeftDerivedFunctor.isRightKanExtension D.functor
        D.comparison
        (HomologicalComplex.quasiIso (ModuleCat.{max v u w} A) (ComplexShape.up ℤ))
      constructor
      exact (Functor.isRightKanExtension_iff_of_iso₂ D.comparison α eComp
        (Iso.refl D.functor) (by simp [α])).mp hright
    let : D.functor.IsLeftDerivedFunctor α
        (HomologicalComplex.quasiIso (ModuleCat.{max v u w} A) (ComplexShape.up ℤ)) := hLD
    let : (ModuleCat.extendScalars.{u, w, max v u w} (algebraMap A B)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max v u w, u, w} (algebraMap A B)).isLeftAdjoint
    let : (ModuleCat.restrictScalars.{max v u w, u, w} (algebraMap A B)).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max v u w, u, w}
        (algebraMap A B)).isRightAdjoint
    let : (ModuleCat.restrictScalars.{max v u w, u, w} (algebraMap A B)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max v u w, u, w}
        (algebraMap A B)).isLeftAdjoint
    have hbc : IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max v u w}
        (algebraMap A B) D.functor α KU KU) :=
      Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, w, max v u w}
        (algebraMap A B) D.functor α KU KU
        (Or.inr (Or.inr (Or.inl ⟨hf, hpc, ⟨a, hKUge⟩⟩)))
    have hIuInj : ∀ i, Injective (Iu.X i) := by
      intro i
      change Injective (U.obj (I.X i))
      let : Injective (I.X i) := hIinj i
      infer_instance
    have hSourceQI : QuasiIso (sourceHomothetyAtCommonUniverse.{u, v, w} I) :=
      sourceHomothetyAtCommonUniverse_quasiIso I
        (hK.homothetyQuasiIso I ⟨eI.symm⟩ hIinj ⟨a, b, hGE, hLE⟩)
    let HRA := Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max v u w} A
    let R₀ := ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A (ULift.{v} A)))
    let eSource : HRA.obj (Opposite.op KU, KU) ≅ DerivedCategory.Q.obj R₀ :=
      HRA.mapIso (eK.symm.op.prod eK) ≪≫
        derivedInternalHomModelIso.{u, max v w} Iu a hIuGE hIuInj ≪≫
          (asIso (DerivedCategory.Q.map
            (sourceHomothetyAtCommonUniverse.{u, v, w} I))).symm
    have hcompR₀ : IsIso (D.comparison.app R₀) := localized_extension_model S R₀
    let : IsIso (D.comparison.app R₀) := hcompR₀
    let HRB := Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{w, max v u w} B
    let eTarget : HRB.obj (Opposite.op (D.functor.obj KU), D.functor.obj KU) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R₀) :=
      (asIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max v u w}
        (algebraMap A B) D.functor α KU KU)).symm ≪≫
        D.functor.mapIso eSource ≪≫
          @asIso _ _ _ _ (D.comparison.app R₀) hcompR₀
    let U₂ := ModuleCat.uliftFunctor.{w, max u v} A
    let M₁ := ModuleCat.of A (ULift.{v} A)
    let eSingle : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R₀ ≅
        (CochainComplex.singleFunctor (ModuleCat.{max v u w} B) 0).obj
          (F.obj (U₂.obj M₁)) :=
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
          ((Functor.mapCochainComplexSingleFunctor U₂ 0).app M₁) ≪≫
        (Functor.mapCochainComplexSingleFunctor F 0).app (U₂.obj M₁)
    let eTargetSingle := eTarget ≪≫ DerivedCategory.Q.mapIso eSingle
    intro J hJ hJinj hJbound
    obtain ⟨c, d, hJGE, hJLE⟩ := hJbound
    let eJ : DerivedCategory.Q.obj J ≅ D.functor.obj KU := Classical.choice hJ
    let eJHom : HRB.obj (Opposite.op (DerivedCategory.Q.obj J), DerivedCategory.Q.obj J) ≅
        HRB.obj (Opposite.op (D.functor.obj KU), D.functor.obj KU) :=
      HRB.mapIso (eJ.symm.op.prod eJ)
    let eJModel :
        HRB.obj (Opposite.op (DerivedCategory.Q.obj J), DerivedCategory.Q.obj J) ≅
        DerivedCategory.Q.obj (CochainComplex.HomComplexR B J J) :=
      derivedInternalHomModelIso.{w, max v u} J c hJGE hJinj
    let eJSingle : DerivedCategory.Q.obj (CochainComplex.HomComplexR B J J) ≅
        DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat.{max v u w} B) 0).obj
            (F.obj (U₂.obj M₁))) :=
      eJModel.symm ≪≫ eJHom ≪≫ eTargetSingle
    let HJ := CochainComplex.HomComplexR B J J
    let MB := F.obj (U₂.obj M₁)
    let SB := (CochainComplex.singleFunctor (ModuleCat.{max v u w} B) 0).obj MB
    let eHn (n : ℤ) : HJ.homology n ≅ SB.homology n :=
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u w} B) n).app HJ).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max v u w} B) n).mapIso eJSingle ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u w} B) n).app SB
    let eH₀B : (HJ.homology 0) ≃ₗ[B] B :=
      (eHn 0 ≪≫ HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 MB
        ).toLinearEquiv.trans (localized_baseModuleEquiv.{u, v, w})
    have hHjZero (n : ℤ) (hn : n ≠ 0) : IsZero (HJ.homology n) :=
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 MB n hn).of_iso
        (eHn n)
    let : J.IsStrictlyGE c := hJGE
    let : ∀ i, Injective (J.X i) := hJinj
    let : J.IsKInjective := CochainComplex.isKInjective_of_injective J c
    exact quasiIso_homothety_of_rankOne J eH₀B hHjZero

end Localization

end Dualizing

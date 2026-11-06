module

public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafUngradedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange
public import StacksFrontier.RingTheory.SymmetricAlgebra.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationLocallySurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of the symmetric algebra of a module sheaf on an algebraic space

Let `ℱ` be a quasi-coherent `𝒪_W`-module on an algebraic space `W`.  The symmetric algebra
`Sym(ℱ)` of `StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion` is the degreewise
sheafification of the sectionwise symmetric algebra `U ↦ Sym_{𝒪(U)}(ℱ(U))`.  Over an affine
étale chart sheafification changes nothing; consequently `Sym(ℱ)` is quasi-coherent, and of
finite presentation when `ℱ` is.

## Main results

* `AlgebraicGeometry.Space.SymAlgSheaf.symSections_bijective`: over an affine étale chart the
  comparison `Sym_{𝒪(U)}(ℱ(U)) → Sym(ℱ)(U)` is bijective.
* `AlgebraicGeometry.Space.SymAlgSheaf.symSections_algebraMap` and
  `AlgebraicGeometry.Space.SymAlgSheaf.symSections_naturality`: the comparison is a natural
  homomorphism of algebras.
* `AlgebraicGeometry.Space.SymAlgSheaf.isQuasicoherent_symmetricAlgebraSheaf`: `Sym(ℱ)` is
  quasi-coherent.
* `AlgebraicGeometry.Space.SymAlgSheaf.isFinitePresentation_symmetricAlgebraSheaf`: `Sym(ℱ)` is
  of finite presentation when `ℱ` is.

## References

* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v₁ u₁ w

namespace Stacks.GradedAlgebra

/-! ### Local injectivity of the ungraded realization of a homomorphism -/

section LocallyInjective

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P Q : ι → PresheafOfModules.{w} R} {A : GradedAlgebra P} {B : GradedAlgebra Q}

/-- The degree-`i` component of a section of the ungraded realization. -/
def component (A : GradedAlgebra P) {X : Cᵒᵖ} (a : A.Total X) (i : ι) : (P i).obj X :=
  DFinsupp.toFun (β := fun i => ((P i).obj X : Type w)) a i

/-- The components of the inclusion of a homogeneous section of degree `j`: the section itself in
degree `j` and zero elsewhere. -/
lemma component_incl (A : GradedAlgebra P) {X : Cᵒᵖ} (j i : ι) (y : (P j).obj X) :
    component A (A.incl j y) i = if h : j = i then h ▸ y else 0 := by
  show (DirectSum.of (fun i => ((P i).obj X : Type w)) j y) i = _
  split_ifs with h
  · subst h; exact DirectSum.of_eq_same _ _
  · exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)

/-- Taking a homogeneous component is additive. -/
lemma component_add (A : GradedAlgebra P) {X : Cᵒᵖ} (a b : A.Total X) (i : ι) :
    component A (a + b) i = component A a i + component A b i :=
  DFinsupp.add_apply (β := fun i => ((P i).obj X : Type w)) a b i

/-- Every homogeneous component of zero is zero. -/
lemma component_zero (A : GradedAlgebra P) {X : Cᵒᵖ} (i : ι) :
    component A (0 : A.Total X) i = 0 :=
  DFinsupp.zero_apply (β := fun i => ((P i).obj X : Type w)) i

/-- A section of the ungraded realization all of whose homogeneous components vanish is zero. -/
lemma eq_zero_of_component (A : GradedAlgebra P) {X : Cᵒᵖ} (a : A.Total X)
    (h : ∀ i, component A a i = 0) : a = 0 :=
  DFinsupp.ext (β := fun i => ((P i).obj X : Type w)) fun i => h i

/-- The homogeneous components of the image of a section of the ungraded realization are the
images of its homogeneous components. -/
lemma component_totalAddHom (f : Hom A B) (X : Cᵒᵖ) (a : A.Total X) (i : ι) :
    component B (totalAddHom f X a) i =
      PresheafOfModules.Hom.app (f.app i) X (component A a i) := by
  induction a using A.incl_induction with
  | zero =>
      rw [map_zero, component_zero, component_zero]
      exact (map_zero (PresheafOfModules.Hom.app (f.app i) X).hom).symm
  | incl j y =>
      rw [totalAddHom_incl, component_incl, component_incl]
      split_ifs with h
      · subst h; rfl
      · exact (map_zero (PresheafOfModules.Hom.app (f.app i) X).hom).symm
  | add a b ha hb =>
      rw [map_add, component_add, component_add, ha, hb]
      exact (map_add (PresheafOfModules.Hom.app (f.app i) X).hom _ _).symm

/-- The homogeneous components of a restricted section of the ungraded realization are the
restrictions of its homogeneous components. -/
lemma component_totalRestrict (A : GradedAlgebra P) {X Y : Cᵒᵖ} (g : X ⟶ Y) (a : A.Total X)
    (i : ι) :
    component A (A.totalRestrict g a) i = sectionRestrict (P i) g (component A a i) := by
  induction a using A.incl_induction with
  | zero => rw [map_zero, component_zero, component_zero, map_zero]
  | incl j y =>
      rw [totalRestrict_incl, component_incl, component_incl]
      split_ifs with h
      · subst h; rfl
      · exact (map_zero (sectionRestrict (P i) g)).symm
  | add a b ha hb =>
      rw [map_add, component_add, component_add, ha, hb, map_add]

/-- A finite intersection of covering sieves is a covering sieve. -/
@[sga "4 II 1.1.1"]
lemma finset_inf_mem {D : Type u₁} [Category.{v₁} D] (K : GrothendieckTopology D) {U : D}
    {κ : Type*} (s : Finset κ) (T : κ → Sieve U) (hT : ∀ i ∈ s, T i ∈ K U) :
    s.inf T ∈ K U := by
  classical
  induction s using Finset.induction_on with
  | empty => exact K.top_mem U
  | insert i s hi ih =>
      rw [Finset.inf_insert]
      exact K.intersection_covering (hT i (Finset.mem_insert_self i s))
        (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

/-- **A homomorphism of graded algebras whose homogeneous pieces are locally injective induces a
locally injective morphism of the ungraded realizations as presheaves of rings.** -/
theorem isLocallyInjective_totalPresheafMap (J : GrothendieckTopology C) (f : UnitalHom A B)
    (hf : ∀ i : ι,
      Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map (f.app i))) :
    Presheaf.IsLocallyInjective J (totalPresheafMap f) := by
  classical
  refine ⟨fun {X} x y hxy => ?_⟩
  let z : A.Total X := x - y
  have hz : totalAddHom f.toHom X z = 0 :=
    (map_sub (totalRingHom f X) x y).trans (sub_eq_zero.mpr hxy)
  have hcomp : ∀ i, PresheafOfModules.Hom.app (f.app i) X (component A z i) = 0 := fun i => by
    rw [← component_totalAddHom, hz, component_zero]
  let T : ι → Sieve X.unop := fun i =>
    Presheaf.equalizerSieve (F := (PresheafOfModules.toPresheaf R).obj (P i))
      (component A z i) 0
  have hT : ∀ i, T i ∈ J X.unop := by
    intro i
    refine (hf i).equalizerSieve_mem (component A z i) 0 ?_
    show PresheafOfModules.Hom.app (f.app i) X (component A z i) =
      PresheafOfModules.Hom.app (f.app i) X 0
    rw [hcomp i, map_zero]
  let supp : Finset ι := DFinsupp.support (β := fun i => ((P i).obj X : Type w)) z
  refine J.superset_covering ?_ (finset_inf_mem J supp T fun i _ => hT i)
  intro Y g hg
  show A.totalRestrict g.op x = A.totalRestrict g.op y
  refine sub_eq_zero.mp ((map_sub (A.totalRestrict g.op) x y).symm.trans ?_)
  refine eq_zero_of_component A _ fun i => ?_
  refine (component_totalRestrict A g.op z i).trans ?_
  by_cases hi : i ∈ supp
  · have hgi : T i g := (Finset.inf_le hi : supp.inf T ≤ T i) g hg
    exact hgi.trans (map_zero (((PresheafOfModules.toPresheaf R).obj (P i)).map g.op).hom)
  · have h0 : component A z i = 0 := DFinsupp.notMem_support_iff.mp hi
    show sectionRestrict (P i) g.op (component A z i) = 0
    rw [h0, map_zero]

/-- The sheafification unit of a presheaf of modules is locally injective. -/
theorem isLocallyInjective_sheafifyUnit {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}}
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    (M : PresheafOfModules.{w} R₀) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R₀).map (PresheafOfModules.sheafifyUnit α M)) := by
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact (J.W_toSheafify _).isLocallyInjective

end LocallyInjective

end Stacks.GradedAlgebra

namespace SymPow

/-! ### The integer-graded decomposition of the symmetric algebra -/

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- **The symmetric algebra is the internal direct sum of its symmetric powers in all integer
degrees**, the negative ones being zero. -/
theorem isInternal_symmetricPowerInt :
    DirectSum.IsInternal fun n : ℤ => symmetricPowerInt n R M := by
  have hN : DirectSum.IsInternal fun n : ℕ => symmetricPower n R M :=
    DirectSum.Decomposition.isInternal _
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [← iSupIndep_ne_bot]
    let g : {i : ℤ // symmetricPowerInt i R M ≠ ⊥} → ℕ := fun i => i.1.toNat
    have hnn : ∀ i : {i : ℤ // symmetricPowerInt i R M ≠ ⊥}, 0 ≤ i.1 := fun i =>
      not_lt.1 fun h => i.2 (symmetricPowerInt_eq_bot_of_neg R M h)
    have hg : Function.Injective g := fun i j hij => by
      refine Subtype.ext ?_
      rw [← Int.toNat_of_nonneg (hnn i), ← Int.toNat_of_nonneg (hnn j)]
      exact congrArg _ hij
    have hfun : (fun i : {i : ℤ // symmetricPowerInt i R M ≠ ⊥} => symmetricPowerInt i.1 R M) =
        (fun n : ℕ => symmetricPower n R M) ∘ g := by
      funext i
      show symmetricPowerInt i.1 R M = symmetricPowerInt (i.1.toNat : ℤ) R M
      rw [Int.toNat_of_nonneg (hnn i)]
    rw [hfun]
    exact hN.submodule_iSupIndep.comp hg
  · refine eq_top_iff.2 ?_
    rw [← hN.submodule_iSup_eq_top]
    exact iSup_le fun n => le_iSup (fun n : ℤ => symmetricPowerInt n R M) (n : ℤ)

/-! ### Base change of the symmetric algebra along a cartesian semilinear map -/

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {M N : Type*} [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The comparison `S ⊗_R Sym_R(M) → Sym_S(N)` attached to an `R`-linear `u : M → N` whose base
change `S ⊗_R M → N` is bijective: the base change of symmetric algebras followed by the
symmetric algebra of that isomorphism. -/
noncomputable def symBaseChangeOfBijective (u : M →ₗ[R] N)
    (hu : Function.Bijective (LinearMap.liftBaseChange S u)) :
    S ⊗[R] SymmetricAlgebra R M ≃ₐ[S] SymmetricAlgebra S N :=
  (symAlgBaseChangeEquiv S M).trans
    (Stacks.SymAlg.congrEquiv (LinearEquiv.ofBijective (LinearMap.liftBaseChange S u) hu))

/-- The comparison `S ⊗_R Sym_R(M) → Sym_S(N)` sends `s ⊗ x` to `s` times the image of `x` under
the symmetric algebra of `u`. -/
theorem symBaseChangeOfBijective_tmul (u : M →ₗ[R] N)
    (hu : Function.Bijective (LinearMap.liftBaseChange S u)) (s : S)
    (x : SymmetricAlgebra R M) :
    symBaseChangeOfBijective u hu (s ⊗ₜ[R] x) =
      s • SymmetricAlgebra.mapₛₗ (algebraMap R S)
        { toFun := u, map_add' := u.map_add,
          map_smul' := fun r m => by rw [u.map_smul, algebraMap_smul] } x := by
  have key : ((Stacks.SymAlg.congrEquiv (LinearEquiv.ofBijective
        (LinearMap.liftBaseChange S u) hu)).toAlgHom.toRingHom.comp
        (SymmetricAlgebra.lift (toSymBaseChange S M)).toRingHom) =
      SymmetricAlgebra.mapₛₗ (algebraMap R S)
        { toFun := u, map_add' := u.map_add,
          map_smul' := fun r m => by rw [u.map_smul, algebraMap_smul] } := by
    refine SymmetricAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · rw [SymmetricAlgebra.mapₛₗ_algebraMap]
      show (Stacks.SymAlg.congrEquiv _) ((SymmetricAlgebra.lift (toSymBaseChange S M))
        (algebraMap R (SymmetricAlgebra R M) r)) = _
      rw [AlgHom.commutes]
      show (Stacks.SymAlg.congrEquiv _) (algebraMap S _ (algebraMap R S r)) = _
      rw [AlgEquiv.commutes]
    · rw [SymmetricAlgebra.mapₛₗ_ι]
      show (Stacks.SymAlg.congrEquiv _) ((SymmetricAlgebra.lift (toSymBaseChange S M))
        (SymmetricAlgebra.ι R M m)) = _
      rw [SymmetricAlgebra.lift_ι_apply, toSymBaseChange_apply]
      show SymmetricAlgebra.lift _ (SymmetricAlgebra.ι S (S ⊗[R] M) (1 ⊗ₜ[R] m)) = _
      rw [SymmetricAlgebra.lift_ι_apply]
      show SymmetricAlgebra.ι S N (LinearMap.liftBaseChange S u (1 ⊗ₜ[R] m)) = _
      rw [LinearMap.liftBaseChange_tmul, one_smul]
      rfl
  show (Stacks.SymAlg.congrEquiv _) (symAlgBaseChangeHom S M (s ⊗ₜ[R] x)) = _
  rw [symAlgBaseChangeHom_tmul, map_mul, AlgEquiv.commutes, ← Algebra.smul_def]
  exact congrArg (s • ·) (DFunLike.congr_fun key x)

end BaseChange

end SymPow

namespace AlgebraicGeometry.Space

/-- **A locally bijective morphism of presheaves of sets on the small étale site of an algebraic
space, from a presheaf which is a sheaf on the affine charts to a sheaf, is bijective over every
affine chart.** -/
theorem bijective_app_of_isLocallyBijective (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {P Q : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u} (τ : P ⟶ Q)
    [Presheaf.IsLocallyInjective (SmallEtale.topology B S hS F) τ]
    [Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F) τ]
    (hP : Presieve.IsSheaf (AffineEtale.topology B S hS F)
      ((AffineEtale.inclusion B S hS F).op ⋙ P))
    (hQ : Presieve.IsSheaf (SmallEtale.topology B S hS F) Q) (U : AffineEtale B S hS F) :
    Function.Bijective (τ.app (op ((AffineEtale.inclusion B S hS F).obj U))) := by
  have hsp := AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF
  let _ : (AffineEtale.inclusion B S hS F).IsCocontinuous
    (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) := hsp.1
  let _ : (AffineEtale.inclusion B S hS F).IsDenseSubsite
    (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) := hsp.2
  let q' : (⟨(AffineEtale.inclusion B S hS F).op ⋙ P,
        (isSheaf_iff_isSheaf_of_type _ _).2 hP⟩ : Sheaf (AffineEtale.topology B S hS F) (Type u)) ⟶
      ((AffineEtale.inclusion B S hS F).sheafPushforwardContinuous (Type u)
        (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)).obj
          ⟨Q, (isSheaf_iff_isSheaf_of_type _ _).2 hQ⟩ :=
    ⟨(AffineEtale.inclusion B S hS F).op.whiskerLeft τ⟩
  have hqi : Presheaf.IsLocallyInjective (AffineEtale.topology B S hS F) q'.hom :=
    Presheaf.isLocallyInjective_whisker (AffineEtale.topology B S hS F)
      (SmallEtale.topology B S hS F) (AffineEtale.inclusion B S hS F) τ
  have hqs : Presheaf.IsLocallySurjective (AffineEtale.topology B S hS F) q'.hom :=
    Presheaf.isLocallySurjective_whisker (AffineEtale.topology B S hS F)
      (SmallEtale.topology B S hS F) (AffineEtale.inclusion B S hS F) τ
  have _ : IsIso q' := (Sheaf.isLocallyBijective_iff_isIso q').mp ⟨hqi, hqs⟩
  have _ : IsIso q'.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (AffineEtale.topology B S hS F) (Type u)).map q'))
  exact (isIso_iff_bijective (q'.hom.app (op U))).mp inferInstance

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.SymAlgSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W : AlgebraicSpaces B S hS) (F : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-! ### The comparison from the sectionwise symmetric algebra -/

/-- `F` read as a presheaf of modules over the structure presheaf of commutative rings, the form
in which the sectionwise symmetric powers take it. -/
abbrev Fv :
    PresheafOfModules.{u} ((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat) :=
  F.val

/-- The sectionwise symmetric algebra `U ↦ Sym_{𝒪(U)}(F(U))`, as a graded algebra of presheaves
of modules; `Sym(F)` is its degreewise sheafification. -/
abbrev sectionwiseGraded :=
  PresheafOfModules.symPowIntGradedAlgebra.{u, u + 1, u, u}
    (O := (structureSheaf B S hS W.1 W.2).obj) (Fv B S hS W F)

/-- The sheafification units of the homogeneous pieces, as a unital homomorphism from the
sectionwise symmetric algebra to the graded algebra of presheaves underlying `Sym(F)`. -/
def sheafifyUnitHom :
    Stacks.GradedAlgebra.UnitalHom (sectionwiseGraded B S hS W F)
      (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra where
  app n := @PresheafOfModules.sheafifyUnit.{u, u + 1, u, u} _ _
    (SmallEtale.topology B S hS W.1) _ (structureRingSheaf B S hS W)
    (𝟙 (structureRingSheaf B S hS W).obj) (isLocallyInjective_id_structureRingSheaf B S hS W)
    (isLocallySurjective_id_structureRingSheaf B S hS W)
    (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W)
    (PresheafOfModules.symPowInt n (Fv B S hS W F))
  map_mul i j X x y :=
    (@Stacks.GradedAlgebra.sheafify_mul_unit.{u, u + 1, u, u} _ _
      (SmallEtale.topology B S hS W.1) _ (structureRingSheaf B S hS W)
      (𝟙 (structureRingSheaf B S hS W).obj) (isLocallyInjective_id_structureRingSheaf B S hS W)
      (isLocallySurjective_id_structureRingSheaf B S hS W)
      (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W) _
      (sectionwiseGraded B S hS W F) i j X x y).symm
  map_one _ := rfl

/-- The ring of sections of the structure sheaf over a chart. -/
abbrev chartO (X : (SmallEtale B S hS W.1)ᵒᵖ) : RingCat.{u} :=
  ((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj X

/-- **The presheaf of sectionwise symmetric algebras** `U ↦ Sym_{𝒪(U)}(F(U))`, as a presheaf of
commutative rings, with the symmetric algebras of the restriction maps of `F`. -/
def sectionwiseSym : (SmallEtale B S hS W.1)ᵒᵖ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X))
  map {X Y} f := CommRingCat.ofHom
    (SymmetricAlgebra.mapₛₗ (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ _ RingCat).map f).hom
      ((Fv B S hS W F).restrictₛₗ f))
  map_id X := by
    ext x
    exact SymmetricAlgebra.mapₛₗ_eq_self ((Fv B S hS W F).restrictₛₗ (𝟙 X))
      (fun r => congrArg (fun φ : chartO B S hS W X ⟶ chartO B S hS W X =>
        (ConcreteCategory.hom φ) r)
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ _ RingCat).map_id X))
      (fun m => (Fv B S hS W F).map_id_apply_ungraded X m) x
  map_comp {X _ Z} f g := by
    ext x
    exact SymmetricAlgebra.mapₛₗ_eq_comp ((Fv B S hS W F).restrictₛₗ f)
      ((Fv B S hS W F).restrictₛₗ g)
      ((Fv B S hS W F).restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : chartO B S hS W X ⟶ chartO B S hS W Z =>
        (ConcreteCategory.hom φ) r)
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ _ RingCat).map_comp f g))
      (fun m => (Fv B S hS W F).map_comp_apply f g m) x

/-- The sum of the homogeneous components: the sections of the ungraded realization of the
sectionwise symmetric algebra, read in the symmetric algebra of the sections. -/
def sigmaAdd (X : (SmallEtale B S hS W.1)ᵒᵖ) :
    (sectionwiseGraded B S hS W F).Total X →+
      SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X) :=
  DirectSum.coeAddMonoidHom fun n : ℤ => SymPow.symmetricPowerInt n (chartO B S hS W X)
    ((Fv B S hS W F).obj X)

/-- The sum of the homogeneous components of a homogeneous section is that section. -/
theorem sigmaAdd_incl (X : (SmallEtale B S hS W.1)ᵒᵖ) (n : ℤ)
    (y : (PresheafOfModules.symPowInt n (Fv B S hS W F)).obj X) :
    sigmaAdd B S hS W F X ((sectionwiseGraded B S hS W F).incl n y) =
      PresheafOfModules.symPowIntVal y :=
  DirectSum.coeAddMonoidHom_of _ _ _

/-- The sum of the homogeneous components is bijective: the symmetric algebra is the direct sum of
its symmetric powers. -/
theorem sigmaAdd_bijective (X : (SmallEtale B S hS W.1)ᵒᵖ) :
    Function.Bijective (sigmaAdd B S hS W F X) :=
  SymPow.isInternal_symmetricPowerInt _ _

/-- Additive maps out of the sections of the ungraded realization agree when they agree on
homogeneous sections. -/
private theorem total_addHom_ext {X : (SmallEtale B S hS W.1)ᵒᵖ} {N : Type*} [AddCommMonoid N]
    (f g : (sectionwiseGraded B S hS W F).Total X →+ N)
    (h : ∀ (i : ℤ) (x : (PresheafOfModules.symPowInt i (Fv B S hS W F)).obj X),
      f ((sectionwiseGraded B S hS W F).incl i x) = g ((sectionwiseGraded B S hS W F).incl i x)) :
    f = g :=
  DirectSum.addHom_ext h

/-- The sum of the homogeneous components is multiplicative. -/
theorem sigmaAdd_mul (X : (SmallEtale B S hS W.1)ᵒᵖ)
    (a b : (sectionwiseGraded B S hS W F).Total X) :
    sigmaAdd B S hS W F X (a * b) = sigmaAdd B S hS W F X a * sigmaAdd B S hS W F X b := by
  let M₁ : (sectionwiseGraded B S hS W F).Total X →+ (sectionwiseGraded B S hS W F).Total X →+
      SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X) :=
    AddMonoidHom.compr₂ AddMonoidHom.mul (sigmaAdd B S hS W F X)
  let M₂ : (sectionwiseGraded B S hS W F).Total X →+ (sectionwiseGraded B S hS W F).Total X →+
      SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X) :=
    AddMonoidHom.compl₂ (AddMonoidHom.mul.comp (sigmaAdd B S hS W F X)) (sigmaAdd B S hS W F X)
  have hM : M₁ = M₂ := by
    refine total_addHom_ext B S hS W F _ _ fun i x => total_addHom_ext B S hS W F _ _ fun j y => ?_
    show sigmaAdd B S hS W F X ((sectionwiseGraded B S hS W F).incl i x *
        (sectionwiseGraded B S hS W F).incl j y) =
      sigmaAdd B S hS W F X ((sectionwiseGraded B S hS W F).incl i x) *
        sigmaAdd B S hS W F X ((sectionwiseGraded B S hS W F).incl j y)
    rw [Stacks.GradedAlgebra.incl_mul_incl, sigmaAdd_incl, sigmaAdd_incl, sigmaAdd_incl]
    exact PresheafOfModules.symPowIntVal_mul (Fv B S hS W F) i j X x y
  exact DFunLike.congr_fun (DFunLike.congr_fun hM a) b

/-- The sum of the homogeneous components sends one to one. -/
theorem sigmaAdd_one (X : (SmallEtale B S hS W.1)ᵒᵖ) :
    sigmaAdd B S hS W F X 1 = 1 := by
  rw [Stacks.GradedAlgebra.one_eq_incl, sigmaAdd_incl]
  rfl

/-- **The sections of the ungraded realization of the sectionwise symmetric algebra are the
symmetric algebra of the sections**, as rings. -/
def sigma (X : (SmallEtale B S hS W.1)ᵒᵖ) :
    (sectionwiseGraded B S hS W F).Total X ≃+*
      SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X) :=
  RingEquiv.ofBijective
    (show (sectionwiseGraded B S hS W F).Total X →+*
        SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X) from
      { toFun := sigmaAdd B S hS W F X
        map_one' := sigmaAdd_one B S hS W F X
        map_mul' := sigmaAdd_mul B S hS W F X
        map_zero' := map_zero _
        map_add' := map_add _ })
    (sigmaAdd_bijective B S hS W F X)

/-- The ring isomorphism `sigma` is the sum of the homogeneous components. -/
theorem sigma_apply (X : (SmallEtale B S hS W.1)ᵒᵖ) (a : (sectionwiseGraded B S hS W F).Total X) :
    sigma B S hS W F X a = sigmaAdd B S hS W F X a :=
  rfl

/-- `sigma` sends a homogeneous section to itself in the symmetric algebra of the sections. -/
theorem sigma_incl (X : (SmallEtale B S hS W.1)ᵒᵖ) (n : ℤ)
    (y : (PresheafOfModules.symPowInt n (Fv B S hS W F)).obj X) :
    sigma B S hS W F X ((sectionwiseGraded B S hS W F).incl n y) =
      PresheafOfModules.symPowIntVal y :=
  sigmaAdd_incl B S hS W F X n y

/-- `sigma` commutes with restriction along a morphism of charts. -/
theorem sigma_naturality {X Y : (SmallEtale B S hS W.1)ᵒᵖ} (f : X ⟶ Y)
    (a : (sectionwiseGraded B S hS W F).Total X) :
    sigma B S hS W F Y ((sectionwiseGraded B S hS W F).totalRestrict f a) =
      ((sectionwiseSym B S hS W F).map f).hom (sigma B S hS W F X a) := by
  refine DFunLike.congr_fun (total_addHom_ext B S hS W F
    ((sigmaAdd B S hS W F Y).comp ((sectionwiseGraded B S hS W F).totalRestrict f))
    (((sectionwiseSym B S hS W F).map f).hom.toAddMonoidHom.comp (sigmaAdd B S hS W F X))
    fun i x => ?_) a
  show sigmaAdd B S hS W F Y ((sectionwiseGraded B S hS W F).totalRestrict f
      ((sectionwiseGraded B S hS W F).incl i x)) =
    ((sectionwiseSym B S hS W F).map f).hom
      (sigmaAdd B S hS W F X ((sectionwiseGraded B S hS W F).incl i x))
  rw [Stacks.GradedAlgebra.totalRestrict_incl, sigmaAdd_incl, sigmaAdd_incl]
  rfl

/-- `sigma` is linear over the ring of sections of the structure sheaf. -/
theorem sigma_smul (X : (SmallEtale B S hS W.1)ᵒᵖ) (r : chartO B S hS W X)
    (a : (sectionwiseGraded B S hS W F).Total X) :
    sigma B S hS W F X (r • a) = r • sigma B S hS W F X a := by
  refine DFunLike.congr_fun (total_addHom_ext B S hS W F
    ((sigmaAdd B S hS W F X).comp (DistribSMul.toAddMonoidHom _ r))
    ((DistribSMul.toAddMonoidHom _ r).comp (sigmaAdd B S hS W F X)) fun i x => ?_) a
  show sigmaAdd B S hS W F X (r • (sectionwiseGraded B S hS W F).incl i x) =
    r • sigmaAdd B S hS W F X ((sectionwiseGraded B S hS W F).incl i x)
  rw [← Stacks.GradedAlgebra.incl_smul, sigmaAdd_incl, sigmaAdd_incl]
  rfl

/-! ### The sectionwise symmetric algebra is a sheaf on the affine charts -/

/-- The structure map of the sectionwise symmetric algebra. -/
def toSectionwiseSym : (structureSheaf B S hS W.1 W.2).obj ⟶ sectionwiseSym B S hS W F where
  app X := CommRingCat.ofHom
    (algebraMap (chartO B S hS W X) (SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X)))
  naturality X Y f := by
    ext r
    exact (SymmetricAlgebra.mapₛₗ_algebraMap _ _ r).symm

/-- The sectionwise symmetric algebra on the affine charts. -/
abbrev affineSym : (AffineEtale B S hS W.1)ᵒᵖ ⥤ CommRingCat.{u} :=
  (AffineEtale.inclusion B S hS W.1).op ⋙ sectionwiseSym B S hS W F

/-- The sectionwise symmetric algebra on the affine charts, as a presheaf of modules over the
chart rings. -/
noncomputable abbrev affineSymModule :
    PresheafOfModules.{u}
      (affineEtaleChartRings B S hS W.1 ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  Stacks.PresheafOfModules.algModule _ (affineSym B S hS W F)
    ((AffineEtale.inclusion B S hS W.1).op.whiskerLeft (toSectionwiseSym B S hS W F))

open Stacks.PresheafOfModules in
/-- **The sectionwise symmetric algebra of a quasi-coherent module is cartesian over every morphism
of affine étale charts.** -/
theorem isIso_restrictionBaseChange_affineSymModule (hF : F.IsQuasicoherentOnSite)
    {X Y : (AffineEtale B S hS W.1)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange (affineSymModule B S hS W F) f) := by
  let g : Y.unop.obj ⟶ X.unop.obj := f.unop.hom
  let := chartAlgebra (hF := W.2) g
  let := chartSectionsModule F g
  have := chartSections_isScalarTower F g
  have hu := bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS W.1 W.2 F hF
    X.unop.property Y.unop.property g
  let E := SymPow.symBaseChangeOfBijective (chartRestrictLinear F g) hu
  have key : ∀ z, restrictionBaseChange (affineSymModule B S hS W F) f z = E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero E).symm
    | add x y hx hy =>
      exact ((map_add _ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add E x y).symm
    | tmul b x =>
      refine (restrictionBaseChange_tmul _ f b x).trans ?_
      refine Eq.trans ?_
        (SymPow.symBaseChangeOfBijective_tmul (chartRestrictLinear F g) hu b x).symm
      rfl
  have hb : Function.Bijective (restrictionBaseChange (affineSymModule B S hS W F) f) := by
    rw [show (restrictionBaseChange (affineSymModule B S hS W F) f : _ → _) = E from funext key]
    exact E.bijective
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

open Stacks.PresheafOfModules in
/-- **The sectionwise symmetric algebra of a quasi-coherent module is a sheaf of sets on the
affine étale charts.** -/
theorem isSheaf_affineSym (hF : F.IsQuasicoherentOnSite) :
    Presieve.IsSheaf (AffineEtale.topology B S hS W.1)
      (affineSym B S hS W F ⋙ CategoryTheory.forget CommRingCat.{u}) := by
  have hcart : ∀ {Z V : (AffineEtale B S hS W.1)ᵒᵖ} (f : Z ⟶ V),
      IsIso (restrictionBaseChange.{u + 1, u, u, u + 1}
        ((affineSymModule B S hS W F).uliftSections.{u + 1}) f) := fun f =>
    isIso_restrictionBaseChange_uliftSections.{u + 1, u + 1, u, u, u} _ f
      (isIso_restrictionBaseChange_affineSymModule B S hS W F hF f)
  have hsheaf := isSheaf_of_cartesian_affineEtaleChart.{u, u} B S hS W.1
    ((affineSymModule B S hS W F).uliftSections.{u + 1}) hcart
  rw [Presheaf.isSheaf_iff_isSheaf_comp (AffineEtale.topology B S hS W.1) _
    (CategoryTheory.forget AddCommGrpCat.{u + 1})] at hsheaf
  replace hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 hsheaf
  have e : ((affineSymModule B S hS W F).uliftSections.{u + 1}).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
      (affineSym B S hS W F ⋙ CategoryTheory.forget CommRingCat.{u}) ⋙
        CategoryTheory.uliftFunctor.{u + 1, u} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact (Presieve.isSheaf_comp_uliftFunctor_iff (J := AffineEtale.topology B S hS W.1)).mp
    (Presieve.isSheaf_iso _ e hsheaf)

/-- The ungraded realization of the sectionwise symmetric algebra, as a presheaf of sets on the
affine charts, is the sectionwise symmetric algebra. -/
def affineTotalIso :
    (AffineEtale.inclusion B S hS W.1).op ⋙ (sectionwiseGraded B S hS W F).totalPresheaf ⋙
        CategoryTheory.forget RingCat.{u} ≅
      affineSym B S hS W F ⋙ CategoryTheory.forget CommRingCat.{u} :=
  NatIso.ofComponents
    (fun X => (sigma B S hS W F ((AffineEtale.inclusion B S hS W.1).op.obj X)).toEquiv.toIso)
    fun {X Y} f => by
      ext a
      exact sigma_naturality B S hS W F ((AffineEtale.inclusion B S hS W.1).op.map f) a

/-- **The ungraded realization of the sectionwise symmetric algebra of a quasi-coherent module is
a sheaf of sets on the affine étale charts.** -/
theorem isSheaf_affineTotal (hF : F.IsQuasicoherentOnSite) :
    Presieve.IsSheaf (AffineEtale.topology B S hS W.1)
      ((AffineEtale.inclusion B S hS W.1).op ⋙ (sectionwiseGraded B S hS W F).totalPresheaf ⋙
        CategoryTheory.forget RingCat.{u}) :=
  Presieve.isSheaf_iso _ (affineTotalIso B S hS W F).symm (isSheaf_affineSym B S hS W F hF)

/-! ### The comparison is locally bijective -/

/-- The comparison from the ungraded realization of the sectionwise symmetric algebra to the
sections of `Sym(F)`: the sheafification units in every degree, followed by the sheafification
unit of the ungraded realization. -/
def psiCmp :
    (sectionwiseGraded B S hS W F).totalPresheaf ⟶
      ((symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.totalSheaf
        (SmallEtale.topology B S hS W.1)).obj :=
  Stacks.GradedAlgebra.totalPresheafMap (sheafifyUnitHom B S hS W F) ≫
    (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.toTotalSheaf
      (SmallEtale.topology B S hS W.1)

/-- The comparison from the ungraded realization of the sectionwise symmetric algebra to the
sections of `Sym(F)` is locally surjective. -/
theorem isLocallySurjective_psiCmp :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS W.1) (psiCmp B S hS W F) := by
  have h₁ : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS W.1)
      (Stacks.GradedAlgebra.totalPresheafMap (sheafifyUnitHom B S hS W F)) :=
    Stacks.GradedAlgebra.isLocallySurjective_totalPresheafMap _ _ fun i =>
      ⟨fun s => @Stacks.liftSieve_mem.{u, u + 1, u, u} _ _ (SmallEtale.topology B S hS W.1) _
        (structureRingSheaf B S hS W) (𝟙 (structureRingSheaf B S hS W).obj)
        (isLocallyInjective_id_structureRingSheaf B S hS W)
        (isLocallySurjective_id_structureRingSheaf B S hS W)
        (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W)
        (PresheafOfModules.symPowInt i (Fv B S hS W F)) _ s⟩
  have h₂ : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS W.1)
      ((symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.toTotalSheaf
        (SmallEtale.topology B S hS W.1)) :=
    GrothendieckTopology.W.isLocallySurjective (CA := fun R : RingCat.{u} => ToType R)
      ((SmallEtale.topology B S hS W.1).W_toSheafify _)
  exact @Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂

/-- The comparison from the ungraded realization of the sectionwise symmetric algebra to the
sections of `Sym(F)` is locally injective. -/
theorem isLocallyInjective_psiCmp :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS W.1) (psiCmp B S hS W F) := by
  have h₁ : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS W.1)
      (Stacks.GradedAlgebra.totalPresheafMap (sheafifyUnitHom B S hS W F)) :=
    Stacks.GradedAlgebra.isLocallyInjective_totalPresheafMap _ _ fun i =>
      @Stacks.GradedAlgebra.isLocallyInjective_sheafifyUnit.{u, u + 1, u} _ _
        (SmallEtale.topology B S hS W.1) _ (structureRingSheaf B S hS W)
        (𝟙 (structureRingSheaf B S hS W).obj) (isLocallyInjective_id_structureRingSheaf B S hS W)
        (isLocallySurjective_id_structureRingSheaf B S hS W)
        (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W)
        (PresheafOfModules.symPowInt i (Fv B S hS W F))
  have h₂ : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS W.1)
      ((symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.toTotalSheaf
        (SmallEtale.topology B S hS W.1)) :=
    GrothendieckTopology.W.isLocallyInjective (CA := fun R : RingCat.{u} => ToType R)
      ((SmallEtale.topology B S hS W.1).W_toSheafify _)
  exact @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂

/-- **The comparison of the sectionwise symmetric algebra with `Sym(F)`, over one chart**: the
ring homomorphism `Sym_{𝒪(U)}(F(U)) → Sym(F)(U)`. -/
def symSections (X : (SmallEtale B S hS W.1)ᵒᵖ) :
    SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X) →+*
      (symmetricAlgebraSheaf B S hS W F).right.obj.obj X :=
  ((psiCmp B S hS W F).app X).hom.comp (sigma B S hS W F X).symm.toRingHom

/-- On the image of a section under `sigma`, the comparison `symSections` is `psiCmp`. -/
theorem symSections_apply_sigma (X : (SmallEtale B S hS W.1)ᵒᵖ)
    (a : (sectionwiseGraded B S hS W F).Total X) :
    symSections B S hS W F X (sigma B S hS W F X a) = (psiCmp B S hS W F).app X a := by
  show ((psiCmp B S hS W F).app X).hom ((sigma B S hS W F X).symm (sigma B S hS W F X a)) = _
  rw [RingEquiv.symm_apply_apply]

/-- **Over an affine chart, the sections of the symmetric algebra of a quasi-coherent module are
the symmetric algebra of its sections**: `Sym_{𝒪(U)}(F(U)) → Sym(F)(U)` is bijective. -/
theorem symSections_bijective (hF : F.IsQuasicoherentOnSite) (U : SmallEtale B S hS W.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Bijective (symSections B S hS W F (op U)) := by
  let τ := Functor.whiskerRight (psiCmp B S hS W F) (CategoryTheory.forget RingCat.{u})
  have hi : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS W.1) τ :=
    (Presheaf.isLocallyInjective_forget_iff _ _).2 (isLocallyInjective_psiCmp B S hS W F)
  have hs : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS W.1) τ :=
    (Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 (isLocallySurjective_psiCmp B S hS W F)
  have hQ : Presieve.IsSheaf (SmallEtale.topology B S hS W.1)
      ((symmetricAlgebraSheaf B S hS W F).right.obj ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose (SmallEtale.topology B S hS W.1)
        (CategoryTheory.forget CommRingCat.{u})).obj
          (symmetricAlgebraSheaf B S hS W F).right).property
  have hb := bijective_app_of_isLocallyBijective B S hS W.1 W.2 τ
    (isSheaf_affineTotal B S hS W F hF) hQ ⟨U, hU⟩
  exact hb.comp (sigma B S hS W F (op U)).symm.bijective

/-! ### The comparison is a natural homomorphism of algebras -/

/-- `sigma` sends the structure map of the sectionwise graded algebra to the algebra map of the
symmetric algebra. -/
theorem sigma_structureMap (X : (SmallEtale B S hS W.1)ᵒᵖ) (r : chartO B S hS W X) :
    sigma B S hS W F X ((sectionwiseGraded B S hS W F).structureMap X r) =
      algebraMap (chartO B S hS W X)
        (SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X)) r := by
  show sigma B S hS W F X (r • (1 : (sectionwiseGraded B S hS W F).Total X)) = _
  rw [sigma_smul, map_one, Algebra.algebraMap_eq_smul_one]

/-- `psiCmp` sends the structure map of the sectionwise graded algebra to the algebra map of
`Sym(F)`. -/
theorem psiCmp_structureMap (X : (SmallEtale B S hS W.1)ᵒᵖ) (r : chartO B S hS W X) :
    ((psiCmp B S hS W F).app X).hom ((sectionwiseGraded B S hS W F).structureMap X r) =
      (symmetricAlgebraSheaf B S hS W F).algebraMap X r := by
  have h := congrArg (fun φ => (φ.app X).hom r)
    (Stacks.GradedAlgebra.structureHom_totalPresheafMap (sheafifyUnitHom B S hS W F))
  show ((symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.totalUnit
      (SmallEtale.topology B S hS W.1) X)
      ((Stacks.GradedAlgebra.totalPresheafMap (sheafifyUnitHom B S hS W F)).app X
        ((sectionwiseGraded B S hS W F).structureMap X r)) = _
  have h' : (Stacks.GradedAlgebra.totalPresheafMap (sheafifyUnitHom B S hS W F)).app X
      ((sectionwiseGraded B S hS W F).structureMap X r) =
      (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.structureMap X r := h
  rw [h']
  rfl

/-- **The comparison `Sym_{𝒪(U)}(F(U)) → Sym(F)(U)` is a homomorphism of `𝒪(U)`-algebras.** -/
theorem symSections_algebraMap (X : (SmallEtale B S hS W.1)ᵒᵖ) (r : chartO B S hS W X) :
    symSections B S hS W F X
        (algebraMap (chartO B S hS W X)
          (SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X)) r) =
      (symmetricAlgebraSheaf B S hS W F).algebraMap X r := by
  rw [← sigma_structureMap, symSections_apply_sigma]
  exact psiCmp_structureMap B S hS W F X r

/-- **The comparison `Sym_{𝒪(U)}(F(U)) → Sym(F)(U)` is natural in `U`.** -/
theorem symSections_naturality {X Y : (SmallEtale B S hS W.1)ᵒᵖ} (f : X ⟶ Y)
    (x : SymmetricAlgebra (chartO B S hS W X) ((Fv B S hS W F).obj X)) :
    symSections B S hS W F Y (((sectionwiseSym B S hS W F).map f).hom x) =
      ((symmetricAlgebraSheaf B S hS W F).right.obj.map f).hom (symSections B S hS W F X x) := by
  obtain ⟨a, rfl⟩ := (sigma B S hS W F X).surjective x
  rw [← sigma_naturality, symSections_apply_sigma, symSections_apply_sigma]
  exact NatTrans.naturality_apply (psiCmp B S hS W F) f a

/-- `F`, read as an `𝒪_W`-module in the spelling of `AlgebraicGeometry.Space.Modules`, the one
on which the chart rings `AlgebraicGeometry.Space.chartRing` act. -/
abbrev FM : Modules.{u, u} B S hS W.1 W.2 := F

/-- The comparison `Sym_{𝒪(U)}(F(U)) → Sym(F)(U)` as a map of `𝒪(U)`-modules, the target with
the module structure of the underlying `𝒪_W`-module of `Sym(F)`. -/
def symSectionsLinear (U : SmallEtale B S hS W.1) :
    SymmetricAlgebra (chartRing B S hS W.1 W.2 U) ((FM B S hS W F).val.obj (op U)) →ₗ[
      chartRing B S hS W.1 W.2 U]
      (AlgebraSheaf.underlyingModule (symmetricAlgebraSheaf B S hS W F)).val.obj (op U) where
  toFun := symSections B S hS W F (op U)
  map_add' := map_add _
  map_smul' r x := by
    change symSections B S hS W F (op U) (r • x) =
      (symmetricAlgebraSheaf B S hS W F).algebraMap (op U) r * symSections B S hS W F (op U) x
    refine (congrArg (symSections B S hS W F (op U)) (Algebra.smul_def r x)).trans ?_
    refine (map_mul (symSections B S hS W F (op U)) _ _).trans ?_
    exact congrArg (· * _) (symSections_algebraMap B S hS W F (op U) r)

/-- The linear comparison `symSectionsLinear` is `symSections`. -/
theorem symSectionsLinear_apply (U : SmallEtale B S hS W.1)
    (x : SymmetricAlgebra (chartRing B S hS W.1 W.2 U) ((FM B S hS W F).val.obj (op U))) :
    symSectionsLinear B S hS W F U x = symSections B S hS W F (op U) x := rfl

/-- **The symmetric algebra of a quasi-coherent module is cartesian on affine charts**: over a
morphism `V ⟶ U` of affine étale charts, `𝒪(V) ⊗_{𝒪(U)} Sym(F)(U) → Sym(F)(V)` is bijective. -/
theorem isCartesianOnAffineCharts_symmetricAlgebraSheaf (hF : F.IsQuasicoherentOnSite) :
    IsCartesianOnAffineCharts
      (AlgebraSheaf.underlyingModule (symmetricAlgebraSheaf B S hS W F)) := by
  intro U V hU hV g
  let := chartAlgebra (hF := W.2) g
  let := chartSectionsModule (FM B S hS W F) g
  have := chartSections_isScalarTower (FM B S hS W F) g
  let := chartSectionsModule (AlgebraSheaf.underlyingModule (symmetricAlgebraSheaf B S hS W F)) g
  have hu := bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS W.1 W.2
    (FM B S hS W F) hF hU hV g
  let E := SymPow.symBaseChangeOfBijective (chartRestrictLinear (FM B S hS W F) g) hu
  let L := symSectionsLinear B S hS W F U
  have hL : Function.Bijective L := symSections_bijective B S hS W F hF U hU
  let T := LinearMap.lTensor (chartRing B S hS W.1 W.2 V) L
  have hT : Function.Bijective T :=
    (LinearEquiv.lTensor (chartRing B S hS W.1 W.2 V) (LinearEquiv.ofBijective L hL)).bijective
  let G := AlgebraSheaf.underlyingModule (symmetricAlgebraSheaf B S hS W F)
  have key : ∀ z, sectionsBaseChange G g (T z) = symSectionsLinear B S hS W F V (E z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      rw [LinearMap.lTensor_tmul, chartBaseChange_tmul]
      have h1 := SymPow.symBaseChangeOfBijective_tmul (chartRestrictLinear (FM B S hS W F) g) hu b x
      refine Eq.trans ?_ (congrArg (symSectionsLinear B S hS W F V) h1).symm
      rw [LinearMap.map_smul]
      congr 1
      exact (symSections_naturality B S hS W F g.op x).symm
  have hcomp : Function.Bijective (fun z => sectionsBaseChange G g (T z)) := by
    rw [show (fun z => sectionsBaseChange G g (T z)) =
        (symSectionsLinear B S hS W F V) ∘ E from funext key]
    exact (symSections_bijective B S hS W F hF V hV).comp E.bijective
  exact (Function.Bijective.of_comp_iff _ hT).mp hcomp

/-- **The symmetric algebra of a quasi-coherent module on an algebraic space is
quasi-coherent.** -/
@[ega "II 1.7.7" "more general"]
theorem isQuasicoherent_symmetricAlgebraSheaf (hF : F.IsQuasicoherentOnSite) :
    (symmetricAlgebraSheaf B S hS W F).IsQuasicoherent :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_symmetricAlgebraSheaf B S hS W F hF)

/-- **The symmetric algebra of a quasi-coherent module of finite presentation is of finite
presentation.** -/
theorem isFinitePresentation_symmetricAlgebraSheaf (hF : F.IsQuasicoherentOnSite)
    (hfp : SheafOfModules.IsFinitePresentationOnSite (FM B S hS W F)) :
    (symmetricAlgebraSheaf B S hS W F).IsFinitePresentation := by
  intro U hU
  have : Module.FinitePresentation (chartRing B S hS W.1 W.2 U)
      ((FM B S hS W F).val.obj (op U)) :=
    module_finitePresentation_sections_of_isFinitePresentationOnSite
      (FM B S hS W F) hF hfp U hU
  have hSym : (algebraMap (chartRing B S hS W.1 W.2 U)
      (SymmetricAlgebra (chartRing B S hS W.1 W.2 U)
        ((FM B S hS W F).val.obj (op U)))).FinitePresentation :=
    Stacks.SymAlg.finitePresentation (chartRing B S hS W.1 W.2 U)
      ((FM B S hS W F).val.obj (op U))
  have hcomp : (symmetricAlgebraSheaf B S hS W F).algebraMap (op U) =
      (symSections B S hS W F (op U)).comp (algebraMap (chartRing B S hS W.1 W.2 U)
        (SymmetricAlgebra (chartRing B S hS W.1 W.2 U) ((FM B S hS W F).val.obj (op U)))) :=
    RingHom.ext fun r => (symSections_algebraMap B S hS W F (op U) r).symm
  rw [hcomp]
  exact (RingHom.FinitePresentation.of_bijective
    (symSections_bijective B S hS W F hF U hU)).comp hSym

/-- The comparison `Sym_{𝒪(U)}(F(U)) → Sym(F)(U)` as a ring homomorphism, in the spelling of the
chart rings. -/
def symSectionsRingHom (U : SmallEtale B S hS W.1) :
    SymmetricAlgebra (chartRing B S hS W.1 W.2 U) ((FM B S hS W F).val.obj (op U)) →+*
      (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op U) :=
  symSections B S hS W F (op U)

/-- Over an affine chart, `symSectionsRingHom` is bijective. -/
theorem symSectionsRingHom_bijective (hF : F.IsQuasicoherentOnSite) (U : SmallEtale B S hS W.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Bijective (symSectionsRingHom B S hS W F U) :=
  symSections_bijective B S hS W F hF U hU

/-- `symSectionsRingHom` is compatible with the algebra maps from the chart ring. -/
theorem symSectionsRingHom_comp_algebraMap (U : SmallEtale B S hS W.1) :
    (symSectionsRingHom B S hS W F U).comp (algebraMap (chartRing B S hS W.1 W.2 U)
      (SymmetricAlgebra (chartRing B S hS W.1 W.2 U) ((FM B S hS W F).val.obj (op U)))) =
      (symmetricAlgebraSheaf B S hS W F).algebraMap (op U) :=
  RingHom.ext fun r => symSections_algebraMap B S hS W F (op U) r

end AlgebraicGeometry.Space.SymAlgSheaf

end

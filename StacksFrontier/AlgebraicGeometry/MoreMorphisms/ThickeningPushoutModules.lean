module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.FiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.RingTheory.MilnorPatching.RelativeProperties
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Modules on the base changes of a pushout along a thickening

Let `i : X ⟶ X'` be a thickening of schemes, let `f : X ⟶ Y` be an affine morphism, let
`Y' = Y ⨿_X X'` be the pushout of [Stacks Project, Tag 07RT] and let `g : V' ⟶ Y'` be a morphism
of schemes.  Write `V = Y ×_{Y'} V'`, `U' = X' ×_{Y'} V'` and `U = X ×_{Y'} V'`.
[Stacks Project, Tag 08KU] compares quasi-coherent `𝒪_{V'}`-modules flat over `Y'` with triples
`(𝒢, ℱ', φ)` consisting of a module on `V`, a module on `U'` and an isomorphism of their two
restrictions to `U`, the comparison being the functor that sends `𝒢'` to its two restrictions
together with the canonical isomorphism between their restrictions to `U`.

This file builds that comparison functor, both on all modules and between the two categories
the tag names — quasi-coherent modules flat over `Y'` on the one side, triples of a
quasi-coherent module on `V` flat over `Y` and a quasi-coherent module on `U'` flat over `X'` on
the other — and proves the finite-type and finite-presentation clauses of the tag, each as the
equivalence of conditions that the tag asserts.

## Main definitions

* `Stacks.Pushout.overlapComparison` is the canonical isomorphism between the two ways of
  restricting a module on `V'` to `U`, as a natural isomorphism of functors.
* `Stacks.Pushout.GluingTriple` is the category of triples: a module on `V`, a module on `U'`,
  and an isomorphism of their restrictions to `U`.
* `Stacks.Pushout.baseChangeTripleFunctor` is the comparison functor.
* `Stacks.Pushout.FlatQuasicoherentModule` is the category of quasi-coherent modules flat over
  a given base.
* `Stacks.Pushout.FlatGluingTriple` is the category of triples with the quasi-coherence and
  relative flatness conditions imposed on both components.
* `Stacks.Pushout.flatBaseChangeTripleFunctor` is the comparison functor between those two
  categories; `Stacks.Pushout.flatBaseChangeTripleFunctor_comp_ι` says that it is the
  restriction of `Stacks.Pushout.baseChangeTripleFunctor`.

## Main results

* `Stacks.Pushout.isFiniteType_iff_baseChangeTripleFunctor_obj`: a quasi-coherent module on `V'`
  flat over `Y'` is of finite type if and only if both components of its triple are.
* `Stacks.Pushout.isFinitePresentation_iff_baseChangeTripleFunctor_obj`: the same for finite
  presentation, when `V' ⟶ Y'` is locally of finite presentation.
* `Stacks.Pushout.isFiniteType_baseChangeTripleFunctor_obj` and
  `Stacks.Pushout.isFinitePresentation_baseChangeTripleFunctor_obj`: for an arbitrary module on
  `V'`, both components of the triple of a module of finite type (of finite presentation) are of
  finite type (of finite presentation).
* `Stacks.Pushout.isFlatQuasicoherentTriple_baseChangeTripleFunctor_obj`: the triple of a
  quasi-coherent module flat over `Y'` consists of quasi-coherent modules flat over `Y` and
  over `X'`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RW](https://stacks.math.columbia.edu/tag/07RW)
* [Stacks Project, Tag 08IH](https://stacks.math.columbia.edu/tag/08IH)
* [Stacks Project, Tag 08KP](https://stacks.math.columbia.edu/tag/08KP)
* [Stacks Project, Tag 08KU](https://stacks.math.columbia.edu/tag/08KU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.Pushout

variable {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
  (g : V' ⟶ pushout i f)

/-- The restriction `V = Y ×_{Y'} V' ⟶ V'`. -/
noncomputable abbrev targetRestriction : pullback (pushout.inr i f) g ⟶ V' :=
  pullback.snd _ _

/-- The restriction `U' = X' ×_{Y'} V' ⟶ V'`. -/
noncomputable abbrev ambientRestriction : pullback (pushout.inl i f) g ⟶ V' :=
  pullback.snd _ _

/-- The restriction `U = X ×_{Y'} V' ⟶ V`, induced by `f : X ⟶ Y`. -/
noncomputable def commonToTarget :
    pullback (i ≫ pushout.inl i f) g ⟶ pullback (pushout.inr i f) g :=
  pullback.lift (pullback.fst (i ≫ pushout.inl i f) g ≫ f)
    (pullback.snd (i ≫ pushout.inl i f) g) (by
      rw [Category.assoc, ← pushout.condition]
      exact pullback.condition)

/-- The restriction `U = X ×_{Y'} V' ⟶ U'`, induced by the thickening `i`. -/
noncomputable def commonToAmbient :
    pullback (i ≫ pushout.inl i f) g ⟶ pullback (pushout.inl i f) g :=
  pullback.lift (pullback.fst (i ≫ pushout.inl i f) g ≫ i)
    (pullback.snd (i ≫ pushout.inl i f) g) (by
      rw [Category.assoc]
      exact pullback.condition)

/-- The two restrictions of `U` agree after composing into `V'`. -/
theorem commonToTarget_comp_targetRestriction :
    commonToTarget i f g ≫ targetRestriction i f g =
      commonToAmbient i f g ≫ ambientRestriction i f g := by
  simp only [commonToTarget, commonToAmbient, pullback.lift_snd]

/-- The canonical isomorphism between the two ways of restricting a module on `V'` to `U`: via
`V` and via `U'`. -/
noncomputable def overlapComparison :
    Scheme.Modules.pullback (targetRestriction i f g) ⋙
        Scheme.Modules.pullback (commonToTarget i f g) ≅
      Scheme.Modules.pullback (ambientRestriction i f g) ⋙
        Scheme.Modules.pullback (commonToAmbient i f g) :=
  Scheme.Modules.pullbackComp (commonToTarget i f g) (targetRestriction i f g) ≪≫
    Scheme.Modules.pullbackCongr (commonToTarget_comp_targetRestriction i f g) ≪≫
      (Scheme.Modules.pullbackComp (commonToAmbient i f g)
        (ambientRestriction i f g)).symm

/-- A gluing triple: a module on `V`, a module on `U'`, and an isomorphism of their two
restrictions to `U`. -/
structure GluingTriple where
  /-- The module on `V = Y ×_{Y'} V'`. -/
  target : (pullback (pushout.inr i f) g).Modules
  /-- The module on `U' = X' ×_{Y'} V'`. -/
  ambient : (pullback (pushout.inl i f) g).Modules
  /-- The comparison of the two restrictions to `U = X ×_{Y'} V'`. -/
  comparison : (Scheme.Modules.pullback (commonToTarget i f g)).obj target ≅
    (Scheme.Modules.pullback (commonToAmbient i f g)).obj ambient

variable {i f g}

/-- A morphism of triples is a pair of morphisms of modules commuting with the comparisons. -/
structure GluingTripleHom (A B : GluingTriple i f g) where
  /-- The morphism of the modules on `V`. -/
  target : A.target ⟶ B.target
  /-- The morphism of the modules on `U'`. -/
  ambient : A.ambient ⟶ B.ambient
  /-- The two morphisms agree on `U` through the comparisons. -/
  comm : (Scheme.Modules.pullback (commonToTarget i f g)).map target ≫ B.comparison.hom =
    A.comparison.hom ≫ (Scheme.Modules.pullback (commonToAmbient i f g)).map ambient

/-- The category of gluing triples, whose morphisms are the `GluingTripleHom`s. -/
noncomputable instance : Category (GluingTriple i f g) where
  Hom := GluingTripleHom
  id A := ⟨𝟙 A.target, 𝟙 A.ambient, by simp⟩
  comp φ ψ := ⟨φ.target ≫ ψ.target, φ.ambient ≫ ψ.ambient, by
    simp only [Functor.map_comp]
    rw [Category.assoc, ψ.comm, ← Category.assoc, φ.comm, Category.assoc]⟩
  id_comp φ := by cases φ; congr
  comp_id φ := by cases φ; congr
  assoc φ ψ χ := by
    cases φ; cases ψ; cases χ
    congr 1

variable (i f g)

open Stacks.Thickenings in
omit [HasPushout i f] in
/-- The comparison functor, sending a module on `V'` to its two restrictions to `V` and to `U'`
together with the canonical isomorphism `Stacks.Pushout.overlapComparison` between their
restrictions to `U`. -/
@[stacks 08KU "the comparison functor of the tag, on all modules on V'"]
noncomputable def baseChangeTripleFunctor (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
    ∀ g : V' ⟶ pushout i f, V'.Modules ⥤ GluingTriple i f g :=
  letI := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
  fun g ↦
  { obj := fun M ↦
      { target := (Scheme.Modules.pullback (targetRestriction i f g)).obj M
        ambient := (Scheme.Modules.pullback (ambientRestriction i f g)).obj M
        comparison := (overlapComparison i f g).app M }
    map := fun φ ↦
      { target := (Scheme.Modules.pullback (targetRestriction i f g)).map φ
        ambient := (Scheme.Modules.pullback (ambientRestriction i f g)).map φ
        comm := (overlapComparison i f g).hom.naturality φ }
    map_id := fun M ↦ by congr 1 <;> simp
    map_comp := fun φ ψ ↦ by congr 1 <;> simp }

open Stacks.Thickenings in
omit [HasPushout i f] in
/-- If a module on `V'` is of finite type, then both components of its comparison triple, its
restrictions to `V` and to `U'`, are of finite type. -/
@[stacks 08KU "the finite type clause, for an arbitrary module on V'"]
theorem isFiniteType_baseChangeTripleFunctor_obj (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
    ∀ (g : V' ⟶ pushout i f) (M : V'.Modules) [M.IsFiniteType],
      ((baseChangeTripleFunctor i f hi g).obj M).target.IsFiniteType ∧
        ((baseChangeTripleFunctor i f hi g).obj M).ambient.IsFiniteType :=
  let := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
  fun g M _ ↦
  ⟨AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      (targetRestriction i f g).toLRSHom.toShHom M,
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      (ambientRestriction i f g).toLRSHom.toShHom M⟩

open Stacks.Thickenings in
omit [HasPushout i f] in
/-- If a module on `V'` is of finite presentation, then both components of its comparison
triple, its restrictions to `V` and to `U'`, are of finite presentation. -/
@[stacks 08KU "the finite presentation clause, for an arbitrary module on V'"]
theorem isFinitePresentation_baseChangeTripleFunctor_obj (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
    ∀ (g : V' ⟶ pushout i f) (M : V'.Modules) [M.IsFinitePresentation],
      ((baseChangeTripleFunctor i f hi g).obj M).target.IsFinitePresentation ∧
        ((baseChangeTripleFunctor i f hi g).obj M).ambient.IsFinitePresentation :=
  let := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
  fun g M hM ↦
  ⟨@_root_.Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (targetRestriction i f g).toLRSHom.toShHom M hM,
    @_root_.Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (ambientRestriction i f g).toLRSHom.toShHom M hM⟩

/-! ### Quasi-coherent modules flat over the base -/

/-- The projection `V = Y ×_{Y'} V' ⟶ Y`, the base change of `g` along `Y ⟶ Y'`. -/
noncomputable abbrev targetBase : pullback (pushout.inr i f) g ⟶ Y :=
  pullback.fst _ _

/-- The projection `U' = X' ×_{Y'} V' ⟶ X'`, the base change of `g` along `X' ⟶ Y'`. -/
noncomputable abbrev ambientBase : pullback (pushout.inl i f) g ⟶ X' :=
  pullback.fst _ _

variable {i f g}

/-- Quasi-coherent modules on `W` that are flat over `S` along `h : W ⟶ S`. -/
def FlatQuasicoherent {W S : Scheme.{u}} (h : W ⟶ S) : ObjectProperty W.Modules :=
  fun M ↦ M.IsQuasicoherent ∧ AlgebraicGeometry.IsFlatOver h.toLRSHom.toShHom M

/-- The category of quasi-coherent modules on `W` flat over `S` along `h : W ⟶ S`. -/
abbrev FlatQuasicoherentModule {W S : Scheme.{u}} (h : W ⟶ S) :=
  (FlatQuasicoherent h).FullSubcategory

variable (i f g)

/-- The condition on a gluing triple that the module on `V` be quasi-coherent and flat over `Y`,
and the module on `U'` quasi-coherent and flat over `X'`. -/
def IsFlatQuasicoherentTriple : ObjectProperty (GluingTriple i f g) := fun T ↦
  FlatQuasicoherent (targetBase i f g) T.target ∧
    FlatQuasicoherent (ambientBase i f g) T.ambient

/-- The category of gluing triples consisting of a quasi-coherent module on `V` flat over `Y`, a
quasi-coherent module on `U'` flat over `X'`, and an isomorphism of their two restrictions to
`U`. -/
abbrev FlatGluingTriple := (IsFlatQuasicoherentTriple i f g).FullSubcategory

/-- The comparison triple of a quasi-coherent module on `V'` flat over `Y'` consists of
quasi-coherent modules flat over `Y` and over `X'`. -/
theorem isFlatQuasicoherentTriple_baseChangeTripleFunctor_obj
    (hi : Stacks.Thickenings.IsThickening i) [IsAffineHom f] (M : V'.Modules)
    (hM : FlatQuasicoherent g M) :
    IsFlatQuasicoherentTriple i f g ((baseChangeTripleFunctor i f hi g).obj M) := by
  obtain ⟨hqc, hflat⟩ := hM
  have hV : IsPullback (targetRestriction i f g) (targetBase i f g) g (pushout.inr i f) :=
    (IsPullback.of_hasPullback (pushout.inr i f) g).flip
  have hU' : IsPullback (ambientRestriction i f g) (ambientBase i f g) g (pushout.inl i f) :=
    (IsPullback.of_hasPullback (pushout.inl i f) g).flip
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (targetRestriction i f g).toLRSHom.toShHom M hqc
  · exact @AlgebraicGeometry.modulePullback_isFlatOver _ _ _ _ _ _ _ _ hV M hqc hflat
  · exact @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (ambientRestriction i f g).toLRSHom.toShHom M hqc
  · exact @AlgebraicGeometry.modulePullback_isFlatOver _ _ _ _ _ _ _ _ hU' M hqc hflat

/-- The restriction of `Stacks.Pushout.baseChangeTripleFunctor` to quasi-coherent modules flat
over `Y'` on the one side and to triples of quasi-coherent modules flat over `Y` and over `X'` on
the other. -/
noncomputable def flatBaseChangeTripleFunctor (hi : Stacks.Thickenings.IsThickening i)
    [IsAffineHom f] :
    FlatQuasicoherentModule g ⥤ FlatGluingTriple i f g :=
  (IsFlatQuasicoherentTriple i f g).lift
    ((FlatQuasicoherent g).ι ⋙ baseChangeTripleFunctor i f hi g)
    fun M ↦ isFlatQuasicoherentTriple_baseChangeTripleFunctor_obj i f g hi M.obj M.property

/-- The restricted comparison functor followed by the inclusion of `FlatGluingTriple` is the
inclusion of `FlatQuasicoherentModule g` followed by the comparison functor. -/
theorem flatBaseChangeTripleFunctor_comp_ι (hi : Stacks.Thickenings.IsThickening i)
    [IsAffineHom f] :
    flatBaseChangeTripleFunctor i f g hi ⋙ (IsFlatQuasicoherentTriple i f g).ι =
      (FlatQuasicoherent g).ι ⋙ baseChangeTripleFunctor i f hi g :=
  rfl

/-! ### Finite type -/

/-- Finite type transports along an isomorphism of modules on a scheme. -/
private theorem finiteType_of_iso {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N)
    (hM : M.IsFiniteType) : N.IsFiniteType :=
  let : M.IsFiniteType := hM
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} e

/-- If the restriction of a module along `q` is of finite type and `p` factors through `q`, then
the restriction along `p` is of finite type as well. -/
private theorem finiteType_pullback_of_factorization
    {A B Z : Scheme.{u}} (M : Z.Modules) (p : A ⟶ Z) (q : B ⟶ Z)
    (h : A ⟶ B) (w : h ≫ q = p)
    (hq : ((Scheme.Modules.pullback q).obj M).IsFiniteType) :
    ((Scheme.Modules.pullback p).obj M).IsFiniteType :=
  let : ((Scheme.Modules.pullback q).obj M).IsFiniteType := hq
  finiteType_of_iso
    ((Scheme.Modules.pullbackComp h q).app M ≪≫ (Scheme.Modules.pullbackCongr w).app M)
    (AlgebraicGeometry.SheafOfModules.pullback_isFiniteType h.toLRSHom.toShHom
      ((Scheme.Modules.pullback q).obj M))

/-- If the restriction of a module along `pullback.snd u v` is of finite type, then so is its
restriction along any `p` such that `q ≫ u = p ≫ v`. -/
private theorem finiteType_pullback_of_lift
    {A B Z T : Scheme.{u}} (M : A.Modules) (u : B ⟶ Z) (v : A ⟶ Z)
    (p : T ⟶ A) (q : T ⟶ B) (w : q ≫ u = p ≫ v)
    (h : ((Scheme.Modules.pullback (pullback.snd u v)).obj M).IsFiniteType) :
    ((Scheme.Modules.pullback p).obj M).IsFiniteType :=
  finiteType_pullback_of_factorization M p (pullback.snd u v)
    (pullback.lift q p w) (pullback.lift_snd _ _ _) h

/-- Over a pair of affine charts of a cartesian square, finite type of the restriction to the
fibre product gives finite type of the extension of scalars to the tensor product of the two
coordinate rings. -/
private theorem finiteType_tensor_pullback
    {A B Z : Scheme.{u}} (M : A.Modules) (u : B ⟶ Z) (v : A ⟶ Z)
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (p : Spec (.of S) ⟶ A) (q : Spec (.of T) ⟶ B) (k : Spec (.of R) ⟶ Z)
    (hp : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ k = p ≫ v)
    (hq : Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ k = q ≫ u)
    (h : ((Scheme.Modules.pullback (pullback.snd u v)).obj M).IsFiniteType) :
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T)))).obj
        ((Scheme.Modules.pullback p).obj M)).IsFiniteType := by
  let l := CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T)
  let r := CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : T →+* S ⊗[R] T)
  have w : (Spec.map r ≫ q) ≫ u = (Spec.map l ≫ p) ≫ v := by
    rw [Category.assoc, ← hq, Category.assoc, ← hp,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    exact (CommRingCat.isPushout_tensorProduct R S T).w.symm
  exact finiteType_of_iso ((Scheme.Modules.pullbackComp (Spec.map l) p).app M).symm
    (finiteType_pullback_of_lift M u v _ _ w h)

/-- On an affine scheme a quasi-coherent module whose global sections are a finite module is of
finite type. -/
private theorem finiteType_on_affine_of_moduleFinite
    {R : CommRingCat.{u}} (N : (Spec R).Modules) [N.IsQuasicoherent]
    (hN : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj N)) :
    N.IsFiniteType := by
  have htilde : (tilde ((moduleSpecΓFunctor (R := R)).obj N)).IsFiniteType :=
    (AlgebraicGeometry.tilde_isFiniteType_iff ((moduleSpecΓFunctor (R := R)).obj N)).mpr hN
  have := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  exact finiteType_of_iso (asIso N.fromTildeΓ) htilde

/-- For a relative Milnor patching situation over a ring fibre product, a module flat over the
fibre product whose two base changes are finite is itself finite. -/
private theorem finite_of_flat_and_finite_components
    {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base)
    (L : ModuleCat.{u} D')
    (hL : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L))
    (hB : Module.Finite s.D
      ((letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
        letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
        letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
        letI : Algebra base.fibreProduct A :=
          (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
        MilnorPatching.extensionOfScalarsToTensorProductPullback (D' := D')
          ({ toBase with commutes' := fun _ ↦ rfl } : B →ₐ[base.fibreProduct] A)
          ({ surjection with commutes' := fun r ↦ r.property.symm } :
            A' →ₐ[base.fibreProduct] A)).obj L).fst)
    (hA : Module.Finite s.C'
      ((letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
        letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
        letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
        letI : Algebra base.fibreProduct A :=
          (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
        MilnorPatching.extensionOfScalarsToTensorProductPullback (D' := D')
          ({ toBase with commutes' := fun _ ↦ rfl } : B →ₐ[base.fibreProduct] A)
          ({ surjection with commutes' := fun r ↦ r.property.symm } :
            A' →ₐ[base.fibreProduct] A)).obj L).snd) :
    Module.Finite D' L := by
  let E := (let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    let : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    let : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    let : Algebra base.fibreProduct A :=
      (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
    MilnorPatching.extensionOfScalarsToTensorProductPullback (D' := D')
      ({ toBase with commutes' := fun _ ↦ rfl } : B →ₐ[base.fibreProduct] A)
      ({ surjection with commutes' := fun r ↦ r.property.symm } :
        A' →ₐ[base.fibreProduct] A))
  obtain ⟨G, e, adjG, he, -, -, hflat, hunit, hrest⟩ :=
    MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct s
  obtain ⟨F, eF, adjF, heF, hF⟩ :=
    MilnorPatching.relativeCompatiblePairsRightAdjoint_counit_isIso s
  have hunitL := hunit L hL
  have hfinite := MilnorPatching.finite_relativeRightAdjoint_obj_of_finite_components
    s F adjF hF (E.obj L) hB hA
  let : Module.Finite D' (F.obj (E.obj L)) := hfinite
  exact Module.Finite.equiv
    ((((adjG.rightAdjointUniq adjF).app (E.obj L)).toLinearEquiv.symm)
      ≪≫ₗ (asIso (adjG.unit.app L)).toLinearEquiv.symm)

/-- Finite type of the restriction of a quasi-coherent module on an affine scheme along a map of
affine schemes is finiteness of the extension of scalars of its sections. -/
private theorem finite_extendScalars_of_pullback
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (N : (Spec R).Modules) [N.IsQuasicoherent]
    (h : ((Scheme.Modules.pullback (Spec.map φ)).obj N).IsFiniteType) :
    Module.Finite S ((ModuleCat.extendScalars φ.hom).obj
      ((moduleSpecΓFunctor (R := R)).obj N)) := by
  exact (AlgebraicGeometry.tilde_isFiniteType_iff _).mp <| finiteType_of_iso
    (((Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso N.fromTildeΓ).symm) ≪≫
      (AlgebraicGeometry.pullbackTildeIso R S φ).app
        ((moduleSpecΓFunctor (R := R)).obj N)) h

/-- The affine case of the converse half of the finite-type clause, in the language of a relative
Milnor patching situation: a flat quasi-coherent module whose two base changes are of finite type
is of finite type. -/
private theorem finiteType_of_finite_pullbacks_over_fibreProduct
    {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base)
    (N : (Spec (CommRingCat.of D')).Modules) [N.IsQuasicoherent]
    (hflat : Module.Flat base.fibreProduct
      ((ModuleCat.restrictScalars s.toD').obj ((moduleSpecΓFunctor (R := .of D')).obj N)))
    (hB : ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom s.toD))).obj N).IsFiniteType)
    (hA : ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom s.toC'))).obj N).IsFiniteType) :
    N.IsFiniteType := by
  exact finiteType_on_affine_of_moduleFinite N <| finite_of_flat_and_finite_components s _ hflat
    (finite_extendScalars_of_pullback (CommRingCat.ofHom s.toD) N hB)
    (finite_extendScalars_of_pullback (CommRingCat.ofHom s.toC') N hA)

open Stacks.Thickenings in
/-- For a thickening `i` and an affine `f`, the map `X' ⟶ Y'` into the pushout is affine. -/
theorem isAffineHom_pushout_inl_of_isThickening (hi : IsThickening i) [IsAffineHom f] :
    IsAffineHom (pushout.inl i f) := by
  have : IsClosedImmersion (pushout.inr i f) :=
    (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  have : IsAffineHom (i ≫ pushout.inl i f) := by
    rw [pushout.condition]
    infer_instance
  exact isAffineHom_of_isThickening_comp forall_isAffine_of_isThickening i _ hi

/-- Identifying the sections over an affine open `W` of the target with a ring `R` by `E`, the
chart of an affine open `U` above `W` is compatible with `Spec` of any map `φ` equal to the
composite of `E.inv` and the restriction map of sections. -/
private theorem spec_map_comp_fromSpec_eq_of_appLE {V Y : Scheme.{u}} (g : V ⟶ Y)
    {W : Y.Opens} (hW : IsAffineOpen W) {U : V.Opens} (hU : IsAffineOpen U) (hUW : U ≤ g ⁻¹ᵁ W)
    {R : CommRingCat.{u}} (E : Γ(Y, W) ≅ R) (φ : R ⟶ Γ(V, U)) (hφ : E.inv ≫ g.appLE W U hUW = φ) :
    Spec.map φ ≫ (Spec.map E.hom ≫ hW.fromSpec) = hU.fromSpec ≫ g := by
  rw [← hφ]
  simp only [Spec.map_comp, Category.assoc]
  rw [← Spec.map_comp_assoc E.hom E.inv, E.hom_inv_id, Spec.map_id, Category.id_comp]
  exact IsAffineOpen.SpecMap_appLE_fromSpec g hW hU hUW

open Stacks.Thickenings in
/-- Let `U` be an affine open of `V'` lying above an affine open `W` of `Y'`. The restriction to
`U` of a quasi-coherent module flat over `Y'` whose two restrictions, to `V` and to `U'`, are of
finite type is of finite type. -/
private theorem finiteType_restrict_affine (hi : IsThickening i) [IsAffineHom f]
    (M : FlatQuasicoherentModule g)
    (U : V'.Opens) (hU : IsAffineOpen U) (W : (pushout i f).Opens) (hW : IsAffineOpen W)
    (hUW : U ≤ g ⁻¹ᵁ W)
    (hV : ((Scheme.Modules.pullback (targetRestriction i f g)).obj M.obj).IsFiniteType)
    (hX' : ((Scheme.Modules.pullback (ambientRestriction i f g)).obj M.obj).IsFiniteType) :
    (M.obj.restrict hU.fromSpec).IsFiniteType := by
  let a := pushout.inl i f
  let b := pushout.inr i f
  have : IsClosedImmersion i := hi.1
  have : IsClosedImmersion b := (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  have : IsAffineHom a := isAffineHom_pushout_inl_of_isThickening i f hi
  have hB : IsAffineOpen (b ⁻¹ᵁ W) := hW.preimage b
  have hA' : IsAffineOpen (a ⁻¹ᵁ W) := hW.preimage a
  let e : i ⁻¹ᵁ (a ⁻¹ᵁ W) = f ⁻¹ᵁ (b ⁻¹ᵁ W) :=
    congrArg (fun k : X ⟶ pushout i f ↦ k ⁻¹ᵁ W) (pushout.condition (f := i) (g := f))
  let t := f.app (b ⁻¹ᵁ W)
  let v := i.app (a ⁻¹ᵁ W) ≫ eqToHom (congrArg (fun V ↦ Γ(X, V)) e)
  let base : RingFibreProduct.Situation t.hom v.hom (RingHom.ker v.hom) :=
    ⟨(ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (fun V ↦ Γ(X, V)) e))).surjective.comp
        (i.app_surjective _ hA'), rfl⟩
  have hsq := pushout_structureSheaf_isPullback forall_isAffine_of_isThickening i f hi W
  have hcan := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit t v)
  let E : Γ(pushout i f, W) ≅ CommRingCat.of base.fibreProduct := hsq.isoIsPullback _ _ hcan
  let c := g.appLE W U hUW
  let s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base :=
    ⟨(E.inv ≫ c).hom⟩
  let N := M.obj.restrict hU.fromSpec
  have : M.obj.IsQuasicoherent := M.property.1
  have : N.IsQuasicoherent := inferInstance
  have hflat : Module.Flat base.fibreProduct
      ((ModuleCat.restrictScalars s.toD').obj
        ((moduleSpecΓFunctor (R := Γ(V', U))).obj N)) := by
    let : Module Γ(pushout i f, W) Γ(M.obj, U) := Module.compHom _ c.hom
    have : Module.Flat Γ(pushout i f, W) Γ(M.obj, U) :=
      ((AlgebraicGeometry.isFlatOver_tfae g M.obj).out 1 2 rfl rfl).mp M.property.2 U hU W hW hUW
    let : Algebra base.fibreProduct Γ(pushout i f, W) := E.inv.hom.toAlgebra
    let : Module base.fibreProduct Γ(M.obj, U) := Module.compHom _ E.inv.hom
    let : IsScalarTower base.fibreProduct Γ(pushout i f, W) Γ(M.obj, U) :=
      IsScalarTower.restrictScalars _ _ _
    have : Module.Flat base.fibreProduct Γ(pushout i f, W) :=
      Module.Flat.of_linearEquiv
        (Module.compHom.toLinearEquiv E.symm.commRingCatIsoToRingEquiv).symm
    have : Module.Flat base.fibreProduct Γ(M.obj, U) :=
      Module.Flat.trans _ Γ(pushout i f, W) _
    let L := affineSectionsLinearEquiv M.obj hU
    apply Module.Flat.of_linearEquiv
      (show ((ModuleCat.restrictScalars s.toD').obj
        ((moduleSpecΓFunctor (R := Γ(V', U))).obj N)) ≃ₗ[base.fibreProduct] Γ(M.obj, U) from
        { L.toAddEquiv with map_smul' := fun r m ↦ L.map_smul (c (E.inv r)) m })
  have hp := spec_map_comp_fromSpec_eq_of_appLE g hW hU hUW E (E.inv ≫ c) rfl
  have hE : E.inv ≫ b.app W = CommRingCat.ofHom (t.hom.pullbackFst v.hom) :=
    hsq.isoIsPullback_inv_fst _ _ hcan
  have hE' : E.inv ≫ a.app W = CommRingCat.ofHom (t.hom.pullbackSnd v.hom) :=
    hsq.isoIsPullback_inv_snd _ _ hcan
  let : Algebra base.fibreProduct Γ(V', U) := s.toD'.toAlgebra
  let : Algebra base.fibreProduct Γ(Y, b ⁻¹ᵁ W) := (t.hom.pullbackFst v.hom).toAlgebra
  let : Algebra base.fibreProduct Γ(X', a ⁻¹ᵁ W) := (t.hom.pullbackSnd v.hom).toAlgebra
  have hq := spec_map_comp_fromSpec_eq_of_appLE b hW hB le_rfl E _
    (by rw [← Scheme.Hom.app_eq_appLE, hE])
  have hq' := spec_map_comp_fromSpec_eq_of_appLE a hW hA' le_rfl E _
    (by rw [← Scheme.Hom.app_eq_appLE, hE'])
  apply finiteType_of_finite_pullbacks_over_fibreProduct s N hflat
  · exact finiteType_of_iso
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom s.toD))).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M.obj)).symm
      (finiteType_tensor_pullback M.obj b g hU.fromSpec hB.fromSpec _ hp hq hV)
  · exact finiteType_of_iso
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom s.toC'))).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M.obj)).symm
      (finiteType_tensor_pullback M.obj a g hU.fromSpec hA'.fromSpec _ hp hq' hX')

open Stacks.Thickenings in
/-- A quasi-coherent module on `V'` flat over `Y'` whose two restrictions, to `V` and to `U'`,
are of finite type is itself of finite type. -/
private theorem isFiniteType_of_components (hi : IsThickening i) [IsAffineHom f]
    (M : FlatQuasicoherentModule g)
    (hV : ((Scheme.Modules.pullback (targetRestriction i f g)).obj M.obj).IsFiniteType)
    (hX' : ((Scheme.Modules.pullback (ambientRestriction i f g)).obj M.obj).IsFiniteType) :
    M.obj.IsFiniteType := by
  classical
  let I := {p : V'.affineOpens × (pushout i f).affineOpens // p.1.1 ≤ g ⁻¹ᵁ p.2.1}
  let cov : V'.OpenCover := Scheme.Cover.mkOfCovers I
    (fun j ↦ Spec Γ(V', j.1.1.1)) (fun j ↦ j.1.1.2.fromSpec) (by
      intro x
      obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
        (X := pushout i f) (x := g x) (U := ⊤) (by trivial)
      obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset
        (X := V') (x := x) (U := g ⁻¹ᵁ W) hxW
      obtain ⟨y, hy⟩ : x ∈ Set.range hU.fromSpec.base := by rwa [hU.range_fromSpec]
      exact ⟨⟨(⟨U, hU⟩, ⟨W, hW⟩), hUW⟩, y, hy⟩)
    (fun j ↦ j.1.1.2.isOpenImmersion_fromSpec)
  apply AlgebraicGeometry.isFiniteType_of_pullback_fpqc M.obj M.property.1 cov.X cov.f
    (Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ cov.mem₀)
  intro j
  have : IsOpenImmersion j.1.1.2.fromSpec := j.1.1.2.isOpenImmersion_fromSpec
  exact finiteType_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback j.1.1.2.fromSpec).app M.obj)
    (finiteType_restrict_affine i f g hi M j.1.1.1 j.1.1.2 j.1.2.1 j.1.2.2 j.2 hV hX')

open Stacks.Thickenings in
omit [HasPushout i f] in
/-- A quasi-coherent module on `V'` flat over `Y'` is of finite type if and only if both
components of its comparison triple, its restrictions to `V` and to `U'`, are of finite type. -/
@[stacks 08KU "the finite type clause"]
theorem isFiniteType_iff_baseChangeTripleFunctor_obj (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
    ∀ (g : V' ⟶ pushout i f) (M : FlatQuasicoherentModule g),
      M.obj.IsFiniteType ↔
        ((baseChangeTripleFunctor i f hi g).obj M.obj).target.IsFiniteType ∧
          ((baseChangeTripleFunctor i f hi g).obj M.obj).ambient.IsFiniteType := by
  let := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
  intro g M
  refine ⟨fun hM ↦ ?_, fun hT ↦ isFiniteType_of_components i f g hi M hT.1 hT.2⟩
  let : M.obj.IsFiniteType := hM
  exact isFiniteType_baseChangeTripleFunctor_obj i f hi g M.obj

/-! ### Finite presentation -/

/-- The global sections of a finitely presented quasi-coherent module, restricted along an open
immersion from an affine scheme, are a finitely presented module. -/
private theorem finitePresentation_sections_of_openImmersion
    {Z : Scheme.{u}} (F : Z.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    {R : CommRingCat.{u}} (j : Spec R ⟶ Z) [IsOpenImmersion j] :
    Module.FinitePresentation R
      ((modulesSpecToSheaf.obj (F.restrict j)).presheaf.obj (.op ⊤)) := by
  let G := F.restrict j
  have hF : F.IsFinitePresentation := inferInstance
  have : G.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app F).symm
      (@_root_.Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
        j.toLRSHom.toShHom F hF)
  have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j F
  exact AlgebraicGeometry.finitePresentation_sections_of_affine G

/-- The sections of a finitely presented quasi-coherent module over an affine open are a finitely
presented module. -/
private theorem affineSections_of_isFinitePresentation
    {Z : Scheme.{u}} (M : Z.Modules) [M.IsQuasicoherent] [M.IsFinitePresentation]
    {U : Z.Opens} (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(Z, U) Γ(M, U) :=
  (affineSectionsLinearEquiv M hU).finitePresentation_iff.mp
    (finitePresentation_sections_of_openImmersion M hU.fromSpec)

/-- A finite presentation can be transported along an isomorphism of modules. -/
private theorem exists_isFinite_presentation_of_iso {Z : Scheme.{u}} {M N : Z.Modules}
    (e : M ≅ N) (P : M.Presentation) [hP : P.IsFinite] : ∃ Q : N.Presentation, Q.IsFinite :=
  ⟨@SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom e.isIso_hom P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

/-- A finite presentation of the restriction of a module to an open gives a finite presentation
of its slice over that open. -/
private theorem over_has_finite_global_presentation
    {Z : Scheme.{u}} (U : Z.Opens) (M : Z.Modules)
    (P : (M.restrict U.ι).Presentation) [P.IsFinite] :
    ∃ Q : (M.over U).Presentation, Q.IsFinite := by
  let e := Scheme.Modules.overEquiv U
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  have : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} e.inverse :=
    CategoryTheory.Adjunction.isEquivalence_preservesColimits e.inverse
  let η : SheafOfModules.unit (Z.ringCatSheaf.over U) ≅
      e.inverse.obj (SheafOfModules.unit (U : Scheme).ringCatSheaf) :=
    (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit U Z.ringCatSheaf).symm
  have hpres : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      e.inverse := inferInstance
  let P' : (e.inverse.obj (M.restrict U.ι)).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P e.inverse hpres η
  let iso : e.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm) ≪≫
      (e.unitIso.app (M.over U)).symm
  let Q := P'.ofIsIso iso.hom
  refine ⟨Q, ?_⟩
  have : P'.IsFinite :=
    ⟨⟨‹P.IsFinite›.isFiniteType_generators.finite⟩, ⟨‹P.IsFinite›.isFiniteType_relations.finite⟩⟩
  infer_instance

/-- On the iterated slice of the opens site of a topological space, the inclusion of
abelian-group-valued sheaves into presheaves has a left adjoint. -/
private instance isRightAdjoint_sheafToPresheaf_opensOverOver {T : Type u} [TopologicalSpace T]
    (W : TopologicalSpace.Opens T) (Q : CategoryTheory.Over W) :
    (CategoryTheory.sheafToPresheaf
      (((_root_.Opens.grothendieckTopology T).over W).over Q)
      AddCommGrpCat.{u}).IsRightAdjoint := inferInstance

/-- On the iterated slice of the opens site of a topological space, sheafification of
abelian-group-valued presheaves inverts exactly the locally bijective maps. -/
private instance wEqualsLocallyBijective_opensOverOver {T : Type u} [TopologicalSpace T]
    (W : TopologicalSpace.Opens T) (Q : CategoryTheory.Over W) :
    (((_root_.Opens.grothendieckTopology T).over W).over Q).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance

/-- A module whose restriction to an open admits a finite presentation is of finite presentation
on the slice over that open. -/
private theorem over_isFinitePresentation_of_finite_global
    {Z : Scheme.{u}} (U : Z.Opens) (M : Z.Modules)
    (P : (M.restrict U.ι).Presentation) [P.IsFinite] :
    (M.over U).IsFinitePresentation := by
  obtain ⟨Q, hQ⟩ := over_has_finite_global_presentation U M P
  let : Q.IsFinite := hQ
  refine { exists_quasicoherentData := ⟨Q.quasicoherentData.shrink, ?_⟩ }
  constructor
  intro j
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · change Finite Q.generators.I
    exact hQ.isFiniteType_generators.finite
  · change Finite Q.relations.I
    exact hQ.isFiniteType_relations.finite

/-- Finite presentation is local: a module of finite presentation on each member of a covering
family of the terminal object is of finite presentation. -/
private theorem isFinitePresentation_of_coversTop
    {C : Type u} [CategoryTheory.Category.{u} C]
    {J : CategoryTheory.GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{u}}
    [CategoryTheory.Limits.HasBinaryProducts C]
    [CategoryTheory.HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ Z, CategoryTheory.HasWeakSheafify (J.over Z) AddCommGrpCat.{u}]
    [∀ Z, (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ Z W, CategoryTheory.HasWeakSheafify ((J.over Z).over W) AddCommGrpCat.{u}]
    [∀ Z W, ((J.over Z).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) {I : Type u} (Z : I → C)
    (hZ : J.CoversTop Z) [∀ j, (M.over (Z j)).IsFinitePresentation] :
    M.IsFinitePresentation := by
  let D (j : I) := (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (M.over (Z j))).choose
  let (j : I) : (D j).IsFinitePresentation :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (M.over (Z j))).choose_spec
  refine { exists_quasicoherentData :=
    ⟨SheafOfModules.QuasicoherentData.bind M Z hZ D, ?_⟩ }
  constructor
  intro j
  refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
  all_goals constructor
  · exact inferInstanceAs (Finite ((D j.1).presentation j.2).generators.I)
  · exact inferInstanceAs (Finite ((D j.1).presentation j.2).relations.I)

/-- A quasi-coherent module whose sections over an affine open are a finitely presented module is
of finite presentation on the slice over that affine open. -/
private theorem finitePresentation_of_affineSections
    {Z : Scheme.{u}} (M : Z.Modules) [M.IsQuasicoherent]
    {U : Z.Opens} (hU : IsAffineOpen U)
    (hM : Module.FinitePresentation Γ(Z, U) Γ(M, U)) :
    (M.over hU.fromSpec.opensRange).IsFinitePresentation := by
  classical
  let j := hU.fromSpec
  have : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  let N := M.restrict j
  have hA : Module.FinitePresentation Γ(Z, U)
      ((modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)) :=
    (affineSectionsLinearEquiv M hU).finitePresentation_iff.mpr hM
  have : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j M
  let eN : tilde ((modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)) ≅ N := asIso N.fromTildeΓ
  have hExists : ∃ P : N.Presentation, P.IsFinite := by
    let A : ModuleCat Γ(Z, U) := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
    have : Module.FinitePresentation Γ(Z, U) A := hA
    obtain ⟨P₀, hP₀⟩ := AlgebraicGeometry.tilde_has_finite_presentation A
    let : P₀.IsFinite := hP₀
    exact exists_isFinite_presentation_of_iso eN P₀
  obtain ⟨P, hP⟩ := hExists
  let fU := j.isoOpensRange
  have hfU : fU.inv ≫ j = j.opensRange.ι := Scheme.Hom.isoOpensRange_inv_comp j
  let eF : N.restrict fU.inv ≅ M.restrict j.opensRange.ι :=
    ((Scheme.Modules.restrictFunctorIsoPullback fU.inv).app N) ≪≫
      ((Scheme.Modules.pullback fU.inv).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback j).app M)) ≪≫
      ((Scheme.Modules.pullbackComp fU.inv j).app M) ≪≫
      ((Scheme.Modules.pullbackCongr hfU).app M) ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback j.opensRange.ι).app M).symm
  let P' := Scheme.Modules.presentationRestrict fU.inv P
  have : P'.IsFinite :=
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩
  obtain ⟨P'', hP''⟩ := exists_isFinite_presentation_of_iso eF P'
  exact over_isFinitePresentation_of_finite_global j.opensRange M P''

/-- Finite presentation of an extension of scalars is invariant under an isomorphism of the
target ring over the source. -/
private theorem finitePresentation_extendScalars_of_ringEquiv
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : R →+* T) (e : S ≃+* T)
    (he : e.toRingHom.comp φ = ψ) (M : ModuleCat.{u} R)
    (h : Module.FinitePresentation T ((ModuleCat.extendScalars ψ).obj M)) :
    Module.FinitePresentation S ((ModuleCat.extendScalars φ).obj M) := by
  let : Algebra R S := φ.toAlgebra
  let : Algebra R T := ψ.toAlgebra
  let : Algebra S T := e.toRingHom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' he.symm
  let eL : S ≃ₗ[S] T := LinearEquiv.ofBijective (Algebra.linearMap S T) e.bijective
  let : Module.FinitePresentation S T := Module.FinitePresentation.of_equiv eL
  let : Module.FinitePresentation T (T ⊗[R] M) := h
  let : Module.FinitePresentation S (T ⊗[R] M) := Module.FinitePresentation.trans S _ T
  exact (TensorProduct.AlgebraTensorModule.congr eL
    (LinearEquiv.refl R M)).finitePresentation_iff.mpr inferInstance

/-- Flatness of a restriction of scalars is invariant under an isomorphism of the base ring. -/
private theorem flat_restrictScalars_ringEquiv
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* T) (e : S ≃+* R) (M : ModuleCat.{u} T)
    (h : Module.Flat R ((ModuleCat.restrictScalars φ).obj M)) :
    Module.Flat S ((ModuleCat.restrictScalars (φ.comp e.toRingHom)).obj M) := by
  let : Algebra S R := e.toRingHom.toAlgebra
  let : Module R M := Module.compHom M φ
  let : Module S M := Module.compHom M (φ.comp e.toRingHom)
  let : IsScalarTower S R M := ⟨fun s r m ↦ by
    change (φ (e s * r)) • m = φ (e s) • (φ r • m)
    rw [map_mul, mul_smul]⟩
  let eL : S ≃ₗ[S] R := LinearEquiv.ofBijective (Algebra.linearMap S R) e.bijective
  let : Module.Flat S R := Module.Flat.of_linearEquiv eL.symm
  let : Module.Flat R M := h
  exact Module.Flat.trans S R M

/-- Finite presentation passes to the tensor product along a cocartesian square of rings, the
base being identified with another ring by an isomorphism. -/
private theorem finitePresentation_extendScalars_of_isPushout
    {R R' S T Q : Type u} [CommRing R] [CommRing R'] [CommRing S] [CommRing T]
    [CommRing Q] (φ : R →+* S) (ψ : R →+* T) (α : S →+* Q) (β : T →+* Q)
    (h : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
      (CommRingCat.ofHom α) (CommRingCat.ofHom β))
    (e : R ≃+* R') (ψ' : R' →+* T) (hψ : ψ'.comp e.toRingHom = ψ)
    (M : ModuleCat.{u} S)
    (hM : Module.FinitePresentation Q ((ModuleCat.extendScalars α).obj M)) :
    letI : Algebra R' S := (φ.comp e.symm.toRingHom).toAlgebra
    letI : Algebra R' T := ψ'.toAlgebra
    Module.FinitePresentation (S ⊗[R'] T)
      ((ModuleCat.extendScalars (Algebra.TensorProduct.includeLeftRingHom
        (R := R') (A := S) (B := T))).obj M) := by
  let φ' := φ.comp e.symm.toRingHom
  let : Algebra R' S := φ'.toAlgebra
  let : Algebra R' T := ψ'.toAlgebra
  let : Algebra S Q := α.toAlgebra
  let : Algebra T Q := β.toAlgebra
  let : Algebra R' Q := (β.comp ψ').toAlgebra
  have h' : IsPushout (CommRingCat.ofHom φ') (CommRingCat.ofHom ψ')
      (CommRingCat.ofHom α) (CommRingCat.ofHom β) := by
    apply h.of_iso e.toCommRingCatIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · ext x
      simp [φ', RingHom.comp_apply]
    · exact CommRingCat.hom_ext hψ.symm
    · simp
    · simp
  let : IsScalarTower R' T Q := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R' S Q := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom h'.w).symm
  let : Algebra.IsPushout R' S T Q := CommRingCat.isPushout_iff_isPushout.mp h'
  let eQ := Algebra.IsPushout.equiv R' S T Q
  exact finitePresentation_extendScalars_of_ringEquiv _ α eQ.toRingEquiv
    (RingHom.ext eQ.commutes) M hM

/-- For an affine morphism `u` and affine opens `W ⊆ S`, `T ⊆ A` with `T ≤ v ⁻¹ᵁ W`, the square
of coordinate rings of `W`, `u ⁻¹ᵁ W`, `T` and of the corresponding chart of `B ×_S A` is
cocartesian. -/
theorem affinePullbackChart_isPushout
    {A B S : Scheme.{u}} (u : B ⟶ S) (v : A ⟶ S) [IsAffineHom u]
    {W : S.Opens} (hW : IsAffineOpen W) {T : A.Opens} (hT : IsAffineOpen T)
    (hWT : T ≤ v ⁻¹ᵁ W) :
    IsPushout (u.appLE W (u ⁻¹ᵁ W) le_rfl) (v.appLE W T hWT)
      ((pullback.fst u v).appLE (u ⁻¹ᵁ W)
        (pullback.fst u v ⁻¹ᵁ (u ⁻¹ᵁ W) ⊓ pullback.snd u v ⁻¹ᵁ T) inf_le_left)
      ((pullback.snd u v).appLE T
        (pullback.fst u v ⁻¹ᵁ (u ⁻¹ᵁ W) ⊓ pullback.snd u v ⁻¹ᵁ T) inf_le_right) := by
  let YW := u ⁻¹ᵁ W
  let Z := pullback.fst u v ⁻¹ᵁ YW ⊓ pullback.snd u v ⁻¹ᵁ T
  have hYW : IsAffineOpen YW := hW.preimage u
  let : IsAffine YW.toScheme := hYW
  let : IsAffine T.toScheme := hT
  let : IsAffine W.toScheme := hW
  have hZ : IsAffineOpen Z := isAffineOpen_inf_preimage u v (le_refl YW) hWT
  let : IsAffine Z.toScheme := hZ
  have hres : IsPullback
      ((pullback.fst u v).resLE YW Z inf_le_left)
      ((pullback.snd u v).resLE T Z inf_le_right)
      (u.resLE W YW le_rfl) (v.resLE W T hWT) :=
    Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback u v) hWT le_rfl (UY := Z) rfl
  have hpush0 := isPushout_appTop_of_isPullback hres
  have hcommf : (u.resLE W YW le_rfl).appTop ≫ YW.topIso.hom =
      W.topIso.hom ≫ u.appLE W YW le_rfl :=
    (arrowResLEAppIso u W YW le_rfl).hom.w.symm
  have hcommg : (v.resLE W T hWT).appTop ≫ T.topIso.hom =
      W.topIso.hom ≫ v.appLE W T hWT :=
    (arrowResLEAppIso v W T hWT).hom.w.symm
  have hcommfst : ((pullback.fst u v).resLE YW Z inf_le_left).appTop ≫ Z.topIso.hom =
      YW.topIso.hom ≫ (pullback.fst u v).appLE YW Z inf_le_left :=
    (arrowResLEAppIso (pullback.fst u v) YW Z inf_le_left).hom.w.symm
  have hcommsnd : ((pullback.snd u v).resLE T Z inf_le_right).appTop ≫ Z.topIso.hom =
      T.topIso.hom ≫ (pullback.snd u v).appLE T Z inf_le_right :=
    (arrowResLEAppIso (pullback.snd u v) T Z inf_le_right).hom.w.symm
  exact hpush0.of_iso W.topIso YW.topIso T.topIso Z.topIso
    hcommf hcommg hcommfst hcommsnd

/-- Over the affine charts of `Stacks.Pushout.affinePullbackChart_isPushout`, finite presentation
of the restriction of a module to the fibre product is finite presentation of the extension of
its sections to the tensor product of the two coordinate rings. -/
private theorem finitePresentation_tensor_of_affinePullback
    {A B S : Scheme.{u}} (u : B ⟶ S) (v : A ⟶ S) [IsAffineHom u]
    {W : S.Opens} (hW : IsAffineOpen W) {T : A.Opens} (hT : IsAffineOpen T)
    (hWT : T ≤ v ⁻¹ᵁ W) (M : A.Modules) [M.IsQuasicoherent]
    (hM : ((Scheme.Modules.pullback (pullback.snd u v)).obj M).IsFinitePresentation)
    {R : Type u} [CommRing R] (e : Γ(S, W) ≃+* R)
    (b : R →+* Γ(B, u ⁻¹ᵁ W)) (hb : b.comp e.toRingHom = (u.app W).hom) :
    letI : Algebra R Γ(A, T) := ((v.appLE W T hWT).hom.comp e.symm.toRingHom).toAlgebra
    letI : Algebra R Γ(B, u ⁻¹ᵁ W) := b.toAlgebra
    Module.FinitePresentation (TensorProduct R Γ(A, T) Γ(B, u ⁻¹ᵁ W))
      ((ModuleCat.extendScalars (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := Γ(A, T)) (B := Γ(B, u ⁻¹ᵁ W)))).obj
          (ModuleCat.of Γ(A, T) Γ(M, T))) := by
  let YW := u ⁻¹ᵁ W
  let Z := pullback.fst u v ⁻¹ᵁ YW ⊓ pullback.snd u v ⁻¹ᵁ T
  have hYW : IsAffineOpen YW := hW.preimage u
  let : IsAffine YW.toScheme := hYW
  let : IsAffine T.toScheme := hT
  let : IsAffine W.toScheme := hW
  have hZ : IsAffineOpen Z := isAffineOpen_inf_preimage u v (le_refl YW) hWT
  let N := (Scheme.Modules.pullback (pullback.snd u v)).obj M
  let : N.IsFinitePresentation := hM
  have : N.IsQuasicoherent :=
    ⟨⟨(SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose⟩⟩
  have hN := affineSections_of_isFinitePresentation N hZ
  let eN := affinePullbackSectionsBaseChangeIso (pullback.snd u v) M hT hZ inf_le_right
  have hN' : Module.FinitePresentation Γ(pullback u v, Z)
      ((ModuleCat.extendScalars ((pullback.snd u v).appLE T Z inf_le_right).hom).obj
        (ModuleCat.of Γ(A, T) Γ(M, T))) :=
    eN.toLinearEquiv.finitePresentation_iff.mpr hN
  apply finitePresentation_extendScalars_of_isPushout
    (v.appLE W T hWT).hom (u.appLE W YW le_rfl).hom
    ((pullback.snd u v).appLE T Z inf_le_right).hom
    ((pullback.fst u v).appLE YW Z inf_le_left).hom
    (affinePullbackChart_isPushout u v hW hT hWT).flip e b ?_
    (ModuleCat.of Γ(A, T) Γ(M, T)) hN'
  simpa only [YW, Scheme.Hom.appLE_eq_app] using hb

/-- The relative scalar extension of a Milnor patching situation: a `D'`-module goes to the
compatible pair of its two base changes. -/
private noncomputable abbrev fibreProductScalarExtension
    {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base) :
    ModuleCat.{u} D' ⥤
      MilnorPatching.RelativeModuleFibreProductSituation.CompatibleModules s :=
  letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
  letI : Algebra base.fibreProduct B :=
    (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
  letI : Algebra base.fibreProduct A' :=
    (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
  letI : Algebra base.fibreProduct A :=
    (toBase.comp (MilnorPatching.RelativeModuleFibreProductSituation.toB
      (base := base))).toAlgebra
  MilnorPatching.extensionOfScalarsToTensorProductPullback (D' := D')
    ({ toBase with commutes' := fun _ ↦ rfl } : B →ₐ[base.fibreProduct] A)
    ({ surjection with
        commutes' := fun r ↦ by
          change surjection r.1.2 = toBase r.1.1
          exact r.property.symm } : A' →ₐ[base.fibreProduct] A)

/-- The two components of the relative scalar extension of a module flat over the fibre product
are flat over their respective rings. -/
private theorem flat_fibreProductScalarExtension
    {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base)
    (L : ModuleCat.{u} D')
    (hL : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L)) :
    Module.Flat B ((ModuleCat.restrictScalars s.BtoD).obj
      ((fibreProductScalarExtension s).obj L).fst) ∧
    Module.Flat A' ((ModuleCat.restrictScalars s.A'toC').obj
      ((fibreProductScalarExtension s).obj L).snd) := by
  obtain ⟨F, e, adj, -, -, -, -, -, q, ⟨α⟩, -⟩ :=
    MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct s
  let L' : (show ObjectProperty (ModuleCat.{u} D') from fun K ↦
      Module.Flat base.fibreProduct
        ((ModuleCat.restrictScalars s.toD').obj K)).FullSubcategory := ⟨L, hL⟩
  have hflat := (q.functor.obj L').property
  let iso := α.app L'
  refine ⟨?_, ?_⟩
  · exact @Module.Flat.of_linearEquiv B _ _ _ _ _ _ _ hflat.1
      ((ModuleCat.restrictScalars s.BtoD).mapIso (asIso iso.hom.fst)).toLinearEquiv
  · exact @Module.Flat.of_linearEquiv A' _ _ _ _ _ _ _ hflat.2
      ((ModuleCat.restrictScalars s.A'toC').mapIso (asIso iso.hom.snd)).toLinearEquiv

/-- A module flat over the fibre product whose two base changes are finitely presented and
relatively flat is finitely presented, given a factorization of `B' ⟶ D'` through a flat algebra
followed by a finitely presented ring map. -/
private theorem moduleFinitePresentation_of_flat_fibreProduct_baseChange
    {A A' B D' D'' : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing D'] [CommRing D''] {toBase : B →+* A} {surjection : A' →+* A}
    {I : Ideal A'} {base : RingFibreProduct.Situation toBase surjection I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base)
    (L : ModuleCat.{u} D')
    (hLflat : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L))
    (hBfp : Module.FinitePresentation s.D ((fibreProductScalarExtension s).obj L).fst)
    (hBflat : Module.Flat B
      ((ModuleCat.restrictScalars s.BtoD).obj ((fibreProductScalarExtension s).obj L).fst))
    (hAfp : Module.FinitePresentation s.C' ((fibreProductScalarExtension s).obj L).snd)
    (hAflat : Module.Flat A'
      ((ModuleCat.restrictScalars s.A'toC').obj ((fibreProductScalarExtension s).obj L).snd))
    (toD'' : base.fibreProduct →+* D'') (fromD'' : D'' →+* D')
    (hfac : fromD''.comp toD'' = s.toD')
    (hD''flat : @Module.Flat base.fibreProduct D'' _ _ (Module.compHom D'' toD''))
    (hD''fp : RingHom.FinitePresentation fromD'') :
    Module.FinitePresentation D' L := by
  let E : ModuleCat.{u} D' ⥤
      MilnorPatching.RelativeModuleFibreProductSituation.CompatibleModules s :=
    fibreProductScalarExtension s
  obtain ⟨F₀, e₀, adj₀, -, hcounit⟩ :=
    MilnorPatching.relativeCompatiblePairsRightAdjoint_counit_isIso s
  have hcounit' : IsIso adj₀.counit := hcounit
  obtain ⟨F₁, e₁, adj₁, -, -, -, -, hunit₁, -⟩ :=
    MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct s
  have hunit₁L : IsIso (adj₁.unit.app L) := hunit₁ L hLflat
  let α : F₀ ≅ F₁ := adj₀.rightAdjointUniq adj₁
  let X₀ := E.obj L
  have hunit₀L : IsIso (adj₀.unit.app L) := by
    have hcomp : IsIso (adj₀.unit.app L ≫ α.hom.app X₀) := by
      rw [Adjunction.unit_rightAdjointUniq_hom_app adj₀ adj₁ L]
      exact hunit₁L
    exact IsIso.of_isIso_comp_right (adj₀.unit.app L) (α.hom.app X₀)
  let : IsIso adj₀.counit := hcounit'
  have hFfp : Module.FinitePresentation D' (F₀.obj X₀) :=
    MilnorPatching.finitePresentation_rightAdjoint_obj_of_factorization
      s F₀ adj₀ hcounit' X₀ hBfp hBflat hAfp hAflat
        toD'' fromD'' hfac hD''flat hD''fp
  let : IsIso (adj₀.unit.app L) := hunit₀L
  exact (asIso (adj₀.unit.app L)).toLinearEquiv.finitePresentation_iff.mpr hFfp

/-- If `B' ⟶ D'` is of finite presentation, a module flat over the fibre product whose two base
changes are finitely presented and relatively flat is finitely presented. -/
private theorem moduleFinitePresentation_of_affine_fibreProduct_baseChange
    {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base)
    (hsfp : RingHom.FinitePresentation s.toD')
    (L : ModuleCat.{u} D')
    (hLflat : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L))
    (hBfp : Module.FinitePresentation s.D ((fibreProductScalarExtension s).obj L).fst)
    (hBflat : Module.Flat B
      ((ModuleCat.restrictScalars s.BtoD).obj ((fibreProductScalarExtension s).obj L).fst))
    (hAfp : Module.FinitePresentation s.C' ((fibreProductScalarExtension s).obj L).snd)
    (hAflat : Module.Flat A'
      ((ModuleCat.restrictScalars s.A'toC').obj ((fibreProductScalarExtension s).obj L).snd)) :
    Module.FinitePresentation D' L := by
  let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
  have : Algebra.FinitePresentation base.fibreProduct D' :=
    RingHom.finitePresentation_algebraMap.mp hsfp
  obtain ⟨n, φ, hsurj, hker⟩ :=
    Algebra.FinitePresentation.out (R := base.fibreProduct) (A := D')
  let D'' := MvPolynomial (Fin n) base.fibreProduct
  let toD'' : base.fibreProduct →+* D'' := algebraMap _ _
  let fromD'' : D'' →+* D' := φ.toRingHom
  have hfac : fromD''.comp toD'' = s.toD' := by
    ext r
    change φ (algebraMap base.fibreProduct D'' r) = s.toD' r
    exact φ.commutes r
  have hD''flat : @Module.Flat base.fibreProduct D'' _ _ (Module.compHom D'' toD'') := by
    have hmod : Module.compHom D'' toD'' = AddMonoidAlgebra.instModule :=
      Module.ext' (Module.compHom D'' toD'') AddMonoidAlgebra.instModule
        (fun r x ↦ by
          change @SMul.smul base.fibreProduct D''
              (Module.compHom D'' toD'').toDistribMulAction.toSMul r x =
            @SMul.smul base.fibreProduct D''
              AddMonoidAlgebra.instModule.toDistribMulAction.toSMul r x
          calc
            _ = toD'' r * x := rfl
            _ = algebraMap base.fibreProduct D'' r * x := rfl
            _ = @SMul.smul base.fibreProduct D''
                AddMonoidAlgebra.instModule.toDistribMulAction.toSMul r x :=
              (AddMonoidAlgebra.algebra (R := base.fibreProduct)
                (A := base.fibreProduct) (M := Fin n →₀ ℕ)).smul_def' r x |>.symm)
    have hfree : @Module.Free base.fibreProduct D'' _ _ AddMonoidAlgebra.instModule :=
      @Module.Free.of_basis base.fibreProduct D'' _ _ AddMonoidAlgebra.instModule
        (Fin n →₀ ℕ) (AddMonoidAlgebra.basis (Fin n →₀ ℕ) base.fibreProduct)
    have hflat : @Module.Flat base.fibreProduct D'' _ _ AddMonoidAlgebra.instModule :=
      @Module.Flat.of_free base.fibreProduct D'' _ _ AddMonoidAlgebra.instModule hfree
    exact hmod ▸ hflat
  exact moduleFinitePresentation_of_flat_fibreProduct_baseChange s L hLflat
    hBfp hBflat hAfp hAflat toD'' fromD'' hfac hD''flat
    (RingHom.FinitePresentation.of_surjective fromD'' hsurj hker)

open Stacks.Thickenings in
/-- Let `g` be locally of finite presentation and let `U` be an affine open of `V'` lying above an
affine open `W` of `Y'`. The sections over `U` of a quasi-coherent module flat over `Y'` whose two
restrictions are of finite presentation are a finitely presented module. -/
private theorem finitePresentation_sections_of_components (hi : IsThickening i) [IsAffineHom f]
    (hg : LocallyOfFinitePresentation g) (M : FlatQuasicoherentModule g)
    (hV : ((Scheme.Modules.pullback (targetRestriction i f g)).obj
      M.obj).IsFinitePresentation)
    (hX' : ((Scheme.Modules.pullback (ambientRestriction i f g)).obj
      M.obj).IsFinitePresentation)
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W) :
    Module.FinitePresentation Γ(V', U) Γ(M.obj, U) := by
  have : M.obj.IsQuasicoherent := M.property.1
  have : IsClosedImmersion i := hi.1
  have : IsClosedImmersion (pushout.inr i f) :=
    (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  have : IsAffineHom (pushout.inl i f) := isAffineHom_pushout_inl_of_isThickening i f hi
  have hA' : IsAffineOpen (pushout.inl i f ⁻¹ᵁ W) := hW.preimage (pushout.inl i f)
  let eop : i ⁻¹ᵁ (pushout.inl i f ⁻¹ᵁ W) = f ⁻¹ᵁ (pushout.inr i f ⁻¹ᵁ W) :=
    congrArg (fun k : X ⟶ pushout i f ↦ k ⁻¹ᵁ W) (pushout.condition (f := i) (g := f))
  let t := f.app (pushout.inr i f ⁻¹ᵁ W)
  let v := i.app (pushout.inl i f ⁻¹ᵁ W) ≫ eqToHom (congrArg (fun V ↦ Γ(X, V)) eop)
  let base : RingFibreProduct.Situation t.hom v.hom (RingHom.ker v.hom) :=
    ⟨(ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (fun V ↦ Γ(X, V)) eop))).surjective.comp
        (i.app_surjective _ hA'), rfl⟩
  have hsq := pushout_structureSheaf_isPullback forall_isAffine_of_isThickening i f hi W
  have hcan := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit t v)
  let E : Γ(pushout i f, W) ≅ CommRingCat.of base.fibreProduct := hsq.isoIsPullback _ _ hcan
  let e : Γ(pushout i f, W) ≃+* base.fibreProduct := E.commRingCatIsoToRingEquiv
  let s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base :=
    ⟨(g.appLE W U hUW).hom.comp e.symm.toRingHom⟩
  let L := ModuleCat.of Γ(V', U) Γ(M.obj, U)
  have hflat : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L) := by
    exact flat_restrictScalars_ringEquiv (g.appLE W U hUW).hom e.symm L
      (((AlgebraicGeometry.isFlatOver_tfae g M.obj).out 1 2 rfl rfl).mp M.property.2 U hU W hW hUW)
  have heB : (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).comp
      e.toRingHom = ((pushout.inr i f).app W).hom :=
    congrArg CommRingCat.Hom.hom (hsq.isoIsPullback_hom_fst _ _ hcan)
  have heA : (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)).comp
      e.toRingHom = ((pushout.inl i f).app W).hom :=
    congrArg CommRingCat.Hom.hom (hsq.isoIsPullback_hom_snd _ _ hcan)
  have hBfp : Module.FinitePresentation s.D ((fibreProductScalarExtension s).obj L).fst :=
    finitePresentation_tensor_of_affinePullback (pushout.inr i f) g hW hU hUW
      M.obj hV e _ heB
  have hAfp : Module.FinitePresentation s.C' ((fibreProductScalarExtension s).obj L).snd :=
    finitePresentation_tensor_of_affinePullback (pushout.inl i f) g hW hU hUW
      M.obj hX' e _ heA
  obtain ⟨hBflat, hAflat⟩ := flat_fibreProductScalarExtension s L hflat
  have hsfp : RingHom.FinitePresentation s.toD' := by
    have hφ : RingHom.FinitePresentation (g.appLE W U hUW).hom :=
      hg.finitePresentation_appLE hW hU hUW
    have he : RingHom.FinitePresentation e.symm.toRingHom := by
      apply RingHom.FinitePresentation.of_surjective e.symm.toRingHom e.symm.surjective
      have hker : RingHom.ker e.symm.toRingHom = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).mp e.symm.injective
      rw [hker]
      exact Submodule.fg_bot
    exact RingHom.FinitePresentation.comp hφ he
  exact moduleFinitePresentation_of_affine_fibreProduct_baseChange s hsfp L hflat
    hBfp hBflat hAfp hAflat

open Stacks.Thickenings in
/-- If `V' ⟶ Y'` is locally of finite presentation, a quasi-coherent module on `V'` flat over `Y'`
whose two restrictions, to `V` and to `U'`, are of finite presentation is itself of finite
presentation. -/
private theorem isFinitePresentation_of_components (hi : IsThickening i) [IsAffineHom f]
    (hg : LocallyOfFinitePresentation g) (M : FlatQuasicoherentModule g)
    (hV : ((Scheme.Modules.pullback (targetRestriction i f g)).obj
      M.obj).IsFinitePresentation)
    (hX' : ((Scheme.Modules.pullback (ambientRestriction i f g)).obj
      M.obj).IsFinitePresentation) :
    M.obj.IsFinitePresentation := by
  classical
  have : M.obj.IsQuasicoherent := M.property.1
  have hlocal (x : V') : ∃ T : V'.Opens, x ∈ T ∧ (M.obj.over T).IsFinitePresentation := by
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ := (pushout i f).isBasis_affineOpens.exists_subset_of_mem_open
      (show g x ∈ (⊤ : (pushout i f).Opens) from trivial) (⊤ : (pushout i f).Opens).2
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUW⟩ := V'.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ g ⁻¹ᵁ W from hxW) (g ⁻¹ᵁ W).2
    refine ⟨U, hxU, ?_⟩
    have h := finitePresentation_of_affineSections M.obj hU
      (finitePresentation_sections_of_components i f g hi hg M hV hX' hW hU hUW)
    exact Eq.mp (congrArg (fun Q ↦ (M.obj.over Q).IsFinitePresentation)
      hU.opensRange_fromSpec) h
  choose T hxT hT using hlocal
  let (x : V') : (M.obj.over (T x)).IsFinitePresentation := hT x
  apply isFinitePresentation_of_coversTop M.obj T
  apply (_root_.Opens.coversTop_iff _ _).2
  apply le_antisymm le_top
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxT x⟩

open Stacks.Thickenings in
omit [HasPushout i f] in
/-- If `V' ⟶ Y'` is locally of finite presentation, a quasi-coherent module on `V'` flat over `Y'`
is of finite presentation if and only if both components of its comparison triple, its
restrictions to `V` and to `U'`, are of finite presentation. -/
@[stacks 08KU "the finite presentation clause"]
theorem isFinitePresentation_iff_baseChangeTripleFunctor_obj (hi : IsThickening i)
    [IsAffineHom f] :
    letI := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
    ∀ (g : V' ⟶ pushout i f), LocallyOfFinitePresentation g →
      ∀ M : FlatQuasicoherentModule g,
        M.obj.IsFinitePresentation ↔
          ((baseChangeTripleFunctor i f hi g).obj M.obj).target.IsFinitePresentation ∧
            ((baseChangeTripleFunctor i f hi g).obj M.obj).ambient.IsFinitePresentation := by
  let := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
  intro g hg M
  refine ⟨fun hM ↦ ?_, fun hT ↦ isFinitePresentation_of_components i f g hi hg M hT.1 hT.2⟩
  let : M.obj.IsFinitePresentation := hM
  exact isFinitePresentation_baseChangeTripleFunctor_obj i f hi g M.obj

end Stacks.Pushout

end

module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationRestrict
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SubsingletonSpaceModuleEquivalence

/-!
# Sheaf-level graded algebras over a one-point base from their global sections

Let `g : S₁ ⟶ S₂` be an isomorphism of schemes, where the only opens of `S₂` are `⊥` and `⊤` (for
instance `S₂` the spectrum of an Artinian local ring), and let `A₂`, `A₁` be quasi-coherent graded
algebras on `S₂`, `S₁` in the sheaf-level form `SheafGradedAlgebra`. This file shows that a
bijective ring homomorphism `α : Γ(S₂, A₂) ⟶ Γ(S₁, A₁)` of the graded rings of global sections
which preserves the grading and is semilinear along `g^♯ : Γ(S₂, 𝒪) ⟶ Γ(S₁, 𝒪)` comes from a
homomorphism of sheaf-level graded algebras `γ : g^* A₂ ⟶ A₁` that is an isomorphism in every
degree, and that on the pullback of a homogeneous global section `x` of degree `n` the map `γ` is
the degree-`n` component of `α x`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.modulesHomOfTop`: on a scheme with at most one
  point, the morphism of `𝒪_X`-modules extending a linear map of global sections.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.globalDegreeMap` and `globalPieceMap`: the degree
  components of `α`, in `ℕ`- and in `ℤ`-indexed degrees.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.globalPushforwardUnitalHom`: the unital
  homomorphism `A₂ ⟶ g_* A₁` of sheaves of graded algebras extending `α`.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.pullbackSheafGradedAlgebraHom`: its adjoint
  transpose `g^* A₂ ⟶ A₁`, as a homomorphism of sheaf-level graded algebras.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.isIso_pullbackSheafGradedAlgebraHom_app`: along an
  isomorphism `g`, every component of `pullbackSheafGradedAlgebraHom` is an isomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.exists_sheafGradedAlgebraHom_isIso_of_sectionRing`:
  **the existence statement**, with the formula on global sections.

## Implementation notes

The hypothesis that every open of `S₂` is `⊥` or `⊤` is converted at once into
`Subsingleton S₂` (`subsingleton_of_forall_opens_eq_bot_or_eq_top`, which uses that a scheme is
`T₀`), because the identification of modules on a space with at most one point with their global
sections, `Stacks.Cohomology.SubsingletonSections.evaluationTop_full` and
`Stacks.Cohomology.SubsingletonSections.subsingleton_obj_of_ne_top`, is stated in that form. That
identification turns the degree components of `α`, read as linear maps into the global sections of
`g_* A₁`, into morphisms `A₂.piece n ⟶ g_* (A₁.piece n)`; multiplicativity and unitality have only
the open `⊤` to be checked on, since off `⊤` the target has zero sections. The transpose along
`g^* ⊣ g_*` is `Stacks.RingedSpace.transposeUnitalHom`, as in
`…ProjectiveDeformation.PolarizedFamily.AdmissibleDeformation.algebraPullbackSheafHom`;
it is `g^*` of an isomorphism followed by the counit of `g^* ⊣ g_*`, which is an isomorphism
because `g_*` is fully faithful along the open immersion `g`.

In negative degrees both pieces vanish (`SheafGradedAlgebra.negative_isZero`), and the degree
component is taken to be zero there.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjMapDomain Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

/-- A scheme whose only opens are `⊥` and `⊤` has at most one point. -/
theorem subsingleton_of_forall_opens_eq_bot_or_eq_top {X : Scheme.{u}}
    (h : ∀ U : X.Opens, U = ⊥ ∨ U = ⊤) : Subsingleton X := by
  refine ⟨fun x y => Inseparable.eq ?_⟩
  rw [inseparable_iff_forall_isOpen]
  intro s hs
  rcases h ⟨s, hs⟩ with h1 | h1
  · have : s = ∅ := congrArg (fun U : X.Opens => (U : Set X)) h1
    simp [this]
  · have : s = Set.univ := congrArg (fun U : X.Opens => (U : Set X)) h1
    simp [this]

section Modules

variable {X : Scheme.{u}} [Subsingleton X] {M N : X.Modules}

/-- A morphism of `𝒪_X`-modules on a scheme with at most one point, extending a linear map of
global sections. -/
def modulesHomOfTop (f : M.val.obj (op ⊤) ⟶ N.val.obj (op ⊤)) : M ⟶ N :=
  haveI : Subsingleton X.toRingedSpace.carrier := ‹Subsingleton X›
  ⟨(Stacks.Cohomology.SubsingletonSections.evaluationTop X.toRingedSpace).preimage f⟩

private instance : Subsingleton X.toRingedSpace.carrier := ‹Subsingleton X›

/-- `modulesHomOfTop f` is `f` on global sections. -/
theorem modulesHomOfTop_val_app_top (f : M.val.obj (op ⊤) ⟶ N.val.obj (op ⊤)) :
    (modulesHomOfTop f).val.app (op ⊤) = f :=
  Functor.map_preimage (Stacks.Cohomology.SubsingletonSections.evaluationTop X.toRingedSpace) f

/-- `modulesHomOfTop f` is an isomorphism as soon as `f` is: evaluation on `⊤` is fully faithful
on a space with at most one point, hence reflects isomorphisms. -/
theorem isIso_modulesHomOfTop (f : M.val.obj (op ⊤) ⟶ N.val.obj (op ⊤)) [IsIso f] :
    IsIso (modulesHomOfTop f) := by
  have h1 : IsIso ((Stacks.Cohomology.SubsingletonSections.evaluationTop X.toRingedSpace).map
      (modulesHomOfTop f).val) := by
    rw [show (Stacks.Cohomology.SubsingletonSections.evaluationTop X.toRingedSpace).map
      (modulesHomOfTop f).val = f from modulesHomOfTop_val_app_top f]
    exact ‹IsIso f›
  have h2 : IsIso ((Scheme.Modules.toPresheafOfModules X).map (modulesHomOfTop f)) :=
    (Functor.FullyFaithful.ofFullyFaithful
      (Stacks.Cohomology.SubsingletonSections.evaluationTop X.toRingedSpace)).isIso_of_isIso_map
      (modulesHomOfTop f).val
  exact (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).isIso_of_isIso_map _

/-- On a scheme with at most one point an `𝒪_X`-module has zero sections over a proper open. -/
theorem subsingleton_val_obj_of_ne_top (M : X.Modules) {U : X.Opens} (hU : U ≠ ⊤) :
    Subsingleton (M.val.obj (op U)) :=
  Stacks.Cohomology.SubsingletonSections.subsingleton_obj_of_ne_top X.toRingedSpace M.val hU

end Modules

section Degree

variable {S₁ S₂ : Scheme.{u}} {A₂ : SheafGradedAlgebra S₂} {A₁ : SheafGradedAlgebra S₁}
  (α : A₂.sectionRing ⊤ →+* A₁.sectionRing ⊤)

/-- The degree-`n` component of a ring homomorphism of graded rings of global sections, read on
homogeneous sections of degree `n`. -/
def globalDegreeMap (n : ℕ) : A₂.sectionPieces ⊤ n →+ A₁.sectionPieces ⊤ n where
  toFun x := α (DirectSum.of (A₂.sectionPieces ⊤) n x) n
  map_zero' := by rw [map_zero, map_zero]; rfl
  map_add' x y := by rw [map_add, map_add]; rfl

/-- The defining formula of `globalDegreeMap`. -/
theorem globalDegreeMap_apply (n : ℕ) (x : A₂.sectionPieces ⊤ n) :
    globalDegreeMap α n x = α (DirectSum.of (A₂.sectionPieces ⊤) n x) n := rfl

variable {α}
variable (hgr : ∀ (n : ℕ) (x : A₂.sectionRing ⊤), x ∈ A₂.grading ⊤ n → α x ∈ A₁.grading ⊤ n)

include hgr

/-- A grading-preserving homomorphism carries a homogeneous section to the homogeneous section of
the same degree given by its degree component. -/
theorem map_of_eq_of_globalDegreeMap (n : ℕ) (x : A₂.sectionPieces ⊤ n) :
    α (DirectSum.of (A₂.sectionPieces ⊤) n x) =
      DirectSum.of (A₁.sectionPieces ⊤) n (globalDegreeMap α n x) := by
  obtain ⟨y, hy⟩ := hgr n _ (A₂.of_mem_grading ⊤ x)
  rw [globalDegreeMap_apply, ← hy, DirectSum.of_eq_same]

/-- A grading-preserving homomorphism acts componentwise through its degree components. -/
theorem map_apply_eq_globalDegreeMap (w : A₂.sectionRing ⊤) (k : ℕ) :
    α w k = globalDegreeMap α k (w k) := by
  induction w using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
  | of m x =>
    rw [map_of_eq_of_globalDegreeMap hgr m x]
    rcases eq_or_ne m k with rfl | hmk
    · rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne m k _ hmk.symm, DirectSum.of_eq_of_ne m k _ hmk.symm, map_zero]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, map_add, hx, hy]

/-- The degree components of a bijective grading-preserving homomorphism are bijective. -/
theorem globalDegreeMap_bijective (hα : Function.Bijective α) (n : ℕ) :
    Function.Bijective (globalDegreeMap α n) := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have h := hα.1 ((map_of_eq_of_globalDegreeMap hgr n x).trans
      ((congrArg _ hxy).trans (map_of_eq_of_globalDegreeMap hgr n y).symm))
    exact DirectSum.of_injective n h
  · obtain ⟨w, hw⟩ := hα.2 (DirectSum.of (A₁.sectionPieces ⊤) n y)
    refine ⟨w n, ?_⟩
    rw [← map_apply_eq_globalDegreeMap hgr, hw, DirectSum.of_eq_same]

/-- The degree components are multiplicative. -/
theorem globalDegreeMap_mul (i j : ℕ) (x : A₂.sectionPieces ⊤ i) (y : A₂.sectionPieces ⊤ j) :
    globalDegreeMap α (i + j) ((A₂.mul (i : ℤ) (j : ℤ)).app ⊤ x y) =
      (A₁.mul (i : ℤ) (j : ℤ)).app ⊤ (globalDegreeMap α i x) (globalDegreeMap α j y) := by
  have h := congrArg α (DirectSum.of_mul_of (A := A₂.sectionPieces ⊤) x y)
  rw [map_mul, map_of_eq_of_globalDegreeMap hgr, map_of_eq_of_globalDegreeMap hgr,
    map_of_eq_of_globalDegreeMap hgr, DirectSum.of_mul_of] at h
  exact (DirectSum.of_injective (i + j) h).symm

/-- The degree-`0` component preserves the unit. -/
theorem globalDegreeMap_one : globalDegreeMap α 0 (A₂.one ⊤) = A₁.one ⊤ := by
  have h := map_one α
  rw [DirectSum.one_def, map_of_eq_of_globalDegreeMap hgr, DirectSum.one_def] at h
  exact DirectSum.of_injective 0 h

/-- The degree components are semilinear along a ring map of global functions, when `α` is. -/
theorem globalDegreeMap_smul (ρ : Γ(S₂, ⊤) →+* Γ(S₁, ⊤))
    (hsl : ∀ (r : Γ(S₂, ⊤)) (x : A₂.sectionRing ⊤),
      α (A₂.strHom ⊤ r * x) = A₁.strHom ⊤ (ρ r) * α x)
    (n : ℕ) (r : Γ(S₂, ⊤)) (x : A₂.sectionPieces ⊤ n) :
    globalDegreeMap α n (r • x) = ρ r • globalDegreeMap α n x := by
  have h := hsl r (DirectSum.of (A₂.sectionPieces ⊤) n x)
  rw [A₂.strHom_mul_of, map_of_eq_of_globalDegreeMap hgr, map_of_eq_of_globalDegreeMap hgr,
    A₁.strHom_mul_of] at h
  exact DirectSum.of_injective n h

end Degree

section Piece

variable {S₁ S₂ : Scheme.{u}} {A₂ : SheafGradedAlgebra S₂} {A₁ : SheafGradedAlgebra S₁}
  (α : A₂.sectionRing ⊤ →+* A₁.sectionRing ⊤)

/-- The map of global sections in each integer degree induced by a homomorphism of graded rings
of global sections: its degree component in nonnegative degrees, and zero in negative degrees,
where both pieces vanish. -/
def globalPieceMap : (n : ℤ) → Γ(A₂.piece n, ⊤) →+ Γ(A₁.piece n, ⊤)
  | (k : ℕ) => globalDegreeMap α k
  | Int.negSucc _ => 0

/-- In nonnegative degrees `globalPieceMap` is the degree component `globalDegreeMap`. -/
theorem globalPieceMap_natCast (k : ℕ) : globalPieceMap α (k : ℤ) = globalDegreeMap α k := rfl

/-- A global section of a negative piece vanishes. -/
theorem globalSection_eq_zero_of_neg {S : Scheme.{u}} (A : SheafGradedAlgebra S) (a : ℕ)
    (x : Γ(A.piece (Int.negSucc a), ⊤)) : x = 0 :=
  section_eq_zero_of_isZero (A.negative_isZero _ (Int.negSucc_lt_zero a)) ⊤ x

variable {α}
variable (hgr : ∀ (n : ℕ) (x : A₂.sectionRing ⊤), x ∈ A₂.grading ⊤ n → α x ∈ A₁.grading ⊤ n)

include hgr

/-- The maps of global sections are multiplicative. -/
theorem globalPieceMap_mul (i j : ℤ) (x : Γ(A₂.piece i, ⊤)) (y : Γ(A₂.piece j, ⊤)) :
    globalPieceMap α (i + j) ((A₂.mul i j).app ⊤ x y) =
      (A₁.mul i j).app ⊤ (globalPieceMap α i x) (globalPieceMap α j y) := by
  rcases i with a | a
  · rcases j with b | b
    · exact globalDegreeMap_mul hgr a b x y
    · obtain rfl := globalSection_eq_zero_of_neg A₂ b y
      simp only [map_zero]
  · obtain rfl := globalSection_eq_zero_of_neg A₂ a x
    simp only [map_zero, AddMonoidHom.zero_apply]

/-- The map of global sections in degree `0` preserves the unit. -/
theorem globalPieceMap_one : globalPieceMap α 0 (A₂.one ⊤) = A₁.one ⊤ :=
  globalDegreeMap_one hgr

/-- The maps of global sections are semilinear along a ring map of global functions. -/
theorem globalPieceMap_smul (ρ : Γ(S₂, ⊤) →+* Γ(S₁, ⊤))
    (hsl : ∀ (r : Γ(S₂, ⊤)) (x : A₂.sectionRing ⊤),
      α (A₂.strHom ⊤ r * x) = A₁.strHom ⊤ (ρ r) * α x)
    (n : ℤ) (r : Γ(S₂, ⊤)) (x : Γ(A₂.piece n, ⊤)) :
    globalPieceMap α n (r • x) = ρ r • globalPieceMap α n x := by
  rcases n with k | k
  · exact globalDegreeMap_smul hgr ρ hsl k r x
  · exact (smul_zero (ρ r)).symm

/-- The maps of global sections of a bijective grading-preserving homomorphism are bijective. -/
theorem globalPieceMap_bijective (hα : Function.Bijective α) (n : ℤ) :
    Function.Bijective (globalPieceMap α n) := by
  rcases n with k | k
  · exact globalDegreeMap_bijective hgr hα k
  · refine ⟨fun x y _ => ?_, fun y => ⟨0, ?_⟩⟩
    · rw [globalSection_eq_zero_of_neg A₂ k x, globalSection_eq_zero_of_neg A₂ k y]
    · rw [globalSection_eq_zero_of_neg A₁ k y]
      rfl

end Piece

section Hom

variable {S₁ S₂ : Scheme.{u}} (g : S₁ ⟶ S₂) {A₂ : SheafGradedAlgebra S₂}
  {A₁ : SheafGradedAlgebra S₁} {α : A₂.sectionRing ⊤ →+* A₁.sectionRing ⊤}
  (hgr : ∀ (n : ℕ) (x : A₂.sectionRing ⊤), x ∈ A₂.grading ⊤ n → α x ∈ A₁.grading ⊤ n)
  (hsl : ∀ (r : Γ(S₂, ⊤)) (x : A₂.sectionRing ⊤),
    α (A₂.strHom ⊤ r * x) = A₁.strHom ⊤ (g.appTop r) * α x)

include hgr hsl

/-- The map of global sections in degree `n`, as a linear map into the global sections of the
direct image of the degree-`n` piece. -/
def globalPieceHom (n : ℤ) :
    (A₂.piece n).val.obj (op ⊤) ⟶
      ((Scheme.Modules.pushforward g).obj (A₁.piece n)).val.obj (op ⊤) :=
  ModuleCat.ofHom (Y := ((Scheme.Modules.pushforward g).obj (A₁.piece n)).val.obj (op ⊤))
    { toFun := globalPieceMap α n
      map_add' := map_add _
      map_smul' := globalPieceMap_smul hgr g.appTop.hom hsl n }

/-- The underlying function of `globalPieceHom` is `globalPieceMap`. -/
theorem globalPieceHom_apply (n : ℤ) (x : Γ(A₂.piece n, ⊤)) :
    globalPieceHom g hgr hsl n x = globalPieceMap α n x := rfl

variable [Subsingleton S₂]

/-- The morphism `A₂.piece n ⟶ g_* (A₁.piece n)` on a base with at most one point, extending the
map of global sections. -/
def pushforwardPieceHom (n : ℤ) : A₂.piece n ⟶ (Scheme.Modules.pushforward g).obj (A₁.piece n) :=
  modulesHomOfTop (globalPieceHom g hgr hsl n)

/-- On global sections `pushforwardPieceHom` is `globalPieceMap`. -/
theorem pushforwardPieceHom_val_app_top (n : ℤ) (x : Γ(A₂.piece n, ⊤)) :
    (pushforwardPieceHom g hgr hsl n).val.app (op ⊤) x = globalPieceMap α n x := by
  rw [pushforwardPieceHom, modulesHomOfTop_val_app_top]
  rfl

/-- `pushforwardPieceHom` is an isomorphism when `α` is bijective: it is bijective on global
sections, and a morphism of modules on a scheme with at most one point is determined there. -/
theorem isIso_pushforwardPieceHom (hα : Function.Bijective α) (n : ℤ) :
    IsIso (pushforwardPieceHom g hgr hsl n) := by
  have : IsIso (globalPieceHom g hgr hsl n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (globalPieceMap_bijective hgr hα n)
  exact isIso_modulesHomOfTop _

/-- The morphisms `A₂.piece n ⟶ g_* (A₁.piece n)` form a unital homomorphism of sheaves of graded
algebras `A₂ ⟶ g_* A₁`. Over `⊤` this is the multiplicativity of `α`; over any other open the
target has zero sections. -/
def globalPushforwardUnitalHom :
    SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₂)
      (Stacks.RingedSpace.pushforwardAlgebra (ringedSpaceHom g) (situationAlgebra A₁)) where
  app n := pushforwardPieceHom g hgr hsl n
  map_mul i j U x y := by
    obtain ⟨U⟩ := U
    by_cases hU : U = ⊤
    · subst hU
      refine (pushforwardPieceHom_val_app_top g hgr hsl (i + j) _).trans ?_
      refine (globalPieceMap_mul hgr i j x y).trans ?_
      exact congrArg₂ (fun a b => (A₁.mul i j).app ⊤ a b)
        (pushforwardPieceHom_val_app_top g hgr hsl i x).symm
        (pushforwardPieceHom_val_app_top g hgr hsl j y).symm
    · exact (subsingleton_val_obj_of_ne_top
        ((Scheme.Modules.pushforward g).obj (A₁.piece (i + j))) hU).elim _ _
  map_one U := by
    obtain ⟨U⟩ := U
    by_cases hU : U = ⊤
    · subst hU
      exact (pushforwardPieceHom_val_app_top g hgr hsl 0 _).trans (globalPieceMap_one hgr)
    · exact (subsingleton_val_obj_of_ne_top
        ((Scheme.Modules.pushforward g).obj (A₁.piece 0)) hU).elim _ _

/-- **The homomorphism of sheaf-level graded algebras `g^* A₂ ⟶ A₁` attached to a homomorphism
of graded rings of global sections**, on a base with at most one point: the adjoint transpose of
`globalPushforwardUnitalHom` under `g^* ⊣ g_*`. -/
def pullbackSheafGradedAlgebraHom : SheafGradedAlgebraHom (A₂.pullback g) A₁ where
  app n := (Stacks.RingedSpace.transposeUnitalHom (ringedSpaceHom g)
    (globalPushforwardUnitalHom g hgr hsl)).app n
  app_mul i j U a b := (Stacks.RingedSpace.transposeUnitalHom (ringedSpaceHom g)
    (globalPushforwardUnitalHom g hgr hsl)).map_mul i j (op U) a b
  app_one U := (Stacks.RingedSpace.transposeUnitalHom (ringedSpaceHom g)
    (globalPushforwardUnitalHom g hgr hsl)).map_one (op U)

/-- The degree-`n` component of `pullbackSheafGradedAlgebraHom` is the adjoint transpose of
`pushforwardPieceHom`. -/
theorem pullbackSheafGradedAlgebraHom_app (n : ℤ) :
    (pullbackSheafGradedAlgebraHom g hgr hsl).app n =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
        (pushforwardPieceHom g hgr hsl n) := rfl

/-- **On global sections**, `pullbackSheafGradedAlgebraHom` sends the pullback of a homogeneous
global section `x` of `A₂` to the degree-`n` component of `α x`. -/
theorem pullbackSheafGradedAlgebraHom_app_unit (n : ℕ) (x : A₂.sectionPieces ⊤ n) :
    ((pullbackSheafGradedAlgebraHom g hgr hsl).app (n : ℤ)).val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (A₂.piece n)).val.app
          (op ⊤) x) =
      α (DirectSum.of (A₂.sectionPieces ⊤) n x) n :=
  (Stacks.RingedSpace.transposeApp_pullbackUnit (ringedSpaceHom g)
    (globalPushforwardUnitalHom g hgr hsl) (n : ℤ) ⊤ x).trans
    (pushforwardPieceHom_val_app_top g hgr hsl (n : ℤ) x)

/-- **Along an isomorphism `g`, every component of `pullbackSheafGradedAlgebraHom` is an
isomorphism** when `α` is bijective: it is `g^*` of the isomorphism `pushforwardPieceHom`
followed by the counit of `g^* ⊣ g_*`, which is invertible because `g_*` is fully faithful along
the open immersion `g`. -/
theorem isIso_pullbackSheafGradedAlgebraHom_app [IsIso g] (hα : Function.Bijective α) (n : ℤ) :
    IsIso ((pullbackSheafGradedAlgebraHom g hgr hsl).app n) := by
  have : IsIso (Scheme.Modules.pullbackPushforwardAdjunction g).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  have h1 : IsIso ((Scheme.Modules.pullback g).map (pushforwardPieceHom g hgr hsl n)) :=
    have := isIso_pushforwardPieceHom g hgr hsl hα n
    Functor.map_isIso (Scheme.Modules.pullback g) (pushforwardPieceHom g hgr hsl n)
  have h2 : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app (A₁.piece n)) :=
    NatIso.isIso_app_of_isIso _ _
  rw [pullbackSheafGradedAlgebraHom_app, Adjunction.homEquiv_counit]
  exact IsIso.comp_isIso' h1 h2

end Hom

/-- **A bijective graded semilinear isomorphism of the rings of global sections comes from an
isomorphism of sheaf-level graded algebras**, on a base whose only opens are `⊥` and `⊤` and along
an isomorphism `g` of bases: there is a homomorphism `γ : g^* A₂ ⟶ A₁` of sheaf-level graded
algebras, invertible in every degree, which on the pullback of a homogeneous global section `x` of
`A₂` of degree `n` is the degree-`n` component of `α x`. -/
theorem exists_sheafGradedAlgebraHom_isIso_of_sectionRing {S₁ S₂ : Scheme.{u}} (g : S₁ ⟶ S₂)
    [IsIso g] (h₂ : ∀ U : S₂.Opens, U = ⊥ ∨ U = ⊤) {A₂ : SheafGradedAlgebra S₂}
    {A₁ : SheafGradedAlgebra S₁} (α : A₂.sectionRing ⊤ →+* A₁.sectionRing ⊤)
    (hα : Function.Bijective α)
    (hgr : ∀ (n : ℕ) (x : A₂.sectionRing ⊤), x ∈ A₂.grading ⊤ n → α x ∈ A₁.grading ⊤ n)
    (hsl : ∀ (r : Γ(S₂, ⊤)) (x : A₂.sectionRing ⊤),
      α (A₂.strHom ⊤ r * x) = A₁.strHom ⊤ (g.appTop r) * α x) :
    ∃ γ : SheafGradedAlgebraHom (A₂.pullback g) A₁, (∀ n : ℤ, IsIso (γ.app n)) ∧
      ∀ (n : ℕ) (x : A₂.sectionPieces ⊤ n),
        (γ.app (n : ℤ)).val.app (op ⊤)
            (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (A₂.piece n)).val.app
              (op ⊤) x) =
          α (DirectSum.of (A₂.sectionPieces ⊤) n x) n := by
  have := subsingleton_of_forall_opens_eq_bot_or_eq_top h₂
  exact ⟨pullbackSheafGradedAlgebraHom g hgr hsl,
    isIso_pullbackSheafGradedAlgebraHom_app g hgr hsl hα,
    pullbackSheafGradedAlgebraHom_app_unit g hgr hsl⟩

end Stacks.AlgebraicGeometry.RelativeProjBridge

end

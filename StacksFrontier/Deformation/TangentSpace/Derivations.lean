module

public import Mathlib.Algebra.Module.TransferInstance
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.TangentSpace.Functor
public import StacksFrontier.Deformation.TangentSpace.SquareZero

/-!
# The tangent space of a prorepresentable functor is a space of derivations (Stacks 06IC)

Let `S` be a Noetherian complete local `Λ`-algebra with residue field `k`. The tangent
space of the functor prorepresented by `S` — that is, the value of `restrictedCoyoneda S`
on the dual numbers `k[ε]` — is canonically the `k`-vector space of `Λ`-derivations
`S → k`, where `S` acts on `k` through its augmentation.

A morphism `S ⟶ k[ε]` of complete local algebras is exactly an augmentation-compatible
`Λ`-algebra map, i.e. a square-zero point of `S`, and Tag 06IC's square-zero-point
description identifies those with derivations. The only work here is bookkeeping: the dual
numbers of Tag 06IB are modelled on `ULift k` so that their carrier universe can contain
both the carrier of `S` and the residue field independently, so the derivation module has
to be transported along `ULift.moduleEquiv`, and the two `Λ`- and `S`-module structures on
`ULift k` coming from `Module.compHom` have to be identified with the ones `ULift.module'`
provides.

The first part of the file uses the resulting bijection to *transport* the additive and
`k`-linear structures of the derivations onto `tangentSpaceArtinian Λ k (restrictedCoyoneda S)`;
for that transported structure the bijection is linear by construction, so it says nothing
about the canonical structure.

The second part proves the actual claim of Stacks 06IC. The canonical `k`-vector space
structure on `F(k[V])` is the one of Lemma 06IA (`tangentSpaceModuleStructure`), which exists
because `F` takes `k[0] = k` to a point and `k[M × N]` to products; for `F` prorepresented
by `S` these hypotheses hold (`prorepresented_tangentSpaceFunctorConditions`). The
identifications `F(k[V]) = Der_Λ(S, V)` are natural in `V`
(`prorepresentedSquareZeroDerivationsIso`), and `V ↦ Der_Λ(S, V)` is a `k`-linear functor, so
by Lemma 06I7 (`fgModuleCat_linearFunctorLift_natTrans`) and the uniqueness of linear lifts
(Lemma 06I6) the bijections are `k`-linear for the canonical structures. Taking `V = k` gives
`TF = Der_Λ(S, k)` as vector spaces, and then `dim_k TF < ∞` by Lemma 06SC.

The Over model of Lemma 06IA uses the carrier universe of `k` for the square-zero extensions,
so the second part is stated for `S : CompleteLocalAlgCat.{u, w, w} Λ k`.

## Main results

* `Deformation.dualNumberDerivationsEquiv`: the underlying bijection.
* `Deformation.tangentSpaceDerivationsLinearEquiv`: that bijection, as a linear equivalence
  for the transported structure.
* `Deformation.tangentSpaceDerivationsLinearEquiv_apply` and
  `Deformation.tangentSpaceDerivationsLinearEquiv_precomp`: its value on a tangent vector,
  and its compatibility with precomposition in the representing algebra.
* `Deformation.tangentSpace_finiteDimensional`: finite-dimensionality for the transported
  structure, when `Λ → k` is finite.
* `Deformation.prorepresented_tangentSpaceFunctorConditions`: **Stacks 06IC**, the
  prorepresented functor satisfies the hypotheses of Lemma 06IA.
* `Deformation.tangentSpaceModuleStructureDerivationsLinearEquiv`: **Stacks 06IC**,
  `F(k[V]) = Der_Λ(S, V)` as `k`-vector spaces, for the canonical structure of Lemma 06IA.
* `Deformation.tangentSpaceModuleStructureRankOneDerivationsLinearEquiv`: **Stacks 06IC**,
  `TF = Der_Λ(S, k)` as `k`-vector spaces, for the canonical structure of 06IA/06IB.
* `Deformation.tangentSpaceModuleStructure_prorepresented_finiteDimensional`:
  **Stacks 06IC**, `dim_k TF < ∞` for the canonical structure, when `Λ → k` is finite (the
  chapter's standing assumption).
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The tangent space of the functor prorepresented by `S` is in bijection with the
`Λ`-derivations from `S` to its residue field. -/
@[sga "3 VIIA 1.2.1" "special case"]
noncomputable def dualNumberDerivationsEquiv
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
    tangentSpaceArtinian Λ k (restrictedCoyoneda S) ≃ Derivation Λ S k := by
  letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
  letI : IsScalarTower Λ S k :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      rw [show algebraMap Λ S r • x = residueHom S (algebraMap Λ S r) * x from rfl,
        (residueHom S).commutes]
      exact (Algebra.smul_def r x).symm
  let A := artinianToComplete.obj (artinianDualNumbers Λ k)
  let mΛ : Module Λ (ULift.{v} k) := Module.compHom (ULift.{v} k) (algebraMap Λ k)
  let mS : Module S (ULift.{v} k) :=
    Module.compHom (ULift.{v} k) (residueHom S).toRingHom
  let nΛ : Module Λ (ULift.{v} k) := ULift.module'
  let nS : Module S (ULift.{v} k) := ULift.module'
  have hΛmod : mΛ = nΛ :=
    Module.ext' _ _ fun r x ↦ ULift.ext (Algebra.smul_def r x.down).symm
  have hSmod : mS = nS := Module.ext' _ _ fun _ _ ↦ rfl
  have htype : Derivations S (ULift.{v} k) = Derivation Λ S (ULift.{v} k) :=
    congrArg₂ (@Derivation Λ S (ULift.{v} k) _ _ _ _) hSmod hΛmod
  exact (squareZeroPointsDerivationsEquivHom S A (ULift.{v} k) (RingEquiv.refl _)
      (fun _ ↦ rfl) (fun _ ↦ rfl)).trans
    ((Equiv.cast htype).trans (ULift.moduleEquiv : ULift.{v} k ≃ₗ[S] k).compDer.toEquiv)

/-- The additive structure on the tangent space of the functor represented by `S`, transported
from the derivations along `dualNumberDerivationsEquiv`. Its agreement with the canonical
structure of Stacks 06IA is `tangentSpaceModuleStructureRankOneDerivationsLinearEquiv`. -/
noncomputable instance tangentSpaceAddCommGroup
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    AddCommGroup (tangentSpaceArtinian Λ k (restrictedCoyoneda S)) :=
  (dualNumberDerivationsEquiv S).addCommGroup

/-- The `k`-module structure on the tangent space of the functor represented by `S`, transported
from the derivations along `dualNumberDerivationsEquiv`. Its agreement with the canonical
structure of Stacks 06IA is `tangentSpaceModuleStructureRankOneDerivationsLinearEquiv`. -/
noncomputable instance tangentSpaceModule
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    Module k (tangentSpaceArtinian Λ k (restrictedCoyoneda S)) :=
  ((dualNumberDerivationsEquiv S).addEquiv).module k

/-- The bijection `dualNumberDerivationsEquiv` as a linear equivalence, for the structures
`tangentSpaceAddCommGroup` and `tangentSpaceModule` transported along it; it is linear by
construction. The statement of Stacks 06IC, linearity for the canonical structure of
Lemma 06IA, is `tangentSpaceModuleStructureRankOneDerivationsLinearEquiv`. -/
noncomputable def tangentSpaceDerivationsLinearEquiv
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
    tangentSpaceArtinian Λ k (restrictedCoyoneda S) ≃ₗ[k] Derivation Λ S k :=
  letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
  (dualNumberDerivationsEquiv S).addEquiv.linearEquiv k

/-- Transporting a derivation along equalities of its two module structures does not
change its values. -/
private theorem cast_derivation_module_apply
    {R A M : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
    [Algebra R A] (mA nA : Module A M) (mR nR : Module R M)
    (hA : mA = nA) (hR : mR = nR)
    (D : @Derivation R A M _ _ _ _ mA mR) (a : A) :
    (cast (by rw [hA, hR] :
      @Derivation R A M _ _ _ _ mA mR = @Derivation R A M _ _ _ _ nA nR) D) a = D a := by
  subst nA
  subst nR
  rfl

/-- A tangent vector corresponds to the downlifted square-zero component: the bijection is
`f ↦ f - q`. -/
@[stacks 06IC "the bijection TF = Der_Λ(S, k), f ↦ f - q"]
theorem tangentSpaceDerivationsLinearEquiv_apply
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (f : tangentSpaceArtinian Λ k (restrictedCoyoneda S)) (s : S) :
    letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
    tangentSpaceDerivationsLinearEquiv S f s = (f.hom s).snd.down := by
  let : Algebra S k := (residueHom S).toRingHom.toAlgebra
  let : IsScalarTower Λ S k :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      rw [show algebraMap Λ S r • x = residueHom S (algebraMap Λ S r) * x from rfl,
        (residueHom S).commutes]
      exact (Algebra.smul_def r x).symm
  let A := artinianToComplete.obj (artinianDualNumbers Λ k)
  let mΛ : Module Λ (ULift.{v} k) := Module.compHom (ULift.{v} k) (algebraMap Λ k)
  let mS : Module S (ULift.{v} k) :=
    Module.compHom (ULift.{v} k) (residueHom S).toRingHom
  let nΛ : Module Λ (ULift.{v} k) := ULift.module'
  let nS : Module S (ULift.{v} k) := ULift.module'
  have hΛmod : mΛ = nΛ :=
    Module.ext' _ _ fun r x ↦ ULift.ext (Algebra.smul_def r x.down).symm
  have hSmod : mS = nS := Module.ext' _ _ fun _ _ ↦ rfl
  have htype : Derivations S (ULift.{v} k) = Derivation Λ S (ULift.{v} k) :=
    congrArg₂ (@Derivation Λ S (ULift.{v} k) _ _ _ _) hSmod hΛmod
  let E := squareZeroPointsDerivationsEquivHom S A (ULift.{v} k) (RingEquiv.refl _)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  change ((cast htype (E f)) s).down = _
  rw [cast_derivation_module_apply mS nS mΛ nΛ hSmod hΛmod (E f) s]
  exact congrArg ULift.down
    (squareZeroPointsDerivationsEquivHom_apply S A (ULift.{v} k) (RingEquiv.refl _)
      (fun _ ↦ rfl) (fun _ ↦ rfl) f s)

/-- The identification commutes with precomposition by morphisms of representing
algebras. -/
@[stacks 06IC "the bijection TF = Der_Λ(S, k), f ↦ f - q"]
theorem tangentSpaceDerivationsLinearEquiv_precomp
    (T S : CompleteLocalAlgCat.{u, max v w, w} Λ k) (g : T ⟶ S)
    (f : tangentSpaceArtinian Λ k (restrictedCoyoneda S)) (t : T) :
    tangentSpaceDerivationsLinearEquiv T (g ≫ f) t =
      tangentSpaceDerivationsLinearEquiv S f (g.hom t) := by
  rw [tangentSpaceDerivationsLinearEquiv_apply, tangentSpaceDerivationsLinearEquiv_apply,
    CompleteLocalAlgCat.comp_hom]
  rfl

/-- The tangent space of a prorepresentable functor is finite-dimensional for the transported
structure `tangentSpaceModule`, under the chapter's standing assumption that `Λ → k` is
finite. The statement of Stacks 06IC for the canonical structure of Lemma 06IA is
`tangentSpaceModuleStructure_prorepresented_finiteDimensional`. -/
@[sga "7 VI 1.11" "(ii), special case"]
theorem tangentSpace_finiteDimensional [Module.Finite Λ k]
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    FiniteDimensional k (tangentSpaceArtinian Λ k (restrictedCoyoneda S)) := by
  let := (residueHom S).toRingHom.toAlgebra
  have : Module.Finite k (Derivation Λ S k) := derivation_module_finite S.residueEquiv
  exact Module.Finite.equiv (tangentSpaceDerivationsLinearEquiv S).symm

/-! ### Comparison with the canonical structure of Tag 06IA -/

section Canonical

open CategoryTheory CategoryTheory.Limits

universe uR vM uM

/-- Two linear lifts of product-preserving functors carry every natural transformation of the
underlying functors to linear maps (the content of Tag 06I7, phrased for arbitrary lifts). -/
private theorem exists_linearMap_of_linearFunctorLift
    (R : Type uR) [CommRing R] (F G : FGModuleCat.{vM} R ⥤ Type uM)
    [PreservesFiniteProducts F] [Unique (F.obj (FGModuleCat.of R PUnit))]
    [PreservesFiniteProducts G] [Unique (G.obj (FGModuleCat.of R PUnit))]
    (A : LinearFunctorLift R F) (B : LinearFunctorLift R G) (t : F ⟶ G)
    (X : FGModuleCat.{vM} R) :
    ∃ l : A.functor.obj X →ₗ[R] B.functor.obj X, ∀ x : A.functor.obj X,
      cast (congrArg (fun H : FGModuleCat.{vM} R ⥤ Type uM ↦ H.obj X) B.forget_comp) (l x) =
        t.app X
          (cast (congrArg (fun H : FGModuleCat.{vM} R ⥤ Type uM ↦ H.obj X) A.forget_comp) x) := by
  let uF : Unique (LinearFunctorLift R F) :=
    Classical.choice (fgModuleCat_linearFunctorLift_unique R F)
  let uG : Unique (LinearFunctorLift R G) :=
    Classical.choice (fgModuleCat_linearFunctorLift_unique R G)
  obtain rfl : A = fgModuleCatLinearFunctorLift R F := Subsingleton.elim _ _
  obtain rfl : B = fgModuleCatLinearFunctorLift R G := Subsingleton.elim _ _
  obtain ⟨τ, hτ, -⟩ := fgModuleCat_linearFunctorLift_natTrans R F G t
  refine ⟨(τ.app X).hom, fun x ↦ ?_⟩
  have hx := congrFun (congrArg (fun η ↦ η.app X) hτ) x
  change τ.app X x =
    (eqToHom (fgModuleCatLinearFunctorLift R G).forget_comp.symm).app X
      (t.app X ((eqToHom (fgModuleCatLinearFunctorLift R F).forget_comp).app X x)) at hx
  rw [eqToHom_app_apply_cast (fgModuleCatLinearFunctorLift R F).forget_comp X x,
    eqToHom_app_apply_cast (fgModuleCatLinearFunctorLift R G).forget_comp.symm X] at hx
  change cast _ (τ.app X x) = _
  rw [hx, cast_cast, cast_eq]

variable (S : CompleteLocalAlgCat.{u, w, w} Λ k)

local instance derivationsBaseModule (V : FGModuleCat.{w} k) : Module Λ V :=
  Module.compHom V (algebraMap Λ k)

local instance derivationsBaseScalarTower (V : FGModuleCat.{w} k) : IsScalarTower Λ k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

local instance derivationsBaseSMulCommClass (V : FGModuleCat.{w} k) : SMulCommClass Λ k V :=
  ⟨fun r c v ↦ smul_comm (algebraMap Λ k r) c v⟩

local instance derivationsOppositeModule (V : FGModuleCat.{w} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance derivationsIsCentralScalar (V : FGModuleCat.{w} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

local instance derivationsOppositeScalarTower (V : FGModuleCat.{w} k) :
    IsScalarTower Λ kᵐᵒᵖ V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

noncomputable local instance derivationsResidueModule (V : FGModuleCat.{w} k) : Module S V :=
  Module.compHom V (residueHom S).toRingHom

local instance derivationsResidueScalarTower (V : FGModuleCat.{w} k) : IsScalarTower Λ S V :=
  IsScalarTower.of_algebraMap_smul fun r v ↦ by
    change residueHom S (algebraMap Λ S r) • v = algebraMap Λ k r • v
    rw [(residueHom S).commutes]

local instance derivationsResidueSMulCommClass (V : FGModuleCat.{w} k) : SMulCommClass k S V :=
  ⟨fun c s v ↦ smul_comm c (residueHom S s) v⟩

/-- A `k`-linear map of vector spaces, regarded as `S`-linear through the residue map. -/
noncomputable def residueLinearMap {V W : FGModuleCat.{w} k} (f : V ⟶ W) : V →ₗ[S] W where
  toFun := f.hom.hom
  map_add' := f.hom.hom.map_add
  map_smul' s v := f.hom.hom.map_smul (residueHom S s) v

/-- The functor `V ↦ Der_Λ(S, V)` from finite-dimensional vector spaces to vector spaces. -/
noncomputable def derivationsFunctor : FGModuleCat.{w} k ⥤ ModuleCat.{w} k where
  obj V := ModuleCat.of k (Derivation Λ S V)
  map {V W} f := ModuleCat.ofHom
    { toFun := fun D ↦ (residueLinearMap S f).compDer D
      map_add' := fun D E ↦ by ext; simp
      map_smul' := fun c D ↦ by
        ext s
        exact f.hom.hom.map_smul c (D s) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Postcomposition of derivations is additive in the linear map. -/
instance derivationsFunctor_additive : (derivationsFunctor S).Additive where
  map_add := rfl

/-- Postcomposition of derivations is `k`-linear in the linear map. -/
instance derivationsFunctor_linear : (derivationsFunctor S).Linear k where
  map_smul _ _ := rfl

/-- `V ↦ F(k[V])` for the functor `F` prorepresented by `S`, through the Over model of the
square-zero extensions used by Tag 06IA. -/
noncomputable abbrev prorepresentedSquareZeroFunctor : FGModuleCat.{w} k ⥤ Type w :=
  tangentSpaceSetFunctor Λ k (artinianLocalOver Λ k)
    (squareZeroExtension_mem_artinianLocalOver Λ k)
    (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)

/-- The identification `F(k[V]) = Der_Λ(S, V)`, `f ↦ f - q`. -/
noncomputable def prorepresentedSquareZeroDerivationsEquiv (V : FGModuleCat.{w} k) :
    (prorepresentedSquareZeroFunctor S).obj V ≃ Derivation Λ S V :=
  squareZeroPointsDerivationsEquivHom S
    (artinianToComplete.obj ((squareZeroExtensionArtinian Λ k).obj V)) V
    (RingEquiv.refl _) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The identification `F(k[V]) = Der_Λ(S, V)` commutes with the maps induced by linear maps
`V → W`. -/
theorem prorepresentedSquareZeroDerivationsEquiv_map {V W : FGModuleCat.{w} k} (f : V ⟶ W)
    (x : (prorepresentedSquareZeroFunctor S).obj V) (s : S) :
    prorepresentedSquareZeroDerivationsEquiv S W ((prorepresentedSquareZeroFunctor S).map f x) s =
      f.hom.hom (prorepresentedSquareZeroDerivationsEquiv S V x s) := by
  exact TrivSqZeroExt.snd_map f.hom.hom (x.hom s)

/-- The identification sends `f` to its square-zero component. -/
theorem prorepresentedSquareZeroDerivationsEquiv_apply (V : FGModuleCat.{w} k)
    (f : (prorepresentedSquareZeroFunctor S).obj V) (s : S) :
    prorepresentedSquareZeroDerivationsEquiv S V f s = (f.hom s).snd :=
  rfl

/-- The identification `F(k[V]) = Der_Λ(S, V)` is natural in `V`. -/
noncomputable def prorepresentedSquareZeroDerivationsIso :
    prorepresentedSquareZeroFunctor S ≅ derivationsFunctor S ⋙ forget (ModuleCat.{w} k) :=
  NatIso.ofComponents (fun V ↦ (prorepresentedSquareZeroDerivationsEquiv S V).toIso)
    (fun {V W} f ↦ by
      ext x
      apply Derivation.ext
      intro s
      exact prorepresentedSquareZeroDerivationsEquiv_map S f x s)

/-- The pairing `Der_Λ(S, M) × Der_Λ(S, N) → Der_Λ(S, M × N)`. -/
noncomputable def derivationPair {M N : FGModuleCat.{w} k} (D₁ : Derivation Λ S M)
    (D₂ : Derivation Λ S N) : Derivation Λ S (prodFGModule k M N) where
  toFun s := (D₁ s, D₂ s)
  map_add' a b := Prod.ext (D₁.map_add a b) (D₂.map_add a b)
  map_smul' r a := Prod.ext (D₁.map_smul r a) (D₂.map_smul r a)
  map_one_eq_zero' := Prod.ext D₁.map_one_eq_zero D₂.map_one_eq_zero
  leibniz' a b := Prod.ext (D₁.leibniz a b) (D₂.leibniz a b)

/-- **Stacks Project, Tag 06IC.** The functor prorepresented by `S` satisfies the hypotheses
of Lemma 06IA: its value on `k[0] = k` is a singleton and it takes `k[M × N]` to the product
of its values on `k[M]` and `k[N]`. -/
@[stacks 06IC "the prorepresented functor satisfies the hypotheses of Lemma 06IA"]
theorem prorepresented_tangentSpaceFunctorConditions :
    TangentSpaceFunctorConditions Λ k (artinianLocalOver Λ k)
      (squareZeroExtension_mem_artinianLocalOver Λ k)
      (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S) where
  zero_nonempty := ⟨(prorepresentedSquareZeroDerivationsEquiv S _).symm 0⟩
  zero_subsingleton := ⟨fun _ _ ↦ (prorepresentedSquareZeroDerivationsEquiv S _).injective
    (Derivation.ext fun _ ↦ Subsingleton.elim _ _)⟩
  prod_bijective M N := by
    let φ := prorepresentedSquareZeroDerivationsEquiv S
    refine ⟨fun x y h ↦ (φ _).injective (Derivation.ext fun s ↦ Prod.ext ?_ ?_), fun p ↦ ?_⟩
    · have h₁ := congrArg (fun q ↦ φ M q.1 s) h
      simp only [φ, prorepresentedSquareZeroDerivationsEquiv_map] at h₁
      exact h₁
    · have h₂ := congrArg (fun q ↦ φ N q.2 s) h
      simp only [φ, prorepresentedSquareZeroDerivationsEquiv_map] at h₂
      exact h₂
    · refine ⟨(φ _).symm (derivationPair S (φ M p.1) (φ N p.2)), Prod.ext ?_ ?_⟩
      · apply (φ M).injective
        ext s
        rw [prorepresentedSquareZeroDerivationsEquiv_map, Equiv.apply_symm_apply]
        rfl
      · apply (φ N).injective
        ext s
        rw [prorepresentedSquareZeroDerivationsEquiv_map, Equiv.apply_symm_apply]
        rfl

/-- The underlying set of the canonical (Tag 06IA) module `F(k[V])` is `F(k[V])`. -/
theorem tangentSpaceModuleStructure_prorepresented_carrier (V : FGModuleCat.{w} k) :
    ((tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
      (squareZeroExtension_mem_artinianLocalOver Λ k)
      (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
      (prorepresented_tangentSpaceFunctorConditions S)).functor.obj V : Type w) =
      (prorepresentedSquareZeroFunctor S).obj V :=
  congrArg (fun H : FGModuleCat.{w} k ⥤ Type w ↦ H.obj V)
    (tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
      (squareZeroExtension_mem_artinianLocalOver Λ k)
      (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
      (prorepresented_tangentSpaceFunctorConditions S)).forget_comp

/-- The canonical bijection `F(k[V]) → Der_Λ(S, V)` is additive and `k`-linear for the module
structure of Tag 06IA. -/
private theorem exists_linearMap_tangentSpaceModuleStructure_prorepresented
    (V : FGModuleCat.{w} k) :
    ∃ l : (tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
        (squareZeroExtension_mem_artinianLocalOver Λ k)
        (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
        (prorepresented_tangentSpaceFunctorConditions S)).functor.obj V →ₗ[k]
          Derivation Λ S V,
      ∀ x, l x = prorepresentedSquareZeroDerivationsEquiv S V
        (cast (tangentSpaceModuleStructure_prorepresented_carrier S V) x) := by
  let LF := tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
    (squareZeroExtension_mem_artinianLocalOver Λ k)
    (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
    (prorepresented_tangentSpaceFunctorConditions S)
  let φ := prorepresentedSquareZeroDerivationsEquiv S
  have : PreservesFiniteProducts LF.functor :=
    Functor.preservesFiniteProductsOfAdditive LF.functor
  have : PreservesFiniteProducts (prorepresentedSquareZeroFunctor S) := by
    have h : PreservesFiniteProducts (LF.functor ⋙ forget (ModuleCat.{w} k)) := inferInstance
    rw [LF.forget_comp] at h
    exact h
  have : PreservesFiniteProducts (derivationsFunctor S) :=
    Functor.preservesFiniteProductsOfAdditive (derivationsFunctor S)
  have : PreservesFiniteProducts (derivationsFunctor S ⋙ forget (ModuleCat.{w} k)) :=
    inferInstance
  let : Unique ((prorepresentedSquareZeroFunctor S).obj (FGModuleCat.of k PUnit)) :=
    { default := (φ _).symm 0
      uniq := fun _ ↦ (φ _).injective (Derivation.ext fun _ ↦ Subsingleton.elim _ _) }
  let : Unique ((derivationsFunctor S ⋙ forget (ModuleCat.{w} k)).obj (FGModuleCat.of k PUnit)) :=
    { default := (0 : Derivation Λ S (FGModuleCat.of k PUnit.{w + 1}))
      uniq := fun _ ↦ Derivation.ext fun _ ↦ Subsingleton.elim _ _ }
  obtain ⟨l, hl⟩ := exists_linearMap_of_linearFunctorLift k _ _ LF
    ⟨derivationsFunctor S, rfl⟩ (prorepresentedSquareZeroDerivationsIso S).hom V
  exact ⟨l, fun x ↦ (cast_eq _ _).symm.trans (hl x)⟩

/-- **Stacks Project, Tag 06IC.** For the functor `F` prorepresented by `S` and a
finite-dimensional `k`-vector space `V`, the bijection `F(k[V]) = Der_Λ(S, V)`,
`f ↦ f - q`, is `k`-linear for the canonical module structure on `F(k[V])` of Lemma 06IA
(the one coming from `F` preserving finite products), so it is a `k`-linear equivalence. -/
@[stacks 06IC "F(k[V]) = Der_Λ(S, V) as vector spaces, for the canonical structure of 06IA"]
noncomputable def tangentSpaceModuleStructureDerivationsLinearEquiv (V : FGModuleCat.{w} k) :
    (tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
      (squareZeroExtension_mem_artinianLocalOver Λ k)
      (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
      (prorepresented_tangentSpaceFunctorConditions S)).functor.obj V ≃ₗ[k]
        Derivation Λ S V where
  toFun x := prorepresentedSquareZeroDerivationsEquiv S V
    (cast (tangentSpaceModuleStructure_prorepresented_carrier S V) x)
  invFun D := cast (tangentSpaceModuleStructure_prorepresented_carrier S V).symm
    ((prorepresentedSquareZeroDerivationsEquiv S V).symm D)
  map_add' x y := by
    obtain ⟨l, hl⟩ := exists_linearMap_tangentSpaceModuleStructure_prorepresented S V
    rw [← hl, ← hl, ← hl, map_add]
  map_smul' c x := by
    obtain ⟨l, hl⟩ := exists_linearMap_tangentSpaceModuleStructure_prorepresented S V
    rw [← hl, ← hl, map_smul]
    rfl
  left_inv x := by simp
  right_inv D := by simp

/-- The linear equivalence is the bijection `f ↦ f - q`: it sends `f` to its square-zero
component. -/
@[stacks 06IC "F(k[V]) = Der_Λ(S, V) as vector spaces, for the canonical structure of 06IA"]
theorem tangentSpaceModuleStructureDerivationsLinearEquiv_apply (V : FGModuleCat.{w} k)
    (x : (tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
      (squareZeroExtension_mem_artinianLocalOver Λ k)
      (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
      (prorepresented_tangentSpaceFunctorConditions S)).functor.obj V) (s : S) :
    tangentSpaceModuleStructureDerivationsLinearEquiv S V x s =
      ((cast (tangentSpaceModuleStructure_prorepresented_carrier S V) x).hom s).snd :=
  rfl

/-- A `k`-linear identification `V ≅ k` identifies `Der_Λ(S, V)` with `Der_Λ(S, k)`, where `S`
acts on `k` through its residue map. -/
noncomputable def derivationsCongrResidueField (V : FGModuleCat.{w} k) (e : V ≃ₗ[k] k) :
    Derivation Λ S V ≃ₗ[k]
      (letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
       Derivation Λ S k) :=
  letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
  let eS : V ≃ₗ[S] k :=
    { e with map_smul' := fun s v ↦ e.map_smul (residueHom S s) v }
  { toFun := fun D ↦ eS.toLinearMap.compDer D
    invFun := fun D ↦ eS.symm.toLinearMap.compDer D
    map_add' := fun D E ↦ by ext; simp
    map_smul' := fun c D ↦ by
      ext s
      exact e.map_smul c (D s)
    left_inv := fun D ↦ by ext; simp
    right_inv := fun D ↦ by ext; simp }

/-- The tangent space `TF = F(k[ε])` of Definition 06IB, for `F` prorepresented by `S`, is the
value of the canonical module structure of Lemma 06IA at the rank-one vector space. -/
theorem tangentSpaceModuleStructure_prorepresented_carrier_rankOne :
    ((tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
      (squareZeroExtension_mem_artinianLocalOver Λ k)
      (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
      (prorepresented_tangentSpaceFunctorConditions S)).functor.obj (FGModuleCat.of k k) :
        Type w) = artinianTangentSpace Λ k (restrictedCoyoneda S) :=
  tangentSpaceModuleStructure_prorepresented_carrier S (FGModuleCat.of k k)

/-- **Stacks Project, Tag 06IC.** For the functor `F` prorepresented by `S`, the tangent space
`TF = F(k[ε]) = Der_Λ(S, k)`, and the `k`-vector space structure on `TF` of Lemma 06IA and
Definition 06IB (the canonical one, coming from `F` preserving finite products) corresponds
to the one on `Der_Λ(S, k)`: the bijection `f ↦ f - q` is a `k`-linear equivalence. -/
@[stacks 06IC "TF = Der_Λ(S, k) as vector spaces, for the canonical structure of 06IA/06IB"]
noncomputable def tangentSpaceModuleStructureRankOneDerivationsLinearEquiv :
    letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
    (tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
      (squareZeroExtension_mem_artinianLocalOver Λ k)
      (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
      (prorepresented_tangentSpaceFunctorConditions S)).functor.obj (FGModuleCat.of k k) ≃ₗ[k]
        Derivation Λ S k :=
  (tangentSpaceModuleStructureDerivationsLinearEquiv S (FGModuleCat.of k k)).trans
    (derivationsCongrResidueField S (FGModuleCat.of k k) (LinearEquiv.refl k k))

/-- The identification sends a tangent vector `f : S → k[ε]` to its `ε`-component. -/
@[stacks 06IC "TF = Der_Λ(S, k) as vector spaces, for the canonical structure of 06IA/06IB"]
theorem tangentSpaceModuleStructureRankOneDerivationsLinearEquiv_apply
    (x : (tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
      (squareZeroExtension_mem_artinianLocalOver Λ k)
      (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
      (prorepresented_tangentSpaceFunctorConditions S)).functor.obj (FGModuleCat.of k k))
    (s : S) :
    letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
    tangentSpaceModuleStructureRankOneDerivationsLinearEquiv S x s =
      ((cast (tangentSpaceModuleStructure_prorepresented_carrier_rankOne S) x).hom s).snd :=
  rfl

/-- **Stacks Project, Tag 06IC.** The tangent space of a prorepresentable functor, with its
canonical vector space structure of Lemma 06IA and Definition 06IB, is finite-dimensional
(by Lemma 06SC), under the chapter's standing assumption that `Λ → k` is finite. -/
@[stacks 06IC "dim_k TF < ∞ for the canonical structure of 06IA/06IB"]
theorem tangentSpaceModuleStructure_prorepresented_finiteDimensional [Module.Finite Λ k] :
    FiniteDimensional k
      ((tangentSpaceModuleStructure Λ k (artinianLocalOver Λ k)
        (squareZeroExtension_mem_artinianLocalOver Λ k)
        (artinianLocalOverToArtinian Λ k ⋙ restrictedCoyoneda S)
        (prorepresented_tangentSpaceFunctorConditions S)).functor.obj (FGModuleCat.of k k)) := by
  let := (residueHom S).toRingHom.toAlgebra
  have : Module.Finite k (Derivation Λ S k) := derivation_module_finite S.residueEquiv
  exact Module.Finite.equiv (tangentSpaceModuleStructureRankOneDerivationsLinearEquiv S).symm

end Canonical

end Deformation

end

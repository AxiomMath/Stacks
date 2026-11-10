module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Data.Fin.Tuple.Sort
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksCore.Algebra.Homology.TotalComplexHomotopy
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.Homology.HomComplex.Evaluation.KFlat
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ChainHomotopy
import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleFlat

/-!
# The total Cech complex of a relative complex is K-flat

Let `f : X ⟶ S` be a morphism of schemes with `S` affine and `A = Γ(S, 𝒪_S)`, and let
`𝒰 = (U_i)_{i ∈ I}` be a finite family of opens of `X` all of whose finite intersections are
affine. Let `K` be a bounded complex of presheaves of `A`-modules on `X` whose degree-`n` term
is the presheaf of sections of a quasi-coherent `𝒪_X`-module `F n` that is flat over `S`, the
differentials being merely `A`-linear. Then `Tot(Č^•(𝒰, K))` is K-flat as a complex of
`A`-modules.

## Main definitions

* `AlgebraicGeometry.sectionsPresheaf`: the presheaf of `Γ(S, 𝒪_S)`-modules of sections of an
  `𝒪_X`-module.
* `AlgebraicGeometry.cechComplexInt`: the Cech complex of a presheaf of modules, extended by
  zero to integer degrees.
* `AlgebraicGeometry.cechDoubleComplex`: the same applied degreewise to a complex.
* `AlgebraicGeometry.totalCechComplex`: the total complex `Tot(Č^•(𝒰, -))`.

## Main results

* `AlgebraicGeometry.kFlat_totalCechComplex`: the total Cech complex is K-flat over
  `Γ(S, 𝒪_S)`.

## Implementation notes

The base is an affine scheme `S` with `A := Γ(S, 𝒪_S)` rather than a chosen presentation
`S = Spec A`; the two readings agree and this one needs no comparison isomorphism. The
`A`-module structure on sections is `Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule`,
the one used by Stacks 01U4.

The source states its complex as a complex of `f^{-1}𝒪_S`-modules whose terms carry compatible
quasi-coherent `𝒪_X`-module structures. Here the complex is one of presheaves of `A`-modules
whose degree-`n` term is identified with the sections of a quasi-coherent `𝒪_X`-module. Since
`A` acts through `f^{-1}𝒪_S`, every `f^{-1}𝒪_S`-linear differential is `A`-linear, so the
hypothesis on the differentials is weaker than the source's and the statement correspondingly
more general; no category of `f^{-1}𝒪_S`-modules is needed to express it.

Flatness of the terms is relative, over the base: `AlgebraicGeometry.IsFlatOver`, flatness of
every stalk `(F n)_x` over `𝒪_{S, f(x)}`. By the discussion following Stacks 08KT this is
exactly flatness of `F n` as an `f^{-1}𝒪_S`-module, which is what the source assumes;
absolute flatness over `𝒪_X` is a different, incomparable condition and is not assumed.

The family of opens need not cover `X`: the proof uses only finiteness and the affineness of
the finite intersections, and the alternating Cech comparison holds for an arbitrary family.

The Cech construction is Mathlib's `CategoryTheory.cechComplexFunctor`, which applies to
presheaves valued in any preadditive category with products, here `ModuleCat A`. The Cech
degree is the first degree of the double complex, so totalization puts the sign `(-1)^p` on the
differential in the direction of the complex. All products and coproducts involved exist in
`ModuleCat A`, so no boundedness is needed for the total complex to exist. In degree `p` the
Cech complex evaluates the presheaf at the categorical product of `U (s 0), …, U (s p)` in
`Opens X`, which is their infimum; the affineness hypothesis is stated for those infima, and at
`p = 0` it says that each `U i` is affine.

## References

* [Stacks Project, Tag 0FMQ](https://stacks.math.columbia.edu/tag/0FMQ)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
-/

@[expose] public noncomputable section

attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver
attribute [local instance 2100] Quiver.opposite

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange (le_preimage_top baseModule)

universe u

/-- Products in `ModuleCat`, found directly (instance search for them times out). -/
local instance moduleCatHasProducts {R : Type u} [Ring R] : HasProducts.{u} (ModuleCat.{u} R) :=
  fun _ => inferInstance

/-- Products of complexes of modules, found directly (instance search for them times out). -/
local instance homologicalComplexModuleCatHasProducts {R : Type u} [Ring R] {ι : Type*}
    (c : ComplexShape ι) : HasProducts.{u} (HomologicalComplex (ModuleCat.{u} R) c) :=
  fun J =>
    have : HasLimitsOfShape (Discrete J) (ModuleCat.{u} R) := moduleCatHasProducts J
    ⟨fun F => ⟨⟨⟨_, HomologicalComplex.isLimitConeOfHasLimitEval F⟩⟩⟩⟩

namespace AlgebraicGeometry

open Stacks.Cech.ChainHomotopy

/-- The presheaf of `Γ(S, 𝒪_S)`-modules of sections of an `𝒪_X`-module: it sends an open
`U ⊆ X` to `F(U)` with the scalars restricted along `Γ(S, 𝒪_S) ⟶ 𝒪_X(U)`, with the
restriction maps of `F`. These are linear for these actions because pulling a global
function of the base back along `f` and restricting it commutes with restriction
(`Scheme.Hom.appLE_map`). -/
public noncomputable def sectionsPresheaf {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} ↑Γ(S, ⊤) :=
  letI inst : ∀ U : X.Opens, Module ↑Γ(S, ⊤) ↑Γ(F, U) := baseModule f F
  let res : ∀ {U V : (X.Opens)ᵒᵖ}, (U ⟶ V) →
      (ModuleCat.of ↑Γ(S, ⊤) ↑Γ(F, U.unop) ⟶ ModuleCat.of ↑Γ(S, ⊤) ↑Γ(F, V.unop)) :=
    fun {U V} g => ModuleCat.ofHom
      { toFun := fun s => F.presheaf.map g s
        map_add' := fun s t => map_add _ s t
        map_smul' := fun c s => by
          have hmap :
              X.presheaf.map g.unop.op
                  (f.appLE ⊤ U.unop (le_preimage_top f U.unop) c) =
                f.appLE ⊤ V.unop (le_preimage_top f V.unop) c := by
            rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map]
          have h := Scheme.Modules.map_smul F g.unop
            (f.appLE ⊤ U.unop (le_preimage_top f U.unop) c) s
          rw [hmap] at h
          exact h }
  { obj := fun U => ModuleCat.of ↑Γ(S, ⊤) ↑Γ(F, U.unop)
    map := fun {_ _} g => res g
    map_id := fun U => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change F.presheaf.map (𝟙 U) s = s
      rw [F.presheaf.map_id]
      rfl
    map_comp := fun {_ _ _} g h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change F.presheaf.map (g ≫ h) s = F.presheaf.map h (F.presheaf.map g s)
      rw [F.presheaf.map_comp]
      rfl }

private lemma cechComplexFunctor_map_zero {X : Scheme.{u}} {R : Type u} [CommRing R]
    {I : Type u} (U : I → X.Opens) (P Q : (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R) :
    (CategoryTheory.cechComplexFunctor (A := ModuleCat.{u} R) U).map (0 : P ⟶ Q) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  change Limits.Pi.map (fun i => (0 : P.obj _ ⟶ Q.obj _)) = 0
  apply Limits.Pi.hom_ext
  intro j
  rw [Limits.Pi.map_π]
  simp

section Cech

variable {X : Scheme.{u}} {R : Type u} [CommRing R] {I : Type u} (U : I → X.Opens)

/-- The Čech complex functor for the family `U` preserves zero morphisms. -/
local instance :
    (CategoryTheory.cechComplexFunctor (A := ModuleCat.{u} R) U).PreservesZeroMorphisms where
  map_zero := by
    intro P Q
    exact cechComplexFunctor_map_zero U P Q

/-- The Čech complex of a presheaf of `R`-modules on `X` for the family `U`, extended by
zero from nonnegative to integer degrees. In degree `p ≥ 0` it is the product, over the
`(p + 1)`-tuples `s` from the index set, of the sections over `U (s 0) ⊓ ⋯ ⊓ U (s p)`. -/
public noncomputable def cechComplexInt :
    ((X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R) ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  CategoryTheory.cechComplexFunctor U ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)

/-- The functor `cechComplexInt U` preserves zero morphisms. -/
local instance : (cechComplexInt (R := R) U).PreservesZeroMorphisms := by
  constructor
  intro P Q
  change (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map
    ((CategoryTheory.cechComplexFunctor U).map 0) = 0
  rw [Functor.map_zero, Functor.map_zero]

/-- The Čech double complex of a complex of presheaves of `R`-modules: the first degree is
the Čech degree and the second the degree in the given complex. -/
public noncomputable def cechDoubleComplex :
    CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R) ℤ ⥤
      HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (cechComplexInt U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)

/-- `Tot(Č^•(𝒰, -))`: the total complex of the Čech double complex of a complex of
presheaves of `R`-modules, a complex of `R`-modules. -/
public noncomputable def totalCechComplex :
    CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  cechDoubleComplex U ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)

end Cech

open MonoidalCategory


private lemma sections_flat {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (F : ℤ → X.Modules) (hqc : ∀ n, (F n).IsQuasicoherent)
    (hflat : ∀ n, IsFlatOver f.toLRSHom.toShHom (F n))
    (n : ℤ) (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Module ↑Γ(S, ⊤) ↑Γ(F n, U) := baseModule f (F n) U
    Module.Flat ↑Γ(S, ⊤) ↑Γ(F n, U) := by
  let : (F n).IsQuasicoherent := hqc n
  let hsections := ((isFlatOver_tfae f (F n)).out 1 2).mp (hflat n)
  let h := hsections U hU ⊤ (isAffineOpen_top S) (le_preimage_top f U)
  simpa only [baseModule] using h

private alias flat_pi_of_finite := Stacks.Cech.flat_pi_of_finite

private lemma flat_categorical_pi {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (M : ι → ModuleCat R) (hM : ∀ i, Module.Flat R (M i)) :
    Module.Flat R ↑(∏ᶜ M) := by
  classical
  let := Fintype.ofFinite ι
  have : Module.Flat R (∀ i, (M i : Type _)) := flat_pi_of_finite fun i => (M i : Type _)
  exact Module.Flat.of_linearEquiv (ModuleCat.piIsoPi M).toLinearEquiv

private lemma flat_evalOp_obj {C : Type u} [Category.{u} C] {R : Type u} [CommRing R]
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R) (V : CategoryTheory.Limits.FormalCoproduct.{u} C)
    [Finite V.I] (hP : ∀ i, Module.Flat R (P.obj (Opposite.op (V.obj i)))) :
    Module.Flat R ↑(((CategoryTheory.Limits.FormalCoproduct.evalOp C (ModuleCat R)).obj P).obj
      (Opposite.op V)) := by
  change Module.Flat R ↑(∏ᶜ fun i : V.I => P.obj (Opposite.op (V.obj i)))
  exact flat_categorical_pi _ hP

private lemma flat_categorical_coprod {R : Type*} [CommRing R] {ι : Type*}
    (M : ι → ModuleCat R) (hM : ∀ i, Module.Flat R (M i)) :
    Module.Flat R ↑(∐ M) := by
  classical
  exact Module.Flat.of_linearEquiv (ModuleCat.coprodIsoDirectSum M).toLinearEquiv

private lemma cech_term_flat {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    {I : Type u} [Finite I] (U : I → X.Opens)
    (haffine : ∀ (p : ℕ) (s : Fin (p + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (F : ℤ → X.Modules) (hqc : ∀ n, (F n).IsQuasicoherent)
    (hflat : ∀ n, IsFlatOver f.toLRSHom.toShHom (F n))
    (n : ℤ) (p : ℕ) :
    Module.Flat ↑Γ(S, ⊤)
      (((CategoryTheory.cechComplexFunctor U).obj (sectionsPresheaf f (F n))).X p) := by
  classical
  let E : CategoryTheory.Limits.FormalCoproduct.{u} X.Opens :=
    CategoryTheory.Limits.FormalCoproduct.mk _ U
  let V : CategoryTheory.Limits.FormalCoproduct.{u} X.Opens :=
    E.cech.obj (Opposite.op (SimplexCategory.mk p))
  have : Finite V.I := by
    change Finite (Fin (p + 1) → I)
    infer_instance
  change Module.Flat ↑Γ(S, ⊤)
    (((CategoryTheory.Limits.FormalCoproduct.evalOp X.Opens (ModuleCat ↑Γ(S, ⊤))).obj
      (sectionsPresheaf f (F n))).obj (Opposite.op V))
  apply flat_evalOp_obj
  intro s
  have hs : V.obj s = ⨅ k, U (s k) := by
    calc
      V.obj s = ∏ᶜ fun k => U (s k) := by
        rfl
      _ = ⨅ k, U (s k) := by
        let Z := fun k : Fin (p + 1) => U (s k)
        let e := IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor Z))
          (Preorder.isLimitIInf Z)
        exact le_antisymm (leOfHom e.hom) (leOfHom e.inv)
  rw [hs]
  exact sections_flat f F hqc hflat n _ (haffine p s)

private lemma cechInt_term_flat {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    {I : Type u} [Finite I] (U : I → X.Opens)
    (haffine : ∀ (p : ℕ) (s : Fin (p + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (F : ℤ → X.Modules) (hqc : ∀ n, (F n).IsQuasicoherent)
    (hflat : ∀ n, IsFlatOver f.toLRSHom.toShHom (F n))
    (P : (X.Opens)ᵒᵖ ⥤ ModuleCat ↑Γ(S, ⊤))
    (n : ℤ) (eP : P ≅ sectionsPresheaf f (F n)) (p : ℤ) :
    Module.Flat ↑Γ(S, ⊤) ↑(((cechComplexInt U).obj P).X p) := by
  classical
  by_cases hp : ∃ m : ℕ, ComplexShape.embeddingUpNat.f m = p
  · obtain ⟨m, hm⟩ := hp
    let e := (cechComplexInt U).mapIso eP
    let eQ := HomologicalComplex.extendXIso
      ((CategoryTheory.cechComplexFunctor U).obj (sectionsPresheaf f (F n)))
      ComplexShape.embeddingUpNat hm
    let e := (asIso (e.hom.f p)).trans eQ
    have : Module.Flat ↑Γ(S, ⊤)
        ↑(((CategoryTheory.cechComplexFunctor U).obj (sectionsPresheaf f (F n))).X m) :=
      cech_term_flat f U haffine F hqc hflat n m
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  · have hz : IsZero (((cechComplexInt U).obj P).X p) := by
      apply HomologicalComplex.isZero_extend_X
      exact fun m hm => hp ⟨m, hm⟩
    have : Subsingleton ↑(((cechComplexInt U).obj P).X p) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    exact Module.Flat.of_free

private lemma cechDouble_component_flat {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    {I : Type u} [Finite I] (U : I → X.Opens)
    (haffine : ∀ (p : ℕ) (s : Fin (p + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (K : CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat ↑Γ(S, ⊤)) ℤ)
    (F : ℤ → X.Modules) (hqc : ∀ n, (F n).IsQuasicoherent)
    (hflat : ∀ n, IsFlatOver f.toLRSHom.toShHom (F n))
    (hterm : ∀ n, K.X n ≅ sectionsPresheaf f (F n)) (p q : ℤ) :
    Module.Flat ↑Γ(S, ⊤) ↑((((cechDoubleComplex U).obj K).X p).X q) := by
  change Module.Flat ↑Γ(S, ⊤) ↑(((cechComplexInt U).obj (K.X q)).X p)
  exact cechInt_term_flat f U haffine F hqc hflat (K.X q) q (hterm q) p

private lemma totalCech_term_flat {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    {I : Type u} [Finite I] (U : I → X.Opens)
    (haffine : ∀ (p : ℕ) (s : Fin (p + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (K : CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat ↑Γ(S, ⊤)) ℤ)
    (F : ℤ → X.Modules) (hqc : ∀ n, (F n).IsQuasicoherent)
    (hflat : ∀ n, IsFlatOver f.toLRSHom.toShHom (F n))
    (hterm : ∀ n, K.X n ≅ sectionsPresheaf f (F n)) (n : ℤ) :
    Module.Flat ↑Γ(S, ⊤) ↑(((totalCechComplex U).obj K).X n) := by
  classical
  let B := (cechDoubleComplex U).obj K
  change Module.Flat ↑Γ(S, ⊤)
    ↑(∐ B.toGradedObject.mapObjFun (ComplexShape.π (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)
  exact flat_categorical_coprod _ fun pq =>
    cechDouble_component_flat f U haffine K F hqc hflat hterm pq.1.1 pq.1.2


namespace CategoricalCech

-- Mathlib's `CategoryTheory.cechComplexFunctor` spells the `p`-th Cech object through the
-- `Functor.rightOp` of the formal-coproduct cosimplicial object, and the bicomplex below is
-- reached from it through `mapHomologicalComplex` and `HomologicalComplex₂.flip`. Identifying
-- the resulting factors with the products `∏ᶜ (U ∘ tuple)` is definitional, and these are
-- exactly the definitions whose unfolding that identification needs; naming them here makes
-- the unfoldings available to `rfl`, `rw` and `simp` without switching off transparency
-- altogether.
attribute [local implicit_reducible] CategoryTheory.cechComplexFunctor
  FormalCoproduct.power FormalCoproduct.cosimplicialObjectFunctor
  FormalCoproduct.cochainComplexFunctor FormalCoproduct.evalOp
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj
  HomologicalComplex.asFunctor HomologicalComplex₂.flipFunctor HomologicalComplex₂.flip

variable {X : TopCat.{u}} {I : Type u} [LinearOrder I]
  (U : I → Opens X)
  {C : Type*} [Category* C] [Preadditive C] [HasProducts.{u} C]

private abbrev cochains (P : X.Presheaf C) (p : ℕ) : C :=
  ∏ᶜ fun tuple : Fin (p + 1) → I => P.obj (op (CechCochains.inter U tuple))

private def evaluation (P : X.Presheaf C) (V : Opens X) (p : ℕ) :
    SupportedChain U V p →+ (cochains U P p ⟶ P.obj (op V)) :=
  FreeAbelianGroup.lift fun tuple =>
    Pi.π _ tuple.1 ≫ P.map (homOfLE tuple.2).op

private def differential (P : X.Presheaf C) (p : ℕ) :
    cochains U P p ⟶ cochains U P (p + 1) :=
  Pi.lift fun tuple =>
    ∑ vertex : Fin (p + 2), (-1 : ℤ) ^ (vertex : ℕ) •
      (Pi.π _ (tuple ∘ vertex.succAbove) ≫
        P.map (homOfLE (CechCochains.inter_le_omit U tuple vertex)).op)

private def sorting (P : X.Presheaf C) (p : ℕ) :
    cochains U P p ⟶ cochains U P p :=
  Pi.lift fun tuple => evaluation U P (CechCochains.inter U tuple) p
    (projection U (CechCochains.inter U tuple) p
      (FreeAbelianGroup.of ⟨tuple, le_rfl⟩))

private def homotopy (P : X.Presheaf C) (p : ℕ) :
    cochains U P (p + 1) ⟶ cochains U P p :=
  Pi.lift fun tuple => evaluation U P (CechCochains.inter U tuple) (p + 1)
    (chainHomotopy U (CechCochains.inter U tuple) p
      (FreeAbelianGroup.of ⟨tuple, le_rfl⟩))

omit [LinearOrder I] in
private lemma evaluation_boundary (P : X.Presheaf C) (V : Opens X) (p : ℕ)
    (chain : SupportedChain U V (p + 1)) :
    evaluation U P V p (boundary U V p chain) =
      differential U P p ≫ evaluation U P V (p + 1) chain := by
  suffices (evaluation U P V p).comp (boundary U V p) =
      (Preadditive.leftComp _ (differential U P p)).comp (evaluation U P V (p + 1)) from
    DFunLike.congr_fun this chain
  apply FreeAbelianGroup.lift_ext
  intro tuple
  change evaluation U P V p (boundary U V p (FreeAbelianGroup.of tuple)) =
    differential U P p ≫ evaluation U P V (p + 1) (FreeAbelianGroup.of tuple)
  simp only [boundary,
    FreeAbelianGroup.lift_apply_of, map_sum, map_zsmul, evaluation,
    face, differential,
    Pi.lift_comp_π_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro vertex _
  rw [← P.map_comp, ← op_comp]
  rfl

omit [LinearOrder I] in
private lemma evaluation_chainMap (P : X.Presheaf C) {V W : Opens X}
    (inclusion : V ≤ W) (p : ℕ) (chain : SupportedChain U W p) :
    evaluation U P V p (chainMap U inclusion p chain) =
      evaluation U P W p chain ≫ P.map (homOfLE inclusion).op := by
  suffices (evaluation U P V p).comp (chainMap U inclusion p) =
      (Preadditive.rightComp _ (P.map (homOfLE inclusion).op)).comp
        (evaluation U P W p) from DFunLike.congr_fun this chain
  apply FreeAbelianGroup.lift_ext
  intro tuple
  change evaluation U P V p (chainMap U inclusion p (FreeAbelianGroup.of tuple)) =
    evaluation U P W p (FreeAbelianGroup.of tuple) ≫ P.map (homOfLE inclusion).op
  simp only [chainMap,
    FreeAbelianGroup.lift_apply_of, evaluation,
    Category.assoc, ← P.map_comp, ← op_comp]
  rfl

/-- A cochain map built from a family of natural chain maps `T` acts on evaluations through `T`. -/
private lemma comp_evaluation_of_natural {J : Type u} (U : J → Opens X) (P : X.Presheaf C)
    {a b : ℕ}
    (t : cochains U P b ⟶ cochains U P a) (T : ∀ V, SupportedChain U V a →+ SupportedChain U V b)
    (hT : ∀ {V W : Opens X} (h : V ≤ W) (chain : SupportedChain U W a),
      chainMap U h b (T W chain) = T V (chainMap U h a chain))
    (ht : ∀ tuple : Fin (a + 1) → J, t ≫ Pi.π _ tuple =
      evaluation U P (CechCochains.inter U tuple) b (T _ (FreeAbelianGroup.of ⟨tuple, le_rfl⟩)))
    (V : Opens X) (chain : SupportedChain U V a) :
    t ≫ evaluation U P V a chain = evaluation U P V b (T V chain) := by
  suffices (Preadditive.leftComp _ t).comp (evaluation U P V a) =
      (evaluation U P V b).comp (T V) from DFunLike.congr_fun this chain
  apply FreeAbelianGroup.lift_ext
  intro tuple
  change t ≫ evaluation U P V a (FreeAbelianGroup.of tuple) = _
  simp only [evaluation, FreeAbelianGroup.lift_apply_of, ← Category.assoc, ht]
  change evaluation U P (CechCochains.inter U tuple.1) b
      (T _ (FreeAbelianGroup.of ⟨tuple.1, le_rfl⟩)) ≫ P.map (homOfLE tuple.2).op = _
  rw [← evaluation_chainMap, hT]
  rfl

private lemma evaluation_homotopy (P : X.Presheaf C) (V : Opens X) (p : ℕ)
    (chain : SupportedChain U V p) :
    homotopy U P p ≫ evaluation U P V p chain =
      evaluation U P V (p + 1) (chainHomotopy U V p chain) :=
  comp_evaluation_of_natural U P _ (fun V => chainHomotopy U V p) (fun h => chainMap_homotopy U h p)
    (fun _ => Pi.lift_comp_π _ _) V chain

private lemma homotopy_identity (P : X.Presheaf C) (p : ℕ) :
    differential U P (p + 1) ≫ homotopy U P (p + 1) +
      homotopy U P p ≫ differential U P p = 𝟙 _ - sorting U P (p + 1) := by
  apply Pi.hom_ext
  intro tuple
  have identity := congrArg (evaluation U P (CechCochains.inter U tuple) (p + 1))
    (chainHomotopy_identity U (CechCochains.inter U tuple) p
      (FreeAbelianGroup.of ⟨tuple, le_rfl⟩))
  simp only [map_add, map_sub, evaluation_boundary, ← evaluation_homotopy] at identity
  simpa [homotopy, sorting, evaluation, Category.assoc] using identity

private lemma evaluation_projection (P : X.Presheaf C) (V : Opens X) (p : ℕ)
    (chain : SupportedChain U V p) :
    sorting U P p ≫ evaluation U P V p chain =
      evaluation U P V p (projection U V p chain) :=
  comp_evaluation_of_natural U P _ (fun V => projection U V p) (fun h => chainMap_projection U h p)
    (fun _ => Pi.lift_comp_π _ _) V chain

omit [LinearOrder I] in
private lemma evaluation_self (P : X.Presheaf C) (p : ℕ) (tuple : Fin (p + 1) → I) :
    evaluation U P (CechCochains.inter U tuple) p
      (FreeAbelianGroup.of ⟨tuple, le_rfl⟩) = Pi.π _ tuple := by
  simp [evaluation]

omit [LinearOrder I] in
private lemma differential_comp (P : X.Presheaf C) (p : ℕ) :
    differential U P p ≫ differential U P (p + 1) = 0 := by
  apply Pi.hom_ext
  intro tuple
  rw [← evaluation_self U P (p + 2) tuple, Category.assoc,
    ← evaluation_boundary, ← evaluation_boundary, boundary_boundary]
  simp

private lemma sorting_comm (P : X.Presheaf C) (p : ℕ) :
    sorting U P p ≫ differential U P p = differential U P p ≫ sorting U P (p + 1) := by
  apply Pi.hom_ext
  intro tuple
  rw [← evaluation_self U P (p + 1) tuple, Category.assoc, Category.assoc,
    evaluation_projection, ← evaluation_boundary, evaluation_projection,
    ← boundary_projection, evaluation_boundary]

private lemma sorting_idempotent (P : X.Presheaf C) (p : ℕ) :
    sorting U P p ≫ sorting U P p = sorting U P p := by
  apply Pi.hom_ext
  intro tuple
  rw [← evaluation_self U P p tuple, Category.assoc,
    evaluation_projection, evaluation_projection, projection_idempotent]

private lemma sorting_zero (P : X.Presheaf C) : sorting U P 0 = 𝟙 _ := by
  apply Pi.hom_ext
  intro tuple
  simp only [sorting, Pi.lift_comp_π, projection_zero, evaluation_self,
    Category.id_comp]

private lemma sorting_eq_zero [Finite I] (P : X.Presheaf C) (p : ℕ)
    (hp : Nat.card I ≤ p) : sorting U P p = 0 := by
  apply Pi.hom_ext
  intro tuple
  simp [sorting, projection_eq_zero U _ p hp]

private abbrev complex (P : X.Presheaf C) : CochainComplex C ℕ :=
  CochainComplex.of (cochains U P) (differential U P) (differential_comp U P)

private def sortingMap (P : X.Presheaf C) : complex U P ⟶ complex U P :=
  CochainComplex.ofHom (sorting U P) (by
    intro degree
    simpa [complex, CochainComplex.of_d] using sorting_comm U P degree)

private def sortingHomotopy (P : X.Presheaf C) :
    Homotopy (𝟙 (complex U P)) (sortingMap U P) where
  hom first second := if equality : second + 1 = first then
    eqToHom (by simp only [← equality]) ≫
      homotopy U P second else 0
  zero first second inequality := by
    change ¬ second + 1 = first at inequality
    simp [inequality]
  comm degree := by
    cases degree with
    | zero =>
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel 0 1 from rfl),
        prevD_eq_zero _ _ (by simp [ComplexShape.up])]
      have zero_homotopy : homotopy U P 0 = 0 := by
        apply Pi.hom_ext
        intro tuple
        simp [homotopy, chainHomotopy]
      simp [complex, sortingMap, zero_homotopy, sorting_zero, zero_add]
    | succ degree =>
      have identity := homotopy_identity U P degree
      have rearranged := (eq_sub_iff_add_eq.mp identity).symm
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel (degree + 1) (degree + 2) from rfl),
        prevD_eq _ (show (ComplexShape.up ℕ).Rel degree (degree + 1) from rfl)]
      simp only [complex, sortingMap,
        eqToHom_refl, Category.id_comp]
      change 𝟙 _ = CochainComplex.of.d (cochains U P) (differential U P)
        (degree + 1) ((degree + 1) + 1) ≫ homotopy U P (degree + 1) +
          homotopy U P degree ≫ CochainComplex.of.d (cochains U P) (differential U P)
            degree (degree + 1) + sorting U P (degree + 1)
      rw [CochainComplex.of_d, CochainComplex.of_d]
      exact rearranged

private def intersectionIso {p : ℕ} (tuple : Fin p → I) :
    ∏ᶜ (U ∘ tuple) ≅ CechCochains.inter U tuple :=
  limit.isoLimitCone ⟨_, Preorder.isLimitIInf (U ∘ tuple)⟩

private def objectIso (P : X.Presheaf C) (p : ℕ) :
    cochains U P p ≅ ((CategoryTheory.cechComplexFunctor U).obj P).X p where
  hom := CategoryTheory.Limits.Pi.map fun tuple => P.map (intersectionIso U tuple).hom.op
  inv := CategoryTheory.Limits.Pi.map fun tuple => P.map (intersectionIso U tuple).inv.op
  hom_inv_id := by
    apply Pi.hom_ext
    intro tuple
    change (CategoryTheory.Limits.Pi.map
      (fun tuple => P.map (intersectionIso U tuple).hom.op) ≫
      CategoryTheory.Limits.Pi.map
        (fun tuple => P.map (intersectionIso U tuple).inv.op)) ≫
          Pi.π (fun tuple : Fin (p + 1) → I => P.obj (op (CechCochains.inter U tuple))) tuple = _
    simp only [Category.assoc, CategoryTheory.Limits.Pi.map_π,
      CategoryTheory.Limits.Pi.map_π_assoc, ← P.map_comp, ← op_comp,
      Iso.inv_hom_id, op_id, P.map_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro tuple
    change (CategoryTheory.Limits.Pi.map
      (fun tuple => P.map (intersectionIso U tuple).inv.op) ≫
      CategoryTheory.Limits.Pi.map
        (fun tuple => P.map (intersectionIso U tuple).hom.op)) ≫
          Pi.π (fun tuple : Fin (p + 1) → I => P.obj (op (∏ᶜ (U ∘ tuple)))) tuple = _
    simp only [Category.assoc, CategoryTheory.Limits.Pi.map_π,
      CategoryTheory.Limits.Pi.map_π_assoc, ← P.map_comp, ← op_comp,
      Iso.hom_inv_id, op_id, P.map_id, Category.comp_id]
    exact (Category.id_comp _).symm

omit [LinearOrder I] in
@[reassoc]
private lemma objectIso_hom_π (P : X.Presheaf C) (p : ℕ) (tuple : Fin (p + 1) → I) :
    (objectIso U P p).hom ≫
      Pi.π (fun tuple : Fin (p + 1) → I => P.obj (op (∏ᶜ (U ∘ tuple)))) tuple =
        Pi.π (fun tuple : Fin (p + 1) → I => P.obj (op (CechCochains.inter U tuple))) tuple ≫
          P.map (intersectionIso U tuple).hom.op :=
  Limits.Pi.map_π (fun tuple : Fin (p + 1) → I => P.map (intersectionIso U tuple).hom.op) tuple

omit [LinearOrder I] in
/-- The components of `differential`: an alternating sum over the vertex that is omitted. -/
private lemma differential_π (P : X.Presheaf C) (p : ℕ) (tuple : Fin (p + 2) → I) :
    differential U P p ≫
        Pi.π (fun other : Fin (p + 2) → I => P.obj (op (CechCochains.inter U other))) tuple =
      ∑ vertex : Fin (p + 2), (-1 : ℤ) ^ (vertex : ℕ) •
        (Pi.π (fun other : Fin (p + 1) → I => P.obj (op (CechCochains.inter U other)))
            (tuple ∘ vertex.succAbove) ≫
          P.map (homOfLE (CechCochains.inter_le_omit U tuple vertex)).op) :=
  Pi.lift_comp_π _ tuple

omit [LinearOrder I] in
/-- The differential of Mathlib's Cech complex is the alternating sum of the maps that omit
one vertex, read on the products `∏ᶜ (U ∘ tuple)`. -/
private lemma cechComplexFunctor_obj_d (P : X.Presheaf C) (p : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj P).d p (p + 1) =
      ∑ vertex : Fin (p + 2), (-1 : ℤ) ^ (vertex : ℕ) •
        Pi.lift (f := fun other : Fin (p + 2) → I => P.obj (op (∏ᶜ (U ∘ other))))
          fun other => Pi.π (fun tuple : Fin (p + 1) → I => P.obj (op (∏ᶜ (U ∘ tuple))))
              (other ∘ vertex.succAbove) ≫
            P.map (Pi.lift fun index => Pi.π (U ∘ other) (vertex.succAbove index)).op :=
  (CochainComplex.of_d
      (fun step => ((FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj P).obj (SimplexCategory.mk step))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj P)) p).trans
    (Finset.sum_congr rfl fun _ _ => rfl)

omit [LinearOrder I] in
/-- The square comparing `differential` with the alternating sum of the omit maps, stated
entirely through products indexed by tuples. -/
private lemma prodObjectIso_comm (P : X.Presheaf C) (p : ℕ) :
    (Limits.Pi.map fun tuple : Fin (p + 1) → I =>
        P.map (intersectionIso U tuple).hom.op) ≫
      (∑ vertex : Fin (p + 2), (-1 : ℤ) ^ (vertex : ℕ) •
        Pi.lift (f := fun other : Fin (p + 2) → I => P.obj (op (∏ᶜ (U ∘ other))))
          fun other => Pi.π (fun tuple : Fin (p + 1) → I => P.obj (op (∏ᶜ (U ∘ tuple))))
              (other ∘ vertex.succAbove) ≫
            P.map (Pi.lift fun index => Pi.π (U ∘ other) (vertex.succAbove index)).op) =
      differential U P p ≫ Limits.Pi.map fun tuple : Fin (p + 2) → I =>
        P.map (intersectionIso U tuple).hom.op := by
  apply Pi.hom_ext
  intro tuple
  simp only [Category.assoc, Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, Pi.lift_comp_π,
    CategoryTheory.Limits.Pi.map_π, CategoryTheory.Limits.Pi.map_π_assoc]
  rw [← Category.assoc (differential U P p), differential, Pi.lift_comp_π]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  refine Finset.sum_congr rfl fun vertex _ => ?_
  congr 1
  simp only [← P.map_comp, ← op_comp]
  congr 2

omit [LinearOrder I] in
private lemma objectIso_comm (P : X.Presheaf C) (p : ℕ) :
    (objectIso U P p).hom ≫ ((CategoryTheory.cechComplexFunctor U).obj P).d p (p + 1) =
      differential U P p ≫ (objectIso U P (p + 1)).hom := by
  rw [cechComplexFunctor_obj_d]
  exact prodObjectIso_comm U P p

private def complexIso (P : X.Presheaf C) :
    complex U P ≅ (CategoryTheory.cechComplexFunctor U).obj P :=
  HomologicalComplex.Hom.isoOfComponents (objectIso U P) (by
    intro first second relation
    obtain rfl : first + 1 = second := relation
    simpa [complex, CochainComplex.of_d] using objectIso_comm U P first)

end CategoricalCech

namespace CechTotalization

-- The same list of definitional unfoldings as in `CategoricalCech` above; see the comment
-- there for why each is needed.
attribute [local implicit_reducible] CategoryTheory.cechComplexFunctor
  FormalCoproduct.power FormalCoproduct.cosimplicialObjectFunctor
  FormalCoproduct.cochainComplexFunctor FormalCoproduct.evalOp
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj
  HomologicalComplex.asFunctor HomologicalComplex₂.flipFunctor HomologicalComplex₂.flip

variable {X : Scheme.{u}} {R : Type u} [CommRing R]
  {I : Type u} [LinearOrder I] (U : I → X.Opens)
  (K : CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R) ℤ)

/-- The Čech complex functor for the family `U` preserves zero morphisms. -/
local instance :
    (CategoryTheory.cechComplexFunctor (A := ModuleCat.{u} R) U).PreservesZeroMorphisms where
  map_zero := by
    intro P Q
    exact cechComplexFunctor_map_zero U P Q

private abbrev bicomplexNat :=
  CategoricalCech.complex U K.asFunctor

private abbrev usualBicomplexNat :=
  ((HomologicalComplex₂.flipFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
    (ComplexShape.up ℕ)).obj
      (((CategoryTheory.cechComplexFunctor U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))

private def componentIso (p : ℕ) (q : ℤ) :
    ((bicomplexNat U K).X p).X q ≅ ((usualBicomplexNat U K).X p).X q :=
  (PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) q)
    (fun tuple : Fin (p + 1) → I => K.asFunctor.obj (op (CechCochains.inter U tuple)))).trans
      (CategoricalCech.objectIso U (K.X q) p)

omit [LinearOrder I] in
@[reassoc]
private lemma componentIso_hom_π (p : ℕ) (q : ℤ) (tuple : Fin (p + 1) → I) :
    (componentIso U K p q).hom ≫
      Pi.π (fun tuple : Fin (p + 1) → I => (K.X q).obj (op (∏ᶜ (U ∘ tuple)))) tuple =
      (Pi.π (fun tuple : Fin (p + 1) → I =>
        K.asFunctor.obj (op (CechCochains.inter U tuple))) tuple).f q ≫
          (K.X q).map (CategoricalCech.intersectionIso U tuple).hom.op := by
  have projection :
      (CategoricalCech.objectIso U (K.X q) p).hom ≫
          Pi.π (fun other : Fin (p + 1) → I => (K.X q).obj (op (∏ᶜ (U ∘ other)))) tuple =
        Pi.π (fun other : Fin (p + 1) → I =>
            (K.X q).obj (op (CechCochains.inter U other))) tuple ≫
          (K.X q).map (CategoricalCech.intersectionIso U tuple).hom.op :=
    CategoricalCech.objectIso_hom_π U (K.X q) p tuple
  have comparison :
      (PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) q)
            fun other : Fin (p + 1) → I =>
              K.asFunctor.obj (op (CechCochains.inter U other))).hom ≫
          Pi.π (fun other : Fin (p + 1) → I =>
            (K.X q).obj (op (CechCochains.inter U other))) tuple =
        (Pi.π (fun other : Fin (p + 1) → I =>
          K.asFunctor.obj (op (CechCochains.inter U other))) tuple).f q :=
    piComparison_comp_π _ _ tuple
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun morphism =>
    (PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) q)
      (fun other : Fin (p + 1) → I =>
        K.asFunctor.obj (op (CechCochains.inter U other)))).hom ≫ morphism) projection).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun morphism => morphism ≫
    (K.X q).map (CategoricalCech.intersectionIso U tuple).hom.op) comparison

private def columnIso (p : ℕ) :
    (bicomplexNat U K).X p ≅ (usualBicomplexNat U K).X p :=
  HomologicalComplex.Hom.isoOfComponents (componentIso U K p) (by
    intro first second relation
    apply Pi.hom_ext (f := fun tuple : Fin (p + 1) → I =>
      (K.X second).obj (op (∏ᶜ (U ∘ tuple))))
    intro tuple
    have column : ((usualBicomplexNat U K).X p).d first second ≫
          Pi.π (fun other : Fin (p + 1) → I =>
            (K.X second).obj (op (∏ᶜ (U ∘ other)))) tuple =
        Pi.π (fun other : Fin (p + 1) → I =>
            (K.X first).obj (op (∏ᶜ (U ∘ other)))) tuple ≫
          (K.d first second).app (op (∏ᶜ (U ∘ tuple))) :=
      CategoryTheory.Limits.Pi.map_π (fun other : Fin (p + 1) → I =>
        (K.d first second).app (op (∏ᶜ (U ∘ other)))) tuple
    have naturality : ((Pi.π (fun other : Fin (p + 1) → I =>
              K.asFunctor.obj (op (CechCochains.inter U other))) tuple).f first ≫
            (K.X first).map (CategoricalCech.intersectionIso U tuple).hom.op) ≫
          (K.d first second).app (op (∏ᶜ (U ∘ tuple))) =
        ((bicomplexNat U K).X p).d first second ≫
          (Pi.π (fun other : Fin (p + 1) → I =>
              K.asFunctor.obj (op (CechCochains.inter U other))) tuple).f second ≫
            (K.X second).map (CategoricalCech.intersectionIso U tuple).hom.op := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun morphism =>
        (Pi.π (fun other : Fin (p + 1) → I =>
          K.asFunctor.obj (op (CechCochains.inter U other))) tuple).f first ≫ morphism)
        ((K.d first second).naturality
          (CategoricalCech.intersectionIso U tuple).hom.op)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun morphism => morphism ≫
        (K.X second).map (CategoricalCech.intersectionIso U tuple).hom.op)
        ((Pi.π (fun other : Fin (p + 1) → I =>
          K.asFunctor.obj (op (CechCochains.inter U other))) tuple).comm first second)).trans ?_
      exact Category.assoc _ _ _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun morphism =>
      (componentIso U K p first).hom ≫ morphism) column).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun morphism =>
      morphism ≫ (K.d first second).app (op (∏ᶜ (U ∘ tuple))))
      (componentIso_hom_π U K p first tuple)).trans ?_
    refine naturality.trans ?_
    refine (congrArg (fun morphism =>
      ((bicomplexNat U K).X p).d first second ≫ morphism)
      (componentIso_hom_π U K p second tuple).symm).trans ?_
    exact (Category.assoc _ _ _).symm)

omit [LinearOrder I] in
/-- The comparison maps `piComparison` for the products over tuples are compatible with the
Cech differential of `CategoricalCech.complex`. -/
private lemma comparison_differential (first : ℕ) (degree : ℤ) :
    (PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.up ℤ) degree)
        fun other : Fin (first + 1) → I =>
          K.asFunctor.obj (op (CechCochains.inter U other))).hom ≫
        CategoricalCech.differential U (K.X degree) first =
      ((CategoricalCech.complex U K.asFunctor).d first (first + 1)).f degree ≫
        (PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{u} R)
            (ComplexShape.up ℤ) degree)
          fun other : Fin (first + 2) → I =>
            K.asFunctor.obj (op (CechCochains.inter U other))).hom := by
  apply Pi.hom_ext (f := fun other : Fin (first + 2) → I =>
    (K.X degree).obj (op (CechCochains.inter U other)))
  intro other
  have left : ((PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{u} R)
            (ComplexShape.up ℤ) degree)
          fun tuple : Fin (first + 1) → I =>
            K.asFunctor.obj (op (CechCochains.inter U tuple))).hom ≫
          CategoricalCech.differential U (K.X degree) first) ≫
        Pi.π (fun tuple : Fin (first + 2) → I =>
          (K.X degree).obj (op (CechCochains.inter U tuple))) other =
      ∑ vertex : Fin (first + 2), (-1 : ℤ) ^ (vertex : ℕ) •
        ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) degree).map
            (Pi.π (fun tuple : Fin (first + 1) → I =>
              K.asFunctor.obj (op (CechCochains.inter U tuple))) (other ∘ vertex.succAbove)) ≫
          (K.X degree).map (homOfLE (CechCochains.inter_le_omit U other vertex)).op) := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun morphism =>
      (PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.up ℤ) degree)
        (fun tuple : Fin (first + 1) → I =>
          K.asFunctor.obj (op (CechCochains.inter U tuple)))).hom ≫ morphism)
      (CategoricalCech.differential_π U (K.X degree) first other)).trans ?_
    refine (Preadditive.comp_sum _ _ _).trans (Finset.sum_congr rfl fun vertex _ => ?_)
    refine (Preadditive.comp_zsmul _ _ _).trans ?_
    refine congrArg (fun morphism => (-1 : ℤ) ^ (vertex : ℕ) • morphism) ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (fun morphism => morphism ≫
      (K.X degree).map (homOfLE (CechCochains.inter_le_omit U other vertex)).op)
      (piComparison_comp_π (HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.up ℤ) degree)
        (fun tuple : Fin (first + 1) → I => K.asFunctor.obj (op (CechCochains.inter U tuple)))
        (other ∘ vertex.succAbove))
  have source : (CategoricalCech.complex U K.asFunctor).d first (first + 1) ≫
        Pi.π (fun tuple : Fin (first + 2) → I =>
          K.asFunctor.obj (op (CechCochains.inter U tuple))) other =
      ∑ vertex : Fin (first + 2), (-1 : ℤ) ^ (vertex : ℕ) •
        (Pi.π (fun tuple : Fin (first + 1) → I =>
            K.asFunctor.obj (op (CechCochains.inter U tuple))) (other ∘ vertex.succAbove) ≫
          K.asFunctor.map (homOfLE (CechCochains.inter_le_omit U other vertex)).op) := by
    rw [show (CategoricalCech.complex U K.asFunctor).d first (first + 1) =
      CategoricalCech.differential U K.asFunctor first by
        simp [CategoricalCech.complex, CochainComplex.of_d]]
    exact CategoricalCech.differential_π U K.asFunctor first other
  have right : (((CategoricalCech.complex U K.asFunctor).d first (first + 1)).f degree ≫
          (PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{u} R)
              (ComplexShape.up ℤ) degree)
            fun tuple : Fin (first + 2) → I =>
              K.asFunctor.obj (op (CechCochains.inter U tuple))).hom) ≫
        Pi.π (fun tuple : Fin (first + 2) → I =>
          (K.X degree).obj (op (CechCochains.inter U tuple))) other =
      ∑ vertex : Fin (first + 2), (-1 : ℤ) ^ (vertex : ℕ) •
        ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) degree).map
            (Pi.π (fun tuple : Fin (first + 1) → I =>
              K.asFunctor.obj (op (CechCochains.inter U tuple))) (other ∘ vertex.succAbove)) ≫
          (K.X degree).map (homOfLE (CechCochains.inter_le_omit U other vertex)).op) := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun morphism =>
      ((CategoricalCech.complex U K.asFunctor).d first (first + 1)).f degree ≫ morphism)
      (piComparison_comp_π (HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.up ℤ) degree)
        (fun tuple : Fin (first + 2) → I =>
          K.asFunctor.obj (op (CechCochains.inter U tuple))) other)).trans ?_
    refine (congrArg (HomologicalComplex.eval (ModuleCat.{u} R)
      (ComplexShape.up ℤ) degree).map source).trans ?_
    rw [Functor.map_sum]
    simp only [Functor.map_zsmul, Functor.map_comp]
    exact Finset.sum_congr rfl fun _ _ => rfl
  exact left.trans right.symm

omit [LinearOrder I] in
/-- In each degree, the comparison isomorphism `componentIso` commutes with the Cech
differential. -/
private lemma comparison_square (first : ℕ) (degree : ℤ) :
    (componentIso U K first degree).hom ≫
        ((CategoryTheory.cechComplexFunctor U).obj (K.X degree)).d first (first + 1) =
      ((CategoricalCech.complex U K.asFunctor).d first (first + 1)).f degree ≫
        (componentIso U K (first + 1) degree).hom := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun morphism =>
    (PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{u} R)
      (ComplexShape.up ℤ) degree) (fun other : Fin (first + 1) → I =>
        K.asFunctor.obj (op (CechCochains.inter U other)))).hom ≫ morphism)
    (CategoricalCech.objectIso_comm U (K.X degree) first)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun morphism =>
    morphism ≫ (CategoricalCech.objectIso U (K.X degree) (first + 1)).hom)
    (comparison_differential U K first degree)).trans ?_
  exact Category.assoc _ _ _

private def bicomplexNatIso : bicomplexNat U K ≅ usualBicomplexNat U K :=
  HomologicalComplex.Hom.isoOfComponents (columnIso U K) (by
    intro first second relation
    obtain rfl : first + 1 = second := relation
    exact HomologicalComplex.Hom.ext (funext (comparison_square U K first)))

end CechTotalization

private noncomputable def extendFlipComponentIso
    {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    {J : Type*} (shape : ComplexShape J)
    (double : HomologicalComplex₂ C shape (ComplexShape.up ℕ))
    (position : Option ℕ) (index : J) :
    (HomologicalComplex.extend.X double.flip position).X index ≅
      HomologicalComplex.extend.X (double.X index) position :=
  match position with
  | some _ => Iso.refl _
  | none => IsZero.iso
      ((HomologicalComplex.eval C shape index).map_isZero (isZero_zero _))
      (isZero_zero _)

private lemma extendFlipComponentIso_comm
    {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    {J : Type*} (shape : ComplexShape J)
    (double : HomologicalComplex₂ C shape (ComplexShape.up ℕ))
    (position : Option ℕ) (first second : J) :
    (extendFlipComponentIso shape double position first).hom ≫
        HomologicalComplex.extend.mapX (double.d first second) position =
      (HomologicalComplex.extend.X double.flip position).d first second ≫
        (extendFlipComponentIso shape double position second).hom := by
  cases position with
  | none =>
    exact ((HomologicalComplex.eval C shape first).map_isZero
      (isZero_zero _)).eq_of_src _ _
  | some position => simp [extendFlipComponentIso, HomologicalComplex.extend.X,
      HomologicalComplex.extend.mapX, HomologicalComplex₂.flip]

private def extendFlipColumnIso {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    {J : Type*} (shape : ComplexShape J)
    (double : HomologicalComplex₂ C shape (ComplexShape.up ℕ)) (degree : ℤ) :
    (double.flip.extend ComplexShape.embeddingUpNat).X degree ≅
      (HomologicalComplex₂.flip
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex shape).obj
          double)).X degree :=
  HomologicalComplex.Hom.isoOfComponents
    (fun index => extendFlipComponentIso shape double
      (ComplexShape.embeddingUpNat.r degree) index)
    fun first second _ => extendFlipComponentIso_comm shape double
      (ComplexShape.embeddingUpNat.r degree) first second

private lemma extendFlipComponentIso_d_comm
    {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    {J : Type*} (shape : ComplexShape J)
    (double : HomologicalComplex₂ C shape (ComplexShape.up ℕ))
    (first second : Option ℕ) (index : J) :
    (extendFlipComponentIso shape double first index).hom ≫
        HomologicalComplex.extend.d (double.X index) first second =
      (HomologicalComplex.extend.d double.flip first second).f index ≫
        (extendFlipComponentIso shape double second index).hom := by
  cases first with
  | none =>
    exact ((HomologicalComplex.eval C shape index).map_isZero
      (isZero_zero _)).eq_of_src _ _
  | some first =>
    cases second with
    | none => exact (isZero_zero C).eq_of_tgt _ _
    | some second => simp [extendFlipComponentIso, HomologicalComplex.extend.d,
        HomologicalComplex.extend.X, HomologicalComplex₂.flip]

private def extendFlipIso {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    {J : Type*} (shape : ComplexShape J)
    (double : HomologicalComplex₂ C shape (ComplexShape.up ℕ)) :
    double.flip.extend ComplexShape.embeddingUpNat ≅
      HomologicalComplex₂.flip
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex shape).obj
          double) :=
  HomologicalComplex.Hom.isoOfComponents (extendFlipColumnIso shape double)
    fun first second _ => HomologicalComplex.Hom.ext (funext fun degree =>
      extendFlipComponentIso_d_comm shape double
        (ComplexShape.embeddingUpNat.r first) (ComplexShape.embeddingUpNat.r second) degree)

private alias acyclic_of_homotopyEquiv :=
  Stacks.DerivedHom.KFlatHomComplex.acyclic_of_homotopyEquiv

private noncomputable def tensorHomotopyEquiv0FMQ {R : Type u} [CommRing R]
    {K₁ K₂ L₁ L₂ : CochainComplex (ModuleCat.{u} R) ℤ}
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (K₁ ⊗ K₂) (L₁ ⊗ L₂) where
  hom := e₁.hom ⊗ₘ e₂.hom
  inv := e₁.inv ⊗ₘ e₂.inv
  homotopyHomInvId := by
    rw [tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId
        (e₂.hom ≫ e₂.inv) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K₁) e₂.homotopyHomInvId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (id_tensorHom_id K₁ K₂)))
  homotopyInvHomId := by
    rw [tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId
        (e₂.inv ≫ e₂.hom) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 L₁) e₂.homotopyInvHomId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (id_tensorHom_id L₁ L₂)))

private alias kFlat_of_homotopyEquiv :=
  Stacks.DerivedHom.KFlatHomComplex.kFlat_of_homotopyEquiv

private lemma kFlat_of_bounded_idempotent {R : Type u} [CommRing R]
    (complex : CochainComplex (ModuleCat.{u} R) ℤ)
    (projection : complex ⟶ complex) (idempotent : projection ≫ projection = projection)
    (homotopy : Homotopy projection (𝟙 complex)) (bound : ℤ)
    (vanishing : ∀ degree, bound < degree → projection.f degree = 0)
    (flatness : ∀ degree, Module.Flat R (complex.X degree)) : complex.KFlat := by
  obtain ⟨image, inclusion, retraction, split, factorization⟩ :=
    IsIdempotentComplete.idempotents_split complex projection idempotent
  have componentSplit (degree : ℤ) : inclusion.f degree ≫ retraction.f degree = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun morphism => morphism.f degree) split
  have componentFactorization (degree : ℤ) :
      retraction.f degree ≫ inclusion.f degree = projection.f degree := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun morphism => morphism.f degree) factorization
  have imageFlat (degree : ℤ) : Module.Flat R (image.X degree) := by
    have := flatness degree
    exact Module.Flat.of_retract (inclusion.f degree).hom (retraction.f degree).hom
      (congrArg ModuleCat.Hom.hom (componentSplit degree))
  have imageBounded : image.IsStrictlyLE bound := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro degree beyond
    rw [IsZero.iff_id_eq_zero]
    calc
      𝟙 (image.X degree) = inclusion.f degree ≫ projection.f degree ≫
          retraction.f degree := by
        simp only [← componentFactorization degree, ← Category.assoc,
          componentSplit degree, Category.id_comp]
      _ = 0 := by rw [vanishing degree beyond, zero_comp, comp_zero]
  let equivalence : HomotopyEquiv image complex :=
    ⟨inclusion, retraction, Homotopy.ofEq split,
      (Homotopy.ofEq factorization).trans homotopy⟩
  exact kFlat_of_homotopyEquiv equivalence
    (CochainComplex.KFlat.kFlat_of_flat image bound)

private lemma extendMap_f_eq_zero_of_le {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] {K L : CochainComplex C ℕ} (φ : K ⟶ L) (N : ℕ)
    (hφ : ∀ n, N ≤ n → φ.f n = 0) (m : ℤ) (hm : (N : ℤ) ≤ m) :
    (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat).f m = 0 := by
  by_cases h : ∃ n, ComplexShape.embeddingUpNat.f n = m
  · obtain ⟨n, hn⟩ := h
    have hN : N ≤ n := by
      change (n : ℤ) = m at hn
      omega
    rw [HomologicalComplex.extendMap_f φ _ hn, hφ n hN, zero_comp, comp_zero]
  · exact HomologicalComplex.extendMap_f_eq_zero φ _ m fun n hn => h ⟨n, hn⟩

private lemma total_map_f_eq_zero_of_lt {C : Type*} [Category* C] [Preadditive C]
    {K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] (φ : K ⟶ K) (N b : ℤ) (hφ : ∀ p, N < p → φ.f p = 0)
    (hK : ∀ p q, b < q → IsZero ((K.X p).X q)) (n : ℤ) (hn : N + b < n) :
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rw [HomologicalComplex₂.ιTotal_map]
  by_cases hq : b < q
  · exact (hK p q hq).eq_of_src _ _
  · have hp : N < p := by
      change p + q = n at hpq
      omega
    simp only [hφ p hp, HomologicalComplex.zero_f, zero_comp, comp_zero]

private lemma kFlat_total_extend_of_idempotent {R : Type u} [CommRing R]
    (natural : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℤ))
    (φ : natural ⟶ natural) (idempotent : φ ≫ φ = φ) (homotopy : Homotopy (𝟙 natural) φ)
    (N : ℕ) (vanishing : ∀ n, N ≤ n → φ.f n = 0) (b : ℤ)
    (bounded : ∀ p q, b < q → IsZero (((natural.extend ComplexShape.embeddingUpNat).X p).X q))
    (flatness : ∀ n, Module.Flat R ((HomologicalComplex₂.total
      (natural.extend ComplexShape.embeddingUpNat) (ComplexShape.up ℤ)).X n)) :
    CochainComplex.KFlat.{u, u} (HomologicalComplex₂.total
      (natural.extend ComplexShape.embeddingUpNat) (ComplexShape.up ℤ)) := by
  have extendedHomotopy : Homotopy (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
      (𝟙 _) := by
    simpa only [HomologicalComplex.extendMap_id] using
      homotopy.symm.extend ComplexShape.embeddingUpNat
  refine kFlat_of_bounded_idempotent _ (HomologicalComplex₂.total.map
    (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) (ComplexShape.up ℤ)) ?_ ?_
    ((N : ℤ) + b) (total_map_f_eq_zero_of_lt _ N b
      (fun p hp => extendMap_f_eq_zero_of_le φ N vanishing p hp.le) bounded) flatness
  · rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex.extendMap_comp, idempotent]
  · simpa only [HomologicalComplex₂.total.map_id] using
      HomologicalComplex₂.totalMapHomotopy₁ extendedHomotopy (ComplexShape.up ℤ)

/-- **Stacks 0FMQ.** Let `f : X ⟶ S` be a morphism of schemes with `S` affine and
`A = Γ(S, 𝒪_S)`, and let `U : I → X.Opens` be a finite family of opens all of whose
finite intersections are affine. Let `K` be a bounded complex of presheaves of `A`-modules
on `X` whose degree-`n` term is the presheaf of sections of a quasi-coherent `𝒪_X`-module
`F n` that is flat over `S`. Then `Tot(Č^•(𝒰, K))` is K-flat as a complex of `A`-modules. -/
@[stacks 0FMQ]
public theorem kFlat_totalCechComplex {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    {I : Type u} [Finite I] (U : I → X.Opens)
    (haffine : ∀ (p : ℕ) (s : Fin (p + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (K : CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{u} ↑Γ(S, ⊤)) ℤ) (a b : ℤ)
    [CochainComplex.IsStrictlyGE K a] [CochainComplex.IsStrictlyLE K b]
    (F : ℤ → X.Modules) (hqc : ∀ n, (F n).IsQuasicoherent)
    (hflat : ∀ n, IsFlatOver f.toLRSHom.toShHom (F n))
    (hterm : ∀ n, K.X n ≅ sectionsPresheaf f (F n)) :
    CochainComplex.KFlat.{u, u} ((totalCechComplex U).obj K) := by
  classical
  let := Fintype.ofFinite I
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I)
    (Fintype.equivFin I).injective
  let : (CategoryTheory.cechComplexFunctor
      (A := ModuleCat.{u} ↑Γ(S, ⊤)) U).PreservesZeroMorphisms :=
    ⟨fun first second => cechComplexFunctor_map_zero U first second⟩
  let : (cechComplexInt (R := ↑Γ(S, ⊤)) U).PreservesZeroMorphisms := by
    dsimp [cechComplexInt]
    infer_instance
  let natural := CechTotalization.bicomplexNat U K
  let comparison := ((ComplexShape.embeddingUpNat.extendFunctor
      (CochainComplex (ModuleCat.{u} ↑Γ(S, ⊤)) ℤ)).mapIso
        (CechTotalization.bicomplexNatIso U K)).trans
    (extendFlipIso (ComplexShape.up ℤ)
      (((CategoryTheory.cechComplexFunctor U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))
  let totalComparison : HomologicalComplex₂.total
      (natural.extend ComplexShape.embeddingUpNat) (ComplexShape.up ℤ) ≅
        (totalCechComplex U).obj K :=
    (HomologicalComplex₂.totalFunctor (ModuleCat.{u} ↑Γ(S, ⊤)) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapIso comparison
  refine CochainComplex.KFlat.of_iso totalComparison
    (kFlat_total_extend_of_idempotent natural (CategoricalCech.sortingMap U K.asFunctor)
      ?_ (CategoricalCech.sortingHomotopy U K.asFunctor) (Nat.card I)
      (CategoricalCech.sorting_eq_zero U K.asFunctor) b ?_ ?_)
  · exact HomologicalComplex.Hom.ext (funext (CategoricalCech.sorting_idempotent U K.asFunctor))
  · intro first second secondBound
    have actualZero : IsZero ((((cechDoubleComplex U).obj K).X first).X second) :=
      ((cechComplexInt U) ⋙ HomologicalComplex.eval _ _ first).map_isZero
        (K.isZero_of_isStrictlyLE b second secondBound)
    exact actualZero.of_iso
      ((HomologicalComplex.eval (ModuleCat.{u} ↑Γ(S, ⊤)) (ComplexShape.up ℤ) second).mapIso
        ((HomologicalComplex.eval _ (ComplexShape.up ℤ) first).mapIso comparison))
  · intro degree
    have := totalCech_term_flat f U haffine K F hqc hflat hterm degree
    let equivalence : _ ≃ₗ[↑Γ(S, ⊤)] (((totalCechComplex U).obj K).X degree) :=
      ((HomologicalComplex.eval (ModuleCat.{u} ↑Γ(S, ⊤))
        (ComplexShape.up ℤ) degree).mapIso totalComparison).toLinearEquiv
    exact Module.Flat.of_linearEquiv equivalence

end AlgebraicGeometry

end

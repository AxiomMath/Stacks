module

public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingComposition.Factorizations

/-!
# Trace maps between relative dualizing modules

The composition map for relative dualizing modules is assembled from three elementary moves on
the module `ω_{B/A} = Hom_A(B', A) ⊗_{B'} B` attached to a finite-open factorization
`A → B' → B`: composing the `A`-linear functional with a functional on a smaller base,
transporting the construction along an isomorphism of the target, and restricting a functional
along a map of intermediate algebras. This file constructs those maps and records how each
interacts with the canonical comparison of two finite-open factorizations.

## Main definitions

* `Stacks.Discriminant.dualizingModule.dualComp` composes an `A`-linear functional on `R` with
  an `R`-linear functional.
* `Stacks.Discriminant.dualizingModule.surjectiveRestriction` restricts functionals along a
  surjection of intermediate algebras.
* `Stacks.Discriminant.dualizingModule.finiteTrace` is the resulting map from the relative
  dualizing module over a finite base extension to the one over the base.
* `Stacks.Discriminant.dualizingModule.retargetDualizingMap` transports the relative dualizing
  module along an isomorphism of the target.

## Main results

* `Stacks.Discriminant.dualizingModule.comparison_tmul_of_injective` and
  `Stacks.Discriminant.dualizingModule.comparison_tmul_of_surjective` compute the canonical
  comparison on pure tensors when the two intermediate algebras are related by an injection
  into the target or by a surjection.
* `Stacks.Discriminant.dualizingModule.finiteTrace_naturality` and
  `Stacks.Discriminant.dualizingModule.retargetDualizingMap_naturality`: both maps commute with
  the canonical comparison.

## Implementation notes

Each naturality statement is proved by reducing to pure tensors over a common refinement of the
two factorizations, where the comparison is computed by restriction of functionals. That is why
`comparison_induction` is phrased as an induction principle over such a refinement rather than
over arbitrary pure tensors.

## References

* [Stacks Project, Tag 0BT4](https://stacks.math.columbia.edu/tag/0BT4)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y z

namespace Stacks.Discriminant

namespace dualizingModule

attribute [local instance] algebraDualModule

/-- The canonical comparison of relative dualizing modules is transitive, applied to an
element. -/
lemma comparison_trans_apply
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{u, v, y} A B)
    (H : FiniteOpenFactorization.{u, v, z} A B)
    (ω : dualizingModule F) :
    dualizingModuleEquiv G H (dualizingModuleEquiv F G ω) =
      dualizingModuleEquiv F H ω :=
  congrArg (fun e : dualizingModule F ≃ₗ[B] dualizingModule H => e ω)
    (dualizingModuleEquiv_trans F G H)

/-- When the intermediate algebra of `G` maps injectively to the target and receives `F`'s,
the canonical comparison `G → F` restricts a functional along that map. -/
lemma comparison_tmul_of_injective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (hG : Function.Injective (algebraMap G.middle B))
    (r : F.middle →ₐ[A] G.middle)
    (hr : ∀ t, algebraMap G.middle B (r t) = algebraMap F.middle B t)
    (f : Module.Dual A G.middle) (b : B) :
    dualizingModuleEquiv G F (dualizingModule.tmul G f b) =
      dualizingModule.tmul F (f.comp r.toLinearMap) b := by
  simpa using dualizingModuleEquiv_tmul G F G hG
    (AlgHom.id A G.middle) r (fun _ => rfl) hr f b

/-- To prove a property of every element of a relative dualizing module it suffices to treat
zero, sums, and the pure tensors coming from a refinement with injective structure map. -/
lemma comparison_induction
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (hG : Function.Injective (algebraMap G.middle B))
    (r : F.middle →ₐ[A] G.middle)
    (hr : ∀ t, algebraMap G.middle B (r t) = algebraMap F.middle B t)
    {P : dualizingModule F → Prop}
    (hzero : P 0)
    (htmul : ∀ (f : Module.Dual A G.middle) b,
      P (dualizingModule.tmul F (f.comp r.toLinearMap) b))
    (hadd : ∀ m n, P m → P n → P (m + n))
    (m : dualizingModule F) : P m := by
  obtain ⟨n, rfl⟩ := (dualizingModuleEquiv G F).surjective m
  induction n using dualizingModule.induction_on G with
  | zero => simpa only [map_zero] using hzero
  | add m n hm hn => simpa only [map_add] using hadd _ _ hm hn
  | tmul f b =>
    rw [comparison_tmul_of_injective F G hG r hr]
    exact htmul f b

/-- Composing an `A`-linear functional on `R` with an `R`-linear functional on `S` gives an
`A`-linear functional on `S`, linearly in the second functional. -/
def dualComp
    {A : Type u} {R : Type v} {S : Type w}
    [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    (f : Module.Dual A R) : Module.Dual R S →ₗ[S] Module.Dual A S where
  toFun g := f.comp (g.restrictScalars A)
  map_add' g h := by ext t; simp
  map_smul' s g := by ext t; rfl

/-- Reading a finite-open factorization over two successively smaller bases gives the same
relative dualizing module, and the canonical comparison between the two readings carries a
pure tensor to the pure tensor of the same functional. -/
lemma comparison_tmul_restrictBaseFactorization_trans
    {A : Type u} {R : Type v} {S : Type w} {C : Type x}
    [CommRing A] [CommRing R] [CommRing S] [CommRing C]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    [Algebra S C] [Algebra R C] [Algebra A C]
    [IsScalarTower R S C] [IsScalarTower A R C] [IsScalarTower A S C]
    [Module.Finite A R] [Module.Finite R S] [Module.Finite A S]
    [IsNoetherianRing A]
    (K : FiniteOpenFactorization.{w, x, y} S C)
    (hK : Function.Injective (algebraMap K.middle C)) :
    let KR := restrictBaseFactorization (A := R) K
    let JR := restrictBaseFactorization (A := A) KR
    let JS := restrictBaseFactorization (A := A) K
    ∀ (fR : Module.Dual A JR.middle) (fS : Module.Dual A JS.middle)
      (_hf : ∀ t, fR t = fS t) (c : C),
      dualizingModuleEquiv JR JS (dualizingModule.tmul JR fR c) =
        dualizingModule.tmul JS fS c := by
  dsimp only
  let KR := restrictBaseFactorization (A := R) K
  let JR := restrictBaseFactorization (A := A) KR
  let JS := restrictBaseFactorization (A := A) K
  intro fR fS hf c
  let r : JR.middle →ₐ[A] JS.middle := {
    (RingHom.id K.middle) with
    commutes' := fun a => by
      change algebraMap S K.middle (algebraMap R S (algebraMap A R a)) =
        algebraMap S K.middle (algebraMap A S a)
      rw [← IsScalarTower.algebraMap_apply A R S] }
  have hf' : fR = fS.comp r.toLinearMap :=
    DFunLike.ext _ _ hf
  rw [hf']
  simpa using dualizingModuleEquiv_tmul JR JS JS hK r (AlgHom.id A JS.middle)
    (fun _ => rfl) (fun _ => rfl) fS c

/-- Restriction of functionals along a surjection of intermediate algebras, as a linear map
of relative dualizing modules. -/
noncomputable def surjectiveRestriction
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] G.middle) (hr : Function.Surjective r)
    (hB : ∀ t, algebraMap G.middle B (r t) = algebraMap F.middle B t) :
    dualizingModule G →ₗ[B] dualizingModule F := by
  let M := dualizingModule F
  letI : Module G.middle M := Module.compHom _ (algebraMap G.middle B)
  letI : IsScalarTower G.middle B M := IsScalarTower.of_compHom G.middle B M
  let l : Module.Dual A G.middle →ₗ[G.middle] M := {
    toFun := fun f => dualizingModule.tmul F (f.comp r.toLinearMap) 1
    map_add' := fun f g => by
      change ((f + g).comp r.toLinearMap) ⊗ₜ[F.middle] (1 : B) = _
      rw [LinearMap.add_comp, TensorProduct.add_tmul]
      rfl
    map_smul' := fun t f => by
      obtain ⟨s, rfl⟩ := hr t
      have hf : (r s • f).comp r.toLinearMap = s • (f.comp r.toLinearMap) := by
        ext t
        change f (r s * r t) = f (r (s * t))
        exact congrArg f (r.map_mul s t).symm
      rw [hf]
      change (s • f.comp r.toLinearMap) ⊗ₜ[F.middle] (1 : B) =
        algebraMap G.middle B (r s) • dualizingModule.tmul F (f.comp r.toLinearMap) 1
      rw [TensorProduct.smul_tmul, dualizingModule.smul_tmul, hB,
        Algebra.smul_def]
      rfl }
  exact (l.liftBaseChange B).comp
    (_root_.Stacks.Discriminant.dualizingModuleCommEquiv G).toLinearMap

/-- Restriction along a surjection of intermediate algebras acts on pure tensors by
restricting the functional. -/
lemma surjectiveRestriction_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] G.middle) (hr : Function.Surjective r)
    (hB : ∀ t, algebraMap G.middle B (r t) = algebraMap F.middle B t)
    (f : Module.Dual A G.middle) (b : B) :
    surjectiveRestriction F G r hr hB (dualizingModule.tmul G f b) =
      dualizingModule.tmul F (f.comp r.toLinearMap) b := by
  change b • dualizingModule.tmul F (f.comp r.toLinearMap) 1 = _
  rw [dualizingModule.smul_tmul, mul_one]

/-- When the intermediate algebra of `F` is a quotient of that of `G`, the canonical
comparison `G → F` restricts a functional along the quotient map. -/
lemma comparison_tmul_of_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] G.middle) (hr : Function.Surjective r)
    (hB : ∀ t, algebraMap G.middle B (r t) = algebraMap F.middle B t)
    (f : Module.Dual A G.middle) (b : B) :
    dualizingModuleEquiv G F (dualizingModule.tmul G f b) =
      dualizingModule.tmul F (f.comp r.toLinearMap) b := by
  have he : (dualizingModuleEquiv G F).toLinearMap =
      surjectiveRestriction F G r hr hB := by
    obtain ⟨H, rG, _, hH, hG, _⟩ := exists_common_finite_open_factorization G G
    let rF := rG.comp r
    have hF (t : F.middle) : algebraMap H.middle B (rF t) = algebraMap F.middle B t :=
      (hG (r t)).trans (hB t)
    ext m
    induction m using comparison_induction G H hH rG hG with
    | hzero => simp only [map_zero]
    | hadd m n hm hn => simp only [map_add, hm, hn]
    | htmul g c =>
      change dualizingModuleEquiv G F
        (dualizingModule.tmul G (g.comp rG.toLinearMap) c) = _
      rw [dualizingModuleEquiv_tmul G F H hH rG rF hG hF,
        surjectiveRestriction_tmul]
      rfl
  exact (LinearMap.congr_fun he _).trans (surjectiveRestriction_tmul F G r hr hB f b)

/-- Composing with a fixed `A`-linear functional on a finite `A`-algebra `R` turns the
relative dualizing module over `R` into the one over `A`. -/
noncomputable def finiteTrace
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C]
    [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R]
    (K : FiniteOpenFactorization.{v, w, x} R C) (f : Module.Dual A R) :
    dualizingModule K →ₗ[C]
      dualizingModule (restrictBaseFactorization (A := A) K) := by
  letI : Algebra A K.middle := ((algebraMap R K.middle).comp (algebraMap A R)).toAlgebra
  letI : IsScalarTower A R K.middle := IsScalarTower.of_algebraMap_eq' rfl
  exact (_root_.Stacks.Discriminant.dualizingModuleCommEquiv
      (restrictBaseFactorization (A := A) K)).symm.toLinearMap.comp
    ((TensorProduct.AlgebraTensorModule.lTensor C C (dualComp (S := K.middle) f)).comp
      (_root_.Stacks.Discriminant.dualizingModuleCommEquiv K).toLinearMap)

/-- The finite trace map acts on pure tensors by composing the functionals. -/
lemma finiteTrace_tmul
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C]
    [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R]
    (K : FiniteOpenFactorization.{v, w, x} R C) (f : Module.Dual A R)
    (g : Module.Dual R K.middle) (c : C) :
    letI : Algebra A K.middle := ((algebraMap R K.middle).comp (algebraMap A R)).toAlgebra
    letI : IsScalarTower A R K.middle := IsScalarTower.of_algebraMap_eq' rfl
    finiteTrace K f (dualizingModule.tmul K g c) =
      dualizingModule.tmul (restrictBaseFactorization K) (dualComp (S := K.middle) f g) c := by
  let : Algebra A K.middle := ((algebraMap R K.middle).comp (algebraMap A R)).toAlgebra
  let : IsScalarTower A R K.middle := IsScalarTower.of_algebraMap_eq' rfl
  change (TensorProduct.comm K.middle (Module.Dual A K.middle) C).symm
    ((dualComp (S := K.middle) f).lTensor C
      ((TensorProduct.comm K.middle (Module.Dual R K.middle) C) (g ⊗ₜ[K.middle] c))) = _
  simp [dualizingModule.tmul]

/-- The finite trace map is additive in the functional on the finite algebra. -/
lemma finiteTrace_add
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C]
    [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R]
    (K : FiniteOpenFactorization.{v, w, x} R C) (f h : Module.Dual A R) :
    finiteTrace K (f + h) = finiteTrace K f + finiteTrace K h := by
  let : Algebra A K.middle := ((algebraMap R K.middle).comp (algebraMap A R)).toAlgebra
  let : IsScalarTower A R K.middle := IsScalarTower.of_algebraMap_eq' rfl
  apply LinearMap.ext
  intro m
  induction m using dualizingModule.induction_on K with
  | zero => simp
  | add m n hm hn => simp only [map_add, LinearMap.add_apply, hm, hn]
  | tmul g c =>
    simp only [LinearMap.add_apply]
    change finiteTrace K (f + h) (dualizingModule.tmul K g c) = _
    simp only [finiteTrace_tmul]
    change (dualComp (f + h) g) ⊗ₜ[K.middle] c =
      (dualComp f g) ⊗ₜ[K.middle] c + (dualComp h g) ⊗ₜ[K.middle] c
    rw [show dualComp (f + h) g = dualComp f g + dualComp h g by rfl,
      TensorProduct.add_tmul]

/-- The finite trace map is linear in the functional on the finite algebra. -/
lemma finiteTrace_smul
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C]
    [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R]
    (K : FiniteOpenFactorization.{v, w, x} R C) (r : R) (f : Module.Dual A R) :
    finiteTrace K (r • f) = algebraMap R C r • finiteTrace K f := by
  let : Algebra A K.middle := ((algebraMap R K.middle).comp (algebraMap A R)).toAlgebra
  let : IsScalarTower A R K.middle := IsScalarTower.of_algebraMap_eq' rfl
  apply LinearMap.ext
  intro m
  induction m using dualizingModule.induction_on K with
  | zero => simp
  | add m n hm hn => simp only [map_add, LinearMap.smul_apply, hm, hn]
  | tmul g c =>
    change finiteTrace K (r • f) (dualizingModule.tmul K g c) = _
    simp only [finiteTrace_tmul, LinearMap.smul_apply]
    rw [dualizingModule.smul_tmul]
    have hd : dualComp (S := K.middle) (r • f) g =
        algebraMap R K.middle r • dualComp (S := K.middle) f g := by
      ext t
      change f (r * g t) = f (g (algebraMap R K.middle r * t))
      rw [← Algebra.smul_def, map_smul, smul_eq_mul]
    change dualComp (S := K.middle) (r • f) g ⊗ₜ[K.middle] c =
      dualComp (S := K.middle) f g ⊗ₜ[K.middle] (algebraMap R C r * c)
    rw [hd, TensorProduct.smul_tmul, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply R K.middle C]

/-- The finite trace map commutes with the canonical comparison of finite-open
factorizations. -/
lemma finiteTrace_naturality
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C]
    [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing A] [IsNoetherianRing R]
    (K : FiniteOpenFactorization.{v, w, x} R C)
    (L : FiniteOpenFactorization.{v, w, y} R C)
    (f : Module.Dual A R) (m : dualizingModule K) :
    finiteTrace L f (dualizingModuleEquiv K L m) =
      dualizingModuleEquiv
        (restrictBaseFactorization (A := A) K) (restrictBaseFactorization (A := A) L)
        (finiteTrace K f m) := by
  obtain ⟨T, rK, rL, hT, hK, hL⟩ := exists_common_finite_open_factorization K L
  let : Algebra A K.middle := ((algebraMap R K.middle).comp (algebraMap A R)).toAlgebra
  let : Algebra A L.middle := ((algebraMap R L.middle).comp (algebraMap A R)).toAlgebra
  let : Algebra A T.middle := ((algebraMap R T.middle).comp (algebraMap A R)).toAlgebra
  let : IsScalarTower A R K.middle := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A R L.middle := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A R T.middle := IsScalarTower.of_algebraMap_eq' rfl
  induction m using comparison_induction K T hT rK hK with
  | hzero => simp only [map_zero]
  | hadd m n hm hn => simp only [map_add, hm, hn]
  | htmul g c =>
    rw [dualizingModuleEquiv_tmul K L T hT rK rL hK hL]
    rw [finiteTrace_tmul, finiteTrace_tmul]
    exact (dualizingModuleEquiv_tmul
      (restrictBaseFactorization (A := A) K) (restrictBaseFactorization (A := A) L)
      (restrictBaseFactorization (A := A) T) hT
      (rK.restrictScalars A) (rL.restrictScalars A) hK hL
      (dualComp f g) c).symm

/-- Transporting the relative dualizing module along an isomorphism of the target. -/
def retargetDualizingMap
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, v, x} A B) (e : B ≃ₐ[A] C) :
    dualizingModule F →+ dualizingModule (retargetFactorization F e) := by
  letI : Algebra F.middle C := (e.toRingHom.comp (algebraMap F.middle B)).toAlgebra
  let l : B →ₗ[F.middle] C := {
    toFun := e
    map_add' := e.map_add
    map_smul' := fun r b => by
      simp only [RingHom.id_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        RingHom.comp_apply, map_mul]
      rfl }
  exact (TensorProduct.map (LinearMap.id : Module.Dual A F.middle →ₗ[F.middle] _) l).toAddMonoidHom

/-- Transport along an isomorphism of the target acts on pure tensors by moving the
coefficient. -/
lemma retargetDualizingMap_tmul
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, v, x} A B) (e : B ≃ₐ[A] C)
    (f : Module.Dual A F.middle) (b : B) :
    retargetDualizingMap F e (dualizingModule.tmul F f b) =
      dualizingModule.tmul (retargetFactorization F e) f (e b) := by
  let : Algebra F.middle C := (e.toRingHom.comp (algebraMap F.middle B)).toAlgebra
  change TensorProduct.map _ _ (f ⊗ₜ[F.middle] b) = _
  rw [TensorProduct.map_tmul]
  rfl

/-- Transport along an isomorphism of the target is semilinear over that isomorphism. -/
lemma retargetDualizingMap_smul
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, v, x} A B) (e : B ≃ₐ[A] C)
    (b : B) (m : dualizingModule F) :
    retargetDualizingMap F e (b • m) = e b • retargetDualizingMap F e m := by
  induction m using dualizingModule.induction_on F with
  | zero => simp only [smul_zero, map_zero]
  | add m n hm hn => simp only [smul_add, map_add, hm, hn]
  | tmul f c =>
    rw [dualizingModule.smul_tmul, retargetDualizingMap_tmul,
      retargetDualizingMap_tmul, dualizingModule.smul_tmul, map_mul]

/-- Transport along an isomorphism of the target is bijective. -/
lemma retargetDualizingMap_bijective
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, v, x} A B) (e : B ≃ₐ[A] C) :
    Function.Bijective (retargetDualizingMap F e) := by
  let : Algebra F.middle C := (e.toRingHom.comp (algebraMap F.middle B)).toAlgebra
  let l : B ≃ₗ[F.middle] C := {
    e.toAddEquiv with
    map_smul' := fun r b => by
      simp only [RingHom.id_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        RingHom.comp_apply]
      exact e.map_mul _ _ }
  exact (TensorProduct.congr (LinearEquiv.refl F.middle (Module.Dual A F.middle)) l).bijective

/-- Transport along an isomorphism of the target commutes with the canonical comparison of
finite-open factorizations. -/
lemma retargetDualizingMap_naturality
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{u, v, y} A B) (e : B ≃ₐ[A] C)
    (m : dualizingModule F) :
    retargetDualizingMap G e (dualizingModuleEquiv F G m) =
      dualizingModuleEquiv (retargetFactorization F e) (retargetFactorization G e)
        (retargetDualizingMap F e m) := by
  obtain ⟨H, rF, rG, hH, hF, hG⟩ := exists_common_finite_open_factorization F G
  have hi : Function.Injective
      (algebraMap (retargetFactorization H e).middle C) := e.injective.comp hH
  have hF' (t : F.middle) :
      algebraMap (retargetFactorization H e).middle C (rF t) =
        algebraMap (retargetFactorization F e).middle C t := congrArg e (hF t)
  have hG' (t : G.middle) :
      algebraMap (retargetFactorization H e).middle C (rG t) =
        algebraMap (retargetFactorization G e).middle C t := congrArg e (hG t)
  induction m using comparison_induction F H hH rF hF with
  | hzero => simp only [map_zero]
  | hadd m n hm hn => simp only [map_add, hm, hn]
  | htmul f b =>
    rw [dualizingModuleEquiv_tmul F G H hH rF rG hF hG,
      retargetDualizingMap_tmul, retargetDualizingMap_tmul,
      dualizingModuleEquiv_tmul (retargetFactorization F e)
        (retargetFactorization G e) (retargetFactorization H e) hi rF rG hF' hG']

/-- The lift of a map along a base change is additive in that map. -/
lemma isBaseChange_lift_add
    {R S M N Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    {f : M →ₗ[R] N} (h : IsBaseChange S f) (g k : M →ₗ[R] Q) :
    h.lift (g + k) = h.lift g + h.lift k := by
  apply h.algHom_ext
  intro m
  simp only [IsBaseChange.lift_eq, LinearMap.add_apply]

/-- The lift of a map along a base change is linear in that map. -/
lemma isBaseChange_lift_smul
    {R S M N Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    {f : M →ₗ[R] N} (h : IsBaseChange S f) (r : R) (g : M →ₗ[R] Q) :
    h.lift (r • g) = r • h.lift g := by
  apply h.algHom_ext
  intro m
  simp only [IsBaseChange.lift_eq, LinearMap.smul_apply]

end dualizingModule

end Stacks.Discriminant

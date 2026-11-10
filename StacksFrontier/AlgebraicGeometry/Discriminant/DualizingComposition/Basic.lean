module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingComposition.OpenBaseChange

/-!
# Composition of relative dualizing modules

For composable quasi-finite maps `A → B → C` of Noetherian rings the tensor product of the
relative dualizing modules of `B` over `A` and of `C` over `B` maps canonically to the relative
dualizing module of `C` over `A`. This file constructs that map and proves the two properties
that characterize it: a formula on pure tensors whose functionals are compatible, and
independence of the three chosen finite-open factorizations.

The construction is a pairing. Fixing a functional `f` on the intermediate algebra of the
factorization of `B`, the relative dualizing module of `C` over `B` is the base change along
`B' → B` of the one computed over `B'`, so composing with `f` gives a map to the relative
dualizing module of `C` over `A`. Letting `f` vary and extending scalars to `B` turns this into
the required pairing.

## Main definitions

* `Stacks.Discriminant.pairingComp` postcomposes a pairing that is linear over a ring in its
  first variable and over an algebra over it in its second with a map on the target.
* `Stacks.Discriminant.dualizingModule.compositionPairing` is the pairing for three given
  finite-open factorizations.
* `Stacks.Discriminant.dualizingModule.comp` is the composition map, defined using the
  canonical factorizations so that it depends on nothing but the three algebras.

## Main results

* `Stacks.Discriminant.dualizingModule.comp_of_compatible`: when a functional on the
  intermediate algebra of the factorization of `C` over `A` descends along a compatible map to
  the one of `C` over `B`, the composition map multiplies the two functionals.
* `Stacks.Discriminant.dualizingModule.comp_naturality`: the composition map commutes with the
  canonical comparison in each of its three factorizations.

## Implementation notes

The composition map is linear over `C`; its source is regarded as a module over `B` by
restriction of scalars along `B → C`, which is why the pairing is stated with the first
argument `B`-linear and the second `C`-linear.

`comp_of_compatible` applies to maps that are not themselves finite: the hypothesis is only
that the second functional descends along a map of the chosen finite intermediate algebras
whose image spans the target.

Both `compositionPairing` and `comp` are assembled from maps whose linearity is established
elsewhere — by `traceAfterOpenBaseChangeComp` and by `pairingComp` — rather than from a
structure literal whose field goals are proved on the spot.  The `C`-module structure on
`dualizingModule F ⊗[B] dualizingModule G` is transported along `TensorProduct.comm`, and
unfolding that transport reaches the universal property of the tensor product, so any goal
stated in a context where it is in scope is far deeper than it looks; the linearity proofs are
kept out of that context.

## References

* [Stacks Project, Tag 0BT4](https://stacks.math.columbia.edu/tag/0BT4)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y z x' y' z'

namespace Stacks.Discriminant

/-- Postcomposition of a pairing `M →ₗ[B] N →ₗ[C] Z'` with a `C`-linear map `Z' →ₗ[C] Z`, where
`B` acts on both targets through `C`.

`LinearMap.compr₂` is the same construction for a scalar tower the other way round: it asks for
`Module C B`, so it does not apply to a pairing whose first variable is linear over the smaller
ring. -/
def pairingComp
    {B : Type*} {C : Type*} [CommSemiring B] [CommSemiring C] [Algebra B C]
    {M N Z Z' : Type*}
    [AddCommMonoid M] [Module B M]
    [AddCommMonoid N] [Module C N]
    [AddCommMonoid Z] [Module C Z] [Module B Z] [SMulCommClass C B Z] [IsScalarTower B C Z]
    [AddCommMonoid Z'] [Module C Z'] [Module B Z'] [SMulCommClass C B Z'] [IsScalarTower B C Z']
    (q : M →ₗ[B] N →ₗ[C] Z') (w : Z' →ₗ[C] Z) :
    M →ₗ[B] N →ₗ[C] Z where
  toFun m := w.comp (q m)
  map_add' m m' := by
    apply LinearMap.ext
    intro n
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
  map_smul' b m := by
    apply LinearMap.ext
    intro n
    simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_smul,
      LinearMap.smul_apply, ← algebraMap_smul (A := C) (R := B), map_smul]

/-- The value of `Stacks.Discriminant.pairingComp` is the value of the pairing followed by the
map on the target. -/
@[simp]
lemma pairingComp_apply
    {B : Type*} {C : Type*} [CommSemiring B] [CommSemiring C] [Algebra B C]
    {M N Z Z' : Type*}
    [AddCommMonoid M] [Module B M]
    [AddCommMonoid N] [Module C N]
    [AddCommMonoid Z] [Module C Z] [Module B Z] [SMulCommClass C B Z] [IsScalarTower B C Z]
    [AddCommMonoid Z'] [Module C Z'] [Module B Z'] [SMulCommClass C B Z'] [IsScalarTower B C Z']
    (q : M →ₗ[B] N →ₗ[C] Z') (w : Z' →ₗ[C] Z) (m : M) (n : N) :
    pairingComp q w m n = w (q m n) :=
  rfl

namespace dualizingModule

attribute [local instance] algebraDualModule

/-- The pairing of the relative dualizing module of `B` over `A` with that of `C` over `B`,
valued in the relative dualizing module of `C` over `A` computed from a given finite-open
factorization. -/
noncomputable def compositionPairing
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C) :
    letI : Module B (dualizingModule H) := Module.compHom _ (algebraMap B C)
    letI : SMulCommClass C B (dualizingModule H) :=
      ⟨fun c b m => smul_comm c (algebraMap B C b) m⟩
    dualizingModule F →ₗ[B]
      dualizingModule G →ₗ[C] dualizingModule H := by
  let : Algebra F.middle C := ((algebraMap B C).comp (algebraMap F.middle B)).toAlgebra
  let : IsScalarTower F.middle B C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A F.middle C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra,
      ← IsScalarTower.algebraMap_apply A F.middle B,
      ← IsScalarTower.algebraMap_apply A B C])
  let : IsNoetherianRing F.middle := IsNoetherianRing.of_finite A F.middle
  let : Module.Flat F.middle B := finiteOpenFactorization_flat F
  let K := compositeFiniteOpenFactorization F G
  let J := restrictBaseFactorization (A := A) K
  let N := dualizingModule G
  let P := dualizingModule H
  let : Module B P := Module.compHom _ (algebraMap B C)
  let : SMulCommClass C B P := ⟨fun c b m => smul_comm c (algebraMap B C b) m⟩
  let : Module F.middle P := Module.compHom _ (algebraMap F.middle C)
  let : SMulCommClass C F.middle P :=
    ⟨fun c r m => smul_comm c (algebraMap F.middle C r) m⟩
  let : IsScalarTower F.middle B P := IsScalarTower.of_algebraMap_smul (fun r m => rfl)
  let e := (dualizingModuleEquiv J H).toLinearMap
  let hepi := isEpi_of_finiteOpenFactorization F
  let l : Module.Dual A F.middle →ₗ[F.middle] (N →ₗ[C] P) :=
    traceAfterOpenBaseChangeComp (A := A) hepi K G e (fun _ _ => rfl)
  exact (l.liftBaseChange B).comp
    (_root_.Stacks.Discriminant.dualizingModuleCommEquiv F).toLinearMap

/-- If `R → C` factors through `B`, then `A → R → C` is a scalar tower. -/
private theorem isScalarTower_of_algebraMap_comp
    {A R B C : Type*} [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra A B] [IsScalarTower A R B]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Algebra R C]
    (h : algebraMap R C = (algebraMap B C).comp (algebraMap R B)) : IsScalarTower A R C :=
  IsScalarTower.of_algebraMap_eq' (by
    ext a
    simp only [RingHom.comp_apply, h, ← IsScalarTower.algebraMap_apply A R B,
      ← IsScalarTower.algebraMap_apply A B C])

/-- The pairing on a pure tensor in the first variable is the trace map across the open base
change, for any finite-open factorization of `C` over the intermediate algebra of `F`. -/
lemma compositionPairing_tmul
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C)
    (f : Module.Dual A F.middle) (b : B) (m : dualizingModule G) :
    letI : Algebra F.middle C := ((algebraMap B C).comp (algebraMap F.middle B)).toAlgebra
    letI : IsScalarTower F.middle B C := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A F.middle C := IsScalarTower.of_algebraMap_eq' (by
      ext a
      simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra,
        ← IsScalarTower.algebraMap_apply A F.middle B,
        ← IsScalarTower.algebraMap_apply A B C])
    letI : IsNoetherianRing F.middle := IsNoetherianRing.of_finite A F.middle
    letI : Module.Flat F.middle B := finiteOpenFactorization_flat F
    ∀ K : FiniteOpenFactorization.{x, w, x'} F.middle C,
      compositionPairing F G H (dualizingModule.tmul F f b) m =
        algebraMap B C b • dualizingModuleEquiv
          (restrictBaseFactorization (A := A) K) H
          (traceAfterOpenBaseChange (isEpi_of_finiteOpenFactorization F) K G f m) := by
  let : Algebra F.middle C := ((algebraMap B C).comp (algebraMap F.middle B)).toAlgebra
  let : IsScalarTower F.middle B C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A F.middle C := isScalarTower_of_algebraMap_comp rfl
  let : IsNoetherianRing F.middle := IsNoetherianRing.of_finite A F.middle
  let : Module.Flat F.middle B := finiteOpenFactorization_flat F
  intro K
  let K₀ := compositeFiniteOpenFactorization F G
  change algebraMap B C b • dualizingModuleEquiv
    (restrictBaseFactorization (A := A) K₀) H
    (traceAfterOpenBaseChange (isEpi_of_finiteOpenFactorization F) K₀ G f m) = _
  rw [traceAfterOpenBaseChange_naturality (isEpi_of_finiteOpenFactorization F) K₀ K G f m,
    comparison_trans_apply]

/-- The pairing is unchanged by the canonical comparison in the second variable. -/
lemma compositionPairing_naturality_right
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (G' : FiniteOpenFactorization.{v, w, y'} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C)
    (m : dualizingModule F) (n : dualizingModule G) :
    compositionPairing F G' H m (dualizingModuleEquiv G G' n) =
      compositionPairing F G H m n := by
  let : Algebra F.middle C := ((algebraMap B C).comp (algebraMap F.middle B)).toAlgebra
  let : IsScalarTower F.middle B C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A F.middle C := isScalarTower_of_algebraMap_comp rfl
  let : IsNoetherianRing F.middle := IsNoetherianRing.of_finite A F.middle
  let : Module.Flat F.middle B := finiteOpenFactorization_flat F
  let K := compositeFiniteOpenFactorization F G
  induction m using dualizingModule.induction_on F with
  | add m n hm hn => simp only [map_add, LinearMap.add_apply, hm, hn]
  | tmul f b =>
    rw [compositionPairing_tmul F G' H f b _ K, compositionPairing_tmul F G H f b n K]
    congr 2
    simp only [traceAfterOpenBaseChange, linearMapOfSemilinearComp_apply,
      retargetDualizingMap_naturality, comparison_trans_apply]

/-- The pairing is unchanged by the canonical comparison in the first variable, when the
second factorization has injective structure map and refines the first. -/
lemma compositionPairing_naturality_left_of_injective
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (F' : FiniteOpenFactorization.{u, v, x'} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C)
    (hi : Function.Injective (algebraMap F'.middle B))
    (r : F.middle →ₐ[A] F'.middle)
    (hr : ∀ t, algebraMap F'.middle B (r t) = algebraMap F.middle B t)
    (m : dualizingModule F') (n : dualizingModule G) :
    compositionPairing F G H (dualizingModuleEquiv F' F m) n =
      compositionPairing F' G H m n := by
  let R := F.middle
  let S := F'.middle
  let : Algebra R S := r.toRingHom.toAlgebra
  let : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (r.commutes a).symm)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' (by
    ext t
    exact (hr t).symm)
  let : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  let : Algebra S C := ((algebraMap B C).comp (algebraMap S B)).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower S B C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A R C := isScalarTower_of_algebraMap_comp rfl
  let : IsScalarTower A S C := isScalarTower_of_algebraMap_comp rfl
  let : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' (by
    ext t
    change algebraMap B C (algebraMap R B t) = algebraMap B C (algebraMap S B (r t))
    rw [hr])
  let : Module.Finite R S := Module.Finite.of_restrictScalars_finite A R S
  let : IsNoetherianRing R := IsNoetherianRing.of_finite A R
  let : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  let : Module.Flat R B := finiteOpenFactorization_flat F
  let : Module.Flat S B := finiteOpenFactorization_flat F'
  let hepi := isEpi_of_finiteOpenFactorization F
  let K := compositeFiniteOpenFactorization F' G
  let KR := restrictBaseFactorization (A := R) K
  let : Algebra R K.middle := KR.algebraMiddle
  let : IsScalarTower R S K.middle := IsScalarTower.of_algebraMap_eq' rfl
  have hK : Function.Injective (algebraMap K.middle C) := Subtype.val_injective
  induction m using dualizingModule.induction_on F' with
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | tmul f b =>
    rw [comparison_tmul_of_injective F F' hi r hr]
    induction n using openBaseChange_induction hepi KR G with
    | hadd m n hm hn => simp only [map_add, hm, hn]
    | hsmul c n hn => simp only [map_smul, hn]
    | htmul g c =>
      let Kb := FiniteOpenFactorization.baseChange KR B
      let G₀ := retargetFactorization Kb (tensorEpiLmulEquiv hepi)
      let j : K.middle →+* G₀.middle :=
        (Algebra.TensorProduct.includeRight : K.middle →ₐ[R] B ⊗[R] K.middle).toRingHom
      have hjR (a : R) : j (algebraMap R K.middle a) =
          algebraMap B G₀.middle (algebraMap R B a) := by
        change (1 : B) ⊗ₜ[R] algebraMap R K.middle a = algebraMap R B a ⊗ₜ[R] (1 : K.middle)
        simpa only [Algebra.smul_def, mul_one] using
          (TensorProduct.smul_tmul a (1 : B) (1 : K.middle)).symm
      have hjS (s : S) : j (algebraMap S K.middle s) =
          algebraMap B G₀.middle (algebraMap S B s) :=
        includeRight_algebraMap_of_flat_epi hepi hi s
      have hjC (t : K.middle) : algebraMap G₀.middle C (j t) = algebraMap K.middle C t := by
        change tensorEpiLmulEquiv hepi (1 ⊗ₜ[R] algebraMap K.middle C t) = _
        rw [tensorEpiLmulEquiv_tmul, map_one, one_mul]
      have hjspan : Submodule.span B (Set.range j) = ⊤ := span_range_includeRight
      have hgR (t : K.middle) : g.baseChange B (j t) = algebraMap R B (g t) := by
        change g.baseChange B (1 ⊗ₜ[R] t) = _
        rw [Module.Dual.baseChange_apply_tmul, Algebra.smul_def, mul_one]
      let gS : Module.Dual S K.middle := dualMapOfFlatEpi hepi hi g
      have hgS (t : K.middle) : g.baseChange B (j t) = algebraMap S B (gS t) := by
        change g.baseChange B (j t) = algebraMap S B (algebraMap R S (g t))
        rw [← IsScalarTower.algebraMap_apply R S B]
        exact hgR t
      rw [compositionPairing_naturality_right F G₀ G H,
        compositionPairing_naturality_right F' G₀ G H,
        compositionPairing_tmul F G₀ H (f.comp r.toLinearMap) b _ KR,
        compositionPairing_tmul F' G₀ H f b _ K,
        traceAfterOpenBaseChange_tmul_of_compatible hepi KR G₀ j hjR hjC hjspan
          (f.comp r.toLinearMap) (g.baseChange B) g hgR c,
        traceAfterOpenBaseChange_tmul_of_compatible (isEpi_of_finiteOpenFactorization F') K G₀
          j hjS hjC hjspan f (g.baseChange B) gS hgS c]
      congr 1
      rw [← comparison_trans_apply (restrictBaseFactorization (A := A) KR)
        (restrictBaseFactorization (A := A) K) H]
      congr 1
      apply comparison_tmul_restrictBaseFactorization_trans (A := A) (R := R) K hK
      intro t
      rfl

/-- The pairing is unchanged by the canonical comparison in the first variable. -/
lemma compositionPairing_naturality_left
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (F' : FiniteOpenFactorization.{u, v, x'} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C)
    (m : dualizingModule F) (n : dualizingModule G) :
    compositionPairing F' G H (dualizingModuleEquiv F F' m) n =
      compositionPairing F G H m n := by
  obtain ⟨S, rF, rF', hi, hF, hF'⟩ := exists_common_finite_open_factorization F F'
  obtain ⟨m, rfl⟩ := (dualizingModuleEquiv S F).surjective m
  rw [comparison_trans_apply,
    compositionPairing_naturality_left_of_injective F' S G H hi rF' hF',
    compositionPairing_naturality_left_of_injective F S G H hi rF hF]

/-- Changing the finite-open factorization of `C` over `A` changes the pairing by the
canonical comparison. -/
lemma compositionPairing_naturality_target
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C)
    (H' : FiniteOpenFactorization.{u, w, z'} A C)
    (m : dualizingModule F) (n : dualizingModule G) :
    compositionPairing F G H' m n =
      dualizingModuleEquiv H H' (compositionPairing F G H m n) := by
  let : Algebra F.middle C := ((algebraMap B C).comp (algebraMap F.middle B)).toAlgebra
  let : IsScalarTower F.middle B C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A F.middle C := isScalarTower_of_algebraMap_comp rfl
  let : IsNoetherianRing F.middle := IsNoetherianRing.of_finite A F.middle
  let : Module.Flat F.middle B := finiteOpenFactorization_flat F
  let K := compositeFiniteOpenFactorization F G
  induction m using dualizingModule.induction_on F with
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | tmul f b =>
    rw [compositionPairing_tmul F G H' f b n K,
      compositionPairing_tmul F G H f b n K, map_smul, comparison_trans_apply]

/-- **Stacks Project, Tag 0BT4.** The canonical composition map for relative
dualizing modules of two composable quasi-finite algebra maps. -/
@[stacks 0BT4]
noncomputable def comp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C) :
    letI : Module B (dualizingModule G) :=
      Module.compHom _ (algebraMap B C)
    letI : SMulCommClass B C (dualizingModule G) :=
      ⟨fun b c m => by
        change (algebraMap B C b) • c • m = c • (algebraMap B C b) • m
        rw [smul_comm]⟩
    letI : Module C
        (dualizingModule G ⊗[B] dualizingModule F) :=
      TensorProduct.leftModule
    letI : Module C
        (dualizingModule F ⊗[B] dualizingModule G) :=
      (TensorProduct.comm B (dualizingModule F)
        (dualizingModule G)).toAddEquiv.module C
    (dualizingModule F ⊗[B] dualizingModule G) →ₗ[C]
      dualizingModule H := by
  let : Module B (dualizingModule G) := Module.compHom _ (algebraMap B C)
  let : SMulCommClass B C (dualizingModule G) :=
    ⟨fun b c m => smul_comm (algebraMap B C b) c m⟩
  let : Module C
      (dualizingModule G ⊗[B] dualizingModule F) :=
    TensorProduct.leftModule
  let : Module C
      (dualizingModule F ⊗[B] dualizingModule G) :=
    (TensorProduct.comm B (dualizingModule F)
      (dualizingModule G)).toAddEquiv.module C
  let : IsScalarTower B C (dualizingModule G) :=
    IsScalarTower.of_compHom B C _
  let F₀ := canonicalFactorization F
  let G₀ := canonicalFactorization G
  let H₀ := canonicalFactorization H
  let P := dualizingModule H
  let P₀ := dualizingModule H₀
  let : Module B P := Module.compHom _ (algebraMap B C)
  let : IsScalarTower B C P := IsScalarTower.of_compHom B C P
  let : SMulCommClass C B P := ⟨fun c b m => smul_comm c (algebraMap B C b) m⟩
  let : Module B P₀ := Module.compHom _ (algebraMap B C)
  let : SMulCommClass C B P₀ := ⟨fun c b m => smul_comm c (algebraMap B C b) m⟩
  let eF := (dualizingModuleEquiv F F₀).toLinearMap
  let eG := (dualizingModuleEquiv G G₀).toLinearMap
  let eH := (dualizingModuleEquiv H₀ H).toLinearMap
  let : IsScalarTower B C P₀ := IsScalarTower.of_compHom B C P₀
  let q := compositionPairing F₀ G₀ H₀
  exact (TensorProduct.AlgebraTensorModule.lift
      (pairingComp ((q.comp eF).compl₂ eG) eH).flip).comp
    ((TensorProduct.comm B (dualizingModule F)
      (dualizingModule G)).toAddEquiv.linearEquiv C).toLinearMap

/-- The composition map on a pure tensor is the pairing for the canonical factorizations. -/
lemma comp_tmul
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C)
    (ω : dualizingModule F) (η : dualizingModule G) :
    letI : Module B (dualizingModule G) := Module.compHom _ (algebraMap B C)
    comp F G H (ω ⊗ₜ[B] η) =
      dualizingModuleEquiv (canonicalFactorization H) H
        (compositionPairing (canonicalFactorization F) (canonicalFactorization G)
          (canonicalFactorization H)
          (dualizingModuleEquiv F (canonicalFactorization F) ω)
          (dualizingModuleEquiv G (canonicalFactorization G) η)) := by
  rfl

/-- The composition map on a pure tensor is the pairing for the given factorizations. -/
lemma comp_tmul_eq_compositionPairing
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C)
    (m : dualizingModule F) (n : dualizingModule G) :
    letI : Module B (dualizingModule G) := Module.compHom _ (algebraMap B C)
    comp F G H (m ⊗ₜ[B] n) = compositionPairing F G H m n := by
  rw [comp_tmul, compositionPairing_naturality_left, compositionPairing_naturality_right,
    ← compositionPairing_naturality_target]

/-- For compatible finite-open factorizations, a functional on the middle
algebra that descends to the finite intermediate algebra composes with the
first functional. This applies to nonfinite quasi-finite maps as well. -/
@[stacks 0BT4 "composition of Hom maps for compatible factorizations"]
theorem comp_of_compatible
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C)
    [Algebra F.middle H.middle] [IsScalarTower A F.middle H.middle]
    (j : H.middle →+* G.middle)
    (hjF : ∀ s : F.middle,
      j (algebraMap F.middle H.middle s) =
        algebraMap B G.middle (algebraMap F.middle B s))
    (hjC : ∀ t : H.middle,
      algebraMap G.middle C (j t) = algebraMap H.middle C t)
    (hjspan : Submodule.span B (Set.range j) = ⊤)
    (f : Module.Dual A F.middle) (g : Module.Dual B G.middle)
    (g' : Module.Dual F.middle H.middle)
    (hg : ∀ t : H.middle, g (j t) = algebraMap F.middle B (g' t))
    (d : F.middle) (c : C) :
    letI : Module B (dualizingModule G) :=
      Module.compHom _ (algebraMap B C)
    letI : SMulCommClass B C (dualizingModule G) :=
      ⟨fun b c m => by
        change (algebraMap B C b) • c • m = c • (algebraMap B C b) • m
        rw [smul_comm]⟩
    letI : Module C
        (dualizingModule G ⊗[B] dualizingModule F) :=
      TensorProduct.leftModule
    letI : Module C
        (dualizingModule F ⊗[B] dualizingModule G) :=
      (TensorProduct.comm B (dualizingModule F)
        (dualizingModule G)).toAddEquiv.module C
    ∃ h : Module.Dual A H.middle,
      (comp F G H ((dualizingModule.tmul F f
          (algebraMap F.middle B d)) ⊗ₜ[B]
        (dualizingModule.tmul G g c)) =
          dualizingModule.tmul H h c) ∧
      (∀ t : H.middle,
        h t = f (d * g' t)) := by
  let : Algebra F.middle C := ((algebraMap B C).comp (algebraMap F.middle B)).toAlgebra
  let : IsScalarTower F.middle B C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A F.middle C := isScalarTower_of_algebraMap_comp rfl
  let : IsNoetherianRing F.middle := IsNoetherianRing.of_finite A F.middle
  let : Module.Flat F.middle B := finiteOpenFactorization_flat F
  have ht : IsScalarTower F.middle H.middle C := IsScalarTower.of_algebraMap_eq' (by
    ext s
    change algebraMap B C (algebraMap F.middle B s) =
      algebraMap H.middle C (algebraMap F.middle H.middle s)
    rw [IsScalarTower.algebraMap_apply B G.middle C, ← hjF, hjC])
  let K : FiniteOpenFactorization.{x, w, z} F.middle C := {
    middle := H.middle
    commRingMiddle := inferInstance
    algebraMiddle := inferInstance
    algebraTarget := H.algebraTarget
    scalarTower := ht
    finite_middle := Module.Finite.of_restrictScalars_finite A F.middle H.middle
    isOpenEmbedding_comap := H.isOpenEmbedding_comap
    awayMap_bijective := H.awayMap_bijective }
  let J := restrictBaseFactorization (A := A) K
  let rJH : J.middle →ₐ[A] H.middle := {
    (RingHom.id H.middle) with
    commutes' := fun a => by
      change algebraMap F.middle H.middle (algebraMap A F.middle a) = algebraMap A H.middle a
      rw [← IsScalarTower.algebraMap_apply A F.middle H.middle] }
  let h : Module.Dual A H.middle := (d • f).comp (g'.restrictScalars A)
  refine ⟨h, ?_, fun t => rfl⟩
  have hin : dualizingModule.tmul F f (algebraMap F.middle B d) =
      dualizingModule.tmul F (d • f) 1 := by
    change f ⊗ₜ[F.middle] algebraMap F.middle B d = (d • f) ⊗ₜ[F.middle] (1 : B)
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rw [hin, comp_tmul_eq_compositionPairing,
    compositionPairing_tmul F G H (d • f) 1 _ K,
    traceAfterOpenBaseChange_tmul_of_compatible (isEpi_of_finiteOpenFactorization F)
      K G j hjF hjC hjspan (d • f) g g' hg c, map_one, one_smul]
  apply (dualizingModuleEquiv H J).injective
  rw [comparison_trans_apply, dualizingModuleEquiv_refl,
    comparison_tmul_of_surjective J H rJH Function.surjective_id (fun _ => rfl)]
  rfl

/-- The composition map commutes with the canonical comparison isomorphisms
when any of the three finite-open factorizations is changed. -/
@[stacks 0BT4 "independence of factorization"]
theorem comp_naturality
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    (H : FiniteOpenFactorization.{u, w, z} A C)
    (F' : FiniteOpenFactorization.{u, v, x'} A B)
    (G' : FiniteOpenFactorization.{v, w, y'} B C)
    (H' : FiniteOpenFactorization.{u, w, z'} A C)
    (ω : dualizingModule F)
    (η : dualizingModule G) :
    letI : Module B (dualizingModule G) :=
      Module.compHom _ (algebraMap B C)
    letI : SMulCommClass B C (dualizingModule G) :=
      ⟨fun b c m => by
        change (algebraMap B C b) • c • m = c • (algebraMap B C b) • m
        rw [smul_comm]⟩
    letI : Module C
        (dualizingModule G ⊗[B] dualizingModule F) :=
      TensorProduct.leftModule
    letI : Module C
        (dualizingModule F ⊗[B] dualizingModule G) :=
      (TensorProduct.comm B (dualizingModule F)
        (dualizingModule G)).toAddEquiv.module C
    letI : Module B (dualizingModule G') :=
      Module.compHom _ (algebraMap B C)
    letI : SMulCommClass B C (dualizingModule G') :=
      ⟨fun b c m => by
        change (algebraMap B C b) • c • m = c • (algebraMap B C b) • m
        rw [smul_comm]⟩
    letI : Module C
        (dualizingModule G' ⊗[B] dualizingModule F') :=
      TensorProduct.leftModule
    letI : Module C
        (dualizingModule F' ⊗[B] dualizingModule G') :=
      (TensorProduct.comm B (dualizingModule F')
        (dualizingModule G')).toAddEquiv.module C
    comp F' G' H'
        ((dualizingModuleEquiv F F' ω) ⊗ₜ[B]
          (dualizingModuleEquiv G G' η)) =
      dualizingModuleEquiv H H' (comp F G H (ω ⊗ₜ[B] η)) := by
  rw [comp_tmul, comp_tmul, comparison_trans_apply, comparison_trans_apply,
    comparison_trans_apply]
  rfl

end dualizingModule

end Stacks.Discriminant

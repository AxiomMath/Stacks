module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomComplex

/-!
# Chain maps into the internal Hom complex from equivariant pairings

Let `R` be a finite ring, `Q` a compact topological group, `S` a ring and `φ : S →+* Rᵐᵒᵖ`. An
additive map `f` from a discrete `S`-`Q`-module `N` to `Hom_ℤ(V, W)` that is `Q`-equivariant for
the conjugation action and satisfies `f (s • n) = f n ∘ ((φ s).unop • -)` intertwines the actions
of the completed group algebras, `f (x • n) = mapCoeff φ x • f n`
(`Stacks.ContinuousCohomology.internalHomSMul_map_of_semilinear`): `x` acts on `f n` at `v`
through the discrete module `Hom_ℤ(T, W)`, for `T` the finite stable submodule spanned by the
orbit of `v`, and restriction to `T` is a `φ`-semilinear morphism of discrete modules.

Consequently a family of `ℤ`-bilinear pairings `Aⁿ × E^p → G^{p+n}` between complexes of discrete
modules that is equivariant, balanced along `φ`, and satisfies the Leibniz rule of the Hom-complex
differential gives a morphism of complexes of `S[[Q]]`-modules from `A`, viewed through the exact
functor `Stacks.ContinuousCohomology.discreteToCompletedGroupAlgebra`, to the internal Hom complex
`Hom^•_ℤ(E, G)` with scalars restricted along `mapCoeff φ`
(`Stacks.ContinuousCohomology.internalHomComplexOfPairing`). This is the shape of the
Galois-equivariant Poincaré pairing of Tag 03VM: `A` is `RΓ_c` of the representation sheaf over
`S = Λ`, `E` the Galois-equivariant `RHom` over `R = Λᵐᵒᵖ`, `φ = RingEquiv.opOp Λ`, and the
pairing is evaluation followed by the trace.

## Main results

* `Stacks.ContinuousCohomology.internalHomSMul_map_of_semilinear`.
* `Stacks.ContinuousCohomology.internalHomComplexOfPairing`.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex Stacks.GroupHomology

universe u u' v w w₂

namespace Stacks.ContinuousCohomology

open scoped InternalHomAction

section Linear

variable (R : Type u) [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q]
  (V : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)
  (W : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q)
  {S : Type u'} [Ring S] (φ : S →+* Rᵐᵒᵖ)
  (N : Stacks.Injectives.ContinuousModule.{u', v, w₂} S Q)

/-- **An equivariant additive map from a discrete `S`-module to `Hom_ℤ(V, W)`, semilinear along
`φ : S →+* Rᵐᵒᵖ`, intertwines `S[[Q]]` and `Rᵐᵒᵖ[[Q]]`** through `mapCoeff φ`. -/
theorem internalHomSMul_map_of_semilinear (f : N.obj.obj.V →+ (V.obj.obj.V →+ W.obj.obj.V))
    (hq : ∀ (q : Q) (a : N.obj.obj.V) (v : V.obj.obj.V),
      f ((N.obj.obj.ρ q).asHom.hom a) v =
        (W.obj.obj.ρ q).asHom.hom (f a ((V.obj.obj.ρ q⁻¹).asHom.hom v)))
    (hr : ∀ (s : S) (a : N.obj.obj.V) (v : V.obj.obj.V),
      f (s • a) v = f a ((φ s).unop • v))
    (x : CompletedGroupAlgebra S Q) (a : N.obj.obj.V) :
    f (discreteSMul S N x a) =
      internalHomSMul R V W (CompletedGroupAlgebra.mapCoeff φ x) (f a) := by
  refine AddMonoidHom.ext fun v => ?_
  have hS := isStableSubmodule_orbitSpan R V v
  let g : N.obj.obj.V →ₛₗ[φ] ((orbitSpan R V v) →+ W.obj.obj.V) :=
    { toFun a := (f a).comp (orbitSpan R V v).subtype.toAddMonoidHom
      map_add' a b := by rw [map_add, AddMonoidHom.add_comp]
      map_smul' s a := AddMonoidHom.ext fun t => hr s a t }
  have key := discreteSMul_map_semilinear S Q φ (N' := restrictedHomObj R V W hS) g
    (fun q a => AddMonoidHom.ext fun t =>
      (hq q a t).trans (restrictedHomRep_apply R V W hS q (g a) t).symm) x a
  exact congrArg (fun ψ : (orbitSpan R V v) →+ W.obj.obj.V => ψ ⟨v, mem_orbitSpan_self R V v⟩) key

end Linear

section Pairing

variable (R : Type u) [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] {S : Type u'} [Ring S] (φ : S →+* Rᵐᵒᵖ)
  (A : CochainComplex (Stacks.Injectives.ContinuousModule.{u', v, w} S Q) ℤ)
  (E : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ)
  (G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ)

/-- **A pairing of complexes of discrete modules** `Aⁿ × E^p → G^{p+n}`: `ℤ`-bilinear,
equivariant for the conjugation action, balanced along `φ : S →+* Rᵐᵒᵖ`, and satisfying the
Leibniz rule of the Hom-complex differential, `φ(d a) = d ∘ φ(a) + (-1)^{n+1} φ(a) ∘ d`. -/
structure ComplexPairing where
  /-- The components. -/
  pair : ∀ (n p q : ℤ), p + n = q →
    (A.X n).obj.obj.V →+ ((E.X p).obj.obj.V →+ (G.X q).obj.obj.V)
  /-- Equivariance, in the conjugation form. -/
  galois : ∀ (n p q : ℤ) (h : p + n = q) (σ : Q) (a : (A.X n).obj.obj.V) (e : (E.X p).obj.obj.V),
    pair n p q h (((A.X n).obj.obj.ρ σ).asHom.hom a) e =
      ((G.X q).obj.obj.ρ σ).asHom.hom (pair n p q h a (((E.X p).obj.obj.ρ σ⁻¹).asHom.hom e))
  /-- Balancing along `φ`. -/
  balanced : ∀ (n p q : ℤ) (h : p + n = q) (s : S) (a : (A.X n).obj.obj.V)
    (e : (E.X p).obj.obj.V), pair n p q h (s • a) e = pair n p q h a ((φ s).unop • e)
  /-- The Leibniz rule. -/
  leibniz : ∀ (n p q q' : ℤ) (h : p + n = q) (hq : q + 1 = q') (a : (A.X n).obj.obj.V)
    (e : (E.X p).obj.obj.V),
    pair (n + 1) p q' (by omega) ((A.d n (n + 1)).hom.hom.hom.hom a) e =
      ((G.d q q').hom.hom.hom.hom (pair n p q h a e)) +
        (n + 1).negOnePow • pair n (p + 1) q' (by omega) a ((E.d p (p + 1)).hom.hom.hom.hom e)

variable {R φ A E G}

open InternalHomCochain

/-- The degree-`n` component of the chain map attached to a pairing. -/
def ComplexPairing.cochain (P : ComplexPairing R φ A E G) (n : ℤ) (a : (A.X n).obj.obj.V) :
    InternalHomCochain R E G n :=
  of (Cochain.mk fun p q hpq => AddCommGrpCat.ofHom (P.pair n p q hpq a))

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- The `(p, q)` component of `ComplexPairing.cochain P n a` is the map `P.pair n p q hpq a`. -/
lemma ComplexPairing.cochain_v (P : ComplexPairing R φ A E G) (n : ℤ) (a : (A.X n).obj.obj.V)
    (p q : ℤ) (hpq : p + n = q) :
    (toCochain (P.cochain n a)).v p q hpq = AddCommGrpCat.ofHom (P.pair n p q hpq a) := rfl

/-- **The chain map attached to a pairing**, from `A` viewed as a complex of `S[[Q]]`-modules to
the internal Hom complex `Hom^•_ℤ(E, G)`, with scalars restricted along `mapCoeff φ`. -/
def internalHomComplexOfPairing (P : ComplexPairing R φ A E G) :
    ((discreteToCompletedGroupAlgebra.{u', v, w} S Q).mapHomologicalComplex _).obj A ⟶
      ((ModuleCat.restrictScalars (CompletedGroupAlgebra.mapCoeff (G := Q) φ)).mapHomologicalComplex
        _).obj (internalHomComplex R E G) where
  f n :=
    letI := discreteCompletedGroupAlgebraModule S (A.X n)
    ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (CompletedGroupAlgebra.mapCoeff (G := Q) φ)).obj
        ((internalHomComplex R E G).X n))
    { toFun a := P.cochain n a
      map_add' a b := by
        apply InternalHomCochain.ext
        refine Cochain.ext _ _ fun p q hpq => ?_
        exact AddCommGrpCat.hom_ext (map_add (P.pair n p q hpq) a b)
      map_smul' x a := by
        apply InternalHomCochain.ext
        refine Cochain.ext _ _ fun p q hpq => ?_
        change (toCochain (P.cochain n (discreteSMul S (A.X n) x a))).v p q hpq =
          (toCochain (CompletedGroupAlgebra.mapCoeff φ x • P.cochain n a)).v p q hpq
        rw [toCochain_smul_v, P.cochain_v, P.cochain_v]
        exact AddCommGrpCat.hom_ext <| internalHomSMul_map_of_semilinear R (E.X p) (G.X q) φ
          (A.X n) (P.pair n p q hpq) (P.galois n p q hpq) (P.balanced n p q hpq) x a }
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    refine ModuleCat.hom_ext <| LinearMap.ext fun a => ?_
    apply InternalHomCochain.ext
    refine Cochain.ext _ _ fun p q' hpq' => ?_
    change (δ n (n + 1) (toCochain (P.cochain n a))).v p q' hpq' =
      (toCochain (P.cochain (n + 1) ((A.d n (n + 1)).hom.hom.hom.hom a))).v p q' hpq'
    rw [δ_v n (n + 1) rfl _ p q' hpq' (q' - 1) (p + 1) (by omega) rfl]
    exact AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun e =>
      (P.leibniz n p (q' - 1) q' (by omega) (by omega) a e).symm

end Pairing

end Stacks.ContinuousCohomology

end

module

public import StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormulaNatural
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChange
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare

/-!
# The enriched adjunction `Δ_* ⊣ Δ^!`, and Step 1 of the duality route to [stacks 0E2D]

Let `R → A` be flat, put `B = A ⊗[R] A`, write `p₁ : A → B` for the left coprojection and
`Δ : B → A` for the multiplication map, and write `T(X) = Δ^!(p₁^*X)` for the functor the
defining condition of [stacks 0E2C] is about.  The duality route to [stacks 0E2D] described in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` asks, as its Step 1, for

> `T(RHom_A(M, N)) ≅ RHom_A(M, T(N))`   for `M` pseudo-coherent and `N` bounded below.

`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessHomCommutation` and
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare` compose everything but
one ingredient, reaching

`T(RHom_A(M, N)) ≅ p₁_* RHom_B(Δ_*M, p₁^*N)`,

and record that what separates that from Step 1 is the **enriched** form of the adjunction
`Δ_* ⊣ Δ^!` of [stacks 0A70],

`p₁_* RHom_B(Δ_*M, Y) ≅ RHom_A(M, Δ^!Y)`,

true at `M = A[0]` and a separate theorem for general `M`.  **This file proves it, and hence
Step 1.**

## The shape of the proof

The enriched adjunction is Yoneda, and it is proved that way, for arbitrary data: in
`Dualizing.enrichedHomIso` the two sides are shown to corepresent the same functor of `Z`
through five bijections —

`Hom_A(Z, Ψ RHom_B(F M, Y)) ≅ Hom_B(Φ Z, RHom_B(F M, Y)) ≅ Hom_B(Φ Z ⊗ᴸ_B F M, Y)`
`≅ Hom_B(F(M ⊗ᴸ_A Z), Y) ≅ Hom_A(M ⊗ᴸ_A Z, G Y) ≅ Hom_A(Z, RHom_A(M, G Y))`

— using an adjunction `Φ ⊣ Ψ`, the two tensor--Hom adjunctions of [stacks 0A63], an adjunction
`F ⊣ G`, and a **projection formula natural in the tensor factor**,
`F(M ⊗ᴸ_A -) ≅ F M ⊗ᴸ_B Φ(-)`.  Each of the five is natural in `Z`, which is the whole content of
`Dualizing.enrichedEquiv_naturality`; the naturality of the projection formula is the one of the
five that is not formal, and it is
`Dualizing.diagonalProjectionNatIso` of
`StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormulaNatural`.

At the diagonal the data are: `Φ = p₁^*` and `Ψ = p₁_*`, adjoint by [stacks 0GMT]
(`Dualizing.diagonalDerivedExtensionAdjunction`); `F = Δ_*` and `G = Δ^!`, adjoint by
[stacks 0A70] (`Dualizing.derivedHomAdjunction`); and the projection formula just named.  That
gives `Dualizing.enrichedDiagonalHomIso`, and composing it with
`Dualizing.nonempty_relativeDualizingDiagonalHom_modelHom_iso` gives Step 1.

## Main definitions

* `Dualizing.enrichedHomIso` — **the enriched form of an adjunction `F ⊣ G`**, for arbitrary
  adjunctions and an arbitrary projection formula natural in the tensor factor.
* `Dualizing.diagonalDerivedExtensionAdjunction` — `p₁^* ⊣ p₁_*` of [stacks 0GMT], stated for
  `Dualizing.diagonalDerivedExtension`.
* `Dualizing.enrichedDiagonalHomIso` — **the enriched `Δ_* ⊣ Δ^!`**:
  `p₁_* RHom_B(Δ_*M, Y) ≅ RHom_A(M, Δ^!Y)`, for arbitrary `M` and `Y`.

## Main results

* `Dualizing.nonempty_relativeDualizingFunctor_modelHom_commutation` — **Step 1 of the duality
  route**: `T(RHom_A(M, N)) ≅ RHom_A(M, T(N))` for `M` pseudo-coherent and `N` bounded below.  No
  condition on the ring is used, and in particular nothing about bounded-below acyclic complexes
  of flat modules, which is where the diagonal route to [stacks 0E2D] stalls.
* `Dualizing.nonempty_modelHom_dual_iso_of_relativeDualizingCondition` — **Step 1 consumed.**
  From the defining condition of [stacks 0E2C] at two objects `ω` and `K` and biduality at `K`
  for `ω`, it produces `RHom_A(RHom_A(K, ω), one) ≅ one` — the input that
  `Dualizing.nonempty_derivedHom_iso_one_of_isIso_bidualityMor` and
  `Dualizing.nonempty_tensor_iso_of_hom_iso_one` of
  `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` are waiting for, and which the
  module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeBiduality` records as not
  following from [stacks 0E2C].

## What [stacks 0E2D] still needs

Nothing in the `D(B)` half: with Step 1 proved, the route's remaining obligation is the local
computation of Step 2 alone — `RHom_A(P, A) ≅ A ⟹ P ≅ A` for `P` with bounded coherent
cohomology — whose degree half, length half and endgame are the theorems listed in the module
documentation of `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality`.  The three glue
steps — the associativity
`P ⊗ᴸ (ω ⊗ᴸ κ) ≅ (P ⊗ᴸ ω) ⊗ᴸ κ`, the hypotheses of `T = ω ⊗ᴸ κ`, and `IsPerfect P` from fibre
concentration via [stacks 068V] — are `Dualizing.tensorResidueIso`,
`Dualizing.isTorsionBySet_homology_derivedFibre` together with
`Dualizing.finite_homology_derivedFibre_and_exists_isLE`, and
`Dualizing.isPerfect_of_fibre_concentrated` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation`, where the computation
itself is assembled as well.  **One of those hypotheses is not a theorem**: the fixed object is asked to be bounded *below* as well as above, and a dualizing
complex has no finite Tor dimension, so at the witness `A = k[x, y]/(x, y)²` the object
`ω ⊗ᴸ_A κ` is unbounded below.  That module's documentation records what the bound is worth and
what a one-sided computation would need instead.

No tag is claimed here: none of these declarations states [stacks 0E2D].

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/
@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

open StacksDraft.DerivedHom

noncomputable section

section Abstract

universe u₀ v₀ w₀

variable {A B : Type u₀} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w₀} (ModuleCat.{v₀} A)] [HasDerivedCategory.{w₀} (ModuleCat.{v₀} B)]

/-- Precomposition with an isomorphism, as an equivalence of morphism types. -/
def precompEquiv {C : Type*} [Category* C] {X X' : C} (e : X ≅ X') (Y : C) :
    (X' ⟶ Y) ≃ (X ⟶ Y) where
  toFun f := e.hom ≫ f
  invFun g := e.inv ≫ g
  left_inv f := Iso.inv_hom_id_assoc e f
  right_inv g := Iso.hom_inv_id_assoc e g

/-- The Hom equivalence of [stacks 0A63] is natural in the first variable, read on its
inverse. -/
lemma homEquiv_symm_naturality_left {R : Type u₀} [CommRing R]
    [HasDerivedCategory.{w₀} (ModuleCat.{v₀} R)] (d : DerivedHomAdjunction R)
    {K K' L N : DerivedCategory (ModuleCat.{v₀} R)} (f : K' ⟶ K)
    (c : d.tensor.obj (K, L) ⟶ N) :
    (d.homEquiv K' L N).symm
        (d.tensor.map (show ((K', L) : _ × _) ⟶ (K, L) from (f, 𝟙 L)) ≫ c) =
      f ≫ (d.homEquiv K L N).symm c := by
  have h := d.homEquiv_naturality_left f ((d.homEquiv K L N).symm c)
  rw [AddEquiv.apply_symm_apply] at h
  rw [← h, AddEquiv.symm_apply_apply]

variable (dA : DerivedHomAdjunction A) (dB : DerivedHomAdjunction B)
    (Φ : DerivedCategory (ModuleCat.{v₀} A) ⥤ DerivedCategory (ModuleCat.{v₀} B))
    (Ψ : DerivedCategory (ModuleCat.{v₀} B) ⥤ DerivedCategory (ModuleCat.{v₀} A))
    (adjΦ : Φ ⊣ Ψ)
    (F : DerivedCategory (ModuleCat.{v₀} A) ⥤ DerivedCategory (ModuleCat.{v₀} B))
    (G : DerivedCategory (ModuleCat.{v₀} B) ⥤ DerivedCategory (ModuleCat.{v₀} A))
    (adjF : F ⊣ G) (M : DerivedCategory (ModuleCat.{v₀} A))
    (ξ : (CategoryTheory.Functor.curry.obj dA.tensor).obj M ⋙ F ≅
      Φ ⋙ (CategoryTheory.Functor.curry.obj dB.tensor).obj (F.obj M))
    (Y : DerivedCategory (ModuleCat.{v₀} B))

/-- The Yoneda comparison behind the enriched adjunction: for every `Z`, the morphisms
`Z ⟶ Ψ(RHom_B(F M, Y))` and `Z ⟶ RHom_A(M, G Y)` correspond.  Reading from the inside out: the
adjunction `Φ ⊣ Ψ` moves `Z` across, the tensor--Hom adjunction of [stacks 0A63] on `D(B)`
transposes, the projection formula `ξ` and the symmetry replace `F M ⊗ᴸ_B Φ Z` by `F(M ⊗ᴸ_A Z)`,
the adjunction `F ⊣ G` transposes back, and the tensor--Hom adjunction on `D(A)` finishes. -/
def enrichedEquiv (Z : DerivedCategory (ModuleCat.{v₀} A)) :
    (Z ⟶ Ψ.obj (dB.hom.obj (Opposite.op (F.obj M), Y))) ≃
      (Z ⟶ dA.hom.obj (Opposite.op M, G.obj Y)) :=
  (adjΦ.homEquiv Z (dB.hom.obj (Opposite.op (F.obj M), Y))).symm.trans
    ((dB.homEquiv (Φ.obj Z) (F.obj M) Y).toEquiv.trans
      (((precompEquiv (dB.tensorSwap (F.obj M) (Φ.obj Z)) Y).trans
          (precompEquiv (ξ.app Z) Y)).trans
        ((adjF.homEquiv (dA.tensor.obj (M, Z)) Y).trans
          ((precompEquiv (dA.tensorSwap Z M) (G.obj Y)).trans
            (dA.homEquiv Z M (G.obj Y)).toEquiv.symm))))

/-- The Yoneda comparison is natural in `Z`: each of its five steps is. -/
lemma enrichedEquiv_naturality {Z Z' : DerivedCategory (ModuleCat.{v₀} A)} (f : Z' ⟶ Z)
    (a : Z ⟶ Ψ.obj (dB.hom.obj (Opposite.op (F.obj M), Y))) :
    enrichedEquiv dA dB Φ Ψ adjΦ F G adjF M ξ Y Z' (f ≫ a) =
      f ≫ enrichedEquiv dA dB Φ Ψ adjΦ F G adjF M ξ Y Z a := by
  have e1 : (adjΦ.homEquiv Z' (dB.hom.obj (Opposite.op (F.obj M), Y))).symm (f ≫ a) =
      Φ.map f ≫ (adjΦ.homEquiv Z (dB.hom.obj (Opposite.op (F.obj M), Y))).symm a :=
    adjΦ.homEquiv_naturality_left_symm f a
  have e2 := dB.homEquiv_naturality_left (L := F.obj M) (M := Y) (Φ.map f)
    ((adjΦ.homEquiv Z (dB.hom.obj (Opposite.op (F.obj M), Y))).symm a)
  have e3 : (dB.tensorSwap (F.obj M) (Φ.obj Z')).hom ≫
        dB.tensor.map (show ((Φ.obj Z', F.obj M) : _ × _) ⟶ (Φ.obj Z, F.obj M) from
          (Φ.map f, 𝟙 (F.obj M))) =
      dB.tensor.map (show ((F.obj M, Φ.obj Z') : _ × _) ⟶ (F.obj M, Φ.obj Z) from
          (𝟙 (F.obj M), Φ.map f)) ≫
        (dB.tensorSwap (F.obj M) (Φ.obj Z)).hom :=
    (dB.tensorSwap_naturality (𝟙 (F.obj M)) (Φ.map f)).symm
  have e4 : (ξ.app Z').hom ≫
        dB.tensor.map (show ((F.obj M, Φ.obj Z') : _ × _) ⟶ (F.obj M, Φ.obj Z) from
          (𝟙 (F.obj M), Φ.map f)) =
      F.map (dA.tensor.map (show ((M, Z') : _ × _) ⟶ (M, Z) from (𝟙 M, f))) ≫
        (ξ.app Z).hom :=
    (ξ.hom.naturality f).symm
  have e6 : (dA.tensorSwap Z' M).hom ≫
        dA.tensor.map (show ((M, Z') : _ × _) ⟶ (M, Z) from (𝟙 M, f)) =
      dA.tensor.map (show ((Z', M) : _ × _) ⟶ (Z, M) from (f, 𝟙 M)) ≫
        (dA.tensorSwap Z M).hom :=
    (dA.tensorSwap_naturality f (𝟙 M)).symm
  show (dA.homEquiv Z' M (G.obj Y)).symm
      ((dA.tensorSwap Z' M).hom ≫ adjF.homEquiv (dA.tensor.obj (M, Z')) Y
        ((ξ.app Z').hom ≫ (dB.tensorSwap (F.obj M) (Φ.obj Z')).hom ≫
          dB.homEquiv (Φ.obj Z') (F.obj M) Y
            ((adjΦ.homEquiv Z' (dB.hom.obj (Opposite.op (F.obj M), Y))).symm (f ≫ a)))) = _
  rw [e1, e2, reassoc_of% e3, reassoc_of% e4, adjF.homEquiv_naturality_left, reassoc_of% e6,
    homEquiv_symm_naturality_left dA f]
  exact rfl

/-- **The enriched form of the adjunction `F ⊣ G`.**  Let `Φ ⊣ Ψ` and `F ⊣ G` be adjunctions
between `D(A)` and `D(B)`, let `dA`, `dB` be tensor--Hom adjunctions of [stacks 0A63] on the two
derived categories, and suppose the **projection formula** holds naturally in the tensor factor:

`F(M ⊗ᴸ_A Z) ≅ F M ⊗ᴸ_B Φ Z`,   naturally in `Z`.

Then the adjunction `F ⊣ G` holds in its internal-Hom-enriched form:

`Ψ(RHom_B(F M, Y)) ≅ RHom_A(M, G Y)`.

Only the projection formula's naturality in `Z` is used, and the proof is Yoneda and nothing
else: both sides corepresent the same functor of `Z`, by
`Dualizing.enrichedEquiv` and `Dualizing.enrichedEquiv_naturality`.  No coherence of the tensor
is used beyond naturality of the symmetry. -/
def enrichedHomIso :
    Ψ.obj (dB.hom.obj (Opposite.op (F.obj M), Y)) ≅ dA.hom.obj (Opposite.op M, G.obj Y) :=
  Yoneda.ext _ _ (fun {Z} a => enrichedEquiv dA dB Φ Ψ adjΦ F G adjF M ξ Y Z a)
    (fun {Z} b => (enrichedEquiv dA dB Φ Ψ adjΦ F G adjF M ξ Y Z).symm b)
    (fun {_Z} a => (enrichedEquiv dA dB Φ Ψ adjΦ F G adjF M ξ Y _).symm_apply_apply a)
    (fun {_Z} b => (enrichedEquiv dA dB Φ Ψ adjΦ F G adjF M ξ Y _).apply_symm_apply b)
    (fun {_Z _Z'} f a => enrichedEquiv_naturality dA dB Φ Ψ adjΦ F G adjF M ξ Y f a)

end Abstract

section Diagonal

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]

/-- **Derived base change along the left coprojection is left adjoint to restriction of scalars
along it**, [stacks 0GMT], stated for `Dualizing.diagonalDerivedExtension`.  The coprojection is
flat, so that functor is the total left derived functor of degreewise base change
(`Dualizing.diagonalDerivedExtensionIsoTotalDerived`), and the adjunction is transported along
that identification. -/
def diagonalDerivedExtensionAdjunction :
    diagonalDerivedExtension R A ⊣
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).mapDerivedCategory :=
  Adjunction.ofNatIsoLeft
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
      A (A ⊗[R] A) _ _ (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) _ _
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).functor
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).comparison
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).isLeftDerived)
    (diagonalDerivedExtensionIsoTotalDerived R A)

/-- **The enriched form of the adjunction `Δ_* ⊣ Δ^!` of [stacks 0A70].**  Let `R → A` be flat,
put `B = A ⊗[R] A`, write `p₁ : A → B` for the left coprojection and `Δ : B → A` for the
multiplication map.  For every object `M` of `D(A)` and every object `Y` of `D(B)`,

`p₁_* RHom_B(Δ_*M, Y) ≅ RHom_A(M, Δ^!Y)`.

This is the one obligation of the duality route to [stacks 0E2D] that
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessHomCommutation` records as a theorem about
derived categories rather than bookkeeping.  It is `Dualizing.enrichedHomIso` fed with: the
adjunction `p₁^* ⊣ p₁_*` of [stacks 0GMT], the adjunction `Δ_* ⊣ Δ^!` of [stacks 0A70], the two
tensor--Hom adjunctions of [stacks 0A63], and the projection formula at the diagonal **natural in
the tensor factor**, `Dualizing.diagonalProjectionNatIso`.  At `M = A[0]` it specializes to
`Dualizing.nonempty_derivedHom_iso_restrictScalars_modelHom`; for general `M` the naturality of
the projection formula is exactly what was missing. -/
def enrichedDiagonalHomIso (M : DerivedCategory (ModuleCat.{u} A))
    (Y : DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) :
    (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeLeftRingHom :
            A →+* A ⊗[R] A)).mapDerivedCategory.obj
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
          (Opposite.op ((ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.lmul' R :
              A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj M), Y)) ≅
      (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
        (Opposite.op M,
          (derivedHom.{u, u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj Y) :=
  enrichedHomIso
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction A).toDerivedHomAdjunction
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction
      (A ⊗[R] A)).toDerivedHomAdjunction
    (diagonalDerivedExtension R A)
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).mapDerivedCategory
    (diagonalDerivedExtensionAdjunction R A)
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory
    (derivedHom.{u, u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom)
    (_root_.Dualizing.derivedHomAdjunction.{u, u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom)
    M (diagonalProjectionNatIso R A M) Y

/-- **Step 1 of the duality route to [stacks 0E2D]: the functor `T` of [stacks 0E2C] commutes
with derived Hom out of a pseudo-coherent object.**  Let `R → A` be flat, put `B = A ⊗[R] A` and
write `T(X) = Δ^!(p₁^*X)` for the functor the defining condition of [stacks 0E2C] is about.  For
`M` pseudo-coherent and `N` bounded below,

`T(RHom_A(M, N)) ≅ RHom_A(M, T(N))`.

This is the whole of Step 1 as the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` describes it: flat base change for
derived Hom along the flat coprojection [stacks 0A6A], the currying isomorphism [stacks 0A65],
the unrestricted projection formula at the diagonal, and the adjunction `Δ_* ⊣ Δ^!` [stacks 0A70],
composed.  The first three and the reconciliation of the library's two internal-Hom bifunctors
are `Dualizing.nonempty_relativeDualizingDiagonalHom_modelHom_iso`; the fourth is needed in its
**enriched** form `Dualizing.enrichedDiagonalHomIso`, which rests on the projection formula at
the diagonal being natural in the tensor factor
(`Dualizing.diagonalProjectionNatIso`).  The hypotheses are those of [stacks 0A6A] (3) and
nothing more: no condition on the ring, and in particular nothing about bounded-below acyclic
complexes of flats, which is where the diagonal route to the tag stalls. -/
theorem nonempty_relativeDualizingFunctor_modelHom_commutation
    (M N : DerivedCategory (ModuleCat.{u} A))
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M) (b : ℤ) (hN : N.IsGE b) :
    Nonempty
      ((derivedHom.{u, u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((diagonalDerivedExtension R A).obj
              ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
                (Opposite.op M, N))) ≅
        (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
          (Opposite.op M,
            (derivedHom.{u, u, u}
              (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
              ((diagonalDerivedExtension R A).obj N))) := by
  obtain ⟨e₁⟩ := nonempty_relativeDualizingDiagonalHom_modelHom_iso R A M N hM b hN
  exact ⟨(derivedHom.{u, u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
        ((diagonalDerivedExtension R A).mapIso
          (modelHomIsoDerivedHomAdjunctionOverRing A M N)) ≪≫
    e₁ ≪≫ enrichedDiagonalHomIso R A M ((diagonalDerivedExtension R A).obj N)⟩

/-- **The hypothesis the duality route to [stacks 0E2D] needs, discharged from the defining
condition of [stacks 0E2C].**  Let `R → A` be flat, write `T(X) = Δ^!(p₁^*X)`, let `ω` and `K` be
objects of `D(A)` with `T(ω)` and `T(K)` both isomorphic to one and the same object `one` — which
is the defining condition of [stacks 0E2C] for both, with `one` the tensor unit — and suppose
biduality holds at `K` for `ω`, i.e. `K ≅ RHom_A(RHom_A(K, ω), ω)`.  Then, writing
`P = RHom_A(K, ω)`,

`RHom_A(P, one) ≅ one`.

This is Step 2 of the duality route of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` up to its one remaining obligation:
`Dualizing.nonempty_derivedHom_iso_one_of_isIso_bidualityMor` turns this conclusion into
`RHom_A(ω, K) ≅ one`, which is the hypothesis of `Dualizing.nonempty_iso_of_isIso_evaluation`
that the module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeBiduality` records as
not following from [stacks 0E2C]; and `Dualizing.nonempty_tensor_iso_of_hom_iso_one` turns it
into `P ⊗ᴸ_A ω ≅ ω`, the first step of the rigidity argument whose remaining content is the local
computation alone.

The proof is Step 1 and nothing else: `RHom_A(P, one) ≅ RHom_A(P, T(ω))` because `T(ω) ≅ one`,
that is `T(RHom_A(P, ω))` by
`Dualizing.nonempty_relativeDualizingFunctor_modelHom_commutation`, that is `T(K)` by biduality,
and `T(K) ≅ one`.  The hypotheses are those of Step 1: `P` pseudo-coherent and `ω` bounded
below. -/
theorem nonempty_modelHom_dual_iso_of_relativeDualizingCondition
    (ω K one : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj (Opposite.op K, ω)))
    (b : ℤ) (hω : ω.IsGE b)
    (hbid : K ≅ (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
      (Opposite.op ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
        (Opposite.op K, ω)), ω))
    (hTω : (derivedHom.{u, u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
        ((diagonalDerivedExtension R A).obj ω) ≅ one)
    (hTK : (derivedHom.{u, u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
        ((diagonalDerivedExtension R A).obj K) ≅ one) :
    Nonempty
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
        (Opposite.op ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
          (Opposite.op K, ω)), one) ≅ one) := by
  obtain ⟨e⟩ := nonempty_relativeDualizingFunctor_modelHom_commutation R A
    ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj (Opposite.op K, ω)) ω hP b hω
  exact ⟨homIso
      (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction A).toDerivedHomAdjunction
      (Iso.refl _) hTω.symm ≪≫
    e.symm ≪≫
    (derivedHom.{u, u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
        ((diagonalDerivedExtension R A).mapIso hbid.symm) ≪≫ hTK⟩

end Diagonal

end

end Dualizing

end

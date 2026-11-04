module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionFunctor
public import StacksCore.Tactic.StacksAttribute

/-! # Precomposition on derived Hom out of a differential graded bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let
`f : M → N` be a homomorphism of differential graded `(A, B)`-bimodules. Precomposition with `f`
is a natural transformation of the internal hom functors on the homotopy categories
(`DifferentialGraded.Bimodule.precompHomotopyNatTrans`), hence of the functors
`K(B) ⥤ D(A, d)` whose right derived functors are the derived Hom functors of Tag 09LI. By the
universal property of a right derived functor — being a left Kan extension along the
localization — it therefore descends to a natural transformation

  `RHom(N, -) ⟹ RHom(M, -)`

of functors `D(B, d) ⥤ D(A, d)`, uniquely characterized by the comparison square it fits into.
This is the first assertion of Tag 0BYV.

## Main definitions

* `DifferentialGraded.Bimodule.precompToDerivedNatTrans`: precomposition on the functors being
  derived, namely internal hom on homotopy categories followed by localization of the target.
* `DifferentialGraded.Bimodule.derivedPrecomp`: the induced natural transformation of the
  derived Hom functors.

## Main results

* `DifferentialGraded.Bimodule.derivedPrecomp_comparison`: the characterizing comparison square,
  relating the derived transformation to the underived one through the canonical comparison maps
  of the two derived Hom functors.
* `DifferentialGraded.Bimodule.derivedPrecomp_unique`: the comparison square determines the
  derived transformation.
* `DifferentialGraded.Bimodule.derivedPrecomp_id` and
  `DifferentialGraded.Bimodule.derivedPrecomp_comp`: the derived transformation is
  contravariantly functorial in the bimodule.

## Implementation notes

*The derived Hom functor is an argument.* The existence of the right derived functor of internal
hom, Tag 09LI, is an input to Tag 0BYV rather than part of it; it is recorded as
`DifferentialGradedModule.DerivedHomData`, and every declaration below takes one for each of the
two bimodules. Given resolutions by modules orthogonal on the right to the acyclic ones
(Tag 09KU), `DifferentialGradedModule.DerivedHomData.ofResolutions` constructs it.

*Everything is Kan extension descent.* `DerivedHomData.isRightDerived` says that the
functor together with its comparison is a left Kan extension along the localization, so the
descent of a transformation, its characterization and its functoriality are
`CategoryTheory.Functor.rightDerivedNatTrans` and its lemmas. Nothing specific to differential
graded modules enters at this level; the differential graded content is in
`DifferentialGraded.Bimodule.precompDGNatTrans`.

*Universes.* The differential graded algebras and their modules use the single-universe
encoding `StacksDraft.Ch22.Sec4.Tag09JJ`, as in
`StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHom`; the Stacks source is
universe-polymorphic in the base ring and in each of the two algebras separately. Nothing below
uses the universes being equal.

## References

* [Stacks Project, Tag 0BYV](https://stacks.math.columbia.edu/tag/0BYV); the derived Hom functor
  is [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI) and the internal hom functor is
  [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R} {M N L : Bimodule A B}

/-- Precomposition with a bimodule homomorphism on the functors being right derived: internal
hom on the homotopy categories, followed by localization of the target at the
quasi-isomorphisms of differential graded `A`-modules. -/
def precompToDerivedNatTrans (f : M ⟶ N) :
    homToDerivedCategory A B N.rightModule N.leftAction ⟶
      homToDerivedCategory A B M.rightModule M.leftAction :=
  Functor.whiskerRight (precompHomotopyNatTrans f) (quasiIsomorphisms' A).Q

/-- Precomposition with the identity of `M` is the identity transformation. -/
@[simp] theorem precompToDerivedNatTrans_id (M : Bimodule A B) :
    precompToDerivedNatTrans (𝟙 M) =
      𝟙 (homToDerivedCategory A B M.rightModule M.leftAction) := by
  rw [precompToDerivedNatTrans, precompHomotopyNatTrans_id]
  ext P
  simp only [Functor.whiskerRight_app, NatTrans.id_app]
  exact (quasiIsomorphisms' A).Q.map_id _

/-- Precomposition with `f ≫ g` is precomposition with `g` followed by precomposition with `f`. -/
theorem precompToDerivedNatTrans_comp (f : M ⟶ N) (g : N ⟶ L) :
    precompToDerivedNatTrans (f ≫ g) =
      precompToDerivedNatTrans g ≫ precompToDerivedNatTrans f := by
  rw [precompToDerivedNatTrans, precompToDerivedNatTrans, precompToDerivedNatTrans,
    precompHomotopyNatTrans_comp]
  ext P
  simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.map_comp]
  rfl

variable (DN : DerivedHomData A B N.rightModule N.leftAction)
  (DM : DerivedHomData A B M.rightModule M.leftAction)

/-- Precomposition with a homomorphism `f : M ⟶ N` of differential graded `(A, B)`-bimodules
induces a natural transformation `RHom(N, -) ⟹ RHom(M, -)` of derived Hom functors
`D(B, d) ⥤ D(A, d)`. -/
@[stacks 0BYV "the natural transformation"]
def derivedPrecomp (f : M ⟶ N) : DN.functor ⟶ DM.functor :=
  haveI := DN.isRightDerived
  Functor.rightDerivedNatTrans DN.functor DM.functor DN.comparison DM.comparison
    (quasiIsomorphisms' B) (precompToDerivedNatTrans f)

/-- The derived transformation is compatible with the canonical comparison maps from ordinary
internal hom to derived Hom. -/
@[stacks 0BYV "compatibility with the comparison maps"]
theorem derivedPrecomp_comparison (f : M ⟶ N) :
    DN.comparison ≫
        Functor.whiskerLeft (quasiIsomorphisms' B).Q (derivedPrecomp DN DM f) =
      precompToDerivedNatTrans f ≫ DM.comparison :=
  have := DN.isRightDerived
  Functor.rightDerivedNatTrans_fac DN.functor DM.functor DN.comparison DM.comparison
    (quasiIsomorphisms' B) (precompToDerivedNatTrans f)

/-- The comparison square determines the derived transformation: there is at most one
transformation of derived Hom functors fitting into it. -/
theorem derivedPrecomp_unique (f : M ⟶ N) (θ : DN.functor ⟶ DM.functor)
    (hθ : DN.comparison ≫ Functor.whiskerLeft (quasiIsomorphisms' B).Q θ =
      precompToDerivedNatTrans f ≫ DM.comparison) :
    θ = derivedPrecomp DN DM f :=
  have := DN.isRightDerived
  Functor.rightDerived_ext DN.functor DN.comparison (quasiIsomorphisms' B) DM.functor θ
    (derivedPrecomp DN DM f) (by rw [hθ, derivedPrecomp_comparison])

/-- Precomposition with the identity induces the identity transformation of derived Hom. -/
@[simp] theorem derivedPrecomp_id (M : Bimodule A B)
    (D : DerivedHomData A B M.rightModule M.leftAction) :
    derivedPrecomp D D (𝟙 M) = 𝟙 D.functor := by
  have := D.isRightDerived
  rw [derivedPrecomp, precompToDerivedNatTrans_id]
  exact Functor.rightDerivedNatTrans_id D.functor D.comparison (quasiIsomorphisms' B)

/-- Precomposition reverses composition, as transformations of derived Hom functors. -/
theorem derivedPrecomp_comp (f : M ⟶ N) (g : N ⟶ L)
    (DL : DerivedHomData A B L.rightModule L.leftAction) :
    derivedPrecomp DL DM (f ≫ g) = derivedPrecomp DL DN g ≫ derivedPrecomp DN DM f := by
  have := DL.isRightDerived
  have := DN.isRightDerived
  rw [derivedPrecomp, derivedPrecomp, derivedPrecomp, precompToDerivedNatTrans_comp,
    ← Functor.rightDerivedNatTrans_comp DL.functor DN.functor DM.functor DL.comparison
      DN.comparison DM.comparison (quasiIsomorphisms' B) (precompToDerivedNatTrans g)
      (precompToDerivedNatTrans f)]

end DifferentialGraded.Bimodule

end

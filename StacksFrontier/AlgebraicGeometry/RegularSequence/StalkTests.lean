module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalkComplexIso
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularIdealSheaves
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.QuasiRegular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalkwise tests for regularity of a sequence, at the constructed sheaves

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalk.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalkComplexIso.lean` prove the stalk
computations of Stacks Tag 063C for an arbitrary *presentation* of the sheaves involved: the
quotient `O_X/(f₀, …, f_{i-1})` with multiplication by `fᵢ` on it, the quasi-regularity morphism
`(O_X/J)[T₁, …, T_r] ⟶ ⨁_d J^d/J^{d+1}`, and the Koszul complex of `(f₀, …, f_{r-1})` each enter
as data satisfying a characterization, not as a chosen construction.

This file applies those computations to the sheaves that are actually constructed elsewhere in
the library, so that the stalk statements hold of named terms rather than of hypotheses:

* the quotient-with-multiplication datum of Stacks Tag 0639,
  `AlgebraicGeometry.regularSequenceMultiplication`;
* the quasi-regularity datum of Stacks Tag 063B,
  `Stacks.AlgebraicGeometry.QuasiRegular.quasiRegularMap`;
* the tensor/exterior/symmetric algebra package of a sheaf of modules,
  `SheafOfModules.algebras`, which discharges the algebra-bundle hypothesis of the Koszul
  comparison.

## Main results

* `Stacks.RegularSequence.exists_regularSequenceMultiplication_stalkRingEquiv`: the stalk of the
  Tag 0639 quotient sheaf is `O_{X,x}` modulo the germs of the preceding sections, by an
  isomorphism specified on germs of local sections.
* `Stacks.RegularSequence.regularSequenceMultiplication_stalk`: under that isomorphism the Tag
  0639 multiplication endomorphism becomes multiplication by the class of the germ of `fᵢ`.
* `Stacks.RegularSequence.isIso_quasiRegularMap_iff_bijective`: the Tag 063B morphism is an
  isomorphism exactly when the ring-level quasi-regularity map of the germs is bijective at
  every point, in the `polynomialQuasiRegularCanonicalMap` spelling.
* `Stacks.RegularSequence.KoszulChainData.exists_stalkChainIso_algebras`: the stalk comparison
  for the Koszul complex, with the algebra bundle taken to be the constructed one.

## Implementation notes

Two definitions are duplicated across the trees this file joins, in each case *verbatim*, so
the bridges below are `rfl` and are recorded here as the evidence that the duplication is
harmless and removable:

* `Stacks.AlgebraicGeometry.QuasiRegular.germSequence` and
  `Stacks.RegularSequence.germSequence`;
* `Stacks.RingTheory.QuasiRegular.associatedGradedMap` and
  `Stacks.RegularSequence.polynomialQuasiRegularCanonicalMap`.

The sectionwise membership condition is no longer among them: both trees now use the single
`AlgebraicGeometry.IsLocallyInPrecedingIdeal` of
`StacksFrontier/Topology/Sheaves/RingedSpace/PrecedingIdealSections.lean`.

The Koszul comparison keeps one hypothesis, and it is not removable here: the chain data of
Stacks Tag 062K. Tag 062K *asserts* the existence and uniqueness of the Koszul differential on
the exterior algebra of `(O_X)ʳ`, and that existence theorem is not proved anywhere in the
library, so there is no term of type `Stacks.RegularSequence.KoszulChainData` to supply. The
algebra bundle, by contrast, *is* constructed — `SheafOfModules.algebras` — and the corollary
below records that, so the Koszul statement's remaining hypothesis is exactly Tag 062K's own
obligation.

The universes of `SheafOfModules.algebras` and of `KoszulChainData` must be written out. In a
binder whose earlier entries fix the site only through the bundle argument, the structure's
universe metavariables are solved as `0` before the bundle is examined; this is the elaboration
pitfall already recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulSheafDifferential.lean`.

## References

* [Stacks Project, Tag 0639](https://stacks.math.columbia.edu/tag/0639)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 063B](https://stacks.math.columbia.edu/tag/063B)
* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.RegularSequence

/-! ### The two verbatim duplications, bridged -/

/-- The germ sequence of
`StacksFrontier/AlgebraicGeometry/QuasiRegular/Germs.lean` is the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalk.lean`. -/
theorem quasiRegular_germSequence_eq (X : RingedSpace.{u}) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op (⊤ : Opens X))) (x : X) :
    Stacks.AlgebraicGeometry.QuasiRegular.germSequence X f x = germSequence X f x :=
  rfl

/-- The canonical quasi-regularity map of
`StacksFrontier/AlgebraicGeometry/QuasiRegular/Algebra.lean` is the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalk.lean`. -/
theorem associatedGradedMap_eq {R : Type u} [CommRing R] {c : ℕ} (g : Fin c → R) :
    Stacks.RingTheory.QuasiRegular.associatedGradedMap g =
      polynomialQuasiRegularCanonicalMap g :=
  rfl

/-! ### The quotient by the preceding sections, and multiplication on it -/

section Quotient

variable (X : RingedSpace.{u}) {r : ℕ} (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))

/-- **The stalk of the Tag 0639 quotient sheaf.** The stalk at `x` of
`O_X/(f₀, …, f_{i-1})`, as constructed by `AlgebraicGeometry.regularSequenceMultiplication`, is
the quotient of `O_{X,x}` by the ideal generated by the germs of `f₀, …, f_{i-1}`. The displayed
equation specifies the isomorphism on germs of local sections, so this identifies the canonical
map and not merely the two rings.

This is `Stacks.RegularSequence.exists_stalkRingEquiv_quotient` at the constructed quotient: its
local surjectivity and kernel hypotheses are the Tag 0639 datum's own fields, the kernel one
through `AlgebraicGeometry.RegularSequenceMultiplicationData.mem_precedingIdeal_iff`. -/
theorem exists_regularSequenceMultiplication_stalkRingEquiv (i : Fin r) (x : X) :
    ∃ e : (regularSequenceMultiplication X f i).quotientSheaf.presheaf.stalk x
        ≃+* (X.presheaf.stalk x ⧸ precedingGermIdeal X f i x),
      ∀ (U : Opens X) (hx : x ∈ U) (s : X.presheaf.obj (op U)),
        e ((regularSequenceMultiplication X f i).quotientSheaf.presheaf.germ U x hx
            ((regularSequenceMultiplication X f i).quotientMap U s)) =
          Ideal.Quotient.mk (precedingGermIdeal X f i x) (X.presheaf.germ U x hx s) :=
  exists_stalkRingEquiv_quotient X f
    (regularSequenceMultiplication X f i).quotientSheaf
    (regularSequenceMultiplication X f i).quotientMap
    (regularSequenceMultiplication X f i).quotientMap_naturality i
    (fun U s y hy =>
      (regularSequenceMultiplication X f i).quotientMap_locallySurjective U s y hy)
    (fun U s => ((regularSequenceMultiplication X f i).quotientMap_eq_zero_iff U s).trans
      ((regularSequenceMultiplication X f i).mem_precedingIdeal_iff U s))
    x

/-- **The stalk of the Tag 0639 multiplication endomorphism.** Under any isomorphism of the kind
produced by `exists_regularSequenceMultiplication_stalkRingEquiv` — in particular under that one
— multiplication by `fᵢ` on `O_X/(f₀, …, f_{i-1})` becomes multiplication by the class of the
germ of `fᵢ` in `O_{X,x}` modulo the germs of the preceding sections.

This is `Stacks.RegularSequence.germ_mul_eq_germSequence_mul` at the constructed quotient; the
only property of the endomorphism used is the Tag 0639 datum's field
`multiplication_quotientMap`. -/
theorem regularSequenceMultiplication_stalk (i : Fin r) (x : X)
    (e : (regularSequenceMultiplication X f i).quotientSheaf.presheaf.stalk x
      ≃+* (X.presheaf.stalk x ⧸ precedingGermIdeal X f i x))
    (he : ∀ (U : Opens X) (hx : x ∈ U) (s : X.presheaf.obj (op U)),
      e ((regularSequenceMultiplication X f i).quotientSheaf.presheaf.germ U x hx
          ((regularSequenceMultiplication X f i).quotientMap U s)) =
        Ideal.Quotient.mk (precedingGermIdeal X f i x) (X.presheaf.germ U x hx s))
    (U : Opens X) (hx : x ∈ U) (s : X.presheaf.obj (op U)) :
    e ((regularSequenceMultiplication X f i).quotientSheaf.presheaf.germ U x hx
        (((regularSequenceMultiplication X f i).multiplication.app (op U))
          ((regularSequenceMultiplication X f i).quotientMap U s))) =
      Ideal.Quotient.mk (precedingGermIdeal X f i x) (germSequence X f x i) *
        e ((regularSequenceMultiplication X f i).quotientSheaf.presheaf.germ U x hx
          ((regularSequenceMultiplication X f i).quotientMap U s)) :=
  germ_mul_eq_germSequence_mul X f
    (regularSequenceMultiplication X f i).quotientSheaf
    (regularSequenceMultiplication X f i).quotientMap i
    (fun U t => (regularSequenceMultiplication X f i).multiplication.app (op U) t)
    (regularSequenceMultiplication X f i).multiplication_quotientMap e he U hx s

end Quotient

/-! ### Quasi-regularity -/

section QuasiRegular

/-- **The stalkwise test for quasi-regularity, in the polynomial spelling.** The canonical
morphism of Stacks Tag 063B is an isomorphism exactly when the ring-level quasi-regularity map
`(O_{X,x}/J_x)[T₁, …, T_r] ⟶ ⨁_d J_x^d/J_x^{d+1}` of the germs is bijective at every point.

This is `Stacks.AlgebraicGeometry.RegularIdealSheaf.isIso_quasiRegularMap_hom_iff` restated with
the two definitions of `Stacks.RegularSequence.quasiRegular_germSequence_eq` and
`Stacks.RegularSequence.associatedGradedMap_eq`, which are the same definitions. The same
conclusion is also an instance of
`Stacks.RegularSequence.isIso_iff_bijective_polynomialQuasiRegularCanonicalMap` applied to the
`polynomialStalkIso`, `associatedGradedStalkIso` and `stalk_map` fields of
`Stacks.AlgebraicGeometry.QuasiRegular.quasiRegularMap`. -/
@[ega "0 15.2.2" "special case"]
theorem isIso_quasiRegularMap_iff_bijective (X : RingedSpace.{u}) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op (⊤ : Opens X))) :
    IsIso (Stacks.AlgebraicGeometry.QuasiRegular.quasiRegularMap X f).hom ↔
      ∀ x : X, Function.Bijective
        (polynomialQuasiRegularCanonicalMap (germSequence X f x)) :=
  Stacks.AlgebraicGeometry.RegularIdealSheaf.isIso_quasiRegularMap_hom_iff X f

end QuasiRegular

/-! ### The Koszul complex, with the algebra bundle discharged -/

section Koszul

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {r : ℕ}

/-- **The algebra-bundle hypothesis of the Koszul comparison is satisfied.** The
tensor/exterior/symmetric algebra package of the finite free sheaf `(O♯)ʳ` is the constructed
one, `SheafOfModules.algebras`, so the hypothesis `A` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalkComplexIso.lean` is not an assumption
about an object that might not exist. -/
noncomputable def koszulAlgebras (Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u})
    (r : ℕ) :
    SheafOfModules.TensorExteriorSymmetricAlgebras.{u, u, u} (Opens.grothendieckTopology ↥X)
      (koszulFreeSheaf Osharp r) :=
  SheafOfModules.algebras.{u, u, u} _ _

namespace KoszulChainData

variable {φ : koszulFreeSheaf Osharp r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **The stalk comparison for the Koszul complex of a sequence of global sections, at the
constructed algebra bundle.** This is
`Stacks.RegularSequence.KoszulChainData.exists_stalkChainIso` with the algebra package taken to
be `Stacks.RegularSequence.koszulAlgebras`, so the only remaining hypothesis is the chain data
of Stacks Tag 062K, whose existence Tag 062K itself asserts and which is not proved in the
library. -/
theorem exists_stalkChainIso_algebras
    (K : KoszulChainData.{u, u, u} (koszulAlgebras Osharp r) φ)
    (f : Fin r → ↑(Osharp.obj.obj (op (⊤ : Opens ↥X))))
    (hφ : ∀ k : Fin r,
      ((SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).freeHomEquiv φ
        (ULift.up k)).val (op (⊤ : Opens ↥X)) = f k) (x : ↥X) :
    ∃ e : (((stalkAbFunctor Osharp x).mapHomologicalComplex (ComplexShape.down ℤ)).obj
          K.chain) ≅
        ((koszulAbFunctor Osharp x).mapHomologicalComplex (ComplexShape.down ℤ)).obj
          (((Koszul.seqComplex fun k =>
                TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x)
                  (f k)).extend ComplexShape.embeddingDownNat).restriction
            ComplexShape.embeddingDownIntUpInt),
      ∀ (n : ℕ) (U : Opens ↥X) (hx : x ∈ U) (a : ↑(Osharp.obj.obj (op U)))
          (i : Fin n → Fin r),
        ((Koszul.seqComplex fun k =>
              TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x)
                (f k)).extendXIso ComplexShape.embeddingDownNat (i := n) rfl).hom
          ((e.hom.f (n : ℤ))
            ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
                (K.chain.X ((n : ℕ) : ℤ)).val.presheaf U x hx)
              (((eqToHom (K.chain_X ((n : ℕ) : ℤ)).symm).val.app (op U))
                (a • exteriorBasisSection (koszulAlgebras Osharp r) U n i)))) =
          TopCat.Presheaf.germ Osharp.obj U x hx a •
            (⟨ExteriorAlgebra.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
                fun j => Pi.single (i j) 1, Koszul.ιMulti_mem n _⟩ :
              ↥(⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^n
                (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x)))) :=
  K.exists_stalkChainIso f hφ x

end KoszulChainData

end Koszul

end Stacks.RegularSequence

end

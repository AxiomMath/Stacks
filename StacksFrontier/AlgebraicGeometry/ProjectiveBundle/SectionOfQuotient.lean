module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ClassifyingData
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.UniversalGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransport
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTwisting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictTensorator
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleBridge
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Sections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A section of `𝐏(E) ⟶ X` from an invertible quotient of `E`

Let `X` be a scheme, `E` a quasi-coherent `𝒪_X`-module and `π : 𝐏(E) ⟶ X` the projection of the
projective bundle of `E`. Tag 0B3V asserts a bijection between the sections of `π` and the
surjections `E ⟶ ℒ` onto invertible `𝒪_X`-modules. This file proves the direction that
**produces a section**: every such surjection determines a morphism `σ : X ⟶ 𝐏(E)` with
`σ ≫ π = 𝟙 X`.

The construction is Section 01NS's functor of quadruples at degree one over `𝟙_X`. A quadruple
`(d, f, ℒ, ψ)` there is an invertible module `ℒ` on the test scheme together with a homomorphism
of sheaves of graded algebras `ψ : f^*𝒜^{(d)} ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` whose degree-one component is
surjective, and `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.classifyingHom` — backed by
the unconditional representability of that functor, Tag 01NZ — classifies such a quadruple by a
morphism into `Proj_X(𝒜)` over `X`. For `𝒜 = Sym(E)`, `f = 𝟙_X` and `d = 1` the quadruple is
built out of the surjection `q : E ⟶ ℒ` by the **universal property of the symmetric algebra**:
the pullback of `Sym(E)` along `𝟙_X` is a symmetric algebra of `(𝟙_X)^*E`
(`Stacks.RingedSpace.isSymmetricAlgebra_pullbackGradedAlgebra`), the Laurent algebra
`⨁_{n ∈ ℤ} ℒ^{⊗ n}` has commuting degree-one local sections because `ℒ` is invertible, and so `q`
extends uniquely to a unital homomorphism `(𝟙_X)^*Sym(E) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`.

No local triviality of `ℒ`, no cover of `X` and no gluing of local morphisms is used, and `E` is
arbitrary quasi-coherent: in particular nothing here is restricted to an `E` of rank one or to a
direct sum of invertible modules.

## Main definitions

* `Stacks.RelativeProj.twistingOfUnitalHom`: **the map `ψ` of a quadruple at `d = 1` out of a
  unital homomorphism of sheaves of graded algebras `f^*𝒜 ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}`,** as a
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting`.
* `Stacks.RelativeProj.quotientUnitalHom`: the unital homomorphism
  `(𝟙_X)^*Sym(E) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` that `q : E ⟶ ℒ` determines.
* `Stacks.RelativeProj.quadrupleOfQuotient`: that homomorphism as a quadruple of Section 01NS of
  degree one over `𝟙_X`.
* `Stacks.RelativeProj.sectionOfInvertibleQuotient`: **the section of `π : 𝐏(E) ⟶ X` attached to
  a surjection `q : E ⟶ ℒ` onto an invertible `𝒪_X`-module.**
* `Stacks.RelativeProj.sectionOfQuotient`: the same, taking a
  `Stacks.Divisors.InvertibleQuotient` as its input.

## Main results

* `Stacks.RelativeProj.oneHom_pullbackGradedAlgebra`: **the two pullbacks of a sheaf of graded
  algebras have the same global unit.** `Stacks.RingedSpace.pullbackGradedAlgebra` takes its
  multiplication and unit stalkwise and is the one whose universality for the symmetric algebra
  is proved, while `Twisting.app_one` is stated with
  `Stacks.PullbackGradedAlgebra.pullbackOne`, the unit transported along the monoidal pullback;
  this identifies the two units. The two multiplications were already identified, each being
  the multiplication of `𝒜` conjugated by the comparison of Tag 01CD.
* `Stacks.RelativeProj.isSymmetricAlgebra_symmetricAlgebraOfQuasicoherent`: the graded algebra of
  the projective-bundle situation of `E` is the symmetric algebra of `E`, with its degree-one
  generator out of `E` itself.
* `Stacks.RelativeProj.epi_quotientUnitalHom_app_one`: the degree-one component of the unital
  homomorphism is surjective, which is the quadruple's remaining clause. It holds because the
  component is precomposed with the pullback of the degree-one generator of `Sym(E)` to give the
  surjection `q`.
* `Stacks.RelativeProj.sectionOfInvertibleQuotient_comp_projectiveBundleToBase`: **the morphism
  is a section of `π`.**
* `Stacks.RelativeProj.strictlyEquivalent_of_classifyingHom_eq`: **a quadruple of positive degree
  is determined up to strict equivalence by the morphism it classifies**, the inclusion of the
  degree-`d` open of relative `Proj` being a monomorphism and the representation of `F_d` a
  bijection.
* `Stacks.RelativeProj.exists_iso_of_sectionOfInvertibleQuotient_eq`: hence **two surjections
  onto invertible modules with the same section differ by an isomorphism of their targets** —
  `q ≫ α = q'` for an isomorphism `α : ℒ ≅ ℒ'`. So the map of Tag 0B3V from invertible quotients
  of `E`, taken up to isomorphism of the quotient module, to sections of `π` is injective.
* `Stacks.RelativeProj.isClosedImmersion_sectionOfInvertibleQuotient`: it is a closed immersion,
  by `Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase`.

## Implementation notes

**The degree bookkeeping `n * 1 = n` is isolated in two statements with free degrees.**
`Stacks.RelativeProj.unitalHom_app_mul_of_eq` and `unitalHom_app_one_of_eq` take the source
degrees as variables together with the equalities identifying them, so that `subst` turns every
`eqToHom` into an identity and the aligned statements apply; `n * 1 = n` is not `rfl` for an
integer, so it cannot be rewritten inside the dependent types. This is the device
`Stacks.AlgebraicGeometry.ProjRepresentsF1.laurentApp_app_mul_of_eq` uses for the same purpose.

**`Stacks.RelativeProj.symmetricAlgebraOfQuasicoherent` has a declared type, and that is the
point.** `(symmetricSituationOfQuasicoherent X E).algebra` records its base as
`(symmetricSituationOfQuasicoherent X E).base.ringCatSheaf`, and a type ascription at the
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace` spelling would only *check*: the
recorded argument would stay the unascribed one, and the goals of every later `rw` would fail to
be type-correct at `implicit` transparency. A definition with the type written down pins it.

**Three `Epi` facts are supplied as terms rather than found.** `Epi` of an `eqToHom`, of the
inverse of `Stacks.SheafOfModules.TensorPower.tensorPowerOneIso` and of a composite of those
with `q` are not reached by instance search, the invertibility and the composition reaching the
`Category` instance of the sheaves of modules by two different routes;
`Stacks.AlgebraicGeometry.ProjRepresentsF1.epi_isoHom_comp_comp_isoHom`, which is stated in an
arbitrary category with every object and morphism free, is what applies.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf AlgebraicGeometry Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackMonoidalSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open SheafOfModules.GradedAlgebra Stacks.PullbackTensorCoherence

universe u

namespace Stacks.RelativeProj

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal

section Twisting

variable {S T : Scheme.{u}} (f : T ⟶ S)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))

/-- The global unit of the stalkwise pullback of a sheaf of graded algebras is the global unit
produced by the monoidal pullback. -/
theorem oneHom_pullbackGradedAlgebra :
    SheafOfModules.GradedAlgebra.oneHom
        (Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom f) A) =
      Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A := by
  refine ((((Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom f) A).piece
    0).unitHomEquiv).injective ?_)
  refine Stacks.AlgebraicGeometry.AffineTwisting.sections_eq_of_eval_top _ _ _ ?_
  refine Eq.trans (congrArg (fun z => PresheafOfModules.sections.eval z (op ⊤))
    (SheafOfModules.GradedAlgebra.unitHomEquiv_oneHom
      (Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom f) A))) ?_
  refine Eq.trans ?_ (Stacks.PullbackTensorCoherence.unitHomEquiv_eval _ _ (op ⊤)).symm
  refine Eq.trans ?_
    (Stacks.AlgebraicGeometry.AffineTwisting.pullbackOne_val_app_oneSec f A).symm
  exact Stacks.RingedSpace.pullbackGradedAlgebra_one_eval (ringedSpaceHom f) A ⊤

variable (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom f) A) (laurent L))

/-- The multiplicativity of `Φ` in the shape `Twisting.app_mul` has, but with the degrees not
shifted by `n * 1`. -/
theorem unitalHom_mulSheaf_aligned (i j : ℤ) :
    MonoidalCategoryStruct.tensorHom (Φ.app i) (Φ.app j) ≫ (laurent L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece i) (A.piece j)) ≫
        (pullbackFunctor (ringedSpaceHom f)).map (A.mulSheaf i j) ≫ Φ.app (i + j) := by
  refine (unitalHom_mulSheaf_comp Φ i j).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ Φ.app (i + j))
    (Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra (ringedSpaceHom f) A i j)) ?_
  exact Category.assoc _ _ _

/-- The multiplicativity clause of `Twisting`, with the three source degrees as variables. -/
theorem unitalHom_app_mul_of_eq (i j i' j' k' : ℤ)
    (hi : i' = i) (hj : j' = j) (hk : k' = i + j) (h : i' + j' = k') :
    MonoidalCategoryStruct.tensorHom
          (eqToHom (congrArg
            (fun n : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece n)) hi) ≫ Φ.app i)
          (eqToHom (congrArg
            (fun n : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece n)) hj) ≫ Φ.app j) ≫
        (laurent L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece i') (A.piece j')) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (A.mulSheaf i' j' ≫ eqToHom (congrArg A.piece h)) ≫
          (eqToHom (congrArg
            (fun n : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece n)) hk) ≫
            Φ.app (i + j)) := by
  have := Stacks.PullbackTensorCoherence.isIso_pullbackTensorComparison
    (ringedSpaceHom f) (A.piece i') (A.piece j')
  subst hi
  subst hj
  subst hk
  simp only [eqToHom_refl]
  exact unitalHom_mulSheaf_aligned f A L Φ i' j'

/-- The unit clause of `Twisting`, with the source degree as a variable. -/
theorem unitalHom_app_one_of_eq (k' : ℤ) (hk : k' = 0) (h : (0 : ℤ) = k') :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece h)) ≫
          (eqToHom (congrArg
            (fun n : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece n)) hk) ≫
            Φ.app 0) =
      oneHom (laurent L) := by
  subst hk
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← oneHom_pullbackGradedAlgebra f A]
  exact oneHom_comp_app_zero Φ

/-- **The map `ψ` of a quadruple of Section 01NS, at `d = 1`, out of a unital homomorphism of
sheaves of graded algebras `f^*𝒜 ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}`.** -/
def twistingOfUnitalHom : Twisting f A 1 L where
  app n := eqToHom (congrArg
    (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece k)) (mul_one n)) ≫ Φ.app n
  app_mul i j := unitalHom_app_mul_of_eq f A L Φ i j (i * 1) (j * 1) ((i + j) * 1)
    (mul_one i) (mul_one j) (mul_one (i + j)) (by ring)
  app_one := unitalHom_app_one_of_eq f A L Φ (0 * 1) (mul_one 0) (by ring)

/-- The degree-`n` component of `twistingOfUnitalHom` is the transport along `n * 1 = n` followed
by the degree-`n` component of `Φ`. -/
@[simp] theorem twistingOfUnitalHom_app (n : ℤ) :
    (twistingOfUnitalHom f A L Φ).app n =
      eqToHom (congrArg
        (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece k)) (mul_one n)) ≫
      Φ.app n :=
  rfl

/-- The degree-`n` component of `twistingOfUnitalHom` is surjective when that of `Φ` is: the two
differ by the transport along `n * 1 = n`. -/
theorem epi_twistingOfUnitalHom_app (n : ℤ) [Epi (Φ.app n)] :
    Epi ((twistingOfUnitalHom f A L Φ).app n) := by
  have h1 : Epi (eqToHom (congrArg
      (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece k)) (mul_one n))) :=
    inferInstance
  exact epi_comp' h1 ‹Epi (Φ.app n)›

end Twisting

section SectionOfQuotient

variable (X : Scheme.{u}) (E : X.Modules) [E.IsQuasicoherent]

/-- **The symmetric algebra of `E`**, as the graded algebra of the projective-bundle situation of
`E` read at the `Stacks.RingedSpace.structureRingSheaf` spelling of the structure ring sheaf. The
type is declared, which pins the base of the category of sheaves of modules; a type ascription
on `(symmetricSituationOfQuasicoherent X E).algebra` would only check, leaving the recorded base
the one read off the situation. -/
def symmetricAlgebraOfQuasicoherent :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace) :=
  (symmetricSituationOfQuasicoherent X E).algebra

/-- The degree-one generator `E ⟶ Sym¹(E)` of the symmetric algebra of `E`. -/
def symmetricAlgebraOfQuasicoherentGen :
    E ⟶ (symmetricAlgebraOfQuasicoherent X E).piece 1 :=
  SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X) E

/-- **The graded algebra of the projective-bundle situation of `E` is the symmetric algebra of
`E`**, with the degree-one generator out of `E` itself. -/
theorem isSymmetricAlgebra_symmetricAlgebraOfQuasicoherent :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra
      (symmetricAlgebraOfQuasicoherent X E) (symmetricAlgebraOfQuasicoherentGen X E) :=
  SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra _ E

variable (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L]
  (q : E ⟶ L)

/-- The degree-one generator `(𝟙_X)^*E ⟶ L^{⊗ 1}` of the Laurent algebra of `L` that a
morphism `q : E ⟶ L` determines. -/
def quotientGenerator :
    (pullbackFunctor (ringedSpaceHom (𝟙 X))).obj E ⟶ (laurent L).piece 1 :=
  haveI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    X.toRingedSpace.presheaf (isSheafStruct X) L
  (Scheme.Modules.pullbackId X).hom.app E ≫ q ≫
    (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso X.toRingedSpace.presheaf
      (isSheafStruct X) L).inv

omit [SheafOfModules.IsQuasicoherent E] in
/-- The degree-one generator of the Laurent algebra has pairwise commuting image: homogeneous
multiplication in the Laurent algebra of an invertible module is commutative. -/
theorem pairwiseCommutes_quotientGenerator :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (quotientGenerator X E L q) := fun U _ _ =>
  eq_of_heq (Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm
    X.toRingedSpace.presheaf (isSheafStruct X) L 1 1 U _ _)

/-- **The unital homomorphism `(𝟙_X)^*Sym(E) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` that a morphism `E ⟶ L` onto an
invertible module determines**, by the universal property of the symmetric algebra: the pullback
of `Sym(E)` is the symmetric algebra of the pullback of `E`, and the Laurent algebra of an
invertible module has commuting degree-one sections. -/
def quotientUnitalHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom (𝟙 X))
        (symmetricAlgebraOfQuasicoherent X E)) (laurent L) :=
  (Stacks.RingedSpace.isSymmetricAlgebra_pullbackGradedAlgebra (ringedSpaceHom (𝟙 X))
      (isSymmetricAlgebra_symmetricAlgebraOfQuasicoherent X E)).isUniversal.desc (laurent L)
    (quotientGenerator X E L q) (pairwiseCommutes_quotientGenerator X E L q)

/-- The unital homomorphism extends the given generator in degree one. -/
theorem quotientUnitalHom_app_one :
    (pullbackFunctor (ringedSpaceHom (𝟙 X))).map (symmetricAlgebraOfQuasicoherentGen X E) ≫
        (quotientUnitalHom X E L q).app 1 =
      quotientGenerator X E L q :=
  (Stacks.RingedSpace.isSymmetricAlgebra_pullbackGradedAlgebra (ringedSpaceHom (𝟙 X))
      (isSymmetricAlgebra_symmetricAlgebraOfQuasicoherent X E)).isUniversal.desc_extends
    (laurent L) (quotientGenerator X E L q) (pairwiseCommutes_quotientGenerator X E L q)

/-- The degree-one generator is surjective when `q` is: it is `q` composed with two
isomorphisms. -/
instance epi_quotientGenerator [Epi q] : Epi (quotientGenerator X E L q) := by
  have := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    X.toRingedSpace.presheaf (isSheafStruct X) L
  exact Stacks.AlgebraicGeometry.ProjRepresentsF1.epi_isoHom_comp_comp_isoHom
    (asIso ((Scheme.Modules.pullbackId X).hom.app E)) q
    (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso X.toRingedSpace.presheaf
      (isSheafStruct X) L).symm ‹Epi q›

/-- **The degree-one component of the unital homomorphism is surjective.** Precomposed with the
pullback of the degree-one generator of `Sym(E)` it is the surjection `q`, and a morphism through
which a surjection factors is a surjection. -/
theorem epi_quotientUnitalHom_app_one [Epi q] : Epi ((quotientUnitalHom X E L q).app 1) := by
  have h : Epi ((pullbackFunctor (ringedSpaceHom (𝟙 X))).map
      (symmetricAlgebraOfQuasicoherentGen X E) ≫ (quotientUnitalHom X E L q).app 1) := by
    rw [quotientUnitalHom_app_one]
    infer_instance
  exact epi_of_epi ((pullbackFunctor (ringedSpaceHom (𝟙 X))).map
    (symmetricAlgebraOfQuasicoherentGen X E)) ((quotientUnitalHom X E L q).app 1)

/-- **The quadruple of Section 01NS, at `d = 1` and over `𝟙_X`, that a surjection of `E` onto an
invertible module determines.** -/
def quadrupleOfQuotient [Epi q] :
    Quadruple (𝟙 X) (symmetricAlgebraOfQuasicoherent X E) 1 where
  L := L
  isInvertible := inferInstance
  twisting := twistingOfUnitalHom (𝟙 X) _ L (quotientUnitalHom X E L q)
  epi_app_one :=
    haveI := epi_quotientUnitalHom_app_one X E L q
    epi_twistingOfUnitalHom_app (𝟙 X) _ L (quotientUnitalHom X E L q) 1

/-- **A surjection `q : E ⟶ ℒ` onto an invertible `𝒪_X`-module determines a section of
`π : 𝐏(E) ⟶ X`.** This is the direction of Tag 0B3V's bijection that produces a section: `q`
determines a unital homomorphism `(𝟙_X)^*Sym(E) ⟶ ⨁_n ℒ^{⊗ n}` of sheaves of graded algebras
whose degree-one component is surjective — a quadruple of Section 01NS of degree one over
`𝟙_X` — and the representability of the functor of quadruples classifies that quadruple by a
morphism `X ⟶ 𝐏(E)` over `X`. -/
@[stacks 0B3V "from an invertible quotient to a section: the construction"]
def sectionOfInvertibleQuotient [Epi q] : X ⟶ projectiveBundle X E :=
  Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.classifyingHom
    (symmetricSituationOfQuasicoherent X E) Int.one_pos (quadrupleOfQuotient X E L q)

/-- **The morphism of `sectionOfInvertibleQuotient` is a section of `π : 𝐏(E) ⟶ X`.** -/
@[stacks 0B3V "from an invertible quotient to a section: it is a section of the projection"]
theorem sectionOfInvertibleQuotient_comp_projectiveBundleToBase [Epi q] :
    sectionOfInvertibleQuotient X E L q ≫ projectiveBundleToBase X E = 𝟙 X :=
  Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.classifyingHom_comp_toBase
    (symmetricSituationOfQuasicoherent X E) Int.one_pos (quadrupleOfQuotient X E L q)

/-- **The section attached to an invertible quotient is a closed immersion**, by
`Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase`. -/
instance isClosedImmersion_sectionOfInvertibleQuotient [Epi q] :
    IsClosedImmersion (sectionOfInvertibleQuotient X E L q) :=
  isClosedImmersion_of_section_projectiveBundleToBase X E _
    (sectionOfInvertibleQuotient_comp_projectiveBundleToBase X E L q)

/-- **The section of `π : 𝐏(E) ⟶ X` attached to an invertible quotient of `E`**, taking the
quotient in the packaged form `Stacks.Divisors.InvertibleQuotient`. The two Tag 01CS
invertibility classes are crossed once, by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
@[sga "4 XVIII 1.3.3" "partial"]
def sectionOfQuotient (Q : Stacks.Divisors.InvertibleQuotient X E) : X ⟶ projectiveBundle X E :=
  @sectionOfInvertibleQuotient X E _ Q.L
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr Q.invertible) Q.q Q.epi

/-- **The morphism of `sectionOfQuotient` is a section of `π : 𝐏(E) ⟶ X`.** -/
theorem sectionOfQuotient_comp_projectiveBundleToBase
    (Q : Stacks.Divisors.InvertibleQuotient X E) :
    sectionOfQuotient X E Q ≫ projectiveBundleToBase X E = 𝟙 X :=
  @sectionOfInvertibleQuotient_comp_projectiveBundleToBase X E _ Q.L
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr Q.invertible) Q.q Q.epi

/-! ### A section determines the quadruple it classifies -/

/-- **A quadruple of positive degree is determined, up to strict equivalence, by the morphism it
classifies.** The classifying morphism is the representing bijection of `F_d` followed by the
inclusion of the degree-`d` open of relative `Proj`, and that inclusion is a monomorphism; so
two quadruples with the same classifying morphism have the same class in `F_d(T)`, which by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.mk_eq_mk_iff` is strict equivalence. -/
theorem strictlyEquivalent_of_classifyingHom_eq (s : Situation.{u}) {T : Scheme.{u}}
    {f : T ⟶ s.base} {d : ℤ} (hd : 0 < d) (P P' : Quadruple f s.algebra d)
    (h : Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.classifyingHom s hd P =
      Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.classifyingHom s hd P') :
    Quadruple.StrictlyEquivalent P P' :=
  (Fd.mk_eq_mk_iff P P').mp
    ((Fd.degreeOpenEquiv'
      (Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.sheafGradedAlgebra s)
      (Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.relativeProjData s) hd T).injective
      ((cancel_mono (((Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.relativeProjData
        s).degreeOpen d.toNat).ι)).mp h))

/-- The degree-one generator, followed by the identification `ℒ^{⊗ 1} ≅ ℒ`, is `q` read out of
the pullback of `E` along `𝟙_X`. -/
theorem quotientGenerator_comp_oneIso_hom [Epi q] :
    quotientGenerator X E L q ≫ (quadrupleOfQuotient X E L q).oneIso.hom =
      (Scheme.Modules.pullbackId X).hom.app E ≫ q := by
  have := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    X.toRingedSpace.presheaf (isSheafStruct X) L
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun z => (Scheme.Modules.pullbackId X).hom.app E ≫ z) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun z => q ≫ z) (Iso.inv_hom_id _)).trans (Category.comp_id _)

/-- **Two surjections onto invertible modules determining the same section of `π` differ by an
isomorphism of their targets.** This is the injectivity of Tag 0B3V's map from invertible
quotients to sections: the two quadruples are strictly equivalent, which gives an isomorphism
`β : ℒ ≅ ℒ'` carrying one twisting to the other, and in degree one that equation — precomposed
with the pullback of the degree-one generator of `Sym(E)` and postcomposed with the
identification `(ℒ')^{⊗ 1} ≅ ℒ'` — is `q ≫ β = q'`. -/
@[stacks 0B3V "from an invertible quotient to a section: the map is injective, i.e. a section \
determines the invertible quotient it comes from up to isomorphism of the quotient module"]
theorem exists_iso_of_sectionOfInvertibleQuotient_eq [Epi q]
    (L' : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L']
    (q' : E ⟶ L') [Epi q']
    (h : sectionOfInvertibleQuotient X E L q = sectionOfInvertibleQuotient X E L' q') :
    ∃ α : L ≅ L', q ≫ α.hom = q' := by
  obtain ⟨β, γ, hγ1, hγ⟩ := strictlyEquivalent_of_classifyingHom_eq
    (symmetricSituationOfQuasicoherent X E) Int.one_pos
    (quadrupleOfQuotient X E L q) (quadrupleOfQuotient X E L' q') h
  refine ⟨β, ?_⟩
  have hone : (quotientUnitalHom X E L q).app 1 ≫ γ.hom.app 1 =
      (quotientUnitalHom X E L' q').app 1 :=
    (cancel_epi (eqToHom (congrArg (fun k : ℤ =>
      (pullbackFunctor (ringedSpaceHom (𝟙 X))).obj
        ((symmetricAlgebraOfQuasicoherent X E).piece k)) (mul_one (1 : ℤ))))).mp
      ((Category.assoc _ _ _).symm.trans (hγ 1))
  have hkey : quotientGenerator X E L q ≫ γ.hom.app 1 = quotientGenerator X E L' q' :=
    Eq.trans (Eq.trans (congrArg (fun z => z ≫ γ.hom.app 1)
        (quotientUnitalHom_app_one X E L q).symm)
      ((Category.assoc _ _ _).trans (congrArg
        (fun z => (pullbackFunctor (ringedSpaceHom (𝟙 X))).map
          (symmetricAlgebraOfQuasicoherentGen X E) ≫ z) hone)))
      (quotientUnitalHom_app_one X E L' q')
  rw [hγ1] at hkey
  have hβ : (quadrupleOfQuotient X E L q).oneIso.hom ≫ β.hom =
      (Quadruple.pieceOneIso β).hom ≫ (quadrupleOfQuotient X E L' q').oneIso.hom := by
    simp
  have hkey2 : (quotientGenerator X E L q ≫ (quadrupleOfQuotient X E L q).oneIso.hom) ≫ β.hom =
      quotientGenerator X E L' q' ≫ (quadrupleOfQuotient X E L' q').oneIso.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => quotientGenerator X E L q ≫ z) hβ).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ (quadrupleOfQuotient X E L' q').oneIso.hom) hkey)))
  rw [quotientGenerator_comp_oneIso_hom, quotientGenerator_comp_oneIso_hom] at hkey2
  exact (cancel_epi ((Scheme.Modules.pullbackId X).hom.app E)).mp
    ((Category.assoc _ _ _).symm.trans hkey2)

end SectionOfQuotient

end Stacks.RelativeProj

end

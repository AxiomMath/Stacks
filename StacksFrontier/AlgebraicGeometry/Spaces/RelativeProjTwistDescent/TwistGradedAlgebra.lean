module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGradedAlgebraOfMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraLaws

/-!
# The sheaf of `ℤ`-graded algebras `⨁_{n ∈ ℤ} 𝒪_P(n)` on a relative Proj

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of the quasi-coherent
graded `𝒪_X`-algebra `𝒜` on the algebraic space `X`.  The twists `𝒪_P(n)`
(`AlgebraicGeometry.Space.RelativeProjSituation.twistModule`), their multiplication
`𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` (`…twistAlgebraMul`) and their unit `𝒪_P ⟶ 𝒪_P(0)`
(`…twistAlgebraUnit`) are descended along a presentation `P = P_U/P_R` from the twists of
Stacks 01NR on the scheme of `P_U`, and they satisfy the algebra laws as equalities of morphisms
(`…twistAlgebraMul_assoc`, `…twistAlgebraUnit_mul`, `…twistAlgebraMul_unit`).  This file
assembles them into a sheaf of `ℤ`-graded `𝒪_P`-algebras in the sense of
`SheafOfModules.GradedAlgebra` — the structure in which the graded algebra `𝒜` of Situation 0849
itself and the scheme-level graded algebras of Stacks 01NR are stated — whose homogeneous pieces
are the twists `𝒪_P(n)`, all quasi-coherent: the first assertion of Stacks 084D.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationGradedAlgebra`: the sheaf of
  graded algebras on `P` descended along the presentation `P = P_U/P_R` from quasi-coherent
  modules `M_n` on the scheme of `P_U` with transitions, a multiplication and a unit compatible
  with the transitions and satisfying the algebra laws there.
* `AlgebraicGeometry.Space.QuasicoherentMulAssoc`, `AlgebraicGeometry.Space.QuasicoherentOneMul`
  and `AlgebraicGeometry.Space.QuasicoherentMulComm`: associativity, the left unit law and
  commutativity of a graded multiplication of quasi-coherent modules on the scheme of an object of
  the site, as named propositions.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistGradedAlgebra`: **the quasi-coherent sheaf of
  `ℤ`-graded `𝒪_P`-algebras `⨁_{n ∈ ℤ} 𝒪_P(n)`** (Stacks 084D).

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.twistGradedAlgebra_piece`: its `n`-th
  homogeneous piece is the twist `𝒪_P(n)`, on the nose.
* `AlgebraicGeometry.Space.RelativeProjSituation.isQuasicoherentOnSite_twistGradedAlgebra_piece`:
  every homogeneous piece is quasi-coherent.
* `AlgebraicGeometry.Space.RelativeProjSituation.mulSheaf_twistGradedAlgebra` and
  `…oneHom_twistGradedAlgebra`: its multiplication and its unit, as morphisms of sheaves of
  modules, are `…twistAlgebraMul` and `…twistAlgebraUnit`.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistGradedAlgebra_mul_comm`: it is commutative.
* `AlgebraicGeometry.Space.RelativeProjSituation.quasicoherentMulAssoc_twistPieceMul`,
  `…quasicoherentOneMul_twistPieceUnit` and `…quasicoherentMulComm_twistPieceMul`: the laws of the
  twists of Stacks 01NR on the scheme of a base change, as the named propositions
  `AlgebraicGeometry.Space.QuasicoherentMulAssoc`, `…QuasicoherentOneMul` and
  `…QuasicoherentMulComm` that the construction consumes.

## Implementation notes

The multiplication `…twistAlgebraMul` is a morphism out of the tensor product of
`AlgebraicGeometry.Space.modulesMonoidalCategory`, the localization along sheafification of the
objectwise tensor product; `SheafOfModules.GradedAlgebra.ofLocalizedMorphismData`, specialized to
`𝒪_P`-modules as `AlgebraicGeometry.Space.modulesGradedAlgebraOfMorphisms`, conjugates it by
the identification `Stacks.SheafOfModules.tensorObjIso` with the tensor product sheaf and reads the
result on local sections.

The structure is first built at the level of a general presentation datum, with every input a
variable, and only then instantiated at the twists: as recorded for
`…twistAlgebraMul_assoc`, terms that apply lemmas to the presentation of `P` at the twists are
expensive for the kernel, while the same terms at variables are free, so the instance at the
twists is a single application.  The three laws enter it as the named propositions
`AlgebraicGeometry.Space.QuasicoherentMulAssoc`, `…QuasicoherentOneMul` and
`…QuasicoherentMulComm`, which the kernel compares argument by argument rather than through the
types of the twists (the device of
`AlgebraicGeometry.Space.RelativeProjPoints.TransitionMulCompat`).

The statements naming `SheafOfModules.GradedAlgebra.mulSheaf` and
`SheafOfModules.GradedAlgebra.oneHom` put the sheafification instances of the small étale site
(`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`,
`AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective`) in the local context and pin the
universes: these instances have low priority, and with the imports of this file instance search
otherwise tries a universe-polymorphic instance first and is left with an unsolvable universe
constraint.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open scoped TensorProduct

universe u m

namespace AlgebraicGeometry.Space

section Laws

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (U : BigFppfOver B S hS)
  {Mn : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
  (m : ∀ i j, quasicoherentTensorObj B S hS U (Mn i) (Mn j) ⟶ Mn (i + j))
  (ν : quasicoherentUnitObj B S hS U ⟶ Mn 0)

/-- **Associativity of a graded multiplication of quasi-coherent modules on the scheme of `U`**,
as an equation of morphisms out of `(M_i ⊗ M_j) ⊗ M_k`, up to the identification of the degrees.

It is a named proposition so that a construction taking it as an argument can be instantiated
inside a definition: written out, the instantiated equation is compared with the statement that
proves it through the deep types of the modules, which exhausts the kernel's budget at the twists
of a relative Proj, while this name is compared argument by argument. -/
def QuasicoherentMulAssoc : Prop :=
  ∀ i j k, quasicoherentTensorHom B S hS U (m i j) (𝟙 (Mn k)) ≫ m (i + j) k =
    (quasicoherentAssociator B S hS U (Mn i) (Mn j) (Mn k)).hom ≫
      quasicoherentTensorHom B S hS U (𝟙 (Mn i)) (m j k) ≫ m i (j + k) ≫
      eqToHom (congrArg Mn (add_assoc i j k).symm)

/-- **A morphism `ν : 𝒪 ⟶ M_0` is a left unit for a graded multiplication of quasi-coherent
modules on the scheme of `U`**, up to the identification of the degrees; a named proposition for
the reason given at `AlgebraicGeometry.Space.QuasicoherentMulAssoc`. -/
def QuasicoherentOneMul : Prop :=
  ∀ n, quasicoherentTensorHom B S hS U ν (𝟙 (Mn n)) ≫ m 0 n =
    (quasicoherentLeftUnitor B S hS U (Mn n)).hom ≫ eqToHom (congrArg Mn (zero_add n).symm)

/-- **Commutativity of a graded multiplication of quasi-coherent modules on the scheme of `U`**,
up to the identification of the degrees; a named proposition for the reason given at
`AlgebraicGeometry.Space.QuasicoherentMulAssoc`. -/
def QuasicoherentMulComm : Prop :=
  ∀ i j, (quasicoherentBraiding B S hS U (Mn i) (Mn j)).hom ≫ m j i =
    m i j ≫ eqToHom (congrArg Mn (add_comm i j))

end Laws

namespace RelativeProjPoints

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P) {Mn : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ : ∀ n, quasicoherentPullbackObj B S hS (d.spaceTarget Px hP) (Mn n) ⟶
    quasicoherentPullbackObj B S hS (d.spaceSource Px hP) (Mn n))
  (hc : ∀ n, PresentationSchemeCocycle (d.spacePresentation Px hP) (Mn n) (τ n))
  (hu : ∀ n, PresentationSchemeUnit (d.spacePresentation Px hP) (Mn n) (τ n))
  (m : ∀ i j, quasicoherentTensorObj B S hS (d.fibre Px.U Px.toSpace) (Mn i) (Mn j) ⟶ Mn (i + j))
  (hbt : ∀ i j, RepresentedC3TensorCompat B S hS (d.spaceTarget Px hP) (Mn i) (Mn j))
  (hbs : ∀ i j, RepresentedC3TensorCompat B S hS (d.spaceSource Px hP) (Mn i) (Mn j))
  (hm : ∀ i j, d.TransitionMulCompat Px hP (τ i) (τ j) (τ (i + j)) (m i j))
  (ν : quasicoherentUnitObj B S hS (d.fibre Px.U Px.toSpace) ⟶ Mn 0)
  (hbtu : RepresentedC3UnitCompat B S hS (d.spaceTarget Px hP))
  (hbsu : RepresentedC3UnitCompat B S hS (d.spaceSource Px hP))
  (hmu : d.TransitionUnitCompat Px hP (τ 0) ν)
  (hassoc : QuasicoherentMulAssoc (d.fibre Px.U Px.toSpace) m)
  (hone : QuasicoherentOneMul (d.fibre Px.U Px.toSpace) m ν)
  (hcomm : QuasicoherentMulComm (d.fibre Px.U Px.toSpace) m)

/-- **The sheaf of graded algebras descended along the presentation `P = P_U/P_R`.**  For
quasi-coherent modules `M_n` on the scheme of `P_U = U ×_X P` with scheme transitions `τ_n`, a
multiplication `m` and a unit `ν` compatible with the transitions, associative, unital and
commutative there, the sheaf of graded `𝒪_P`-algebras whose `n`-th piece is the descended module
`D(M_n)` (`AlgebraicGeometry.Space.presentationDescendedModule`), with the descended
multiplication and unit
(`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedMul`,
`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedUnit`).  Commutativity is
used for the right unit law, which is deduced from the left one. -/
def spacePresentationGradedAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS ⟨P, hP⟩) :=
  modulesGradedAlgebraOfMorphisms B S hS P hP
    (fun n => (presentationDescendedModule (d.spacePresentation Px hP) (Mn n) (τ n) (hc n)
      (hu n)).obj)
    (fun i j => d.spacePresentationDescendedMul Px hP (τ i) (τ j) (τ (i + j)) (m i j) (hc i)
      (hu i) (hc j) (hu j) (hc (i + j)) (hu (i + j)) (hbt i j) (hbs i j) (hm i j))
    (d.spacePresentationDescendedUnit Px hP (τ 0) ν (hc 0) (hu 0) hbtu hbsu hmu)
    (fun i j k => d.spacePresentationDescendedMul_assoc Px hP τ hc hu m hbt hbs hm hassoc i j k)
    (fun n => d.spacePresentationDescendedUnit_mul Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hone
      n)
    (fun n => d.spacePresentationDescendedMul_unit Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hone
      hcomm n)

/-- The homogeneous pieces of `spacePresentationGradedAlgebra` are the descended modules. -/
theorem spacePresentationGradedAlgebra_piece (n : ℤ) :
    (d.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hassoc hone
      hcomm).piece n =
      (presentationDescendedModule (d.spacePresentation Px hP) (Mn n) (τ n) (hc n) (hu n)).obj :=
  rfl

/-- **The morphism-level multiplication of `spacePresentationGradedAlgebra` is the descended
multiplication**, read out of the tensor product sheaf through
`AlgebraicGeometry.Space.modulesTensorObjIso`. -/
theorem mulSheaf_spacePresentationGradedAlgebra (i j : ℤ) :
    haveI := SmallEtale.instHasSheafify B S hS P AddCommGrpCat.{u}
    haveI := SmallEtale.instWEqualsLocallyBijective B S hS P AddCommGrpCat.{u}
    SheafOfModules.GradedAlgebra.mulSheaf.{u, u + 1, u, u} (J := SmallEtale.topology B S hS P)
        (d.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hassoc hone
          hcomm) i j =
      (modulesTensorObjIso B S hS P hP
          (presentationDescendedModule (d.spacePresentation Px hP) (Mn i) (τ i) (hc i) (hu i)).obj
          (presentationDescendedModule (d.spacePresentation Px hP) (Mn j) (τ j) (hc j)
            (hu j)).obj).inv ≫
        d.spacePresentationDescendedMul Px hP (τ i) (τ j) (τ (i + j)) (m i j) (hc i) (hu i)
          (hc j) (hu j) (hc (i + j)) (hu (i + j)) (hbt i j) (hbs i j) (hm i j) :=
  mulSheaf_modulesGradedAlgebraOfMorphisms B S hS P hP _ _ _ _ _ _ i j

/-- **The morphism-level unit of `spacePresentationGradedAlgebra` is the descended unit.** -/
theorem oneHom_spacePresentationGradedAlgebra :
    haveI := SmallEtale.instHasSheafify B S hS P AddCommGrpCat.{u}
    haveI := SmallEtale.instWEqualsLocallyBijective B S hS P AddCommGrpCat.{u}
    SheafOfModules.GradedAlgebra.oneHom.{u, u + 1, u} (J := SmallEtale.topology B S hS P)
        (d.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hassoc hone
          hcomm) =
      d.spacePresentationDescendedUnit Px hP (τ 0) ν (hc 0) (hu 0) hbtu hbsu hmu :=
  oneHom_modulesGradedAlgebraOfMorphisms B S hS P hP _ _ _ _ _ _

/-- **Homogeneous local sections of `spacePresentationGradedAlgebra` commute**, since the
descended multiplication of a commutative multiplication is commutative
(`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedMul_comm`). -/
theorem spacePresentationGradedAlgebra_mul_comm (i j : ℤ) (U : (SmallEtale B S hS P)ᵒᵖ)
    (x : ((d.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hassoc hone
      hcomm).piece i).val.obj U)
    (y : ((d.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hassoc hone
      hcomm).piece j).val.obj U) :
    HEq (((d.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hassoc hone
        hcomm).mul i j).app U x y)
      (((d.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hassoc hone
        hcomm).mul j i).app U y x) :=
  modulesGradedAlgebraOfMorphisms_mul_comm B S hS P hP _ _ _ _ _ _
    (fun i j => d.spacePresentationDescendedMul_comm Px hP τ hc hu m hbt hbs hm hcomm i j)
    i j U x y

end RelativeProjPoints

namespace RelativeProjSituation

attribute [local instance] modulesMonoidalCategory

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- The multiplication of the twists on the scheme of a base change is associative, as the named
proposition `AlgebraicGeometry.Space.QuasicoherentMulAssoc`. -/
theorem quasicoherentMulAssoc_twistPieceMul (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) :
    QuasicoherentMulAssoc (s.relativeProjPoints.fibre V v) (Mn := s.twistPieceQcoh V v)
      (s.twistPieceMul V v) :=
  s.twistPieceMul_assoc V v

/-- The unit of the twists on the scheme of a base change is a left unit, as the named
proposition `AlgebraicGeometry.Space.QuasicoherentOneMul`. -/
theorem quasicoherentOneMul_twistPieceUnit (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) :
    QuasicoherentOneMul (s.relativeProjPoints.fibre V v) (Mn := s.twistPieceQcoh V v)
      (s.twistPieceMul V v) (s.twistPieceUnit V v) :=
  s.twistPieceUnit_mul V v

/-- The multiplication of the twists on the scheme of a base change is commutative, as the named
proposition `AlgebraicGeometry.Space.QuasicoherentMulComm`. -/
theorem quasicoherentMulComm_twistPieceMul (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) :
    QuasicoherentMulComm (s.relativeProjPoints.fibre V v) (Mn := s.twistPieceQcoh V v)
      (s.twistPieceMul V v) :=
  s.twistPieceMul_comm V v

/-- **Stacks 084D, the graded algebra of twists: the quasi-coherent sheaf of `ℤ`-graded
`𝒪_P`-algebras `⨁_{n ∈ ℤ} 𝒪_P(n)` on the relative Proj `P = Proj_X(𝒜)`.**  Its `n`-th
homogeneous piece is the twist `𝒪_P(n)` (`…twistGradedAlgebra_piece`), quasi-coherent
(`…isQuasicoherentOnSite_twistGradedAlgebra_piece`); its multiplication is the
descended multiplication `AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedMul`
at the twists, which is `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul` by
definition, read on local sections through the identification of the tensor product of
`𝒪_P`-modules with the tensor product sheaf, and its unit is the descended unit
`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedUnit` at the twists, which is
`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit` by definition
(`…mulSheaf_twistGradedAlgebra`, `…oneHom_twistGradedAlgebra`).  All three are
descended along the presentation `P = P_U/P_R` from the twists of Stacks 01NR on the scheme of
`P_U`. -/
def twistGradedAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf s.site s.base s.containsBase
      ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩) :=
  s.relativeProjPoints.spacePresentationGradedAlgebra Px s.isAlgebraicSpace_relativeProjFunctor
    (Mn := s.twistPieceQcoh Px.U Px.toSpace) (s.twistTransition Px)
    (s.presentationSchemeCocycle_twistTransition Px) (s.presentationSchemeUnit_twistTransition Px)
    (s.twistPieceMul Px.U Px.toSpace)
    (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
    (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
    (s.transitionMulCompat_twistTransition Px)
    (s.twistPieceUnit Px.U Px.toSpace) (representedC3UnitCompat s.site s.base s.containsBase _)
    (representedC3UnitCompat s.site s.base s.containsBase _)
    (s.transitionUnitCompat_twistTransition Px)
    (s.quasicoherentMulAssoc_twistPieceMul Px.U Px.toSpace)
    (s.quasicoherentOneMul_twistPieceUnit Px.U Px.toSpace)
    (s.quasicoherentMulComm_twistPieceMul Px.U Px.toSpace)

/-- **The `n`-th homogeneous piece of `⨁_{n ∈ ℤ} 𝒪_P(n)` is the twist `𝒪_P(n)`**, on the nose. -/
theorem twistGradedAlgebra_piece (n : ℤ) :
    (s.twistGradedAlgebra Px).piece n = (s.twistModule Px n).obj :=
  rfl

/-- **Every homogeneous piece of `⨁_{n ∈ ℤ} 𝒪_P(n)` is quasi-coherent** (Stacks 084D). -/
theorem isQuasicoherentOnSite_twistGradedAlgebra_piece (n : ℤ) :
    ((s.twistGradedAlgebra Px).piece n).IsQuasicoherentOnSite :=
  s.isQuasicoherentOnSite_twistModule Px n

/-- **The multiplication of `⨁_{n ∈ ℤ} 𝒪_P(n)` is `twistAlgebraMul`**: as a morphism out of the
tensor product sheaf `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)`
(`SheafOfModules.GradedAlgebra.mulSheaf`), the multiplication of the graded algebra is
`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul`, read through the identification
`AlgebraicGeometry.Space.modulesTensorObjIso` of the tensor product of
`AlgebraicGeometry.Space.modulesMonoidalCategory` with the tensor product sheaf. -/
theorem mulSheaf_twistGradedAlgebra (i j : ℤ) :
    haveI := SmallEtale.instHasSheafify s.site s.base s.containsBase s.relativeProjFunctor
      AddCommGrpCat.{u}
    haveI := SmallEtale.instWEqualsLocallyBijective s.site s.base s.containsBase
      s.relativeProjFunctor AddCommGrpCat.{u}
    SheafOfModules.GradedAlgebra.mulSheaf.{u, u + 1, u, u}
        (J := SmallEtale.topology s.site s.base s.containsBase s.relativeProjFunctor)
        (s.twistGradedAlgebra Px) i j =
      (modulesTensorObjIso s.site s.base s.containsBase s.relativeProjFunctor
          s.isAlgebraicSpace_relativeProjFunctor (s.twistModule Px i).obj
          (s.twistModule Px j).obj).inv ≫ s.twistAlgebraMul Px i j :=
  s.relativeProjPoints.mulSheaf_spacePresentationGradedAlgebra Px _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i j

/-- **The unit of `⨁_{n ∈ ℤ} 𝒪_P(n)` is `twistAlgebraUnit`**: as a morphism `𝒪_P ⟶ 𝒪_P(0)`
(`SheafOfModules.GradedAlgebra.oneHom`), the global unit of the graded algebra is
`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit`. -/
theorem oneHom_twistGradedAlgebra :
    haveI := SmallEtale.instHasSheafify s.site s.base s.containsBase s.relativeProjFunctor
      AddCommGrpCat.{u}
    haveI := SmallEtale.instWEqualsLocallyBijective s.site s.base s.containsBase
      s.relativeProjFunctor AddCommGrpCat.{u}
    SheafOfModules.GradedAlgebra.oneHom.{u, u + 1, u}
        (J := SmallEtale.topology s.site s.base s.containsBase s.relativeProjFunctor)
        (s.twistGradedAlgebra Px) = s.twistAlgebraUnit Px :=
  s.relativeProjPoints.oneHom_spacePresentationGradedAlgebra Px _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **`⨁_{n ∈ ℤ} 𝒪_P(n)` is commutative**: homogeneous local sections of the graded algebra of
twists commute, up to the identification of the degrees `i + j = j + i`.  This is the
commutativity of the multiplication of the twists of Stacks 01NR on the scheme of `P_U`, carried
through the descent (`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul_comm`) and
read on local sections through the braiding of the tensor product sheaf. -/
theorem twistGradedAlgebra_mul_comm (i j : ℤ)
    (U : (SmallEtale s.site s.base s.containsBase s.relativeProjFunctor)ᵒᵖ)
    (x : ((s.twistGradedAlgebra Px).piece i).val.obj U)
    (y : ((s.twistGradedAlgebra Px).piece j).val.obj U) :
    HEq (((s.twistGradedAlgebra Px).mul i j).app U x y)
      (((s.twistGradedAlgebra Px).mul j i).app U y x) :=
  s.relativeProjPoints.spacePresentationGradedAlgebra_mul_comm Px _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    i j U x y

end RelativeProjSituation

end AlgebraicGeometry.Space

end

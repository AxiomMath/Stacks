module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPushforwardRestrictCoeffIso

/-!
# The pullback of a good acyclic differential graded module is acyclic

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi, `A` a sheaf of differential
graded `O`-algebras, `B` a sheaf of differential graded `O'`-algebras and `ψ : A ⟶ f_*B` a unital
homomorphism. Let `P` be a good acyclic right differential graded `A`-module. The source's proof
of Tag 0FSI (2) reads the pullback `f^*P = f⁻¹P ⊗_{f⁻¹A} B` as a tensor product over `f⁻¹O`:

* `g : (Sh(C'), f⁻¹O) ⟶ (Sh(C), O)` is `f` with the identity of `f⁻¹O` as structure map
  (`Stacks.Sheaves.RingedToposModules.RingedToposHom.inverseImageRingedToposHom`); pulling back
  along it is the inverse image, which is exact, so `g^*P` is acyclic, and it is K-flat because
  `P` is good;
* the restriction of scalars `B♭` of `B` along `α : f⁻¹O ⟶ O'` receives a unital homomorphism
  `ψ' : A ⟶ g_*B♭`, and the pullback `L = g^*P ⊗_{g^*A} B♭` of `P` along `(g, B♭, ψ')` is
  acyclic by clause (1) of Tag 0FSI;
* if the direct image along `(f, ψ)` is restriction of scalars along `α` followed by the direct
  image along `(g, ψ')`, then any pullback `T` of `P` along `(f, B, ψ)` corepresents the functor
  corepresented by `L`, precomposed with restriction of scalars, so `T` is the lift of `L` to a
  differential graded `B`-module and is acyclic with it.

The comparison of direct images is `toposPushforwardRestrictCoeffIso`.

## Main results

* `acyclic_toposPullbackModule_inverseImageRingedToposHom`: `g^*P` is acyclic for an acyclic `P`.
* `acyclic_of_toposCorepresentableBy_of_restrictCoeffIso`: every pullback of a good acyclic
  module along `(f, B, ψ)` is acyclic, given a comparison
  `f_{*,ψ} ≅ restrictCoeffFunctor α ⋙ g_{*,ψ'}`.
* `acyclic_of_toposCorepresentableBy_of_isGoodToposBaseChange`: **every pullback of a good
  acyclic module along every base change is acyclic.**
* `acyclic_toposPullbackModule_of_isGoodToposBaseChange`: **`f^*P` is acyclic for a good
  acyclic `P`.**

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.RingedToposModules.RingedToposHom

universe v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, max u₁ v₁}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify Y.J AddCommGrpCat.{max u₁ v₁}]
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, max u₁ v₁}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify X.J AddCommGrpCat.{max u₁ v₁}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (f : RingedToposHom X Y)

/-- Sheafification of sheaves of sets on `(Sh(C'), f⁻¹O)` is that on `X`. -/
instance hasSheafify_inverseImageRingedTopos_type :
    HasSheafify (inverseImageRingedTopos f).J (Type (max u₁ v₁)) :=
  inferInstanceAs (HasSheafify X.J (Type (max u₁ v₁)))

variable {A : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat Y.J Y.O)}

omit [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})] in
/-- **The pullback of an acyclic module along `(Sh(C'), f⁻¹O) ⟶ (Sh(C), O)` is acyclic**: its
complex is the inverse image of the complex of `P`, and the inverse image is exact. -/
theorem acyclic_toposPullbackModule_inverseImageRingedToposHom
    (P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A)
    (hac : P.complex.Acyclic) :
    (toposPullbackModule (inverseImageRingedToposHom f) P).complex.Acyclic :=
  acyclic_map_pullbackModules_inverseImageRingedToposHom f P.complex hac

variable {B : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat X.J X.O)}
  (ψ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B) (hψ : ψ.IsUnital)
  {α : toRingCat X.J (inverseImageStructureSheaf f) ⟶ toRingCat X.J X.O}

/-- **Every pullback of a good acyclic module is acyclic, given the comparison of direct
images.** Let `g : (Sh(C'), f⁻¹O) ⟶ (Sh(C), O)` be `f` with the identity of `f⁻¹O` as structure
map, `α : f⁻¹O ⟶ O'` a morphism of sheaves of rings, and `ψ' : A ⟶ g_*B♭` a unital homomorphism
into the direct image of the restriction of scalars of `B`. If the direct image along `(f, ψ)` is
restriction of scalars along `α` followed by the direct image along `(g, ψ')`, then every
object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)` is acyclic, for `P` good and acyclic. -/
theorem acyclic_of_toposCorepresentableBy_of_restrictCoeffIso
    [HasSheafify Y.J (Type (max u₁ v₁))]
    {P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A}
    (hP : IsGoodToposBaseChange.{max u₁ v₁, v₁, u₁} P) (hac : P.complex.Acyclic)
    (ψ' : A ⟶ toposPushforwardAlgebra (toposDirectImageModules (inverseImageRingedToposHom f))
      (B.restrictCoeff α))
    (hψ' : ψ'.IsUnital)
    (Φ : toposPushforward (toposDirectImageModules f) ψ hψ ≅
      restrictCoeffFunctor α ⋙
        toposPushforward (toposDirectImageModules (inverseImageRingedToposHom f)) ψ' hψ')
    {T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B}
    (eT : (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T) :
    T.complex.Acyclic := by
  let g := inverseImageRingedToposHom f
  let eL := toposBaseChangeCorepresentableBy g ψ' hψ' P
  have hL := acyclic_of_toposCorepresentableBy g ψ' hψ' P
    (isKFlat_toposPullbackModule_of_isGoodToposBaseChange hP)
    (acyclic_toposPullbackModule_inverseImageRingedToposHom f P hac) eL
  exact acyclic_of_corepresentableBy_restrictCoeff eL
    (eT.ofIso (Functor.isoWhiskerRight Φ _ ≪≫ Functor.associator _ _ _)) hL

/-- **Every pullback of a good acyclic module along every base change is acyclic** (the
acyclicity half of Tag 0FSI (2)): for a morphism of ringed topoi `f`, a sheaf of differential
graded algebras `B` on its source and a unital `ψ : A ⟶ f_*B`, every object corepresenting
`Q ↦ Hom_A(P, f_{*,ψ}Q)` — that is, every pullback `f^*P ⊗_{f^*A} B` of `P` — is acyclic. -/
theorem acyclic_of_toposCorepresentableBy_of_isGoodToposBaseChange
    [HasSheafify Y.J (Type (max u₁ v₁))]
    {P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A}
    (hP : IsGoodToposBaseChange.{max u₁ v₁, v₁, u₁} P) (hac : P.complex.Acyclic)
    {T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B}
    (eT : (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T) :
    T.complex.Acyclic :=
  acyclic_of_toposCorepresentableBy_of_restrictCoeffIso f ψ hψ hP hac
    (restrictCoeffStructureMap f ψ) (isUnital_restrictCoeffStructureMap f ψ hψ)
    (toposPushforwardRestrictCoeffIso f ψ hψ) eT

/-- **The pullback `f^*P` of a good acyclic module along a morphism of ringed topoi is
acyclic**, `f^*P` being the pullback of `P` along `(f, f^*A, η)`. -/
theorem acyclic_toposPullbackModule_of_isGoodToposBaseChange
    [HasSheafify Y.J (Type (max u₁ v₁))]
    {P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A}
    (hP : IsGoodToposBaseChange.{max u₁ v₁, v₁, u₁} P) (hac : P.complex.Acyclic) :
    (toposPullbackModule f P).complex.Acyclic :=
  acyclic_of_toposCorepresentableBy_of_isGoodToposBaseChange f (toposPullbackUnit f A)
    (isUnital_toposPullbackUnit f A) hP hac (toposPullbackCorepresentableBy f P)

end SheafOfModules.DifferentialGradedModule

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafFlatCover
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafPolynomial
public import StacksFrontier.CategoryTheory.Sites.Modules.PolynomialPresheafDerivations
import StacksCore.Tactic.StacksAttribute

/-!
# The differentials of a free algebra sheaf are free on its sheaf of generators

Let `A` be a sheaf of commutative rings on a site and let `E` be a presheaf of sets. The free
`A`-algebra sheaf `A[E]` on `E` is locally the presheaf of polynomial rings `U ↦ A(U)[E(U)]`,
and `Ω[A(U)[E(U)]⁄A(U)]` is the free `A(U)[E(U)]`-module on `E(U)`. So `Ω_{A[E]/A}` is the free
sheaf of `A[E]`-modules on `E`, and in particular it is flat.

## Main definitions

* `Stacks.SheafOfModules.freeModuleSheaf` is the free sheaf of `O`-modules on a presheaf of
  sets, the sheaf of modules associated to `U ↦ O(U)^{(E(U))}`, with
  `Stacks.SheafOfModules.freeModuleSheafGen` its generators and
  `Stacks.SheafOfModules.freeModuleSheafHomEquiv` its universal property.
* `Stacks.SheafOfModules.polynomialVariableAlong` is the family of variables of the polynomial
  presheaf, read in a sheaf of rings receiving a morphism from it, and
  `Stacks.SheafOfModules.derivationAtVariables` the values of a relative derivation on it.

## Main results

* `Stacks.SheafOfModules.derivationAtVariablesEquiv`: a relative derivation of such a sheaf of
  rings over `A` is the same thing as a prescription of the values at the variables.
* `Stacks.SheafOfModules.derivationsCorepresentableByFreeModuleSheaf` and
  `Stacks.SheafOfModules.differentialsIsoFreeModuleSheaf`: **the derivations are corepresented
  by the free sheaf of modules on `E`**, so the sheaf of relative differentials is that free
  sheaf of modules.
* `Stacks.SheafOfModules.isFlat_moduleSheafification` and
  `Stacks.SheafOfModules.isFlat_freeModuleSheaf`: **the free sheaf of modules on a presheaf of
  sets is flat**, and `Stacks.SheafOfModules.isFlat_differentials_of_polynomialVariable`: so are
  those differentials.
* `CategoryTheory.Sheaf.freeAlgebraSheafDifferentialsIso` and
  `CategoryTheory.Sheaf.isFlat_freeAlgebraSheafDifferentials`: the same two statements for the
  coproduct spelling `A ⨿ ℤ[E]` of the free algebra sheaf, which is the one the standard
  resolution of [Stacks, Tag 08SR] is built from.

## Implementation notes

Nothing here computes the sections of `Ω_{A[E]/A}`. The whole argument is the universal
property: a derivation of `A[E]` over `A` with values in a sheaf of modules is determined by,
and may be prescribed by, its values at the variables
(`Stacks.SheafOfModules.exists_derivation_of_polynomialVariable` and
`Stacks.SheafOfModules.derivation_ext_of_polynomialVariable`), and morphisms out of the free
sheaf of modules on `E` are also prescriptions of values at `E`. The two bijections are natural
in the coefficient sheaf of modules, which is what makes the free sheaf of modules a
corepresenting object, and `CategoryTheory.Functor.CorepresentableBy.isoCoreprX` turns that into
the isomorphism with `CategoryTheory.Functor.coreprX`, which is the object Tag 04BL names.

The statements are given for an arbitrary sheaf of rings `Q` receiving a locally bijective
morphism `α : A(-)[E(-)] ⟶ Q` compatible with the structural morphisms from `A`, rather than for
one chosen construction of `A[E]`. Both spellings in the tree are of that form: the
sheafification `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf` of the polynomial presheaf takes `α`
to be the unit of the sheafification, and the coproduct `CategoryTheory.Sheaf.freeAlgebraSheaf`
of the standard resolution takes it to be that unit followed by the comparison isomorphism
`CategoryTheory.Sheaf.freeAlgebraSheafIso`. This avoids transporting the derivations functor
along an isomorphism of the pair of ring sheaves, which would mean transporting the category of
coefficient modules too.

Flatness is read off the presheaf level: the free presheaf of modules on `E` is objectwise a
free module, hence objectwise flat, and tensoring with an objectwise flat presheaf of modules is
left exact, which survives sheafification because the unit of the sheafification is locally
bijective. That is the argument of `Stacks.isFlat_flatCover` with the presheaf of sections of a
sheaf of modules replaced by an arbitrary presheaf of modules, so
`Stacks.SheafOfModules.isFlat_moduleSheafification` states it once at that generality, at the
split module universe `max t w` the flat-cover development is stated at.

## References

* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), corepresentability of
  the functor of relative derivations.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the free algebra sheaf.
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER), flatness of a sheaf of
  modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w t

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra
open AlgebraicGeometry.SheafOfModules (derivationsFunctor)

/-! ### Flatness of the sheafification of an objectwise flat presheaf of modules -/

section Flat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{max t w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t w}]
  [HasWeakSheafify J AddCommGrpCat.{max t w}]
  (O : Sheaf J CommRingCat.{w})

/-- Tensoring and then sheafifying does not distinguish a presheaf of modules from its
sheafification, because the unit of the sheafification is locally bijective and
`Stacks.isIso_sheafification_map_tensorMapRight` says the second tensor variable does not see a
local bijection. -/
noncomputable def tensorRightSheafificationIso
    (P : PresheafOfModules.{max t w} (ringPresheaf O.obj)) :
    tensorRightOf O P ⋙ moduleSheafification O ≅
      tensorRightOf O ((moduleSheafification O).obj P).val ⋙ moduleSheafification O := by
  let η : P ⟶ ((moduleSheafification O).obj P).val :=
    (PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (ringSheafCompare O)).unit.app P
  haveI : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringPresheaf O.obj)).map η) := by
    change Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.presheaf)
    infer_instance
  haveI : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (ringPresheaf O.obj)).map η) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.presheaf)
    infer_instance
  -- The type of `M` is spelled out: elaborated from the natural transformation alone it comes
  -- out as `ringPresheaf O.obj`, which is only definitionally the spelling the instance for
  -- `NatIso.isIso_of_isIso_app` is then looked for at.
  haveI : ∀ M : PresheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj,
      IsIso ((Functor.whiskerRight
        (tensorRightNatTrans (O := O.obj) η) (moduleSheafification O)).app M) := fun M ↦
    isIso_sheafification_map_tensorMapRight (O := O.obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (M := M) (ringSheafCompare O) η
  exact @asIso _ _ _ _ (Functor.whiskerRight (tensorRightNatTrans (O := O.obj) η)
    (moduleSheafification O)) (NatIso.isIso_of_isIso_app _)

/-- **The sheafification of an objectwise flat presheaf of modules is a flat sheaf of
modules.** -/
theorem isFlat_moduleSheafification
    (P : PresheafOfModules.{max t w} (ringPresheaf O.obj))
    (hP : ∀ X : Cᵒᵖ, Module.Flat ((ringPresheaf O.obj).obj X) (P.obj X)) :
    IsFlat ((moduleSheafification O).obj P) := by
  refine (exactFunctor_iff _).2 ⟨?_, inferInstance⟩
  have : PreservesFiniteLimits (tensorRightOf O P) :=
    preservesFiniteLimits_tensorRight_of_flat_obj_split (O := O.obj) P hP
  have : PreservesFiniteLimits (tensorRightOf O P ⋙ moduleSheafification O) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        (tensorRightOf O P ⋙ moduleSheafification O)) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    (Functor.isoWhiskerLeft
      (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (tensorRightSheafificationIso O P))

end Flat

/-! ### The free sheaf of modules on a presheaf of sets -/

section FreeModuleSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (O : Sheaf J CommRingCat.{max u v w}) (E : Cᵒᵖ ⥤ Type (max u v w))

/-- **The free sheaf of `O`-modules on a presheaf of sets `E`**: the sheaf of modules associated
to the presheaf of modules `U ↦ O(U)^{(E(U))}`. -/
noncomputable def freeModuleSheaf :
    _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (PresheafOfModules.sheafification (ringSheafCompare O)).obj (PresheafOfModules.freeObj E)

/-- **The universal property of the free sheaf of modules on `E`**: a morphism of sheaves of
modules out of it is a morphism of presheaves of sets from `E` to the sections. -/
@[ega "0 5.1.1" "more general"]
noncomputable def freeModuleSheafHomEquiv
    (F : _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (freeModuleSheaf J O E ⟶ F) ≃
      (E ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{max u v w}) :=
  (PresheafOfModules.sheafificationHomEquiv (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (ringSheafCompare O) (P := PresheafOfModules.freeObj E) (F := F)).trans
    (PresheafOfModules.freeHomEquiv (F := E)
      (G := (PresheafOfModules.restrictScalars (ringSheafCompare O)).obj F.val))

/-- The generators `E ⟶ O^{(E)}` of the free sheaf of modules on `E`. -/
noncomputable def freeModuleSheafGen :
    E ⟶ (freeModuleSheaf J O E).val.presheaf ⋙ forget AddCommGrpCat.{max u v w} :=
  freeModuleSheafHomEquiv J O E (freeModuleSheaf J O E) (𝟙 _)

/-- A morphism out of the free sheaf of modules on `E` corresponds to its values on the
generators. -/
lemma freeModuleSheafHomEquiv_app
    (F : _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (k : freeModuleSheaf J O E ⟶ F) (X : Cᵒᵖ) (e : E.obj X) :
    (freeModuleSheafHomEquiv J O E F k).app X e =
      k.val.app X ((freeModuleSheafGen J O E).app X e) := rfl

end FreeModuleSheaf

/-! ### Derivations prescribed on the variables -/

section Corepresentability

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (A : Sheaf J CommRingCat.{max u v w}) (E : Cᵒᵖ ⥤ Type (max u v w))
  {Q : Sheaf J CommRingCat.{max u v w}} {φ : A ⟶ Q}
  (α : polynomialPresheaf J A E ⟶ Q.obj)

/-- The variables of the presheaf of polynomial rings, read in a sheaf of commutative rings
receiving a morphism `α` from it. -/
noncomputable def polynomialVariableAlong :
    E ⟶ Q.obj ⋙ forget CommRingCat.{max u v w} :=
  polynomialVariable J A E ≫ Functor.whiskerRight α (forget CommRingCat.{max u v w})

/-- The values of a relative derivation at the variables, as a morphism of presheaves of
sets. -/
noncomputable def derivationAtVariables
    (F : _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf Q))
    (D : PresheafOfModulesOfCommRing.Derivation' F.val φ.hom) :
    E ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{max u v w} :=
  polynomialVariableAlong J A E α ≫
    { app := fun X => TypeCat.ofHom fun x => D.d x
      naturality := fun X Y g => by
        ext x
        exact D.d_map g x }

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The value of `derivationAtVariables` at a variable `e` is `D` applied to the image of
`MvPolynomial.X e` under `α`. -/
lemma derivationAtVariables_app
    (F : _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf Q))
    (D : PresheafOfModulesOfCommRing.Derivation' F.val φ.hom) (X : Cᵒᵖ) (e : E.obj X) :
    (derivationAtVariables J A E α F D).app X e = D.d (α.app X (MvPolynomial.X e)) := rfl

variable [Presheaf.IsLocallySurjective J α] [Presheaf.IsLocallyInjective J α]

/-- **A relative derivation of `Q` over `A` is the same thing as a prescription of the values at
the variables.** -/
noncomputable def derivationAtVariablesEquiv
    (hα : polynomialCoefficientMap J A E ≫ α = φ.hom)
    (F : _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf Q)) :
    PresheafOfModulesOfCommRing.Derivation' F.val φ.hom ≃
      (E ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{max u v w}) := by
  refine Equiv.ofBijective (derivationAtVariables J A E α F) ⟨?_, ?_⟩
  · intro D₁ D₂ h
    refine derivation_ext_of_polynomialVariable J A E α hα F D₁ D₂ fun X e => ?_
    exact congrArg (fun s : E ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{max u v w} =>
      s.app X e) h
  · intro ψ
    obtain ⟨D, hD⟩ := exists_derivation_of_polynomialVariable J A E α F ψ
    refine ⟨{ d := D.d
              d_mul := D.d_mul
              d_map := D.d_map
              d_app := fun {X} a =>
                (congrArg (fun s : A.obj ⟶ Q.obj => D.d (s.app X a)) hα.symm).trans
                  (D.d_app a) }, ?_⟩
    ext X e
    exact hD X e

omit [HasWeakSheafify J AddCommGrpCat] in
/-- The derivation prescribing a given family of values at the variables takes those values. -/
lemma derivationAtVariablesEquiv_symm_d
    (hα : polynomialCoefficientMap J A E ≫ α = φ.hom)
    (F : _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf Q))
    (ψ : E ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{max u v w}) (X : Cᵒᵖ) (e : E.obj X) :
    ((derivationAtVariablesEquiv J A E α hα F).symm ψ).d (α.app X (MvPolynomial.X e)) =
      ψ.app X e :=
  congrArg (fun s : E ⟶ F.val.presheaf ⋙ forget AddCommGrpCat.{max u v w} => s.app X e)
    (Equiv.apply_symm_apply (derivationAtVariablesEquiv J A E α hα F) ψ)

/-- **The relative derivations of `Q` over `A` are corepresented by the free sheaf of
`Q`-modules on `E`.** -/
noncomputable def derivationsCorepresentableByFreeModuleSheaf
    (hα : polynomialCoefficientMap J A E ≫ α = φ.hom) :
    (derivationsFunctor.{max u v w} A Q φ).CorepresentableBy
      (freeModuleSheaf J Q E) where
  homEquiv {F} := (freeModuleSheafHomEquiv J Q E F).trans
    (derivationAtVariablesEquiv J A E α hα F).symm
  homEquiv_comp {F F'} g k := by
    refine derivation_ext_of_polynomialVariable J A E α hα F' _ _ fun X e => ?_
    refine Eq.trans ((derivationAtVariablesEquiv_symm_d J A E α hα F' _ X e).trans
      (freeModuleSheafHomEquiv_app J Q E F' (k ≫ g) X e)) ?_
    exact (congrArg (fun y => g.val.app X y)
      ((derivationAtVariablesEquiv_symm_d J A E α hα F _ X e).trans
        (freeModuleSheafHomEquiv_app J Q E F k X e))).symm

/-- **The sheaf of relative differentials of `Q` over `A` is the free sheaf of `Q`-modules on
`E`.** -/
noncomputable def differentialsIsoFreeModuleSheaf
    (hα : polynomialCoefficientMap J A E ≫ α = φ.hom) :
    (derivationsFunctor.{max u v w} A Q φ).coreprX ≅ freeModuleSheaf J Q E :=
  ((derivationsCorepresentableByFreeModuleSheaf J A E α hα).isoCoreprX).symm

end Corepresentability

/-! ### Flatness of the differentials -/

section FreeFlat

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (E : Cᵒᵖ ⥤ Type (max u v w))

/-- **The free sheaf of modules on a presheaf of sets is flat.** It is the sheafification of a
presheaf of modules which is objectwise a free module. -/
theorem isFlat_freeModuleSheaf (O : Sheaf J CommRingCat.{max u v w}) :
    IsFlat (freeModuleSheaf J O E) :=
  isFlat_moduleSheafification.{v, u, max u v w, max u v w} O
    (PresheafOfModules.freeObj E) fun X => by
      show Module.Flat ((ringPresheaf O.obj).obj X) (E.obj X →₀ (ringPresheaf O.obj).obj X)
      infer_instance

variable (A : Sheaf J CommRingCat.{max u v w})
  {Q : Sheaf J CommRingCat.{max u v w}} {φ : A ⟶ Q}
  (α : polynomialPresheaf J A E ⟶ Q.obj)
  [Presheaf.IsLocallySurjective J α] [Presheaf.IsLocallyInjective J α]

/-- **The sheaf of relative differentials of `Q` over `A` is flat**, being free on `E`. -/
theorem isFlat_differentials_of_polynomialVariable
    (hα : polynomialCoefficientMap J A E ≫ α = φ.hom) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v w, max u v w} (O := Q)
      (derivationsFunctor.{max u v w} A Q φ).coreprX :=
  FlatRetract.isFlat_of_iso Q (differentialsIsoFreeModuleSheaf J A E α hα).symm
    (isFlat_freeModuleSheaf J E Q)

end FreeFlat

/-! ### The sheafified polynomial presheaf -/

section Polynomial

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (A : Sheaf J CommRingCat.{max u v w}) (E : Cᵒᵖ ⥤ Type (max u v w))

/-- The unit of the sheafification at the presheaf of polynomial rings: a locally bijective
morphism from `A(-)[E(-)]` into `A[E]`. -/
noncomputable abbrev polynomialToFreeAlgebraSheaf :
    polynomialPresheaf J A E ⟶ (freeAlgebraSheaf J A E).obj :=
  (toSheafification J CommRingCat.{max u v w}).app (polynomialPresheaf J A E)

/-- The sheafification unit `polynomialToFreeAlgebraSheaf` is locally surjective. -/
instance isLocallySurjective_polynomialToFreeAlgebraSheaf :
    Presheaf.IsLocallySurjective J (polynomialToFreeAlgebraSheaf J A E) :=
  (isLocallyBijective_toSheafification_commRingCat.{v, u, w} J _).1

/-- The sheafification unit `polynomialToFreeAlgebraSheaf` is locally injective. -/
instance isLocallyInjective_polynomialToFreeAlgebraSheaf :
    Presheaf.IsLocallyInjective J (polynomialToFreeAlgebraSheaf J A E) :=
  (isLocallyBijective_toSheafification_commRingCat.{v, u, w} J _).2

/-- **The sheaf of relative differentials of the free algebra sheaf `A[E]` over `A` is the free
sheaf of `A[E]`-modules on `E`.** -/
noncomputable def freeAlgebraSheafDifferentialsIso :
    (derivationsFunctor.{max u v w} A (freeAlgebraSheaf J A E)
        (freeAlgebraSheafCoefficientMap J A E)).coreprX ≅
      freeModuleSheaf J (freeAlgebraSheaf J A E) E :=
  differentialsIsoFreeModuleSheaf J A E (polynomialToFreeAlgebraSheaf J A E) rfl

/-- **The sheaf of relative differentials of the free algebra sheaf `A[E]` over `A` is
flat.** -/
theorem isFlat_freeAlgebraSheafDifferentials :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v w, max u v w}
      (O := freeAlgebraSheaf J A E)
      (derivationsFunctor.{max u v w} A (freeAlgebraSheaf J A E)
        (freeAlgebraSheafCoefficientMap J A E)).coreprX :=
  isFlat_differentials_of_polynomialVariable J E A (polynomialToFreeAlgebraSheaf J A E) rfl

end Polynomial

end Stacks.SheafOfModules

namespace CategoryTheory.Sheaf

open Stacks.Sites.FreeAlgebra
open Stacks.SheafOfModules (freeModuleSheaf differentialsIsoFreeModuleSheaf
  isFlat_differentials_of_polynomialVariable polynomialToFreeAlgebraSheaf)
open AlgebraicGeometry.SheafOfModules (derivationsFunctor)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (A : Sheaf J CommRingCat.{max u v w}) (E : Sheaf J (Type (max u v w)))

/-- The underlying morphism of presheaves of rings of the comparison morphism
`CategoryTheory.Sheaf.freeAlgebraSheafComparisonInv` is an isomorphism. -/
instance isIso_freeAlgebraSheafComparisonInv_right_hom :
    IsIso (freeAlgebraSheafComparisonInv J A E).right.hom := by
  have : IsIso (freeAlgebraSheafComparisonInv J A E) := (freeAlgebraSheafIso J A E).isIso_inv
  exact inferInstanceAs (IsIso ((sheafToPresheaf J CommRingCat.{max u v w}).map
    ((Under.forget A).map (freeAlgebraSheafComparisonInv J A E))))

/-- The presheaf of polynomial rings `A(-)[E(-)]`, mapped into the coproduct spelling
`A ⨿ ℤ[E]` of the free algebra sheaf: the unit of the sheafification followed by the comparison
isomorphism of `CategoryTheory.Sheaf.freeAlgebraSheafIso`. -/
noncomputable abbrev polynomialToCoproductFreeAlgebraSheaf :
    polynomialPresheaf J A E.obj ⟶ ((freeAlgebraSheaf J A).obj E).right.obj :=
  polynomialToFreeAlgebraSheaf J A E.obj ≫ (freeAlgebraSheafComparisonInv J A E).right.hom

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The comparison into the coproduct spelling of the free algebra sheaf is compatible with the
structural morphisms from `A`. -/
theorem polynomialCoefficientMap_comp_polynomialToCoproductFreeAlgebraSheaf :
    polynomialCoefficientMap J A E.obj ≫ polynomialToCoproductFreeAlgebraSheaf J A E =
      ((freeAlgebraSheaf J A).obj E).hom.hom := by
  rw [← Category.assoc]
  exact congrArg (fun k : A ⟶ ((freeAlgebraSheaf J A).obj E).right => k.hom)
    (Under.w (freeAlgebraSheafComparisonInv J A E))

/-- **The sheaf of relative differentials of the free `A`-algebra sheaf on a sheaf of sets `E`
is the free sheaf of modules on `E`.** This is the coproduct spelling `A ⨿ ℤ[E]` of the free
algebra sheaf, the one the standard resolution of [Stacks, Tag 08SR] is built from. -/
noncomputable def freeAlgebraSheafDifferentialsIso :
    (derivationsFunctor.{max u v w} A ((freeAlgebraSheaf J A).obj E).right
        ((freeAlgebraSheaf J A).obj E).hom).coreprX ≅
      freeModuleSheaf J ((freeAlgebraSheaf J A).obj E).right E.obj :=
  differentialsIsoFreeModuleSheaf J A E.obj (polynomialToCoproductFreeAlgebraSheaf J A E)
    (polynomialCoefficientMap_comp_polynomialToCoproductFreeAlgebraSheaf J A E)

/-- **The sheaf of relative differentials of the free `A`-algebra sheaf on a sheaf of sets `E`
is flat**, being free on `E`. -/
theorem isFlat_freeAlgebraSheafDifferentials :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v w, max u v w}
      (O := ((freeAlgebraSheaf J A).obj E).right)
      (derivationsFunctor.{max u v w} A ((freeAlgebraSheaf J A).obj E).right
        ((freeAlgebraSheaf J A).obj E).hom).coreprX :=
  isFlat_differentials_of_polynomialVariable J E.obj A
    (polynomialToCoproductFreeAlgebraSheaf J A E)
    (polynomialCoefficientMap_comp_polynomialToCoproductFreeAlgebraSheaf J A E)

end CategoryTheory.Sheaf

end

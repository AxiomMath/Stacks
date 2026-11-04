module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineMap
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso

/-!
# The stalks of the two complexes of Stacks 0D0I

Let `f : X ⟶ Y` be a morphism of schemes, let `U` be an open of `Y` and `V` an open of `X` with
`V ⊆ f^{-1}U`.  Stacks 0D0I asserts that the canonical map
`(NL_{A/R})~ ⟶ NL_{X/Y}|_V` of `Stacks.NaiveCotangentAffineMap.comparisonMap` is an isomorphism
in `D(𝒪_V)`.  That is a stalkwise statement
(`AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso`), and this file supplies
the identifications of the stalks of the two complexes that the stalkwise criterion consumes.

## Main definitions

* `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne` and
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero`: the stalk at `z` of the degree `-1`,
  respectively degree `0`, term of `NL_{B/A}` is the conormal module, respectively the cotangent
  space, of the canonical presentation of `Bₓ` over `Aₓ`.  This is Stacks 0D09
  (`Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv`) read through the identification of
  the terms of the complex (`Stacks.SheafOfModules.naiveCotangentComplex_X_negOne`).
* `Stacks.NaiveCotangentAffineStalkLegs.restrictStalkAddEquiv`: the stalk at `x` of the
  restriction of a sheaf of `𝒪_X`-modules along `V.ι` is the stalk of the sheaf itself at the
  image of `x`; this is `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` read as a
  bijection.
* `Stacks.NaiveCotangentAffineStalkLegs.stalkAlgEquiv`: the stalk of `𝒪_V` at `x` is the stalk of
  `𝒪_X` at the image of `x`, as an algebra over `Γ(X, V)`.
* `Stacks.NaiveCotangentAffineStalkLegs.uLeg`: the stalk at `x` of the sheaf associated to a
  `Γ(X, V)`-module `M` is `𝒪_{X,x} ⊗_{Γ(X,V)} M`.  This is clause (3) of Stacks 01BH
  (`Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv`) transported along the previous item, so
  that the base ring is the stalk of `𝒪_X` and not that of `𝒪_V`.

## Main results

* `Stacks.NaiveCotangentAffineStalkLegs.conormal_germ_smul` and
  `Stacks.NaiveCotangentAffineStalkLegs.tensor_germ_smul`: **the two actions on the stalk of a
  term of `NL_{B/A}` agree.**  The identification of Stacks 0D09 is semilinear over the stalk of
  the canonical presentation `A[B] ⟶ B`
  (`Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_semilinear`), while the action a
  stalkwise argument produces is that of the stalk of `B`.  These two statements convert one into
  the other: a section `σ` of `B` is the image of the variable `X_σ` of the canonical
  presentation, and the germ of the action of a section of `A[B]` is the action of its germ.
* `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne_germ_smul` and
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero_germ_smul`: the same, for the
  identifications of the terms of `NL_{B/A}` themselves.
* `Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d`: the two identifications carry the stalk of
  the differential of `NL_{B/A}` to the cotangent complex of the stalk extension.
* `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne_germ_sectionsConormalComparison` and
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero_germ_sectionsTensorComparison`: the germ of
  the comparison on sections, read through the identification of stalks, is the functorial map of
  the morphism of extensions given by the germ maps.
* `Stacks.NaiveCotangentAffineStalkLegs.restrictTop_germ_smul`: the germ at `x` of a scalar
  multiple of the restriction to `V.ι ''ᵁ ⊤` of a section over `V`, read through
  `restrictStalkAddEquiv`, is the germ of the corresponding section of `𝒩` over `V.ι ''ᵁ W`.

## Implementation notes

**Why the two-actions statement is proved from `PresheafOfModules.germ_smul` and not from
`Stacks.NaiveCotangentAffineIso.germ_smul_conormalSheaf`.**  The latter is stated for an
arbitrary morphism `φ : A ⟶ B` of sheaves of rings, and substituting the canonical presentation
`A[B] ⟶ B` for `φ` costs more than 200000 heartbeats: the unifier has to compare two
sheafifications built from the substituted ring sheaf, and the colimit data they contain is not
exposed, so it cannot be unfolded.

`PresheafOfModules.germ_smul` is abstract in the *module* rather than in the ring sheaf: it takes
the presheaf of modules as a variable, so substituting
`Stacks.Sites.Conormal.conormalSheafOverSource` for it is a plain substitution.

For the same reason every identification here is phrased with the scalar given as the germ of a
*section*: that keeps the two stalk rings — the `CommRingCat` stalk of `B` and the `RingCat`
stalk of the sheaf of rings underlying it — from having to be compared.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof this is a
  step.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), clause (3): the stalks
  of the sheaf associated to a module.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), the stalkwise criterion
  for quasi-isomorphy.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineStalkLegs

open Stacks.NaiveCotangentAffineIso Stacks.NaiveCotangentAffineMap Stacks.AssociatedSheaf
open Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open Stacks.RelativeDifferentialStalk (algebraStalk)

/-- The additive isomorphism of stalks at `z` induced by an isomorphism `e : M ≅ N` of sheaves of
`O`-modules. -/
def stalkAddEquivOfIso {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (z : T) {M N : _root_.SheafOfModules.{u} O} (e : M ≅ N) :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z) ≃+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf z) :=
  ((AlgebraicGeometry.SheafOfModules.stalkFunctor O z).mapIso e).toLinearEquiv.toAddEquiv

/-- `stalkAddEquivOfIso z e` sends the germ at `z` of a section `t` over `U` to the germ of the
image of `t` under `e`. -/
theorem stalkAddEquivOfIso_germ {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (z : T) {M N : _root_.SheafOfModules.{u} O} (e : M ≅ N) (U : Opens T) (hz : z ∈ U)
    (t : M.val.obj (op U)) :
    stalkAddEquivOfIso z e
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U z hz) t) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.val.presheaf U z hz)
        ((e.hom.val.app (op U)) t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U z hz
    ((PresheafOfModules.toPresheaf O.obj).map e.hom.val) t

/-- `stalkAddEquivOfIso z e` is the map of stalks at `z` induced by `e.hom`. -/
theorem stalkAddEquivOfIso_apply {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (z : T) {M N : _root_.SheafOfModules.{u} O} (e : M ≅ N)
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z)) :
    stalkAddEquivOfIso z e w =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map e.hom.val)) w := rfl

/-- Equal scalars act equally on a section of a sheaf of modules. -/
theorem smul_congr_left {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (M : _root_.SheafOfModules.{u} O) (Y : (Opens T)ᵒᵖ)
    {r r' : ToType (O.obj.obj Y)} (h : r = r') (m : M.val.obj Y) : r • m = r' • m :=
  congrArg (fun y : ToType (O.obj.obj Y) => y • m) h

/-- The map of stalks at `z` induced by a composite `ψ ≫ χ` of morphisms of sheaves of modules is
the composite of the maps of stalks induced by `ψ` and `χ`. -/
theorem stalkMap_comp_apply {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (z : T)
    {M N P : _root_.SheafOfModules.{u} O} (ψ : M ⟶ N) (χ : N ⟶ P)
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map (ψ ≫ χ).val)).hom ω =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map χ.val)).hom
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
          ((PresheafOfModules.toPresheaf O.obj).map ψ.val)).hom ω) := by
  rw [show ((ψ ≫ χ).val) = ψ.val ≫ χ.val from rfl, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  exact ConcreteCategory.comp_apply _ _ ω

/-- For an equality `e : M = N` of sheaves of modules, the component of `eqToHom e` over `Y` is a
left inverse of the component of `eqToHom e.symm`. -/
theorem app_eqToHom_cancel {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} O} (e : M = N) (Y : (Opens T)ᵒᵖ) (c : N.val.obj Y) :
    ((eqToHom e).val.app Y) (((eqToHom e.symm).val.app Y) c) = c := by
  subst e; rfl

/-! ### the stalk of `NL_{B/A}`, degreewise (Stacks 0D09) -/

section Site
variable {T : TopCat.{u}}
  (A B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (z : T)

/-- The canonical presentation `A[B] ⟶ B` of `B` over `A`, whose variables are the sections of
`B`. -/
abbrev pres := presentation (Opens.grothendieckTopology T) A B a
  (underlyingPresheaf (Opens.grothendieckTopology T) B) (𝟙 _)

/-- The sheaf `A[B]` of polynomial `A`-algebras on the sections of `B`. -/
abbrev AA := freeAlgebraSheaf (Opens.grothendieckTopology T) A
  (underlyingPresheaf (Opens.grothendieckTopology T) B)

/-- The conormal sheaf of the canonical presentation `A[B] ⟶ B`. -/
abbrev cSheaf := conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology T) (AA A B) B (pres A B a)

/-- The sheaf `Ω_{A[B]/A} ⊗_{A[B]} B` of the canonical presentation `A[B] ⟶ B`. -/
abbrev tSheaf := tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology T) A
  (AA A B) B (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
    (underlyingPresheaf (Opens.grothendieckTopology T) B)) (pres A B a)

/-- The stalk at `z` of the degree `-1` term of the naive cotangent complex of `a : A ⟶ B` is the
conormal module of the canonical presentation of `B_z` over `A_z`. -/
def stalkLegNegOne :
    letI := algebraStalk a.hom z
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
          (-1)).val.presheaf z) ≃+
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.Cotangent :=
  letI := algebraStalk a.hom z
  (stalkAddEquivOfIso z (eqToIso
      (naiveCotangentComplex_X_negOne.{u, u, u, u} (Opens.grothendieckTopology T) A B a))).trans
    (naiveCotangentStalkCotangentEquiv A B a z)

/-- The stalk at `z` of the degree `0` term of the naive cotangent complex of `a : A ⟶ B` is the
cotangent space of the canonical presentation of `B_z` over `A_z`. -/
def stalkLegZero :
    letI := algebraStalk a.hom z
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
          0).val.presheaf z) ≃+
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.CotangentSpace :=
  letI := algebraStalk a.hom z
  (stalkAddEquivOfIso z (eqToIso
      (naiveCotangentComplex_X_zero.{u, u, u, u} (Opens.grothendieckTopology T) A B a))).trans
    (naiveCotangentStalkCotangentSpaceEquiv A B a z)

/-- `stalkLegNegOne` is the identification of the degree `-1` term with the conormal sheaf,
followed by `naiveCotangentStalkCotangentEquiv`. -/
theorem stalkLegNegOne_apply
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        (-1)).val.presheaf z)) :
    letI := algebraStalk a.hom z
    stalkLegNegOne A B a z w =
      naiveCotangentStalkCotangentEquiv A B a z
        (stalkAddEquivOfIso z (eqToIso
          (naiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology T) A B a)) w) := rfl

/-- `stalkLegZero` is the identification of the degree `0` term with the sheaf
`Ω_{A[B]/A} ⊗_{A[B]} B`, followed by `naiveCotangentStalkCotangentSpaceEquiv`. -/
theorem stalkLegZero_apply
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        0).val.presheaf z)) :
    letI := algebraStalk a.hom z
    stalkLegZero A B a z w =
      naiveCotangentStalkCotangentSpaceEquiv A B a z
        (stalkAddEquivOfIso z (eqToIso
          (naiveCotangentComplex_X_zero.{u, u, u, u}
            (Opens.grothendieckTopology T) A B a)) w) := rfl

/-! ### the differential on stalks -/

/-- Under `stalkLegNegOne` and `stalkLegZero`, the map of stalks at `z` induced by the
differential of the naive cotangent complex is the cotangent complex of the canonical presentation
of `B_z` over `A_z`. -/
theorem stalkLeg_d
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        (-1)).val.presheaf z)) :
    letI := algebraStalk a.hom z
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _
    stalkLegZero A B a z
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
          ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).d
              (-1) 0).val)).hom ω) =
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.cotangentComplex
        (stalkLegNegOne A B a z ω) := by
  let := algebraStalk a.hom z
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _
  have key : (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).d (-1) 0 ≫
        eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology T) A B a) =
      eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology T) A B a) ≫
        conormalSequenceFHom A (AA A B) B
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
            (underlyingPresheaf (Opens.grothendieckTopology T) B)) (pres A B a) := by
    rw [naiveCotangentComplex_d_negOne_zero.{u, u, u, u} (Opens.grothendieckTopology T) A B a,
      Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      canonicalConormalSequence_f_eq_conormalSequenceFHom A B a]
    rfl
  have step : stalkAddEquivOfIso z (eqToIso (naiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology T) A B a))
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
          ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).d
              (-1) 0).val)).hom ω) =
      conormalSequenceStalkMapF A (AA A B) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
          (underlyingPresheaf (Opens.grothendieckTopology T) B)) (pres A B a) z
        (stalkAddEquivOfIso z (eqToIso (naiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology T) A B a)) ω) := by
    refine Eq.trans (stalkAddEquivOfIso_apply z _ _) ?_
    refine Eq.trans (stalkMap_comp_apply z
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).d (-1) 0)
      (eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
        (Opens.grothendieckTopology T) A B a)) ω).symm ?_
    refine Eq.trans (congrArg (fun ψ :
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X (-1) ⟶
          (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X₂ =>
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
          ψ.val)).hom ω)
      key) ?_
    exact stalkMap_comp_apply z _ _ ω
  refine Eq.trans (stalkLegZero_apply A B a z _) ?_
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentSpaceEquiv A B a z) step) ?_
  refine Eq.trans (naiveCotangentStalk_d_eq_cotangentComplex A B a z _) ?_
  exact congrArg (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
      (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.cotangentComplex
    (stalkLegNegOne_apply A B a z ω).symm

variable (U : Opens T) (hz : z ∈ U)

/-- `stalkAddEquivOfIso` for `eqToIso h` sends the germ of the transport of `c` along `h.symm` to
the germ of `c`. -/
private theorem stalkAddEquivOfIso_eqToIso_germ {M N : SheafOfModules.{u} (Tensor.ringSheaf B)}
    (h : M = N) (c : ToType (N.val.obj (op U))) :
    stalkAddEquivOfIso z (eqToIso h)
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U z hz).hom
          ((eqToHom h.symm).val.app (op U) c)) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.val.presheaf U z hz).hom c :=
  Eq.trans (stalkAddEquivOfIso_germ z (eqToIso h) U hz _)
    (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.val.presheaf U z hz).hom
      (app_eqToHom_cancel h (op U) c))

/-- `stalkAddEquivOfIso` sends the germ of `σ • t` to the germ of `σ` acting on the image of `t`. -/
private theorem stalkAddEquivOfIso_germ_smul {M N : SheafOfModules.{u} (Tensor.ringSheaf B)}
    (e : M ≅ N) (σ : ToType (B.obj.obj (op U))) (t : ToType (M.val.obj (op U))) :
    stalkAddEquivOfIso z e
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U z hz).hom (σ • t)) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.val.presheaf U z hz).hom
        (σ • (e.hom.val.app (op U)).hom t) :=
  Eq.trans (stalkAddEquivOfIso_germ z e U hz _)
    (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.val.presheaf U z hz).hom
      (map_smul (e.hom.val.app (op U)).hom σ t))

/-- Under `stalkLegNegOne`, the germ at `z` of the image of `c` under
`sectionsConormalComparison` over `U` is the image of `c` under the map of conormal modules
induced by `germSelfHom`. -/
theorem stalkLegNegOne_germ_sectionsConormalComparison :
    letI := algebraSections (Opens.grothendieckTopology T) A B a (op U)
    letI := algebraStalk a.hom z
    letI := algebraGerm A z U hz
    letI := algebraGerm B z U hz
    letI := algebraGermComp A B a z U hz
    haveI := isScalarTower_germ A B a z U hz
    ∀ c : (Algebra.Generators.self (ToType (A.obj.obj (op U)))
      (ToType (B.obj.obj (op U)))).toExtension.Cotangent,
    stalkLegNegOne A B a z
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
            (-1)).val.presheaf U z hz).hom
          ((eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology T) A B a).symm).val.app (op U)
            (sectionsConormalComparison.{u, u, u, u}
              (Opens.grothendieckTopology T) A B a (op U) c))) =
      Algebra.Extension.Cotangent.map (germSelfHom A B a z U hz) c := by
  let := algebraSections (Opens.grothendieckTopology T) A B a (op U)
  let := algebraStalk a.hom z
  let := algebraGerm A z U hz
  let := algebraGerm B z U hz
  let := algebraGermComp A B a z U hz
  have _ := isScalarTower_germ A B a z U hz
  intro c
  refine Eq.trans (stalkLegNegOne_apply A B a z _) ?_
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentEquiv A B a z)
    (stalkAddEquivOfIso_eqToIso_germ B z U hz (naiveCotangentComplex_X_negOne.{u, u, u, u}
      (Opens.grothendieckTopology T) A B a) _)) ?_
  exact naiveCotangentStalkCotangentEquiv_germ_sectionsConormalComparison A B a z U hz c

/-- Under `stalkLegZero`, the germ at `z` of the image of `c` under `sectionsTensorComparison`
over `U` is the image of `c` under the map of cotangent spaces induced by `germSelfHom`. -/
theorem stalkLegZero_germ_sectionsTensorComparison :
    letI := algebraSections (Opens.grothendieckTopology T) A B a (op U)
    letI := algebraStalk a.hom z
    letI := algebraGerm A z U hz
    letI := algebraGerm B z U hz
    letI := algebraGermComp A B a z U hz
    haveI := isScalarTower_germ A B a z U hz
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _
    ∀ c : (Algebra.Generators.self (ToType (A.obj.obj (op U)))
      (ToType (B.obj.obj (op U)))).toExtension.CotangentSpace,
    stalkLegZero A B a z
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
            0).val.presheaf U z hz).hom
          ((eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
            (Opens.grothendieckTopology T) A B a).symm).val.app (op U)
            (sectionsTensorComparison.{u, u, u, u}
              (Opens.grothendieckTopology T) A B a (op U) c))) =
      Algebra.Extension.CotangentSpace.map (germSelfHom A B a z U hz) c := by
  let := algebraSections (Opens.grothendieckTopology T) A B a (op U)
  let := algebraStalk a.hom z
  let := algebraGerm A z U hz
  let := algebraGerm B z U hz
  let := algebraGermComp A B a z U hz
  have _ := isScalarTower_germ A B a z U hz
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _
  intro c
  refine Eq.trans (stalkLegZero_apply A B a z _) ?_
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentSpaceEquiv A B a z)
    (stalkAddEquivOfIso_eqToIso_germ B z U hz (naiveCotangentComplex_X_zero.{u, u, u, u}
      (Opens.grothendieckTopology T) A B a) _)) ?_
  exact naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison A B a z U hz c


/-- If `E` is semilinear over the stalk of `A[B]`, then `E` of the germ of `σ • u` is the germ of
`σ` acting on `E` of the germ of `u`: the variable `X_σ` of the presentation acts as `σ`. -/
private theorem germ_smul_of_semilinear {M : SheafOfModules.{u} (Tensor.ringSheaf B)} {Q : Type*}
    [SMul (ToType (TopCat.Presheaf.stalk (AA A B).obj z))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z))]
    [SMul (ToType (TopCat.Presheaf.stalk B.obj z)) Q]
    (E : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z) → Q)
    (hE : ∀ (r : ToType (TopCat.Presheaf.stalk (AA A B).obj z)) ξ, E (r • ξ) =
      (show ToType (TopCat.Presheaf.stalk B.obj z) from
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map (pres A B a).hom).hom r) • E ξ)
    (hM : ∀ (r : ToType ((AA A B).obj.obj (op U))) (u : ToType (M.val.obj (op U))),
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U z hz).hom
          (((pres A B a).hom.app (op U)).hom r • u) =
        (show ToType (TopCat.Presheaf.stalk (AA A B).obj z) from
          (TopCat.Presheaf.germ (AA A B).obj U z hz).hom r) •
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U z hz).hom u)
    (σ : ToType (B.obj.obj (op U))) (u : ToType (M.val.obj (op U))) :
    E ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U z hz).hom (σ • u)) =
      (show ToType (TopCat.Presheaf.stalk B.obj z) from
          (TopCat.Presheaf.germ B.obj U z hz).hom σ) •
        E ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U z hz).hom u) := by
  have hσ := presentation_app_freeAlgebraSectionsMap_X A B a U σ
  have h := hM (freeAlgebraSectionsMap (Opens.grothendieckTopology T) A B (op U)
    (MvPolynomial.X σ)) u
  rw [hσ] at h
  rw [h, hE]
  exact congrArg (· • _) (Eq.trans
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U z hz (pres A B a).hom _)
    (congrArg (TopCat.Presheaf.germ B.obj U z hz).hom hσ))

/-- For a section `σ` of `B` and a section `u` of the conormal sheaf over `U`,
`naiveCotangentStalkCotangentEquiv` sends the germ of `σ • u` to the germ of `σ` acting on the
image of the germ of `u`. -/
theorem conormal_germ_smul (σ : ToType (B.obj.obj (op U)))
    (u : ToType ((cSheaf A B a).val.obj (op U))) :
    letI := algebraStalk a.hom z
    naiveCotangentStalkCotangentEquiv A B a z
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (cSheaf A B a).val.presheaf U z hz).hom (σ • u)) =
      (show ToType (TopCat.Presheaf.stalk B.obj z) from
          (TopCat.Presheaf.germ B.obj U z hz).hom σ) •
        naiveCotangentStalkCotangentEquiv A B a z
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (cSheaf A B a).val.presheaf U z hz).hom u) := by
  let := algebraStalk a.hom z
  exact germ_smul_of_semilinear A B a z U hz (naiveCotangentStalkCotangentEquiv A B a z)
    (naiveCotangentStalkCotangentEquiv_semilinear A B a z)
    (PresheafOfModules.germ_smul (conormalSheafOverSource (AA A B) B (pres A B a)) z U hz) σ u

/-- For a section `σ` of `B` and a section `u` of `Ω_{A[B]/A} ⊗_{A[B]} B` over `U`,
`naiveCotangentStalkCotangentSpaceEquiv` sends the germ of `σ • u` to the germ of `σ` acting on
the image of the germ of `u`. -/
theorem tensor_germ_smul (σ : ToType (B.obj.obj (op U)))
    (u : ToType ((tSheaf A B a).val.obj (op U))) :
    letI := algebraStalk a.hom z
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _
    naiveCotangentStalkCotangentSpaceEquiv A B a z
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tSheaf A B a).val.presheaf U z hz).hom (σ • u)) =
      (show ToType (TopCat.Presheaf.stalk B.obj z) from
          (TopCat.Presheaf.germ B.obj U z hz).hom σ) •
        naiveCotangentStalkCotangentSpaceEquiv A B a z
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (tSheaf A B a).val.presheaf U z hz).hom u) := by
  let := algebraStalk a.hom z
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _
  exact germ_smul_of_semilinear A B a z U hz (naiveCotangentStalkCotangentSpaceEquiv A B a z)
    (naiveCotangentStalkCotangentSpaceEquiv_semilinear A B a z)
    (PresheafOfModules.germ_smul (tensorSheafOverSource A (AA A B) B
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
        (underlyingPresheaf (Opens.grothendieckTopology T) B)) (pres A B a)) z U hz) σ u


/-- For a section `σ` of `B` and a section `t` of the degree `-1` term over `U`, `stalkLegNegOne`
sends the germ of `σ • t` to the germ of `σ` acting on the image of the germ of `t`. -/
theorem stalkLegNegOne_germ_smul (σ : ToType (B.obj.obj (op U)))
    (t : ToType (((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
      (-1)).val.obj (op U))) :
    letI := algebraStalk a.hom z
    stalkLegNegOne A B a z
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
            (-1)).val.presheaf U z hz).hom (σ • t)) =
      (show ToType (TopCat.Presheaf.stalk B.obj z) from
          (TopCat.Presheaf.germ B.obj U z hz).hom σ) •
        stalkLegNegOne A B a z
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
              (-1)).val.presheaf U z hz).hom t) := by
  let := algebraStalk a.hom z
  refine Eq.trans (stalkLegNegOne_apply A B a z _) ?_
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentEquiv A B a z)
    (stalkAddEquivOfIso_germ_smul B z U hz (eqToIso (naiveCotangentComplex_X_negOne.{u, u, u, u}
      (Opens.grothendieckTopology T) A B a)) σ t)) ?_
  refine Eq.trans (conormal_germ_smul A B a z U hz σ _) ?_
  refine congrArg (fun y : (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
      (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.Cotangent =>
    (show ToType (TopCat.Presheaf.stalk B.obj z) from
      (TopCat.Presheaf.germ B.obj U z hz).hom σ) • y) ?_
  refine Eq.symm (Eq.trans (stalkLegNegOne_apply A B a z _) ?_)
  exact congrArg (naiveCotangentStalkCotangentEquiv A B a z)
    (stalkAddEquivOfIso_germ z (eqToIso (naiveCotangentComplex_X_negOne.{u, u, u, u}
      (Opens.grothendieckTopology T) A B a)) U hz t)

/-- For a section `σ` of `B` and a section `t` of the degree `0` term over `U`, `stalkLegZero`
sends the germ of `σ • t` to the germ of `σ` acting on the image of the germ of `t`. -/
theorem stalkLegZero_germ_smul (σ : ToType (B.obj.obj (op U)))
    (t : ToType (((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
      0).val.obj (op U))) :
    letI := algebraStalk a.hom z
    stalkLegZero A B a z
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
            0).val.presheaf U z hz).hom (σ • t)) =
      (show ToType (TopCat.Presheaf.stalk B.obj z) from
          (TopCat.Presheaf.germ B.obj U z hz).hom σ) •
        stalkLegZero A B a z
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
              0).val.presheaf U z hz).hom t) := by
  let := algebraStalk a.hom z
  refine Eq.trans (stalkLegZero_apply A B a z _) ?_
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentSpaceEquiv A B a z)
    (stalkAddEquivOfIso_germ_smul B z U hz (eqToIso (naiveCotangentComplex_X_zero.{u, u, u, u}
      (Opens.grothendieckTopology T) A B a)) σ t)) ?_
  refine Eq.trans (tensor_germ_smul A B a z U hz σ _) ?_
  refine congrArg (fun y : (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
      (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.CotangentSpace =>
    (show ToType (TopCat.Presheaf.stalk B.obj z) from
      (TopCat.Presheaf.germ B.obj U z hz).hom σ) • y) ?_
  refine Eq.symm (Eq.trans (stalkLegZero_apply A B a z _) ?_)
  exact congrArg (naiveCotangentStalkCotangentSpaceEquiv A B a z)
    (stalkAddEquivOfIso_germ z (eqToIso (naiveCotangentComplex_X_zero.{u, u, u, u}
      (Opens.grothendieckTopology T) A B a)) U hz t)


end Site

/-! ### the stalk of a restriction along an open immersion -/

section Restrict

variable {X : Scheme.{u}} (V : X.Opens) (𝒩 : X.Modules) (x : V)

/-- The stalk at `x` of the restriction of `𝒩` along `V.ι` is additively isomorphic to the stalk
of `𝒩` at the image of `x`. -/
def restrictStalkAddEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩).val.presheaf x) ≃+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) 𝒩.val.presheaf x.1) :=
  AddEquiv.ofBijective
    (AddCommGrpCat.Hom.hom ((Scheme.Modules.restrictStalkNatIso V.ι x).hom.app 𝒩))
    (ConcreteCategory.bijective_of_isIso (C := AddCommGrpCat.{u}) _)

/-- `restrictStalkAddEquiv` sends the germ at `x` of a section `v` over `W` of the restriction of
`𝒩` to the germ at the image of `x` of `v`, viewed as a section of `𝒩` over `V.ι ''ᵁ W`. -/
theorem restrictStalkAddEquiv_germ (W : V.toScheme.Opens) (hx : x ∈ W)
    (v : ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩).val.obj (op W)) :
    restrictStalkAddEquiv V 𝒩 x
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩).val.presheaf W x hx).hom v) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) 𝒩.val.presheaf (V.ι ''ᵁ W) x.1
        (show (x : X) ∈ V.ι ''ᵁ W by simpa using hx)).hom v :=
  ConcreteCategory.congr_hom
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app V.ι x 𝒩 (U := W) hx) v

/-- `restrictStalkAddEquiv` is natural in the sheaf of modules: it intertwines the maps of stalks
induced by a morphism `ε : 𝒩 ⟶ 𝒩'` and by its restriction along `V.ι`. -/
theorem restrictStalkAddEquiv_naturality {𝒩' : X.Modules} (ε : 𝒩 ⟶ 𝒩')
    (ζ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩).val.presheaf x)) :
    restrictStalkAddEquiv V 𝒩' x
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf V.toScheme.ringCatSheaf.obj).map
            ((Scheme.Modules.restrictFunctor V.ι).map ε).val)).hom ζ) =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map ε.val)).hom
        (restrictStalkAddEquiv V 𝒩 x ζ) :=
  Eq.trans (ConcreteCategory.comp_apply _ _ ζ).symm
    (Eq.trans (ConcreteCategory.congr_hom
      ((Scheme.Modules.restrictStalkNatIso V.ι x).hom.naturality ε) ζ)
      (ConcreteCategory.comp_apply _ _ ζ))

/-- The isomorphism `V.stalkIso x` sends the germ at `x` of `alpha s`, for a section `s` of `𝒪_X`
over `V`, to the germ of `s` at the image of `x`. -/
theorem germ_alpha (s : Γ(X, V)) :
    ((V.stalkIso x).hom) ((V.toScheme.presheaf.germ ⊤ x trivial) (alpha s)) =
      (X.presheaf.germ V x.1 x.2) s := by
  refine Eq.trans (ConcreteCategory.congr_hom
    (V.germ_stalkIso_hom (V := ⊤) x trivial) (alpha s)) ?_
  refine Eq.trans ?_ (TopCat.Presheaf.germ_res_apply X.presheaf (eqToHom V.ι_image_top) x.1
    (show (x : X) ∈ V.ι ''ᵁ ⊤ by simp) s)
  exact congrArg (X.presheaf.germ (V.ι ''ᵁ ⊤) x.1 (show (x : X) ∈ V.ι ''ᵁ ⊤ by simp)).hom
    (congrArg (fun r : Γ(X, V) →+* _ => r s) (congrArg CommRingCat.Hom.hom
      (Scheme.Opens.topIso_inv V)))

/-- The stalk of `𝒪_V` at `x` is isomorphic, as a `Γ(X, V)`-algebra, to the stalk of `𝒪_X` at the
image of `x`. -/
def stalkAlgEquiv :
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    (V.toScheme.presheaf.stalk x) ≃ₐ[Γ(X, V)] (X.presheaf.stalk x.1) := by
  letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  refine AlgEquiv.ofRingEquiv (f := (V.stalkIso x).commRingCatIsoToRingEquiv) ?_
  intro s
  exact germ_alpha V x s

/-- The stalk at `x` of the sheaf on `V` associated to a `Γ(X, V)`-module `M` is additively
isomorphic to `𝒪_{X,x} ⊗_{Γ(X, V)} M`. -/
def uLeg (M : ModuleCat.{u} Γ(X, V)) :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).obj
          M).val.presheaf x) ≃+
      (ToType (X.presheaf.stalk x.1) ⊗[Γ(X, V)] M) := by
  letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  exact (associatedSheafStalkAddEquiv V.toScheme.toRingedSpace (alpha (V := V)) M x).trans
    (TensorProduct.congr (stalkAlgEquiv V x).toLinearEquiv (LinearEquiv.refl Γ(X, V) M)).toAddEquiv

/-- `uLeg` sends the preimage of `w` under `associatedSheafStalkAddEquiv` to the image of `w`
under the base change of `stalkAlgEquiv`. -/
theorem uLeg_assoc_symm (M : ModuleCat.{u} Γ(X, V))
    (w : letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
      ToType (V.toScheme.presheaf.stalk x) ⊗[Γ(X, V)] M) :
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    uLeg V x M
        ((associatedSheafStalkAddEquiv V.toScheme.toRingedSpace (alpha (V := V)) M x).symm w) =
      TensorProduct.congr (stalkAlgEquiv V x).toLinearEquiv (LinearEquiv.refl Γ(X, V) M) w := by
  let := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  exact congrArg
    (TensorProduct.congr (stalkAlgEquiv V x).toLinearEquiv (LinearEquiv.refl Γ(X, V) M))
    ((associatedSheafStalkAddEquiv V.toScheme.toRingedSpace (alpha (V := V)) M
      x).apply_symm_apply w)

/-- The inverse of `uLeg` sends `stalkAlgEquiv V x g ⊗ m`, for the germ `g` at `x` of a section
of `𝒪_V`, to the preimage of `g ⊗ m` under `associatedSheafStalkAddEquiv`. -/
theorem uLeg_symm_tmul (M : ModuleCat.{u} Γ(X, V)) (W : V.toScheme.Opens) (hx : x ∈ W)
    (s : V.toScheme.presheaf.obj (op W)) (m : M) :
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    (uLeg V x M).symm
        ((stalkAlgEquiv V x ((V.toScheme.presheaf.germ W x hx).hom s)) ⊗ₜ[Γ(X, V)] m) =
      (associatedSheafStalkAddEquiv V.toScheme.toRingedSpace (alpha (V := V)) M x).symm
        ((V.toScheme.presheaf.germ W x hx).hom s ⊗ₜ[Γ(X, V)] m) := by
  let := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  refine ((uLeg V x M).symm_apply_eq).mpr ?_
  refine Eq.trans ?_ (uLeg_assoc_symm V x M _).symm
  exact (TensorProduct.congr_tmul (stalkAlgEquiv V x).toLinearEquiv (LinearEquiv.refl Γ(X, V) M)
    ((V.toScheme.presheaf.germ W x hx).hom s) m).symm

/-- For a section `q` of `𝒪_X` and a section `v` of `𝒩` over `V.ι ''ᵁ W`, the action of `q` on
`v` as sections over `W` of `𝒪_V` and of the restriction of `𝒩` along `V.ι` is `q • v`. -/
theorem smul_restrict (W : V.toScheme.Opens) (q : Γ(X, V.ι ''ᵁ W)) (v : Γ(𝒩, V.ι ''ᵁ W)) :
    (show Γ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩, W) from
      ((show Γ(V.toScheme, W) from q) •
        (show Γ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩, W) from v))) = q • v := by
  have h := Scheme.Modules.smul_restrictAppIso_hom_apply V.ι 𝒩 W q v
  rw [Scheme.Opens.ι_appIso] at h
  exact h

/-- `restrictStalkAddEquiv` sends the germ of `s` acting on the germ of `restrictTop V 𝒩 t` to the
germ at the image of `x` of `s` acting on the restriction of `restrictTop V 𝒩 t` to `W`, viewed
as sections over `V.ι ''ᵁ W`. -/
theorem restrictTop_germ_smul (W : V.toScheme.Opens) (hx : x ∈ W)
    (s : Γ(V.toScheme, W)) (t : Γ(𝒩, V)) :
    restrictStalkAddEquiv V 𝒩 x
        ((TopCat.Presheaf.germ (C := RingCat.{u}) V.toScheme.ringCatSheaf.obj W x hx).hom s •
          (show ToType (AlgebraicGeometry.SheafOfModules.stalkObj V.toScheme.ringCatSheaf x
              ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩)) from
            (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
              ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩).val.presheaf ⊤ x trivial).hom
              (restrictTop V 𝒩 t))) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) 𝒩.val.presheaf (V.ι ''ᵁ W) x.1
        (show (x : X) ∈ V.ι ''ᵁ W by simpa using hx)).hom
        ((show Γ(X, V.ι ''ᵁ W) from s) •
          (show Γ(𝒩, V.ι ''ᵁ W) from
            ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩).val.map
              (homOfLE (le_top (a := W))).op (restrictTop V 𝒩 t))) := by
  have h1 := TopCat.Presheaf.germ_res_apply
    ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩).val.presheaf (homOfLE (le_top (a := W))) x hx
    (restrictTop V 𝒩 t)
  refine Eq.trans (congrArg (fun ζ : ToType
      (AlgebraicGeometry.SheafOfModules.stalkObj V.toScheme.ringCatSheaf x
        ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩)) =>
    restrictStalkAddEquiv V 𝒩 x
      ((TopCat.Presheaf.germ (C := RingCat.{u}) V.toScheme.ringCatSheaf.obj W x hx).hom s • ζ))
    h1.symm) ?_
  refine Eq.trans (congrArg (restrictStalkAddEquiv V 𝒩 x)
    (AlgebraicGeometry.SheafOfModules.germ_hom_smul V.toScheme.ringCatSheaf x
      ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩).val W hx s _).symm) ?_
  refine Eq.trans (congrArg (restrictStalkAddEquiv V 𝒩 x)
    (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩).val.presheaf W x hx).hom
      (smul_restrict V 𝒩 W s _))) ?_
  exact restrictStalkAddEquiv_germ V 𝒩 x W hx _

end Restrict

end Stacks.NaiveCotangentAffineStalkLegs

end

end

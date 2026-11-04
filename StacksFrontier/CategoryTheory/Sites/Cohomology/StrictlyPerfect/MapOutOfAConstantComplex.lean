module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfALocallyConstantComplex
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing
import StacksCore.Tactic.StacksAttribute

/-!
# Maps out of the complex of constant sheaves on a bounded complex of finite projectives

Let `Λ` be a commutative ring and let `K^•` be a bounded complex of finite projective
`Λ`-modules. On the *constant ringed site* `(C, Λ̲)` — a site `(C, J)` with the constant sheaf of
commutative rings on `Λ` as its structure sheaf — the complex of constant sheaves of modules
`K̲^•` is a complex of `Λ̲`-modules, and every morphism `K̲^• ⟶ L^•` in the derived category of
`Λ̲|_U`-modules is, after restriction along the arrows of a covering sieve of `U`, the image of
an honest map of complexes.

## Main definitions

* `Stacks.SheafOfModules.restrictScalarsUnitIso`: restriction of scalars along an isomorphism
  of sheaves of rings carries the unit module to the unit module.
* `AlgebraicGeometry.RingedSite.constantRingedSite`: a site together with the constant sheaf of
  commutative rings on `Λ` as its structure sheaf.
* `AlgebraicGeometry.RingedSite.constantFunctorOver`: the constant sheaf of modules functor,
  read as a functor into sheaves of modules over the structure sheaf of the constant ringed
  site restricted to an object `U`.

Each of `constantRingedSite`, `constantRingSheafIso`, `constantRingSheafOverIso`,
`constantRestrict`, `constantFunctorOver` and `exists_coveringSieve_complexMap_constant` is stated
at `RingedSite.{0, 0, 0}`, and has a form with the suffix `_general` at an arbitrary site universe
`u` and coefficient universe `w` with `UnivLE.{u, w}`.

## Main results

* `AlgebraicGeometry.RingedSite.constantRingSheafIso`: the sheaf of rings underlying the
  structure sheaf of the constant ringed site is the constant sheaf of rings on `Λ`.
* `AlgebraicGeometry.RingedSite.constantRingSheafOverIso`: on the slice site `C/U` the same
  holds for the restriction of that sheaf of rings.
* `AlgebraicGeometry.RingedSite.constantFunctorOverUnitIso`: the constant sheaf of modules on
  `Λ` itself is the unit object.
* `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_constant`: **Stacks 09BD** for
  the complex of constant sheaves of modules.

## References

* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u d

namespace Stacks.SheafOfModules

section RestrictScalarsUnit

variable {T : Type u} [Category.{v} T] {K : GrothendieckTopology T}
  {A B : Sheaf K RingCat.{w}} (e : A ≅ B)

/-- The inverse of an isomorphism of sheaves of rings undoes it on sections. -/
lemma ringIso_hom_inv_apply (Z : Tᵒᵖ) (a : A.obj.obj Z) :
    (e.inv.hom.app Z).hom ((e.hom.hom.app Z).hom a) = a :=
  congr_arg (fun t : A ⟶ A => (t.hom.app Z).hom a) e.hom_inv_id

/-- An isomorphism of sheaves of rings undoes its inverse on sections. -/
lemma ringIso_inv_hom_apply (Z : Tᵒᵖ) (b : B.obj.obj Z) :
    (e.hom.hom.app Z).hom ((e.inv.hom.app Z).hom b) = b :=
  congr_arg (fun t : B ⟶ B => (t.hom.app Z).hom b) e.inv_hom_id

/-- An isomorphism of sheaves of rings is linear for the scalar action it transports: on
sections, `e (e⁻¹ b * a) = b * e a`. -/
lemma ringIso_hom_smul (Z : Tᵒᵖ) (b : B.obj.obj Z) (a : A.obj.obj Z) :
    (e.hom.hom.app Z).hom ((e.inv.hom.app Z).hom b * a) = b * (e.hom.hom.app Z).hom a := by
  rw [map_mul, ringIso_inv_hom_apply e Z b]

/-- The morphism of underlying presheaves of abelian groups of
`Stacks.SheafOfModules.restrictScalarsUnitIso`. -/
def restrictScalarsUnitAbHom :
    ((_root_.SheafOfModules.restrictScalars.{w} e.inv).obj
        (_root_.SheafOfModules.unit A)).val.presheaf ⟶
      (_root_.SheafOfModules.unit B).val.presheaf where
  app Z := AddCommGrpCat.ofHom (e.hom.hom.app Z).hom.toAddMonoidHom
  naturality Z Z' f := by
    ext x
    exact RingHom.congr_fun (congrArg RingCat.Hom.hom (e.hom.hom.naturality f)) x

/-- The morphism of underlying presheaves of abelian groups of the inverse of
`Stacks.SheafOfModules.restrictScalarsUnitIso`. -/
def restrictScalarsUnitAbInv :
    (_root_.SheafOfModules.unit B).val.presheaf ⟶
      ((_root_.SheafOfModules.restrictScalars.{w} e.inv).obj
        (_root_.SheafOfModules.unit A)).val.presheaf where
  app Z := AddCommGrpCat.ofHom (e.inv.hom.app Z).hom.toAddMonoidHom
  naturality Z Z' f := by
    ext x
    exact RingHom.congr_fun (congrArg RingCat.Hom.hom (e.inv.hom.naturality f)) x

/-- `e` itself, read as a morphism of sheaves of `B`-modules out of the unit module of `A` with
its scalars restricted along `e⁻¹`. -/
def restrictScalarsUnitHom :
    (_root_.SheafOfModules.restrictScalars.{w} e.inv).obj (_root_.SheafOfModules.unit A) ⟶
      _root_.SheafOfModules.unit B :=
  ⟨PresheafOfModules.homMk (restrictScalarsUnitAbHom e) fun Z b m => ringIso_hom_smul e Z b m⟩

/-- The inverse of `e`, read as a morphism of sheaves of `B`-modules into the unit module of `A`
with its scalars restricted along `e⁻¹`. -/
def restrictScalarsUnitInv :
    _root_.SheafOfModules.unit B ⟶
      (_root_.SheafOfModules.restrictScalars.{w} e.inv).obj (_root_.SheafOfModules.unit A) :=
  ⟨PresheafOfModules.homMk (restrictScalarsUnitAbInv e) fun Z b b' =>
    map_mul (e.inv.hom.app Z).hom b b'⟩

/-- **Restriction of scalars along an isomorphism of sheaves of rings carries the unit module to
the unit module.** The underlying sheaves of abelian groups are the two sheaves of rings
themselves, and the isomorphism between them is `e`. -/
def restrictScalarsUnitIso :
    (_root_.SheafOfModules.restrictScalars.{w} e.inv).obj (_root_.SheafOfModules.unit A) ≅
      _root_.SheafOfModules.unit B where
  hom := restrictScalarsUnitHom e
  inv := restrictScalarsUnitInv e
  hom_inv_id := by
    ext Z
    exact ringIso_hom_inv_apply e Z _
  inv_hom_id := by
    ext Z
    exact ringIso_inv_hom_apply e Z _

/-- Restriction of scalars along an isomorphism of sheaves of rings is an equivalence of the
categories of sheaves of modules. -/
instance isEquivalence_restrictScalars_inv :
    (_root_.SheafOfModules.restrictScalars.{w} e.inv).IsEquivalence :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso e).isEquivalence_functor

/-- Restriction of scalars along an isomorphism of sheaves of rings preserves finite colimits:
it is an equivalence, hence preserves colimits of every size. -/
instance preservesFiniteColimits_restrictScalars_inv :
    PreservesFiniteColimits (_root_.SheafOfModules.restrictScalars.{w} e.inv) :=
  letI _h : PreservesColimitsOfSize.{0, 0} (_root_.SheafOfModules.restrictScalars.{w} e.inv) :=
    Adjunction.isEquivalence_preservesColimits
      (_root_.SheafOfModules.restrictScalars.{w} e.inv)
  PreservesColimitsOfSize.preservesFiniteColimits
    (_root_.SheafOfModules.restrictScalars.{w} e.inv)

end RestrictScalarsUnit

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules Stacks.SheafOfModules.Constant Stacks.Sheaves.RingedPoint

section ConstantRingedSiteGeneral

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]
  [UnivLE.{u, w}]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J RingCat.{w}]

/-- **The constant ringed site, at an arbitrary site universe and an arbitrary coefficient
universe.** A site `(C, J)` with `C : Type u` and `Category.{u} C`, together with the constant
sheaf of commutative rings on a ring `Λ : Type w` as its structure sheaf, where
`UnivLE.{u, w}`.

This is the general form of `AlgebraicGeometry.RingedSite.constantRingedSite`. -/
abbrev constantRingedSite_general : RingedSite.{u, u, w} where
  C := C
  J := J
  O := (constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)

/-- The sheaf of rings underlying the structure sheaf of the constant ringed site is the
constant sheaf of rings on `Λ`: forgetting commutativity commutes with sheafification.

This is the general form of `AlgebraicGeometry.RingedSite.constantRingSheafIso`, taken over
`AlgebraicGeometry.RingedSite.constantRingedSite_general`. -/
def constantRingSheafIso_general :
    (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O) ≅
      (constantSheaf J RingCat.{w}).obj (RingCat.of Λ) :=
  (constantCommuteCompose J (forget₂ CommRingCat.{w} RingCat.{w})).app (CommRingCat.of Λ)

variable (U : C) [HasWeakSheafify (J.over U) RingCat.{w}]

/-- On the slice site `C/U` the constant sheaf of rings on `Λ` is the restriction of the sheaf
of rings underlying the structure sheaf of the constant ringed site.

This is the general form of `AlgebraicGeometry.RingedSite.constantRingSheafOverIso`, taken over
`AlgebraicGeometry.RingedSite.constantRingedSite_general`. -/
def constantRingSheafOverIso_general :
    (constantSheaf (J.over U) RingCat.{w}).obj (RingCat.of Λ) ≅
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O)).over U :=
  (Stacks.ConstantSheaf.overPullbackConstantSheafIso J RingCat.{w} U).app (RingCat.of Λ) ≪≫
    ((J.overPullback RingCat.{w} U).mapIso (constantRingSheafIso_general J Λ)).symm

variable [(J.over U).WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction of scalars along
`AlgebraicGeometry.RingedSite.constantRingSheafOverIso_general`: it reads a sheaf of
`Λ̲`-modules on `C/U` as a sheaf of modules over the restricted structure sheaf of the constant
ringed site.

This is the general form of `AlgebraicGeometry.RingedSite.constantRestrict`, taken over
`AlgebraicGeometry.RingedSite.constantRingedSite_general`. -/
abbrev constantRestrict_general :
    _root_.SheafOfModules.{w} ((constantSheaf (J.over U) RingCat.{w}).obj (RingCat.of Λ)) ⥤
      _root_.SheafOfModules.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over U) :=
  _root_.SheafOfModules.restrictScalars (constantRingSheafOverIso_general J Λ U).inv

/-- **The constant sheaf of modules over the constant ringed site.** The constant sheaf of
modules functor on `C/U`, read as a functor into sheaves of modules over the restriction to `U`
of the structure sheaf of the constant ringed site.

This is the general form of `AlgebraicGeometry.RingedSite.constantFunctorOver`, taken over
`AlgebraicGeometry.RingedSite.constantRingedSite_general`. -/
abbrev constantFunctorOver_general :
    ModuleCat.{w} Λ ⥤ _root_.SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over U) :=
  constantModuleSheafFunctor (J.over U) (R := Λ) ⋙ constantRestrict_general J Λ U

/-- The general form of
`AlgebraicGeometry.RingedSite.preservesFiniteColimits_constantFunctorOver`: the constant sheaf
of modules functor into sheaves of modules over the restricted structure sheaf preserves finite
colimits. -/
instance preservesFiniteColimits_constantFunctorOver_general :
    PreservesFiniteColimits (constantFunctorOver_general J Λ U) :=
  @comp_preservesFiniteColimits _ _ _ _ _ _
    (constantModuleSheafFunctor (J.over U) (R := Λ)) (constantRestrict_general J Λ U)
    (preservesFiniteColimits_constantModuleSheafFunctor (J.over U) (R := Λ))
    (preservesFiniteColimits_restrictScalars_inv (constantRingSheafOverIso_general J Λ U))

/-- The general form of `AlgebraicGeometry.RingedSite.additive_constantFunctorOver`: the
constant sheaf of modules functor into sheaves of modules over the restricted structure sheaf
is additive. -/
instance additive_constantFunctorOver_general :
    (constantFunctorOver_general J Λ U).Additive :=
  letI _h :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts (constantFunctorOver_general J Λ U)
  Functor.additive_of_preservesBinaryBiproducts (constantFunctorOver_general J Λ U)

/-- The constant sheaf of modules on `Λ` itself is the unit object.

This is the general form of `AlgebraicGeometry.RingedSite.constantFunctorOverUnitIso`, taken
over `AlgebraicGeometry.RingedSite.constantRingedSite_general`. -/
def constantFunctorOverUnitIso_general :
    (constantFunctorOver_general J Λ U).obj (ModuleCat.of Λ Λ) ≅
      _root_.SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over U) :=
  (constantRestrict_general J Λ U).mapIso
      (unitIsoConstantModuleSheaf (J.over U) (R := Λ)).symm ≪≫
    restrictScalarsUnitIso (constantRingSheafOverIso_general J Λ U)

omit [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Maps out of the complex of constant sheaves of modules, at an arbitrary site universe and
an arbitrary coefficient universe.** Let `Λ` be a commutative ring, let `K^•` be a bounded
complex of finite projective `Λ`-modules, and let `L^•` be a complex of sheaves of modules over
the restriction to `U` of the structure sheaf `Λ̲` of the constant ringed site. Any morphism
`K̲^• ⟶ L^•` of `D(Λ̲|_U)` is, after restriction along the arrows of a covering sieve of `U`,
the image under the localisation functor of a morphism of complexes.

This is the general form of
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_constant`. -/
theorem exists_coveringSieve_complexMap_constant_general
    [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{w}]
    [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasDerivedCategory.{d}
      (_root_.SheafOfModules.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over U))]
    {P : CochainComplex (ModuleCat.{w} Λ) ℤ} (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i))
    {F : CochainComplex
      (_root_.SheafOfModules.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over U)) ℤ}
    (α : DerivedCategory.Q.obj
        (((constantFunctorOver_general J Λ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj F) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ {V : C} (f : V ⟶ U), S f →
        let H := _root_.SheafOfModules.overMap
          (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O) f
        ∃ (hsheaf : HasSheafify (J.over V) AddCommGrpCat)
          (hlocal : (J.over V).WEqualsLocallyBijective AddCommGrpCat),
          letI := hsheaf
          letI := hlocal
          letI : HasDerivedCategory
              (_root_.SheafOfModules
                ((Stacks.SheafOfModules.Tensor.ringSheaf
                  (constantRingedSite_general J Λ).O).over V)) :=
            HasDerivedCategory.standard _
          ∃ (hadd : H.Additive)
            (hlim : PreservesFiniteLimits H)
            (hcolim : PreservesFiniteColimits H),
            letI := hadd
            letI := hlim
            letI := hcolim
            ∃ β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((constantFunctorOver_general J Λ U).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P) ⟶
                (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
              H.mapDerivedCategory.map α ≫ H.mapDerivedCategoryFactors.hom.app F =
                H.mapDerivedCategoryFactors.hom.app
                    (((constantFunctorOver_general J Λ U).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj P) ≫
                  DerivedCategory.Q.map β :=
  exists_coveringSieve_complexMap (constantRingedSite_general J Λ) U
    (Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective
      (constantFunctorOver_general J Λ U) (constantFunctorOverUnitIso_general J Λ U)
      (Stacks.SheafOfModules.finite_notIsZero_of_strictlyBounded P a b) hfin hproj) α

end ConstantRingedSiteGeneral

variable {C : Type} [SmallCategory C] (J : GrothendieckTopology C) (Λ : Type) [CommRing Λ]
  [HasWeakSheafify J CommRingCat.{0}] [HasWeakSheafify J RingCat.{0}]

/-- **The constant ringed site.** A site together with the constant sheaf of commutative rings
on `Λ` as its structure sheaf. -/
abbrev constantRingedSite : RingedSite.{0, 0, 0} where
  C := C
  J := J
  O := (constantSheaf J CommRingCat.{0}).obj (CommRingCat.of Λ)

/-- The sheaf of rings underlying the structure sheaf of the constant ringed site is the
constant sheaf of rings on `Λ`: forgetting commutativity commutes with sheafification. -/
def constantRingSheafIso :
    (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite J Λ).O) ≅
      (constantSheaf J RingCat.{0}).obj (RingCat.of Λ) :=
  (constantCommuteCompose J (forget₂ CommRingCat.{0} RingCat.{0})).app (CommRingCat.of Λ)

variable (U : C) [HasWeakSheafify (J.over U) RingCat.{0}]

/-- On the slice site `C/U` the constant sheaf of rings on `Λ` is the restriction of the sheaf
of rings underlying the structure sheaf of the constant ringed site. -/
def constantRingSheafOverIso :
    (constantSheaf (J.over U) RingCat.{0}).obj (RingCat.of Λ) ≅
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite J Λ).O)).over U :=
  (Stacks.ConstantSheaf.overPullbackConstantSheafIso J RingCat.{0} U).app (RingCat.of Λ) ≪≫
    ((J.overPullback RingCat.{0} U).mapIso (constantRingSheafIso J Λ)).symm

variable [(J.over U).WEqualsLocallyBijective RingCat.{0}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{0}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Restriction of scalars along `AlgebraicGeometry.RingedSite.constantRingSheafOverIso`: it
reads a sheaf of `Λ̲`-modules on `C/U` as a sheaf of modules over the restricted structure sheaf
of the constant ringed site. -/
abbrev constantRestrict :
    _root_.SheafOfModules.{0} ((constantSheaf (J.over U) RingCat.{0}).obj (RingCat.of Λ)) ⥤
      _root_.SheafOfModules.{0}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite J Λ).O).over U) :=
  _root_.SheafOfModules.restrictScalars (constantRingSheafOverIso J Λ U).inv

/-- **The constant sheaf of modules over the constant ringed site.** The constant sheaf of
modules functor on `C/U`, read as a functor into sheaves of modules over the restriction to `U`
of the structure sheaf of the constant ringed site. -/
abbrev constantFunctorOver :
    ModuleCat.{0} Λ ⥤ _root_.SheafOfModules.{0}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite J Λ).O).over U) :=
  constantModuleSheafFunctor (J.over U) (R := Λ) ⋙ constantRestrict J Λ U

/-- The constant sheaf of modules functor into sheaves of modules over the restricted structure
sheaf preserves finite colimits. -/
instance preservesFiniteColimits_constantFunctorOver :
    PreservesFiniteColimits (constantFunctorOver J Λ U) :=
  @comp_preservesFiniteColimits _ _ _ _ _ _
    (constantModuleSheafFunctor (J.over U) (R := Λ)) (constantRestrict J Λ U)
    (preservesFiniteColimits_constantModuleSheafFunctor (J.over U) (R := Λ))
    (preservesFiniteColimits_restrictScalars_inv (constantRingSheafOverIso J Λ U))

/-- The constant sheaf of modules functor into sheaves of modules over the restricted structure
sheaf is additive. -/
instance additive_constantFunctorOver : (constantFunctorOver J Λ U).Additive :=
  letI _h := preservesBinaryBiproducts_of_preservesBinaryCoproducts (constantFunctorOver J Λ U)
  Functor.additive_of_preservesBinaryBiproducts (constantFunctorOver J Λ U)

/-- The constant sheaf of modules on `Λ` itself is the unit object. -/
def constantFunctorOverUnitIso :
    (constantFunctorOver J Λ U).obj (ModuleCat.of Λ Λ) ≅
      _root_.SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite J Λ).O).over U) :=
  (constantRestrict J Λ U).mapIso (unitIsoConstantModuleSheaf (J.over U) (R := Λ)).symm ≪≫
    restrictScalarsUnitIso (constantRingSheafOverIso J Λ U)

omit [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- **Maps out of the complex of constant sheaves of modules.** Let `Λ` be a commutative ring, let
`K^•` be a bounded complex of finite projective `Λ`-modules, and let `L^•` be a complex of sheaves
of modules over the restriction to `U` of the structure sheaf `Λ̲` of the constant ringed site.
Any morphism `K̲^• ⟶ L^•` of `D(Λ̲|_U)` is, after restriction along the arrows of a covering sieve
of `U`, the image under the localisation functor of a morphism of complexes. -/
@[stacks 09BD "local_representation_for_the_constant_complex"]
theorem exists_coveringSieve_complexMap_constant
    [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{0}]
    [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [HasDerivedCategory.{d}
      (_root_.SheafOfModules.{0}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite J Λ).O).over U))]
    {P : CochainComplex (ModuleCat.{0} Λ) ℤ} (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i))
    {F : CochainComplex
      (_root_.SheafOfModules.{0}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite J Λ).O).over U)) ℤ}
    (α : DerivedCategory.Q.obj
        (((constantFunctorOver J Λ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj F) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ {V : C} (f : V ⟶ U), S f →
        let H := _root_.SheafOfModules.overMap
          (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite J Λ).O) f
        ∃ (hsheaf : HasSheafify (J.over V) AddCommGrpCat)
          (hlocal : (J.over V).WEqualsLocallyBijective AddCommGrpCat),
          letI := hsheaf
          letI := hlocal
          letI : HasDerivedCategory
              (_root_.SheafOfModules
                ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite J Λ).O).over V)) :=
            HasDerivedCategory.standard _
          ∃ (hadd : H.Additive)
            (hlim : PreservesFiniteLimits H)
            (hcolim : PreservesFiniteColimits H),
            letI := hadd
            letI := hlim
            letI := hcolim
            ∃ β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((constantFunctorOver J Λ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
                (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
              H.mapDerivedCategory.map α ≫ H.mapDerivedCategoryFactors.hom.app F =
                H.mapDerivedCategoryFactors.hom.app
                    (((constantFunctorOver J Λ U).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj P) ≫
                  DerivedCategory.Q.map β :=
  exists_coveringSieve_complexMap_of_finite_projective (constantRingedSite J Λ) U
    (constantFunctorOver J Λ U) (constantFunctorOverUnitIso J Λ U) a b hfin hproj α

end AlgebraicGeometry.RingedSite

end

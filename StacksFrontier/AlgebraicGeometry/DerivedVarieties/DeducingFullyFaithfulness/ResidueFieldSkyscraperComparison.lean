module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.DerivedTensorResidueFieldSkyscraper
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.LocalVanishingCriteria
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.ResidueFieldSkyscraper
public import StacksCore.Tactic.StacksAttribute

/-!
# The two residue-field skyscrapers at a point agree

Let `X` be a scheme and `x` a point of it.  The skyscraper sheaf `𝒪_x` of `𝒪_X`-modules at `x`
with value the residue field `κ(x)` is built in two ways in this library, and
[Stacks, Tag 0G03] states six things about one `𝒪_x`:

* `AlgebraicGeometry.residueFieldSkyscraper`, the sheafification of the skyscraper presheaf of
  modules at `x` with value `κ(x) = X.residueField x`, a module over the `CommRingCat`-valued
  stalk `𝒪_{X,x}`;
* `AlgebraicGeometry.residueFieldSkyscraperSheaf`, the skyscraper sheaf of modules at `x` with
  value the residue field of the maximal ideal of the `RingCat`-valued stalk, which is the ring
  the sheaf-of-modules stalk functor and the derived tensor product work over.

Parts (1), (2), (3), (5) and (6) of the tag are stated with the second, part (4) with the first.
This file identifies them, so that the six parts speak about one sheaf, and restates part (4) in
the spelling of the other five.

## Main definitions

* `AlgebraicGeometry.residueFieldSkyscraperIso`: the isomorphism of `𝒪_X`-modules between the two
  constructions.

## Main results

* `AlgebraicGeometry.residueFieldStalkRingEquiv_symm_smul`: the two readings of `κ(x)` agree
  compatibly with the two readings of the stalk ring.
* `exists_mem_forall_isZero_stalkHomology_of_subsingleton_hom_to_residueFieldSkyscraperSheaf`:
  part (4) of the tag, with `𝒪_x` read as `residueFieldSkyscraperSheaf`.

## Implementation notes

The comparison is built at the level of presheaves of modules, as
`AlgebraicGeometry.residueFieldSkyscraperPOMHom`, and then sheafified.

## References

* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
* [Stacks Project, Tag 0GWZ](https://stacks.math.columbia.edu/tag/0GWZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open StacksDraft.StalkRingComparison

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- The residue map makes the residue field `κ(x)` an algebra over the stalk `𝒪_{X,x}`. -/
@[instance_reducible]
def residueFieldAlgebra (X : Scheme.{u}) (x : X) :
    Algebra (X.presheaf.stalk x) (X.residueField x) :=
  (X.residue x).hom.toAlgebra

attribute [local instance] residueFieldAlgebra Classical.propDecidable

variable (X : Scheme.{u}) (x : X)

/-- `κ(x)`, as a module over the `CommRingCat`-valued stalk `𝒪_{X,x}` acting through the residue
map: the value of the skyscraper `AlgebraicGeometry.residueFieldSkyscraper`. -/
abbrev residueFieldValueComm : ModuleCat.{u} (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x) (X.residueField x)

/-- `residueFieldSkyscraper X x` is the sheafification of the skyscraper presheaf of modules at
`x` with value `κ(x)`. -/
theorem residueFieldSkyscraper_eq_sheafify :
    residueFieldSkyscraper X x =
      OXModule.sheafify.obj (OXModule.skyscraperPOM x (residueFieldValueComm X x)) := rfl

/-- The residue field of the maximal ideal of a local ring `R`, regarded as a prime, receives the
residue map of `R` through its structure map. -/
theorem residueFieldMaximalIdealEquiv_algebraMap (R : Type u) [CommRing R] [IsLocalRing R]
    (a : R) :
    residueFieldMaximalIdealEquiv R
        (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a) =
      IsLocalRing.residue R a := by
  exact congrArg (IsLocalRing.residue R)
    (RingEquiv.symm_apply_apply (IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
      (S := Localization.AtPrime (IsLocalRing.maximalIdeal R))
      fun _ ha => IsLocalRing.notMem_maximalIdeal.mp ha).toRingEquiv a)

/-- The identification of the residue field of the maximal ideal of the `RingCat`-valued stalk
with `κ(x)` sends the class of `a` to the residue of the image of `a` in `𝒪_{X,x}`. -/
theorem residueFieldStalkRingEquiv_algebraMap (a : ToType (stalkRing X x)) :
    residueFieldStalkRingEquiv X x
        (algebraMap (ToType (stalkRing X x))
          (IsLocalRing.maximalIdeal (ToType (stalkRing X x))).ResidueField a) =
      (X.residue x).hom (stalkRingEquiv X x a) :=
  congrArg (IsLocalRing.ResidueField.mapEquiv (stalkRingEquiv X x))
    (residueFieldMaximalIdealEquiv_algebraMap (ToType (stalkRing X x)) a)

/-- **The two residue fields agree compatibly with the two stalk rings.**  The identification of
the residue field of the maximal ideal of the `RingCat`-valued stalk with `κ(x)` is semilinear
over the comparison of the two stalk rings. -/
theorem residueFieldStalkRingEquiv_symm_smul (a : ToType (stalkRing X x))
    (y : residueFieldValueComm X x) :
    (residueFieldStalkRingEquiv X x).symm (stalkRingEquiv X x a • y) =
      a • (residueFieldStalkRingEquiv X x).symm y := by
  simp only [Algebra.smul_def]
  rw [map_mul]
  exact congrArg (fun z => z * (residueFieldStalkRingEquiv X x).symm y)
    ((RingEquiv.symm_apply_eq _).2 (residueFieldStalkRingEquiv_algebraMap X x a).symm)

/-- Over an open containing `x`, the sections of the two skyscrapers at `x` are both the residue
field `κ(x)`: those of the skyscraper presheaf of modules by definition, those of the skyscraper
sheaf as the constant functions out of the proof of membership. -/
def residueFieldSkyscraperAppIsoOfMem (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop) :
    (OXModule.skyscraperPOM x (residueFieldValueComm X x)).presheaf.obj U ≅
      (residueFieldSkyscraperSheaf X x).val.presheaf.obj U :=
  eqToIso (OXModule.skyscraperPOM_presheaf_obj_eq x (residueFieldValueComm X x) U hx) ≪≫
    AddEquiv.toAddCommGrpIso
      { toFun := fun m _ => (residueFieldStalkRingEquiv X x).symm m
        invFun := fun s => residueFieldStalkRingEquiv X x (s ⟨hx⟩)
        left_inv := fun m => (residueFieldStalkRingEquiv X x).apply_symm_apply m
        right_inv := fun s => funext fun _ =>
          ((residueFieldStalkRingEquiv X x).symm_apply_apply (s ⟨hx⟩)).trans rfl
        map_add' := fun m₁ m₂ =>
          funext fun _ => map_add (residueFieldStalkRingEquiv X x).symm m₁ m₂ }

/-- Away from `x` the skyscraper presheaf of modules has no sections beyond zero. -/
theorem isZero_skyscraperPOM_presheaf_obj (U : (Opens X.carrier)ᵒᵖ) (hx : x ∉ U.unop) :
    IsZero ((OXModule.skyscraperPOM x (residueFieldValueComm X x)).presheaf.obj U) :=
  AddCommGrpCat.isZero_iff_subsingleton.2
    (OXModule.subsingleton_skyscraperPOM_presheaf_obj x (residueFieldValueComm X x) U hx)

/-- Away from `x` the skyscraper sheaf has no sections beyond zero. -/
theorem isZero_residueFieldSkyscraperSheaf_presheaf_obj (U : (Opens X.carrier)ᵒᵖ)
    (hx : x ∉ U.unop) :
    IsZero ((residueFieldSkyscraperSheaf X x).val.presheaf.obj U) := by
  refine AddCommGrpCat.isZero_iff_subsingleton.2 ⟨fun f g => ?_⟩
  exact funext fun h => absurd h.down hx

/-- The component of the comparison of the underlying presheaves of abelian groups at an open:
the identification above where the open contains `x`, and the unique map between zero objects
elsewhere. -/
def residueFieldSkyscraperAppIso (U : (Opens X.carrier)ᵒᵖ) :
    (OXModule.skyscraperPOM x (residueFieldValueComm X x)).presheaf.obj U ≅
      (residueFieldSkyscraperSheaf X x).val.presheaf.obj U :=
  if hx : x ∈ U.unop then residueFieldSkyscraperAppIsoOfMem X x U hx
  else (isZero_skyscraperPOM_presheaf_obj X x U hx).iso
    (isZero_residueFieldSkyscraperSheaf_presheaf_obj X x U hx)

/-- Over an open containing `x`, the component of the comparison is the identification of both
sections modules with `κ(x)`. -/
theorem residueFieldSkyscraperAppIso_of_mem (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop) :
    residueFieldSkyscraperAppIso X x U = residueFieldSkyscraperAppIsoOfMem X x U hx :=
  dite_eq_left hx

/-- **The underlying presheaves of abelian groups of the two residue-field skyscrapers at `x`
agree.** -/
def residueFieldSkyscraperPresheafIso :
    (OXModule.skyscraperPOM x (residueFieldValueComm X x)).presheaf ≅
      (residueFieldSkyscraperSheaf X x).val.presheaf :=
  NatIso.ofComponents (residueFieldSkyscraperAppIso X x) (by
    intro U V i
    by_cases hxV : x ∈ V.unop
    · have hxU : x ∈ U.unop := (leOfHom i.unop) hxV
      rw [residueFieldSkyscraperAppIso_of_mem X x U hxU,
        residueFieldSkyscraperAppIso_of_mem X x V hxV,
        OXModule.skyscraperPOM_presheaf_map_eq x (residueFieldValueComm X x) i hxV]
      simp only [residueFieldSkyscraperAppIsoOfMem, Iso.trans_hom, eqToIso.hom, Category.assoc,
        eqToHom_trans_assoc, eqToHom_trans]
      rfl
    · exact (isZero_residueFieldSkyscraperSheaf_presheaf_obj X x V hxV).eq_of_tgt _ _)

/-- On an open containing `x`, the comparison sends a section of the skyscraper presheaf of
modules to the constant function at the image of its value. -/
theorem residueFieldSkyscraperPresheafIso_hom_app_apply (U : (Opens X.carrier)ᵒᵖ)
    (hx : x ∈ U.unop)
    (m : (OXModule.skyscraperPOM x (residueFieldValueComm X x)).presheaf.obj U)
    (h : PLift (x ∈ U.unop)) :
    ConcreteCategory.hom ((residueFieldSkyscraperPresheafIso X x).hom.app U) m h =
      (residueFieldStalkRingEquiv X x).symm
        (ConcreteCategory.hom (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x
          (residueFieldValueComm X x) U hx)) m) := by
  have happ : (residueFieldSkyscraperPresheafIso X x).hom.app U =
      (residueFieldSkyscraperAppIsoOfMem X x U hx).hom :=
    congrArg Iso.hom (residueFieldSkyscraperAppIso_of_mem X x U hx)
  rw [happ]
  rfl

/-- The identification of the sections of the skyscraper presheaf of modules over an open
containing `x` with the residue field of the `RingCat`-valued stalk turns the action of the
structure sheaf into the action of that stalk through its germ at `x`. -/
theorem residueFieldStalkRingEquiv_symm_leg_smul (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop)
    (r : (X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
    (m : OXModule.skyscraperObj x (residueFieldValueComm X x) U) :
    (residueFieldStalkRingEquiv X x).symm
        (ConcreteCategory.hom (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x
          (residueFieldValueComm X x) U hx)) (r • m)) =
      ConcreteCategory.hom (TopCat.Presheaf.germ (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj U.unop x hx) r •
        (residueFieldStalkRingEquiv X x).symm
          (ConcreteCategory.hom (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x
            (residueFieldValueComm X x) U hx)) m) := by
  rw [OXModule.skyscraperPOM_leg_smul x (residueFieldValueComm X x) U hx r m,
    ← stalkRingEquiv_germ X x U.unop hx r, residueFieldStalkRingEquiv_symm_smul]

/-- On an open containing `x`, the comparison is linear for the action of the structure sheaf:
both actions are through the germ at `x`, and the two readings of the residue field match. -/
theorem residueFieldSkyscraperPresheafIso_hom_app_smul (U : (Opens X.carrier)ᵒᵖ)
    (hx : x ∈ U.unop)
    (r : (OXModule.ringSheaf X.toRingedSpace).obj.obj U)
    (m : (OXModule.skyscraperPOM x (residueFieldValueComm X x)).obj U)
    (h : PLift (x ∈ U.unop)) :
    ConcreteCategory.hom ((residueFieldSkyscraperPresheafIso X x).hom.app U) (r • m) h =
      ConcreteCategory.hom (TopCat.Presheaf.germ (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj U.unop x hx) r •
        (residueFieldStalkRingEquiv X x).symm
          (ConcreteCategory.hom (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x
            (residueFieldValueComm X x) U hx)) m) := by
  rw [residueFieldSkyscraperPresheafIso_hom_app_apply X x U hx (r • m) h]
  exact residueFieldStalkRingEquiv_symm_leg_smul X x U hx r m

/-- The comparison `residueFieldSkyscraperPresheafIso` as a morphism of presheaves of modules from
the skyscraper presheaf of modules at `x` to the skyscraper sheaf of modules at `x`. -/
def residueFieldSkyscraperPOMHom :
    OXModule.skyscraperPOM x (residueFieldValueComm X x) ⟶
      (residueFieldSkyscraperSheaf X x).val :=
  PresheafOfModules.homMk (residueFieldSkyscraperPresheafIso X x).hom (by
    intro U r m
    by_cases hx : x ∈ U.unop
    · refine funext fun h => Eq.trans
        (residueFieldSkyscraperPresheafIso_hom_app_smul X x U hx r m h) ?_
      exact congrArg
        (fun z : (IsLocalRing.maximalIdeal (ToType (stalkRing X x))).ResidueField =>
          ConcreteCategory.hom (TopCat.Presheaf.germ (C := RingCat.{u})
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj U.unop x hx) r • z)
        (residueFieldSkyscraperPresheafIso_hom_app_apply X x U hx m h).symm
    · exact funext fun h => absurd h.down hx)

/-- The comparison `residueFieldSkyscraperPOMHom` of presheaves of modules is an isomorphism. -/
instance isIso_residueFieldSkyscraperPOMHom : IsIso (residueFieldSkyscraperPOMHom X x) := by
  have h : IsIso ((PresheafOfModules.toPresheaf ((OXModule.ringSheaf X.toRingedSpace).obj)).map
      (residueFieldSkyscraperPOMHom X x)) :=
    (residueFieldSkyscraperPresheafIso X x).isIso_hom
  exact isIso_of_reflects_iso _
    (PresheafOfModules.toPresheaf ((OXModule.ringSheaf X.toRingedSpace).obj))

/-- **The two residue-field skyscrapers at `x` agree.**  The sheafification of the skyscraper
presheaf of modules at `x` with value `κ(x)` is the skyscraper sheaf of modules at `x` with value
the residue field of the `RingCat`-valued stalk. -/
@[stacks 0G03 "the two spellings of the residue-field skyscraper 𝒪_x agree, identifying part \
(4)'s with the one used by parts (1), (2), (3), (5), (6)"]
def residueFieldSkyscraperIso :
    residueFieldSkyscraper X x ≅ residueFieldSkyscraperSheaf X x :=
  OXModule.sheafify.mapIso (asIso (residueFieldSkyscraperPOMHom X x)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := OXModule.ringSheaf X.toRingedSpace) (𝟙 _)).counit).app
        (residueFieldSkyscraperSheaf X x)

/-- Let `X` be a Noetherian scheme, `x ∈ X` a point, `𝒪_x` the skyscraper sheaf
`residueFieldSkyscraperSheaf X x` at `x` with value `κ(x)` and `K` a perfect object of `D(𝒪_X)`.
If `Hom_X(K, 𝒪_x[i]) = 0` for all `i ∈ ℤ`, then there is an open neighbourhood of `x` at every
point of which every cohomology sheaf of `K` has zero stalk. -/
@[stacks 0G03 "part (4), for X a Noetherian scheme (which every scheme of finite type over a \
field is), x any point and K perfect, with 𝒪_x read as residueFieldSkyscraperSheaf, the spelling \
parts (1), (2), (3), (5) and (6) use: if Hom_{D(𝒪_X)}(K, 𝒪_x[i]) = 0 for all i then every \
cohomology sheaf of K has vanishing stalk at every point of an open neighbourhood of x"]
theorem exists_mem_forall_isZero_stalkHomology_of_subsingleton_hom_to_residueFieldSkyscraperSheaf
    [IsNoetherian X] (K : DerivedCategory X.Modules)
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ i : ℤ, Subsingleton (K ⟶ ((DerivedCategory.singleFunctor X.Modules 0).obj
      (residueFieldSkyscraperSheaf X x))⟦i⟧)) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (OXModule.stalk ((DerivedCategory.homologyFunctor X.Modules i).obj K) y) :=
  exists_mem_forall_isZero_stalkHomology_of_subsingleton_hom_to_residueFieldSkyscraper X x K hK
    fun i => @Function.Injective.subsingleton _ _ _
      (Iso.homCongr (Iso.refl K)
        ((shiftFunctor (DerivedCategory X.Modules) i).mapIso
          ((DerivedCategory.singleFunctor X.Modules 0).mapIso
            (residueFieldSkyscraperIso X x)))).injective (h i)

end AlgebraicGeometry

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.StalkDepthCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs

/-!
# An invertible sheaf with trivial divisor class is trivial

Let `X` be a normal locally Noetherian integral scheme. The first Chern class
`Pic(X) → Cl(X)` of `AlgebraicGeometry.picardToWeilDivisorClassGroup` is injective: an
invertible sheaf whose Weil divisor class vanishes is isomorphic to `𝒪_X`.

The argument is the one of the Stacks Project. Let `L` be invertible and let `s` be a regular
meromorphic section of it; the hypothesis says that `div_L(s) = div(f)` for an invertible
rational function `f`. The generic stalk `L_η` is free of rank one over the function field `K`,
and the *normalized* generic vector `v = f⁻¹ · s_η` is a basis of it. At a point `ξ` of
codimension one the module `L_ξ` is free of rank one over the discrete valuation ring
`𝒪_{X, ξ}`, with basis `m` say, and the coordinate `a` of `s_η` against `m` has
`ord_ξ(a) = ord_ξ(f)` — that is exactly the coefficientwise form of `div_L(s) = div(f)`. So
`f⁻¹ a` has order of vanishing zero at `ξ`, hence is the image of a *unit* of `𝒪_{X, ξ}`, and
`v = (unit) · m`: the normalized vector generates the image of `L_ξ` in `L_η` as well.

Multiplication by `v` and the coordinate against `v` are therefore mutually inverse
`K`-linear maps between `𝒪_{X, η}` and `L_η` which, at every codimension-one point, carry the
image of one stalk into the image of the other. The extension criterion of Tag 0AY7 turns each
into a map of `𝒪_X`-modules, because `L` and `𝒪_X` are reflexive, and the two composites are
the identity because a map into a torsion-free module is determined by its generic stalk. That
is the required isomorphism `L ≅ 𝒪_X`.

## Main definitions

* `AlgebraicGeometry.genericStructStalkEquiv`: the generic stalk of the structure sheaf is the
  function field.

## Main results

* `AlgebraicGeometry.isReflexive_of_isInvertible`: an invertible module is reflexive.
* `AlgebraicGeometry.exists_hom_of_mapsTo_stalkSpecializes`: a linear map of generic stalks
  which respects the codimension-one lattices extends to a morphism of modules, when the target
  is reflexive. This is Tag 0AY7 with the reflexive hull removed.
* `AlgebraicGeometry.hom_ext_of_genericStalk`: two morphisms into an invertible module agree as
  soon as they agree on generic stalks.
* `AlgebraicGeometry.exists_isUnit_smul_stalkSpecializes_eq`: the normalization step — at a
  codimension-one point the normalized generic vector is a unit multiple of a generator.
* `AlgebraicGeometry.nonempty_iso_unit_of_weilDivisorClassOfInvertibleSheaf_eq_zero`: an
  invertible module with vanishing Weil divisor class is isomorphic to the structure sheaf.
* `AlgebraicGeometry.picardToWeilDivisorClassGroup_injective`: Tag 0BE8.

## Implementation notes

**Which invertibility.** `AlgebraicGeometry.SheafOfModules.IsInvertible` throughout, since that
is the spelling of the Weil divisor class of Tag 0BE6 and of the first Chern class of Tag 0BE7;
the Picard group of Tag 01CX used here is
`Stacks.SheafOfModules.PicardGroup`, stated at `Stacks.SheafOfModules.IsInvertible`, and the two
are exchanged by the existing bridge
`Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry`. No new bridge is written.

**Which structure module.** The structure sheaf read as a module over itself is
`Stacks.Divisors.structureModule`, the one the associated points of a scheme are defined at; it
is not redefined here, only shown to be invertible.

**Which order of vanishing.** `AlgebraicGeometry.orderOfVanishingMeromorphic` of Tag 02SF, read
through `AlgebraicGeometry.orderOfVanishingMeromorphicData`, and Mathlib's
`AlgebraicGeometry.Scheme.ord`. That `ord` is zero exactly on the images of the units of the
local ring is `Stacks.AlgebraicGeometry.UnitsNormalProper.exists_isUnit_of_ord_eq_zero`, which
is where normality enters a second time, after Tag 0AY7.

## References

* [Stacks Project, Tag 0BE8](https://stacks.math.columbia.edu/tag/0BE8)
* [Stacks Project, Tag 0BE7](https://stacks.math.columbia.edu/tag/0BE7)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 0AY7](https://stacks.math.columbia.edu/tag/0AY7)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Order TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open _root_.AlgebraicGeometry

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-- The stalk map of a composite of morphisms of modules is the composite of the stalk maps. -/
theorem stalkMapOfHom_comp_apply {F G H : X.Modules} (f : F ⟶ G) (g : G ⟶ H) (x : X)
    (m : F.presheaf.stalk x) :
    stalkMapOfHom (f ≫ g) x m = stalkMapOfHom g x (stalkMapOfHom f x m) :=
  (ConcreteCategory.congr_hom
      ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_comp f g) m).trans
    (ConcreteCategory.comp_apply (stalkMapOfHom f x) (stalkMapOfHom g x) m)

/-- The stalk map of an identity morphism is the identity. -/
theorem stalkMapOfHom_id_apply (F : X.Modules) (x : X) (m : F.presheaf.stalk x) :
    stalkMapOfHom (𝟙 F) x m = m :=
  (ConcreteCategory.congr_hom
      ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_id F) m).trans
    (ConcreteCategory.id_apply m)

/-- The identification of the stalk of the structure sheaf read as the unit module with the
stalk of the structure sheaf as a ring commutes with specialization: both sides send a germ to
the germ at the more generic point. -/
theorem structStalkLinearEquiv_stalkSpecializes (X : _root_.AlgebraicGeometry.Scheme.{u})
    {x y : X} (h : y ⤳ x) (m : structStalk X x) :
    structStalkLinearEquiv X y
        (TopCat.Presheaf.stalkSpecializes (C := Ab.{u})
          (unitModulePresheaf X.presheaf).presheaf h m)
      = X.presheaf.stalkSpecializes h (structStalkLinearEquiv X x m) := by
  obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (C := Ab.{u}) (unitModulePresheaf X.presheaf).presheaf m
  have hunit : TopCat.Presheaf.stalkSpecializes (C := Ab.{u})
        (unitModulePresheaf X.presheaf).presheaf h
        (TopCat.Presheaf.germ (C := Ab.{u}) (unitModulePresheaf X.presheaf).presheaf U x hxU r)
      = TopCat.Presheaf.germ (C := Ab.{u}) (unitModulePresheaf X.presheaf).presheaf U y
          (h.mem_open U.isOpen hxU) r :=
    congrArg (fun f => (ConcreteCategory.hom f) r)
      (TopCat.Presheaf.germ_stalkSpecializes (C := Ab.{u})
        (unitModulePresheaf X.presheaf).presheaf hxU h)
  have hring : X.presheaf.stalkSpecializes h (X.presheaf.germ U x hxU r)
      = X.presheaf.germ U y (h.mem_open U.isOpen hxU) r :=
    congrArg (fun f => (ConcreteCategory.hom f) r)
      (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU h)
  have hy : structStalkLinearEquiv X y
        (TopCat.Presheaf.germ (C := Ab.{u}) (unitModulePresheaf X.presheaf).presheaf U y
          (h.mem_open U.isOpen hxU) r)
      = X.presheaf.germ U y (h.mem_open U.isOpen hxU) r :=
    structStalkLinearEquiv_germ X y U (h.mem_open U.isOpen hxU) r
  have hx : structStalkLinearEquiv X x
        (TopCat.Presheaf.germ (C := Ab.{u}) (unitModulePresheaf X.presheaf).presheaf U x hxU r)
      = X.presheaf.germ U x hxU r :=
    structStalkLinearEquiv_germ X x U hxU r
  rw [hunit, hy, hx, hring]

end Stacks.AlgebraicGeometry.ReflexiveModules

namespace AlgebraicGeometry

attribute [local instance] schemePicardGroupAddCommGroup

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- The structure sheaf is invertible as a module over itself, in the spelling the Weil divisor
class of Tag 0BE6 is stated at; the mathematics is `Stacks.SheafOfModules.isInvertible_unit`,
crossed by the existing comparison of the two spellings of invertibility. -/
instance isInvertible_structureModule :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Divisors.structureModule X) :=
  (Stacks.SheafOfModules.isInvertible_unit _ _).toAlgebraicGeometry _ _ _

omit [IsLocallyNoetherian X] in
/-- The canonical map from the local ring at a point to the function field is the specialization
map of the structure sheaf towards the generic point. -/
theorem algebraMap_functionField_eq_stalkSpecializes (x : X) (r : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk x) X.functionField r =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x)) r :=
  rfl

/-- **The generic stalk of the structure sheaf is the function field.** This is
`Stacks.AlgebraicGeometry.ReflexiveModules.structStalkLinearEquiv` at the generic point, read at
the module structure of the generic stalk of an `𝒪_X`-module, which is the one the extension
criterion of Tag 0AY7 is stated at. -/
def genericStructStalkEquiv :
    (Stacks.Divisors.structureModule X).presheaf.stalk (genericPoint X) ≃ₗ[X.functionField]
      X.functionField :=
  structStalkLinearEquiv X (genericPoint X)

omit [IsLocallyNoetherian X] in
/-- The identification of the generic stalk of the structure sheaf with the function field
commutes with specialization from the generic point. -/
theorem genericStructStalkEquiv_stalkSpecializes {x : X}
    (m : (Stacks.Divisors.structureModule X).presheaf.stalk x) :
    genericStructStalkEquiv X
        ((Stacks.Divisors.structureModule X).presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes (Set.mem_univ x)) m)
      = X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x))
          (structStalkLinearEquiv X x m) :=
  structStalkLinearEquiv_stalkSpecializes X _ m

/-! ### Invertible modules are reflexive -/

/-- **An invertible `𝒪_X`-module on an integral locally Noetherian scheme is reflexive.** Its
stalks are free of rank one, by `Stacks.Divisors.isTrivializedNear_of_isInvertible`, hence
reflexive as modules over the local rings; that is condition (2) of Tag 0AY5. -/
theorem isReflexive_of_isInvertible (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] : IsReflexive L := by
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := ‹_›
  have : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  refine (isReflexive_iff_stalk_isReflexive_or_depth_two X L).2 fun x => Or.inl ?_
  obtain ⟨W, hxW, e, hb⟩ := Stacks.Divisors.isTrivializedNear_of_isInvertible L x
  exact Module.equiv (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (X.presheaf.stalk x) (L.presheaf.stalk x)
      (L.presheaf.germ W x hxW e)) (hb x hxW))

/-! ### Extending a map of generic stalks -/

/-- **Tag 0AY7 for a reflexive target.** On a normal locally Noetherian integral scheme, a
linear map `T : G_η → F_η` of generic stalks between coherent modules with `F` reflexive is the
generic stalk map of a morphism `G ⟶ F`, as soon as `T` carries the image of `G_x` into the
image of `F_x` at every point `x` whose local ring has dimension one.

The extension criterion `AlgebraicGeometry.exists_lift_toReflexiveHull_iff_codimension_one`
produces a map into the reflexive hull of `F`, and reflexivity of `F` makes the canonical map
`F ⟶ F^∨∨` an isomorphism. -/
theorem exists_hom_of_mapsTo_stalkSpecializes [IsNormal X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G] (hF : IsReflexive F)
    (T : G.presheaf.stalk (genericPoint X) →ₗ[X.functionField]
      F.presheaf.stalk (genericPoint X))
    (hT : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      Set.MapsTo T
        (Set.range (G.presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes (Set.mem_univ x))))
        (Set.range (F.presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes (Set.mem_univ x))))) :
    ∃ f : G ⟶ F, ∀ m, stalkMapOfHom f (genericPoint X) m = T m := by
  obtain ⟨e, he⟩ := (exists_lift_toReflexiveHull_iff_codimension_one X F G T).2 hT
  have hiso : IsIso (toReflexiveHull F).1 := hF
  refine ⟨e ≫ inv (toReflexiveHull F).1, fun m => ?_⟩
  have step1 : stalkMapOfHom (e ≫ inv (toReflexiveHull F).1) (genericPoint X) m
      = stalkMapOfHom (inv (toReflexiveHull F).1) (genericPoint X)
          (stalkMapOfHom e (genericPoint X) m) :=
    stalkMapOfHom_comp_apply e (inv (toReflexiveHull F).1) (genericPoint X) m
  have step2 : stalkMapOfHom (inv (toReflexiveHull F).1) (genericPoint X)
        (stalkMapOfHom e (genericPoint X) m)
      = stalkMapOfHom (inv (toReflexiveHull F).1) (genericPoint X)
          (stalkMapOfHom (toReflexiveHull F).1 (genericPoint X) (T m)) :=
    congrArg _ (he m)
  have step3 : stalkMapOfHom (inv (toReflexiveHull F).1) (genericPoint X)
        (stalkMapOfHom (toReflexiveHull F).1 (genericPoint X) (T m))
      = stalkMapOfHom ((toReflexiveHull F).1 ≫ inv (toReflexiveHull F).1) (genericPoint X)
          (T m) :=
    (stalkMapOfHom_comp_apply (toReflexiveHull F).1 (inv (toReflexiveHull F).1)
      (genericPoint X) (T m)).symm
  have step4 : stalkMapOfHom ((toReflexiveHull F).1 ≫ inv (toReflexiveHull F).1)
      (genericPoint X) (T m) = T m := by
    rw [IsIso.hom_inv_id]
    exact stalkMapOfHom_id_apply F (genericPoint X) (T m)
  exact ((step1.trans step2).trans step3).trans step4

/-- **A morphism into an invertible module is determined by its generic stalk map.** An
invertible module is reflexive, hence torsion free by Tag 0AY2, and a local section of a torsion
free module whose germ at the generic point vanishes is zero — that is the equivalence of Tag
0AXR. -/
theorem hom_ext_of_genericStalk {F G : X.Modules}
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property G] (f g : F ⟶ G)
    (h : ∀ m, stalkMapOfHom f (genericPoint X) m = stalkMapOfHom g (genericPoint X) m) :
    f = g := by
  have hqc : G.IsQuasicoherent := isQuasicoherent_of_isInvertible G
  have hG : IsTorsionFree G := isTorsionFree_of_isReflexive G (isReflexive_of_isInvertible X G)
  refine Scheme.Modules.hom_ext f g fun U => ConcreteCategory.hom_ext _ _ fun s => ?_
  refine sub_eq_zero.mp (hG U (Scheme.Modules.Hom.app f U s - Scheme.Modules.Hom.app g U s) ?_)
  by_cases hU : Nonempty U
  · have : Nonempty U := hU
    have hη : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
    have hgerm : ∀ k : F ⟶ G,
        G.presheaf.germ U (genericPoint X) hη (Scheme.Modules.Hom.app k U s) =
          stalkMapOfHom k (genericPoint X)
            (F.presheaf.germ U (genericPoint X) hη s) :=
      fun k => (stalkMapOfHom_germ k (genericPoint X) U hη s).symm
    have hgen : G.presheaf.germ U (genericPoint X) hη
        (Scheme.Modules.Hom.app f U s - Scheme.Modules.Hom.app g U s) = 0 := by
      rw [map_sub, hgerm f, hgerm g, h, sub_self]
    exact ((torsion_section_tfae X G U
      (Scheme.Modules.Hom.app f U s - Scheme.Modules.Hom.app g U s)).out 3 2).mp hgen
  · exact fun x hx => absurd (⟨⟨x, hx⟩⟩ : Nonempty U) hU

/-! ### The normalized generic vector at a codimension-one point -/

variable (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

-- An invertible module is quasi-coherent; registered locally as an instance so that the generic
-- value of a meromorphic section, which is read through the comparison isomorphism of Tag 01X5
-- part (2) and therefore needs quasi-coherence, is available from invertibility alone.
attribute [local instance] isQuasicoherent_of_isInvertible

omit [IsLocallyNoetherian X] in
/-- **A nonzero element of the generic stalk of an invertible module is a stalk basis.** The
generic stalk is free of rank one over the function field, so any nonzero element generates
it. -/
theorem isStalkBasis_genericPoint_of_ne_zero {v : L.presheaf.stalk (genericPoint X)}
    (hv : v ≠ 0) : Stacks.Divisors.IsStalkBasis L (genericPoint X) v := by
  obtain ⟨e, hbe⟩ := exists_isStalkBasis_genericPoint X L
  obtain ⟨b, hb⟩ := hbe.surjective v
  replace hb : b • e = v := hb
  have hb0 : b ≠ 0 := fun h0 => hv (by rw [← hb, h0, zero_smul])
  exact hb ▸ hbe.smul_of_isUnit (isUnit_iff_ne_zero.mpr hb0)

/-- **The normalization step.** Let `s` be a regular meromorphic section of an invertible module
`L` on a normal locally Noetherian integral scheme, let `Z` be a prime divisor with generic
point `ξ`, and let `c` be a nonzero element of the function field whose order of vanishing at
`ξ` is the order of vanishing of `s` along `Z`. Then `c⁻¹ · s_η` is the image of a generator of
`L_ξ` scaled by the image of a *unit* of `𝒪_{X, ξ}`; in particular it generates the image of
`L_ξ` in the generic stalk.

The coordinate `a` of `s` against a generator `m` of `L_ξ` has `ord_ξ(a)` equal to the order of
vanishing of `s`, by Tag 02SF, so `c⁻¹ a` has order of vanishing zero at `ξ` and is therefore
the image of a unit, by
`Stacks.AlgebraicGeometry.UnitsNormalProper.exists_isUnit_of_ord_eq_zero`. -/
theorem exists_isUnit_smul_stalkSpecializes_eq [IsNormal X] (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) (c : X.functionField) (hc : c ≠ 0)
    (Z : PrimeDivisor X)
    (hord : orderOfVanishingMeromorphic X L s hs Z = X.ord c Z.genericPoint) :
    ∃ m : L.presheaf.stalk Z.genericPoint,
      Submodule.span (X.presheaf.stalk Z.genericPoint) {m} = ⊤ ∧
        ∃ u : X.presheaf.stalk Z.genericPoint, IsUnit u ∧
          c⁻¹ • meromorphicGenericValue X L s =
            algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField u •
              L.presheaf.stalkSpecializes
                ((genericPoint_spec X).specializes (Set.mem_univ Z.genericPoint)) m := by
  obtain ⟨m, hm, a, ha⟩ := (orderOfVanishingMeromorphicData X L s hs Z).2.1
  have hval : meromorphicGenericValue X L s =
      a • L.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes (Set.mem_univ Z.genericPoint)) m :=
    meromorphicGenericValue_eq X L s _ ha
  have ha0 : a ≠ 0 := fun h0 =>
    meromorphicGenericValue_ne_zero X L s hs (by rw [hval, h0, zero_smul])
  have horda : orderOfVanishingMeromorphic X L s hs Z = X.ord a Z.genericPoint :=
    (orderOfVanishingMeromorphicData X L s hs Z).2.2 m hm a ha
  have hinv0 : c⁻¹ * a ≠ 0 := mul_ne_zero (inv_ne_zero hc) ha0
  have hsum : X.ord c Z.genericPoint + X.ord (c⁻¹ * a) Z.genericPoint =
      X.ord a Z.genericPoint := by
    rw [← X.ord_mul hc hinv0, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hord0 : X.ord (c⁻¹ * a) Z.genericPoint = 0 := by
    have hca : X.ord a Z.genericPoint = X.ord c Z.genericPoint := horda ▸ hord
    omega
  obtain ⟨u, hu, hue⟩ := Stacks.AlgebraicGeometry.UnitsNormalProper.exists_isUnit_of_ord_eq_zero
    Z.coheight_genericPoint hinv0 hord0
  refine ⟨m, hm, u, hu, ?_⟩
  rw [hue, hval, smul_smul]

/-! ### Triviality of an invertible module with vanishing divisor class -/

/-- **Stacks 0BE8, the content.** An invertible `𝒪_X`-module on a normal locally Noetherian
integral scheme whose Weil divisor class vanishes is isomorphic to `𝒪_X`.

A regular meromorphic section `s` exists by Tag 02OZ, and the hypothesis says that its Weil
divisor is the principal divisor of an invertible rational function `f`. The normalized generic
vector `v = f⁻¹ · s_η` is a stalk basis of `L_η`, and
`AlgebraicGeometry.exists_isUnit_smul_stalkSpecializes_eq` says that it generates the image of
`L_x` at every codimension-one point `x`. So multiplication by `v` and the coordinate against
`v` respect the codimension-one lattices in both directions, and
`AlgebraicGeometry.exists_hom_of_mapsTo_stalkSpecializes` turns them into morphisms of
`𝒪_X`-modules, mutually inverse because they are so on generic stalks. -/
theorem nonempty_iso_unit_of_weilDivisorClassOfInvertibleSheaf_eq_zero [IsNormal X]
    (h : weilDivisorClassOfInvertibleSheaf X L = 0) :
    Nonempty (L ≅ Stacks.Divisors.structureModule X) := by
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := ‹_›
  have hLcoh : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  have hOcoh : (Stacks.Divisors.structureModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral X L
  obtain ⟨f, hf⟩ := (mk_eq_zero_iff X (weilDivisorOfMeromorphicSection X L s hs)).1
    ((weilDivisorClassOfInvertibleSheaf_eq X L s hs).symm.trans h)
  set c : X.functionField := (Stacks.Chow.rationalFunctionsEquivFunctionField X).val
    (f : Stacks.Chow.rationalFunctions X) with hcdef
  have hc : c ≠ 0 :=
    (f.isUnit.map (Stacks.Chow.rationalFunctionsEquivFunctionField X).val.toRingHom).ne_zero
  have hordZ : ∀ Z : PrimeDivisor X,
      orderOfVanishingMeromorphic X L s hs Z = X.ord c Z.genericPoint := fun Z => by
    rw [← weilDivisorOfMeromorphicSection_apply X L s hs Z, ← hf, principalDivisor_apply]
  -- the normalized generic vector, and the stalk basis of the generic stalk it provides
  set v : L.presheaf.stalk (genericPoint X) := c⁻¹ • meromorphicGenericValue X L s with hvdef
  have hv : v ≠ 0 := fun h0 => meromorphicGenericValue_ne_zero X L s hs
    ((smul_eq_zero.mp h0).resolve_left (inv_ne_zero hc))
  set E : X.functionField ≃ₗ[X.functionField] L.presheaf.stalk (genericPoint X) :=
    LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton X.functionField (L.presheaf.stalk (genericPoint X)) v)
      (isStalkBasis_genericPoint_of_ne_zero X L hv) with hEdef
  have hE (z : X.functionField) : E z = z • v := rfl
  -- at a codimension-one point the normalized vector is a unit multiple of a generator
  have hgen : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      ∃ m : L.presheaf.stalk x, Submodule.span (X.presheaf.stalk x) {m} = ⊤ ∧
        ∃ u : X.presheaf.stalk x, IsUnit u ∧
          v = algebraMap (X.presheaf.stalk x) X.functionField u •
            L.presheaf.stalkSpecializes
              ((genericPoint_spec X).specializes (Set.mem_univ x)) m := by
    intro x hdim
    have hx : coheight x = 1 := by
      rw [ringKrullDim_stalk_eq_coheight] at hdim
      exact WithBot.coe_injective hdim
    obtain ⟨Z, rfl⟩ : ∃ Z : PrimeDivisor X, Z.genericPoint = x :=
      ⟨PrimeDivisor.ofCoheightOne x hx, PrimeDivisor.genericPoint_ofCoheightOne x hx⟩
    exact exists_isUnit_smul_stalkSpecializes_eq X L s hs c hc Z (hordZ Z)
  -- multiplication by `v` carries the local ring at a codimension-one point into the stalk
  have hSrange : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      ∀ r : X.presheaf.stalk x,
        X.presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes (Set.mem_univ x)) r • v ∈
          Set.range (L.presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes (Set.mem_univ x))) := by
    intro x hdim r
    obtain ⟨m, -, u, -, hvu⟩ := hgen x hdim
    refine ⟨(r * u) • m, ?_⟩
    rw [Stacks.ModuleStalkSpecialization.stalkSpecializes_smul, hvu,
      ← algebraMap_functionField_eq_stalkSpecializes,
      ← algebraMap_functionField_eq_stalkSpecializes, map_mul, smul_smul]
  -- the coordinate against `v` carries the stalk into the local ring
  have hTrange : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      ∀ n : L.presheaf.stalk x,
        E.symm (L.presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes (Set.mem_univ x)) n) ∈
          Set.range (X.presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes (Set.mem_univ x))) := by
    intro x hdim n
    obtain ⟨m, hm, u, hu, hvu⟩ := hgen x hdim
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hm ▸ Submodule.mem_top (x := n))
    refine ⟨r * w, ?_⟩
    refine (E.symm_apply_eq.mpr ?_).symm
    rw [← algebraMap_functionField_eq_stalkSpecializes, hE, hvu, smul_smul, ← map_mul, mul_assoc,
      mul_comm w u, hw, mul_one, algebraMap_functionField_eq_stalkSpecializes,
      ← Stacks.ModuleStalkSpecialization.stalkSpecializes_smul, hr]
  -- the two morphisms of modules, and the two composites
  obtain ⟨p, hp⟩ := exists_hom_of_mapsTo_stalkSpecializes X (Stacks.Divisors.structureModule X) L
    (isReflexive_of_isInvertible X (Stacks.Divisors.structureModule X))
    ((genericStructStalkEquiv X).symm.toLinearMap.comp E.symm.toLinearMap) (by
      rintro x hdim - ⟨n, rfl⟩
      obtain ⟨t, ht⟩ := hTrange x hdim n
      refine ⟨(structStalkLinearEquiv X x).symm t, (genericStructStalkEquiv X).injective ?_⟩
      refine (genericStructStalkEquiv_stalkSpecializes X _).trans ?_
      rw [LinearEquiv.apply_symm_apply]
      exact ht.trans ((genericStructStalkEquiv X).apply_symm_apply _).symm)
  obtain ⟨q, hq⟩ := exists_hom_of_mapsTo_stalkSpecializes X L (Stacks.Divisors.structureModule X)
    (isReflexive_of_isInvertible X L)
    (E.toLinearMap.comp (genericStructStalkEquiv X).toLinearMap) (by
      rintro x hdim - ⟨n, rfl⟩
      have hcompat : (E.toLinearMap.comp (genericStructStalkEquiv X).toLinearMap)
            ((Stacks.Divisors.structureModule X).presheaf.stalkSpecializes
              ((genericPoint_spec X).specializes (Set.mem_univ x)) n)
          = X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x))
              (structStalkLinearEquiv X x n) • v :=
        (congrArg E (genericStructStalkEquiv_stalkSpecializes X n)).trans (hE _)
      exact Set.mem_of_eq_of_mem hcompat (hSrange x hdim (structStalkLinearEquiv X x n)))
  refine ⟨⟨p, q, hom_ext_of_genericStalk X _ _ fun m => ?_,
    hom_ext_of_genericStalk X _ _ fun m => ?_⟩⟩
  · rw [stalkMapOfHom_comp_apply, hp, hq, stalkMapOfHom_id_apply]
    change E (genericStructStalkEquiv X ((genericStructStalkEquiv X).symm (E.symm m))) = m
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · rw [stalkMapOfHom_comp_apply, hq, hp, stalkMapOfHom_id_apply]
    change (genericStructStalkEquiv X).symm (E.symm (E (genericStructStalkEquiv X m))) = m
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-! ### Injectivity of the first Chern class -/

/-- **Stacks 0BE8.** On a normal locally Noetherian integral scheme the first Chern class
`Pic(X) → Cl(X)` of Tag 0BE7 is injective.

The map is a group homomorphism, so it is enough that a Picard class in its kernel vanishes.
Such a class is the Picard class of an invertible module `L`, whose image is the Weil divisor
class of `L`, and
`AlgebraicGeometry.nonempty_iso_unit_of_weilDivisorClassOfInvertibleSheaf_eq_zero` then makes
`L` isomorphic to `𝒪_X`, which is triviality of the Picard class. -/
@[stacks 0BE8, ega "IV 21.6.10" "(i), integral case", sga "2 XI 3.8" "partial"]
theorem picardToWeilDivisorClassGroup_injective [IsNormal X] :
    Function.Injective (picardToWeilDivisorClassGroup X) := by
  intro cx cy hxy
  refine sub_eq_zero.mp ?_
  obtain ⟨L, hL, hLc⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.sheaf.obj
    X.ringCatSheaf.property (cx - cy)
  have hLinv : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry _ _ _
  have hzero : picardToWeilDivisorClassGroup X (cx - cy) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hker : weilDivisorClassOfInvertibleSheaf X L = 0 := by
    rw [← weilDivisorClassOfPicardClass_picardClass X L, hLc]
    exact hzero
  rw [← hLc]
  exact (Stacks.SheafOfModules.picardClass_eq_zero_iff X.sheaf.obj X.ringCatSheaf.property L
    hL).mpr (nonempty_iso_unit_of_weilDivisorClassOfInvertibleSheaf_eq_zero X L hker)

end AlgebraicGeometry

end

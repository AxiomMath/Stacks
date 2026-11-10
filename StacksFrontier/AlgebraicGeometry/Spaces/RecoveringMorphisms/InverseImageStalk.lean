module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PolynomialTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartRingMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.StalkReflectsUnits
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.ToposHomUnitsSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheafStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks of an inverse image along a morphism of small étale ringed topoi

Let `(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of the small étale ringed
topoi of two algebraic spaces and let `x̄` be a geometric point of `X`, with its point `Φ` of the
small étale site of `X` (Stacks 04K0).  The functor `F ↦ (g⁻¹F)_x̄` from sheaves on `Y_étale` to
sets is left exact and preserves colimits: it is the inverse image of the point `g ∘ x̄` of the
topos of `Y`.  This file defines the stalk `R = (g⁻¹𝒪_Y)_x̄` as a commutative ring, the stalk
`𝒪_{X,x̄}`, the local map `R ⟶ 𝒪_{X,x̄}` induced by `g♯`, and, for an étale chart `V` of `Y` and
an element `σ` of the stalk of `g⁻¹h_V`, the ring map `Γ(V, 𝒪_V) ⟶ R`, `b ↦ (g⁻¹b)(σ)`.

## Main definitions

* `AlgebraicGeometry.Space.invStalk`: the functor `F ↦ (g⁻¹F)_x̄`.
* `AlgebraicGeometry.Space.invStalkRing`: the ring `R = (g⁻¹𝒪_Y)_x̄`.
* `AlgebraicGeometry.Space.structureStalk`: the ring `𝒪_{X,x̄}`.
* `AlgebraicGeometry.Space.invStalkRingHom`: the map `R ⟶ 𝒪_{X,x̄}` induced by `g♯`.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
  (x : GeometricPoint B S hS X.1)

attribute [local instance] smallEtaleTopology_subcanonical

/-- The small étale site of an algebraic space is locally `u`-small. -/
instance (Z : AlgebraicSpaces B S hS) : LocallySmall.{u} (SmallEtale B S hS Z.1) :=
  inferInstance

/-- The point of the small étale site of `X` determined by the geometric point `x̄`. -/
abbrev sitePt : (SmallEtale.topology B S hS X.1).Point.{u} := etaleSitePoint B S hS X.1 x X.2

/-- **The stalk of an inverse image**, `F ↦ (g⁻¹F)_x̄`. -/
abbrev invStalk : Sheaf (SmallEtale.topology B S hS Y.1) (Type u) ⥤ Type u :=
  g.toToposHom.inverseImage ⋙ (sitePt x).sheafFiber

/-- The functor `F ↦ (g⁻¹F)_x̄` preserves finite limits. -/
instance : PreservesFiniteLimits (invStalk g x) := by
  have := g.toToposHom.preservesFiniteLimits
  exact comp_preservesFiniteLimits _ _

/-- The functor `F ↦ (g⁻¹F)_x̄` preserves `u`-small colimits. -/
instance : PreservesColimitsOfSize.{u, u} (invStalk g x) := by
  have : PreservesColimitsOfSize.{u, u} g.toToposHom.inverseImage :=
    g.toToposHom.adj.leftAdjoint_preservesColimits
  exact comp_preservesColimits _ _

/-- The ring `R = (g⁻¹𝒪_Y)_x̄`, the stalk at `x̄` of the inverse image of the structure sheaf of
`Y`, with the ring structure transported along the left exact functor `F ↦ (g⁻¹F)_x̄`. -/
abbrev invStalkRing : Type u := (invStalk g x).obj (Sheaf.ringSheaf (ringO Y))

/-- The sections of the sheaf of rings underlying the structure sheaf commute. -/
theorem ringO_mul_comm (Z : AlgebraicSpaces B S hS) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (a b : (Sheaf.sectionsFunctor _ W).obj (Sheaf.ringSheaf (ringO Z))) : a * b = b * a :=
  mul_comm (G := ToType ((smallEtaleRingedTopos B S hS Z).O.obj.obj W)) a b

/-- The commutative ring structure on `R = (g⁻¹𝒪_Y)_x̄`. -/
instance : CommRing (invStalkRing g x) :=
  Sheaf.ringObjCommRing (R := ringO Y) (ringO_mul_comm Y) (invStalk g x)

/-- The ring `𝒪_{X,x̄}`, the stalk at `x̄` of the structure sheaf of `X`, with the ring structure
transported along the stalk functor. -/
abbrev structureStalk : Type u := (sitePt x).sheafFiber.obj (Sheaf.ringSheaf (ringO X))

/-- The commutative ring structure on `𝒪_{X,x̄}`. -/
instance : CommRing (structureStalk x) :=
  Sheaf.ringObjCommRing (R := ringO X) (ringO_mul_comm X) (sitePt x).sheafFiber

/-! ### The structure map is a map of internal rings -/

section Internal

open Sheaf

/-- Binary products of sheaves of sets on a small étale site, supplied directly: under Lean
v4.35.0 instance search for them times out in this file. -/
local instance (priority := high) hasBinaryProduct_sheaf_inverseImageStalk
    {Z : AlgebraicSpaces B S hS} (A A' : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)) :
    HasBinaryProduct A A' :=
  (inferInstance : HasBinaryProducts (Sheaf (SmallEtale.topology B S hS Z.1) (Type u))).has_limit _

/-- The functor `g⁻¹` followed by sections over `W`. -/
abbrev invSections (W : SmallEtale B S hS X.1) :
    Sheaf (SmallEtale.topology B S hS Y.1) (Type u) ⥤ Type u :=
  g.toToposHom.inverseImage ⋙ sectionsFunctor (SmallEtale.topology B S hS X.1) (op W)

/-- The functor `g⁻¹` followed by sections over `W` preserves finite products. -/
instance (W : SmallEtale B S hS X.1) : PreservesFiniteProducts (invSections g W) := by
  have := g.toToposHom.preservesFiniteLimits
  exact comp_preservesFiniteProducts _ _

/-- The inverse-image form `g⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map, as a map of the underlying sheaves
of sets of the sheaves of rings. -/
abbrev fSharpRing :
    g.toToposHom.inverseImage.obj (ringSheaf (ringO Y)) ⟶ ringSheaf (ringO X) :=
  g.fSharpSet

/-- On sections, `fSharpRing` is the component of the inverse-image structure map of sheaves of
commutative rings. -/
theorem sectionsFunctor_map_fSharpRing (W : SmallEtale B S hS X.1)
    (a : (invSections g W).obj (ringSheaf (ringO Y))) :
    (sectionsFunctor _ (op W)).map (fSharpRing g) a =
      (g.fSharpInverseImage.hom.app (op W)).hom a := by
  change g.fSharpSet.hom.app (op W) a = _
  rw [← g.forgetRing_map_fSharpInverseImage_eq_fSharpSet]
  rfl

/-- On sections, `fSharpRing` is additive for the ring structure of the sections of `g⁻¹𝒪_Y`,
which is the one transported along `g⁻¹` followed by sections. -/
theorem fSharpRing_add (W : SmallEtale B S hS X.1)
    (a b : (invSections g W).obj (ringSheaf (ringO Y))) :
    (sectionsFunctor _ (op W)).map (fSharpRing g) (ringAddObj (ringO Y) (invSections g W) a b) =
      (sectionsFunctor _ (op W)).map (fSharpRing g) a +
        (sectionsFunctor _ (op W)).map (fSharpRing g) b := by
  rw [sectionsFunctor_map_fSharpRing, sectionsFunctor_map_fSharpRing,
    sectionsFunctor_map_fSharpRing]
  exact (g.fSharpInverseImage.hom.app (op W)).hom.map_add a b

/-- On sections, `fSharpRing` is multiplicative. -/
theorem fSharpRing_mul (W : SmallEtale B S hS X.1)
    (a b : (invSections g W).obj (ringSheaf (ringO Y))) :
    (sectionsFunctor _ (op W)).map (fSharpRing g) (ringMulObj (ringO Y) (invSections g W) a b) =
      (sectionsFunctor _ (op W)).map (fSharpRing g) a *
        (sectionsFunctor _ (op W)).map (fSharpRing g) b := by
  rw [sectionsFunctor_map_fSharpRing, sectionsFunctor_map_fSharpRing,
    sectionsFunctor_map_fSharpRing]
  exact (g.fSharpInverseImage.hom.app (op W)).hom.map_mul a b

/-- On sections, `fSharpRing` preserves `1`. -/
theorem fSharpRing_one (W : SmallEtale B S hS X.1) :
    (sectionsFunctor _ (op W)).map (fSharpRing g) (ringOneObj (ringO Y) (invSections g W)) =
      1 := by
  rw [sectionsFunctor_map_fSharpRing]
  exact (g.fSharpInverseImage.hom.app (op W)).hom.map_one

/-- On sections, `fSharpRing` preserves `0`. -/
theorem fSharpRing_zero (W : SmallEtale B S hS X.1) :
    (sectionsFunctor _ (op W)).map (fSharpRing g) (ringZeroObj (ringO Y) (invSections g W)) =
      0 := by
  rw [sectionsFunctor_map_fSharpRing]
  exact (g.fSharpInverseImage.hom.app (op W)).hom.map_zero

/-- To show `g⁻¹(m) ≫ g♯ = (g♯ × g♯) ≫ m'` for binary operations `m`, `m'`, it suffices to check
it on pairs of sections of `g⁻¹𝒪_Y`. -/
private theorem inverseImage_map_comp_fSharpRing_of_prodObjMk
    (m : ringSheaf (ringO Y) ⨯ ringSheaf (ringO Y) ⟶ ringSheaf (ringO Y))
    (m' : ringSheaf (ringO X) ⨯ ringSheaf (ringO X) ⟶ ringSheaf (ringO X))
    (h : ∀ (W : SmallEtale B S hS X.1) (a b : (invSections g W).obj (ringSheaf (ringO Y))),
      (sectionsFunctor _ (op W)).map (fSharpRing g) ((invSections g W).map m
        (Functor.prodObjMk a b)) = (sectionsFunctor _ (op W)).map m' (Functor.prodObjMk
          ((sectionsFunctor _ (op W)).map (fSharpRing g) a)
          ((sectionsFunctor _ (op W)).map (fSharpRing g) b))) :
    g.toToposHom.inverseImage.map m ≫ fSharpRing g =
      prodComparison g.toToposHom.inverseImage _ _ ≫
        prod.map (fSharpRing g) (fSharpRing g) ≫ m' := by
  refine hom_ext_sections fun W z ↦ ?_
  obtain ⟨W⟩ := W
  rw [Functor.map_comp_apply, Functor.map_comp_apply, Functor.map_comp_apply,
    Functor.map_prodComparison_apply, Functor.map_prodMap_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk]
  have := h W ((invSections g W).map prod.fst z) ((invSections g W).map prod.snd z)
  rw [Functor.prodObjMk_map_fst_map_snd] at this
  exact this

/-- **`g♯` is a morphism of internal rings, addition.** As maps of sheaves of sets on `X`,
`g⁻¹(+) ≫ g♯ = (g♯ × g♯) ≫ (+)`, through the comparison `g⁻¹(𝒪_Y × 𝒪_Y) ≅ g⁻¹𝒪_Y × g⁻¹𝒪_Y`. -/
theorem inverseImage_map_ringAddHom_comp_fSharpRing :
    g.toToposHom.inverseImage.map (ringAddHom (ringO Y)) ≫ fSharpRing g =
      prodComparison g.toToposHom.inverseImage _ _ ≫
        prod.map (fSharpRing g) (fSharpRing g) ≫ ringAddHom (ringO X) :=
  inverseImage_map_comp_fSharpRing_of_prodObjMk g _ _ fun W a b ↦
    (fSharpRing_add g W a b).trans (sectionsFunctor_map_ringAddHom _ _ _ _).symm

/-- **`g♯` is a morphism of internal rings, multiplication.** -/
theorem inverseImage_map_ringMulHom_comp_fSharpRing :
    g.toToposHom.inverseImage.map (ringMulHom (ringO Y)) ≫ fSharpRing g =
      prodComparison g.toToposHom.inverseImage _ _ ≫
        prod.map (fSharpRing g) (fSharpRing g) ≫ ringMulHom (ringO X) :=
  inverseImage_map_comp_fSharpRing_of_prodObjMk g _ _ fun W a b ↦
    (fSharpRing_mul g W a b).trans (sectionsFunctor_map_ringMulHom _ _ _ _).symm

/-- To show `g⁻¹(m) ≫ g♯ = m'` for nullary operations `m`, `m'`, it suffices to check it on the
unique section of `g⁻¹ 1`. -/
private theorem inverseImage_map_comp_fSharpRing_of_default
    (m : ⊤_ _ ⟶ ringSheaf (ringO Y)) (m' : ⊤_ _ ⟶ ringSheaf (ringO X))
    (h : ∀ W : SmallEtale B S hS X.1,
      (sectionsFunctor _ (op W)).map (fSharpRing g) ((invSections g W).map m default) =
        (sectionsFunctor _ (op W)).map m' default) :
    g.toToposHom.inverseImage.map m ≫ fSharpRing g = terminal.from _ ≫ m' := by
  refine hom_ext_sections fun W z ↦ ?_
  obtain ⟨W⟩ := W
  rw [Functor.map_comp_apply, Functor.map_comp_apply]
  refine Eq.trans ?_ ((h W).trans (congrArg _ (Subsingleton.elim (α :=
    (sectionsFunctor _ (op W)).obj (⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u)))
      default _)))
  exact congrArg _ (congrArg _ (Subsingleton.elim (α :=
    (invSections g W).obj (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u))) z default))

/-- **`g♯` is a morphism of internal rings, unit.** -/
theorem inverseImage_map_ringOneHom_comp_fSharpRing :
    g.toToposHom.inverseImage.map (ringOneHom (ringO Y)) ≫ fSharpRing g =
      terminal.from _ ≫ ringOneHom (ringO X) :=
  inverseImage_map_comp_fSharpRing_of_default g _ _ fun W ↦
    (fSharpRing_one g W).trans (sectionsFunctor_map_ringOneHom _ _ _).symm

/-- **`g♯` is a morphism of internal rings, zero.** -/
theorem inverseImage_map_ringZeroHom_comp_fSharpRing :
    g.toToposHom.inverseImage.map (ringZeroHom (ringO Y)) ≫ fSharpRing g =
      terminal.from _ ≫ ringZeroHom (ringO X) :=
  inverseImage_map_comp_fSharpRing_of_default g _ _ fun W ↦
    (fSharpRing_zero g W).trans (sectionsFunctor_map_ringZeroHom _ _ _).symm

end Internal

/-! ### The ring maps -/

section RingMaps

open Sheaf

/-- For `f : A' ⟶ A` and `m : g⁻¹A ⟶ E`, the stalk of `m` applied to `(g⁻¹f)_x̄ z` is the stalk of
`g⁻¹f ≫ m` applied to `z`. -/
theorem sheafFiber_map_invStalk_map {A A' : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)}
    {E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (f : A' ⟶ A)
    (m : g.toToposHom.inverseImage.obj A ⟶ E) (z : (invStalk g x).obj A') :
    (sitePt x).sheafFiber.map m ((invStalk g x).map f z) =
      (sitePt x).sheafFiber.map (g.toToposHom.inverseImage.map f ≫ m) z := by
  rw [Functor.map_comp, types_comp_apply]
  rfl

/-- **The map of stalks `R ⟶ 𝒪_{X,x̄}` induced by `g♯`**, a ring map for the transported ring
structures. -/
def invStalkRingHom : invStalkRing g x →+* structureStalk x where
  toFun := (sitePt x).sheafFiber.map (fSharpRing g)
  map_one' := by
    change (sitePt x).sheafFiber.map (fSharpRing g)
      ((invStalk g x).map (ringOneHom (ringO Y)) default) = _
    rw [sheafFiber_map_invStalk_map, inverseImage_map_ringOneHom_comp_fSharpRing,
      Functor.map_comp, types_comp_apply, Functor.map_terminalFrom_apply]
    rfl
  map_mul' a b := by
    change (sitePt x).sheafFiber.map (fSharpRing g)
      ((invStalk g x).map (ringMulHom (ringO Y)) (Functor.prodObjMk a b)) =
      (sitePt x).sheafFiber.map (ringMulHom (ringO X)) (Functor.prodObjMk
        ((sitePt x).sheafFiber.map (fSharpRing g) a) ((sitePt x).sheafFiber.map (fSharpRing g) b))
    rw [sheafFiber_map_invStalk_map, inverseImage_map_ringMulHom_comp_fSharpRing,
      Functor.map_comp, Functor.map_comp, types_comp_apply, types_comp_apply,
      Functor.map_prodComparison_apply, Functor.map_prodMap_apply, Functor.map_fst_prodObjMk,
      Functor.map_snd_prodObjMk, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]
  map_zero' := by
    change (sitePt x).sheafFiber.map (fSharpRing g)
      ((invStalk g x).map (ringZeroHom (ringO Y)) default) = _
    rw [sheafFiber_map_invStalk_map, inverseImage_map_ringZeroHom_comp_fSharpRing,
      Functor.map_comp, types_comp_apply, Functor.map_terminalFrom_apply]
    rfl
  map_add' a b := by
    change (sitePt x).sheafFiber.map (fSharpRing g)
      ((invStalk g x).map (ringAddHom (ringO Y)) (Functor.prodObjMk a b)) =
      (sitePt x).sheafFiber.map (ringAddHom (ringO X)) (Functor.prodObjMk
        ((sitePt x).sheafFiber.map (fSharpRing g) a) ((sitePt x).sheafFiber.map (fSharpRing g) b))
    rw [sheafFiber_map_invStalk_map, inverseImage_map_ringAddHom_comp_fSharpRing,
      Functor.map_comp, Functor.map_comp, types_comp_apply, types_comp_apply,
      Functor.map_prodComparison_apply, Functor.map_prodMap_apply, Functor.map_fst_prodObjMk,
      Functor.map_snd_prodObjMk, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

/-- The map `R ⟶ 𝒪_{X,x̄}` is the stalk at `x̄` of `g♯`. -/
@[simp]
theorem invStalkRingHom_apply (a : invStalkRing g x) :
    invStalkRingHom g x a = (sitePt x).sheafFiber.map (fSharpRing g) a :=
  rfl

/-- **The map of stalks `R ⟶ 𝒪_{X,x̄}` is a local ring map** when `(g, g♯)` is a morphism of
locally ringed topoi. -/
@[sga "4 IV 13.9" "(i), special case"]
theorem isLocalHom_invStalkRingHom (hg : g.IsLocallyRinged) :
    IsLocalHom (invStalkRingHom g x) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨t, ht⟩ := hg
  obtain ⟨u, hu⟩ := (RingedTopos.isUnit_iff_exists_map_unitsIncl (smallEtaleRingedTopos B S hS X)
    (sitePt x).sheafFiber _).1 ha
  have hpb := (ht.map (sitePt x).sheafFiber)
  obtain ⟨v, hv, -⟩ := (Types.isPullback_iff _ _ _ _).1 hpb.flip |>.2.2 a u (by
    exact hu.symm)
  exact (RingedTopos.isUnit_iff_exists_map_unitsIncl (smallEtaleRingedTopos B S hS Y)
    (invStalk g x) a).2 ⟨v, hv⟩

/-- The ring `R = (g⁻¹𝒪_Y)_x̄` is nontrivial whenever `𝒪_{X,x̄}` is. -/
theorem nontrivial_invStalkRing [Nontrivial (structureStalk x)] : Nontrivial (invStalkRing g x) :=
  (invStalkRingHom g x).domain_nontrivial

/-- The structure stalk `𝒪_{X,x̄}` is a nontrivial ring. -/
instance nontrivial_structureStalk : Nontrivial (structureStalk x) := by
  have hloc : IsLocalRing (((sitePt x).sheafFiber (A := CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X).O) :=
    isLocalRing_presheafFiber_structurePresheaf B S hS X.1 x X.2
  exact (RingedTopos.stalkRingMulEquiv (sitePt x) (smallEtaleRingedTopos B S hS X).O).symm
    |>.injective.nontrivial

/-- The ring `R = (g⁻¹𝒪_Y)_x̄` is nontrivial. -/
instance : Nontrivial (invStalkRing g x) := nontrivial_invStalkRing g x

/-- A regular function on an étale chart `V` of `Y`, read as a map `h_V ⟶ 𝒪_Y`. -/
def secToHom (V : SmallEtale B S hS Y.1) (b : Γ(chartSch V, ⊤)) :
    (SmallEtale.topology B S hS Y.1).yoneda.obj V ⟶ ringSheaf (ringO Y) :=
  (SmallEtale.topology B S hS Y.1).yonedaEquiv.symm
    (show (ringSheaf (ringO Y)).obj.obj (op V) from b)

/-- On sections over `W`, the map `h_V ⟶ 𝒪_Y` attached to `b` sends `φ : W ⟶ V` to the
restriction of `b` along `φ`. -/
theorem sectionsFunctor_map_secToHom (V : SmallEtale B S hS Y.1) (b : Γ(chartSch V, ⊤))
    (W : SmallEtale B S hS Y.1)
    (φ : (sectionsFunctor _ (op W)).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V)) :
    (sectionsFunctor _ (op W)).map (secToHom V b) φ =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (show W ⟶ V from φ).hom.left).op b :=
  GrothendieckTopology.yonedaEquiv_symm_app_apply _ _ _ _

/-- `secToHom` is multiplicative. -/
theorem secToHom_mul (V : SmallEtale B S hS Y.1) (a b : Γ(chartSch V, ⊤)) :
    secToHom V (a * b) = secToHom V a * secToHom V b := by
  refine hom_ext_sections fun W φ ↦ ?_
  obtain ⟨W⟩ := W
  rw [hom_mul_eq, Functor.map_comp, types_comp_apply, Functor.map_lift_apply,
    sectionsFunctor_map_ringMulHom, sectionsFunctor_map_secToHom, sectionsFunctor_map_secToHom,
    sectionsFunctor_map_secToHom]
  exact map_mul _ a b

/-- `secToHom` is additive. -/
theorem secToHom_add (V : SmallEtale B S hS Y.1) (a b : Γ(chartSch V, ⊤)) :
    secToHom V (a + b) = secToHom V a + secToHom V b := by
  refine hom_ext_sections fun W φ ↦ ?_
  obtain ⟨W⟩ := W
  rw [hom_add_eq, Functor.map_comp, types_comp_apply, Functor.map_lift_apply,
    sectionsFunctor_map_ringAddHom, sectionsFunctor_map_secToHom, sectionsFunctor_map_secToHom,
    sectionsFunctor_map_secToHom]
  exact map_add _ a b

/-- `secToHom` sends `1` to `1`. -/
theorem secToHom_one (V : SmallEtale B S hS Y.1) : secToHom V 1 = 1 := by
  refine hom_ext_sections fun W φ ↦ ?_
  obtain ⟨W⟩ := W
  rw [hom_one_eq, Functor.map_comp, types_comp_apply, sectionsFunctor_map_ringOneHom,
    sectionsFunctor_map_secToHom]
  exact map_one _

/-- `secToHom` sends `0` to `0`. -/
theorem secToHom_zero (V : SmallEtale B S hS Y.1) : secToHom V 0 = 0 := by
  refine hom_ext_sections fun W φ ↦ ?_
  obtain ⟨W⟩ := W
  rw [hom_ringZero_eq, Functor.map_comp, types_comp_apply, sectionsFunctor_map_ringZeroHom,
    sectionsFunctor_map_secToHom]
  exact map_zero _

/-- Regular functions on `V` are maps `h_V ⟶ 𝒪_Y`; for the pointwise ring structure on the
latter this identification is a ring map. -/
def yonedaRingHom (V : SmallEtale B S hS Y.1) :
    Γ(chartSch V, ⊤) →+* ((SmallEtale.topology B S hS Y.1).yoneda.obj V ⟶ ringSheaf (ringO Y))
    where
  toFun := secToHom V
  map_one' := secToHom_one V
  map_mul' := secToHom_mul V
  map_zero' := secToHom_zero V
  map_add' := secToHom_add V

/-- **The ring map `Γ(V, 𝒪_V) ⟶ R` attached to an element `σ` of the stalk of `g⁻¹h_V`**:
`b ↦ (g⁻¹b)(σ)`, where `b` is read as a map `h_V ⟶ 𝒪_Y`. -/
def stalkCoordRingHom (V : SmallEtale B S hS Y.1)
    (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V)) :
    Γ(chartSch V, ⊤) →+* invStalkRing g x :=
  (evalRingHom (invStalk g x) σ).comp (yonedaRingHom V)

/-- The ring map `Γ(V, 𝒪_V) ⟶ R` sends `b` to `(g⁻¹b)_x̄ σ`. -/
@[simp]
theorem stalkCoordRingHom_apply (V : SmallEtale B S hS Y.1)
    (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V))
    (b : Γ(chartSch V, ⊤)) :
    stalkCoordRingHom g x V σ b = (invStalk g x).map (secToHom V b) σ :=
  rfl

end RingMaps

end AlgebraicGeometry.Space

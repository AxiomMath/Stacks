module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingPicard
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingUnitsSequence
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Local
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Sections
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.NativeLongExactSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.PicardGroupAndFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingTwoPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exact sequence of Picard groups of a glueing of two rational points

Let `k` be an algebraically closed field and let `f : X' ⟶ X` glue the two distinct rational
points `a` and `b` of an algebraic `k`-scheme `X'` to the point `x` of `X`, in the sense of
[Stacks, Tag 0C1J]. [Stacks, Tag 0C1M] records the exact sequence

`k^* ⟶ Pic(X) ⟶ Pic(X') ⟶ 0`,

whose second map is pullback along `f` and whose first map sends a scalar to the invertible
`𝒪_X`-module obtained by glueing the fibres of `𝒪_{X'}` at `a` and `b` with that ratio. This
file constructs the first map, identifies its kernel, and proves it injective when `X'` is
proper and the two points lie on the same connected component.

The first map is the connecting homomorphism of the short exact sequence of sheaves of units

`1 ⟶ 𝒪_X^* ⟶ f_*𝒪_{X'}^* ⟶ (k^*)_x ⟶ 1`

of [Stacks, Tag 0C1J], read through the five-term low-degree cohomology sequence over the whole
space and through the identification of `H¹(X, 𝒪_X^*)` with the Picard group of
[Stacks, Tag 09NU]. Surjectivity of pullback — the other end of the sequence, which is
[Stacks, Tag 0C0T] — is
`Stacks.GluePicard.surjective_schemePullbackClassHom`.

## Main definitions

* `Stacks.GluePicard.picardGluingHom` — **the gluing homomorphism** `k^* ⟶ Pic(X)`.
* `Stacks.GluePicard.picardModelAddEquiv` — the translation between the two models of the
  Picard group of a ringed space.
* `Stacks.GluePicard.h1UnitsAddEquivOfScheme` — first cohomology of the sheaf of units, read
  over `Stacks.Picard.ofScheme`.
* `Stacks.GluePicard.UnitsSequence` and `Stacks.GluePicard.connectingHom` — the short exact
  sequence of sheaves of units and its connecting map.

## Main results

* `Stacks.GluePicard.exists_globalUnit_unitRatioAt_eq_of_picardGluingHom_eq_zero` — a scalar
  killed by the gluing homomorphism is the ratio of the two values of a unit on the whole of
  `X'`; equivalently, the kernel of the gluing homomorphism is the image of
  `𝒪^*(X') ⟶ k^*`.
* `Stacks.GluePicard.injective_picardGluingHom_of_connectedComponents_eq` — **the gluing
  homomorphism is injective** when `X'` is proper over `k` and the two glued points lie on the
  same connected component of `X'`.

## Implementation notes

The Picard group is `Stacks.Picard.ofScheme`, the units of the skeleton of the category of
invertible sheaves of modules on a scheme. The identification of `H¹` of the sheaf of units
with the Picard group, `Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup`, is stated over
the *small* model of Tag 01CX — the skeleton shrunk into the universe of the sections, which is
the model in which the comparison with first cohomology is statable at all. The two models are
translated by `picardModelAddEquiv`: both are the image of one and the same skeleton under a
chosen bijection, so the translation is the composite of the two bijections, and it sends the
class of an invertible module to the class of the same module.

The low-degree cohomology sequence is
`Stacks.Cohomology.AbelianColimit.H'longExactSequence_exact` and its pieces, instantiated at
the open `⊤` and the degrees `0` and `1`. It is applied with a bare type carrying a topology
rather than with a `TopCat`, since the `HasExt` instance it needs is not found at the
`TopCat.Sheaf` spelling; `(X : Type u)` for a scheme `X` is that bare type, and the sheaves and
opens need no translation. Degree-zero native cohomology
is identified with sections through `Functor.rightDerivedZeroIsoSelf`, legitimate because
sections over an open are left exact, and degree-one native cohomology with right-derived
sections, which is the spelling `h1UnitsAddEquivPicardGroup` is in.

Every spelling of an object is kept fixed across the file, and the maps are composed in the
category rather than applied to elements wherever possible. The reason is that
`(abSections ⊤).obj S.complex.X₃` and the sections of the skyscraper sheaf over `⊤` are the
same type only after unfolding, so an element whose type carries the second spelling is
invisible to the rewriting that the first spelling needs; `sequenceTopIso` exists to name the
comparison once, with its source in the first spelling, and `UnitsSequence.sequenceTopIso_map_g`
restates the description of the quotient map on sections there.

Injectivity is read off the kernel description. What it needs is that a function on a connected
component of a scheme proper over `k` cannot separate two rational points, and that is proved
here without reducedness and without algebraic closedness: the component is open — the space of
a scheme of finite type over a field is locally Noetherian, hence locally connected — and
closed, so its inclusion is a closed immersion and the component is again proper over `k`;
its ring of functions is therefore integral over `k`, has no idempotents besides `0` and `1`
because the component is connected, and is consequently a local ring. Evaluation at a rational
point is a surjective ring homomorphism onto `k`, since the value of a constant is that
constant, so its kernel is maximal, hence *the* maximal ideal; a section therefore differs from
the constant given by its value at one point by an element killed by the evaluation at the
other.

The short exact sequence of units is produced by Tag 0C1J as an existential statement, so it is
chosen once by `unitsSequence` and carried as a bundle; both of its maps are pinned down on
sections, which is what makes the connecting map the map of the tag rather than the connecting
map of some exact sequence with the same terms.

## References

* [Stacks Project, Tag 0C1M](https://stacks.math.columbia.edu/tag/0C1M)
* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.GluePicard

open Stacks.Cohomology.Generators (unitsSheaf)
open Stacks.Cohomology.AbelianColimit (abSections H'functor H'δ
  nonempty_H'functor_iso_rightDerived)
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules (IsInvertible isInvertible_tensorSheaf)
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)

/-! ### The two models of the Picard group -/

/-- The small model of the Picard group of a ringed space. -/
abbrev smallPicard (R : RingedSpace.{u, u}) : Type u :=
  Stacks.SheafOfModules.Picard.PicardGroup R.presheaf (structureIsSheaf R)

/-- Translation between the two models. -/
def picardModelEquiv (R : RingedSpace.{u, u}) :
    Stacks.Picard.ofRingedSpace R ≃ smallPicard R :=
  ((Stacks.Picard.picardGroupData R.presheaf (structureIsSheaf R)).classEquiv).symm.trans
    (Stacks.SheafOfModules.Picard.picardGroupData R.presheaf (structureIsSheaf R)).classEquiv

/-- The translation sends a class to the class of the same module. -/
theorem picardModelEquiv_classOf (R : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf R.presheaf (structureIsSheaf R)))
    (hL : IsInvertible R.presheaf (structureIsSheaf R) L) :
    picardModelEquiv R (Stacks.SheafOfModules.picardClass R.presheaf (structureIsSheaf R) L hL) =
      Stacks.SheafOfModules.Picard.classOf R.presheaf (structureIsSheaf R) L hL := by
  show (Stacks.SheafOfModules.Picard.picardGroupData R.presheaf
      (structureIsSheaf R)).classEquiv
      ((Stacks.Picard.picardGroupData R.presheaf (structureIsSheaf R)).classEquiv.symm
        ((Stacks.Picard.picardGroupData R.presheaf (structureIsSheaf R)).classEquiv
          (toSkeleton (C := Stacks.SheafOfModules.InvertibleModules R.presheaf (structureIsSheaf R))
            ⟨L, hL⟩))) = _
  rw [Equiv.symm_apply_apply]

/-- Every Picard class is the class of an invertible module. -/
theorem exists_classOf (R : RingedSpace.{u, u}) (x : Stacks.Picard.ofRingedSpace R) :
    ∃ (L : SheafOfModules.{u} (structureSheaf R.presheaf (structureIsSheaf R)))
      (hL : IsInvertible R.presheaf (structureIsSheaf R) L),
      Stacks.SheafOfModules.picardClass R.presheaf (structureIsSheaf R) L hL = x :=
  ⟨_, _, Stacks.Picard.classOf_picardRepresentative R x⟩

/-- Translation between the two models, as an isomorphism of abelian groups. -/
def picardModelAddEquiv (R : RingedSpace.{u, u}) :
    Stacks.Picard.ofRingedSpace R ≃+ smallPicard R :=
  { picardModelEquiv R with
    map_add' := by
      intro x y
      obtain ⟨L, hL, rfl⟩ := exists_classOf R x
      obtain ⟨N, hN, rfl⟩ := exists_classOf R y
      have hLN := @isInvertible_tensorSheaf _ _ _ R.presheaf (structureIsSheaf R) _ _ _ _ hL hN
      change picardModelEquiv R _ = picardModelEquiv R _ + picardModelEquiv R _
      -- Only the two classes of `L` and `N` are reachable by rewriting. The class of the tensor
      -- product sheaf is not: its argument is seated at `Stacks.SheafOfModules.Tensor.ringSheaf`
      -- while `L` and `N` are seated at `TensorSheafification.structureSheaf`, so the motive a
      -- rewrite would abstract is not type-correct at reducible transparency. The remaining step
      -- is therefore taken in term mode, as in `Stacks.SheafOfModules.picardGroupShrinkAddEquiv`.
      rw [Stacks.SheafOfModules.picardClass_tensorSheaf _ _ L N hL hN hLN,
        picardModelEquiv_classOf, picardModelEquiv_classOf]
      exact (picardModelEquiv_classOf R _ hLN).trans
        (Stacks.SheafOfModules.Picard.classOf_tensor _ _ L N hL hN hLN).symm }

/-- The translation of abelian groups sends a class to the class of the same module. -/
theorem picardModelAddEquiv_classOf (R : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf R.presheaf (structureIsSheaf R)))
    (hL : IsInvertible R.presheaf (structureIsSheaf R) L) :
    picardModelAddEquiv R (Stacks.SheafOfModules.picardClass R.presheaf (structureIsSheaf R) L hL) =
      Stacks.SheafOfModules.Picard.classOf R.presheaf (structureIsSheaf R) L hL :=
  picardModelEquiv_classOf R L hL

/-! ### Native cohomology in degrees zero and one -/

/-- Degree-zero native cohomology over the whole space is sections. -/
def h0Iso (T : Type u) [TopologicalSpace T]
    [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}] :
    H'functor (X := T) ⊤ 0 ≅ abSections (X := T) ⊤ :=
  (nonempty_H'functor_iso_rightDerived (X := T) ⊤ 0).some.trans
    (abSections (X := T) ⊤).rightDerivedZeroIsoSelf

/-- Degree-one native cohomology over the whole space is first right-derived sections. -/
def h1Iso (T : Type u) [TopologicalSpace T]
    [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}] :
    H'functor (X := T) ⊤ 1 ≅ (abSections (X := T) ⊤).rightDerived 1 :=
  (nonempty_H'functor_iso_rightDerived (X := T) ⊤ 1).some

/-- The identification of first cohomology of the units sheaf with the Picard group of
[Stacks, Tag 09NU], read at the spelling of the structure presheaf of a ringed space. -/
@[ega "0 5.4.7" "special case", ega "IV 21.3.6" "special case", sga "1 XI 6.4"]
def h1UnitsAddEquivSmallPicard (X : Scheme.{u}) :
    ((abSections (X := (X : Type u)) ⊤).rightDerived 1).obj (unitsSheaf X.toRingedSpace) ≃+
      smallPicard X.toRingedSpace :=
  Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup X.toRingedSpace

/-- **First cohomology of the sheaf of units is the Picard group**, over the Picard group
`Stacks.Picard.ofScheme`. -/
@[ega "IV 21.3.6" "special case"]
def h1UnitsAddEquivOfScheme (X : Scheme.{u}) :
    (H'functor (X := (X : Type u)) ⊤ 1).obj (unitsSheaf X.toRingedSpace) ≃+
      Stacks.Picard.ofScheme X :=
  (((h1Iso (X : Type u)).app (unitsSheaf X.toRingedSpace)).addCommGroupIsoToAddEquiv.trans
      (h1UnitsAddEquivSmallPicard X)).trans (picardModelAddEquiv X.toRingedSpace).symm

/-! ### The short exact sequence of units, chosen once -/

open Stacks.GlueSquishUnits (gluedPoint skyscraperUnitsSheaf skyscraperUnitsEval unitRatioAt)

/-- The two glued points have the same image. -/
theorem comp_eq_comp {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) : a ≫ f = b ≫ f :=
  h.2.2.2.2.2.2.2.2.fst

/-- The short exact sequence of sheaves of units of a glueing of two rational points, with both
of its maps pinned down on sections. -/
structure UnitsSequence {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X') where
  /-- Pullback of units along `f`. -/
  phi : unitsSheaf X.toRingedSpace ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj (unitsSheaf X'.toRingedSpace)
  /-- The ratio of the two values of a unit. -/
  psi : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj (unitsSheaf X'.toRingedSpace) ⟶
    skyscraperUnitsSheaf (k := k) X (gluedPoint f a)
  /-- The two maps compose to zero. -/
  zero : phi ≫ psi = 0
  /-- The resulting short complex is short exact. -/
  shortExact : (ShortComplex.mk phi psi zero).ShortExact
  /-- The first map is pullback of units on sections. -/
  phi_app : ∀ (U : X.Opens) (s : Γ(X, U)ˣ),
    phi.hom.app (op U) (Additive.ofMul s) =
      Additive.ofMul (Units.map (f.app U).hom.toMonoidHom s)
  /-- The second map is the ratio of the two values on sections. -/
  psi_app : ∀ (U : X.Opens) (hz : gluedPoint f a ∈ U)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U) (s : Γ(X', f ⁻¹ᵁ U)ˣ),
    skyscraperUnitsEval X (gluedPoint f a) hz (psi.hom.app (op U) (Additive.ofMul s)) =
      Additive.ofMul (unitRatioAt a b (f ⁻¹ᵁ U) ha hb s)

/-- The chosen short exact sequence of sheaves of units. -/
def unitsSequence {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) : UnitsSequence f a b :=
  let hex := Stacks.GlueSquishUnits.isShortExact_units_of_isGlueingTwoPoints f a b h
    (comp_eq_comp f a b h)
  { phi := hex.choose
    psi := hex.choose_spec.choose
    zero := hex.choose_spec.choose_spec.choose
    shortExact := hex.choose_spec.choose_spec.choose_spec.1
    phi_app := hex.choose_spec.choose_spec.choose_spec.2.1
    psi_app := hex.choose_spec.choose_spec.choose_spec.2.2 }

/-- The short complex underlying the chosen sequence, at the spelling of the site of opens. -/
def UnitsSequence.complex {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) :
    ShortComplex (Sheaf (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u}) :=
  ShortComplex.mk S.phi S.psi S.zero

/-- That short complex is short exact. -/
theorem UnitsSequence.complex_shortExact {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) :
    S.complex.ShortExact :=
  S.shortExact

/-- Evaluation of a section of the skyscraper sheaf of units is an isomorphism. -/
instance isIso_skyscraperUnitsEval {k : Type u} [Field k] (X : Scheme.{u}) (x : X)
    {U : X.Opens} (hx : x ∈ U) : IsIso (skyscraperUnitsEval (k := k) X x hx) := by
  classical
  exact inferInstanceAs (IsIso (eqToHom (Stacks.GlueSquishUnits.skyscraperPresheaf_obj_eq x
    (AddCommGrpCat.of (Additive kˣ)) hx)))

/-! ### The gluing homomorphism -/

/-- The sections of the third sheaf of the sequence over the whole space are the fibre `k^*`.
The source is spelled through the sections functor, which is the spelling the long exact
sequence works in. -/
def sequenceTopIso {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) :
    (abSections (X := (X : Type u)) ⊤).obj S.complex.X₃ ≅ AddCommGrpCat.of (Additive kˣ) := by
  classical
  exact eqToIso (Stacks.GlueSquishUnits.skyscraperPresheaf_obj_eq (gluedPoint f a)
    (AddCommGrpCat.of (Additive kˣ)) (Opens.mem_top _))

/-- **The second map of the sequence on sections over the whole space is the ratio of the two
values of a unit**, in the spelling of the sections functor. -/
theorem UnitsSequence.sequenceTopIso_map_g {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ (⊤ : X.Opens))
    (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ (⊤ : X.Opens))
    (t : (abSections (X := (X : Type u)) ⊤).obj S.complex.X₂) :
    (sequenceTopIso S).hom ((abSections (X := (X : Type u)) ⊤).map S.complex.g t) =
      Additive.ofMul (unitRatioAt a b (f ⁻¹ᵁ (⊤ : X.Opens)) ha hb (Additive.toMul t)) :=
  S.psi_app (⊤ : X.Opens) (Opens.mem_top _) ha hb (Additive.toMul t)

/-- The connecting map of the units sequence, read on `k^*` through the sections of the
skyscraper sheaf over the whole space and on cohomology through the identification of
degree-zero native cohomology with sections. -/
def connectingHom {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) :
    AddCommGrpCat.of (Additive kˣ) ⟶
      (H'functor (X := (X : Type u)) ⊤ 1).obj (unitsSheaf X.toRingedSpace) :=
  (sequenceTopIso S).inv ≫ (h0Iso (X : Type u)).inv.app S.complex.X₃ ≫
    H'δ S.complex_shortExact ⊤ (zero_add 1)

/-- The connecting map, on an element of `k^*`. -/
theorem connectingHom_apply {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) (c : Additive kˣ) :
    AddCommGrpCat.Hom.hom' (connectingHom S) c =
      H'δ S.complex_shortExact (⊤ : Opens (X : Type u)) (zero_add 1)
        ((h0Iso (X : Type u)).inv.app S.complex.X₃ ((sequenceTopIso S).inv c)) :=
  rfl

/-- **Stacks Project, Tag 0C1M.** The gluing homomorphism `k^* ⟶ Pic(X)`. -/
@[stacks 0C1M "the gluing homomorphism"]
def picardGluingHom {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) :
    Additive kˣ →+ Stacks.Picard.ofScheme X where
  toFun c := h1UnitsAddEquivOfScheme X
    (AddCommGrpCat.Hom.hom' (connectingHom (unitsSequence f a b h)) c)
  map_zero' := by rw [map_zero, map_zero]
  map_add' c d := by rw [map_add, map_add]

/-- The gluing homomorphism is the connecting map followed by the identification of first
cohomology with the Picard group. -/
theorem picardGluingHom_apply {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) (c : Additive kˣ) :
    picardGluingHom f a b h c =
      h1UnitsAddEquivOfScheme X
        (AddCommGrpCat.Hom.hom' (connectingHom (unitsSequence f a b h)) c) :=
  rfl

/-- **Exactness of the five-term low-degree sequence at `k^*`**: a scalar killed by the
connecting map of the units sequence is the ratio of the two values of a unit on the whole
of `X'`. -/
theorem exists_unit_unitRatioAt_eq_of_connectingHom_eq_zero {k : Type u} [Field k]
    [IsAlgClosed k] {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) (c : Additive kˣ)
    (h0 : AddCommGrpCat.Hom.hom' (connectingHom S) c = 0) :
    ∃ s : Γ(X', f ⁻¹ᵁ (⊤ : X.Opens))ˣ,
      unitRatioAt a b (f ⁻¹ᵁ (⊤ : X.Opens)) (Opens.mem_top _) (Opens.mem_top _) s =
        Additive.toMul c := by
  classical
  rw [connectingHom_apply] at h0
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1
    (Stacks.Cohomology.AbelianColimit.shortComplex_H'_exact₃ S.complex_shortExact
      (⊤ : Opens (X : Type u)) (zero_add 1)) _ h0
  have hy' : (H'functor (X := (X : Type u)) ⊤ 0).map S.complex.g y =
      (h0Iso (X : Type u)).inv.app S.complex.X₃ ((sequenceTopIso S).inv c) := hy
  have hnat : (h0Iso (X : Type u)).hom.app S.complex.X₃
        ((H'functor (X := (X : Type u)) ⊤ 0).map S.complex.g y) =
      (abSections (X := (X : Type u)) ⊤).map S.complex.g
        ((h0Iso (X : Type u)).hom.app S.complex.X₂ y) := by
    have hn := ConcreteCategory.congr_hom
      ((h0Iso (X : Type u)).hom.naturality S.complex.g) y
    rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
  have hval : (abSections (X := (X : Type u)) ⊤).map S.complex.g
        ((h0Iso (X : Type u)).hom.app S.complex.X₂ y) = (sequenceTopIso S).inv c := by
    rw [← hnat, hy']
    simp
  have hkey := S.sequenceTopIso_map_g (Opens.mem_top _) (Opens.mem_top _)
    ((h0Iso (X : Type u)).hom.app S.complex.X₂ y)
  rw [hval] at hkey
  refine ⟨Additive.toMul ((h0Iso (X : Type u)).hom.app S.complex.X₂ y),
    Additive.ofMul.injective ?_⟩
  rw [← hkey]
  simp

/-- **A scalar killed by the gluing homomorphism is the ratio of the two values of a unit on
the whole of `X'`.** -/
theorem exists_globalUnit_unitRatioAt_eq_of_picardGluingHom_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) (c : Additive kˣ)
    (hc : picardGluingHom f a b h c = 0) :
    ∃ s : Γ(X', ⊤)ˣ,
      unitRatioAt a b ⊤ (Opens.mem_top _) (Opens.mem_top _) s = Additive.toMul c := by
  refine exists_unit_unitRatioAt_eq_of_connectingHom_eq_zero (unitsSequence f a b h) c ?_
  refine (h1UnitsAddEquivOfScheme X).injective ?_
  rw [← picardGluingHom_apply, hc, map_zero]

/-! ### The functions on a connected component of a proper scheme -/

/-- The constants of a scheme over `k`, restricted to an open, are the structure map of the
scheme followed by restriction. -/
private theorem constHom_eq {k : Type u} [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (U : Y.Opens) (hU : U ≤ (Y ↘ Spec (.of k)) ⁻¹ᵁ ⊤) :
    constHom Y U hU =
      ((((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) ≫
        Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)).hom := by
  show (((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).app ⊤ ≫
    Y.presheaf.map (homOfLE hU).op)).hom = _
  rw [← Category.assoc]
  rfl

/-- Sections over `U ⊆ Y` of the structure sheaf of `Y`, read through the identification of `U`
with the global sections of `U` as a scheme in its own right, are computed by the restriction
map. -/
private theorem ι_appTop_comp_topIso_hom' {Y : Scheme.{u}} (U : Y.Opens) :
    U.ι.appTop ≫ U.topIso.hom = Y.presheaf.map (homOfLE le_top).op :=
  (Y.presheaf.map_comp (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op
      (eqToIso U.ι_image_top.symm).op.hom).symm.trans
    (congrArg Y.presheaf.map (Subsingleton.elim _ _))

/-- **The constants of a connected component of a scheme proper over a field are an integral
ring extension.** The component is open and closed, hence a closed immersion into `Y`, hence
again proper over the base, and the functions on a scheme proper over a field are integral over
that field. -/
private theorem isIntegral_constHom_connectedComponentOpens {k : Type u} [Field k]
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    [LocallyConnectedSpace Y] (c : ConnectedComponents Y)
    (hU : Y.connectedComponentOpens c ≤ (Y ↘ Spec (.of k)) ⁻¹ᵁ ⊤) :
    (constHom Y (Y.connectedComponentOpens c) hU).IsIntegral := by
  have hci : IsClosedImmersion (Y.connectedComponentOpens c).ι :=
    ⟨⟨(Y.connectedComponentOpens c).ι.isOpenEmbedding.isEmbedding, by
      rw [(Y.connectedComponentOpens c).range_ι]
      exact Y.isClosed_connectedComponentOpens c⟩⟩
  have hpr : IsProper ((Y.connectedComponentOpens c).ι ≫ (Y ↘ Spec (.of k))) := inferInstance
  have heq : ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) ≫
      Y.presheaf.map (homOfLE (le_top (a := Y.connectedComponentOpens c))).op =
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((Y.connectedComponentOpens c).ι ≫ (Y ↘ Spec (.of k))).appTop) ≫
          (Y.connectedComponentOpens c).topIso.hom := by
    rw [← ι_appTop_comp_topIso_hom' (Y.connectedComponentOpens c),
      Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
  rw [constHom_eq, heq]
  refine RingHom.IsIntegral.trans _ _ ?_ ?_
  · exact Stacks.AlgebraicGeometry.ProperGeomConnected.isIntegral_toSpecΓ_algebraMap
      ((Y.connectedComponentOpens c).ι ≫ (Y ↘ Spec (.of k)))
  · exact RingHom.isIntegral_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Y.connectedComponentOpens c).topIso.hom).2

/-- **The functions on a connected open of a scheme over `k` which are integral over `k` form a
local ring.** A preconnected open carries no idempotent sections besides `0` and `1`, and a
nontrivial algebra integral over a field with only trivial idempotents is local. -/
private theorem isLocalRing_sections_of_isPreconnected {k : Type u} [Field k]
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] (U : Y.Opens)
    (hU : U ≤ (Y ↘ Spec (.of k)) ⁻¹ᵁ ⊤) (hint : (constHom Y U hU).IsIntegral)
    (hconn : _root_.IsPreconnected (U : Set Y)) (hne : Nontrivial Γ(Y, U)) :
    IsLocalRing Γ(Y, U) := by
  let : Algebra k Γ(Y, U) := (constHom Y U hU).toAlgebra
  have hia : Algebra.IsIntegral k Γ(Y, U) := ⟨fun x => by
    rw [_root_.IsIntegral, RingHom.algebraMap_toAlgebra]
    exact hint x⟩
  have := hne
  exact (Stacks.RingTheory.IntegralOverField.isLocalRing_and_krullDimLE_zero (K := k)
    (fun e he => Stacks.AlgebraicGeometry.ProperGeomConnected.isIdempotentElem_eq_zero_or_one
      hconn he)).2

/-- **Two rational points of an open whose functions form a local ring have the same value on
every section over that open.** Both evaluations are surjective ring homomorphisms onto `k`,
since the value of a constant is that constant, so both kernels are maximal, hence both are
*the* maximal ideal; a section therefore differs from the constant given by its value at the
first point by an element killed by the second evaluation too. -/
private theorem sectionAt_eq_of_isLocalRing {k : Type u} [Field k] {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] (U : Y.Opens) (hU : U ≤ (Y ↘ Spec (.of k)) ⁻¹ᵁ ⊤)
    (a b : Spec (.of k) ⟶ Y) (ha : a.IsOver (Spec (.of k))) (hb : b.IsOver (Spec (.of k)))
    (haU : a.base (IsLocalRing.closedPoint k) ∈ U)
    (hbU : b.base (IsLocalRing.closedPoint k) ∈ U) (hloc : IsLocalRing Γ(Y, U))
    (t : Γ(Y, U)) :
    AlgebraicGeometry.sectionAt a U haU t = AlgebraicGeometry.sectionAt b U hbU t := by
  have := hloc
  have hker : ∀ (p : Spec (.of k) ⟶ Y) (hp : p.IsOver (Spec (.of k)))
      (hpU : p.base (IsLocalRing.closedPoint k) ∈ U),
      RingHom.ker (sectionAtHom p U hpU) = IsLocalRing.maximalIdeal Γ(Y, U) := fun p hp hpU =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ fun c =>
      ⟨constHom Y U hU c, sectionAt_constHom p hp U hpU hU c⟩)
  have hkey : t - constHom Y U hU (AlgebraicGeometry.sectionAt a U haU t) ∈
      RingHom.ker (sectionAtHom a U haU) := by
    rw [RingHom.mem_ker, map_sub, sectionAtHom_apply, sectionAtHom_apply,
      sectionAt_constHom a ha U haU hU, sub_self]
  rw [hker a ha haU, ← hker b hb hbU, RingHom.mem_ker, map_sub, sectionAtHom_apply,
    sectionAtHom_apply, sectionAt_constHom b hb U hbU hU, sub_eq_zero] at hkey
  exact hkey.symm

/-- **Two rational points on the same connected component of a scheme proper over a field have
the same value on every global function.** The connected component is open, the space being
locally Noetherian, and closed, so it is proper over `k`; its ring of functions is therefore
integral over `k`, and being connected it has no idempotents besides `0` and `1`, hence is a
local ring. -/
private theorem sectionAt_eq_of_connectedComponents_eq {k : Type u} [Field k]
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    (a b : Spec (.of k) ⟶ Y) (ha : a.IsOver (Spec (.of k))) (hb : b.IsOver (Spec (.of k)))
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) =
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k)))
    (s : Γ(Y, ⊤)) :
    AlgebraicGeometry.sectionAt a ⊤ (Opens.mem_top _) s =
      AlgebraicGeometry.sectionAt b ⊤ (Opens.mem_top _) s := by
  classical
  have hlN : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have hlc : LocallyConnectedSpace Y :=
    (isLocallyNoetherianSpace_of_isLocallyNoetherian Y).locallyConnectedSpace Y
  set c := ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) with hc
  set U := Y.connectedComponentOpens c with hU
  have hUle : U ≤ (Y ↘ Spec (.of k)) ⁻¹ᵁ ⊤ := by simp
  have haU : a.base (IsLocalRing.closedPoint k) ∈ U := Y.mem_connectedComponentOpens.2 rfl
  have hbU : b.base (IsLocalRing.closedPoint k) ∈ U := Y.mem_connectedComponentOpens.2 hab.symm
  have hconn : _root_.IsPreconnected (U : Set Y) := by
    rw [hU, Y.coe_connectedComponentOpens, connectedComponents_preimage_singleton]
    exact isPreconnected_connectedComponent
  have hne : Nontrivial Γ(Y, U) := by
    refine ⟨0, 1, fun hcon => zero_ne_one (α := k) ?_⟩
    have hz := congrArg (sectionAtHom a U haU) hcon
    rwa [map_zero, map_one] at hz
  have hloc := isLocalRing_sections_of_isPreconnected U hUle
    (isIntegral_constHom_connectedComponentOpens _ hUle) hconn hne
  have hres := sectionAt_eq_of_isLocalRing U hUle a b ha hb haU hbU hloc
    (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
  rwa [sectionAt_map a (homOfLE le_top) haU s, sectionAt_map b (homOfLE le_top) hbU s] at hres

/-- **Two rational points on the same connected component of a scheme proper over a field have
the same value on every global function.**

This is the form other modules use: `Stacks.GluePicard.sectionAt_eq_of_connectedComponents_eq`
is private to this file. -/
alias sectionAt_eq_of_connectedComponents_eq' := sectionAt_eq_of_connectedComponents_eq

/-! ### Injectivity of the gluing homomorphism for a proper scheme -/

/-- **Stacks Project, Tag 0C1M.** The gluing homomorphism is injective when `X'` is proper and
the two glued points lie on the same connected component of `X'`: a scalar in its kernel is the
ratio of the two values of a unit on `X'`, and on a connected component of a proper scheme over
an algebraically closed field the two values of any function agree. -/
@[stacks 0C1M "injectivity if X' is proper and the two points lie on the same connected component"]
theorem injective_picardGluingHom_of_connectedComponents_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) [IsProper (X' ↘ Spec (.of k))]
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) =
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))) :
    Function.Injective (picardGluingHom f a b h) := by
  intro c d hcd
  have hzero : picardGluingHom f a b h (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  obtain ⟨s, hs⟩ :=
    exists_globalUnit_unitRatioAt_eq_of_picardGluingHom_eq_zero f a b h (c - d) hzero
  have hone : unitRatioAt a b ⊤ (Opens.mem_top _) (Opens.mem_top _) s = 1 :=
    (Stacks.GlueSquishUnits.unitRatioAt_eq_one_iff a b ⊤ (Opens.mem_top _)
      (Opens.mem_top _) s).2
      (sectionAt_eq_of_connectedComponents_eq a b h.1 h.2.1 hab (s : Γ(X', ⊤)))
  rw [hone] at hs
  refine sub_eq_zero.mp ?_
  simpa using congrArg Additive.ofMul hs.symm

end Stacks.GluePicard

end

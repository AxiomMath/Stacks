module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pushforward and pullback functors compose for ringed spaces

For morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, we have:

1. A canonical natural isomorphism `(g ∘ f)_* ≅ g_* ∘ f_*` of pushforward
   functors on sheaves of modules. (The Stacks Project states this as an
   *equality* of functors; in the categorical setting this is the canonical
   identity natural isomorphism.)

2. A canonical natural isomorphism `(g ∘ f)^* ≅ f^* ∘ g^*` of pullback
   functors on sheaves of modules.

## Main definitions

* `pushforwardComp`: the isomorphism `(g ∘ f)_* ≅ g_* ∘ f_*` (Stacks Tag 0097, part 1).
* `pullbackComp`: the isomorphism `(g ∘ f)^* ≅ f^* ∘ g^*` (Stacks Tag 0097, part 2).

## Implementation notes

Pushforward and pullback of sheaves of modules along morphisms of ringed spaces
are obtained from the generic `SheafOfModules.pushforward` /
`SheafOfModules.pullback` applied to the morphism of sheaves of rings induced
by the morphism of ringed spaces.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

/-- The underlying sheaf of rings (in `RingCat`) of a ringed space, obtained
by composing the structure sheaf of commutative rings with the forgetful
functor `CommRingCat ⥤ RingCat`. -/
@[ega "0 4.1.1"]
abbrev ringCatSheaf (X : RingedSpace.{u}) :
    TopCat.Sheaf RingCat.{u} (X : TopCat) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The morphism of sheaves of rings on `Y` induced by a morphism of ringed
spaces `f : X ⟶ Y`. -/
noncomputable def toRingCatSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ringCatSheaf Y ⟶
      ((Opens.map f.hom.base).sheafPushforwardContinuous _ _ _).obj
        (ringCatSheaf X) where
  hom := Functor.whiskerRight f.hom.c _

/-- The category of sheaves of modules over a ringed space. -/
@[ega "0 4.1.3" "special case",
  sga "2 I 1.7" "partial",
  sga "4 II 6.3.2" "special case",
  sga "4 II 6.7" "special case",
  sga "4 IV 11.1.2" "special case",
  sga "4 V 3.5" "special case",
  sga "4 V 6.13" "special case",
  sga "6 I 4.8" "partial",
  sga "6 II 2.0" "Mod for a ringed space",
  sga "6 II 2.3.2" "Mod(S), special case",
  sga "6 III 5.1" "special case"]
abbrev Modules (X : RingedSpace.{u}) : Type _ :=
  SheafOfModules.{u} (ringCatSheaf X)

/-- The pushforward functor on sheaves of modules induced by a morphism of
ringed spaces. -/
@[ega "0 12.2.1",
  ega "0 4.2.1",
  ega "II 1.1.1" "partial",
  sga "3 VIIA 1.1" "more general",
  sga "4 IV 11.2.2" "special case",
  sga "4 IV 13.2.1" "special case",
  sga "4 Vbis 1.3.6" "special case"]
noncomputable def pushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Modules X ⥤ Modules Y :=
  SheafOfModules.pushforward.{u} (toRingCatSheafHom f)

-- isDefEq transparency bump: infer F through ringCatSheaf defs
set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback functor on sheaves of modules induced by a morphism of
ringed spaces. It is left adjoint to the pushforward. -/
@[ega "0 4.3.1",
  ega "I 9.1.8" "more general",
  ega "III 1.4.15" "partial",
  ega "III 4.7.1" "more general",
  ega "IV 2.1.4" "more general",
  ega "IV 2.5.1",
  ega "IV 9.4.1" "more general",
  sga "3 I 4.6.1" "more general",
  sga "3 III 0.1.4" "more general",
  sga "4 IV 13.2.2" "special case",
  sga "4 Vbis 1.3.6" "special case",
  sga "4 XVII 4.1" "special case",
  sga "6 IV 2.6" "special case",
  sga "6 VI 2.3.1" "more general"]
noncomputable def pullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Modules Y ⥤ Modules X :=
  SheafOfModules.pullback.{u} (toRingCatSheafHom f)

-- isDefEq transparency bump: infer F through ringCatSheaf defs
set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback is left adjoint to the pushforward. -/
@[ega "0 4.4.3",
  ega "III 7.7.9" "more general",
  sga "3 I 4.6.4" "more general",
  sga "3 VIB 11.4" "Last equality of (†)",
  sga "4 IV 13.4" "special case",
  sga "4 IV 14.2" "partial",
  sga "4 Vbis 1.3.6" "adjunction φ* ⊣ φ_*",
  sga "6 VI 2.3.1" "more general"]
noncomputable def pullbackPushforwardAdjunction {X Y : RingedSpace.{u}}
    (f : X ⟶ Y) : pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction _

/-- Naturality of `toRingCatSheafHom` with respect to composition of morphisms
of ringed spaces. The structure morphism of a composite ringed-space morphism
factors as the structure morphism of `g` followed by the pushforward (along
`g.hom.base`) of the structure morphism of `f`. -/
@[ega "0 4.1.1" "partial"]
lemma toRingCatSheafHom_comp {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toRingCatSheafHom (f ≫ g) =
      toRingCatSheafHom g ≫
        ((Opens.map g.hom.base).sheafPushforwardContinuous
          RingCat.{u} _ _).map (toRingCatSheafHom f) := by
  apply (fullyFaithfulSheafToPresheaf _ _).map_injective
  ext U : 2
  rfl

/-- For composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, there
is a canonical natural isomorphism between the pushforward of the composite
and the composite of the pushforwards. -/
@[stacks 0097 "(1)", ega "0 4.2.6"]
noncomputable def pushforwardComp {X Y Z : RingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward (f ≫ g) ≅ pushforward f ⋙ pushforward g :=
  SheafOfModules.pushforwardCongr (toRingCatSheafHom_comp f g) ≪≫
    (SheafOfModules.pushforwardComp.{u}
      (toRingCatSheafHom g) (toRingCatSheafHom f)).symm

/-- For composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, there
is a canonical natural isomorphism between the pullback of the composite and
the composite of the pullbacks (in the reverse order). -/
@[stacks 0097 "(2)", ega "0 4.3.6"]
noncomputable def pullbackComp {X Y Z : RingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  Adjunction.leftAdjointUniq
    (pullbackPushforwardAdjunction (f ≫ g))
    (((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f)).ofNatIsoRight (pushforwardComp f g).symm)

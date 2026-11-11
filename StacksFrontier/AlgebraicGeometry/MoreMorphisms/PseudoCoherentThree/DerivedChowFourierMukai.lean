module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowLemma
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# The Fourier–Mukai transform attached to a derived Chow datum

Let `p : T ⟶ X` and `q : T ⟶ P` be two morphisms out of a scheme `T` — in the situation of
Chow's lemma in the derived category, `T = X ×_A ℙⁿ_A` and `p`, `q` are its two projections —
let `iZ : Z ⟶ T` be a closed subscheme with projections `b = iZ ≫ p` and `c = iZ ≫ q`, and let
`U ⊆ X` and `V ⊆ P` be opens such that `b` is an isomorphism over `U`, `c` is a closed immersion
over `V`, and `b ⁻¹ᵁ U = c ⁻¹ᵁ V`.  The morphism

`c ∘ (b|_U)⁻¹ : U ⟶ V`

is then a closed immersion, and it is of finite presentation as soon as `U` and `V` are of finite
presentation over the base.  This file constructs that morphism, proves those two properties, and
proves the comparison of [Stacks, Tag 0CSK]: for `K ∈ D(𝒪_X)` and `E ∈ D(𝒪_T)`,

`Rq_*(Lp^*K ⊗^𝐋 E)|_V ≅ R(c ∘ (b|_U)⁻¹)_*(K|_U)`.

## Main results

* `AlgebraicGeometry.chowDatumMorphism`: the morphism `c ∘ (b|_U)⁻¹ : U ⟶ V`.
* `AlgebraicGeometry.chowDatumGraphIso`: the isomorphism `W ≅ U` induced by `b|_U`, where
  `W = b ⁻¹ᵁ U = c ⁻¹ᵁ V` is read as the part of `Z` lying over the open `q ⁻¹ᵁ V` of `T`; its
  two factorization identities `chowDatumGraphIso_comp_chowDatumMorphism` and
  `chowDatumGraphIso_comp_ι` are the whole geometric input of the comparison.
* `AlgebraicGeometry.isClosedImmersion_chowDatumMorphism` and
  `AlgebraicGeometry.finitePresentation_chowDatumMorphism`: **the first assertion of
  [Stacks, Tag 0CSK]** — the morphism `U ⟶ V` is a finitely presented closed immersion.  Finite
  presentation is [Stacks, Tag 02FV] applied to `U ⟶ V ⟶ S`.
* `AlgebraicGeometry.DerivedChow.derivedPushforwardRestrictOpenIso`: **[Stacks, Tag 08FE]** for
  the standard derived direct image and the standard derived pullback, at an open of the target
  of a morphism of schemes.  This is the step of the source proof that "forming the total direct
  image commutes with localization".
* `AlgebraicGeometry.chowDatum_derivedPushforward_tensor_restrict_iso`: the chain of
  isomorphisms of the source proof of [Stacks, Tag 0CSK], with the two steps described below
  entering as arguments.

[Stacks, Tag 0CSK] itself, at the source's hypothesis `K ∈ D_QCoh(𝒪_X)` and with every clause
of its conclusion, is `AlgebraicGeometry.chowDatum_fourierMukai`, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/PseudoCoherentThree/DerivedChowFourierMukaiQCoh.lean`;
the derived comparison there is
`AlgebraicGeometry.chowDatum_derivedPushforward_tensor_restrict_iso_of_isDQCoh`, which supplies
both arguments of the chain below.

## The two steps taken as arguments

`AlgebraicGeometry.chowDatum_derivedPushforward_tensor_restrict_iso` is stated for an arbitrary
`K ∈ D(𝒪_X)`, and two steps of the source proof enter it as arguments; both are proved in the
library at the source's hypotheses, in `DerivedChowFourierMukaiQCoh`.

*The projection formula,* `hproj`.  The source's step 4 is [Stacks, Tag 08EU] at the closed
immersion `i : W ⟶ q ⁻¹ᵁ V`: `M ⊗^𝐋 Ri_*𝒪_W ≅ Ri_*(Li^*M)` with `M` the restriction of `Lp^*K`.
For `K ∈ D_QCoh(𝒪_X)` this is `AlgebraicGeometry.derivedProjectionFormulaUnitRightIso`, built
from `Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh` and the
commutativity and unit constraints of [Stacks, Tag 0FPT].

*Clause (5) of [Stacks, Tag 0CSJ] in its restricted form,* `hE`: `Lj^*E ≅ Ri_*𝒪_W[0]`.  From
clause (5) as [Stacks, Tag 0CSJ] states it this is
`AlgebraicGeometry.DerivedChow.pushforwardUnitRestrictIso`, which composes
[Stacks, Tag 08FE], the identification of direct image along an affine morphism with its derived
direct image, and the unit comparison
`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`.

The chain uses the quasi-coherence of `K` nowhere else, which is why it is stated for an
arbitrary `K`.

## Implementation notes

Everything derived is read in the ringed-space spelling of [Stacks, Tag 079W]:
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` and `derivedPullback`,
applied to `f.toLRSHom.toShHom`.  For a morphism of schemes this agrees with the scheme-level
functors on the nose — `Stacks.ProjectionFormula.modulePushforward_eq_schemePushforward` and its
pullback companion are `rfl` — and it is the spelling in which the composition isomorphisms of
[Stacks, Tag 0D5S] and [Stacks, Tag 0D5T], the monoidality of [Stacks, Tag 079U] and
[Stacks, Tag 08FE] are all stated.  `HasDerivedCategory.standard` is seated at a raised priority
for the same reason as in `DerivedChowLemma`: the import closure carries the locally small model
as a global instance, and the coherences of [Stacks, Tag 0D5S] are baked at the standard one.

The two morphism-equality transports are paid by dependent pattern matching
(`AlgebraicGeometry.DerivedChow.derivedPullbackFactorIso` and
`AlgebraicGeometry.DerivedChow.derivedPushforwardFactorIso`) rather than by `eqToIso`, so that
no `eqToHom` survives in the composite isomorphism.

## References

* [Stacks Project, Tag 0CSK](https://stacks.math.columbia.edu/tag/0CSK)
* [Stacks Project, Tag 0CSJ](https://stacks.math.columbia.edu/tag/0CSJ)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

namespace DerivedChow

/-- The morphism of ringed spaces underlying a morphism of schemes. -/
abbrev ofScheme {X Y : Scheme.{u}} (f : X ⟶ Y) : X.toRingedSpace ⟶ Y.toRingedSpace :=
  f.toLRSHom.toShHom

/-- Passing to underlying ringed spaces is functorial. -/
theorem ofScheme_comp {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W) :
    ofScheme f ≫ ofScheme g = ofScheme (f ≫ g) := rfl

/-- Passing to underlying ringed spaces preserves identities. -/
theorem ofScheme_id (X : Scheme.{u}) : ofScheme (𝟙 X) = 𝟙 X.toRingedSpace := rfl

/-- The inclusion of an open subscheme, as a morphism of ringed spaces, is an open immersion of
ringed spaces. -/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafedSpace.IsOpenImmersion (ofScheme f) :=
  inferInstanceAs (SheafedSpace.IsOpenImmersion f.toLRSHom.toShHom)

/-! ### [Stacks, Tag 08FE] for the standard derived functors

The library's [Stacks, Tag 08FE] is stated for arbitrary choices of right derived functors of
direct image and of pullback.  Along an open immersion the degreewise pullback is exact, so the
*left* derived pullback of [Stacks, Tag 079W] is also a right derived functor of it, and the
statement specializes to the standard four functors. -/

section OpenImmersion

variable {A B : RingedSpace.{u, u}} (i : A ⟶ B) [SheafedSpace.IsOpenImmersion i]

/-- Along an open immersion of ringed spaces the comparison `Li^* ∘ Q ⟶ Q ∘ i^*` is invertible:
degreewise pullback is exact, so it inverts the quasi-isomorphisms. -/
theorem isIso_derivedPullbackComparison_of_isOpenImmersion :
    IsIso (derivedPullbackComparison i) :=
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts (derivedPullback i)
    (derivedPullbackComparison i)
    (Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso
      (modulePullback i))

/-- The unit exhibiting `Li^*` as a *right* derived functor of degreewise pullback along an open
immersion: the inverse of the comparison of [Stacks, Tag 079W]. -/
def openImmersionPullbackUnit :
    (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Qh ⋙ derivedPullback i :=
  have := isIso_derivedPullbackComparison_of_isOpenImmersion i
  (asIso (derivedPullbackComparison i)).symm

/-- Along an open immersion the derived pullback of [Stacks, Tag 079W] is a right derived functor
of degreewise pullback. -/
theorem isRightDerivedFunctor_derivedPullback_of_isOpenImmersion :
    (derivedPullback i).IsRightDerivedFunctor (openImmersionPullbackUnit i).hom
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing B)) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing B)) (ComplexShape.up ℤ))
    (derivedPullback i) (openImmersionPullbackUnit i).symm

end OpenImmersion

/-- **[Stacks, Tag 08FE] for the standard derived functors.**  For a cartesian square of ringed
spaces whose two vertical edges `i` and `j` are open immersions, `Rf_* ⋙ Lj^* ≅ Li^* ⋙ Rg_*`. -/
def derivedPushforwardRestrictIsoOfStandard {X Y A B : RingedSpace.{u, u}} (f : X ⟶ Y) (i : A ⟶ X)
    (j : B ⟶ Y) (g : A ⟶ B) [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (h : IsPullback i g f j) :
    derivedPushforward f ⋙ derivedPullback j ≅ derivedPullback i ⋙ derivedPushforward g :=
  have := isRightDerivedFunctor_derivedPullback_of_isOpenImmersion i
  have := isRightDerivedFunctor_derivedPullback_of_isOpenImmersion j
  Stacks.Cohomology.derivedPushforwardRestrictIso f i j g h (derivedPushforward f)
    (derivedPushforward g) (derivedPullback i) (derivedPullback j)
    (derivedPushforwardUnit f) (derivedPushforwardUnit g)
    (openImmersionPullbackUnit i).hom (openImmersionPullbackUnit j).hom

section Square

variable {T P : Scheme.{u}} (q : T ⟶ P) (V : P.Opens)

/-- The square cutting a morphism of schemes down over an open of its target is cartesian. -/
theorem isPullback_morphismRestrict : IsPullback (q ∣_ V) (q ⁻¹ᵁ V).ι V.ι q :=
  IsOpenImmersion.isPullback (q ∣_ V) (q ⁻¹ᵁ V).ι V.ι q (morphismRestrict_ι q V).symm (by simp)

/-- **[Stacks, Tag 08FE] at an open of the target of a morphism of schemes.**  Restricting the
derived direct image along `q` to an open `V` of the target is the derived direct image along
`q ∣_ V` of the restriction to `q ⁻¹ᵁ V`: "forming the total direct image commutes with
localization". -/
@[stacks 08FE "for the standard derived direct image and derived pullback of [Stacks, Tag 079W], \
at the inclusion of an open subscheme of the target of a morphism of schemes"]
def derivedPushforwardRestrictOpenIso :
    derivedPushforward (ofScheme q) ⋙ derivedPullback (ofScheme V.ι) ≅
      derivedPullback (ofScheme (q ⁻¹ᵁ V).ι) ⋙ derivedPushforward (ofScheme (q ∣_ V)) :=
  derivedPushforwardRestrictIsoOfStandard (ofScheme q) (ofScheme (q ⁻¹ᵁ V).ι) (ofScheme V.ι)
    (ofScheme (q ∣_ V))
    (isPullback_toShHom (q ⁻¹ᵁ V).ι (q ∣_ V) q V.ι (isPullback_morphismRestrict q V).flip)

end Square

/-! ### Transporting the composition isomorphisms along a factorization -/

section Factor

variable {A B C : RingedSpace.{u, u}}

/-- The composition isomorphism of [Stacks, Tag 0D5S] read through a factorization `f ≫ g = k`.
Matching on the equality keeps `eqToHom` out of the result. -/
def derivedPullbackFactorIso (f : A ⟶ B) (g : B ⟶ C) :
    ∀ (k : A ⟶ C), f ≫ g = k → (derivedPullback g ⋙ derivedPullback f ≅ derivedPullback k)
  | _, rfl => Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g

/-- The composition isomorphism of [Stacks, Tag 0D5T] read through a factorization `f ≫ g = k`. -/
def derivedPushforwardFactorIso (f : A ⟶ B) (g : B ⟶ C) :
    ∀ (k : A ⟶ C), f ≫ g = k →
      (derivedPushforward f ⋙ derivedPushforward g ≅ derivedPushforward k)
  | _, rfl => derivedPushforwardCompIso f g

/-- **Derived pullback along an isomorphism of ringed spaces is an equivalence.**  A two-sided
inverse `g` of `f` gives the quasi-inverse `Lg^*`, by the composition isomorphisms of
[Stacks, Tag 0D5S] at the two identities. -/
theorem isEquivalence_derivedPullback_of_inverse (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A)
    (hgf : g ≫ f = 𝟙 B) : (derivedPullback f).IsEquivalence :=
  Functor.IsEquivalence.mk' (derivedPullback g)
    (derivedPullbackFactorIso g f (𝟙 B) hgf ≪≫
      Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso B).symm
    (derivedPullbackFactorIso f g (𝟙 A) hfg ≪≫
      Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso A)

/-- **For an isomorphism `f` of ringed spaces, `N ≅ Rf_*Lf^*N`**: the unit of the derived
adjunction of [Stacks, Tag 079W] is invertible, `Lf^*` being an equivalence. -/
def derivedUnitIsoOfInverse (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 B)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing B))) :
    N ≅ (derivedPushforward f).obj ((derivedPullback f).obj N) :=
  have := isEquivalence_derivedPullback_of_inverse f g hfg hgf
  have : IsIso (derivedAdjunction f).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful (derivedAdjunction f)
  asIso ((derivedAdjunction f).unit.app N)

end Factor

/-- The structure sheaf of a scheme, placed in degree zero, as an object of the unbounded derived
category of its sheaves of modules in the ringed-space spelling. -/
abbrev structureSheafSingle (A : Scheme.{u}) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing A.toRingedSpace)) :=
  (DerivedCategory.singleFunctor A.Modules 0).obj (SheafOfModules.unit A.ringCatSheaf)

end DerivedChow

open DerivedChow

/-! ### The finitely presented closed immersion `U ⟶ V` -/

section Morphism

variable {X P T Z : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ P) (iZ : Z ⟶ T) (U : X.Opens) (V : P.Opens)

/-- Transporting the inclusion of an open subscheme along an equality of opens. -/
theorem eqToHom_toScheme_comp_ι {Y : Scheme.{u}} {W W' : Y.Opens} (h : W = W') :
    eqToHom (congrArg Scheme.Opens.toScheme h) ≫ W'.ι = W.ι := by
  subst h; simp

/-- Transporting the restriction of a morphism to an open of its target along an equality of
opens of the source. -/
theorem eqToHom_toScheme_comp_morphismRestrict_comp_ι {Y Y' : Scheme.{u}} (k : Y ⟶ Y')
    (O : Y'.Opens) {W : Y.Opens} (h : W = k ⁻¹ᵁ O) :
    eqToHom (congrArg Scheme.Opens.toScheme h) ≫ (k ∣_ O) ≫ O.ι = W.ι ≫ k := by
  subst h; rw [eqToHom_refl, Category.id_comp, morphismRestrict_ι]

/-- Two transports along an equality of opens and its inverse cancel. -/
theorem eqToHom_symm_trans_comp {Y A : Scheme.{u}} {W W' : Y.Opens} (h : W = W')
    (m : W'.toScheme ⟶ A) :
    eqToHom (congrArg Scheme.Opens.toScheme h.symm) ≫
        eqToHom (congrArg Scheme.Opens.toScheme h) ≫ m = m := by
  subst h; simp

/-- **The morphism `c ∘ (b|_U)⁻¹ : U ⟶ V` of [Stacks, Tag 0CSK].**  Here `b = iZ ≫ p` is an
isomorphism over `U`, the open `b ⁻¹ᵁ U` is identified with `c ⁻¹ᵁ V` by hypothesis, and
`c = iZ ≫ q` is restricted to `V`. -/
def chowDatumMorphism (hb : IsIso ((iZ ≫ p) ∣_ U))
    (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V) : U.toScheme ⟶ V.toScheme :=
  @inv _ _ _ _ ((iZ ≫ p) ∣_ U) hb ≫ eqToHom (congrArg Scheme.Opens.toScheme hW) ≫
    ((iZ ≫ q) ∣_ V)

/-- The isomorphism `W ≅ U` given by `b|_U`, with `W = c ⁻¹ᵁ V` read as the part of `Z` lying
over the open `q ⁻¹ᵁ V` of `T`. -/
def chowDatumGraphIso (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V) :
    (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ U.toScheme :=
  eqToHom (congrArg Scheme.Opens.toScheme hW.symm) ≫ ((iZ ≫ p) ∣_ U)

/-- `chowDatumGraphIso` is an isomorphism, `b|_U` being one. -/
theorem isIso_chowDatumGraphIso (hb : IsIso ((iZ ≫ p) ∣_ U))
    (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V) :
    IsIso (chowDatumGraphIso p q iZ U V hW) := by
  have := hb
  unfold chowDatumGraphIso
  infer_instance

/-- **The first factorization identity.**  Composing `W ≅ U` with the morphism `U ⟶ V` is the
restriction of `c` to `V`, read as the composite `W ⟶ q ⁻¹ᵁ V ⟶ V`. -/
theorem chowDatumGraphIso_comp_chowDatumMorphism (hb : IsIso ((iZ ≫ p) ∣_ U))
    (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V) :
    chowDatumGraphIso p q iZ U V hW ≫ chowDatumMorphism p q iZ U V hb hW =
      (iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ∣_ V) := by
  have key : chowDatumGraphIso p q iZ U V hW ≫ chowDatumMorphism p q iZ U V hb hW =
      (iZ ≫ q) ∣_ V := by
    change (eqToHom (congrArg Scheme.Opens.toScheme hW.symm) ≫ ((iZ ≫ p) ∣_ U)) ≫
      (@inv _ _ _ _ ((iZ ≫ p) ∣_ U) hb ≫
        eqToHom (congrArg Scheme.Opens.toScheme hW) ≫ ((iZ ≫ q) ∣_ V)) = (iZ ≫ q) ∣_ V
    rw [Category.assoc, IsIso.hom_inv_id_assoc, eqToHom_symm_trans_comp hW]
  exact key.trans (morphismRestrict_comp iZ q V)

/-- **The second factorization identity.**  Composing `W ≅ U` with the inclusion of `U` is the
composite `W ⟶ q ⁻¹ᵁ V ⟶ T ⟶ X`. -/
theorem chowDatumGraphIso_comp_ι (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V) :
    chowDatumGraphIso p q iZ U V hW ≫ U.ι = (iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ⁻¹ᵁ V).ι ≫ p := by
  have key : chowDatumGraphIso p q iZ U V hW ≫ U.ι = ((iZ ≫ q) ⁻¹ᵁ V).ι ≫ (iZ ≫ p) := by
    change (eqToHom (congrArg Scheme.Opens.toScheme hW.symm) ≫ ((iZ ≫ p) ∣_ U)) ≫ U.ι =
      ((iZ ≫ q) ⁻¹ᵁ V).ι ≫ (iZ ≫ p)
    rw [Category.assoc, eqToHom_toScheme_comp_morphismRestrict_comp_ι (iZ ≫ p) U hW.symm]
  exact key.trans (morphismRestrict_ι_assoc iZ (q ⁻¹ᵁ V) p).symm

/-- **[Stacks, Tag 0CSK], first assertion: `U ⟶ V` is a closed immersion.**  It is the inverse of
an isomorphism, a transport along an equality of opens, and the closed immersion `c|_V`. -/
@[stacks 0CSK "the morphism U ⟶ V of the statement is a closed immersion; finite presentation \
of U ⟶ V is finitePresentation_chowDatumMorphism_of_locallyOfFinitePresentation, the derived \
comparison for K in D_QCoh(O_X) is chowDatum_derivedPushforward_tensor_restrict_iso_of_isDQCoh, \
and the whole statement is chowDatum_fourierMukai"]
theorem isClosedImmersion_chowDatumMorphism (hb : IsIso ((iZ ≫ p) ∣_ U))
    (hc : IsClosedImmersion ((iZ ≫ q) ∣_ V))
    (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V) :
    IsClosedImmersion (chowDatumMorphism p q iZ U V hb hW) := by
  have := hb
  have := hc
  unfold chowDatumMorphism
  infer_instance

/-- **`U ⟶ V` is of finite presentation when `U` and `V` are.**  The two factorization
identities show that `U ⟶ V` is a morphism over the base `S`, and [Stacks, Tag 02FV] then
deduces finite presentation of `U ⟶ V` from finite presentation of `U ⟶ S` and of `V ⟶ S`;
this is the argument of the source proof of [Stacks, Tag 0CSK].  The form at the hypotheses of
that tag, asking only local finite presentation of `X` over the base, is
`AlgebraicGeometry.finitePresentation_chowDatumMorphism_of_locallyOfFinitePresentation`. -/
theorem finitePresentation_chowDatumMorphism {S : Scheme.{u}} (f : X ⟶ S) (g : P ⟶ S)
    (hpq : p ≫ f = q ≫ g) (hb : IsIso ((iZ ≫ p) ∣_ U))
    (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V)
    (hU : AlgebraicGeometry.FinitePresentation (U.ι ≫ f))
    (hV : AlgebraicGeometry.FinitePresentation (V.ι ≫ g)) :
    AlgebraicGeometry.FinitePresentation (chowDatumMorphism p q iZ U V hb hW) := by
  have := hV.1
  have := hV.2.2
  have key : chowDatumMorphism p q iZ U V hb hW ≫ (V.ι ≫ g) = U.ι ≫ f := by
    have hiso := isIso_chowDatumGraphIso p q iZ U V hb hW
    have h1 : chowDatumGraphIso p q iZ U V hW ≫
          chowDatumMorphism p q iZ U V hb hW ≫ V.ι ≫ g =
        chowDatumGraphIso p q iZ U V hW ≫ U.ι ≫ f := by
      rw [← Category.assoc _ _ (V.ι ≫ g), chowDatumGraphIso_comp_chowDatumMorphism,
        ← Category.assoc _ _ f, chowDatumGraphIso_comp_ι]
      simp only [Category.assoc]
      rw [morphismRestrict_ι_assoc, hpq]
    exact (cancel_epi (chowDatumGraphIso p q iZ U V hW)).mp h1
  rw [← key] at hU
  exact finitePresentation_of_comp _ (V.ι ≫ g) hU

end Morphism

/-! ### The comparison of [Stacks, Tag 0CSK] -/

section Comparison

variable {X P T Z : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ P) (iZ : Z ⟶ T) (U : X.Opens) (V : P.Opens)
  (hb : IsIso ((iZ ≫ p) ∣_ U)) (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V)
  (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing T.toRingedSpace)))
  (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

/-- **The chain of isomorphisms of the source proof of [Stacks, Tag 0CSK].**  In the situation
of Chow's lemma in the derived category — `p : T ⟶ X` and `q : T ⟶ P` the two projections of
`T = X ×_A P`, `iZ : Z ⟶ T` the closed subscheme, `b = iZ ≫ p` an isomorphism over the open
`U ⊆ X`, and `b ⁻¹ᵁ U = c ⁻¹ᵁ V` for `c = iZ ≫ q` and an open `V ⊆ P` — for every
`E ∈ D(𝒪_T)` and every `K ∈ D(𝒪_X)`, given

* `hE`, clause (5) of [Stacks, Tag 0CSJ] in its restricted form: the restriction of `E` to
  `q ⁻¹ᵁ V` is the derived direct image of the structure sheaf of `W = c ⁻¹ᵁ V` along the closed
  immersion `i = iZ ∣_ (q ⁻¹ᵁ V)`, and
* `hproj`, [Stacks, Tag 08EU] at `i` and at the restriction of `Lp^*K`,

one has `Rq_*(Lp^*K ⊗^𝐋 E)|_V ≅ R(c ∘ (b|_U)⁻¹)_*(K|_U)`.

Both arguments are supplied, at the source's hypothesis `K ∈ D_QCoh(𝒪_X)`, by
`AlgebraicGeometry.chowDatum_derivedPushforward_tensor_restrict_iso_of_isDQCoh`
(through `AlgebraicGeometry.DerivedChow.pushforwardUnitRestrictIso` and
`AlgebraicGeometry.derivedProjectionFormulaUnitRightIso`); [Stacks, Tag 0CSK] in full is
`AlgebraicGeometry.chowDatum_fourierMukai`.

The steps of the chain: the localization of the direct image is [Stacks, Tag 08FE], here
`AlgebraicGeometry.DerivedChow.derivedPushforwardRestrictOpenIso`; the monoidality of derived
pullback is [Stacks, Tag 079U]; the two composition isomorphisms are [Stacks, Tag 0D5S] and
[Stacks, Tag 0D5T]; and the final identification uses that `b|_U` is an isomorphism, so that the
unit of the derived adjunction of [Stacks, Tag 079W] along it is invertible. -/
theorem chowDatum_derivedPushforward_tensor_restrict_iso
    (hE : (derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj E ≅
      (derivedPushforward (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).obj
        (structureSheafSingle (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme))
    (hproj : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            (q ⁻¹ᵁ V).toScheme.sheaf).obj
          ((derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj
            ((derivedPullback (ofScheme p)).obj K))).obj
        ((derivedPushforward (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).obj
          (structureSheafSingle (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme)) ≅
      (derivedPushforward (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).obj
        ((derivedPullback (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).obj
          ((derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj
            ((derivedPullback (ofScheme p)).obj K)))) :
    Nonempty ((derivedPullback (ofScheme V.ι)).obj ((derivedPushforward (ofScheme q)).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor T.sheaf).obj
          ((derivedPullback (ofScheme p)).obj K)).obj E)) ≅
      (derivedPushforward (ofScheme (chowDatumMorphism p q iZ U V hb hW))).obj
        ((derivedPullback (ofScheme U.ι)).obj K)) := by
  have hiso := isIso_chowDatumGraphIso p q iZ U V hb hW
  -- Step 1: [Stacks, Tag 08FE], the localization of the total direct image.
  refine ⟨(derivedPushforwardRestrictOpenIso q V).app
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor T.sheaf).obj
        ((derivedPullback (ofScheme p)).obj K)).obj E) ≪≫
    (derivedPushforward (ofScheme (q ∣_ V))).mapIso
      -- Steps 2–4: [Stacks, Tag 079U], then clause (5) of [Stacks, Tag 0CSJ], then the
      -- projection formula.
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
          (ofScheme (q ⁻¹ᵁ V).ι)).app ((derivedPullback (ofScheme p)).obj K, E) ≪≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            (q ⁻¹ᵁ V).toScheme.sheaf).obj
          ((derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj
            ((derivedPullback (ofScheme p)).obj K))).mapIso hE ≪≫ hproj) ≪≫
    -- Step 5: [Stacks, Tag 0D5T] for `i` and `q ∣_ V`.
    (derivedPushforwardFactorIso (ofScheme (iZ ∣_ (q ⁻¹ᵁ V))) (ofScheme (q ∣_ V))
      (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ∣_ V))) rfl).app _ ≪≫
    -- Step 6: [Stacks, Tag 0D5S] twice, and the second factorization identity.
    (derivedPushforward (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ∣_ V)))).mapIso
      ((derivedPullback (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).mapIso
          ((derivedPullbackFactorIso (ofScheme (q ⁻¹ᵁ V).ι) (ofScheme p)
            (ofScheme ((q ⁻¹ᵁ V).ι ≫ p)) rfl).app K) ≪≫
        (derivedPullbackFactorIso (ofScheme (iZ ∣_ (q ⁻¹ᵁ V))) (ofScheme ((q ⁻¹ᵁ V).ι ≫ p))
          (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ⁻¹ᵁ V).ι ≫ p)) rfl).app K ≪≫
        ((derivedPullbackFactorIso (ofScheme (chowDatumGraphIso p q iZ U V hW)) (ofScheme U.ι)
          (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ⁻¹ᵁ V).ι ≫ p))
          (congrArg ofScheme (chowDatumGraphIso_comp_ι p q iZ U V hW))).app K).symm) ≪≫
    -- Steps 7–8: the first factorization identity, [Stacks, Tag 0D5T], and the unit of
    -- [Stacks, Tag 079W] along the isomorphism `b|_U`.
    ((derivedPushforwardFactorIso (ofScheme (chowDatumGraphIso p q iZ U V hW))
      (ofScheme (chowDatumMorphism p q iZ U V hb hW))
      (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ∣_ V)))
      (congrArg ofScheme (chowDatumGraphIso_comp_chowDatumMorphism p q iZ U V hb hW))).app
        ((derivedPullback (ofScheme (chowDatumGraphIso p q iZ U V hW))).obj
          ((derivedPullback (ofScheme U.ι)).obj K))).symm ≪≫
    (derivedPushforward (ofScheme (chowDatumMorphism p q iZ U V hb hW))).mapIso
      (derivedUnitIsoOfInverse (ofScheme (chowDatumGraphIso p q iZ U V hW))
        (ofScheme (inv (chowDatumGraphIso p q iZ U V hW)))
        (congrArg ofScheme (IsIso.hom_inv_id _)) (congrArg ofScheme (IsIso.inv_hom_id _))
        ((derivedPullback (ofScheme U.ι)).obj K)).symm⟩

end Comparison

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalAmbientSquareZeroValues
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap.RecoveryAndThickeningHom

/-!
# Modifying a morphism of first order thickenings by a derivation

This file is the second part of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap`; see that module's
docstring for the mathematical overview.  It contains [Stacks Project, Tag 04D0]: the
modification `α = (a')^♯ + D` of the structure map of a morphism `(a, a')` of first order
thickenings over `T` by an `𝒪_X`-linear map `θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}`, the construction of
the modification datum from `θ` on the site of the ambient space, and the existence and
uniqueness of the resulting morphism of pairs.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.RingedToposModules (directImageModules inverseImageDerivationEquiv)
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Modification

variable {T X' Y' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1} {H : Subfunctor Y'.1}
  (hG : IsThickening B S hS X' G) (hH : IsThickening B S hS Y' H)
  (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (a : IsThickening.space B S hS hG ⟶ IsThickening.space B S hS hH)

/-- The `𝒪_X`-linear maps `θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 04D0], for a
morphism `a : X ⟶ Y` of the closed subspaces of two thickenings over `T`. -/
noncomputable abbrev ThickeningDerivationMap :=
  (modulePullback B S hS a).obj
      (sheafOfDifferentials B S hS (IsThickening.inclusion B S hS hH ≫ pY')) ⟶
    conormalModule B S hS X' ⟨G, hG.1⟩

/-- The modification of the structure map of a morphism `(a, a')` of first order thickenings
over `T` by an `𝒪_X`-linear map `θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}`: the map
`α = (a')^♯ + D` of [Stacks Project, Tag 04D0], where `D = d_{Y/T} ∘ θ` is the `𝒪_T`-derivation
attached to `θ` by Equation (0619), read as a morphism of the small étale ringed topoi of `X'`
and `Y'`.

Only what the source's proof uses of the sum is recorded: that it is a map of `𝒪_T`-algebras
fitting the commuting square, which is what makes [Stacks Project, Tag 05ZN] applicable; that
it is locally ringed; that `θ = 0` gives back `(a')^♯`; and that distinct `θ` give
non-2-isomorphic morphisms, which is injectivity of Equation (0619). -/
structure DerivationModification (a' : X' ⟶ Y') where
  /-- The thickening `X ⊂ X'` is of first order. -/
  firstOrderSource : IsFirstOrderThickening B S hS X' G
  /-- The thickening `Y ⊂ Y'` is of first order. -/
  firstOrderTarget : IsFirstOrderThickening B S hS Y' H
  /-- The modified structure map `α = (a')^♯ + d_{Y/T} ∘ θ`, as a morphism of ringed topoi. -/
  hom : ThickeningDerivationMap B S hS hG hH pY' a →
    RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y')
  /-- The modified structure map is a morphism of locally ringed topoi. -/
  isLocallyRinged : ∀ θ, (hom θ).IsLocallyRinged
  /-- The modified structure map fits the commuting square of [Stacks Project, Tag 05ZN]. -/
  square : ∀ θ, Nonempty (SmallEtaleTwoIso B S hS
    (smallEtaleComp B S hS (hom θ)
      (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)))
    (smallEtaleRingedToposHom B S hS (a ≫ IsThickening.inclusion B S hS hH)))
  /-- The modified structure map is a map of `𝒪_T`-algebras. -/
  algebra : ∀ θ, Nonempty (SmallEtaleTwoIso B S hS
    (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pY') (hom θ))
    (smallEtaleRingedToposHom B S hS pX'))
  /-- The map `θ` which does not move `a'`: the zero map of the source. -/
  base : ThickeningDerivationMap B S hS hG hH pY' a
  /-- Modifying by the zero map returns the structure map of `a'`. -/
  hom_base : Nonempty (SmallEtaleTwoIso B S hS (smallEtaleRingedToposHom B S hS a') (hom base))
  /-- Distinct maps `θ` modify the structure map to non-2-isomorphic morphisms. -/
  injective : ∀ θ₁ θ₂, Nonempty (SmallEtaleTwoIso B S hS (hom θ₁) (hom θ₂)) → θ₁ = θ₂

/-! ### Building the modification datum -/

/-- **The values of the derivation of [Stacks Project, Tag 04D0] on the site of the ambient
space.**  The conormal module `𝒞_{X/X'}` pushed forward along `i_X` to the small étale site of
`X'` and read as a module over `(a')^{-1}𝒪_{Y'}` through the structure map of `a'`.

This is where the correction term `D = d_{Y/T} ∘ θ` of the modified structure map takes its
values once that map is formed on the site of `X'`, which is where
`AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionHom` forms it. -/
noncomputable abbrev ambientConormalDerivationValues (a' : X' ⟶ Y') :
    SheafOfModules.{u}
      (inverseImageStructureRingSheaf B S hS (smallEtaleRingedToposHom B S hS a')) :=
  (SheafOfModules.restrictScalars
      ((sheafCompose (smallEtaleRingedTopos B S hS X').J
        (forget₂ CommRingCat.{u} RingCat.{u})).map
        (smallEtaleRingedToposHom B S hS a').fSharpInverseImage)).obj
    ((modulePushforward B S hS (subspaceInclusion B S hS X' ⟨G, hG.1⟩)).obj
      (conormalModule B S hS X' ⟨G, hG.1⟩))

/-- **The assignment `θ ↦ D` of Equation [Stacks Project, Tag 0619], read on the site of the
ambient space `X'`, together with the two first order conditions.**

This is the input that `AlgebraicGeometry.Space.derivationModificationOfFamily` turns into a
`AlgebraicGeometry.Space.DerivationModification`, and it is exactly the part of that datum which
the transport of `ConormalAmbientSquareZeroValues.lean` does *not* supply: Equation (0619) is a
bijection between the `𝒪_X`-linear maps `θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}` and the `𝒪_T`-derivations of
`𝒪_Y` with values in `a_*𝒞_{X/X'}` on the small étale site of the closed subspace `Y`
(`AlgebraicGeometry.Space.derivationDirectImageEquiv`), whereas the modified structure map `α` of
[Stacks Project, Tag 04D0] is a map on the site of `X'` and so needs a derivation of
`(a')^{-1}𝒪_{Y'}` there.

Carrying a derivation across that change of site and of source is
`AlgebraicGeometry.Space.ambientConormalDerivation`, and `AlgebraicGeometry.Space.thickeningDerivationFamilyOfHom` builds the structure.
What the transport does *not* do is go through the site of the closed subspace `Y` at all —
Equation (0619) is read at the composite `X ⟶ X' ⟶ Y'` instead, and only the map `θ` itself is
carried from `Ω_{Y/T}` to `Ω_{Y'/T}`, by the comparison of [Stacks Project, Tag 04CX].

The derivation is an unbundled explicit family rather than a `PresheafOfModules.Derivation'` for
the reason recorded in `StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceSurjective.lean`: the
bundled form has its index implicit and unifying it against the sections of the small étale
structure sheaf is a deterministic `whnf` timeout. -/
structure ThickeningDerivationFamily (a' : X' ⟶ Y') where
  /-- The thickening `X ⊂ X'` is of first order. -/
  firstOrderSource : IsFirstOrderThickening B S hS X' G
  /-- The thickening `Y ⊂ Y'` is of first order. -/
  firstOrderTarget : IsFirstOrderThickening B S hS Y' H
  /-- The derivation `D = d_{Y/T} ∘ θ` attached to `θ` by Equation [Stacks Project, Tag 0619]. -/
  d : ∀ (_θ : ThickeningDerivationMap B S hS hG hH pY' a)
      (V : (SmallEtale B S hS X'.1)ᵒᵖ),
    (inverseImageStructureRingSheaf B S hS
        (smallEtaleRingedToposHom B S hS a')).obj.obj V →+
      (ambientConormalDerivationValues B S hS hG a').val.obj V
  /-- Each member of the family satisfies the Leibniz rule. -/
  d_mul : ∀ (θ : ThickeningDerivationMap B S hS hG hH pY' a)
      (V : (SmallEtale B S hS X'.1)ᵒᵖ)
      (s t : (inverseImageStructureRingSheaf B S hS
        (smallEtaleRingedToposHom B S hS a')).obj.obj V),
    d θ V (s * t) = s • d θ V t + t • d θ V s
  /-- Each member of the family commutes with restriction. -/
  d_map : ∀ (θ : ThickeningDerivationMap B S hS hG hH pY' a)
      (V W : (SmallEtale B S hS X'.1)ᵒᵖ) (h : V ⟶ W)
      (s : (inverseImageStructureRingSheaf B S hS
        (smallEtaleRingedToposHom B S hS a')).obj.obj V),
    d θ W ((inverseImageStructureRingSheaf B S hS
        (smallEtaleRingedToposHom B S hS a')).obj.map h s) =
      (ambientConormalDerivationValues B S hS hG a').val.map h (d θ V s)
  /-- The map `θ` which is to leave `(a')^♯` unmoved. -/
  base : ThickeningDerivationMap B S hS hG hH pY' a
  /-- Equation (0619) sends `base` to the zero derivation. -/
  d_base : ∀ (V : (SmallEtale B S hS X'.1)ᵒᵖ)
      (x : (inverseImageStructureRingSheaf B S hS
        (smallEtaleRingedToposHom B S hS a')).obj.obj V),
    d base V x = 0

section Family

variable {a' : X' ⟶ Y'} (F : ThickeningDerivationFamily B S hS hG hH pY' a a')

/-- **The modified structure map `α = (a')^♯ + D` of [Stacks Project, Tag 04D0], as a morphism of
the small étale ringed topoi of `X'` and `Y'`.**  This is the field `hom` of
`AlgebraicGeometry.Space.DerivationModification`, constructed rather than assumed: it is
`AlgebraicGeometry.Space.conormalAmbientDerivationRingedToposHom` at the structure map of `a'`
and the derivation the family attaches to `θ`. -/
noncomputable abbrev derivationFamilyHom (θ : ThickeningDerivationMap B S hS hG hH pY' a) :
    RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y') :=
  conormalAmbientDerivationRingedToposHom B S hS ⟨G, hG.1⟩ F.firstOrderSource
    (smallEtaleRingedToposHom B S hS a')
    (smallEtaleRingedToposHom B S hS a').fSharpInverseImage
    (F.d θ) (F.d_mul θ) (F.d_map θ)

/-- **The modified structure map is a morphism of locally ringed topoi.**  The field
`isLocallyRinged` of `AlgebraicGeometry.Space.DerivationModification`, discharged: the
unperturbed structure map is that of a morphism of algebraic spaces, which reflects units at
every geometric point by [Stacks Project, Tag 04KJ] and [Stacks Project, Tag 04H9], and the
correction term is a section of a square-zero ideal of `𝒪_{X\'}`. -/
theorem isLocallyRinged_derivationFamilyHom
    (hpb : ∀ ψ : RingedToposHom (smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedTopos B S hS Y'),
      Limits.HasPullback (RingedTopos.unitsιOf (smallEtaleRingedTopos B S hS X').O)
        (RingedTopos.forgetRingMap ψ.fSharpInverseImage))
    (θ : ThickeningDerivationMap B S hS hG hH pY' a) :
    (derivationFamilyHom B S hS hG hH pY' a F θ).IsLocallyRinged :=
  have := hpb (derivationFamilyHom B S hS hG hH pY' a F θ)
  isLocallyRinged_conormalAmbientDerivationRingedToposHom B S hS ⟨G, hG.1⟩ F.firstOrderSource
    (smallEtaleRingedToposHom B S hS a')
    (smallEtaleRingedToposHom B S hS a').fSharpInverseImage
    (F.d θ) (F.d_mul θ) (F.d_map θ)
    fun x => RingedToposHom.reflectsUnitsObj_of_isLocallyRinged
      (smallEtaleRingedToposHom B S hS a')
      (smallEtaleRingedToposHom_isLocallyRinged B S hS a')
      ((etaleSitePoint B S hS X'.1 x X'.2).sheafFiber (A := Type u))

/-- **Modifying by the derivation of `base` returns `a'` itself**, as an equality of morphisms of
ringed topoi and not merely up to 2-isomorphism.  The field `hom_base` of
`AlgebraicGeometry.Space.DerivationModification` follows. -/
theorem derivationFamilyHom_base :
    derivationFamilyHom B S hS hG hH pY' a F F.base = smallEtaleRingedToposHom B S hS a' :=
  conormalAmbientDerivationRingedToposHom_eq_of_eq_zero B S hS ⟨G, hG.1⟩ F.firstOrderSource
    (smallEtaleRingedToposHom B S hS a') (F.d F.base) (F.d_mul F.base) (F.d_map F.base) F.d_base

end Family

/-! ### Carrying Equation (0619) to the site of the ambient space -/

section AmbientTransport

variable {a' : X' ⟶ Y'}

/-- **The direct image of the ambient conormal module, read on the two sides of the
adjunction `(a')^{-1} ⊣ (a')_*`.**  On the left the module `𝒞_{X/X'}` pushed forward along the
composite `X ⟶ X' ⟶ Y'` in one step, over `𝒪_{Y'}`; on the right the values
`AlgebraicGeometry.Space.ambientConormalDerivationValues` of the correction term — `𝒞_{X/X'}`
pushed to the site of `X'` and restricted along `(a')^♯` — pushed forward along the morphism of
topoi of `a'`.

The two differ only in the order in which the direct image and the restriction of scalars are
taken, and in which of the two adjunct forms of the structure map restricts them: the first
factor is [Stacks Project, Tag 03LU] for a composite
(`AlgebraicGeometry.Space.modulePushforwardCompIso`) and the second is the comparison of the two
direct images of modules (`AlgebraicGeometry.Space.modulePushforwardIso`).  Both are already
proved, and the identification of the right-hand side with the four-field direct image of
`𝒞_{X/X'}` pushed to the site of `X'` holds by `rfl`. -/
noncomputable def ambientConormalDirectImageIso :
    (modulePushforward B S hS (IsThickening.inclusion B S hS hG ≫ a')).obj
        (conormalModule B S hS X' ⟨G, hG.1⟩) ≅
      (directImageModules (smallEtaleRingedToposHom B S hS a').toToposHom
          (structureRingSheaf B S hS Y')).obj
        (ambientConormalDerivationValues B S hS hG a') :=
  ((modulePushforwardCompIso B S hS (IsThickening.inclusion B S hS hG) a').app
      (conormalModule B S hS X' ⟨G, hG.1⟩)).symm ≪≫
    ((modulePushforwardIso B S hS a').app
      ((modulePushforward B S hS (IsThickening.inclusion B S hS hG)).obj
        (conormalModule B S hS X' ⟨G, hG.1⟩))).symm

/-- **Equation [Stacks Project, Tag 0619] on the site of the ambient space `X'`.**  The
`𝒪_T`-derivation `D = d_{Y'/T} ∘ θ'` of `(a')^{-1}𝒪_{Y'}` with values in
`AlgebraicGeometry.Space.ambientConormalDerivationValues`, attached to an `𝒪_X`-linear map
`θ' : (i_X ≫ a')^*Ω_{Y'/T} ⟶ 𝒞_{X/X'}`.

This is the transport that `AlgebraicGeometry.Space.ThickeningDerivationFamily` was introduced
to name, and it is a composite of two proved statements and nothing else:

* Equation (0619) itself, `AlgebraicGeometry.Space.derivationDirectImageEquiv`, applied at the
  *composite* `i_X ≫ a' : X ⟶ Y'` and at `p_{Y'} : Y' ⟶ T`, which already produces an
  `𝒪_T`-derivation of `𝒪_{Y'}` with values in `(i_X ≫ a')_*𝒞_{X/X'}` on the small étale site of
  `Y'` — no passage through the site of the closed subspace `Y` is involved;
* the transposition of derivations along a morphism of topoi,
  `Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv`, which is the module-level
  half of [Stacks Project, Tag 08TQ], run backwards at the morphism of topoi of `a'`.

The comparison `AlgebraicGeometry.Space.ambientConormalDirectImageIso` is what makes the
coefficient module of the first match the direct image demanded by the second.  An earlier
version of the note on `ThickeningDerivationFamily` said that the passage was performed by
neither `PresheafOfModules.Derivation'.precomp` nor the inverse-image transport of
`StacksFrontier/Cotangent/SheavesOfRings/InverseImageDerivations.lean`.  That is true of `precomp`,
which works over a fixed site; it is not true of the inverse-image transport, which is in the
second file and does exactly this once Equation (0619) is read at the composite rather than at
`a : X ⟶ Y`. -/
noncomputable def ambientConormalDerivation
    (θ : (modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ a')).obj
        (sheafOfDifferentials B S hS pY') ⟶ conormalModule B S hS X' ⟨G, hG.1⟩) :
    PresheafOfModulesOfCommRing.Derivation' (ambientConormalDerivationValues B S hS hG a').val
      (((smallEtaleRingedToposHom B S hS a').toToposHom.inverseImageRing).map
        (structureSharpInverseImage B S hS pY')).hom :=
  (inverseImageDerivationEquiv (smallEtaleRingedToposHom B S hS a').toToposHom
      (structureSharpInverseImage B S hS pY')
      (ambientConormalDerivationValues B S hS hG a')).symm
    ((derivationDirectImageEquiv B S hS (IsThickening.inclusion B S hS hG ≫ a') pY'
      (conormalModule B S hS X' ⟨G, hG.1⟩) θ).postcomp
        (ambientConormalDirectImageIso B S hS hG (a' := a')).hom.val)

/-- **The transported derivation as an unbundled family indexed by an explicit object.**  This
is the field `d` of `AlgebraicGeometry.Space.ThickeningDerivationFamily`.

The index is explicit for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceSurjective.lean`: the bundled
`PresheafOfModules.Derivation'` has it implicit, and leaving it to unification against the
sections of the small étale structure sheaf is a deterministic `whnf` timeout.  Pinning it here
spends that defeq once, exactly as `AlgebraicGeometry.Space.derivationFamilyOfHom` does on the
site of the closed subspace. -/
noncomputable def ambientConormalDerivationFamily
    (θ : (modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ a')).obj
        (sheafOfDifferentials B S hS pY') ⟶ conormalModule B S hS X' ⟨G, hG.1⟩)
    (V : (SmallEtale B S hS X'.1)ᵒᵖ) :
    (inverseImageStructureRingSheaf B S hS
        (smallEtaleRingedToposHom B S hS a')).obj.obj V →+
      (ambientConormalDerivationValues B S hS hG a').val.obj V :=
  (ambientConormalDerivation B S hS hG pY' θ).d (X := V)

/-- The Leibniz rule for `AlgebraicGeometry.Space.ambientConormalDerivationFamily`: the field
`d_mul` of `AlgebraicGeometry.Space.ThickeningDerivationFamily`. -/
theorem ambientConormalDerivationFamily_mul
    (θ : (modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ a')).obj
        (sheafOfDifferentials B S hS pY') ⟶ conormalModule B S hS X' ⟨G, hG.1⟩)
    (V : (SmallEtale B S hS X'.1)ᵒᵖ)
    (s t : (inverseImageStructureRingSheaf B S hS
      (smallEtaleRingedToposHom B S hS a')).obj.obj V) :
    ambientConormalDerivationFamily B S hS hG pY' θ V (s * t) =
      s • ambientConormalDerivationFamily B S hS hG pY' θ V t +
        t • ambientConormalDerivationFamily B S hS hG pY' θ V s :=
  (ambientConormalDerivation B S hS hG pY' θ).d_mul s t

/-- `AlgebraicGeometry.Space.ambientConormalDerivationFamily` commutes with restriction: the
field `d_map` of `AlgebraicGeometry.Space.ThickeningDerivationFamily`. -/
theorem ambientConormalDerivationFamily_map
    (θ : (modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ a')).obj
        (sheafOfDifferentials B S hS pY') ⟶ conormalModule B S hS X' ⟨G, hG.1⟩)
    (V W : (SmallEtale B S hS X'.1)ᵒᵖ) (h : V ⟶ W)
    (s : (inverseImageStructureRingSheaf B S hS
      (smallEtaleRingedToposHom B S hS a')).obj.obj V) :
    ambientConormalDerivationFamily B S hS hG pY' θ W
        ((inverseImageStructureRingSheaf B S hS
          (smallEtaleRingedToposHom B S hS a')).obj.map h s) =
      (ambientConormalDerivationValues B S hS hG a').val.map h
        (ambientConormalDerivationFamily B S hS hG pY' θ V s) :=
  (ambientConormalDerivation B S hS hG pY' θ).d_map h s

/-- **The `θ` of [Stacks Project, Tag 04D0], read on the ambient target.**  An `𝒪_X`-linear map
`θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}` on the small étale site of the closed subspace `Y` determines a map
`(i_X ≫ a')^*Ω_{Y'/T} ⟶ 𝒞_{X/X'}`, which is what
`AlgebraicGeometry.Space.ambientConormalDerivation` consumes.

The input is the hypothesis of Tag 04D0 that `(a, a')` is a morphism of thickenings — the square
`i_X ≫ a' = a ≫ i_Y`, which `AlgebraicGeometry.Space.ThickeningDerivationFamily` does not record
and so has to be supplied here.  Given it, the map is the comparison
`i_Y^*Ω_{Y'/T} ⟶ Ω_{Y/T}` of [Stacks Project, Tag 04CX]
(`AlgebraicGeometry.Space.sheafOfDifferentialsMap` at `q = 𝟙 T`), pulled back along `a` and
composed with `θ`, the two pullbacks being compared by [Stacks Project, Tag 03LU]
(`AlgebraicGeometry.Space.modulePullbackCompIso`). -/
noncomputable def ambientThickeningDerivationMap
    (hcomm : IsThickening.inclusion B S hS hG ≫ a' = a ≫ IsThickening.inclusion B S hS hH)
    (θ : ThickeningDerivationMap B S hS hG hH pY' a) :
    (modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ a')).obj
        (sheafOfDifferentials B S hS pY') ⟶ conormalModule B S hS X' ⟨G, hG.1⟩ :=
  eqToHom (congrArg
      (fun m ↦ (modulePullback B S hS m).obj (sheafOfDifferentials B S hS pY')) hcomm) ≫
    ((modulePullbackCompIso B S hS a (IsThickening.inclusion B S hS hH)).app
        (sheafOfDifferentials B S hS pY')).inv ≫
      (modulePullback B S hS a).map
          (sheafOfDifferentialsMap B S hS (IsThickening.inclusion B S hS hH) pY'
            (IsThickening.inclusion B S hS hH ≫ pY') (𝟙 T) (by simp)) ≫
        θ

/-- **`AlgebraicGeometry.Space.ThickeningDerivationFamily` built from `θ` rather than assumed**,
up to one clause about its base point.

The three fields carrying the derivation — `d`, `d_mul` and `d_map` — are
`AlgebraicGeometry.Space.ambientConormalDerivationFamily` and its two laws, so the assignment
`θ ↦ D` of Equation [Stacks Project, Tag 0619] on the site of `X'` is now a construction.  Two
inputs remain, and neither is about derivations:

* `hcomm`, that `(a, a')` is a morphism of thickenings, which is a hypothesis of Tag 04D0 that
  the structure does not record;
* `hbase`, that the transported derivation of the chosen base point vanishes.  For the base
  point `θ = 0` this is a consequence of additivity of the two adjunctions involved —
  `AlgebraicGeometry.Space.modulePullbackAdjunction` and
  `Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules` are both additive — and
  of `Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv_symm_postcomp`, which moves
  the zero coefficient map outside the transposition.  It is a hypothesis here and not a
  conclusion because that argument has to be assembled at the concrete instance, where the
  `rfl`-level composition of two `PresheafOfModules.Derivation.postcomp`s is a deterministic
  `isDefEq` timeout at the small étale structure sheaf; it is the same hazard that forces the
  unbundled family, and no `maxHeartbeats` is raised here to hide it. -/
noncomputable def thickeningDerivationFamilyOfHom
    (hfirstG : IsFirstOrderThickening B S hS X' G)
    (hfirstH : IsFirstOrderThickening B S hS Y' H)
    (hcomm : IsThickening.inclusion B S hS hG ≫ a' = a ≫ IsThickening.inclusion B S hS hH)
    (base : ThickeningDerivationMap B S hS hG hH pY' a)
    (hbase : ∀ (V : (SmallEtale B S hS X'.1)ᵒᵖ)
        (x : (inverseImageStructureRingSheaf B S hS
          (smallEtaleRingedToposHom B S hS a')).obj.obj V),
      ambientConormalDerivationFamily B S hS hG pY'
        (ambientThickeningDerivationMap B S hS hG hH pY' a hcomm base) V x = 0) :
    ThickeningDerivationFamily B S hS hG hH pY' a a' where
  firstOrderSource := hfirstG
  firstOrderTarget := hfirstH
  d θ := ambientConormalDerivationFamily B S hS hG pY'
    (ambientThickeningDerivationMap B S hS hG hH pY' a hcomm θ)
  d_mul _ := ambientConormalDerivationFamily_mul B S hS hG pY' _
  d_map _ := ambientConormalDerivationFamily_map B S hS hG pY' _
  base := base
  d_base := hbase

end AmbientTransport

variable {a' : X' ⟶ Y'}

/-- **The modification datum of [Stacks Project, Tag 04D0], built rather than assumed.**

`AlgebraicGeometry.Space.DerivationModification` need no longer be assumed wholesale.  Of its
nine fields exactly three carry mathematical content that is *proved* here:

* `hom` is `AlgebraicGeometry.Space.derivationFamilyHom`, the sum `α = (a')^♯ + D` formed on the
  site of `X'` and carried back into an `AlgebraicGeometry.RingedToposHom`;
* `isLocallyRinged` is `AlgebraicGeometry.Space.isLocallyRinged_derivationFamilyHom`, which
  spends [Stacks Project, Tag 04KJ] on the unperturbed map and the square-zero property of the
  conormal ideal on the correction term;
* `hom_base` is `AlgebraicGeometry.Space.derivationFamilyHom_base`, which is an *equality* of
  morphisms of ringed topoi and not merely a 2-isomorphism.

Three fields are relocated rather than discharged — `firstOrderSource`, `firstOrderTarget` and
`base` are fields of the family instead of fields of the datum, and `d_base` replaces `hom_base`
as the hypothesis about the base point — and three clauses remain outright hypotheses:
`hsquare` (the commuting square of [Stacks Project, Tag 05ZN]), `halgebra` (that `α` is a map of
`𝒪_T`-algebras) and `hinjective` (injectivity of Equation [Stacks Project, Tag 0619] read
through the modification).  `hpb` is the existence of the pullback defining the units square.

The family `F` is still an argument of this definition, but it is no longer an assumption that
nothing produces: `AlgebraicGeometry.Space.thickeningDerivationFamilyOfHom` builds it from a map
`θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}`, the square `i_X ≫ a' = a ≫ i_Y` of [Stacks Project, Tag 04D0], and
the vanishing of the transported derivation at the base point.  The passage of Equation (0619) to
the site of `X'` is `AlgebraicGeometry.Space.ambientConormalDerivation`.

**No consumer can drop `DerivationModification` as an argument.**
`AlgebraicGeometry.Space.existsUnique_hom_of_derivationModification` and its companions still
take the datum, because `hsquare`, `halgebra` and `hinjective` are proved nowhere; what has
changed is that the datum can now be *produced* from them rather than only assumed. -/
noncomputable def derivationModificationOfFamily
    (F : ThickeningDerivationFamily B S hS hG hH pY' a a')
    (hpb : ∀ ψ : RingedToposHom (smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedTopos B S hS Y'),
      Limits.HasPullback (RingedTopos.unitsιOf (smallEtaleRingedTopos B S hS X').O)
        (RingedTopos.forgetRingMap ψ.fSharpInverseImage))
    (hsquare : ∀ θ, Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (derivationFamilyHom B S hS hG hH pY' a F θ)
        (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)))
      (smallEtaleRingedToposHom B S hS (a ≫ IsThickening.inclusion B S hS hH))))
    (halgebra : ∀ θ, Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pY')
        (derivationFamilyHom B S hS hG hH pY' a F θ))
      (smallEtaleRingedToposHom B S hS pX')))
    (hinjective : ∀ θ₁ θ₂,
      Nonempty (SmallEtaleTwoIso B S hS (derivationFamilyHom B S hS hG hH pY' a F θ₁)
        (derivationFamilyHom B S hS hG hH pY' a F θ₂)) → θ₁ = θ₂) :
    DerivationModification B S hS hG hH pX' pY' a a' where
  firstOrderSource := F.firstOrderSource
  firstOrderTarget := F.firstOrderTarget
  hom := derivationFamilyHom B S hS hG hH pY' a F
  isLocallyRinged := isLocallyRinged_derivationFamilyHom B S hS hG hH pY' a F hpb
  square := hsquare
  algebra := halgebra
  base := F.base
  hom_base := ⟨by
    rw [derivationFamilyHom_base B S hS hG hH pY' a F]
    exact RingedToposHom.TwoIso.refl (smallEtaleRingedToposHom B S hS a')⟩
  injective := hinjective

/-- **Stacks 04D0**, with the recovery of morphisms over the base and the modification datum
taken as arguments.  For a morphism `(a, a')`
of first order thickenings over `T` and an `𝒪_X`-linear map `θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}` there
is exactly one morphism `b' : X' ⟶ Y'` whose structure map is `(a')^♯ + d_{Y/T} ∘ θ`, and the
pair `(a, b')` is a morphism of thickenings over `T`.

Setting `b = a` this is the unique morphism of pairs `(b, b')` of the source: conditions (1)
and (2) of [Stacks Project, Tag 0618] are the two displayed equations, and the derivation `D`
is related to `θ` by Equation (0619) because that is how the datum `hom θ` is built. -/
@[stacks 04D0 "over a base SCHEME whose canonical morphism to the spectrum of its global \
functions is a monomorphism -- an affine base, a quasi-affine base: the morphism of pairs and \
its uniqueness, with the modified structure map (a')^sharp + D taken as an argument \
(`DerivationModification`), which packages that sum as a morphism of ringed topoi together with \
the two 2-isomorphisms Stacks 05ZN consumes.  The recovery of morphisms over the base is NOT \
taken as an argument any more: it is proved for such a base scheme by \
`isRecoveredFromSmallEtale_of_mono_toSpecGamma`, which is where the hypothesis on the base \
enters and the only place it enters"]
theorem existsUnique_hom_of_derivationModification_of_mono_toSpecΓ (hSmono : Mono S.toSpecΓ)
    (M : DerivationModification B S hS hG hH pX' pY' a a')
    (θ : ThickeningDerivationMap B S hS hG hH pY' a) :
    ∃! b' : X' ⟶ Y', InducesSmallEtaleRingedToposHom B S hS b' (M.hom θ) ∧
      IsThickening.inclusion B S hS hG ≫ b' = a ≫ IsThickening.inclusion B S hS hH ∧
      b' ≫ pY' = pX' :=
  existsUnique_thickeningHom B S hS hSmono hG hH pX' pY' a (M.hom θ) (M.square θ) (M.algebra θ)

/-- **Stacks 04D0 with the recovery of morphisms over the base taken as an argument.**

This is the shape in which the statement was first written.  The argument `hKL` is now available
without being assumed, for a base scheme whose canonical morphism to the spectrum of its global
functions is a monomorphism, so the tag is registered on
`AlgebraicGeometry.Space.existsUnique_hom_of_derivationModification_of_mono_toSpecΓ` above rather
than here. -/
@[stacks 04D0 "the morphism of pairs and its uniqueness, with the recovery of morphisms over \
the base taken as an argument (`IsRecoveredFromSmallEtale`, which is Stacks 04KL over a base) \
and with the modified structure map (a')^sharp + D taken as an argument \
(`DerivationModification`), since forming that sum needs the structure-sheaf half of 05ZM"]
theorem existsUnique_hom_of_derivationModification (hKL : IsRecoveredFromSmallEtale B S hS)
    (M : DerivationModification B S hS hG hH pX' pY' a a')
    (θ : ThickeningDerivationMap B S hS hG hH pY' a) :
    ∃! b' : X' ⟶ Y', InducesSmallEtaleRingedToposHom B S hS b' (M.hom θ) ∧
      IsThickening.inclusion B S hS hG ≫ b' = a ≫ IsThickening.inclusion B S hS hH ∧
      b' ≫ pY' = pX' :=
  existsUnique_thickeningHom_of_isLocallyRinged B S hS hKL hG hH pX' pY' a (M.hom θ)
    (isLocallyRinged_of_thickeningSquare B S hS hG hH a (M.hom θ) (M.square θ))
    (M.square θ) (M.algebra θ)

/-- **The uniqueness half of [Stacks Project, Tag 04D0], with nothing assumed.**  Two morphisms
`b₁', b₂' : X' ⟶ Y'` whose structure maps are both the modification `(a')^♯ + d_{Y/T} ∘ θ` are
equal.

This is the "unique" of the source's "there exists a unique morphism of pairs `(b, b')`", and
unlike the existence it needs neither Stacks 04KL over a base nor any property of the modified
structure map: it is [Stacks Project, Tag 04M6] applied to the composite 2-isomorphism, through
`AlgebraicGeometry.Space.eq_of_inducesCommonSmallEtaleRingedToposHom`.  Since `b = a` is fixed by
the source's construction, uniqueness of `b'` is uniqueness of the pair.

The `@[stacks 04D0]` attribute is **not** here but on
`AlgebraicGeometry.Space.eq_of_derivationModificationHomOfMap_induces`
(`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/DerivationModificationMorphism.lean`), which
is the same statement for the modification `α = (a')^♯ + D` *constructed* from `θ` rather than
for the modification of an abstract datum, and so carries only the source's own hypotheses. -/
theorem eq_of_derivationModification_induces
    (M : DerivationModification B S hS hG hH pX' pY' a a')
    (θ : ThickeningDerivationMap B S hS hG hH pY' a) (b₁' b₂' : X' ⟶ Y')
    (h₁ : InducesSmallEtaleRingedToposHom B S hS b₁' (M.hom θ))
    (h₂ : InducesSmallEtaleRingedToposHom B S hS b₂' (M.hom θ)) :
    b₁' = b₂' :=
  eq_of_inducesCommonSmallEtaleRingedToposHom B S hS b₁' b₂' h₁ h₂

/-- **The correspondence of [Stacks Project, Tag 04D0] is injective.**  Two `𝒪_X`-linear maps
`θ` which modify the structure map of `a'` to the same morphism of thickenings are equal. -/
@[stacks 04D0 "injectivity of the correspondence theta -> b', with the modified structure map \
taken as an argument (`DerivationModification`)"]
theorem eq_of_derivationModification_eq (M : DerivationModification B S hS hG hH pX' pY' a a')
    (θ₁ θ₂ : ThickeningDerivationMap B S hS hG hH pY' a) (b' : X' ⟶ Y')
    (h₁ : InducesSmallEtaleRingedToposHom B S hS b' (M.hom θ₁))
    (h₂ : InducesSmallEtaleRingedToposHom B S hS b' (M.hom θ₂)) :
    θ₁ = θ₂ := by
  obtain ⟨t₁⟩ := h₁
  obtain ⟨t₂⟩ := h₂
  exact M.injective θ₁ θ₂ ⟨t₁.symm.trans t₂⟩

/-- **The zero map of [Stacks Project, Tag 04D0] does not move `a'`.**  The morphism of
thickenings whose structure map is the modification of `(a')^♯` by the zero map is `a'`
itself. -/
@[stacks 04D0 "that the zero map returns the given morphism of thickenings, with the \
modified structure map taken as an argument (`DerivationModification`).  The recovery of \
morphisms over the base is NOT taken as an argument: only the faithfulness half of 04KL is \
used here, and that is proved, by `eq_of_inducesCommonSmallEtaleRingedToposHom`"]
theorem eq_of_derivationModification_base_of_induces
    (M : DerivationModification B S hS hG hH pX' pY' a a') (b' : X' ⟶ Y')
    (h : InducesSmallEtaleRingedToposHom B S hS b' (M.hom M.base)) :
    b' = a' :=
  eq_of_inducesCommonSmallEtaleRingedToposHom B S hS b' a' h M.hom_base

/-- **The zero map of [Stacks Project, Tag 04D0] does not move `a'`**, with the recovery of
morphisms over the base taken as an argument.

This is the shape in which the statement was first written.  The argument `hKL` is not needed:
only the faithfulness half of Stacks 04KL over a base is used, and that is proved for every base,
so the tag is registered on
`AlgebraicGeometry.Space.eq_of_derivationModification_base_of_induces` above rather than here. -/
@[stacks 04D0 "that the zero map returns the given morphism of thickenings, with the recovery \
of morphisms over the base taken as an argument (`IsRecoveredFromSmallEtale`, which is Stacks \
04KL over a base) and with the modified structure map taken as an argument \
(`DerivationModification`)"]
theorem eq_of_derivationModification_base (hKL : IsRecoveredFromSmallEtale B S hS)
    (M : DerivationModification B S hS hG hH pX' pY' a a') (b' : X' ⟶ Y')
    (h : InducesSmallEtaleRingedToposHom B S hS b' (M.hom M.base)) :
    b' = a' := by
  obtain ⟨_, -, huniq⟩ :=
    hKL pX' pY' (M.hom M.base)
      (isLocallyRinged_of_thickeningSquare B S hS hG hH a (M.hom M.base) (M.square M.base))
      (M.algebra M.base)
  exact (huniq b' h).trans (huniq a' M.hom_base).symm

end Modification

end AlgebraicGeometry.Space

end

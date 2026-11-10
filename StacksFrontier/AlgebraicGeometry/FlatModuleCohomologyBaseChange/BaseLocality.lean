module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DerivedCases
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DerivedLocality
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.Locality
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.PastingBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness

/-!
# The derived comparison of flat base change is local on the base

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes and let `G` be a quasi-coherent `𝒪_{S'}`-module flat over `S`.
Invertibility of the derived comparison `RΦ ∘ Rf_* ⟶ Rf'_* ∘ RΨ` of [Stacks, Tag 0GN5] at a
module placed in degree zero is a condition on an object of `D⁺(𝒪_{S'})`, hence local on `S'`;
this file shrinks both bases at once.  For an affine open `U` of `S` and an affine open `V` of
`S'` contained in `g ⁻¹ᵁ U` the original square restricts to the cartesian square

```
f' ⁻¹ᵁ V -----> f ⁻¹ᵁ U
    |              |
    v              v
    V    ------->  U
```

whose horizontal morphisms are `g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V)` and `g.resLE U V`, whose vertical
morphisms are `f' ∣_ V` and `f ∣_ U`, and whose coefficient module is the inverse image of `G`
along `V.ι`.  The comparison of the original square at `F[0]` is invertible as soon as the
comparison of every such restricted square is invertible at the inverse image of `F` along
`(f ⁻¹ᵁ U).ι`, placed in degree zero.  Since `U` is affine and `f ∣_ U` inherits quasi-compactness
and separatedness from `f`, the affine-base case of `DerivedCases.lean` then settles
[Stacks, Tag 0GN5] in derived form for a quasi-compact separated morphism over an arbitrary base.

## The route

The restricted square is reached by shrinking the two bases in turn, and the rectangle over
`V ⟶ S` obtained from the original square by restricting the base to `V` is the meeting point of
the two steps.

*Shrinking `S'` to `V`.*  By `DerivedLocality.lean` it is enough to invert the derived inverse
image along `V.ι` of the comparison, and by the pasting law of `Pasting.lean` — applied with the
left-hand square the restriction square of `f'` over `V` — the comparison of the rectangle over
`V ⟶ S` is `Stacks.Cohomology.BaseChange.derivedPaste` of that derived inverse image and the
derived base-change morphism of the restriction square.  The latter is invertible by
`BaseChangeDerivedIso.lean`, the base-change morphism of a restriction square being invertible at
every module and restriction to an open subscheme preserving injective objects.

*Shrinking `S` to `U`.*  The same rectangle decomposes the other way: by the pasting law of
`PastingBaseChange.lean` — applied with the right-hand square the restriction square of `f` over
`U` and the left-hand square the restricted square above — it is `derivedPaste` of the derived
base-change morphism of the restriction square of `f`, again invertible, and the comparison of
the restricted square, evaluated at the derived inverse image of `F[0]`.  The two decompositions
describe the same rectangle, up to the two identities `resLE _ _ ≫ ι = ι ≫ _`, and combine.

## Main results

* `isIso_derived_baseChangeNatTrans_restrictSquare`: the derived base-change morphism of a
  restriction square is invertible.
* `isIso_derivedComparison_app_single_of_affineBases`: **the derived comparison of
  [Stacks, Tag 0GN5] is local on the base**, in the form of a criterion over pairs of affine opens
  `V ⊆ g ⁻¹ᵁ U`.
* `isIso_derivedComparison_app_single_of_isSeparated'`: **the derived comparison is invertible at
  `F[0]` for a quasi-compact separated morphism over an arbitrary base.**
* `isIso_derivedComparison_app_single_of_isAffine_source`: the same for a morphism with affine
  source over a quasi-separated base.

## Implementation notes

The two uses of `Stacks.Cohomology.BaseChange.derivedPaste_app`, which splits a pasted derived
comparison into four factors, are made in the generic setting of additive functors between
abelian categories, where the identification of the second factor with the comparison of one of
the two squares is cheap; instantiating them at the concrete categories of sheaves of modules
afterwards costs only the unfolding of
`Stacks.AlgebraicGeometry.ModuleBaseChange.derivedComparison`.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 007T](https://stacks.math.columbia.edu/tag/007T)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Two formal lemmas on four-fold composites -/

/-- A four-fold composite whose factors are all invertible is invertible. -/
private theorem isIso_comp₄ {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    (ha : IsIso a) (hb : IsIso b) (hc : IsIso c) (hd : IsIso d) :
    IsIso (a ≫ b ≫ c ≫ d) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ ha
    (@IsIso.comp_isIso _ _ _ _ _ _ _ hb (@IsIso.comp_isIso _ _ _ _ _ _ _ hc hd))

/-- In a four-fold composite whose first, third and fourth factors are invertible, invertibility
of the composite is invertibility of the second factor. -/
private theorem isIso_of_isIso_comp₄ {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    (h : IsIso (a ≫ b ≫ c ≫ d)) (ha : IsIso a) (hc : IsIso c) (hd : IsIso d) : IsIso b :=
  @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ hc hd)
    (@IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ha h)

/-! ### The two factors of a pasted derived comparison, generically -/

section GenericPaste

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* B₂]
  [Abelian A₀] [Abelian A₁] [Abelian A₂]
  [Abelian B₀] [Abelian B₁] [Abelian B₂]
  [EnoughInjectives A₀] [EnoughInjectives A₁] [EnoughInjectives A₂]
  [EnoughInjectives B₀] [EnoughInjectives B₁]
  (P₀ : A₀ ⥤ B₀) (P₁ : A₁ ⥤ B₁) (P₂ : A₂ ⥤ B₂)
  (U₁ : B₀ ⥤ B₁) (U₂ : B₁ ⥤ B₂) (U : B₀ ⥤ B₂)
  (V₁ : A₀ ⥤ A₁) (V₂ : A₁ ⥤ A₂) (V : A₀ ⥤ A₂)
  [P₀.Additive] [P₁.Additive] [P₂.Additive]
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [V₁.Additive] [V₂.Additive] [V.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits V₂] [PreservesFiniteColimits V₂]
  (cU : U₁ ⋙ U₂ ≅ U) (cV : V₁ ⋙ V₂ ≅ V)
  (τ₁ : P₀ ⋙ U₁ ⟶ V₁ ⋙ P₁) (τ₂ : P₁ ⋙ U₂ ⟶ V₂ ⋙ P₂)

/-- A pasted derived comparison is invertible at an object as soon as the two squares'
comparisons are: the two remaining factors of
`Stacks.Cohomology.BaseChange.derivedPaste_app` are components of isomorphisms. -/
private theorem isIso_derivedPaste_app
    (M : DerivedCategory.Plus A₀)
    (h₁ : IsIso (U₂.rightDerivedFunctorPlus.map
      ((Stacks.Cohomology.BaseChange.derived P₀ P₁ U₁ V₁ τ₁
        (asIso U₁.rightDerivedFunctorPlusUnith)).app M)))
    (h₂ : IsIso ((Stacks.Cohomology.BaseChange.derived P₁ P₂ U₂ V₂ τ₂
      (asIso U₂.rightDerivedFunctorPlusUnith)).app (V₁.rightDerivedFunctorPlus.obj M))) :
    IsIso ((Stacks.Cohomology.BaseChange.derivedPaste P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV τ₁ τ₂).app
      M) := by
  rw [Stacks.Cohomology.BaseChange.derivedPaste_app]
  exact isIso_comp₄ inferInstance h₁ h₂ inferInstance

/-- Conversely, invertibility of a pasted derived comparison at an object, together with
invertibility of the left-hand square's comparison there, gives invertibility of the right-hand
square's comparison after the derived functor of the outer base functor. -/
private theorem isIso_map_derived_of_isIso_derivedPaste_app
    (M : DerivedCategory.Plus A₀)
    (h : IsIso ((Stacks.Cohomology.BaseChange.derivedPaste P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV
      τ₁ τ₂).app M))
    (h₂ : IsIso ((Stacks.Cohomology.BaseChange.derived P₁ P₂ U₂ V₂ τ₂
      (asIso U₂.rightDerivedFunctorPlusUnith)).app (V₁.rightDerivedFunctorPlus.obj M))) :
    IsIso (U₂.rightDerivedFunctorPlus.map
      ((Stacks.Cohomology.BaseChange.derived P₀ P₁ U₁ V₁ τ₁
        (asIso U₁.rightDerivedFunctorPlusUnith)).app M)) := by
  rw [Stacks.Cohomology.BaseChange.derivedPaste_app] at h
  exact isIso_of_isIso_comp₄ h inferInstance h₂ inferInstance

end GenericPaste

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- Invertibility at an object of a natural transformation transports along an identity of
natural transformations. -/
private theorem isIso_app_of_natTrans_eq {C D : Type*} [Category* C] [Category* D] {E E' : C ⥤ D}
    {τ σ : E ⟶ E'} (h : τ = σ) (M : C) (hσ : IsIso (σ.app M)) : IsIso (τ.app M) := by
  subst h
  exact hσ

/-! ### Transport along an identity of the two horizontal morphisms -/

/-- Invertibility of the derived comparison depends on the two horizontal morphisms of the square
only through their values: equal horizontal morphisms give equal comparisons, the commutativity
of the square and the flatness of `G` being propositions. -/
private theorem isIso_derivedComparison_app_congr {g₁ g₂ : S' ⟶ S} {g'₁ g'₂ : X' ⟶ X}
    (hg : g₁ = g₂) (hg' : g'₁ = g'₂)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (w₁ : g'₁ ≫ f = f' ≫ g₁) (hG₁ : AlgebraicGeometry.IsFlatOver g₁.toLRSHom.toShHom G)
    (w₂ : g'₂ ≫ f = f' ≫ g₂) (hG₂ : AlgebraicGeometry.IsFlatOver g₂.toLRSHom.toShHom G)
    (E : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (h : IsIso ((derivedComparison G w₁ hG₁).app E)) :
    IsIso ((derivedComparison G w₂ hG₂).app E) := by
  subst hg
  subst hg'
  exact h

/-! ### The derived base-change morphism of a restriction square -/

/-- **The derived base-change morphism of a restriction square is invertible.**  The base-change
morphism of [Stacks, Tag 02KG] for the square `(q ⁻¹ᵁ V).ι ≫ q = (q ∣_ V) ≫ V.ι` is invertible at
every module, and restriction to an open subscheme preserves injective objects, so its descent to
bounded below derived categories is invertible. -/
theorem isIso_derived_baseChangeNatTrans_restrictSquare {Y Z : Scheme.{u}} (q : Y ⟶ Z)
    (V : Z.Opens) [PreservesFiniteLimits (modulePullback V.ι.toLRSHom.toShHom)]
    [PreservesFiniteColimits (modulePullback V.ι.toLRSHom.toShHom)] :
    IsIso (Stacks.Cohomology.BaseChange.derived (modulePushforward q.toLRSHom.toShHom)
      (modulePushforward (q ∣_ V).toLRSHom.toShHom) (modulePullback V.ι.toLRSHom.toShHom)
      (modulePullback (q ⁻¹ᵁ V).ι.toLRSHom.toShHom)
      (baseChangeNatTrans (AffineBaseChange.restrictSquare q V))
      (asIso (modulePullback V.ι.toLRSHom.toShHom).rightDerivedFunctorPlusUnith)) := by
  let := preservesInjectiveObjects_modulePullback_opensι (q ⁻¹ᵁ V)
  have : ∀ M, IsIso ((baseChangeNatTrans (AffineBaseChange.restrictSquare q V)).app M) :=
    fun M => AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare q V M
  have : IsIso (baseChangeNatTrans (AffineBaseChange.restrictSquare q V)) :=
    NatIso.isIso_of_isIso_app _
  exact Stacks.Cohomology.BaseChange.isIso_derived _ _ _ _ _ _

/-! ### Shrinking the base of the source to an affine open -/

/-- **The comparison of the rectangle over `V ⟶ S` is invertible once the comparison of the
restricted square over `V ⟶ U` is.**  The rectangle obtained from the original square by
restricting the base to `V` is the composite of the restriction square of `f` over `U`, which
carries no coefficients, and the restricted square over `V ⟶ U`; the pasting law of
`PastingBaseChange.lean` expresses its comparison as a four-fold composite whose factors other
than the restricted square's comparison are invertible. -/
private theorem isIso_derivedComparison_restrictedRectangle (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (U : S.Opens) (V : S'.Opens) (hUV : V ≤ g ⁻¹ᵁ U)
    (hUVle : f' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U))
    (HV : IsPullback (g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hUVle) (f' ∣_ V) (f ∣_ U)
      (g.resLE U V hUV))
    [((modulePullback V.ι.toLRSHom.toShHom).obj G).IsQuasicoherent]
    (hflatS : AlgebraicGeometry.IsFlatOver (V.ι ≫ g).toLRSHom.toShHom
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (hflatU : AlgebraicGeometry.IsFlatOver (g.resLE U V hUV).toLRSHom.toShHom
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (hflatSU : AlgebraicGeometry.IsFlatOver (g.resLE U V hUV ≫ U.ι).toLRSHom.toShHom
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (hone : IsIso ((derivedComparison ((modulePullback V.ι.toLRSHom.toShHom).obj G)
      HV.w hflatU).app
      ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u}
          (structureSheafRing (f ⁻¹ᵁ U).toScheme.toRingedSpace)) 0).obj
        ((modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj F)))) :
    IsIso ((derivedComparison ((modulePullback V.ι.toLRSHom.toShHom).obj G)
      (FlatBaseChangeCohomology.pasteBase H.w (AffineBaseChange.restrictSquare f' V))
      hflatS).app ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  let := preservesFiniteLimits_modulePullback_opensι U
  let := preservesFiniteColimits_modulePullback_opensι U
  let := preservesFiniteLimits_modulePullback_opensι (f ⁻¹ᵁ U)
  let := preservesFiniteColimits_modulePullback_opensι (f ⁻¹ᵁ U)
  let := preservesFiniteLimits_baseCoefficients (g.resLE U V hUV)
    ((modulePullback V.ι.toLRSHom.toShHom).obj G) hflatU
  let := preservesFiniteColimits_baseCoefficients (g.resLE U V hUV)
    ((modulePullback V.ι.toLRSHom.toShHom).obj G) hflatU
  let := preservesFiniteLimits_baseCoefficients (g.resLE U V hUV ≫ U.ι)
    ((modulePullback V.ι.toLRSHom.toShHom).obj G) hflatSU
  let := preservesFiniteColimits_baseCoefficients (g.resLE U V hUV ≫ U.ι)
    ((modulePullback V.ι.toLRSHom.toShHom).obj G) hflatSU
  let := preservesFiniteLimits_totalCoefficients HV
    ((modulePullback V.ι.toLRSHom.toShHom).obj G) hflatU
  let := preservesFiniteColimits_totalCoefficients HV
    ((modulePullback V.ι.toLRSHom.toShHom).obj G) hflatU
  have := isIso_derived_baseChangeNatTrans_restrictSquare f U
  refine isIso_derivedComparison_app_congr (Scheme.Hom.resLE_comp_ι g hUV)
    (Scheme.Hom.resLE_comp_ι g' hUVle) ((modulePullback V.ι.toLRSHom.toShHom).obj G)
    (FlatBaseChangeCohomology.pasteBase (AffineBaseChange.restrictSquare f U) HV.w) hflatSU
    (FlatBaseChangeCohomology.pasteBase H.w (AffineBaseChange.restrictSquare f' V)) hflatS
    _ ?_
  refine isIso_app_of_natTrans_eq
    (derivedComparison_eq_derivedPasteBaseChange (AffineBaseChange.restrictSquare f U) HV.w
      ((modulePullback V.ι.toLRSHom.toShHom).obj G) hflatSU) _ ?_
  refine isIso_derivedPaste_app (modulePushforward f.toLRSHom.toShHom)
    (modulePushforward (f ∣_ U).toLRSHom.toShHom)
    (modulePushforward (f' ∣_ V).toLRSHom.toShHom) (modulePullback U.ι.toLRSHom.toShHom)
    (baseCoefficients (g.resLE U V hUV) ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (baseCoefficients (g.resLE U V hUV ≫ U.ι)
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom)
    (totalCoefficients (g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hUVle) (f' ∣_ V)
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (totalCoefficients (g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hUVle ≫ (f ⁻¹ᵁ U).ι) (f' ∣_ V)
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (baseCoefficientsCompIso U.ι (g.resLE U V hUV)
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (totalCoefficientsCompIso (f ⁻¹ᵁ U).ι (g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hUVle) (f' ∣_ V)
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (baseChangeNatTrans (AffineBaseChange.restrictSquare f U))
    (underivedComparison HV.w ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    _ inferInstance ?_
  exact (CategoryTheory.NatTrans.isIso_app_iff_of_iso
    (derivedComparison ((modulePullback V.ι.toLRSHom.toShHom).obj G) HV.w hflatU)
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom) 0).app F)).mp hone

/-! ### Shrinking the base of the target to an open -/

/-- **The derived inverse image along `V.ι` of the comparison is invertible once the comparison
of the rectangle over `V ⟶ S` is.**  The pasting law of `Pasting.lean`, applied with the
left-hand square the restriction square of `f'` over `V`, expresses the rectangle's comparison as
a four-fold composite whose factors other than that derived inverse image are invertible. -/
private theorem isIso_map_derivedComparison_of_restrictedRectangle (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (V : S'.Opens)
    (hflatS : AlgebraicGeometry.IsFlatOver (V.ι ≫ g).toLRSHom.toShHom
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (hrect : IsIso ((derivedComparison ((modulePullback V.ι.toLRSHom.toShHom).obj G)
      (FlatBaseChangeCohomology.pasteBase H.w (AffineBaseChange.restrictSquare f' V))
      hflatS).app ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F))) :
    IsIso ((modulePullback V.ι.toLRSHom.toShHom).rightDerivedFunctorPlus.map
      ((derivedComparison G H.w hG).app
        ((DerivedCategory.Plus.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F))) := by
  let := preservesFiniteLimits_baseCoefficients g G hG
  let := preservesFiniteColimits_baseCoefficients g G hG
  let := preservesFiniteLimits_modulePullback_opensι V
  let := preservesFiniteColimits_modulePullback_opensι V
  let := preservesFiniteLimits_modulePullback_opensι (f' ⁻¹ᵁ V)
  let := preservesFiniteColimits_modulePullback_opensι (f' ⁻¹ᵁ V)
  let := preservesFiniteLimits_baseCoefficients (V.ι ≫ g)
    ((modulePullback V.ι.toLRSHom.toShHom).obj G) hflatS
  let := preservesFiniteColimits_baseCoefficients (V.ι ≫ g)
    ((modulePullback V.ι.toLRSHom.toShHom).obj G) hflatS
  have := isIso_derived_baseChangeNatTrans_restrictSquare f' V
  exact isIso_map_derived_of_isIso_derivedPaste_app (modulePushforward f.toLRSHom.toShHom)
    (modulePushforward f'.toLRSHom.toShHom)
    (modulePushforward (f' ∣_ V).toLRSHom.toShHom) (baseCoefficients g G)
    (modulePullback V.ι.toLRSHom.toShHom)
    (baseCoefficients (V.ι ≫ g) ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (totalCoefficients g' f' G) (modulePullback (f' ⁻¹ᵁ V).ι.toLRSHom.toShHom)
    (totalCoefficients ((f' ⁻¹ᵁ V).ι ≫ g') (f' ∣_ V)
      ((modulePullback V.ι.toLRSHom.toShHom).obj G))
    (baseCoefficientsPullbackIso g V.ι G)
    (totalCoefficientsPullbackIso g' (AffineBaseChange.restrictSquare f' V) G)
    (underivedComparison H.w G) (baseChangeNatTrans (AffineBaseChange.restrictSquare f' V))
    ((DerivedCategory.Plus.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    (isIso_app_of_natTrans_eq
      (derivedComparison_eq_derivedPaste H.w (AffineBaseChange.restrictSquare f' V) G
        hflatS).symm _ hrect)
    inferInstance

/-! ### Locality on the base -/

/-- **The derived comparison of [Stacks, Tag 0GN5] is local on the base.**  Let `G` be a
quasi-coherent `𝒪_{S'}`-module flat over `S` and let `F` be an `𝒪_X`-module.  Suppose that for
every affine open `U` of `S` and every affine open `V` of `S'` contained in `g ⁻¹ᵁ U` the derived
comparison of the restricted cartesian square

```
f' ⁻¹ᵁ V -----> f ⁻¹ᵁ U
    |              |
    v              v
    V    ------->  U
```

at the coefficient module `V.ι ^* G` is invertible at the inverse image of `F` along
`(f ⁻¹ᵁ U).ι`, placed in degree zero.  Then the derived comparison of the original square is
invertible at `F[0]`. -/
theorem isIso_derivedComparison_app_single_of_affineBases (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hres : ∀ (U : S.Opens) (V : S'.Opens), IsAffineOpen U → IsAffineOpen V →
      ∀ (hUV : V ≤ g ⁻¹ᵁ U) (e : f' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U))
        (HV : IsPullback (g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) e) (f' ∣_ V) (f ∣_ U)
          (g.resLE U V hUV))
        (hGV : AlgebraicGeometry.IsFlatOver (g.resLE U V hUV).toLRSHom.toShHom
          ((modulePullback V.ι.toLRSHom.toShHom).obj G)),
        IsIso ((derivedComparison ((modulePullback V.ι.toLRSHom.toShHom).obj G) HV.w hGV).app
          ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u}
              (structureSheafRing (f ⁻¹ᵁ U).toScheme.toRingedSpace)) 0).obj
            ((modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj F)))) :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  refine isIso_of_isIso_derivedPullback _ (fun p : AffinePair g => p.1.2)
    (isOpenCover_affinePairs g) ?_
  rintro ⟨⟨U, V⟩, hU, hV, hUV⟩
  change IsIso ((modulePullback V.ι.toLRSHom.toShHom).rightDerivedFunctorPlus.map
    ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)))
  -- The inclusion of `f' ⁻¹ᵁ V` into `X` factors through `f ⁻¹ᵁ U`.
  have hpre : f' ⁻¹ᵁ (g ⁻¹ᵁ U) = g' ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    change (f' ≫ g) ⁻¹ᵁ U = (g' ≫ f) ⁻¹ᵁ U
    rw [H.w]
  have hUVle : f' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U) := hpre ▸ f'.preimage_mono hUV
  -- The restricted square is cartesian.
  have HV : IsPullback (g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hUVle) (f' ∣_ V) (f ∣_ U)
      (g.resLE U V hUV) := by
    have hpb := Scheme.Hom.isPullback_resLE H hUV (le_refl (f ⁻¹ᵁ U))
      (UY := f' ⁻¹ᵁ V) (inf_eq_right.mpr hUVle).symm
    rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict] at hpb
    exact hpb
  -- The three flatness statements for the inverse image of `G` along `V.ι`.
  have : ((modulePullback V.ι.toLRSHom.toShHom).obj G).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ G
  have hflatS : AlgebraicGeometry.IsFlatOver (V.ι ≫ g).toLRSHom.toShHom
      ((modulePullback V.ι.toLRSHom.toShHom).obj G) := fun p =>
    (AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt V.ι g G p
      (Flat.stalkMap V.ι p)).mp (hG _)
  have hflatU : AlgebraicGeometry.IsFlatOver (g.resLE U V hUV).toLRSHom.toShHom
      ((modulePullback V.ι.toLRSHom.toShHom).obj G) :=
    (AlgebraicGeometry.isFlatOver_iff_of_moduleIso _
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app G)).mp
      (AlgebraicGeometry.isFlatOver_resLE G hG V U hUV)
  have hflatSU : AlgebraicGeometry.IsFlatOver (g.resLE U V hUV ≫ U.ι).toLRSHom.toShHom
      ((modulePullback V.ι.toLRSHom.toShHom).obj G) := by
    rw [Scheme.Hom.resLE_comp_ι]
    exact hflatS
  exact isIso_map_derivedComparison_of_restrictedRectangle H G hG F V hflatS
    (isIso_derivedComparison_restrictedRectangle H G F U V hUV hUVle HV hflatS hflatU hflatSU
      (hres U V hU hV hUV hUVle HV hflatU))

/-! ### Tag 0GN5 in derived form over an arbitrary base -/

/-- **The derived comparison of [Stacks, Tag 0GN5] is invertible at `F[0]` for a quasi-compact
separated morphism over an arbitrary base.**  The restriction `f ∣_ U` of `f` over an affine open
`U` of `S` is again quasi-compact and separated and its target is affine, so the affine-base case
applies to every restricted square; locality on the base does the rest. -/
theorem isIso_derivedComparison_app_single_of_isSeparated' (H : IsPullback g' f' f g)
    [QuasiCompact f] [IsSeparated f]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  refine isIso_derivedComparison_app_single_of_affineBases H G hG F ?_
  intro U V hU hV hUV e HV hGV
  have : IsAffine U.toScheme := hU
  have : ((modulePullback V.ι.toLRSHom.toShHom).obj G).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ G
  have : ((modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj F).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ F
  exact isIso_derivedComparison_app_single_of_isSeparated HV _ hGV _

/-- **The derived comparison of [Stacks, Tag 0GN5] is invertible at `F[0]` for a morphism with
affine source over a quasi-separated base.**  An affine scheme is a compact space and is
separated, so such a morphism is quasi-compact and separated. -/
theorem isIso_derivedComparison_app_single_of_isAffine_source (H : IsPullback g' f' f g)
    [IsAffine X] [QuasiSeparatedSpace ↥S]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) :=
  isIso_derivedComparison_app_single_of_isSeparated' H G hG F

end Stacks.AlgebraicGeometry.ModuleBaseChange

end

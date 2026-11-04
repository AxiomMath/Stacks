module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategoryCocycle
import StacksCore.Tactic.StacksAttribute

/-!
# Extending a perfect object with a map into a quasi-coherent object, with support

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, `W ⊆ X` a
quasi-compact open subspace, `T ⊆ |X|` a closed subset whose open complement has quasi-compact
inclusion, `E` an object of `D_QCoh(𝒪_X)` and `α : P ⟶ E|_W` a morphism from a perfect object
`P` of `D(𝒪_W)` supported on `T ∩ |W|`. Then there is a morphism `β : R ⟶ E` from a perfect
object `R` of `D(𝒪_X)` supported on `T` such that `P` is a direct summand of `R|_W`, compatibly
with `α` and `β|_W` (Stacks 09IV).

## Main definitions

* `CategoryTheory.IsFiniteSumOfPositiveShifts P C`: `C` is a finite direct sum of objects
  `P⟦k⟧` with `k ≥ 1`, that is, `C ≅ P^{⊕ n₁}[1] ⊕ ⋯ ⊕ P^{⊕ nₘ}[m]`.
* `AlgebraicGeometry.Space.derivedEtaleRestrictComp`: restricting along `g` and then along `f`
  is restricting along `f ≫ g`, on unbounded derived categories.

## Main results

* `AlgebraicGeometry.Space.derivedEtaleRestrictComp_cocycle` and
  `AlgebraicGeometry.Space.derivedEtaleRestrictComp_hom_app_of_eq_id`: the associativity and unit
  laws of these comparisons.
* `AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts`:
  the construction of the proof, with the shape it produces:
  `R|_W ≅ P ⊕ C` with `C ≅ P^{⊕ n₁}[1] ⊕ ⋯ ⊕ P^{⊕ nₘ}[m]` and `β|_W` equal to `α` on `P` and
  to zero on `C`. This is the shape Stacks 09IW reads off the proof.
* `AlgebraicGeometry.Space.exists_isPerfect_retract_restrict_of_supported`: **Stacks 09IV**.

## Implementation notes

The proof is the source's. The induction principle of Stacks 09IT, on the quasi-compact open
subspaces `D` of `X` containing `W`, reduces the statement to an elementary distinguished square
`(W₁ ⊆ W₂, f : V ⟶ W₂)` with `V` affine. There
`AlgebraicGeometry.Space.exists_glued_approximation` produces, from a perfect `R₁` on `W₁`
supported on `T` with a morphism `R₁ ⟶ E|_{W₁}`, a perfect `R₂` on `W₂` supported on `T` with
`R₂|_{W₁} ≅ R₁ ⊕ R₁[1]` and a morphism `R₂ ⟶ E|_{W₂}` restricting to the given one on the
first summand and to zero on the second: Stacks 08EK and 08EH on `V` read through Stacks 071Q
(`AlgebraicGeometry.Space.supportedLiftProperty_edsSnd`), glued by Stacks 08HB. If
`R₁|_W ≅ P ⊕ C` then `R₂|_W ≅ (P ⊕ C) ⊕ (P ⊕ C)[1] ≅ P ⊕ (C ⊕ (P ⊕ C)[1])`, and the
complementary summand is again a finite sum of positive shifts of `P`.

"`P` is a direct summand of `R|_W` compatibly with `α` and `β|_W`" is read as: there are
`s : P ⟶ R|_W` and `r : R|_W ⟶ P` with `s ≫ r = 𝟙 P` and `s ≫ β|_W = α`. Support on `T ∩ |W|`
is support on the inverse image of `T` in `|W|`. Restriction to an open subspace is étale
restriction of modules along its inclusion, `AlgebraicGeometry.Space.openSubspaceHom`.

Tracking `β` through the induction needs the identifications of iterated restrictions to be
coherent, which is what the cocycle and unit laws of
`AlgebraicGeometry.Space.derivedEtaleRestrictComp` provide; they are the chain-level identities
`SheafOfModules.pushforwardComp`, read on derived categories through
`Dualizing.mapDerivedCategoryCompNatIso_cocycle` and
`Dualizing.mapDerivedCategoryCompNatIso_hom_app_of_unit`.

## References

* [Stacks Project, Tag 09IV](https://stacks.math.columbia.edu/tag/09IV)
* [Stacks Project, Tag 09IW](https://stacks.math.columbia.edu/tag/09IW)
* [Stacks Project, Tag 09IT](https://stacks.math.columbia.edu/tag/09IT)
* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe u

/-! ### Finite sums of positive shifts -/

namespace CategoryTheory

section Shifts

variable {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D] [HasShift D ℤ]

/-- `C` is a finite direct sum of objects `P⟦k⟧` with `k ≥ 1`: either `C` is zero, or
`C ≅ A ⊞ P⟦k + 1⟧` for some natural number `k` and some `A` which is itself such a sum. Up to
reordering the summands this says `C ≅ P^{⊕ n₁}⟦1⟧ ⊕ ⋯ ⊕ P^{⊕ nₘ}⟦m⟧` for some `m ≥ 0` and
`n_j ≥ 0`. -/
inductive IsFiniteSumOfPositiveShifts (P : D) : D → Prop
  | zero {Z : D} : IsZero Z → IsFiniteSumOfPositiveShifts P Z
  | add {A Z : D} (k : ℕ) : IsFiniteSumOfPositiveShifts P A →
      Nonempty (Z ≅ A ⊞ P⟦(k : ℤ) + 1⟧) → IsFiniteSumOfPositiveShifts P Z

namespace IsFiniteSumOfPositiveShifts

variable {P : D}

/-- An object isomorphic to a finite sum of positive shifts of `P` is one. -/
theorem of_iso {A Z : D} (h : IsFiniteSumOfPositiveShifts P A) (e : A ≅ Z) :
    IsFiniteSumOfPositiveShifts P Z := by
  cases h with
  | zero hA => exact zero (hA.of_iso e.symm)
  | add k h' e' => exact add k h' ⟨e.symm ≪≫ e'.some⟩

/-- The biproduct with a zero object on the right is the object itself. -/
def biprodIsoOfIsZeroRight (A : D) {Z : D} (hZ : IsZero Z) : A ⊞ Z ≅ A where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := by
    rw [← biprod.total, hZ.eq_of_tgt biprod.snd 0]
    simp
  inv_hom_id := biprod.inl_fst

/-- The biproduct of two finite sums of positive shifts of `P` is one. -/
theorem biprod {A B : D} (hA : IsFiniteSumOfPositiveShifts P A)
    (hB : IsFiniteSumOfPositiveShifts P B) : IsFiniteSumOfPositiveShifts P (A ⊞ B) := by
  induction hB with
  | zero hZ => exact hA.of_iso (biprodIsoOfIsZeroRight A hZ).symm
  | @add B' Z k _ e ih =>
    exact add k ih ⟨biprod.mapIso (Iso.refl A) e.some ≪≫ (biprod.associator A B' _).symm⟩

/-- `P⟦1⟧` is a finite sum of positive shifts of `P`. -/
theorem shift_one_self [HasZeroObject D] : IsFiniteSumOfPositiveShifts P (P⟦(1 : ℤ)⟧) :=
  add 0 (zero (isZero_zero D))
    ⟨(biprodIsoOfIsZeroRight _ (isZero_zero D)).symm ≪≫ biprod.braiding _ _ ≪≫
      biprod.mapIso (Iso.refl _) (eqToIso (by simp))⟩

variable [∀ n : ℤ, (shiftFunctor D n).Additive]

/-- The shift `A⟦1⟧` of a finite sum of positive shifts of `P` is one. -/
theorem shift_one {A : D} (hA : IsFiniteSumOfPositiveShifts P A) :
    IsFiniteSumOfPositiveShifts P (A⟦(1 : ℤ)⟧) := by
  induction hA with
  | zero hZ => exact zero ((shiftFunctor D (1 : ℤ)).map_isZero hZ)
  | @add A' Z k _ e ih =>
    have : PreservesBinaryBiproducts (shiftFunctor D (1 : ℤ)) :=
      preservesBinaryBiproducts_of_preservesBiproducts _
    refine add (k + 1) ih ⟨(shiftFunctor D (1 : ℤ)).mapIso e.some ≪≫
      (shiftFunctor D (1 : ℤ)).mapBiprod _ _ ≪≫ biprod.mapIso (Iso.refl _)
        ((shiftFunctorAdd' D ((k : ℤ) + 1) 1 (((k + 1 : ℕ) : ℤ) + 1) (by push_cast; ring)).symm.app
          P)⟩

/-- **The inductive step of the shape.** If `C` is a finite sum of positive shifts of `P`, so is
`C ⊞ (P ⊞ C)⟦1⟧`. -/
theorem biprod_shift_biprod [HasZeroObject D] {C : D} (hC : IsFiniteSumOfPositiveShifts P C) :
    IsFiniteSumOfPositiveShifts P (C ⊞ (P ⊞ C)⟦(1 : ℤ)⟧) := by
  have : PreservesBinaryBiproducts (shiftFunctor D (1 : ℤ)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact hC.biprod ((shift_one_self.biprod hC.shift_one).of_iso
    ((shiftFunctor D (1 : ℤ)).mapBiprod _ _).symm)

end IsFiniteSumOfPositiveShifts

end Shifts

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {B S hS}

/-! ### Iterated étale restriction on derived categories -/

/-- **Derived étale restriction along a composite.** For étale `f : X ⟶ Y`, `g : Y ⟶ Z` and
`k = f ≫ g`, restricting along `g` and then along `f` is restricting along `k`, on unbounded
derived categories. -/
def derivedEtaleRestrictComp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hk : IsEtale B S hS k.hom) (h : f ≫ g = k) :
    (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory ⋙
        (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory ≅
      (etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory :=
  Dualizing.mapDerivedCategoryCompNatIso _ _ _
    (etaleModulePullbackCompIso B S hS f g hf hg (isEtale_comp B S hS hf hg) ≪≫
      eqToIso (etaleModulePullback_congr B S hS _ hk h))

/-- **The cocycle law for iterated derived étale restriction**: for `f₁ : A ⟶ B`, `f₂ : B ⟶ C`,
`f₃ : C ⟶ D`, the two identifications of restricting along `f₃`, `f₂`, `f₁` in turn with
restricting along `f₁ ≫ f₂ ≫ f₃` agree. -/
theorem derivedEtaleRestrictComp_cocycle {A₁ A₂ A₃ A₄ : AlgebraicSpaces B S hS}
    (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄) (k₁₂ : A₁ ⟶ A₃) (k₂₃ : A₂ ⟶ A₄)
    (k : A₁ ⟶ A₄) (hf₁ : IsEtale B S hS f₁.hom) (hf₂ : IsEtale B S hS f₂.hom)
    (hf₃ : IsEtale B S hS f₃.hom) (hk₁₂ : IsEtale B S hS k₁₂.hom)
    (hk₂₃ : IsEtale B S hS k₂₃.hom) (hk : IsEtale B S hS k.hom)
    (h₁₂ : f₁ ≫ f₂ = k₁₂) (h₂₃ : f₂ ≫ f₃ = k₂₃) (h : k₁₂ ≫ f₃ = k) (h' : f₁ ≫ k₂₃ = k)
    (K : DerivedCategory (Modules.{u, u} B S hS A₄.1 A₄.2)) :
    (etaleModulePullback.{u, u} B S hS f₁ hf₁).mapDerivedCategory.map
        ((derivedEtaleRestrictComp f₂ f₃ k₂₃ hf₂ hf₃ hk₂₃ h₂₃).hom.app K) ≫
      (derivedEtaleRestrictComp f₁ k₂₃ k hf₁ hk₂₃ hk h').hom.app K =
    (derivedEtaleRestrictComp f₁ f₂ k₁₂ hf₁ hf₂ hk₁₂ h₁₂).hom.app
        ((etaleModulePullback.{u, u} B S hS f₃ hf₃).mapDerivedCategory.obj K) ≫
      (derivedEtaleRestrictComp k₁₂ f₃ k hk₁₂ hf₃ hk h).hom.app K := by
  refine Dualizing.mapDerivedCategoryCompNatIso_cocycle _ _ _ _ _ _ _ _ _ _ (fun M => ?_) K
  subst h₁₂ h₂₃ h
  rfl

/-- The lift to derived categories of the unit law `etaleModulePullbackIdIso` along a morphism
equal to the identity. -/
def derivedEtaleRestrictIdIso {X : AlgebraicSpaces B S hS} (f : X ⟶ X) (hf : IsEtale B S hS f.hom)
    (h : f = 𝟙 X) :
    (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory ≅ 𝟭 _ :=
  Dualizing.mapDerivedCategoryIdNatIso _
    (eqToIso (etaleModulePullback_congr B S hS hf (h ▸ hf) h) ≪≫ etaleModulePullbackIdIso B S hS _)

/-- **The unit law for iterated derived étale restriction, on the left**: when the first map is
the identity, the identification of the iterated restriction is the unit law at the
restriction. -/
theorem derivedEtaleRestrictComp_hom_app_of_eq_id {X Y : AlgebraicSpaces B S hS} (f : X ⟶ X)
    (g : X ⟶ Y) (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom) (hfid : f = 𝟙 X)
    (h : f ≫ g = g) (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    (derivedEtaleRestrictComp f g g hf hg hg h).hom.app K =
      (derivedEtaleRestrictIdIso f hf hfid).hom.app
        ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj K) := by
  refine Dualizing.mapDerivedCategoryCompNatIso_hom_app_of_unit _ _ _ _ (fun M => ?_) K
  subst hfid
  rfl

/-- **The unit law for iterated derived étale restriction, on the right**: when the second map
is the identity, the identification of the iterated restriction is the restriction of the unit
law. -/
theorem derivedEtaleRestrictComp_hom_app_of_eq_id' {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Y) (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom) (hgid : g = 𝟙 Y)
    (h : f ≫ g = f) (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    (derivedEtaleRestrictComp f g f hf hg hf h).hom.app K =
      (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.map
        ((derivedEtaleRestrictIdIso g hg hgid).hom.app K) := by
  refine Dualizing.mapDerivedCategoryCompNatIso_hom_app_of_unit' _ _ _ _ (fun M => ?_) K
  subst hgid
  rfl

/-! ### Iterated restriction, objectwise -/

/-- Étale restriction on unbounded derived categories, `K ↦ K|_X` along an étale `f : X ⟶ Y`. -/
abbrev etaleDerivedRestrict {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
  (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory

/-- `AlgebraicGeometry.Space.derivedEtaleRestrictComp` at an object: `(K|_Y)|_X ≅ K|_X` for
`f ≫ g = k`. -/
def derivedEtaleRestrictCompApp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hk : IsEtale B S hS k.hom) (h : f ≫ g = k)
    (K : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :
    (etaleDerivedRestrict f hf).obj ((etaleDerivedRestrict g hg).obj K) ≅
      (etaleDerivedRestrict k hk).obj K :=
  (derivedEtaleRestrictComp f g k hf hg hk h).app K

/-- The isomorphisms `derivedEtaleRestrictCompApp` are natural in the object `K`. -/
@[reassoc]
theorem derivedEtaleRestrictCompApp_naturality {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (k : X ⟶ Z) (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hk : IsEtale B S hS k.hom) (h : f ≫ g = k)
    {K K' : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)} (φ : K ⟶ K') :
    (etaleDerivedRestrict f hf).map ((etaleDerivedRestrict g hg).map φ) ≫
        (derivedEtaleRestrictCompApp f g k hf hg hk h K').hom =
      (derivedEtaleRestrictCompApp f g k hf hg hk h K).hom ≫ (etaleDerivedRestrict k hk).map φ :=
  (derivedEtaleRestrictComp f g k hf hg hk h).hom.naturality φ

/-- The cocycle law `derivedEtaleRestrictComp_cocycle`, stated objectwise in terms of
`derivedEtaleRestrictCompApp`. -/
@[reassoc]
theorem derivedEtaleRestrictCompApp_cocycle {A₁ A₂ A₃ A₄ : AlgebraicSpaces B S hS}
    (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄) (k₁₂ : A₁ ⟶ A₃) (k₂₃ : A₂ ⟶ A₄)
    (k : A₁ ⟶ A₄) (hf₁ : IsEtale B S hS f₁.hom) (hf₂ : IsEtale B S hS f₂.hom)
    (hf₃ : IsEtale B S hS f₃.hom) (hk₁₂ : IsEtale B S hS k₁₂.hom)
    (hk₂₃ : IsEtale B S hS k₂₃.hom) (hk : IsEtale B S hS k.hom)
    (h₁₂ : f₁ ≫ f₂ = k₁₂) (h₂₃ : f₂ ≫ f₃ = k₂₃) (h : k₁₂ ≫ f₃ = k) (h' : f₁ ≫ k₂₃ = k)
    (K : DerivedCategory (Modules.{u, u} B S hS A₄.1 A₄.2)) :
    (etaleDerivedRestrict f₁ hf₁).map
        (derivedEtaleRestrictCompApp f₂ f₃ k₂₃ hf₂ hf₃ hk₂₃ h₂₃ K).hom ≫
        (derivedEtaleRestrictCompApp f₁ k₂₃ k hf₁ hk₂₃ hk h' K).hom =
      (derivedEtaleRestrictCompApp f₁ f₂ k₁₂ hf₁ hf₂ hk₁₂ h₁₂
          ((etaleDerivedRestrict f₃ hf₃).obj K)).hom ≫
        (derivedEtaleRestrictCompApp k₁₂ f₃ k hk₁₂ hf₃ hk h K).hom :=
  derivedEtaleRestrictComp_cocycle f₁ f₂ f₃ k₁₂ k₂₃ k hf₁ hf₂ hf₃ hk₁₂ hk₂₃ hk h₁₂ h₂₃ h h' K

/-- The inverse of `derivedEtaleRestrictCompApp` followed by it is the identity. -/
@[reassoc (attr := simp)]
theorem derivedEtaleRestrictCompApp_inv_hom {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (k : X ⟶ Z) (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hk : IsEtale B S hS k.hom) (h : f ≫ g = k)
    (K : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :
    (derivedEtaleRestrictCompApp f g k hf hg hk h K).inv ≫
      (derivedEtaleRestrictCompApp f g k hf hg hk h K).hom = 𝟙 _ :=
  Iso.inv_hom_id _

/-! ### Inclusions of open subspaces -/

/-- The inclusion `W ⟶ D` of an open subspace into a larger one, as a morphism of algebraic
spaces. -/
def openSubspaceInclusion {X : AlgebraicSpaces B S hS} {W D : Subfunctor X.1}
    (hW : IsOpenSubspace B S hS W) (hD : IsOpenSubspace B S hS D) (h : W ≤ D) :
    openSubspaceSpace B S hS W hW ⟶ openSubspaceSpace B S hS D hD :=
  ObjectProperty.homMk (Subfunctor.homOfLe h)

/-- The inclusion of an open subspace into a larger open subspace is étale. -/
theorem isEtale_openSubspaceInclusion {X : AlgebraicSpaces B S hS} {W D : Subfunctor X.1}
    (hW : IsOpenSubspace B S hS W) (hD : IsOpenSubspace B S hS D) (h : W ≤ D) :
    IsEtale B S hS (openSubspaceInclusion hW hD h).hom :=
  isEtale_of_comp_mono B S hS (Subfunctor.homOfLe h) D.ι (by
    rw [Subfunctor.homOfLe_ι]
    exact isEtale_of_isOpenImmersion B S hS hW.2)

/-- The inclusion `W ⟶ D` followed by the inclusion of `D` into `X` is the inclusion of `W`
into `X`. -/
@[reassoc]
theorem openSubspaceInclusion_comp {X : AlgebraicSpaces B S hS} {W D : Subfunctor X.1}
    (hW : IsOpenSubspace B S hS W) (hD : IsOpenSubspace B S hS D) (h : W ≤ D) :
    openSubspaceInclusion hW hD h ≫ openSubspaceHom B S hS D hD = openSubspaceHom B S hS W hW :=
  ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι h)

/-! ### The induction -/

/-- Étale restriction along `f` carries an object supported over `T` on `Y` to one supported on
any `T'` containing the points of `A` whose image under `k = f ≫ ι` lies in `T`. -/
private theorem cohomologySupportedOn_restrict_of_comp_eq {X Y A : AlgebraicSpaces B S hS}
    (f : A ⟶ Y) (hf : IsEtale B S hS f.hom) (ι : Y ⟶ X) (k : A.1 ⟶ X.1) (hk : f.hom ≫ ι.hom = k)
    {T : Set (points B S hS X.1)} {T' : Set (points B S hS A.1)}
    (hT : ∀ x, pointsMap B S hS _ k x ∈ T → x ∈ T')
    {R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)}
    (hR : CohomologySupportedOn B S hS Y.1 Y.2 (pointsMap B S hS Y.1 ι.hom ⁻¹' T) R) :
    CohomologySupportedOn B S hS A.1 A.2 T' ((etaleDerivedRestrict f hf).obj R) := by
  subst hk
  exact fun i x hx => hT x ((pointsMap_comp_apply B S hS f.hom ι.hom x).symm ▸
    cohomologySupportedOn_etaleModulePullback B S hS f hf _ R hR i hx)


attribute [local instance] pointTopology

section Extension

variable {X : AlgebraicSpaces B S hS} {W : Subfunctor X.1} (hW : IsOpenSubspace B S hS W)
  (T : Set (points B S hS X.1)) (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
  (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
    (openSubspaceSpace B S hS W hW).2))
  (α : P ⟶ (etaleDerivedRestrict (openSubspaceHom B S hS W hW)
    (isEtale_openSubspaceHom B S hS W hW)).obj E.obj)

/-- The induction statement for Stacks 09IV at a quasi-compact open `D ⊇ W`: there are a perfect
`R` on `D` supported on `T ∩ |D|`, a morphism `β : R ⟶ E|_D` and an isomorphism
`R|_W ≅ P ⊕ C` with `C` a finite sum of positive shifts of `P`, under which `β|_W` is `α` on `P`
and zero on `C`. -/
def ExtendsSupportedPerfect (D : Subfunctor X.1) : Prop :=
  ∀ (hD : IsOpenSubspace B S hS D) (hWD : W ≤ D),
    ∃ (R : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS D hD).1
        (openSubspaceSpace B S hS D hD).2))
      (β : R ⟶ (etaleDerivedRestrict (openSubspaceHom B S hS D hD)
        (isEtale_openSubspaceHom B S hS D hD)).obj E.obj),
      (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS D hD).1
        (openSubspaceSpace B S hS D hD).2).IsPerfect R ∧
      CohomologySupportedOn B S hS (openSubspaceSpace B S hS D hD).1
        (openSubspaceSpace B S hS D hD).2 (pointsMap B S hS D.toFunctor D.ι ⁻¹' T) R ∧
      ∃ (C : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2))
        (e : (etaleDerivedRestrict (openSubspaceInclusion hW hD hWD)
          (isEtale_openSubspaceInclusion hW hD hWD)).obj R ≅ P ⊞ C),
        IsFiniteSumOfPositiveShifts P C ∧
        (etaleDerivedRestrict (openSubspaceInclusion hW hD hWD)
            (isEtale_openSubspaceInclusion hW hD hWD)).map β ≫
          (derivedEtaleRestrictCompApp (openSubspaceInclusion hW hD hWD)
            (openSubspaceHom B S hS D hD) (openSubspaceHom B S hS W hW)
            (isEtale_openSubspaceInclusion hW hD hWD) (isEtale_openSubspaceHom B S hS D hD)
            (isEtale_openSubspaceHom B S hS W hW)
            (openSubspaceInclusion_comp hW hD hWD) E.obj).hom =
          e.hom ≫ biprod.fst ≫ α

/-- The base case of the induction: on `W` itself, `R = P` and `β = α`. -/
theorem extendsSupportedPerfect_self
    (hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P)
    (hPT : CohomologySupportedOn B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2 (pointsMap B S hS W.toFunctor W.ι ⁻¹' T) P) :
    ExtendsSupportedPerfect hW T E P α W := by
  intro hD hWD
  have hid : openSubspaceInclusion hW hD hWD = 𝟙 _ := ObjectProperty.hom_ext _ rfl
  let τ := derivedEtaleRestrictIdIso (openSubspaceInclusion hW hD hWD)
    (isEtale_openSubspaceInclusion hW hD hWD) hid
  refine ⟨P, α, hP, hPT, 0, τ.app P ≪≫ (IsFiniteSumOfPositiveShifts.biprodIsoOfIsZeroRight P
    (isZero_zero _)).symm, IsFiniteSumOfPositiveShifts.zero (isZero_zero _), ?_⟩
  show (etaleModulePullback.{u, u} B S hS (openSubspaceInclusion hW hD hWD)
      (isEtale_openSubspaceInclusion hW hD hWD)).mapDerivedCategory.map α ≫
    (derivedEtaleRestrictComp (openSubspaceInclusion hW hD hWD)
      (openSubspaceHom B S hS W hD) (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceInclusion hW hD hWD) (isEtale_openSubspaceHom B S hS W hD)
      (isEtale_openSubspaceHom B S hS W hW)
      (openSubspaceInclusion_comp hW hD hWD)).hom.app E.obj = _
  rw [derivedEtaleRestrictComp_hom_app_of_eq_id _ _ _ _ hid]
  have hnat := τ.hom.naturality α
  dsimp only [Functor.id_obj, Functor.id_map] at hnat
  rw [hnat]
  simp [IsFiniteSumOfPositiveShifts.biprodIsoOfIsZeroRight]

/-- **The glueing step, for abstract data.** Let `(U ⊆ W', f : V ⟶ W')` be an elementary
distinguished square, `ι₂ : W' ⟶ X` and `ι₁ : Y₁ ⟶ X` étale with `Y₁ ≅ U` over `X`, and `Z` an
algebraic space mapping to `Y₁` and to `W'` compatibly. Given a perfect `R₁` on `Y₁` supported
over `T`, a morphism `β₁ : R₁ ⟶ E|_{Y₁}` and `R₁|_Z ≅ P ⊕ C₁` under which `β₁|_Z` is `α` on `P`
and zero on `C₁`, and the supported lifting property of `U ×_{W'} V ⟶ V`, there are a perfect
`R₂` on `W'` supported over `T`, a morphism `β₂ : R₂ ⟶ E|_{W'}` and
`R₂|_Z ≅ P ⊕ (C₁ ⊕ (P ⊕ C₁)[1])` under which `β₂|_Z` is `α` on `P` and zero on the rest. -/
theorem exists_glued_extension {X Y₁ Z W' : AlgebraicSpaces B S hS}
    {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W'.1} {fV : Ve ⟶ W'.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W'.2 Uo fV) (T : Set (points B S hS X.1))
    (ι₂ : W' ⟶ X) (hι₂ : IsEtale B S hS ι₂.hom)
    (hlift : SupportedLiftProperty B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹'
        (pointsMap B S hS W'.1 ι₂.hom ⁻¹' T)))
    (ι₁ : Y₁ ⟶ X) (hι₁ : IsEtale B S hS ι₁.hom) (eU : Y₁ ≅ edsOpen B S hS hsq)
    (hUi : IsEtale B S hS eU.inv.hom) (kU : edsOpen B S hS hsq ⟶ X)
    (hkU : IsEtale B S hS kU.hom) (hkUdef : edsOpenHom B S hS hsq ≫ ι₂ = kU)
    (E1 : eU.inv ≫ ι₁ = kU)
    (ιZ : Z ⟶ X) (hιZ : IsEtale B S hS ιZ.hom) (inc₁ : Z ⟶ Y₁) (hinc₁ : IsEtale B S hS inc₁.hom)
    (inc₂ : Z ⟶ W') (hinc₂ : IsEtale B S hS inc₂.hom) (b : Z ⟶ edsOpen B S hS hsq)
    (hb : IsEtale B S hS b.hom) (hbdef : inc₁ ≫ eU.hom = b) (h₁ : inc₁ ≫ ι₁ = ιZ)
    (h₂ : inc₂ ≫ ι₂ = ιZ) (E2 : b ≫ edsOpenHom B S hS hsq = inc₂)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (P : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (α : P ⟶ (etaleDerivedRestrict ιZ hιZ).obj E.obj)
    (R₁ : DerivedCategory (Modules.{u, u} B S hS Y₁.1 Y₁.2))
    (β₁ : R₁ ⟶ (etaleDerivedRestrict ι₁ hι₁).obj E.obj)
    (hR₁ : (smallEtaleRingedSite B S hS Y₁.1 Y₁.2).IsPerfect R₁)
    (hR₁T : CohomologySupportedOn B S hS Y₁.1 Y₁.2 (pointsMap B S hS Y₁.1 ι₁.hom ⁻¹' T) R₁)
    (C₁ : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (e₁ : (etaleDerivedRestrict inc₁ hinc₁).obj R₁ ≅ P ⊞ C₁)
    (hβ₁ : (etaleDerivedRestrict inc₁ hinc₁).map β₁ ≫
        (derivedEtaleRestrictCompApp inc₁ ι₁ ιZ hinc₁ hι₁ hιZ h₁ E.obj).hom =
      e₁.hom ≫ biprod.fst ≫ α) :
    ∃ (R₂ : DerivedCategory (Modules.{u, u} B S hS W'.1 W'.2))
      (β₂ : R₂ ⟶ (etaleDerivedRestrict ι₂ hι₂).obj E.obj),
      (smallEtaleRingedSite B S hS W'.1 W'.2).IsPerfect R₂ ∧
      CohomologySupportedOn B S hS W'.1 W'.2 (pointsMap B S hS W'.1 ι₂.hom ⁻¹' T) R₂ ∧
      ∃ e₂ : (etaleDerivedRestrict inc₂ hinc₂).obj R₂ ≅ P ⊞ (C₁ ⊞ (P ⊞ C₁)⟦(1 : ℤ)⟧),
        (etaleDerivedRestrict inc₂ hinc₂).map β₂ ≫
          (derivedEtaleRestrictCompApp inc₂ ι₂ ιZ hinc₂ hι₂ hιZ h₂ E.obj).hom =
        e₂.hom ≫ biprod.fst ≫ α := by
  have heo : IsEtale B S hS (edsOpenHom B S hS hsq).hom := isEtale_edsOpenHom B S hS hsq
  have E3 : b ≫ eU.inv = inc₁ := by rw [← hbdef]; simp
  have E4 : b ≫ kU = ιZ := by rw [← hkUdef, ← Category.assoc, E2, h₂]
  have hP' := isPerfect_etaleModulePullback_standard B S hS eU.inv hUi R₁ hR₁
  have hP'T : CohomologySupportedOn B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
      (pointsMap B S hS (edsOpen B S hS hsq).1 (edsOpenHom B S hS hsq).hom ⁻¹'
        (pointsMap B S hS W'.1 ι₂.hom ⁻¹' T)) ((etaleDerivedRestrict eU.inv hUi).obj R₁) := by
    refine cohomologySupportedOn_restrict_of_comp_eq eU.inv hUi ι₁
      ((edsOpenHom B S hS hsq).hom ≫ ι₂.hom)
      (congrArg (fun g => g.hom) (E1.trans hkUdef.symm))
      (fun x hx => ?_) hR₁T
    rwa [pointsMap_comp_apply] at hx
  obtain ⟨R₂, φ, f₂, hR₂, hR₂T, hφ⟩ := exists_glued_approximation B S hS hsq
    (pointsMap B S hS W'.1 ι₂.hom ⁻¹' T) hlift
    ⟨(etaleDerivedRestrict ι₂ hι₂).obj E.obj,
      derivedQuasicoherent_etaleModulePullback B S hS ι₂ hι₂ E.obj E.property⟩
    ((etaleDerivedRestrict eU.inv hUi).obj R₁) hP' hP'T
    ((etaleDerivedRestrict eU.inv hUi).map β₁ ≫
      (derivedEtaleRestrictCompApp eU.inv ι₁ kU hUi hι₁ hkU E1 E.obj).hom ≫
      (derivedEtaleRestrictCompApp (edsOpenHom B S hS hsq) ι₂ kU heo hι₂ hkU hkUdef E.obj).inv)
  refine ⟨R₂, φ, hR₂, hR₂T,
    (derivedEtaleRestrictCompApp b (edsOpenHom B S hS hsq) inc₂ hb heo hinc₂ E2 R₂).symm ≪≫
      (etaleDerivedRestrict b hb).mapIso f₂ ≪≫
      mapBiprodShiftIso (etaleDerivedRestrict b hb) ((etaleDerivedRestrict eU.inv hUi).obj R₁) ≪≫
      biprod.mapIso (derivedEtaleRestrictCompApp b eU.inv inc₁ hb hUi hinc₁ E3 R₁ ≪≫ e₁)
        ((shiftFunctor _ (1 : ℤ)).mapIso
          (derivedEtaleRestrictCompApp b eU.inv inc₁ hb hUi hinc₁ E3 R₁ ≪≫ e₁)) ≪≫
      biprod.associator _ _ _, ?_⟩
  have hφ' : (etaleDerivedRestrict (edsOpenHom B S hS hsq) heo).map φ =
      f₂.hom ≫ biprod.fst ≫ (etaleDerivedRestrict eU.inv hUi).map β₁ ≫
        (derivedEtaleRestrictCompApp eU.inv ι₁ kU hUi hι₁ hkU E1 E.obj).hom ≫
        (derivedEtaleRestrictCompApp (edsOpenHom B S hS hsq) ι₂ kU heo hι₂ hkU hkUdef
          E.obj).inv := hφ
  have hF₂φ : (etaleDerivedRestrict inc₂ hinc₂).map φ =
      (derivedEtaleRestrictCompApp b (edsOpenHom B S hS hsq) inc₂ hb heo hinc₂ E2 R₂).inv ≫
        (etaleDerivedRestrict b hb).map ((etaleDerivedRestrict (edsOpenHom B S hS hsq) heo).map φ) ≫
        (derivedEtaleRestrictCompApp b (edsOpenHom B S hS hsq) inc₂ hb heo hinc₂ E2
          ((etaleDerivedRestrict ι₂ hι₂).obj E.obj)).hom := by
    rw [derivedEtaleRestrictCompApp_naturality, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, biprod.mapIso_hom,
    biprod.associator_hom, Category.assoc]
  rw [hF₂φ]
  simp only [Category.assoc]
  simp only [← derivedEtaleRestrictCompApp_cocycle b (edsOpenHom B S hS hsq) ι₂ inc₂ kU ιZ hb heo
    hι₂ hinc₂ hkU hιZ E2 hkUdef h₂ E4 E.obj]
  simp only [hφ', Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  simp only [derivedEtaleRestrictCompApp_cocycle b eU.inv ι₁ inc₁ kU ιZ hb hUi hι₁ hinc₁
    hkU hιZ E3 E1 h₁ E4 E.obj]
  simp only [derivedEtaleRestrictCompApp_naturality_assoc b eU.inv inc₁ hb hUi hinc₁ E3, hβ₁,
    biprod.lift_fst_assoc, biprod.map_fst_assoc, Category.assoc,
    reassoc_of% (mapBiprodShiftIso_hom_fst (etaleDerivedRestrict b hb)
      ((etaleDerivedRestrict eU.inv hUi).obj R₁))]

/-- **The inductive step.** Let `(W₁ ⊆ W₂, f : V ⟶ W₂)` be an elementary distinguished square of
quasi-compact open subspaces of `X` containing `W`, with `V` affine. If the statement holds on
`W₁`, it holds on `W₂`: the perfect object `R₁` on `W₁` and `R₁|_{W₁ ×_{W₂} V}` lifted to `V`
glue to `R₂` with `R₂|_{W₁} ≅ R₁ ⊕ R₁[1]`, and `R₂|_W ≅ P ⊕ (C ⊕ (P ⊕ C)[1])`. -/
theorem extendsSupportedPerfect_step (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    {W₁ W₂ : Subfunctor X.1} (hW₁ : IsOpenSubspace B S hS W₁) (hW₂ : IsOpenSubspace B S hS W₂)
    (hW₁qc : IsQuasiCompactSpace B S hS W₁.toFunctor) (hle : W₁ ≤ W₂) (hWW₁ : W ≤ W₁)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W₂.toFunctor) (hV : IsAffineSpace B S hS V)
    (hsq : IsElementaryDistinguishedSquare B S hS hW₂.1
      (Subfunctor.range (Subfunctor.homOfLe hle)) f)
    (IH : ExtendsSupportedPerfect hW T E P α W₁) :
    ExtendsSupportedPerfect hW T E P α W₂ := by
  intro hW₂' hWW₂
  let Y₁ := openSubspaceSpace B S hS W₁ hW₁
  let Y₂ := openSubspaceSpace B S hS W₂ hW₂'
  let Uo := Subfunctor.range (Subfunctor.homOfLe hle)
  have hsq' : IsElementaryDistinguishedSquare B S hS Y₂.2 Uo f := hsq
  obtain ⟨R₁, β₁, hR₁, hR₁T, C₁, e₁, hC₁, hβ₁⟩ := IH hW₁ hWW₁
  let φU : W₁.toFunctor ≅ Uo.toFunctor := asIso (Subfunctor.toRange (Subfunctor.homOfLe hle))
  let eU : Y₁ ≅ edsOpen B S hS (W := Y₂) hsq' := ObjectProperty.isoMk _ φU
  have hUi : IsEtale B S hS eU.inv.hom := isEtale_of_isIso B S hS φU.inv
  have hUh : IsEtale B S hS eU.hom.hom := isEtale_of_isIso B S hS φU.hom
  have hφU : φU.hom ≫ Uo.ι ≫ W₂.ι = W₁.ι := by
    show Subfunctor.toRange (Subfunctor.homOfLe hle) ≫ Uo.ι ≫ W₂.ι = W₁.ι
    rw [Subfunctor.toRange_ι_assoc, Subfunctor.homOfLe_ι]
  have E1 : eU.inv ≫ openSubspaceHom B S hS W₁ hW₁ =
      edsOpenHom B S hS (W := Y₂) hsq' ≫ openSubspaceHom B S hS W₂ hW₂' := by
    apply ObjectProperty.hom_ext
    show φU.inv ≫ W₁.ι = Uo.ι ≫ W₂.ι
    rw [← hφU, Iso.inv_hom_id_assoc]
  have E2 : (openSubspaceInclusion hW hW₁ hWW₁ ≫ eU.hom) ≫ edsOpenHom B S hS (W := Y₂) hsq' =
      openSubspaceInclusion hW hW₂' hWW₂ := by
    apply ObjectProperty.hom_ext
    refine (cancel_mono W₂.ι).1 ?_
    show Subfunctor.homOfLe hWW₁ ≫ φU.hom ≫ Uo.ι ≫ W₂.ι = Subfunctor.homOfLe hWW₂ ≫ W₂.ι
    rw [hφU, Subfunctor.homOfLe_ι, Subfunctor.homOfLe_ι]
  -- the supported lifting property on the affine member
  let T₂ : Set (points B S hS W₂.toFunctor) := pointsMap B S hS W₂.toFunctor W₂.ι ⁻¹' T
  have hT₂ : IsClosed T₂ := hT.preimage (continuous_pointsMap B S hS _)
  have hT₂qc := isQuasiCompact_openSubspacesOrderIso_symm_preimage B S hS X.2 hW₂'.1 W₂.ι T hT
    hTqc hT₂
  have hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor :=
    IsQuasiCompactSpace.of_iso B S hS hW₁qc φU
  have hW₂qs := isAbsolutelyQuasiSeparated_of_isOpenSubspace B S hS hZ hXqs W₂ hW₂'
  have hUVqc : IsQuasiCompactSpace B S hS (edsInter B S hS (W := Y₂) hsq').1 :=
    isQuasiCompactSpace_pullback B S hS hZ Uo.ι f hsq'.isOpenSubspace.1 Y₂.2 hUqc
      hV.isQuasiCompactSpace hW₂qs
  have hlift := supportedLiftProperty_edsSnd B S hS (W := Y₂) hsq' hV hUVqc T₂ hT₂ hT₂qc
  obtain ⟨R₂, β₂, hR₂, hR₂T, e₂, hβ₂⟩ := exists_glued_extension hsq' T
    (openSubspaceHom B S hS W₂ hW₂') (isEtale_openSubspaceHom B S hS W₂ hW₂') hlift
    (openSubspaceHom B S hS W₁ hW₁) (isEtale_openSubspaceHom B S hS W₁ hW₁) eU hUi
    _ (isEtale_comp B S hS (isEtale_edsOpenHom B S hS (W := Y₂) hsq')
      (isEtale_openSubspaceHom B S hS W₂ hW₂')) rfl E1
    (openSubspaceHom B S hS W hW) (isEtale_openSubspaceHom B S hS W hW)
    (openSubspaceInclusion hW hW₁ hWW₁) (isEtale_openSubspaceInclusion hW hW₁ hWW₁)
    (openSubspaceInclusion hW hW₂' hWW₂) (isEtale_openSubspaceInclusion hW hW₂' hWW₂)
    _ (isEtale_comp B S hS (isEtale_openSubspaceInclusion hW hW₁ hWW₁) hUh) rfl
    (openSubspaceInclusion_comp hW hW₁ hWW₁) (openSubspaceInclusion_comp hW hW₂' hWW₂) E2
    E P α R₁ β₁ hR₁ hR₁T C₁ e₁ hβ₁
  exact ⟨R₂, β₂, hR₂, hR₂T, _, e₂, hC₁.biprod_shift_biprod, hβ₂⟩


end Extension

/-- **The construction of Stacks 09IV, with the shape it produces.** Let `X` be a quasi-compact
and quasi-separated algebraic space over `S`, `W ⊆ X` a quasi-compact open subspace, `T ⊆ |X|` a
closed subset such that `X \ T ⟶ X` is quasi-compact, `E` an object of `D_QCoh(𝒪_X)` and
`α : P ⟶ E|_W` a morphism from a perfect object `P` of `D(𝒪_W)` supported on `T ∩ |W|`. Then
there are a perfect object `R` of `D(𝒪_X)` supported on `T`, a morphism `β : R ⟶ E` and an
isomorphism `R|_W ≅ P ⊕ C` with `C ≅ P^{⊕ n₁}[1] ⊕ ⋯ ⊕ P^{⊕ nₘ}[m]`
(`CategoryTheory.IsFiniteSumOfPositiveShifts`), under which `β|_W` is `α` on `P` and zero on
`C`. This is the shape Stacks 09IW reads off the proof of Stacks 09IV. -/
theorem exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (hWqc : IsQuasiCompactSpace B S hS W.toFunctor) (T : Set (points B S hS X.1))
    (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P)
    (hPT : CohomologySupportedOn B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2 (pointsMap B S hS W.toFunctor W.ι ⁻¹' T) P)
    (α : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj E.obj) :
    ∃ (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (β : R ⟶ E.obj),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R ∧
      CohomologySupportedOn B S hS X.1 X.2 T R ∧
      ∃ (C : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2))
        (e : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R ≅ P ⊞ C),
        IsFiniteSumOfPositiveShifts P C ∧
        (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β =
          e.hom ≫ biprod.fst ≫ α := by
  have htop := isOpenSubspace_top (B := B) (S := S) (hS := hS) X.2
  obtain ⟨R, β, hR, hRT, C, e, hC, hβ⟩ :=
    qcqs_induction_on_enlargement B S hS hZ X hXqc hXqs W hW hWqc
      (ExtendsSupportedPerfect hW T E P α) (extendsSupportedPerfect_self hW T E P α hP hPT)
      (fun W₁ W₂ hW₁ hW₂ hW₁qc _ hle hWW₁ _ f hV hsq IH =>
        extendsSupportedPerfect_step hW T E P α hZ hXqs hT hTqc hW₁ hW₂ hW₁qc hle hWW₁ f hV hsq IH)
      htop le_top
  let φT : (⊤ : Subfunctor X.1).toFunctor ≅ X.1 := asIso (⊤ : Subfunctor X.1).ι
  let eT : openSubspaceSpace B S hS (⊤ : Subfunctor X.1) htop ≅ X := ObjectProperty.isoMk _ φT
  have hTi : IsEtale B S hS eT.inv.hom := isEtale_of_isIso B S hS φT.inv
  have hιW := isEtale_openSubspaceHom B S hS W hW
  have hιT := isEtale_openSubspaceHom B S hS (⊤ : Subfunctor X.1) htop
  have hinc := isEtale_openSubspaceInclusion hW htop le_top
  have hid : IsEtale B S hS (𝟙 X : X ⟶ X).hom := isEtale_of_isIso B S hS (𝟙 X.1)
  have hφT : φT.inv ≫ (⊤ : Subfunctor X.1).ι = 𝟙 X.1 := φT.inv_hom_id
  have H1 : eT.inv ≫ openSubspaceHom B S hS (⊤ : Subfunctor X.1) htop = 𝟙 X :=
    ObjectProperty.hom_ext _ hφT
  have H2 : openSubspaceHom B S hS W hW ≫ eT.inv = openSubspaceInclusion hW htop le_top := by
    apply ObjectProperty.hom_ext
    refine (cancel_mono (⊤ : Subfunctor X.1).ι).1 ?_
    show W.ι ≫ φT.inv ≫ (⊤ : Subfunctor X.1).ι = Subfunctor.homOfLe le_top ≫ _
    rw [hφT, Category.comp_id, Subfunctor.homOfLe_ι]
  have H3 : openSubspaceHom B S hS W hW ≫ 𝟙 X = openSubspaceHom B S hS W hW :=
    Category.comp_id _
  let τ := derivedEtaleRestrictIdIso (𝟙 X) hid rfl
  refine ⟨(etaleDerivedRestrict eT.inv hTi).obj R,
    (etaleDerivedRestrict eT.inv hTi).map β ≫
      (derivedEtaleRestrictCompApp eT.inv (openSubspaceHom B S hS (⊤ : Subfunctor X.1) htop)
        (𝟙 X) hTi hιT hid H1 E.obj).hom ≫ τ.hom.app E.obj,
    isPerfect_etaleModulePullback_standard B S hS eT.inv hTi R hR, ?_, C,
    derivedEtaleRestrictCompApp (openSubspaceHom B S hS W hW) eT.inv
      (openSubspaceInclusion hW htop le_top) hιW hTi hinc H2 R ≪≫ e, hC, ?_⟩
  · exact cohomologySupportedOn_restrict_of_comp_eq eT.inv hTi _ (𝟙 X.1) hφT
      (fun x hx => by rwa [pointsMap_id] at hx) hRT
  · have cocycle := derivedEtaleRestrictCompApp_cocycle (openSubspaceHom B S hS W hW) eT.inv
      (openSubspaceHom B S hS (⊤ : Subfunctor X.1) htop) (openSubspaceInclusion hW htop le_top)
      (𝟙 X) (openSubspaceHom B S hS W hW) hιW hTi hιT hinc hid hιW H2 H1
      (openSubspaceInclusion_comp hW htop le_top) H3 E.obj
    have unit : (derivedEtaleRestrictCompApp (openSubspaceHom B S hS W hW) (𝟙 X)
        (openSubspaceHom B S hS W hW) hιW hid hιW H3 E.obj).hom =
        (etaleDerivedRestrict (openSubspaceHom B S hS W hW) hιW).map (τ.hom.app E.obj) :=
      derivedEtaleRestrictComp_hom_app_of_eq_id' _ (𝟙 X) hιW hid rfl H3 E.obj
    have hβ' : (etaleDerivedRestrict (openSubspaceInclusion hW htop le_top) hinc).map β ≫
        (derivedEtaleRestrictCompApp (openSubspaceInclusion hW htop le_top)
          (openSubspaceHom B S hS (⊤ : Subfunctor X.1) htop) (openSubspaceHom B S hS W hW)
          hinc hιT hιW (openSubspaceInclusion_comp hW htop le_top) E.obj).hom =
        e.hom ≫ biprod.fst ≫ α := hβ
    show (etaleDerivedRestrict (openSubspaceHom B S hS W hW) hιW).map
        ((etaleDerivedRestrict eT.inv hTi).map β ≫
          (derivedEtaleRestrictCompApp eT.inv (openSubspaceHom B S hS (⊤ : Subfunctor X.1) htop)
            (𝟙 X) hTi hιT hid H1 E.obj).hom ≫ τ.hom.app E.obj) = _
    rw [Functor.map_comp, Functor.map_comp, ← unit, cocycle,
      derivedEtaleRestrictCompApp_naturality_assoc, hβ']
    simp only [Iso.trans_hom, Category.assoc]

/-- **Stacks 09IV.** Let `S` be a scheme, `X` a quasi-compact and quasi-separated algebraic space
over `S`, `W ⊆ X` a quasi-compact open subspace and `T ⊆ |X|` a closed subset such that
`X \ T ⟶ X` is quasi-compact. Let `E` be an object of `D_QCoh(𝒪_X)` and `α : P ⟶ E|_W` a map
where `P` is a perfect object of `D(𝒪_W)` supported on `T ∩ W`. Then there exists a map
`β : R ⟶ E` where `R` is a perfect object of `D(𝒪_X)` supported on `T` such that `P` is a
direct summand of `R|_W` in `D(𝒪_W)` compatibly with `α` and `β|_W`: there are
`s : P ⟶ R|_W` and `r : R|_W ⟶ P` with `s ≫ r = 𝟙 P` and `s ≫ β|_W = α`. -/
@[stacks 09IV]
theorem exists_isPerfect_retract_restrict_of_supported
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (hWqc : IsQuasiCompactSpace B S hS W.toFunctor) (T : Set (points B S hS X.1))
    (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P)
    (hPT : CohomologySupportedOn B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2 (pointsMap B S hS W.toFunctor W.ι ⁻¹' T) P)
    (α : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj E.obj) :
    ∃ (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (β : R ⟶ E.obj),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R ∧
      CohomologySupportedOn B S hS X.1 X.2 T R ∧
      ∃ (s : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R)
        (r : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R ⟶ P),
        s ≫ r = 𝟙 P ∧
        s ≫ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β = α := by
  obtain ⟨R, β, hR, hRT, C, e, -, hβ⟩ :=
    exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts hZ X hXqc hXqs W hW hWqc
      T hT hTqc E P hP hPT α
  exact ⟨R, β, hR, hRT, biprod.inl ≫ e.inv, e.hom ≫ biprod.fst, by simp, by simp [hβ]⟩

end AlgebraicGeometry.Space

end

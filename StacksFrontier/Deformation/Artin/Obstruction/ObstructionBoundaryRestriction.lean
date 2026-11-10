module

public import StacksFrontier.Deformation.Artin.Obstruction.DualSituationTransport
public import StacksFrontier.Deformation.Artin.Obstruction.LiftSituationPullback
public import StacksFrontier.Deformation.Artin.Infinitesimal.SiteContainment

/-!
# Condition (iv) of Stacks 07YY reduced to one identity at the canonical restriction

Condition (iv) of [Stacks, Tag 07YY] concerns a short exact sequence of deformation situations
`(x, A₁' → A) → (x, A₂' → A) → (x, A₃' → A)` (Remark 07YE) and a lift `x'₂` of `x` over `A₂'`. It
says that the obstruction element of `A₃'` is `∂θ`, where `θ` is the tangent class of
`x'₂|_{Spec(A₁')}` read through the identification `A₁' = A[I₁]`.

When the condition is written out in the data of `Deformation.Artin.FunctorDeformationTheory` (the
`boundary` field), most of what it asks for is data the source treats as evident: the kernel
sequence `0 → I₃ → I₂ → I₁ → 0` is short exact, `Spec A[I₁]` lies in the site, there is the
splitting `s : A → A₁'` and the map `ψ : A₂' → A[I₁]` of Remark 07YE, the morphism
`Spec A[I₁] ⟶ Spec A₂'` over `S`, and the restriction of `x'₂` along it. This file constructs all
of that, for any category fibred in groupoids over the big fppf site of `S`. What is left is the
one identity that carries mathematical content: the obstruction of `A₃'` equals `δ` applied to the
tangent class of the canonical restriction.

## Main definitions

* `Deformation.Artin.ObstructionBoundaryRestriction.kernelSequenceShortExact`: the kernel sequence
  `0 → I₃ → I₂ → I₁ → 0` of a short exact sequence of deformation situations is short exact.
* `Deformation.Artin.ObstructionBoundaryRestriction.baseSplitting`: the splitting `s : A → A₁'`.
* `Deformation.Artin.ObstructionBoundaryRestriction.splitMap`: the map `ψ : A₂' → A[I₁]`,
  `y ↦ (q₂ y, g₂₁ y - s (q₂ y))`.
* `Deformation.Artin.ObstructionBoundaryRestriction.splitOver`: the morphism
  `Spec A[I₁] ⟶ Spec A₂'` over `S` defined by `ψ`.
* `Deformation.Artin.ObstructionBoundaryRestriction.restrictedLiftClass`: the class of the
  restriction of a lift over `A₂'` along `Spec A[I₁] ⟶ Spec A₂'`.

## Main results

* `Deformation.Artin.ObstructionBoundaryRestriction.boundary_of_restrictedLiftClass`: if the
  obstruction of `A₃'` equals `δ` applied to the tangent class of `restrictedLiftClass`, for every
  short exact sequence of deformation situations and every lift over the middle one, then the
  `boundary` field of `Deformation.Artin.FunctorDeformationTheory` holds.

## References

* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
* [Stacks Project, Tag 07YE](https://stacks.math.columbia.edu/tag/07YE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin.ObstructionBoundaryRestriction

universe u v w

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
  {D₁ : SquareZeroThickening A B S hS toS hA A₁}
  {D₂ : SquareZeroThickening A B S hS toS hA A₂}
  {D₃ : SquareZeroThickening A B S hS toS hA A₃}
  {g₂₁ : SquareZeroThickening.Hom D₂ D₁} {g₃₂ : SquareZeroThickening.Hom D₃ D₂}

/-! ### The kernel sequence -/

/-- The two kernel maps of a short exact sequence of deformation situations compose to zero. -/
public theorem kernelMap_comp_eq_zero
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    g₃₂.kernelMap ≫ g₂₁.kernelMap = 0 := by
  let := kerModule D₁.q D₁.squareZeroSurjection
  let := kerModule D₃.q D₃.squareZeroSurjection
  refine ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext ?_)
  change (g₂₁.kernelMap (g₃₂.kernelMap z)).1 = 0
  rw [g₂₁.kernelMap_spec]
  exact (hses.2.2.2.2.2.2.1 (g₃₂.kernelMap z)).2 ⟨z, (g₃₂.kernelMap_spec z).symm⟩

/-- **The kernel sequence `0 → I₃ → I₂ → I₁ → 0` is short exact**, for a short exact sequence of
deformation situations (Remark 07YE). -/
public theorem kernelSequenceShortExact
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    (ShortComplex.mk g₃₂.kernelMap g₂₁.kernelMap (kernelMap_comp_eq_zero hses)).ShortExact := by
  obtain ⟨_, _, _, _, _, hinj, hexact, hsurj⟩ := hses
  have hmono : Mono g₃₂.kernelMap := by
    rw [ModuleCat.mono_iff_injective]
    intro z z' hzz'
    apply hinj
    change g₃₂.ringHom z.1 = g₃₂.ringHom z'.1
    rw [← g₃₂.kernelMap_spec, ← g₃₂.kernelMap_spec, hzz']
  have hepi : Epi g₂₁.kernelMap := by
    rw [ModuleCat.epi_iff_surjective]
    intro t
    obtain ⟨y, hy⟩ := hsurj t
    exact ⟨y, Subtype.ext ((g₂₁.kernelMap_spec y).trans hy)⟩
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  have hy' : g₂₁.ringHom y.1 = 0 := by
    rw [← g₂₁.kernelMap_spec]
    exact congrArg Subtype.val hy
  obtain ⟨z, hz⟩ := (hexact y).1 hy'
  exact ⟨z, Subtype.ext ((g₃₂.kernelMap_spec z).trans hz)⟩

/-! ### The site module `I₁` -/

/-- The trivial square-zero extension `A[I₁]` of `A` by the kernel of a deformation situation has
its spectrum in the site: it is no larger than the thickened algebra, whose spectrum is in the
site. -/
public theorem contains_spec_squareZeroRing_kernel :
    B.Contains (Spec (squareZeroRing A D₁.kernel)) := by
  refine contains_spec_squareZeroRing_of_mk_le B D₁.hA' A D₁.kernel ?_ ?_
  · exact (Cardinal.mk_le_of_surjective D₁.squareZeroSurjection.1).trans (le_max_right _ _)
  · exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans (le_max_right _ _)

/-- The kernel `I₁` of a deformation situation, as a site module. -/
public def kernelSiteModule (D₁ : SquareZeroThickening A B S hS toS hA A₁) : SiteModule A B :=
  ⟨D₁.kernel, contains_spec_squareZeroRing_kernel⟩

/-! ### The splitting and the map `ψ` -/

/-- The splitting `s : A → A₁'` of a short exact sequence of deformation situations, through
which `A₃' → A₂' → A₁'` factors (Remark 07YE). -/
public def baseSplitting
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) : A →+* A₁ :=
  (exists_factorization_through_base D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom hses).choose

/-- `A₃' → A₂' → A₁'` is `A₃' → A → A₁'` through the splitting. -/
public theorem comp_eq_baseSplitting_comp
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    g₂₁.ringHom.comp g₃₂.ringHom = (baseSplitting hses).comp D₃.q :=
  (exists_factorization_through_base D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom hses).choose_spec.symm

/-- The map `A₂' → A₁'` is compatible with the maps to `A`. -/
private theorem q_ringHom_apply
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) (y : A₂) :
    D₁.q (g₂₁.ringHom y) = D₂.q y :=
  RingHom.congr_fun hses.2.2.2.1 y

/-- The splitting is a section of `q₁ : A₁' → A`. -/
public theorem q_baseSplitting
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) (a : A) :
    D₁.q (baseSplitting hses a) = a := by
  obtain ⟨t, rfl⟩ := hses.2.2.1.1 a
  have h := congrArg (fun φ : A₃ →+* A₁ => D₁.q (φ t)) (comp_eq_baseSplitting_comp hses)
  simp only [RingHom.comp_apply] at h
  rw [← h, q_ringHom_apply hses, ← RingHom.comp_apply D₂.q, hses.2.2.2.2.1]

/-- The canonical isomorphism `A₁' = A[I₁]` of Remark 07YE, as a ring map into the trivial
square-zero extension of `A` by the site module `I₁`. -/
public def splitIso (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    A₁ →+* (squareZeroRing A (kernelSiteModule D₁).obj : Type u) := by
  let := kerModule D₁.q hses.1
  let : Module Aᵐᵒᵖ (RingHom.ker D₁.q) :=
    Module.compHom _ (RingHom.fromOpposite (RingHom.id A) fun _ _ => Commute.all _ _)
  let : IsCentralScalar A (RingHom.ker D₁.q) := ⟨fun _ _ => rfl⟩
  exact (splitExtensionRingEquiv hses).toRingHom

public theorem splitIso_fst
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) (t : A₁) :
    (splitIso hses t).fst = D₁.q t :=
  rfl

public theorem splitIso_snd
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) (t : A₁) :
    ((splitIso hses t).snd).1 = t - baseSplitting hses (D₁.q t) :=
  rfl

/-- **The map `ψ : A₂' → A[I₁]`** of a short exact sequence of deformation situations,
`y ↦ (q₂ y, g₂₁ y - s (q₂ y))`: the map `A₂' → A₁'` followed by the canonical isomorphism
`A₁' = A[I₁]` of Remark 07YE. -/
public def splitMap (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    A₂ →+* (squareZeroRing A (kernelSiteModule D₁).obj : Type u) :=
  (splitIso hses).comp g₂₁.ringHom

public theorem splitMap_fst
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) (y : A₂) :
    (splitMap hses y).fst = D₂.q y :=
  q_ringHom_apply hses y

public theorem splitMap_snd
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) (y : A₂) :
    ((splitMap hses y).snd).1 = g₂₁.ringHom y - baseSplitting hses (D₂.q y) := by
  change g₂₁.ringHom y - baseSplitting hses (D₁.q (g₂₁.ringHom y)) = _
  rw [q_ringHom_apply hses]

/-- The canonical isomorphism `A₁' = A[I₁]` carries the splitting to the inclusion of `A`. -/
public theorem ofHom_inlHom_eq
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    CommRingCat.ofHom (TrivSqZeroExt.inlHom A (kernelSiteModule D₁).obj) =
      CommRingCat.ofHom (baseSplitting hses) ≫ CommRingCat.ofHom (splitIso hses) := by
  apply CommRingCat.hom_ext
  ext a
  · exact (q_baseSplitting hses a).symm
  · refine Subtype.ext ?_
    change (0 : A₁) = baseSplitting hses a - baseSplitting hses (D₁.q (baseSplitting hses a))
    rw [q_baseSplitting hses a, sub_self]

/-! ### The morphism `Spec A[I₁] ⟶ Spec A₂'` over `S` -/

/-- The structure morphism of a thickening, after the closed immersion `Spec A ⟶ Spec A'`, is
the structure morphism of `Spec A`. -/
public theorem spec_q_comp_toS' {A' : Type u} [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A') :
    Spec.map (CommRingCat.ofHom D.q) ≫ B.inclusion.map D.toS' = toS := by
  rw [← D.arrow_spec]
  exact (B.inclusion.map_comp _ _).symm.trans
    (congrArg (fun m => B.inclusion.map m) (Over.w D.arrow))

/-- The structure morphism of `Spec A₁'` to `S` is `Spec A₁' → Spec A → S` through the
splitting. -/
public theorem toS'_eq_baseSplitting
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    B.inclusion.map D₁.toS' = Spec.map (CommRingCat.ofHom (baseSplitting hses)) ≫ toS := by
  calc B.inclusion.map D₁.toS'
      = Spec.map (CommRingCat.ofHom g₂₁.ringHom) ≫ Spec.map (CommRingCat.ofHom g₃₂.ringHom) ≫
          B.inclusion.map D₃.toS' := by rw [g₃₂.overS, g₂₁.overS]
    _ = Spec.map (CommRingCat.ofHom (baseSplitting hses)) ≫
          Spec.map (CommRingCat.ofHom D₃.q) ≫ B.inclusion.map D₃.toS' := by
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, comp_eq_baseSplitting_comp hses]
    _ = Spec.map (CommRingCat.ofHom (baseSplitting hses)) ≫ toS := by
        rw [spec_q_comp_toS' D₃]

/-- **The morphism `Spec A[I₁] ⟶ Spec A₂'` over `S`** defined by `ψ`. -/
public def splitOver (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    squareZeroOver A B S hS toS (kernelSiteModule D₁) ⟶ (Over.mk D₂.toS' : BigFppfOver B S hS) := by
  refine Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (splitMap hses))) :
    B.obj (kernelSiteModule D₁).property ⟶ B.obj D₂.hA') ?_
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (splitMap hses)) ≫ B.inclusion.map D₂.toS' =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A (kernelSiteModule D₁).obj)) ≫ toS
  have h1 : Spec.map (CommRingCat.ofHom (splitMap hses)) =
      Spec.map (CommRingCat.ofHom (splitIso hses)) ≫
        Spec.map (CommRingCat.ofHom g₂₁.ringHom) := by
    rw [← Spec.map_comp]
    rfl
  have h2 : Spec.map (CommRingCat.ofHom (splitIso hses)) ≫
        Spec.map (CommRingCat.ofHom (baseSplitting hses)) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A (kernelSiteModule D₁).obj)) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (ofHom_inlHom_eq hses).symm
  rw [h1, Category.assoc, g₂₁.overS, toS'_eq_baseSplitting hses, ← Category.assoc]
  exact congrArg (· ≫ toS) h2

public theorem inclusion_map_splitOver_left
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    B.inclusion.map (splitOver hses).left = Spec.map (CommRingCat.ofHom (splitMap hses)) :=
  rfl

/-- The closed immersion `Spec A ⟶ Spec A[I₁]` followed by `Spec A[I₁] ⟶ Spec A₂'` is the closed
immersion `Spec A ⟶ Spec A₂'`. -/
public theorem squareZeroArrow_comp_splitOver
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    squareZeroArrow A B S hS toS hA (kernelSiteModule D₁) ≫ splitOver hses = D₂.arrow := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.fstHom A A (kernelSiteModule D₁).obj).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (splitMap hses)) = B.inclusion.map D₂.arrow.left
  rw [D₂.arrow_spec, ← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext (splitMap_fst hses)

/-! ### The restriction of a lift -/

variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver A B S hS toS hA} (fibered : p.IsFiberedInGroupoids)

/-- The restriction of a lift of `x` over `A₂'` along `Spec A[I₁] ⟶ Spec A₂'`, with its strongly
cartesian comparison arrow. -/
public def restrictedLift
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom)
    (lift₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D₂.arrow))) :
    { v : (Under.post p).Fiber
        (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA (kernelSiteModule D₁))) //
      ∃ ρ : v.1.right ⟶ lift₂.1.right,
        p.IsStronglyCartesian (splitOver hses) ρ ∧ v.1.hom ≫ ρ = 𝟙 x ≫ lift₂.1.hom } :=
  underFiberPullback p fibered (splitOver hses)
    (by rw [Category.id_comp, squareZeroArrow_comp_splitOver hses]) (𝟙 x)
    (IsHomLift.id hx) lift₂

/-- **The class of the restriction of a lift over `A₂'` to `A₁' = A[I₁]`.** -/
public def restrictedLiftClass
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom)
    (lift₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D₂.arrow))) :
    Quotient (isIsomorphicSetoid ((Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA (kernelSiteModule D₁))))) :=
  Quotient.mk _ (restrictedLift fibered hses lift₂).1

/-! ### Condition (iv) from the identity at the canonical restriction -/

variable (A B S hS toS hA X p x hx) (rsStar : SatisfiesRSStar B S hS p fibered)

/-- **Condition (iv) of [Stacks, Tag 07YY] from one identity.** For functors `T¹`, `T²` with a
connecting map `δ`, a transformation `T_x(−) → T¹(−)` and obstruction elements in `T²`, the
`boundary` field of `Deformation.Artin.FunctorDeformationTheory` holds as soon as, for every
short exact sequence of deformation situations and every lift `x'₂` over the middle one, the
obstruction element of the smallest one is `δ` of the tangent class of the restriction of `x'₂`
along `Spec A[I₁] ⟶ Spec A₂'` (`restrictedLiftClass`). Everything else the field asks for is
constructed: the exactness of the kernel sequence, `Spec A[I₁]` in the site, the splitting, `ψ`,
the morphism over `S` and the restricted lift with its cartesian arrow. -/
public theorem boundary_of_restrictedLiftClass
    (T₁ T₂ : ModuleCat.{u} A ⥤ ModuleCat.{u} A)
    (δ : ∀ {Sq : ShortComplex (ModuleCat.{u} A)}, Sq.ShortExact → (T₁.obj Sq.X₃ ⟶ T₂.obj Sq.X₁))
    (tangentMap : ∀ M : SiteModule A B,
      ((tangentFunctor A B S hS toS hA p x hx fibered rsStar).functor.obj M : Type _) →ₗ[A]
        (T₁.obj M.obj : Type _))
    (obstruction : ∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A'),
      T₂.obj D.kernel)
    (restriction_identity : ∀ (A₁ A₂ A₃ : Type u) [CommRing A₁] [CommRing A₂] [CommRing A₃]
      (D₁ : SquareZeroThickening A B S hS toS hA A₁)
      (D₂ : SquareZeroThickening A B S hS toS hA A₂)
      (D₃ : SquareZeroThickening A B S hS toS hA A₃)
      (g₂₁ : SquareZeroThickening.Hom D₂ D₁) (g₃₂ : SquareZeroThickening.Hom D₃ D₂)
      (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom)
      (lift₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D₂.arrow))),
      obstruction A₃ D₃ =
        δ (kernelSequenceShortExact hses) (tangentMap (kernelSiteModule D₁)
          (((tangentFunctor A B S hS toS hA p x hx fibered rsStar).liftEquiv
            (kernelSiteModule D₁)).symm (restrictedLiftClass fibered hses lift₂)))) :
    ∀ (A₁ A₂ A₃ : Type u) [CommRing A₁] [CommRing A₂] [CommRing A₃]
      (D₁ : SquareZeroThickening A B S hS toS hA A₁)
      (D₂ : SquareZeroThickening A B S hS toS hA A₂)
      (D₃ : SquareZeroThickening A B S hS toS hA A₃)
      (g₂₁ : SquareZeroThickening.Hom D₂ D₁) (g₃₂ : SquareZeroThickening.Hom D₃ D₂),
      IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom →
      ∀ lift₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D₂.arrow)),
      ∃ (hzero : g₃₂.kernelMap ≫ g₂₁.kernelMap = 0)
        (hSq : (ShortComplex.mk g₃₂.kernelMap g₂₁.kernelMap hzero).ShortExact)
        (hmem : B.Contains (Spec (squareZeroRing A D₁.kernel)))
        (s : A →+* A₁) (ψ : A₂ →+* (squareZeroRing A D₁.kernel : Type u))
        (_hs : g₂₁.ringHom.comp g₃₂.ringHom = s.comp D₃.q)
        (_hψfst : ∀ y : A₂, (ψ y).fst = D₂.q y)
        (_hψsnd : ∀ y : A₂, ((ψ y).snd).1 = g₂₁.ringHom y - s (D₂.q y)),
        letI M₁ : SiteModule A B := ⟨D₁.kernel, hmem⟩
        ∃ (dMap : squareZeroOver A B S hS toS M₁ ⟶ (Over.mk D₂.toS' : BigFppfOver B S hS))
          (lift₁ : (Under.post p).Fiber
            (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M₁)))
          (φ : lift₁.1.right ⟶ lift₂.1.right),
          B.inclusion.map dMap.left = Spec.map (CommRingCat.ofHom ψ) ∧
          squareZeroArrow A B S hS toS hA M₁ ≫ dMap = D₂.arrow ∧
          p.IsStronglyCartesian dMap φ ∧ lift₁.1.hom ≫ φ = lift₂.1.hom ∧
            obstruction A₃ D₃ =
              δ hSq (tangentMap M₁
                (((tangentFunctor A B S hS toS hA p x hx fibered rsStar).liftEquiv M₁).symm
                  (Quotient.mk _ lift₁))) := by
  intro A₁ A₂ A₃ _ _ _ D₁ D₂ D₃ g₂₁ g₃₂ hses lift₂
  obtain ⟨ρ, hρ, hfac⟩ := (restrictedLift fibered hses lift₂).2
  exact ⟨kernelMap_comp_eq_zero hses, kernelSequenceShortExact hses,
    contains_spec_squareZeroRing_kernel, baseSplitting hses, splitMap hses,
    comp_eq_baseSplitting_comp hses, splitMap_fst hses, splitMap_snd hses, splitOver hses,
    (restrictedLift fibered hses lift₂).1, ρ, inclusion_map_splitOver_left hses,
    squareZeroArrow_comp_splitOver hses, hρ, by rw [hfac, Category.id_comp],
    restriction_identity A₁ A₂ A₃ D₁ D₂ D₃ g₂₁ g₃₂ hses lift₂⟩

end Deformation.Artin.ObstructionBoundaryRestriction

end

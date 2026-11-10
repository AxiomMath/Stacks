module

public import StacksFrontier.Deformation.ToposThickening.QuotientLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.ExtensionAlongTorsor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.Exactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatness

/-!
# Flatness of the deformed quotients of Stacks 0CZU and 0CZV

Let `(f, f')` be a strict morphism of first order thickenings of ringed topoi as in Situation
08M7, with square-zero ideals `I ⊂ O'` and `𝒥 ⊂ O_{ℬ'}`, let `ℱ'` be an `O'`-module flat over
`O_{ℬ'}`, and let `𝒦 ⊂ ℱ = i^*ℱ'` be the kernel of a quotient `ℱ ⟶ 𝒬`. The two remarks of
Stacks 0CZU and 0CZV construct lifts `ℱ' ⟶ ℱ'/𝒦'` of the quotient from submodules
`𝒦' ⊂ π⁻¹(𝒦)`, and assert that the lifts are flat over `O_{ℬ'}` and conversely that every lift
flat over `O_{ℬ'}` is of this form. This file proves the module-theoretic facts this rests on.

* **Pulling back a short exact sequence with flat last term**: for `0 ⟶ 𝒦' ⟶ ℱ' ⟶ 𝒬' ⟶ 0` with
  `𝒬'` flat over `O_{ℬ'}`, the sequence `0 ⟶ i^*𝒦' ⟶ i^*ℱ' ⟶ i^*𝒬' ⟶ 0` is short exact. This is
  the vanishing of `Tor₁` that turns a flat lift into an extension of `𝒦` by `𝒦 ⊗ 𝒥` in
  Stacks 0CZU.
* **The square-zero ideal acts injectively on `ℱ'/𝒦''`** whenever `𝒦''` is cut out of
  `π⁻¹(𝒦)` by a map extending the canonical map `I·ℱ' ⟶ 𝒬 ⊗ 𝒥`; together with the flatness
  criterion of Stacks 08MQ this makes the quotients of Stacks 0CZV flat.

## Main results

* `Deformation.ToposThickening.shortExact_map_pullbackModules_of_mono_idealAction` and
  `Deformation.ToposThickening.shortExact_map_pullbackModules_of_isFlat`: the pullback of a
  short exact sequence whose last term carries an injective action of the ideal, respectively
  is flat over `O_{ℬ'}`, is short exact.
* `Deformation.ToposThickening.canonicalFirstFactor_naturality_in_module`: the first factor of the
  canonical map of Stacks 08MQ is natural in the module.
* `Deformation.ToposThickening.mono_idealAction_cokernel_of_isExtensionKernel`: the injectivity
  of the action on the deformed quotients.
* `Deformation.ToposThickening.deformedQuotientReduction_shortExact`: the presentation
  `0 ⟶ I·(ℱ'/𝒦'') ⟶ ℱ'/𝒦'' ⟶ i_*𝒬 ⟶ 0` of a deformed quotient.
* `Deformation.ToposThickening.isIso_canonicalFirstFactor_cokernel`: the first factor of the
  canonical map of Stacks 08MQ is invertible at `𝒬`.
* `Deformation.ToposThickening.isFlat_cokernel_of_isExtensionKernel`: **the deformed quotients
  are flat over `O_{ℬ'}`.**

## Implementation notes

The arguments are diagram chases in the abelian category of `O'`-modules, carried out with
refinements (`CategoryTheory.Abelian.Refinements`); the generic statements
(`Deformation.ToposThickening.mono_of_cokernel_action`,
`Deformation.ToposThickening.mono_action_of_shortExact`,
`Deformation.ToposThickening.isIso_τ₃_of_epi_τ₁`) are stated for an arbitrary right exact
additive endofunctor with a map to the identity, which is how the action `I ⊗_{O'} - ⟶ 𝟭` of the
square-zero ideal enters.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

section Generic

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- A monomorphism followed by its cokernel projection is a short exact sequence. -/
private theorem shortExact_cokernel_of_mono {X Y : D} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f) inferInstance inferInstance

/-- **The snake lemma for an action with injective last component.** Let `T` be a right exact
additive endofunctor with a map `a : T ⟶ 𝟭`, let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be short exact with
`a` a monomorphism at `X₃`, and let `q₁`, `q₂` be cokernels of `a` at `X₁` and `X₂`. Then the
map `m` of cokernels induced by `X₁ ⟶ X₂` is a monomorphism. -/
theorem mono_of_cokernel_action
    (T : D ⥤ D) [T.Additive] [PreservesFiniteColimits T]
    (a : T ⟶ 𝟭 D) (S : ShortComplex D) (hS : S.ShortExact) [Mono (a.app S.X₃)]
    {Q₁ Q₂ : D} (q₁ : S.X₁ ⟶ Q₁) (hq₁ : a.app S.X₁ ≫ q₁ = 0)
    (hc₁ : IsColimit (CokernelCofork.ofπ q₁ hq₁))
    (q₂ : S.X₂ ⟶ Q₂) (hq₂ : a.app S.X₂ ≫ q₂ = 0)
    (hc₂ : IsColimit (CokernelCofork.ofπ q₂ hq₂))
    (m : Q₁ ⟶ Q₂) (hm : q₁ ≫ m = S.f ≫ q₂) : Mono m := by
  have := hS.mono_f
  have := hS.epi_g
  have : Epi q₁ := epi_of_isColimit_cofork hc₁
  have hT := hS.exact.map_of_epi_of_preservesCokernel T
    (inferInstance : Epi S.g) (inferInstance : PreservesColimit (parallelPair S.f 0) T)
  apply (Preadditive.mono_iff_cancel_zero _).2
  intro Z z hz
  obtain ⟨Z₁, p₁, hp₁, x₁, hx₁⟩ := surjective_up_to_refinements_of_epi q₁ z
  have hx₁f : (x₁ ≫ S.f) ≫ q₂ = 0 := by
    rw [Category.assoc, ← hm, ← Category.assoc, ← hx₁, Category.assoc, hz, comp_zero]
  obtain ⟨Z₂, p₂, hp₂, x, hx⟩ :=
    (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements hc₂ (x₁ ≫ S.f)).1 hx₁f
  have hxg : x ≫ T.map S.g = 0 := by
    apply (cancel_mono (a.app S.X₃)).1
    rw [zero_comp, Category.assoc, a.naturality, ← Category.assoc, ← hx,
      Category.assoc, Category.assoc, Functor.id_map, S.zero, comp_zero, comp_zero]
  obtain ⟨Z₃, p₃, hp₃, y, hy⟩ := hT.exact_up_to_refinements x hxg
  change p₃ ≫ x = y ≫ T.map S.f at hy
  have hx₁' : p₃ ≫ p₂ ≫ x₁ = y ≫ a.app S.X₁ := by
    apply (cancel_mono S.f).1
    rw [Category.assoc, Category.assoc, hx, ← Category.assoc, hy, Category.assoc,
      a.naturality, Functor.id_map, Category.assoc]
  apply (cancel_epi p₁).1
  apply (cancel_epi p₂).1
  apply (cancel_epi p₃).1
  rw [comp_zero, comp_zero, comp_zero, hx₁]
  have h := congrArg (· ≫ q₁) hx₁'
  simp only [Category.assoc, hq₁, comp_zero] at h
  exact h

/-- **The action on a quotient is injective when the action on the middle term is and nothing
new is killed.** Let `T` be a right exact additive endofunctor with a map `a : T ⟶ 𝟭`, and let
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be short exact with `a` a monomorphism at `X₂`. If every map
`z : Z ⟶ T X₂` whose action lands in `X₁` comes, up to refinement, from `T X₁`, then `a` is a
monomorphism at `X₃`. -/
theorem mono_action_of_shortExact
    (T : D ⥤ D) [T.Additive] [PreservesFiniteColimits T]
    (a : T ⟶ 𝟭 D) (S : ShortComplex D) (hS : S.ShortExact)
    (hX : ∀ ⦃Z : D⦄ (z : Z ⟶ T.obj S.X₂), z ≫ a.app S.X₂ ≫ S.g = 0 →
      ∃ (Z' : D) (p : Z' ⟶ Z) (_ : Epi p) (y : Z' ⟶ T.obj S.X₁), p ≫ z = y ≫ T.map S.f) :
    Mono (a.app S.X₃) := by
  have := hS.epi_g
  apply (Preadditive.mono_iff_cancel_zero _).2
  intro Z w hw
  obtain ⟨Z₁, p₁, hp₁, z, hz⟩ := surjective_up_to_refinements_of_epi (T.map S.g) w
  obtain ⟨Z₂, p₂, hp₂, y, hy⟩ := hX z (by
    have h1 : a.app S.X₂ ≫ S.g = T.map S.g ≫ a.app S.X₃ := (a.naturality S.g).symm
    rw [h1, ← Category.assoc, ← hz, Category.assoc, hw, comp_zero])
  apply (cancel_epi p₁).1
  apply (cancel_epi p₂).1
  rw [comp_zero, comp_zero, hz, ← Category.assoc, hy, Category.assoc, ← T.map_comp, S.zero,
    T.map_zero, comp_zero]

/-- **A map of right exact sequences which is invertible in the middle and surjective on the
left is invertible on the right.** For `A₁ ⟶ A₂ ⟶ A₃ ⟶ 0` and exact `B₁ ⟶ B₂ ⟶ B₃ ⟶ 0` and a
map of complexes `φ` with `φ.τ₁` an epimorphism and `φ.τ₂` an isomorphism, `φ.τ₃` is an
isomorphism. -/
theorem isIso_τ₃_of_epi_τ₁ {A B : ShortComplex D} (φ : A ⟶ B) (hB : B.Exact)
    [Epi A.g] [Epi B.g] [Epi φ.τ₁] [IsIso φ.τ₂] : IsIso φ.τ₃ := by
  have hepi : Epi φ.τ₃ := by
    have : Epi (A.g ≫ φ.τ₃) := by rw [← φ.comm₂₃]; infer_instance
    exact epi_of_epi A.g φ.τ₃
  have hmono : Mono φ.τ₃ := by
    apply (Preadditive.mono_iff_cancel_zero _).2
    intro Z z hz
    obtain ⟨Z₁, p₁, hp₁, x, hx⟩ := surjective_up_to_refinements_of_epi A.g z
    have hx' : (x ≫ φ.τ₂) ≫ B.g = 0 := by
      rw [Category.assoc, φ.comm₂₃, ← Category.assoc, ← hx, Category.assoc, hz, comp_zero]
    obtain ⟨Z₂, p₂, hp₂, y, hy⟩ := hB.exact_up_to_refinements (x ≫ φ.τ₂) hx'
    obtain ⟨Z₃, p₃, hp₃, y', hy'⟩ := surjective_up_to_refinements_of_epi φ.τ₁ y
    have hxy : p₃ ≫ p₂ ≫ x = y' ≫ A.f := by
      apply (cancel_mono φ.τ₂).1
      rw [Category.assoc, Category.assoc, hy, ← Category.assoc, hy', Category.assoc,
        Category.assoc, φ.comm₁₂]
    apply (cancel_epi p₁).1
    apply (cancel_epi p₂).1
    apply (cancel_epi p₃).1
    rw [comp_zero, comp_zero, comp_zero, hx]
    have h := congrArg (· ≫ A.g) hxy
    simp only [Category.assoc, A.zero, comp_zero] at h
    exact h
  exact isIso_of_mono_of_epi _

/-- **A natural transformation between right exact functors which is surjective at the kernel
and invertible at the middle term of a right exact sequence is invertible at its cokernel.** -/
theorem isIso_app_of_exact {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ] {F₁ F₂ : D ⥤ ℬ}
    [F₁.Additive] [F₂.Additive] [PreservesFiniteColimits F₁] [PreservesFiniteColimits F₂]
    (α : F₁ ⟶ F₂) (S : ShortComplex D) (hS : S.Exact) [Epi S.g]
    (h₁ : Epi (α.app S.X₁)) (h₂ : IsIso (α.app S.X₂)) : IsIso (α.app S.X₃) := by
  have hB := hS.map_of_epi_of_preservesCokernel F₂ inferInstance inferInstance
  have : Epi (S.map F₁).g := (inferInstance : Epi (F₁.map S.g))
  have : Epi (S.map F₂).g := (inferInstance : Epi (F₂.map S.g))
  have : Epi (S.mapNatTrans α).τ₁ := h₁
  have : IsIso (S.mapNatTrans α).τ₂ := h₂
  exact isIso_τ₃_of_epi_τ₁ (S.mapNatTrans α) hB

end Generic

section IdealAction

open AlgebraicGeometry (RingedTopos RingedToposHom)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] pullbackModules_additive

/-- **A short exact sequence whose last term carries an injective ideal action stays short exact
after pullback along a first order thickening.** This is the vanishing of `Tor₁(X₃, O)`: the
pullback is the cokernel of the action of the square-zero ideal, and the snake lemma
`Deformation.ToposThickening.mono_of_cokernel_action` makes the pullback of the first map a
monomorphism. -/
theorem shortExact_map_pullbackModules_of_mono_idealAction (hi : FirstOrderThickening i)
    (S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hS : S.ShortExact) [Mono ((idealAction hi).app S.X₃)] :
    (S.map (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      i.toRingedToposModulesHom)).ShortExact := by
  let := hi.abelian
  let L := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    i.toRingedToposModulesHom
  let R := i.pushforwardModules
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  let ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  let : R.Faithful := ff.faithful
  let := adj.leftAdjoint_preservesColimits
  let : Mono (R.map (L.map S.f)) :=
    mono_of_cokernel_action (idealTensorFunctor hi) (idealAction hi) S hS
      _ (idealAction_comp_unit hi S.X₁) (unitIsCokernelIdealAction hi S.X₁)
      _ (idealAction_comp_unit hi S.X₂) (unitIsCokernelIdealAction hi S.X₂)
      _ (adj.unit.naturality S.f).symm
  let : Mono (L.map S.f) := R.mono_of_mono_map inferInstance
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk'
    (hS.exact.map_of_epi_of_preservesCokernel L inferInstance inferInstance) ?_ ?_
  · change Mono (L.map S.f)
    infer_instance
  · change Epi (L.map S.g)
    infer_instance

end IdealAction

section FirstFactor

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [S.J.HasSheafCompose (forget AddCommGrpCat)] in
include comm in
/-- **The first factor `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of the canonical map of Stacks 08MQ is natural in
`ℱ`.** -/
theorem canonicalFirstFactor_naturality_in_module
    {F₁ F₂ : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (k : F₁ ⟶ F₂) :
    ((sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).obj
          (inverseImageBaseIdeal t f' ht)).map
        ((SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).map k) ≫
        canonicalFirstFactor i t f f' hi ht comm F₂ =
      canonicalFirstFactor i t f f' hi ht comm F₁ ≫
        (SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).map
          (((sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map k) := by
  rw [canonicalFirstFactor, canonicalFirstFactor, Functor.flip_obj_map, Functor.flip_obj_map,
    ← Category.assoc, ((sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).map
      (inverseImageBaseIdealToIdeal i t f f' hi ht comm)).naturality, Category.assoc,
    Category.assoc]
  congr 1
  exact Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_natural_right
    (inverseImageReducedStructureMap i t f f' comm) hi.I (𝟙 _) (𝟙 _)
    ((SheafOfModules.restrictScalars
      (ringMap (inverseImageReducedStructureMap i t f f' comm))).map k) k
    (by rw [Category.id_comp, Category.comp_id])

include comm in
/-- **The first factor `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of the canonical map of Stacks 08MQ, as a natural
transformation** between the two functors `ℱ ↦ f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ` and `ℱ ↦ I ⊗_O ℱ` of
`O`-modules (presented on the thickened topos), both read over `f⁻¹O_ℬ`. -/
noncomputable def canonicalFirstFactorNatTrans :
    SheafOfModules.restrictScalars (ringMap (inverseImageReducedStructureMap i t f f' comm)) ⋙
        (sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).obj
          (inverseImageBaseIdeal t f' ht) ⟶
      (sheafTensor.{u', v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj
          hi.I ⋙
        SheafOfModules.restrictScalars (ringMap (inverseImageReducedStructureMap i t f f' comm))
    where
  app F := canonicalFirstFactor i t f f' hi ht comm F
  naturality _ _ k := canonicalFirstFactor_naturality_in_module i t f f' hi ht comm k

end FirstFactor

section Relative

open AlgebraicGeometry (RingedTopos RingedToposHom)

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)

attribute [local instance] pullbackModules_additive

omit [HasWeakSheafify S.J AddCommGrpCat] [S.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
include comm in
/-- **A short exact sequence of `O'`-modules whose last term is flat over `O_{ℬ'}` stays short
exact after pullback to `Sh(C)`**, for a strict morphism of first order thickenings: the last
term carries an injective action of the square-zero ideal (the final assertion of Stacks 08MQ,
`Deformation.ToposThickening.isIdealActionMono`). For `0 ⟶ 𝒦' ⟶ ℱ' ⟶ 𝒬' ⟶ 0` this is the
exactness of `0 ⟶ i^*𝒦' ⟶ i^*ℱ' ⟶ i^*𝒬' ⟶ 0` that Stacks 0CZU and 0CZV use. -/
theorem shortExact_map_pullbackModules_of_isFlat
    (Sc : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)))
    (hSc : Sc.ShortExact)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj Sc.X₃)) :
    (Sc.map (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      i.toRingedToposModulesHom)).ShortExact := by
  let : Mono ((idealAction hi).app Sc.X₃) :=
    isIdealActionMono i t f f' hi ht comm Sc.X₃ hstrict hflat
  exact shortExact_map_pullbackModules_of_mono_idealAction hi Sc hSc

end Relative

section IdealActionQuotient

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}]
  {i : RingedToposHom X X'} (hi : FirstOrderThickening i)
  (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  (K : Subobject ((pullbackModules i.toRingedToposModulesHom).obj F'))

omit [HasSheafify X.J AddCommGrpCat] in
/-- **The square-zero ideal acts injectively on `ℱ'/𝒦''`** for a subobject `𝒦'' ⊂ π⁻¹(𝒦)` cut
out by a map extending `c : I·ℱ' ⟶ M`, provided it acts injectively on `ℱ'` and `c` is a
cokernel of the action `a' : I ⊗ π⁻¹(𝒦) ⟶ I·ℱ'`. This is the injectivity half of the flatness of
the quotients `ℱ'/𝒦'_φ` of Stacks 0CZV. -/
theorem mono_idealAction_cokernel_of_isExtensionKernel
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}
    (c : (idealProductSubmodule hi F').toSheafOfModules ⟶ M)
    (a' : (idealTensorFunctor hi).obj (quotientLiftPreimage i F' K) ⟶
      (idealProductSubmodule hi F').toSheafOfModules)
    (ha' : a' ≫ (idealProductSubmodule hi F').ι =
      (idealTensorFunctor hi).map (quotientLiftPreimageι i F' K) ≫ (idealAction hi).app F')
    (hac : a' ≫ c = 0) (hc : IsColimit (CokernelCofork.ofπ c hac))
    [Mono ((idealAction hi).app F')]
    (K'' : Subobject (quotientLiftPreimage i F' K))
    (hK'' : IsExtensionKernel (quotientLiftPreimageShortComplex i hi F' K) c K'') :
    Mono ((idealAction hi).app (cokernel (K''.arrow ≫ quotientLiftPreimageι i F' K))) := by
  let T := idealTensorFunctor hi
  let a := idealAction hi
  let Sq := quotientLiftPreimageShortComplex i hi F' K
  have hSq := quotientLiftPreimageShortComplex_shortExact i hi F' K
  let N := idealProductSubmodule hi F'
  let ιP := quotientLiftPreimageι i F' K
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  let ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  let : i.pushforwardModules.Faithful := ff.faithful
  let : i.pushforwardModules.Full := ff.full
  have : i.pushforwardModules.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  have : Mono ιP := inferInstanceAs (Mono (pullback.snd _ _))
  have hιSq : Sq.f ≫ ιP = N.ι := pullback.lift_snd _ _ _
  let S₀ := ShortComplex.mk (K''.arrow ≫ ιP) (cokernel.π _) (cokernel.condition _)
  have hS₀ : S₀.ShortExact := shortExact_cokernel_of_mono _
  have hNunit : IsIso (adj.unit.app N.toSheafOfModules) :=
    adj.isIso_unit_app_iff_mem_essImage.2 (essImage_idealProductSubmodule hi F')
  have hTN : T.map N.ι = 0 := by
    apply (cancel_mono (a.app F')).1
    rw [zero_comp, a.naturality, Functor.id_map, idealAction_app_eq_zero hi N.toSheafOfModules,
      zero_comp]
  obtain ⟨hepi, hfac⟩ := hK''
  let f₁ : N.toSheafOfModules ⟶ quotientLiftPreimage i F' K :=
    idealProductToQuotientLiftPreimage i hi F' K
  have hf₁ : f₁ ≫ ιP = N.ι := hιSq
  have hdesc : Epi (biprod.desc K''.arrow f₁) := epi_biprodDesc_of_epi_comp hSq K'' hepi
  refine mono_action_of_shortExact T a S₀ hS₀ ?_
  intro Z z hz
  obtain ⟨n, hn⟩ : ∃ n : T.obj F' ⟶ N.toSheafOfModules, n ≫ N.ι = a.app F' :=
    ⟨_, (KernelFork.IsLimit.lift' (idealProductShortComplex_shortExact hi F').fIsKernel
      (a.app F') (idealAction_comp_unit hi F')).2⟩
  have hnc : (z ≫ n) ≫ c = 0 := by
    refine (hfac (z ≫ n)).1 ?_
    obtain ⟨w', hw'⟩ := hS₀.exact.lift' (z ≫ n ≫ N.ι) (by
      rw [Category.assoc, hn]
      exact hz)
    change w' ≫ K''.arrow ≫ ιP = _ at hw'
    have : w' ≫ K''.arrow = (z ≫ n) ≫ f₁ := (cancel_mono ιP).1 (by
      rw [Category.assoc, hw', Category.assoc, Category.assoc, hf₁])
    change K''.Factors ((z ≫ n) ≫ f₁)
    rw [← this]
    exact Subobject.factors_comp_arrow w'
  obtain ⟨Z₁, p₁, hp₁, y, hy⟩ :=
    (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements hc (z ≫ n)).1 hnc
  have hzy : p₁ ≫ z = y ≫ T.map ιP := (cancel_mono (a.app F')).1 (calc
    (p₁ ≫ z) ≫ a.app F' = (p₁ ≫ z ≫ n) ≫ N.ι := by
      rw [← hn]; simp only [Category.assoc]
    _ = (y ≫ a') ≫ N.ι := by rw [hy]
    _ = (y ≫ T.map ιP) ≫ a.app F' := by rw [Category.assoc, ha', Category.assoc])
  obtain ⟨Z₂, p₂, hp₂, x, hx⟩ :=
    surjective_up_to_refinements_of_epi (T.map (biprod.desc K''.arrow f₁)) y
  refine ⟨Z₂, p₂ ≫ p₁, inferInstance, x ≫ T.map biprod.fst, ?_⟩
  have hsplit : biprod.desc K''.arrow f₁ ≫ ιP =
      biprod.fst ≫ K''.arrow ≫ ιP + biprod.snd ≫ N.ι := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Preadditive.comp_add, biprod.inl_fst_assoc,
        biprod.inl_snd_assoc, zero_comp, add_zero]
    · rw [biprod.inr_desc_assoc, Preadditive.comp_add, biprod.inr_fst_assoc, zero_comp,
        zero_add, biprod.inr_snd_assoc, hf₁]
  change (p₂ ≫ p₁) ≫ z = (x ≫ T.map biprod.fst) ≫ T.map (K''.arrow ≫ ιP)
  rw [Category.assoc, hzy, ← Category.assoc, hx, Category.assoc, ← T.map_comp, hsplit,
    Functor.map_add, Functor.map_comp T biprod.snd, hTN, comp_zero, add_zero,
    Functor.map_comp T biprod.fst, Category.assoc]

omit [HasWeakSheafify X'.J AddCommGrpCat] [X'.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] [HasSheafify X'.J AddCommGrpCat] in
/-- A map into a direct image kills the ideal product: it factors through the unit, which does. -/
theorem idealProductSubmodule_ι_comp_eq_zero_of_pushforward
    {G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : G ⟶ i.pushforwardModules.obj M) :
    (idealProductSubmodule hi G).ι ≫ g = 0 := by
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  rw [← (adj.homEquiv G M).apply_symm_apply g, adj.homEquiv_unit, ← Category.assoc,
    idealProductSubmodule_unit_comp_zero hi G, zero_comp]

omit [HasSheafify X.J AddCommGrpCat] in
/-- **The ideal product is functorial**: a map `G ⟶ H` carries `I·G` into `I·H`. -/
theorem exists_idealProductSubmodule_ι_comp
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)} (g : G ⟶ H) :
    ∃ m : (idealProductSubmodule hi G).toSheafOfModules ⟶
        (idealProductSubmodule hi H).toSheafOfModules,
      (idealProductSubmodule hi G).ι ≫ g = m ≫ (idealProductSubmodule hi H).ι := by
  obtain ⟨m, hm⟩ := KernelFork.IsLimit.lift' (idealProductShortComplex_shortExact hi H).fIsKernel
    ((idealProductSubmodule hi G).ι ≫ g) (by
      change ((idealProductSubmodule hi G).ι ≫ g) ≫
        i.pullbackAdjPushforwardModulesViaComparison.unit.app H = 0
      rw [Category.assoc]
      exact idealProductSubmodule_ι_comp_eq_zero_of_pushforward hi _)
  exact ⟨m, hm.symm⟩

/-- **The reduction of `ℱ'/𝒦''` onto `𝒬`**: for `𝒦'' ⊂ π⁻¹(𝒦)`, the map `ℱ'/𝒦'' ⟶ i_*𝒬`
induced by `ℱ' ⟶ i_*ℱ ⟶ i_*𝒬`. -/
noncomputable def deformedQuotientReduction (K'' : Subobject (quotientLiftPreimage i F' K)) :
    cokernel (K''.arrow ≫ quotientLiftPreimageι i F' K) ⟶
      i.pushforwardModules.obj (cokernel K.arrow) :=
  cokernel.desc _ (i.pullbackAdjPushforwardModulesViaComparison.unit.app F' ≫
    i.pushforwardModules.map (cokernel.π K.arrow)) (by
      rw [Category.assoc, ← Category.assoc (quotientLiftPreimageι i F' K), ← pullback.condition,
        Category.assoc, ← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero,
        comp_zero])

/-- **`0 ⟶ I·(ℱ'/𝒦'') ⟶ ℱ'/𝒦'' ⟶ i_*𝒬 ⟶ 0` is short exact** when `𝒦''` and `I·ℱ'` together cover
`π⁻¹(𝒦)`, i.e. when `𝒦''` maps onto `i_*𝒦`. This is the presentation of the reduction of the
deformed quotient by `𝒬` that the flatness criterion of Stacks 08MQ consumes. -/
theorem deformedQuotientReduction_shortExact (K'' : Subobject (quotientLiftPreimage i F' K))
    (hK'' : Epi (K''.arrow ≫ quotientLiftPreimageπ i F' K)) :
    (ShortComplex.mk (idealProductSubmodule hi
        (cokernel (K''.arrow ≫ quotientLiftPreimageι i F' K))).ι
      (deformedQuotientReduction F' K K'')
      (idealProductSubmodule_ι_comp_eq_zero_of_pushforward hi _)).ShortExact := by
  let R := i.pushforwardModules
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  let ιP := quotientLiftPreimageι i F' K
  let p := cokernel.π (K''.arrow ≫ ιP)
  have hp : p ≫ deformedQuotientReduction F' K K'' =
      adj.unit.app F' ≫ R.map (cokernel.π K.arrow) := cokernel.π_desc _ _ _
  have : PreservesFiniteLimits R :=
    (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_exact hi.closedRingedImmersion).1
  have : PreservesFiniteColimits R :=
    (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_exact hi.closedRingedImmersion).2
  let SK := ShortComplex.mk K.arrow (cokernel.π K.arrow) (cokernel.condition _)
  have hSK : SK.ShortExact := shortExact_cokernel_of_mono _
  have hRSK : (SK.map R).ShortExact := hSK.map_of_exact R
  have := hRSK.epi_g
  have := epi_pullbackAdjPushforward_unit_app hi F'
  have hSq := quotientLiftPreimageShortComplex_shortExact i hi F' K
  have hdesc : Epi (biprod.desc K''.arrow (idealProductToQuotientLiftPreimage i hi F' K)) :=
    epi_biprodDesc_of_epi_comp hSq K'' hK''
  refine ShortComplex.ShortExact.mk' ?_
    (inferInstanceAs (Mono (idealProductSubmodule hi (cokernel (K''.arrow ≫ ιP))).ι)) ?_
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x₂ hx₂
    change x₂ ≫ deformedQuotientReduction F' K K'' = 0 at hx₂
    obtain ⟨A₁, p₁, hp₁, y, hy⟩ := surjective_up_to_refinements_of_epi p x₂
    have hy0 : (y ≫ adj.unit.app F') ≫ R.map (cokernel.π K.arrow) = 0 := by
      rw [Category.assoc, ← hp, ← Category.assoc, ← hy, Category.assoc, hx₂, comp_zero]
    obtain ⟨A₂, p₂, hp₂, k, hk⟩ := hRSK.exact.exact_up_to_refinements _ hy0
    change p₂ ≫ y ≫ adj.unit.app F' = k ≫ R.map K.arrow at hk
    let l : A₂ ⟶ quotientLiftPreimage i F' K := pullback.lift k (p₂ ≫ y)
      (by rw [← hk, Category.assoc])
    obtain ⟨A₃, p₃, hp₃, u, hu⟩ := surjective_up_to_refinements_of_epi
      (biprod.desc K''.arrow (idealProductToQuotientLiftPreimage i hi F' K)) l
    obtain ⟨m, hm⟩ := exists_idealProductSubmodule_ι_comp hi p
    refine ⟨A₃, p₃ ≫ p₂ ≫ p₁, inferInstance,
      u ≫ biprod.snd ≫ m, ?_⟩
    change (p₃ ≫ p₂ ≫ p₁) ≫ x₂ =
      (u ≫ biprod.snd ≫ m) ≫ (idealProductSubmodule hi (cokernel (K''.arrow ≫ ιP))).ι
    have hl : l ≫ ιP = p₂ ≫ y := pullback.lift_snd _ _ _
    have hN : idealProductToQuotientLiftPreimage i hi F' K ≫ ιP =
        (idealProductSubmodule hi F').ι := pullback.lift_snd _ _ _
    calc (p₃ ≫ p₂ ≫ p₁) ≫ x₂ = p₃ ≫ p₂ ≫ y ≫ p := by
          rw [Category.assoc, Category.assoc, hy]
      _ = p₃ ≫ l ≫ ιP ≫ p := by rw [← Category.assoc l, hl, Category.assoc]
      _ = u ≫ biprod.desc K''.arrow (idealProductToQuotientLiftPreimage i hi F' K) ≫ ιP ≫ p := by
          rw [← Category.assoc p₃, hu, Category.assoc]
      _ = u ≫ biprod.snd ≫ (idealProductSubmodule hi F').ι ≫ p := by
          congr 1
          apply biprod.hom_ext'
          · rw [biprod.inl_desc_assoc, biprod.inl_snd_assoc, zero_comp, ← Category.assoc,
              cokernel.condition]
          · rw [biprod.inr_desc_assoc, biprod.inr_snd_assoc, ← Category.assoc, hN]
      _ = (u ≫ biprod.snd ≫ m) ≫ (idealProductSubmodule hi (cokernel (K''.arrow ≫ ιP))).ι := by
          rw [hm, Category.assoc, Category.assoc]
  · have : Epi (adj.unit.app F' ≫ R.map (cokernel.π K.arrow)) := epi_comp _ _
    rw [← hp] at this
    exact epi_of_epi p _

end IdealActionQuotient

section DeformedQuotientFlatness

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap)

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  (K : Subobject ((pullbackModules i.toRingedToposModulesHom).obj F'))

omit [HasWeakSheafify S.J AddCommGrpCat] [S.J.WEqualsLocallyBijective AddCommGrpCat] in
include comm in
/-- **The first factor of the canonical map of Stacks 08MQ is invertible at a quotient `𝒬` of
`ℱ = i^*ℱ'`** when `ℱ'` is flat over `O_{ℬ'}` and the square is strict: it is invertible at `ℱ`
(the final assertion of Stacks 08MQ), surjective at the kernel `𝒦` (strictness), and natural, so
`Deformation.ToposThickening.isIso_app_of_exact` applies to `𝒦 ⟶ ℱ ⟶ 𝒬 ⟶ 0`. -/
theorem isIso_canonicalFirstFactor_cokernel
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F')) :
    IsIso (canonicalFirstFactor i t f f' hi ht comm
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (cokernel K.arrow))) := by
  have hstrictP : IsStrictPullbackIdealMap i t f f' hi ht comm :=
    (isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hstrict
  have : PreservesFiniteLimits i.pushforwardModules :=
    (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_exact hi.closedRingedImmersion).1
  have : PreservesFiniteColimits i.pushforwardModules :=
    (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_exact hi.closedRingedImmersion).2
  have : ((sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).obj
      (inverseImageBaseIdeal t f' ht)).Additive :=
    Stacks.SheafOfModules.FlatSquareZero.tensorLeft_additive _ _
  have : ((sheafTensor.{u', v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj
      X.O)).obj hi.I).Additive :=
    Stacks.SheafOfModules.FlatSquareZero.tensorLeft_additive _ _
  have : PreservesFiniteColimits ((sheafTensor.{u', v', w, w, w}
      (inverseImageReducedBaseRing t f')).obj (inverseImageBaseIdeal t f' ht)) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, w} _
  have : PreservesFiniteColimits ((sheafTensor.{u', v', w, w, w}
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, w} _
  let SK := ShortComplex.mk K.arrow (cokernel.π K.arrow) (cokernel.condition _)
  have hSK : SK.ShortExact := shortExact_cokernel_of_mono _
  let SP₀ := SK.map
    (pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let SP : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) := SP₀
  have hSP : SP.ShortExact :=
    Stacks.SheafOfModules.ChangeOfRings.shortExact_of_shortExact_map_restrictScalars
      (ringMap i.fSharp) (hSK.map_of_exact i.pushforwardModules)
  have := hSP.epi_g
  exact isIso_app_of_exact (canonicalFirstFactorNatTrans i t f f' hi ht comm) SP hSP.exact
    (epi_canonicalFirstFactor i t f f' hi ht comm _ hstrictP)
    (isIso_canonicalFactors_of_isFlat i t f f' hi ht comm F' hstrict hflat).1

omit [HasWeakSheafify S.J AddCommGrpCat] [S.J.WEqualsLocallyBijective AddCommGrpCat] in
include comm in
/-- **The deformed quotients of Stacks 0CZV are flat.** Let `𝒦'' ⊂ π⁻¹(𝒦)` be cut out by a map
extending `c : I·ℱ' ⟶ M`, where `c` is a cokernel of the action `a' : I ⊗ π⁻¹(𝒦) ⟶ I·ℱ'`. If
`ℱ'` is flat over `O_{ℬ'}`, the quotient `𝒬 = ℱ/𝒦` is flat over `O_ℬ` and the square is strict,
then `ℱ'/𝒦''` is flat over `O_{ℬ'}`.

By the criterion of Stacks 08MQ, for the presentation
`0 ⟶ I·(ℱ'/𝒦'') ⟶ ℱ'/𝒦'' ⟶ i_*𝒬 ⟶ 0`
(`Deformation.ToposThickening.deformedQuotientReduction_shortExact`), it suffices that both
factors `f^*𝒥 ⊗ 𝒬 ⟶ I ⊗ 𝒬 ⟶ I·(ℱ'/𝒦'')` of the canonical map are invertible: the first is
`Deformation.ToposThickening.isIso_canonicalFirstFactor_cokernel`, the second is surjective
and injective because the ideal acts injectively on `ℱ'/𝒦''`
(`Deformation.ToposThickening.mono_idealAction_cokernel_of_isExtensionKernel`). -/
theorem isFlat_cokernel_of_isExtensionKernel
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hQ : IsFlatOverBase i f
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (cokernel K.arrow)))
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}
    (c : (idealProductSubmodule hi F').toSheafOfModules ⟶ M)
    (a' : (idealTensorFunctor hi).obj (quotientLiftPreimage i F' K) ⟶
      (idealProductSubmodule hi F').toSheafOfModules)
    (ha' : a' ≫ (idealProductSubmodule hi F').ι =
      (idealTensorFunctor hi).map (quotientLiftPreimageι i F' K) ≫ (idealAction hi).app F')
    (hac : a' ≫ c = 0) (hc : IsColimit (CokernelCofork.ofπ c hac))
    (K'' : Subobject (quotientLiftPreimage i F' K))
    (hK'' : IsExtensionKernel (quotientLiftPreimageShortComplex i hi F' K) c K'') :
    AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj (cokernel (K''.arrow ≫ quotientLiftPreimageι i F' K))) := by
  have : Mono ((idealAction hi).app F') := isIdealActionMono i t f f' hi ht comm F' hstrict hflat
  have hmono := mono_idealAction_cokernel_of_isExtensionKernel hi F' K c a' ha' hac hc K'' hK''
  have hq := idealProductSubmodule_ι_comp_eq_zero_of_pushforward hi
    (deformedQuotientReduction F' K K'')
  have hqex := deformedQuotientReduction_shortExact hi F' K K'' hK''.1
  refine (isFlat_iff_isIso_canonicalMap_of_isStrict i t f f' hi ht comm
    ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
      (cokernel K.arrow)) _ (deformedQuotientReduction F' K K'') hq hqex hstrict hQ).1.mpr ?_
  have := isIso_canonicalFirstFactor_cokernel i t f f' hi ht comm F' K hstrict hflat
  have := isIso_reductionTensorMap_thickening i hi
    ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
      (cokernel K.arrow)) _
    (deformedQuotientReduction F' K K'') hq hqex
  have : Mono (canonicalSecondFactor i hi
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (cokernel K.arrow)) _ (deformedQuotientReduction F' K K'') hq hqex) := by
    have h := reductionTensorMap_comp_canonicalSecondFactor i hi
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (cokernel K.arrow)) _
      (deformedQuotientReduction F' K K'') hq hqex
    have hm : Mono (Stacks.SheafOfModules.FlatSquareZero.multiplicationMap i.fSharp hi.I
        (cokernel (K''.arrow ≫ quotientLiftPreimageι i F' K)) hi.incl) := hmono
    rw [← h, mono_comp_iff_of_isIso] at hm
    exact mono_of_mono _ (idealProductSubmodule hi
      (cokernel (K''.arrow ≫ quotientLiftPreimageι i F' K))).ι
  have := epi_canonicalSecondFactor i hi
    ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
      (cokernel K.arrow)) _ (deformedQuotientReduction F' K K'') hq hqex
  have : IsIso (canonicalSecondFactor i hi
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (cokernel K.arrow)) _ (deformedQuotientReduction F' K K'') hq hqex) :=
    isIso_of_mono_of_epi _
  have := isIso_squareTransportSymm f'.fSharpInverseImage i.fSharp
    (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
    (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
    (((sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj
        X.O)).flip.obj ((pushforwardModuleFunctor i.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (cokernel K.arrow))).obj hi.I)
  have : IsIso (squareTransport f'.fSharpInverseImage i.fSharp
      (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
      (((sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj
          X.O)).flip.obj ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (cokernel K.arrow))).obj hi.I)) :=
    ⟨⟨squareTransportSymm f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
        (inverseImageReducedStructureMap i t f f' comm)
        (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) _,
      squareTransport_comp_squareTransportSymm _ _ _ _ _ _,
      squareTransportSymm_comp_squareTransport _ _ _ _ _ _⟩⟩
  unfold canonicalMap
  infer_instance

end DeformedQuotientFlatness

end Deformation.ToposThickening

end

module

public import StacksFrontier.RingTheory.MilnorPatching.RelativeProperties
public import StacksFrontier.RingTheory.Localization.Glueing.CategoricalPullback
import Mathlib

/-!
# Relatively flat finitely presented quotients over a fibre product

In the relative situation of a fibre product `B' = B ×_A A'` with a ring map `B' → D'`, the
finitely presented quotients of a `D'`-module that are flat over `B'` correspond exactly to
compatible pairs of finitely presented quotients of its two base changes that are flat over `B`
and over `A'`.  The correspondence is extension of scalars in one direction and the module fibre
product in the other.

## Main definitions

* `MilnorPatching.RelativeFlatFinitelyPresentedQuotient` is the property of a quotient over `D'`
  appearing on the first side of the correspondence.
* `MilnorPatching.CompatibleRelativeFlatFinitelyPresentedQuotient` is the corresponding property
  of a compatible pair of quotients over `D` and `C'`.

## Main results

* `MilnorPatching.relativeFlatFinitelyPresentedQuotientsEquivalence` is Stacks Tag 08KR: the
  equivalence of the two categories of quotients, with its forward functor identified with
  extension of scalars and its inverse identified on objects with the module fibre product.

## Implementation notes

A quotient is represented by an object of an under category whose structure morphism is
surjective.  That keeps the quotient map as part of the datum and makes two presentations of the
same quotient canonically isomorphic rather than equal.  Compatibility of two quotient maps over
`C` is exactly the commuting-square condition on a morphism in the categorical pullback of the
module categories, so no separate compatibility datum is needed.

## References

* [Stacks Project, Tag 08KR](https://stacks.math.columbia.edu/tag/08KR)
-/

section

section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u

namespace MilnorPatching
open ModuleGlueing
@[expose] public section

variable {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
variable {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
variable {base : RingFibreProduct.Situation toBase surjection I}

/-- The property of a surjective quotient of `L` which is finitely presented over `D'`
and flat over the original fibre-product ring `B'`. -/
public def RelativeFlatFinitelyPresentedQuotient
    (s : RelativeModuleFibreProductSituation (D' := D') base)
    (L : ModuleCat.{u} D') : ObjectProperty (Under L) :=
  fun q ↦ Function.Surjective q.hom ∧
    Module.FinitePresentation D' q.right ∧
      Module.Flat base.fibreProduct
        ((ModuleCat.restrictScalars.{u, u, u} s.toD').obj q.right)

/-- The property of a compatible pair of quotient maps after extending `L` to `D` and
`C'`: both maps are surjective, both targets are finitely presented, and the targets are
flat over `B` and `A'`, respectively.  Since the map is a morphism in the categorical
pullback, its two scalar extensions to `C` agree as quotients of `C ⊗_{D'} L`. -/
public def CompatibleRelativeFlatFinitelyPresentedQuotient
    (s : RelativeModuleFibreProductSituation (D' := D') base)
    (L : ModuleCat.{u} D') :
    letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    letI : Algebra base.fibreProduct A :=
      (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
    ObjectProperty
      (Under
        ((extensionOfScalarsToTensorProductPullback (D' := D')
          ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
          ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
            A)).obj L)) :=
  fun q ↦ Function.Surjective q.hom.fst ∧ Function.Surjective q.hom.snd ∧
    Module.FinitePresentation s.D q.right.fst ∧
      Module.Flat B ((ModuleCat.restrictScalars.{u, u, u} s.BtoD).obj q.right.fst) ∧
        Module.FinitePresentation s.C' q.right.snd ∧
          Module.Flat A'
            ((ModuleCat.restrictScalars.{u, u, u} s.A'toC').obj q.right.snd)

end
end MilnorPatching
end
section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

universe u v w

namespace MilnorPatching
open ModuleGlueing
set_option backward.isDefEq.respectTransparency false

private lemma exists_lift_compatibleTensorPair {R S T U : Type u} [CommRing R] [CommRing S]
    [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (k : T →+* U)
    (comm : h.comp f = k.comp g)
    (hf : Function.Surjective f) (hk : Function.Surjective k)
    (hker : ∀ t : T, k t = 0 → ∃ r : R, f r = 0 ∧ g r = t)
    (L : ModuleCat.{u} R)
    (p : CompatiblePairs h k
      ((extensionOfScalarsToPullback f g h k comm).obj L)) :
    ∃ l : L, p.1.1 = (1 : S) ⊗ₜ[R,f] l ∧ p.1.2 = (1 : T) ⊗ₜ[R,g] l := by
  let : Module R S := Module.compHom S f
  let : Module R T := Module.compHom T g
  let : Module R U := Module.compHom U (k.comp g)
  let : Module T U := Module.compHom U k
  obtain ⟨l₀, hl₀⟩ := tensorUnit_surjective f hf L p.1.1
  let p₀ : CompatiblePairs h k
      ((extensionOfScalarsToPullback f g h k comm).obj L) :=
    ⟨((1 : S) ⊗ₜ[R,f] l₀, (1 : T) ⊗ₜ[R,g] l₀),
      extension_iso_one_tmul f g h k comm L l₀⟩
  have hp₀B : p₀.1.1 = (1 : S) ⊗ₜ[R,f] l₀ := rfl
  have hp₀T : p₀.1.2 = (1 : T) ⊗ₜ[R,g] l₀ := rfl
  let z : (extensionOfScalarsToPullback f g h k comm).obj L |>.snd :=
    p.1.2 - p₀.1.2
  have hzouter : (1 : U) ⊗ₜ[T,k] z = 0 := by
    have hsame : (1 : U) ⊗ₜ[T,k] p.1.2 =
        (1 : U) ⊗ₜ[T,k] p₀.1.2 := by
      calc
        _ = ((extensionOfScalarsToPullback f g h k comm).obj L).iso.hom
              ((1 : U) ⊗ₜ[S,h] p.1.1) := p.2.symm
        _ = ((extensionOfScalarsToPullback f g h k comm).obj L).iso.hom
              ((1 : U) ⊗ₜ[S,h] p₀.1.1) :=
            congrArg (fun x : ((extensionOfScalarsToPullback f g h k comm).obj L).fst =>
              ((extensionOfScalarsToPullback f g h k comm).obj L).iso.hom
                ((1 : U) ⊗ₜ[S,h] x)) (hl₀.symm.trans hp₀B.symm)
        _ = _ := p₀.2
    show (1 : U) ⊗ₜ[T,k] (p.1.2 - p₀.1.2) = 0
    rw [TensorProduct.tmul_sub, hsame, sub_self]
  have hzker : (LinearMap.rTensor L (tensorRingMapLinear g k)) z = 0 := by
    have hc := extendScalarsComp_rTensor g k L z
    apply ((ModuleCat.extendScalarsComp g k).app L).toLinearEquiv.injective
    simpa only [Iso.toLinearEquiv_apply, Iso.app_hom, map_zero] using hc.trans hzouter
  obtain ⟨l₁, hl₁B, hl₁T⟩ :=
    compatibleTensorPairs_surjective f g h k hf hk hker
      (show S →ₗ[R] U from
        { toFun := h, map_add' := h.map_add, map_smul' := fun r t => by
            show h (f r * t) = k (g r) * h t
            exact (map_mul h (f r) t).trans
              (congrArg (fun x : U => x * h t) (DFunLike.congr_fun comm r)) })
      (tensorRingMapLinear g k) (fun _ => rfl) (fun _ => rfl)
      (0 : (ModuleCat.extendScalars f).obj L) z (by simpa using hzker.symm)
  refine ⟨l₀ + l₁, ?_, ?_⟩
  · rw [TensorProduct.tmul_add, hl₁B, add_zero]
    exact hl₀.symm
  · rw [TensorProduct.tmul_add, hl₁T, ← hp₀T]
    dsimp [z]
    abel

private lemma compatiblePairs_map_surjective
    {S T U : Type u} [CommRing S] [CommRing T] [CommRing U]
    (h : S →+* U) (k : T →+* U) (hk : Function.Surjective k)
    {X Y : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} h)
      (ModuleCat.extendScalars.{u, u, u} k)}
    (f : X ⟶ Y) (hf : Function.Surjective f.fst) (hg : Function.Surjective f.snd)
    (p : CompatiblePairs h k Y) :
    ∃ q : CompatiblePairs h k X,
      f.fst q.1.1 = p.1.1 ∧ f.snd q.1.2 = p.1.2 := by
  let : Algebra T U := k.toAlgebra
  obtain ⟨n, hn⟩ := hf p.1.1
  obtain ⟨m, hm⟩ := tensorUnit_surjective k hk X.snd
    (X.iso.hom ((1 : U) ⊗ₜ[S,h] n))
  have hc : (1 : U) ⊗ₜ[T,k] (f.snd m) = (1 : U) ⊗ₜ[T,k] p.1.2 := by
    have H := ConcreteCategory.congr_hom f.w ((1 : U) ⊗ₜ[S,h] n)
    change Y.iso.hom ((1 : U) ⊗ₜ[S,h] (f.fst n)) =
      (ModuleCat.extendScalars k).map f.snd (X.iso.hom ((1 : U) ⊗ₜ[S,h] n)) at H
    rw [← hm] at H
    change Y.iso.hom ((1 : U) ⊗ₜ[S,h] (f.fst n)) =
      (1 : U) ⊗ₜ[T,k] (f.snd m) at H
    rw [hn] at H
    exact H.symm.trans p.property
  have hj : p.1.2 - f.snd m ∈ (RingHom.ker k • (⊤ : Submodule T Y.snd)) := by
    rw [← ker_tensorProductMk_of_surjective k hk]
    show (1 : U) ⊗ₜ[T,k] (p.1.2 - f.snd m) = 0
    rw [TensorProduct.tmul_sub, hc, sub_self]
  have hi : RingHom.ker k • (⊤ : Submodule T Y.snd) ≤
      Submodule.map f.snd.hom (RingHom.ker k • (⊤ : Submodule T X.snd)) := by
    rw [Submodule.smul_le]
    intro r hr x _
    obtain ⟨y, rfl⟩ := hg x
    rw [← map_smul]
    exact Submodule.mem_map_of_mem (Submodule.smul_mem_smul hr Submodule.mem_top)
  obtain ⟨j, hj, hfj⟩ := hi hj
  have hj0 : (1 : U) ⊗ₜ[T,k] j = 0 := by
    rwa [← ker_tensorProductMk_of_surjective k hk] at hj
  refine ⟨⟨(n, m + j), ?_⟩, hn, ?_⟩
  · show X.iso.hom ((1 : U) ⊗ₜ[S,h] n) = (1 : U) ⊗ₜ[T,k] (m + j)
    rw [TensorProduct.tmul_add, hj0, add_zero]
    exact hm.symm
  · show f.snd (m + j) = p.1.2
    rw [map_add, hfj]
    abel

private lemma surjective_homEquiv_of_surjective_components
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (k : T →+* U)
    (comm : h.comp f = k.comp g)
    (hf : Function.Surjective f) (hk : Function.Surjective k)
    (hker : ∀ t : T, k t = 0 → ∃ r : R, f r = 0 ∧ g r = t)
    (F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} h)
      (ModuleCat.extendScalars.{u, u, u} k) ⥤ ModuleCat.{u} R)
    (e : ∀ X, F.obj X ≃ CompatiblePairs h k X)
    (adj : extensionOfScalarsToPullback f g h k comm ⊣ F)
    (he : ∀ (M : ModuleCat.{u} R) X (a : M ⟶ F.obj X) (m : M),
      (e X (a m)).1.1 = ((adj.homEquiv M X).symm a).fst ((1 : S) ⊗ₜ[R,f] m) ∧
      (e X (a m)).1.2 = ((adj.homEquiv M X).symm a).snd ((1 : T) ⊗ₜ[R,g] m))
    (L : ModuleCat.{u} R) (X)
    (a : (extensionOfScalarsToPullback f g h k comm).obj L ⟶ X)
    (ha : Function.Surjective a.fst) (hb : Function.Surjective a.snd) :
    Function.Surjective ((adj.homEquiv L X) a) := by
  intro y
  obtain ⟨p, hp, hp'⟩ := compatiblePairs_map_surjective h k hk a ha hb (e X y)
  obtain ⟨l, hl, hl'⟩ :=
    exists_lift_compatibleTensorPair f g h k comm hf hk hker L p
  refine ⟨l, (e X).injective ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · have H := (he L X ((adj.homEquiv L X) a) l).1
    rwa [Equiv.symm_apply_apply, ← hl, hp] at H
  · have H := (he L X ((adj.homEquiv L X) a) l).2
    rwa [Equiv.symm_apply_apply, ← hl', hp'] at H

private lemma isIso_counit_of_surjective_pullback
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (k : T →+* U)
    (comm : h.comp f = k.comp g)
    (F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} h)
      (ModuleCat.extendScalars.{u, u, u} k) ⥤ ModuleCat.{u} R)
    (adj : extensionOfScalarsToPullback f g h k comm ⊣ F)
    (hk : Function.Surjective k)
    (hlift : ∀ (b : S) (a : T), h b = k a → ∃ r : R, f r = b ∧ g r = a) :
    IsIso adj.counit := by
  obtain ⟨G, _, adjG, _, hcG⟩ :=
    compatiblePairsRightAdjoint_counit_isIso_of_surjective h k f g comm hk
      (by
        intro p
        obtain ⟨r, hr, hr'⟩ := hlift p.1.1 p.1.2 p.property
        exact ⟨r, Subtype.ext (Prod.ext hr hr')⟩)
  have : IsIso adjG.counit := hcG
  rw [← adj.rightAdjointUniq_hom_counit adjG]
  infer_instance

private lemma finitePresentation_extendScalars
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    Module.FinitePresentation S ((ModuleCat.extendScalars f).obj M) := by
  let : Algebra R S := f.toAlgebra
  show Module.FinitePresentation S (S ⊗[R] M)
  infer_instance

private lemma extendScalars_map_surjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) (hg : Function.Surjective g) :
    Function.Surjective ((ModuleCat.extendScalars f).map g) := by
  have : Epi g := (ModuleCat.epi_iff_surjective g).mpr hg
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- A morphism in an under category is an isomorphism if its underlying morphism is. -/
private theorem isIso_of_isIso_right {C : Type u} [Category.{w} C] {X : C} {u v : Under X}
    (φ : u ⟶ v) (h : IsIso φ.right) : IsIso φ :=
  have : IsIso ((Under.forget X).map φ) := h
  isIso_of_reflects_iso φ (Under.forget X)

private theorem exists_under_fullSubcategory_equivalence_of_adjunction
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D]
    (E : C ⥤ D) (F : D ⥤ C) (adj : E ⊣ F)
    (L : C) (P : ObjectProperty (Under L))
    (Q : ObjectProperty (Under (E.obj L)))
    (hE : ∀ q, P q → Q ((Under.post E).obj q))
    (hF : ∀ q, Q q → P ((Under.post F ⋙ Under.map (adj.unit.app L)).obj q))
    (hu : ∀ q, P q → IsIso (adj.unit.app q.right))
    (hc : ∀ q, Q q → IsIso (adj.counit.app q.right)) :
    ∃ e : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (P.ι ⋙ Under.post E ≅ e.functor ⋙ Q.ι) ∧
        ∀ q, (e.inverse.obj q).obj =
          (Under.post F ⋙ Under.map (adj.unit.app L)).obj q.obj := by
  let eF := Q.lift (P.ι ⋙ Under.post E) (fun q => hE q.obj q.property)
  let eG := P.lift (Q.ι ⋙ Under.post F ⋙ Under.map (adj.unit.app L))
    (fun q => hF q.obj q.property)
  let a : eF ⊣ eG :=
    (Under.postAdjunctionLeft adj).restrictFullyFaithful
      P.fullyFaithfulι Q.fullyFaithfulι (Iso.refl _) (Iso.refl _)
  have hu' (q : P.FullSubcategory) : IsIso (a.unit.app q) := by
    rw [← P.isIso_hom_iff]
    show IsIso (P.ι.map (a.unit.app q))
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    have : IsIso ((Under.postAdjunctionLeft adj).unit.app (P.ι.obj q)) :=
      isIso_of_isIso_right _ (hu q.obj q.property)
    infer_instance
  have hc' (q : Q.FullSubcategory) : IsIso (a.counit.app q) := by
    rw [← Q.isIso_hom_iff]
    show IsIso (Q.ι.map (a.counit.app q))
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    have : IsIso ((Under.postAdjunctionLeft adj).counit.app (Q.ι.obj q)) :=
      isIso_of_isIso_right _ (hc q.obj q.property)
    infer_instance
  exact ⟨a.toEquivalence, ⟨Iso.refl _⟩, fun _ => rfl⟩

variable {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
variable {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
variable {base : RingFibreProduct.Situation toBase surjection I}

set_option maxHeartbeats 8000000 in
-- Comparing the scalar-extension functors unfolds several layers of module structures.
/-- **Stacks Project, Tag 08KR.** If `B' → D'` is of finite presentation, the
finitely presented quotients of a `D'`-module which are flat over `B'` correspond to
pairs of finitely presented quotients after base change to `D` and `C'`, flat over `B`
and `A'`, and agreeing as quotients after base change to `C`.

The forward correspondence is extension of scalars.  The inverse target module is the
fibre product of the two quotient modules over their common quotient over `C`; the final
formula records the prescribed quotient map from `L`.

Scalar extension and the compatible-pairs construction give the canonical equivalence of
finitely presented relatively flat quotient categories. -/
@[stacks 08KR]
public theorem relativeFlatFinitelyPresentedQuotientsEquivalence
    (s : RelativeModuleFibreProductSituation (D' := D') base)
    (hfp : s.toD'.FinitePresentation) (L : ModuleCat.{u} D') :
    let E := (letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A))
    let source := (RelativeFlatFinitelyPresentedQuotient s L).FullSubcategory
    let target := (CompatibleRelativeFlatFinitelyPresentedQuotient s L).FullSubcategory
    ∃ e : source ≌ target,
      Nonempty
          ((RelativeFlatFinitelyPresentedQuotient s L).ι ⋙ Under.post E ≅
            e.functor ⋙ (CompatibleRelativeFlatFinitelyPresentedQuotient s L).ι) ∧
        ∀ q : target,
          ∃ glueEquiv : (e.inverse.obj q).obj.right ≃
              RelativeCompatiblePairs s q.obj.right,
            ∀ l : L,
              (glueEquiv ((e.inverse.obj q).obj.hom l)).1.1 =
                  q.obj.hom.fst
                    ((ModuleCat.extendRestrictScalarsAdj s.toD).unit.app L l) ∧
                (glueEquiv ((e.inverse.obj q).obj.hom l)).1.2 =
                  q.obj.hom.snd
                    ((ModuleCat.extendRestrictScalarsAdj s.toC').unit.app L l) := by
  let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
  let : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
  let : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
  let : Algebra base.fibreProduct A :=
    (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
  let E := extensionOfScalarsToTensorProductPullback (D' := D')
    ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
    ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A)
  let P := RelativeFlatFinitelyPresentedQuotient s L
  let Q := CompatibleRelativeFlatFinitelyPresentedQuotient s L
  obtain ⟨F, glue, adj, hglue, -, -, hflat, hunit, eqv, ⟨eqvE⟩, _⟩ :=
    relativelyFlatModulesEquivalenceOverFibreProduct s
  have hk : Function.Surjective s.C'toC := by
    exact Algebra.TensorProduct.map_surjective (AlgHom.id base.fibreProduct D')
      ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A)
      Function.surjective_id base.surjective_surjection
  have hlift : ∀ (b : s.D) (a : s.C'), s.DtoC b = s.C'toC a →
      ∃ r : D', s.toD r = b ∧ s.toC' r = a := by
    intro b a ha
    obtain ⟨r, hr⟩ := s.toRelativePullback_surjective ⟨(b, a), ha⟩
    exact ⟨r, congrArg (fun x => x.1.1) hr, congrArg (fun x => x.1.2) hr⟩
  have : IsIso adj.counit := isIso_counit_of_surjective_pullback
    s.toD s.toC' s.DtoC s.C'toC s.relativeSquare_comm F adj hk hlift
  have hf : Function.Surjective s.toD := by
    intro b
    obtain ⟨a, ha⟩ := hk (s.DtoC b)
    obtain ⟨r, hr, _⟩ := hlift b a ha.symm
    exact ⟨r, hr⟩
  have hker : ∀ a : s.C', s.C'toC a = 0 → ∃ r : D', s.toD r = 0 ∧ s.toC' r = a :=
    fun a ha => hlift 0 a ((map_zero s.DtoC).trans ha.symm)
  have hE : ∀ q, P q → Q ((Under.post E).obj q) := by
    intro q hq
    obtain ⟨hs, hfpq, hflq⟩ := hq
    have : Module.FinitePresentation D' q.right := hfpq
    let qflat : ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{u} D' => Module.Flat base.fibreProduct
          ((ModuleCat.restrictScalars s.toD').obj M)) := ⟨q.right, hflq⟩
    let i := eqvE.app qflat
    have hB := (eqv.functor.obj qflat).property.1
    have hA := (eqv.functor.obj qflat).property.2
    refine ⟨extendScalars_map_surjective s.toD q.hom hs,
      extendScalars_map_surjective s.toC' q.hom hs,
      finitePresentation_extendScalars s.toD q.right, ?_,
      finitePresentation_extendScalars s.toC' q.right, ?_⟩
    · exact @Module.Flat.of_linearEquiv B _ _ _ _ _ _ _ hB
        (((ModuleCat.restrictScalars s.BtoD).mapIso
          ((CategoricalPullback.π₁ _ _).mapIso i)).toLinearEquiv)
    · exact @Module.Flat.of_linearEquiv A' _ _ _ _ _ _ _ hA
        (((ModuleCat.restrictScalars s.A'toC').mapIso
          ((CategoricalPullback.π₂ _ _).mapIso i)).toLinearEquiv)
  have hF : ∀ q, Q q → P ((Under.post F ⋙ Under.map (adj.unit.app L)).obj q) := by
    intro q hq
    obtain ⟨hs₁, hs₂, hfp₁, hfl₁, hfp₂, hfl₂⟩ := hq
    refine ⟨?_, ?_, hflat q.right ⟨hfl₁, hfl₂⟩⟩
    · show Function.Surjective (adj.unit.app L ≫ F.map q.hom)
      have H := surjective_homEquiv_of_surjective_components s.toD s.toC' s.DtoC s.C'toC
        s.relativeSquare_comm hf hk hker F (fun X ↦ (glue X).toEquiv) adj hglue L q.right q.hom
        hs₁ hs₂
      exact adj.homEquiv_apply L q.right q.hom ▸ H
    · exact finitePresentation_rightAdjoint_obj_of_factorization
        s F adj inferInstance q.right hfp₁ hfl₁ hfp₂ hfl₂
        (RingHom.id base.fibreProduct) s.toD' (RingHom.comp_id _)
        (by change Module.Flat base.fibreProduct base.fibreProduct; infer_instance) hfp
  obtain ⟨e, he, hi⟩ :=
    exists_under_fullSubcategory_equivalence_of_adjunction E F adj L P Q hE hF
    (fun q hq => hunit q.right hq.2.2) (fun _ _ => inferInstance)
  refine ⟨e, he, ?_⟩
  intro q
  rw [hi q]
  refine ⟨(glue q.obj.right).toEquiv, ?_⟩
  intro l
  show (glue q.obj.right ((adj.unit.app L ≫ F.map q.obj.hom) l)).1.1 = _ ∧
    (glue q.obj.right ((adj.unit.app L ≫ F.map q.obj.hom) l)).1.2 = _
  have H := hglue L q.obj.right ((adj.homEquiv L q.obj.right) q.obj.hom) l
  rw [Equiv.symm_apply_apply] at H
  have hhom := adj.homEquiv_apply L q.obj.right q.obj.hom
  exact hhom ▸ H

end MilnorPatching
end

end
